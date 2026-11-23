module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerDefs
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Devissage
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ABHNPrep
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteSetOfNsmulEqZeroQZ
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplit
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.EqZeroOfBrauerLocalApplyEqZero

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global DirectSum

noncomputable section

theorem QZ.nsmul_mk (j : ℕ) (r : ℚ) : j • QZ.mk r = QZ.mk (j * r) := by
  have h := map_nsmul QZ.mkHom j r
  rw [nsmul_eq_mul] at h
  exact h.symm


open Classical in
def qzDiv (ℓ : ℕ) (q : QZ) : QZ :=
  if q = 0 then 0 else QZ.mk ((QZ.mk_surjective q).choose / ℓ)

theorem qzDiv_zero (ℓ : ℕ) : qzDiv ℓ 0 = 0 := by
  simp [qzDiv]

theorem nsmul_qzDiv {ℓ : ℕ} (hℓ : ℓ ≠ 0) (q : QZ) : ℓ • qzDiv ℓ q = q := by
  by_cases hq : q = 0
  · rw [hq, qzDiv_zero, smul_zero]
  · rw [qzDiv, if_neg hq, QZ.nsmul_mk]
    have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ
    rw [mul_div_cancel₀ _ hℓq]
    exact (QZ.mk_surjective q).choose_spec

variable {K : FiniteSubfield}

theorem eq_zero_inl_of_pow_nsmul_eq_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (v : InfinitePlace K.1)
    (hv : ℓ ≠ 2 ∨ v.IsComplex) (t : localGaloisCohomology K 2 (.inl v)) (k : ℕ) (ht : ℓ ^ k • t = 0) :
    t = 0 := by
  rcases hv with h2 | hc
  · have h2t : 2 • t = 0 := by
      apply placeInv_injective (.inl v)
      rw [map_nsmul, map_zero]
      rcases placeInv_inl_eq_zero_or_eq_half v t with h | h
      · rw [h, smul_zero]
      · rw [h, two_nsmul, QZ.mk_half_add_mk_half]
    exact eq_zero_of_coprime_nsmul_eq_zero ((Nat.coprime_primes Nat.prime_two hℓ).2 (Ne.symm h2)) h2t ht
  · have := subsingleton_cohomology_two_of_isComplex v hc
    exact Subsingleton.elim (α := cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) _ _

variable (K) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)


include hℓ hS in
theorem exists_nsmul_eq_localPrimaryKernel (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1)
    (t : localPrimaryKernel K S ℓ) : ∃ s : localPrimaryKernel K S ℓ, ℓ • s = t := by
  classical
  obtain ⟨⟨k, hk⟩, hout, hsum⟩ := t.2
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hinf : ∀ v : InfinitePlace K.1, (t : ⨁ v : Place K.1, localGaloisCohomology K 2 v) (.inl v) = 0 :=
    fun v => eq_zero_inl_of_pow_nsmul_eq_zero hℓ v (hK.imp id fun h => h.isComplex v) _ k (by
      have := congrArg (fun x : ⨁ v : Place K.1, localGaloisCohomology K 2 v => x (.inl v)) hk
      rwa [DFinsupp.smul_apply] at this)
  let e : ∀ v : HeightOneSpectrum (𝓞 K.1), localGaloisCohomology K 2 (.inr v) ≃+ QZ := fun v =>
    AddEquiv.ofBijective (placeInv (.inr v)) (placeInv_bijective_inr v)
  let f : ∀ v : Place K.1, localGaloisCohomology K 2 v → localGaloisCohomology K 2 v
    | .inl _ => fun _ => 0
    | .inr v => fun x => (e v).symm (qzDiv ℓ (e v x))
  have hf : ∀ v, f v 0 = 0 := by
    rintro (v | v)
    · rfl
    · change (e v).symm (qzDiv ℓ (e v 0)) = 0
      rw [map_zero, qzDiv_zero, map_zero]
  let s₀ : ⨁ v : Place K.1, localGaloisCohomology K 2 v := DFinsupp.mapRange f hf t.1
  have hs₀ : ℓ • s₀ = t := by
    refine DFinsupp.ext fun v => ?_
    rw [DFinsupp.smul_apply, DFinsupp.mapRange_apply]
    rcases v with v | v
    · change ℓ • (0 : localGaloisCohomology K 2 (.inl v)) = _
      rw [smul_zero, hinf v]
    · change ℓ • (e v).symm (qzDiv ℓ (e v _)) = _
      rw [← map_nsmul, nsmul_qzDiv hℓ0, AddEquiv.symm_apply_apply]
  obtain ⟨v₀, hv₀⟩ := exists_place_above K ℓ hℓ
  let c := sumPlaceInv K s₀
  let o : ⨁ v : Place K.1, localGaloisCohomology K 2 v :=
    DirectSum.of (fun v : Place K.1 => localGaloisCohomology K 2 v) (Sum.inr v₀) ((e v₀).symm c)
  let s : ⨁ v : Place K.1, localGaloisCohomology K 2 v := s₀ - o
  have hc : ℓ • c = 0 := by
    change ℓ • sumPlaceInv K s₀ = 0
    rw [← map_nsmul, hs₀, hsum]
  have hs : ℓ • s = t := by
    rw [smul_sub, hs₀, ← map_nsmul, ← map_nsmul, hc, map_zero, map_zero, sub_zero]
  refine ⟨⟨s, ⟨k + 1, ?_⟩, fun v hv => ?_, ?_⟩, Subtype.ext hs⟩
  · rw [pow_succ, mul_smul, hs, hk]
  · have hne : (.inr v : Place K.1) ≠ .inr v₀ := fun h => hv (by cases h; exact hS v₀ hv₀)
    change s₀ (.inr v) - o (.inr v) = 0
    rw [show o (.inr v) = 0 from DirectSum.of_eq_of_ne _ _ _ hne, sub_zero]
    change (e v).symm (qzDiv ℓ (e v (t.1 (.inr v)))) = 0
    rw [hout v hv, map_zero, qzDiv_zero, map_zero]
  · change sumPlaceInv K (s₀ - o) = 0
    rw [map_sub, sumPlaceInv_of]
    change c - e v₀ ((e v₀).symm c) = 0
    rw [AddEquiv.apply_symm_apply, sub_self]



include hℓ hS in
theorem exists_nsmul_eq_h2SUnits (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1)
    (y : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 (AlgebraicClosure ℚ) S) 2) ℓ) :
    ∃ z : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 (AlgebraicClosure ℚ) S) 2) ℓ,
      ℓ • z = y := by
  obtain ⟨ιs⟩ := nonempty_localEmbeddings K
  let E := sUnitsH2PrimaryEquiv K S ℓ hℓ hS ιs
  obtain ⟨s, hs⟩ := exists_nsmul_eq_localPrimaryKernel K S ℓ hℓ hS hK (E y)
  refine ⟨E.symm s, ?_⟩
  rw [← E.symm_apply_apply y, ← hs]
  exact (map_nsmul E.symm ℓ s).symm

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory

universe u

section General

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
  [IsSepClosed Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n]
  (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal)


include hnS in
theorem finite_cohomology_one_rootsOfUnity [Finite S] :
    Finite (cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 1) := by
  refine (AddMonoidHom.finite_iff_finite_ker_range (kummerPicHom (Ω := Ω) S n)).2 ⟨?_, inferInstance⟩
  let k := kummerSUnitsHom (Ω := Ω) S n hnS
  have : Module.Finite ℤ (Additive (S.unit F)) := inferInstance
  have : AddGroup.FG (Additive (S.unit F)) := Module.Finite.iff_addGroup_fg.1 this
  have : AddGroup.FG k.range := AddGroup.fg_of_surjective k.rangeRestrict_surjective
  have htor : IsAddTorsion k.range := by
    rintro ⟨_, a, rfl⟩
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero (NeZero.ne n), ?_⟩
    apply Subtype.ext
    change n • k a = 0
    rw [← map_nsmul]
    exact (kummerSUnitsHom_eq_zero_iff (Ω := Ω) S n hnS _).2 ⟨a, rfl⟩
  have : Finite k.range := AddCommGroup.finite_of_fg_isAddTorsion _ htor
  refine Finite.of_injective (β := k.range) (fun y => ⟨y.1, ?_⟩) ?_
  · exact (kummerPicHom_eq_zero_iff (Ω := Ω) S n hnS y.1).1 y.2
  · intro y z h
    simp only at h
    exact Subtype.ext (Subtype.mk.inj h)


include hnS in
theorem finite_cohomology_two_rootsOfUnity_of_finite
    (hfin : {y : cohomology (galSUnits S (maxUnramifiedOutside F Ω S)) 2 | n • y = 0}.Finite) :
    Finite (cohomology (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) 2) := by
  have hK := sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS
  let f := (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).f 2).hom.toAddMonoidHom
  refine (AddMonoidHom.finite_iff_finite_ker_range f).2 ⟨?_, ?_⟩
  · have : Finite (cohomology (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).X₃ 1) :=
      Finite.of_injective _ (h1SUnitsToSPic_injective (Ω := Ω) S)
    let d := (δ hK 1 2 rfl).hom.toAddMonoidHom
    have : Finite d.range := Set.finite_coe_iff.2 (Set.finite_range d)
    refine Finite.of_injective (β := d.range) (fun y => ⟨y.1, ?_⟩) ?_
    · obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hK 1 2 rfl) y.1 y.2
      exact ⟨z, hz⟩
    · intro y z h
      simp only at h
      exact Subtype.ext (Subtype.mk.inj h)
  · show Finite (SetLike.coe f.range)
    refine (hfin.subset ?_).to_subtype
    rintro _ ⟨x, rfl⟩
    have h1 := cohomologyMap_g_cohomologyMap_f_apply
      (S := sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n) 2 x
    have hg : (cohomologyMap (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).g 2).hom (f x) =
        n • f x :=
      cohomologyMap_nsmul_id_apply (galSUnits S (maxUnramifiedOutside F Ω S)) n 2 (f x)
    exact hg.symm.trans h1

end General

section Brauer

open GroundTheory.Global FiniteSubfield DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

theorem mem_of_dvd_of_mem {d n : ℕ} (hd : d ∣ n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K.1)) (hv : ((d : ℕ) : 𝓞 K.1) ∈ v.asIdeal) : v ∈ S := by
  obtain ⟨c, hc⟩ := hd
  refine hS v ?_
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hv

theorem eq_zero_of_nsmul_eq_zero_of_sUnitsBrauer_eq_zero (n : ℕ) (hn0 : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) (hy : n • y = 0) (hy' : sUnitsBrauer K S y = 0) :
    y = 0 := by
  induction n using Nat.strong_induction_on generalizing y with
  | _ n ih =>
  by_cases h1 : n = 1
  · subst h1
    exact (one_nsmul y).symm.trans hy
  have hℓ : n.minFac.Prime := Nat.minFac_prime h1
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 n.minFac hℓ.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn0 (hn.trans (mul_zero _))
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hn
    exact hm (hn ▸ Nat.minFac_dvd n)
  have hmy : m • y = 0 := by
    have ht : n.minFac ^ a • (m • y) = 0 := by rw [smul_smul, ← hn, hy]
    have hb : sUnitsBrauer K S (m • y) = 0 := by rw [map_nsmul, hy', nsmul_zero]
    exact eq_zero_of_sUnitsBrauer_eq_zero K S n.minFac hℓ
      (mem_of_dvd_of_mem K S (Nat.minFac_dvd n) hS) (m • y) a ht hb
  have hlt : m < n := by
    have h2 : 1 < n.minFac ^ a := Nat.one_lt_pow ha hℓ.one_lt
    rw [hn]
    exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) h2
  exact ih m hlt hm0 (mem_of_dvd_of_mem K S ⟨n.minFac ^ a, hn.trans (mul_comm _ _)⟩ hS) y hmy hy'

theorem finite_nsmul_eq_zero_sUnits_two [Finite S] (n : ℕ) (hn0 : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    {y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 | n • y = 0}.Finite := by
  obtain ⟨ιs⟩ := nonempty_localEmbeddings K
  let T : Set QZ := {u | n • u = 0}
  have : Finite T := (AddCircle.finite_torsion (1 : ℚ) (Nat.pos_of_ne_zero hn0)).to_subtype
  let t := (brauerLocal ιs).comp (sUnitsBrauer K S)
  let inv (v : Place K.1) := (placeInv (K := K) v).comp
    ((DFinsupp.evalAddMonoidHom (β := localGaloisCohomology K 2) v).comp t)
  have ht (y : {y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 | n • y = 0}) (v : Place K.1) :
      inv v y.1 ∈ T :=
    (map_nsmul (inv v) n y.1).symm.trans ((congrArg (inv v) y.2).trans (inv v).map_zero)
  let Φ : {y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2 | n • y = 0} →
      (InfinitePlace K.1 → T) × (S → T) := fun y =>
    (fun w => ⟨inv (.inl w) y.1, ht y _⟩, fun w => ⟨inv (.inr w.1) y.1, ht y _⟩)
  refine Set.finite_coe_iff.1 (Finite.of_injective Φ fun y z h => ?_)
  have hinv (v : Place K.1) (hv : inv v y.1 = inv v z.1) : t y.1 v = t z.1 v :=
    placeInv_injective (K := K) v hv
  have htyz : t y.1 = t z.1 := by
    apply DFinsupp.ext
    intro v
    rcases v with w | w
    · have hw := congrArg (fun a : (InfinitePlace K.1 → T) × (S → T) => (a.1 w).1) h
      dsimp only [Φ] at hw
      exact hinv (.inl w) hw
    · by_cases hw : w ∈ S
      · have hw' := congrArg (fun a : (InfinitePlace K.1 → T) × (S → T) => (a.2 ⟨w, hw⟩).1) h
        dsimp only [Φ] at hw'
        exact hinv (.inr w) hw'
      · exact (brauerLocal_sUnitsBrauer_inr K S ιs y.1 w hw).trans
          (brauerLocal_sUnitsBrauer_inr K S ιs z.1 w hw).symm
  have hyz : sUnitsBrauer K S (y.1 - z.1) = 0 := by
    refine brauerLocal_injective ιs ?_
    rw [map_sub, map_sub, map_zero]
    exact sub_eq_zero.2 htyz
  have h0 := eq_zero_of_nsmul_eq_zero_of_sUnitsBrauer_eq_zero K S n hn0 hS (y.1 - z.1)
    (by rw [smul_sub, y.2, z.2, sub_zero]) hyz
  exact Subtype.ext (sub_eq_zero.1 h0)

theorem finite_cohomology_rootsOfUnity [Finite S] (n : ℕ) (hn0 : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (r : ℕ)
    (hr : r ≤ 2) :
    Finite (cohomology (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n) r) := by
  have : NeZero n := ⟨hn0⟩
  have hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv h => hv (hS v h)
  interval_cases r
  · have : Finite (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n) :=
      inferInstanceAs (Finite (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))))
    exact finite_cohomology_zero _
  · exact finite_cohomology_one_rootsOfUnity S n hnS
  · exact finite_cohomology_two_rootsOfUnity_of_finite S n hnS
      (finite_nsmul_eq_zero_sUnits_two K S n hn0 hS)

end Brauer

end GroundTheory.ProfCoh
end
