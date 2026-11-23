module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.Algebra.Group.Subgroup.Order

@[expose] public section

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.minkRam :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K ≠ 1 → ∃ p : ℕ, p.Prime ∧ ¬ UnramAt K p := by
  intro K _ _ hK
  have h1 : 1 < Module.finrank ℚ K := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    omega
  have h2 := NumberField.abs_discr_gt_two h1
  set D := differentIdeal ℤ (𝓞 K) with hD
  have hnorm : D.absNorm = (NumberField.discr K).natAbs :=
    NumberField.absNorm_differentIdeal K (𝓞 K)
  have hDtop : D ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at hnorm
    have h3 : ((NumberField.discr K).natAbs : ℤ) = |NumberField.discr K| := Int.natCast_natAbs _
    rw [← hnorm] at h3
    omega
  obtain ⟨P, hPmax, hDP⟩ := Ideal.exists_le_maximal D hDtop
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff] at hDP
    exact differentIdeal_ne_bot hDP
  haveI : NeZero P := ⟨hPne⟩
  refine ⟨Ideal.absNorm (Ideal.under ℤ P), Nat.absNorm_under_prime P, fun hun => ?_⟩
  have hram := hun P hPmax.isPrime (Int.absNorm_under_mem P)
  rw [Ideal.ramificationIdx_eq_one_iff] at hram
  exact (dvd_differentIdeal_iff.mp (Ideal.dvd_iff_le.mpr hDP)) hram
end

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineMap :
    ∀ (k K H : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field H] [NumberField H] [Algebra k K] [Algebra K H] [Algebra k H] [IsScalarTower k K H] [IsGalois k K] [IsGalois k H] (w : HeightOneSpectrum (𝓞 H)), (w.asIdeal.inertia Gal(H/k)).map (resTo k K H) = (w.asIdeal.under (𝓞 K)).inertia Gal(K/k) := by
  intro k K H _ _ _ _ _ _ _ _ _ _ _ _ w
  haveI : IsGalois K H := IsGalois.tower_top_of_isGalois k K H
  have comm : ∀ (σ : Gal(H/k)) (x : 𝓞 K),
      algebraMap (𝓞 K) (𝓞 H) (resTo k K H σ • x) = σ • algebraMap (𝓞 K) (𝓞 H) x := by
    intro σ x
    apply FaithfulSMul.algebraMap_injective (𝓞 H) H
    have e1 : algebraMap (𝓞 H) H (σ • algebraMap (𝓞 K) (𝓞 H) x) =
        σ • algebraMap (𝓞 H) H (algebraMap (𝓞 K) (𝓞 H) x) := algebraMap.smul' _ _ _
    have e2 : algebraMap (𝓞 K) K (resTo k K H σ • x) = resTo k K H σ • algebraMap (𝓞 K) K x :=
      algebraMap.smul' _ _ _
    rw [e1, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) K H, IsScalarTower.algebraMap_apply (𝓞 K) K H, e2]
    exact AlgEquiv.restrictNormal_commutes σ K _
  have comm2 : ∀ (τ : Gal(H/K)) (y : 𝓞 H), (τ.restrictScalars k) • y = τ • y := by
    intro τ y
    apply FaithfulSMul.algebraMap_injective (𝓞 H) H
    have e1 : algebraMap (𝓞 H) H ((τ.restrictScalars k) • y) =
        (τ.restrictScalars k) • algebraMap (𝓞 H) H y := algebraMap.smul' _ _ _
    have e2 : algebraMap (𝓞 H) H (τ • y) = τ • algebraMap (𝓞 H) H y := algebraMap.smul' _ _ _
    rw [e1, e2]
    rfl
  set P := w.asIdeal with hP
  set Q := P.under (𝓞 K) with hQ
  set p := P.under (𝓞 k) with hp
  haveI : Nonempty (Q.primesOver (𝓞 H)) := ⟨⟨P, inferInstance, inferInstance⟩⟩
  have hle : (P.inertia Gal(H/k)).map (resTo k K H) ≤ Q.inertia Gal(K/k) := by
    rintro _ ⟨σ, hσ, rfl⟩
    intro x
    have h1 := hσ (algebraMap (𝓞 K) (𝓞 H) x)
    show _ ∈ Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) P
    rw [Ideal.mem_comap, map_sub, comm]
    exact h1
  apply Subgroup.eq_of_le_of_card_ge hle
  have cG : Nat.card (P.inertia Gal(H/k)) = p.ramificationIdxIn (𝓞 H) :=
    Ideal.card_inertia_eq_ramificationIdxIn p P
  have cK : Nat.card (Q.inertia Gal(K/k)) = p.ramificationIdxIn (𝓞 K) :=
    Ideal.card_inertia_eq_ramificationIdxIn p Q
  have cH : Nat.card (P.inertia Gal(H/K)) = Q.ramificationIdxIn (𝓞 H) :=
    Ideal.card_inertia_eq_ramificationIdxIn Q P
  have hmul : p.ramificationIdxIn (𝓞 K) * Q.ramificationIdxIn (𝓞 H) = p.ramificationIdxIn (𝓞 H) :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn Q Gal(K/k) (𝓞 H) Gal(H/k) Gal(H/K)
  let f : (P.inertia Gal(H/k)) →* Gal(K/k) := (resTo k K H).comp (Subgroup.subtype _)
  have hrange : f.range = (P.inertia Gal(H/k)).map (resTo k K H) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let g : (P.inertia Gal(H/K)) →* (P.inertia Gal(H/k)) :=
    { toFun := fun τ => ⟨(τ.1.restrictScalars k), fun y => by
        rw [comm2]
        exact τ.2 y⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hker : f.ker ≤ g.range := by
    intro σ hσ
    have hfix : ∀ c : K, σ.1 (algebraMap K H c) = algebraMap K H c := by
      intro c
      have h2 : resTo k K H σ.1 = 1 := hσ
      rw [← AlgEquiv.restrictNormal_commutes σ.1 K c]
      have h3 : σ.1.restrictNormal K = 1 := h2
      rw [h3]
      rfl
    let τ : Gal(H/K) := AlgEquiv.ofRingEquiv (f := σ.1.toRingEquiv) hfix
    have hτ : τ ∈ P.inertia Gal(H/K) := by
      intro y
      have h4 := σ.2 y
      rw [← comm2] at *
      exact h4
    exact ⟨⟨τ, hτ⟩, by
      apply Subtype.ext
      ext z
      rfl⟩
  have hcardker : Nat.card f.ker ≤ Nat.card (P.inertia Gal(H/K)) :=
    (Subgroup.card_le_of_le hker).trans
      (Nat.card_le_card_of_surjective g.rangeRestrict g.rangeRestrict_surjective)
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have key := f.ker.card_mul_index
  rw [Subgroup.index_ker, hrange, cG, ← hmul] at key
  rw [cK]
  by_contra hlt
  push_neg at hlt
  have hQpos : 0 < Q.ramificationIdxIn (𝓞 H) := by
    rw [← cH]
    exact Nat.card_pos
  rw [cH] at hcardker
  nlinarith [Nat.mul_le_mul hcardker (le_of_lt hlt)]
end

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.grMaxOf :
    ∀ (p : ℕ) [Fact p.Prime] (R G : Type) [CommRing R] [IsLocalRing R] [CommGroup G] [Finite G], (p : R) ∈ IsLocalRing.maximalIdeal R → IsPGroup p G → ∀ M : Ideal (MonoidAlgebra R G), M.IsMaximal → M = (IsLocalRing.maximalIdeal R).comap (aug R G) := by
  intro p _ R G _ _ _ _ hpm hG M hM
  classical
  have hcomap : M.comap (algebraMap R (MonoidAlgebra R G)) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal M)
  letI : Field (MonoidAlgebra R G ⧸ M) := Ideal.Quotient.field M
  have hpQ : ((p : ℕ) : MonoidAlgebra R G ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]
    have h0 : (p : R) ∈ M.comap (algebraMap R (MonoidAlgebra R G)) := by
      rw [hcomap]; exact hpm
    simpa using h0
  haveI : CharP (MonoidAlgebra R G ⧸ M) p := by
    have h := CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hpQ
    exact h ▸ ringChar.charP _
  have hg : ∀ g : G, Ideal.Quotient.mk M (MonoidAlgebra.single g 1) = 1 := by
    intro g
    obtain ⟨k, hk⟩ := hG g
    have h1 : (Ideal.Quotient.mk M (MonoidAlgebra.single g (1 : R)) - 1) ^ p ^ k = 0 := by
      rw [sub_pow_char_pow, one_pow, ← map_pow, MonoidAlgebra.single_pow, one_pow, hk,
        ← MonoidAlgebra.one_def, map_one, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mp h1)
  have hext : Ideal.Quotient.mkₐ R M = (Algebra.ofId R _).comp (aug R G) := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp [hg, aug_single]
    · exact Subsingleton.elim _ _
  have hle : (IsLocalRing.maximalIdeal R).comap (aug R G) ≤ M := by
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h3 := congrArg (fun f => f x) hext
    simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, Algebra.ofId_apply] at h3
    rw [h3, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
    have h2 : aug R G x ∈ M.comap (algebraMap R (MonoidAlgebra R G)) := by
      rw [hcomap]; exact hx
    exact h2
  haveI : ((IsLocalRing.maximalIdeal R).comap (aug R G)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (aug R G) (fun r => ⟨MonoidAlgebra.single 1 r, aug_single R G 1 r⟩)
  exact (Ideal.IsMaximal.eq_of_le this hM.ne_top hle).symm
end

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.augKer :
    ∀ (R G : Type) [CommRing R] [CommGroup G], RingHom.ker (aug R G) = augIdeal R G ∧ Function.Surjective (aug R G) := by
  intro R G _ _
  have key : ∀ x : MonoidAlgebra R G,
      x - algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ augIdeal R G := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
      exact add_mem hx hy
    | single g r =>
      rw [aug_single]
      have h1 : MonoidAlgebra.single g r - algebraMap R (MonoidAlgebra R G) r =
          MonoidAlgebra.single 1 r * (MonoidAlgebra.of R G g - 1) := by
        rw [mul_sub, mul_one, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul,
          mul_one, MonoidAlgebra.coe_algebraMap]
        rfl
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, rfl⟩)
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro x hx
    have := key x
    rwa [RingHom.mem_ker.mp hx, map_zero, sub_zero] at this
  · rw [augIdeal, Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, MonoidAlgebra.of_apply, aug_single,
      sub_self]
  · intro r
    exact ⟨MonoidAlgebra.single 1 r, aug_single R G 1 r⟩
end

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.phiLe :
    ∀ (p : ℕ) [Fact p.Prime] (P : Type) [Group P] [Finite P], IsPGroup p P → ∀ K : Subgroup P, IsCoatom K → K.Normal ∧ K.index = p ∧ phi p P ≤ K := by
  intro p _ P _ _ hP K hK
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hN : K.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom K Group.normalizerCondition_of_isNilpotent hK
  refine ⟨hN, ?_⟩
  have hQp : IsPGroup p (P ⧸ K) := hP.to_quotient K
  have hne : Nontrivial (P ⧸ K) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hK.1
  have hdvd : p ∣ Nat.card (P ⧸ K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
    have h1 : 1 < Nat.card (P ⧸ K) := Finite.one_lt_card
    rcases n with _ | n
    · rw [hn, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · rw [hn, pow_succ]
      exact dvd_mul_left _ _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P ⧸ K) p hdvd
  have htop : Subgroup.zpowers x = ⊤ := by
    have h1 : K ≤ (Subgroup.zpowers x).comap (QuotientGroup.mk' K) := by
      intro k hk
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
      exact one_mem _
    rcases hK.le_iff.mp h1 with h | h
    · rw [eq_top_iff]
      intro y _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      have : g ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' K) := by
        rw [h]
        exact Subgroup.mem_top g
      exact this
    · exfalso
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      have : g ∈ (Subgroup.zpowers ((g : P ⧸ K))).comap (QuotientGroup.mk' K) :=
        Subgroup.mem_zpowers _
      rw [h] at this
      rw [(QuotientGroup.eq_one_iff g).mpr this, orderOf_one] at hx
      exact (Fact.out : p.Prime).one_lt.ne hx
  have hcard : Nat.card (P ⧸ K) = p := by
    rw [← Subgroup.card_top, ← htop, Nat.card_zpowers, hx]
  have hidx : K.index = p := by
    rw [Subgroup.index, hcard]
  refine ⟨hidx, ?_⟩
  have hcomm : ∀ a b : P ⧸ K, a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.zpowers x := htop ▸ Subgroup.mem_top a
    have hb : b ∈ Subgroup.zpowers x := htop ▸ Subgroup.mem_top b
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self x m n).eq
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    show g ^ p ∈ K
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
    exact pow_card_eq_one'
  · rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hcomm (a : P ⧸ K) (b : P ⧸ K), mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
end

section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.unramIff :
    (∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ), p.Prime → (UnramAt L p ↔ ∀ w : HeightOneSpectrum (𝓞 L), (p : 𝓞 L) ∈ w.asIdeal → w.asIdeal.inertia Gal(L/ℚ) = ⊥)) ∧ (∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → (UnramAt L p ↔ ¬ (p : ℤ) ∣ NumberField.discr L)) ∧ ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime → UnramAt L p → UnramAt K p := by
  have h2 : ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime →
      (UnramAt L p ↔ ¬ (p : ℤ) ∣ NumberField.discr L) := by
    intro L _ _ p hp
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rw [NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L) hpZ]
    unfold UnramAt
    refine forall_congr' fun P => forall_congr' fun hP => ?_
    haveI := hP
    rw [Int.cast_natCast, Ideal.ramificationIdx_eq_one_iff]
  refine ⟨?_, h2, ?_⟩
  · intro L _ _ _ p hp
    unfold UnramAt
    constructor
    · intro h w hw
      haveI := w.isPrime
      rw [← Subgroup.card_eq_one,
        Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under ℤ) w.asIdeal,
        Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal Gal(L/ℚ)]
      exact h w.asIdeal w.isPrime hw
    · intro h P hP hpP
      haveI := hP
      have hne : P ≠ ⊥ := by
        intro hb
        rw [hb, Ideal.mem_bot] at hpP
        exact hp.ne_zero (by exact_mod_cast hpP)
      have hw := h ⟨P, hP, hne⟩ hpP
      rw [← Subgroup.card_eq_one,
        Ideal.card_inertia_eq_ramificationIdxIn (P.under ℤ) P,
        Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P Gal(L/ℚ)] at hw
      exact hw
  · intro K L _ _ _ _ _ p hp hL
    exact (h2 K p hp).2 fun hd => (h2 L p hp).1 hL (hd.trans (NumberField.discr_dvd_discr K L))
end
