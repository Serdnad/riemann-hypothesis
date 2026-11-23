module

public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Formalism.CharacterColumnKernels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle204
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.UnramifiedH2Bound

open GlobalTheory.ShapeNeg GlobalTheory.CyclotomicH2Bound

theorem pow_mul_eq_zero_of_mul {p : ℕ} (hp : p.Prime) {n m : ℕ} {b : ℤ} (hb : ¬ ((p : ℤ) ^ m ∣ b))
    {x : ZMod (p ^ n)} (hx : (b : ZMod (p ^ n)) * x = 0) : ((p ^ m : ℕ) : ZMod (p ^ n)) * x = 0 := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩

  have hbx : b • x = 0 := by rwa [zsmul_eq_mul]
  have h1 : (addOrderOf x : ℤ) ∣ b := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hbx
  have h2 : addOrderOf x ∣ p ^ n := by
    have := addOrderOf_dvd_card (x := x)
    rwa [ZMod.card] at this
  obtain ⟨j, -, hjx⟩ := (Nat.dvd_prime_pow hp).mp h2
  have hjm : j < m := by
    by_contra hcon
    push Not at hcon
    apply hb
    rw [hjx] at h1
    exact (pow_dvd_pow (p : ℤ) hcon).trans (by exact_mod_cast h1)
  have h3 : addOrderOf x ∣ p ^ m := by
    rw [hjx]; exact pow_dvd_pow _ hjm.le
  have h4 : (p ^ m : ℕ) • x = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp h3
  rwa [nsmul_eq_mul] at h4

theorem h2_bounded_of_trivial_action : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} → (p : O) ≠ 0 →
    ∀ {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) →
    ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M), (∀ g m, ρ g m = m) →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  intro hTD p _ K hK O _ _ _ _ ϖ hϖ hpϖ hp0 M _ _ eM ρ hρ hcont
  have hp : p.Prime := Fact.out

  obtain ⟨σ, N, ζ', hζ'1, hσζ'⟩ :=
    GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity (p := p) (K := K) hK 1 Nat.one_pos
  rw [pow_one] at hσζ'

  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {(p : O) ^ N}) (by rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero N hp0) hϖ
  have hfinQ : Finite (O ⧸ Ideal.span {(p : O) ^ N}) := by
    rw [hk]; exact finite_quot hϖ k
  refine ⟨(p ^ N) ^ ((p ^ N) ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N})), ?_⟩
  intro n hn h
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
  have htriv : ∀ (g : Formalism.GaloisCohomology.GK p K) (m : Lev M (ϖ ^ n)), levRepZ p n h ρ g m = m := by
    intro g m
    rw [levRepZ_apply]
    exact Lev.ext (by rw [levRep_val, hρ])

  obtain ⟨x₀, hx₀⟩ := lev_cyclic eM hϖ n
  have hx₀k : (ϖ ^ n) • x₀ = 0 := Lev.ext (by rw [Lev.val_smul, Lev.smul_val, Lev.val_zero])
  have hfinL : Finite (Lev M (ϖ ^ n)) := by
    have := finite_quot hϖ n
    refine Finite.of_surjective (fun q : O ⧸ Ideal.span {ϖ ^ n} => q.out • x₀) ?_
    intro y
    obtain ⟨t, rfl⟩ := hx₀ y
    exact ⟨Ideal.Quotient.mk _ t, out_smul n hx₀k t⟩
  obtain ⟨⟨e⟩, -, -, -, hcup⟩ :=
    hTD p K hK n (Lev M (ϖ ^ n)) (levRepZ p n h ρ) hn (hcont n h)

  have hkill : ∀ (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (m : Lev M (ϖ ^ n)), ((p ^ N : ℕ) : ZMod (p ^ n)) * φ.1 m = 0 := by
    intro φ m
    by_cases hnN : n ≤ N
    · rw [(ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow p hnN), zero_mul]
    push Not at hnN
    obtain ⟨ζ, hζ⟩ := exists_prim p n
    have hσζn : (σ ζ) ^ (p ^ n) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hσζn
    have hcyc := cycK_eq_of_prim n σ hζ a ha.symm
    have hfixm : ((Formalism.GaloisCohomology.cycK p K n σ : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) *
        φ.1 (levRepZ p n h ρ σ⁻¹ m) = φ.1 m := by
      rw [← twDual_apply]
      exact DFunLike.congr_fun ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).mp φ.2 σ) m
    rw [htriv, hcyc] at hfixm
    have hnd : ¬ ((p : ℤ) ^ N ∣ (a : ℤ) - 1) := by
      rintro ⟨d, hd⟩
      apply hσζ'
      have hζ'n : ζ' ^ (p ^ n) = 1 := by
        obtain ⟨c, hc⟩ := pow_dvd_pow p hnN.le
        rw [hc, pow_mul, hζ'1, one_pow]
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hζ'n
      have hσ' : σ ζ' = ζ' ^ a := by
        rw [← hj, map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]
      have hne : ζ' ≠ 0 := by
        rintro rfl
        rw [zero_pow (pow_ne_zero N hp.ne_zero)] at hζ'1
        exact zero_ne_one hζ'1
      have ha' : (a : ℤ) = 1 + ((p ^ N : ℕ) : ℤ) * d := by push_cast; linarith
      rw [hσ', ← zpow_natCast, ha', zpow_add₀ hne, zpow_one, zpow_mul, zpow_natCast, hζ'1,
        one_zpow, mul_one]
    have hb : (((a : ℤ) - 1 : ℤ) : ZMod (p ^ n)) * φ.1 m = 0 := by
      push_cast
      rw [sub_mul, one_mul, hfixm, sub_self]
    exact pow_mul_eq_zero_of_mul hp hnd hb

  have hTcard : Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ≤ p ^ N := by
    have key : ∀ z : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0},
        z.1.val = p ^ (n - N) * (z.1.val / p ^ (n - N)) ∧ z.1.val / p ^ (n - N) < p ^ N := by
      intro z
      have hlt : z.1.val < p ^ (n - N) * p ^ N := by
        calc z.1.val < p ^ n := ZMod.val_lt _
          _ ≤ p ^ (n - N + N) := Nat.pow_le_pow_right hp.pos (by omega)
          _ = _ := pow_add _ _ _
      have hdvd : p ^ (n - N) ∣ z.1.val := by
        by_cases hnN : n ≤ N
        · rw [Nat.sub_eq_zero_of_le hnN, pow_zero]; exact one_dvd _
        · push Not at hnN
          have h1 : ((p ^ N * z.1.val : ℕ) : ZMod (p ^ n)) = 0 := by
            rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact z.2
          rw [ZMod.natCast_eq_zero_iff] at h1
          have h2 : p ^ n = p ^ N * p ^ (n - N) := by rw [← pow_add]; congr 1; omega
          have h1' : p ^ N * p ^ (n - N) ∣ p ^ N * z.1.val := by rw [← h2]; exact h1
          exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos N) h1'
      exact ⟨(Nat.mul_div_cancel' hdvd).symm, Nat.div_lt_of_lt_mul hlt⟩
    have hinj : Function.Injective
        (fun z : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} => ((z.1.val / p ^ (n - N) : ℕ) : ZMod (p ^ N))) := by
      intro z w hzw
      have hz := key z
      have hw := key w
      have hv := congrArg ZMod.val hzw
      simp only [ZMod.val_cast_of_lt hz.2, ZMod.val_cast_of_lt hw.2] at hv
      apply Subtype.ext
      apply ZMod.val_injective
      rw [hz.1, hw.1, hv]
    have : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
    calc _ ≤ Nat.card (ZMod (p ^ N)) := Nat.card_le_card_of_injective _ hinj
      _ = p ^ N := Nat.card_zmod _

  have hval : ∀ (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (t : O),
      φ.1 (t • x₀) = φ.1 ((Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out • x₀) := by
    intro φ t
    have hmem : (Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out - t ∈
        Ideal.span {(p : O) ^ N} :=
      Ideal.Quotient.eq.mp (by rw [Ideal.Quotient.mk_out])
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
    have hout : (Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out = t + ((p ^ N : ℕ) : O) * s := by
      rw [Nat.cast_pow]; linear_combination -hs
    rw [hout, add_smul, mul_smul, Nat.cast_smul_eq_nsmul, td_add, td_nsmul, nsmul_eq_mul,
      hkill φ, add_zero]
  have hΦ : Function.Injective (fun (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (q : O ⧸ Ideal.span {(p : O) ^ N}) =>
      (⟨φ.1 (q.out • x₀), hkill φ _⟩ : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0})) := by
    intro φ ψ hφψ
    apply Subtype.ext
    refine DFunLike.ext _ _ fun m => ?_
    obtain ⟨t, rfl⟩ := hx₀ m
    rw [hval φ t, hval ψ t]
    exact congrArg Subtype.val (congrFun hφψ (Ideal.Quotient.mk _ t))
  have hfinH0 : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Finite.of_injective _ hΦ
  have hH0card : Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) ≤ (p ^ N) ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N}) := by
    calc _ ≤ Nat.card (O ⧸ Ideal.span {(p : O) ^ N} → {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0}) :=
          Nat.card_le_card_of_injective _ hΦ
      _ = Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N}) := Nat.card_fun
      _ ≤ _ := Nat.pow_le_pow_left hTcard _

  have hsmul0 : ∀ φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))), ((p ^ N : ℕ) : ZMod (p ^ n)) • φ = 0 := by
    intro φ
    apply Subtype.ext
    refine DFunLike.ext _ _ fun m => ?_
    rw [Submodule.coe_smul, TDual.smul_apply, hkill φ m]
    rfl
  have hΨ : Function.Injective (fun (x : H2 ((levRepZ p n h ρ).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))))
      (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) =>
      (⟨e (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) x φ), by
        have h0 := congrArg e (congrArg
          (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) x) (hsmul0 φ))
        rw [LinearMap.map_smul, LinearEquiv.map_smul, LinearMap.map_zero, LinearEquiv.map_zero,
          smul_eq_mul] at h0
        exact h0⟩ : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0})) := by
    intro x y hxy
    apply hcup.1
    apply LinearMap.ext
    intro φ
    apply e.injective
    exact congrArg Subtype.val (congrFun hxy φ)
  calc Nat.card (H2 (levRepZ p n h ρ))
      = Nat.card (H2 ((levRepZ p n h ρ).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := rfl
    _ ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))) → {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0}) := Nat.card_le_card_of_injective _ hΨ
    _ = Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ^ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Nat.card_fun
    _ ≤ (p ^ N) ^ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Nat.pow_le_pow_left hTcard _
    _ ≤ _ := Nat.pow_le_pow_right (pow_pos hp.pos N) hH0card

end GlobalTheory.UnramifiedH2Bound
end
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem finite_of_finite_quotient_submodule {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) [Finite (N ⧸ S)] [Finite S] : Finite N := by
  classical
  let s := Function.surjInv (Submodule.Quotient.mk_surjective S)
  have hs : ∀ x : N, x - s (Submodule.Quotient.mk x) ∈ S := fun x =>
    (Submodule.Quotient.eq S).1 (Function.surjInv_eq (Submodule.Quotient.mk_surjective S) _).symm
  refine Finite.of_injective (fun x : N => ((Submodule.Quotient.mk x : N ⧸ S), (⟨_, hs x⟩ : S))) ?_
  intro x y h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  simpa using h2

theorem finite_cocycles_of_finite_h1 {R : Type*} [CommRing R] {H : Type*} [Group H] [TopologicalSpace H]
    {Q : Type*} [AddCommGroup Q] [Module R Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q]
    [ContinuousConstSMul R Q] [Finite Q] (σ : Representation R H Q) [Finite (H1 σ)] :
    Finite (Z1 σ) := by
  haveI : Finite ((B1 σ).comap (Z1 σ).subtype) := by
    haveI : Finite (B1 σ) := by
      haveI : Finite (Set.range (d0 σ)) := Set.finite_range _
      exact Finite.of_injective (fun x : B1 σ => (⟨x.1, x.2⟩ : Set.range (d0 σ)))
        (fun x y h => Subtype.ext (congrArg Subtype.val h))
    exact Finite.of_injective (fun x : (B1 σ).comap (Z1 σ).subtype => (⟨x.1.1, x.2⟩ : B1 σ))
      (fun x y h => by
        apply Subtype.ext; apply Subtype.ext
        have := congrArg Subtype.val h
        simpa using this)
  exact finite_of_finite_quotient_submodule ((B1 σ).comap (Z1 σ).subtype)

end GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.LocDualInt

def toZModRep {R H Q : Type*} [CommRing R] [Group H] [AddCommGroup Q] [Module R Q] (m : ℕ)
    [Module (ZMod m) Q] (τ : Representation R H Q) : Representation (ZMod m) H Q where
  toFun h := (τ h).toAddMonoidHom.toZModLinearMap m
  map_one' := LinearMap.ext fun x => by simp
  map_mul' g h := LinearMap.ext fun x => by simp [Module.End.mul_apply]

section Transport

variable {R G H Q : Type*} [CommRing R] [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] [AddCommGroup Q] [Module R Q] [TopologicalSpace Q]
  [IsTopologicalAddGroup Q] [ContinuousConstSMul R Q] (m : ℕ) [Module (ZMod m) Q]
  [ContinuousConstSMul (ZMod m) Q]

theorem contAction_toZModRep (τ : Representation R H Q) (hτ : ContAction τ) :
    ContAction (toZModRep m τ) := hτ

theorem cocycles_subset_image_toZModRestriction (i : G ≃ₜ* H) (τ : Representation R G Q) :
    (Z1 τ : Set (G → Q)) ⊆
      (fun f : H → Q => f ∘ i) '' (Z1 (toZModRep m (τ.comp i.symm.toMonoidHom)) : Set (H → Q)) := by
  intro f hf
  refine ⟨f ∘ i.symm, ⟨hf.1.comp i.symm.continuous, fun g h => ?_⟩, ?_⟩
  · show f (i.symm (g * h)) = f (i.symm g) + τ (i.symm g) (f (i.symm h))
    rw [map_mul, hf.2]
  · funext x
    simp

end Transport

end GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.LocDualInt

theorem finite_cocycles_quotient_pow_smul_module : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [CompactSpace M], FiniteDimensional ℚ_[p] K → (p : O) ∈ IsLocalRing.maximalIdeal O → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (ρ : Representation O G M), ContAction ρ → ∀ ϖ : O, Irreducible ϖ → (∀ n : ℕ, IsOpen ((powSub (M := M) ϖ n : Submodule O M) : Set M)) → ∀ n : ℕ, (Z1 (quotRep ρ ϖ n) : Set (G → M ⧸ powSub (M := M) ϖ n)).Finite := by
  intro hT p _ K O _ _ _ G _ _ M _ _ _ _ _ _ hK hp i ρ hρ ϖ hϖ hopen n
  have hmk := Submodule.isOpenQuotientMap_mkQ (powSub (M := M) ϖ n)
  haveI hdisc : DiscreteTopology (M ⧸ powSub (M := M) ϖ n) := by
    rw [discreteTopology_iff_isOpen_singleton_zero, ← hmk.isQuotientMap.isOpen_preimage]
    convert hopen n using 1
    ext x
    simp [Submodule.Quotient.mk_eq_zero]
  haveI : CompactSpace (M ⧸ powSub (M := M) ϖ n) :=
    ⟨by simpa [hmk.surjective.range_eq] using isCompact_univ.image hmk.continuous⟩
  haveI : Finite (M ⧸ powSub (M := M) ϖ n) := finite_of_compact_of_discrete
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (M ⧸ powSub (M := M) ϖ 0) := by
      refine ⟨fun a b => ?_⟩
      induction a using Submodule.Quotient.induction_on with | _ x => ?_
      induction b using Submodule.Quotient.induction_on with | _ y => ?_
      rw [Submodule.Quotient.eq]
      exact mem_powSub.2 ⟨x - y, by simp⟩
    exact Set.Subsingleton.finite fun f _ g _ => Subsingleton.elim f g
  obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton'.1 (hϖ.maximalIdeal_eq ▸ hp))
  have kill : ∀ x : M ⧸ powSub (M := M) ϖ n, (p ^ n) • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with | _ y => ?_
    rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    push_cast
    rw [← ha, mul_pow, mul_comm, mul_smul]
    exact smul_mem_powSub ϖ n _
  letI : Module (ZMod (p ^ n)) (M ⧸ powSub (M := M) ϖ n) := AddCommGroup.zmodModule kill
  haveI : ContinuousConstSMul (ZMod (p ^ n)) (M ⧸ powSub (M := M) ϖ n) :=
    ⟨fun _ => continuous_of_discreteTopology⟩
  have hcont : ContAction ((quotRep ρ ϖ n).comp i.symm.toMonoidHom) := by
    refine continuous_prod_of_discrete_right.2 fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    show Continuous fun g => quotRep ρ ϖ n (i.symm g) (Submodule.Quotient.mk x)
    simp only [quotRep_mk]
    exact hmk.continuous.comp (hρ.comp (i.symm.continuous.prodMk continuous_const))
  haveI := (GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK n (M ⧸ powSub (M := M) ϖ n)
    (toZModRep (p ^ n) ((quotRep ρ ϖ n).comp i.symm.toMonoidHom)) hn
    (contAction_toZModRep _ _ hcont)).1
  haveI := finite_cocycles_of_finite_h1 (toZModRep (p ^ n) ((quotRep ρ ϖ n).comp i.symm.toMonoidHom))
  exact ((Set.toFinite _).image _).subset (cocycles_subset_image_toZModRestriction (p ^ n) i (quotRep ρ ϖ n))

end GlobalTheory.LocDualInt
end
end
end
end

section

open ReciprocityTheory.Gal

namespace GlobalTheory

theorem modpi_cocycles_finite_classes : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [CompactSpace M] {G : Type} [Group G] [TopologicalSpace G] (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (ρ : Representation O G M), ContAction ρ → ∀ (ϖ : O), (p : O) ∈ Ideal.span {ϖ} → IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) → ∃ s : Finset (Z1 ρ), ∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈ LinearMap.range (LinearMap.lsmul O M ϖ) := by
  classical
  intro hT p _ K hK O _ M _ _ _ _ _ _ G _ _ e ρ hρ ϖ hp hN
  set N : Submodule O M := LinearMap.range (LinearMap.lsmul O M ϖ) with hNdef
  have hmemN : ∀ m : M, ϖ • m ∈ N := fun m => ⟨m, rfl⟩
  have hstab : ∀ g : G, N ≤ N.comap (ρ g) := by
    rintro g _ ⟨m, rfl⟩
    show ρ g (ϖ • m) ∈ N
    rw [map_smul]; exact hmemN _
  haveI hdisc : DiscreteTopology (M ⧸ N) :=
    QuotientAddGroup.discreteTopology (N := N.toAddSubgroup) hN
  haveI : CompactSpace (M ⧸ N) :=
    (Submodule.Quotient.mk_surjective N).compactSpace (Submodule.isOpenQuotientMap_mkQ N).continuous
  haveI : Finite (M ⧸ N) := finite_of_compact_of_discrete
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
  obtain ⟨k, hk1⟩ : ∃ k : ℕ, k = 1 := ⟨1, rfl⟩
  have hkill : ∀ q : M ⧸ N, (p ^ k : ℕ) • q = 0 := by
    intro q
    subst hk1
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [pow_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have : (p • m : M) = ϖ • (r • m) := by
      rw [← Nat.cast_smul_eq_nsmul O, ← hr, smul_smul, mul_comm]
    rw [this]; exact hmemN _
  haveI : Module (ZMod (p ^ k)) (M ⧸ N) := AddCommGroup.zmodModule (n := p ^ k) hkill
  haveI : ContinuousConstSMul (ZMod (p ^ k)) (M ⧸ N) := ⟨fun _ => continuous_of_discreteTopology⟩
  let f : Formalism.GaloisCohomology.GK p K → Module.End (ZMod (p ^ k)) (M ⧸ N) := fun h =>
    (N.mapQ N (ρ (e.symm h)) (hstab _)).toAddMonoidHom.toZModLinearMap (p ^ k)
  have hf1 : f 1 = 1 := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    simp
  have hfm : ∀ a b, f (a * b) = f a * f b := by
    intro a b; refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    simp
  let ρ' : Representation (ZMod (p ^ k)) (Formalism.GaloisCohomology.GK p K) (M ⧸ N) := MonoidHom.mk (OneHom.mk f hf1) hfm
  have hρ'mk : ∀ h m, ρ' h (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρ (e.symm h) m) := fun h m => rfl
  have hρ' : ContAction ρ' := by
    have hq : Topology.IsQuotientMap (Prod.map (id : Formalism.GaloisCohomology.GK p K → Formalism.GaloisCohomology.GK p K) (N.mkQ)) :=
      (IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ N)).isQuotientMap
    show Continuous _
    rw [hq.continuous_iff]
    have : ((fun x : Formalism.GaloisCohomology.GK p K × (M ⧸ N) => ρ' x.1 x.2) ∘ Prod.map id N.mkQ)
        = fun x => Submodule.Quotient.mk (p := N) (ρ (e.symm x.1) x.2) := by
      funext x; rfl
    rw [this]
    exact (Submodule.isOpenQuotientMap_mkQ N).continuous.comp
      (hρ.comp ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))
  have hfin := (GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK k (M ⧸ N) ρ' (by omega) hρ').1
  let cb : Z1 ρ → (Formalism.GaloisCohomology.GK p K → M ⧸ N) := fun c h => Submodule.Quotient.mk ((c : G → M) (e.symm h))
  have hcb : ∀ c, cb c ∈ Z1 ρ' := by
    intro c
    refine ⟨(Submodule.isOpenQuotientMap_mkQ N).continuous.comp (c.2.1.comp e.symm.continuous), ?_⟩
    intro a b
    simp only [cb, map_mul, c.2.2, Submodule.Quotient.mk_add, hρ'mk]
  let κ : Z1 ρ → H1 ρ' := fun c => Submodule.Quotient.mk ⟨cb c, hcb c⟩
  haveI := Fintype.ofFinite (H1 ρ')
  let pick : H1 ρ' → Z1 ρ := fun y => if hy : ∃ c, κ c = y then hy.choose else 0
  refine ⟨Finset.univ.image pick, fun c => ?_⟩
  have hex : ∃ c', κ c' = κ c := ⟨c, rfl⟩
  have hpick : pick (κ c) = hex.choose := dif_pos hex
  refine ⟨pick (κ c), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  set c₀ := pick (κ c)
  have heq : κ c₀ = κ c := by rw [hpick]; exact hex.choose_spec
  have hB := (Submodule.Quotient.eq _).mp heq.symm
  rw [Submodule.mem_comap] at hB
  obtain ⟨q, hq⟩ := (mem_coboundaries1 ρ' _).mp hB
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
  refine ⟨x, fun g => ?_⟩
  have := hq (e g)
  simp only [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply, cb, hρ'mk,
    MulEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply] at this
  rw [← Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.Quotient.mk_sub]
  rw [this]; abel

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.periodCyclotomicChar_reduces_mod_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (r : ℕ) (g : ↥(GK K)), ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧ (PadicInt.toZModPow r u : ZMod (l ^ r)) = ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) := by
  first | exact @GlobalTheory.CycLevel.chi_reduces | exact GlobalTheory.CycLevel.chi_reduces | (intros; apply GlobalTheory.CycLevel.chi_reduces <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

theorem _root_.GlobalTheory.T.normalizedLength_latticeQuotient_baseChange_eq : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → (l : 𝓞 K) ∈ w.asIdeal → (∀ a : 𝓞 K, ∀ z : O, algebraMap O (FractionRing O) z = e (a : K) → (a ∈ w.asIdeal ↔ ¬ IsUnit z)) → ∀ (A B : Submodule (𝓞 K) V), A.FG → B ≤ A → lenUnit (O := O) l (↥(Submodule.span O (iV '' (A : Set V))) ⧸ (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) = Formalism.L2.Col.lenUW w A B := by
  first | exact @GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW | exact GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW | (intros; apply GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW <;> assumption)
end

section

open Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.isSemisimpleRep_of_isSemisimpleRing_range : ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k), IsSemisimpleRing ρ.range → IsSSRep ((ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits) := by
  first | exact @GlobalTheory.isSSRep_of_isSemisimpleRing_range | exact GlobalTheory.isSSRep_of_isSemisimpleRing_range | (intros; apply GlobalTheory.isSSRep_of_isSemisimpleRing_range <;> assumption)
end
