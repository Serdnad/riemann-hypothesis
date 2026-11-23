module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle127
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle128
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle129
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle130
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle005
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.ker_inf_map_le_map_mul_ker_of_flat_target : ∀ (B P A : Type) [CommRing B] [CommRing P] [CommRing A] [Algebra B P] [Algebra B A] [Module.Flat B A] (Ψ : P →ₐ[B] A), Function.Surjective Ψ → ∀ I : Ideal B, RingHom.ker Ψ ⊓ I.map (algebraMap B P) ≤ I.map (algebraMap B P) * RingHom.ker Ψ := by
  first | exact @GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat | exact GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat | (intros; apply GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat <;> assumption)
end

section


theorem _root_.GlobalTheory.T.flat_localization_membership : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D] (Q : Ideal D) [Q.IsPrime] (f b : B), algebraMap B (Localization.AtPrime Q) b ∈ Ideal.span {algebraMap B (Localization.AtPrime Q) f} → ∃ s : B, s ∉ Q.comap (algebraMap B D) ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.localFlat_dvd_descends) | (exact GlobalTheory.localFlat_dvd_descends) | (intros; apply GlobalTheory.localFlat_dvd_descends <;> assumption)
end

section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.exists_linear_splitting_unit_faithfullyFlat : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  first | (exact @GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (exact GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (intros; apply GlobalTheory.unit_splits_of_projective_faithfullyFlat  <;> assumption)
end

section

open scoped TensorProduct

namespace GlobalTheory.SymDesc

variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Algebra R R₁]

theorem injective_quotient (Q : Ideal R₁) (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    Function.Injective (algebraMap R (R₁ ⧸ Q)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  have : r ∈ Q.comap (algebraMap R R₁) := by
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
    exact hr
  rwa [hQ, Ideal.mem_bot] at this

theorem exists_sub_mem_of_under_eq_bot [IsIntegrallyClosed R] [CharZero R]
    [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q : Ideal R₁) [Q.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    ∃ e : R, s - algebraMap R R₁ e ∈ Q := by
  classical
  let A := R₁ ⧸ Q
  let K₀ := FractionRing A
  let F := FractionRing R
  have hRA : Function.Injective (algebraMap R A) := injective_quotient Q hQ
  have hRK : Function.Injective (algebraMap R K₀) := by
    rw [IsScalarTower.algebraMap_eq R A K₀]
    exact (IsFractionRing.injective A K₀).comp hRA
  haveI : FaithfulSMul R K₀ := (faithfulSMul_iff_algebraMap_injective R K₀).2 hRK
  letI : Algebra F K₀ := FractionRing.liftAlgebra R K₀
  haveI : IsScalarTower R F K₀ := FractionRing.isScalarTower_liftAlgebra R K₀
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hRA
  haveI : Algebra.IsAlgebraic R A := Algebra.IsIntegral.isAlgebraic
  haveI : Algebra.IsAlgebraic R K₀ := (IsFractionRing.isAlgebraic_iff' R A K₀).1 inferInstance
  haveI : Algebra.IsAlgebraic F K₀ :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff R F K₀).1 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  let π : R₁ →+* K₀ := (algebraMap A K₀).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ r : R, π (algebraMap R R₁ r) = algebraMap F K₀ (algebraMap R F r) := by
    intro r
    have hq : (Ideal.Quotient.mk Q) ((algebraMap R R₁) r) = algebraMap R A r := by
      first | rfl | exact Ideal.Quotient.mk_algebraMap _ _ | simp [A]
    simp only [π, RingHom.comp_apply]
    rw [hq, ← IsScalarTower.algebraMap_apply R A K₀, ← IsScalarTower.algebraMap_apply R F K₀]
  obtain ⟨e', he'⟩ := GlobalTheory.mem_range_of_forall_algHom_eq F K₀ inferInstance (π s) (by
    intro Ω _ _ φ₁ φ₂
    have h := hs Ω (φ₁.toRingHom.comp π) (φ₂.toRingHom.comp π) (by
      ext r
      simp only [RingHom.comp_apply, hπ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes])
    simpa using h)
  have hint : IsIntegral R (π s) := by
    have h1 : IsIntegral R (Ideal.Quotient.mk Q s) := Algebra.IsIntegral.isIntegral _
    exact h1.map (IsScalarTower.toAlgHom R A K₀)
  rw [← he'] at hint
  have hint' : IsIntegral R e' :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R F K₀) (algebraMap F K₀).injective).1 hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  refine ⟨y, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply IsFractionRing.injective A K₀
  rw [map_zero]
  have h : π (s - algebraMap R R₁ y) = 0 := by
    rw [RingHom.map_sub, hπ, hy, he', sub_self]
  exact h

theorem eq_of_sub_mem [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q Q' : Ideal R₁) [Q.IsPrime] [Q'.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥)
    (hQ' : Q'.comap (algebraMap R R₁) = ⊥) (e e' : R) (he : s - algebraMap R R₁ e ∈ Q)
    (he' : s - algebraMap R R₁ e' ∈ Q') : e = e' := by
  classical
  let F := FractionRing R
  let M := AlgebraicClosure F
  have hRM : Function.Injective (algebraMap R M) := by
    rw [IsScalarTower.algebraMap_eq R F M]
    exact (algebraMap F M).injective.comp (IsFractionRing.injective R F)
  haveI : FaithfulSMul R M := (faithfulSMul_iff_algebraMap_injective R M).2 hRM
  haveI : Module.IsTorsionFree R M := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRM
  have key : ∀ (P : Ideal R₁) [P.IsPrime], P.comap (algebraMap R R₁) = ⊥ →
      ∃ j : R₁ →+* M, j.comp (algebraMap R R₁) = algebraMap R M ∧ ∀ x ∈ P, j x = 0 := by
    intro P _ hP
    have hRA : Function.Injective (algebraMap R (R₁ ⧸ P)) := injective_quotient P hP
    haveI : FaithfulSMul R (R₁ ⧸ P) := (faithfulSMul_iff_algebraMap_injective R _).2 hRA
    haveI : Module.IsTorsionFree R (R₁ ⧸ P) := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRA
    haveI : Algebra.IsAlgebraic R (R₁ ⧸ P) := Algebra.IsIntegral.isAlgebraic
    let l : (R₁ ⧸ P) →ₐ[R] M := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨l.toRingHom.comp (Ideal.Quotient.mk P), ?_, fun x hx => ?_⟩
    · ext r
      simp only [RingHom.comp_apply, Ideal.Quotient.mk_algebraMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgHom.commutes]
    · simp only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  obtain ⟨j, hj, hj0⟩ := key Q hQ
  obtain ⟨j', hj', hj0'⟩ := key Q' hQ'
  have h := hs M j j' (hj.trans hj'.symm)
  have h1 : j s = algebraMap R M e := by
    have := hj0 _ he
    rw [map_sub, sub_eq_zero] at this
    rw [this, ← RingHom.comp_apply, hj]
  have h2 : j' s = algebraMap R M e' := by
    have := hj0' _ he'
    rw [map_sub, sub_eq_zero] at this
    rw [this, ← RingHom.comp_apply, hj']
  exact hRM (h1.symm.trans (h.trans h2))

end GlobalTheory.SymDesc

namespace GlobalTheory

theorem exists_eq_algebraMap_of_forall_ringHom_eq : ∀ (R R₁ : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing R₁] [Algebra R R₁], Module.Finite R R₁ →
    Module.FaithfullyFlat R R₁ → ∀ s : R₁, (∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s) →
    ∃ e : R, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K), i₁ s = i₁ (algebraMap R R₁ e) := by
  intro R R₁ _ _ _ _ _ _ hfin hff s hs
  haveI := hfin
  haveI := hff
  haveI : Algebra.IsIntegral R R₁ := Algebra.IsIntegral.of_finite R R₁
  have hinj : Function.Injective (algebraMap R R₁) := FaithfulSMul.algebraMap_injective R R₁
  have hker : Ideal.comap (algebraMap R R₁) (⊥ : Ideal R₁) ≤ ⊥ := by
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_bot] at hr
    rw [Ideal.mem_bot]
    exact hinj (by rw [hr, map_zero])
  obtain ⟨Q₀, -, hQ₀, hQ₀b⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (⊥ : Ideal R) ⊥ hker
  haveI := hQ₀
  obtain ⟨e, he⟩ := SymDesc.exists_sub_mem_of_under_eq_bot s hs Q₀ hQ₀b
  refine ⟨e, fun K _ i₁ => ?_⟩
  let P := RingHom.ker i₁
  haveI : P.IsPrime := RingHom.ker_isPrime i₁
  haveI : P.LiesOver (P.under R) := ⟨rfl⟩
  obtain ⟨Q, hQP, hQ, hQo⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal R)) (q := P.under R) P bot_le
  have hQb : Q.comap (algebraMap R R₁) = ⊥ := hQo.over.symm
  obtain ⟨e₁, he₁⟩ := SymDesc.exists_sub_mem_of_under_eq_bot s hs Q hQb
  have hee := SymDesc.eq_of_sub_mem s hs Q₀ Q hQ₀b hQb e e₁ he he₁
  subst hee
  have hm : s - algebraMap R R₁ e ∈ P := hQP he₁
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  exact hm

end GlobalTheory
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.isUnit_of_isUnit_mul_comul_eq_tmul : ∀ (K H : Type) [Field K] [CommRing H] [HopfAlgebra K H] (c : H ⊗[K] H), IsUnit c → ∀ u : H, u ≠ 0 → c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u → IsUnit u := by
  first | exact @GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self | exact GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self | (intros; apply GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.derivation_family_cotangent_basis : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra R A] (e : A →+* R), (∀ r, e (algebraMap R A r) = r) → Module.Free R (RingHom.ker e).Cotangent → Module.Finite R (RingHom.ker e).Cotangent → ∀ (n : ℕ) (dv : Fin n → A → R), (∀ a x y, dv a (x + y) = dv a x + dv a y) → (∀ a x y, dv a (x * y) = e x * dv a y + e y * dv a x) → (∀ a r, dv a (algebraMap R A r) = 0) → (∀ D : A → R, (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = e x * D y + e y * D x) → (∀ r, D (algebraMap R A r) = 0) → ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * dv a x) → ∃ z : Fin n → A, (∀ i, e (z i) = 0) ∧ (∀ a i, dv a (z i) = if a = i then 1 else 0) ∧ maximalIdeal A = (maximalIdeal R).map (algebraMap R A) ⊔ Ideal.span (Set.range z) := by
  first | exact @GlobalTheory.CoordsAlg.coords_of_derivation_basis | exact GlobalTheory.CoordsAlg.coords_of_derivation_basis | (intros; apply GlobalTheory.CoordsAlg.coords_of_derivation_basis <;> assumption)
end

section

open scoped BigOperators Matrix ComplexConjugate
open Polynomial

namespace GlobalTheory

theorem integral_of_forall_height_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
      (t : FractionRing R),
      (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → ∃ a b : R, b ∉ p ∧
        t * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) →
      ∃ a : R, algebraMap R (FractionRing R) a = t := by
  intro R _ _ _ _ t h
  exact ReciprocityTheory.ChartRestriction.G.T0.mem_of_mem_heightOne_localizations (K := FractionRing R) t
    (fun p hp h1 => @h p hp h1)

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_unit_eq_mul_of_height_one_avoiding (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n))
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (hπ : ∀ j ∈ J, IsUnit (π j) ∨ Prime (π j))
    (hdiv : ∀ j ∈ J, Prime (π j) → ¬ π j ∣ a ∧ ¬ π j ∣ b)
    (h : ∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) →
      ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ a * d = b * c) :
    ∃ u : Rˣ, a = u * b := by

  have avoid : ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → ∀ x : R, x ≠ 0 → x ∈ Q →
      (∀ j ∈ J, Prime (π j) → ¬ π j ∣ x) → ∀ j ∈ J, π j ∉ Q := by
    intro Q hQ h1 x hx hxQ hnd j hj hjQ
    rcases hπ j hj with hu | hp
    · exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hjQ hu)
    · have hmin := mem_minimalPrimes_span_singleton_of_height_eq_one h1 hp.ne_zero hjQ
      have hsp : (Ideal.span {π j}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
      have hle : Q ≤ Ideal.span {π j} :=
        hmin.2 ⟨hsp, le_refl _⟩ ((Ideal.span_singleton_le_iff_mem Q).mpr hjQ)
      exact hnd j hj hp (Ideal.mem_span_singleton.mp (hle hxQ))
  have hba : b ∣ a := dvd_of_forall_height_eq_one hb fun Q _ h1 hbQ => by
    obtain ⟨c, d, hc, hd, e⟩ :=
      h Q inferInstance h1 (avoid Q h1 b hb hbQ fun j hj hp => (hdiv j hj hp).2)
    exact ⟨d, hd, c, by rw [mul_comm d a, e]⟩
  have hab : a ∣ b := dvd_of_forall_height_eq_one ha fun Q _ h1 haQ => by
    obtain ⟨c, d, hc, hd, e⟩ :=
      h Q inferInstance h1 (avoid Q h1 a ha haQ fun j hj hp => (hdiv j hj hp).1)
    exact ⟨c, hc, d, by rw [mul_comm c b, ← e]⟩
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hba hab
  exact ⟨u, by rw [← hu, mul_comm]⟩

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem exists_notMem_dvd_mul_of_algebraMap_dvd {B : Type} [CommRing B] (Q : Ideal B) [Q.IsPrime]
    {a b : B}
    (h : algebraMap B (Localization.AtPrime Q) a ∣ algebraMap B (Localization.AtPrime Q) b) :
    ∃ t ∉ Q, a ∣ t * b := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨⟨z, s⟩, hs⟩ := IsLocalization.surj Q.primeCompl y
  have e : algebraMap B (Localization.AtPrime Q) (b * s) =
      algebraMap B (Localization.AtPrime Q) (a * z) := by
    rw [map_mul, map_mul, hy, mul_assoc, hs]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists Q.primeCompl _).mp e
  refine ⟨c * s, Q.primeCompl.mul_mem c.2 s.2, c * z, ?_⟩
  linear_combination hc

theorem exists_locally_associated_algebraMap_of_height_eq_one (A' B' : Type) [CommRing A']
    [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A' B']
    (𝔭 : Ideal A') (hQ : (𝔭.map (algebraMap A' B')).IsPrime)
    (h1 : (𝔭.map (algebraMap A' B')).height = 1) (c : B') (hc : c ≠ 0) :
    ∃ j : A', (∃ t ∉ 𝔭.map (algebraMap A' B'), c ∣ t * algebraMap A' B' j) ∧
      (∃ t ∉ 𝔭.map (algebraMap A' B'), algebraMap A' B' j ∣ t * c) := by
  have hdvr : IsDiscreteValuationRing (Localization.AtPrime (𝔭.map (algebraMap A' B'))) :=
    isDiscreteValuationRing_of_height_eq_one _ h1 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
    (Localization.AtPrime (𝔭.map (algebraMap A' B')))
  have hm : maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  obtain ⟨p, hp𝔭, hp⟩ : ∃ p ∈ 𝔭, ¬ ϖ ^ 2 ∣
      algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) (algebraMap A' B' p) := by
    by_contra! H
    have hle : maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) ≤
        Ideal.span {ϖ ^ 2} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact H q hq
    have hmem : ϖ ∈ Ideal.span {ϖ ^ 2} := hle (hm ▸ Ideal.mem_span_singleton_self ϖ)
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨r, ?_⟩
    apply mul_left_cancel₀ hϖ.ne_zero
    rw [mul_one]
    linear_combination -hr
  have hxm : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (algebraMap A' B' p) ∈ maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hp𝔭)
  have hx0 : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (algebraMap A' B' p) ≠ 0 := fun h => hp (h ▸ dvd_zero _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hn : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, mul_one] at hu
      exact (mem_maximalIdeal _).mp hxm (hu ▸ u.isUnit)
    · rfl
    · exfalso
      apply hp
      rw [hu]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  subst hn
  have hc0 : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) c ≠ 0 := by
    intro h
    apply hc
    apply IsLocalization.injective (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (𝔭.map (algebraMap A' B')).primeCompl_le_nonZeroDivisors
    rw [h, map_zero]
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  have hass : Associated (algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) c)
      (algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
        (algebraMap A' B' (p ^ m))) := by
    rw [map_pow, map_pow, hu, hv, pow_one, mul_pow]
    exact (associated_unit_mul_left _ _ v.isUnit).trans
      (associated_unit_mul_left _ _ (u.isUnit.pow m)).symm
  exact ⟨p ^ m, exists_notMem_dvd_mul_of_algebraMap_dvd _ hass.dvd,
    exists_notMem_dvd_mul_of_algebraMap_dvd _ hass.symm.dvd⟩

end GlobalTheory
end

section

namespace GlobalTheory.NormalHeightOne

theorem mem_of_forall_height_eq_one : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (z : K),
    (∀ Q : Ideal A, Q.IsPrime → Q.height = 1 → ∃ r c : A, r ∉ Q ∧ algebraMap A K r * z = algebraMap A K c) →
    ∃ c : A, z = algebraMap A K c := by
  intro A K _ _ _ _ _ _ _ z h
  have hz := ((GlobalTheory.normal_domain_height_one.{0, 0, 0} A K).2.1 z).2 (fun p _ hp => by
    obtain ⟨r, c, hr, e⟩ := h p inferInstance hp
    exact (GlobalTheory.mem_primeLocalSubalgebra_iff p z).2 ⟨r, hr, ⟨c, by rw [Algebra.smul_def, e]⟩⟩)
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, hc.symm⟩

end GlobalTheory.NormalHeightOne
end

section


theorem _root_.GlobalTheory.T.nilpotent_approximation_surjective : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (I : Ideal B) (K : Ideal A) (N : ℕ), (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ I.map (algebraMap B A) ⊔ K) → (I ^ N).map (algebraMap B A) ≤ K → ∀ a : A, ∃ b : B, a - algebraMap B A b ∈ K := by
  first | (exact @GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le) | (exact GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le) | (intros; apply GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tensor_basis_criterion : ∀ (A B R S : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] [CommRing S] (κ : R ⊗[A] B →+* S) {r : ℕ} (v : Fin r → B), Function.Bijective (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) ↔ (Function.Surjective κ ∧ LinearIndependent R (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) = ⊤) := by
  first | (exact @GlobalTheory.tensorSum_bijective_iff) | (exact GlobalTheory.tensorSum_bijective_iff) | (intros; apply GlobalTheory.tensorSum_bijective_iff <;> assumption)
end
