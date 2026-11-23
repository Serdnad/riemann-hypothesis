module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle012
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle125
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle127
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
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_maximal_over_closedPoint_closedFibre : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := by
  first | (exact @GlobalTheory.exists_maximal_over_closedPt) | (exact GlobalTheory.exists_maximal_over_closedPt) | (intros; apply GlobalTheory.exists_maximal_over_closedPt  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_finset_awayMap_bijective_of_subalgebra_ge : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (g : Finset B), (∀ b ∈ g, Algebra.FiniteType R (Localization.Away b)) → ∃ s : Finset B, (↑g : Set B) ⊆ ↑s ∧ ∀ C : Subalgebra R B, (↑s : Set B) ⊆ ↑C → ∀ b ∈ g, ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
  first | exact @GlobalTheory.exists_finset_awayMap_subalgebra_bijective | exact GlobalTheory.exists_finset_awayMap_subalgebra_bijective | (intros; apply GlobalTheory.exists_finset_awayMap_subalgebra_bijective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem finite_setOf_ringHom_comp_eq_of_finite : ∀ (A Ω K : Type) [CommRing A] [CommRing Ω] [Field K]
    (φ : A →+* Ω) (ρ : A →+* K), φ.Finite → Set.Finite {τ : Ω →+* K | τ.comp φ = ρ} := by
  intro A Ω K _ _ _ φ ρ hφ
  classical
  letI : Algebra A Ω := φ.toAlgebra
  haveI : Module.Finite A Ω := hφ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := Ω)
  haveI : Algebra.IsIntegral A Ω := Algebra.IsIntegral.of_finite A Ω
  have hint : ∀ g : Ω, ∃ p : Polynomial A, p.Monic ∧ p.eval₂ φ g = 0 := fun g => by
    obtain ⟨q, hq, he⟩ := Algebra.IsIntegral.isIntegral (R := A) g
    exact ⟨q, hq, he⟩
  choose p hpm hpe using hint
  let F : (Ω →+* K) → (s → K) := fun τ g => τ g
  apply Set.Finite.of_finite_image (f := F)
  · refine Set.Finite.subset (Set.Finite.pi (t := fun g : s => (((p g).map ρ).roots.toFinset : Set K))
      (fun _ => Finset.finite_toSet _)) ?_
    rintro _ ⟨τ, hτ, rfl⟩ g _
    have hτ' : τ.comp φ = ρ := hτ
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots ((hpm g).map ρ).ne_zero, Polynomial.IsRoot, Polynomial.eval_map,
      ← hτ', ← Polynomial.hom_eval₂, hpe, map_zero]
  · intro τ₁ h₁ τ₂ h₂ he
    have h₁' : τ₁.comp φ = ρ := h₁
    have h₂' : τ₂.comp φ = ρ := h₂
    ext x
    have hx : x ∈ Submodule.span A (s : Set Ω) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact congrFun he ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy =>
      rw [Algebra.smul_def, map_mul, map_mul, hy]
      congr 1
      exact (RingHom.congr_fun h₁' a).trans (RingHom.congr_fun h₂' a).symm

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_separating_element_ringHom_moduleFinite_int : ∀ (k : Type) [Field k] (C : Type) [CommRing C] [Module.Finite ℤ C] (S : Finset (C →+* k)) (χ₀ : C →+* k), ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  first | (exact @GlobalTheory.ringHom_exists_sep_of_moduleFinite_int) | (exact GlobalTheory.ringHom_exists_sep_of_moduleFinite_int) | (intros; apply GlobalTheory.ringHom_exists_sep_of_moduleFinite_int  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_sublevel_of_int_quadratic_ge_one : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (q : X → ℤ), (∀ a, q (-a) = q a) → (∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b)) → (∀ a, a ≠ 0 → 1 ≤ q a) → ∀ N : ℤ, {a | q a ≤ N}.Finite := by
  first | exact @GlobalTheory.posquad_finite | exact GlobalTheory.posquad_finite | (intros; apply GlobalTheory.posquad_finite <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.le_sup_ker_mul_of_le_sup_maximal_mul_section : ∀ (O P : Type) [CommRing O] [IsLocalRing O] [CommRing P] [Algebra O P] (η : P →ₐ[O] O) (J S : Ideal P), J.FG → J ≤ S ⊔ (IsLocalRing.maximalIdeal O).comap η * J → J ≤ S ⊔ RingHom.ker η * J := by
  first | exact @GlobalTheory.nakayama_at_section | exact GlobalTheory.nakayama_at_section | (intros; apply GlobalTheory.nakayama_at_section <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_nat_mul_mem_range_pi_quotient_minimalPrimes' : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], ∃ n : ℕ, n ≠ 0 ∧ ∀ b' : ((P : minimalPrimes B) → B ⧸ (P : Ideal B)), (n : (P : minimalPrimes B) → B ⧸ (P : Ideal B)) * b' ∈ (Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)).range := by
  first | exact @GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes | exact GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes | (intros; apply GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (N : Submodule R' A'), N.FG → ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by
  first | exact @GlobalTheory.fg_localizationAway_span_finset | exact GlobalTheory.fg_localizationAway_span_finset | (intros; apply GlobalTheory.fg_localizationAway_span_finset <;> assumption)
end

section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finite_of_surjective_semilinear_tensor : ∀ (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (O : Type) [CommRing O] (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], Module.Finite Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → Module.Finite (k ⊗[ℤ] O) N := by
  first | exact @GlobalTheory.finite_of_surjective_tensor_semilinear | exact GlobalTheory.finite_of_surjective_tensor_semilinear | (intros; apply GlobalTheory.finite_of_surjective_tensor_semilinear <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) → (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) → (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by
  first | exact @GlobalTheory.bijective_of_lTensor_flat_family | exact GlobalTheory.bijective_of_lTensor_flat_family | (intros; apply GlobalTheory.bijective_of_lTensor_flat_family <;> assumption)
end

section


theorem _root_.GlobalTheory.T.flat_of_forall_finset_subset_flat_submodule : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], (∀ s : Finset M, ∃ N : Submodule R M, (↑s : Set M) ⊆ ↑N ∧ Module.Flat R ↥N) → Module.Flat R M := by
  first | exact @GlobalTheory.flat_of_forall_finset_subset_flat | exact GlobalTheory.flat_of_forall_finset_subset_flat | (intros; apply GlobalTheory.flat_of_forall_finset_subset_flat <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.flat_tensor_kernel_mem_map_ideal : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [Module.Flat P L] (I : Ideal P),
    RingHom.ker (algebraMap P T) = I → ∀ y : L, (1 : T) ⊗ₜ[P] y = 0 → y ∈ I.map (algebraMap P L) := by
  first | (exact @GlobalTheory.flat_one_tmul_eq_zero_mem_map) | (exact GlobalTheory.flat_one_tmul_eq_zero_mem_map) | (intros; apply GlobalTheory.flat_one_tmul_eq_zero_mem_map  <;> assumption)
end
