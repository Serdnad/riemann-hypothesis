module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle089
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefQuadraticAdjointPairBound
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicUnitMultipleFractionRing
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle092
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle024
public import Mathlib.LinearAlgebra.Matrix.Block
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle094
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_idempotent_lift_adicComplete_free_algebra : ∀ (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Free A Λ] [Module.Finite A Λ] (x : Λ), x * x - x ∈ I • (⊤ : Submodule A Λ) → ∃ e : Λ, IsIdempotentElem e ∧ e - x ∈ I • (⊤ : Submodule A Λ) := by
  first | (exact @GlobalTheory.IdemNewton.exists_idem) | (exact GlobalTheory.IdemNewton.exists_idem) | (intros; apply GlobalTheory.IdemNewton.exists_idem  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_pos_mul_extend_int_linearForm' : ∀ (F : Type) [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ), ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  first | exact @GlobalTheory.exists_pos_mul_extend_int_linearForm | exact GlobalTheory.exists_pos_mul_extend_int_linearForm | (intros; apply GlobalTheory.exists_pos_mul_extend_int_linearForm <;> assumption)
end

section


theorem _root_.GlobalTheory.T.posSemidef_quadratic_adjoint_pair_bound : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h h' : X →+ X), ∃ C : ℕ, ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y := by
  first | exact @GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound | exact GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound | (intros; apply GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_even_cubic_unit_multiple_fractionRing : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (κ₀ : X → (FractionRing R)ˣ), (∀ a, ∃ u : Rˣ, ((κ₀ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R)) → (∀ a a' b, ∃ u : Rˣ, ((κ₀ (a + a' + b) * κ₀ a * κ₀ a' * κ₀ b : (FractionRing R)ˣ) : FractionRing R) = ((κ₀ (a + a') * κ₀ (a + b) * κ₀ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) → ∃ κ : X → (FractionRing R)ˣ, (∀ a, κ (-a) = κ a) ∧ (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) ∧ ∀ a, ∃ u : Rˣ, ((κ a : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R) := by
  first | exact @GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple | exact GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple | (intros; apply GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_isHomogeneous_eval_eq_norm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n d : ℕ) (f : MvPolynomial (Fin n) L), f.IsHomogeneous d → ∃ F : MvPolynomial (Fin n × Fin (Module.finrank K L)) K, F.IsHomogeneous (d * Module.finrank K L) ∧ ∀ y : Fin n × Fin (Module.finrank K L) → K, MvPolynomial.eval y F = Algebra.norm K (MvPolynomial.eval (fun i => ∑ j, algebraMap K L (y (i, j)) * Module.finBasis K L j) f) := by
  first | exact @GlobalTheory.norm_comp_homogeneous_isHomogeneous | exact GlobalTheory.norm_comp_homogeneous_isHomogeneous | (intros; apply GlobalTheory.norm_comp_homogeneous_isHomogeneous <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_dvd_coords_of_definite_parallelogram_form : ∀ (E : Type) [AddCommGroup E] (H : AddSubgroup E) (Q : E → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f ∈ H, Q f = 0 → f = 0) → ∀ (n : ℕ) (u : Fin n → E), (∀ i, u i ∈ H) → LinearIndependent ℤ u → ∃ e : ℕ, 0 < e ∧ ∀ (k : ℕ) (m : Fin n → ℤ) (h : E), h ∈ H → k • h = ∑ i, m i • u i → ∀ i, (k : ℤ) ∣ e * m i := by
  first | exact @GlobalTheory.exists_dvd_coords_of_definite_form | exact GlobalTheory.exists_dvd_coords_of_definite_form | (intros; apply GlobalTheory.exists_dvd_coords_of_definite_form <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_linearIndependent_adapted_to_decreasing_chain' : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ), (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) → (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ), LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧ ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  first | exact @GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain | exact GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain | (intros; apply GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.linearIndependent_of_injective_valuationLike : ∀ (C V Γ ι : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → ∀ f : ι → V, (∀ i, f i ≠ 0) → Function.Injective (fun i => ν (f i)) → LinearIndependent C f := by
  first | exact @GlobalTheory.linearIndependent_of_distinct_valuationLike | exact GlobalTheory.linearIndependent_of_distinct_valuationLike | (intros; apply GlobalTheory.linearIndependent_of_distinct_valuationLike <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.truncatedMonomials_linearIndependent_over_constants : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] (d : ℕ) (x : Fin d → A) (E : Fin d → Derivation k A A), (∀ i j, E i (x j) = if i = j then 1 else 0) → ∀ B : Subalgebra k A, (∀ i, ∀ b ∈ B, E i b = 0) → LinearIndependent B (fun a : Fin d → Fin p => ∏ i, x i ^ (a i : ℕ)) := by
  first | exact @GlobalTheory.truncMono_linearIndependent | exact GlobalTheory.truncMono_linearIndependent | (intros; apply GlobalTheory.truncMono_linearIndependent <;> assumption)
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R), δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) := by
  first | exact @GlobalTheory.DetDeriv.main | exact GlobalTheory.DetDeriv.main | (intros; apply GlobalTheory.DetDeriv.main <;> assumption)
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.piola_identity_adjugate_divergence_free : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → Derivation K R R) (M : Matrix ι ι R), (∀ h i j, δ h (M i j) = δ i (M h j)) → ∀ j, ∑ i, δ i (M.adjugate j i) = 0 := by
  first | exact @GlobalTheory.PiolaAlg.piola_identity | exact GlobalTheory.PiolaAlg.piola_identity | (intros; apply GlobalTheory.PiolaAlg.piola_identity <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_lu_of_isUnit_leading_minors : ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R), (∀ (k : ℕ) (hk : k ≤ n), IsUnit (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) → ∃ L U : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → L i j = 0) ∧ (∀ i, L i i = 1) ∧ U.BlockTriangular id ∧ (∀ i, IsUnit (U i i)) ∧ M = L * U := by
  first | exact @GlobalTheory.lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors | exact GlobalTheory.lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors | (intros; apply GlobalTheory.lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors <;> assumption)
end
