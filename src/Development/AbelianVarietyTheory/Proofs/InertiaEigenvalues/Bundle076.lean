module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle003
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle011
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle006
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle004
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle007
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

section

namespace GlobalTheory

theorem semilinear_sub_mem_pow_succ_smul {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (n : Ideal A) (γ : A →+* A) (Y : N →+ N) (hY : ∀ a x, Y (a • x) = γ a • Y x)
    (hγ : ∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1))
    (h1 : ∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) (k : ℕ) (x : N)
    (hx : x ∈ n ^ k • (⊤ : Submodule A N)) :
    Y x - x ∈ n ^ (k + 1) • (⊤ : Submodule A N) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    have e : Y (a • y) - a • y = γ a • (Y y - y) + (γ a - a) • y := by
      rw [hY, smul_sub, sub_smul]; abel
    have hga : γ a ∈ n ^ k := by
      have h2 : γ a - a ∈ n ^ k := Ideal.pow_le_pow_right (Nat.le_succ k) (hγ k a ha)
      simpa using (n ^ k).add_mem h2 ha
    rw [e]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem_smul (hγ k a ha) trivial)
    rw [pow_succ, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hga (h1 y)
  · intro y z hy hz
    have e : Y (y + z) - (y + z) = (Y y - y) + (Y z - z) := by
      rw [map_add (f := _)]; abel
    rw [e]
    exact Submodule.add_mem _ hy hz

theorem semilinear_sub_one_pow_mem {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (n : Ideal A) (γ : A →+* A) (Y : N →+ N) (hY : ∀ a x, Y (a • x) = γ a • Y x)
    (hγ : ∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1))
    (h1 : ∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) (k : ℕ) (x : N) :
    ((Y.toIntLinearMap - 1 : Module.End ℤ N) ^ k) x ∈ n ^ k • (⊤ : Submodule A N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' (Y.toIntLinearMap - 1 : Module.End ℤ N), Module.End.mul_apply]
    exact semilinear_sub_mem_pow_succ_smul n γ Y hY hγ h1 k _ ih

theorem semilinear_iterate_prime_pow_sub_mem :
    ∀ (l : ℕ) [Fact l.Prime] (A N : Type) [CommRing A] [AddCommGroup N] [Module A N] (n : Ideal A) (γ : A →+* A) (Y : N →+ N), (∀ a x, Y (a • x) = γ a • Y x) → (∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1)) → (∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) → ∀ b : ℕ, 1 ≤ b → ∀ x, Y^[l ^ b] x - x ∈ (Ideal.span {((l : A)) ^ 2} ⊔ n ^ (l ^ (b - 1))) • (⊤ : Submodule A N) := by
  intro l _ A N _ _ _ n γ Y hY hγ h1 b hb x
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (GlobalTheory.one_add_X_pow_prime_pow_sub_one_mem_span l b hb)
  set D : Module.End ℤ N := Y.toIntLinearMap - 1 with hD
  have h := congrArg (Polynomial.aeval D) huv
  rw [mul_comm u, mul_comm v] at h
  simp only [map_add (f := _), map_mul, map_pow, map_sub, map_one, map_natCast, Polynomial.aeval_X] at h
  have hYD : (1 + D) = Y.toIntLinearMap := by rw [hD]; abel
  rw [hYD] at h
  have h' := congrArg (fun f : Module.End ℤ N => f x) h
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply] at h'
  have e : (Y.toIntLinearMap ^ (l ^ b)) x = Y^[l ^ b] x := by
    rw [Module.End.pow_apply]; rfl
  rw [e] at h'
  rw [← h']
  refine Submodule.add_mem _ ?_ ?_
  · have e2 : ∀ y : N, (((l : Module.End ℤ N)) ^ 2) y = ((l : A) ^ 2) • y := by
      intro y
      rw [← Nat.cast_pow, ← Nat.cast_pow, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    rw [e2]
    exact Submodule.smul_mem_smul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) trivial
  · exact Submodule.smul_mono_left le_sup_right
      (semilinear_sub_one_pow_mem n γ Y hY hγ h1 _ _)

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.cauchy_product_partial_sums_dvd_pow : ∀ {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R), (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p) → (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) → ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) := by
  first | exact @GlobalTheory.cauchy_product_dvd_pow | exact GlobalTheory.cauchy_product_dvd_pow | (intros; apply GlobalTheory.cauchy_product_dvd_pow <;> assumption)
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_least_weight_exponent : ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ, (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) → ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by
  first | exact @GlobalTheory.exists_exponent_strictly_least_weight | exact GlobalTheory.exists_exponent_strictly_least_weight | (intros; apply GlobalTheory.exists_exponent_strictly_least_weight <;> assumption)
end

section

open Filter

theorem _root_.GlobalTheory.T.tendsto_ratio_box_counts_prod_one : ∀ (r : ℕ) (c : Fin r → ℕ) (m : ℕ), Filter.Tendsto (fun k : ℕ => ((∏ i, (2 * (k + m) * c i + 1) : ℕ) : ℝ) / ((∏ i, (2 * k * c i + 1) : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
  first | exact @GlobalTheory.ratio_box_counts_tendsto_one | exact GlobalTheory.ratio_box_counts_tendsto_one | (intros; apply GlobalTheory.ratio_box_counts_tendsto_one <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.ringHom_isPushout_of_pi_components : ∀ {A P A' P' : Type} [CommRing A] [CommRing P] [CommRing A'] [CommRing P'] {n : ℕ}
    {Pi P'i : Fin n → Type} [∀ i, CommRing (Pi i)] [∀ i, CommRing (P'i i)]
    (f : A →+* P) (k : A →+* A') (k' : P →+* P') (h' : A' →+* P')
    (g : ∀ i, P →+* Pi i) (g' : ∀ i, P' →+* P'i i) (kk : ∀ i, Pi i →+* P'i i) (hh : ∀ i, A' →+* P'i i),
    Function.Bijective (fun (x : P) (i : Fin n) => g i x) →
    Function.Bijective (fun (x : P') (i : Fin n) => g' i x) →
    (∀ i, (g' i).comp k' = (kk i).comp (g i)) → (∀ i, (g' i).comp h' = hh i) →
    (∀ i, CategoryTheory.IsPushout (CommRingCat.ofHom ((g i).comp f)) (CommRingCat.ofHom k)
      (CommRingCat.ofHom (kk i)) (CommRingCat.ofHom (hh i))) →
    CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom k) (CommRingCat.ofHom k')
      (CommRingCat.ofHom h') := by
  first | exact @GlobalTheory.isPushout_of_pi_components | exact GlobalTheory.isPushout_of_pi_components | (intros; apply GlobalTheory.isPushout_of_pi_components <;> assumption)
end

section

namespace GlobalTheory

open Polynomial

theorem ringHom_apply_eq_pow_of_pow_pow_eq_self :
    ∀ {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (τ : k →+* k) (N : ℕ), 0 < N →
      ∀ (z : k), z ^ p ^ N = z → ∃ e : ℕ, τ z = z ^ p ^ e := by
  first
  | exact @_root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow
  | exact _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow
  | (apply _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow ..)

end GlobalTheory
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.coeff_aeval_one_add_X_pow_sub_one_ne_zero' : ∀ (k σ : Type) [Field k] [Fintype σ] (l M : ℕ) [Fact l.Prime] [CharP k l] (D u : MvPolynomial σ k) (n e : σ → ℕ), u.coeff 0 ≠ 0 → D - u * ∏ q, MvPolynomial.X q ^ n q ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) → ∑ q, n q * l ^ e q < l ^ M → (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) D).coeff (∑ q, n q * l ^ e q) ≠ 0 := by
  first | exact @GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero | exact GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero | (intros; apply GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.echelon_projector_kernel_frobenius : ∀ (l : ℕ) [Fact l.Prime] (C : Type) [Field C] [CharP C l] (d : ℕ) (Y A : Matrix (Fin d) (Fin d) C), A.det ≠ 0 → Y.map (frobenius C l) = Y * A → ∃ (I : Finset (Fin d)) (Q Λ : Matrix (Fin d) (Fin d) C), Y * Q = 0 ∧ (∀ v, Y.mulVec v = 0 → Q.mulVec v = v) ∧ (∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0) ∧ (∀ i, ∀ j ∉ I, Q i j = 0) ∧ Q = A * Q.map (frobenius C l) * Λ := by
  first | exact @GlobalTheory.echelon_projector_frobenius | exact GlobalTheory.echelon_projector_frobenius | (intros; apply GlobalTheory.echelon_projector_frobenius <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.hodgeTate_operator_of_galois_relations : ∀ {k : Type} [Field k] (d N q : ℕ) (p : Fin d → ℕ) (a b z w : k) (y y' v v₀ e r sy sv : Matrix (Fin d) (Fin d) k), a ≠ 0 → b ≠ 0 → z * w = 1 → y * y' = a ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) k) → y * v₀ = a ^ N • v → a ^ N • (r * sy) = b ^ N • (y * e) → r * sv * Matrix.diagonal (fun j => w ^ p j) = w ^ q • v → sy * v₀ = b ^ N • sv → ∃ u : Matrix (Fin d) (Fin d) k, u * y = y * e ∧ u * v = v * Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
  first | (exact @GlobalTheory.ht_operator_of_galois_relations) | (exact GlobalTheory.ht_operator_of_galois_relations) | (intros; apply GlobalTheory.ht_operator_of_galois_relations  <;> assumption)
end

section

open Matrix

namespace GlobalTheory

theorem invariant_right_inverse_of_right_inverse :
    ∀ (L : Type) [CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type)
      [Fintype N] [DecidableEq N] [Fintype b] [DecidableEq b] (κ : Matrix b N L)
      (Y : Matrix N b L), κ * Y = 1 → (∀ g, κ.map (act g) = κ) →
      ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g, Λ.map (act g) = Λ := by
  first
  | exact @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | (apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse ..)

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_subfield_adjoin_rootsOfUnity_embedding_complex : ∀ {L0 K : Type} [Field L0] [Field K] (s : L0 →+* K) (t : L0 →+* ℂ) (Z : Set K), (∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1) → ∃ (E : Subfield K) (j : E →+* ℂ), (∀ x, s x ∈ E) ∧ Z ⊆ E ∧ ∀ x (hx : s x ∈ E), j ⟨s x, hx⟩ = t x := by
  first | exact @GlobalTheory.adjoin_roots_of_unity_embeds_complex | exact GlobalTheory.adjoin_roots_of_unity_embeds_complex | (intros; apply GlobalTheory.adjoin_roots_of_unity_embeds_complex <;> assumption)
end

section

open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.quotient_equiv_restrictedComponentFamilies : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ), (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → ∃ e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}, ∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v)) := by
  first | exact @GlobalTheory.quotient_equiv_restrictedFamilies | exact GlobalTheory.quotient_equiv_restrictedFamilies | (intros; apply GlobalTheory.quotient_equiv_restrictedFamilies <;> assumption)
end
