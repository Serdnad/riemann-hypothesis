module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle024
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle025
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle027
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle026
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle095
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle100
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

open Matrix Polynomial

theorem _root_.GlobalTheory.T.ker_aeval_orthogonal_range_unitary_selfReciprocal : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K), (γ.map σ)ᵀ * γ = 1 → ∀ (Q : K[X]), C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse → ∀ (x z : Fin n → K), aeval γ Q *ᵥ x = 0 → ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 := by
  first | exact @GlobalTheory.csr_ker_orth_range | exact GlobalTheory.csr_ker_orth_range | (intros; apply GlobalTheory.csr_ker_orth_range <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.hermitian_form_eq_combination_of_selfAdjoint_identity : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    (∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w)) →
    ∀ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ),
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) →
    ∀ z w : Fin g → ℂ, z ⬝ᵥ H₁.mulVec (star w) = (c₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) +
      ∑ i, (c i : ℂ) * (Polynomial.aeval γ (p i) z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (p i) w))) := by
  first | exact @GlobalTheory.herm_form_identity | exact GlobalTheory.herm_form_identity | (intros; apply GlobalTheory.herm_form_identity <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.rational_matrix_identity_transfer_to_complex_map : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ),
    (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tq + ∑ i, c i • ((Polynomial.aeval Tq (p i)) ^ 2 * Tq) →
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) := by
  first | exact @GlobalTheory.matrix_identity_transfer | exact GlobalTheory.matrix_identity_transfer | (intros; apply GlobalTheory.matrix_identity_transfer <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.nsmul_aeval_mem_lattice_of_int_rational_matrix : ∀ (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
    (∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (p : Polynomial ℚ) (D : ℕ), (∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) →
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ := by
  first | exact @GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix | exact GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix | (intros; apply GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_mem_eigencharacters_of_eigenvector : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V)) (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) → (∀ t ∈ T, p t ≠ 0) → ∃ X' : Set (Module.End ℂ V → ℂ), X'.Finite ∧ ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → ∀ (χ' : Module.End ℂ V → ℂ) (u : V), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V))) → u ≠ 0 → (∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), χ' z = χ z := by
  first | exact @GlobalTheory.eigencharacters_finite_of_commuting_annihilated | exact GlobalTheory.eigencharacters_finite_of_commuting_annihilated | (intros; apply GlobalTheory.eigencharacters_finite_of_commuting_annihilated <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.finiteDimensional_span_adjoin_apply_of_annihilating : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (c : ℕ → Module.End ℂ V) (g : ℂ → Module.End ℂ V), (∀ u, g u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) → (∀ u u', Commute (g u) (g u')) → ∀ (w : V) (P : ℂ → Polynomial ℂ), (∀ u, P u ≠ 0) → (∀ u, Polynomial.aeval (g u) (P u) w = 0) → FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w}) := by
  first | exact @GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin | exact GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin | (intros; apply GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finiteDimensional_span_algebra_orbit_of_annihilated : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V)) (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) → (∀ t ∈ T, p t ≠ 0) → ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ≤ ∏ t ∈ T, (p t).natDegree := by
  first | exact @GlobalTheory.killed_span_adjoin_finrank_le | exact GlobalTheory.killed_span_adjoin_finrank_le | (intros; apply GlobalTheory.killed_span_adjoin_finrank_le <;> assumption)
end

section


theorem _root_.GlobalTheory.T.kummer_aeval_valuation_dvr : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)],
    Function.Injective (algebraMap T V) →
    ∀ (γ : V) (ϖ u : T) (k : ℕ), Irreducible ϖ → IsUnit u → IsUnit (k : T) → 0 < k →
    γ ^ k = algebraMap T V u →
    ∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h' := by
  first | (exact @GlobalTheory.kummer_valuation) | (exact GlobalTheory.kummer_valuation) | (intros; apply GlobalTheory.kummer_valuation  <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.noether_normalization_finite_aeval_pow_add : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (t a : A), (Polynomial.aeval (R := k) t).Finite → ∃ M : ℕ, (Polynomial.aeval (R := k) (t ^ M + a)).Finite := by
  first | exact @GlobalTheory.noether_trick | exact GlobalTheory.noether_trick | (intros; apply GlobalTheory.noether_trick <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_inversion_coordinate_localization_polynomial : ∀ (k : Type) [Field k] (P : Polynomial k), P ≠ 0 → ∃ Q : Polynomial k, Q ≠ 0 ∧ ∃ (σ : Localization.Away P →ₐ[k] Localization.Away Q) (τ : Localization.Away Q →ₐ[k] Localization.Away (Polynomial.X * P)), (τ.comp σ).toRingHom.comp (algebraMap (Polynomial k) (Localization.Away P)) = algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) ∧ τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q)) = (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P * IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  first | exact @GlobalTheory.localizationAway_inv_coordinate | exact GlobalTheory.localizationAway_inv_coordinate | (intros; apply GlobalTheory.localizationAway_inv_coordinate <;> assumption)
end

section

open scoped TensorProduct Polynomial

namespace GlobalTheory


open Polynomial in
theorem exists_prime_gt_dvd_eval :
    ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
  first
  | exact @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | (apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval ..)

end GlobalTheory
end

section

noncomputable section

open Polynomial Matrix GlobalTheory.LatOrb IsLocalRing

namespace GlobalTheory.MaxOrder

theorem exists_eq_uniformizer_smul {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {n : ℕ} (P₀ : O[X])
    (hP : IsCoprime P₀ (derivative P₀)) (γ : Matrix (Fin n) (Fin n) K)
    (hγ : γ.charpoly = P₀.map (algebraMap O K)) (π : O) (hπ : Irreducible π)
    (y : Matrix (Fin n) (Fin n) K) (hy : IsIntegral O y) (N : ℕ) (hN : 1 ≤ N) (f : O[X])
    (hf : aeval γ f = π ^ N • y) : ∃ h : O[X], aeval γ f = π • aeval γ h := by
  classical
  obtain ⟨Q, hQm, hQ⟩ := hy
  set m := Q.natDegree with hm
  set u := π ^ N with hu
  let F : O[X] := ∑ i ∈ Finset.range (m + 1), C (Q.coeff i * u ^ (m - i)) * f ^ i
  have hF : aeval γ F = 0 := by
    have h1 : aeval γ F = u ^ m • aeval y Q := by
      rw [aeval_eq_sum_range (p := Q) y, Finset.smul_sum]

      simp only [F, map_sum, map_mul, aeval_C, map_pow, hf]
      refine Finset.sum_congr rfl fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hAlg : ∀ (c : O) (X : Matrix (Fin n) (Fin n) K), algebraMap O _ c * X = c • X :=
        fun c X => (Algebra.smul_def c X).symm
      have hmi : u ^ (m - i) * u ^ i = u ^ m := by rw [← pow_add, Nat.sub_add_cancel him]
      simp only [_root_.smul_pow, ← map_pow, hAlg, smul_mul_assoc, smul_smul]
      congr 1
      linear_combination (Q.coeff i) * hmi
    rw [h1, show aeval y Q = 0 from hQ, smul_zero]
  have hmon : P₀.Monic := monic_of_injective (IsFractionRing.injective O K) (hγ ▸ γ.charpoly_monic)
  have hd : P₀ ∣ F ^ n := by
    have h := GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval γ (F.map (algebraMap O K))
      (by rw [aeval_map_algebraMap]; exact hF)
    rw [hγ, Fintype.card_fin, ← Polynomial.map_pow] at h
    exact (map_dvd_map _ (IsFractionRing.injective O K) hmon).1 h
  let φ := residue O
  have hφπ : φ π = 0 := (residue_eq_zero_iff π).2 ((mem_maximalIdeal _).2 hπ.not_isUnit)
  have hFm : F.map φ = (f.map φ) ^ m := by

    simp only [F, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_mul, map_pow]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, hQm.coeff_natDegree, Nat.sub_self,
      pow_zero, mul_one, map_one, C_1, one_mul]
    intro i hi
    have him : 0 < m - i := Nat.sub_pos_of_lt (Finset.mem_range.1 hi)
    rw [hu, map_pow, hφπ, zero_pow (by omega), C_0, zero_pow him.ne', mul_zero, zero_mul]
  have hsep : (P₀.map φ).Separable := by
    unfold Separable
    rw [derivative_map]
    exact hP.map (mapRingHom φ)
  have hd2 : P₀.map φ ∣ (f.map φ) ^ (m * n + 1) := by
    have h := Polynomial.map_dvd φ hd
    rw [Polynomial.map_pow, hFm, ← pow_mul] at h
    exact h.trans (pow_dvd_pow _ (Nat.le_succ _))
  obtain ⟨qb, hqb⟩ := (hsep.squarefree.dvd_pow_iff_dvd (Nat.succ_ne_zero _)).1 hd2
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective φ (residue_surjective) qb
  have hker : f - P₀ * q ∈ Ideal.span {C π} := by
    have h : f - P₀ * q ∈ RingHom.ker (mapRingHom φ) := by
      rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, hqb, sub_self]
    rwa [Polynomial.ker_mapRingHom, ker_residue, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ,
      Ideal.map_span, Set.image_singleton] at h
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hker
  refine ⟨h, ?_⟩
  have hP0 : aeval γ P₀ = 0 := by
    rw [← aeval_map_algebraMap K, ← hγ, aeval_self_charpoly]
  have hfe : f = P₀ * q + h * C π := by rw [hh]; ring
  rw [hfe, map_add (f := _), map_mul, map_mul, hP0, zero_mul, zero_add, aeval_C, ← Algebra.commutes,
    ← Algebra.smul_def]

theorem isIntegral_aeval_eq_aeval_map : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ p : K[X], IsIntegral O (aeval γ p) → ∃ r : O[X], aeval γ p = aeval γ (r.map (algebraMap O K)) := by
  intro O K _ _ _ _ _ _ n P₀ hP γ hγ p hp
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  simp only [aeval_map_algebraMap]
  have hπK : algebraMap O K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]; exact hπ.ne_zero
  have key : ∀ k : ℕ, ∀ f : O[X], aeval γ f = π ^ k • aeval γ p → ∃ r : O[X], aeval γ p = aeval γ r := by
    intro k
    induction k with
    | zero => intro f hf; exact ⟨f, by rw [hf, pow_zero, one_smul]⟩
    | succ k ih =>
      intro f hf
      obtain ⟨h, hh⟩ := exists_eq_uniformizer_smul P₀ hP γ hγ π hπ _ hp (k + 1) (by omega) f hf
      refine ih h ?_
      have h1 : π • (π ^ k • aeval γ p) = π • aeval γ h := by rw [smul_smul, ← pow_succ', ← hf, hh]
      rw [← algebraMap_smul K π (π ^ k • aeval γ p), ← algebraMap_smul K π (aeval γ h)] at h1
      exact (smul_right_injective _ hπK h1).symm
  obtain ⟨b, hb, hbmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) p
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
  refine key k (C (↑v⁻¹ : O) * IsLocalization.integerNormalization (nonZeroDivisors O) p) ?_
  rw [map_mul, aeval_C, ← aeval_map_algebraMap K γ (IsLocalization.integerNormalization _ p), hbmap,
    ← algebraMap_smul K b p, map_smul, algebraMap_smul, ← Algebra.smul_def, smul_smul, hv,
    ← mul_assoc, Units.inv_mul, one_mul]

end GlobalTheory.MaxOrder
end
end
