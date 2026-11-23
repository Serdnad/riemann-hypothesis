module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle060
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle005
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle057
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle058
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042

@[expose] public section

section

open scoped Matrix

theorem _root_.GlobalTheory.T.frobenius_strictLower_comparison_near_identity : ∀ (r : ℕ) (g n b B W H : Matrix (Fin r) (Fin r) ℂ) (δ : ℝ), 0 ≤ δ → (r : ℝ) * δ ≤ 1 / 100 → (∀ a c : Fin r, a < c → n a c = 0) → (∀ a : Fin r, n a a = 1) → (∀ a c : Fin r, c < a → ‖n a c‖ ≤ δ) → (∀ a c : Fin r, c < a → b a c = 0) → (∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ) → (∀ a c : Fin r, a < c → ‖b a c‖ ≤ 6 * δ) → (∀ a c : Fin r, c < a → B a c = 0) → (∀ a c : Fin r, a ≤ c → W a c = 0) → (∀ a c : Fin r, a ≤ c → H a c = 0) → g * n = b → g * W = H * b + B → ∑ a, ∑ c, ‖W a c‖ ^ 2 ≤ 2 * ∑ a, ∑ c, ‖H a c‖ ^ 2 := by
  first | exact @GlobalTheory.frobenius_lower_comparison | exact GlobalTheory.frobenius_lower_comparison | (intros; apply GlobalTheory.frobenius_lower_comparison <;> assumption)
end

section

open Topology Filter

theorem _root_.GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s) := by
  first | exact @GlobalTheory.span_finiteDimensional_of_bounded_forms | exact GlobalTheory.span_finiteDimensional_of_bounded_forms | (intros; apply GlobalTheory.span_finiteDimensional_of_bounded_forms <;> assumption)
end

section


theorem _root_.GlobalTheory.T.det_near_one_matrix_norm_bounds : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ), (∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ε) → (n : ℝ) * ε ≤ 1 / 2 → (1 / 2 : ℝ) ^ n ≤ ‖A.det‖ ∧ ‖A.det‖ ≤ 2 ^ n := by
  first | exact @GlobalTheory.det_near_one_bounds | exact GlobalTheory.det_near_one_bounds | (intros; apply GlobalTheory.det_near_one_bounds <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.hermitian_similitude_entry_sq_bound : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ), P.IsHermitian → (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) → ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * P * Y = (s : ℂ) • P → ∀ i j, ‖Y i j‖ ^ 2 ≤ K * s := by
  first | (exact @GlobalTheory.herm_scale_entry_bound) | (exact GlobalTheory.herm_scale_entry_bound) | (intros; apply GlobalTheory.herm_scale_entry_bound  <;> assumption)
end

section

open scoped Matrix

namespace GlobalTheory.UnitaryMinor

theorem sum_norm_sq_col {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i, ‖u.1 i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 u.2) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ i, ‖u.1 i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  exact_mod_cast h2

theorem norm_det_submatrix_le_one (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ)
    (I J : Fin s → Fin n) : ‖(u.1.submatrix I J).det‖ ≤ 1 := by
  by_cases hI : Function.Injective I
  · have h : ‖(u.1.submatrix I J).det‖ ^ 2 ≤ 1 := by
      refine (GlobalTheory.Hadamard.norm_det_sq_le_prod_col (u.1.submatrix I J)).trans ?_
      refine Finset.prod_le_one₀ (fun j _ => Finset.sum_nonneg fun _ _ => by positivity)
        fun j _ => ?_
      rw [← sum_norm_sq_col u (J j)]
      simp only [Matrix.submatrix_apply]
      rw [← Finset.sum_image (s := Finset.univ) (g := I) (f := fun i => ‖u.1 i (J j)‖ ^ 2)
        (fun a _ b _ h => hI h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => by positivity
    exact (sq_le_one_iff₀ (norm_nonneg _)).1 h
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hI
    rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hab])]
    simp

theorem unitary_minor_and_hadamard :
    (∀ (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : Fin s → Fin n),
      ‖(u.1.submatrix I J).det‖ ≤ 1) ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ),
      ‖M.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖M i j‖ ^ 2 :=
  ⟨norm_det_submatrix_le_one, fun _ _ _ M => GlobalTheory.Hadamard.norm_det_sq_le_prod_col M⟩

end GlobalTheory.UnitaryMinor
end

section

open NumberField IsDedekindDomain Filter

theorem _root_.GlobalTheory.T.finite_of_bounded_embeddings_and_valuations : ∀ (K : Type) [Field K] [NumberField K] (A : Set K) (R : ℝ), (∀ x ∈ A, ∀ τ : K →+* ℂ, ‖τ x‖ ≤ R) → (∀ w : HeightOneSpectrum (𝓞 K), ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ A, w.valuation K x ≤ B) → (∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ x ∈ A, w.valuation K x ≤ 1) → A.Finite := by
  first | exact @GlobalTheory.BddFinite.finite_of_bdd | exact GlobalTheory.BddFinite.finite_of_bdd | (intros; apply GlobalTheory.BddFinite.finite_of_bdd <;> assumption)
end

section

open NumberField IsDedekindDomain Filter

theorem _root_.GlobalTheory.T.finite_of_valuation_bounded_norm_le_one : ∀ (E : Type) [Field E] [NumberField E] (X : Set E), (∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N) → (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1) → (∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1) → X.Finite := by
  first | exact @GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one | exact GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one | (intros; apply GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.finite_monic_of_roots_bdd_of_mul_isIntegral : ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ) (B : ℝ), 0 < N →
    {P : Polynomial F | P.Monic ∧ P.natDegree = n ∧ ∀ φ : F →+* ℂ, ∀ w ∈ (P.map φ).roots,
      ‖w‖ ≤ B ∧ IsIntegral ℤ ((N : ℂ) * w)}.Finite := by
  first | (exact @GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (exact GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (intros; apply GlobalTheory.finite_monic_roots_bdd_mul_isIntegral <;> assumption)
end

section

namespace GlobalTheory


open Polynomial in
theorem cauchy_roots_bound : ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), B.card = n → 1 ≤ M →
    (∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ M) →
    ∀ b ∈ B, ‖(b : ℂ)‖ ≤ n * M := by
  first
  | exact @_root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm
  | exact _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm
  | (apply _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> assumption)
  | (intros; apply _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm ..)

end GlobalTheory
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder MatrixOrder

namespace GlobalTheory


open scoped MatrixOrder in
theorem cartanInvolution_conj_of_posDef (ι : Type) [Fintype ι] [DecidableEq ι]
    (s s' : Matrix ι ι ℂ) (hs : sᴴ = s) (hss : s * s = 1) (hs's' : s' * s' = 1)
    (hM : (s * s').PosDef) :
    ∃ a : Matrix ι ι ℂ, aᴴ * s * a = s ∧ a * s = s' * a := by
  set M := s * s' with hMdef
  have hMpsd : M.PosSemidef := hM.posSemidef
  have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hMpsd
  set R := CFC.sqrt M with hRdef
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg M
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hR0
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM0
  have hRh : Rᴴ = R := hRpsd.isHermitian
  have hsM : s * M = s' := by rw [hMdef, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  have hMinv : M⁻¹ = s * M * s := by
    apply Matrix.inv_eq_left_inv
    calc s * M * s * M = (s * M) * (s * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hsM, hs's']
  have hsRs : CFC.sqrt M⁻¹ = s * R * s := by
    refine CFC.sqrt_unique ?_ ?_
    · calc s * R * s * (s * R * s) = s * (R * R) * s := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc s s, hss, Matrix.one_mul]
        _ = M⁻¹ := by rw [hRR, hMinv]
    · have h := hRpsd.conjTranspose_mul_mul_same s
      rw [hs] at h
      exact Matrix.nonneg_iff_posSemidef.mpr h
  have hRinv : R⁻¹ = s * R * s := by
    rw [← hsRs]
    exact hMpsd.inv_sqrt
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hRu : IsUnit R.det := by
    rw [← hRR, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_left hMu
  have hsRinv : s * R⁻¹ = R * s := by
    rw [hRinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  refine ⟨R⁻¹, ?_, ?_⟩
  · rw [Matrix.conjTranspose_nonsing_inv, hRh, Matrix.mul_assoc, hsRinv, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]
  · calc R⁻¹ * s = s * R := by rw [hRinv, Matrix.mul_assoc, hss, Matrix.mul_one]
      _ = s * M * R⁻¹ := by
        rw [← hRR, Matrix.mul_assoc s, Matrix.mul_assoc R, Matrix.mul_nonsing_inv _ hRu,
          Matrix.mul_one]
      _ = s' * R⁻¹ := by rw [hsM]

end GlobalTheory
end

section

open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_unipotent_unitary_shift_making_complement_orthogonal : ∀ (n a b : ℕ) (J Q : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → Q.PosDef →
    ∀ (X₁ Y₁ : Matrix (Fin n) (Fin a) ℂ) (Xb Yb : Matrix (Fin n) (Fin b) ℂ),
      X₁.conjTranspose * J * X₁ = 0 → X₁.conjTranspose * J * Xb = 0 → Xb.conjTranspose * J * Xb = 0 →
      X₁.conjTranspose * J * Y₁ = 1 → X₁.conjTranspose * J * Yb = 0 → Yb.conjTranspose * J * Yb = 0 →
      Xb.conjTranspose * J * Yb = 1 →
    ∃ (u₂ : GL (Fin n) ℂ) (A : Matrix (Fin a) (Fin b) ℂ), (u₂.1).conjTranspose * J * u₂.1 = J ∧
      u₂.1 * X₁ = X₁ ∧ u₂.1 * Xb = Xb + X₁ * A ∧ u₂.1 * Yb = Yb ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₁.conjTranspose * J) v = 0 →
        Matrix.mulVec u₂.1 v = v + Matrix.mulVec X₁ (Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v))) ∧
      X₁.conjTranspose * Q * (Xb + X₁ * A) = 0 := by
  first | exact @GlobalTheory.levi_element_cpx | exact GlobalTheory.levi_element_cpx | (intros; apply GlobalTheory.levi_element_cpx <;> assumption)
end

section

open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hermitian_flag_complement_posDef_factorization : ∀ (n r : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → (J * θ).PosDef →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * Y = 1 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u₁ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
      let Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩
      θ * X₂ = u₁ * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) → X₁.conjTranspose * (J * θ) * (Xb + X₁ * A) = 0 →
      θ * (Xb + X₁ * A) = u₁ * Yb * (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)) ∧
        (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)).PosDef := by
  first | exact @GlobalTheory.schur_complement_step_cpx | exact GlobalTheory.schur_complement_step_cpx | (intros; apply GlobalTheory.schur_complement_step_cpx <;> assumption)
end
