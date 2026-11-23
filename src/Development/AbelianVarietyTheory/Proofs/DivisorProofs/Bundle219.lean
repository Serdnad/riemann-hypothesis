module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle094
public import Mathlib.LinearAlgebra.Matrix.Defs
public import ReciprocityTheory.DualLattices.Bundle001
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle098
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle099
public import Mathlib.RingTheory.Ideal.Prime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle097
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub

@[expose] public section

section


theorem _root_.GlobalTheory.T.rightInvariant_GL_of_upperTriangular_rightInvariant : ∀ {k : Type} [Field k] [Infinite k] {m : ℕ} (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k), (∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x) → (∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A) → (∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id → ψ (A * T) = ψ A) → ∀ A B : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → B.det ≠ 0 → ψ (A * B) = ψ A := by
  first | exact @GlobalTheory.rightInv_of_upperTriangular_rightInv | exact GlobalTheory.rightInv_of_upperTriangular_rightInv | (intros; apply GlobalTheory.rightInv_of_upperTriangular_rightInv <;> assumption)
end

section

namespace GlobalTheory.DepthStages

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def rebase (G : LogFGL v d) (X : Matrix (Fin d) (Fin d) C) (γ : Fin d → Fin d → PowerSeries C) :
    Fin d → Fin d → PowerSeries C :=
  fun a => G.sumF fun b => rescaleCurve (X a b) (γ b)

def glue {ι : Type} (lab : Fin d → ι) (S : ι → Finset (Fin d)) (x : ι → Matrix (Fin d) (Fin d) C) :
    Matrix (Fin d) (Fin d) C :=
  Matrix.of fun a b => if a ∈ S (lab a) then x (lab a) a b else if a = b then 1 else 0

end

end GlobalTheory.DepthStages
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_det_ne_zero_of_separating_functionals : ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K), (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) → ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  first | exact @GlobalTheory.exists_det_ne_zero_of_rows_separating | exact GlobalTheory.exists_det_ne_zero_of_rows_separating | (intros; apply GlobalTheory.exists_det_ne_zero_of_rows_separating <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_rank_normal_form_matrix_field : ∀ (k : Type) [Field k] (n : ℕ) (C : Matrix (Fin n) (Fin n) k),
    ∃ (U P : Matrix (Fin n) (Fin n) k) (e : Fin n → k), U.det ≠ 0 ∧ P.det ≠ 0 ∧ (∀ i, e i = 0 ∨ e i = 1) ∧
      U * C * P = Matrix.diagonal e := by
  first | exact @GlobalTheory.rank_normal_form_field | exact GlobalTheory.rank_normal_form_field | (intros; apply GlobalTheory.rank_normal_form_field <;> assumption)
end

section

open Matrix Polynomial

theorem _root_.GlobalTheory.T.gram_det_change_of_basis' : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] (u : ι → Fin n → K) (u' : ι' → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = W → LinearIndependent K u' → Submodule.span K (Set.range u') = W → ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (u' i k) * u' j k).det = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by
  first | exact @GlobalTheory.gram_det_change_of_bases | exact GlobalTheory.gram_det_change_of_bases | (intros; apply GlobalTheory.gram_det_change_of_bases <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_skewHermitian_det_mul_add_ne_zero_of_idempotent : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by
  first | exact @GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero | exact GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero | (intros; apply GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero <;> assumption)
end

section


theorem _root_.GlobalTheory.T.det_block_change_of_basis_via_two_families_implicit : ∀ {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N] {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N),
    (∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) → ∀ (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F),
    (∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) → (∀ k, mu k = ∑ l, A k l • nu l) →
    (∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) →
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  first | exact @GlobalTheory.Div.BlockChangeDet.det_block_change' | exact GlobalTheory.Div.BlockChangeDet.det_block_change' | (intros; apply GlobalTheory.Div.BlockChangeDet.det_block_change' <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_standard_basis_extension_det_ne_zero : ∀ {K : Type} [Field K] {J : Type} [Fintype J] {n : ℕ} (v : J → Fin n → K), LinearIndependent K v → ∃ e : J → Fin n, Function.Injective e ∧ (Matrix.of (Function.extend e v (fun i => Pi.single i (1 : K)))).det ≠ 0 := by
  first | exact @GlobalTheory.extend_linearIndependent_rows_by_standard_basis | exact GlobalTheory.extend_linearIndependent_rows_by_standard_basis | (intros; apply GlobalTheory.extend_linearIndependent_rows_by_standard_basis <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_admissible_lagrangian_transverse_field : ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.lagrangian_transverse_field | exact GlobalTheory.lagrangian_transverse_field | (intros; apply GlobalTheory.lagrangian_transverse_field <;> assumption)
end

section

open Matrix Polynomial

theorem _root_.GlobalTheory.T.gram_det_ne_zero_of_ker_orth' : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A) → (∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0) → (∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) → (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 := by
  first | exact @GlobalTheory.gram_det_ne_zero_of_ker_orth | exact GlobalTheory.gram_det_ne_zero_of_ker_orth | (intros; apply GlobalTheory.gram_det_ne_zero_of_ker_orth <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_integral_unimodular_mul_lowerTriangular_of_det_ne_zero : ∀ (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F] [IsFractionRing V F] (n : ℕ) (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 → ∃ k : Matrix (Fin n) (Fin n) V, IsUnit k.det ∧ ∀ i j, i < j → (k.map (algebraMap V F) * A) i j = 0 := by
  first | exact @GlobalTheory.iwasawa_lowerTriangular_of_det | exact GlobalTheory.iwasawa_lowerTriangular_of_det | (intros; apply GlobalTheory.iwasawa_lowerTriangular_of_det <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_perm_leadingMinors_not_mem : ∀ (R : Type) [CommRing R] (n : ℕ) (T : Matrix (Fin n) (Fin n) R) (p : Ideal R), p.IsPrime → T.det ∉ p → ∃ w : Equiv.Perm (Fin n), ∀ (k : ℕ) (hk : k ≤ n), ((T.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ∉ p := by
  first | exact @GlobalTheory.exists_rowPerm_leadingMinors_not_mem | exact GlobalTheory.exists_rowPerm_leadingMinors_not_mem | (intros; apply GlobalTheory.exists_rowPerm_leadingMinors_not_mem <;> assumption)
end
