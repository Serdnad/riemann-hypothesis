module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

namespace GramSubmodular

variable {m α β γ : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]


end GramSubmodular

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_det_re_nonneg_and_im_eq_zero (X : Matrix m α ℂ) : 0 ≤ (Xᴴ * X).det.re ∧ (Xᴴ * X).det.im = 0 := by
  have h := Complex.le_def.mp (posSemidef_conjTranspose_mul_self X).det_nonneg
  exact ⟨by simpa using h.1, by simpa using h.2.symm⟩

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_fromCols_eq_fromBlocks (X : Matrix m α ℂ) (N : Matrix m n ℂ) :
    (fromCols X N)ᴴ * fromCols X N = fromBlocks (Xᴴ * X) (Xᴴ * N) (Nᴴ * X) (Nᴴ * N) := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_projection_residual_eq [DecidableEq m] (X : Matrix m α ℂ) (N : Matrix m n ℂ)
    (h : (Xᴴ * X).det ≠ 0) :
    ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N)ᴴ * ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N) =
      Nᴴ * N - Nᴴ * X * (Xᴴ * X)⁻¹ * (Xᴴ * N) := by
  have hG : (Xᴴ * X)⁻¹ᴴ = (Xᴴ * X)⁻¹ := by
    rw [conjTranspose_nonsing_inv, conjTranspose_mul, conjTranspose_conjTranspose]
  have hGG : (Xᴴ * X)⁻¹ * (Xᴴ * X) = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)
  have hQ : X * (Xᴴ * X)⁻¹ * Xᴴ * (X * (Xᴴ * X)⁻¹ * Xᴴ) = X * (Xᴴ * X)⁻¹ * Xᴴ := by
    rw [show X * (Xᴴ * X)⁻¹ * Xᴴ * (X * (Xᴴ * X)⁻¹ * Xᴴ) =
      X * ((Xᴴ * X)⁻¹ * (Xᴴ * X)) * (Xᴴ * X)⁻¹ * Xᴴ by simp only [Matrix.mul_assoc], hGG,
      Matrix.mul_one]
  have hP : (1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * (1 - X * (Xᴴ * X)⁻¹ * Xᴴ) =
      1 - X * (Xᴴ * X)⁻¹ * Xᴴ := by
    rw [sub_mul, mul_sub, mul_sub, hQ]
    simp only [Matrix.one_mul, Matrix.mul_one]
    abel
  have hPh : (1 - X * (Xᴴ * X)⁻¹ * Xᴴ)ᴴ = 1 - X * (Xᴴ * X)⁻¹ * Xᴴ := by
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hG, Matrix.mul_assoc]
  rw [conjTranspose_mul, hPh, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ N, hP]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_det_fromCols_eq_mul_residual [DecidableEq m] (X : Matrix m α ℂ) (N : Matrix m n ℂ)
    (h : (Xᴴ * X).det ≠ 0) :
    ((fromCols X N)ᴴ * fromCols X N).det = (Xᴴ * X).det *
      (((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N)ᴴ * ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N)).det := by
  haveI := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr h)
  rw [gram_fromCols_eq_fromBlocks, det_fromBlocks₁₁, invOf_eq_nonsing_inv, gram_projection_residual_eq X N h]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma re_mul_of_im_eq_zero {z w : ℂ} (hz : z.im = 0) : (z * w).re = z.re * w.re := by
  simp [Complex.mul_re, hz]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_det_fromCols_eq_zero_of_gram_det_eq_zero (X : Matrix m α ℂ) (N : Matrix m n ℂ)
    (h : (Xᴴ * X).det = 0) : ((fromCols X N)ᴴ * fromCols X N).det = 0 := by
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr h
  have hXv : X *ᵥ v = 0 := (conjTranspose_mul_self_mulVec_eq_zero X v).mp hv
  refine exists_mulVec_eq_zero_iff.mp ⟨Sum.elim v 0, fun hw => hv0 ?_, ?_⟩
  · funext a
    simpa using congrFun hw (Sum.inl a)
  · rw [conjTranspose_mul_self_mulVec_eq_zero, fromCols_mulVec]
    simp [Function.comp_def, hXv]
    exact N.mulVec_zero

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_det_fromCols_le_mul
    (hmono : ∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0))
    (Y : Matrix m β ℂ) (Z : Matrix m γ ℂ) :
    ((fromCols Y Z)ᴴ * fromCols Y Z).det.re ≤ (Yᴴ * Y).det.re * (Zᴴ * Z).det.re := by
  classical
  by_cases h : (Yᴴ * Y).det = 0
  · rw [gram_det_fromCols_eq_zero_of_gram_det_eq_zero Y Z h, h]
    simp
  · rw [gram_det_fromCols_eq_mul_residual Y Z h, re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero Y).2]
    refine mul_le_mul_of_nonneg_left ?_ (gram_det_re_nonneg_and_im_eq_zero Y).1
    have hQ : ((Yᴴ * Z)ᴴ * (Yᴴ * Y)⁻¹ * (Yᴴ * Z)).PosSemidef :=
      (posSemidef_conjTranspose_mul_self Y).inv.conjTranspose_mul_mul_same _
    have hmono' := (hmono γ _ _ (posSemidef_conjTranspose_mul_self
      ((1 - Y * (Yᴴ * Y)⁻¹ * Yᴴ) * Z)) hQ).2.1
    refine hmono'.trans (le_of_eq ?_)
    rw [gram_projection_residual_eq Y Z h, conjTranspose_mul, conjTranspose_conjTranspose, sub_add_cancel]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_det_koteljanskii_inequality
    (hmono : ∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0))
    (X : Matrix m α ℂ) (Y : Matrix m β ℂ) (Z : Matrix m γ ℂ) :
    (Xᴴ * X).det.re * ((fromCols X (fromCols Y Z))ᴴ * fromCols X (fromCols Y Z)).det.re ≤
      ((fromCols X Y)ᴴ * fromCols X Y).det.re * ((fromCols X Z)ᴴ * fromCols X Z).det.re := by
  classical
  by_cases h : (Xᴴ * X).det = 0
  · rw [h]
    simpa using mul_nonneg (gram_det_re_nonneg_and_im_eq_zero (fromCols X Y)).1 (gram_det_re_nonneg_and_im_eq_zero (fromCols X Z)).1
  · rw [gram_det_fromCols_eq_mul_residual X _ h, gram_det_fromCols_eq_mul_residual X Y h, gram_det_fromCols_eq_mul_residual X Z h, mul_fromCols,
      re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero X).2, re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero X).2,
      re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero X).2]
    have hF := gram_det_fromCols_le_mul hmono ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * Y)
      ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * Z)
    nlinarith [mul_le_mul_of_nonneg_left hF (mul_self_nonneg (Xᴴ * X).det.re)]


open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
theorem _root_.GlobalTheory.gram_det_submodular :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0)) → (∀ (m α β γ : Type) [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (M : Matrix m (α ⊕ β ⊕ γ) ℂ), (((M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))).det.re) * (((M)ᴴ * (M)).det.re) ≤ (((M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))).det.re) * (((M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))).det.re)) := by
  intro hmono m α β γ _ _ _ _ _ _ _ M
  have key := gram_det_koteljanskii_inequality hmono (M.submatrix id Sum.inl)
    (M.submatrix id (Sum.inr ∘ Sum.inl)) (M.submatrix id (Sum.inr ∘ Sum.inr))
  have hM : fromCols (M.submatrix id Sum.inl)
      (fromCols (M.submatrix id (Sum.inr ∘ Sum.inl)) (M.submatrix id (Sum.inr ∘ Sum.inr))) = M := by
    ext x (a | b | c) <;> rfl
  have hXY : fromCols (M.submatrix id Sum.inl) (M.submatrix id (Sum.inr ∘ Sum.inl)) =
      M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ) := by
    ext x (a | b) <;> rfl
  have hXZ : fromCols (M.submatrix id Sum.inl) (M.submatrix id (Sum.inr ∘ Sum.inr)) =
      M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ) := by
    ext x (a | c) <;> rfl
  rwa [hM, hXY, hXZ] at key

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem gram_det_cauchy_schwarz_of_det_mono :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0)) → (∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq n] (A B : Matrix m n ℂ), ‖(Aᴴ * B).det‖ ^ 2 ≤ (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ∧ ((Aᴴ * B).det ≠ 0 → (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ≤ ‖(Aᴴ * B).det‖ ^ 2 → ∃ C : Matrix n n ℂ, B = A * C)) := by
  intro H m n _ _ _ A B
  classical
  have hA : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  have hB : (Bᴴ * B).PosSemidef := posSemidef_conjTranspose_mul_self B
  have hA0 : 0 ≤ (Aᴴ * A).det.re := (H n _ _ hA hA).1
  have hB0 : 0 ≤ (Bᴴ * B).det.re := (H n _ _ hB hB).1
  by_cases hG : (Aᴴ * A).det = 0
  · obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hG
    have hAv : A *ᵥ v = 0 := (conjTranspose_mul_self_mulVec_eq_zero A v).mp hv0
    have h1 : (Bᴴ * A).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, by rw [← mulVec_mulVec, hAv, mulVec_zero]⟩
    have h2 : (Aᴴ * B).det = 0 := by
      have : Aᴴ * B = (Bᴴ * A)ᴴ := by simp
      rw [this, det_conjTranspose, h1, star_zero]
    refine ⟨?_, fun h => (h h2).elim⟩
    rw [h2]
    simpa using mul_nonneg hA0 hB0
  · have hreal : (Aᴴ * A).det = ((Aᴴ * A).det.re : ℂ) := by
      have : star (Aᴴ * A).det = (Aᴴ * A).det := by
        rw [← det_conjTranspose, hA.1.eq]
      exact (Complex.conj_eq_iff_re.mp this).symm
    set g : ℝ := (Aᴴ * A).det.re with hg
    have hg0 : g ≠ 0 := fun h => hG (by rw [hreal, h]; simp)
    have hgpos : 0 < g := lt_of_le_of_ne hA0 hg0.symm
    obtain ⟨C, hC⟩ : ∃ C : Matrix n n ℂ, (Aᴴ * A) * C = Aᴴ * B :=
      ⟨(Aᴴ * A)⁻¹ * (Aᴴ * B), mul_nonsing_inv_cancel_left _ _ (Ne.isUnit hG)⟩
    have horth : (A * C)ᴴ * (B - A * C) = 0 := by
      rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_sub, ← Matrix.mul_assoc Aᴴ A C, hC,
        sub_self, Matrix.mul_zero]
    have horth' : (B - A * C)ᴴ * (A * C) = 0 := by
      have := congrArg conjTranspose horth
      rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
    have hsum : Bᴴ * B = (A * C)ᴴ * (A * C) + (B - A * C)ᴴ * (B - A * C) := by
      have hBe : B = A * C + (B - A * C) := by abel
      generalize B - A * C = D at *
      generalize A * C = E at *
      rw [hBe, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, horth, horth']
      simp
    have hP : ((A * C)ᴴ * (A * C)).det = ((g * ‖C.det‖ ^ 2 : ℝ) : ℂ) := by
      have : (A * C)ᴴ * (A * C) = Cᴴ * (Aᴴ * A) * C := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [this, det_mul, det_mul, det_conjTranspose, hreal]
      push_cast
      rw [← Complex.conj_mul' C.det]
      simp only [RCLike.star_def]
      ring
    have hAB : (Aᴴ * B).det = g * C.det := by rw [← hC, det_mul, hreal]
    have hN : ‖(Aᴴ * B).det‖ ^ 2 = g * (g * ‖C.det‖ ^ 2) := by
      rw [hAB, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA0]
      ring
    obtain ⟨-, h2, h3⟩ := H n _ _ (posSemidef_conjTranspose_mul_self (A * C))
      (posSemidef_conjTranspose_mul_self (B - A * C))
    rw [← hsum, hP, Complex.ofReal_re] at h2 h3
    rw [hN]
    refine ⟨mul_le_mul_of_nonneg_left h2 hA0, fun hne hle => ⟨C, ?_⟩⟩
    have hc : C.det ≠ 0 := fun h => hne (by rw [hAB, h, mul_zero])
    have hQ := h3 (by
      have : g * ‖C.det‖ ^ 2 ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))
      exact_mod_cast this) (le_of_mul_le_mul_left hle hgpos)
    exact sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp hQ)

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem subspace_sup_alternative :
    (∀ (K V Y σ : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype σ] (r : ℕ) (t : σ → Y → Y) (D : Y → Submodule K V → ℝ) (α : ℕ → Y → ℝ) (c Ω : ℝ), Module.finrank K V = r → 1 ≤ Ω → (∀ y W, 0 < D y W) → (∀ i ≤ r, ∀ y, IsLUB (D y '' {W | Module.finrank K W = i}) (α i y)) → (∀ y W₁ W₂, D y W₁ * D y W₂ ≤ D y (W₁ ⊓ W₂) * D y (W₁ ⊔ W₂)) → (∀ s y W, D (t s y) W ≤ Ω * D y W ∧ D y W ≤ Ω * D (t s y) W) → (∀ y W, W ≠ ⊥ → W ≠ ⊤ → ∑ s, D (t s y) W ≤ Fintype.card σ * (c * D y W)) → ∃ C : ℝ, 0 ≤ C ∧ (∀ (y : Y) (i : ℕ), 0 < i → i < r → (∑ s, α i (t s y) ≤ Fintype.card σ * (c * α i y)) ∨ ∃ j : ℕ, 0 < j ∧ j ≤ i ∧ i + j ≤ r ∧ ∀ s, α i (t s y) ≤ C * Real.sqrt (α (i - j) y * α (i + j) y))) := by
  intro K V Y σ _ _ _ _ _ r t D α c Ω hr hΩ hpos hlub hsub hmove hcon
  have hΩ0 : 0 < Ω := by linarith
  refine ⟨2 * Ω ^ 3, by positivity, fun y i hi0 hir => ?_⟩
  have hle : ∀ k ≤ r, ∀ z (W : Submodule K V), Module.finrank K W = k → D z W ≤ α k z :=
    fun k hk z W hW => (hlub k hk z).1 ⟨W, hW, rfl⟩
  have hub : ∀ k ≤ r, ∀ z (b : ℝ), (∀ W : Submodule K V, Module.finrank K W = k → D z W ≤ b) →
      α k z ≤ b := fun k hk z b hb => (hlub k hk z).2 (by
        rintro _ ⟨W, hW, rfl⟩
        exact hb W hW)
  have hex : ∀ b < α i y, ∃ W : Submodule K V, Module.finrank K W = i ∧ b < D y W := by
    intro b hb
    by_contra h
    push Not at h
    exact absurd (hub i hir.le y b h) (not_le.2 hb)
  have hA : 0 < α i y := by
    obtain ⟨W, hW, -⟩ := hex (α i y - 1) (by linarith)
    exact (hpos y W).trans_le (hle i hir.le y W hW)
  set A := α i y with hAdef
  set B := A / (2 * Ω ^ 2) with hBdef
  have hB0 : 0 < B := by positivity
  have hAB : A = 2 * Ω ^ 2 * B := by rw [hBdef]; field_simp
  have hBA : B < A := by
    have : 1 ≤ Ω ^ 2 := one_le_pow₀ hΩ
    nlinarith
  obtain ⟨W₀, hW₀, hBW₀⟩ := hex B hBA
  by_cases hcase : ∀ W : Submodule K V, Module.finrank K W = i → B < D y W → W = W₀
  · left
    have h0 : A = D y W₀ := by
      refine le_antisymm (hub i hir.le y _ fun W hW => ?_) (hle i hir.le y W₀ hW₀)
      by_cases h : B < D y W
      · rw [hcase W hW h]
      · exact (not_lt.1 h).trans hBW₀.le
    have h1 : ∀ s, α i (t s y) ≤ D (t s y) W₀ := by
      intro s
      refine hub i hir.le _ _ fun W hW => ?_
      by_cases h : B < D y W
      · rw [hcase W hW h]
      · have a1 := (hmove s y W).1
        have a2 := (hmove s y W₀).2
        have a3 : Ω * D y W ≤ Ω * B := mul_le_mul_of_nonneg_left (not_lt.1 h) hΩ0.le
        have a4 : Ω * (Ω * B) ≤ Ω * D (t s y) W₀ := by
          have : 0 < Ω ^ 2 * B := by positivity
          nlinarith
        have a5 := le_of_mul_le_mul_left a4 hΩ0
        linarith
    have hb : W₀ ≠ ⊥ := by
      rintro rfl
      rw [finrank_bot] at hW₀
      omega
    have ht : W₀ ≠ ⊤ := by
      rintro rfl
      rw [finrank_top] at hW₀
      omega
    rw [h0]
    exact (Finset.sum_le_sum fun s _ => h1 s).trans (hcon y W₀ hb ht)
  · right
    push Not at hcase
    obtain ⟨W₁, hW₁, hBW₁, hne⟩ := hcase
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₀
    have hlt : Module.finrank K ↥(W₁ ⊓ W₀) < i := by
      rw [← hW₁]
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => hne ?_)
      exact Submodule.eq_of_le_of_finrank_eq (inf_eq_left.1 h) (hW₁.trans hW₀.symm)
    have hsr : Module.finrank K ↥(W₁ ⊔ W₀) ≤ r := hr ▸ Submodule.finrank_le _
    refine ⟨i - Module.finrank K ↥(W₁ ⊓ W₀), by omega, by omega, by omega, fun s => ?_⟩
    set j := i - Module.finrank K ↥(W₁ ⊓ W₀) with hj
    have e1 : D y (W₁ ⊓ W₀) ≤ α (i - j) y := hle _ (by omega) y _ (by omega)
    have e2 : D y (W₁ ⊔ W₀) ≤ α (i + j) y := hle _ (by omega) y _ (by omega)
    have e3 : B ^ 2 ≤ α (i - j) y * α (i + j) y := by
      calc B ^ 2 = B * B := sq B
        _ ≤ D y W₁ * D y W₀ := mul_le_mul hBW₁.le hBW₀.le hB0.le (hpos _ _).le
        _ ≤ _ := hsub y W₁ W₀
        _ ≤ _ := mul_le_mul e1 e2 (hpos _ _).le ((hpos _ _).le.trans e1)
    have e4 : B ≤ Real.sqrt (α (i - j) y * α (i + j) y) := Real.le_sqrt_of_sq_le e3
    have e5 : α i (t s y) ≤ Ω * A := hub i hir.le _ _ fun W hW =>
      (hmove s y W).1.trans (mul_le_mul_of_nonneg_left (hle i hir.le y W hW) hΩ0.le)
    calc α i (t s y) ≤ Ω * A := e5
      _ = 2 * Ω ^ 3 * B := by rw [hAB]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e4 (by positivity)

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory


open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
theorem _root_.GlobalTheory.sum_log_gramDet_ratio_pos : (∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq n] (A B : Matrix m n ℂ), ‖(Aᴴ * B).det‖ ^ 2 ≤ (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ∧ ((Aᴴ * B).det ≠ 0 → (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ≤ ‖(Aᴴ * B).det‖ ^ 2 → ∃ C : Matrix n n ℂ, B = A * C)) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, 0 < (((a * M)ᴴ * (a * M)).det.re)) ∧ 0 < ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  intro hCS r S hS hirr i hi0 hir M hM
  have hG0 : ∀ X : Matrix (Fin r) (Fin i) ℂ, 0 ≤ (Xᴴ * X).det.re ∧ (Xᴴ * X).det.im = 0 := by
    intro X
    have h := Complex.le_def.mp (posSemidef_conjTranspose_mul_self X).det_nonneg
    exact ⟨by simpa using h.1, by simpa using h.2.symm⟩
  have hnorm : ∀ X : Matrix (Fin r) (Fin i) ℂ, ‖(Xᴴ * X).det‖ = (Xᴴ * X).det.re := by
    intro X
    have h : (Xᴴ * X).det = (((Xᴴ * X).det.re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [(hG0 X).2])
    rw [h, Complex.norm_real, Real.norm_of_nonneg (by simpa using (hG0 X).1)]
    simp
  have hunit : ∀ a ∈ S, IsUnit a.det := fun a ha => isUnit_iff_ne_zero.mpr (hS a ha).2.1
  have hmul : ∀ a ∈ S, (a * M)ᴴ * (a⁻¹ * M) = Mᴴ * M := by
    intro a ha
    rw [conjTranspose_mul, (hS a ha).1.eq, Matrix.mul_assoc, ← Matrix.mul_assoc a,
      mul_nonsing_inv _ (hunit a ha), Matrix.one_mul]
  have hpair : ∀ a ∈ S, ((Mᴴ * M).det.re) ^ 2 ≤
      ((a * M)ᴴ * (a * M)).det.re * ((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re := by
    intro a ha
    have h := (hCS (Fin r) (Fin i) (a * M) (a⁻¹ * M)).1
    rwa [hmul a ha, hnorm] at h
  have hMsq : 0 < ((Mᴴ * M).det.re) ^ 2 := pow_pos hM 2
  have hpos : ∀ a ∈ S, 0 < ((a * M)ᴴ * (a * M)).det.re := by
    intro a ha
    refine lt_of_le_of_ne (hG0 _).1 fun h => ?_
    have h' := hpair a ha
    rw [← h, zero_mul] at h'
    linarith
  refine ⟨hpos, ?_⟩
  have hinvinv : ∀ a ∈ S, a⁻¹⁻¹ = a := fun a ha => nonsing_inv_nonsing_inv a (hunit a ha)
  have hsum_inv : ∑ a ∈ S, Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) =
      ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) :=
    Finset.sum_nbij' (·⁻¹) (·⁻¹) (fun a ha => (hS a ha).2.2) (fun a ha => (hS a ha).2.2)
      (fun a ha => hinvinv a ha) (fun a ha => hinvinv a ha) (fun a _ => rfl)
  have hterm : ∀ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) =
      Real.log (((a * M)ᴴ * (a * M)).det.re * ((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re /
        ((Mᴴ * M).det.re) ^ 2) := by
    intro a ha
    rw [← Real.log_mul (div_pos (hpos a ha) hM).ne' (div_pos (hpos _ (hS a ha).2.2) hM).ne']
    congr 1
    field_simp
  have hnonneg : ∀ a ∈ S, 0 ≤ Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) := by
    intro a ha
    rw [hterm a ha]
    exact Real.log_nonneg ((one_le_div hMsq).mpr (hpair a ha))
  have hstrict : ∃ a ∈ S, 0 < Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) := by
    by_contra hcon
    push_neg at hcon
    have hle : ∀ a ∈ S, ((a * M)ᴴ * (a * M)).det.re * ((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re ≤
        ((Mᴴ * M).det.re) ^ 2 := by
      intro a ha
      refine (div_le_one hMsq).mp (not_lt.mp fun h => ?_)
      have h' := hcon a ha
      rw [hterm a ha] at h'
      exact absurd h' (not_le.mpr (Real.log_pos h))
    have hdet : (Mᴴ * M).det ≠ 0 := by
      intro h
      rw [h] at hM
      simp at hM
    have hcol : ∀ a ∈ S, ∃ C : Matrix (Fin i) (Fin i) ℂ, a * a * M = M * C := by
      intro a ha
      have ha' := (hS a ha).2.2
      have h := (hCS (Fin r) (Fin i) (a⁻¹ * M) (a⁻¹⁻¹ * M)).2
      rw [hmul _ ha', hnorm] at h
      obtain ⟨C, hC⟩ := h hdet (hle _ ha')
      rw [hinvinv a ha] at hC
      refine ⟨C, ?_⟩
      rw [Matrix.mul_assoc, hC, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        mul_nonsing_inv _ (hunit a ha), Matrix.one_mul]
    have hW : ∀ a ∈ S, ∀ v ∈ LinearMap.range (Matrix.mulVecLin M), (a * a).mulVec v ∈
        LinearMap.range (Matrix.mulVecLin M) := by
      rintro a ha v ⟨w, rfl⟩
      obtain ⟨C, hC⟩ := hcol a ha
      refine ⟨C *ᵥ w, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hC]
    rcases hirr _ hW with h | h
    · have hM0 : M = 0 := by
        ext x l
        have h2 := congrArg (fun f => f (Pi.single l 1) x) (LinearMap.range_eq_bot.mp h)
        simpa [Matrix.mulVecLin_apply] using h2
      haveI : Nonempty (Fin i) := ⟨⟨0, hi0⟩⟩
      rw [hM0] at hM
      simp at hM
    · have h1 := LinearMap.finrank_range_le (Matrix.mulVecLin M)
      rw [h, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h1
      omega
  have htot : 0 < ∑ a ∈ S, (Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re))) :=
    Finset.sum_pos' hnonneg hstrict
  rw [Finset.sum_add_distrib, hsum_inv] at htot
  linarith

end GlobalTheory
end
