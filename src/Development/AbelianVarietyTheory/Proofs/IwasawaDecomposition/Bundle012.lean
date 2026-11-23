module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

section

namespace GlobalTheory.FirstColumnConjugation

open Matrix

theorem exists_det_ne_zero_first_col {n : ℕ} (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, P.det ≠ 0 ∧ ∀ k, P k 0 = v k := by
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hv
  let u : Fin (n + 1) → ℂ := v - Pi.single k₀ (1 : ℂ)
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    1 + replicateCol Unit u * replicateRow Unit (Pi.single k₀ (1 : ℂ))
  have hQdet : Q.det = v k₀ := by
    simp only [Q]
    rw [det_one_add_replicateCol_mul_replicateRow]
    simp [u]
  have hQcol : ∀ k, Q k k₀ = v k := by
    intro k
    simp only [Q, u]
    by_cases h : k = k₀ <;> simp [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, h]
  refine ⟨Q.submatrix id (Equiv.swap 0 k₀), ?_, fun k => ?_⟩
  · rw [det_permute', hQdet]
    exact mul_ne_zero (by simp) hk₀
  · simp [hQcol]

theorem exists_conj_first_col_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      Matrix.det P ≠ 0 ∧ (∀ a : Fin n, B (Fin.succ a) 0 = 0) ∧ A * P = P * B := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv : A *ᵥ v = μ • v := by
    have h := Module.End.mem_eigenspace_iff.1 hv.1
    rwa [Matrix.toLin'_apply] at h
  obtain ⟨P, hP, hPv⟩ := exists_det_ne_zero_first_col v hv.2
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 (Ne.isUnit hP)
  refine ⟨P, P⁻¹ * A * P, hP, fun a => ?_, ?_⟩
  · have hPe : P *ᵥ Pi.single 0 1 = v := by
      ext k
      rw [mulVec_single_one]
      exact hPv k
    have hcol : (P⁻¹ * A * P) *ᵥ Pi.single 0 1 = μ • Pi.single 0 1 := by
      rw [← mulVec_mulVec, hPe, ← mulVec_mulVec, hAv, mulVec_smul, ← hPe, mulVec_mulVec,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det P).1 hu), one_mulVec]
    have h := congrFun hcol (Fin.succ a)
    rw [mulVec_single_one] at h
    simpa [Pi.single_apply, Fin.succ_ne_zero] using h
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).1 hu),
      Matrix.one_mul]

end GlobalTheory.FirstColumnConjugation
end

section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem gaussian_pairing_moment_algebra :
    ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ)
      (t f : ℂ) (p q : σ → ℂ) (m n : Matrix σ σ ℂ),
      Sᵀ = S → Tᵀ = T → IsUnit (1 - (t ^ 2) • (T * S)).det →
      p = t • (f • y + T *ᵥ q) → q = t • (f • x + S *ᵥ p) →
      m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec y q + t • (T * n) →
      n = t • vecMulVec x q + t • (S * m) →
      (let w : σ → ℂ := (1 - (t ^ 2) • (T * S))⁻¹ *ᵥ (y + t • T *ᵥ x)
       let u : σ → ℂ := x + t • S *ᵥ w
       f * (x ⬝ᵥ y) + x ⬝ᵥ T *ᵥ q + y ⬝ᵥ S *ᵥ p + (S * m * Tᵀ).trace =
         f * (u ⬝ᵥ w + t * (T * S * (1 - (t ^ 2) • (T * S))⁻¹).trace)) := by
  intro σ _ _ S T x y t f p q m n hS hT hA hp hq hm hn w u
  set A : Matrix σ σ ℂ := 1 - (t ^ 2) • (T * S) with hAdef
  have hKA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hAK : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hAv : ∀ v : σ → ℂ, A *ᵥ v = v - (t ^ 2) • T *ᵥ (S *ᵥ v) := by
    intro v
    rw [hAdef, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have hAp : A *ᵥ p = (t * f) • (y + t • T *ᵥ x) := by
    have h1 : p = t • (f • y + T *ᵥ (t • (f • x + S *ᵥ p))) := by rw [← hq]; exact hp
    rw [hAv]
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul] at h1
    rw [sub_eq_iff_eq_add]
    refine h1.trans ?_
    module
  have hpw : p = (t * f) • w := by
    have : p = A⁻¹ *ᵥ (A *ᵥ p) := by rw [Matrix.mulVec_mulVec, hKA, Matrix.one_mulVec]
    rw [this, hAp, Matrix.mulVec_smul]
  have hqu : q = (t * f) • u := by
    rw [hq, hpw, Matrix.mulVec_smul]
    simp only [u]
    module
  have hAw : A *ᵥ w = y + t • T *ᵥ x := by
    simp only [w]
    rw [Matrix.mulVec_mulVec, hAK, Matrix.one_mulVec]
  have hw : w = y + t • T *ᵥ u := by
    rw [hAv, sub_eq_iff_eq_add] at hAw
    refine hAw.trans ?_
    simp only [u]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    module
  have hAm : A * m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec (y + t • T *ᵥ x) q := by
    have h1 : m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec y q
        + t • (T * (t • vecMulVec x q + t • (S * m))) := by rw [← hn]; exact hm
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_vecMulVec,
      ← Matrix.mul_assoc] at h1
    rw [hAdef, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, sub_eq_iff_eq_add,
      Matrix.add_vecMulVec, Matrix.smul_vecMulVec]
    refine h1.trans ?_
    module
  have hmK : m = (t * f) • A⁻¹ + t • vecMulVec w q := by
    have : m = A⁻¹ * (A * m) := by rw [← Matrix.mul_assoc, hKA, Matrix.one_mul]
    rw [this, hAm, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_vecMulVec]
  have htr : (S * m * Tᵀ).trace
      = (t * f) * (T * S * A⁻¹).trace + t * ((S *ᵥ w) ⬝ᵥ (T *ᵥ q)) := by
    rw [hmK, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, Matrix.vecMul_transpose,
      hT, Matrix.trace_mul_comm (S * A⁻¹) T, Matrix.mul_assoc T S, smul_eq_mul, smul_eq_mul]
  have huw : u ⬝ᵥ w = x ⬝ᵥ y + t * (x ⬝ᵥ T *ᵥ u) + t * (y ⬝ᵥ S *ᵥ w)
      + t ^ 2 * ((S *ᵥ w) ⬝ᵥ (T *ᵥ u)) := by
    have h1 : u ⬝ᵥ w = (x + t • S *ᵥ w) ⬝ᵥ (y + t • T *ᵥ u) := by rw [← hw]
    rw [h1]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (S *ᵥ w) y]
    ring
  rw [htr, huw, hqu, hpw]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

end GlobalTheory
end

section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem schur_scalar_bound (u w C₀ c₀ : ℝ) (hC : 0 ≤ C₀) (hc : 0 < c₀) :
    u ^ 2 + w ^ 2 ≤ (1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀) *
      ((1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2) := by
  set α := C₀ / c₀ with hα
  have hα0 : 0 ≤ α := div_nonneg hC hc.le
  set p := w - α * u with hp
  have e : (1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2 = u ^ 2 + c₀ * p ^ 2 := by
    rw [hp, hα]; field_simp; ring
  have hw : w = p + α * u := by rw [hp]; ring
  have h1 : u ^ 2 + w ^ 2 ≤ (1 + α) ^ 2 * (u ^ 2 + p ^ 2) := by
    rw [hw]
    nlinarith [mul_nonneg hα0 (sq_nonneg (p - u)), mul_nonneg hα0 (sq_nonneg u),
      mul_nonneg (mul_nonneg hα0 hα0) (sq_nonneg u), mul_nonneg hα0 (sq_nonneg p),
      mul_nonneg (mul_nonneg hα0 hα0) (sq_nonneg p)]
  set M := max 1 (1 / c₀) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMc : 1 ≤ M * c₀ := by
    have : 1 / c₀ ≤ M := le_max_right _ _
    rw [div_le_iff₀ hc] at this; linarith
  have h2 : u ^ 2 + p ^ 2 ≤ M * (u ^ 2 + c₀ * p ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hM1 (sq_nonneg u),
      mul_le_mul_of_nonneg_right hMc (sq_nonneg p)]
  rw [e]
  calc u ^ 2 + w ^ 2 ≤ (1 + α) ^ 2 * (u ^ 2 + p ^ 2) := h1
    _ ≤ (1 + α) ^ 2 * (M * (u ^ 2 + c₀ * p ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

theorem dot_sq_le (n : ℕ) (x v : Fin n → ℝ) : (x ⬝ᵥ v) ^ 2 ≤ (x ⬝ᵥ x) * (v ⬝ᵥ v) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x v
  simpa [dotProduct, sq] using this

theorem dot_self_nonneg' (n : ℕ) (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem schur_block_lower_bound : ∀ (k l : ℕ) (a bt : Matrix (Fin k) (Fin k) ℝ) (b : Matrix (Fin k) (Fin l) ℝ) (d : Matrix (Fin l) (Fin l) ℝ) (C₀ c₀ b₀ : ℝ), 0 ≤ C₀ → 0 < c₀ → 0 < b₀ → a.IsSymm → d.IsSymm → bt.IsSymm → (∀ x, |x ⬝ᵥ a.mulVec x| ≤ C₀ * (x ⬝ᵥ x)) → (∀ y, (b.mulVec y) ⬝ᵥ (b.mulVec y) ≤ C₀ ^ 2 * (y ⬝ᵥ y)) → (∀ y, c₀ * (y ⬝ᵥ y) ≤ y ⬝ᵥ d.mulVec y) → (∀ x, b₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ bt.mulVec x) → ∀ z : Fin k ⊕ Fin l → ℝ, ((1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀))⁻¹ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Matrix.fromBlocks (a + ((1 + C₀ + C₀ ^ 2 / c₀) / b₀) • bt) b b.transpose d).mulVec z := by
  intro k l a bt b d C₀ c₀ b₀ hC hc hb _ _ _ ha hbb hd hbt z
  set x : Fin k → ℝ := z ∘ Sum.inl with hx
  set y : Fin l → ℝ := z ∘ Sum.inr with hy
  set L := (1 + C₀ + C₀ ^ 2 / c₀) / b₀ with hL
  have hsum : ∀ (f g : Fin k ⊕ Fin l → ℝ), f ⬝ᵥ g = (f ∘ Sum.inl) ⬝ᵥ (g ∘ Sum.inl) + (f ∘ Sum.inr) ⬝ᵥ (g ∘ Sum.inr) := by
    intro f g; simp [dotProduct, Fintype.sum_sum_type]
  have htr : y ⬝ᵥ b.transpose.mulVec x = x ⬝ᵥ b.mulVec y := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hexp : z ⬝ᵥ (Matrix.fromBlocks (a + L • bt) b b.transpose d).mulVec z
      = x ⬝ᵥ a.mulVec x + L * (x ⬝ᵥ bt.mulVec x) + 2 * (x ⬝ᵥ b.mulVec y) + y ⬝ᵥ d.mulVec y := by
    rw [hsum, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [← hx, ← hy, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_add, dotProduct_add,
      dotProduct_smul, htr, smul_eq_mul]
    ring
  have hzz : z ⬝ᵥ z = x ⬝ᵥ x + y ⬝ᵥ y := hsum z z
  rw [hexp, hzz]
  set U := x ⬝ᵥ x
  set W := y ⬝ᵥ y
  have hU : 0 ≤ U := dot_self_nonneg' k x
  have hW : 0 ≤ W := dot_self_nonneg' l y
  set u := Real.sqrt U
  set w := Real.sqrt W
  have hu : u ^ 2 = U := Real.sq_sqrt hU
  have hw : w ^ 2 = W := Real.sq_sqrt hW
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _

  have hQ : |x ⬝ᵥ b.mulVec y| ≤ C₀ * u * w := by
    have h1 := dot_sq_le k x (b.mulVec y)
    have h2 := hbb y
    have h3 : (x ⬝ᵥ b.mulVec y) ^ 2 ≤ (C₀ * u * w) ^ 2 := by
      calc (x ⬝ᵥ b.mulVec y) ^ 2 ≤ U * (b.mulVec y ⬝ᵥ b.mulVec y) := h1
        _ ≤ U * (C₀ ^ 2 * W) := mul_le_mul_of_nonneg_left h2 hU
        _ = (C₀ * u * w) ^ 2 := by rw [← hu, ← hw]; ring
    exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2 |> fun h => abs_le.mpr ⟨(abs_le_of_sq_le_sq' h3 (by positivity)).1, h⟩
  have hT : -(C₀ * U) ≤ x ⬝ᵥ a.mulVec x := by
    have := ha x; exact (abs_le.mp this).1
  have hB : (1 + C₀ + C₀ ^ 2 / c₀) * U ≤ L * (x ⬝ᵥ bt.mulVec x) := by
    have h := hbt x
    have hL0 : 0 ≤ L := by rw [hL]; positivity
    calc (1 + C₀ + C₀ ^ 2 / c₀) * U = L * (b₀ * U) := by rw [hL]; field_simp
      _ ≤ L * (x ⬝ᵥ bt.mulVec x) := mul_le_mul_of_nonneg_left h hL0
  have hD := hd y
  have hQ' := (abs_le.mp hQ).1
  have key := schur_scalar_bound u w C₀ c₀ hC hc
  have hK : 0 < (1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀) := by
    have : 0 < 1 + C₀ / c₀ := by have := div_nonneg hC hc.le; linarith
    exact mul_pos (pow_pos this 2) (lt_of_lt_of_le one_pos (le_max_left _ _))
  rw [inv_mul_le_iff₀ hK]
  have hS : (1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2 ≤
      x ⬝ᵥ a.mulVec x + L * (x ⬝ᵥ bt.mulVec x) + 2 * (x ⬝ᵥ b.mulVec y) + y ⬝ᵥ d.mulVec y := by
    rw [hu, hw]; nlinarith
  calc U + W = u ^ 2 + w ^ 2 := by rw [hu, hw]
    _ ≤ _ := key
    _ ≤ _ := mul_le_mul_of_nonneg_left hS hK.le

end GlobalTheory
end

section

noncomputable section

open Matrix

namespace GlobalTheory.RedTh

structure IsSiegel {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) : Prop where

  nonneg : ∀ i, 0 ≤ d i

  step : ∀ p q : Fin n, (q : ℕ) = p + 1 → d p ≤ 4 * d q

  diag : ∀ i, u i i = 1

  lower : ∀ i j, j < i → u i j = 0

  upper : ∀ i j, i < j → |u i j| ≤ 1 / 2

def gram {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := uᵀ * diagonal d * u

section Act

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {n : ℕ}

def actMat (b : Module.Basis (Fin n) ℤ X) : O →+* Matrix (Fin n) (Fin n) ℤ :=
  ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom).comp (Module.toModuleEnd ℤ X)

theorem actMat_apply (b : Module.Basis (Fin n) ℤ X) (c : O) (i j : Fin n) : actMat b c i j = b.repr (c • b j) i := by
  show LinearMap.toMatrixAlgEquiv b (Module.toModuleEnd ℤ X c) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

end Act

end GlobalTheory.RedTh
end
end

section

namespace GlobalTheory.UpperTriangularMul

theorem upperTriangular_mul :
    ∀ {n : ℕ} {R : Type} [inst : CommRing R] {M N : Matrix (Fin n) (Fin n) R},
      (∀ (a i : Fin n), i < a → M a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → N a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → (M * N) a i = (0 : R)) ∧
        ∀ (i : Fin n), (M * N) i i = M i i * N i i := by
  intro n R _ M N hM hN
  refine ⟨fun a i hia => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j a with h | h
    · rw [hM a j h, zero_mul]
    · rw [hN j i (lt_of_lt_of_le hia h), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hM i j h, zero_mul]
    · rw [hN j i h, mul_zero]

end GlobalTheory.UpperTriangularMul
end

section

open Matrix

namespace GlobalTheory

theorem dualV_pairing_exists : ∀ (r g rk : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)) (ε : Fin g → Fin r → ℚ), Mqᵀ = -Mq → LinearIndependent ℚ ε → (∀ i : Fin g, i.val < rk → ∀ w ∈ V, ε i ⬝ᵥ Mq *ᵥ w = 0) → (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → y ∈ Submodule.span ℚ (ε '' {i | i.val < rk})) → ∀ j : Fin g, rk ≤ j.val → ∃ x ∈ V, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0 := by
  intro r g rk Mq V ε hskew hli horth hperp j hj
  have skew : ∀ x y : Fin r → ℚ, x ⬝ᵥ Mq *ᵥ y = -(y ⬝ᵥ Mq *ᵥ x) := by
    intro x y
    rw [dotProduct_mulVec x Mq y, dotProduct_comm y, ← vecMul_transpose, hskew, vecMul_neg,
      neg_dotProduct, neg_neg]
  let Φ : (Fin r → ℚ) →ₗ[ℚ] (Fin g → ℚ) :=
    { toFun := fun x i => x ⬝ᵥ Mq *ᵥ ε i
      map_add' := by intro x y; funext i; simp [add_dotProduct]
      map_smul' := by intro c x; funext i; simp [smul_dotProduct] }
  have hΦ : ∀ x i, Φ x i = x ⬝ᵥ Mq *ᵥ ε i := fun _ _ => rfl
  suffices h : Pi.single j (1 : ℚ) ∈ V.map Φ by
    obtain ⟨x, hx, hxe⟩ := h
    refine ⟨x, hx, fun i => ?_⟩
    rw [← hΦ, hxe, Pi.single_apply]
  by_contra hnot
  obtain ⟨f, hfj, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hf0 : ∀ s ∈ V.map Φ, f s = 0 := by
    intro s hs
    have : f s ∈ (V.map Φ).map f := Submodule.mem_map_of_mem hs
    rw [hfS] at this
    simpa using this
  set a : Fin g → ℚ := fun i => f (Pi.single i 1) with ha
  have hfsum : ∀ s : Fin g → ℚ, f s = ∑ i, a i * s i := by
    intro s
    conv_lhs => rw [pi_eq_sum_univ s]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    congr 1
    simp only [ha]
    congr 1
    funext k
    simp [Pi.single_apply, eq_comm]
  set a' : Fin g → ℚ := fun i => if rk ≤ i.val then a i else 0 with ha'
  have hΦlow : ∀ w ∈ V, ∀ i : Fin g, i.val < rk → Φ w i = 0 := by
    intro w hw i hi
    rw [hΦ, skew, horth i hi w hw, neg_zero]
  have hsum' : ∀ w ∈ V, ∑ i, a' i * Φ w i = 0 := by
    intro w hw
    have h1 : ∑ i, a' i * Φ w i = ∑ i, a i * Φ w i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : rk ≤ i.val
      · simp [ha', hi]
      · simp [ha', hi, hΦlow w hw i (by omega)]
    rw [h1, ← hfsum]
    exact hf0 _ (Submodule.mem_map_of_mem hw)
  set e : Fin r → ℚ := ∑ i, a' i • ε i with he
  have heV : ∀ w ∈ V, e ⬝ᵥ Mq *ᵥ w = 0 := by
    intro w hw
    rw [he, sum_dotProduct]
    have : ∑ i, (a' i • ε i) ⬝ᵥ Mq *ᵥ w = -∑ i, a' i * Φ w i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_dotProduct, smul_eq_mul, hΦ, skew w, mul_neg, neg_neg]
    rw [this, hsum' w hw, neg_zero]
  have hespan := hperp e heV
  rw [Finsupp.mem_span_image_iff_linearCombination] at hespan
  obtain ⟨l, hl, hc⟩ := hespan
  let c' : Fin g → ℚ := fun i => l i
  have hc' : ∑ i, c' i • ε i = e := by
    rw [← hc, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  have hzero : ∑ i, (a' i - c' i) • ε i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hc', he, sub_self]
  have := Fintype.linearIndependent_iff.mp hli _ hzero j
  have hcj : c' j = 0 := (Finsupp.mem_supported' ℚ l).mp hl j (by simp; omega)
  have haj : a' j = a j := by simp [ha', hj]
  rw [hcj, haj, sub_zero] at this
  exact hfj this

end GlobalTheory
end

section

namespace GlobalTheory.NatCastNotMemPrime

theorem natCast_notMem_of_prime_ne {A : Type} [inst : CommRing A] (P : Ideal A)
    [hP : Ideal.IsPrime P] {p l : ℕ} (hp : Nat.Prime p) (hl : Nat.Prime l) (hne : l ≠ p)
    (hpP : (↑p : A) ∈ P) : (↑l : A) ∉ P := by
  intro hlP
  have hcop : Nat.Coprime l p := (Nat.coprime_primes hl hp).2 hne
  have hc : IsCoprime (l : A) (p : A) := Nat.Coprime.cast hcop
  obtain ⟨a, b, hab⟩ := hc
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact P.add_mem (P.mul_mem_left a hlP) (P.mul_mem_left b hpP)

end GlobalTheory.NatCastNotMemPrime
end
