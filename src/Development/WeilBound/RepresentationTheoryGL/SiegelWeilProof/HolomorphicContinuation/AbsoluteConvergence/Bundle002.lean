module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.IwaPf

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [JJ, fromBlocks_multiply, Matrix.one_apply]

theorem inG_blocks (g : M2 n) (h : InG g) :
    g.toBlocks₁₁ᴴ * g.toBlocks₂₁ - g.toBlocks₂₁ᴴ * g.toBlocks₁₁ = 0 ∧
    g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂ = 1 ∧
    g.toBlocks₁₂ᴴ * g.toBlocks₂₂ - g.toBlocks₂₂ᴴ * g.toBlocks₁₂ = 0 := by
  have h' := h
  unfold InG at h'
  rw [← fromBlocks_toBlocks g, fromBlocks_conjTranspose, JJ, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_inj] at h'
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add] at h'
  obtain ⟨h1, h2, h3, h4⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]; abel
  · rw [← h2]; abel
  · rw [← h4]; abel

theorem inG_rows (g : M2 n) (h : InG g) : g * JJ n * gᴴ = JJ n := by
  have hJ : JJ n * JJ n = -1 := JJ_mul_self
  have h1 : (-(JJ n * gᴴ * JJ n)) * g = 1 := by
    have e : gᴴ * JJ n * g = JJ n := h
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, e, hJ, neg_neg]
  have h2 := mul_eq_one_comm.mp h1
  have h3 : g * (JJ n * gᴴ * JJ n) = -1 := by
    rw [Matrix.mul_neg] at h2
    exact neg_eq_iff_eq_neg.mp h2
  calc g * JJ n * gᴴ = -(g * (JJ n * gᴴ * JJ n) * JJ n) := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_neg, Matrix.mul_one, neg_neg]
    _ = JJ n := by rw [h3, Matrix.neg_mul, Matrix.one_mul, neg_neg]

theorem key (a b c d : Matrix (Fin n) (Fin n) ℂ) (E1 : aᴴ * c - cᴴ * a = 0) (E2 : aᴴ * d - cᴴ * b = 1)
    (E3 : bᴴ * d - dᴴ * b = 0) (s : ℂ) :
    (s • a + b)ᴴ * (s • c + d) - (s • c + d)ᴴ * (s • a + b) = (star s - s) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have E2' : dᴴ * a - bᴴ * c = 1 := by
    have e := congrArg conjTranspose E2
    simpa [conjTranspose_sub, conjTranspose_mul] using e
  have expand : (s • a + b)ᴴ * (s • c + d) - (s • c + d)ᴴ * (s • a + b)
      = (star s * s) • (aᴴ * c - cᴴ * a) + star s • (aᴴ * d - cᴴ * b)
        - s • (dᴴ * a - bᴴ * c) + (bᴴ * d - dᴴ * b) := by
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [expand, E1, E2, E2', E3]
  module

theorem det_ne (g : M2 n) (h : InG g) (s : ℂ) (hs : star s - s ≠ 0) : (s • g.toBlocks₂₁ + g.toBlocks₂₂).det ≠ 0 := by
  obtain ⟨E1, E2, E3⟩ := inG_blocks g h
  intro hdet
  obtain ⟨v, hv, hYv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have K := key g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂ E1 E2 E3 s
  set X := s • g.toBlocks₁₁ + g.toBlocks₁₂
  set Y := s • g.toBlocks₂₁ + g.toBlocks₂₂
  have L : star v ⬝ᵥ ((Xᴴ * Y - Yᴴ * X) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hYv,
      Matrix.mulVec_zero, zero_sub, dotProduct_neg, dotProduct_mulVec, ← star_mulVec,
      hYv, star_zero, zero_dotProduct, neg_zero]
  rw [K, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at L
  rcases mul_eq_zero.mp L with h0 | h0
  · exact hs h0
  · exact hv (dotProduct_star_self_eq_zero.mp h0)

end PositivityTheory.Rg.Sw.AbsSt.IwaPf
end
end

section

open scoped Matrix
open Matrix

noncomputable section

namespace PositivityTheory.Rg.Sw.KAKB

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def S0 (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

def C0 (n : ℕ) : M2 n := fromBlocks 1 1 (Complex.I • 1) (-(Complex.I • 1))

def C1 (n : ℕ) : M2 n := (1 / 2 : ℂ) • (C0 n)ᴴ

theorem cayley_conjTranspose_eq : (C0 n)ᴴ = fromBlocks 1 (-(Complex.I • 1)) 1 (Complex.I • 1) := by
  simp [C0, fromBlocks_conjTranspose, conjTranspose_smul]

theorem cayley_conjTranspose_mul : (C0 n)ᴴ * C0 n = (2 : ℂ) • 1 := by
  rw [cayley_conjTranspose_eq, C0, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, two_smul] <;> module

theorem cayley_mul_conjTranspose : C0 n * (C0 n)ᴴ = (2 : ℂ) • 1 := by
  rw [cayley_conjTranspose_eq, C0, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, two_smul] <;> module

theorem cayley_inverse_mul : C1 n * C0 n = 1 := by
  rw [C1, Matrix.smul_mul, cayley_conjTranspose_mul, smul_smul]; norm_num

theorem cayley_mul_inverse : C0 n * C1 n = 1 := by
  rw [C1, Matrix.mul_smul, cayley_mul_conjTranspose, smul_smul]; norm_num

theorem complex_structure_cayley : JJ n * C0 n = C0 n * (Complex.I • S0 n) := by
  simp only [JJ, C0, S0, fromBlocks_multiply, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul] <;> module

end PositivityTheory.Rg.Sw.KAKB

end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def ept (x : Fin m → Fin n → ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1

theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (ept x) P := rfl

theorem norm_ept_le (x : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ‖ept x k‖ ≤ ‖x‖ := by
  have h : ‖x k.1 k.2.1‖ ≤ ‖x‖ := (norm_le_pi_norm (x k.1) k.2.1).trans (norm_le_pi_norm x k.1)
  unfold ept
  split_ifs
  · simpa using h
  · exact h

theorem continuous_ept : Continuous (ept : (Fin m → Fin n → ℂ) → _) := by
  refine continuous_pi fun k => ?_
  unfold ept
  split_ifs
  · exact continuous_star.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  · exact (continuous_apply k.2.1).comp (continuous_apply k.1)

theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x :=
  (MvPolynomial.continuous_eval P).comp continuous_ept

theorem poly_bound (P : PX m n) : ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧ ∀ x, ‖evX P x‖ ≤ C * (1 + ‖x‖) ^ k := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun x => by simp [evX_eq]⟩
  | add p q hp hq =>
    obtain ⟨C₁, k₁, h₁, hb₁⟩ := hp
    obtain ⟨C₂, k₂, h₂, hb₂⟩ := hq
    refine ⟨C₁ + C₂, k₁ + k₂, add_nonneg h₁ h₂, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
    have e1 : (1 + ‖x‖) ^ k₁ ≤ (1 + ‖x‖) ^ (k₁ + k₂) := pow_le_pow_right₀ h1 (Nat.le_add_right _ _)
    have e2 : (1 + ‖x‖) ^ k₂ ≤ (1 + ‖x‖) ^ (k₁ + k₂) := pow_le_pow_right₀ h1 (Nat.le_add_left _ _)
    rw [evX_eq, map_add (f := _)]
    calc ‖eval (ept x) p + eval (ept x) q‖ ≤ ‖eval (ept x) p‖ + ‖eval (ept x) q‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + ‖x‖) ^ k₁ + C₂ * (1 + ‖x‖) ^ k₂ := add_le_add (hb₁ x) (hb₂ x)
      _ ≤ C₁ * (1 + ‖x‖) ^ (k₁ + k₂) + C₂ * (1 + ‖x‖) ^ (k₁ + k₂) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 h₁) (mul_le_mul_of_nonneg_left e2 h₂)
      _ = (C₁ + C₂) * (1 + ‖x‖) ^ (k₁ + k₂) := by ring
  | mul_X p i hp =>
    obtain ⟨C, k, h0, hb⟩ := hp
    refine ⟨C, k + 1, h0, fun x => ?_⟩
    rw [evX_eq, map_mul, eval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (hb x) ((norm_ept_le x i).trans (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _)
      (mul_nonneg h0 (pow_nonneg (by positivity) _))

theorem sq_norm_le_sum (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ j, ‖x a j‖ ^ 2 :=
  _root_.UpperTheory.Reformulated.B.Yhb3.main x

theorem decay (k : ℕ) (κ : ℝ) (hκ : 0 < κ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ k * Real.exp (-(κ * s ^ 2)) ≤ C * (1 + s) ^ (-r) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((k : ℝ) + r)
  refine ⟨2 ^ N * (1 + N.factorial / κ ^ N), by positivity, fun s hs => ?_⟩
  have h1 : (1 : ℝ) ≤ 1 + s := le_add_of_nonneg_right hs
  have hpos : 0 < 1 + s := by linarith
  have hE : 0 < Real.exp (-(κ * s ^ 2)) := Real.exp_pos _

  have hA : (1 + s) ^ N ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := by
    rcases le_total s 1 with h | h
    · calc (1 + s) ^ N ≤ 2 ^ N := pow_le_pow_left₀ hpos.le (by linarith) N
        _ ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := le_mul_of_one_le_right (by positivity)
            (le_add_of_nonneg_right (by positivity))
    · have : 1 + s ≤ 2 * s ^ 2 := by nlinarith
      calc (1 + s) ^ N ≤ (2 * s ^ 2) ^ N := pow_le_pow_left₀ hpos.le this N
        _ = 2 ^ N * (s ^ 2) ^ N := by rw [mul_pow]
        _ ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := by nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 2) N]
  have hB : (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) ≤ N.factorial / κ ^ N := by
    have := Real.pow_div_factorial_le_exp (x := κ * s ^ 2) (by positivity) N
    rw [div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by positivity)]
    have e : Real.exp (-(κ * s ^ 2)) * Real.exp (κ * s ^ 2) = 1 := by rw [← Real.exp_add]; simp
    calc (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) * κ ^ N = (κ * s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) := by ring
      _ ≤ (Real.exp (κ * s ^ 2) * N.factorial) * Real.exp (-(κ * s ^ 2)) :=
          mul_le_mul_of_nonneg_right this hE.le
      _ = N.factorial := by rw [mul_comm (Real.exp _), mul_assoc, mul_comm (Real.exp _), e, mul_one]
  have hC : (1 + s) ^ N * Real.exp (-(κ * s ^ 2)) ≤ 2 ^ N * (1 + N.factorial / κ ^ N) := by
    calc (1 + s) ^ N * Real.exp (-(κ * s ^ 2)) ≤ 2 ^ N * (1 + (s ^ 2) ^ N) * Real.exp (-(κ * s ^ 2)) :=
          mul_le_mul_of_nonneg_right hA hE.le
      _ = 2 ^ N * (Real.exp (-(κ * s ^ 2)) + (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2))) := by ring
      _ ≤ 2 ^ N * (1 + N.factorial / κ ^ N) := by
          gcongr
          · exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg s])
  have hR : (1 + s) ^ k * (1 + s) ^ r ≤ (1 + s) ^ N := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 hN
  have hr : (1 + s) ^ r * (1 + s) ^ (-r) = 1 := by
    rw [← Real.rpow_add hpos]; simp
  calc (1 + s) ^ k * Real.exp (-(κ * s ^ 2))
      = ((1 + s) ^ k * (1 + s) ^ r * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) := by
        rw [show ((1 + s) ^ k * (1 + s) ^ r * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) =
          (1 + s) ^ k * Real.exp (-(κ * s ^ 2)) * ((1 + s) ^ r * (1 + s) ^ (-r)) by ring, hr, mul_one]
    _ ≤ ((1 + s) ^ N * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) := by
        gcongr
    _ ≤ (2 ^ N * (1 + N.factorial / κ ^ N)) * (1 + s) ^ (-r) := by gcongr

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end
