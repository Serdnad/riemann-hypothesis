module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open scoped BigOperators

namespace GlobalTheory

private lemma exponent_product_le_G_div_N_mul_rpow (f r : ℕ) (G N H Q l d : ℝ) (hG : 1 ≤ G) (hN : 1 ≤ N)
    (hGH : G ≤ H) (hNH : N ≤ H) (hQ : 0 ≤ Q) (hQH : Q * 9 ^ f ≤ H) (hl : 0 ≤ l) (hd : 1 ≤ d)
    (hdG : d ≤ G) :
    (G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
        (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)) ≤
      G / N * H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) := by
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hd0 : 0 < d := by linarith
  have hGd0 : 0 < G / d := div_pos (by linarith) hd0
  have hGdG : G / d ≤ G := div_le_self (by linarith) hd

  have h1 : (G / d) ^ (l + 3) ≤ G * H ^ (l + 2) := by
    rw [show l + 3 = 1 + (l + 2) by ring, Real.rpow_add hGd0, Real.rpow_one]
    exact mul_le_mul hGdG (Real.rpow_le_rpow hGd0.le (hGdG.trans hGH) (by linarith))
      (Real.rpow_nonneg hGd0.le _) (by linarith)

  have h2 : N ^ (2 * r) * N * (Q * 9 ^ f) ≤ H ^ (2 * r + 2) := by
    have hN2 : N ^ (2 * r) ≤ H ^ (2 * r) := pow_le_pow_left₀ hN0.le hNH _
    calc N ^ (2 * r) * N * (Q * 9 ^ f) ≤ H ^ (2 * r) * H * H :=
          mul_le_mul (mul_le_mul hN2 hNH hN0.le (pow_nonneg hH0.le _)) hQH
            (mul_nonneg hQ (by positivity)) (mul_nonneg (pow_nonneg hH0.le _) hH0.le)
      _ = H ^ (2 * r + 2) := by ring
  have h3 : G ^ r ≤ H ^ r := pow_le_pow_left₀ (by linarith) hGH r

  have hE : H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) =
      H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r * H ^ (9 + 9 * r + 16 * r ^ 2) := by
    rw [← Real.rpow_natCast H (2 * r + 2), ← Real.rpow_natCast H r,
      ← Real.rpow_natCast H (9 + 9 * r + 16 * r ^ 2), ← Real.rpow_add hH0, ← Real.rpow_add hH0,
      ← Real.rpow_add hH0, ← Real.rpow_add hH0]
    congr 1
    push_cast
    ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hN0, hE]
  have hP : 0 ≤ H ^ (11 + 3 * l) := Real.rpow_nonneg hH0.le _
  have hM : 0 ≤ N ^ (2 * r) * N * (Q * 9 ^ f) :=
    mul_nonneg (mul_nonneg (pow_nonneg hN0.le _) hN0.le) (mul_nonneg hQ (by positivity))
  have hA : 0 ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hH0.le _)) hP
  have hR : 0 ≤ G ^ r := pow_nonneg (by linarith) _
  have hS : 0 ≤ H ^ (9 + 9 * r + 16 * r ^ 2) := pow_nonneg hH0.le _
  have hAM : 0 ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) :=
    mul_nonneg hA (pow_nonneg hH0.le _)
  calc (G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
          (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)) * N
        = (G / d) ^ (l + 3) * H ^ (11 + 3 * l) * (N ^ (2 * r) * N * (Q * 9 ^ f)) * G ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2) := by ring
    _ ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right h1 hP) h2 hM hA) h3 hR hAM) hS
    _ = G * (H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2)) := by ring

theorem exponent_term (k f r : ℕ) (G N H a Q l d : ℝ) (hk : 1 ≤ k)
    (hG : 1 ≤ G) (hN : 1 ≤ N) (hGH : G ≤ H) (hNH : N ≤ H) (ha : 0 ≤ a) (hQ : 0 ≤ Q)
    (hQH : Q * 9 ^ f ≤ H) (hl : 0 ≤ l) (hd : 1 ≤ d) (hdG : d ≤ G) :
    (d / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * l)) *
        ((G / d) ^ ((k : ℝ) + (1 + l) + 1) *
          (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤
      H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hN0 : 0 < N := by linarith
  have hd0 : 0 < d := by linarith
  have hGd0 : 0 < G / d := div_pos (by linarith) hd0

  have hexp : ((m + 1 : ℕ) : ℝ) + (1 + l) + 1 = (m : ℝ) + (l + 3) := by push_cast; ring
  rw [hexp, Real.rpow_add hGd0, Real.rpow_natCast, Nat.add_sub_cancel, pow_succ]
  have hdm : (d / N) ^ m * (G / d) ^ m = (G / N) ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hB := exponent_product_le_G_div_N_mul_rpow f r G N H Q l d hG hN hGH hNH hQ hQH hl hd hdG
  have hX : 0 ≤ a * (G / N) ^ m := mul_nonneg ha (pow_nonneg (div_nonneg (by linarith) hN0.le) _)
  calc (d / N) ^ m * a * (Q * H ^ (11 + 3 * l)) *
          ((G / d) ^ m * (G / d) ^ (l + 3) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)))
        = a * ((d / N) ^ m * (G / d) ^ m) * ((G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) := by ring
    _ = a * (G / N) ^ m * ((G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) := by rw [hdm]
    _ ≤ a * (G / N) ^ m * (G / N * H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hB hX
    _ = H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * ((G / N) ^ m * (G / N))) := by
          ring

theorem exponent_sum_le :
    ∀ (k f r : ℕ) (G N H a Q C : ℝ), 1 ≤ k → 1 ≤ r → 1 ≤ f → Real.log f ≤ Real.sqrt r → 1 ≤ G → 1 ≤ N → G ≤ H → N ≤ H → 0 ≤ a → 0 ≤ Q → Q * 9 ^ f ≤ H → 60 ≤ C → ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, ((de : ℝ) / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * Real.logb 2 f)) * ((G / de) ^ ((k : ℝ) + Real.logb 2 (2 * f) + 1) * (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  intro k f r G N H a Q C hk hr hf hlog hG hN hGH hNH ha hQ hQH hC
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl0 : 0 ≤ Real.logb 2 (f : ℝ) := Real.logb_nonneg one_lt_two hf1
  have h2f : Real.logb 2 (2 * (f : ℝ)) = 1 + Real.logb 2 f := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt (by linarith)), Real.logb_self_eq_one one_lt_two]
  have hX : 0 ≤ a * (G / N) ^ k := mul_nonneg ha (pow_nonneg (div_nonneg (by linarith) hN0.le) _)

  refine le_trans (Finset.sum_le_sum (g := fun _ =>
    H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * (G / N) ^ k)) ?_) ?_
  · intro de hde
    rw [Finset.mem_Icc] at hde
    have hd1 : (1 : ℝ) ≤ de := by exact_mod_cast hde.1
    have hdG : (de : ℝ) ≤ G := le_trans (Nat.cast_le.mpr hde.2) (Nat.floor_le (by linarith))
    simp only [h2f]
    exact exponent_term k f r G N H a Q (Real.logb 2 f) de hk hG hN hGH hNH ha hQ hQH
      hl0 hd1 hdG
  ·
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hfl : (⌊G⌋₊ : ℝ) ≤ H := (Nat.floor_le (by linarith)).trans hGH
    have hsq : Real.sqrt r ≤ r := by
      have h0 := Real.sqrt_nonneg (r : ℝ)
      have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ r by linarith)
      nlinarith
    have hlog2 := Real.log_two_gt_d9
    have hlb : Real.logb 2 (f : ℝ) ≤ 7 / 4 * r := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by linarith)
        (show (0 : ℝ) ≤ Real.log 2 - 0.69 by linarith)]
    have hexp : 1 + (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) ≤
        C * (r : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg (r : ℝ))]
    have hE0 : 0 ≤ H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) :=
      Real.rpow_nonneg hH0.le _
    calc (⌊G⌋₊ : ℝ) * (H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) *
            (a * (G / N) ^ k))
        ≤ H * (H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) *
            (a * (G / N) ^ k)) := mul_le_mul_of_nonneg_right hfl (mul_nonneg hE0 hX)
      _ = H ^ (1 + (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2)) *
            (a * (G / N) ^ k) := by rw [Real.rpow_add hH0 1, Real.rpow_one]; ring
      _ ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) hX

end GlobalTheory
end

section

open Matrix Finset Real

namespace GlobalTheory

theorem one_add_add_sq_div_three_le_exp (u : ℝ) (hu : |u| ≤ 1) :
    1 + u + u ^ 2 / 3 ≤ Real.exp u := by
  have h := Real.exp_bound hu (n := 5) (by norm_num)
  have h1 := (abs_le.mp h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h4 : |u| ^ 4 = u ^ 4 := by
    rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have h5 : |u| ^ 5 ≤ u ^ 4 := by
    rw [← h4, pow_succ]
    exact mul_le_of_le_one_right (by positivity) hu
  have h6 : -1 ≤ u := (abs_le.mp hu).1
  have h7 : 0 ≤ u ^ 2 * (1 + u) := mul_nonneg (sq_nonneg u) (by linarith)
  have h8 : 0 ≤ u ^ 4 := by positivity
  nlinarith

theorem three_mul_div_four_le_log_one_add (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 3) :
    3 * u / 4 ≤ Real.log (1 + u) := by
  have hp : 0 < 1 + u := by linarith
  refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hp)
  have : (1 + u)⁻¹ ≤ 1 - 3 * u / 4 := by
    rw [inv_eq_one_div, div_le_iff₀ hp]
    nlinarith
  linarith

theorem exp_quadratic_lower_and_log_linear_lower :
    (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) :=
  ⟨one_add_add_sq_div_three_le_exp, three_mul_div_four_le_log_one_add⟩

end GlobalTheory
end

section

open Matrix Finset Real

namespace GlobalTheory

theorem abs_sub_le_exp_neg_sixteenth_mul :
    ∀ (D Ds n f : ℝ), 0 ≤ D → 0 ≤ Ds → Real.exp 15 ≤ n → 1 ≤ f → |D - Ds| ≤ (2 * Real.exp (-(1 / 4) * n * f * Real.log n) + Real.exp (-n ^ 2 * f)) * Ds + Real.exp (-n ^ 2 * f) * D → |D - Ds| ≤ Real.exp (-(1 / 16) * n * f * Real.log n) * Ds := by
  intro D Ds n f hD hDs hn hf h
  have hn16 : (16:ℝ) ≤ n := by
    have := Real.add_one_le_exp (15:ℝ); linarith
  have hn0 : 0 < n := by linarith
  have hL : 15 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos 15) hn
    rwa [Real.log_exp] at this
  have hLn : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hn0; linarith
  have hnf : 16 ≤ n * f := by nlinarith
  have ha : 240 ≤ n * f * Real.log n := by nlinarith
  have hnn : n * f * Real.log n ≤ n ^ 2 * f := by
    have := mul_le_mul_of_nonneg_left hLn (by linarith : (0:ℝ) ≤ n * f)
    nlinarith
  have hlog8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8); linarith
  have hT8 : Real.exp (-(1 / 16) * n * f * Real.log n - Real.log 8) =
      Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  have e1 : Real.exp (-(1 / 4) * n * f * Real.log n) ≤
      Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [← hT8]; apply Real.exp_le_exp.mpr; nlinarith
  have e2 : Real.exp (-n ^ 2 * f) ≤ Real.exp (-(1 / 16) * n * f * Real.log n) / 8 := by
    rw [← hT8]; apply Real.exp_le_exp.mpr; nlinarith
  have hT1 : Real.exp (-(1 / 16) * n * f * Real.log n) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr; nlinarith
  have hδ0 : 0 ≤ Real.exp (-n ^ 2 * f) := (Real.exp_pos _).le
  have hδ : Real.exp (-n ^ 2 * f) ≤ 1 / 2 := by linarith
  have hX : 0 ≤ |D - Ds| := abs_nonneg _
  have hD' : D ≤ Ds + |D - Ds| := by have := le_abs_self (D - Ds); linarith
  have p1 := mul_le_mul_of_nonneg_left hD' hδ0
  have p2 := mul_le_mul_of_nonneg_right hδ hX
  have p3 := mul_le_mul_of_nonneg_right e1 hDs
  have p4 := mul_le_mul_of_nonneg_right e2 hDs
  nlinarith

end GlobalTheory
end

section

open Matrix Finset Real

namespace GlobalTheory

theorem moderate_log_factor_absorbed : ∀ Cg : ℝ, ∃ n₀ : ℕ, ∀ (n f q : ℕ) (rd g b : ℝ), n₀ ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → Real.log rd ≤ Real.exp n → Real.log f ≤ Real.sqrt n → 2 ≤ b → Real.log b ≤ Real.exp (1 / 16 * n * f * Real.log n) → 1 ≤ g → g ≤ b ^ Cg → 2 * f * q * (11 * q * Real.log (n * f * rd * g * b)) ≤ Real.exp (1 / 8 * n * f * Real.log n) ∧ 2 * (2 : ℝ) ^ q * Real.exp (-(3 / 8) * n * f * Real.log n) ≤ Real.exp (-(1 / 4) * n * f * Real.log n) := by
  intro Cg
  set K : ℝ := 22 * (|Cg| + 4) with hK
  have hC : 0 ≤ |Cg| := abs_nonneg _
  have hK0 : 0 ≤ K := by positivity
  refine ⟨⌈Real.exp (16 * (1 + K))⌉₊, ?_⟩
  intro n f q rd g b hn hf hq hqn hrd hlrd hlf hb hlb hg hgb
  have hn' : Real.exp (16 * (1 + K)) ≤ (n : ℝ) := Nat.ceil_le.mp hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (Real.one_le_exp (by positivity)) hn'
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 16 * (1 + K) ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hn'
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hqn
  set L := Real.log n with hLdef
  have hm1 : (n : ℝ) ≤ n * f := by nlinarith
  have hm : (1 : ℝ) ≤ n * f := by linarith
  have hX : (n * f : ℝ) * (1 + K) ≤ 1 / 16 * n * f * L := by nlinarith
  have hX1 : (n * f : ℝ) ≤ 1 / 16 * n * f * L := by nlinarith
  have hX2 : (n * f : ℝ) + K ≤ 1 / 16 * n * f * L := by nlinarith
  set E := Real.exp (1 / 16 * n * f * L) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEn : Real.exp n ≤ E := Real.exp_le_exp.mpr (by linarith)
  have hnE : (n : ℝ) ≤ E := by
    have := Real.add_one_le_exp (n : ℝ); linarith
  constructor
  · have hb0 : 0 < b := by linarith
    have hlb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
    have h1 : L ≤ E := by
      have := Real.log_le_sub_one_of_pos hn0; linarith
    have h2 : Real.log f ≤ E := by
      have : Real.sqrt n ≤ n := Real.sqrt_le_iff.mpr ⟨hn0.le, by nlinarith⟩
      linarith
    have h3 : Real.log g ≤ |Cg| * E := by
      have h4 : Real.log g ≤ Real.log (b ^ Cg) := Real.log_le_log (by linarith) hgb
      rw [Real.log_rpow hb0] at h4
      have h5 : Cg * Real.log b ≤ |Cg| * Real.log b :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlb0
      have h6 : |Cg| * Real.log b ≤ |Cg| * E := mul_le_mul_of_nonneg_left hlb hC
      linarith
    have hlog : Real.log (n * f * rd * g * b) ≤ (|Cg| + 4) * E := by
      have hf0 : (0 : ℝ) < f := by linarith
      have hrd0 : 0 < rd := by linarith
      have hg0 : 0 < g := by linarith
      rw [Real.log_mul (by positivity) hb0.ne', Real.log_mul (by positivity) hg0.ne',
        Real.log_mul (by positivity) hrd0.ne', Real.log_mul hn0.ne' hf0.ne']
      linarith
    have hKE : (n * f : ℝ) * K ≤ E := by
      have a1 : (n * f : ℝ) ≤ Real.exp (n * f) := by
        have := Real.add_one_le_exp (n * f : ℝ); linarith
      have a2 : K ≤ Real.exp K := by
        have := Real.add_one_le_exp K; linarith
      calc (n * f : ℝ) * K ≤ Real.exp (n * f) * Real.exp K :=
            mul_le_mul a1 a2 hK0 (Real.exp_pos _).le
        _ = Real.exp (n * f + K) := (Real.exp_add _ _).symm
        _ ≤ E := Real.exp_le_exp.mpr hX2
    have hEE : Real.exp (1 / 8 * n * f * L) = E * E := by
      rw [hE, ← Real.exp_add]; congr 1; ring
    rw [hEE]
    calc 2 * (f : ℝ) * q * (11 * q * Real.log (n * f * rd * g * b))
        = (22 * f * q ^ 2) * Real.log (n * f * rd * g * b) := by ring
      _ ≤ (22 * f * q ^ 2) * ((|Cg| + 4) * E) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (22 * f * n) * ((|Cg| + 4) * E) := by gcongr
      _ = (n * f * K) * E := by rw [hK]; ring
      _ ≤ E * E := by gcongr
  · have hqn2 : (q : ℝ) ≤ n := by nlinarith
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hp : (2 : ℝ) ^ q ≤ Real.exp q := by
      calc (2 : ℝ) ^ q ≤ (Real.exp 1) ^ q := by gcongr
        _ = Real.exp q := by rw [← Real.exp_nat_mul]; simp
    calc 2 * (2 : ℝ) ^ q * Real.exp (-(3 / 8) * n * f * L)
        ≤ Real.exp 1 * Real.exp q * Real.exp (-(3 / 8) * n * f * L) := by gcongr
      _ = Real.exp (1 + q + -(3 / 8) * n * f * L) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end GlobalTheory
end

section

open Matrix Finset Real

namespace GlobalTheory

theorem exists_consecutive_ratio_le_rpow :
    ∀ (a q : ℕ) (τ : ℕ → ℝ), 1 ≤ a → a ≤ q → (∀ i ≤ a, 0 < τ i) → (∀ i < a, τ i < τ (i + 1)) →
      τ a = 1 / 2 → ∃ b < a, τ b / τ (b + 1) ≤ (2 * τ 0) ^ ((1 : ℝ) / q) ∧
        τ b ^ 2 ≤ (2 * τ 0) ^ ((1 : ℝ) / q) / 4 := by
  intro a q τ ha haq hpos hinc hta

  have hmono : ∀ j, j ≤ a → ∀ i, i ≤ j → τ i ≤ τ j := by
    intro j
    induction j with
    | zero => intro _ i hi; rw [Nat.le_zero.mp hi]
    | succ n ih =>
      intro hn i hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact (ih (by omega) i (by omega)).trans (hinc n (by omega)).le
      · rw [le_antisymm hi h]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set x := 2 * τ 0 with hx
  have hx0 : 0 < x := by linarith [hpos 0 (Nat.zero_le _)]
  have hx1 : x ≤ 1 := by linarith [hmono a le_rfl 0 (Nat.zero_le _)]
  set r := x ^ ((1 : ℝ) / q) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hx0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one hx0.le hx1 (by positivity)

  have hrq : r ^ q = x := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, one_div_mul_cancel hqpos.ne',
      Real.rpow_one]
  have hra : x ≤ r ^ a := by rw [← hrq]; exact pow_le_pow_of_le_one hr0.le hr1 haq

  obtain ⟨b, hb, hbr⟩ : ∃ b < a, τ b / τ (b + 1) ≤ r := by
    by_contra hne
    push_neg at hne
    have hstep : ∀ b < a, r * τ (b + 1) < τ b := fun b hb => by
      have h1 := hne b hb
      have h2 := hpos (b + 1) (by omega)
      rwa [lt_div_iff₀ h2] at h1
    have hind : ∀ i, i ≤ a → r ^ i * τ i ≤ τ 0 := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        calc r ^ (n + 1) * τ (n + 1) = r ^ n * (r * τ (n + 1)) := by ring
          _ ≤ r ^ n * τ n :=
            mul_le_mul_of_nonneg_left (hstep n (by omega)).le (pow_nonneg hr0.le _)
          _ ≤ τ 0 := ih (by omega)
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    have hlast : r ^ (c + 1) * τ (c + 1) < τ 0 := by
      calc r ^ (c + 1) * τ (c + 1) = r ^ c * (r * τ (c + 1)) := by ring
        _ < r ^ c * τ c := mul_lt_mul_of_pos_left (hstep c (by omega)) (pow_pos hr0 _)
        _ ≤ τ 0 := hind c (by omega)
    rw [hta] at hlast
    linarith
  refine ⟨b, hb, hbr, ?_⟩
  have hb1 : 0 < τ (b + 1) := hpos (b + 1) (by omega)
  have hb0 : 0 < τ b := hpos b (by omega)
  have hle : τ b ≤ r * τ (b + 1) := by rwa [div_le_iff₀ hb1] at hbr
  have hhalf : τ (b + 1) ≤ 1 / 2 := by rw [← hta]; exact hmono a le_rfl (b + 1) (by omega)
  have htb : τ b ≤ r / 2 := by nlinarith [mul_le_mul_of_nonneg_left hhalf hr0.le]
  nlinarith [mul_le_mul htb htb hb0.le (by linarith), mul_le_mul_of_nonneg_left hr1 hr0.le]

end GlobalTheory
end

section

namespace GlobalTheory.StrictUpperNilpotentFlagMeasures

theorem pow_apply_eq_zero_of_strictUpper {m : ℕ} {X : Matrix (Fin m) (Fin m) ℂ}
    (hX : ∀ i j : Fin m, (j : ℕ) ≤ (i : ℕ) → X i j = 0) (n : ℕ) :
    ∀ i j : Fin m, (j : ℕ) < (i : ℕ) + n → (X ^ n) i j = 0 := by
  induction n with
  | zero =>
    intro i j h
    rw [pow_zero]
    apply Matrix.one_apply_ne
    rintro rfl
    omega
  | succ n ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) < (i : ℕ) + n
    · rw [ih i k hk, zero_mul]
    · rw [hX k j (by omega), mul_zero]

end GlobalTheory.StrictUpperNilpotentFlagMeasures
end

section

namespace GlobalTheory.MatrixExtLast

theorem matrix_ext_last {k : ℕ} {M N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h₁ : ∀ i j : Fin k, M (Fin.castSucc i) (Fin.castSucc j) = N (Fin.castSucc i) (Fin.castSucc j))
    (h₂ : ∀ i : Fin k, M (Fin.castSucc i) (Fin.last k) = N (Fin.castSucc i) (Fin.last k))
    (h₃ : ∀ j : Fin k, M (Fin.last k) (Fin.castSucc j) = N (Fin.last k) (Fin.castSucc j))
    (h₄ : M (Fin.last k) (Fin.last k) = N (Fin.last k) (Fin.last k)) : M = N := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact h₄
    | cast j => exact h₃ j
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact h₂ i
    | cast j => exact h₁ i j

end GlobalTheory.MatrixExtLast
end
