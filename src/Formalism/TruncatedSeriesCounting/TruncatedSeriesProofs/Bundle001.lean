module

public import Formalism.TruncatedSeriesCounting.Bundle001
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

open Finset

private theorem geom_sum_range_mul_one_sub (x : ℝ) :
    ∀ n : ℕ, Finset.sum (range n) (fun i => x ^ i) * (1 - x) = 1 - x ^ n := fun
  | 0 => by simp
  | n + 1 => by rw [sum_range_succ, add_mul, geom_sum_range_mul_one_sub x n, pow_succ]; ring

theorem tsum_le_two_level (x A B D : ℝ) (j : ℕ) (f : ℕ → ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hA0 : 0 ≤ A) (hf0 : ∀ a, 0 ≤ f a) (hfB : ∀ a, f a ≤ (B + D) * x ^ a)
    (hfA : ∀ a, a < j → f a ≤ (A + D) * x ^ a) :
    ∑' a, f a ≤ (A + B * x ^ j + D) * (1 - x)⁻¹ := by
  have hx1' : 0 < 1 - x := by linarith
  have hgeo : Summable (fun a : ℕ => (B + D) * x ^ a) :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left (B + D)
  have hsum : Summable f := Summable.of_nonneg_of_le hf0 hfB hgeo
  have hsplit : Finset.sum (range j) f + ∑' a, f (a + j) = ∑' a, f a := by
    exact hsum.sum_add_tsum_nat_add j
  have hshift : Summable (fun a => f (a + j)) := by
    exact (summable_nat_add_iff j).mpr hsum
  have hg2 : HasSum (fun a : ℕ => (B + D) * x ^ j * x ^ a) ((B + D) * x ^ j * (1 - x)⁻¹) :=
    (hasSum_geometric_of_lt_one hx0 hx1).mul_left _
  have h2 : ∑' a, f (a + j) ≤ (B + D) * x ^ j * (1 - x)⁻¹ :=
    hasSum_le (fun a => by
      calc f (a + j) ≤ (B + D) * x ^ (a + j) := hfB (a + j)
        _ = (B + D) * x ^ j * x ^ a := by rw [pow_add]; ring) hshift.hasSum hg2
  have h1 : Finset.sum (range j) f ≤ (A + D) * Finset.sum (range j) (fun a => x ^ a) := by
    rw [mul_sum]
    exact sum_le_sum fun a ha => hfA a (mem_range.mp ha)
  have hS' : Finset.sum (range j) (fun a => x ^ a) = (1 - x ^ j) * (1 - x)⁻¹ := by
    rw [← geom_sum_range_mul_one_sub x j, mul_assoc, mul_inv_cancel₀ hx1'.ne', mul_one]
  have hpos : 0 ≤ A * x ^ j * (1 - x)⁻¹ :=
    mul_nonneg (mul_nonneg hA0 (pow_nonneg hx0 _)) (inv_nonneg.mpr hx1'.le)
  rw [← hsplit]
  calc Finset.sum (range j) f + ∑' a, f (a + j)
      ≤ (A + D) * Finset.sum (range j) (fun a => x ^ a) + (B + D) * x ^ j * (1 - x)⁻¹ :=
        add_le_add h1 h2
    _ = (A + B * x ^ j + D) * (1 - x)⁻¹ - A * x ^ j * (1 - x)⁻¹ := by rw [hS']; ring
    _ ≤ (A + B * x ^ j + D) * (1 - x)⁻¹ := by linarith

theorem rr_arith (l d G h y C L s r q : ℝ) (hld : l = d + 1) (hd2 : 2 ≤ d) (hG0 : 0 ≤ G)
    (hh0 : 0 ≤ h) (hy0 : 0 ≤ y) (hC0 : 0 ≤ C) (hCL : C ≤ 3 + L) (hL0 : 0 ≤ L)
    (hq : q = d / (d - 1)) (hsA : s ≤ (2 * G + 2 * h * y + C + 3) * q)
    (hr : r ≤ s * l / d ^ 2 + C) : r ≤ 20 * (G / l + h * y / d + L + 1) := by
  subst hld
  subst hq
  have hd1 : 0 < d - 1 := by linarith
  have hd0 : 0 < d := by linarith
  have hl0 : 0 < d + 1 := by linarith
  have hdd : 0 < (d - 1) * d := mul_pos hd1 hd0
  have hst : s * (d + 1) / d ^ 2 ≤ (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) := by
    have h1 : s * (d + 1) / d ^ 2 ≤ (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2 := by
      have e : (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2 - s * (d + 1) / d ^ 2
          = ((2 * G + 2 * h * y + C + 3) * (d / (d - 1)) - s) * ((d + 1) / d ^ 2) := by ring
      have : 0 ≤ ((2 * G + 2 * h * y + C + 3) * (d / (d - 1)) - s) * ((d + 1) / d ^ 2) :=
        mul_nonneg (by linarith) (div_nonneg hl0.le (sq_nonneg d))
      linarith
    have h2 : (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2
        = (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) := by
      have hd1' : d - 1 ≠ 0 := hd1.ne'
      have hd0' : d ≠ 0 := hd0.ne'
      field_simp
    linarith
  have ht0 : 0 ≤ (d + 1) / ((d - 1) * d) := div_nonneg hl0.le hdd.le
  have htc : (d + 1) / ((d - 1) * d) ≤ 3 / 2 := by
    have key : d + 1 ≤ 3 / 2 * ((d - 1) * d) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - 2) (by linarith : (0:ℝ) ≤ 3 * d + 1)]
    exact (div_le_iff₀ hdd).mpr key
  have htG : (d + 1) / ((d - 1) * d) ≤ 10 / (d + 1) := by
    have key : (d + 1) * (d + 1) ≤ 10 * ((d - 1) * d) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - 2) (by linarith : (0:ℝ) ≤ 9 * d + 6)]
    exact (div_le_div_iff₀ hdd hl0).mpr key
  have hth : (d + 1) / ((d - 1) * d) ≤ 3 / d := by
    have key : (d + 1) * d ≤ 3 * ((d - 1) * d) := by
      nlinarith [mul_nonneg hd0.le (by linarith : (0:ℝ) ≤ d - 2)]
    exact (div_le_div_iff₀ hdd hd0).mpr key
  have e1 : 2 * G * ((d + 1) / ((d - 1) * d)) ≤ 20 * (G / (d + 1)) := by
    calc 2 * G * ((d + 1) / ((d - 1) * d)) ≤ 2 * G * (10 / (d + 1)) :=
          mul_le_mul_of_nonneg_left htG (by linarith)
      _ = 20 * (G / (d + 1)) := by ring
  have hhy : 0 ≤ h * y := mul_nonneg hh0 hy0
  have e2 : 2 * h * y * ((d + 1) / ((d - 1) * d)) ≤ 20 * (h * y / d) := by
    have hq0 : 0 ≤ h * y / d := div_nonneg hhy hd0.le
    calc 2 * h * y * ((d + 1) / ((d - 1) * d)) = 2 * (h * y) * ((d + 1) / ((d - 1) * d)) := by ring
      _ ≤ 2 * (h * y) * (3 / d) := mul_le_mul_of_nonneg_left hth (by linarith)
      _ = 6 * (h * y / d) := by ring
      _ ≤ 20 * (h * y / d) := by linarith
  have e3 : (C + 3) * ((d + 1) / ((d - 1) * d)) ≤ (C + 3) * (3 / 2) :=
    mul_le_mul_of_nonneg_left htc (by linarith)
  have expand : (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) + C
      = 2 * G * ((d + 1) / ((d - 1) * d)) + 2 * h * y * ((d + 1) / ((d - 1) * d))
        + (C + 3) * ((d + 1) / ((d - 1) * d)) + C := by ring
  linarith

theorem remainder_bound_of_tsum : RrBound := by
  intro ℓ hℓ n _ H G h j cut s r hh hH hG hs hr
  have hL3 : (3:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ
  have hb : (1:ℝ) < (ℓ:ℝ) := by linarith
  have hh1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hlog0 : 0 ≤ Real.logb ℓ (2 * h + 1) := Real.logb_nonneg hb (by linarith)
  have hceil := Nat.ceil_lt_add_one (R := ℝ) (a := 1 + Real.logb ℓ (2 * h + 1)) (by linarith)
  have hlog3 : Real.logb ℓ 3 ≤ 1 := by
    rw [← Real.logb_self_eq_one hb]
    exact (Real.logb_le_logb hb (by norm_num) (by linarith)).mpr hL3
  have hlogmul : Real.logb ℓ (2 * h + 1) ≤ Real.logb ℓ 3 + Real.logb ℓ h := by
    rw [← Real.logb_mul (by norm_num) (by linarith)]
    exact (Real.logb_le_logb hb (by linarith) (by nlinarith)).mpr (by linarith)
  have hL0 : 0 ≤ Real.logb ℓ h := Real.logb_nonneg hb hh1
  have hC0 : (0:ℝ) ≤ (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) := Nat.cast_nonneg _
  have hCL : (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) ≤ 3 + Real.logb ℓ h := by linarith
  have hd2 : (2:ℝ) ≤ (ℓ:ℝ) - 1 := by linarith
  have hdpos : (0:ℝ) < (ℓ:ℝ) - 1 := by linarith
  have hx0 : (0:ℝ) ≤ 1 / ((ℓ:ℝ) - 1) := by positivity
  have hx1 : 1 / ((ℓ:ℝ) - 1) < 1 := by rw [div_lt_one hdpos]; linarith
  have hser := tsum_le_two_level (1 / ((ℓ:ℝ) - 1)) (2 * G) (2 * h)
    ((⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) + 3) j
    (fun a : ℕ => ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ) +
        (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) + 3) / ((ℓ : ℝ) - 1) ^ a)
    hx0 hx1 (by positivity) (fun a => by positivity)
    (fun a => by
      have h' : ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ)) ≤ 2 * h := by
        exact_mod_cast hH (cut + ((a + 1 : ℕ) : ZMod n))
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hdpos.le a))
    (fun a ha => by
      have h' : ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ)) ≤ 2 * G := by
        exact_mod_cast hG (a + 1) (by omega) (by omega)
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hdpos.le a))
  have hsA := hs.trans hser
  have hq : (1 - 1 / ((ℓ:ℝ) - 1))⁻¹ = ((ℓ:ℝ) - 1) / ((ℓ:ℝ) - 1 - 1) := by
    have hd0 : (ℓ:ℝ) - 1 ≠ 0 := by linarith
    have hd1 : (ℓ:ℝ) - 1 - 1 ≠ 0 := by linarith
    field_simp
  have hyd : (h:ℝ) / ((ℓ:ℝ) - 1) ^ (j + 1) =
      (h:ℝ) * (1 / ((ℓ:ℝ) - 1)) ^ j / ((ℓ:ℝ) - 1) := by
    have hd0 : (ℓ:ℝ) - 1 ≠ 0 := by linarith
    rw [pow_succ, one_div_pow]
    field_simp
  rw [hyd]
  have key := rr_arith (ℓ:ℝ) ((ℓ:ℝ) - 1) (G:ℝ) (h:ℝ) ((1 / ((ℓ:ℝ) - 1)) ^ j)
    (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) (Real.logb ℓ h) s r
    (1 - 1 / ((ℓ:ℝ) - 1))⁻¹ (by ring) hd2 (Nat.cast_nonneg _) (by linarith)
    (pow_nonneg hx0 j) hC0 hCL hL0 hq (by linarith) hr
  exact key

end Formalism.TruncatedSeriesCounting.WachCoordinates
end
end

section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

private lemma sigma_exponent_le_real (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (g h j : ℕ) (hj : 1 ≤ j) :
    (sigE ℓ g h j : ℝ) ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hjm : m + 1 - 1 = m := by omega
  unfold sigE
  rw [hjm]
  have hL : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (2 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hq0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hq2 : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hA0 : (0 : ℝ) ≤ (h : ℝ) + 2 * g := by positivity
  have hP1 : (1 : ℝ) ≤ (ℓ : ℝ) ^ m := one_le_pow₀ (by linarith)
  have hPq : ((ℓ : ℝ) - 1) ^ m ≤ (ℓ : ℝ) ^ m := pow_le_pow_left₀ hq0.le (by linarith) m
  have hP0 : (0 : ℝ) < (ℓ : ℝ) ^ m := by linarith
  have hM : (Mpar ℓ g h : ℝ) ≤ ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1 := by
    unfold Mpar
    push_cast
    have hc : (((ℓ - 1 : ℕ)) : ℝ) = (ℓ : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    have := Nat.cast_div_le (α := ℝ) (m := h + 2 * g) (n := ℓ - 1)
    rw [hc] at this
    push_cast at this
    linarith
  have hM0 : (0 : ℝ) ≤ (Mpar ℓ g h : ℝ) := by positivity
  have hr : (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 ≤ 3 / 4 := by
    rw [div_le_iff₀ hq2]
    nlinarith
  have hr0 : (0 : ℝ) ≤ (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have hX0 : (0 : ℝ) ≤ ((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ m) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1 := by
    positivity
  have hceil := Nat.ceil_lt_add_one hX0
  have e1 : ((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ m) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
      3 * g * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) +
        (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
    field_simp
  have t1 : 3 * g * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) ≤ 9 / 4 * g := by nlinarith
  have t2 : (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (m + 1 + 1) + 3 / 4 := by
    have hB : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ (m + 1 + 1) := by positivity
    have s1 : (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤
        (((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
      gcongr
    have s2 : (((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m =
        ((h : ℝ) + 2 * g) * ℓ / (((ℓ : ℝ) - 1) ^ 3 * (ℓ : ℝ) ^ m) +
          ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
      field_simp
    have s3 : ((h : ℝ) + 2 * g) * ℓ / (((ℓ : ℝ) - 1) ^ 3 * (ℓ : ℝ) ^ m) ≤
        3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (m + 1 + 1) := by
      rw [div_le_div_iff₀ (by positivity) hB]
      have k1 : (ℓ : ℝ) * ((ℓ : ℝ) - 1) ^ m ≤ 3 / 2 * ((ℓ : ℝ) - 1) * (ℓ : ℝ) ^ m := by
        have : (ℓ : ℝ) ≤ 3 / 2 * ((ℓ : ℝ) - 1) := by linarith
        calc (ℓ : ℝ) * ((ℓ : ℝ) - 1) ^ m ≤ 3 / 2 * ((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 1) ^ m :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ 3 / 2 * ((ℓ : ℝ) - 1) * (ℓ : ℝ) ^ m :=
              mul_le_mul_of_nonneg_left hPq (by positivity)
      have k2 := mul_le_mul_of_nonneg_left k1 (mul_nonneg hA0 hq2.le)
      have e2 : ((ℓ : ℝ) - 1) ^ (m + 1 + 1) = ((ℓ : ℝ) - 1) ^ m * ((ℓ : ℝ) - 1) ^ 2 := by ring
      rw [e2]
      nlinarith [k2]
    have s4 : ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤ 3 / 4 := by
      rw [div_le_iff₀ hP0]
      nlinarith
    linarith
  rw [e1] at hceil ⊢
  linarith

theorem total_exponent_le_eight_hundred : ExponentBoundOfRankAndKappaBounds := by
  intro ℓ hℓ G g h j ell rr kap hj hG hg hgh hell hrr hkap
  have hσ := sigma_exponent_le_real ℓ hℓ g h j hj
  unfold eE a0E
  have hL : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (2 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hB4 : (4 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ (j + 1) := by
    have := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (ℓ : ℝ) - 1) (by omega : 2 ≤ j + 1)
    nlinarith
  have hB0 : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ (j + 1) := by linarith
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hGg : (G : ℝ) ≤ g := by exact_mod_cast hG
  have hgh' : (g : ℝ) ≤ h := by exact_mod_cast hgh
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hT : (0 : ℝ) ≤ (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) := by positivity
  have hΛ : (0 : ℝ) ≤ Real.logb ℓ h := Real.logb_nonneg (by linarith) hh1
  have hlog2 : Real.logb ℓ (2 * h) = Real.logb ℓ 2 + Real.logb ℓ h :=
    Real.logb_mul (by norm_num) (by positivity)
  have hl2 : Real.logb ℓ 2 ≤ 1 := by
    have := Real.logb_le_logb_of_le (by linarith : (1 : ℝ) < ℓ) (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ ℓ)
    rwa [Real.logb_self_eq_one (by linarith)] at this
  have hGL : (G : ℝ) / ℓ ≤ g / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hgB : (g : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) ≤ g / 4 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hB4
  have h4g : 4 * (g : ℝ) / ((ℓ : ℝ) - 1) ≤ 2 * g := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have eσ : 3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) =
      3 / 2 * ((h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1)) + 3 * ((g : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1)) := by
    ring
  rw [eσ] at hσ
  rw [hlog2] at hkap
  have hge : (g : ℝ) ≤ g * ell := by nlinarith
  have hee : (ell : ℝ) ≤ g * ell := by nlinarith
  have h1e : (1 : ℝ) ≤ g * ell := by nlinarith
  nlinarith

end Formalism.TruncatedSeriesCounting.WachCoordinates
end
end

section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

private lemma log_nat_le (h : ℕ) : Real.log h ≤ (h : ℝ) / 1000 + 998 := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp
  · have hx : (0 : ℝ) < h := by exact_mod_cast hpos
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < h / 1000 by positivity)
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1000 by norm_num)
    rw [Real.log_div hx.ne' (by norm_num)] at h1
    linarith

private lemma mpar_le (ℓ g h : ℕ) (hℓ : 11 ≤ ℓ) :
    (Mpar ℓ g h : ℝ) ≤ ((h:ℝ) + 2 * g) / 10 + 1 := by
  have hk : (10 : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 ≤ ℓ - 1)
  have h1 : (((h + 2 * g) / (ℓ - 1) : ℕ) : ℝ) ≤ ((h + 2 * g : ℕ) : ℝ) / ((ℓ - 1 : ℕ) : ℝ) := Nat.cast_div_le
  have h2 : ((h + 2 * g : ℕ) : ℝ) / ((ℓ - 1 : ℕ) : ℝ) ≤ ((h + 2 * g : ℕ) : ℝ) / 10 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hk
  have h3 := h1.trans h2
  rw [Mpar, Nat.cast_add, Nat.cast_one]
  push_cast at h3 ⊢
  linarith

private lemma sig_lt (ℓ g h j : ℕ) (hℓ : 11 ≤ ℓ) :
    (sigE ℓ g h j : ℝ) < 11 / 100 * (3 * (g:ℝ) + ((h:ℝ) + 2 * g) / 10 + 1) + 2 := by
  unfold sigE
  have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hM := mpar_le ℓ g h hℓ
  have hM0 : (0 : ℝ) ≤ Mpar ℓ g h := Nat.cast_nonneg _
  have hpow : (1 : ℝ) ≤ (ℓ : ℝ) ^ (j - 1) := one_le_pow₀ (by linarith)
  have hq : (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ (j - 1) ≤ Mpar ℓ g h := div_le_self hM0 hpow
  have hfrac : (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 ≤ 11 / 100 := by
    rw [div_le_iff₀ (pow_pos (by linarith) 2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (by linarith : (0 : ℝ) ≤ 11 * ℓ - 1)]
  set A := 3 * (g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ (j - 1) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hx0 : 0 ≤ A * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1 := by positivity
  have hc := Nat.ceil_lt_add_one hx0
  have hAl : A * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤ A * (11 / 100) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hfrac hA0
  have hA : A ≤ 3 * g + ((h : ℝ) + 2 * g) / 10 + 1 := by rw [hAdef]; linarith
  linarith

private lemma rr_le (ℓ G h j : ℕ) (rr : ℝ) (hℓ : 11 ≤ ℓ) (hj : 1 ≤ j)
    (hrr : rr ≤ 20 * ((G : ℝ) / ℓ + (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) + Real.logb ℓ h + 1)) :
    rr ≤ 20 * ((G : ℝ) / 11 + (h : ℝ) / 100 + ((h : ℝ) / 1000 + 998) + 1) := by
  have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h1 : (G : ℝ) / ℓ ≤ G / 11 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hl
  have hp : (100 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ (j + 1) := by
    have h10 : (10 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
    calc (100 : ℝ) = 10 ^ 2 := by norm_num
      _ ≤ ((ℓ : ℝ) - 1) ^ 2 := by gcongr
      _ ≤ ((ℓ : ℝ) - 1) ^ (j + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have h2 : (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) ≤ h / 100 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hp
  have hlog0 : 0 ≤ Real.log h := Real.log_natCast_nonneg h
  have hlogl : 1 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have h3 : Real.logb ℓ h ≤ Real.log h := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h4 := log_nat_le h
  linarith

theorem exists_constant_exponent_inequalities : AprimeArith := by
  refine ⟨100000, by norm_num, ?_⟩
  intro ℓ hℓ b w S η j ell b₀ b₁ rr hj hC hell hb0 hb0' hb1 hb1' hrr
  have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hG0 : (0 : ℝ) ≤ ((w + S + η : ℕ) : ℝ) := Nat.cast_nonneg _
  have hjG : (0 : ℝ) ≤ (j : ℝ) * ((w + S + η : ℕ) : ℝ) := by positivity
  have hbig : (200000 : ℝ) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b := by nlinarith
  have hbG : w + S + η + 1 < b := by
    have : (((w + S + η + 1 : ℕ)) : ℝ) < b := by push_cast at hbig ⊢; linarith
    exact_mod_cast this
  have hb1r : (b : ℝ) ≤ b₁ := by exact_mod_cast hb1
  have hb0r : (b₀ : ℝ) ≤ b + η := by exact_mod_cast hb0'
  have hηG : (η : ℝ) ≤ ((w + S + η : ℕ) : ℝ) := by exact_mod_cast (by omega : η ≤ w + S + η)
  have hlb : (11 : ℝ) * b₁ ≤ ℓ * b₁ := mul_le_mul_of_nonneg_right hl (by positivity)
  refine ⟨by omega, by omega, by linarith, by linarith, ?_⟩
  have hs := sig_lt ℓ (max (w + S + η) 1) (b + η + S) j hℓ
  have hr := rr_le ℓ (w + S + η) (b + η + S) j rr hℓ hj hrr
  have hg : ((max (w + S + η) 1 : ℕ) : ℝ) ≤ ((w + S + η : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : max (w + S + η) 1 ≤ w + S + η + 1)
  have hg0 : (0 : ℝ) ≤ ((max (w + S + η) 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hellr : (ell : ℝ) ≤ 3 * j + 1 := by exact_mod_cast hell
  have hge : ((max (w + S + η) 1 : ℕ) : ℝ) * ell ≤ (((w + S + η : ℕ) : ℝ) + 1) * (3 * j + 1) :=
    mul_le_mul hg hellr (Nat.cast_nonneg _) (by positivity)
  have hH : ((b + η + S : ℕ) : ℝ) ≤ b + ((w + S + η : ℕ) : ℝ) := by
    exact_mod_cast (by omega : b + η + S ≤ b + (w + S + η))
  unfold a0E
  nlinarith
end WachCoordinates
end TruncatedSeriesCounting
end Formalism
end
end

section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

open PowerSeries

theorem mem_span_of_X_pow_mul : CancelQ := by
  intro O _ _ a η b g hg
  rw [Ideal.mem_span_pair] at hg ⊢
  obtain ⟨F, G, hFG⟩ := hg
  have hX : (X : PowerSeries O) ^ η ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  by_cases ha : a = 0
  · subst ha
    refine ⟨0, G, ?_⟩
    have h1 : (X : PowerSeries O) ^ η * (G * X ^ b) = X ^ η * g := by
      rw [← hFG, map_zero, mul_zero, zero_add, pow_add]
      ring
    rw [zero_mul, zero_add]
    exact mul_left_cancel₀ hX h1
  · have hdvd : (X : PowerSeries O) ^ η ∣ F := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      have h1 : (X : PowerSeries O) ^ η ∣ F * C a := by
        have h0 : F * C a = X ^ η * (g - G * X ^ b) := by
          rw [mul_sub, ← hFG, pow_add]
          ring
        rw [h0]
        exact dvd_mul_right _ _
      rw [PowerSeries.X_pow_dvd_iff] at h1
      have h2 := h1 m hm
      rw [mul_comm, PowerSeries.coeff_C_mul] at h2
      exact (mul_eq_zero.mp h2).resolve_left ha
    obtain ⟨F', rfl⟩ := hdvd
    refine ⟨F', G, ?_⟩
    apply mul_left_cancel₀ hX
    rw [← hFG, pow_add]
    ring

end Formalism.TruncatedSeriesCounting.R9
end
end
