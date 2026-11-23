module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle014
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle007
import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle001
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle008
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle010
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronHorizontalSegmentBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

attribute [local irreducible] qd pYd pJd pNd in
theorem zero_detection_second : Detect1 := by
  intro M _ χ hχ1 T hT hM ρ hρ hρim hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, qd M T = X := ⟨_, rfl⟩
  have hMT : (M : ℝ) * T ≤ X := by rw [← hX]; unfold qd; exact Nat.le_ceil _
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX6 : (6 : ℝ) ≤ X := by nlinarith
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hre0 : 0 < ρ.re := by linarith
  have hNX : X ^ 8 ≤ pNd M T := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pNd pJd
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pYd M T = X ^ 3 := by unfold pYd; rw [hX]
  have hYN : pYd M T ≤ pNd M T := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pYd M T := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pNd M T := le_trans hY1 hYN
  have hB := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ1
  have hP := Formalism.FX.l_function_partial_sum M χ hχ1 _ hB ρ hre0 (pNd M T) hN1
  rw [hL, zero_sub, norm_neg] at hP
  have hMI := mollifier_identity M χ ρ (pYd M T) (pNd M T) (pYd M T * pNd M T) hY1 hYN le_rfl
  have hMo := mollM_norm_le χ ρ hre0.le (pYd M T)
  set P := ∑ n ∈ Icc 1 (pNd M T), χ (n : ZMod M) * (n : ℂ) ^ (-ρ) with hPdef
  set Mo := ∑ d ∈ Icc 1 (pYd M T), (((ArithmeticFunction.moebius d : ℤ)) : ℂ) * χ (d : ZMod M) * (d : ℂ) ^ (-ρ)
    with hMdef
  set D := ∑ n ∈ Ioc (pYd M T) (pYd M T * pNd M T), mco (pYd M T) (pNd M T) n * χ (n : ZMod M) * (n : ℂ) ^ (-ρ)
    with hD
  have hnum : ‖P‖ * (pYd M T : ℝ) ≤ 1 / 2 := by
    have hXpos : (0 : ℝ) < X := by linarith
    have hNpos : (0 : ℝ) < pNd M T := by exact_mod_cast hN1
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * T := by
      have h1 : ‖ρ‖ ≤ ρ.re + T := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + T / ρ.re := by
        rw [div_le_iff₀ hre0, add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : T / ρ.re ≤ 4 / 3 * T := by
        rw [div_le_iff₀ hre0]; nlinarith
      linarith
    have hpow : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pNd M T : ℝ) := by exact_mod_cast hNX
    have hpow2 : (X : ℝ) ^ (6 : ℕ) ≤ ((pNd M T : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (3 / 4 : ℝ) = (X : ℝ) ^ (6 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, ← Real.rpow_natCast]
        norm_num
      rw [← e]
      exact Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pYd M T : ℝ) = (X : ℝ) ^ (3 : ℕ) := by rw [hY, Nat.cast_pow]
    have hc : 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 8 * X := by
      have hpos : (0 : ℝ) ≤ 1 + ‖ρ‖ / ρ.re := by positivity
      calc 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 2 * ((M : ℝ) + 1) * (3 * T) :=
            mul_le_mul_of_nonneg_left hrho (by positivity)
        _ ≤ 8 * X := by nlinarith
    have hPle : ‖P‖ ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := by
      refine hP.trans ?_
      have a3 : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := hpow.trans hinv
      calc 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 8 * X * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P‖ * (X : ℝ) ^ (3 : ℕ) ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) * (X : ℝ) ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 8 / X ^ 2 := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          field_simp
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
  have h1D : ‖1 + D‖ ≤ 1 / 2 := by
    rw [← hMI, norm_mul]
    calc ‖P‖ * ‖Mo‖ ≤ ‖P‖ * (pYd M T : ℝ) := mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
      _ ≤ 1 / 2 := hnum
  have hDge : 1 / 2 ≤ ‖D‖ := by
    have := norm_sub_le (1 + D) D
    simp only [add_sub_cancel_right, norm_one] at this
    linarith
  have hsplit : D = ∑ j ∈ range (pJd M T),
      blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ := by
    rw [hD, show pNd M T = 2 ^ pJd M T by unfold pNd; rfl, sum_blocks]
    rfl
  by_contra hcon
  push Not at hcon
  have hJ8 : 8 ≤ pJd M T := by unfold pJd; omega
  have hJpos : (0 : ℝ) < pJd M T := by exact_mod_cast (by omega : 0 < pJd M T)
  have hlt : ‖D‖ < 1 / 2 := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    have hne : (range (pJd M T)).Nonempty := nonempty_range_iff.mpr (by omega)
    calc ∑ j ∈ range (pJd M T), ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ‖
        < ∑ j ∈ range (pJd M T), 1 / (2 * (pJd M T : ℝ)) := sum_lt_sum_of_nonempty hne hcon
      _ = 1 / 2 := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

section

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_left_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ T' B : ℝ) (hy : 1 ≤ y)
    (hσ : 1 / 2 ≤ σ₁) (hσ1 : σ₁ < 1) (hT' : 0 ≤ T')
    (hB : ∀ t : ℝ, |t| ≤ T' → ‖negLD χ ((σ₁ : ℂ) + t * I)‖ ≤ B) :
    ‖∫ t in (-T')..T', Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ 2 * T' * B * y ^ σ₁ / (σ₁ * (1 - σ₁)) := by
  have hy0 : 0 < y := by linarith
  have hσp : 0 < σ₁ := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simpa using hT'))
  have hpt : ∀ t ∈ Set.uIoc (-T') T', ‖Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ B * y ^ σ₁ / (σ₁ * (1 - σ₁)) := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hBt := hB t (abs_le.mpr ⟨ht.1.le, ht.2⟩)
    set w : ℂ := (σ₁ : ℂ) + (t : ℂ) * I with hw
    have hre : w.re = σ₁ := by simp [hw]
    rw [norm_perron_integrand_eq χ y hy0 w, hre]
    have hw1 : σ₁ ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w
      rw [hre, abs_of_pos hσp] at this; exact this
    have hw2 : 1 - σ₁ ≤ ‖w - 1‖ := by
      have h1 : (w - 1).re = σ₁ - 1 := by simp [hre]
      have := Complex.abs_re_le_norm (w - 1)
      rw [h1, abs_of_neg (by linarith)] at this; linarith
    have hden : σ₁ * (1 - σ₁) ≤ ‖w‖ * ‖w - 1‖ :=
      mul_le_mul hw1 hw2 (by linarith) (norm_nonneg _)
    have hdp : 0 < σ₁ * (1 - σ₁) := mul_pos hσp (by linarith)
    have hyp : 0 ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le _
    calc ‖negLD χ w‖ * y ^ σ₁ / (‖w‖ * ‖w - 1‖)
        ≤ B * y ^ σ₁ / (‖w‖ * ‖w - 1‖) := by gcongr
      _ ≤ B * y ^ σ₁ / (σ₁ * (1 - σ₁)) :=
          div_le_div_of_nonneg_left (mul_nonneg hB0 hyp) hdp hden
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine h.trans (le_of_eq ?_)
  have : |T' - -T'| = 2 * T' := by rw [abs_of_nonneg (by linarith)]; ring
  rw [this]; ring

theorem ex_horiz_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ σ₀ v B : ℝ) (hy : 1 ≤ y)
    (hσ : σ₁ ≤ σ₀) (hv : 1 ≤ |v|) (hB0 : 0 ≤ B)
    (hB : ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₀ → ‖negLD χ ((x : ℂ) + v * I)‖ ≤ B) :
    ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + v * I)‖ ≤ (σ₀ - σ₁) * B * y ^ σ₀ / v ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hpt : ∀ x ∈ Set.uIoc σ₁ σ₀, ‖Fchi χ y ((x : ℂ) + v * I)‖ ≤ B * y ^ σ₀ / v ^ 2 := by
    intro x hx
    rw [Set.uIoc_of_le hσ] at hx
    have hBx := hB x hx.1.le hx.2
    set w : ℂ := (x : ℂ) + (v : ℂ) * I with hw
    have hre : w.re = x := by simp [hw]
    have him : w.im = v := by simp [hw]
    rw [norm_perron_integrand_eq χ y hy0 w, hre]
    have hw1 : |v| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
    have hw2 : |v| ≤ ‖w - 1‖ := by
      have : (w - 1).im = v := by simp [him]
      rw [← this]; exact Complex.abs_im_le_norm _
    have hpow : y ^ x ≤ y ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hy hx.2
    have hden : v ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
      rw [← sq_abs]; nlinarith [abs_nonneg v]
    have htp : 0 < v ^ 2 := by rw [← sq_abs]; positivity
    have hyp : 0 ≤ y ^ σ₀ := Real.rpow_nonneg hy0.le _
    calc ‖negLD χ w‖ * y ^ x / (‖w‖ * ‖w - 1‖)
        ≤ B * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by gcongr
      _ ≤ B * y ^ σ₀ / v ^ 2 := div_le_div_of_nonneg_left (mul_nonneg hB0 hyp) htp hden
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine h.trans (le_of_eq ?_)
  rw [abs_of_nonneg (by linarith)]; ring

theorem ex_tail_half (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T)
    (hf : ∀ t : ℝ, T < t → ‖f t‖ ≤ K / t ^ 2) :
    ‖∫ t in Set.Ioi T, f t‖ ≤ K / T := by
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => K * t ^ (-2 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul K
  have h := MeasureTheory.norm_integral_le_of_norm_le (μ := MeasureTheory.volume.restrict (Set.Ioi T))
    (f := f) hint
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => by
      have ht0 : 0 < t := lt_trans hT ht
      have := hf t ht
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
      simpa [div_eq_mul_inv] using this)))
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
  have : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  field_simp

theorem ex_tail_gen (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T) (hi : MeasureTheory.Integrable f)
    (hf : ∀ t : ℝ, T < |t| → ‖f t‖ ≤ K / t ^ 2) :
    ‖(∫ t : ℝ, f t) - ∫ t in (-T)..T, f t‖ ≤ 2 * K / T := by
  have h1 : (∫ t in Set.Iic (-T), f t) + ∫ t in Set.Ioi (-T), f t = ∫ t : ℝ, f t :=
    intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn
  have h2 : (∫ t in (-T)..T, f t) + ∫ t in Set.Ioi T, f t = ∫ t in Set.Ioi (-T), f t :=
    intervalIntegral.integral_interval_add_Ioi hi.integrableOn hi.integrableOn
  have h3 : (∫ t in Set.Ioi T, f (-t)) = ∫ t in Set.Iic (-T), f t := integral_comp_neg_Ioi T f
  have e : (∫ t : ℝ, f t) - ∫ t in (-T)..T, f t
      = (∫ t in Set.Ioi T, f (-t)) + ∫ t in Set.Ioi T, f t := by
    rw [← h1, ← h2, h3]; ring
  rw [e]
  have a := ex_tail_half (fun t => f (-t)) K T hT (fun t ht => by
    have := hf (-t) (by rw [abs_neg]; exact lt_of_lt_of_le ht (le_abs_self t))
    simpa using this)
  have b := ex_tail_half f K T hT (fun t ht => hf t (lt_of_lt_of_le ht (le_abs_self t)))
  calc _ ≤ ‖∫ t in Set.Ioi T, f (-t)‖ + ‖∫ t in Set.Ioi T, f t‖ := norm_add_le _ _
    _ ≤ K / T + K / T := add_le_add a b
    _ = 2 * K / T := by ring

theorem ex_tail_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₀ T' : ℝ),
    1 ≤ y → 1 < σ₀ → 1 ≤ T' →
    ‖(∫ t : ℝ, Fchi χ y ((σ₀ : ℂ) + t * I)) - ∫ t in (-T')..T', Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤
      2 * (1 / (σ₀ - 1) + C) * y ^ σ₀ / T' := by
  obtain ⟨C, hC, hR⟩ := l_log_deriv_right
  refine ⟨C, hC, ?_⟩
  intro M _ χ y σ₀ T' hy hσ hT'
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T' := by linarith
  obtain ⟨hint, -⟩ := perron_formula_character M χ y hy σ₀ hσ
  have h := ex_tail_gen (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) ((1 / (σ₀ - 1) + C) * y ^ σ₀) T' hT0 hint
    (fun t ht => by
      have ht0 : 0 < |t| := lt_trans hT0 ht
      show ‖Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤ _
      set w : ℂ := (σ₀ : ℂ) + (t : ℂ) * I with hw
      have hre : w.re = σ₀ := by simp [hw]
      have him : w.im = t := by simp [hw]
      rw [norm_perron_integrand_eq χ y hy0 w, hre]
      have hζ : ‖negLD χ w‖ ≤ 1 / (σ₀ - 1) + C := by
        have := hR M χ w (by rw [hre]; exact hσ)
        rwa [hre] at this
      have hw1 : |t| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
      have hw2 : |t| ≤ ‖w - 1‖ := by
        have : (w - 1).im = t := by simp [him]
        rw [← this]; exact Complex.abs_im_le_norm _
      have hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
        rw [← sq_abs]; nlinarith [abs_nonneg t]
      have htp : 0 < t ^ 2 := by rw [← sq_abs]; positivity
      have hnum : 0 ≤ 1 / (σ₀ - 1) + C := le_trans (norm_nonneg _) hζ
      have hyp : 0 ≤ y ^ σ₀ := Real.rpow_nonneg hy0.le _
      calc ‖negLD χ w‖ * y ^ σ₀ / (‖w‖ * ‖w - 1‖)
          ≤ (1 / (σ₀ - 1) + C) * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by gcongr
        _ ≤ (1 / (σ₀ - 1) + C) * y ^ σ₀ / t ^ 2 :=
            div_le_div_of_nonneg_left (mul_nonneg hnum hyp) htp hden)
  refine h.trans (le_of_eq ?_)
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
