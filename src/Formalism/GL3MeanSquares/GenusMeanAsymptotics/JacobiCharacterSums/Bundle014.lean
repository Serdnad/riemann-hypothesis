module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle003
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle005
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle001
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle008
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
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

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem charSum_le (hχ : χ ≠ 1) (m : ℕ) : ‖∑ n ∈ Ioc 0 m, χ (n : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have e : Icc 1 m = Ioc 0 m := by ext x; simp; omega
  have := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ m
  rwa [e] at this

theorem cS_approx (hχ : χ ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖DirichletCharacter.LFunction χ 1 - cS χ N‖ ≤ 4 * ((q : ℝ) + 1) / N := by
  have h := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1) (Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ)
    1 (by simp) N hN
  have e : Icc 1 N = Ioc 0 N := by ext x; simp; omega
  have e2 : ∑ n ∈ Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-(1 : ℂ)) = cS χ N := by
    rw [e, cS]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.cpow_neg_one, div_eq_mul_inv]
  rw [e2] at h
  have e3 : (N : ℝ) ^ (-(1 : ℂ).re) = (N : ℝ)⁻¹ := by simp [Real.rpow_neg_one]
  rw [e3] at h
  simp only [norm_one, Complex.one_re, div_one] at h
  calc _ ≤ 2 * ((q : ℝ) + 1) * (1 + 1) * (N : ℝ)⁻¹ := h
    _ = 4 * ((q : ℝ) + 1) / N := by ring

theorem abel_identity (c : ℕ → ℂ) (w : ℕ → ℝ) (U : ℕ) : ∀ V, U ≤ V →
    ∑ n ∈ Ioc U V, c n * (w n : ℂ) =
      (∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ) - (∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ) +
        ∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ) := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hUV ih =>
    rw [Finset.sum_Ioc_succ_top hUV, ih, Finset.sum_Ioc_succ_top hUV,
      Finset.sum_Ioc_succ_top (Nat.zero_le V)]
    push_cast
    ring

theorem tele (w : ℕ → ℝ) (U : ℕ) : ∀ V, U ≤ V →
    ∑ n ∈ Ioc U V, (w n - w (n + 1)) = w (U + 1) - w (V + 1) := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hUV ih => rw [Finset.sum_Ioc_succ_top hUV, ih]; ring

theorem abel_bound (c : ℕ → ℂ) (w : ℕ → ℝ) (B : ℝ) (hA : ∀ m, ‖∑ n ∈ Ioc 0 m, c n‖ ≤ B)
    (U V : ℕ) (hUV : U ≤ V) (hw0 : 0 ≤ w (U + 1))
    (hw : ∀ n, U < n → 0 ≤ w (n + 1) ∧ w (n + 1) ≤ w n) :
    ‖∑ n ∈ Ioc U V, c n * (w n : ℂ)‖ ≤ 2 * B * w (U + 1) := by
  rw [abel_identity c w U V hUV]
  have hV : 0 ≤ w (V + 1) := by
    rcases hUV.lt_or_eq with h | h
    · exact (hw V h).1
    · rw [← h]; exact hw0
  have h1 : ‖(∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)‖ ≤ B * w (V + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hV]
    exact mul_le_mul_of_nonneg_right (hA V) hV
  have h2 : ‖(∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ)‖ ≤ B * w (U + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right (hA U) hw0
  have h3 : ‖∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ)‖ ≤
      B * (w (U + 1) - w (V + 1)) := by
    calc _ ≤ ∑ n ∈ Ioc U V, ‖(∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc U V, B * (w n - w (n + 1)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' : U < n := (Finset.mem_Ioc.mp hn).1
        have hd : 0 ≤ w n - w (n + 1) := by linarith [(hw n hn').2]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (hA n) hd
      _ = B * (w (U + 1) - w (V + 1)) := by rw [← Finset.mul_sum, tele w U V hUV]
  have h4 := norm_add_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ) - (∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ))
    (∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ))
  have h5 := norm_sub_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)) ((∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ))
  linarith

def lw (n : ℕ) : ℝ := Real.log n / n

theorem lw_nonneg (n : ℕ) : 0 ≤ lw n :=
  div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)

theorem lw_anti (n : ℕ) (hn : 3 ≤ n) : 0 ≤ lw (n + 1) ∧ lw (n + 1) ≤ lw n := by
  refine ⟨lw_nonneg _, ?_⟩
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ (n : ℝ) := by
    have := Real.exp_one_lt_d9; linarith
  unfold lw
  push_cast
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (by linarith)) (by linarith)

theorem cT_sub (U V : ℕ) (hUV : U ≤ V) :
    cT χ V - cT χ U = ∑ n ∈ Ioc U V, χ (n : ZMod q) * (lw n : ℂ) := by
  rw [cT, cT, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUV, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold lw; push_cast; ring

theorem cT_diff2 (hχ : χ ≠ 1) (U V : ℕ) (hU : 2 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 2 * ((q : ℝ) + 1) * lw (U + 1) := by
  rw [cT_sub χ U V hUV]
  exact abel_bound (fun n => χ (n : ZMod q)) lw _ (charSum_le χ hχ) U V hUV (lw_nonneg _)
    (fun n hn => lw_anti n (by omega))

theorem cT_diff (hχ : χ ≠ 1) (U V : ℕ) (hU : 1 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 4 * ((q : ℝ) + 1) * ((1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hU0 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hlU : 0 ≤ Real.log ((U : ℝ) + 1) := Real.log_nonneg (by linarith)
  rcases (show 2 ≤ U ∨ U = 1 by omega) with h2 | h1
  · have h := cT_diff2 χ hχ U V h2 hUV
    have e : lw (U + 1) = Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1) := by unfold lw; push_cast; rfl
    rw [e] at h
    have : Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1) ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hy : 0 ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1) := by positivity
    calc _ ≤ _ := h
      _ ≤ 2 * ((q : ℝ) + 1) * ((1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ _ := by nlinarith
  · subst h1
    rcases (show V = 1 ∨ 2 ≤ V by omega) with hv | hv
    · subst hv; simp only [sub_self, norm_zero]; positivity
    · have hA := cT_diff2 χ hχ 2 V le_rfl hv
      have hB : ‖cT χ 2 - cT χ 1‖ ≤ 1 / 2 := by
        rw [cT_sub χ 1 2 (by norm_num)]
        have e : Ioc 1 2 = {2} := by decide
        rw [e, Finset.sum_singleton]
        rw [norm_mul, Complex.norm_real]
        have hc : ‖χ ((2 : ℕ) : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have hl : ‖lw 2‖ ≤ 1 / 2 := by
          rw [Real.norm_of_nonneg (lw_nonneg 2)]
          unfold lw; push_cast
          have := Real.log_two_lt_d9
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
        calc _ ≤ 1 * (1 / 2 : ℝ) := mul_le_mul hc hl (norm_nonneg _) (by norm_num)
          _ = 1 / 2 := by ring
      have hl3 : lw 3 ≤ 2 / 3 := by
        unfold lw; push_cast
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
      have hsplit : cT χ V - cT χ 1 = (cT χ V - cT χ 2) + (cT χ 2 - cT χ 1) := by ring
      rw [hsplit]
      have hl2 : 0 ≤ Real.log ((1 : ℕ) + (1 : ℝ)) := Real.log_nonneg (by norm_num)
      have : (1 : ℝ) ≤ (1 + Real.log ((1 : ℕ) + (1 : ℝ))) / ((1 : ℕ) + (1 : ℝ)) * 2 := by
        push_cast; push_cast at hl2
        rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith
      calc _ ≤ ‖cT χ V - cT χ 2‖ + ‖cT χ 2 - cT χ 1‖ := norm_add_le _ _
        _ ≤ 2 * ((q : ℝ) + 1) * (2 / 3) + 1 / 2 := by
          have : 2 * ((q : ℝ) + 1) * lw (2 + 1) ≤ 2 * ((q : ℝ) + 1) * (2 / 3) :=
            mul_le_mul_of_nonneg_left hl3 (by positivity)
          linarith
        _ ≤ _ := by nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
end
end

section

open Complex Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma sum_blocks (f : ℕ → ℂ) (Y : ℕ) : ∀ J : ℕ,
    ∑ n ∈ Ioc Y (Y * 2 ^ J), f n = ∑ j ∈ range J, ∑ n ∈ Ioc (Y * 2 ^ j) (2 * (Y * 2 ^ j)), f n
  | 0 => by simp
  | J + 1 => by
    rw [sum_range_succ, ← sum_blocks f Y J]
    have h1 : Y ≤ Y * 2 ^ J := Nat.le_mul_of_pos_right Y (by positivity)
    have h2 : Y * 2 ^ J ≤ Y * 2 ^ (J + 1) := Nat.mul_le_mul_left Y (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [show 2 * (Y * 2 ^ J) = Y * 2 ^ (J + 1) by ring]
    exact (Finset.sum_Ioc_consecutive _ h1 h2).symm

lemma mollM_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 0 ≤ s.re) (Y : ℕ) :
    ‖∑ d ∈ Icc 1 Y, (((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ Y := by
  refine le_trans (norm_sum_le _ _) ?_
  have h1 : ∀ d ∈ Icc 1 Y, ‖(((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ 1 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.1 hd).1
    rw [norm_mul, norm_mul]
    have hμ : ‖(((μ d : ℤ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hχ : ‖χ (d : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hp : ‖(d : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) ?_
      simp only [Complex.neg_re]
      linarith
    calc ‖(((μ d : ℤ)) : ℂ)‖ * ‖χ (d : ZMod q)‖ * ‖(d : ℂ) ^ (-s)‖ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  calc ∑ d ∈ Icc 1 Y, ‖(((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ ∑ d ∈ Icc 1 Y, (1 : ℝ) :=
        Finset.sum_le_sum h1
    _ = Y := by simp

attribute [local irreducible] q0 pY pJ pN in
theorem zero_detection : DetectOf := by
  intro hM Q hQ p hp hp1 hpQ ρ hρ hρim hL
  obtain ⟨N0, χ⟩ := p
  simp only at hp hp1 hpQ hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, q0 Q = X := ⟨_, rfl⟩
  have hXQ : Q ≤ (X : ℝ) := by rw [← hX]; unfold q0; exact Nat.le_ceil Q
  have hX20 : (20 : ℝ) ≤ X := le_trans hQ hXQ
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hs0 : s0 = 399 / 400 := by unfold s0; norm_num
  have hre0 : 0 < ρ.re := by rw [hs0] at hρ; linarith

  have hχ1 : χ ≠ 1 := by
    intro h
    have hc : χ.conductor = N0 + 1 := hp
    rw [h, DirichletCharacter.conductor_one] at hc
    omega

  have hJ8 : 8 ≤ pJ Q := by unfold pJ; omega
  have hNX : X ^ 8 ≤ pN Q := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pN pJ
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pY Q = X ^ 4 := by unfold pY; rw [hX]
  have hYN : pY Q ≤ pN Q := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pY Q := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pN Q := le_trans hY1 hYN

  have hB := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ1
  have hP := Formalism.FX.l_function_partial_sum (N0 + 1) χ hχ1 _ hB ρ hre0 (pN Q) hN1
  rw [hL, zero_sub, norm_neg] at hP

  have hMI := hM (N0 + 1) χ ρ (pY Q) (pN Q) (pY Q * pN Q) hY1 hYN le_rfl
  have hMo := mollM_norm_le χ ρ hre0.le (pY Q)
  set P := ∑ n ∈ Icc 1 (pN Q), χ (n : ZMod (N0 + 1)) * (n : ℂ) ^ (-ρ) with hPdef
  set Mo := ∑ d ∈ Icc 1 (pY Q), (((μ d : ℤ)) : ℂ) * χ (d : ZMod (N0 + 1)) * (d : ℂ) ^ (-ρ) with hMdef
  set D := ∑ n ∈ Ioc (pY Q) (pY Q * pN Q), mco (pY Q) (pN Q) n * χ (n : ZMod (N0 + 1)) * (n : ℂ) ^ (-ρ) with hD

  have hnum : ‖P‖ * (pY Q : ℝ) ≤ 1 / 2 := by
    have hq : ((N0 + 1 : ℕ) : ℝ) + 1 ≤ 2 * X := by
      have : ((N0 + 1 : ℕ) : ℝ) ≤ Q := hpQ
      linarith
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * X := by
      have h1 : ‖ρ‖ ≤ ρ.re + Q := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + Q / ρ.re := by
        rw [div_le_iff₀ hre0]; rw [add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : Q / ρ.re ≤ 2 * Q := by
        rw [div_le_iff₀ hre0]; rw [hs0] at hρ; nlinarith
      linarith
    have hNpos : (0 : ℝ) < pN Q := by exact_mod_cast hN1
    have hXpos : (0 : ℝ) < X := by linarith
    have hpow : ((pN Q : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pN Q : ℕ) : ℝ) ^ (-(15 / 16 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by rw [hs0] at hρ; linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pN Q : ℝ) := by exact_mod_cast hNX
    have hpow2 : 4 * (X : ℝ) ^ (7 : ℕ) ≤ ((pN Q : ℕ) : ℝ) ^ (15 / 16 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (15 / 16 : ℝ) = (X : ℝ) ^ (7 : ℕ) * Real.sqrt X := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
          ← Real.rpow_add hXpos]
        norm_num
      have hs : (4 : ℝ) ≤ Real.sqrt X := by
        rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith)
      calc 4 * (X : ℝ) ^ (7 : ℕ) ≤ (X : ℝ) ^ (7 : ℕ) * Real.sqrt X := by
            have : (0 : ℝ) ≤ (X : ℝ) ^ (7 : ℕ) := by positivity
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left hs this
        _ = ((X : ℝ) ^ (8 : ℕ)) ^ (15 / 16 : ℝ) := e.symm
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pN Q : ℕ) : ℝ) ^ (-(15 / 16 : ℝ)) ≤ 1 / (4 * (X : ℝ) ^ (7 : ℕ)) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pY Q : ℝ) = (X : ℝ) ^ (4 : ℕ) := by rw [hY, Nat.cast_pow]
    have hPle : ‖P‖ ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) := by
      refine hP.trans ?_
      have hpos1 : (0 : ℝ) ≤ ((N0 + 1 : ℕ) : ℝ) + 1 := by positivity
      have hpos2 : (0 : ℝ) ≤ 1 + ‖ρ‖ / ρ.re := by positivity
      have a1 : 2 * (((N0 + 1 : ℕ) : ℝ) + 1) ≤ 2 * (2 * X) := by linarith
      have a12 : 2 * (((N0 + 1 : ℕ) : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 2 * (2 * X) * (3 * X) :=
        mul_le_mul a1 hrho hpos2 (by positivity)
      have a3 : ((pN Q : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (4 * (X : ℝ) ^ (7 : ℕ)) := hpow.trans hinv
      calc 2 * (((N0 + 1 : ℕ) : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) * ((pN Q : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 2 * (2 * X) * (3 * X) * ((pN Q : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right a12 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) :=
            mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P‖ * (X : ℝ) ^ (4 : ℕ) ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) * (X : ℝ) ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 3 / X := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          rw [eq_div_iff hX0]
          field_simp
          ring
      _ ≤ 1 / 2 := by rw [div_le_iff₀ hXpos]; linarith
  have h1D : ‖1 + D‖ ≤ 1 / 2 := by
    rw [← hMI]
    rw [norm_mul]
    calc ‖P‖ * ‖Mo‖ ≤ ‖P‖ * (pY Q : ℝ) := mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
      _ ≤ 1 / 2 := hnum
  have hDge : 1 / 2 ≤ ‖D‖ := by
    have := norm_sub_le (1 + D) D
    simp only [add_sub_cancel_right, norm_one] at this
    linarith

  have hsplit : D = ∑ j ∈ range (pJ Q), blk (pY Q) (pN Q) (pY Q * 2 ^ j) ⟨N0, χ⟩ ρ := by
    rw [hD, show pN Q = 2 ^ pJ Q by unfold pN; rfl, sum_blocks]
    rfl
  by_contra hcon
  push_neg at hcon
  have hJpos : (0 : ℝ) < pJ Q := by exact_mod_cast (by omega : 0 < pJ Q)
  have hlt : ‖D‖ < 1 / 2 := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    have hne : (range (pJ Q)).Nonempty := nonempty_range_iff.mpr (by omega)
    calc ∑ j ∈ range (pJ Q), ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) ⟨N0, χ⟩ ρ‖
        < ∑ j ∈ range (pJ Q), 1 / (2 * (pJ Q : ℝ)) := sum_lt_sum_of_nonempty hne hcon
      _ = 1 / 2 := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

lemma tail_diff_split (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have h1 : Icc 1 b = Icc 1 a ∪ Ioc a b := by
    ext n
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  rw [h1, sum_union]
  rw [disjoint_left]
  intro n h2 h3
  simp only [mem_Icc, mem_Ioc] at h2 h3
  omega

lemma tail_diff_identity {N : ℕ} (χ : DirichletCharacter ℂ N) (z h : ℝ) (hh : 0 < h) :
    Formalism.ZeroFreeDirichlet.Schi χ (z + h) - Formalism.ZeroFreeDirichlet.Schi χ z -
              (h : ℂ) * ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ)
      = ∑ n ∈ Ioc ⌊z⌋₊ ⌊z + h⌋₊,
          ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * (((z + h) / n - 1 : ℝ) : ℂ) := by
  unfold Formalism.ZeroFreeDirichlet.Schi
  have hmono : ⌊z⌋₊ ≤ ⌊z + h⌋₊ := Nat.floor_le_floor (by linarith)
  rw [tail_diff_split _ hmono]
  have key : ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * (((z + h) / n - 1 : ℝ) : ℂ)
      - ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((z / n - 1 : ℝ) : ℂ)
      - (h : ℂ) * ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ) = 0 := by
    rw [← sum_sub_distrib, mul_sum, ← sum_sub_distrib]
    apply sum_eq_zero
    intro n _
    push_cast
    ring
  linear_combination key

lemma tail_diff_term {N : ℕ} (χ : DirichletCharacter ℂ N) (z h : ℝ) (hz : 1 ≤ z) (hh : 0 < h)
    {n : ℕ} (hn : n ∈ Ioc ⌊z⌋₊ ⌊z + h⌋₊) :
    ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * (((z + h) / n - 1 : ℝ) : ℂ)‖ ≤
      Real.log (z + h) * (h / z) := by
  rw [mem_Ioc] at hn
  have hzpos : 0 < z := by linarith
  have hzn : z < n := Nat.lt_of_floor_lt hn.1
  have hnzh : (n : ℝ) ≤ z + h := (Nat.le_floor_iff (by linarith)).1 hn.2
  have hnpos : (0:ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log (z + h) := Real.log_nonneg (by linarith)
  have hΛ : (Λ n : ℝ) ≤ Real.log (z + h) :=
    vonMangoldt_le_log.trans (Real.log_le_log hnpos hnzh)
  have hΛ0 : 0 ≤ (Λ n : ℝ) := vonMangoldt_nonneg
  have hχ : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have ht0 : 0 ≤ (z + h) / n - 1 := by
    rw [sub_nonneg, le_div_iff₀ hnpos]
    linarith
  have ht1 : (z + h) / n - 1 ≤ h / z := by
    rw [div_sub_one hnpos.ne', div_le_div_iff₀ hnpos hzpos]
    nlinarith [mul_pos hh (sub_pos.2 hzn), mul_pos hzpos (sub_pos.2 hzn)]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hΛ0,
    Real.norm_of_nonneg ht0]
  have e1 : (Λ n : ℝ) * ‖χ (n : ZMod N)‖ ≤ Real.log (z + h) := by
    calc (Λ n : ℝ) * ‖χ (n : ZMod N)‖ ≤ Real.log (z + h) * 1 :=
          mul_le_mul hΛ hχ (norm_nonneg _) hlog
      _ = _ := mul_one _
  exact mul_le_mul e1 ht1 ht0 hlog

theorem tail_diff_schi {N : ℕ} (χ : DirichletCharacter ℂ N) (z h : ℝ) (hz : 1 ≤ z) (hh : 0 < h) :
    ‖Formalism.ZeroFreeDirichlet.Schi χ (z + h) - Formalism.ZeroFreeDirichlet.Schi χ z -
              (h : ℂ) * ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ)‖ ≤
      h * (h + 1) * Real.log (z + h) / z := by
  rw [tail_diff_identity χ z h hh]
  have hzpos : 0 < z := by linarith
  have hlog : 0 ≤ Real.log (z + h) := Real.log_nonneg (by linarith)
  have hmono : ⌊z⌋₊ ≤ ⌊z + h⌋₊ := Nat.floor_le_floor (by linarith)
  have hcard : ((Ioc ⌊z⌋₊ ⌊z + h⌋₊).card : ℝ) ≤ h + 1 := by
    rw [Nat.card_Ioc, Nat.cast_sub hmono]
    have h1 : (⌊z + h⌋₊ : ℝ) ≤ z + h := Nat.floor_le (by linarith)
    have h2 : z < ⌊z⌋₊ + 1 := Nat.lt_floor_add_one z
    linarith
  calc _ ≤ ∑ n ∈ Ioc ⌊z⌋₊ ⌊z + h⌋₊, Real.log (z + h) * (h / z) :=
        (norm_sum_le _ _).trans (sum_le_sum fun n hn => tail_diff_term χ z h hz hh hn)
    _ = ((Ioc ⌊z⌋₊ ⌊z + h⌋₊).card : ℝ) * (Real.log (z + h) * (h / z)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (h + 1) * (Real.log (z + h) * (h / z)) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hlog (div_nonneg hh.le hzpos.le))
    _ = h * (h + 1) * Real.log (z + h) / z := by ring

end Formalism.HermitianLattices.Ext.BoxTail
end
end
