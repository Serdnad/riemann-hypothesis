module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

section

namespace GlobalTheory

theorem hilbertSamuel_ALogA_le (T D : ℕ) (PP b z : ℝ) (hD1 : 1 ≤ D) (hDT : D ≤ T) (hPP : 1 ≤ PP)
    (hb : 1 ≤ b) (hlogb : Real.log b ≤ PP) (hTP : (T : ℝ) * PP ≤ Real.sqrt b) (hz0 : 0 ≤ z)
    (hz : z ≤ 1 / 2) :
    26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) * Real.log (max (26 * (26 * (D : ℝ) ^ 2 + 2 * z * T)) 1)
      ≤ 6000 * b := by
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDT' : (D : ℝ) ≤ T := by exact_mod_cast hDT
  have hT1 : (1 : ℝ) ≤ T := le_trans hD1' hDT'
  set A : ℝ := 26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) with hAdef
  have hA1 : 1 ≤ A := by
    have : (0 : ℝ) ≤ 2 * z * T := by positivity
    nlinarith
  have hmax : max A 1 = A := max_eq_left hA1
  rw [hmax]
  have hApos : 0 < A := by linarith
  have hAle : A ≤ 702 * (T : ℝ) ^ 2 := by
    have h1 : (D : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by nlinarith
    have h2 : 2 * z * (T : ℝ) ≤ T := by nlinarith
    have h3 : (T : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hTsq : (T : ℝ) ≤ Real.sqrt b := by nlinarith
  have hlogT : 2 * Real.log T ≤ PP := by
    have h1 : Real.log T ≤ Real.log (Real.sqrt b) := Real.log_le_log hT0 hTsq
    rw [Real.log_sqrt (by linarith)] at h1
    linarith
  have hlog702 : Real.log 702 < 7 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : Real.exp 7 = Real.exp 1 ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h27 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by
      apply pow_le_pow_left₀ (by norm_num); linarith
    nlinarith
  have hlogA : Real.log A ≤ 8 * PP := by
    have h1 : Real.log A ≤ Real.log (702 * (T : ℝ) ^ 2) := Real.log_le_log hApos hAle
    have h2 : Real.log (702 * (T : ℝ) ^ 2) = Real.log 702 + 2 * Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    linarith
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hmain : A * Real.log A ≤ 702 * (T : ℝ) ^ 2 * (8 * PP) :=
    mul_le_mul hAle hlogA hlogA0 (by positivity)
  have hsq : ((T : ℝ) * PP) ^ 2 ≤ b := by
    have h0 : 0 ≤ (T : ℝ) * PP := by positivity
    calc ((T : ℝ) * PP) ^ 2 ≤ Real.sqrt b ^ 2 := pow_le_pow_left₀ h0 hTP 2
      _ = b := Real.sq_sqrt (by linarith)
  have hTPP : (T : ℝ) ^ 2 * PP ≤ (T : ℝ) ^ 2 * PP ^ 2 := by
    have : PP ≤ PP ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  nlinarith

end GlobalTheory
end

section

open Real

namespace GlobalTheory

theorem covol_numerical_collect : ∀ (CG CB f r Lb S N0 sz c₁ q ℓ lb dd : ℝ), 0 ≤ CG → 0 ≤ CB → 1 ≤ f → 1 ≤ r → 1 ≤ Lb → 0 ≤ S → 0 ≤ q → q ≤ r → 0 ≤ ℓ → ℓ ≤ 3 * Lb → |c₁| ≤ 9 * r * Lb → 0 ≤ N0 → N0 ≤ S + f * (4 * (f * r + 1) + 1) → 0 ≤ sz → sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1) → lb ≤ CB * (f * r * Lb) ^ 2 → dd ≤ 391 / 2 * (f * r * Lb) ^ 2 → (f * r + 1) * (2 * (f * r) * Real.log (2 * Real.pi)) + ((|c₁| + q * ℓ) * N0 + lb + dd + 1) + CG * (f * r * Lb) ^ 2 * sz ≤ (11 * CG + CB + 500) * ((f * r * Lb) ^ 3 * S + (f * r * Lb) ^ 5) := by
  intro CG CB f r Lb S N0 sz c₁ q ℓ lb dd hCG hCB hf hr hLb hS hq hqr hℓ hℓL hc hN0 hN0u hsz hszu hlb hdd
  have hfr : 1 ≤ f * r := by nlinarith
  have hfrF : f * r ≤ f * r * Lb := by nlinarith
  have hrLbF : r * Lb ≤ f * r * Lb := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r) (by linarith : (0:ℝ) ≤ Lb)]
  have hrF : r ≤ f * r * Lb := by nlinarith
  obtain ⟨F, hFd⟩ : ∃ F, F = f * r * Lb := ⟨_, rfl⟩
  rw [← hFd] at hlb hdd hfrF hrLbF hrF ⊢
  have hF : 1 ≤ F := by linarith
  have hF2 : F ^ 2 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF3 : F ^ 3 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF4 : F ^ 4 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF1 : F ≤ F ^ 3 := by simpa using pow_le_pow_right₀ hF (by norm_num : 1 ≤ 3)
  have hX : 0 ≤ F ^ 3 * S := mul_nonneg (by positivity) hS

  have hlog : Real.log (2 * π) ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * π)
    have := Real.pi_le_four
    linarith
  have hfrsq : (f * r) ^ 2 ≤ F ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hfrF) (by linarith : (0:ℝ) ≤ F + f * r)]
  have hT1a : (f * r + 1) * (2 * (f * r) * Real.log (2 * π)) ≤ (f * r + 1) * (2 * (f * r) * 7) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by linarith)) (by linarith)

  have hql : q * ℓ ≤ r * (3 * Lb) := mul_le_mul hqr hℓL hℓ (by linarith)
  have hA : |c₁| + q * ℓ ≤ 12 * (r * Lb) := by linarith
  have hffr : f ≤ f * (f * r) := by nlinarith
  have hB : N0 ≤ S + 9 * (f * (f * r)) := by
    have e : f * (4 * (f * r + 1) + 1) = 4 * (f * (f * r)) + 5 * f := by ring
    linarith
  have hAB : (|c₁| + q * ℓ) * N0 ≤ 12 * (r * Lb) * (S + 9 * (f * (f * r))) :=
    mul_le_mul hA hB hN0 (by positivity)
  have hrLbS : r * Lb * S ≤ F ^ 3 * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hFfr : r * Lb * (f * (f * r)) ≤ F ^ 5 := by
    have e : r * Lb * (f * (f * r)) = F * (f * r) := by rw [hFd]; ring
    rw [e]
    have : F * (f * r) ≤ F * F := mul_le_mul_of_nonneg_left hfrF (by linarith)
    nlinarith

  have hsz1 : (1 + r) * S ≤ 2 * F * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hsz2 : r * f * (4 * (f * r + 1) + 1) ≤ 9 * F ^ 2 := by
    have e : r * f * (4 * (f * r + 1) + 1) = 4 * (f * r) ^ 2 + 5 * (f * r) := by ring
    rw [e]; nlinarith
  have hsz' : sz ≤ 2 * F * S + 9 * F ^ 2 := by linarith
  have hT6a : CG * F ^ 2 * sz ≤ CG * F ^ 2 * (2 * F * S + 9 * F ^ 2) :=
    mul_le_mul_of_nonneg_left hsz' (by positivity)
  have hT6b : CG * F ^ 4 ≤ CG * F ^ 5 := mul_le_mul_of_nonneg_left hF4 hCG
  have hlb' : lb ≤ CB * F ^ 5 := le_trans hlb (mul_le_mul_of_nonneg_left hF2 hCB)
  have p1 : 0 ≤ CG * (F ^ 3 * S) := mul_nonneg hCG hX
  have p2 : 0 ≤ CB * (F ^ 3 * S) := mul_nonneg hCB hX
  have p3 : 0 ≤ CG * F ^ 5 := mul_nonneg hCG (by positivity)
  have e : (11 * CG + CB + 500) * (F ^ 3 * S + F ^ 5)
      = 11 * (CG * (F ^ 3 * S)) + CB * (F ^ 3 * S) + 500 * (F ^ 3 * S) + 11 * (CG * F ^ 5) + CB * F ^ 5 + 500 * F ^ 5 := by ring
  rw [e]
  linarith

end GlobalTheory
end

section

open Real

namespace GlobalTheory

theorem log_size_bounds_class_number_volume : ∀ f r L lrd lM lh w d D : ℝ, 1 ≤ f → 2 ≤ r → 1 ≤ L → log f + log r ≤ L → 0 ≤ lrd → lrd ≤ 2*L → 0 ≤ lM → lM ≤ 30*L → lh ≤ f*lrd + 2*f*log (1 + f*lrd) → 1 ≤ d → log d / 2 ≤ lrd → 0 < w → D = f*r*(r-1)/2 → lh ≤ 9*f*L ∧ lh + 2*f*lM ≤ 69*f*L ∧ log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd ≤ 80*f*r^2*L ∧ log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd + f*r^2/2*log r ≤ 81*f*r^2*L ∧ 2 + D*log (1600*r^2/π) + (2*f*r)^2*log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) + (log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd) ≤ 242*(f*r*L)^2 + 4*f^2*r^2*log (max 1 w) ∧ (w ≤ 3*exp (2*L) → 2 + D*log (1600*r^2/π) + (2*f*r)^2*log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) + (log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd) ≤ 250*f^2*r^2*L) := by
  intro f r L lrd lM lh w d D hf hr hL hfr hrd0 hrd hM0 hM hlh hd hdl hw hD
  have f0 : 0 < f := by linarith
  have r0 : 0 < r := by linarith
  have L0 : 0 < L := by linarith
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have lf0 : 0 ≤ log f := log_nonneg hf
  have lr2 : log 2 ≤ log r := log_le_log (by norm_num) hr
  have lLL : log L ≤ L - 1 := log_le_sub_one_of_pos L0
  have hfL : 1 ≤ f * L := by nlinarith
  have l4 : log 4 = 2 * log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; norm_num
  have l8 : log 8 = 3 * log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, log_pow]; norm_num
  have l16 : log 16 = 4 * log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num, log_pow]; norm_num
  have l1024 : log 1024 = 10 * log 2 := by
    rw [show (1024:ℝ) = 2^10 by norm_num, log_pow]; norm_num
  have l5 : log 5 ≤ 3 * log 2 := l8 ▸ log_le_log (by norm_num) (by norm_num)
  have l15 : log 5 + log 3 ≤ 4 * log 2 := by
    rw [← log_mul (by norm_num) (by norm_num), ← l16]
    exact log_le_log (by norm_num) (by norm_num)
  have hfrd : f * lrd ≤ f * (2 * L) := mul_le_mul_of_nonneg_left hrd f0.le
  have hfrd0 : 0 ≤ f * lrd := by positivity
  have h1 : log (1 + f * lrd) ≤ 2 * L := by
    have : log (1 + f * lrd) ≤ log (4 * f * L) := log_le_log (by linarith) (by linarith)
    rw [log_mul (by positivity) L0.ne', log_mul (by norm_num) f0.ne'] at this
    linarith
  have c1 : lh ≤ 9 * f * L := by
    have := mul_le_mul_of_nonneg_left h1 f0.le
    linarith
  have hfM : f * lM ≤ f * (30 * L) := mul_le_mul_of_nonneg_left hM f0.le
  have r2 : 4 ≤ r ^ 2 := by nlinarith
  have c3 : log 2 + lh + 2*f*(r^2+1)*lM + f*(r^2-1)/2*lrd ≤ 80*f*r^2*L := by
    have a := mul_le_mul_of_nonneg_left hfM (show 0 ≤ r^2+1 by positivity)
    have b := mul_le_mul_of_nonneg_left hfrd (show 0 ≤ r^2-1 by linarith)
    have c := mul_le_mul_of_nonneg_left r2 (show 0 ≤ f * L by linarith)
    linarith
  have lrL : log r ≤ L := by linarith
  have hfr2 : 0 ≤ f * r ^ 2 := by positivity
  have c4 : f*r^2/2*log r ≤ f*r^2*L := by
    have := mul_le_mul_of_nonneg_left lrL hfr2
    have : 0 ≤ f * r^2 * L := by positivity
    linarith
  have pi3 := Real.pi_gt_three
  have h2 : log (1600*r^2/π) ≤ 10 * log 2 + 2 * L := by
    have : log (1600*r^2/π) ≤ log (1024 * r^2) := by
      apply log_le_log (by positivity)
      rw [div_le_iff₀ pi_pos]
      nlinarith
    rw [log_mul (by norm_num) (by positivity), log_pow, l1024] at this
    push_cast at this
    linarith
  have hD0 : 0 ≤ D := by
    rw [hD]; have : 0 ≤ r - 1 := by linarith
    positivity
  have hD1 : D ≤ f * r ^ 2 / 2 := by
    rw [hD]; have : 0 ≤ f * r := by positivity
    nlinarith
  have h3 : D * log (1600*r^2/π) ≤ f * r^2 / 2 * (9 * L) := by
    calc D * log (1600*r^2/π) ≤ D * (9 * L) := mul_le_mul_of_nonneg_left (by linarith) hD0
      _ ≤ _ := mul_le_mul_of_nonneg_right hD1 (by positivity)
  have m1 : (1:ℝ) ≤ max 1 w := le_max_left _ _
  have sd : 1 ≤ √d := Real.one_le_sqrt.mpr hd
  have eM : 1 ≤ exp lM := one_le_exp hM0
  have h4 : max 1 (exp lM*f*w*√d) ≤ exp lM*f*max 1 w*√d := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le eM hf) m1) sd
    · gcongr; exact le_max_right _ _
  have h5 : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d))
      ≤ log 5 - log 2 + 37 * L + log (max 1 w) := by
    have : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d))
        ≤ log (5*f*r*exp (3/2*lrd)*(exp lM*f*max 1 w*√d)) := by
      apply log_le_log (by positivity)
      gcongr
    have e : log (5*f*r*exp (3/2*lrd)*(exp lM*f*max 1 w*√d))
        = log 5 + log f + log r + 3/2*lrd + (lM + log f + log (max 1 w) + log d / 2) := by
      rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_exp, log_exp,
        log_sqrt (by linarith)]
    linarith
  have hX : 0 ≤ f^2 * r^2 := by positivity
  have hA : f * r^2 * L ≤ f^2 * r^2 * L := by
    have : 0 ≤ f * r^2 * L := by positivity
    have := mul_le_mul_of_nonneg_left hf this
    linarith
  have hB : 4 ≤ f * r^2 * L := by
    have := mul_le_mul_of_nonneg_left hfL (show 0 ≤ r^2 by positivity)
    linarith
  have hC : f^2 * r^2 * L ≤ (f*r*L)^2 := by
    have : 0 ≤ f^2 * r^2 * L := by positivity
    have := mul_le_mul_of_nonneg_left hL this
    linarith
  refine ⟨c1, by linarith, c3, by linarith, ?_, fun hw3 => ?_⟩
  · have h6 : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) ≤ 39 * L + log (max 1 w) := by
      linarith
    have := mul_le_mul_of_nonneg_left h6 hX
    generalize log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) = Y at this ⊢
    linarith
  · have h7 : log (max 1 w) ≤ log 3 + 2 * L := by
      have e : 1 ≤ exp (2 * L) := one_le_exp (by linarith)
      have : log (max 1 w) ≤ log (3 * exp (2 * L)) :=
        log_le_log (by positivity) (max_le (by linarith) hw3)
      rwa [log_mul (by norm_num) (by positivity), log_exp] at this
    have h6 : log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) ≤ 411/10 * L := by
      linarith
    have := mul_le_mul_of_nonneg_left h6 hX
    generalize log (5*f*r*exp (3/2*lrd)*max 1 (exp lM*f*w*√d)) = Y at this ⊢
    linarith

end GlobalTheory
end

section

namespace GlobalTheory.CardLength

variable {R : Type} [CommRing R]

noncomputable def lenAt (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q] : ℕ∞ :=
  Module.length (Localization.AtPrime w) (LocalizedModule w.primeCompl Q)

theorem lenAt_exact (w : Ideal R) [w.IsPrime] {N M P : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    lenAt w M = lenAt w N + lenAt w P :=
  Module.length_eq_add_of_exact (LocalizedModule.map w.primeCompl f)
    (LocalizedModule.map w.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)

theorem lenAt_congr (w : Ideal R) [w.IsPrime] {M N : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] N) : lenAt w M = lenAt w N :=
  le_antisymm
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.toLinearMap)
      (LocalizedModule.map_injective _ _ e.injective))
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.symm.toLinearMap)
      (LocalizedModule.map_injective _ _ e.symm.injective))

theorem lenAt_subsingleton (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q]
    [Subsingleton Q] : lenAt w Q = 0 :=
  Module.length_eq_zero_iff.2 (IsLocalizedModule.subsingleton_of_subsingleton w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl Q))

theorem lenAt_quot_ne (w m : Ideal R) [hw : w.IsMaximal] [hm : m.IsMaximal] (h : w ≠ m) :
    lenAt w (R ⧸ m) = 0 := by
  refine Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl (R ⧸ m))).2 ?_)
  have hnle : ¬ m ≤ w := fun hle => h (hm.eq_of_le hw.ne_top hle).symm
  obtain ⟨s, hsm, hsw⟩ := SetLike.not_le_iff_exists.1 hnle
  intro x
  refine ⟨s, hsw, ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact m.mul_mem_right _ hsm

theorem lenAt_quot_self (m : Ideal R) [hm : m.IsMaximal] : lenAt m (R ⧸ m) = 1 := by
  refine Module.length_eq_one_iff.2 (isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨?_, ?_⟩)
  · rw [← not_subsingleton_iff_nontrivial, IsLocalizedModule.subsingleton_iff m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl (R ⧸ m))]
    intro h
    obtain ⟨r, hr, hr0⟩ := h 1
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr hr0
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h a s =>
    induction y using LocalizedModule.induction_on with
    | h c t =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hr : r ∈ m.primeCompl := by
      intro hrm
      apply hx
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hrm, LocalizedModule.zero_mk]
    refine ⟨Localization.mk (r' * s) (⟨r, hr⟩ * t), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Submonoid.coe_mul, Submonoid.coe_one]
    congr 1
    ring

theorem card_eq_prod_lenAt : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module R Q] [Finite Q],
    Nat.card Q = n → ∃ k : MaximalSpectrum R →₀ ℕ,
      (∀ w : MaximalSpectrum R, lenAt w.asIdeal Q = (k w : ℕ∞)) ∧
      Nat.card Q = k.prod fun w j => Nat.card (R ⧸ w.asIdeal) ^ j := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ hn
  by_cases hQ : Subsingleton Q
  · refine ⟨0, fun w => ?_, ?_⟩
    · rw [lenAt_subsingleton]; simp
    · rw [Finsupp.prod_zero_index]; exact Nat.card_of_subsingleton 0
  · rw [not_subsingleton_iff_nontrivial] at hQ
    rcases eq_top_or_exists_le_coatom (⊥ : Submodule R Q) with h | ⟨Q1, hQ1, -⟩
    · exact absurd h bot_ne_top
    · have hsimple : IsSimpleModule R (Q ⧸ Q1) := isSimpleModule_iff_isCoatom.2 hQ1
      obtain ⟨m0, hm0, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hsimple
      have hnt : Nontrivial (Q ⧸ Q1) := IsSimpleModule.nontrivial R _
      have hcard : Nat.card Q = Nat.card Q1 * Nat.card (Q ⧸ Q1) :=
        Submodule.card_eq_card_quotient_mul_card Q1
      have hfq : Finite (Q ⧸ Q1) := Finite.of_surjective _ Q1.mkQ_surjective
      have h1 : 1 < Nat.card (Q ⧸ Q1) := Finite.one_lt_card
      have h2 : 0 < Nat.card Q1 := Nat.card_pos
      have hlt : Nat.card Q1 < n := by
        rw [← hn, hcard]; nlinarith
      obtain ⟨k1, hk1, hk1c⟩ := ih _ hlt Q1 rfl
      refine ⟨k1 + Finsupp.single ⟨m0, hm0⟩ 1, fun w => ?_, ?_⟩
      · have := w.isMaximal
        rw [lenAt_exact w.asIdeal Q1.subtype Q1.mkQ Q1.injective_subtype Q1.mkQ_surjective
          (LinearMap.exact_subtype_mkQ Q1), hk1 w, lenAt_congr w.asIdeal e, Finsupp.add_apply,
          Finsupp.single_apply]
        by_cases hw : (⟨m0, hm0⟩ : MaximalSpectrum R) = w
        · subst hw
          rw [if_pos rfl, lenAt_quot_self]; simp
        · rw [if_neg hw, lenAt_quot_ne w.asIdeal m0
            (fun h => hw (MaximalSpectrum.ext h.symm))]; simp
      · have hz : ∀ w : MaximalSpectrum R, Nat.card (R ⧸ w.asIdeal) ^ 0 = 1 :=
          fun _ => pow_zero _
        have ha : ∀ (w : MaximalSpectrum R) (a c : ℕ), Nat.card (R ⧸ w.asIdeal) ^ (a + c) =
            Nat.card (R ⧸ w.asIdeal) ^ a * Nat.card (R ⧸ w.asIdeal) ^ c := fun _ _ _ => pow_add _ _ _
        rw [Finsupp.prod_add_index'
            (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) hz ha,
          Finsupp.prod_single_index
            (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) (hz _),
          pow_one, hcard, hk1c, Nat.card_congr e.toEquiv]

theorem log_card_eq_finsum_length : ∀ (B : Type) [CommRing B] (N : Type) [AddCommGroup N]
    [Module B N] [Finite N], Real.log (Nat.card N) = ∑ᶠ m : MaximalSpectrum B,
      ((Module.length (Localization.AtPrime m.asIdeal)
        (LocalizedModule m.asIdeal.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (B ⧸ m.asIdeal)) := by
  intro B _ N _ _ _
  classical
  obtain ⟨k, hk, hc⟩ := card_eq_prod_lenAt (R := B) _ N rfl
  have hlen : ∀ m : MaximalSpectrum B, (Module.length (Localization.AtPrime m.asIdeal)
      (LocalizedModule m.asIdeal.primeCompl N)).toNat = k m := fun m => by
    have h := hk m
    unfold lenAt at h
    rw [h]; rfl
  simp_rw [hlen]
  rw [finsum_eq_sum_of_support_subset (s := k.support) _ ?_]
  · have h0 : (k.prod fun w j => Nat.card (B ⧸ w.asIdeal) ^ j) ≠ 0 := by
      rw [← hc]; exact Nat.card_pos.ne'
    rw [Finsupp.prod, Finset.prod_ne_zero_iff] at h0
    rw [hc, Finsupp.prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro m hm
      exact_mod_cast h0 m hm
  · intro m hm
    rw [Function.mem_support] at hm
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0; apply hm; simp [h0]

end GlobalTheory.CardLength
end

section

namespace GlobalTheory

theorem exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq (x y : ℝ) (k : ℕ) (hk : 0 < k)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) :
    ∃ n : ℤ, y - x = n * k := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((y - x : ℝ) : ℂ) = ((n * k : ℝ) : ℂ) := by
    push_cast
    field_simp at hn
    linear_combination hn
  exact_mod_cast this

theorem real_eq_of_exp_neg_two_pi_I_div_eq : ∀ x y : ℝ, (∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) →
    x = y := by
  intro x y h
  obtain ⟨m, hm⟩ := exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y 1 one_pos (h 1 one_pos)
  simp only [Nat.cast_one, mul_one] at hm
  obtain ⟨n, hn⟩ := exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y (m.natAbs + 1) (Nat.succ_pos _)
    (h _ (Nat.succ_pos _))
  generalize hK : m.natAbs + 1 = K at hn
  have hmn : m = n * (K : ℤ) := by
    have : ((m : ℤ) : ℝ) = ((n * (K : ℤ) : ℤ) : ℝ) := by push_cast; rw [← hm, hn]
    exact_mod_cast this
  have hm0 : m = 0 := by
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hmn)
    have h1 : m.natAbs = n.natAbs * K := by
      rw [hmn, Int.natAbs_mul]; simp
    have h2 : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn0
    nlinarith
  have : y - x = 0 := by rw [hm, hm0]; simp
  linarith

end GlobalTheory
end
