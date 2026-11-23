module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def derivL1Norm (f : V → ℂ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖

lemma derivL1Norm_nonneg (f : V → ℂ) (n : ℕ) : 0 ≤ derivL1Norm f n :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _

lemma integrable_iteratedFDeriv {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (k n : ℕ) :
    Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) := by
  have hcont : Continuous (fun v => iteratedFDeriv ℝ n f v) :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hc : Continuous (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) :=
    (continuous_norm.pow k).mul hcont.norm
  have hs : HasCompactSupport (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) :=
    ((hfc.iteratedFDeriv n).comp_left norm_zero).mul_left
  exact hc.integrable_of_hasCompactSupport hs

lemma pow_mul_norm_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (n : ℕ) (w : V) :
    ‖w‖ ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * derivL1Norm f n := by
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := n)
    (hf.of_le (by exact_mod_cast le_top))
    (fun k j _ _ => integrable_iteratedFDeriv hf hfc k j) (k := 0) (n := n) (by simp) le_rfl w
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add,
    Finset.sum_product, Finset.sum_range_one] at h
  unfold derivL1Norm
  exact h

lemma one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  have htn : 0 ≤ t ^ n := pow_nonneg ht n
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  rcases le_total t 1 with h | h
  · have h1 : (1 + t) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have h3 : (2 : ℝ) ^ n ≤ 2 ^ n * (1 + t ^ n) := le_mul_of_one_le_right h2 (by linarith)
    linarith
  · have h1 : (1 + t) ^ n ≤ (2 * t) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have h3 : (2 : ℝ) ^ n * t ^ n ≤ 2 ^ n * (1 + t ^ n) := mul_le_mul_of_nonneg_left (by linarith) h2
    rw [mul_pow] at h1
    linarith

lemma one_add_pow_mul_norm_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (n : ℕ) (w : V) :
    (1 + ‖w‖) ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n := by
  have hL := pow_mul_norm_fourier_le hf hfc n w
  have h0 := pow_mul_norm_fourier_le hf hfc 0 w
  simp only [pow_zero, one_mul] at h0
  have hmono : derivL1Norm f 0 ≤ derivL1Norm f n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun _ _ _ => integral_nonneg fun _ => norm_nonneg _)
  have hpos : 0 ≤ ‖𝓕 f w‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hb := one_add_pow_le ‖w‖ (norm_nonneg w) n
  calc (1 + ‖w‖) ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * (1 + ‖w‖ ^ n) * ‖𝓕 f w‖ := mul_le_mul_of_nonneg_right hb hpos
    _ = 2 ^ n * (‖𝓕 f w‖ + ‖w‖ ^ n * ‖𝓕 f w‖) := by ring
    _ ≤ 2 ^ n * (derivL1Norm f n + 2 ^ n * derivL1Norm f n) := by
        refine mul_le_mul_of_nonneg_left ?_ h2
        linarith
    _ = 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n := by ring

lemma norm_fourier_le_rpow {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (n : ℕ) (w : V) :
    ‖𝓕 f w‖ ≤ 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n * (1 + ‖w‖) ^ (-(n : ℝ)) := by
  have h5 := one_add_pow_mul_norm_fourier_le hf hfc n w
  have hp : 0 < 1 + ‖w‖ := by positivity
  have hpn : 0 < (1 + ‖w‖) ^ n := pow_pos hp n
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpn]
  linarith [h5, mul_comm ((1 + ‖w‖) ^ n) ‖𝓕 f w‖]

lemma lintegral_weight_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (m : ℕ) :
    (∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ m) * ‖𝓕 f w‖ₑ) ≤
      ENNReal.ofReal (2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1))) *
      ∫⁻ w : V, ENNReal.ofReal ((1 + ‖w‖) ^ (-((Module.finrank ℝ V + 1 : ℕ) : ℝ))) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun w => ?_
  dsimp only
  have hp : 0 < 1 + ‖w‖ := by positivity
  have h6 := norm_fourier_le_rpow hf hfc (m + (Module.finrank ℝ V + 1)) w
  have hA : 0 ≤ (1 + ‖w‖) ^ m := by positivity
  have hC : 0 ≤ 2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
      derivL1Norm f (m + (Module.finrank ℝ V + 1)) :=
    mul_nonneg (by positivity) (derivL1Norm_nonneg f _)
  have hexp : (1 + ‖w‖) ^ m * (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ)) =
      (1 + ‖w‖) ^ (-((Module.finrank ℝ V + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp]
    congr 1
    push_cast
    ring
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  calc (1 + ‖w‖) ^ m * ‖𝓕 f w‖
      ≤ (1 + ‖w‖) ^ m * (2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1)) *
        (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ))) := mul_le_mul_of_nonneg_left h6 hA
    _ = 2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1)) *
        ((1 + ‖w‖) ^ m * (1 + ‖w‖) ^ (-((m + (Module.finrank ℝ V + 1) : ℕ) : ℝ))) := by ring
    _ = _ := by rw [hexp]

lemma lintegral_weight_fourier_lt_top {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (m : ℕ) :
    (∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ m) * ‖𝓕 f w‖ₑ) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_weight_fourier_le hf hfc m)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (finite_integral_one_add_norm ?_))
  push_cast
  linarith

end

end ZetaZeros.D.EllReg
end

section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma norm_fourier_comp_dil (c : V → ℂ) (r : ℝ) (hr : 0 < r) (x0 w : V) :
    ‖𝓕 (fun x => c (r⁻¹ • (x - x0))) w‖ = r ^ Module.finrank ℝ V * ‖𝓕 c (r • w)‖ := by
  have hrw : ∀ y : V, Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y =
      Complex.exp (↑(-2 * Real.pi * inner ℝ x0 w) * Complex.I) *
        (Complex.exp (↑(-2 * Real.pi * inner ℝ y (r • w)) * Complex.I) • c y) := by
    intro y
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_right]
    push_cast
    ring
  rw [Real.fourier_eq', Real.fourier_eq']
  have h1 : (∫ v : V, Complex.exp (↑(-2 * Real.pi * inner ℝ v w) * Complex.I) • c (r⁻¹ • (v - x0))) =
      ∫ v : V, (fun y => Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y)
        (r⁻¹ • v) := by
    rw [← MeasureTheory.integral_add_right_eq_self _ x0]
    congr 1
    funext v
    simp only [add_sub_cancel_right, smul_inv_smul₀ hr.ne']
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (MeasureTheory.volume : MeasureTheory.Measure V)
    (fun y => Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y) hr.le
  rw [h1.trans h2]
  simp only [hrw]
  rw [MeasureTheory.integral_const_mul, norm_smul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma lintegral_dil_weight (r : ℝ) (hr : 0 < r) (D : ℝ) (hD : (Module.finrank ℝ V : ℝ) < D) :
    (∫⁻ w : V, ENNReal.ofReal (r ^ Module.finrank ℝ V * (1 + ‖r • w‖) ^ (-D))) =
      ∫⁻ w : V, ENNReal.ofReal ((1 + ‖w‖) ^ (-D)) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hmeas : Measurable (fun w : V => r • w) := measurable_const_smul r
  have hg : Measurable (fun u : V => ENNReal.ofReal ((1 + ‖u‖) ^ (-D))) := by fun_prop
  have h1 : ∀ w : V, ENNReal.ofReal (r ^ Module.finrank ℝ V * (1 + ‖r • w‖) ^ (-D)) =
      ENNReal.ofReal (r ^ Module.finrank ℝ V) * ENNReal.ofReal ((1 + ‖r • w‖) ^ (-D)) :=
    fun w => ENNReal.ofReal_mul (by positivity)
  simp_rw [h1]
  have hg' : Measurable (fun w : V => ENNReal.ofReal ((1 + ‖r • w‖) ^ (-D))) := hg.comp hmeas
  rw [MeasureTheory.lintegral_const_mul _ hg']
  rw [← MeasureTheory.lintegral_map hg hmeas, MeasureTheory.Measure.map_addHaar_smul _ hr0,
    MeasureTheory.lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

end

end ZetaZeros.D.EllReg
end
