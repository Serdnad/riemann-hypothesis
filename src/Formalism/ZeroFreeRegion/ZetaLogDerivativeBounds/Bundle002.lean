module

public import Formalism.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormCpowSubLePoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Complex

noncomputable section

namespace Formalism.ZF

open ArithmeticFunction in
theorem zetaPrimeSum_nonneg_and_le (y : ℝ) (hy : 1 ≤ y) :
    0 ≤ Formalism.Sz y ∧ Formalism.Sz y ≤ y * y * Real.log y := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊, 0 ≤ ArithmeticFunction.vonMangoldt n * (y / n - 1) ∧
      ArithmeticFunction.vonMangoldt n * (y / n - 1) ≤ Real.log y * y := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < n := by linarith
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr hn2).trans (Nat.floor_le hy0)
    have h1 : 0 ≤ y / n - 1 := by
      rw [sub_nonneg, le_div_iff₀ hnpos]
      linarith
    have h2 : y / n - 1 ≤ y := by
      have : y / n ≤ y := div_le_self hy0 hn1'
      linarith
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log y :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos hny)
    exact ⟨mul_nonneg ArithmeticFunction.vonMangoldt_nonneg h1, mul_le_mul hΛ h2 h1 hlog⟩
  unfold Formalism.Sz
  refine ⟨Finset.sum_nonneg fun n hn => (hterm n hn).1, ?_⟩
  calc ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)
        ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Real.log y * y := Finset.sum_le_sum fun n hn => (hterm n hn).2
    _ = (⌊y⌋₊ : ℝ) * (Real.log y * y) := by simp
    _ ≤ y * (Real.log y * y) := mul_le_mul_of_nonneg_right (Nat.floor_le hy0) (mul_nonneg hlog hy0)
    _ = y * y * Real.log y := by ring

theorem abs_zetaPrimeSumError_le_of_one_le (y : ℝ) (hy : 1 ≤ y) :
    |Formalism.Gz y| ≤ y * (y * Real.log y + Real.log y + 2) := by
  obtain ⟨hS0, hS1⟩ := zetaPrimeSum_nonneg_and_le y hy
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hp1 : 0 ≤ y * Real.log y := mul_nonneg hy0 hlog
  have hp2 : 0 ≤ y * (y * Real.log y) := mul_nonneg hy0 hp1
  have hγy : Real.eulerMascheroniConstant * y ≤ y := by nlinarith
  have hγy0 : 0 ≤ Real.eulerMascheroniConstant * y := by nlinarith
  unfold Formalism.Gz
  rw [abs_le]
  constructor <;> nlinarith

end Formalism.ZF
end
end

section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

namespace ComplexPowerDifferenceIntegral

def dz (s : ℂ) (n : ℕ) : ℂ :=
  (((n : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) - ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (1 - s) -
    (s - 1) * ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s)

def Dz (s : ℂ) : ℂ := ∑' n, dz s n

lemma norm_dz_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dz s n‖ ≤ ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [dz, d_eq ha s, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_eint_le ha hs) (norm_nonneg _)

lemma summable_shift {p : ℝ} (hp : p < -1) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  simpa [Nat.cast_add, Nat.cast_one] using h

lemma summable_norm_dz {s : ℂ} (hs : 0 < s.re) : Summable (fun n => ‖dz s n‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_dz_le hs n)
    ((summable_shift (by linarith : -s.re - 1 < -1)).mul_left _)

lemma Dz_differentiableOn : DifferentiableOn ℂ Dz {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  have hs0' : 0 < s0.re := hs0
  let U : Set ℂ := {s | s0.re / 2 < s.re} ∩ Metric.ball s0 1
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s0 ∈ U := ⟨by show s0.re / 2 < s0.re; linarith, Metric.mem_ball_self one_pos⟩
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun s => dz s n) U := by
    intro n
    apply Differentiable.differentiableOn
    intro s
    have h1 : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : ((n : ℝ) + 1) ≠ 0)
    have h2 : ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : ((n : ℝ) + 1 + 1) ≠ 0)
    unfold dz
    refine ((DifferentiableAt.sub ?_ ?_).sub ((differentiableAt_id.sub_const 1).mul ?_))
    · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h1)
    · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h2)
    · exact differentiableAt_id.neg.const_cpow (Or.inl h2)
  have hbound : ∀ n : ℕ, ∀ s ∈ U,
      ‖dz s n‖ ≤ (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) := by
    intro n s hs
    have hre : s0.re / 2 < s.re := hs.1
    have hd : ‖s - s0‖ < 1 := by
      have := hs.2
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have hpos : 0 < s.re := by linarith
    have hsR : ‖s‖ ≤ ‖s0‖ + 1 := by
      have := norm_sub_norm_le s s0
      linarith
    have hs1 : ‖s - 1‖ ≤ ‖s0‖ + 1 + 1 := by
      have := norm_sub_le s 1
      rw [norm_one] at this
      linarith
    have hp : ((n : ℝ) + 1) ^ (-s.re - 1) ≤ ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by linarith)
    calc ‖dz s n‖ ≤ ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := norm_dz_le hpos n
      _ ≤ (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) := by gcongr
  have hsum : Summable (fun n : ℕ =>
      (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1)) :=
    (summable_shift (by linarith)).mul_left _
  have hD : DifferentiableOn ℂ (fun s => ∑' n, dz s n) U :=
    differentiableOn_tsum_of_summable_norm hsum hdiff hU hbound
  exact (hD.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

end ComplexPowerDifferenceIntegral

end Formalism.ZF
end
end
