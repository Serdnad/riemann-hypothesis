module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.Complete
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Fourier.AddCircle
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

section

noncomputable section

namespace PI.SSU

open Complex Filter Topology

theorem siegel_set_completeness : Complete := by
  intro f hf hper hcoef
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hpr : Function.Periodic (fun x : ℝ => f x) 1 := fun x => by
    simpa using hper (x : ℂ)
  have hcont : Continuous (fun x : ℝ => f x) := hf.continuous.comp Complex.continuous_ofReal
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hpr.lift, by
    first
      | exact continuous_coinduced_dom.mpr hcont
      | exact hcont.quotient_liftOn' _
      | exact (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr hcont⟩
  have hF : ∀ x : ℝ, F x = f x := fun x => rfl
  have hcF : ∀ n : ℤ, fourierCoeff F n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
    have h1 : ∫ x in (0 : ℝ)..1, fourier (-n) (x : AddCircle (1 : ℝ)) • F x = coef f n := by
      unfold coef
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [fourier_coe_apply, hF, smul_eq_mul]
      push_cast
      ring_nf
    rw [h1, hcoef n, smul_zero]
  have hL : ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ F = 0 := by
    have hs := hasSum_fourier_series_L2 (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ F)
    simp only [fourierCoeff_toLp, hcF, zero_smul] at hs
    exact hs.unique hasSum_zero
  have hF0 : F = 0 := by
    first
      | exact ContinuousMap.toLp_injective AddCircle.haarAddCircle (hL.trans (map_zero _).symm)
      | exact ContinuousMap.toLp_injective (p := 2) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ)
          (hL.trans (map_zero _).symm)
  have hreal : ∀ x : ℝ, f x = 0 := fun x => by
    have := DFunLike.congr_fun hF0 (x : AddCircle (1 : ℝ))
    rwa [hF, ContinuousMap.zero_apply] at this
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 := by
    have ht : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [Function.comp_def] using this
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        exact (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).ne'
    exact ht.frequently (Frequently.of_forall fun n => hreal _)
  funext z
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0)
    hfreq (Set.mem_univ z)

end PI.SSU
end
end

section

noncomputable section

namespace PI.SSU

open Complex

theorem siegel_set_shift_invariance : ShiftInv := by
  intro f hf hper w n
  set g : ℂ → ℂ := fun z => f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z)) with hg
  have hgd : Differentiable ℂ g := by
    show Differentiable ℂ (fun z => f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z)))
    exact hf.mul (by fun_prop)

  have hgp : ∀ z, g (z + 1) = g z := by
    intro z
    show f (z + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (z + 1))) =
      f z * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * z))
    rw [hper z]
    congr 1
    rw [show -(2 * (Real.pi : ℂ) * I * n * (z + 1)) =
        -(2 * (Real.pi : ℂ) * I * n * z) + -((n : ℂ) * (2 * Real.pi * I)) by ring,
      Complex.exp_add, Complex.exp_neg ((n : ℂ) * _), Complex.exp_int_mul_two_pi_mul_I, inv_one, mul_one]

  have hvert : ∀ b : ℝ, ∫ x in (0 : ℝ)..1, g (x + b * I) = ∫ x in (0 : ℝ)..1, g x := by
    intro b
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g 0 (1 + b * I)
      hgd.differentiableOn
    have h1 : ((1 : ℂ) + b * I).re = 1 := by simp
    have h2 : ((1 : ℂ) + b * I).im = b := by simp
    rw [h1, h2, Complex.zero_re, Complex.zero_im] at hrect
    have hs : (fun y : ℝ => g (((1 : ℝ) : ℂ) + y * I)) = fun y : ℝ => g (((0 : ℝ) : ℂ) + y * I) := by
      funext y
      rw [← hgp (((0 : ℝ) : ℂ) + y * I)]
      congr 1
      push_cast
      ring
    rw [hs, add_sub_cancel_right, sub_eq_zero] at hrect
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hrect
    exact hrect.symm

  have hH : Function.Periodic (fun y : ℝ => g (y + w.im * I)) 1 := by
    intro y
    show g (((y + 1 : ℝ) : ℂ) + w.im * I) = g ((y : ℂ) + w.im * I)
    rw [← hgp ((y : ℂ) + w.im * I)]
    congr 1
    push_cast
    ring
  have hw : ∀ x : ℝ, (x : ℂ) + w = ((x + w.re : ℝ) : ℂ) + w.im * I := by
    intro x
    apply Complex.ext <;> simp
  calc ∫ x in (0 : ℝ)..1, f (x + w) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (x + w)))
      = ∫ x in (0 : ℝ)..1, (fun y : ℝ => g (y + w.im * I)) (x + w.re) := by
        congr 1
        funext x
        show g ((x : ℂ) + w) = g (((x + w.re : ℝ) : ℂ) + w.im * I)
        rw [hw x]
    _ = ∫ x in (0 + w.re)..(1 + w.re), (fun y : ℝ => g (y + w.im * I)) x :=
        intervalIntegral.integral_comp_add_right (fun y : ℝ => g (y + w.im * I)) w.re
    _ = ∫ x in (0 : ℝ)..(0 + 1), (fun y : ℝ => g (y + w.im * I)) x := by
        rw [zero_add w.re, add_comm 1 w.re]
        exact hH.intervalIntegral_add_eq w.re 0
    _ = ∫ x in (0 : ℝ)..1, g (x + w.im * I) := by rw [zero_add]
    _ = ∫ x in (0 : ℝ)..1, g x := hvert w.im
    _ = coef f n := rfl

end PI.SSU
end
end

section

noncomputable section

namespace PI.SSU

open Complex

theorem coef_shift (hS : ShiftInv) (f : ℂ → ℂ) (τ K : ℂ) (k : ℤ) (hf : Differentiable ℂ f)
    (h1 : ∀ u, f (u + 1) = f u)
    (hτ : ∀ u, f (u + τ) = K * Complex.exp (-(2 * (Real.pi : ℂ) * I * k * u)) * f u) (n : ℤ) :
    coef f n = K * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * τ)) * coef f (n + k) := by
  rw [← hS f hf h1 τ n, ← hS f hf h1 0 (n + k), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [hτ, add_zero]
  have e : cexp (-(2 * (Real.pi : ℂ) * I * k * x)) * cexp (-(2 * (Real.pi : ℂ) * I * n * (x + τ))) =
      cexp (-(2 * (Real.pi : ℂ) * I * n * τ)) * cexp (-(2 * (Real.pi : ℂ) * I * ((n + k : ℤ) : ℂ) * x)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (K * f x) * e

theorem key_of (hS : ShiftInv) (hC : Complete) : KeyP := by
  intro f τ K k hf hK hk h1 hτ h0
  apply hC f hf h1
  have hrel : ∀ n : ℤ, coef f n = 0 ↔ coef f (n + k) = 0 := by
    intro n
    rw [coef_shift hS f τ K k hf h1 hτ n, mul_eq_zero,
      or_iff_right (mul_ne_zero hK (Complex.exp_ne_zero _))]
  have H : ∀ n : ℤ, coef f n = 0 ↔ coef f (n + 1) = 0 := by
    intro n
    rcases hk with rfl | rfl
    · exact hrel n
    · have := hrel (n + 1)
      rw [show n + 1 + -1 = n by ring] at this
      exact this.symm
  intro n
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i hi => exact (H i).mp hi
  | pred i hi =>
    have := H (-(i:ℤ) - 1)
    rw [show -(i:ℤ) - 1 + 1 = -i by ring] at this
    exact this.mpr hi

end PI.SSU
end
end
