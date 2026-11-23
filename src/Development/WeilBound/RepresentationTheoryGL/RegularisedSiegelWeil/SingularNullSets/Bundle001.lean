module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Metric Complex
open scoped Topology NNReal ENNReal Real

namespace PositivityTheory.Rg.Rsw.L.LCfRel

section Circle

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem circle_swap (ν : Measure X) [IsFiniteMeasure ν] (f : ℂ → X → ℂ) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn (fun p : ℂ × X => f p.1 p.2) (sphere c R ×ˢ Set.univ)) {M : ℝ}
    (hM : ∀ z ∈ sphere c R, ∀ x, ‖f z x‖ ≤ M) :
    (∮ z in C(c, R), ∫ x, f z x ∂ν) = ∫ x, (∮ z in C(c, R), f z x) ∂ν := by
  have h1 : Continuous fun p : ℝ × X => f (circleMap c R p.1) p.2 :=
    hf.comp_continuous (((continuous_circleMap c R).comp continuous_fst).prodMk continuous_snd)
      fun p => ⟨circleMap_mem_sphere c hR p.1, Set.mem_univ _⟩
  have hG : Continuous fun p : ℝ × X => deriv (circleMap c R) p.1 • f (circleMap c R p.1) p.2 := by
    simp only [deriv_circleMap]
    exact (((continuous_circleMap 0 R).comp continuous_fst).mul continuous_const).smul h1
  have hint : Integrable (Function.uncurry fun θ x => deriv (circleMap c R) θ • f (circleMap c R θ) x)
      ((volume.restrict (Set.Ioc 0 (2 * π))).prod ν) := by
    refine Integrable.of_bound hG.aestronglyMeasurable (R * M) (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, deriv_circleMap, smul_eq_mul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one,
      abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_left (hM _ (circleMap_mem_sphere c hR p.1) p.2) hR
  simp only [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  calc ∫ θ in Set.Ioc 0 (2 * π), deriv (circleMap c R) θ • ∫ x, f (circleMap c R θ) x ∂ν
      = ∫ θ in Set.Ioc 0 (2 * π), ∫ x, deriv (circleMap c R) θ • f (circleMap c R θ) x ∂ν := by
        congr 1; ext θ; exact (integral_smul _ _).symm
    _ = _ := integral_integral_swap hint

theorem contOn_integral (ν : Measure X) [IsFiniteMeasure ν] (F : ℂ → X → ℂ) {s : Set ℂ}
    (hF : ContinuousOn (fun p : ℂ × X => F p.1 p.2) (s ×ˢ Set.univ)) {M : ℝ} (hM : ∀ z ∈ s, ∀ x, ‖F z x‖ ≤ M) :
    ContinuousOn (fun z => ∫ x, F z x ∂ν) s := by
  refine continuousOn_of_dominated (bound := fun _ => M) (fun z hz => ?_) (fun z hz => ae_of_all _ (hM z hz))
    (integrable_const M) (ae_of_all _ fun x => ?_)
  · exact (hF.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hz, Set.mem_univ _⟩).aestronglyMeasurable
  · exact hF.comp (continuous_id.prodMk continuous_const).continuousOn fun z hz => ⟨hz, Set.mem_univ _⟩

theorem diffOn_integral (ν : Measure X) [IsFiniteMeasure ν] (F : ℂ → X → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hc : ContinuousOn (fun p : ℂ × X => F p.1 p.2) (U ×ˢ Set.univ)) (hd : ∀ x, DifferentiableOn ℂ (F · x) U)
    (hb : ∀ S ⊆ U, IsCompact S → ∃ M, ∀ z ∈ S, ∀ x, ‖F z x‖ ≤ M) :
    DifferentiableOn ℂ (fun z => ∫ x, F z x ∂ν) U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  let R : ℝ≥0 := ⟨r / 2, by positivity⟩
  have hR : (0 : ℝ) < R := by show 0 < r / 2; positivity
  have hsub : closedBall z₀ R ⊆ U := (closedBall_subset_ball (show (R : ℝ) < r by show r / 2 < r; linarith)).trans hrU
  obtain ⟨M, hM⟩ := hb _ hsub (isCompact_closedBall z₀ R)
  have hsph : sphere z₀ (R : ℝ) ⊆ closedBall z₀ R := sphere_subset_closedBall
  have hcont : ContinuousOn (fun z => ∫ x, F z x ∂ν) (sphere z₀ R) :=
    contOn_integral ν F (hc.mono (Set.prod_mono (hsph.trans hsub) le_rfl)) fun z hz => hM z (hsph hz)
  have hps := hasFPowerSeriesOn_cauchy_integral (hcont.circleIntegrable hR.le) (by exact_mod_cast hR)
  have key : ∀ w ∈ ball z₀ (R : ℝ), (∫ x, F w x ∂ν) =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(z₀, R), (z - w)⁻¹ • ∫ x, F z x ∂ν := by
    intro w hw
    have hinv : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (sphere z₀ R) :=
      ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz => sub_ne_zero.2 fun h => by
        rw [mem_sphere] at hz; rw [mem_ball, ← h, hz] at hw; exact lt_irrefl _ hw
    obtain ⟨B, hB⟩ := (isCompact_sphere z₀ (R : ℝ)).exists_bound_of_continuousOn hinv
    have hsw := circle_swap ν (fun z x => (z - w)⁻¹ • F z x) z₀ hR.le
      ((hinv.comp continuousOn_fst fun (p : ℂ × X) (hp : p ∈ sphere z₀ (R : ℝ) ×ˢ (Set.univ : Set X)) => hp.1).smul (hc.mono (Set.prod_mono (hsph.trans hsub) le_rfl)))
      (M := B * M) fun z hz x => by
        rw [norm_smul]
        exact mul_le_mul (hB z hz) (hM z (hsph hz) x) (norm_nonneg _) ((norm_nonneg _).trans (hB z hz))
    have e1 : (∮ z in C(z₀, R), (z - w)⁻¹ • ∫ x, F z x ∂ν) = ∮ z in C(z₀, R), ∫ x, (z - w)⁻¹ • F z x ∂ν :=
      circleIntegral.integral_congr hR.le fun z _ => (integral_smul _ _).symm
    rw [e1, hsw]
    have e2 : ∀ x, (∮ z in C(z₀, R), (z - w)⁻¹ • F z x) = (2 * π * I : ℂ) • F w x := fun x =>
      ((hd x).mono hsub).circleIntegral_sub_inv_smul hw
    simp only [e2, integral_smul, smul_smul]
    rw [inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]
  have hev : (fun z => ∫ x, F z x ∂ν) =ᶠ[𝓝 z₀]
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(z₀, R), (z - w)⁻¹ • ∫ x, F z x ∂ν) :=
    Filter.eventually_of_mem (ball_mem_nhds z₀ hR) key
  exact (hps.analyticAt.differentiableAt.congr_of_eventuallyEq hev).differentiableWithinAt

end Circle

theorem eqOn_right {U : Set ℂ} (hUo : IsOpen U) (hU : ∃ τ : ℝ, {z : ℂ | τ < z.re} ⊆ U) (hpc : IsPreconnected U)
    {h g : ℂ → ℂ} (hh : DifferentiableOn ℂ h U) (hg : DifferentiableOn ℂ g U) (σ : ℝ)
    (e : ∀ z : ℂ, σ < z.re → h z = g z) : Set.EqOn h g U := by
  obtain ⟨τ, hτ⟩ := hU
  have hx : max τ σ < (((max τ σ + 1 : ℝ)) : ℂ).re := by simp
  have hxU : (((max τ σ + 1 : ℝ)) : ℂ) ∈ U := hτ (lt_of_le_of_lt (le_max_left _ _) hx)
  have ev : h =ᶠ[𝓝 (((max τ σ + 1 : ℝ)) : ℂ)] g := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx] with w hw
    exact e w (lt_of_le_of_lt (le_max_right _ _) hw)
  exact (hh.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo) hpc hxU ev

theorem integral_tsum_dom {ι α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ι → α → ℂ) (u : ι → ℝ) (hu : Summable u) (hF : ∀ i a, ‖F i a‖ ≤ u i)
    (hm : ∀ i, AEStronglyMeasurable (F i) μ) :
    ∫ a, ∑' i, F i a ∂μ = ∑' i, ∫ a, F i a ∂μ := by
  have hs := hu.countable_support
  have : Countable (Function.support u) := hs.to_subtype
  have h0 : ∀ i, i ∉ Function.support u → ∀ a, F i a = 0 := fun i hi a => by
    have : u i = 0 := Function.notMem_support.1 hi
    exact norm_le_zero_iff.1 (this ▸ hF i a)
  have e1 : ∀ a, ∑' i, F i a = ∑' i : Function.support u, F i a := fun a =>
    (tsum_subtype_eq_of_support_subset fun i hi => by_contra fun h => hi (h0 i h a)).symm
  have e2 : ∑' i, ∫ a, F i a ∂μ = ∑' i : Function.support u, ∫ a, F i a ∂μ :=
    (tsum_subtype_eq_of_support_subset fun i hi => by_contra fun h => hi (by simp [h0 i h])).symm
  simp_rw [e1, e2]
  have hI : ∀ i, Integrable (F i) μ := fun i => Integrable.of_bound (hm i) (u i) (ae_of_all _ (hF i))
  refine (integral_tsum_of_summable_integral_norm (ι := Function.support u) (F := fun i a => F i a) (fun i => hI i) ?_).symm
  refine ((hu.subtype _).mul_right (μ.real Set.univ)).of_nonneg_of_le
    (fun i => integral_nonneg fun _ => norm_nonneg _) fun i => ?_
  calc ∫ a, ‖F i a‖ ∂μ ≤ ∫ _, u i ∂μ := integral_mono (hI i).norm (integrable_const _) fun a => hF i a
    _ = u i * μ.real Set.univ := by simp [mul_comm]

theorem circle_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (g : ι → ℂ → ℂ) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hg : ∀ i ∈ s, ContinuousOn (g i) (sphere c R)) :
    (∮ z in C(c, R), ∑ i ∈ s, a i * g i z) = ∑ i ∈ s, a i * ∮ z in C(c, R), g i z := by
  have hc : ∀ i ∈ s, Continuous fun θ => deriv (circleMap c R) θ • (a i * g i (circleMap c R θ)) := fun i hi => by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).mul continuous_const).smul (continuous_const.mul
      ((hg i hi).comp_continuous (continuous_circleMap c R) fun θ => circleMap_mem_sphere c hR θ))
  simp only [circleIntegral, Finset.smul_sum]
  rw [intervalIntegral.integral_finsetSum fun i hi => (hc i hi).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  congr 1; ext θ; simp only [smul_eq_mul]; ring

end PositivityTheory.Rg.Rsw.L.LCfRel

end
end

section

noncomputable section

open MeasureTheory Filter Metric Complex
open scoped Topology NNReal ENNReal Real

namespace PositivityTheory.Rg.Rsw.L.LCfRel

theorem circle_entire_mul (c : ℂ → ℂ) (hc : Differentiable ℂ c) (f : ℂ → ℂ) (s₀ : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hf : ContinuousOn f (sphere s₀ ε)) (k : ℕ) (hk : 1 ≤ k)
    (h0 : ∀ j, k < j → (∮ z in C(s₀, ε), (z - s₀) ^ (j - 1) * f z) = 0) :
    (∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (c z * f z)) = c s₀ * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * f z := by
  obtain ⟨M, hM⟩ := (isCompact_sphere s₀ ε).exists_bound_of_continuousOn hf
  have hps := hc.hasFPowerSeriesOnBall s₀ (R := 1) one_pos
  set p := cauchyPowerSeries c s₀ 1 with hp
  have hfc : Continuous fun θ => f (circleMap s₀ ε θ) :=
    hf.comp_continuous (continuous_circleMap s₀ ε) fun θ => circleMap_mem_sphere s₀ hε.le θ
  let T : ℕ → ℝ → ℂ := fun i θ => deriv (circleMap s₀ ε) θ •
    ((circleMap s₀ ε θ - s₀) ^ (k - 1) * ((circleMap s₀ ε θ - s₀) ^ i * p.coeff i * f (circleMap s₀ ε θ)))
  have hT : ∀ i, Continuous (T i) := fun i => by
    simp only [T, deriv_circleMap]
    exact ((continuous_circleMap 0 ε).mul continuous_const).smul
      ((((continuous_circleMap s₀ ε).sub continuous_const).pow _).mul
        (((((continuous_circleMap s₀ ε).sub continuous_const).pow _).mul continuous_const).mul hfc))
  have hsum : HasSum (fun i => ∫ θ in (0 : ℝ)..2 * π, T i θ)
      (∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (c z * f z)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun i _ => ε * ε ^ (k - 1) * M * (‖p i‖ * ε ^ i)) (fun i => (hT i).aestronglyMeasurable)
      (fun i => ae_of_all _ fun θ _ => ?_) (ae_of_all _ fun θ _ => ?_) intervalIntegrable_const
      (ae_of_all _ fun θ _ => ?_)
    · have h1 : ‖circleMap s₀ ε θ - s₀‖ = ε := by rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hε]
      have h2 := hM _ (circleMap_mem_sphere s₀ hε.le θ)
      simp only [T, deriv_circleMap, smul_eq_mul, norm_mul, norm_pow, h1, norm_circleMap_zero, abs_of_pos hε,
        Complex.norm_I, mul_one, ← p.norm_apply_eq_norm_coef]
      have hpos : 0 ≤ ε * ε ^ (k - 1) * (‖p i‖ * ε ^ i) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 hpos]
    · have hr : ((ε.toNNReal : ℝ≥0) : ℝ≥0∞) < p.radius := lt_of_lt_of_le ENNReal.coe_lt_top hps.r_le
      have hs : Summable fun n => ‖p n‖ * ε ^ n := by
        simpa [Real.coe_toNNReal _ hε.le] using p.summable_norm_mul_pow hr
      exact hs.mul_left _
    · have := hps.hasSum_sub (y := circleMap s₀ ε θ) (Metric.mem_eball.2 (edist_lt_top _ _))
      simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] at this
      exact ((this.mul_right (f (circleMap s₀ ε θ))).mul_left ((circleMap s₀ ε θ - s₀) ^ (k - 1))).const_smul _
  have hterm : ∀ i, ∫ θ in (0 : ℝ)..2 * π, T i θ = p.coeff i * ∮ z in C(s₀, ε), (z - s₀) ^ (k + i - 1) * f z := by
    intro i
    simp only [circleIntegral, T]
    rw [← intervalIntegral.integral_const_mul, show k + i - 1 = k - 1 + i by omega]
    congr 1; ext θ
    simp only [smul_eq_mul, pow_add]; ring
  have hc0 : p.coeff 0 = c s₀ := hps.hasFPowerSeriesAt.coeff_zero 1
  have hval : (fun i => ∫ θ in (0 : ℝ)..2 * π, T i θ) =
      fun i => if i = 0 then c s₀ * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * f z else 0 := by
    funext i; rw [hterm]; split_ifs with h
    · subst h; rw [hc0, Nat.add_zero]
    · rw [h0 (k + i) (by omega), mul_zero]
  rw [hval] at hsum
  exact hsum.unique (hasSum_ite_eq 0 _)

end PositivityTheory.Rg.Rsw.L.LCfRel

end
end

section

noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

open Metric
open scoped ContDiff

def lmajABump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

lemma lmajABump_bound (m : ℕ) : ∃ C, ∀ t : ℝ, ‖iteratedFDeriv ℝ m lmajABump t‖ ≤ C :=
  ((lmajABump.contDiff (n := ⊤)).continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
    (lmajABump.hasCompactSupport.iteratedFDeriv m)

lemma lmajABump_deriv_zero (m : ℕ) (t : ℝ) (ht : 2 < |t|) : iteratedFDeriv ℝ m lmajABump t = 0 := by
  by_contra hne
  have h1 : t ∈ tsupport (lmajABump : ℝ → ℝ) := support_iteratedFDeriv_subset m hne
  rw [lmajABump.tsupport_eq, mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  exact absurd h1 (by simp [lmajABump]; linarith)

theorem lmajASeqSchwartz (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ k : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ k)) :
    ∃ h : SchwartzMap ℝ ℂ, (∀ t, 0 ≤ (h t).re ∧ (h t).im = 0) ∧
      ∀ (n : ℕ) (t : ℝ), |t - n| ≤ 1 → b n ≤ (h t).re := by
  choose C hC using lmajABump_bound
  set φ : ℕ → ℝ → ℝ := fun n => b n • fun t => lmajABump (t - n) with hφ
  have hφc : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ n) := fun n =>
    ((lmajABump.contDiff).comp (contDiff_id.sub contDiff_const)).const_smul (b n)
  have hD : ∀ m n t, iteratedFDeriv ℝ m (φ n) t = b n • iteratedFDeriv ℝ m lmajABump (t - n) := by
    intro m n t
    have hc : ContDiff ℝ m (fun t : ℝ => lmajABump (t - n)) :=
      (lmajABump.contDiff).comp (contDiff_id.sub contDiff_const)
    rw [hφ]
    simp only
    rw [iteratedFDeriv_const_smul_apply hc.contDiffAt, iteratedFDeriv_comp_sub]
  have hs0 : Summable b := by simpa using hb 0
  have hv : ∀ m : ℕ, ((m : ℕ∞)) ≤ (⊤ : ℕ∞) → Summable (fun n => b n * C m) :=
    fun m _ => hs0.mul_right _
  have hbd : ∀ (m : ℕ) (n : ℕ) (t : ℝ), ((m : ℕ∞)) ≤ (⊤ : ℕ∞) →
      ‖iteratedFDeriv ℝ m (φ n) t‖ ≤ b n * C m := by
    intro m n t _
    rw [hD, norm_smul, Real.norm_of_nonneg (hb0 n)]
    exact mul_le_mul_of_nonneg_left (hC m _) (hb0 n)
  set g : ℝ → ℝ := fun t => ∑' n, φ n t with hg
  have hgc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := contDiff_tsum hφc hv hbd
  have hφv : ∀ n t, φ n t = b n * lmajABump (t - n) := fun n t => rfl
  have hφs : ∀ t, Summable (fun n => φ n t) := by
    intro t
    refine hs0.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · rw [hφv]; exact mul_nonneg (hb0 n) (lmajABump.nonneg)
    · rw [hφv]; exact mul_le_of_le_one_right (hb0 n) (lmajABump.le_one)
  have hg0 : ∀ t, 0 ≤ g t := fun t => tsum_nonneg fun n => by
    rw [hφv]; exact mul_nonneg (hb0 n) (lmajABump.nonneg)
  have hdecay : ∀ k m : ℕ, ∀ t : ℝ, ‖t‖ ^ k * ‖iteratedFDeriv ℝ m g t‖ ≤
      ∑' n, b n * ((n : ℝ) + 2) ^ k * C m := by
    intro k m t
    rw [hg, iteratedFDeriv_tsum_apply hφc hv hbd (mod_cast le_top) t]
    have hsn : Summable (fun n => ‖iteratedFDeriv ℝ m (φ n) t‖) :=
      (hv m le_top).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbd m n t le_top)
    calc ‖t‖ ^ k * ‖∑' n, iteratedFDeriv ℝ m (φ n) t‖
        ≤ ‖t‖ ^ k * ∑' n, ‖iteratedFDeriv ℝ m (φ n) t‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsn) (by positivity)
      _ = ∑' n, ‖t‖ ^ k * ‖iteratedFDeriv ℝ m (φ n) t‖ := (tsum_mul_left).symm
      _ ≤ ∑' n, b n * ((n : ℝ) + 2) ^ k * C m := by
          refine (hsn.mul_left _).tsum_le_tsum (fun n => ?_) ((hb k).mul_right _)
          rw [hD, norm_smul, Real.norm_of_nonneg (hb0 n)]
          by_cases htn : |t - n| ≤ 2
          · have h1 : ‖t‖ ≤ (n : ℝ) + 2 := by
              rw [Real.norm_eq_abs]
              have := abs_sub_abs_le_abs_sub t n
              rw [Nat.abs_cast] at this
              linarith
            have h2 : ‖t‖ ^ k ≤ ((n : ℝ) + 2) ^ k := pow_le_pow_left₀ (norm_nonneg _) h1 k
            have hCm : 0 ≤ C m := (norm_nonneg _).trans (hC m 0)
            calc ‖t‖ ^ k * (b n * ‖iteratedFDeriv ℝ m (lmajABump : ℝ → ℝ) (t - n)‖)
                ≤ ((n : ℝ) + 2) ^ k * (b n * C m) :=
                  mul_le_mul h2 (mul_le_mul_of_nonneg_left (hC m _) (hb0 n)) (mul_nonneg (hb0 n) (norm_nonneg _))
                    (by positivity)
              _ = b n * ((n : ℝ) + 2) ^ k * C m := by ring
          · rw [lmajABump_deriv_zero m _ (not_le.mp htn), norm_zero, mul_zero, mul_zero]
            have hCm : 0 ≤ C m := (norm_nonneg _).trans (hC m 0)
            exact mul_nonneg (mul_nonneg (hb0 n) (by positivity)) hCm
  refine ⟨⟨Complex.ofRealLI ∘ g, ?_, ?_⟩, ?_, ?_⟩
  · exact Complex.ofRealLI.contDiff.comp hgc
  · intro k m
    refine ⟨∑' n, b n * ((n : ℝ) + 2) ^ k * C m, fun t => ?_⟩
    rw [LinearIsometry.norm_iteratedFDeriv_comp_left _ hgc.contDiffAt (mod_cast le_top)]
    exact hdecay k m t
  · intro t
    show 0 ≤ (Complex.ofRealLI (g t)).re ∧ (Complex.ofRealLI (g t)).im = 0
    simp [hg0 t]
  · intro n t ht
    have h1 : (t - n) ∈ closedBall (0 : ℝ) lmajABump.rIn := by
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]; simpa [lmajABump] using ht
    have h2 : φ n t = b n := by rw [hφv, lmajABump.one_of_mem_closedBall h1, mul_one]
    show b n ≤ (Complex.ofRealLI (g t)).re
    simp only [Complex.ofRealLI_apply, Complex.ofReal_re]
    rw [← h2]
    exact (hφs t).le_tsum n (fun j _ => by rw [hφv]; exact mul_nonneg (hb0 j) (lmajABump.nonneg))

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

section

noncomputable section

open Set MeasureTheory CompactlySupported

namespace PositivityTheory.Rg.Rsw.L.LPosExt

variable {X : Type} [TopologicalSpace X]

def AR (A : Submodule ℂ (X → ℂ)) : Submodule ℝ (X → ℂ) where
  carrier := {f | f ∈ A ∧ ∀ x, (f x).im = 0}
  add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨A.add_mem ha hb, fun x => by simp [ha' x, hb' x]⟩
  zero_mem' := ⟨A.zero_mem, fun x => by simp⟩
  smul_mem' c f := fun ⟨hf, hf'⟩ => ⟨by
      have : c • f = (c : ℂ) • f := by ext x; simp [Complex.real_smul]
      rw [this]; exact A.smul_mem _ hf, fun x => by simp [hf' x]⟩

def reC (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f) :
    AR A →ₗ[ℝ] C_c(X, ℝ) where
  toFun f := ⟨⟨fun x => (f.1 x).re, Complex.continuous_re.comp (hA _ f.2.1).1⟩,
    (hA _ f.2.1).2.comp_left Complex.zero_re⟩
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

theorem reC_inj (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f) :
    Function.Injective (reC A hA) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  have h := congrArg (fun u : C_c(X, ℝ) => u x) hfg
  simp only [reC, LinearMap.coe_mk, AddHom.coe_mk] at h
  exact Complex.ext h ((f.2.2 x).trans (g.2.2 x).symm)

def reL (A : Submodule ℂ (X → ℂ)) (L : A →ₗ[ℂ] ℂ) : AR A →ₗ[ℝ] ℝ where
  toFun f := (L ⟨f.1, f.2.1⟩).re
  map_add' f g := by
    have : (⟨(f + g).1, (f + g).2.1⟩ : A) = ⟨f.1, f.2.1⟩ + ⟨g.1, g.2.1⟩ := rfl
    simp only [this, map_add (f := _), Complex.add_re]
  map_smul' c f := by
    have : (⟨(c • f).1, (c • f).2.1⟩ : A) = (c : ℂ) • ⟨f.1, f.2.1⟩ := by
      apply Subtype.ext; ext x; simp [Complex.real_smul]
    simp only [this, map_smul, smul_eq_mul, Complex.re_ofReal_mul, RingHom.id_apply]

theorem dom (A : Submodule ℂ (X → ℂ))
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    {y : X → ℝ} (hy : Continuous y) (hyc : HasCompactSupport y) :
    ∃ b ∈ A, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x, 0 ≤ M * (b x).re + y x ∧ 0 ≤ M * (b x).re - y x := by
  obtain ⟨b, hbA, hb0, hb1⟩ := hbump (tsupport y) hyc
  obtain ⟨C, hC⟩ := hy.bounded_above_of_compact_support hyc
  refine ⟨b, hbA, hb0, max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport y
  · rw [hb1 x hx, Complex.one_re, mul_one]
    have := hC x
    rw [Real.norm_eq_abs] at this
    constructor <;> linarith [abs_le.mp this, le_max_left C 0]
  · rw [image_eq_zero_of_notMem_tsupport hx]
    have := mul_nonneg (le_max_right C 0) (hb0 x).1
    constructor <;> linarith

end PositivityTheory.Rg.Rsw.L.LPosExt
end
end
