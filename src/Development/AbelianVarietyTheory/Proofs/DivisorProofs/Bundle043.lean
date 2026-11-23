module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.MatrixAlgebra

@[expose] public section

section

open scoped ContDiff

namespace GlobalTheory

theorem contDiff_tsum_of_locally_summable_bounds {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ)
    (hf : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i))
    (hu : ∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧
      ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by
  choose u hus hub using hu
  have hinf : ((⊤ : ℕ∞) : WithTop ℕ∞) = ∞ := rfl
  rw [hinf] at hf ⊢
  rw [contDiff_infty]
  intro n
  rw [contDiff_iff_contDiffAt]
  intro t₀
  let ρ : ContDiffBump t₀ := ⟨1/2, 1, by norm_num, by norm_num⟩
  set R : ℝ := ‖t₀‖ + 1 with hR
  let ρc : (Fin k → ℝ) → ℂ := fun t => ((ρ t : ℝ) : ℂ)
  have hρc : ContDiff ℝ ∞ ρc := Complex.ofRealCLM.contDiff.comp ρ.contDiff
  have hρcs : HasCompactSupport ρc := ρ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hB : ∀ j : ℕ, ∃ B, ∀ x, ‖iteratedFDeriv ℝ j ρc x‖ ≤ B := fun j =>
    (hρc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hρcs.iteratedFDeriv j)
  choose B hB using hB
  have hsupp : ∀ j x, x ∉ Metric.closedBall t₀ 1 → iteratedFDeriv ℝ j ρc x = 0 := by
    intro j x hx
    by_contra h
    have hx1 : x ∈ tsupport ρc := support_iteratedFDeriv_subset j h
    have h2 : tsupport ρc ⊆ tsupport (ρ : (Fin k → ℝ) → ℝ) :=
      tsupport_comp_subset Complex.ofReal_zero _
    rw [ρ.tsupport_eq] at h2
    exact hx (h2 hx1)
  have hunonneg : ∀ m i, 0 ≤ u m R i := fun m i =>
    (norm_nonneg _).trans (hub m R i 0 (by rw [norm_zero, hR]; positivity))
  have hB0 : ∀ j, 0 ≤ B j := fun j => (norm_nonneg _).trans (hB j 0)
  let v : ℕ → ι → ℝ := fun m i =>
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * B j * u (m - j) R i
  have hv : ∀ m, Summable (v m) := fun m => by
    apply summable_sum
    intro j _
    exact (hus (m - j) R).mul_left _
  have hbound : ∀ m i x, ‖iteratedFDeriv ℝ m (fun y => ρc y * f i y) x‖ ≤ v m i := by
    intro m i x
    refine (norm_iteratedFDeriv_mul_le hρc (hf i) x (by exact_mod_cast le_top)).trans ?_
    apply Finset.sum_le_sum
    intro j _
    by_cases hx : x ∈ Metric.closedBall t₀ 1
    · have hxR : ‖x‖ ≤ R := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        have := norm_sub_norm_le x t₀
        rw [hR]; linarith
      apply mul_le_mul _ (hub _ _ _ _ hxR) (norm_nonneg _)
        (mul_nonneg (by positivity) (hB0 j))
      exact mul_le_mul_of_nonneg_left (hB j x) (by positivity)
    · rw [hsupp j x hx, norm_zero, mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (by positivity) (hB0 j)) (hunonneg _ _)
  have hsm : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, ρc t * f i t) :=
    contDiff_tsum (fun i => (hρc.mul (hf i)).of_le (by exact_mod_cast le_top))
      (fun m _ => hv m) (fun m i x _ => hbound m i x)
  have heq : (fun t => ∑' i, f i t) =ᶠ[nhds t₀] (fun t => ∑' i, ρc t * f i t) := by
    filter_upwards [Metric.closedBall_mem_nhds t₀ (by norm_num : (0:ℝ) < 1/2)] with t ht
    rw [tsum_mul_left]
    have h1 : ρ t = 1 := ρ.one_of_mem_closedBall ht
    simp [ρc, h1]
  exact (hsm.contDiffAt).congr_of_eventuallyEq heq

end GlobalTheory
end

section

open scoped ContDiff

namespace GlobalTheory

open intervalIntegral Filter Topology

theorem bichar_deriv_contDiff (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ)
    (hQ : Continuous (Function.uncurry Q))
    (hs : ∀ t s s', Q t (s + s') = Q t s * Q t s')
    (ht : ∀ t t' s, Q (t + t') s = Q t s * Q t' s)
    (h0 : ∀ t, Q t 0 = 1) :
    ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := by
  have hQt : ∀ t, Continuous (Q t) := fun t =>
    hQ.comp (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (t, s))
  set g : (Fin k → ℝ) → ℝ → ℂ := fun t δ => ∫ r in (0:ℝ)..δ, Q t r with hgdef
  have hg : ∀ t x, HasDerivAt (g t) (Q t x) x := fun t x =>
    ((hQt t).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hid : ∀ t s δ, Q t s * g t δ = g t (s + δ) - g t s := by
    intro t s δ
    have hint : ∀ a b : ℝ, IntervalIntegrable (Q t) MeasureTheory.volume a b :=
      fun a b => (hQt t).intervalIntegrable a b
    simp only [hgdef]
    rw [integral_interval_sub_left (hint _ _) (hint _ _)]
    have h1 : ∫ x in (0:ℝ)..δ, Q t (x + s) = ∫ x in s..s + δ, Q t x := by
      rw [intervalIntegral.integral_comp_add_right (fun x => Q t x) s]
      simp [add_comm]
    rw [← h1]
    simp_rw [hs, intervalIntegral.integral_mul_const]
    ring
  have hder : ∀ t δ, g t δ ≠ 0 → ∀ s,
      HasDerivAt (Q t) ((Q t (s + δ) - Q t s) / g t δ) s := by
    intro t δ hδ s
    have heq : Q t = fun u => (g t (u + δ) - g t u) / g t δ := by
      funext u; rw [← hid t u δ, mul_div_cancel_right₀ _ hδ]
    have ha : HasDerivAt (fun u => g t (u + δ)) (Q t (s + δ)) s :=
      HasDerivAt.comp_add_const s δ (hg t (s + δ))
    have h1 : HasDerivAt (fun u => (g t (u + δ) - g t u) / g t δ)
        ((Q t (s + δ) - Q t s) / g t δ) s := (ha.sub (hg t s)).div_const _
    rwa [← heq] at h1
  have hex : ∀ t, ∃ δ, g t δ ≠ 0 := by
    intro t
    have h := (hg t 0).eventually_ne (c := 0) (by rw [h0]; exact one_ne_zero)
    obtain ⟨z, hz⟩ := h.exists
    refine ⟨z, ?_⟩
    simpa [hgdef] using hz
  have hd : ∀ t, HasDerivAt (Q t) (deriv (Q t) 0) 0 := by
    intro t
    obtain ⟨δ, hδ⟩ := hex t
    exact (hder t δ hδ 0).differentiableAt.hasDerivAt
  have hadd : ∀ t t', deriv (Q (t + t')) 0 = deriv (Q t) 0 + deriv (Q t') 0 := by
    intro t t'
    have e : Q (t + t') = Q t * Q t' := funext fun s => by rw [Pi.mul_apply, ht]
    have hm := (hd t).mul (hd t')
    rw [← e] at hm
    rw [hm.deriv, h0, h0]; ring
  let c : (Fin k → ℝ) →+ ℂ := AddMonoidHom.mk' (fun t => deriv (Q t) 0) hadd
  have hQ0 : ∀ s, Q 0 s = 1 := by
    intro s
    have h1 : Q 0 s = Q 0 s * Q 0 s := by simpa using ht 0 0 s
    have h2 : Q 0 s * Q 0 (-s) = 1 := by rw [← hs, add_neg_cancel, h0]
    have hne : Q 0 s ≠ 0 := left_ne_zero_of_mul_eq_one h2
    have := mul_left_cancel₀ hne (h1.symm.trans (mul_one _).symm)
    exact this
  have hgc : Continuous fun t => g t 1 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hQ 0 1
  have hg01 : g 0 1 = 1 := by simp [hgdef, hQ0]
  have hne : ∀ᶠ t in 𝓝 (0 : Fin k → ℝ), g t 1 ≠ 0 :=
    hgc.continuousAt.eventually_ne (by rw [hg01]; exact one_ne_zero)
  have hc0 : ContinuousAt c 0 := by
    have hQ1 : Continuous fun t => Q t 1 :=
      hQ.comp (continuous_id.prodMk continuous_const : Continuous fun t => (t, (1:ℝ)))
    have hf : ContinuousAt (fun t => (Q t 1 - 1) / g t 1) 0 :=
      ((hQ1.sub continuous_const).continuousAt).div hgc.continuousAt (by rw [hg01]; exact one_ne_zero)
    refine hf.congr ?_
    filter_upwards [hne] with t htne
    have := (hder t 1 htne 0).deriv
    simp only [zero_add, h0] at this
    simp [c, this]
  have hcc : Continuous c := continuous_of_continuousAt_zero c hc0
  have : (fun t => deriv (Q t) 0) = ⇑(c.toRealLinearMap hcc) := by
    funext t; simp [c]
  rw [this]
  exact (c.toRealLinearMap hcc).contDiff

end GlobalTheory
end

section

open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace GlobalTheory

theorem fderiv_integral_mul_kernel_apply :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
      [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] {U : Set V}, IsOpen U →
      ∀ {α : V → ℂ}, Continuous α → HasCompactSupport α → tsupport α ⊆ U →
      ∀ {K : V × V → ℂ}, ContDiffOn ℝ ∞ K (U ×ˢ U) → ∀ {x : V}, x ∈ U → ∀ v : V,
      fderiv ℝ (fun x' => ∫ y, α y * K (x', y) ∂ν) x v =
        ∫ y, α y * fderiv ℝ (fun x' => K (x', y)) x v ∂ν := by
  intro V _ _ _ _ _ ν _ U hU α hα hαc hαU K hK x hx v
  have hUU : IsOpen (U ×ˢ U) := hU.prod hU
  have hα0 : ∀ y, y ∉ U → α y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hαU h))

  have hKd : ∀ p ∈ U ×ˢ U, HasFDerivAt K (fderiv ℝ K p) p := fun p hp =>
    ((hK.differentiableOn (by simp)) p hp).differentiableAt
      (hUU.mem_nhds hp) |>.hasFDerivAt
  have hKp : ∀ x' ∈ U, ∀ y ∈ U,
      HasFDerivAt (fun x'' => K (x'', y)) ((fderiv ℝ K (x', y)).comp (ContinuousLinearMap.inl ℝ V V)) x' :=
    fun x' hx' y hy => (hKd (x', y) ⟨hx', hy⟩).comp x' (hasFDerivAt_prodMk_left x' y)
  have hcf : ContinuousOn (fderiv ℝ K) (U ×ˢ U) :=
    hK.continuousOn_fderiv_of_isOpen hUU (by exact_mod_cast le_top)
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.mp hU x hx
  set r := ε / 2 with hr
  have rpos : 0 < r := half_pos εpos
  have hcb : closedBall x r ⊆ U := (closedBall_subset_ball (half_lt_self εpos)).trans hε
  have hcomp : IsCompact (closedBall x r ×ˢ tsupport α) :=
    (isCompact_closedBall x r).prod hαc
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
    (hcf.mono (Set.prod_mono hcb hαU))
  set F' : V → V → V →L[ℝ] ℂ :=
    fun x' y => α y • (fderiv ℝ K (x', y)).comp (ContinuousLinearMap.inl ℝ V V) with hF'
  have hcontF : ∀ x' ∈ U, Continuous (fun y => α y * K (x', y)) := by
    intro x' hx'
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((tsupport_mul_subset_left).trans hαU)
    refine hα.continuousOn.mul ?_
    exact hK.continuousOn.comp (Continuous.continuousOn (by fun_prop))
      (fun y hy => ⟨hx', hy⟩)
  have hcontF' : Continuous (F' x) := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((tsupport_smul_subset_left _ _).trans hαU)
    refine hα.continuousOn.smul ?_
    have h1 : ContinuousOn (fun y => fderiv ℝ K (x, y)) U :=
      hcf.comp (Continuous.continuousOn (by fun_prop)) (fun y hy => ⟨hx, hy⟩)
    exact h1.clm_comp continuousOn_const
  have hbound : ∀ y, ∀ x' ∈ ball x r, ‖F' x' y‖ ≤ ‖α y‖ * C := by
    intro y x' hx'
    by_cases hy : y ∈ tsupport α
    · rw [hF', norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖(fderiv ℝ K (x', y)).comp (ContinuousLinearMap.inl ℝ V V)‖
          ≤ ‖fderiv ℝ K (x', y)‖ * ‖ContinuousLinearMap.inl ℝ V V‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ K (x', y)‖ * 1 :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ V V) (norm_nonneg _)
        _ ≤ C := by rw [mul_one]; exact hC _ ⟨ball_subset_closedBall hx', hy⟩
    · have : α y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hF', this]
  have hαi : Integrable α ν := hα.integrable_of_hasCompactSupport hαc
  have hF'i : Integrable (F' x) ν :=
    Integrable.mono' (hαi.norm.mul_const C) hcontF'.aestronglyMeasurable
      (Eventually.of_forall fun y => hbound y x (mem_ball_self rpos))
  have hmain : HasFDerivAt (fun x' => ∫ y, α y * K (x', y) ∂ν) (∫ y, F' x y ∂ν) x := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x r) (bound := fun y => ‖α y‖ * C)
      (ball_mem_nhds x rpos) ?_ ?_ hcontF'.aestronglyMeasurable
      (Eventually.of_forall fun y => hbound y) (hαi.norm.mul_const C) ?_
    · filter_upwards [hU.mem_nhds hx] with x' hx'
      exact (hcontF x' hx').aestronglyMeasurable
    · exact (hcontF x hx).integrable_of_hasCompactSupport (hαc.mul_right)
    · refine Eventually.of_forall fun y x' hx' => ?_
      by_cases hy : y ∈ U
      · exact (hKp x' (hcb (ball_subset_closedBall hx')) y hy).const_mul (α y)
      · have : α y = 0 := hα0 y hy
        simp only [hF', this, zero_mul, zero_smul]
        exact hasFDerivAt_const _ _
  rw [hmain.fderiv, ContinuousLinearMap.integral_apply hF'i]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ U
  · simp only [hF', ContinuousLinearMap.smul_apply, smul_eq_mul, (hKp x hx y hy).fderiv]
  · simp [hF', hα0 y hy]

end GlobalTheory
end

section

open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory

theorem exp_neg_le_norm_tprod_one_sub_inv {ι : Type} (x : ι → ℂ) (B : ℝ)
    (h : ∀ a, ‖x a‖ ≤ 1 / 2) (hs : Summable (fun a => ‖x a‖)) (hB : ∑' a, ‖x a‖ ≤ B) :
    Real.exp (-B) ≤ ‖∏' a, (1 - x a)⁻¹‖ := by
  have hlow : ∀ a, 1 / 2 ≤ ‖1 - x a‖ := by
    intro a
    have h1 := norm_sub_norm_le (1 : ℂ) (x a)
    rw [norm_one] at h1
    linarith [h a]
  have hne : ∀ a, 1 - x a ≠ 0 := by
    intro a h0
    have := hlow a
    rw [h0, norm_zero] at this
    linarith
  have heq : ∀ a, (1 - x a)⁻¹ = 1 + x a * (1 - x a)⁻¹ := by
    intro a
    have := hne a
    field_simp
    ring
  have hsum : Summable (fun a => ‖x a * (1 - x a)⁻¹‖) := by
    refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_) (hs.mul_right 2)
    rw [norm_mul, norm_inv]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [inv_le_comm₀ (by linarith [hlow a]) (by norm_num)]
    linarith [hlow a]
  have hm : Multipliable (fun a => (1 - x a)⁻¹) := by
    have := multipliable_one_add_of_summable hsum
    simpa only [← heq] using this
  have hfac : ∀ a, Real.exp (-‖x a‖) ≤ ‖(1 - x a)⁻¹‖ := by
    intro a
    rw [norm_inv, Real.exp_neg]
    refine inv_anti₀ (by linarith [hlow a]) ?_
    have h1 := norm_sub_le (1 : ℂ) (x a)
    rw [norm_one] at h1
    linarith [Real.add_one_le_exp ‖x a‖]
  have ht := (continuous_norm.tendsto _).comp hm.hasProd
  refine ge_of_tendsto' ht (fun s => ?_)
  have hsle : ∑ a ∈ s, ‖x a‖ ≤ B :=
    (hs.sum_le_tsum s (fun a _ => norm_nonneg _)).trans hB
  calc Real.exp (-B) ≤ Real.exp (∑ a ∈ s, -‖x a‖) := by
        rw [Finset.sum_neg_distrib]
        exact Real.exp_le_exp.2 (neg_le_neg hsle)
    _ = ∏ a ∈ s, Real.exp (-‖x a‖) := Real.exp_sum _ _
    _ ≤ ∏ a ∈ s, ‖(1 - x a)⁻¹‖ :=
        Finset.prod_le_prod₀ (fun a _ => (Real.exp_pos _).le) (fun a _ => hfac a)
    _ = _ := by simp only [Function.comp, norm_prod]

end GlobalTheory
end

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem schwartz_weighted_sobolev_of_finrank_zero :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], finrank ℝ E = 0 → ∀ (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  intro E _ _ _ _ _ μ _ hE k n
  haveI : Subsingleton E := Module.finrank_zero_iff.mp hE
  have hcpt : IsCompact (univ : Set E) := (Set.subsingleton_univ).isCompact
  have hfin : μ univ ≠ ∞ := hcpt.measure_lt_top.ne
  have hne : μ univ ≠ 0 := isOpen_univ.measure_ne_zero μ univ_nonempty
  set m : ℝ := μ.real univ with hm
  have hmpos : 0 < m := ENNReal.toReal_pos hne hfin
  refine ⟨n, Real.sqrt m⁻¹, Real.sqrt_nonneg _, fun f x => ?_⟩
  have hx : x = 0 := Subsingleton.elim _ _
  subst hx
  set a : ℝ := ‖iteratedFDeriv ℝ n f (0 : E)‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have h1 : ‖(0 : E)‖ ^ k * a ≤ a := by
    apply mul_le_of_le_one_left ha0
    rw [norm_zero]
    exact pow_le_one₀ le_rfl zero_le_one
  refine h1.trans ?_
  have hterm : ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2 ∂μ = m * a ^ 2 := by
    have : (fun z : E => (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2) = fun _ => a ^ 2 := by
      funext z
      rw [Subsingleton.elim z 0, pow_zero, one_mul]
    rw [this, integral_const, smul_eq_mul]
  have hnn : ∀ i j : ℕ, 0 ≤ ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ :=
    fun i j => integral_nonneg fun z => sq_nonneg _
  have hle : m * a ^ 2 ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ := by
    rw [← hterm]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ∑ j ∈ Finset.range (n + 1),
        ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ)
      (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)
      (Finset.mem_range.mpr (Nat.succ_pos n)))
    exact Finset.single_le_sum
      (f := fun j => ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ)
      (fun j _ => hnn 0 j) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  rw [← Real.sqrt_mul (inv_nonneg.mpr hmpos.le)]
  apply Real.le_sqrt_of_sq_le
  calc a ^ 2 = m⁻¹ * (m * a ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hmpos.le)

end GlobalTheory
end

section

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_pairing_conj_clm_of_borelSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (k : SchwartzMap V ℂ) :
    ∃ L : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      L u = ∫ x, u x * starRingEnd ℂ (k x) ∂μ := by
  let kc : 𝓢(V, ℂ) := SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) k
  have hkc : ∀ x, kc x = starRingEnd ℂ (k x) := fun x => rfl
  have hg : Function.HasTemperateGrowth (fun x => starRingEnd ℂ (k x)) := by
    have := kc.hasTemperateGrowth
    simpa [funext hkc] using this
  refine ⟨(SchwartzMap.integralCLM ℂ μ).comp
    (SchwartzMap.smulLeftCLM ℂ (fun x => starRingEnd ℂ (k x))), fun u => ?_⟩
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply hg]
  congr 1
  funext x
  simp [smul_eq_mul, mul_comm]

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem linearIndependent_real_map_of_fieldEmb {E : Type} [Field E] {r n : ℕ} (τ : E →+* ℂ)
    (e : Fin n → Matrix (Fin r) (Fin r) E) (he : LinearIndependent E e) :
    LinearIndependent ℝ (fun i => (e i).map τ) := by
  letI : Algebra E ℂ := τ.toAlgebra
  have h1 : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[E] e i) :=
    Module.Flat.linearIndependent_one_tmul he
  let j := (matrixEquivTensor (Fin r) E ℂ).symm
  have hc : ∀ (c : ℂ) (x : TensorProduct E ℂ (Matrix (Fin r) (Fin r) E)),
      j (c • x) = c • j x := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a M =>
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      simp only [j, matrixEquivTensor_apply_symm, mul_smul]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  have h2 : LinearIndependent ℂ (j.toRingEquiv.toAddEquiv.toAddMonoidHom ∘
      fun i => (1 : ℂ) ⊗ₜ[E] e i) :=
    h1.map_of_injective_injective id _ (fun _ h => h)
      (fun m hm => by simpa using hm) (fun c x => hc c x)
  have h3 : (j.toRingEquiv.toAddEquiv.toAddMonoidHom ∘ fun i => (1 : ℂ) ⊗ₜ[E] e i) =
      fun i => (e i).map τ := by
    funext i
    simp only [Function.comp_apply]
    show j ((1 : ℂ) ⊗ₜ[E] e i) = _
    simp only [j, matrixEquivTensor_apply_symm, one_smul]
    rfl
  rw [h3] at h2
  exact h2.restrict_scalars' ℝ

end GlobalTheory
end
