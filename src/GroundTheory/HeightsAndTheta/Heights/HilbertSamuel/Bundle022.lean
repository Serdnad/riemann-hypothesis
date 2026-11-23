module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle012
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PolydiscMean
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Real Module
open scoped Nat

noncomputable section

theorem pi_pow_div_factorial_le_six (k : ℕ) : π ^ k / (k ! : ℝ) ≤ 6 := by
  have hπ := pi_lt_d2
  have hπ0 := pi_pos
  have step : ∀ k, 3 ≤ k → π ^ (k + 1) / ((k + 1) ! : ℝ) ≤ π ^ k / (k ! : ℝ) := by
    intro k hk
    have hk' : (4 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have hf : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_div_iff₀ (by positivity) hf]
    push_cast
    have hp : 0 < π ^ k := pow_pos hπ0 k
    nlinarith [mul_pos hp hf]
  have h3 : π ^ 3 / ((3 : ℕ) ! : ℝ) ≤ 6 := by
    norm_num [Nat.factorial]
    nlinarith [sq_nonneg π, mul_pos hπ0 hπ0]
  rcases lt_or_ge k 3 with hk | hk
  · interval_cases k
    · norm_num
    · norm_num; linarith
    · norm_num [Nat.factorial]; nlinarith
  · induction k, hk using Nat.le_induction with
    | base => exact h3
    | succ n hn ih => exact (step n hn).trans ih

theorem pi_pow_mul_two_pow_div_doubleFactorial_le_six (k : ℕ) :
    π ^ k * 2 ^ (k + 1) / ((2 * k + 1)‼ : ℝ) ≤ 6 := by
  have hπ := pi_lt_d2
  have hπ0 := pi_pos
  have step : ∀ k, 2 ≤ k → π ^ (k + 1) * 2 ^ (k + 1 + 1) / ((2 * (k + 1) + 1)‼ : ℝ) ≤
      π ^ k * 2 ^ (k + 1) / ((2 * k + 1)‼ : ℝ) := by
    intro k hk
    have hk' : (7 : ℝ) ≤ 2 * (k : ℝ) + 3 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [he, Nat.doubleFactorial_add_two, Nat.cast_mul, pow_succ, pow_succ (2 : ℝ) (k + 1)]
    have hf : (0 : ℝ) < ((2 * k + 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
    rw [div_le_div_iff₀ (by positivity) hf]
    push_cast
    have hp : 0 < π ^ k * 2 ^ (k + 1) := by positivity
    nlinarith [mul_pos hp hf]
  have h2 : π ^ 2 * 2 ^ (2 + 1) / ((2 * 2 + 1)‼ : ℝ) ≤ 6 := by
    norm_num [Nat.doubleFactorial]
    nlinarith
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · norm_num [Nat.doubleFactorial]
    · norm_num [Nat.doubleFactorial]; linarith
  · induction k, hk using Nat.le_induction with
    | base => exact h2
    | succ n hn ih => exact (step n hn).trans ih

theorem SmallBallVolume.proof : SmallBallVolume.Statement := by
  intro R
  unfold unitBallVolume
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin R)) = R := finrank_euclideanSpace_fin
  rcases Nat.even_or_odd' R with ⟨k, hk | hk⟩
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp only [mul_zero] at hk
      subst hk
      have : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)).toReal ≤ 1 := by
        have hle : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1) ≤ 1 := by
          calc volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)
              ≤ volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := measure_mono (Set.subset_univ _)
            _ = 1 := by
              rw [← (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage
                MeasurableSet.univ.nullMeasurableSet, Set.preimage_univ, MeasureTheory.volume_pi,
                Measure.pi_univ]
              simp
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)
      linarith
    · have : Nontrivial (EuclideanSpace ℝ (Fin R)) :=
        Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
      rw [InnerProductSpace.volume_ball_of_dim_even (hfin.trans hk), ENNReal.ofReal_one, one_pow,
        one_mul, ENNReal.toReal_ofReal (by positivity)]
      exact pi_pow_div_factorial_le_six k
  · rw [InnerProductSpace.volume_ball_of_dim_odd (hfin.trans hk), ENNReal.ofReal_one, one_pow,
      one_mul, ENNReal.toReal_ofReal (by positivity), hfin, hk]
    exact pi_pow_mul_two_pow_div_doubleFactorial_le_six k

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights
open scoped ContDiff

noncomputable section

namespace ChartTaylorCover

theorem inv_sum_pos {ι : Type*} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    0 < (∑ k ∈ t, 1 / a k + 1)⁻¹ := by
  have : 0 ≤ ∑ k ∈ t, 1 / a k := Finset.sum_nonneg fun k _ => (one_div_pos.2 (ha k)).le
  positivity

theorem inv_sum_le {ι : Type*} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 < a i) {i : ι}
    (hi : i ∈ t) : (∑ k ∈ t, 1 / a k + 1)⁻¹ ≤ a i := by
  have h1 : 1 / a i ≤ ∑ k ∈ t, 1 / a k :=
    Finset.single_le_sum (f := fun k => 1 / a k) (fun k _ => (one_div_pos.2 (ha k)).le) hi
  have h0 : 0 < ∑ k ∈ t, 1 / a k + 1 := by
    have : 0 ≤ ∑ k ∈ t, 1 / a k := Finset.sum_nonneg fun k _ => (one_div_pos.2 (ha k)).le
    linarith
  rw [inv_le_comm₀ h0 (ha i), ← one_div]
  linarith

theorem norm_sq_le_sum {D : ℕ} (z : Fin D → ℂ) : ‖z‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := by positivity
  have h : ‖z‖ ≤ √(∑ i, ‖z i‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    exact (Real.le_sqrt (norm_nonneg _) hS).2
      (Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun k _ => by positivity)
        (Finset.mem_univ i))
  calc ‖z‖ ^ 2 ≤ (√(∑ i, ‖z i‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, ‖z i‖ ^ 2 := Real.sq_sqrt hS

theorem taylor_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) {y z : E} {M : ℝ}
    (hB : closedBall y ‖z‖ ⊆ U) (hM : ∀ w ∈ closedBall y ‖z‖, ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ M) :
    f (y + z) ≤ f y + fderiv ℝ f y z + M * ‖z‖ ^ 2 := by
  set s := closedBall y ‖z‖ with hs
  have hconv : Convex ℝ s := convex_closedBall _ _
  have hys : y ∈ s := mem_closedBall_self (norm_nonneg z)
  have hyzs : y + z ∈ s := by
    rw [hs, mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ f) y)) (hM y hys)
  have hca : ∀ w ∈ U, ContDiffAt ℝ 2 f w := fun w hw => hf.contDiffAt (hU.mem_nhds hw)
  have hd1 : ∀ w ∈ s, DifferentiableAt ℝ f w := fun w hw =>
    (hca w (hB hw)).differentiableAt (by norm_num)
  have hd2 : ∀ w ∈ s, DifferentiableAt ℝ (fderiv ℝ f) w := fun w hw =>
    ((hca w (hB hw)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set ℓ := fderiv ℝ f y with hℓ
  have h1 : ∀ w ∈ s, ‖fderiv ℝ f w - ℓ‖ ≤ M * ‖z‖ := by
    intro w hw
    have := hconv.norm_image_sub_le_of_norm_fderiv_le hd2 hM hys hw
    have hw' : ‖w - y‖ ≤ ‖z‖ := by rwa [hs, mem_closedBall, dist_eq_norm] at hw
    exact this.trans (mul_le_mul_of_nonneg_left hw' hM0)
  have hh : ∀ w ∈ s, HasFDerivWithinAt (fun w => f w - ℓ w) (fderiv ℝ f w - ℓ) s w :=
    fun w hw => ((hd1 w hw).hasFDerivAt.sub ℓ.hasFDerivAt).hasFDerivWithinAt
  have h2 := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hh h1 hys hyzs
  have h3 := (Real.le_norm_self _).trans h2
  rw [map_add (f := _), add_sub_cancel_left] at h3
  have h4 : M * ‖z‖ * ‖z‖ = M * ‖z‖ ^ 2 := by ring
  linarith

theorem weight_contDiffOn {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) (j : Fin A.n) :
    ContDiffOn ℝ 2 (W.φ j ∘ (A.chart j).symm) (A.chart j).target :=
  ((W.smooth j j).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)).mono fun _ hy => ⟨hy, (A.chart j).map_target hy⟩

theorem proof : ChartTaylorCover.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV
  classical
  have hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source := fun p =>
    Classical.choose_spec (A.cover p)

  have hrad : ∀ p : X, ∃ ρ : ℝ, 0 < ρ ∧
      closedBall (A.chart (chartIdx A p) p) (2 * ρ) ⊆ (A.chart (chartIdx A p)).target := by
    intro p
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (A.chart (chartIdx A p)).open_target _
      ((A.chart _).map_source (hsrc p))
    exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hball⟩
  choose ρ hρ hρB using hrad

  have hdens : ∀ p : X, ∃ c : ℝ, 0 < c ∧
      ∀ y ∈ closedBall (A.chart (chartIdx A p) p) (2 * ρ p), c ≤ dV.dens (chartIdx A p) y := by
    intro p
    have hne : (closedBall (A.chart (chartIdx A p) p) (2 * ρ p)).Nonempty :=
      nonempty_closedBall.2 (by linarith [hρ p])
    obtain ⟨y₀, hy₀, hmin⟩ := (isCompact_closedBall _ _).exists_isMinOn hne
      ((dV.smooth _).continuousOn.mono (hρB p))
    exact ⟨dV.dens _ y₀, dV.pos _ _ (hρB p hy₀), fun y hy => isMinOn_iff.1 hmin y hy⟩
  choose c hc hcB using hdens

  have hsec : ∀ (W : Weight L) (p : X), ∃ M : ℝ,
      ∀ w ∈ closedBall (A.chart (chartIdx A p) p) (2 * ρ p),
        ‖fderiv ℝ (fderiv ℝ (W.φ (chartIdx A p) ∘ (A.chart (chartIdx A p)).symm)) w‖ ≤ M := by
    intro W p
    have hop := (A.chart (chartIdx A p)).open_target
    have h1 := (weight_contDiffOn W (chartIdx A p)).fderiv_of_isOpen hop (m := 1) (by norm_num)
    exact (isCompact_closedBall _ _).exists_bound_of_continuousOn
      ((h1.continuousOn_fderiv_of_isOpen hop le_rfl).mono (hρB p))
  choose M hM using hsec

  let V : X → Set X := fun p => (A.chart (chartIdx A p)).source ∩
    (A.chart (chartIdx A p)) ⁻¹' ball (A.chart (chartIdx A p) p) (ρ p)
  have hVo : ∀ p, IsOpen (V p) := fun p =>
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun p _ => mem_iUnion.2 ⟨p, hsrc p, by exact Set.mem_preimage.mpr (mem_ball_self (hρ p))⟩)
  set Mt := ∑ p ∈ t, (|M W₀ p| + |M W₁ p|) with hMt
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun p _ => by positivity
  refine ⟨(∑ p ∈ t, 1 / ρ p + 1)⁻¹, inv_sum_pos t ρ hρ, Mt, (∑ p ∈ t, 1 / c p + 1)⁻¹,
    inv_sum_pos t c hc, ?_⟩
  intro x
  obtain ⟨p, hpt, hxV⟩ : ∃ p ∈ t, x ∈ V p := by simpa using ht (mem_univ x)
  set j := chartIdx A p with hj
  have hxs : x ∈ (A.chart j).source := hxV.1
  have hxb : A.chart j x ∈ ball (A.chart j p) (ρ p) := hxV.2
  have hr := inv_sum_le t ρ hρ hpt
  have hsub : closedBall (A.chart j x) (∑ p ∈ t, 1 / ρ p + 1)⁻¹ ⊆
      closedBall (A.chart j p) (2 * ρ p) := by
    refine closedBall_subset_closedBall' ?_
    have := mem_ball.1 hxb
    linarith
  refine ⟨j, hxs, hsub.trans (hρB p), fun y hy => (inv_sum_le t c hc hpt).trans (hcB p y (hsub hy)),
    ?_⟩

  have key : ∀ W : Weight L, |M W p| ≤ Mt → ∃ ℓ : (Fin D → ℂ) →L[ℝ] ℝ, ∀ z : Fin D → ℂ,
      ‖z‖ ≤ (∑ p ∈ t, 1 / ρ p + 1)⁻¹ →
        W.φ j ((A.chart j).symm (A.chart j x + z)) ≤ W.φ j x + ℓ z + Mt * ∑ i, ‖z i‖ ^ 2 := by
    intro W hWM
    refine ⟨fderiv ℝ (W.φ j ∘ (A.chart j).symm) (A.chart j x), fun z hz => ?_⟩
    have hzB : closedBall (A.chart j x) ‖z‖ ⊆ closedBall (A.chart j p) (2 * ρ p) :=
      (closedBall_subset_closedBall hz).trans hsub
    have hT := taylor_le (A.chart j).open_target (weight_contDiffOn W j) (hzB.trans (hρB p))
      (fun w hw => (hM W p w (hzB hw)).trans (le_abs_self _))
    have hx' : (W.φ j ∘ (A.chart j).symm) (A.chart j x) = W.φ j x := by
      simp only [Function.comp_apply, (A.chart j).left_inv hxs]
    rw [hx'] at hT
    have h1 : |M W p| * ‖z‖ ^ 2 ≤ Mt * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right hWM (by positivity)
    have h2 : Mt * ‖z‖ ^ 2 ≤ Mt * ∑ i, ‖z i‖ ^ 2 := mul_le_mul_of_nonneg_left (norm_sq_le_sum z) hMt0
    simp only [Function.comp_apply] at hT
    linarith
  intro W hW
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
  rcases hW with rfl | rfl
  · refine key _ ?_
    calc |M W p| ≤ |M W p| + |M W₁ p| := le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ Mt := Finset.single_le_sum (f := fun p => |M W p| + |M W₁ p|)
          (fun k _ => by positivity) hpt
  · refine key _ ?_
    calc |M W p| ≤ |M W₀ p| + |M W p| := le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ Mt := Finset.single_le_sum (f := fun p => |M W₀ p| + |M W p|)
          (fun k _ => by positivity) hpt

end ChartTaylorCover

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ContDiff

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

lemma mem_source_chartIdx (A : FinHolAtlas D X) (x : X) : x ∈ (A.chart (chartIdx A x)).source :=
  Classical.choose_spec (A.cover x)

lemma target_inter_symm_source (A : FinHolAtlas D X) (j : Fin A.n) :
    (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source = (A.chart j).target :=
  inter_eq_left.2 fun _ hy => (A.chart j).map_target hy

theorem LocalBergmanBound.proof (hC : ChartBergmanBound.Statement) :
    LocalBergmanBound.Statement := by
  intro D X _ _ _ _ _ A L W dV hW V _ hV x ε hε
  have := dV.isProb
  set k := chartIdx A x with hk
  set e := A.chart k with he
  have hx : x ∈ e.source := mem_source_chartIdx A x
  have hy0 : e x ∈ e.target := e.map_source hx
  have hψ : ContDiffOn ℝ ∞ (W.φ k ∘ e.symm) e.target := by
    have := W.smooth k k
    rwa [target_inter_symm_source] at this
  have hmain := hC D e.target (W.φ k ∘ e.symm) (dV.dens k) (e x) e.open_target hy0
    (hψ.of_le (WithTop.coe_le_coe.2 le_top)) ((dV.smooth k).continuousOn) (dV.pos k _ hy0)
    (fun w => hW k (e x) hy0 w) ε hε
  have hb : bergmanDens W dV x =
      (((1 / Real.pi : ℝ) : ℂ) • hessC (W.φ k ∘ e.symm) (e x)).det.re / dV.dens k (e x) := by
    have hD : (D.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero D)
    exact mul_div_mul_left _ _ hD
  filter_upwards [hmain] with n hn
  rw [← hb] at hn
  set K := (bergmanDens W dV x + ε) * (n : ℝ) ^ D with hK

  have hKpos : 0 < K := by
    by_contra hle
    have h1 := hn (fun _ => 1) analyticOnNhd_const
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 hle), zero_mul, nonpos_iff_eq_zero,
      ENNReal.ofReal_eq_zero] at h1
    have : 0 < ‖(1 : ℂ)‖ ^ 2 * Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x)) := by
      simp [Real.exp_pos]
    linarith
  refine ciSup_le fun s => ?_
  have hs : (s : Fin A.n → X → ℂ) ∈ L.sections n := hV n s.2
  have hcont := continuous_ptNormSq W hs
  have hnn : ∀ z, 0 ≤ ptNormSq W n s z := ptNormSq_nonneg W n s
  have hint : Integrable (ptNormSq W n s) dV.μ := integrable_ptNormSq W dV hs
  have hl2 : 0 ≤ sectionL2NormSq W dV n s := sectionL2NormSq_nonneg W dV n s

  have hF : AnalyticOnNhd ℂ ((s : Fin A.n → X → ℂ) k ∘ e.symm) e.target := by
    have := hs.1 k k
    rwa [target_inter_symm_source] at this
  have h1 := hn _ hF
  have hleft : ‖((s : Fin A.n → X → ℂ) k ∘ e.symm) (e x)‖ ^ 2 *
      Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x)) = ptNormSq W n s x := by
    simp only [Function.comp, e.left_inv hx]
    rfl
  have hright : ∫⁻ y in e.target, ENNReal.ofReal (‖((s : Fin A.n → X → ℂ) k ∘ e.symm) y‖ ^ 2 *
      Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) y) * dV.dens k y) ≤
        ENNReal.ofReal (sectionL2NormSq W dV n s) := by
    have hmeas : Measurable fun z => ENNReal.ofReal (ptNormSq W n s z) :=
      hcont.measurable.ennreal_ofReal
    calc _ = ∫⁻ y in e.target, ENNReal.ofReal (ptNormSq W n s (e.symm y)) *
          ENNReal.ofReal (dV.dens k y) := by
          refine setLIntegral_congr_fun e.open_target.measurableSet fun y hy => ?_
          rw [← ENNReal.ofReal_mul (hnn _), ptNormSq_eq_of_mem W hs k (e.map_target hy)]
          rfl
      _ = ∫⁻ z in e.source, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ :=
          (dV.chart_lintegral k _ hmeas).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (sectionL2NormSq W dV n s) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)).symm
  rw [hleft] at h1
  have h2 : ENNReal.ofReal (ptNormSq W n s x) ≤ ENNReal.ofReal (K * sectionL2NormSq W dV n s) := by
    rw [ENNReal.ofReal_mul hKpos.le]
    exact h1.trans (by gcongr)
  have h3 : ptNormSq W n s x ≤ K * sectionL2NormSq W dV n s :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKpos.le hl2)).1 h2
  rcases hl2.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; exact hKpos.le
  · exact (div_le_iff₀ hpos).2 h3

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric Real

noncomputable section

theorem integral_polydisc_gauss (D n : ℕ) (lam : Fin D → ℝ) (R : ℝ) (hn : 0 < n) (hR : 0 < R) :
    ∫ z in closedBall (0 : Fin D → ℂ) (R / Real.sqrt n),
        Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) =
      ((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hρ : 0 < R / Real.sqrt n := div_pos hR (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hsq : (R / Real.sqrt n) ^ 2 = R ^ 2 / n := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hball : closedBall (0 : Fin D → ℂ) (R / Real.sqrt n) =
      Set.univ.pi fun _ => closedBall (0 : ℂ) (R / Real.sqrt n) := by
    rw [closedBall_pi _ hρ.le]
    rfl
  have hw : ∀ z : Fin D → ℂ, Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) =
      ∏ j, Real.exp (-((n : ℝ) * lam j) * ‖z j‖ ^ 2) := by
    intro z
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hfac : ∀ j, ∫ x in closedBall (0 : ℂ) (R / Real.sqrt n),
      Real.exp (-((n : ℝ) * lam j) * ‖x‖ ^ 2) = gaussDiscMass (lam j) R * (n : ℝ)⁻¹ := by
    intro j
    rw [integral_closedBall_gauss _ _ hρ.le, gaussDiscMass]
    by_cases hl : lam j = 0
    · rw [if_pos (by simp [hl]), if_pos hl, hsq]
      ring
    · have hnl : (n : ℝ) * lam j ≠ 0 := mul_ne_zero hn' hl
      rw [if_neg hnl, if_neg hl, hsq]
      have e : -((n : ℝ) * lam j) * (R ^ 2 / n) = -lam j * R ^ 2 := by
        field_simp
      rw [e]
      field_simp
  simp_rw [hw]
  rw [hball, volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod
    (fun (j : Fin D) (x : ℂ) => Real.exp (-((n : ℝ) * lam j) * ‖x‖ ^ 2))]
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow,
    mul_comm]

theorem PolydiscSubmean.proof : PolydiscSubmean.Statement := by
  intro D n lam R f hn hR _ hf
  set w : (Fin D → ℂ) → ℝ := fun z => Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) with hwdef
  have hwc : Continuous w := by
    rw [hwdef]
    fun_prop
  have hw0 : ∀ z, 0 ≤ w z := fun z => (Real.exp_pos _).le
  have hrot : ∀ (u : Circle) z, w ((u : ℂ) • z) = w z := by
    intro u z
    simp only [hwdef, Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
  have h := sq_norm_mul_setIntegral_le hf hwc hw0 hrot
  simp only [hwdef] at h
  rw [integral_polydisc_gauss D n lam R hn hR, ← mul_assoc] at h
  exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
