module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact

variable {H Z : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {Γ : Type} [TopologicalSpace Γ] [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]

def LocSupp {W : Type} [Zero W] (O : Set H) (ι : Γ → Z) (Φ : H × Z → W) : Prop :=
  ∀ x₀ ∈ O, ∃ U : Set H, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ O ∧
    ∃ K : Set Γ, IsCompact K ∧ ∀ x ∈ U, ∀ y : Γ, y ∉ K → Φ (x, ι y) = 0

def pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (Φ : H × Z → W) (p : H × Z) : H →L[ℝ] W :=
  (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ H Z)

variable {O : Set H} {OZ : Set Z}

theorem contDiffOn_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) : ContDiffOn ℝ ∞ (pd Φ) (O ×ˢ OZ) := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ Φ) (O ×ˢ OZ) := hΦ.fderiv_of_isOpen (hO.prod hOZ) (by simp)
  exact h1.clm_comp contDiffOn_const

theorem hasFDerivAt_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) {x : H} {z : Z} (hx : x ∈ O)
    (hz : z ∈ OZ) : HasFDerivAt (fun x' => Φ (x', z)) (pd Φ (x, z)) x := by
  have hd : DifferentiableAt ℝ Φ (x, z) :=
    (hΦ.differentiableOn (by simp)).differentiableAt ((hO.prod hOZ).mem_nhds ⟨hx, hz⟩)
  exact hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x z)

theorem pd_eq_zero {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) {U : Set H} (hU : IsOpen U)
    (hUO : U ⊆ O) {z : Z} (hz : z ∈ OZ) (h0 : ∀ x ∈ U, Φ (x, z) = 0) {x : H} (hx : x ∈ U) : pd Φ (x, z) = 0 := by
  have h1 := hasFDerivAt_pd hO hOZ hΦ (hUO hx) hz
  have h2 : HasFDerivAt (fun x' => Φ (x', z)) (0 : H →L[ℝ] W) x :=
    (hasFDerivAt_const (0 : W) x).congr_of_eventuallyEq
      (eventually_of_mem (hU.mem_nhds hx) fun x' hx' => h0 x' hx')
  exact h1.unique h2

theorem locSupp_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W} {ι : Γ → Z}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hι : ∀ y, ι y ∈ OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ))
    (hS : LocSupp O ι Φ) : LocSupp O ι (pd Φ) := by
  intro x₀ hx₀
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := hS x₀ hx₀
  exact ⟨U, hUo, hxU, hUO, K, hK, fun x hx y hy =>
    pd_eq_zero hO hOZ hΦ hUo hUO (hι y) (fun x' hx' => hKz x' hx' y hy) hx⟩

theorem continuous_slice {W : Type} [TopologicalSpace W] {Φ : H × Z → W} {ι : Γ → Z} (hιc : Continuous ι)
    (hι : ∀ y, ι y ∈ OZ) (hΦ : ContinuousOn Φ (O ×ˢ OZ)) {x : H} (hx : x ∈ O) :
    Continuous fun y : Γ => Φ (x, ι y) :=
  hΦ.comp_continuous (continuous_const.prodMk hιc) fun y => ⟨hx, hι y⟩

section Int

variable (μ : Measure Γ) [IsFiniteMeasureOnCompacts μ] {ι : Γ → Z}

theorem integrable_slice {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ) (hΦ : ContinuousOn Φ (O ×ˢ OZ)) {x : H} (hx : x ∈ O)
    {K : Set Γ} (hK : IsCompact K) (hKz : ∀ y : Γ, y ∉ K → Φ (x, ι y) = 0) :
    Integrable (fun y : Γ => Φ (x, ι y)) μ :=
  (continuous_slice hιc hι hΦ hx).integrable_of_hasCompactSupport (HasCompactSupport.intro hK hKz)

theorem integrable_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) {x : H} (hx : x ∈ O) :
    Integrable (fun y : Γ => pd Φ (x, ι y)) μ := by
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := locSupp_pd hO hOZ hι hΦ hS x hx
  exact integrable_slice μ hιc hι (contDiffOn_pd hO hOZ hΦ).continuousOn hx hK fun y hy => hKz x hxU y hy

theorem hasFDerivAt_int {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) {x₀ : H} (hx₀ : x₀ ∈ O) :
    HasFDerivAt (fun x => ∫ y : Γ, Φ (x, ι y) ∂μ) (∫ y : Γ, pd Φ (x₀, ι y) ∂μ) x₀ := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℝ W
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := hS x₀ hx₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo x₀ hxU
  have hcb : closedBall x₀ (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hpdc : ContinuousOn (pd Φ) (O ×ˢ OZ) := (contDiffOn_pd hO hOZ hΦ).continuousOn
  have hcomp : IsCompact (closedBall x₀ (r / 2) ×ˢ K) := (isCompact_closedBall x₀ (r / 2)).prod hK
  have hcont : ContinuousOn (fun q : H × Γ => ‖pd Φ (q.1, ι q.2)‖) (closedBall x₀ (r / 2) ×ˢ K) := by
    refine (hpdc.comp (continuous_fst.prodMk (hιc.comp continuous_snd)).continuousOn ?_).norm
    intro q hq
    exact ⟨hUO (hcb hq.1), hι q.2⟩
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (F' := fun x y => pd Φ (x, ι y)) (s := ball x₀ (r / 2))
    (bound := K.indicator fun _ => C) (ball_mem_nhds x₀ (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hUo.mem_nhds hxU] with x hx
    exact (continuous_slice hιc hι hΦ.continuousOn (hUO hx)).aestronglyMeasurable
  · exact integrable_slice μ hιc hι hΦ.continuousOn hx₀ hK fun y hy => hKz x₀ hxU y hy
  · exact (continuous_slice hιc hι hpdc hx₀).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y x hx => ?_
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
      have := hC (x, y) ⟨ball_subset_closedBall hx, hy⟩
      simpa using this
    · rw [indicator_of_notMem hy, pd_eq_zero hO hOZ hΦ hUo hUO (hι y) (fun x' hx' => hKz x' hx' y hy)
        (hcb (ball_subset_closedBall hx))]
      simp
  · exact (integrable_indicator_iff hKm).2 (integrableOn_const hK.measure_lt_top.ne)
  · exact Filter.Eventually.of_forall fun y x hx =>
      hasFDerivAt_pd hO hOZ hΦ (hUO (hcb (ball_subset_closedBall hx))) (hι y)

theorem contDiffOn_int_nat (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ) :
    ∀ (m : ℕ) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W}, ContDiffOn ℝ ∞ Φ (O ×ˢ OZ) → LocSupp O ι Φ →
    ContDiffOn ℝ m (fun x => ∫ y : Γ, Φ (x, ι y) ∂μ) O := by
  intro m
  induction m with
  | zero =>
    intro W _ _ _ Φ hΦ hS
    refine contDiffOn_zero.2 fun x hx => ?_
    exact (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).continuousAt.continuousWithinAt
  | succ m ih =>
    intro W _ _ _ Φ hΦ hS
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hO]
    refine ⟨fun x hx => (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have h1 := ih (contDiffOn_pd hO hOZ hΦ) (locSupp_pd hO hOZ hι hΦ hS)
    exact h1.congr fun x hx => (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).fderiv

theorem contDiffOn_int {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) :
    ContDiffOn ℝ ∞ (fun x => ∫ y : Γ, Φ (x, ι y) ∂μ) O :=
  contDiffOn_infty.2 fun m => contDiffOn_int_nat μ hO hOZ hιc hι m hΦ hS

end Int

end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
end
end

section

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cwave

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

def pX {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (Φ : ℝ × H → W) : ℝ × H → (H →L[ℝ] W) :=
  fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inr ℝ ℝ H)

def Good {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (O : Set H) (Φ : ℝ × H → W) (T : ℝ) : Prop :=
  ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ O) ∧ ∀ t x, T < |t| → Φ (t, x) = 0

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {O : Set H}

theorem Good.deriv (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) : Good O (pX Φ) T := by
  refine ⟨(h.1.fderiv_of_isOpen (isOpen_univ.prod hO) (by simp)).clm_comp contDiffOn_const, fun t x ht => ?_⟩
  have hO' : IsOpen {q : ℝ × H | T < |q.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : Φ =ᶠ[𝓝 (t, x)] fun _ => 0 :=
    Filter.eventuallyEq_of_mem (hO'.mem_nhds ht) fun q hq => h.2 q.1 q.2 hq
  show (fderiv ℝ Φ (t, x)).comp _ = 0
  rw [hev.fderiv_eq]
  simp

theorem Good.cont_line {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H} (hx : x ∈ O) :
    Continuous fun t => Φ (t, x) :=
  h.1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hx⟩

theorem Good.integrable {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H} (hx : x ∈ O) :
    Integrable (fun t => Φ (t, x)) := by
  refine (h.cont_line hx).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_)
  refine h.2 t x ?_
  by_contra hc
  exact ht (abs_le.1 (not_lt.1 hc))

theorem Good.hasFDerivAt [CompleteSpace W] (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x₀ : H}
    (hx₀ : x₀ ∈ O) : HasFDerivAt (fun x => ∫ t, Φ (t, x)) (∫ t, pX Φ (t, x₀)) x₀ := by
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hO x₀ hx₀
  have hsub : closedBall x₀ (ε / 2) ⊆ O := (closedBall_subset_ball (by linarith)).trans hε
  have hK : IsCompact (Icc (-T) T ×ˢ closedBall x₀ (ε / 2)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKsub : Icc (-T) T ×ˢ closedBall x₀ (ε / 2) ⊆ Set.univ ×ˢ O := fun q hq => ⟨mem_univ _, hsub hq.2⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((h.deriv hO).1.continuousOn.mono hKsub)
  have hdiff : ∀ t, ∀ x ∈ O, HasFDerivAt (fun y => Φ (t, y)) (pX Φ (t, x)) x := fun t x hx =>
    ((h.1.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ t, hx⟩)).differentiableAt (by simp)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right t x)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => Φ (t, x)) (F' := fun x t => pX Φ (t, x)) (s := closedBall x₀ (ε / 2))
    (bound := (Icc (-T) T).indicator fun _ => C) (closedBall_mem_nhds _ (by linarith)) ?_ (h.integrable hx₀)
    ((h.deriv hO).cont_line hx₀).aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards [hO.mem_nhds hx₀] with x hx using (h.cont_line hx).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t x hx => ?_
    by_cases ht : t ∈ Icc (-T) T
    · rw [indicator_of_mem ht]
      exact hC (t, x) ⟨ht, hx⟩
    · rw [indicator_of_notMem ht, (h.deriv hO).2 t x ?_, norm_zero]
      by_contra hc
      exact ht (abs_le.1 (not_lt.1 hc))
  · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  · exact Filter.Eventually.of_forall fun t x hx => hdiff t x (hsub hx)

theorem integral_good_contDiffOn (hO : IsOpen O) (k : ℕ) : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (Φ : ℝ × H → W) (T : ℝ), Good O Φ T → ContDiffOn ℝ k (fun x => ∫ t, Φ (t, x)) O := by
  induction k with
  | zero =>
    intro W _ _ _ Φ T h
    exact contDiffOn_zero.2 fun x hx => (h.hasFDerivAt hO hx).continuousAt.continuousWithinAt
  | succ k ih =>
    intro W _ _ _ Φ T h
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by norm_cast, contDiffOn_succ_iff_fderiv_of_isOpen hO]
    refine ⟨fun x hx => (h.hasFDerivAt hO hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih (pX Φ) T (h.deriv hO)).congr fun x hx => (h.hasFDerivAt hO hx).fderiv

theorem good_smooth [CompleteSpace W] (hO : IsOpen O) (Φ : ℝ × H → W) (T : ℝ) (h : Good O Φ T) :
    ContDiffOn ℝ ∞ (fun x => ∫ t, Φ (t, x)) O :=
  contDiffOn_infty.2 fun k => integral_good_contDiffOn hO k Φ T h

theorem good_fderiv_apply [CompleteSpace W] (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H}
    (hx : x ∈ O) (v : H) : fderiv ℝ (fun x => ∫ t, Φ (t, x)) x v = ∫ t, fderiv ℝ (fun y => Φ (t, y)) x v := by
  rw [(h.hasFDerivAt hO hx).fderiv, ContinuousLinearMap.integral_apply (((h.deriv hO).integrable hx))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hd : DifferentiableAt ℝ Φ (t, x) :=
    (h.1.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ t, hx⟩)).differentiableAt (by simp)
  have e : HasFDerivAt (fun y => Φ (t, y)) (pX Φ (t, x)) x := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  show pX Φ (t, x) v = fderiv ℝ (fun y => Φ (t, y)) x v
  rw [e.fderiv]

end PositivityTheory.RgBcC.LfSt.ChainPf.Cwave
end
end
