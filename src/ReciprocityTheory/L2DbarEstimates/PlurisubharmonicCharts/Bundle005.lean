module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem aap_continuous_nsq (la : La) (u : ι → Y → ℂ)
    (hcoc : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → u i y = A.g la i j y * u j y)
    (hc : ∀ i, ContinuousOn (u i ∘ (A.chart i).symm) (A.chart i).target) :
    Continuous (A.nsq la u) := by
  have hloc : ∀ i y, y ∈ (A.chart i).source →
      A.nsq la u y = ‖u i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
    intro i y hy
    have hg := A.g_ne la (A.pick y) i y (A.mem_pick y) hy
    have ht := A.ph_trans la (A.pick y) i y (A.mem_pick y) hy
    have hg2 : 0 < ‖A.g la (A.pick y) i y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hg) 2
    have hp : A.ph la (A.pick y) y = A.ph la i y + Real.log (‖A.g la (A.pick y) i y‖ ^ 2) := by
      linarith
    unfold nsq
    rw [hcoc (A.pick y) i y (A.mem_pick y) hy, hp, norm_mul, mul_pow, neg_add, Real.exp_add,
      Real.exp_neg (Real.log _), Real.exp_log hg2]
    field_simp
  rw [continuous_iff_continuousAt]
  intro y0
  have hy0 : y0 ∈ (A.chart (A.pick y0)).source := A.mem_pick y0
  have hs : (A.chart (A.pick y0)).source ∈ 𝓝 y0 := (A.chart (A.pick y0)).open_source.mem_nhds hy0
  have hu : ContinuousOn (u (A.pick y0)) (A.chart (A.pick y0)).source := by
    have h1 := (hc (A.pick y0)).comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    exact h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
  have hph : ContinuousOn (A.ph la (A.pick y0)) (A.chart (A.pick y0)).source := by
    have h1 := (A.smooth_ph la (A.pick y0)).continuousOn.comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    exact h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
  have hf : ContinuousOn (fun y => ‖u (A.pick y0) y‖ ^ 2 * Real.exp (-A.ph la (A.pick y0) y))
      (A.chart (A.pick y0)).source :=
    (hu.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  exact (hf.congr fun y hy => hloc (A.pick y0) y hy).continuousAt hs

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ap_lintegral_chart (A : WeightedAtlas n Y ι La) (i : ι) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y in (A.chart i).source, g y ∂A.mu =
      ∫⁻ v in (A.chart i).target, g ((A.chart i).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) := by
  have htm : MeasurableSet (A.chart i).target := (A.chart i).open_target.measurableSet
  have hsm : MeasurableSet (A.chart i).source := (A.chart i).open_source.measurableSet
  have hsymm : AEMeasurable (A.chart i).symm (volume.restrict (A.chart i).target) :=
    (A.chart i).continuousOn_symm.aemeasurable htm
  have hρm : AEMeasurable (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))
      (volume.restrict (A.chart i).target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)).aemeasurable htm
  have hsymm' : AEMeasurable (A.chart i).symm ((volume.restrict (A.chart i).target).withDensity
      (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmeas : A.mu.restrict (A.chart i).source = Measure.map (A.chart i).symm
      ((volume.restrict (A.chart i).target).withDensity
        (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))) := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.map_apply_of_aemeasurable hsymm' hs,
      withDensity_apply' _ _, Measure.restrict_restrict' htm,
      A.mu_chart i _ (hs.inter hsm) Set.inter_subset_right, Set.inter_comm s (A.chart i).source,
      (A.chart i).image_source_inter_eq', Set.inter_comm (A.chart i).target]
  rw [hmeas, lintegral_map' hg.aemeasurable hsymm']
  refine (lintegral_withDensity_eq_lintegral_mul₀ hρm (hg.comp_aemeasurable hsymm)).trans
    (lintegral_congr fun v => ?_)
  simp only [Pi.mul_apply, Function.comp]
  ring

theorem ap_mu_compact (A : WeightedAtlas n Y ι La) (K : Set Y) (hK : IsCompact K) :
    A.mu K < ⊤ := by
  refine hK.measure_lt_top_of_nhdsWithin fun y _ => ?_
  set e := A.chart (A.pick y) with he
  have hys : y ∈ e.source := A.mem_pick y
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hys)
  have hδ : 0 < ε / 2 := by positivity
  have hcb : Metric.closedBall (e y) (ε / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hSo : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)) :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  have hyS : y ∈ e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2) := ⟨hys, Set.mem_preimage.mpr (Metric.mem_ball_self hδ)⟩
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2),
    mem_nhdsWithin_of_mem_nhds (hSo.mem_nhds hyS), ?_⟩
  rw [A.mu_chart _ _ hSo.measurableSet Set.inter_subset_left]
  have himg : e '' (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)) ⊆ Metric.closedBall (e y) (ε / 2) := by
    rintro _ ⟨x, hx, rfl⟩
    exact Metric.ball_subset_closedBall hx.2
  have hcont : ContinuousOn (fun v => Real.exp (A.ph A.kap (A.pick y) (e.symm v)))
      (Metric.closedBall (e y) (ε / 2)) :=
    (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap (A.pick y)).continuousOn).mono hcb
  obtain ⟨M, hM⟩ := (isCompact_closedBall (e y) (ε / 2)).exists_bound_of_continuousOn hcont
  calc _ ≤ ∫⁻ v in Metric.closedBall (e y) (ε / 2),
          ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) (e.symm v))) := lintegral_mono_set himg
    _ ≤ ∫⁻ v in Metric.closedBall (e y) (ε / 2), ENNReal.ofReal M := by
        apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
        intro v hv
        apply ENNReal.ofReal_le_ofReal
        have h1 := hM v hv
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
        exact h1
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

theorem api_contOn_chart {E : Type*} [TopologicalSpace E] (A : WeightedAtlas n Y ι La)
    (φ : Y → E) {U : Set Y} (hU : IsOpen U)
    (h : ∀ i, ContinuousOn (φ ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) :
    ContinuousOn φ U := by
  intro x hx
  set e := A.chart (A.pick x) with he
  have hxs : x ∈ e.source := A.mem_pick x
  have hex : e x ∈ e.target := e.map_source hxs
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hmem : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨hex, ?_⟩
    show e.symm (e x) ∈ U
    rw [e.left_inv hxs]
    exact hx
  have h1 : ContinuousAt (φ ∘ e.symm) (e x) :=
    (h (A.pick x)).continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((φ ∘ e.symm) ∘ e) x := h1.comp (e.continuousAt hxs)
  have h3 : (φ ∘ e.symm) ∘ e =ᶠ[𝓝 x] φ := by
    filter_upwards [e.eventually_left_inverse hxs] with y hy
    simp [hy]
  exact (h2.congr h3).continuousWithinAt

theorem api_nsq_eq (A : WeightedAtlas n Y ι La) {la : La} {U : Set Y} {F : ι → Y → ℂ}
    (hFs : A.IsSecOn la U F) {i : ι} {x : Y}
    (hxs : x ∈ (A.chart i).source) (hxU : x ∈ U) :
    ‖F i x‖ ^ 2 * Real.exp (-A.ph la i x) = A.nsq la F x := by
  unfold WeightedAtlas.nsq
  have hj : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
  have hsec := hFs.2 i (A.pick x) x hxU hxs hj
  have hph := A.ph_trans la i (A.pick x) x hxs hj
  have hg := A.g_ne la i (A.pick x) x hxs hj
  have hgpos : 0 < ‖A.g la i (A.pick x) x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hg) 2
  rw [hsec, hph, norm_mul, mul_pow,
    show -(A.ph la i x - Real.log (‖A.g la i (A.pick x) x‖ ^ 2)) =
      Real.log (‖A.g la i (A.pick x) x‖ ^ 2) + -A.ph la i x by ring,
    Real.exp_add, Real.exp_log hgpos]
  ring

theorem api_nsq_contOn (A : WeightedAtlas n Y ι La) {la : La} {U : Set Y} (hU : IsOpen U)
    {F : ι → Y → ℂ} (hFs : A.IsSecOn la U F) : ContinuousOn (A.nsq la F) U := by
  apply api_contOn_chart A _ hU
  intro i
  set e := A.chart i with he
  have hF : ContinuousOn (F i ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) := (hFs.1 i).continuousOn
  have hph : ContinuousOn (A.ph la i ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) :=
    (A.smooth_ph la i).continuousOn.mono Set.inter_subset_left
  have hc : ContinuousOn (fun v => ‖F i (e.symm v)‖ ^ 2 * Real.exp (-A.ph la i (e.symm v)))
      (e.target ∩ e.symm ⁻¹' U) :=
    (hF.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  refine hc.congr ?_
  intro v hv
  exact (api_nsq_eq A hFs (e.map_target hv.1) hv.2).symm

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem nsq_eq_chart (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s)
    {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  unfold nsq
  set j := A.pick y
  have hj : y ∈ (A.chart j).source := A.mem_pick y
  have h1 : s i y = A.g la i j y * s j y := hs.2 i j y trivial hy hj
  have h2 : A.ph la j y = A.ph la i y - Real.log (‖A.g la i j y‖ ^ 2) := A.ph_trans la i j y hy hj
  have hg : 0 < ‖A.g la i j y‖ ^ 2 := by
    have := A.g_ne la i j y hy hj
    positivity
  rw [h1, h2, norm_mul, mul_pow, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hg]
  ring

theorem continuousOn_sec (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s)
    (i : ι) : ContinuousOn (s i) (A.chart i).source := by
  have h1 : ContinuousOn (s i ∘ (A.chart i).symm) (A.chart i).target := by
    have := (hs.1 i).continuousOn
    simpa [Set.preimage_univ, Set.inter_univ] using this
  have h2 : ContinuousOn ((s i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)
  refine h2.congr (fun x hx => ?_)
  simp [Function.comp, (A.chart i).left_inv hx]

theorem continuousOn_ph (A : WeightedAtlas n Y ι La) (la : La) (i : ι) :
    ContinuousOn (A.ph la i) (A.chart i).source := by
  have h1 : ContinuousOn (A.ph la i ∘ (A.chart i).symm) (A.chart i).target :=
    (A.smooth_ph la i).continuousOn
  have h2 : ContinuousOn ((A.ph la i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)
  refine h2.congr (fun x hx => ?_)
  simp [Function.comp, (A.chart i).left_inv hx]

theorem continuous_nsq (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s) :
    Continuous (A.nsq la s) := by
  rw [continuous_iff_continuousAt]
  intro y
  set i := A.pick y
  have hU : (A.chart i).source ∈ 𝓝 y := (A.chart i).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousOn (fun x => ‖s i x‖ ^ 2 * Real.exp (-A.ph la i x)) (A.chart i).source :=
    ((A.continuousOn_sec hs i).norm.pow 2).mul ((A.continuousOn_ph la i).neg.rexp)
  refine (hc.continuousAt hU).congr ?_
  filter_upwards [hU] with x hx
  exact (A.nsq_eq_chart hs hx).symm

theorem continuous_sqn (A : WeightedAtlas n Y ι La) {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    (hw : ∀ k, A.IsSec la (w k)) : Continuous (A.sqn la w) := by
  unfold sqn
  exact continuous_finsetSum _ (fun k _ => A.continuous_nsq (hw k))

theorem nsq_nonneg (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) (y : Y) :
    0 ≤ A.nsq la s y := by
  unfold nsq; positivity

theorem sqn_nonneg (A : WeightedAtlas n Y ι La) (la : La) {N : ℕ} (w : Fin N → ι → Y → ℂ) (y : Y) :
    0 ≤ A.sqn la w y := by
  unfold sqn; exact Finset.sum_nonneg (fun k _ => A.nsq_nonneg la (w k) y)

theorem isSec_sum (A : WeightedAtlas n Y ι La) {la : La} {κ : Type*} (F : Finset κ)
    {h : κ → ι → Y → ℂ} (hh : ∀ q ∈ F, A.IsSec la (h q)) :
    A.IsSec la (fun i y => ∑ q ∈ F, h q i y) := by
  refine ⟨fun i => ?_, fun i j y hy hi hj => ?_⟩
  · have : (fun y => ∑ q ∈ F, h q i y) ∘ (A.chart i).symm =
        fun v => ∑ q ∈ F, (h q i ∘ (A.chart i).symm) v := by
      funext v; simp
    rw [this]
    exact DifferentiableOn.fun_sum (fun q hq => (hh q hq).1 i)
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q hq => (hh q hq).2 i j y hy hi hj)

theorem nsq_sum_le (A : WeightedAtlas n Y ι La) (la : La) {κ : Type*} (F : Finset κ)
    (h : κ → ι → Y → ℂ) (y : Y) :
    A.nsq la (fun i y => ∑ q ∈ F, h q i y) y ≤ (F.card : ℝ) * ∑ q ∈ F, A.nsq la (h q) y := by
  unfold nsq
  have h1 : ‖∑ q ∈ F, h q (A.pick y) y‖ ^ 2 ≤ (F.card : ℝ) * ∑ q ∈ F, ‖h q (A.pick y) y‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq
  have he : 0 ≤ Real.exp (-A.ph la (A.pick y) y) := (Real.exp_pos _).le
  calc ‖∑ q ∈ F, h q (A.pick y) y‖ ^ 2 * Real.exp (-A.ph la (A.pick y) y)
      ≤ ((F.card : ℝ) * ∑ q ∈ F, ‖h q (A.pick y) y‖ ^ 2) * Real.exp (-A.ph la (A.pick y) y) :=
        mul_le_mul_of_nonneg_right h1 he
    _ = _ := by rw [mul_assoc, Finset.sum_mul]

theorem mu_singleton (A : WeightedAtlas n Y ι La) (hn : 1 ≤ n) (P : Y) : A.mu {P} = 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [A.mu_chart (A.pick P) {P} (measurableSet_singleton P)
    (Set.singleton_subset_iff.2 (A.mem_pick P)), Set.image_singleton]
  exact setLIntegral_measure_zero _ _ (measure_singleton _)

theorem lintegral_chart_le (A : WeightedAtlas n Y ι La) (i : ι) (y0 : Y) {W : Set (V n)}
    (hW : IsOpen W) (hWt : W ⊆ (A.chart i).target) (c : ℝ≥0∞)
    (hc : ∀ v ∈ W, ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) ≤ c)
    (ψ : V n → ℝ≥0∞) (hψ : Continuous ψ) :
    ∫⁻ x in (A.chart i).source ∩ A.chart i ⁻¹' W, ψ (A.chart i x) ∂A.mu ≤
      c * ∫⁻ v in W, ψ v := by
  classical
  set e := A.chart i
  set U := e.source ∩ e ⁻¹' W with hUdef
  have hUo : IsOpen U := e.isOpen_inter_preimage hW
  have hUm : MeasurableSet U := hUo.measurableSet
  set φ : V n → Y := W.piecewise e.symm (fun _ => y0) with hφdef
  have hφ : Measurable φ :=
    ContinuousOn.measurable_piecewise (e.continuousOn_symm.mono hWt) continuousOn_const
      hW.measurableSet
  have himg : ∀ B : Set Y, e '' (B ∩ U) = φ ⁻¹' B ∩ W := by
    intro B
    ext v
    constructor
    · rintro ⟨x, ⟨hxB, hxs, hxW⟩, rfl⟩
      refine ⟨?_, hxW⟩
      show φ (e x) ∈ B
      rw [show φ (e x) = e.symm (e x) from Set.piecewise_eq_of_mem _ _ _ hxW, e.left_inv hxs]
      exact hxB
    · rintro ⟨hvB, hvW⟩
      rw [Set.mem_preimage, show φ v = e.symm v from Set.piecewise_eq_of_mem _ _ _ hvW] at hvB
      have hvt := hWt hvW
      refine ⟨e.symm v, ⟨hvB, e.map_target hvt, ?_⟩, e.right_inv hvt⟩
      show e (e.symm v) ∈ W
      rwa [e.right_inv hvt]
  set ν : Measure (V n) := c • (volume.restrict W)
  have hle : A.mu.restrict U ≤ Measure.map φ ν := by
    rw [Measure.le_iff]
    intro B hB
    rw [Measure.restrict_apply hB, Measure.map_apply hφ hB,
      A.mu_chart i (B ∩ U) (hB.inter hUm) (Set.inter_subset_right.trans Set.inter_subset_left),
      himg B]
    have hm : MeasurableSet (φ ⁻¹' B ∩ W) := (hφ hB).inter hW.measurableSet
    calc ∫⁻ v in φ ⁻¹' B ∩ W, ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v)))
        ≤ ∫⁻ _ in φ ⁻¹' B ∩ W, c := setLIntegral_mono' hm (fun v hv => hc v hv.2)
      _ = ν (φ ⁻¹' B) := by
        rw [setLIntegral_const, Measure.smul_apply, Measure.restrict_apply (hφ hB), smul_eq_mul,
          mul_comm]
  set Φ : Y → ℝ≥0∞ := U.piecewise (fun x => ψ (e x)) (fun _ => 0) with hΦdef
  have hΦ : Measurable Φ :=
    ContinuousOn.measurable_piecewise (hψ.comp_continuousOn (e.continuousOn.mono
      Set.inter_subset_left)) continuousOn_const hUm
  calc ∫⁻ x in U, ψ (e x) ∂A.mu = ∫⁻ x in U, Φ x ∂A.mu :=
        setLIntegral_congr_fun hUm (fun x hx => by simp [Φ, Set.piecewise_eq_of_mem _ _ _ hx])
    _ ≤ ∫⁻ x, Φ x ∂(Measure.map φ ν) := lintegral_mono' hle le_rfl
    _ = ∫⁻ v, Φ (φ v) ∂ν := lintegral_map hΦ hφ
    _ = c * ∫⁻ v in W, Φ (φ v) := lintegral_smul_measure _ _
    _ = c * ∫⁻ v in W, ψ v := by
        congr 1
        refine setLIntegral_congr_fun hW.measurableSet (fun v hv => ?_)
        have hvt := hWt hv
        have hU : e.symm v ∈ U := ⟨e.map_target hvt, by
          show e (e.symm v) ∈ W
          rwa [e.right_inv hvt]⟩
        simp only [φ, Φ, Set.piecewise_eq_of_mem _ _ _ hv, Set.piecewise_eq_of_mem _ _ _ hU,
          e.right_inv hvt]

end WeightedAtlas

theorem lintegral_ball_rpow_lt_top {n : ℕ} (hMVI : MVIntStatement n) (hn : 1 ≤ n) (vP : V n)
    {r : ℝ} (hr : r ≤ 1) {a : ℝ} (ha : a < n) :
    ∫⁻ v in Metric.ball vP r, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) < ⊤ := by
  have h0 := (hMVI hn a).2 ha
  have h1 : ∫⁻ v in Metric.ball vP r, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) ≤
      ∫⁻ v in Metric.ball vP 1, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) :=
    lintegral_mono_set (Metric.ball_subset_ball hr)
  have h2 : ∫⁻ v in Metric.ball vP 1, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) =
      ∫⁻ y in Metric.ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * a) := by
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,
      ← lintegral_indicator Metric.isOpen_ball.measurableSet,
      ← lintegral_sub_right_eq_self ((Metric.ball (0 : V n) 1).indicator
        (fun y => ENNReal.ofReal ‖y‖ ^ (-2 * a))) vP]
    congr 1
    funext v
    by_cases hv : v ∈ Metric.ball vP 1
    · have hv' : v - vP ∈ Metric.ball (0 : V n) 1 := by
        rw [mem_ball_zero_iff]; rwa [Metric.mem_ball, dist_eq_norm] at hv
      rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv']
    · have hv' : v - vP ∉ Metric.ball (0 : V n) 1 := by
        rw [mem_ball_zero_iff]; rwa [Metric.mem_ball, dist_eq_norm] at hv
      rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv']
  exact lt_of_le_of_lt h1 (h2 ▸ h0)

end

end ReciprocityTheory.L2DbarEstimates.Y
end
