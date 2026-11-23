module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeN

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem continuousOn_of_holoOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {W : Set X} {g : X → ℂ} (hg : A.HoloOn W g) : ContinuousOn g W := by
  intro x hx
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ W
      rw [(A.chart j).left_inv hj]; exact hx⟩
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) := (hg j _ hmem).continuousAt
  have h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp h1 ((A.chart j).continuousAt hj)
  have heq : (g ∘ (A.chart j).symm) ∘ A.chart j =ᶠ[nhds x] g := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
    simp [Function.comp, (A.chart j).left_inv hz]
  exact (h2.congr heq).continuousWithinAt

theorem logNormHolo_of_continuousOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {W : Set X} {g : X → ℂ} (hW : IsOpen W) (hg : A.HoloOn W g) (hgc : ContinuousOn g W)
    (hne : ∀ y ∈ W, g y ≠ 0) {y : X} (hy : y ∈ W) : ∃ V : Set X, IsOpen V ∧ y ∈ V ∧
      V ⊆ W ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ z ∈ V, Real.log ‖g z‖ = (G z).re := by
  have hc : g y ≠ 0 := hne y hy
  have hcn : 0 < ‖g y‖ := norm_pos_iff.2 hc

  have hslit : ∀ w ∈ Metric.ball (g y) ‖g y‖, w / g y ∈ Complex.slitPlane := by
    intro w hw
    apply Complex.ball_one_subset_slitPlane
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have : w / g y - 1 = (w - g y) / g y := by field_simp
    rw [this, norm_div, div_lt_one hcn]
    exact hw
  refine ⟨W ∩ g ⁻¹' Metric.ball (g y) ‖g y‖, hgc.isOpen_inter_preimage hW Metric.isOpen_ball,
    ⟨hy, by simpa using hcn⟩, Set.inter_subset_left,
    fun z => Complex.log (g z / g y) + (Real.log ‖g y‖ : ℂ), ?_, ?_⟩
  · intro j v hv
    have ha : AnalyticAt ℂ (g ∘ (A.chart j).symm) v := hg j v ⟨hv.1, hv.2.1⟩
    have hs : (g ∘ (A.chart j).symm) v / g y ∈ Complex.slitPlane := hslit _ hv.2.2
    exact ((ha.div analyticAt_const hc).clog hs).add analyticAt_const
  · intro z hz
    have hz0 : g z ≠ 0 := hne z hz.1
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re]
    rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 hc)]
    ring

theorem LogNormHolo.proof (hCC : ChartCont.Statement) : LogNormHolo.Statement := by
  intro X _ D A W g hW hg hne y hy
  exact logNormHolo_of_continuousOn A hW hg ((hCC D A W hW).2 g hg) hne hy

theorem LogNormHolo.full : LogNormHolo.Statement := by
  intro X _ D A W g hW hg hne y hy
  exact logNormHolo_of_continuousOn A hW hg (continuousOn_of_holoOn A hg) hne hy

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Metric Set Filter Topology
open scoped Interval

noncomputable section

def coordScale {D : ℕ} (i : Fin D) (t : ℝ) : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) :=
  ContinuousLinearMap.id ℂ _ +
    ((t : ℂ) - 1) • (ContinuousLinearMap.proj i : (Fin D → ℂ) →L[ℂ] ℂ).smulRight (Pi.single i (1 : ℂ))

variable {D : ℕ}

theorem coordScale_apply (i : Fin D) (t : ℝ) (v : Fin D → ℂ) (j : Fin D) :
    coordScale i t v j = if j = i then (t : ℂ) * v i else v j := by
  simp only [coordScale]
  simp only [Pi.single_apply, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  split_ifs <;> subst_vars <;> ring

theorem coordScale_of_eq_zero (i : Fin D) (t : ℝ) {v : Fin D → ℂ} (hv : v i = 0) : coordScale i t v = v := by
  funext j; rw [coordScale_apply]; split_ifs with h
  · subst h; simp [hv]
  · rfl

theorem coordScale_one (i : Fin D) (v : Fin D → ℂ) : coordScale i 1 v = v := by
  funext j; rw [coordScale_apply]; split_ifs with h
  · subst h; simp
  · rfl

theorem norm_coordScale_apply_le (i : Fin D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (v : Fin D → ℂ) :
    ‖coordScale i t v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun j => ?_
  rw [coordScale_apply]
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (norm_le_pi_norm v i)
  · exact norm_le_pi_norm v j

theorem norm_coordScale_le (i : Fin D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖coordScale i t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using norm_coordScale_apply_le i ht v

theorem coordScale_mem_ball (i : Fin D) {p z : Fin D → ℂ} {r t : ℝ} (hp : p i = 0) (hz : z ∈ ball p r)
    (ht : t ∈ Icc (0 : ℝ) 1) : coordScale i t z ∈ ball p r := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  calc ‖coordScale i t z - p‖ = ‖coordScale i t (z - p)‖ := by
        rw [map_sub, coordScale_of_eq_zero i t hp]
    _ ≤ ‖z - p‖ := norm_coordScale_apply_le i ht _
    _ < r := hz

theorem hasDerivAt_coordScale (i : Fin D) (z : Fin D → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coordScale i s z) (z i • Pi.single i (1 : ℂ)) t := by
  have h := (((hasDerivAt_id t).ofReal_comp.sub_const (1 : ℂ)).smul_const
    (z i • Pi.single i (1 : ℂ) : Fin D → ℂ)).const_add z
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  funext j
  show coordScale i s z j = _
  rw [coordScale_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, id_eq]
  split_ifs <;> subst_vars <;> ring

theorem continuous_coordScale (i : Fin D) : Continuous (coordScale (D := D) i) :=
  continuous_const.add (((Complex.continuous_ofReal).sub continuous_const).smul continuous_const)

theorem analyticOnNhd_fderiv_apply {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    (v : Fin D → ℂ) : AnalyticOnNhd ℂ (fun w => fderiv ℂ F w v) Ω := fun w hw =>
  (((ContinuousLinearMap.apply ℂ ℂ (E' := Fin D → ℂ) v).analyticAt (fderiv ℂ F w)).comp
    (hF.fderiv w hw)).congr (Eventually.of_forall fun _ => rfl)

theorem eq_mul_integral_partial {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} {i : Fin D}
    (hF : AnalyticOnNhd ℂ F Ω) (h0 : ∀ z ∈ Ω, z i = 0 → F z = 0) {p : Fin D → ℂ} {r : ℝ}
    (hp : p i = 0) (hball : ball p r ⊆ Ω) {z : Fin D → ℂ} (hz : z ∈ ball p r) :
    F z = z i * ∫ t in (0 : ℝ)..1, fderiv ℂ F (coordScale i t z) (Pi.single i 1) := by
  have hFi : AnalyticOnNhd ℂ (fun w => fderiv ℂ F w (Pi.single i 1)) Ω := analyticOnNhd_fderiv_apply hF _
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, coordScale i t z ∈ Ω := fun t ht => hball (coordScale_mem_ball i hp hz ht)
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => F (coordScale i s z))
      (z i * fderiv ℂ F (coordScale i t z) (Pi.single i 1)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 := ((hF _ (hmem t ht)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (hasDerivAt_coordScale i z t)
    refine h1.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hc : ContinuousOn (fun t : ℝ => z i * fderiv ℂ F (coordScale i t z) (Pi.single i 1)) (uIcc 0 1) := by
    refine continuousOn_const.mul (hFi.continuousOn.comp
      ((continuous_coordScale i).clm_apply continuous_const).continuousOn fun t ht => hmem t ?_)
    rwa [uIcc_of_le zero_le_one] at ht
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [intervalIntegral.integral_const_mul, coordScale_one,
    h0 _ (hmem 0 ⟨le_rfl, zero_le_one⟩) (by simp [coordScale_apply])] at h
  rw [h, sub_zero]

theorem differentiableOn_integral_partial {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} {i : Fin D}
    (hF : AnalyticOnNhd ℂ F Ω) {p : Fin D → ℂ} {r : ℝ} (hp : p i = 0) (hball : ball p r ⊆ Ω) (hr : 0 < r) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..1, fderiv ℂ F (coordScale i t z) (Pi.single i 1))
      (ball p (r / 2)) := by
  set Fi : (Fin D → ℂ) → ℂ := fun w => fderiv ℂ F w (Pi.single i 1)
  have hFi : AnalyticOnNhd ℂ Fi Ω := analyticOnNhd_fderiv_apply hF _
  have hK : closedBall p (r / 2) ⊆ Ω := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hB : ball p (r / 2) ⊆ Ω := ball_subset_closedBall.trans hK
  obtain ⟨C, hC⟩ := (isCompact_closedBall p (r / 2)).exists_bound_of_continuousOn
    (hFi.fderiv.continuousOn.mono hK)
  have hI : ∀ {t : ℝ}, t ∈ Ι (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 := fun ht =>
    Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht)
  have hmem : ∀ x ∈ ball p (r / 2), ∀ t ∈ Icc (0 : ℝ) 1, coordScale i t x ∈ ball p (r / 2) :=
    fun x hx t ht => coordScale_mem_ball i hp hx ht
  have hcont : ∀ x ∈ ball p (r / 2), ContinuousOn (fun t : ℝ => Fi (coordScale i t x)) (Icc 0 1) :=
    fun x hx => hFi.continuousOn.comp ((continuous_coordScale i).clm_apply continuous_const).continuousOn
      fun t ht => hB (hmem x hx t ht)
  intro x₀ hx₀
  refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := MeasureTheory.volume)
    (F' := fun x t => (fderiv ℂ Fi (coordScale i t x)).comp (coordScale i t)) (bound := fun _ => C)
    (isOpen_ball.mem_nhds hx₀) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [isOpen_ball.mem_nhds hx₀] with x hx
    exact ((hcont x hx).mono fun t ht => hI ht).aestronglyMeasurable measurableSet_uIoc
  · exact (hcont x₀ hx₀).intervalIntegrable_of_Icc zero_le_one
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    exact ((hFi.fderiv.continuousOn.comp ((continuous_coordScale i).clm_apply continuous_const).continuousOn
      fun t ht => hB (hmem x₀ hx₀ t (hI ht))).clm_comp (continuous_coordScale i).continuousOn)
  · refine Eventually.of_forall fun t ht x hx => ?_
    calc ‖(fderiv ℂ Fi (coordScale i t x)).comp (coordScale i t)‖
        ≤ ‖fderiv ℂ Fi (coordScale i t x)‖ * ‖coordScale i t‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := mul_le_mul (hC _ (ball_subset_closedBall (hmem x hx t (hI ht))))
          (norm_coordScale_le i (hI ht)) (norm_nonneg _)
          ((norm_nonneg _).trans (hC p (mem_closedBall_self (half_pos hr).le)))
      _ = C := mul_one C
  · refine Eventually.of_forall fun t ht x hx => ?_
    exact (hFi _ (hB (hmem x hx t (hI ht)))).differentiableAt.hasFDerivAt.comp x (coordScale i t).hasFDerivAt

theorem HyperplaneDivisible.proof : HyperplaneDivisible.Statement := by
  intro D Ω F i hΩ hF h0
  set Fi : (Fin D → ℂ) → ℂ := fun w => fderiv ℂ F w (Pi.single i 1)
  refine ⟨fun z => if z i = 0 then Fi z else F z / z i, fun p hp => ?_, fun z hz => ?_⟩
  · by_cases hpi : p i = 0
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
      have hH := ReciprocityTheory.AnForm.Osgood.osgood D _ _ isOpen_ball
        (differentiableOn_integral_partial hF hpi hball hr) p (mem_ball_self (half_pos hr))
      refine hH.congr ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (half_pos hr))] with z hz
      have hz' : z ∈ ball p r := ball_subset_ball (half_le_self hr.le) hz
      by_cases hzi : z i = 0
      · simp only [if_pos hzi, coordScale_of_eq_zero i _ hzi, intervalIntegral.integral_const, Fi]
        simp
      · rw [if_neg hzi, eq_mul_integral_partial hF h0 hpi hball hz', mul_div_cancel_left₀ _ hzi]
    · have hproj : AnalyticAt ℂ (fun z : Fin D → ℂ => z i) p :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt p
      refine ((hF p hp).div hproj hpi).congr ?_
      filter_upwards [(isOpen_ne_fun (continuous_apply i) continuous_const).mem_nhds hpi] with z hz
      simp only [if_neg (show z i ≠ 0 from hz)]
      rfl
  · by_cases hzi : z i = 0
    · simp [hzi, h0 z hz hzi]
    · simp only [if_neg hzi]
      rw [mul_div_cancel₀ _ hzi]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem BdCocycle.proof (hDense : RegYoDense.Statement) (hHolo : BdEqHolo.Statement) :
    BdCocycle.Statement := by
  intro X _ D A R g hg hEq j k l
  have hOopen : IsOpen (bdDom R j ∩ bdDom R k ∩ bdDom R l) :=
    ((isOpen_bdDom R j).inter (isOpen_bdDom R k)).inter (isOpen_bdDom R l)
  have hOjl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R l := fun _ hy => ⟨hy.1.1, hy.2⟩
  have hOjk : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R k := fun _ hy => hy.1
  have hOkl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R k ∩ bdDom R l := fun _ hy => ⟨hy.1.2, hy.2⟩
  have hYo : Set.EqOn (g j l) (fun y => g j k y * g k l y)
      ((bdDom R j ∩ bdDom R k ∩ bdDom R l) ∩ R.Yo) := by
    rintro y ⟨hyO, hyY⟩
    have hne : bdEq R l y ≠ 0 := fun h0 => ((hHolo D A R l).2 y hyO.2).1 h0 hyY
    have h1 := hEq j l y (hOjl hyO)
    have h2 := hEq j k y (hOjk hyO)
    have h3 := hEq k l y (hOkl hyO)
    apply mul_right_cancel₀ hne
    show g j l y * bdEq R l y = g j k y * g k l y * bdEq R l y
    rw [← h1, h2, h3, mul_assoc]
  have hall := hYo.of_subset_closure ((hg j l).mono hOjl)
    (((hg j k).mono hOjk).mul ((hg k l).mono hOkl)) Set.inter_subset_left
    ((hDense D A R).open_subset_closure_inter hOopen)
  intro y hy
  exact hall hy

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open Filter Topology

theorem cofactor_vanish {D : ℕ} {Ω : Set (Fin D → ℂ)} (hΩ : IsOpen Ω) {F G : (Fin D → ℂ) → ℂ}
    {i k : Fin D} (hik : k ≠ i) (hG : AnalyticOnNhd ℂ G Ω) (hFG : ∀ z ∈ Ω, F z = z i * G z)
    (hF : ∀ z ∈ Ω, z k = 0 → F z = 0) {z : Fin D → ℂ} (hz : z ∈ Ω) (hzk : z k = 0) : G z = 0 := by
  classical
  by_cases hzi : z i = 0
  swap
  · have h := hFG z hz
    rw [hF z hz hzk] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hzi

  set w : ℂ → (Fin D → ℂ) := fun ε => Function.update z i ε with hw
  have hwc : Continuous w := continuous_const.update i continuous_id
  have hw0 : w 0 = z := by rw [← hzi]; simp [hw]
  have hcont : ContinuousAt (fun ε => G (w ε)) 0 := by
    have h := (hG z hz).continuousAt
    rw [← hw0] at h
    exact h.comp hwc.continuousAt
  have hmem : ∀ᶠ ε in 𝓝 (0 : ℂ), w ε ∈ Ω := by
    exact hwc.continuousAt.preimage_mem_nhds (by rw [hw0]; exact hΩ.mem_nhds hz)

  have hzero : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), G (w ε) = 0 := by
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with ε hε hne
    have hwk : w ε k = 0 := by simp [hw, hik, hzk]
    have hwi : w ε i = ε := by simp [hw]
    have h := hFG _ hε
    rw [hF _ hε hwk, hwi] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hne
  have ht1 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 (G (w 0))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm)
  have h := tendsto_nhds_unique ht1 ht2
  rwa [hw0] at h

theorem CoordDivDivisible.proof (hH : HyperplaneDivisible.Statement) : CoordDivDivisible.Statement := by
  classical
  intro D Ω F S hΩ hFa hF
  induction S using Finset.induction_on generalizing F with
  | empty => exact ⟨F, hFa, fun z _ => by simp⟩
  | insert i S hi ih =>
    obtain ⟨G₁, hG₁a, hG₁⟩ := hH D Ω F i hΩ hFa fun z hz hzi =>
      hF z hz ⟨i, Finset.mem_insert_self i S, hzi⟩
    have hG₁0 : ∀ z ∈ Ω, z ∈ coordDiv S → G₁ z = 0 := by
      rintro z hz ⟨k, hk, hzk⟩
      have hki : k ≠ i := fun h => hi (h ▸ hk)
      exact cofactor_vanish hΩ hki hG₁a hG₁
        (fun y hy hyk => hF y hy ⟨k, Finset.mem_insert_of_mem hk, hyk⟩) hz hzk
    obtain ⟨G, hGa, hG⟩ := ih G₁ hG₁a hG₁0
    refine ⟨G, hGa, fun z hz => ?_⟩
    rw [hG₁ z hz, hG z hz, Finset.prod_insert hi, mul_assoc]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection MIntegrable logNormSec locDens
  locDensCont)

theorem abs_log_mul_exp_le {a : ℝ} (t : ℝ) (ha : 0 ≤ a) :
    |Real.log (a * Real.exp t)| ≤ |Real.log a| + |t| := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_mul h.ne' (Real.exp_pos t).ne', Real.log_exp]; exact abs_add_le _ _

theorem LogNormSecIntegrable.proof : LogNormSecIntegrable.Statement := by
  intro D X _ A L s hL hs _ Φ hΦ j K hK hKc
  refine LocallyIntegrableOn.integrableOn_compact_subset ?_ hK hKc
  intro u0 hu0
  set c := A.chart j with hc
  set p := c.symm u0
  set V := c.target ∩ c.symm ⁻¹' L.U p with hVdef
  have hV : IsOpen V := c.isOpen_inter_preimage_symm (L.isOpen_U p)
  have hu0V : u0 ∈ V := ⟨hu0, L.mem_U p⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0V
  set B := Metric.closedBall u0 (r / 2) with hBdef
  have hBV : B ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  set f : (Fin D → ℂ) → ℂ := s p ∘ c.symm with hfdef
  have hf : AnalyticOnNhd ℂ f V := hs.1 p j
  set φ : (Fin D → ℂ) → ℝ := L.φ p ∘ c.symm with hφdef
  have hφc : ContinuousOn φ V := (hL.1 p j).continuousOn
  have hF : ∀ u ∈ V, logNormSec L s (c.symm u) = Real.log (‖f u‖ * Real.exp (-φ u)) := fun u hu =>
    congrArg Real.log (hs.2 _ p _ ⟨L.mem_U _, hu.2⟩)
  have hDc : ContinuousOn (locDens A Φ j) B :=
    (locDensCont A Φ hΦ j).mono (hBV.trans Set.inter_subset_left)
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hDc
  have hlogf : IntegrableOn (fun u => Real.log ‖f u‖) B :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt' D V f hV hf).integrableOn_compact_subset hBV hBc
  have hφi : IntegrableOn φ B := (hφc.mono hBV).integrableOn_compact hBc
  have hfc : ContinuousOn f B := fun u hu => (hf u (hBV hu)).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun u => Real.log (‖f u‖ * Real.exp (-φ u)) *
      locDens A Φ j u) (volume.restrict B) := by
    have h1 : AEStronglyMeasurable (fun u => ‖f u‖ * Real.exp (-φ u)) (volume.restrict B) :=
      (hfc.norm.mul (Real.continuous_exp.comp_continuousOn (hφc.mono hBV).neg)).aestronglyMeasurable
        hBm
    exact (Real.measurable_log.comp_aemeasurable h1.aemeasurable).aestronglyMeasurable.mul
      (hDc.aestronglyMeasurable hBm)
  have hint : IntegrableOn (fun u => Real.log (‖f u‖ * Real.exp (-φ u)) * locDens A Φ j u) B := by
    refine Integrable.mono' ((hlogf.norm.add hφi.norm).mul_const M) hmeas ?_
    refine ae_restrict_of_forall_mem hBm fun u hu => ?_
    rw [norm_mul]
    have hb := abs_log_mul_exp_le (-φ u) (norm_nonneg (f u))
    rw [abs_neg] at hb
    simp only [Real.norm_eq_abs] at hb ⊢
    exact mul_le_mul hb (hM u hu) (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine hint.congr_fun (fun u hu => ?_) hBm
  simp only
  rw [hF u (hBV hu)]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open Filter Topology
open scoped ContDiff

theorem IndicatorSmooth.proof : IndicatorSmooth.Statement := by
  intro X _ D A U O χ h hU hO hχ hsupp hh j
  set φ := A.chart j
  refine fun v hv => (?_ : ContDiffAt ℝ ∞ _ v).contDiffWithinAt
  by_cases hx : φ.symm v ∈ O
  ·
    have hT : IsOpen (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) := φ.isOpen_inter_preimage_symm (hU.inter hO)
    have hvT : v ∈ φ.target ∩ φ.symm ⁻¹' (U ∩ O) := ⟨hv.1, hv.2, hx⟩
    have hχT : ContDiffOn ℝ ∞ (χ ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) :=
      (hχ j).mono fun z hz => ⟨hz.1, Set.mem_univ _⟩
    have hprod : ContDiffOn ℝ ∞ (fun z => (χ ∘ φ.symm) z * (h ∘ φ.symm) z)
        (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) := hχT.mul (hh j)
    refine (hprod.contDiffAt (hT.mem_nhds hvT)).congr_of_eventuallyEq ?_
    filter_upwards [hT.mem_nhds hvT] with z hz
    simp [Function.comp, Set.indicator_of_mem hz.2.2]
  ·
    have hns : φ.symm v ∉ tsupport χ := fun hm => hx (hsupp hm)
    have hT : IsOpen (φ.target ∩ φ.symm ⁻¹' (tsupport χ)ᶜ) :=
      φ.isOpen_inter_preimage_symm (isClosed_tsupport χ).isOpen_compl
    have hvT : v ∈ φ.target ∩ φ.symm ⁻¹' (tsupport χ)ᶜ := ⟨hv.1, hns⟩
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hT.mem_nhds hvT] with z hz
    have h0 : χ (φ.symm z) = 0 := image_eq_zero_of_notMem_tsupport hz.2
    by_cases hzO : φ.symm z ∈ O
    · simp [Function.comp, Set.indicator_of_mem hzO, h0]
    · simp [Function.comp, Set.indicator_of_notMem hzO]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
