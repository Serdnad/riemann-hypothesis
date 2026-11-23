module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegralIoiFsDensRadial
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle005

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection logNormSec)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem RegSection.proof (hDense : RegYoDense.Statement) (hRC : RegRCont.Statement)
    (hMet : BdMetric.Statement) (hProps : BdSectionProps.Statement)
    (hNorm : BdNormCont.Statement) (hCmp : BdComparison.Statement) : RegSection.Statement := by
  intro X _ _ _ D A R
  obtain ⟨φ, hφ⟩ := hMet D A R
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y : X,
      ‖bdSec R y y‖ * Real.exp (-(bdPot R φ 0).φ y y) ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_univ.image (hNorm D A R φ hφ 0)).bddAbove
    exact ⟨M, fun y => hM ⟨y, Set.mem_univ _, rfl⟩⟩
  have hM1 : (0 : ℝ) < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set c := Real.log (max M 1) with hc
  have hφc : ∀ y : X, (bdPot R φ c).φ y y = (bdPot R φ 0).φ y y + c := fun y => by
    simp [bdPot]
  obtain ⟨hPot, hSec, hOpen⟩ := hProps D A R φ hφ c
  have hle : ∀ y : X, ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y) ≤ 1 := by
    intro y
    rw [hφc, neg_add, Real.exp_add, ← mul_assoc, Real.exp_neg c, hc, Real.exp_log hM1,
      mul_inv_le_iff₀ hM1, one_mul]
    exact (hM y).trans (le_max_left _ _)
  refine ⟨bdPot R φ c, bdSec R, hPot, hSec, hle, hOpen, hDense D A R, hRC D A R, ?_,
    hCmp D A R φ hφ c⟩
  have hne : ∀ y ∈ R.Yo, ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y) ≠ 0 := by
    intro y hy
    rw [← hOpen] at hy
    exact mul_ne_zero (norm_ne_zero_iff.2 hy) (Real.exp_pos _).ne'
  have hlog : ContinuousOn (fun y => logNormSec (bdPot R φ c) (bdSec R) y) R.Yo :=
    (hNorm D A R φ hφ c).continuousOn.log hne
  exact continuousOn_const.sub (continuousOn_const.mul hlog)

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdEqHolo.proof : BdEqHolo.Statement := by
  intro X _ D A R j
  refine ⟨fun m v hv => ?_, fun y hy => ?_⟩
  · have h : AnalyticAt ℂ (R.ψ j ∘ (A.chart m).symm) v := (R.compat j m).1 v ⟨hv.1, hv.2.1⟩
    have hi : ∀ i, AnalyticAt ℂ (fun w => (R.ψ j ∘ (A.chart m).symm) w i) v :=
      (analyticAt_pi_iff (f := fun i w => (R.ψ j ∘ (A.chart m).symm) w i)).1 h
    show AnalyticAt ℂ (fun w => ∏ i ∈ R.S j, (R.ψ j ∘ (A.chart m).symm) w i) v
    exact Finset.analyticAt_fun_prod _ fun i _ => hi i
  · have hmem := R.mem_Yo_iff j (R.ψ j y) hy.2
    rw [(R.ψ j).left_inv hy.1] at hmem
    rw [hmem, not_not]
    simp only [bdEq, Finset.prod_eq_zero_iff, coordDiv, Set.mem_ofPred_eq]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem BdNormCont.proof (hCC : ChartCont.Statement) (hEq : BdEqHolo.Statement) :
    BdNormCont.Statement := by
  intro X _ D A R φ hφ c
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  set j := bdIdx R y₀
  have hU : IsOpen (bdDom R j) := isOpen_bdDom R j
  have hy₀ : y₀ ∈ bdDom R j := mem_bdDom_bdIdx R y₀
  have hEqc : ContinuousOn (bdEq R j) (bdDom R j) := (hCC D A _ hU).2 _ (hEq D A R j).1
  have hφc : ContinuousOn (φ j) (bdDom R j) := (hCC D A _ hU).1 _ (hφ.1 j)
  have hg : ContinuousOn (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) (bdDom R j) :=
    hEqc.norm.mul ((hφc.add continuousOn_const).neg.rexp)
  have hgy : ContinuousAt (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) y₀ :=
    hg.continuousAt (hU.mem_nhds hy₀)
  refine hgy.congr ?_
  filter_upwards [hU.mem_nhds hy₀] with y hy
  have hk : y ∈ bdDom R (bdIdx R y) ∩ bdDom R j := ⟨mem_bdDom_bdIdx R y, hy⟩
  have h3 := hφ.2.2 (bdIdx R y) j y hk
  show ‖bdEq R j y‖ * Real.exp (-(φ j y + c)) = ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y)
  simp only [bdSec, bdPot]
  simp only [neg_add, Real.exp_add, ← mul_assoc, h3]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)

theorem BdSectionProps.proof (hB : BdEqHolo.Statement) : BdSectionProps.Statement := by
  intro X _ D A R φ hφ c
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨⟨fun x j => ?_, fun x x' y hy => ?_⟩, ⟨fun x => (hB D A R _).1, fun x x' y hy => ?_⟩, ?_⟩
  · exact (h1 (bdIdx R x) j).add contDiffOn_const
  · obtain ⟨W, hW, hyW, G, hG, hGe⟩ := h2 (bdIdx R x) (bdIdx R x') y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    have h := hGe z ⟨hz.1.1, hz.1.2, hz.2⟩
    show (φ (bdIdx R x) z + c) - (φ (bdIdx R x') z + c) = (G z).re
    linarith
  · show ‖bdEq R (bdIdx R x) y‖ * Real.exp (-(φ (bdIdx R x) y + c)) =
      ‖bdEq R (bdIdx R x') y‖ * Real.exp (-(φ (bdIdx R x') y + c))
    simp only [neg_add, Real.exp_add, ← mul_assoc]
    rw [h3 _ _ y hy]
  · ext y
    have h := (hB D A R (bdIdx R y)).2 y (mem_bdDom_bdIdx R y)
    show bdEq R (bdIdx R y) y ≠ 0 ↔ y ∈ R.Yo
    rw [Ne, h, not_not]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

theorem bdDom_compact_inner {D : ℕ} {X : Type} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
    (R : RegChartData A) (j : Fin R.n) :
    IsCompact ((R.ψ j).symm '' closure (R.W'' j)) ∧
      (R.ψ j).symm '' closure (R.W'' j) ⊆ bdDom R j ∧
      R.V'' j ⊆ (R.ψ j).symm '' closure (R.W'' j) := by
  have hW : closure (R.W'' j) ⊆ R.W j :=
    (R.closure_W''_subset j).trans (subset_closure.trans (R.closure_W'_subset j))
  have hT : closure (R.W'' j) ⊆ (R.ψ j).target := hW.trans (R.W_subset j)
  have hc : IsCompact (closure (R.W'' j)) :=
    (R.isCompact_closure_middle j).of_isClosed_subset isClosed_closure
      ((R.closure_W''_subset j).trans subset_closure)
  refine ⟨hc.image_of_continuousOn ((R.ψ j).continuousOn_symm.mono hT), ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨(R.ψ j).map_target (hT hz), ?_⟩
    show R.ψ j ((R.ψ j).symm z) ∈ R.W j
    rw [(R.ψ j).right_inv (hT hz)]
    exact hW hz
  · intro y hy
    exact ⟨R.ψ j y, subset_closure hy.2, (R.ψ j).left_inv hy.1⟩

theorem BddOnInner.proof : BddOnInner.Statement := by
  intro X _ D A R j u hu
  obtain ⟨hK, hKD, hVK⟩ := bdDom_compact_inner R j
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hu.mono hKD)
  exact ⟨B, fun y hy => by simpa [Real.norm_eq_abs] using hB y (hVK hy)⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

theorem BdDivides.proof (hdiv : CoordDivDivisible.Statement) : BdDivides.Statement := by
  intro X _ D A R j k
  set Ω : Set (Fin D → ℂ) := (R.ψ j).target ∩ (R.ψ j).symm ⁻¹' (bdDom R j ∩ bdDom R k) with hΩdef
  have hΩ : IsOpen Ω :=
    (R.ψ j).isOpen_inter_preimage_symm ((isOpen_bdDom R j).inter (isOpen_bdDom R k))
  set F : (Fin D → ℂ) → ℂ := fun z => ∏ i ∈ R.S k, R.ψ k ((R.ψ j).symm z) i with hFdef
  have hF : AnalyticOnNhd ℂ F Ω := by
    intro z hz
    have ht : AnalyticAt ℂ (R.ψ k ∘ (R.ψ j).symm) z :=
      ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.compat_trans A (R.compat j) (R.compat k) hz.1 hz.2.2.1
    exact Finset.analyticAt_fun_prod (f := fun i z => R.ψ k ((R.ψ j).symm z) i) _
      fun i _ => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt _ |>.comp ht
  have hvan : ∀ z ∈ Ω, z ∈ coordDiv (R.S j) → F z = 0 := by
    intro z hz hzS
    obtain ⟨hzt, ⟨_, hzW⟩, ⟨hyk, hykW⟩⟩ := hz
    have hjz : R.ψ j ((R.ψ j).symm z) = z := (R.ψ j).right_inv hzt
    rw [Set.mem_preimage, hjz] at hzW
    have hnot : (R.ψ j).symm z ∉ R.Yo := fun h => ((R.mem_Yo_iff j z hzW).1 h) hzS
    have hk : R.ψ k ((R.ψ j).symm z) ∈ coordDiv (R.S k) := by
      by_contra hc
      apply hnot
      have := (R.mem_Yo_iff k _ hykW).2 hc
      rwa [(R.ψ k).left_inv hyk] at this
    obtain ⟨i, hi, h0⟩ := hk
    exact Finset.prod_eq_zero hi h0
  obtain ⟨G, hG, hFG⟩ := hdiv D Ω F (R.S j) hΩ hF hvan
  have hmem : ∀ y ∈ bdDom R j ∩ bdDom R k, R.ψ j y ∈ Ω := fun y hy =>
    ⟨(R.ψ j).map_source hy.1.1, by
      show (R.ψ j).symm (R.ψ j y) ∈ bdDom R j ∩ bdDom R k
      rw [(R.ψ j).left_inv hy.1.1]; exact hy⟩
  refine ⟨fun y => G (R.ψ j y), ?_, ?_, ?_⟩
  · intro m w hw
    have hx : (A.chart m).symm w ∈ bdDom R j ∩ bdDom R k := hw.2
    have hc : AnalyticAt ℂ (R.ψ j ∘ (A.chart m).symm) w := ((R.compat j) m).1 w ⟨hw.1, hx.1.1⟩
    exact (hG _ (hmem _ hx)).comp (f := R.ψ j ∘ (A.chart m).symm) hc
  · exact hG.continuousOn.comp ((R.ψ j).continuousOn.mono fun y hy => hy.1.1) hmem
  · intro y hy
    have h := hFG _ (hmem y hy)
    simp only [hFdef, (R.ψ j).left_inv hy.1.1] at h
    simp only [bdEq]
    rw [h, mul_comm]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)

theorem dense_compl_coordDiv {D : ℕ} (S : Finset (Fin D)) : Dense (coordDiv S)ᶜ := by
  have h : (coordDiv S)ᶜ = ⋂ i ∈ (S : Set (Fin D)), (fun z : Fin D → ℂ => z i) ⁻¹' ({0}ᶜ) := by
    ext z
    simp [coordDiv]
  rw [h]
  refine dense_biInter_of_isOpen (fun i _ => ?_) S.countable_toSet (fun i _ => ?_)
  · exact isOpen_compl_singleton.preimage (continuous_apply i)
  · exact (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval i)

theorem RegYoDense.proof : RegYoDense.Statement := by
  intro X _ D A R
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hxU⟩
  have hxj : x ∈ bdDom R (bdIdx R x) := mem_bdDom_bdIdx R x
  set j := bdIdx R x
  have hO : IsOpen ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))) :=
    (R.ψ j).isOpen_image_source_inter (hU.inter (isOpen_bdDom R j))
  have hne : ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))).Nonempty :=
    ⟨R.ψ j x, x, ⟨hxj.1, hxU, hxj⟩, rfl⟩
  obtain ⟨z, ⟨y, ⟨hys, hyU, hyD⟩, rfl⟩, hz⟩ :=
    (dense_compl_coordDiv (R.S j)).inter_open_nonempty _ hO hne
  have hYo := (R.mem_Yo_iff j (R.ψ j y) hyD.2).2 hz
  rw [(R.ψ j).left_inv hys] at hYo
  exact ⟨y, hyU, hYo⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot logNormSec)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdComparison.proof (hCC : ChartCont.Statement) (hBI : BddOnInner.Statement) :
    BdComparison.Statement := by
  intro X _ D A R φ hφ c
  have hp : ∀ j, ∃ B : ℝ, ∀ y ∈ R.V'' j, |φ j y| ≤ B := fun j =>
    hBI D A R j (φ j) ((hCC D A (bdDom R j) (isOpen_bdDom R j)).1 _ (hφ.1 j))
  choose Bf hBf using R.f_bdd
  choose Bp hBp using hp
  refine ⟨∑ j, (|Bf j| + 2 * |Bp j|) + 2 * |c|, fun y hy => ?_⟩
  have hV := mem_V''_bdIdx R y
  have hdom := V''_subset_bdDom R _ hV
  set j := bdIdx R y with hj
  have hW : R.ψ j y ∈ R.W j := hdom.2
  have hsymm : (R.ψ j).symm (R.ψ j y) = y := (R.ψ j).left_inv hV.1
  have hnd : R.ψ j y ∉ coordDiv (R.S j) := by
    rw [← R.mem_Yo_iff j _ hW, hsymm]; exact hy
  have hz : ∀ i ∈ R.S j, R.ψ j y i ≠ 0 := fun i hi h => hnd ⟨i, hi, h⟩
  have hr := R.r_chart j (R.ψ j y) ⟨hW, hnd⟩
  rw [hsymm] at hr
  have hs : rSec (bdPot R φ c) (bdSec R) y =
      Real.exp 1 - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) + 2 * (φ j y + c) := by
    have hprod : ‖∏ i ∈ R.S j, R.ψ j y i‖ ≠ 0 :=
      norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 hz)
    simp only [rSec, logNormSec, bdPot, bdSec, bdEq, ← hj]
    rw [Real.log_mul hprod (Real.exp_pos _).ne', Real.log_exp, norm_prod,
      Real.log_prod (fun i hi => norm_ne_zero_iff.2 (hz i hi))]
    simp only [Real.log_pow, Nat.cast_ofNat, ← Finset.mul_sum]
    ring
  rw [hr, hs]
  have e : Real.exp 1 + R.f j (R.ψ j y) - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) -
      (Real.exp 1 - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) + 2 * (φ j y + c)) =
      R.f j (R.ψ j y) + (-2) * φ j y + (-2) * c := by ring
  rw [e]
  have h1 : |R.f j (R.ψ j y)| ≤ |Bf j| := (hBf j _ hW).trans (le_abs_self _)
  have h2 : |φ j y| ≤ |Bp j| := (hBp j y hV).trans (le_abs_self _)
  have h3 : |Bf j| + 2 * |Bp j| ≤ ∑ k, (|Bf k| + 2 * |Bp k|) :=
    Finset.single_le_sum (f := fun k => |Bf k| + 2 * |Bp k|)
      (fun k _ => by positivity) (Finset.mem_univ j)
  calc |R.f j (R.ψ j y) + (-2) * φ j y + (-2) * c|
      ≤ |R.f j (R.ψ j y)| + |(-2) * φ j y| + |(-2) * c| := abs_add_three _ _ _
    _ = |R.f j (R.ψ j y)| + 2 * |φ j y| + 2 * |c| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ ∑ k, (|Bf k| + 2 * |Bp k|) + 2 * |c| := by linarith

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M

theorem continuousOn_of_chart_continuousOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {U : Set X} (hU : IsOpen U) {E : Type} [TopologicalSpace E] (h : X → E)
    (hc : ∀ j, ContinuousOn (h ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) :
    ContinuousOn h U := by
  intro x hx
  obtain ⟨m, hm⟩ := A.cover x
  set c := A.chart m
  have hT : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.isOpen_inter_preimage_symm hU
  have hcx : c x ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hm, by simpa [c.left_inv hm] using hx⟩
  have h1 : ContinuousAt (h ∘ c.symm) (c x) := (hc m).continuousAt (hT.mem_nhds hcx)
  have h2 : ContinuousAt ((h ∘ c.symm) ∘ c) x := by
    apply ContinuousAt.comp (f := c)
    · exact h1
    · exact c.continuousAt hm
  have heq : (h ∘ c.symm) ∘ c =ᶠ[nhds x] h := by
    filter_upwards [c.open_source.mem_nhds hm] with y hy
    simp [c.left_inv hy]
  exact (h2.congr heq).continuousWithinAt

theorem ChartCont.proof : ChartCont.Statement := by
  intro X _ D A U hU
  refine ⟨fun f hf => ?_, fun g hg => ?_⟩
  · exact continuousOn_of_chart_continuousOn A hU f fun j => (hf j).continuousOn
  · exact continuousOn_of_chart_continuousOn A hU g fun j => (hg j).continuousOn

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open scoped ContDiff

noncomputable section

theorem BdPartition.proof : BdPartition.Statement := by
  intro X _ _ _ D A R
  set e : Fin R.n → OpenPartialHomeomorph X (Fin D → ℂ) :=
    fun j => (R.ψ j).restrOpen (bdDom R j) (isOpen_bdDom R j) with he
  have hsrc : ∀ j, (e j).source = bdDom R j := by
    intro j
    simp only [he, OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_eq_right.2 Set.inter_subset_left
  have hc : ∀ j, IsCompatChart A (e j) := fun j =>
    ReciprocityTheory.AnForm.M.pa_compat_restr A (R.ψ j) (R.compat j) _ (isOpen_bdDom R j)
  have hcov : ∀ x, ∃ j, x ∈ (e j).source := fun x =>
    ⟨bdIdx R x, by rw [hsrc]; exact mem_bdDom_bdIdx R x⟩
  have htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source) := fun i j =>
    ReciprocityTheory.AnForm.M.pa_holoSmooth _ _ fun v hv =>
      ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.compat_trans A (hc i) (hc j) hv.1 hv.2
  obtain ⟨χ, h0, h1, hs, hsm⟩ := ReciprocityTheory.AnForm.exists_chart_partition e hcov htr
  obtain ⟨B, hAB, -, hB⟩ := ReciprocityTheory.AnForm.M.atlasOfCompat A e hc hcov
  have hBs : ∀ i, B.Smooth (χ i) := by
    intro i j
    obtain ⟨l, hl⟩ := hB j
    rw [hl]
    exact (hsm i l).mono Set.inter_subset_left
  refine ⟨χ, fun i => ReciprocityTheory.AnForm.M.smoothOn_of_compatible hAB.symm' isOpen_univ (hBs i),
    h0, h1, fun i => ?_⟩
  rw [← hsrc]
  exact hs i

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable locDens)

noncomputable section

def shellConst (D : ℕ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 2) ^ (D + 1) / 2 ^ k

def TailLogOfMass.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Yo : Set X) (r : X → ℝ) (th : LocPot X) (u : Fin D → X → ℝ), IsOpen Yo → ContinuousOn r Yo →
    (∀ x ∈ Yo, Real.exp 1 ≤ r x) → IsPotential A th → (∀ i, A.SmoothOn Yo (u i)) →
    (∀ i, FormNonneg A Yo (potForm th (u i))) → ∀ CE : ℝ,
    TailMassBound A Yo r (fun i => potForm th (u i)) CE →
    TailLogBound A Yo r (fun i => potForm th (u i)) (shellConst D * CE)

section Inhabitants

open ReciprocityTheory.AnForm (fsDens fsDens_pos levi)
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic projectiveLine_fubiniStudy_mass_one)
open ReciprocityTheory.AnForm.M.PLC (locDens_congr_phi mInt_congr_phi)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
