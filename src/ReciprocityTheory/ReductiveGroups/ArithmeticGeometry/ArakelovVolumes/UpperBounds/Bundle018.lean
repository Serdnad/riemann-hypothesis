module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle005
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.FD
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace ExG

theorem two_le_inf : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
    | exact WithTop.coe_le_coe.mpr le_top

variable {r : ℕ} (X : Data E r)

private lemma isOpen_omF (x0 : Frame X.Ψ r) : IsOpen (OmF X x0) := by
  first
  | exact ExF.isOpen_OmF X x0

theorem isOpen_Om (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0)) :
    IsOpen {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := by
  have hO := isOpen_omF X x0
  exact hg.continuousOn.isOpen_inter_preimage hO isOpen_ne

theorem g_cd (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℂ ∞ g1 z := by
  exact (contDiffOn_of_differentiableOn (nd X) g1 (OmF X x0) (isOpen_omF X x0) hg).contDiffAt
    ((isOpen_omF X x0).mem_nhds hz)

theorem inv_cd (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) (hne : g1 z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => (‖g1 y‖ ^ 2)⁻¹) z := by
  have h1 : ContDiffAt ℝ ∞ g1 z := (g_cd X x0 g1 hg hz).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun y => ‖g1 y‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt.comp z h1
  exact h2.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))

theorem levi_inv_nonneg (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) (hne : g1 z ≠ 0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun y => (((‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) z ξ).re := by
  have hfun : (fun y => (((‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) = fun y => ((Complex.normSq ((g1 y)⁻¹) : ℝ) : ℂ) := by
    funext y
    rw [Complex.normSq_inv, Complex.normSq_eq_norm_sq]
  have hcd : ContDiffAt ℂ 2 (fun y => (g1 y)⁻¹) z := ((g_cd X x0 g1 hg hz).of_le two_le_inf).inv hne
  rw [hfun, leviV_normSq_comp hcd ξ, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

theorem isCompact_sub (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (g1 : V (nd X) → ℂ)
    (hg : DifferentiableOn ℂ g1 (OmF X x0)) (a : ℝ) :
    IsCompact {z : V (nd X) | (z ∈ OmF X x0 ∧ g1 z ≠ 0) ∧ eF X x0 z + (‖g1 z‖ ^ 2)⁻¹ ≤ a} := by
  have hK := ExF.isCompact_subF X x0 ho a
  have hcont : ContinuousOn (fun z => ‖g1 z‖ ^ 2 * (a - eF X x0 z)) {z | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} :=
    ((hg.continuousOn.norm.pow 2).mul (continuousOn_const.sub (fun z hz =>
      (ExF.eF_contDiffAt X x0 ho hz).continuousAt.continuousWithinAt))).mono (fun z hz => hz.1)
  have hcl := hcont.preimage_isClosed_of_isClosed hK.isClosed (isClosed_Ici (a := (1 : ℝ)))
  have hset : {z : V (nd X) | (z ∈ OmF X x0 ∧ g1 z ≠ 0) ∧ eF X x0 z + (‖g1 z‖ ^ 2)⁻¹ ≤ a} =
      {z | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} ∩ (fun z => ‖g1 z‖ ^ 2 * (a - eF X x0 z)) ⁻¹' Set.Ici 1 := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    constructor
    · rintro ⟨⟨hzO, hz0⟩, hle⟩
      have hpos : 0 < ‖g1 z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz0) 2
      have hinv : 0 ≤ (‖g1 z‖ ^ 2)⁻¹ := inv_nonneg.mpr hpos.le
      refine ⟨⟨hzO, by linarith⟩, ?_⟩
      have hle' : (‖g1 z‖ ^ 2)⁻¹ ≤ a - eF X x0 z := by linarith
      calc (1 : ℝ) = ‖g1 z‖ ^ 2 * (‖g1 z‖ ^ 2)⁻¹ := (mul_inv_cancel₀ hpos.ne').symm
        _ ≤ ‖g1 z‖ ^ 2 * (a - eF X x0 z) := mul_le_mul_of_nonneg_left hle' hpos.le
    · rintro ⟨⟨hzO, _⟩, h1⟩
      have hz0 : g1 z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at h1
        norm_num at h1
      have hpos : 0 < ‖g1 z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz0) 2
      refine ⟨⟨hzO, hz0⟩, ?_⟩
      have hle' : (‖g1 z‖ ^ 2)⁻¹ ≤ a - eF X x0 z := by
        calc (‖g1 z‖ ^ 2)⁻¹ = (‖g1 z‖ ^ 2)⁻¹ * 1 := (mul_one _).symm
          _ ≤ (‖g1 z‖ ^ 2)⁻¹ * (‖g1 z‖ ^ 2 * (a - eF X x0 z)) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)
          _ = a - eF X x0 z := by field_simp
      linarith
  rw [hset]
  exact hK.of_isClosed_subset hcl Set.inter_subset_left

end ExG

private theorem leviV_ofReal_add_of_contDiffAt_two {n : ℕ} {F G : V n → ℝ} {y : V n} (hF : ContDiffAt ℝ 2 F y)
    (hG : ContDiffAt ℝ 2 G y) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((F v + G v : ℝ) : ℂ)) y ξ =
      leviV n (fun v => (F v : ℂ)) y ξ + leviV n (fun v => (G v : ℂ)) y ξ := by
  have h := leviV_ofReal_sum (u := ![F, G]) (x := y) (fun i => by fin_cases i <;> simpa) ξ
  simpa [Fin.sum_univ_two] using h

theorem exhaustG_holds : ExhaustGStatement (E := E) := by
  intro r X x0 ho g1 hg
  have hU : IsOpen {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := ExG.isOpen_Om X x0 g1 hg
  have hLH : IsLocalHomeomorph (Subtype.val : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} → V (nd X)) :=
    hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hf : ∀ z ∈ {z | z ∈ OmF X x0 ∧ g1 z ≠ 0},
      ContDiffAt ℝ ∞ (fun z => eF X x0 z + (‖g1 z‖ ^ 2)⁻¹) z := fun z hz =>
    (ExF.eF_contDiffAt X x0 ho hz.1).add (ExG.inv_cd X x0 g1 hg hz.1 hz.2)
  refine ⟨{ z := Subtype.val
            isLocalHomeomorph := hLH
            e := fun y => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹
            smooth_e := ?_
            levi_e := ?_
            isCompact_le := ?_ }, rfl, rfl⟩
  · intro ch hch
    have hts : ∀ y ∈ ch.target, ((ch.symm y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0}) : V (nd X)) = y := fun y hy => by
      rw [hch (ch.map_target hy)]
      exact ch.right_inv hy
    have hsub : ch.target ⊆ {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := fun y hy => by
      rw [← hts y hy]
      exact (ch.symm y).2
    have hcd : ContDiffOn ℝ ∞ (fun y => ((eF X x0 y + (‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) ch.target :=
      fun y hy => (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hf y (hsub hy))).contDiffWithinAt
    refine hcd.congr (fun y hy => ?_)
    simp only [Function.comp_apply, hts y hy]
  · intro x ξ
    obtain ⟨ch, hx, hch⟩ := hLH x
    have hchart : IsChart (nd X) Subtype.val ch := fun y _ => congrFun hch y
    rw [levi_eq_leviV (nd X) Subtype.val ch hchart _ x hx ξ]
    have htg : ch.target ∈ 𝓝 (x : V (nd X)) := by
      have h0 := ch.open_target.mem_nhds (ch.map_source hx)
      rwa [← congrFun hch x] at h0
    have hgerm : (fun y => (((fun y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹)
        (ch.symm y) : ℝ) : ℂ)) =ᶠ[𝓝 (x : V (nd X))]
        (fun y => ((eF X x0 y + (‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) := by
      filter_upwards [htg] with y hy
      have hy' : ((ch.symm y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0}) : V (nd X)) = y := by
        rw [congrFun hch (ch.symm y)]
        exact ch.right_inv hy
      simp only [hy']
    rw [leviV_congr hgerm ξ]
    have hxO : (x : V (nd X)) ∈ OmF X x0 := x.2.1
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ExG.two_le_inf
    have hE : ContDiffAt ℝ 2 (eF X x0) x := (ExF.eF_contDiffAt X x0 ho hxO).of_le h2
    have hI : ContDiffAt ℝ 2 (fun y => (‖g1 y‖ ^ 2)⁻¹) x :=
      (ExG.inv_cd X x0 g1 hg hxO x.2.2).of_le h2
    have hR : ContDiffAt ℝ 2 (rhF X x0) x := (ExF.rhF_contDiffAt X x0 ho hxO).of_le h2
    have hT : ContDiffAt ℝ 2 (fun z : V (nd X) => Real.log (1 + ‖z‖ ^ 2)) x := ExF.T_cd.contDiffAt.of_le h2
    rw [leviV_ofReal_add_of_contDiffAt_two hE hI ξ]
    have hEsplit : leviV (nd X) (fun v => (eF X x0 v : ℂ)) x ξ =
        leviV (nd X) (fun v => (rhF X x0 v : ℂ)) x ξ +
          leviV (nd X) (fun v => (Real.log (1 + ‖v‖ ^ 2) : ℂ)) x ξ :=
      leviV_ofReal_add_of_contDiffAt_two hR hT ξ
    rw [hEsplit, Complex.add_re, Complex.add_re]
    have h1 := ExF.levi_rhF_nonneg X x0 ho hxO ξ
    have h3 := ExF.leviT_nonneg (x : V (nd X)) ξ
    have h4 := ExG.levi_inv_nonneg X x0 g1 hg hxO x.2.2 ξ
    linarith
  · intro a
    rw [Subtype.isCompact_iff]
    convert ExG.isCompact_sub X x0 ho g1 hg a using 1
    ext z
    constructor
    · rintro ⟨⟨w, hw⟩, hle, rfl⟩
      exact ⟨hw, hle⟩
    · rintro ⟨hw, hle⟩
      exact ⟨⟨z, hw⟩, hle, rfl⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem val_chart_symm_apply {n : ℕ} {U : Set (V n)} (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n Subtype.val e) {w : V n} (hw : w ∈ e.target) : ((e.symm w : U) : V n) = w := by
  have h1 : e.symm w ∈ e.source := e.map_target hw
  rw [he h1]
  exact e.right_inv hw

private theorem comp_chart_symm_eventuallyEq_of_mem_target {n : ℕ} {U : Set (V n)} (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n Subtype.val e) (g : V n → ℂ) {w : V n} (hw : w ∈ e.target) :
    (fun y : U => g y.1) ∘ e.symm =ᶠ[nhds w] g := by
  filter_upwards [e.open_target.mem_nhds hw] with y hy
  simp only [Function.comp_apply]
  rw [val_chart_symm_apply e he hy]

private theorem exists_isChart_subtype_val {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (y : U) : ∃ e : OpenPartialHomeomorph U (V n), IsChart n Subtype.val e ∧ y ∈ e.source := by
  obtain ⟨e, hy, he⟩ := hz y
  exact ⟨e, fun a _ => by rw [he], hy⟩

private theorem db_subtype_val_eq_wdb {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (g : V n → ℂ) (k : Fin n) (y : U) : db n Subtype.val k (fun y : U => g y.1) y = wdb n k g y.1 := by
  have hex := exists_isChart_subtype_val hz y
  unfold db
  rw [dite_eq_left hex]
  have hc := Classical.choose_spec hex
  have hw : y.1 ∈ (Classical.choose hex).target := by
    rw [hc.1 hc.2]
    exact (Classical.choose hex).map_source hc.2
  unfold wdb
  rw [(comp_chart_symm_eventuallyEq_of_mem_target _ hc.1 g hw).fderiv_eq]

private theorem d_subtype_val_eq_wd {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (g : V n → ℂ) (k : Fin n) (y : U) : d n Subtype.val k (fun y : U => g y.1) y = wd n k g y.1 := by
  have hex := exists_isChart_subtype_val hz y
  unfold d
  rw [dite_eq_left hex]
  have hc := Classical.choose_spec hex
  have hw : y.1 ∈ (Classical.choose hex).target := by
    rw [hc.1 hc.2]
    exact (Classical.choose hex).map_source hc.2
  unfold wd
  rw [(comp_chart_symm_eventuallyEq_of_mem_target _ hc.1 g hw).fderiv_eq]

private theorem levi_lemma_6 {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (ph : V n → ℝ) (x : U) (ξ : Fin n → ℂ) :
    Levi n Subtype.val (fun y : U => ph y.1) x ξ = leviV n (fun w => ((ph w : ℝ) : ℂ)) x.1 ξ := by
  unfold Levi leviV
  beta_reduce
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have h1 : db n Subtype.val k (fun y : U => ((ph y.1 : ℝ) : ℂ)) =
      fun y : U => wdb n k (fun w => ((ph w : ℝ) : ℂ)) y.1 :=
    funext fun y => db_subtype_val_eq_wdb hz (fun w => ((ph w : ℝ) : ℂ)) k y
  rw [h1, d_subtype_val_eq_wd hz (wdb n k (fun w => ((ph w : ℝ) : ℂ))) j x]

private theorem leviV_add {n : ℕ} (g1 g2 : V n → ℂ) (y : V n)
    (h1 : ∀ᶠ w in nhds y, ContDiffAt ℝ ∞ g1 w) (h2 : ∀ᶠ w in nhds y, ContDiffAt ℝ ∞ g2 w)
    (ξ : Fin n → ℂ) :
    leviV n (fun w => g1 w + g2 w) y ξ = leviV n g1 y ξ + leviV n g2 y ξ := by
  have hev : ∀ k, wdb n k (fun w => g1 w + g2 w) =ᶠ[nhds y] fun w => wdb n k g1 w + wdb n k g2 w := by
    intro k
    filter_upwards [h1, h2] with w hw1 hw2
    have d1 : DifferentiableAt ℝ g1 w := hw1.differentiableAt (by first | norm_num | simp)
    have d2 : DifferentiableAt ℝ g2 w := hw2.differentiableAt (by first | norm_num | simp)
    unfold wdb
    first
      | rw [fderiv_fun_add d1 d2]
    simp only [ContinuousLinearMap.add_apply]
    ring
  have hdiff : ∀ g : V n → ℂ, ContDiffAt ℝ ∞ g y → ∀ k, DifferentiableAt ℝ (wdb n k g) y := by
    intro g hg k
    have hf : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by
      first
        | exact WithTop.coe_le_coe.mpr le_top
        | (simp; done))
    have hfd : DifferentiableAt ℝ (fderiv ℝ g) y := hf.differentiableAt (by first | exact one_ne_zero | exact le_rfl | simp)
    have ha : DifferentiableAt ℝ (fun w => fderiv ℝ g w (bas n k)) y :=
      hfd.clm_apply (differentiableAt_const _)
    have hb : DifferentiableAt ℝ (fun w => fderiv ℝ g w (Complex.I • bas n k)) y :=
      hfd.clm_apply (differentiableAt_const _)
    unfold wdb
    first
      | exact (ha.fun_add (hb.const_mul Complex.I)).div_const 2
      | exact (ha.add (hb.const_mul Complex.I)).div_const 2
      | fun_prop
  unfold leviV
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : wd n j (wdb n k (fun w => g1 w + g2 w)) y =
      wd n j (wdb n k g1) y + wd n j (wdb n k g2) y := by
    unfold wd
    rw [(hev k).fderiv_eq]
    first
      | rw [fderiv_fun_add (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]
    simp only [ContinuousLinearMap.add_apply]
    ring
  rw [e1]
  ring

theorem exhaustF_holds : ExhaustFStatement (E := E) := by
  intro r X x0 ho
  have hU : IsOpen (OmF X x0) := ExF.isOpen_OmF X x0
  have hz : IsLocalHomeomorph (Subtype.val : OmF X x0 → _) := by
    first
      | exact hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hgE : ∀ w ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ((eF X x0 w : ℝ) : ℂ)) w := fun w hw =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (ExF.eF_contDiffAt X x0 ho hw)
  have hg1 : ∀ w ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w := fun w hw =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (ExF.rhF_contDiffAt X x0 ho hw)
  have hg2 : ∀ {m : ℕ} (w : V m), ContDiffAt ℝ ∞ (fun w : V m => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)) w :=
    fun w => Complex.ofRealCLM.contDiff.contDiffAt.comp w
      ((contDiff_const.add (contDiff_norm_sq ℂ)).log fun w => by positivity).contDiffAt
  refine ⟨{
      z := Subtype.val
      isLocalHomeomorph := hz
      e := (fun y => eF X x0 y.1)
      smooth_e := ?_
      levi_e := ?_
      isCompact_le := ?_ }, rfl, rfl⟩
  · unfold SmoothR Smooth
    intro e he
    refine ContDiffOn.congr (f := fun w => ((eF X x0 w : ℝ) : ℂ))
      (fun w hw => (hgE w ?_).contDiffWithinAt) (fun w hw => ?_)
    · rw [← val_chart_symm_apply e he hw]
      exact (e.symm w).2
    · simp only [Function.comp_apply]
      rw [val_chart_symm_apply e he hw]
  · unfold LeviNonneg
    intro x ξ
    rw [levi_lemma_6 hz (eF X x0) x ξ]
    have hsplit : (fun w => ((eF X x0 w : ℝ) : ℂ)) =
        fun w => ((rhF X x0 w : ℝ) : ℂ) + ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := by
      funext w
      simp [eF]
    have hev1 : ∀ᶠ w in nhds x.1, ContDiffAt ℝ ∞ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w :=
      Filter.eventually_of_mem (hU.mem_nhds x.2) hg1
    have hev2 : ∀ᶠ w in nhds x.1, ContDiffAt ℝ ∞ (fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)) w :=
      Filter.Eventually.of_forall fun w => hg2 w
    rw [hsplit, leviV_add _ _ _ hev1 hev2, Complex.add_re]
    exact add_nonneg (ExF.levi_rhF_nonneg X x0 ho x.2 ξ) (ExF.leviT_nonneg _ ξ)
  · intro a
    have hc := ExF.isCompact_subF X x0 ho a
    rw [Subtype.isCompact_iff]
    convert hc using 1
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hw, ha⟩
      exact ⟨⟨w, hw⟩, ha, rfl⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
