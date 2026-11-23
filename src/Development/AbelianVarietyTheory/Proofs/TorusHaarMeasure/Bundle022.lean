module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA

@[expose] public section

section

namespace GlobalTheory.KronMetric

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem inv_rmul {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ) {x b : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : ψ (rmul x b) = ψ x := by
  have := h 1 X.Γ.one_mem x hx b hb
  rwa [FundSetPf.lact_one] at this

theorem inv_lact {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : ψ (lact γ x) = ψ x := by
  have := h γ hγ x hx _ (ExtFPf.oneF_mem X)
  rwa [ExtFPf.rmul_oneF] at this

theorem continuousOn_of_charts {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ)
    (hs : ∀ x0, IsOrth X x0 → ContinuousOn (fun z => ψ (cpt X x0 z)) (OmF X x0)) :
    ContinuousOn ψ X.dom := by
  intro x hx
  obtain ⟨x1, ho, b, hb, hxe⟩ := ortho_holds r X x hx
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x1 ho
  have h0 : (0 : V (nd X)) ∈ OmF X x1 := by
    show cpt X x1 0 ∈ X.dom
    rw [IW.cpt_zero]
    exact IW.orth_mem_dom X x1 ho
  have hΔ : D.Δ x ≠ 0 := by
    have := (D.uniq 0 h0 b hb).1
    rwa [IW.cpt_zero, ← hxe] at this
  have hc : ContinuousOn (fun y => ψ (cpt X x1 (D.zOf y))) (ExtFPf.cell D) :=
    (hs x1 ho).comp D.hz.continuousOn fun y hy => (D.split y hy.1 hy.2).1
  have hc' : ContinuousOn ψ (ExtFPf.cell D) := by
    refine hc.congr fun y hy => ?_
    obtain ⟨h1, h2, h3⟩ := D.split y hy.1 hy.2
    show ψ y = ψ (cpt X x1 (D.zOf y))
    conv_lhs => rw [h3]
    exact inv_rmul h h1 h2
  exact (hc'.continuousAt ((ExtFPf.isOpen_cell D).mem_nhds ⟨hx, hΔ⟩)).continuousWithinAt

theorem exp_neg_phla {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  unfold phla
  rw [neg_mul, neg_neg, show 2 * Real.log (X.nfac la x) = Real.log (X.nfac la x ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

theorem exp_neg_add {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    Real.exp (-(phla X la x + ψ x)) = X.nfac la x ^ 2 * Real.exp (-ψ x) := by
  rw [neg_add, Real.exp_add, exp_neg_phla X la hx]

theorem kronMetric :
    (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ ψ : Frame X.Ψ r → ℝ, IsInvFn X ψ → (∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → ContinuousOn ψ X.dom ∧ IsMetricW X la (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) ∧ WLower X la (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))))) := by
  rintro ⟨hR, hL, -⟩ r X la ψ hinv hs ⟨C, hC⟩
  classical
  have hψc : ContinuousOn ψ X.dom := continuousOn_of_charts hinv fun x0 h => (hs x0 h).continuousOn
  refine ⟨hψc, ⟨?_, ?_, ?_⟩, Real.exp (-C), Real.exp_pos _, ?_⟩
  · have hc : ContinuousOn (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) X.dom := by
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine (((ExtFPf.nfac_contOn X la).pow 2).mul
        (Real.continuous_exp.comp_continuousOn hψc.neg)).congr fun x hx => ?_
      exact exp_neg_add X la ψ hx
    rw [← Set.piecewise_eq_indicator]
    exact hc.measurable_piecewise continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet
  · intro x hx b hb
    have hxb := OntoS.dom_rmul X hx hb
    have hpos : 0 < ‖bchar la b‖ := norm_pos_iff.2 (OntoE.bchar_ne X la hb)
    rw [Set.indicator_of_mem hxb, Set.indicator_of_mem hx, exp_neg_add X la ψ hxb,
      exp_neg_add X la ψ hx, hR r X la x hx b hb, inv_rmul hinv hx hb,
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · intro γ hγ x hx
    have hγx := OntoS.dom_lact X hγ hx
    rw [Set.indicator_of_mem hγx, Set.indicator_of_mem hx, exp_neg_add X la ψ hγx,
      exp_neg_add X la ψ hx, hL r X la γ hγ x hx, inv_lact hinv hγ hx]
  · intro x hx
    rw [Set.indicator_of_mem hx, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    linarith [hC x hx]

end GlobalTheory.KronMetric
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UnfoldComplex

theorem integral_eq_integral_tsum_of_lintegral {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ ν : Measure α) (f : α → ℂ) (g : ι → α → ℂ) (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (H : ∀ φ : ℂ → ℝ≥0∞, Measurable φ → ∫⁻ z, φ (f z) ∂μ = ∫⁻ z, ∑' i, φ (g i z) ∂ν)
    (hi : Integrable f μ) : ∫ z, f z ∂μ = ∫ z, ∑' i, g i z ∂ν := by
  have hmap : μ.map f = Measure.sum fun i => ν.map (g i) := by
    ext s hs
    have hφ : Measurable (s.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hs
    have h1 := H _ hφ
    rw [lintegral_tsum (f := fun i z => s.indicator (1 : ℂ → ℝ≥0∞) (g i z))
      fun i => (hφ.comp (hg i)).aemeasurable] at h1
    rw [Measure.sum_apply _ hs, ← lintegral_indicator_one hs, lintegral_map hφ hf, h1]
    refine tsum_congr fun i => ?_
    rw [← lintegral_indicator_one hs, lintegral_map hφ (hg i)]
  have hfin : ∑' i, ∫⁻ z, ‖g i z‖ₑ ∂ν ≠ ⊤ := by
    have h1 := H (fun w => ‖w‖ₑ) measurable_enorm
    rw [lintegral_tsum fun i => (hg i).enorm.aemeasurable] at h1
    rw [← h1]
    exact hi.2.ne
  have hid : Integrable (fun w : ℂ => w) (μ.map f) :=
    (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).mpr hi
  rw [integral_tsum (fun i => (hg i).aestronglyMeasurable) hfin]
  calc ∫ z, f z ∂μ = ∫ w, w ∂(μ.map f) := (integral_map hf.aemeasurable aestronglyMeasurable_id).symm
    _ = ∑' i, ∫ w, w ∂(ν.map (g i)) := by
        rw [hmap] at hid ⊢
        exact integral_sum_measure hid
    _ = ∑' i, ∫ z, g i z ∂ν :=
        tsum_congr fun i => integral_map (hg i).aemeasurable aestronglyMeasurable_id

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem continuous_lact {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (fun y : Frame Ψ r => lact δ y) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun y : Frame Ψ r =>
    ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ)
  have hM : Continuous fun y : Frame Ψ r => mat y τ := continuous_apply τ
  exact continuous_const.matrix_mul hM

theorem unfold_integral :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ h : Frame X.Ψ r → ℂ, Measurable h → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, h (rmul x b) = h x) → Integrable (fun z => h (cpt X x0 z)) (muF X x0) → ∫ z, h (cpt X x0 z) ∂muF X x0 = ∫ z in FF, ∑' γ : X.Γ, h (lact γ.1 (cpt X x0 z)) ∂muF X x0) := by
  intro H r X x0 ho FF hFF h hm hinv hint
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  refine integral_eq_integral_tsum_of_lintegral (muF X x0) ((muF X x0).restrict FF)
    (fun z => h (cpt X x0 z)) (fun (γ : X.Γ) z => h (lact γ.1 (cpt X x0 z))) (hm.comp hc)
    (fun γ => hm.comp ((continuous_lact γ.1).measurable.comp hc)) ?_ hint
  intro φ hφ
  exact H r X x0 ho FF hFF (fun x => φ (h x)) (hφ.comp hm)
    (fun x hx b hb => by simp only [hinv x hx b hb])

end GlobalTheory.UnfoldComplex
end
