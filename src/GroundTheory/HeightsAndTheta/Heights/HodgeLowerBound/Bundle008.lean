module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle032
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem ParamImageNull.segre_torusSmul {K : Type} [Fintype K] {ι : K → Type} (c : K → ℂ) (v : (Σ k, ι k) → ℂ) :
    segre (torusSmul c v) = (∏ k, c k) • segre v := by
  funext x
  simp [segre, torusSmul, Finset.prod_mul_distrib]

theorem ParamImageNull.differentiableAt_segre_comp {K : Type} [Fintype K] {ι : K → Type} {d : ℕ}
    {f : (Fin d → ℂ) → (Σ k, ι k) → ℂ} {w : Fin d → ℂ} (hf : DifferentiableAt ℂ f w) :
    DifferentiableAt ℂ (fun u => segre (f u)) w := by
  refine differentiableAt_pi.2 fun x => ?_
  simp only [segre]
  have hk : ∀ k, DifferentiableAt ℂ (fun u => f u ⟨k, x k⟩) w := fun k => differentiableAt_pi.1 hf ⟨k, x k⟩
  fun_prop

theorem ParamImageNull.proof : ParamImageNull.Statement := by
  intro K _ ι _ P d m V A γ N _hV hAV hA hγ hN Ψ _
  classical
  set G : Fin m → (Fin d → ℂ) → Fin (d + 1) → ℂ := fun i w => Ψ (segre (γ i w)) with hG
  set F : Fin m → (Fin d → ℂ) → Fin d → ℂ := fun i w l => G i w l.succ / G i w 0 with hF
  have hsub : {y : Fin d → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} ⊆
      ⋃ i, F i '' (A i ∩ {w | G i w 0 ≠ 0}) := by
    rintro y ⟨z, hzP, hzN, hzy⟩
    obtain ⟨i, w, hw, c, hc, rfl⟩ := hN z ⟨hzN, hzP⟩
    rw [ParamImageNull.segre_torusSmul, map_smul] at hzy
    have h0 := congrFun hzy 0
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero] at h0
    have hG0 : G i w 0 ≠ 0 := by
      intro h
      rw [hG] at h
      simp only at h
      rw [h, mul_zero] at h0
      exact zero_ne_one h0
    refine Set.mem_iUnion.2 ⟨i, w, ⟨hw, hG0⟩, ?_⟩
    funext l
    have hl := congrFun hzy l.succ
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hl
    simp only [hF]
    rw [div_eq_iff hG0, ← hl]
    have h0' : (∏ k, c k) * G i w 0 = 1 := h0
    calc G i w l.succ = G i w l.succ * ((∏ k, c k) * G i w 0) := by rw [h0', mul_one]
      _ = (∏ k, c k) * Ψ (segre (γ i w)) l.succ * G i w 0 := by simp only [hG]; ring
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null Set.inter_subset_left (hA i))
  intro w ⟨hwA, hw0⟩
  have hγw : DifferentiableAt ℂ (γ i) w := (hγ i w (hAV i hwA)).differentiableAt
  have hGw : DifferentiableAt ℂ (G i) w :=
    (LinearMap.toContinuousLinearMap Ψ).differentiableAt.comp w (ParamImageNull.differentiableAt_segre_comp hγw)
  have hFw : DifferentiableAt ℂ (F i) w := by
    refine differentiableAt_pi.2 fun l => ?_
    show DifferentiableAt ℂ (fun u => G i u l.succ / G i u 0) w
    simp only [div_eq_mul_inv]
    exact (differentiableAt_pi.1 hGw l.succ).mul ((differentiableAt_pi.1 hGw 0).inv hw0)
  exact (hFw.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem BdPtsNull.proof (h : ParamImageNull.Statement) : BdPtsNull.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D
  classical
  refine h K ι (mCoordIdeal D.y) D.n D.nCharts (fun _ => Metric.ball 0 1)
    (fun a => {t | t ∈ Metric.ball (0 : Fin D.n → ℂ) 1 ∧ ∃ i : Fin D.n, (i : ℕ) < (D.chart a).a ∧ t i = 0})
    (fun a => (D.chart a).γ) D.Bd (fun _ => Metric.isOpen_ball) (fun _ _ ht => ht.1) ?_
    (fun a => (D.chart a).analytic) ?_
  · intro a
    refine measure_mono_null (t := ⋃ i : Fin D.n, {t : Fin D.n → ℂ | t i = 0}) ?_
      (measure_iUnion_null fun i => ?_)
    · rintro t ⟨-, i, -, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    · rw [volume_pi]
      exact Measure.pi_hyperplane _ i 0
  · rintro z ⟨hz, -⟩
    obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover z (D.bd_subset hz)
    have htb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt ht (by norm_num))
    have hγ : (D.chart a).γ t ∈ D.Bd := by
      have h' := D.bd_torus _ hz c⁻¹ (fun k => inv_ne_zero (hc k))
      convert h' using 1
      funext p
      simp [torusSmul, hc p.1]
    exact ⟨a, t, ⟨htb, ((D.chart a).boundary t htb).1 hγ⟩, c, hc, rfl⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem maDensity_logDiv_nonneg_of_sheet {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hsp : IsSemipositiveH P L) {r : ℝ} (hr : 0 < r) {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun (_ : Fin e) y' => Real.log (L.h (γ y')) / r) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  have hh : ContDiffAt ℝ 2 L.h (γ y) :=
    (hsp.1.contDiffAt
      (HilbertSamuel.IntegralAgainstPositive.isOpen_blocksNonzero.mem_nhds hy.1)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (L.h z)) (γ y) := hh.log (L.pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  have h2r : ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y')) / r) y := h2.div_const r
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2r fun ξ => ?_
  have hfun : (fun y' => Real.log (L.h (γ y')) / r) =
      fun y' => (fun _ : Fin e → ℂ => (0 : ℝ)) y' + r⁻¹ * Real.log (L.h (γ y')) := by
    funext y'
    simp [div_eq_inv_mul]
  rw [hfun, ReciprocityTheory.AnForm.levi_add_smul r⁻¹ contDiffAt_const h2 ξ]
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : Fin e → ℂ => (0 : ℝ)) y ξ = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  have hc : 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (L.h z)) ∘ γ) y ξ := by
    rw [ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (L.h z)) ξ hA hlog]
    exact hsp.2 _ hy _ (HilbertSamuel.IntegralAgainstPositive.isConeTangent_of_sheet le_rfl hA hpts ξ)
  rw [h0, zero_add]
  exact mul_nonneg (inv_nonneg.2 hr.le) hc

theorem PtsMonoSemipos.proof : PtsMonoSemipos.Statement := by
  intro K _ ι _ P e L r g₁ g₂ N hP hL hr hN hle h1 h2
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ
  swap
  · rw [dite_eq_right hΨ, dite_eq_right hΨ]
  rw [dite_eq_left hΨ, dite_eq_left hΨ]
  have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
  unfold ptsIntegralAt
  refine integral_mono_ae (h1 _ hΨg) (h2 _ hΨg) ?_
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun y hy => ?_) (hN _ hΨg)
  by_contra hyB
  apply hy
  have hfin := fibreFinite K ι P e hΨ.choose hP hΨg y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun w _ => ?_
  unfold sheetDensity
  by_cases hγ : ∃ γ, IsSheet P hΨ.choose y w γ
  · rw [dite_eq_left hγ, dite_eq_left hγ]
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have hnot : hγ.choose y ∉ N := fun hN' => hyB ⟨hγ.choose y, hmem, hN', hproj⟩
    exact mul_le_mul_of_nonneg_right (hle _ hmem hnot)
      (maDensity_logDiv_nonneg_of_sheet hL hr hγ.choose_spec)
  · rw [dite_eq_right hγ, dite_eq_right hγ]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
