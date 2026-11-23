module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle320
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle321
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle323
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle005
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_scaling_compatible_expansion_at_infinity : ∀ (F : Type) [Field F] [CharZero F], ∃ (σ : RatFunc F →+* RatFunc F) (j : RatFunc F →+* LaurentSeries F) (r₂ rh : LaurentSeries F →+* LaurentSeries F), r₂.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2) ∧ r₂.comp (algebraMap (RatFunc F) (LaurentSeries F)) = (algebraMap (RatFunc F) (LaurentSeries F)).comp σ ∧ rh.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2⁻¹) ∧ rh.comp j = j.comp σ ∧ j.comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C ∧ (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  first | exact @GlobalTheory.Nef.InfScale.scaling_expansion_infinity | exact GlobalTheory.Nef.InfScale.scaling_expansion_infinity | (intros; apply GlobalTheory.Nef.InfScale.scaling_expansion_infinity <;> assumption)
end

section


theorem _root_.GlobalTheory.T.pic_isOfFinOrder_of_finite_int' : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by
  first | exact @GlobalTheory.pic_isOfFinOrder_of_finite_int | exact GlobalTheory.pic_isOfFinOrder_of_finite_int | (intros; apply GlobalTheory.pic_isOfFinOrder_of_finite_int <;> assumption)
end

section

open IsLocalRing TensorProduct Pointwise

theorem _root_.GlobalTheory.T.isInteger_of_maximalIdeal_pow_smul_isInteger' : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S → ∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ maximalIdeal S ^ k, IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c := by
  first | exact @GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger | exact GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger | (intros; apply GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger <;> assumption)
end

section

open IsLocalRing TensorProduct Pointwise

theorem _root_.GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos_domain' : ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsDomain S] (A : Type) [CommRing A] [Algebra S A], ReciprocityTheory.CA.ModDepthGE S A 1 → (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) → ∀ s : S, s ≠ 0 → IsSMulRegular A s := by
  first | exact @GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos_domain | exact GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos_domain | (intros; apply GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos_domain <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' : ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 1 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ f : R, f ≠ 0 → IsSMulRegular A f := by
  first | exact @GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos | exact GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos | (intros; apply GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos <;> assumption)
end

section

open IsLocalRing RingTheory.Sequence

namespace GlobalTheory

theorem modDepthGE_three_of_free_of_isRegularLocalRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
    3 ≤ ringKrullDim R → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] [Nontrivial M], ReciprocityTheory.CA.ModDepthGE R M 3 := by
  intro R _ _ hd M _ _ _ _ _
  obtain ⟨xs, h, hl⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg : IsRegular R xs := isRegular_of_ofList_eq_maximalIdeal h hl.le
  have h3 : 3 ≤ xs.length := by
    rw [← hl] at hd
    exact_mod_cast hd
  have hm : ∀ r ∈ xs.take 3, r ∈ maximalIdeal R := fun r hr =>
    h ▸ Ideal.subset_span (List.mem_of_mem_take hr)
  have hw : IsWeaklyRegular R (xs.take 3) := by
    have := hreg.1
    rw [← List.take_append_drop 3 xs, isWeaklyRegular_append_iff] at this
    exact this.1
  have hwM : IsWeaklyRegular M (xs.take 3) := by
    have := hw.isWeaklyRegular_lTensor (M₂ := M)
    exact ((TensorProduct.rid R M).isWeaklyRegular_congr _).mp this
  refine ⟨xs.take 3, by simp [h3], hm, ?_⟩
  exact (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hwM

end GlobalTheory
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.ordGe_exp_of_logSum_two_radii : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d M : ℕ) (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C), (∀ a, c a 0 = Pi.single a 1) → (∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → (∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → ∀ (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C), (∀ b, OrdGe v ρ (z b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))) → (∀ b, constantCoeff (t b) = 0) → (∀ b, lgSum p c t b = z b) → ∀ b, OrdGe v ρ (t b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) := by
  first | exact @GlobalTheory.ExpWeightTwoRadii.ordGe_of_lgSum_twoRadii | exact GlobalTheory.ExpWeightTwoRadii.ordGe_of_lgSum_twoRadii | (intros; apply GlobalTheory.ExpWeightTwoRadii.ordGe_of_lgSum_twoRadii <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem lintegral_nsq_chart_part : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (i : ι) (W : Set (V n)) (D : ι → Y → ℂ), MeasurableSet W → W ⊆ (A.chart i).target → (∀ y ∈ (A.chart i).source, A.chart i y ∈ W → D (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D i y) → AEMeasurable (D i ∘ (A.chart i).symm) (volume.restrict W) → ∫⁻ y in (A.chart i).source ∩ A.chart i ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu = ∫⁻ v in W, ENNReal.ofReal (‖D i ((A.chart i).symm v)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A la i W D hW hWt hD hae
  classical
  set e := A.chart i with he
  have hS : MeasurableSet e.source := e.open_source.measurableSet
  have hT : MeasurableSet e.target := e.open_target.measurableSet

  set c : Y → V n := e.source.piecewise e (fun _ => 0) with hc
  have hcm : Measurable c :=
    ContinuousOn.measurable_piecewise e.continuousOn continuousOn_const hS
  set P : V n → ℝ := e.target.piecewise (fun v => A.ph (A.kap + la) i (e.symm v)) (fun _ => 0) with hP
  have hPm : Measurable P :=
    ContinuousOn.measurable_piecewise (A.smooth_ph (A.kap + la) i).continuousOn continuousOn_const hT
  set D' : V n → ℂ := hae.mk _ with hD'
  have hD'm : Measurable D' := hae.measurable_mk
  have hDD' : (D i ∘ e.symm) =ᵐ[volume.restrict W] D' := hae.ae_eq_mk
  have hcs : ∀ y ∈ e.source, c y = e y := fun y hy => by simp [hc, hy]
  have hPt : ∀ v ∈ e.target, P v = A.ph (A.kap + la) i (e.symm v) := fun v hv => by simp [hP, hv]
  set S : Set Y := e.source ∩ c ⁻¹' W with hSdef
  have hSm : MeasurableSet S := hS.inter (hcm hW)
  have hSeq : e.source ∩ e ⁻¹' W = S := by
    ext y; constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [hcs y h1] using h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [hcs y h1] using h2⟩
  set G : Y → ℝ≥0∞ := S.indicator (fun y => ENNReal.ofReal (‖D' (c y)‖ ^ 2 * Real.exp (-P (c y))))
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hSm
    exact ENNReal.measurable_ofReal.comp
      (((hD'm.comp hcm).norm.pow_const 2).mul ((hPm.comp hcm).neg.exp))

  set T : Set (V n) := toMeasurable (volume.restrict W) {v | ¬ (D i ∘ e.symm) v = D' v}
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT0 : volume.restrict W T = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp hDD'
  set E : Set Y := e.source ∩ c ⁻¹' (T ∩ W)
  have hEm : MeasurableSet E := hS.inter (hcm (hTm.inter hW))
  have hE0 : A.mu E = 0 := by
    rw [A.mu_chart i E hEm Set.inter_subset_left]
    apply setLIntegral_measure_zero
    refine measure_mono_null ?_ (show volume (T ∩ W) = 0 by
      rwa [Measure.restrict_apply hTm] at hT0)
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    simpa [hcs y hy1] using hy2

  have hL : ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu =
      ∫⁻ y in e.source, G y ∂A.mu := by
    rw [hSeq]
    have h1 : ∫⁻ y in S, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu =
        ∫⁻ y in e.source, S.indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) D y)) y ∂A.mu := by
      rw [lintegral_indicator hSm, Measure.restrict_restrict hSm,
        Set.inter_eq_left.mpr Set.inter_subset_left]
    rw [h1]
    apply lintegral_congr_ae
    have hnE : ∀ᵐ y ∂A.mu, y ∉ E := measure_eq_zero_iff_ae_notMem.mp hE0
    filter_upwards [ae_restrict_of_ae hnE, ae_restrict_mem hS] with y hyE hys
    by_cases hyS : y ∈ S
    · simp only [G, Set.indicator_of_mem hyS]
      congr 1
      have hyW : e y ∈ W := by simpa [hcs y hys] using hyS.2
      have hyT : e y ∉ T := fun h => hyE ⟨hys, by simp [hcs y hys, h, hyW]⟩
      have hDy : D i y = D' (c y) := by
        rw [hcs y hys]
        have : (D i ∘ e.symm) (e y) = D' (e y) := by
          by_contra hne
          exact hyT (subset_toMeasurable _ _ hne)
        simpa [e.left_inv hys] using this
      have hPy : P (c y) = A.ph (A.kap + la) i y := by
        rw [hcs y hys, hPt _ (e.map_source hys), e.left_inv hys]
      rw [← hDy, hPy]

      unfold WeightedAtlas.nsq
      have hp := A.mem_pick y
      have hg := A.g_ne (A.kap + la) (A.pick y) i y hp hys
      have hg2 : 0 < ‖A.g (A.kap + la) (A.pick y) i y‖ ^ 2 := by positivity
      have ht := A.ph_trans (A.kap + la) (A.pick y) i y hp hys
      rw [hD y hys hyW, norm_mul, mul_pow]
      have : A.ph (A.kap + la) (A.pick y) y =
          A.ph (A.kap + la) i y + Real.log (‖A.g (A.kap + la) (A.pick y) i y‖ ^ 2) := by linarith
      rw [this, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hg2]
      field_simp
    · simp [G, Set.indicator_of_notMem hyS]

  rw [hL, ap_lintegral_chart A i G hGm]
  have h2 : ∫⁻ v in e.target, G (e.symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v))) =
      ∫⁻ v in e.target, W.indicator (fun v => ENNReal.ofReal (‖D' v‖ ^ 2 * Real.exp (-P v)) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v)))) v := by
    refine setLIntegral_congr_fun hT fun v hv => ?_
    have hs := e.map_target hv
    have hcv : c (e.symm v) = v := by rw [hcs _ hs, e.right_inv hv]
    by_cases hvW : v ∈ W
    · have : e.symm v ∈ S := ⟨hs, by simpa [hcv] using hvW⟩
      simp only [G, Set.indicator_of_mem this, Set.indicator_of_mem hvW, hcv]
    · have : e.symm v ∉ S := fun h => hvW (by simpa [hcv] using h.2)
      simp [G, Set.indicator_of_notMem this, Set.indicator_of_notMem hvW]
  rw [h2, lintegral_indicator hW, Measure.restrict_restrict hW, Set.inter_eq_left.mpr hWt]
  apply lintegral_congr_ae
  filter_upwards [hDD', ae_restrict_mem hW] with v hv hvW
  have hvt := hWt hvW
  have hs := e.map_target hvt
  simp only [Function.comp_apply] at hv
  rw [← hv, hPt v hvt, A.ph_add A.kap la i _ hs, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [neg_add, Real.exp_add]
  have := Real.exp_pos (A.ph A.kap i (e.symm v))
  rw [Real.exp_neg (A.ph A.kap i _)]
  field_simp

end GlobalTheory.OTY
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.TaylorLevi

theorem taylor_two {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : E → ℝ) (p : E)
    (hφ : ContDiffAt ℝ 2 φ p) :
    (fun v => φ v - φ p - fderiv ℝ φ p (v - p) - fderiv ℝ (fderiv ℝ φ) p (v - p) (v - p) / 2)
      =o[𝓝 p] (fun v => ‖v - p‖ ^ 2) := by
  set D := fderiv ℝ φ p
  set B := fderiv ℝ (fderiv ℝ φ) p
  have hB : HasFDerivAt (fderiv ℝ φ) B p :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hsymm : ∀ u w, B u w = B w u := fun u w =>
    (hφ.isSymmSndFDerivAt (by simp)) u w
  have hdiff := eventually_differentiableAt_of_contDiffAt hφ
  have hlo := hB.isLittleO
  set g : E → ℝ := fun w => φ w - D (w - p) - 1 / 2 * B (w - p) (w - p)
  have hg : ∀ w, DifferentiableAt ℝ φ w → HasFDerivAt g (fderiv ℝ φ w - D - B (w - p)) w := by
    intro w hw
    have h1 : HasFDerivAt (fun x : E => x - p) (ContinuousLinearMap.id ℝ E) w :=
      (hasFDerivAt_id w).sub_const p
    have h2 : HasFDerivAt (fun y => B (y - p) (y - p)) _ w := B.hasFDerivAt_of_bilinear h1 h1
    have h3 := (hw.hasFDerivAt.sub (D.hasFDerivAt.comp w h1)).sub (HasFDerivAt.const_mul h2 (1 / 2 : ℝ))
    refine h3.congr_fderiv ?_
    ext u
    simp
    rw [hsymm u w, hsymm u p]
    ring
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have h4 := (Asymptotics.isLittleO_iff.1 hlo) hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h4.and hdiff)
  filter_upwards [Metric.ball_mem_nhds p hδ] with v hv
  have hsub : closedBall p ‖v - p‖ ⊆ ball p δ := by
    apply closedBall_subset_ball
    rw [← dist_eq_norm]; exact mem_ball.1 hv
  have hmvt := (convex_closedBall p ‖v - p‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := g) (C := c * ‖v - p‖)
    (fun w hw => (hg w (hball w (hsub hw)).2).hasFDerivWithinAt)
    (fun w hw => by
      have hw' := hball w (hsub hw)
      have e1 : ‖fderiv ℝ φ w - D - B (w - p)‖ ≤ c * ‖w - p‖ := by
        simpa using hw'.1
      have e2 : ‖w - p‖ ≤ ‖v - p‖ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hw
      exact e1.trans (mul_le_mul_of_nonneg_left e2 hc.le))
    (mem_closedBall_self (norm_nonneg _)) (by rw [mem_closedBall, dist_eq_norm])
  have : g v - g p = φ v - φ p - D (v - p) - B (v - p) (v - p) / 2 := by
    simp only [g]; rw [sub_self]; simp; ring
  rw [this] at hmvt
  rw [norm_pow, norm_norm]
  calc _ ≤ c * ‖v - p‖ * ‖v - p‖ := hmvt
    _ = c * ‖v - p‖ ^ 2 := by ring

end GlobalTheory.TaylorLevi

namespace GlobalTheory.TaylorLevi

variable {n : ℕ}

noncomputable section

theorem rmVec_coord (h : V n) : rmVec (fun j => h j) = h := by
  ext i
  simp [rmVec, bas, PiLp.single_apply, Pi.single_apply]

def linCoef (D : V n →L[ℝ] ℝ) (j : Fin n) : ℂ :=
  (D (bas n j) : ℂ) - Complex.I * (D (Complex.I • bas n j) : ℂ)

def quadCoef (B : V n →L[ℝ] V n →L[ℝ] ℝ) (j k : Fin n) : ℂ :=
  ((B (bas n j) (bas n k) - B (Complex.I • bas n j) (Complex.I • bas n k) : ℝ) : ℂ)
    - Complex.I * ((B (Complex.I • bas n j) (bas n k) + B (bas n j) (Complex.I • bas n k) : ℝ) : ℂ)

theorem lin_re (D : V n →L[ℝ] ℝ) (ξ : Fin n → ℂ) :
    (∑ j, linCoef D j * ξ j).re = D (rmVec ξ) := by

  simp only [rmVec, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rm_cplx_smul_eq]
  simp [linCoef, Complex.mul_re]
  ring

theorem quad_re (B : V n →L[ℝ] V n →L[ℝ] ℝ) (ξ : Fin n → ℂ) :
    (∑ j, ∑ k, quadCoef B j k * ξ j * ξ k).re =
      B (rmVec ξ) (rmVec ξ) - B (Complex.I • rmVec ξ) (Complex.I • rmVec ξ) := by
  rw [rm_I_smul_vec, rmVec, rm_bil_sum, rm_bil_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rm_bil_expand B (ξ j) (ξ k), rm_bil_expand B (Complex.I * ξ j) (Complex.I * ξ k)]
  simp [quadCoef, Complex.mul_re, Complex.mul_im]
  ring

end

end GlobalTheory.TaylorLevi

namespace GlobalTheory.TaylorLevi

theorem exists_holo_quadratic_add_levi : ∀ (n : ℕ) (φ : V n → ℝ) (p : V n), ContDiffAt ℝ 2 φ p →
    ∃ q : V n → ℂ, Differentiable ℂ q ∧
      (fun v : V n => φ v - 2 * (q v).re
        - (leviV n (fun w => ((φ w : ℝ) : ℂ)) p (fun j => (v - p) j)).re)
        =o[𝓝 p] (fun v : V n => ‖v - p‖ ^ 2) := by
  intro n φ p hφ
  set D := fderiv ℝ φ p
  set B := fderiv ℝ (fderiv ℝ φ) p
  refine ⟨fun v => (φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2
      + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8, ?_, ?_⟩
  · have hc : ∀ j, Differentiable ℂ (fun v : V n => (v - p) j) := fun j =>
      (EuclideanSpace.proj j : V n →L[ℂ] ℂ).differentiable.comp (differentiable_id.sub_const p)
    fun_prop
  · refine (taylor_two φ p hφ).congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards with v
    have hL := rm_levi_re_ofReal φ p hφ (fun j => (v - p) j)
    have hA := lin_re D (fun j => (v - p) j)
    have hQ := quad_re B (fun j => (v - p) j)
    rw [rmVec_coord] at hL hA hQ
    have hq : ((φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2
        + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8).re
        = φ p / 2 + (∑ j, linCoef D j * (v - p) j).re / 2
          + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k).re / 8 := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re]
    rw [hq, hA, hQ]
    linarith

end GlobalTheory.TaylorLevi
end

section

namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal Matrix

noncomputable section

abbrev Low (r : ℕ) : Type := {p : Fin r × Fin r // p.2 < p.1}

def lowMat {r : ℕ} (w : Low r → ℂ) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  if h : b < a then w ⟨(a, b), h⟩ else if a = b then 1 else 0

def colGram {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (k : Fin (q + 1)) : ℝ := ‖lminor (Mᴴ * M) k‖

def blkW {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : Matrix (Fin (r - 1)) (Fin (r - 1)) ℂ := fun i j =>
  if p0 = 1 then lowMat w ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ else lowMat w ⟨i, by omega⟩ ⟨j, by omega⟩

def gB {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : ℝ :=
  ∏ k : Fin (r - 1), colGram (blkW p0 w) k.castSucc ^ (-2 : ℤ)

def hB {r : ℕ} (p0 : ℕ) : (Low r → ℂ) → ℝ≥0∞ :=
  Set.indicator {w | ∀ p : Low r, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
    fun w => ENNReal.ofReal (gB p0 w)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def zOf (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Low r → ℂ := fun p =>
  z (Fintype.equivFin (Ent X) ⟨τ, p⟩)

def bnd (X : Data E r) (z : V (nd X)) : ℝ := ∏ τ, gB X.p0 (zOf X z τ)

theorem nmat_eq_lowMat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (Matrix.of (nmat X z τ) : Matrix (Fin r) (Fin r) ℂ) = lowMat (zOf X z τ) := by
  ext a b
  simp only [Matrix.of_apply, nmat, lowMat, zOf]

end

end GlobalTheory.IntBall
end

section

noncomputable section

namespace GlobalTheory.RiemConst

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def angles (θ : Fin (r - 1) → ℝ) (a : Fin r) : ℝ :=
  if h : (a : ℕ) < r - 1 then θ ⟨a, h⟩ else -∑ k, θ k

def phaseFrame {Ψ : Finset (E →+* ℂ)} (θ : Ψ → Fin (r - 1) → ℝ) : Frame Ψ r :=
  fun τ => Matrix.diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))

def inFrame {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (Y : Ψ → Fin r → Fin r → ℂ) (τ : Ψ) :
    Matrix (Fin r) (Fin r) ℂ :=
  (mat x τ)⁻¹ * Matrix.of (Y τ) * mat x τ

abbrev ChartSp (X : Data E r) : Type := ReciprocityTheory.L2DbarEstimates.V (nd X) × (X.Ψ → Fin (r - 1) → ℝ)

end GlobalTheory.RiemConst
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ProjField

def NormChart {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (N₀ : LB B.left) : Prop :=
  ∃ (W V : Over (Sp k)) (π : W ⟶ V) (a : W ⟶ B) (U : B.left.Opens) (N : LB (V ⊗ B).left) (n : N.Sec),
    IsFinite π.left ∧ IsOpenImmersion a.left ∧ Nonempty W.left ∧ LocallyOfFiniteType W.hom ∧
    IsAffineOpen U ∧ (U : Set B.left).Nonempty ∧ N.IsLB ∧ LBIso N (N₀.pull (snd V B).left) ∧
    ∀ x : (V ⊗ B).left, x ∈ Out.nonzeroLocus n ↔
      ∀ z : (W ⊗ B).left, (π ▷ B).left z = x → z ∈ ((fst W B ≫ a) * snd W B).left ⁻¹ᵁ U

end GlobalTheory.ProjField
end
end
