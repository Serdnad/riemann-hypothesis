module

public import Mathlib.MeasureTheory.Function.L2Space
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle014
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

theorem sq_add_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem lint_add_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℂ} {k : α → ℝ}
    (hk : ∀ x, 0 < k x) {om : α → ℝ≥0∞}
    (ha : AEMeasurable (fun x => ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) μ) :
    ∫⁻ x, ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x ∂μ ≤
      2 * ∫⁻ x, ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x ∂μ +
        2 * ∫⁻ x, ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x ∂μ := by
  calc ∫⁻ x, ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x ∂μ
      ≤ ∫⁻ x, (2 * (ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) +
          2 * (ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x)) ∂μ := by
        refine lintegral_mono fun x => ?_
        have hk' := hk x
        have hA : 0 ≤ ‖a x‖ ^ 2 / k x := div_nonneg (sq_nonneg _) hk'.le
        have hB : 0 ≤ ‖b x‖ ^ 2 / k x := div_nonneg (sq_nonneg _) hk'.le
        have h1 : ‖a x + b x‖ ^ 2 / k x ≤ 2 * (‖a x‖ ^ 2 / k x) + 2 * (‖b x‖ ^ 2 / k x) := by
          rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
          exact div_le_div_of_nonneg_right (sq_add_le _ _) hk'.le
        calc ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x
            ≤ ENNReal.ofReal (2 * (‖a x‖ ^ 2 / k x) + 2 * (‖b x‖ ^ 2 / k x)) * om x := by
              gcongr
          _ = 2 * (ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) +
                2 * (ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x) := by
              rw [ENNReal.ofReal_add (mul_nonneg zero_le_two hA) (mul_nonneg zero_le_two hB),
                ENNReal.ofReal_mul (zero_le_two : (0 : ℝ) ≤ 2),
                ENNReal.ofReal_mul (zero_le_two : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
              ring
    _ = 2 * ∫⁻ x, ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x ∂μ +
          2 * ∫⁻ x, ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x ∂μ := by
        rw [lintegral_add_left' (ha.const_mul 2), lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

theorem pnorm_sub_le (la : Wt X.Ψ r) (f g : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (fun y => f y - g y) x ≤ X.pnorm la f x + X.pnorm la g x := by
  unfold Data.pnorm
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _)
    (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)

theorem bdd_sub {la : Wt X.Ψ r} {f g : Frame X.Ψ r → ℂ} (hf : X.IsBddSec la f) (hg : X.IsBddSec la g) :
    X.IsBddSec la (fun y => f y - g y) := by
  obtain ⟨hf1, C1, hC1⟩ := hf
  obtain ⟨hg1, C2, hC2⟩ := hg
  refine ⟨?_, C1 + C2, fun x hx => (pnorm_sub_le X la f g x).trans (add_le_add (hC1 x hx) (hC2 x hx))⟩
  unfold Data.IsSec at hf1 hg1 ⊢
  obtain ⟨hd1, hb1, hl1⟩ := hf1
  obtain ⟨hd2, hb2, hl2⟩ := hg1
  refine ⟨hd1.sub hd2, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · simp only [hb1 x hx b hb, hb2 x hx b hb]
    ring
  · simp only [hl1 γ hγ x hx, hl2 γ hγ x hx]
    ring

theorem poin_add (la : Wt X.Ψ r) {P1 P2 : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (h1 : Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P1 (lact γ.1 x)‖)
    (h2 : Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P2 (lact γ.1 x)‖) :
    poin X la (fun y => P1 y + P2 y) x = poin X la P1 x + poin X la P2 x := by
  unfold poin
  rw [← Summable.tsum_add h1.of_norm h2.of_norm]
  congr 1
  funext γ
  ring

theorem poin_smul (la : Wt X.Ψ r) (a : ℂ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    poin X la (fun y => a * P y) x = a * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  ring

theorem poin_zero (la : Wt X.Ψ r) (x : Frame X.Ψ r) : poin X la (fun _ => 0) x = 0 := by
  simp [poin]

variable (W : Frame X.Ψ r → ℝ≥0∞) (FF : Set (V (nd X)))

def nuF : Measure (V (nd X)) :=
  ((muF X x0).restrict FF).withDensity fun z => ENNReal.ofReal (W (cpt X x0 z)).toReal

variable {X x0 W FF}

private lemma measurable_cpt : Measurable (cpt X x0) := by
  refine Measurable.of_eval fun τ => Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [cpt, rmul, mat, nmat, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun c _ => ?_
  split_ifs
  · refine Measurable.const_mul ?_ _
    first
      | exact measurable_pi_apply _
      | exact (EuclideanSpace.proj _).continuous.measurable
      | fun_prop
  · exact measurable_const
  · exact measurable_const

theorem dens_meas (hW : Measurable W) :
    Measurable fun z => ENNReal.ofReal (W (cpt X x0 z)).toReal :=
  (hW.comp measurable_cpt).ennreal_toReal.ennreal_ofReal

theorem nuF_ac : nuF X x0 W FF ≪ muF X x0 := by
  unfold nuF
  exact (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

private lemma measurableSet_dom' : MeasurableSet X.dom := by
  have hc : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
    fun_prop
  have hd : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := fun τ =>
    Continuous.matrix_det (A := fun x : Frame X.Ψ r => mat x τ) (continuous_apply τ)
  have ho : IsOpen X.dom := by
    show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
    simp only [Set.setOf_forall, Set.setOf_and]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hd τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i =>
        isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hc τ i))))
  exact ho.measurableSet

theorem memLp_of (hW : Measurable W) {h : Frame X.Ψ r → ℂ} (hh : ContinuousOn h X.dom)
    (hF : InFF X x0 W FF h) : MemLp (fun z => h (cpt X x0 z)) 2 (nuF X x0 W FF) := by
  classical
  unfold InFF at hF
  have hOm : MeasurableSet (OmF X x0) := measurable_cpt measurableSet_dom'
  have hae : ∀ᵐ z ∂nuF X x0 W FF, z ∈ OmF X x0 := by
    have h1 : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := by
      unfold muF
      exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hOm)
    exact nuF_ac.ae_le h1
  have hg : Measurable (X.dom.piecewise h 0) :=
    ContinuousOn.measurable_piecewise hh continuous_const.continuousOn measurableSet_dom'
  have hm : AEStronglyMeasurable (fun z => h (cpt X x0 z)) (nuF X x0 W FF) := by
    have hm0 : Measurable fun z => X.dom.piecewise h 0 (cpt X x0 z) := hg.comp measurable_cpt
    refine hm0.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with z hz
    exact Set.piecewise_eq_of_mem _ _ _ hz
  refine (memLp_two_iff_integrable_sq_norm hm).2 ⟨hm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => by
    simp only [Pi.zero_apply]
    positivity)]
  refine lt_of_le_of_lt ?_ hF
  unfold nuF
  refine (lintegral_withDensity_le_lintegral_mul _ (dens_meas hW) _).trans (lintegral_mono fun z => ?_)
  simp only [Pi.mul_apply]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le zero_le

theorem integral_nu (hW : Measurable W) (g : V (nd X) → ℂ) :
    ∫ z, g z ∂nuF X x0 W FF = ∫ z in FF, g z * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 := by
  unfold nuF
  rw [integral_withDensity_eq_integral_toReal_smul (dens_meas hW)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext z
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, Complex.real_smul, mul_comm]

theorem inner_toLp (hW : Measurable W) {a b : V (nd X) → ℂ} (ha : MemLp a 2 (nuF X x0 W FF))
    (hb : MemLp b 2 (nuF X x0 W FF)) :
    ⟪ha.toLp a, hb.toLp b⟫_ℂ = ∫ z in FF, conj (a z) * b z * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 := by
  rw [MeasureTheory.L2.inner_def]
  have h : ∀ᵐ z ∂nuF X x0 W FF, ⟪(ha.toLp a) z, (hb.toLp b) z⟫_ℂ = conj (a z) * b z := by
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with z h1 h2
    rw [h1, h2]
    simp [RCLike.inner_apply] <;> ring
  rw [integral_congr_ae h, integral_nu hW]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem measInv_holds : MeasInvStatement (E := E) := GlobalTheory.FrameMeasureClosed.measInv_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem muF_lintegral (x0 : Frame X.Ψ r) (g : V (nd X) → ℝ≥0∞) :
    ∫⁻ z, g z ∂muF X x0 = ∫⁻ z in OmF X x0, ENNReal.ofReal (densF X x0 z) * g z := by
  unfold muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (densF_meas X x0).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rfl

theorem rhoF_split (x0 : Frame X.Ψ r) (Fp : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (bb : ℝ) {z : V (nd X)}
    (hz : z ∈ OmF X x0) :
    rhoF X x0 Fp ψ bb z = densF X x0 z * (Real.exp (-(phla X Fp (cpt X x0 z) + ψ (cpt X x0 z))) /
      kaF X x0 bb z) := by
  unfold rhoF kaF
  rw [Real.exp_add, Real.exp_add, Real.exp_log (densF_pos X x0 hz), div_eq_mul_inv, ← Real.exp_neg,
    show -(-bb * rhF X x0 z) = bb * rhF X x0 z by ring]
  ring

theorem inAt_of (x0 : Frame X.Ψ r) (Fp : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (bb : ℝ) (F : V (nd X) → ℂ)
    (hint : ∫⁻ z in OmF X x0, ENNReal.ofReal (‖F z‖ ^ 2 * rhoF X x0 Fp ψ bb z) < ⊤) :
    InAt X x0 (Wpsi X Fp ψ) bb F := by
  have hmeas : MeasurableSet (OmF X x0) := (ExF.isOpen_OmF X x0).measurableSet
  unfold InAt
  rw [muF_lintegral]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint
  filter_upwards [ae_restrict_mem hmeas] with z hz
  have hd := (densF_pos X x0 hz).le
  have hz' : cpt X x0 z ∈ X.dom := hz
  have hW : Wpsi X Fp ψ (cpt X x0 z) =
      ENNReal.ofReal (Real.exp (-(phla X Fp (cpt X x0 z) + ψ (cpt X x0 z)))) := by
    unfold Wpsi; rw [if_pos hz']
  have hk : 0 < kaF X x0 bb z := Real.exp_pos _
  rw [hW, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hd,
    rhoF_split X x0 Fp ψ bb hz]
  apply le_of_eq
  congr 1
  ring

theorem extF_hyp (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (Fp : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ)
    (C0 : ℝ) (hψb : ∀ x ∈ X.dom, ψ x ≤ C0) (bb : ℝ) (hbb : 0 ≤ bb) (F : V (nd X) → ℂ)
    (hint : ∫⁻ z in OmF X x0, ENNReal.ofReal (‖F z‖ ^ 2 * rhoF X x0 Fp ψ bb z) < ⊤) :
    ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X Fp (cpt X x0 z))) ∂muF X x0 < ⊤ := by
  intro C _ _
  have hmeas : MeasurableSet (OmF X x0) := (ExF.isOpen_OmF X x0).measurableSet
  refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) ?_
  rw [muF_lintegral]
  have hfin : ∫⁻ z in OmF X x0, ENNReal.ofReal (Real.exp C0) *
      ENNReal.ofReal (‖F z‖ ^ 2 * rhoF X x0 Fp ψ bb z) < ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hfin
  filter_upwards [ae_restrict_mem hmeas] with z hz
  have hd := (densF_pos X x0 hz).le
  have hψ := hψb _ hz
  have hrh := ExF.rhF_nonneg X x0 ho hz
  rw [← ENNReal.ofReal_mul hd, ← ENNReal.ofReal_mul (Real.exp_pos _).le, rhoF_split X x0 Fp ψ bb hz]
  apply ENNReal.ofReal_le_ofReal
  have key : 1 ≤ Real.exp C0 * (Real.exp (-(phla X Fp (cpt X x0 z) + ψ (cpt X x0 z))) /
      kaF X x0 bb z) * Real.exp (phla X Fp (cpt X x0 z)) := by
    unfold kaF
    rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.one_le_exp
    nlinarith [mul_nonneg hbb hrh]
  have he : Real.exp (phla X Fp (cpt X x0 z)) * Real.exp (-phla X Fp (cpt X x0 z)) = 1 := by
    rw [← Real.exp_add]; simp
  have hA : 0 ≤ ‖F z‖ ^ 2 := by positivity
  have hE : 0 ≤ Real.exp (-phla X Fp (cpt X x0 z)) := (Real.exp_pos _).le
  calc densF X x0 z * (‖F z‖ ^ 2 * Real.exp (-phla X Fp (cpt X x0 z)))
      = (densF X x0 z * ‖F z‖ ^ 2 * Real.exp (-phla X Fp (cpt X x0 z))) * 1 := by ring
    _ ≤ (densF X x0 z * ‖F z‖ ^ 2 * Real.exp (-phla X Fp (cpt X x0 z))) *
        (Real.exp C0 * (Real.exp (-(phla X Fp (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z) *
          Real.exp (phla X Fp (cpt X x0 z))) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg (mul_nonneg hd hA) hE)
    _ = Real.exp C0 * (‖F z‖ ^ 2 * (densF X x0 z * (Real.exp (-(phla X Fp (cpt X x0 z) +
          ψ (cpt X x0 z))) / kaF X x0 bb z))) *
          (Real.exp (phla X Fp (cpt X x0 z)) * Real.exp (-phla X Fp (cpt X x0 z))) := by ring
    _ = _ := by rw [he, mul_one]

theorem value_base (hV : VanishAtSStatement (E := E)) (x0 : Frame X.Ψ r) (ho : IsOrth X x0)
    (Xa : ArchInM X) (Fl : FlatM X Xa) (ψ : Frame X.Ψ r → ℝ)
    (hψs : ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) (bb : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hball : closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0) (F : V (nd X) → ℂ)
    (hFd : DifferentiableOn ℂ F (OmF X x0))
    (hI : ∫⁻ y in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤)
    (P : Frame X.Ψ r → ℂ) (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z)
    (hw : Fl.w0 x0 ≠ 0) (hs0 : ∀ k, Fl.s k x0 = 0)
    (hdet : (fderiv ℂ (fun z => sig X Fl.w0 Fl.s (cpt X x0 z)) 0).det ≠ 0) : P x0 = 1 := by
  have hn : 0 < nd X := by have := Xa.n_ge; omega
  have h0 : cpt X x0 0 ∈ X.dom := hball (mem_closedBall_self (by linarith))
  have hx0 : x0 ∈ X.dom := by rwa [cpt_zero] at h0
  have hsub2 : closedBall (0 : V (nd X)) ε ⊆ OmF X x0 :=
    fun z hz => hball (closedBall_subset_closedBall (by linarith) hz)
  have hsub : ball (0 : V (nd X)) ε ⊆ OmF X x0 := fun z hz => hsub2 (ball_subset_closedBall hz)
  have hu : DifferentiableOn ℂ (fun z => (fun x => P x - 1) (cpt X x0 z)) (ball 0 ε) :=
    ((hFd.mono hsub).sub_const 1).congr fun z hz => by
      show P (cpt X x0 z) - 1 = F z - 1
      rw [hPF z (hsub hz)]
  have hsd : ∀ k, DifferentiableOn ℂ (fun z => Fl.s k (cpt X x0 z)) (ball 0 ε) :=
    fun k => (comp_cpt_diffOn X (Fl.s_van k).1.1.1.1 x0).mono hsub
  have hwd : DifferentiableOn ℂ (fun z => Fl.w0 (cpt X x0 z)) (ball 0 ε) :=
    (comp_cpt_diffOn X Fl.weightForm_vanishes.1.1.1.1 x0).mono hsub
  have hcont : ContinuousOn (psie X x0 Xa.Fp Xa.L ψ bb) (closedBall 0 ε) := fun z hz =>
    (psie_cdAt X x0 ho Xa.Fp Xa.L ψ hψs bb (hsub2 hz)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : V (nd X)) ε).bddAbove_image hcont
  have hmeasB : MeasurableSet (ball (0 : V (nd X)) ε) := measurableSet_ball
  have hint : ∫⁻ z in ball (0 : V (nd X)) ε, ENNReal.ofReal (‖(fun x => P x - 1) (cpt X x0 z)‖ ^ 2 *
      (∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2) ^ (-(nd X : ℝ))) < ⊤ := by
    have hfin : ∫⁻ y in OmF X x0, ENNReal.ofReal (Real.exp M) *
        ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 * Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI
    refine lt_of_le_of_lt ?_ hfin
    refine le_trans ?_ (lintegral_mono_set hsub)
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hmeasB] with z hz
    have hzc : z ∈ closedBall (0 : V (nd X)) ε := ball_subset_closedBall hz
    have hcut : HE.cut ε hε z = 1 := by
      unfold HE.cut
      rw [(HE.bumpE ε hε).one_of_mem_closedBall hzc]
      simp
    have hnsq : HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z = ∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2 := by
      unfold HE.nsq
      simp [Complex.normSq_eq_norm_sq]
    have hpe : 1 ≤ Real.exp M * Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have := hM ⟨z, hzc, rfl⟩
      linarith
    beta_reduce
    rw [hcut, hnsq, hPF z (hsub hz), ← ENNReal.ofReal_mul (Real.exp_pos _).le, norm_sub_rev (1 : ℂ) (F z)]
    apply ENNReal.ofReal_le_ofReal
    have hN : 0 ≤ (∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2) ^ (-(nd X : ℝ)) :=
      Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _
    have hA : 0 ≤ ‖F z - 1‖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpe (mul_nonneg hA hN)]
  have key := hV r X x0 hn ho hx0 (fun x => P x - 1) Fl.w0 Fl.s ε hε hu hsd hwd hw hs0 hdet hint
  simpa [sub_eq_zero] using key

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end
