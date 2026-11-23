module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.ExpDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)

open scoped ENNReal

theorem gramVol_congr {e n : ℕ} {v v' : (Fin e → ℂ) → (Fin n → ℂ)} {y : Fin e → ℂ}
    (h : v =ᶠ[𝓝 y] v') : gramVol v y = gramVol v' y := by
  unfold gramVol
  rw [h.eq_of_nhds, h.fderiv_eq]

def gramForm {e n : ℕ} (p : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ))) : ℝ :=
  let w : Fin (e + 1) → Fin n → ℂ := Fin.cons p.1 fun j => p.2 (Pi.single j 1)
  (Matrix.det (Matrix.of fun a b => ∑ i, star (w a i) * w b i)).re

theorem gramVol_eq_gramForm {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    gramVol v y = gramForm (v y, fderiv ℂ v y) := rfl

theorem continuous_gramForm {e n : ℕ} :
    Continuous (gramForm : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) → ℝ) := by
  have hw : Continuous fun p : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) =>
      (Fin.cons p.1 fun j => p.2 (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) := by
    refine continuous_pi fun a => ?_
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa using continuous_fst
    · simpa using continuous_snd.clm_apply continuous_const
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_apply i).comp ((continuous_apply a).comp hw)).star.mul
    ((continuous_apply i).comp ((continuous_apply b).comp hw))

theorem aemeasurable_coneTerm {e n : ℕ} {U D : Set (Fin e → ℂ)} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hU : IsOpen U) (hDU : D ⊆ U)
    (hv : DifferentiableOn ℂ v U) (hF : Measurable F) :
    AEMeasurable (fun x => ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
      ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)) (volume.restrict D) := by
  have ha : AEMeasurable v (volume.restrict D) :=
    (hv.continuousOn.aemeasurable hU.measurableSet).mono_measure (Measure.restrict_mono hDU le_rfl)
  have hg : AEMeasurable (fun x => gramVol v x) (volume.restrict D) := by
    have h := continuous_gramForm.measurable.comp_aemeasurable
      (ha.prodMk (measurable_fderiv ℂ v).aemeasurable)
    simpa only [Function.comp_def, ← gramVol_eq_gramForm] using h
  have hmeas : Measurable fun p : (Fin e → ℂ) × ℂ => F (p.2 • WithLp.toLp 2 (ha.mk v p.1)) *
      ENNReal.ofReal (‖p.2‖ ^ (2 * e) * hg.mk _ p.1) := by
    refine (hF.comp (measurable_snd.smul ((PiLp.continuous_toLp 2 _).measurable.comp
      (ha.measurable_mk.comp measurable_fst)))).mul ?_
    exact ENNReal.measurable_ofReal.comp
      ((measurable_snd.norm.pow_const _).mul (hg.measurable_mk.comp measurable_fst))
  refine ⟨_, hmeas.lintegral_prod_right' (ν := (volume : Measure ℂ)), ?_⟩
  filter_upwards [ha.ae_eq_mk, hg.ae_eq_mk] with x h1 h2
  simp only [h1, h2]

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

theorem ConeMapArea.proof (h : ConeMapAreaOne.Statement) : ConeMapArea.Statement := by
  intro n e ι _ U D v F hUD hinj hF
  let g : ι → (Fin e → ℂ) × ℂ → EuclideanSpace ℂ (Fin n) := fun i q => q.2 • WithLp.toLp 2 (v i q.1)
  let S : ι → Set ((Fin e → ℂ) × ℂ) := fun i => {q | q.1 ∈ D i ∧ q.2 ≠ 0}
  have himg : (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0} = ⋃ i, g i '' S i := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i, x, t⟩, hq, rfl⟩
      exact ⟨i, (x, t), hq, rfl⟩
    · rintro ⟨i, ⟨x, t⟩, hq, rfl⟩
      exact ⟨(i, x, t), hq, rfl⟩
  have hinj_i : ∀ i, Set.InjOn (g i) (S i) := by
    intro i p hp p' hp' hpp
    exact (Prod.ext_iff.1 (@hinj (i, p) hp (i, p') hp' hpp)).2
  have hdisj : Pairwise (Function.onFun Disjoint fun i => g i '' S i) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro y ⟨p, hp, rfl⟩ ⟨p', hp', hpp⟩
    exact hij (congrArg Prod.fst (@hinj (j, p') hp' (i, p) hp hpp)).symm
  have hmeas : ∀ i, MeasurableSet (g i '' S i) := by
    intro i
    obtain ⟨-, hD, hDU, hv⟩ := hUD i
    refine MeasurableSet.image_of_continuousOn_injOn ?_ ?_ (hinj_i i)
    · exact (measurable_fst hD).inter (measurable_snd (measurableSet_singleton (0 : ℂ)).compl)
    · have hc : ContinuousOn (fun q : (Fin e → ℂ) × ℂ => WithLp.toLp 2 (v i q.1)) (S i) :=
        (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp_continuousOn
          ((hv.continuousOn.mono hDU).comp continuousOn_fst fun q hq => hq.1)
      exact continuousOn_snd.smul hc
  rw [himg, lintegral_iUnion hmeas hdisj, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  obtain ⟨hU, hD, hDU, hv⟩ := hUD i
  exact h n e (U i) (D i) (v i) F hU hD hDU hv (hinj_i i) hF

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Set Matrix Filter

noncomputable section

namespace ConeFsLog

variable {n : ℕ}

theorem dualNorm_pointOf (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.dualNorm (h.pointOf y) = ‖y‖ := by
  have hA : IsUnit h.matᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  rw [HermNorm.dualNorm, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA,
    Matrix.one_mulVec, EuclideanSpace.norm_eq]

theorem sum_mul_pointOf (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, u j * h.pointOf y j = ∑ i, (h.mat *ᵥ u) i * y i := by
  simp only [HermNorm.pointOf, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem norm_sum_mul_pointOf_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ h.norm u * ‖y‖ := by
  rw [sum_mul_pointOf, HermNorm.norm, EuclideanSpace.norm_eq]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem fsLog_pointOf (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    fsLog h u (h.pointOf y) = Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖) := by
  rw [fsLog, dualNorm_pointOf]

theorem fsLog_pointOf_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    fsLog h u (h.pointOf y) ≤ max (Real.log (h.norm u)) 0 := by
  rw [fsLog_pointOf]
  rcases (div_nonneg (norm_nonneg _) (norm_nonneg y) :
    0 ≤ ‖∑ j, u j * h.pointOf y j‖ / ‖y‖).eq_or_lt with hr | hr
  · rw [← hr, Real.log_zero]; exact le_max_right _ _
  · refine (Real.log_le_log hr ?_).trans (le_max_left _ _)
    have hy : 0 < ‖y‖ := by
      rcases (norm_nonneg y).eq_or_lt with h0 | h0
      · simp [← h0] at hr
      · exact h0
    exact (div_le_iff₀ hy).mpr (norm_sum_mul_pointOf_le h u y)

theorem norm_le_of_fsLog_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) {t : ℝ}
    (hy : fsLog h u (h.pointOf y) ≤ -t) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ Real.exp (-t) * ‖y‖ := by
  rw [fsLog_pointOf] at hy
  rcases (norm_nonneg y).eq_or_lt with h0 | h0
  · have := norm_sum_mul_pointOf_le h u y
    rw [← h0, mul_zero] at this
    rw [← h0, mul_zero]; exact this
  rcases (norm_nonneg (∑ j, u j * h.pointOf y j)).eq_or_lt with ha | ha
  · rw [← ha]; positivity
  · have := (Real.log_le_iff_le_exp (div_pos ha h0)).mp hy
    rwa [div_le_iff₀ h0] at this

end ConeFsLog


open ConeFsLog in
theorem ConeFsLogIntegrable.proof (hfin : ConeBallFinite.Statement)
    (hslab : ConeSlabBound.Statement) : ConeFsLogIntegrable.Statement := by
  intro n e h W f u hW hf hu
  have hS := hfin n e h W f hW hf
  obtain ⟨C, α, hα, hC⟩ := hslab n e h W f u hW hf hu
  set μ := (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict (coneBall h W)
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun y => fsLog h u (h.pointOf y) with hFdef
  set M := max (Real.log (h.norm u)) 0
  have hFm : Measurable F := by
    have : F = fun y => Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖) :=
      funext fun y => fsLog_pointOf h u y
    rw [this]
    have hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y) := by
      unfold HermNorm.pointOf; fun_prop
    refine Real.measurable_log.comp (Measurable.div ?_ measurable_norm)
    exact (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp hp)).norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun y => max (-F y) 0
  have hGm : Measurable G := hFm.neg.max measurable_const

  have hG : ∫⁻ y, ENNReal.ofReal (G y) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Filter.Eventually.of_forall fun y => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro y ⟨hy, hyS⟩
      refine ⟨hyS, norm_le_of_fsLog_le h u y ?_⟩
      have : t ≤ -F y := by
        rcases le_max_iff.mp (show t ≤ G y from hy) with h1 | h1
        · exact h1
        · linarith
      change F y ≤ -t; linarith
    · rw [← Real.exp_mul]; ring_nf
  refine ⟨hFm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hle : ∀ y, ‖F y‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G y) := by
    intro y
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := fsLog_pointOf_le h u y
    rcases le_or_gt 0 (F y) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F y) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F y) 0; have := le_max_right (Real.log (h.norm u)) 0
      linarith
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS, hG⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjSecDegree

variable {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)

set_option hygiene false in
local notation "ℝt" => MvPolynomial (Fin (e + 1)) ℂ

set_option hygiene false in
local notation "𝕂" => FractionRing ℝt

theorem projVar_ne_zero (i : Fin (e + 1)) : projVar e i ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective ℝt 𝕂)).2 (X_ne_zero i)

theorem algebraMap_C (c : ℂ) : algebraMap ℝt 𝕂 (C c) = algebraMap ℂ 𝕂 c := by
  rw [IsScalarTower.algebraMap_apply ℂ ℝt 𝕂 c, MvPolynomial.algebraMap_eq]

theorem chartForm_projPar :
    Vertical.chartForm (projPar A) =
      C (projVar e 0)⁻¹ * (ComplexSets.linPoly A 0).map (algebraMap ℂ 𝕂) := by

  simp only [Vertical.chartForm, linForm, projPar, ComplexSets.linPoly, map_sum, map_mul,
  MvPolynomial.map_C, MvPolynomial.map_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← C_mul, div_eq_inv_mul]

theorem secForm_projPar (i : Fin e) :
    Vertical.secForm (projPar A) i =
      C (projVar e i.succ) * (ComplexSets.linPoly A 0).map (algebraMap ℂ 𝕂) -
        C (projVar e 0) * (ComplexSets.linPoly A i.succ).map (algebraMap ℂ 𝕂) := by

  simp only [Vertical.secForm, linForm, projPar, ComplexSets.linPoly, map_sum, map_mul,
  MvPolynomial.map_C, MvPolynomial.map_X, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [C_sub, C_mul, C_mul]
  ring

theorem projHom_C (c : ℂ) : ComplexSets.projHom J A (C c) = Ideal.Quotient.mk J (C c) := by
  simp [ComplexSets.projHom, ComplexSets.pullback]
  rfl

theorem projHom_X (i : Fin (e + 1)) :
    ComplexSets.projHom J A (X i) = Ideal.Quotient.mk J (ComplexSets.linPoly A i) := by
  simp [ComplexSets.projHom, ComplexSets.pullback]


set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem finrank_eq [Algebra ℝt (MvPolynomial (Fin n) ℂ ⧸ J)]
    (hφ : ∀ p, algebraMap ℝt (MvPolynomial (Fin n) ℂ ⧸ J) p = ComplexSets.projHom J A p) :
    Module.finrank 𝕂 (TensorProduct ℝt 𝕂 (MvPolynomial (Fin n) ℂ ⧸ J)) =
      Module.finrank 𝕂
        (Vertical.SecAlg (J.map (MvPolynomial.map (algebraMap ℂ 𝕂))) (projPar A)) := by
  let I := Vertical.secIdeal (J.map (MvPolynomial.map (algebraMap ℂ 𝕂))) (projPar A)
  let σ : MvPolynomial (Fin n) ℂ →+* MvPolynomial (Fin n) 𝕂 := MvPolynomial.map (algebraMap ℂ 𝕂)
  have hmkC : ∀ k : 𝕂, Ideal.Quotient.mk I (C k) = algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) k :=
    fun _ => rfl
  have hmem : ∀ x ∈ I, Ideal.Quotient.mk I x = 0 := fun _ h => Ideal.Quotient.eq_zero_iff_mem.2 h

  have hunit : IsUnit (algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) (projVar e 0)) :=
    (IsUnit.mk0 _ (projVar_ne_zero 0)).map _
  have ha0 : Ideal.Quotient.mk I (σ (ComplexSets.linPoly A 0)) =
      algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) (projVar e 0) := by
    have h := hmem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [chartForm_projPar, map_sub, map_mul, map_one, hmkC, sub_eq_zero] at h
    calc _ = algebraMap 𝕂 _ (projVar e 0) * (algebraMap 𝕂 _ (projVar e 0)⁻¹ *
          Ideal.Quotient.mk I (σ (ComplexSets.linPoly A 0))) := by
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (projVar_ne_zero _), map_one, one_mul]
      _ = _ := by rw [h, mul_one]
  have ha : ∀ i, Ideal.Quotient.mk I (σ (ComplexSets.linPoly A i)) =
      algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) (projVar e i) := by
    refine Fin.cases ha0 fun i => ?_
    have h := hmem _ (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
    rw [secForm_projPar, map_sub, map_mul, map_mul, hmkC, hmkC, ha0, sub_eq_zero] at h
    exact hunit.mul_left_cancel (h.symm.trans (mul_comm _ _))

  let ψ : MvPolynomial (Fin n) ℂ ⧸ J →+* MvPolynomial (Fin n) 𝕂 ⧸ I :=
    Ideal.Quotient.lift J ((Ideal.Quotient.mk I).comp σ) fun p hp =>
      hmem _ (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp)))
  have hψ : ψ.comp (algebraMap ℝt _) = algebraMap ℝt (MvPolynomial (Fin n) 𝕂 ⧸ I) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, hφ, projHom_C, Ideal.Quotient.lift_mk, RingHom.comp_apply,
        MvPolynomial.map_C, hmkC, IsScalarTower.algebraMap_apply ℝt 𝕂, algebraMap_C]
    · rw [RingHom.comp_apply, hφ, projHom_X, Ideal.Quotient.lift_mk, RingHom.comp_apply, ha,
        IsScalarTower.algebraMap_apply ℝt 𝕂]
      rfl
  let g : (MvPolynomial (Fin n) ℂ ⧸ J) →ₐ[ℝt] MvPolynomial (Fin n) 𝕂 ⧸ I :=
    { ψ with commutes' := fun r => RingHom.congr_fun hψ r }
  let F := AlgHom.liftEquiv ℝt 𝕂 (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n) 𝕂 ⧸ I) g

  let G₀ : MvPolynomial (Fin n) 𝕂 →ₐ[𝕂] TensorProduct ℝt 𝕂 (MvPolynomial (Fin n) ℂ ⧸ J) :=
    aeval fun j => (1 : 𝕂) ⊗ₜ[ℝt] Ideal.Quotient.mk J (X j)
  have hG : G₀.toRingHom.comp σ =
      ((Algebra.TensorProduct.includeRight (R := ℝt) (A := 𝕂)).toRingHom).comp
        (Ideal.Quotient.mk J) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, σ,
        MvPolynomial.map_C, G₀, aeval_C]
      rw [← projHom_C J A, ← hφ, AlgHom.commutes, IsScalarTower.algebraMap_apply ℝt 𝕂, algebraMap_C]
    · simp [G₀, σ]
  have hGa : ∀ i, G₀ (σ (ComplexSets.linPoly A i)) = G₀ (C (projVar e i)) := by
    intro i
    have h := RingHom.congr_fun hG (ComplexSets.linPoly A i)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
    rw [h, ← projHom_X J A, ← hφ, AlgHom.commutes, IsScalarTower.algebraMap_apply ℝt 𝕂, aeval_C]
    rfl
  have hker : I ≤ RingHom.ker G₀ := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (G₀.toRingHom.comp σ) p = 0
      rw [hG, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, secForm_projPar, map_sub, map_mul, map_mul, aeval_C,
        aeval_C]
      change _ * G₀ (σ _) - _ * G₀ (σ _) = 0
      rw [hGa, hGa, aeval_C, aeval_C, ← map_mul, ← map_mul, mul_comm (projVar e i.succ), sub_self]
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, chartForm_projPar, ← C_1, map_sub,
        map_mul, aeval_C, aeval_C]
      change _ * G₀ (σ _) - _ = 0
      rw [hGa, aeval_C, ← map_mul, inv_mul_cancel₀ (projVar_ne_zero _), sub_self]
  let G := Ideal.Quotient.liftₐ I G₀ fun a ha => (RingHom.mem_ker).1 (hker ha)
  have h₁ : F.comp G = AlgHom.id 𝕂 _ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    change F (G₀ (X j)) = Ideal.Quotient.mk I (X j)
    simp only [G₀, aeval_X, F, AlgHom.liftEquiv_tmul, one_smul]
    change ψ (Ideal.Quotient.mk J (X j)) = _
    simp only [ψ, Ideal.Quotient.lift_mk, RingHom.comp_apply, σ, MvPolynomial.map_X]
  have h₂ : G.comp F = AlgHom.id 𝕂 _ := by
    refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    apply AlgHom.toRingHom_injective
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_))
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← projHom_C J A, ← hφ, AlgHom.coe_toRingHom,
        AlgHom.coe_toRingHom, AlgHom.commutes, AlgHom.commutes]
    · simp only [F, G, G₀, g, ψ, σ, RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.coe_comp,
        AlgHom.coe_restrictScalars', Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
        AlgHom.liftEquiv_tmul, one_smul, AlgHom.coe_id, id_eq, AlgHom.coe_mk, Ideal.Quotient.lift_mk,
        MvPolynomial.map_X]
      change G (Ideal.Quotient.mk I (X j)) = _
      exact aeval_X (R := 𝕂) (fun j => (1 : 𝕂) ⊗ₜ[ℝt] Ideal.Quotient.mk J (X j)) j
  exact (AlgEquiv.ofAlgHom G F h₂ h₁).toLinearEquiv.finrank_eq.symm

end ProjSecDegree

theorem ProjSecDegree.proof : ProjSecDegree.Statement := by
  intro n e J A
  let : Algebra (MvPolynomial (Fin (e + 1)) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (ComplexSets.projHom J A).toRingHom.toAlgebra
  exact ProjSecDegree.finrank_eq J A fun _ => rfl

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime geoNum divSupp multAt)

theorem linForm_single {F : Type} [Field F] {n : ℕ} (i : Fin n) : linForm (Pi.single i (1 : F)) = X i := by
  simp [linForm, Pi.single_apply]

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end
