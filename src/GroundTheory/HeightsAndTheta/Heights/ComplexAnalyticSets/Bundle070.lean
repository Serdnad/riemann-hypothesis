module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle048
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import Mathlib.Algebra.Module.Submodule.Union
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle034
public import Mathlib.Topology.Separation.CompletelyRegular
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.MeasureTheory.Integral.ExpDecay

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LinearFormCut.formMap (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] MvPolynomial (Fin n) ℂ where
  toFun a := ∑ j, C (a j) * X j
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [smul_eq_C_mul, Finset.mul_sum, mul_assoc]

theorem LinearFormCut.proof : LinearFormCut.Statement := by
  intro n e I hI
  classical
  let S := {Q : Ideal (MvPolynomial (Fin n) ℂ) | Q ∈ I.minimalPrimes ∧ Q ≠ originIdeal n}
  have : Finite S :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset fun Q (hQ : Q ∈ S) => hQ.1).to_subtype
  let p : S → Submodule ℂ (Fin n → ℂ) := fun Q => (Q.1.restrictScalars ℂ).comap (formMap n)
  have hp : ∀ Q, p Q ≠ ⊤ := by
    intro Q htop
    apply Q.2.2
    have hle : originIdeal n ≤ Q.1 := by
      rw [originIdeal, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : Pi.single j 1 ∈ p Q := htop ▸ Submodule.mem_top
      simpa [p, formMap, Pi.single_apply] using this
    exact ((originIdeal_isMaximal n).eq_of_le Q.2.1.1.1.ne_top hle).symm
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  let B : Matrix (Fin 1) (Fin n) ℂ := Matrix.of fun _ j => a j
  refine ⟨B, ?_⟩
  have hl : formMap n a ∈ linIdeal B := Ideal.subset_span ⟨0, by simp [linPoly, formMap, B]⟩
  rw [ringKrullDim_quotient] at hI ⊢
  refine iSup_le fun l => ?_
  have hIh : I ≤ l.head.1.asIdeal := fun y hy => l.head.2 (Ideal.mem_sup_left hy)
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hIh
  by_cases hQo : Q = originIdeal n
  · have hM : l.head.1.asIdeal.IsMaximal := by
      rw [← (originIdeal_isMaximal n).eq_of_le l.head.1.isPrime.ne_top (hQo ▸ hQle)]
      exact originIdeal_isMaximal n
    have h0 : l.length = 0 := by
      by_contra h
      have hlt : l.head < l.last := l.strictMono (Fin.pos_iff_ne_zero.2 (by simp [Fin.ext_iff]; omega))
      have hlt' : l.head.1.asIdeal < l.last.1.asIdeal := hlt
      exact (hM.eq_of_le l.last.1.isPrime.ne_top hlt'.le ▸ hlt').false
    simp [h0]
  · have hQa : formMap n a ∉ Q := ha ⟨Q, hQ, hQo⟩
    let f : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑(I ⊔ linIdeal B) →
        PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I :=
      fun x => ⟨x.1, fun y hy => x.2 (Ideal.mem_sup_left hy)⟩
    have hf : StrictMono f := fun x y h => h
    let q0 : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I :=
      ⟨⟨Q, hQ.1.1⟩, fun y hy => hQ.1.2 hy⟩
    have hq : q0 < (l.map f hf).head := by
      refine lt_of_le_of_ne hQle fun h => hQa ?_
      have : formMap n a ∈ l.head.1.asIdeal := l.head.2 (Ideal.mem_sup_right hl)
      have hQh : Q = l.head.1.asIdeal :=
        congrArg (fun x : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I => x.1.asIdeal) h
      rwa [hQh]
    have hlen := (Order.LTSeries.length_le_krullDim ((l.map f hf).cons q0 hq)).trans hI
    simp only [RelSeries.cons_length] at hlen
    have : l.length + 1 ≤ e + 1 := by exact_mod_cast hlen
    exact_mod_cast (by omega : l.length ≤ e)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Set Filter ComplexSets

open scoped ENNReal

noncomputable section

namespace LogIntegrableProof

variable {n : ℕ}

theorem lintegral_lt_top (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) {d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} (u : Fin n → ℂ) (R : ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hu : linForm u ∉ J) :
    ∫⁻ z in zeroSetEuc J ∩ {z | ‖z‖ ≤ R}, ‖Real.log ‖∑ j, u j * z j‖‖ₑ
      ∂(μH[((2 * d : ℕ) : ℝ)]) < ⊤ := by
  obtain ⟨C, α, hα, hC⟩ := hS n d J u R hJ hdim hu
  set S := zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | ‖z‖ ≤ R} with hSdef
  set μ := (μH[((2 * d : ℕ) : ℝ)]).restrict S
  have hsub : S ⊆ zeroSetEuc J ∩ Metric.ball 0 (R + 1) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [mem_ball_zero_iff]
    linarith [(show ‖z‖ ≤ R from hz.2)]
  have hSfin : μH[((2 * d : ℕ) : ℝ)] S < ⊤ :=
    (measure_mono hsub).trans_lt (hF n d J hJ hdim (R + 1))
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin n) => ∑ j, u j * z j := by fun_prop
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun z => Real.log ‖∑ j, u j * z j‖
  have hFm : Measurable F := Real.measurable_log.comp hcont.norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun z => max (-F z) 0
  have hGm : Measurable G := hFm.neg.max measurable_const
  set M : ℝ := max (∑ j, ‖u j‖ * R) 0

  have hFle : ∀ z ∈ S, F z ≤ M := by
    intro z hz
    refine (Real.log_le_self (norm_nonneg _)).trans ((norm_sum_le _ _).trans ?_)
    refine le_trans ?_ (le_max_left _ _)
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le z j).trans hz.2) (norm_nonneg _)

  have hG : ∫⁻ z, ENNReal.ofReal (G z) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Eventually.of_forall fun z => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro z ⟨hz, hzS⟩
      refine ⟨hzS, ?_⟩
      have htF : F z ≤ -t := by
        rcases le_max_iff.mp (show t ≤ G z from hz) with h1 | h1
        · linarith
        · linarith
      change ‖∑ j, u j * z j‖ ≤ Real.exp (-t)
      rcases (norm_nonneg (∑ j, u j * z j)).eq_or_lt with h0 | h0
      · rw [← h0]; positivity
      · exact (Real.log_le_iff_le_exp h0).mp htF
    · rw [← Real.exp_mul]; ring_nf
  have hle : ∀ z ∈ S, ‖F z‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G z) := by
    intro z hz
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hFle z hz
    rcases le_or_gt 0 (F z) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F z) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F z) 0; have := le_max_right (∑ j, ‖u j‖ * R) 0
      linarith
  refine lt_of_le_of_lt (setLIntegral_mono (g := fun z => ENNReal.ofReal M + ENNReal.ofReal (G z))
    (measurable_const.add hGm.ennreal_ofReal) hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSfin, hG⟩

end LogIntegrableProof


open LogIntegrableProof in
theorem LogIntegrable.proof (hM : SheetSumMeasurable.Statement) (hD : ChartMassCompare.Statement)
    (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) : LogIntegrable.Statement := by
  intro n d J A u φ R hJ hdim hA hu hφ
  have hcont : Continuous fun x : Fin n → ℂ => linEval u x := by unfold linEval; fun_prop
  have hwm : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖ :=
    Real.measurable_log.comp (continuous_norm.comp hcont).measurable
  refine ⟨(hM n d J A _ φ hJ hdim hA (hwm.indicator measurableSet_closedBall) hφ).2.aestronglyMeasurable,
    ?_⟩
  obtain ⟨K, hK, hDK⟩ := hD n d J A φ R hJ hdim hA hφ

  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ L * ‖WithLp.ofLp z‖ :=
    ⟨(n : ℝ) ^ (2⁻¹ : ℝ), by positivity, fun z => by
      simpa [dist_zero_right] using
        (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℂ)).dist_le_mul (WithLp.ofLp z) 0⟩
  unfold HasFiniteIntegral
  refine (hDK _ hwm).trans_lt (ENNReal.mul_lt_top hK ?_)
  refine lt_of_le_of_lt (lintegral_mono_set ?_) (lintegral_lt_top hS hF u (L * R) hJ hdim hu)
  rintro z ⟨hz, hzB⟩
  refine ⟨hz, ?_⟩
  have : ‖WithLp.ofLp z‖ ≤ R := mem_closedBall_zero_iff.mp hzB
  exact (hL z).trans (mul_le_mul_of_nonneg_left this hL0)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology
open scoped ContDiff

noncomputable section

private def cutProfile (k : ℕ) (w : ℝ) : ℝ :=
  if w = 0 then 0 else if 1 ≤ w then 1 else cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1))

private theorem cutStep_small (k : ℕ) {w : ℝ} (h0 : w ≠ 0) (hw : |w| < cutLevel k) :
    cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1)) = 0 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : Real.log w < -Real.exp ((k : ℝ) + 1) := by
    rw [← Real.log_abs, ← Real.log_exp (-Real.exp _)]
    exact Real.log_lt_log (abs_pos.2 h0) hw
  have h2 : (k : ℝ) + 1 < Real.log (-Real.log w) := by
    rw [← Real.log_exp ((k : ℝ) + 1)]
    exact Real.log_lt_log (Real.exp_pos _) (by linarith)
  have h3 : 1 < Real.log (-Real.log w) / ((k : ℝ) + 1) := (one_lt_div hk).2 h2
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem cutStep_large (k : ℕ) {w : ℝ} (hw : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < w)
    (h1 : w < 1) : cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1)) = 1 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hw0 : 0 < w := (Real.exp_pos _).trans hw
  have hl : -Real.exp (((k : ℝ) + 1) / 2) < Real.log w := by
    rw [← Real.log_exp (-Real.exp _)]
    exact Real.log_lt_log (Real.exp_pos _) hw
  have hneg : 0 < -Real.log w := neg_pos.2 (Real.log_neg hw0 h1)
  have h2 : Real.log (-Real.log w) < ((k : ℝ) + 1) / 2 := by
    rw [← Real.log_exp (((k : ℝ) + 1) / 2)]
    exact Real.log_lt_log hneg (by linarith)
  have h3 : Real.log (-Real.log w) / ((k : ℝ) + 1) < 1 / 2 := by
    rw [div_lt_iff₀ hk]; linarith
  exact Real.smoothTransition.one_of_one_le (by linarith)

private theorem cutProfile_contDiffOn (k : ℕ) :
    ContDiffOn ℝ ∞ (cutProfile k) (Set.Ioi (-cutLevel k)) := by
  obtain ⟨hc0, hc1⟩ := cutLevel_mem k
  set c' := Real.exp (-Real.exp (((k : ℝ) + 1) / 2))
  have hc'1 : c' < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _))
  refine (isOpen_Ioi.contDiffOn_iff).2 fun x hx => ?_
  rcases lt_or_ge x (cutLevel k) with hxc | hxc
  ·
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (Set.mem_Ioi.1 hx) hxc] with w hw
    have hwa : |w| < cutLevel k := abs_lt.2 hw
    unfold cutProfile
    split_ifs with h0 h1
    · rfl
    · exact absurd (h1.trans_lt (hw.2.trans hc1)) (lt_irrefl _)
    · exact cutStep_small k h0 hwa
  rcases lt_or_ge c' x with hxc' | hxc'
  ·
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hxc'] with w hw
    have hw0 : 0 < w := (Real.exp_pos _).trans hw
    unfold cutProfile
    split_ifs with h0 h1
    · exact absurd h0 hw0.ne'
    · rfl
    · exact cutStep_large k hw (not_le.1 h1)
  ·
    have hx0 : 0 < x := hc0.trans_le hxc
    have hx1 : x < 1 := hxc'.trans_lt hc'1
    have hform : ContDiffAt ℝ ∞ (fun w => cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1))) x := by
      have hlog : ContDiffAt ℝ ∞ (fun w => Real.log (-Real.log w)) x :=
        ((Real.contDiffAt_log.2 hx0.ne').neg).log (neg_ne_zero.2 (Real.log_neg hx0 hx1).ne)
      exact Real.smoothTransition.contDiffAt.comp x
        (contDiffAt_const.sub (contDiffAt_const.mul (hlog.div_const _)))
    refine hform.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx0 hx1] with w hw
    simp [cutProfile, hw.1.ne', not_le.2 hw.2]

theorem CutOffShape.proof : CutOffShape.Statement := by
  intro m Q
  have hF : ∀ k, logLogCut Q k = cutProfile k ∘ fun y => ‖eval y Q‖ ^ 2 := fun k => rfl
  have hstep : ∀ t, cutStep t ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨fun k => ⟨?_, fun y => ?_, fun y hy => ?_⟩, fun y hy => ?_⟩
  · rw [hF]
    have hw : ContDiff ℝ ∞ fun y : Fin m → ℂ => ‖eval y Q‖ ^ 2 :=
      contDiff_norm_sq ℝ |>.comp
        (((AnalyticOnNhd.eval_mvPolynomial Q).contDiff (n := ∞)).restrict_scalars ℝ)
    exact (cutProfile_contDiffOn k).comp_contDiff hw fun y =>
      (neg_neg_of_pos (cutLevel_mem k).1).trans_le (by exact sq_nonneg ‖eval y Q‖)
  · unfold logLogCut; split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hstep _
  · have h1 := (cutLevel_mem k).2
    unfold logLogCut logAbsSq; split_ifs with h0 h1'
    · rfl
    · exact absurd (h1'.trans_lt (hy.trans h1)) (lt_irrefl _)
    · exact cutStep_small k h0 (by rwa [abs_of_nonneg (by positivity)])
  · have hw0 : ‖eval y Q‖ ^ 2 ≠ 0 := by positivity
    by_cases hw1 : 1 ≤ ‖eval y Q‖ ^ 2
    · simp [logLogCut, hw0, hw1]
    refine tendsto_const_nhds.congr' ?_
    set L := Real.log (-Real.log (‖eval y Q‖ ^ 2))
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * |L|)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hk' : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
    have h3 : L / ((k : ℝ) + 1) < 1 / 2 := by
      rw [div_lt_iff₀ hk']; linarith [le_abs_self L]
    simp only [logLogCut, logAbsSq, hw0, hw1, if_false]
    exact (Real.smoothTransition.one_of_one_le (by linarith)).symm

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def CutOffGradient.Statement : Prop :=
  ∃ K : ℝ, ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (k : ℕ)
    (y : Fin (d + 1) → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
        (vecCons (logLogCutAlong A P k) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y ∧
    chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
        (vecCons (fun x => logLogCutAlong A P k x ^ 2 / 2) φ) y ≤
      K / ((k : ℝ) + 1) * tubeDens J A P R φ y ∧
    chartAbsDens J A ((Metric.closedBall 0 R).indicator (logLogCutAlong A P k))
        (vecCons (logLogCutAlong A P k) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def CutOffTube.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 → (∀ i, SmoothNear (zeroSet J) (φ i)) → Integrable (tubeDens J A P R φ)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.AnForm

noncomputable section

def LogLogCutHess.Statement : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ), ∃ a b : ℝ,
    |a| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧ |b| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧
    hessC (logLogCut Q k) y = (a : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y ∧
    hessC (fun z => logLogCut Q k z ^ 2 / 2) y = (b : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def TubeCollarCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ C : ℝ, ∀ y, {y | -Real.exp 1 ≤ logAbsSq P y}.indicator (tubeDens J A P R (fun _ => euclPot)) y ≤
        C * chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ))
          (fun _ : Fin (d + 1) => euclPot) y

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def TubeCollarMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      Integrable ({y | -Real.exp 1 ≤ logAbsSq P y}.indicator (tubeDens J A P R (fun _ => euclPot)))

end

end GroundTheory.Heights₂.Heights
end
