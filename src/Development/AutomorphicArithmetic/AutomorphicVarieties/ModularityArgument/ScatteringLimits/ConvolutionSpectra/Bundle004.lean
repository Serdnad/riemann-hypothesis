module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle001
public import Mathlib.Analysis.Fourier.LpSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Fourier.Convolution
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.resCob :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H) (k : H), F.Cob (k - F.av wR k) ∧
      ∫ t in Iic (0 : ℝ), Real.exp t * ‖F.U t k - k‖ ^ 2 = 2 * ‖k‖ ^ 2 - 2 * (⟪k, F.av wR k⟫_ℂ).re := by
  intro H _ _ _ F k
  have hw := (avSpec F).2.1
  have sp := fun h => ((avSpec F).2.2.2 _ hw).1 h
  have cg : Continuous fun r : ℝ => (Real.exp r : ℂ) • F.U r k := by
    have := F.cont k
    fun_prop
  have ig : ∀ t, IntegrableOn (fun r : ℝ => (Real.exp r : ℂ) • F.U r k) (Iic t) := fun t =>
    Integrable.mono' ((integrableOn_exp_Iic t).mul_const ‖k‖) cg.aestronglyMeasurable
      (Eventually.of_forall fun r => by simp [norm_smul, F.norm])
  have R0 : ∀ h, F.av wR h = ∫ r in Iic (0 : ℝ), (Real.exp r : ℂ) • F.U r h := fun h => by
    rw [(sp h).2, ← integral_indicator measurableSet_Iic]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Iic (0 : ℝ) <;> simp [wR, hr]
  constructor
  · set c := F.av wR k with hc
    have Ut : ∀ t, F.U t c = (Real.exp (-t) : ℂ) • (c + ∫ r in (0 : ℝ)..t, (Real.exp r : ℂ) • F.U r k) := fun t => by
      rw [hc, R0, ← intervalIntegral.integral_Iic_sub_Iic (ig 0) (ig t), add_sub_cancel,
        ← (F.U t).integral_comp_comm (ig 0), ← integral_smul, ← integral_indicator measurableSet_Iic,
        ← integral_indicator measurableSet_Iic, ← integral_add_right_eq_self _ (-t)]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      by_cases hr : r ≤ t
      · simp only [indicator_of_mem (show r + -t ∈ Iic (0 : ℝ) by simpa using hr), indicator_of_mem (show r ∈ Iic t from hr),
          map_smul, ← F.add, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
        congr 3 <;> ring
      · simp only [indicator_of_notMem (show r + -t ∉ Iic (0 : ℝ) by simpa using hr), indicator_of_notMem (show r ∉ Iic t from hr)]
    have der : ∀ t, HasDerivAt (fun t => F.U t c) (F.U t (k - c)) t := fun t => by
      have d1 : HasDerivAt (fun t : ℝ => (Real.exp (-t) : ℂ)) (-(Real.exp (-t) : ℂ)) t := by
        simpa using ((hasDerivAt_neg t).exp).ofReal_comp
      have d2 := (cg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add c
      have d3 := d1.smul d2
      refine (d3.congr_of_eventuallyEq (Eventually.of_forall Ut)).congr_deriv ?_
      symm
      rw [map_sub, Ut, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one,
        one_smul, neg_smul, sub_eq_add_neg]
    refine ⟨c, fun t => ?_⟩
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => der s) ((F.cont _).intervalIntegrable _ _), F.zero]
  · have i1 : IntegrableOn (fun r : ℝ => ⟪k, (Real.exp r : ℂ) • F.U r k⟫_ℂ) (Iic 0) := (ig 0).const_inner k
    rw [R0, ← integral_inner (ig 0), ← RCLike.re_to_complex, ← integral_re i1, ← integral_const_mul]
    have e : 2 * ‖k‖ ^ 2 = ∫ t in Iic (0 : ℝ), Real.exp t * (2 * ‖k‖ ^ 2) := by
      rw [integral_mul_const, integral_exp_Iic_zero, one_mul]
    rw [e, ← integral_sub ((integrableOn_exp_Iic 0).mul_const _) (i1.re.const_mul 2)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [norm_sub_rev (F.U t k) k, @norm_sub_sq ℂ, F.norm, inner_smul_right, RCLike.re_to_complex, Complex.re_ofReal_mul]
    ring
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.avApprox :
    (∀ a b : ℝ, a < b → ∃ ψ, Bump ψ a b) ∧ (∀ ψ a b, Bump ψ a b → HasCompactSupport ψ ∧ Integrable (fun t => (ψ t : ℂ)) ∧ ∫ t, ψ t ^ 2 ≤ 2 / (b - a)) ∧
      ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H) (h : H) (ε : ℝ), 0 < ε → ∃ δ > 0, ∀ ψ a b, Bump ψ a b → -δ ≤ a → b ≤ δ → ‖F.av (fun t => (ψ t : ℂ)) h - h‖ ≤ ε := by
  have two : ∀ ψ a b, Bump ψ a b → HasCompactSupport ψ ∧ Integrable (fun t => (ψ t : ℂ)) ∧ ∫ t, ψ t ^ 2 ≤ 2 / (b - a) := by
    intro ψ a b h
    have hs : HasCompactSupport ψ := HasCompactSupport.intro isCompact_Icc h.supp
    have hi : Integrable ψ := h.cont.integrable_of_hasCompactSupport hs
    refine ⟨hs, hi.ofReal, ?_⟩
    have : ∫ t, ψ t ^ 2 ≤ ∫ t, 2 / (b - a) * ψ t :=
      integral_mono_of_nonneg (Eventually.of_forall fun t => sq_nonneg _) (hi.const_mul _)
        (Eventually.of_forall fun t => by show ψ t ^ 2 ≤ _; rw [sq]; exact mul_le_mul_of_nonneg_right (h.le t) (h.nonneg t))
    rwa [integral_const_mul, h.total, mul_one] at this
  refine ⟨fun a b hab => ?_, two, ?_⟩
  · have hd : 0 < b - a := sub_pos.2 hab
    let f : ℝ → ℝ := fun t => 6 / (b - a) ^ 3 * max 0 ((t - a) * (b - t))
    have hsupp : ∀ t, t ∉ Icc a b → f t = 0 := fun t ht => by
      have : (t - a) * (b - t) ≤ 0 := by
        rcases not_and_or.1 ht with h | h <;> push Not at h <;> nlinarith
      simp [f, max_eq_left this]
    refine ⟨f, by fun_prop, fun t => by positivity, fun t => ?_, hsupp, ?_⟩
    · have : max 0 ((t - a) * (b - t)) ≤ (b - a) ^ 2 / 4 := max_le (by positivity) (by nlinarith [sq_nonneg (a + b - 2 * t)])
      calc f t ≤ 6 / (b - a) ^ 3 * ((b - a) ^ 2 / 4) := by simp only [f]; gcongr
        _ = 3 / 2 / (b - a) := by field_simp; norm_num
        _ ≤ 2 / (b - a) := by gcongr; norm_num
    · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab.le]
      have : ∫ t in a..b, f t = ∫ t in a..b, 6 / (b - a) ^ 3 * (-t ^ 2 + (a + b) * t - a * b) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hab.le] at ht
        simp only [f]
        rw [max_eq_right (mul_nonneg (sub_nonneg.2 ht.1) (sub_nonneg.2 ht.2))]; ring
      rw [this, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub, intervalIntegral.integral_add,
        intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, integral_pow, integral_id, intervalIntegral.integral_const]
      · simp only [smul_eq_mul]; field_simp; ring
      all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro H _ _ _ F h ε hε
    obtain ⟨δ, hδ, H1⟩ := Metric.continuousAt_iff.1 ((F.cont h).continuousAt (x := 0)) ε hε
    refine ⟨δ / 2, by positivity, fun ψ a b hψ ha hb => ?_⟩
    obtain ⟨hs, hi, -⟩ := two ψ a b hψ
    obtain ⟨i, e⟩ := ((avSpec F).2.2.2 _ hi).1 h
    have hr : Integrable ψ := hψ.cont.integrable_of_hasCompactSupport hs
    have e2 : h = ∫ t, (ψ t : ℂ) • h := by rw [integral_smul_const, integral_complex_ofReal, hψ.total]; simp
    rw [e]
    conv_lhs => rw [show (∫ t, (ψ t : ℂ) • F.U t h) - h = (∫ t, (ψ t : ℂ) • F.U t h) - ∫ t, (ψ t : ℂ) • h from congrArg _ e2]
    rw [← integral_sub i (hi.smul_const h)]
    refine (norm_integral_le_of_norm_le (hr.mul_const ε) (Eventually.of_forall fun t => ?_)).trans_eq
      (by rw [integral_mul_const, hψ.total, one_mul])
    rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hψ.nonneg t)]
    by_cases ht : t ∈ Icc a b
    · have := H1 (x := t) (by rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [ht.1, ht.2])
      rw [F.zero, dist_eq_norm] at this
      exact mul_le_mul_of_nonneg_left this.le (hψ.nonneg t)
    · simp [hψ.supp t ht]
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem ker_bd {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {κ : ℝ → V →L[ℂ] W} (h : HasCompactSupport κ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R < |t| → κ t = 0 := by
  obtain ⟨R, hR⟩ := h.isCompact.isBounded.exists_norm_le
  refine ⟨|R|, abs_nonneg _, fun t ht => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
  exact absurd ((hR t hm).trans (le_abs_self R)) (not_le.2 ht)

theorem UpperTheory.V.Z.IntegralApplyAeEq.convNear :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (β : ℝ → V →L[ℂ] V), Ker β → ∃ C : ℝ, ∀ u : L V,
      ‖conv β u - (symb β 0).compLpL 2 volume u‖ ^ 2 ≤ C * ∫ t in Iic (0 : ℝ), Real.exp t * ‖sh V t u - u‖ ^ 2 := by
  intro V _ _ _ _ β hk
  obtain ⟨R, hR0, hR⟩ := ker_bd hk.2
  have hk1 : Integrable β := hk.1.integrable_of_hasCompactSupport hk.2
  obtain ⟨B, hB⟩ := hk.1.bounded_above_of_compact_support hk.2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let c : (V →L[ℂ] V) →L[ℂ] (L V →L[ℂ] L V) := LinearMap.mkContinuous
    { toFun := fun A => A.compLpL 2 volume
      map_add' := fun A B => ContinuousLinearMap.add_compLpL A B
      map_smul' := fun a A => ContinuousLinearMap.smul_compLpL a A } 1 fun A => by
      rw [one_mul]; exact ContinuousLinearMap.norm_compLpL_le A
  refine ⟨(2 * B) ^ 2 * (R * Real.exp R), fun u => ?_⟩
  set d : ℝ → ℝ := fun t => ‖sh V t u - u‖ with hd
  have dc : Continuous d := (((shF V).cont u).sub continuous_const).norm
  have dn : ∀ t, d (-t) = d t := fun t => by
    show ‖(shF V).U (-t) u - u‖ = ‖(shF V).U t u - u‖
    rw [← (shF V).norm t, map_sub, ← (shF V).add, add_neg_cancel, (shF V).zero, norm_sub_rev]
  have d2 : ∀ t, d t ≤ 2 * ‖u‖ := fun t => (norm_sub_le _ _).trans_eq (by
    rw [show ‖sh V t u‖ = ‖u‖ from (shF V).norm t u]; ring)
  have i2 : Integrable fun t => c (β t) u := (c.integrable_comp hk1).apply_continuousLinearMap u
  have e1 : (symb β 0).compLpL 2 volume u = ∫ t, c (β t) u := by
    rw [symb]
    simp only [zero_mul, Complex.exp_zero, one_smul]
    rw [← ContinuousLinearMap.integral_apply (c.integrable_comp hk1), c.integral_comp_comm hk1]
    rfl
  have e2 : ‖conv β u - (symb β 0).compLpL 2 volume u‖ ≤ 2 * B * ∫ t in (-R)..0, d t := by
    rw [(convSpec β hk u).2.2, e1, ← integral_sub (convSpec β hk u).2.1 i2]
    have hb : Integrable ((Icc (-R) R).indicator fun t => B * d t) :=
      (integrable_indicator_iff measurableSet_Icc).2 ((dc.const_mul B).integrableOn_Icc)
    refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun t => ?_)).trans_eq ?_
    · by_cases h : t ∈ Icc (-R) R
      · rw [indicator_of_mem h]
        show ‖c (β t) (sh V t u) - c (β t) u‖ ≤ _
        rw [← map_sub]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        gcongr
        exact (ContinuousLinearMap.norm_compLpL_le _).trans (hB t)
      · rw [indicator_of_notMem h]
        show ‖c (β t) (sh V t u) - c (β t) u‖ ≤ _
        rw [hR t (not_le.1 fun h' => h (abs_le.1 h')), map_zero]
        simp
    · rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add_adjacent_intervals (dc.intervalIntegrable (-R) 0) (dc.intervalIntegrable 0 R)]
      have : ∫ t in (0 : ℝ)..R, d t = ∫ t in (-R)..0, d t := by
        rw [← neg_zero, ← intervalIntegral.integral_comp_neg, neg_zero]
        simp only [dn]
      rw [this]; ring
  have e3 : (∫ t in (-R)..0, d t) ^ 2 ≤ R * ∫ t in (-R)..0, d t ^ 2 := by
    set m := ∫ t in (-R)..0, d t with hm
    rcases hR0.eq_or_lt with rfl | hp
    · simp [hm]
    have h0 : 0 ≤ ∫ t in (-R)..0, (R * d t - m) ^ 2 := intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
    have h1 : ∫ t in (-R)..0, (R * d t - m) ^ 2 = R ^ 2 * (∫ t in (-R)..0, d t ^ 2) - 2 * R * m * m + R * m ^ 2 := by
      have : ∀ t, (R * d t - m) ^ 2 = R ^ 2 * d t ^ 2 - 2 * R * m * d t + m ^ 2 := fun t => by ring
      simp only [this]
      rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      · simp [hm]
      all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
    rw [h1] at h0
    nlinarith
  have iw : IntegrableOn (fun t => Real.exp t * d t ^ 2) (Iic 0) := by
    refine ((integrableOn_exp_Iic 0).mul_const ((2 * ‖u‖) ^ 2)).mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
    exact d2 t
  have e4 : ∫ t in (-R)..0, d t ^ 2 ≤ Real.exp R * ∫ t in Iic (0 : ℝ), Real.exp t * d t ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_const_mul]
    refine (setIntegral_mono_on (g := fun t => Real.exp R * (Real.exp t * d t ^ 2)) (dc.pow 2).integrableOn_Ioc
      (Continuous.integrableOn_Ioc (by fun_prop)) measurableSet_Ioc fun t ht => ?_).trans
      (setIntegral_mono_set (iw.const_mul _) (Eventually.of_forall fun t => by positivity) (Eventually.of_forall fun _ ht => Ioc_subset_Iic_self ht))
    rw [← mul_assoc, ← Real.exp_add]
    exact le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_exp (by linarith [ht.1]))
  calc _ ≤ (2 * B * ∫ t in (-R)..0, d t) ^ 2 := by gcongr
    _ = (2 * B) ^ 2 * (∫ t in (-R)..0, d t) ^ 2 := by ring
    _ ≤ (2 * B) ^ 2 * (R * (Real.exp R * ∫ t in Iic (0 : ℝ), Real.exp t * d t ^ 2)) := by
      gcongr
      exact e3.trans (by gcongr)
    _ = _ := by ring
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.fourConv :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → ∀ u : L V, ∀ᵐ ξ : ℝ,
      Lp.fourierTransformₗᵢ ℝ W (conv κ u) ξ = symb κ (2 * Real.pi * Complex.I * ξ) (Lp.fourierTransformₗᵢ ℝ V u ξ) := by
  intro V _ _ _ _ W _ _ _ _ κ hk u
  have ki : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
  let σ : ℝ → V →L[ℂ] W := fun ξ => symb κ (2 * Real.pi * Complex.I * ξ)
  have hσ : ∀ ξ, σ ξ = 𝓕 (fun t => κ (-t)) ξ := fun ξ => by
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [neg_neg]
    congr 2
    push_cast; ring
  have σc : Continuous σ := by
    rw [show σ = _ from funext hσ]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ ki.comp_neg
  have σb : ∀ ξ, ‖σ ξ‖ ≤ ∫ t, ‖κ (-t)‖ := fun ξ => by
    rw [hσ]; exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  set C := ∫ t, ‖κ (-t)‖
  have hm : ∀ v : L V, MemLp (fun ξ => σ ξ (v ξ)) 2 volume := fun v =>
    (Lp.memLp v).of_le_mul (c := C)
      ((ContinuousLinearMap.id ℂ (V →L[ℂ] W)).aestronglyMeasurable_comp₂ σc.aestronglyMeasurable (Lp.aestronglyMeasurable v))
      (Eventually.of_forall fun ξ => (σ ξ).le_of_opNorm_le (σb ξ) _)
  let T : L V → L W := fun v => (hm v).toLp _
  have Tc : Continuous T := by
    refine (LipschitzWith.of_dist_le' (K := C) fun v v' => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm]
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub (T v) (T v'), Lp.coeFn_sub v v', (hm v).coeFn_toLp, (hm v').coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, ← map_sub]
    exact (σ x).le_of_opNorm_le (σb x) _
  have key : Lp.fourierTransformₗᵢ ℝ W (conv κ u) = T (Lp.fourierTransformₗᵢ ℝ V u) := by
    refine DenseRange.induction_on (p := fun u : L V => Lp.fourierTransformₗᵢ ℝ W (conv κ u) = T (Lp.fourierTransformₗᵢ ℝ V u))
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := V) (p := 2) (μ := volume) ENNReal.ofNat_ne_top) u
      (isClosed_eq ((Lp.fourierTransformₗᵢ ℝ W).continuous.comp (conv κ).continuous)
        (Tc.comp (Lp.fourierTransformₗᵢ ℝ V).continuous)) fun f => ?_
    set w : L V := SchwartzMap.toLpCLM ℝ V 2 volume f
    have wi : Integrable (w : ℝ → V) := f.integrable.congr (f.coeFn_toLp 2 volume).symm
    have e : (conv κ w : ℝ → W) =ᵐ[volume] convolution (fun t => κ (-t)) w (ContinuousLinearMap.id ℂ (V →L[ℂ] W)) volume := by
      filter_upwards [(convSpec κ hk w).1] with x hx
      rw [hx, convolution_def, ← integral_neg_eq_self]
      simp [sub_eq_add_neg]
    have ci : Integrable (conv κ w : ℝ → W) := (ki.comp_neg.integrable_convolution _ wi).congr e.symm
    refine Lp.ext ?_
    filter_upwards [fourAe _ ci, fourAe _ wi, (hm (Lp.fourierTransformₗᵢ ℝ V w)).coeFn_toLp] with ξ h1 h2 h3
    rw [h1, h3, h2, Real.fourier_congr_ae e, Real.fourier_bilin_convolution_eq _ ki.comp_neg wi, hσ]
    rfl
  rw [key]
  exact (hm _).coeFn_toLp
end
