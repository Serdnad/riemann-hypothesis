module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.resTail :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (k : L V) (T : ℝ), cut V (Iic T) k = k → Tail (cut V (Ioi T) ((shF V).av wR k)) := by
  intro V _ _ _ _ k T hk
  obtain ⟨-, w1, w2, w3⟩ := avSpec (shF V)
  obtain ⟨a1, a2, -⟩ := w3 wR w1
  have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
  refine ⟨Real.exp |T| * ‖k‖, fun ρ hρ => ?_⟩
  have e := DFunLike.congr_fun (cl (Icc (-ρ) ρ)ᶜ (Ioi T) measurableSet_Icc.compl measurableSet_Ioi).1 ((shF V).av wR k)
  rw [ContinuousLinearMap.comp_apply] at e
  rw [e]
  by_cases h : |T| ≤ ρ
  · have e2 : (Icc (-ρ) ρ)ᶜ ∩ Ioi T = Ioi ρ := by
      ext x
      have := abs_le.1 h
      simp only [mem_inter_iff, mem_compl_iff, mem_Icc, mem_Ioi, not_and_or, not_le]
      constructor
      · rintro ⟨h1 | h1, h2⟩ <;> linarith
      · exact fun h1 => ⟨Or.inr h1, by linarith⟩
    rw [e2, (a1 k).2]
    erw [← (cut V (Ioi ρ)).integral_comp_comm (a1 k).1]
    have ib : Integrable fun t => (Iic (T - ρ)).indicator Real.exp t * ‖k‖ :=
      ((integrable_indicator_iff measurableSet_Iic).2 (integrableOn_exp_Iic _)).mul_const _
    refine (norm_integral_le_of_norm_le ib (Eventually.of_forall fun t => ?_)).trans ?_
    · rw [map_smul, norm_smul]
      by_cases ht : t ≤ T - ρ
      · rw [indicator_of_mem (mem_Iic.2 ht)]
        refine mul_le_mul ?_ (((cl _ univ measurableSet_Ioi .univ).2.2.2.2.2.1 _).trans_eq ((shF V).norm t k)) (norm_nonneg _)
          (Real.exp_pos _).le
        refine (norm_indicator_le_norm_self _ _).trans_eq ?_
        simp
      · have h1 := DFunLike.congr_fun ((cl (Ioi (ρ + t)) univ measurableSet_Ioi .univ).2.2.2.2.2.2.1 t) k
        simp only [ContinuousLinearMap.comp_apply, preimage_add_const_Ioi, add_sub_cancel_right] at h1
        have h2 := DFunLike.congr_fun (cl (Ioi (ρ + t)) (Iic T) measurableSet_Ioi measurableSet_Iic).1 k
        rw [ContinuousLinearMap.comp_apply, hk, Ioi_inter_Iic, Ioc_eq_empty (by linarith [not_le.1 ht]),
          (cl univ univ .univ .univ).2.2.2.2.1] at h2
        have h3 : cut V (Ioi ρ) ((shF V).U t k) = 0 := by
          show cut V (Ioi ρ) (sh V t k) = 0
          rw [← h1, h2]; simp
        rw [h3, indicator_of_notMem (by simpa using ht)]; simp
    · rw [integral_mul_const, integral_indicator measurableSet_Iic, integral_exp_Iic, mul_right_comm, ← Real.exp_add]
      gcongr
      linarith [le_abs_self T]
  · refine ((cl _ univ (measurableSet_Icc.compl.inter measurableSet_Ioi) .univ).2.2.2.2.2.1 _).trans ?_
    refine (((shF V).av wR).le_of_opNorm_le (a2.trans_eq w2) k).trans ?_
    rw [mul_right_comm, ← Real.exp_add]
    gcongr
    exact Real.one_le_exp (by linarith [not_le.1 h])
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem ker_bd {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {κ : ℝ → V →L[ℂ] W} (h : HasCompactSupport κ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R < |t| → κ t = 0 := by
  obtain ⟨R, hR⟩ := h.isCompact.isBounded.exists_norm_le
  refine ⟨|R|, abs_nonneg _, fun t ht => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
  exact absurd ((hR t hm).trans (le_abs_self R)) (not_le.2 ht)

theorem UpperTheory.V.Z.IntegralApplyAeEq.convLaws :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → (∀ a : ℝ, conv κ ∘L sh V a = sh W a ∘L conv κ) ∧
      (∀ ρ T : ℝ, (∀ t, ρ < |t| → κ t = 0) → cut W (Ioi (T + ρ)) ∘L conv κ ∘L cut V (Iic T) = 0) ∧
      ∀ p : L V, Bdd p → Bdd (conv κ p) ∧ ∫ x, conv κ p x = symb κ 0 (∫ x, p x) := by
  intro V _ _ _ _ W _ _ _ _ κ hk
  have q : ∀ x : ℝ, Measure.QuasiMeasurePreserving (fun t : ℝ => x + t) volume volume :=
    fun x => (measurePreserving_add_left volume x).quasiMeasurePreserving
  refine ⟨fun a => ?_, fun ρ T hρ => ?_, fun p ⟨ρ, hp⟩ => ?_⟩
  · ext1 u
    refine Lp.ext ?_
    filter_upwards [(convSpec κ hk (sh V a u)).1, sh_ae W a (conv κ u),
      (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (convSpec κ hk u).1] with x h1 h2 h3
    simp only [ContinuousLinearMap.comp_apply]
    rw [h1, h2, h3]
    refine integral_congr_ae ?_
    filter_upwards [Measure.QuasiMeasurePreserving.ae (q x) (sh_ae V a u)] with t ht
    rw [ht, add_right_comm]
  · ext1 u
    have c1 := (cutLaws (V := W) (Iic (T + ρ)) (Ioi (T + ρ)) measurableSet_Iic measurableSet_Ioi).2.2.2.2.2.2.2.1
    have c2 := cutLaws (V := W) (Ioi (T + ρ)) (Iic (T + ρ)) measurableSet_Ioi measurableSet_Iic
    have c3 := cutLaws (V := V) (Iic T) (Iic T) measurableSet_Iic measurableSet_Iic
    have h0 := (c3.2.2.2.2.2.2.2.1 (cut V (Iic T) u)).1 (by
      have := DFunLike.congr_fun c3.1 u
      rwa [inter_self] at this)
    have h1 : cut W (Iic (T + ρ)) (conv κ (cut V (Iic T) u)) = conv κ (cut V (Iic T) u) := by
      refine (c1 _).2 ?_
      filter_upwards [(convSpec κ hk (cut V (Iic T) u)).1] with x hx hx'
      rw [hx]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [Measure.QuasiMeasurePreserving.ae (q x) h0] with t ht
      by_cases h : ρ < |t|
      · simp [hρ t h]
      · have h2 := (abs_le.1 (not_lt.1 h)).1
        rw [ht (by simp only [mem_Iic, not_le] at hx' ⊢; linarith), map_zero]; rfl
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
    rw [← h1]
    have := DFunLike.congr_fun c2.1 (conv κ (cut V (Iic T) u))
    rw [Ioi_inter_Iic, Ioc_self, c2.2.2.2.2.1] at this
    exact this
  · obtain ⟨R, -, hR⟩ := ker_bd hk.2
    have h0 := ((cutLaws (V := V) (Icc (-ρ) ρ) univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 p).1 hp
    have hpi : Integrable (p : ℝ → V) := by
      have h1 : IntegrableOn (p : ℝ → V) (Icc (-ρ) ρ) := integrableOn_Lp_of_measure_ne_top p (by norm_num) measure_Icc_lt_top.ne
      refine ((integrable_indicator_iff measurableSet_Icc).2 h1).congr ?_
      filter_upwards [h0] with x hx
      by_cases h : x ∈ Icc (-ρ) ρ
      · rw [indicator_of_mem h]
      · rw [indicator_of_notMem h, hx h]
    refine ⟨⟨ρ + R, ((cutLaws (V := W) (Icc (-(ρ + R)) (ρ + R)) univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 _).2 ?_⟩, ?_⟩
    · filter_upwards [(convSpec κ hk p).1] with x hx hx'
      rw [hx]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [Measure.QuasiMeasurePreserving.ae (q x) h0] with t ht
      by_cases h : R < |t|
      · simp [hR t h]
      · obtain ⟨h2, h3⟩ := abs_le.1 (not_lt.1 h)
        rw [ht fun hm => hx' ⟨by linarith [hm.1], by linarith [hm.2]⟩, map_zero]; rfl
    · have hk1 : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
      have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => κ z.1 ((p : ℝ → V) (z.2 + z.1))) (volume.prod volume) :=
        (ContinuousLinearMap.apply ℂ W).flip.aestronglyMeasurable_comp₂ (hk.1.comp continuous_fst).aestronglyMeasurable
          ((Lp.stronglyMeasurable p).comp_measurable (measurable_snd.add measurable_fst)).aestronglyMeasurable
      have hI : Integrable (fun z : ℝ × ℝ => κ z.1 ((p : ℝ → V) (z.2 + z.1))) (volume.prod volume) := by
        refine (integrable_prod_iff hm).2 ⟨Eventually.of_forall fun t => (κ t).integrable_comp (hpi.comp_add_right t), ?_⟩
        refine (hk1.norm.mul_const (∫ x, ‖p x‖)).mono' hm.norm.integral_prod_right' (Eventually.of_forall fun t => ?_)
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← integral_add_right_eq_self (fun x => ‖p x‖) t,
          ← integral_const_mul]
        exact integral_mono ((κ t).integrable_comp (hpi.comp_add_right t)).norm ((hpi.comp_add_right t).norm.const_mul _)
          fun x => (κ t).le_opNorm _
      rw [integral_congr_ae (convSpec κ hk p).1, ← integral_integral_swap (f := fun t x => κ t ((p : ℝ → V) (x + t))) hI, symb]
      simp only [zero_mul, Complex.exp_zero, one_smul]
      rw [ContinuousLinearMap.integral_apply hk1]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      rw [(κ t).integral_comp_comm (hpi.comp_add_right t), integral_add_right_eq_self]
end
