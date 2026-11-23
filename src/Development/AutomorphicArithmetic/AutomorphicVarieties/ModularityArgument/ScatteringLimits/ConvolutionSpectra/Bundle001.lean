module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cutSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (s : Set ℝ), MeasurableSet s → ∀ u : L V, ∀ᵐ x : ℝ, cut V s u x = s.indicator u x := by
  intro V _ _ _ _ s hs
  have hm : ∀ u : L V, MemLp (s.indicator (u : ℝ → V)) 2 volume := fun u => (Lp.memLp u).indicator hs.nullMeasurableSet
  let A : L V →ₗ[ℂ] L V :=
    { toFun := fun u => (hm u).toLp _
      map_add' := fun u v => Lp.ext (by
        filter_upwards [(hm (u + v)).coeFn_toLp, (hm u).coeFn_toLp, (hm v).coeFn_toLp, Lp.coeFn_add u v,
          Lp.coeFn_add ((hm u).toLp _) ((hm v).toLp _)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx]; exact h4
        · simp [hx])
      map_smul' := fun c u => Lp.ext (by
        filter_upwards [(hm (c • u)).coeFn_toLp, (hm u).coeFn_toLp, Lp.coeFn_smul c u,
          Lp.coeFn_smul c ((hm u).toLp _)] with x h1 h2 h4 h5
        rw [h1, RingHom.id_apply, h5, Pi.smul_apply, h2]
        by_cases hx : x ∈ s <;> simp [hx, h4]) }
  have hb : ∀ u, ‖A u‖ ≤ 1 * ‖u‖ := fun u => by
    rw [one_mul]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [(hm u).coeFn_toLp] with x h
    show ‖((hm u).toLp _ : ℝ → V) x‖ ≤ _
    rw [h]
    exact norm_indicator_le_norm_self _ _
  exact Classical.epsilon_spec (p := fun C : L V →L[ℂ] L V => ∀ u, ∀ᵐ x : ℝ, C u x = s.indicator u x)
    ⟨A.mkContinuous 1 hb, fun u => (hm u).coeFn_toLp⟩
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.avSpec :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H), (∀ t, ContinuousLinearMap.adjoint (F.U t) = F.U (-t)) ∧ Integrable wR ∧ (∫ t, ‖wR t‖ = 1) ∧ ∀ ψ : ℝ → ℂ, Integrable ψ →
      (∀ h, Integrable (fun t => ψ t • F.U t h) ∧ F.av ψ h = ∫ t, ψ t • F.U t h) ∧ ‖F.av ψ‖ ≤ ∫ t, ‖ψ t‖ ∧
      ContinuousLinearMap.adjoint (F.av ψ) = F.av (fun t => conj (ψ (-t))) ∧ F.rev.av ψ = F.av (fun t => ψ (-t)) ∧
      ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F' : Flow G) (Y : H →L[ℂ] G), (∀ t h, Y (F.U t h) = F'.U t (Y h)) → Y ∘L F.av ψ = F'.av ψ ∘L Y := by
  intro H _ _ _ F
  have hin : ∀ t x y, ⟪F.U t x, F.U t y⟫_ℂ = ⟪x, y⟫_ℂ := fun t x y =>
    (⟨(F.U t : H →ₗ[ℂ] H), F.norm t⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y
  have hadj : ∀ t x y, ⟪F.U t x, y⟫_ℂ = ⟪x, F.U (-t) y⟫_ℂ := fun t x y => by
    rw [← hin t x, ← F.add, add_neg_cancel, F.zero]
  have hw : Integrable wR := by
    refine (integrable_indicator_iff measurableSet_Iic).2 ?_
    exact (integrableOn_exp_Iic 0).ofReal
  have spec : ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F : Flow G) (ψ : ℝ → ℂ), Integrable ψ →
      ∀ h, Integrable (fun t => ψ t • F.U t h) ∧ F.av ψ h = ∫ t, ψ t • F.U t h := by
    intro G _ _ _ F ψ hψ
    have hi : ∀ h, Integrable (fun t => ψ t • F.U t h) := fun h =>
      hψ.smul_bdd ‖h‖ (F.cont h).aestronglyMeasurable (Eventually.of_forall fun t => (F.norm t h).le)
    let A : G →ₗ[ℂ] G :=
      { toFun := fun h => ∫ t, ψ t • F.U t h
        map_add' := fun x y => by simp only [map_add (f := _), smul_add]; exact integral_add (hi x) (hi y)
        map_smul' := fun c x => by simp only [map_smul, RingHom.id_apply, smul_comm _ c]; exact integral_smul c _ }
    have hb : ∀ h, ‖A h‖ ≤ (∫ t, ‖ψ t‖) * ‖h‖ := fun h => by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      simp only [norm_smul, F.norm]
      exact integral_mul_const _ _
    exact fun h => ⟨hi h, Classical.epsilon_spec (p := fun A : G →L[ℂ] G => ∀ h, A h = ∫ t, ψ t • F.U t h)
      ⟨A.mkContinuous _ hb, fun _ => rfl⟩ h⟩
  refine ⟨fun t => ?_, hw, ?_, fun ψ hψ => ⟨spec F ψ hψ, ?_, ?_, ?_, ?_⟩⟩
  · exact ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => by rw [hadj, neg_neg]).symm
  · have : (fun t => ‖wR t‖) = (Iic (0 : ℝ)).indicator Real.exp := by
      funext t
      by_cases h : t ∈ Iic (0 : ℝ) <;> simp [wR, h]
    rw [this, integral_indicator measurableSet_Iic, integral_exp_Iic_zero]
  · refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) fun h => ?_
    rw [(spec F ψ hψ h).2]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp only [norm_smul, F.norm]
    exact integral_mul_const _ _
  · have hψ' : Integrable fun t => conj (ψ (-t)) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hψ.comp_neg
    refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_).symm
    rw [(spec F ψ hψ y).2, (spec F _ hψ' x).2, ← integral_inner (spec F ψ hψ y).1, ← inner_conj_symm,
      ← integral_inner (spec F _ hψ' x).1, ← integral_conj, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [neg_neg, inner_smul_right, map_mul, Complex.conj_conj, inner_conj_symm, hadj]
  · ext h
    rw [(spec F.rev ψ hψ h).2, (spec F _ hψ.comp_neg h).2, ← integral_neg_eq_self]
    simp [Flow.rev]
  · intro G _ _ _ F' Y hY
    ext h
    simp only [ContinuousLinearMap.comp_apply]
    rw [(spec F ψ hψ h).2, (spec F' ψ hψ _).2, ← Y.integral_comp_comm (spec F ψ hψ h).1]
    simp only [map_smul, hY]
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cobLaws :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H), F.Cob 0 ∧ (∀ h h', F.Cob h → F.Cob h' → F.Cob (h + h') ∧ F.Cob (h - h')) ∧ (∀ (c : ℂ) h, F.Cob h → F.Cob (c • h)) ∧
      (∀ h, F.rev.Cob h ↔ F.Cob h) ∧ (∀ s h, F.Cob (h - F.U s h)) ∧ (∀ h, F.Cob h → ∃ C, ∀ t, ‖∫ s in (0 : ℝ)..t, F.U s h‖ ≤ C) ∧
      (F.Null → ∀ h h' (c : ℝ), F.Cob h → Tendsto (fun a => ∫ s in (c - a)..(c + a), ⟪h', F.U s h⟫_ℂ) atTop (𝓝 0)) ∧
      ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F' : Flow G) (Y : H →L[ℂ] G), (∀ t h, Y (F.U t h) = F'.U t (Y h)) → ∀ h, F.Cob h → F'.Cob (Y h) := by
  intro H _ _ _ F
  have ii : ∀ h a b, IntervalIntegrable (fun s => F.U s h) volume a b := fun h a b => (F.cont h).intervalIntegrable a b
  have hs : ∀ (c : ℂ) h, F.Cob h → F.Cob (c • h) := fun c h ⟨k, hk⟩ =>
    ⟨c • k, fun t => by simp only [map_smul]; rw [intervalIntegral.integral_smul, hk, smul_sub]⟩
  have ha : ∀ h h', F.Cob h → F.Cob h' → F.Cob (h + h') := fun h h' ⟨k, hk⟩ ⟨k', hk'⟩ =>
    ⟨k + k', fun t => by simp only [map_add (f := _)]; rw [intervalIntegral.integral_add (ii _ _ _) (ii _ _ _), hk, hk']; abel⟩
  have hr : ∀ (F : Flow H) h, F.Cob h → F.rev.Cob h := fun F h ⟨k, hk⟩ => ⟨-k, fun t => by
    show ∫ s in (0 : ℝ)..t, F.U (-s) h = F.U (-t) (-k) - -k
    rw [intervalIntegral.integral_comp_neg fun s => F.U s h, neg_zero, intervalIntegral.integral_symm, hk, map_neg]; abel⟩
  refine ⟨⟨0, fun t => by simp⟩, fun h h' a b => ⟨ha _ _ a b, ?_⟩, hs, fun h => ⟨fun x => ?_, hr F h⟩, fun s h => ?_,
    fun h ⟨k, hk⟩ => ⟨‖k‖ + ‖k‖, fun t => ?_⟩, fun hn h h' c ⟨k, hk⟩ => ?_, ?_⟩
  · simpa [sub_eq_add_neg] using ha _ _ a (hs (-1) _ b)
  · obtain ⟨k, hk⟩ := hr F.rev h x
    exact ⟨k, fun t => by simpa [Flow.rev] using hk t⟩
  · refine ⟨-∫ r in (0 : ℝ)..s, F.U r h, fun t => ?_⟩
    simp only [map_sub, ← F.add]
    have hc : Continuous fun r => F.U (r + s) h := (F.cont h).comp (continuous_id.add continuous_const)
    rw [intervalIntegral.integral_sub (ii _ _ _) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_comp_add_right fun r => F.U r h, map_neg, ← (F.U t).intervalIntegral_comp_comm (ii _ _ _)]
    simp only [← F.add]
    rw [intervalIntegral.integral_comp_add_left fun r => F.U r h, zero_add, add_zero]
    have e1 := intervalIntegral.integral_add_adjacent_intervals (ii h 0 t) (ii h t (t + s))
    have e2 := intervalIntegral.integral_add_adjacent_intervals (ii h 0 s) (ii h s (t + s))
    rw [eq_sub_of_add_eq e1, ← e2]; abel
  · rw [hk]; exact (norm_sub_le _ _).trans_eq (by rw [F.norm])
  · have e : ∀ a, ∫ s in (c - a)..(c + a), ⟪h', F.U s h⟫_ℂ = ⟪h', F.U (c + a) k⟫_ℂ - ⟪h', F.U (c - a) k⟫_ℂ := fun a => by
      have := (innerSL ℂ h').intervalIntegral_comp_comm (ii h (c - a) (c + a))
      simp only [innerSL_apply_apply] at this
      rw [this, ← intervalIntegral.integral_interval_sub_left (ii h 0 _) (ii h 0 _), hk, hk, ← inner_sub_right]
      congr 1; abel
    simp only [e]
    simpa [sub_eq_add_neg] using ((hn k h').1.comp (tendsto_atTop_add_const_left _ c tendsto_id)).add
      ((hn k h').2.comp (tendsto_atBot_add_const_left _ c tendsto_neg_atTop_atBot)).neg
  · intro G _ _ _ F' Y hY h ⟨k, hk⟩
    exact ⟨Y k, fun t => by simp only [← hY]; rw [Y.intervalIntegral_comp_comm (ii _ _ _), hk, map_sub]⟩
end
