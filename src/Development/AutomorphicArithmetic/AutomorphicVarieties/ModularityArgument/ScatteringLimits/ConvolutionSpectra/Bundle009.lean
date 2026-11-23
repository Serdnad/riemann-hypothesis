module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle007
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle008
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.bandHS :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (φ : ℝ → ℂ) (a b : ℝ), Continuous φ → HasCompactSupport φ → a ≤ b →
      IsHilbertSchmidt (X ∘L M.P (Ioc a b)) ∧ hsNorm (X ∘L M.P (Ioc a b)) ^ 2 = (b - a) * ∑ i, ‖kv κ (stdOrthonormalBasis ℂ V i)‖ ^ 2 ∧
      IsHilbertSchmidt (M.F.av φ ∘L M.P (Ioc a b)) ∧
      hsNorm (M.F.av φ ∘L M.P (Ioc a b)) ^ 2 = (b - a) * (Module.finrank ℂ V * ∫ x, ‖φ x‖ ^ 2) ∧
      trace (ContinuousLinearMap.adjoint (M.F.av φ ∘L M.P (Ioc a b)) ∘L (X ∘L M.P (Ioc a b))) =
        ∫ y in a..b, ∑ i, M.cor (fun x => φ (-x)) (stdOrthonormalBasis ℂ V i) (kv κ (stdOrthonormalBasis ℂ V i)) (2 * y) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX φ a b h1 h2 hab
  have cU : ∀ (F : Flow H) (A : V →L[ℂ] H), Continuous fun y => F.U y ∘L A := fun F A =>
    continuous_clm_apply.2 fun e => F.cont (A e)
  let A : V →L[ℂ] H := (M.J'.toContinuousLinearEquiv : L W →L[ℂ] H) ∘L kv κ
  let A' : V →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L sv V fun x => φ (-x)
  have pa : ∀ u, M.P (Ioc a b) (M.J u) = M.J (cut V (Ioc a b) u) := fun u => congrArg M.J (congrArg _ (M.J.symm_apply_apply u))
  obtain ⟨s1, s2, s3⟩ := scalSpec (V := V) φ h1 h2
  have hi : Integrable φ := h1.integrable_of_hasCompactSupport h2
  have y1 : ∀ u : L V, (X ∘L M.P (Ioc a b)) (M.J u) = ∫ y in Ioc a b, (M.F.U y ∘L A) (u y) := fun u => by
    obtain ⟨i1, i2⟩ := (kvSpec κ hk).2 a b u
    rw [ContinuousLinearMap.comp_apply, pa, hX, i2]
    refine ((M.J'.toContinuousLinearEquiv : L W →L[ℂ] H).integral_comp_comm i1).symm.trans ?_
    exact integral_congr_ae (Eventually.of_forall fun y => (M.hJ' y _).symm)
  have y2 : ∀ u : L V, (M.F.av φ ∘L M.P (Ioc a b)) (M.J u) = ∫ y in Ioc a b, (M.F.rev.U y ∘L A') (u y) := fun u => by
    obtain ⟨i1, i2⟩ := (kvSpec _ s1).2 a b u
    have c := ((avSpec (shF V)).2.2.2 φ hi).2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) fun t h => (M.hJ t h).symm
    have c' : ∀ v, M.F.av φ (M.J v) = M.J ((shF V).av φ v) := fun v => (DFunLike.congr_fun c v).symm
    rw [ContinuousLinearMap.comp_apply, pa, c', s2, i2]
    refine ((M.J.toContinuousLinearEquiv : L V →L[ℂ] H).integral_comp_comm i1).symm.trans ?_
    rw [s3]
    exact integral_congr_ae (Eventually.of_forall fun y => (M.hJ (-y) _).symm)
  obtain ⟨k1, k2, k3⟩ := kp M.J a b _ _ _ _ hab (cU M.F A) (cU M.F.rev A') y1 y2
  obtain ⟨k4, k5, -⟩ := kp M.J a b _ _ _ _ hab (cU M.F.rev A') (cU M.F.rev A') y2 y2
  refine ⟨k1, ?_, k4, ?_, ?_⟩
  · rw [k2]
    simp [M.F.norm, A]
  · rw [k5]
    have m2 : MemLp (fun x => φ (-x)) 2 volume :=
      (h1.comp continuous_neg).memLp_of_hasCompactSupport (h2.comp_homeomorph (Homeomorph.neg ℝ))
    have n : ∀ i, ‖(M.F.rev.U 0 ∘L A') (stdOrthonormalBasis ℂ V i)‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 := fun i => by
      show ‖M.F.rev.U 0 (M.J (sv V (fun x => φ (-x)) (stdOrthonormalBasis ℂ V i)))‖ ^ 2 = _
      rw [Flow.norm, M.J.norm_map, ((svSpec (V := V)).1 _ m2 _).2, (stdOrthonormalBasis ℂ V).orthonormal.1,
        integral_neg_eq_self fun x => ‖φ x‖ ^ 2]
      simp
    simp only [ContinuousLinearMap.comp_apply, Flow.norm] at n ⊢
    simp [n, mul_left_comm]
  · rw [k3]
    refine intervalIntegral.integral_congr fun y _ => Finset.sum_congr rfl fun i _ => ?_
    show ⟪M.F.U (-y) (M.J _), M.F.U y (M.J' _)⟫_ℂ = ⟪M.J _, M.F.U (2 * y) (M.J' _)⟫_ℂ
    rw [← (avSpec M.F).1, ContinuousLinearMap.adjoint_inner_left, ← M.F.add, two_mul]
    rfl
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nIso :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W), (∀ e, M.F.Cob (M.J (one V e)) → e = 0) ∧ ∀ N, M.IsN N → ∀ w, ‖N w‖ = ‖w‖ := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M
  obtain ⟨g, hg, g1, g2⟩ := grow (V := V) (W := W)
  have hb := (cobLaws M.F).2.2.2.2.2.1
  have e1 : ∀ (e : V) t, ‖∫ s in (0 : ℝ)..t, M.F.U s (M.J (one V e))‖ = g t * ‖e‖ := fun e t => by
    simp only [M.hJ]
    rw [← g1, ← M.J.norm_map]
    exact congrArg _ ((M.J.toContinuousLinearEquiv : L V →L[ℂ] H).intervalIntegral_comp_comm
      (((shF V).cont _).intervalIntegrable _ _))
  have e2 : ∀ (f : W) t, ‖∫ s in (0 : ℝ)..t, M.F.U s (M.J' (one W f))‖ = g t * ‖f‖ := fun f t => by
    simp only [M.hJ']
    rw [← g2, ← M.J'.norm_map]
    exact congrArg _ ((M.J'.toContinuousLinearEquiv : L W →L[ℂ] H).intervalIntegral_comp_comm
      (((shF W).rev.cont _).intervalIntegrable _ _))
  have key : ∀ d C : ℝ, (∀ t, |g t * d| ≤ C) → d = 0 := fun d C h => by
    by_contra hd
    have h1 : Tendsto (fun t => |g t| * |d|) atTop atTop := (tendsto_abs_atTop_atTop.comp hg).atTop_mul_const (abs_pos.2 hd)
    obtain ⟨t, ht⟩ := (h1.eventually_gt_atTop C).exists
    exact absurd (abs_mul (g t) d ▸ h t) (not_le.2 ht)
  refine ⟨fun e he => ?_, fun N hN w => ?_⟩
  · obtain ⟨C, hC⟩ := hb _ he
    exact norm_eq_zero.1 (key _ C fun t => by rw [← e1, abs_norm]; exact hC t)
  · obtain ⟨C, hC⟩ := hb _ (hN w)
    refine (sub_eq_zero.1 (key (‖w‖ - ‖N w‖) C fun t => ?_)).symm
    rw [mul_sub, ← e1, ← e2]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← intervalIntegral.integral_sub ((M.F.cont _).intervalIntegrable _ _) ((M.F.cont _).intervalIntegrable _ _)]
    simpa only [map_sub] using hC t
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nAll :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W →ₗ[ℂ] V), M.IsN N → ∀ p : L W, Bdd p → M.F.Cob (M.J' p - M.J (one V (N (∫ x, p x)))) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN p hp
  obtain ⟨h1, h2⟩ := cobTail p
  have h3 := (h2 (h1 hp)).2
  have h4 := (cobLaws (shF W)).2.2.2.2.2.2.2 M.F.rev (M.J'.toContinuousLinearEquiv : L W →L[ℂ] H) (fun t h => by
    show M.J' (sh W t h) = M.F.U (-t) (M.J' h)
    rw [M.hJ', neg_neg]) _ h3
  have h5 := ((cobLaws M.F).2.2.2.1 _).1 h4
  have h6 := ((cobLaws M.F).2.1 _ _ h5 (hN (∫ x, p x))).1
  convert h6 using 1
  simp
end
