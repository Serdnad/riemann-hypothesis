module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.AeIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem ker_bd {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {κ : ℝ → V →L[ℂ] W} (h : HasCompactSupport κ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R < |t| → κ t = 0 := by
  obtain ⟨R, hR⟩ := h.isCompact.isBounded.exists_norm_le
  refine ⟨|R|, abs_nonneg _, fun t ht => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
  exact absurd ((hR t hm).trans (le_abs_self R)) (not_le.2 ht)

private theorem meas {V Z : Type} [NormedAddCommGroup V] [NormedAddCommGroup Z] {μ : Measure ℝ} (G : ℝ → V → Z)
    (hG : Continuous fun z : ℝ × V => G z.1 z.2) (u : ℝ → V) (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun y => G y (u y)) μ :=
  hG.comp_aestronglyMeasurable (f := fun y => (y, u y)) (aestronglyMeasurable_id.prodMk hu)

private theorem joint {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (k : V →L[ℂ] L W) : Continuous fun z : ℝ × V => sh W (-z.1) (k z.2) :=
  Continuous.compMeasurePreservingLp (f := fun z : ℝ × V => k z.2)
    (g := fun z : ℝ × V => (⟨fun x => x + -z.1, by fun_prop⟩ : C(ℝ, ℝ))) (k.continuous.comp continuous_snd)
    (ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.add (continuous_fst.comp continuous_fst).neg))
    (fun z => measurePreserving_add_right volume (-z.1)) (by simp)

theorem UpperTheory.V.Z.IntegralApplyAeEq.kvSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → (∀ e, (∀ᵐ x : ℝ, kv κ e x = κ (-x) e) ∧ Bdd (kv κ e) ∧ ∫ x, kv κ e x = symb κ 0 e) ∧
      ∀ (a b : ℝ) (u : L V), IntegrableOn (fun y => sh W (-y) (kv κ (u y))) (Ioc a b) ∧
        conv κ (cut V (Ioc a b) u) = ∫ y in Ioc a b, sh W (-y) (kv κ (u y)) := by
  intro V _ _ _ _ W _ _ _ _ κ hk
  have hc : ∀ e : V, Continuous fun x : ℝ => κ (-x) e := fun e => (hk.1.comp continuous_neg).clm_apply continuous_const
  have hs : ∀ e : V, HasCompactSupport fun x : ℝ => κ (-x) e := fun e =>
    (hk.2.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun A : V →L[ℂ] W => A e) rfl
  have hm : ∀ e : V, MemLp (fun x : ℝ => κ (-x) e) 2 volume := fun e => (hc e).memLp_of_hasCompactSupport (hs e)
  let A : V →ₗ[ℂ] L W :=
    { toFun := fun e => (hm e).toLp _
      map_add' := fun e f => by rw [← MemLp.toLp_add]; congr 1; funext x; simp
      map_smul' := fun c e => by rw [RingHom.id_apply, ← MemLp.toLp_const_smul]; congr 1; funext x; simp }
  have sp := Classical.epsilon_spec (p := fun C : V →L[ℂ] L W => ∀ e, ∀ᵐ x : ℝ, C e x = κ (-x) e)
    ⟨LinearMap.toContinuousLinearMap A, fun e => (hm e).coeFn_toLp⟩
  change ∀ e, ∀ᵐ x : ℝ, kv κ e x = κ (-x) e at sp
  obtain ⟨R, -, hR⟩ := ker_bd hk.2
  have hk1 : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
  refine ⟨fun e => ⟨sp e, ⟨R, ((cutLaws (V := W) (Icc (-R) R) univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 _).2 ?_⟩, ?_⟩,
    fun a b u => ?_⟩
  · filter_upwards [sp e] with x hx hx'
    rw [hx, hR _ (by rw [abs_neg]; exact not_le.1 fun h => hx' (abs_le.1 h)), ContinuousLinearMap.zero_apply]
  · rw [integral_congr_ae (sp e), integral_neg_eq_self (fun x => κ x e), symb]
    simp only [zero_mul, Complex.exp_zero, one_smul]
    rw [ContinuousLinearMap.integral_apply hk1]
  · have hu : IntegrableOn (u : ℝ → V) (Ioc a b) := integrableOn_Lp_of_measure_ne_top u (by norm_num) measure_Ioc_lt_top.ne
    have hI : IntegrableOn (fun y => sh W (-y) (kv κ (u y))) (Ioc a b) := by
      refine (hu.norm.const_mul ‖kv κ‖).mono' (meas (fun y e => sh W (-y) (kv κ e)) (joint (kv κ)) _ hu.1)
        (Eventually.of_forall fun y => ?_)
      rw [show ‖sh W (-y) (kv κ (u y))‖ = ‖kv κ (u y)‖ from (shF W).norm _ _]
      exact (kv κ).le_opNorm _
    refine ⟨hI, Lp.ext ?_⟩
    have m1 : Continuous fun z : ℝ × ℝ => κ (-(z.2 + -z.1)) := hk.1.comp (by fun_prop)
    have m2 : StronglyMeasurable fun z : ℝ × ℝ => (u : ℝ → V) z.1 := (Lp.stronglyMeasurable u).comp_measurable measurable_fst
    have m3 : AEStronglyMeasurable (fun z : ℝ × ℝ => κ (-(z.2 + -z.1)) (u z.1)) ((volume.restrict (Ioc a b)).prod volume) :=
      (ContinuousLinearMap.apply ℂ W).flip.aestronglyMeasurable_comp₂ m1.aestronglyMeasurable m2.aestronglyMeasurable
    have m4 : ∀ y : ℝ, ∀ᵐ x : ℝ, sh W (-y) (kv κ (u y)) x = κ (-(x + -y)) (u y) := fun y => by
      filter_upwards [sh_ae W (-y) (kv κ (u y)),
        (measurePreserving_add_right volume (-y)).quasiMeasurePreserving.ae (sp (u y))] with x p q
      rw [p, q]
    have h1 : ∀ᵐ x : ℝ, (∫ y in Ioc a b, sh W (-y) (kv κ (u y)) : L W) x = ∫ y in Ioc a b, κ (-(x + -y)) (u y) :=
      ae_integral (volume.restrict (Ioc a b)) (fun y => sh W (-y) (kv κ (u y))) hI (fun z => κ (-(z.2 + -z.1)) (u z.1)) m3
        (Eventually.of_forall m4)
    filter_upwards [h1, (convSpec κ hk (cut V (Ioc a b) u)).1] with x p q
    rw [p, q, ← integral_indicator measurableSet_Ioc,
      ← integral_add_left_eq_self ((Ioc a b).indicator fun y => κ (-(x + -y)) (u y)) x]
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae (cutSpec (Ioc a b) measurableSet_Ioc u)] with t ht
    rw [ht]
    by_cases h : x + t ∈ Ioc a b
    · simp only [indicator_of_mem h]
      congr 2
      ring
    · simp only [indicator_of_notMem h, map_zero]
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem symb_diff {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (κ : ℝ → V →L[ℂ] V) (hk : Ker κ) : Differentiable ℂ (symb κ) := fun z => by
  have c1 : ∀ w : ℂ, Continuous fun t : ℝ => Complex.exp (w * t) • κ t := fun w =>
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul hk.1
  have c2 : Continuous fun t : ℝ => (Complex.exp (z * t) * t) • κ t :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul Complex.continuous_ofReal).smul hk.1
  have c3 : Continuous fun t : ℝ => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖ := by
    have := hk.1
    fun_prop
  have s1 : HasCompactSupport fun t : ℝ => Complex.exp (z * t) • κ t := hk.2.mono fun t ht h => ht (by simp [h])
  have s3 : HasCompactSupport fun t : ℝ => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖ := hk.2.mono fun t ht h => ht (by simp [h])
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := fun (w : ℂ) (t : ℝ) => Complex.exp (w * t) • κ t)
    (F' := fun (w : ℂ) (t : ℝ) => (Complex.exp (w * t) * t) • κ t) (bound := fun t => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖)
    (Metric.ball_mem_nhds z one_pos) (Eventually.of_forall fun w => (c1 w).aestronglyMeasurable)
    ((c1 z).integrable_of_hasCompactSupport s1) c2.aestronglyMeasurable
    (Eventually.of_forall fun t w hw => ?_) (c3.integrable_of_hasCompactSupport s3)
    (Eventually.of_forall fun t w _ => ?_)).2.differentiableAt
  · rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    have := norm_sub_norm_le w z
    rw [Metric.mem_ball, dist_eq_norm] at hw
    linarith
  · simpa using (((hasDerivAt_id w).mul_const (t : ℂ)).cexp).smul_const (κ t)

theorem UpperTheory.V.Z.IntegralApplyAeEq.convDense :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (β : ℝ → V →L[ℂ] V), Ker β → IsUnit (symb β 0) → DenseRange (conv β) := by
  intro V _ _ _ _ β hk hu
  obtain ⟨k1, k2, k3⟩ := convAdj β hk
  let D : ℂ → ℂ := fun z => LinearMap.det (symb (sharp β) z : V →ₗ[ℂ] V)
  have hD : Differentiable ℂ D := by
    let b := Module.finBasis ℂ V
    have e : D = fun z => ∑ s : Equiv.Perm (Fin (Module.finrank ℂ V)), ((Equiv.Perm.sign s : ℤ) : ℂ) *
        ∏ i, (b.coord (s i)).toContinuousLinearMap (symb (sharp β) z (b i)) := by
      funext z
      simp only [D]
      rw [← LinearMap.det_toMatrix b, Matrix.det_apply']
      simp [LinearMap.toMatrix_apply]
    rw [e]
    refine Differentiable.fun_sum fun s _ => (differentiable_const _).mul ?_
    intro z
    apply (Finset.analyticAt_fun_prod Finset.univ ?_).differentiableAt
    intro i _
    exact ((ContinuousLinearMap.differentiable _).comp ((symb_diff _ k1).clm_apply (differentiable_const _))).analyticAt z
  have h0 : D 0 ≠ 0 := by
    have : IsUnit (symb (sharp β) 0) := by
      rw [k3, map_zero, neg_zero]; exact hu.star
    exact ((LinearMap.isUnit_iff_isUnit_det _).1 ((Module.End.isUnit_iff _).2 (ContinuousLinearMap.isUnit_iff_bijective.1 this))).ne_zero
  let g : ℝ → ℂ := fun ξ => D (2 * Real.pi * Complex.I * ξ)
  have ga : AnalyticOnNhd ℝ g univ := fun ξ _ => by
    have h1 : AnalyticAt ℝ (fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ : ℂ)) ξ :=
      analyticAt_const.mul (Complex.ofRealCLM.analyticAt ξ)
    exact (hD.analyticAt _).restrictScalars.comp h1
  have gz : ∀ᵐ ξ : ℝ, g ξ ≠ 0 := by
    have h1 := ga.preimage_zero_mem_codiscreteWithin (x := 0) (by simpa [g] using h0) trivial isConnected_univ
    have h2 := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ h1
    rw [Measure.restrict_univ] at h2
    exact h2
  have inj : ∀ y : L V, conv (sharp β) y = 0 → y = 0 := fun y hy => by
    rw [← (Lp.fourierTransformₗᵢ ℝ V).map_eq_zero_iff]
    refine Lp.ext ?_
    have h1 := fourConv (sharp β) k1 y
    rw [hy, map_zero] at h1
    filter_upwards [h1, gz, Lp.coeFn_zero V 2 (volume : Measure ℝ)] with ξ a b c
    rw [c] at a ⊢
    have := ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit b))).1
    exact this (a₁ := _) (a₂ := 0) (a.symm.trans (map_zero _).symm)
  have bot : (LinearMap.range (conv β : L V →ₗ[ℂ] L V))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine inj y (ext_inner_left ℂ fun x => ?_)
    rw [← k2, ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    exact hy _ ⟨x, rfl⟩
  exact Submodule.dense_iff_topologicalClosure_eq_top.2 (Submodule.topologicalClosure_eq_top_iff.2 bot)
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem prj {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V →ₗᵢ[ℂ] H) (T : ℝ) :
    let P := J.toContinuousLinearMap ∘L cut V (Ioi T) ∘L ContinuousLinearMap.adjoint J.toContinuousLinearMap
    P * P = P ∧ IsSelfAdjoint P ∧ (∀ h, ∃ u : L V, (∀ᵐ x : ℝ, x ≤ T → u x = 0) ∧ P h = J u) ∧
      ∀ u : L V, (∀ᵐ x : ℝ, x ≤ T → u x = 0) → P (J u) = J u := by
  intro P
  obtain ⟨c1, c2, -, -, -, -, -, c8, -⟩ := cutLaws (V := V) (Ioi T) (Ioi T) measurableSet_Ioi measurableSet_Ioi
  rw [inter_self] at c1
  have cc : ∀ u, cut V (Ioi T) (cut V (Ioi T) u) = cut V (Ioi T) u := fun u => DFunLike.congr_fun c1 u
  have jj : ∀ u, ContinuousLinearMap.adjoint J.toContinuousLinearMap (J u) = u := fun u => ext_inner_left ℂ fun v => by
    rw [ContinuousLinearMap.adjoint_inner_right]; exact J.inner_map_map v u
  have pa : ∀ h, P h = J (cut V (Ioi T) (ContinuousLinearMap.adjoint J.toContinuousLinearMap h)) := fun _ => rfl
  refine ⟨?_, ?_, fun h => ⟨_, ?_, pa h⟩, fun u hu => ?_⟩
  · ext h
    rw [ContinuousLinearMap.mul_apply, pa h, pa, jj, cc]
  · show ContinuousLinearMap.adjoint P = P
    simp only [P, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, c2.adjoint_eq, ContinuousLinearMap.comp_assoc]
  · exact ((c8 _).1 (cc _)).mono fun x hx h => hx (by simpa using h)
  · rw [pa, jj, (c8 u).2 (hu.mono fun x hx h => hx (by simpa using h))]

theorem UpperTheory.V.Z.IntegralApplyAeEq.truncEq :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (T : ℝ) (Λ : H →L[ℂ] H),
      (∀ u v, ⟪J (cut V (Ioi T) u), J' (cut W (Ioi T) v)⟫_ℂ = 0) → (IsTrunc J J' T Λ ↔
        Λ = 1 - J.toContinuousLinearMap ∘L cut V (Ioi T) ∘L ContinuousLinearMap.adjoint J.toContinuousLinearMap -
          J'.toContinuousLinearMap ∘L cut W (Ioi T) ∘L ContinuousLinearMap.adjoint J'.toContinuousLinearMap) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ J J' T Λ ho
  obtain ⟨a1, a2, a3, a4⟩ := prj J T
  obtain ⟨b1, b2, b3, b4⟩ := prj J' T
  set P := J.toContinuousLinearMap ∘L cut V (Ioi T) ∘L ContinuousLinearMap.adjoint J.toContinuousLinearMap
  set P' := J'.toContinuousLinearMap ∘L cut W (Ioi T) ∘L ContinuousLinearMap.adjoint J'.toContinuousLinearMap
  have o1 : P * P' = 0 := by
    ext h
    refine ext_inner_left ℂ fun y => ?_
    rw [ContinuousLinearMap.mul_apply, ← a2.isSymmetric.apply_clm, ContinuousLinearMap.zero_apply, inner_zero_right]
    exact ho _ _
  have o2 : P' * P = 0 := by
    have := congrArg star o1
    rwa [star_mul, a2.star_eq, b2.star_eq, star_zero] at this
  have t0 : IsTrunc J J' T (1 - P - P') := by
    refine ⟨((IsSelfAdjoint.one _).sub a2).sub b2, ?_, fun h => ⟨fun hh => ?_, ?_⟩⟩
    · show (1 - P - P') * (1 - P - P') = _
      simp only [mul_sub, sub_mul, a1, b1, o1, o2, mul_one, one_mul]; abel
    · obtain ⟨u, hu, eu⟩ := a3 h
      obtain ⟨v, hv, ev⟩ := b3 h
      refine ⟨u, v, hu, hv, ?_⟩
      rw [← eu, ← ev]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at hh
      rw [sub_sub, sub_eq_zero] at hh
      exact hh
    · rintro ⟨u, v, hu, hv, rfl⟩
      have e1 : P (J' v) = 0 := by rw [← b4 v hv]; exact DFunLike.congr_fun o1 _
      have e2 : P' (J u) = 0 := by rw [← a4 u hu]; exact DFunLike.congr_fun o2 _
      simp [a4 u hu, b4 v hv, e1, e2]
  refine ⟨fun t1 => ?_, fun h => h ▸ t0⟩
  have key : ∀ A B : H →L[ℂ] H, IsTrunc J J' T A → IsTrunc J J' T B → A * B = A := fun A B hA hB => by
    ext h
    have h1 : B (h - B h) = 0 := by rw [map_sub, sub_eq_zero]; exact (DFunLike.congr_fun hB.2.1 h).symm
    have h2 := (hA.2.2 _).2 ((hB.2.2 _).1 h1)
    rw [map_sub, sub_eq_zero] at h2
    exact h2.symm
  have h1 := congrArg star (key _ _ t1 t0)
  rw [star_mul, t1.1.star_eq, t0.1.star_eq, key _ _ t0 t1] at h1
  exact h1.symm
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem layer (f : ℝ → ℝ) (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (2 * x) * f x) =
      ∫⁻ a, ENNReal.ofReal (2 * Real.exp (2 * a)) * ∫⁻ x in Ioi a, ENNReal.ofReal (f x) := by
  have e1 : ∀ x : ℝ, ENNReal.ofReal (Real.exp (2 * x)) = ∫⁻ a in Iio x, ENNReal.ofReal (2 * Real.exp (2 * a)) := fun x => by
    rw [setLIntegral_congr Iio_ae_eq_Iic, ← ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_exp_mul_Iic two_pos x).const_mul 2) (Eventually.of_forall fun _ => by positivity), integral_const_mul,
      integral_exp_mul_Iic two_pos]
    congr 1; ring
  have m : Measurable fun z : ℝ × ℝ => {z : ℝ × ℝ | z.2 < z.1}.indicator
      (fun z => ENNReal.ofReal (2 * Real.exp (2 * z.2)) * ENNReal.ofReal (f z.1)) z :=
    Measurable.indicator (by fun_prop) (measurableSet_lt measurable_snd measurable_fst)
  have := lintegral_lintegral_swap (μ := volume) (ν := volume) (f := fun x a : ℝ => {z : ℝ × ℝ | z.2 < z.1}.indicator
      (fun z => ENNReal.ofReal (2 * Real.exp (2 * z.2)) * ENNReal.ofReal (f z.1)) (x, a)) m.aemeasurable
  refine (lintegral_congr fun x => ?_).trans (this.trans (lintegral_congr fun a => ?_))
  · rw [ENNReal.ofReal_mul (Real.exp_pos _).le, e1, ← lintegral_mul_const _ (by fun_prop), ← lintegral_indicator measurableSet_Iio]
    rfl
  · rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_indicator measurableSet_Ioi]
    rfl

theorem UpperTheory.V.Z.IntegralApplyAeEq.wBound :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (g : L V) (p : L W) (c Q : ℝ), (∀ a : ℝ, ‖cut V (Ioi a) g‖ ≤ ‖cut W (Iic (c - a)) p‖) → WLe (-2) p Q → WLe 2 g (Real.exp c * Q) := by
  intro V _ _ _ _ W _ _ _ _ g p c Q h ⟨hp1, hp2⟩
  have ig : Integrable fun x => ‖g x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have ip : Integrable fun x => ‖p x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable p)).1 (Lp.memLp p)
  have mg : Measurable fun x => ‖g x‖ ^ 2 := (Lp.stronglyMeasurable g).norm.measurable.pow_const 2
  have mp : Measurable fun x => ‖p x‖ ^ 2 := (Lp.stronglyMeasurable p).norm.measurable.pow_const 2
  have ip' : Integrable fun x => ‖p (c - x)‖ ^ 2 := ip.comp_sub_left c
  have h1 : ∀ a, ∫⁻ x in Ioi a, ENNReal.ofReal (‖g x‖ ^ 2) ≤ ∫⁻ x in Ioi a, ENNReal.ofReal (‖p (c - x)‖ ^ 2) := fun a => by
    rw [← ofReal_integral_eq_lintegral_ofReal ig.integrableOn (Eventually.of_forall fun _ => by positivity),
      ← ofReal_integral_eq_lintegral_ofReal ip'.integrableOn (Eventually.of_forall fun _ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ∫ x in Ioi a, ‖p (c - x)‖ ^ 2 = ∫ x in Iic (c - a), ‖p x‖ ^ 2 := by
      rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Iic,
        ← integral_sub_left_eq_self _ volume c]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases b : x ≤ c - a
      · simp [indicator, b, show a ≤ c - x by linarith]
      · simp [indicator, b, show ¬ a ≤ c - x from fun k => b (by linarith)]
    rw [e, ← (cutLaws (V := V) _ univ measurableSet_Ioi .univ).2.2.2.2.2.2.2.2,
      ← (cutLaws (V := W) _ univ measurableSet_Iic .univ).2.2.2.2.2.2.2.2]
    exact pow_le_pow_left₀ (norm_nonneg _) (h a) 2
  have i2 : Integrable fun x => Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 := by
    refine ((hp1.comp_sub_left c).const_mul (Real.exp (2 * c))).congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [← mul_assoc, ← Real.exp_add]; ring_nf
  have v2 : ∫ x, Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 ≤ (Real.exp c * Q) ^ 2 := by
    have e : ∫ x, Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 = Real.exp (2 * c) * ∫ x, Real.exp (-2 * x) * ‖p x‖ ^ 2 := by
      rw [← integral_sub_left_eq_self (fun x => Real.exp (-2 * x) * ‖p x‖ ^ 2) volume c, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [← mul_assoc, ← Real.exp_add]; ring_nf
    rw [e, mul_pow, ← Real.exp_nat_mul]
    exact mul_le_mul_of_nonneg_left hp2 (Real.exp_pos _).le
  have mp' : Measurable fun x => ‖p (c - x)‖ ^ 2 := mp.comp (measurable_const.sub measurable_id)
  have h2 : ∫⁻ x, ENNReal.ofReal (Real.exp (2 * x) * ‖g x‖ ^ 2) ≤ ENNReal.ofReal ((Real.exp c * Q) ^ 2) := by
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal v2)
    rw [ofReal_integral_eq_lintegral_ofReal i2 (Eventually.of_forall fun _ => by positivity), layer _ mg, layer _ mp']
    exact lintegral_mono fun a => mul_le_mul' le_rfl (h1 a)
  have m2 : Measurable fun x => Real.exp (2 * x) * ‖g x‖ ^ 2 := (by fun_prop : Measurable fun x : ℝ => Real.exp (2 * x)).mul mg
  have i3 : Integrable fun x => Real.exp (2 * x) * ‖g x‖ ^ 2 :=
    ⟨m2.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)).2
      (h2.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨i3, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal i3 (Eventually.of_forall fun _ => by positivity)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cutLim :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (u : L V), (∀ T : ℝ, Tendsto (fun t => cut V (Ioi T) (sh V t u)) atTop (𝓝 0)) ∧
      ∀ a d : ℝ, 0 < d → HasSum (fun n : ℤ => cut V (Ioc (a + n * d) (a + (n + 1) * d)) u) u := by
  intro V _ _ _ _ u
  have hi : Integrable fun x => ‖u x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  have key : ∀ {ι : Type} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] (s : ι → Set ℝ), (∀ i, MeasurableSet (s i)) →
      Antitone s → ⋂ i, s i = ∅ → [Nonempty ι] → Tendsto (fun i => ‖cut V (s i) u‖) atTop (𝓝 0) := by
    intro ι _ _ s hm ha he _
    have h1 := tendsto_setIntegral_of_antitone (μ := volume) (f := fun x => ‖u x‖ ^ 2) hm ha ⟨Classical.arbitrary ι, hi.integrableOn⟩
    rw [he, setIntegral_empty] at h1
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    refine h2.congr fun i => ?_
    rw [Function.comp_apply, ← (cutLaws (V := V) (s i) (s i) (hm i) (hm i)).2.2.2.2.2.2.2.2 u, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨fun T => ?_, fun a d hd => ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (key (fun t : ℝ => Ioi (T + t)) (fun _ => measurableSet_Ioi) (fun x y h => Ioi_subset_Ioi (by linarith)) ?_).congr fun t => ?_
    · refine eq_empty_of_forall_notMem fun x hx => ?_
      have := mem_iInter.1 hx (x - T)
      simp at this
    · have h := DFunLike.congr_fun ((cutLaws (V := V) (Ioi (T + t)) univ measurableSet_Ioi .univ).2.2.2.2.2.2.1 t) u
      simp only [ContinuousLinearMap.comp_apply, preimage_add_const_Ioi, add_sub_cancel_right] at h
      rw [← h]; exact ((shF V).norm t _).symm
  · set I : ℤ → Set ℝ := fun n => Ioc (a + n * d) (a + (n + 1) * d) with hI
    have hm : ∀ F : Finset ℤ, MeasurableSet (⋃ n ∈ F, I n) := fun F => F.measurableSet_biUnion fun _ _ => measurableSet_Ioc
    have hdis : Pairwise (Function.onFun Disjoint I) := by
      simpa [hI] using pairwise_disjoint_Ioc_add_zsmul a d
    have hun : ⋃ n, I n = univ := by simpa [hI] using iUnion_Ioc_add_zsmul hd a
    have hs : ∀ F : Finset ℤ, ∑ n ∈ F, cut V (I n) u = cut V (⋃ n ∈ F, I n) u := by
      intro F
      induction F using Finset.induction_on with
      | empty => simp [(cutLaws (V := V) ∅ ∅ .empty .empty).2.2.2.2.1]
      | insert n F hn ih =>
        rw [Finset.sum_insert hn, ih, Finset.set_biUnion_insert,
          (cutLaws (V := V) (I n) _ measurableSet_Ioc (hm F)).2.2.1, ContinuousLinearMap.add_apply]
        exact disjoint_iUnion₂_right.2 fun k hk => hdis fun e => hn (e ▸ hk)
    have h1 := key (fun F : Finset ℤ => (⋃ n ∈ F, I n)ᶜ) (fun F => (hm F).compl)
      (fun F G h => compl_subset_compl.2 (biUnion_subset_biUnion_left h)) (by
        refine eq_empty_of_forall_notMem fun x hx => ?_
        obtain ⟨n, hn⟩ := mem_iUnion.1 (hun ▸ mem_univ x : x ∈ ⋃ n, I n)
        exact mem_iInter.1 hx {n} (by simpa using hn))
    rw [HasSum, tendsto_iff_norm_sub_tendsto_zero]
    refine h1.congr fun F => ?_
    obtain ⟨-, -, c3, c4, -⟩ := cutLaws (V := V) (⋃ n ∈ F, I n) (⋃ n ∈ F, I n)ᶜ (hm F) (hm F).compl
    have h2 := c3 disjoint_compl_right
    rw [union_compl_self, c4] at h2
    have h3 : u = cut V (⋃ n ∈ F, I n) u + cut V (⋃ n ∈ F, I n)ᶜ u := DFunLike.congr_fun h2 u
    rw [hs, norm_sub_rev, sub_eq_of_eq_add' h3]
end
