module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Convolution
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.Fourier.Notation
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.scalSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (φ : ℝ → ℂ), Continuous φ → HasCompactSupport φ → Ker (scal V φ) ∧ (shF V).av φ = conv (scal V φ) ∧ kv (scal V φ) = sv V fun x => φ (-x) := by
  intro V _ _ _ _ φ h1 h2
  have hk : Ker (scal V φ) := ⟨h1.smul continuous_const, h2.smul_right (f' := fun _ => ContinuousLinearMap.id ℂ V)⟩
  refine ⟨hk, ?_, ?_⟩
  · ext1 u
    rw [(((avSpec (shF V)).2.2.2 φ (h1.integrable_of_hasCompactSupport h2)).1 u).2, (convSpec _ hk u).2.2]
    refine integral_congr_ae (Eventually.of_forall fun t => Lp.ext ?_)
    filter_upwards [Lp.coeFn_smul (φ t) (sh V t u), (scal V φ t).coeFn_compLpL (sh V t u)] with x a b
    rw [b]; exact a
  · ext1 e
    have hm : MemLp (fun x => φ (-x)) 2 volume :=
      (h1.comp continuous_neg).memLp_of_hasCompactSupport (h2.comp_homeomorph (Homeomorph.neg ℝ))
    refine Lp.ext ?_
    filter_upwards [((kvSpec _ hk).1 e).1, ((svSpec (V := V)).1 _ hm e).1] with x a b
    rw [a, b]; rfl
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem r_int : Integrable (fun y : ℝ => ((1 + |y|) ^ 2)⁻¹) ∧ ∫ y : ℝ, ((1 + |y|) ^ 2)⁻¹ = 2 := by
  constructor
  · refine integrable_inv_one_add_sq.mono' (Continuous.aestronglyMeasurable (Continuous.fun_inv₀ (by fun_prop) fun y => by positivity))
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    refine inv_anti₀ (by positivity) ?_
    nlinarith [abs_nonneg y, sq_abs y]
  · rw [integral_comp_abs (f := fun y => ((1 + y) ^ 2)⁻¹)]
    have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (g := fun y : ℝ => -(1 + y)⁻¹) (g' := fun y => ((1 + y) ^ 2)⁻¹) (l := 0)
      (fun y hy => by
        have h0 : (1 + y) ≠ 0 := by have : 0 ≤ y := hy; positivity
        have := (((hasDerivAt_id y).const_add 1).inv h0).neg
        exact this.congr_deriv (by simp only [id]; rw [neg_div, neg_neg, one_div]))
      (fun y _ => by positivity)
      (by simpa using (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ (1 : ℝ) tendsto_id)).neg)
    rw [h]; norm_num

private theorem symb_app {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W) (hk : Ker κ) (z : ℂ) (e : V) :
    symb κ z e = ∫ t : ℝ, Complex.exp (z * t) • κ t e := by
  have c1 : Continuous fun t : ℝ => Complex.exp (z * t) • κ t :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul hk.1
  have s1 : HasCompactSupport fun t : ℝ => Complex.exp (z * t) • κ t := hk.2.mono fun t ht h => ht (by simp [h])
  exact ContinuousLinearMap.integral_apply (c1.integrable_of_hasCompactSupport s1) e

theorem UpperTheory.V.Z.IntegralApplyAeEq.planch :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W) (K : ℝ), Ker κ → (∀ y : ℝ, ‖symb κ (1 + y * Complex.I)‖ ≤ K / (1 + |y|)) →
      ∀ e, WLe (-2) (kv κ e) (K / √3 * ‖e‖) := by
  intro V _ _ _ _ W _ _ _ _ κ K hk hb e
  let f : ℝ → W := fun t => (Real.exp t : ℂ) • κ t e
  have fc : Continuous f := (Complex.continuous_ofReal.comp Real.continuous_exp).smul (hk.1.clm_apply continuous_const)
  have fs : HasCompactSupport f := hk.2.mono fun t ht h => ht (by simp [f, h])
  have fm : MemLp f 2 volume := fc.memLp_of_hasCompactSupport fs
  have fi : Integrable f := fc.integrable_of_hasCompactSupport fs
  have e1 : ∀ᵐ x : ℝ, ‖f (-x)‖ ^ 2 = Real.exp (-2 * x) * ‖kv κ e x‖ ^ 2 := by
    filter_upwards [((kvSpec κ hk).1 e).1] with x hx
    rw [hx, norm_smul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have i2 : Integrable fun x => ‖f x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm fc.aestronglyMeasurable).1 fm
  refine ⟨i2.comp_neg.congr e1, ?_⟩
  rw [← integral_congr_ae e1, integral_neg_eq_self fun x => ‖f x‖ ^ 2]
  have nn : ∀ u : L W, ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := fun u => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner u u)]
    simp only [inner_self_eq_norm_sq]
  have e2 : ∫ x, ‖f x‖ ^ 2 = ‖Lp.fourierTransformₗᵢ ℝ W (fm.toLp f)‖ ^ 2 := by
    rw [LinearIsometryEquiv.norm_map, nn]
    exact integral_congr_ae (fm.coeFn_toLp.mono fun x hx => by simp only [hx])
  have hF : ∀ ξ : ℝ, 𝓕 f ξ = symb κ (1 + ((-(2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I) e := fun ξ => by
    rw [Real.fourier_real_eq_integral_exp_smul, symb_app κ hk]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [f, smul_smul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2; push_cast; ring
  obtain ⟨ri, rv⟩ := r_int
  rw [e2, nn]
  calc _ ≤ ∫ ξ, (K * ‖e‖) ^ 2 * ((1 + |2 * Real.pi * ξ|) ^ 2)⁻¹ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          ((ri.comp_mul_left' (R := 2 * Real.pi) (by positivity)).const_mul _) ?_
        filter_upwards [fourAe (fm.toLp f) (fi.congr fm.coeFn_toLp.symm)] with ξ hξ
        rw [hξ, Real.fourier_congr_ae fm.coeFn_toLp, hF]
        have h1 := (symb κ _).le_of_opNorm_le (hb (-(2 * Real.pi * ξ))) e
        rw [abs_neg] at h1
        refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans_eq ?_
        field_simp
    _ = (K * ‖e‖) ^ 2 * (|(2 * Real.pi)⁻¹| * 2) := by
        rw [integral_const_mul, Measure.integral_comp_mul_left (fun y : ℝ => ((1 + |y|) ^ 2)⁻¹), smul_eq_mul, rv]
    _ ≤ _ := by
        rw [div_mul_eq_mul_div, div_pow, Real.sq_sqrt (by norm_num), div_eq_mul_inv, abs_of_pos (by positivity)]
        gcongr
        rw [mul_inv, mul_right_comm, inv_mul_cancel₀ two_ne_zero, one_mul]
        exact inv_anti₀ (by norm_num) Real.pi_gt_three.le
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.carLaws :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ →
      (∀ t h, X (M.F.U t h) = M.F.U (-t) (X h)) ∧ M.swap.Carries (ContinuousLinearMap.adjoint X) (sharp κ) ∧
      ∀ ρ T : ℝ, (∀ t, ρ < |t| → κ t = 0) → M.P' (Ioi (T + ρ)) ∘L X ∘L (1 - M.P (Ioi T)) = 0 := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX
  obtain ⟨c1, c2, -⟩ := convLaws κ hk
  refine ⟨fun t h => ?_, fun v => ?_, fun ρ T hρ => ?_⟩
  · obtain ⟨u, rfl⟩ := M.J.surjective h
    rw [M.hJ, hX, hX, M.hJ', neg_neg]
    exact congrArg M.J' (DFunLike.congr_fun (c1 t) u)
  · refine ext_inner_left ℂ fun h => ?_
    obtain ⟨u, rfl⟩ := M.J.surjective h
    show ⟪M.J u, ContinuousLinearMap.adjoint X (M.J' v)⟫_ℂ = ⟪M.J u, M.J (conv (sharp κ) v)⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_right, hX, M.J'.inner_map_map, M.J.inner_map_map, ← (convAdj κ hk).2.1,
      ContinuousLinearMap.adjoint_inner_right]
  · ext h
    obtain ⟨u, rfl⟩ := M.J.surjective h
    have e : (1 - M.P (Ioi T)) (M.J u) = M.J (cut V (Iic T) u) := by
      have h1 := (cutLaws (V := V) (Iic T) (Ioi T) measurableSet_Iic measurableSet_Ioi)
      have h2 := h1.2.2.1 (Iic_disjoint_Ioi le_rfl)
      rw [Iic_union_Ioi, h1.2.2.2.1] at h2
      have h3 : u = cut V (Iic T) u + cut V (Ioi T) u := DFunLike.congr_fun h2 u
      simp only [Sc.P, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
      show M.J u - M.J (cut V (Ioi T) (M.J.symm (M.J u))) = _
      rw [M.J.symm_apply_apply, ← map_sub, sub_eq_of_eq_add h3]
    show M.P' (Ioi (T + ρ)) (X ((1 - M.P (Ioi T)) (M.J u))) = 0
    rw [e, hX]
    show M.J' (cut W (Ioi (T + ρ)) (M.J'.symm (M.J' _))) = 0
    rw [M.J'.symm_apply_apply]
    have := DFunLike.congr_fun (c2 ρ T hρ) u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
    rw [this, map_zero]
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem tr {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (e : V) (t : ℝ) :
    ‖∫ s in (0 : ℝ)..t, sh V s (one V e)‖ = ‖∫ s in (0 : ℝ)..t, sh ℂ s (one ℂ 1)‖ * ‖e‖ := by
  let T : L ℂ →L[ℂ] L V := (ContinuousLinearMap.toSpanSingleton ℂ e).compLpL 2 volume
  have hT : ∀ u : L ℂ, ∀ᵐ x : ℝ, T u x = u x • e := fun u =>
    ((ContinuousLinearMap.toSpanSingleton ℂ e).coeFn_compLpL u).mono fun x h => by rw [h]; simp
  have nsq : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (u : L V), ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := fun u => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner u u)]
    simp only [inner_self_eq_norm_sq]
  have hn : ∀ u, ‖T u‖ = ‖u‖ * ‖e‖ := fun u => by
    refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, nsq, nsq, ← integral_mul_const]
    exact integral_congr_ae ((hT u).mono fun x h => by simp only [h, norm_smul, mul_pow])
  have hs : ∀ s, T (sh ℂ s (one ℂ 1)) = sh V s (one V e) := fun s => Lp.ext (by
    have q := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving
    filter_upwards [hT (sh ℂ s (one ℂ 1)), sh_ae ℂ s (one ℂ 1), sh_ae V s (one V e), q.ae ((svSpec (V := ℂ)).2 1).1,
      q.ae ((svSpec (V := V)).2 e).1] with x h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4, h5]
    by_cases b : x + s ∈ Ioc (0 : ℝ) 1 <;> simp [b])
  have ii : IntervalIntegrable (fun s => sh ℂ s (one ℂ 1)) volume 0 t := ((shF ℂ).cont _).intervalIntegrable _ _
  rw [← hn, ← T.intervalIntegral_comp_comm ii]
  exact congrArg _ (intervalIntegral.integral_congr fun s _ => (hs s).symm)

theorem UpperTheory.V.Z.IntegralApplyAeEq.grow :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W], ∃ g : ℝ → ℝ, Tendsto g atTop atTop ∧ (∀ (e : V) (t : ℝ), ‖∫ s in (0 : ℝ)..t, sh V s (one V e)‖ = g t * ‖e‖) ∧
      ∀ (f : W) (t : ℝ), ‖∫ s in (0 : ℝ)..t, sh W (-s) (one W f)‖ = g t * ‖f‖ := by
  intro V _ _ _ _ W _ _ _ _
  refine ⟨fun t => ‖∫ s in (0 : ℝ)..t, sh ℂ s (one ℂ 1)‖, ?_, fun e t => tr e t, fun f t => ?_⟩
  · refine tendsto_atTop_mono' _ ?_ (Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id))
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hf : volume (Ioc (-t) 1) ≠ ⊤ := by simp
    obtain ⟨o1, -, o3⟩ := (svSpec (V := ℂ)).2 1
    have h1 : ⟪indicatorConstLp 2 measurableSet_Ioc hf (1 : ℂ), ∫ s in (0 : ℝ)..t, sh ℂ s (one ℂ 1)⟫_ℂ = t := by
      have := (innerSL ℂ (indicatorConstLp 2 measurableSet_Ioc hf (1 : ℂ))).intervalIntegral_comp_comm
        (((shF ℂ).cont (one ℂ 1)).intervalIntegrable (μ := volume) 0 t)
      simp only [innerSL_apply_apply] at this
      refine this.symm.trans ((intervalIntegral.integral_congr (g := fun _ => (1 : ℂ)) fun s hs => ?_).trans (by simp))
      rw [uIcc_of_le ht] at hs
      show ⟪indicatorConstLp 2 measurableSet_Ioc hf (1 : ℂ), sh ℂ s (one ℂ 1)⟫_ℂ = 1
      rw [L2.inner_indicatorConstLp_one, setIntegral_eq_integral_of_ae_compl_eq_zero, integral_congr_ae (sh_ae ℂ s _),
        integral_add_right_eq_self, o3]
      filter_upwards [sh_ae ℂ s (one ℂ 1), (measurePreserving_add_right volume s).quasiMeasurePreserving.ae o1] with x h1 h2 hx
      rw [h1, h2, indicator_of_notMem fun b => hx ⟨by linarith [b.1, hs.2], by linarith [b.2, hs.1]⟩]
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (indicatorConstLp 2 measurableSet_Ioc hf (1 : ℂ)) (∫ s in (0 : ℝ)..t, sh ℂ s (one ℂ 1))
    have h3 : ‖indicatorConstLp 2 measurableSet_Ioc hf (1 : ℂ)‖ ^ 2 = t + 1 := by
      rw [norm_indicatorConstLp (by simp) (by simp), Real.volume_real_Ioc_of_le (by linarith), norm_one, one_mul,
        ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      simp [add_comm]
    rw [h1, Complex.norm_real, Real.norm_of_nonneg ht] at h2
    have h4 := pow_le_pow_left₀ ht h2 2
    rw [mul_pow, h3] at h4
    refine Real.sqrt_le_iff.2 ⟨norm_nonneg _, ?_⟩
    show t + -1 ≤ _
    refine le_of_mul_le_mul_left (le_trans ?_ h4) (by linarith)
    nlinarith
  · have ii : IntervalIntegrable (fun s => sh W s (one W f)) volume 0 t := ((shF W).cont _).intervalIntegrable _ _
    have n1 : ∀ x, ‖sh W (-t) x‖ = ‖x‖ := (shF W).norm (-t)
    rw [← tr f t, ← n1 (∫ s in (0 : ℝ)..t, sh W s (one W f)), ← (sh W (-t)).intervalIntegral_comp_comm ii]
    congr 1
    have e : ∀ s, sh W (-t) (sh W s (one W f)) = sh W (s - t) (one W f) := fun s => by
      rw [← neg_add_eq_sub]; exact ((shF W).add _ _ _).symm
    simp only [e]
    rw [intervalIntegral.integral_comp_neg fun s => sh W s (one W f), intervalIntegral.integral_comp_sub_right fun s => sh W s (one W f)]
    simp
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.corOne :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (φ : ℝ → ℂ) (e n : V) (c : ℝ), Continuous φ → HasCompactSupport φ →
      Tendsto (fun a => ∫ s in (c - a)..(c + a), ⟪sv V φ e, sh V s (one V n)⟫_ℂ) atTop (𝓝 (conj (∫ x, φ x) * ⟪e, n⟫_ℂ)) := by
  intro V _ _ _ _ φ e n c h1 h2
  have iφ : Integrable φ := h1.integrable_of_hasCompactSupport h2
  have hf : Integrable fun x => conj (φ (-x)) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp iφ.comp_neg
  have hg : Integrable ((Ioc (0 : ℝ) 1).indicator fun _ => ⟪e, n⟫_ℂ) := (integrable_indicator_iff measurableSet_Ioc).2 (by simp)
  have e1 : ∀ s, ⟪sv V φ e, sh V s (one V n)⟫_ℂ = convolution (fun x => conj (φ (-x)))
      ((Ioc (0 : ℝ) 1).indicator fun _ => ⟪e, n⟫_ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume s := fun s => by
    rw [convolution_def, L2.inner_def, ← integral_neg_eq_self _ volume]
    rw [← integral_neg_eq_self (fun t => ContinuousLinearMap.mul ℂ ℂ (conj (φ (-t)))
      ((Ioc (0 : ℝ) 1).indicator (fun _ => ⟪e, n⟫_ℂ) (s - t))) volume, integral_neg_eq_self (fun a => ⟪sv V φ e a, sh V s (one V n) a⟫_ℂ) volume]
    refine integral_congr_ae ?_
    filter_upwards [((svSpec (V := V)).1 φ (h1.memLp_of_hasCompactSupport h2) e).1, sh_ae V s (one V n),
      (measurePreserving_add_right volume s).quasiMeasurePreserving.ae ((svSpec (V := V)).2 n).1] with x a1 a2 a3
    rw [a1, a2, a3, sub_neg_eq_add, add_comm s x, inner_smul_left]
    by_cases b : x + s ∈ Ioc (0 : ℝ) 1 <;> simp [b]
  simp only [e1]
  have t := intervalIntegral_tendsto_integral (hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg)
    (a := fun a : ℝ => c - a) (b := fun a : ℝ => c + a) (l := atTop)
    (tendsto_atBot_add_const_left _ c tendsto_neg_atTop_atBot) (tendsto_atTop_add_const_left _ c tendsto_id)
  rw [integral_convolution _ hf hg, integral_indicator measurableSet_Ioc, integral_conj, integral_neg_eq_self] at t
  simpa using t
end
