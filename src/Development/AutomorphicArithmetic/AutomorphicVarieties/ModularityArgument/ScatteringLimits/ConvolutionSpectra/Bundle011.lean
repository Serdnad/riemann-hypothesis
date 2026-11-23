module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle009
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nInt :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W →ₗ[ℂ] V), M.IsN N → ∀ (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → M.Acts Y β β' →
      ∀ w, N (symb β' 0 w) = symb β 0 (N w) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN Y β β' k1 k2 ha w
  obtain ⟨-, cadd, -, -, -, -, -, cmap⟩ := cobLaws M.F
  have hY : ∀ t h, Y (M.F.U t h) = M.F.U t (Y h) := fun t h => by
    obtain ⟨u, rfl⟩ := M.J.surjective h
    rw [M.hJ, ha.1, ha.1, M.hJ]
    exact congrArg M.J (DFunLike.congr_fun ((convLaws β k1).1 t) u)
  have h1 := cmap M.F Y hY _ (hN w)
  rw [map_sub, ha.1, ha.2] at h1
  obtain ⟨-, b1, s1⟩ := (svSpec (V := W)).2 w
  obtain ⟨-, b2, s2⟩ := (svSpec (V := V)).2 (N w)
  obtain ⟨b3, s3⟩ := (convLaws β' k2).2.2 _ b1
  obtain ⟨b4, s4⟩ := (convLaws β k1).2.2 _ b2
  have h2 := nAll M N hN _ b3
  rw [s3, s1] at h2
  have h3 := ((cobTail _).2 ((cobTail _).1 b4)).2
  rw [s4, s2] at h3
  have h4 := (cobLaws (shF V)).2.2.2.2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) (fun t h => (M.hJ t h).symm) _ h3
  have h5 := (cadd _ _ (cadd _ _ h1 h2).2 h4).1
  have h6 : M.F.Cob (M.J (one V (N (symb β' 0 w) - symb β 0 (N w)))) := by
    convert h5 using 1
    simp
  exact sub_eq_zero.1 ((nIso M).1 _ h6)
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem side {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Sc H V W)
    (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (k : Ker β) (hB : ∀ u, B (M.J u) = M.J (conv β u)) (f : ℕ → H)
    (q0 : Tendsto (fun n => ∫ t in Iic (0 : ℝ), Real.exp t * ‖M.F.U t (f n) - f n‖ ^ 2) atTop (𝓝 0))
    (p : Tendsto (fun n => M.P (Ioi M.T₀) (f n)) atTop (𝓝 0)) :
    Tendsto (fun n => B (f n) - M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) atTop (𝓝 0) ∧
      Tendsto (fun n => M.P (Ioi M.T₀) (B (f n))) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := convNear β k
  have a : Tendsto (fun n => B (f n) - M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) atTop (𝓝 0) := by
    have := (q0.const_mul C).sqrt
    rw [mul_zero, Real.sqrt_zero] at this
    refine squeeze_zero_norm (fun n => Real.le_sqrt_of_sq_le ?_) this
    obtain ⟨u, hu⟩ := M.J.surjective (f n)
    simp only [← hu, hB, M.J.symm_apply_apply, M.hJ, ← map_sub, M.J.norm_map]
    exact hC u
  refine ⟨a, ?_⟩
  let G : H →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L (symb β 0).compLpL 2 volume ∘L
    (M.J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
  have := (((M.P (Ioi M.T₀)).continuous.tendsto 0).comp a).add ((G.continuous.tendsto 0).comp p)
  simp only [map_zero, add_zero] at this
  refine this.congr fun n => ?_
  have e : G (M.P (Ioi M.T₀) (f n)) = M.P (Ioi M.T₀) (M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) := by
    show M.J ((symb β 0).compLpL 2 volume (M.J.symm (M.J (cut V _ _)))) = M.J (cut V _ (M.J.symm (M.J _)))
    rw [M.J.symm_apply_apply, M.J.symm_apply_apply]
    refine congrArg M.J (Lp.ext ?_)
    filter_upwards [(symb β 0).coeFn_compLpL (cut V (Ioi M.T₀) (M.J.symm (f n))), (symb β 0).coeFn_compLpL (M.J.symm (f n)),
      cutSpec (Ioi M.T₀) measurableSet_Ioi (M.J.symm (f n)),
      cutSpec (Ioi M.T₀) measurableSet_Ioi ((symb β 0).compLpL 2 volume (M.J.symm (f n)))] with x h1 h2 h3 h4
    erw [h1, h3, h4]
    by_cases hx : x ∈ Ioi M.T₀
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, map_zero]
  simp only [Function.comp_apply, map_sub, e, sub_add_cancel]

theorem UpperTheory.V.Z.IntegralApplyAeEq.resBelow :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → IsUnit (symb β 0) → IsUnit (symb β' 0) → M.Acts B β β' → IsCompactOperator (M.abelian₂ M.T₀ M.T₀ ∘L B ∘L M.abelian₂ M.T₀ M.T₀) →
      ∀ f : ℕ → H, (∀ n, ‖f n‖ = 1) → Tendsto (fun n => M.abelian₂ M.T₀ M.T₀ (f n) - f n) atTop (𝓝 0) →
        Tendsto (fun n => (⟪f n, M.F.av wR (f n)⟫_ℂ).re) atTop (𝓝 1) → False := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc f hf t1 t2
  set Λ := M.abelian₂ M.T₀ M.T₀ with hΛ
  obtain ⟨-, -, -, -, -, -, l2, -, l4⟩ := (projLaws M).2.2.2.2.2.2.2 M.T₀ M.T₀ (by linarith)
  let q : H → ℝ := fun h => ∫ t in Iic (0 : ℝ), Real.exp t * ‖M.F.U t h - h‖ ^ 2
  have q0 : Tendsto (fun n => q (f n)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (2 : ℝ))).sub (t2.const_mul 2)
    simp only [mul_one, sub_self] at this
    exact this.congr fun n => by simp only [q, (resCob M.F _).2, hf]; ring
  have p1 : Tendsto (fun n => M.P (Ioi M.T₀) (f n)) atTop (𝓝 0) := by
    have := (((M.P (Ioi M.T₀)).continuous.tendsto 0).comp t1).neg
    simp only [map_zero, neg_zero] at this
    exact this.congr fun n => by
      have l : M.P (Ioi M.T₀) (Λ (f n)) = 0 := DFunLike.congr_fun l2 _
      simp [l]
  have p2 : Tendsto (fun n => M.P' (Ioi M.T₀) (f n)) atTop (𝓝 0) := by
    have := (((M.P' (Ioi M.T₀)).continuous.tendsto 0).comp t1).neg
    simp only [map_zero, neg_zero] at this
    exact this.congr fun n => by
      have l : M.P' (Ioi M.T₀) (Λ (f n)) = 0 := DFunLike.congr_fun l4 _
      simp [l]
  obtain ⟨a1, a2⟩ := side M B β k1 ha.1 f q0 p1
  obtain ⟨-, a3⟩ := side M.swap B β' k2 ha.2 f (q0.congr fun n => by
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    show _ = Real.exp t * ‖M.F.U (-t) (f n) - f n‖ ^ 2
    rw [← M.F.norm t (M.F.U (-t) (f n) - f n), map_sub, ← M.F.add, add_neg_cancel, M.F.zero, norm_sub_rev]) p2
  have a4 : Tendsto (fun n => B (f n) - (Λ ∘L B ∘L Λ) (f n)) atTop (𝓝 0) := by
    have := (a2.add a3).sub (((Λ ∘L B).continuous.tendsto 0).comp t1)
    simp only [map_zero, add_zero, sub_zero] at this
    refine this.congr fun n => ?_
    have e : Λ (B (f n)) = B (f n) - M.P (Ioi M.T₀) (B (f n)) - M.swap.P (Ioi M.swap.T₀) (B (f n)) := rfl
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_sub, e]
    abel
  obtain ⟨S, hS, hsub⟩ := hc.image_closedBall_subset_compact 1
  obtain ⟨y, -, φ, hφ, hy⟩ := hS.tendsto_subseq fun n => hsub ⟨f n, by simp [hf], rfl⟩
  obtain ⟨s, hs⟩ := u1
  let G : H →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L ((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).compLpL 2 volume ∘L
    (M.J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
  have hG : ∀ h, G (M.J ((symb β 0).compLpL 2 volume (M.J.symm h))) = h := fun h => by
    show M.J (((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).compLpL 2 volume (M.J.symm (M.J _))) = h
    rw [M.J.symm_apply_apply, ← M.J.eq_symm_apply]
    refine Lp.ext ?_
    filter_upwards [((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).coeFn_compLpL ((symb β 0).compLpL 2 volume (M.J.symm h)),
      (symb β 0).coeFn_compLpL (M.J.symm h)] with x h1 h2
    rw [h1, h2, ← hs]
    exact DFunLike.congr_fun s.inv_mul _
  have c1 : Tendsto (fun n => f (φ n)) atTop (𝓝 (G y)) := by
    have := (G.continuous.tendsto _).comp ((hy.add (a4.comp hφ.tendsto_atTop)).sub (a1.comp hφ.tendsto_atTop))
    simp only [add_zero, sub_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, ContinuousLinearMap.coe_coe, add_sub_cancel, sub_sub_cancel, hG]
  set g := G y
  have g1 : ‖g‖ = 1 := tendsto_nhds_unique c1.norm (by simp [hf])
  have qc : Continuous q := by
    simp only [q, (resCob M.F _).2]
    fun_prop
  have g2 : q g = 0 := tendsto_nhds_unique ((qc.tendsto g).comp c1) (q0.comp hφ.tendsto_atTop)
  have cg : Continuous fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2 := by
    have := M.F.cont g
    fun_prop
  have ig : IntegrableOn (fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2) (Iic 0) := by
    refine Integrable.mono' ((integrableOn_exp_Iic 0).mul_const 4) cg.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have : ‖M.F.U t g - g‖ ≤ 2 := (norm_sub_le _ _).trans_eq (by rw [M.F.norm, g1]; norm_num)
    gcongr
    nlinarith [norm_nonneg (M.F.U t g - g)]
  have g3 := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun t => by positivity) ig).1 g2
  have g4 : EqOn (fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2) 0 (Iio 0) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset Iio_subset_Iic_self g3) isOpen_Iio cg.continuousOn
      continuousOn_const
  have g5 : ∀ᶠ t in atBot, ⟪g, M.F.U t g⟫_ℂ = 1 := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    have := g4 ht
    simp only [Pi.zero_apply, mul_eq_zero, (Real.exp_pos t).ne', false_or, pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero] at this
    rw [this, inner_self_eq_norm_sq_to_K, g1]; simp
  exact one_ne_zero (tendsto_nhds_unique (tendsto_const_nhds.congr' (g5.mono fun _ h => h.symm)) ((projLaws M).1 g g).2)
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.flip :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (a b : ℝ), (∀ t h, X (M.F.U t h) = M.F.U (-t) (X h)) →
      IsHilbertSchmidt (M.P (Ioc a b) ∘L X) → IsHilbertSchmidt (X ∘L M.P (Ioc a b)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X a b hX hs
  obtain ⟨-, -, -, -, pl, p0, -, -⟩ := projLaws M
  rcases le_or_gt b a with hab | hab
  · rw [Ioc_eq_empty_of_le hab, p0, ContinuousLinearMap.comp_zero]
    show hsNormSq _ < _
    rw [hsNormSq_zero]; exact ENNReal.zero_lt_top
  set d := b - a with hd
  have d0 : 0 < d := sub_pos.2 hab
  let I : ℤ → Set ℝ := fun n => Ioc (a + n * d) (a + (n + 1) * d)
  have hI : ∀ n, MeasurableSet (I n) := fun _ => measurableSet_Ioc
  have sa : ∀ s, MeasurableSet s → ContinuousLinearMap.adjoint (M.P s) = M.P s := fun s hs => (pl s s hs hs).2.1.adjoint_eq
  have pyth : ∀ x : H, ‖x‖ₑ ^ 2 = ∑' n, ‖M.P (I n) x‖ₑ ^ 2 := fun x => by
    have h1 : HasSum (fun n => M.P (I n) x) x := by
      have h0 : HasSum (fun n => M.P (I n) x) (M.J (M.J.symm x)) :=
        ((cutLim (M.J.symm x)).2 a d d0).mapL (M.J.toContinuousLinearEquiv : L V →L[ℂ] H)
      rwa [M.J.apply_symm_apply] at h0
    have h2 := (h1.mapL (innerSL ℂ x)).mapL Complex.reCLM
    have e : ∀ n, (⟪x, M.P (I n) x⟫_ℂ).re = ‖M.P (I n) x‖ ^ 2 := fun n => by
      have i1 := DFunLike.congr_fun (pl _ _ (hI n) (hI n)).1 x
      rw [inter_self, ContinuousLinearMap.comp_apply] at i1
      rw [← i1, ← ContinuousLinearMap.adjoint_inner_left, sa _ (hI n), i1, inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    simp only [innerSL_apply_apply, Complex.reCLM_apply, e] at h2
    rw [inner_self_eq_norm_sq_to_K] at h2
    have h3 : HasSum (fun n => ‖M.P (I n) x‖ ^ 2) (‖x‖ ^ 2) := by simpa [← Complex.ofReal_pow] using h2
    have h4 := ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖M.P (I n) x‖) h3.summable
    rw [h3.tsum_eq] at h4
    simpa [ENNReal.ofReal_pow] using h4
  have dec : ∀ Y : H →L[ℂ] H, hsNormSq Y = ∑' n, hsNormSq (M.P (I n) ∘L Y) := fun Y => by
    simp only [hsNormSq]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun m => pyth _
  have un : ∀ t, ‖M.F.U t‖ₑ ≤ 1 := fun t => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_one]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by rw [M.F.norm, one_mul]
  have step : ∀ n : ℤ, hsNormSq (M.P (I n) ∘L X ∘L M.P (Ioc a b)) ≤ hsNormSq (M.P (I n) ∘L ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X)) := fun n => by
    have t1 := ((pl (Ioc a b) _ measurableSet_Ioc (measurableSet_Ioc (a := a) (b := b))).2.2.2.2 (-(n * d))).1
    have pre : (fun x => x + -(n * d)) ⁻¹' Ioc a b = I n := by
      ext x
      simp only [I, mem_preimage, mem_Ioc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [pre] at t1
    have t2 : ∀ h, M.F.U (-(n * d)) (M.P (Ioc a b) h) = M.P (I n) (M.F.U (-(n * d)) h) := fun h => DFunLike.congr_fun t1 h
    have e : M.P (I n) ∘L X ∘L M.P (Ioc a b) = M.F.U (-(n * d)) ∘L (M.P (Ioc a b) ∘L X ∘L M.P (I n)) ∘L M.F.U (-(n * d)) := by
      ext h
      simp only [ContinuousLinearMap.comp_apply]
      rw [← t2, hX, t2, ← M.F.add, add_neg_cancel, M.F.zero]
    have e2 : M.P (I n) ∘L ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X) =
        ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X ∘L M.P (I n)) := by
      simp only [ContinuousLinearMap.adjoint_comp, sa _ (hI n), ContinuousLinearMap.comp_assoc]
    rw [e, e2, hsNormSq_adjoint]
    refine (hsNormSq_comp_left_le _ _).trans ((mul_le_of_le_one_left' (pow_le_one' (un _) _)).trans ?_)
    exact (hsNormSq_comp_right_le _ _).trans (mul_le_of_le_one_left' (pow_le_one' (un _) _))
  show hsNormSq _ < _
  rw [dec]
  refine (ENNReal.tsum_le_tsum step).trans_lt ?_
  rw [← dec]
  exact hs.adjoint
end
