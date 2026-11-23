module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open Filter Topology Metric Set

namespace GlobalTheory

theorem gradedSeries_regroup {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (x s : ℂ)
    (hs : HasSum (fun i => c i * x ^ deg i) s) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) s := by
  have h1 := hs.tsum_fiberwise deg
  have e : (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) =
      (fun k => ∑' i : deg ⁻¹' {k}, c i * x ^ deg i) := by
    funext k
    rw [← tsum_mul_right]
    apply tsum_congr
    rintro ⟨i, hi⟩
    simp only [mem_preimage, mem_singleton_iff] at hi
    simp [hi]
  rw [e]
  exact h1

theorem gradedSeries_continue {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (δ ρ : ℝ) (Q : ℂ → ℂ)
    (hδ : 0 < δ) (hQ : DifferentiableOn ℂ Q (ball 0 ρ))
    (h : ∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => c i * (x : ℂ) ^ deg i) (Q x))
    (X : ℂ) (hX : ‖X‖ < ρ) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * X ^ k) (Q X) := by
  set A : ℕ → ℂ := fun k => ∑' i : deg ⁻¹' {k}, c i with hAdef
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ A with hpdef
  have hx0 : 0 < δ / 2 := by positivity
  set x0 : NNReal := ⟨δ / 2, hx0.le⟩ with hx0def
  have hrad : (x0 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    have hs := (gradedSeries_regroup deg c _ _ (h (δ / 2) hx0 (by linarith))).summable
    have hs' := summable_norm_iff.mpr hs
    refine hs'.congr fun n => ?_
    simp only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx0]
    rfl
  have hF := p.hasFPowerSeriesOnBall (lt_of_lt_of_le (ENNReal.coe_pos.2 (by rw [← NNReal.coe_pos]; exact hx0)) hrad)
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hX
  have hs0 : 0 < min (δ / 2) ρ := lt_min hx0 hρ
  have hQan : AnalyticOnNhd ℂ Q (ball 0 ρ) := hQ.analyticOnNhd isOpen_ball
  have hmem : ∀ z : ℂ, ‖z‖ < δ / 2 → z ∈ Metric.eball (0 : ℂ) p.radius := by
    intro z hz
    change edist _ (0 : ℂ) < _
    rw [edist_zero_right]
    refine lt_of_lt_of_le ?_ hrad
    exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; exact hz)
  have hFan : AnalyticOnNhd ℂ p.sum (ball 0 (min (δ / 2) ρ)) := fun z hz =>
    hF.analyticAt_of_mem (hmem z (lt_of_lt_of_le (by simpa using hz) (min_le_left _ _)))
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by simpa using (ne_of_gt hx))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), p.sum z = Q z := by
    refine ht.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT hx0] with x hx
    have h1 := gradedSeries_regroup deg c _ _ (h x hx.1 (by linarith [hx.2]))
    simp only [p, FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]
    exact h1.tsum_eq
  have heq : EqOn p.sum Q (ball 0 (min (δ / 2) ρ)) :=
    hFan.eqOn_of_preconnected_of_frequently_eq
      (hQan.mono (ball_subset_ball (min_le_right _ _)))
      (convex_ball _ _).isPreconnected (mem_ball_self hs0) hfreq
  have hQp : HasFPowerSeriesAt Q p 0 :=
    hF.hasFPowerSeriesAt.congr (Filter.eventuallyEq_of_mem (ball_mem_nhds 0 hs0) heq)
  have hR0 : 0 < (‖X‖ + ρ) / 2 := by positivity
  set R : NNReal := ⟨(‖X‖ + ρ) / 2, hR0.le⟩ with hRdef
  have hR : 0 < R := by rw [← NNReal.coe_pos]; exact hR0
  have hdR : DifferentiableOn ℂ Q (closedBall 0 R) :=
    hQ.mono (closedBall_subset_ball (by change (‖X‖ + ρ) / 2 < ρ; linarith))
  have hC := hdR.hasFPowerSeriesOnBall hR
  have hCp : cauchyPowerSeries Q 0 R = p := hC.hasFPowerSeriesAt.eq_formalMultilinearSeries hQp
  rw [hCp] at hC
  have hXm : X ∈ Metric.eball (0 : ℂ) R := by
    change edist _ (0 : ℂ) < _
    rw [edist_zero_right]
    exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; change ‖X‖ < (‖X‖ + ρ) / 2; linarith)
  have := hC.hasSum hXm
  simp only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at this
  exact this

theorem gradedSeries_continuation_dominated : ∀ {ι : Type} (deg : ι → ℕ),
    (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ),
    0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) →
    DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) →
    (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧
      HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) →
    ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧
      Summable (fun i => b i * ‖X‖ ^ deg i) := by
  intro ι deg hfin a b C δ ρ P P' hδ hb hab hP hP' h X hX
  have hA := gradedSeries_continue deg a δ ρ P hδ hP (fun x h1 h2 => (h x h1 h2).1) X hX
  have hB := gradedSeries_continue deg (fun i => (b i : ℂ)) δ ρ P' hδ hP'
    (fun x h1 h2 => (h x h1 h2).2) ((‖X‖ : ℝ) : ℂ) (by simpa using hX)
  have hBr : Summable (fun k => (∑' i : deg ⁻¹' {k}, b i) * ‖X‖ ^ k) := by
    rw [← Complex.summable_ofReal]
    refine hB.summable.congr fun k => ?_
    push_cast [Complex.ofReal_tsum]
    rfl
  have hsb : Summable (fun i => b i * ‖X‖ ^ deg i) := by
    rw [← (Equiv.sigmaFiberEquiv deg).summable_iff]
    rw [summable_sigma_of_nonneg (f := (fun i => b i * ‖X‖ ^ deg i) ∘ (Equiv.sigmaFiberEquiv deg))
      (fun _ => mul_nonneg (hb _) (pow_nonneg (norm_nonneg _) _))]
    refine ⟨fun k => ?_, ?_⟩
    · have : Finite {i // deg i = k} := (hfin k).to_subtype
      exact Summable.of_finite
    · refine hBr.congr fun k => ?_
      rw [← tsum_mul_right]
      exact tsum_congr fun y => by
        simp [Equiv.sigmaFiberEquiv, show deg y.1 = k from y.2]
  have hsa : Summable (fun i => a i * X ^ deg i) := by
    refine Summable.of_norm_bounded (hsb.mul_left C) fun i => ?_
    rw [norm_mul, norm_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hab i) (pow_nonneg (norm_nonneg _) _)
  refine ⟨?_, hsb⟩
  have h3 := hsa.hasSum
  have h4 := (gradedSeries_regroup deg a X _ h3).unique hA
  rw [h4] at h3
  exact h3

end GlobalTheory
end

section

open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_eq_gaussian_of_fderiv_add_eq_zero
    (l : Type) [Fintype l] [DecidableEq l] (h : 𝓢(EuclideanSpace ℝ l, ℂ))
    (H : ∀ (j : l) (x : EuclideanSpace ℝ l),
      fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x = 0)
    (x : EuclideanSpace ℝ l) :
    h x = h 0 * ((Real.exp (-Real.pi * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  have hE : ∀ y : EuclideanSpace ℝ l,
      HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2))
        (Real.exp (Real.pi * ‖y‖ ^ 2) • (Real.pi • (2 • innerSL ℝ y))) y := by
    intro y
    exact ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul Real.pi).exp
  have hu : ∀ y : EuclideanSpace ℝ l,
      HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y)
        (0 : EuclideanSpace ℝ l →L[ℝ] ℂ) y := by
    intro y
    have h1 := (hE y).smul (h.differentiableAt (x := y)).hasFDerivAt
    refine h1.congr_fderiv ?_
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun l ℝ).toBasis.ext
    intro j
    have h2 := H j y
    have h3 : fderiv ℝ (⇑h) y (EuclideanSpace.single j 1) = -(2 * Real.pi * (y j : ℂ) * h y) :=
      eq_neg_of_add_eq_zero_left h2
    simp [h3, EuclideanSpace.inner_single_right]
    ring
  have hc := is_const_of_fderiv_eq_zero (𝕜 := ℝ)
    (f := fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y)
    (fun y => (hu y).differentiableAt) (fun y => (hu y).fderiv) x 0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero, one_smul] at hc
  rw [← hc, Complex.real_smul, mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add]
  simp

end GlobalTheory
end

section

open SchwartzMap LineDeriv MeasureTheory ComplexConjugate

noncomputable section

namespace GlobalTheory.WrongSignGauss

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def sesq : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ).flip.comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).flip

@[simp] theorem sesq_apply (u w : ℂ) : sesq u w = u * conj w := by
  simp [sesq]; ring

def mulForm (ℓ : V →ₗ[ℝ] ℝ) : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (⇑(LinearMap.toContinuousLinearMap ℓ))

theorem mulForm_apply (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    mulForm ℓ f x = (ℓ x : ℂ) * f x := by
  rw [mulForm, SchwartzMap.smulLeftCLM_apply_apply (ContinuousLinearMap.hasTemperateGrowth _)]
  simp [Complex.real_smul]

theorem lineDerivOp_mulForm (v : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (mulForm ℓ f) x = (ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x := by
  have e : (⇑(mulForm ℓ f)) = ⇑(LinearMap.toContinuousLinearMap ℓ) • ⇑f := by
    funext y; rw [Pi.smul_apply', mulForm_apply, Complex.real_smul]; rfl
  have h2 := ((LinearMap.toContinuousLinearMap ℓ).hasFDerivAt (x := x)).smul (f.hasFDerivAt x)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, e, h2.fderiv]
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, Complex.real_smul]

theorem lineDerivOp_comm' (u v : V) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (∂_{u} f) x = ∂_{u} (∂_{v} f) x := by
  have key : ∀ (u v : V) x, ∂_{v} (∂_{u} f) x = fderiv ℝ (fderiv ℝ f) x v u := by
    intro u v x
    have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
      ((SchwartzMap.fderivCLM ℝ _ ℂ f).differentiableAt (x := x)).hasFDerivAt
    have h1 := ((ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt (x := fderiv ℝ f x)).comp x hd
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have e : (⇑(∂_{u} f : 𝓢(V, ℂ))) = (ContinuousLinearMap.apply ℝ ℂ u) ∘ fderiv ℝ f := by
      funext y; rfl
    rw [e, h1.fderiv]
    rfl
  rw [key, key]
  exact ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) _ _

def twD (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{a} f - (2 * Real.pi * Complex.I) • mulForm ℓ f

theorem twD_apply (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    twD a ℓ f x = ∂_{a} f x - 2 * Real.pi * Complex.I * ((ℓ x : ℂ) * f x) := by
  simp [twD, mulForm_apply]

section integrals

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

def ip (u w : 𝓢(V, ℂ)) : ℂ := ∫ x, u x * conj (w x) ∂μ

theorem integrable_ip (u w : 𝓢(V, ℂ)) : Integrable (fun x => u x * conj (w x)) μ := by
  have h := (pairing sesq u w).integrable (μ := μ)
  simpa [pairing_apply] using h

theorem ip_smul_left (c : ℂ) (u w : 𝓢(V, ℂ)) : ip μ (c • u) w = c * ip μ u w := by
  simp only [ip, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem ip_smul_right (c : ℂ) (u w : 𝓢(V, ℂ)) : ip μ u (c • w) = conj c * ip μ u w := by
  simp only [ip, SchwartzMap.smul_apply, smul_eq_mul, map_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem ip_sub_left (u v w : 𝓢(V, ℂ)) : ip μ (u - v) w = ip μ u w - ip μ v w := by
  simp only [ip, SchwartzMap.sub_apply, sub_mul]
  exact integral_sub (integrable_ip μ u w) (integrable_ip μ v w)

theorem ip_sub_right (u v w : 𝓢(V, ℂ)) : ip μ w (u - v) = ip μ w u - ip μ w v := by
  simp only [ip, SchwartzMap.sub_apply, map_sub, mul_sub]
  exact integral_sub (integrable_ip μ w u) (integrable_ip μ w v)

theorem ip_lineDerivOp (a : V) (u w : 𝓢(V, ℂ)) : ip μ (∂_{a} u) w = - ip μ u (∂_{a} w) := by
  have h := integral_bilinear_lineDerivOp_right_eq_neg_left (μ := μ) u w sesq a
  simp only [sesq_apply] at h
  simp only [ip, h, neg_neg]

theorem ip_mulForm (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) : ip μ (mulForm ℓ u) w = ip μ u (mulForm ℓ w) := by
  simp only [ip, mulForm_apply, map_mul, Complex.conj_ofReal]
  congr 1; funext x; ring

theorem ip_twD (a : V) (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) :
    ip μ (twD a ℓ u) w = - ip μ u (twD a ℓ w) := by
  simp only [twD, ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right, ip_lineDerivOp, ip_mulForm]
  simp [map_mul, Complex.conj_ofReal, map_ofNat]
  ring

end integrals

theorem lineDerivOp_twD (v a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (twD a ℓ f) x = ∂_{v} (∂_{a} f) x -
      2 * Real.pi * Complex.I * ((ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x) := by
  rw [twD, ← LineDeriv.lineDerivOpCLM_apply (R := ℂ), map_sub, map_smul,
    LineDeriv.lineDerivOpCLM_apply, LineDeriv.lineDerivOpCLM_apply]
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, lineDerivOp_mulForm]

theorem twD_comm (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    twD a₁ ℓ₁ (twD a₂ ℓ₂ f) - twD a₂ ℓ₂ (twD a₁ ℓ₁ f) =
      (-(2 * Real.pi * Complex.I) * ((ℓ₂ a₁ - ℓ₁ a₂ : ℝ) : ℂ)) • f := by
  ext x
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, twD_apply _ _ (twD _ _ f),
    lineDerivOp_twD]
  rw [twD_apply, twD_apply, lineDerivOp_comm' a₁ a₂ f x]
  push_cast
  ring

section main

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

theorem ip_self (h : 𝓢(V, ℂ)) : ip μ h h = ((∫ x, ‖h x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [ip]
  first
  | rw [← integral_complex_ofReal]
  | rw [← integral_ofReal (𝕜 := ℂ)]
  congr 1; funext x
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem norm_sq_twD (f : 𝓢(V, ℂ)) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ)
    (hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f) :
    ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ = Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h1 : ip μ (twD a₁ ℓ₁ (twD a₂ ℓ₂ f)) f = -(Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_left]
  have h2 : ip μ (twD a₂ ℓ₂ (twD a₁ ℓ₁ f)) f = -(conj Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_right]
  have h3 := congrArg (fun u => ip μ u f) (twD_comm a₁ a₂ ℓ₁ ℓ₂ f)
  simp only [ip_sub_left, ip_smul_left, h1, h2, Complex.conj_I, ip_self] at h3
  have E : ((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ((Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    push_cast at h3 ⊢
    linear_combination (Complex.I / 2) * h3 +
      (((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) - Real.pi * ((ℓ₂ a₁ : ℂ) - ℓ₁ a₂) *
        ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ)) * Complex.I_sq
  exact_mod_cast E

end main

theorem vanish : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ),
    (∀ y, fderiv ℝ f y a₂ + (-(2 * Real.pi * Complex.I) * (ℓ₂ y : ℂ)) * f y =
      Complex.I * (fderiv ℝ f y a₁ + (-(2 * Real.pi * Complex.I) * (ℓ₁ y : ℂ)) * f y)) →
    ℓ₂ a₁ - ℓ₁ a₂ < 0 → f = 0 := by
  intro V _ _ _ f a₁ a₂ ℓ₁ ℓ₂ hf hc
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  let μ : Measure V := Measure.addHaar
  have hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f := by
    ext y
    simp only [SchwartzMap.smul_apply, smul_eq_mul, twD_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    linear_combination hf y
  have hk := norm_sq_twD μ f a₁ a₂ ℓ₁ ℓ₂ hD
  have hG : 0 ≤ ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hF : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hP : Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) < 0 := mul_neg_of_pos_of_neg Real.pi_pos hc
  have hF0 : ∫ x, ‖f x‖ ^ 2 ∂μ = 0 := by nlinarith
  have hint : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    refine (integrable_ip μ f f).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_mul, sq]
  rw [integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint] at hF0
  have hcont : Continuous (fun x => ‖f x‖ ^ 2) := f.continuous.norm.pow 2
  have h0 := (Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hF0
  ext x
  have hx := congrFun h0 x
  simpa using hx

end GlobalTheory.WrongSignGauss
end
end

section

noncomputable section

namespace GlobalTheory.FockFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def blockB (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.fst ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

def blockD (J : (V × V) →ₗ[ℝ] (V × V)) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (LinearMap.snd ℝ V V ∘ₗ J ∘ₗ LinearMap.inr ℝ V V)

theorem blockB_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockB J q = (J (0, q)).1 := rfl

theorem blockD_apply (J : (V × V) →ₗ[ℝ] (V × V)) (q : V) : blockD J q = (J (0, q)).2 := rfl

def fockForm (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) : V →ₗ[ℝ] V →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ
    (fun x y => ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ))
    (fun x x' y => by simp only [map_add (f := _), LinearMap.add_apply]; push_cast; ring)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.real_smul]; push_cast; ring)
    (fun x y y' => by simp only [map_add (f := _)]; push_cast; ring)
    (fun c x y => by simp only [map_smul, smul_eq_mul, Complex.real_smul]; push_cast; ring)

theorem fockForm_apply (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (x y : V) :
    fockForm β J x y = ((Real.pi * β x (Ring.inverse (blockB J) y) : ℝ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * ((β x (blockD J (Ring.inverse (blockB J) y)) : ℝ) : ℂ) := rfl

end GlobalTheory.FockFamily

end
end

section

open MeasureTheory

namespace GlobalTheory


open MeasureTheory in
theorem _root_.GlobalTheory.mean_periodic_indep_of_covolume_one :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (μ μ' : Measure G) (𝓕 𝓕' : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → μ'.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕' μ' → μ' 𝓕' = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ∫ x in 𝓕', Φ x ∂μ' := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov μ μ' 𝓕 𝓕' hμ h𝓕 h𝓕1 hμ' h𝓕' h𝓕'1 Φ hΦ hper
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖Φ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hK.image hΦ.norm).bddAbove
    refine ⟨M, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hcov x
    rw [← hper γ hγ x]
    exact hM ⟨_, hx, rfl⟩
  have hint : IntegrableOn Φ 𝓕 μ :=
    Measure.integrableOn_of_bounded (by rw [h𝓕1]; exact ENNReal.one_ne_top)
      hΦ.aestronglyMeasurable (M := M) (Filter.Eventually.of_forall hM)
  refine ⟨hint, ?_⟩
  have hsm := Measure.isAddLeftInvariant_eq_smul μ' μ
  have hc0 : μ'.addHaarScalarFactor μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hsm
    rw [hsm] at h𝓕'1
    simp at h𝓕'1
  have hac : μ ≪ μ' := by
    intro s hs
    rw [hsm, Measure.smul_apply] at hs
    simpa [hc0] using hs
  have h𝓕'μ : IsAddFundamentalDomain Γ 𝓕' μ := h𝓕'.mono hac
  have hc1 : μ'.addHaarScalarFactor μ = 1 := by
    have e := h𝓕'1
    rw [hsm, Measure.smul_apply, h𝓕'μ.measure_eq h𝓕, h𝓕1] at e
    simpa using e
  have hμμ' : μ' = μ := by rw [hsm, hc1, one_smul]
  rw [hμμ']
  exact h𝓕.setIntegral_eq h𝓕'μ (fun g x => hper g g.2 x)

end GlobalTheory
end
