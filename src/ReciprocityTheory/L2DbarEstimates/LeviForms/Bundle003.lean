module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal

theorem vanish_lintegral_ball_smul (n : ℕ) (F : V n → ℝ≥0∞) (hF : Measurable F) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∫⁻ y in ball (0 : V n) 1, F (ρ • y) =
      ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| * ∫⁻ y in ball (0 : V n) ρ, F y := by
  have hind : ∀ y : V n, (ball (0 : V n) 1).indicator (fun y => F (ρ • y)) y =
      (ball (0 : V n) ρ).indicator F (ρ • y) := by
    intro y
    have hm : ρ • y ∈ ball (0 : V n) ρ ↔ y ∈ ball (0 : V n) 1 := by
      simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      exact mul_lt_iff_lt_one_right hρ
    by_cases h : y ∈ ball (0 : V n) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hm.mp h'))]
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  simp_rw [hind]
  have hFm : Measurable ((ball (0 : V n) ρ).indicator F) := hF.indicator measurableSet_ball
  rw [← lintegral_map hFm (measurable_const_smul ρ), Measure.map_addHaar_smul _ hρ.ne',
    lintegral_smul_measure, smul_eq_mul]

theorem vanish_div (n : ℕ) (hn : 1 ≤ n) (hDiv : C.MVDivStatement) {ρ c : ℝ} (hρ : 0 < ρ)
    (hc : 0 < c) {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝[>] 0)) :
    Tendsto (fun k => ∫⁻ y in ball (0 : V n) ρ,
      ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ)))) atTop (𝓝 ∞) := by
  have hn0 : 0 < n := hn
  have hcr : 0 < c * ρ ^ 2 := by positivity
  obtain ⟨hδ0, hδpos⟩ := tendsto_nhdsWithin_iff.mp hδ
  have hη : Tendsto (fun k => δ k / (c * ρ ^ 2)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hδ0.div_const (c * ρ ^ 2)
    · exact hδpos.mono fun k hk => div_pos hk hcr
  have hΦ := (hDiv n hn0).comp hη
  set K : ℝ≥0∞ := ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
    ENNReal.ofReal ((c * ρ ^ 2) ^ (-(n : ℝ))) with hK
  have hK0 : K ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hlim := ENNReal.Tendsto.const_mul (a := K) hΦ (Or.inl ENNReal.top_ne_zero)
  rw [ENNReal.mul_top hK0] at hlim
  refine hlim.congr' ?_
  filter_upwards [hδpos] with k hk
  have hk' : 0 < δ k := hk
  have hG : Measurable fun y : V n => ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) := by
    fun_prop
  have hs := vanish_lintegral_ball_smul n _ hG hρ
  have hd : ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
      ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  have hrhs : ∫⁻ y in ball (0 : V n) ρ, ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) =
      ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
        ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ((c * ‖ρ • y‖ ^ 2 + δ k) ^ (-(n : ℝ))) := by
    rw [hs, ← mul_assoc, hd, one_mul]
  show K * _ = _
  rw [hrhs, hK, mul_assoc]
  congr 1
  simp only [Function.comp_apply]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun z => ?_)
  have hz : 0 ≤ ‖z‖ ^ 2 + δ k / (c * ρ ^ 2) := by positivity
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hcr.le hz]
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  field_simp

end ReciprocityTheory.L2DbarEstimates.I
end

section

open Complex ComplexConjugate Filter Topology

namespace ReciprocityTheory.L2DbarEstimates

def LeviNonnegOn (n : ℕ) (φ : V n → ℝ) (U : Set (V n)) : Prop :=
  ∀ x ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun y => (φ y : ℂ)) x ξ).re

variable {n : ℕ}

theorem wd_congr {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wd n j f x = wd n j g x := by
  simp only [wd, h.fderiv_eq]

theorem wdb_congr {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wdb n j f x = wdb n j g x := by
  simp only [wdb, h.fderiv_eq]

theorem wdb_eventuallyEq {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wdb n j f =ᶠ[𝓝 x] wdb n j g := h.eventuallyEq_nhds.mono fun _ hy => wdb_congr hy

theorem leviV_congr {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) (ξ : Fin n → ℂ) :
    leviV n f x ξ = leviV n g x ξ := by
  unfold leviV
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [wd_congr (wdb_eventuallyEq h)]

theorem wd_add {j : Fin n} {f g : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : wd n j (fun y => f y + g y) x = wd n j f x + wd n j g x := by
  unfold wd
  rw [(show HasFDerivAt (fun y => f y + g y) _ x from hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.add_apply]
  ring

theorem wdb_add {j : Fin n} {f g : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : wdb n j (fun y => f y + g y) x = wdb n j f x + wdb n j g x := by
  unfold wdb
  rw [(show HasFDerivAt (fun y => f y + g y) _ x from hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.add_apply]
  ring

theorem wd_sum {ι : Type*} (s : Finset ι) {j : Fin n} {f : ι → V n → ℂ} {x : V n}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    wd n j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, wd n j (f i) x := by
  have e : (fun y => ∑ i ∈ s, f i y) = ∑ i ∈ s, f i := by
    funext y
    simp [Finset.sum_apply]
  unfold wd
  rw [e, (HasFDerivAt.sum fun i hi => (hf i hi).hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.sum_apply, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]

theorem wdb_sum {ι : Type*} (s : Finset ι) {j : Fin n} {f : ι → V n → ℂ} {x : V n}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    wdb n j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, wdb n j (f i) x := by
  have e : (fun y => ∑ i ∈ s, f i y) = ∑ i ∈ s, f i := by
    funext y
    simp [Finset.sum_apply]
  unfold wdb
  rw [e, (HasFDerivAt.sum fun i hi => (hf i hi).hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.sum_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]

theorem wd_mul {j : Fin n} {f g : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    wd n j (fun y => f y * g y) x = wd n j f x * g x + f x * wd n j g x := by
  unfold wd
  rw [(show HasFDerivAt (fun y => f y * g y) _ x from hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wdb_mul {j : Fin n} {f g : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    wdb n j (fun y => f y * g y) x = wdb n j f x * g x + f x * wdb n j g x := by
  unfold wdb
  rw [(show HasFDerivAt (fun y => f y * g y) _ x from hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem fderiv_ofReal_apply {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) (w : V n) :
    fderiv ℝ (fun y => (v y : ℂ)) x w = (fderiv ℝ v x w : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hv.hasFDerivAt
  rw [(show HasFDerivAt (fun y => (v y : ℂ)) _ x from h).fderiv]
  rfl

theorem differentiableAt_ofReal {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) :
    DifferentiableAt ℝ (fun y => (v y : ℂ)) x := (show HasFDerivAt (fun y => (v y : ℂ)) _ x from
    Complex.ofRealCLM.hasFDerivAt.comp x hv.hasFDerivAt).differentiableAt

theorem wd_ofReal_comp {j : Fin n} {k : ℝ → ℝ} {v : V n → ℝ} {x : V n}
    (hk : DifferentiableAt ℝ k (v x)) (hv : DifferentiableAt ℝ v x) :
    wd n j (fun y => (k (v y) : ℂ)) x = ((deriv k (v x) : ℝ) : ℂ) * wd n j (fun y => (v y : ℂ)) x := by
  have hkv : DifferentiableAt ℝ (fun y => k (v y)) x := hk.comp x hv
  have e : ∀ w, fderiv ℝ (fun y => (k (v y) : ℂ)) x w =
      ((deriv k (v x) : ℝ) : ℂ) * (fderiv ℝ v x w : ℂ) := by
    intro w
    rw [fderiv_ofReal_apply hkv, (show HasFDerivAt (fun y => k (v y)) _ x from
      hk.hasDerivAt.comp_hasFDerivAt x hv.hasFDerivAt).fderiv]
    simp
  simp only [wd, e, fderiv_ofReal_apply hv]
  ring

theorem wdb_ofReal_comp {j : Fin n} {k : ℝ → ℝ} {v : V n → ℝ} {x : V n}
    (hk : DifferentiableAt ℝ k (v x)) (hv : DifferentiableAt ℝ v x) :
    wdb n j (fun y => (k (v y) : ℂ)) x = ((deriv k (v x) : ℝ) : ℂ) * wdb n j (fun y => (v y : ℂ)) x := by
  have hkv : DifferentiableAt ℝ (fun y => k (v y)) x := hk.comp x hv
  have e : ∀ w, fderiv ℝ (fun y => (k (v y) : ℂ)) x w =
      ((deriv k (v x) : ℝ) : ℂ) * (fderiv ℝ v x w : ℂ) := by
    intro w
    rw [fderiv_ofReal_apply hkv, (show HasFDerivAt (fun y => k (v y)) _ x from
      hk.hasDerivAt.comp_hasFDerivAt x hv.hasFDerivAt).fderiv]
    simp
  simp only [wdb, e, fderiv_ofReal_apply hv]
  ring

theorem wdb_ofReal {j : Fin n} {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) :
    wdb n j (fun y => (v y : ℂ)) x = conj (wd n j (fun y => (v y : ℂ)) x) := by
  simp only [wdb, wd, fderiv_ofReal_apply hv]
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]
  all_goals ring

theorem fderiv_conj_apply {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) (w : V n) :
    fderiv ℝ (fun y => conj (f y)) x w = conj (fderiv ℝ f x w) := by
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x hf.hasFDerivAt
  rw [(show HasFDerivAt (fun y => conj (f y)) _ x from h).fderiv]
  rfl

theorem differentiableAt_conj {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => conj (f y)) x := (show HasFDerivAt (fun y => conj (f y)) _ x from
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

theorem wd_conj {j : Fin n} {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) :
    wd n j (fun y => conj (f y)) x = conj (wdb n j f x) := by
  simp only [wd, wdb, fderiv_conj_apply hf]
  simp [map_div₀, map_ofNat]
  all_goals ring

theorem wdb_conj {j : Fin n} {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) :
    wdb n j (fun y => conj (f y)) x = conj (wd n j f x) := by
  simp only [wd, wdb, fderiv_conj_apply hf]
  simp [map_div₀, map_ofNat]
  all_goals ring

theorem fderiv_real_of_complex {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℂ f x) (w : V n) :
    fderiv ℝ f x w = fderiv ℂ f x w := by
  rw [(hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  rfl

theorem wdb_of_differentiableAt {j : Fin n} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℂ f x) : wdb n j f x = 0 := by
  rw [wdb, fderiv_real_of_complex hf, fderiv_real_of_complex hf,
    ContinuousLinearMap.map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

theorem wd_of_differentiableAt {j : Fin n} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℂ f x) : wd n j f x = fderiv ℂ f x (bas n j) := by
  rw [wd, fderiv_real_of_complex hf, fderiv_real_of_complex hf,
    ContinuousLinearMap.map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

theorem differentiableAt_wdb {j : Fin n} {f : V n → ℂ} {x : V n} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (wdb n j f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  show DifferentiableAt ℝ (fun y => (fderiv ℝ f y (bas n j) +
    Complex.I * fderiv ℝ f y (Complex.I • bas n j)) / 2) x
  have h1 := hd.clm_apply (differentiableAt_const (bas n j))
  have h2 := (hd.clm_apply (differentiableAt_const (Complex.I • bas n j))).const_mul Complex.I
  refine ((h1.add h2).mul_const (2 : ℂ)⁻¹).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [div_eq_mul_inv]

theorem differentiableAt_wd {j : Fin n} {f : V n → ℂ} {x : V n} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (wd n j f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  show DifferentiableAt ℝ (fun y => (fderiv ℝ f y (bas n j) -
    Complex.I * fderiv ℝ f y (Complex.I • bas n j)) / 2) x
  have h1 := hd.clm_apply (differentiableAt_const (bas n j))
  have h2 := (hd.clm_apply (differentiableAt_const (Complex.I • bas n j))).const_mul Complex.I
  refine ((h1.sub h2).mul_const (2 : ℂ)⁻¹).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [div_eq_mul_inv]

theorem differentiableAt_deriv_of_contDiffAt {k : ℝ → ℝ} {t : ℝ} (hk : ContDiffAt ℝ 2 k t) :
    DifferentiableAt ℝ (deriv k) t := by
  have hd : DifferentiableAt ℝ (fderiv ℝ k) t :=
    (hk.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  show DifferentiableAt ℝ (fun s => fderiv ℝ k s 1) t
  exact hd.clm_apply (differentiableAt_const _)

theorem eventually_differentiableAt_of_contDiffAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := (hf.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)

end ReciprocityTheory.L2DbarEstimates
end
