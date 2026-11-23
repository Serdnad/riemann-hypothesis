module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

section

open Metric Set Filter
open scoped Topology

namespace GlobalTheory.SCV

section General

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem fderiv_apply_eq_zero_of_frequently {f : E → V} {x s : E} (hf : DifferentiableAt ℂ f x)
    (h : ∃ᶠ t in 𝓝[≠] (0 : ℂ), f (x + t • s) = f x) : fderiv ℂ f x s = 0 := by
  have h1 : HasDerivAt (fun t : ℂ => f (x + t • s)) (fderiv ℂ f x s) 0 :=
    hf.hasFDerivAt.hasLineDerivAt s
  rw [hasDerivAt_iff_tendsto_slope_zero] at h1
  refine tendsto_nhds_unique_of_frequently_eq h1 tendsto_const_nhds (h.mono fun t ht => ?_)
  simp [ht]

theorem frequently_nhdsNE_of_eventually_ofReal {p : ℂ → Prop}
    (h : ∀ᶠ t : ℝ in 𝓝 0, p t) : ∃ᶠ t in 𝓝[≠] (0 : ℂ), p t := by
  have h1 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact h1.frequently (h.filter_mono nhdsWithin_le_nhds).frequently

theorem fderiv_eq_zero_of_real_lines {f : E → V} {x : E} {S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hf : DifferentiableAt ℂ f x)
    (h : ∀ s ∈ S, ∀ᶠ t : ℝ in 𝓝 0, f (x + (t : ℂ) • s) = f x) : fderiv ℂ f x = 0 := by
  have : (fderiv ℂ f x : E →ₗ[ℂ] V) = 0 :=
    LinearMap.ext_on hS fun s hs => fderiv_apply_eq_zero_of_frequently hf
      (frequently_nhdsNE_of_eventually_ofReal (p := fun t => f (x + t • s) = f x) (h s hs))
  ext v
  exact LinearMap.congr_fun this v

theorem eq_of_eventually_real_lines {f : E → V} {U S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ s ∈ S, ∀ᶠ t : ℝ in 𝓝 0, f (z + (t : ℂ) • s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w :=
  hU.is_const_of_fderiv_eq_zero hU' hf
    (fun x hx => fderiv_eq_zero_of_real_lines hS (hf.differentiableAt (hU.mem_nhds hx)) (h x hx))
    hz hw

theorem eq_of_invariant_real_lines {f : E → V} {U S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ s ∈ S, ∀ t : ℝ, z + (t : ℂ) • s ∈ U → f (z + (t : ℂ) • s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_eventually_real_lines hS hU hU' hf (fun x hx s hs => ?_) hz hw
  have h1 : Tendsto (fun t : ℝ => x + (t : ℂ) • s) (𝓝 0) (𝓝 x) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  exact (h1.eventually (hU.mem_nhds hx)).mono fun t ht => h x hx s hs t ht

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem eq_of_invariant_realSubspace {f : E → V} {U : Set E} {S : Submodule ℝ E}
    (hS : Submodule.span ℂ (S : Set E) = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (h : ∀ z ∈ U, ∀ s ∈ S, z + s ∈ U → f (z + s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_invariant_real_lines hS hU hU' hf (fun x hx s hs t ht => h x hx _ ?_ ht) hz hw
  rw [show (t : ℂ) • s = t • s from algebraMap_smul ℂ t s]
  exact S.smul_mem t hs

variable [FiniteDimensional ℂ E] [CompleteSpace V]

end General

section Coordinates

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def scaledRealPoints (ι : Type*) (a : ℂ) : Submodule ℝ (ι → ℂ) where
  carrier := {z | ∃ x : ι → ℝ, z = fun i => a * x i}
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by ext i; simp [mul_add]⟩
  zero_mem' := ⟨0, by ext i; simp⟩
  smul_mem' := by
    rintro t _ ⟨x, rfl⟩
    exact ⟨t • x, by ext i; simp [mul_left_comm]⟩


omit [Fintype ι] in
theorem span_scaledRealPoints {a : ℂ} (ha : a ≠ 0) :
    Submodule.span ℂ (scaledRealPoints ι a : Set (ι → ℂ)) = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  have e : z = a⁻¹ • (fun i => a * ((z i).re : ℂ))
      + (a⁻¹ * Complex.I) • (fun i => a * ((z i).im : ℂ)) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Complex.re_add_im (z i)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    field_simp
  rw [e]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem eq_of_invariant_real {f : (ι → ℂ) → V} {U : Set (ι → ℂ)}
    (hU : IsOpen U) (hU' : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ x : ι → ℝ, (z + fun i => (x i : ℂ)) ∈ U → f (z + fun i => (x i : ℂ)) = f z)
    {z w : ι → ℂ} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_invariant_realSubspace (span_scaledRealPoints one_ne_zero) hU hU' hf ?_ hz hw
  rintro y hy _ ⟨x, rfl⟩
  simpa only [one_mul] using h y hy x

variable [CompleteSpace V]

end Coordinates

end GlobalTheory.SCV
end

section

open MeasureTheory Set Real
open scoped Nat ComplexConjugate

namespace GlobalTheory

section General

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def complexGaussian (g : ℕ) : Measure E :=
  volume.withDensity fun z => ENNReal.ofReal ((π ^ g)⁻¹ * exp (-‖z‖ ^ 2))

variable {E}

theorem integrable_exp_neg_mul_norm_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun z : E => exp (-b * ‖z‖ ^ 2) := by
  by_contra h
  have h1 := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) hb
  rw [integral_undef h] at h1
  exact absurd h1 (by positivity)

theorem integral_exp_neg_mul_norm_sq {g : ℕ} (hE : Module.finrank ℝ E = 2 * g) {b : ℝ}
    (hb : 0 < b) : ∫ z : E, exp (-b * ‖z‖ ^ 2) = (π / b) ^ g := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, hE, ← rpow_natCast]
  congr 1
  push_cast
  ring

theorem isProbabilityMeasure_complexGaussian {g : ℕ} (hE : Module.finrank ℝ E = 2 * g) :
    IsProbabilityMeasure (complexGaussian E g) := by
  constructor
  have h := integral_exp_neg_mul_norm_sq hE one_pos
  have hi := integrable_exp_neg_mul_norm_sq (E := E) one_pos
  simp only [neg_mul, one_mul, div_one] at h hi
  rw [complexGaussian, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) (.of_forall fun z => by positivity),
    integral_const_mul, h, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

theorem integrable_norm_pow_mul_exp_neg_mul_norm_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun z : E => ‖z‖ ^ n * exp (-b * ‖z‖ ^ 2) := by
  rcases subsingleton_or_nontrivial E with h | h
  · exact Integrable.of_finite
  rw [integrable_fun_norm_addHaar volume (f := fun r => r ^ n * exp (-b * r ^ 2))]
  have := integrableOn_rpow_mul_exp_neg_mul_sq hb
    (s := ((Module.finrank ℝ E - 1 + n : ℕ) : ℝ)) (lt_of_lt_of_le neg_one_lt_zero (by positivity))
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [rpow_natCast, smul_eq_mul, pow_add, mul_assoc]

end General

section Combinatorics

end Combinatorics

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Kernel

section Monomials

theorem finrank_real_euclideanSpace_complex (ι : Type*) [Fintype ι] :
    Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  rw [finrank_real_of_complex, finrank_euclideanSpace]

theorem volume_preserving_ofLp_complex (ι : Type*) [Fintype ι] :
    MeasurePreserving (@WithLp.ofLp 2 (ι → ℂ)) := by
  let e : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) := PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => ℂ
  change MeasurePreserving e
  refine ⟨e.continuous.measurable, ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e volume = c • (volume : Measure (ι → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have h1 : ∫ w : ι → ℂ, ∏ i, exp (-1 * ‖w i‖ ^ 2) = π ^ Fintype.card ι := by
    rw [integral_fintype_prod_volume_eq_pow fun w : ℂ => exp (-1 * ‖w‖ ^ 2),
      integral_exp_neg_mul_norm_sq (E := ℂ) (g := 1) (by simp) one_pos]
    simp
  have h2 : ∫ w : ι → ℂ, ∏ i, exp (-1 * ‖w i‖ ^ 2) ∂(Measure.map e volume) =
      π ^ Fintype.card ι := by
    rw [integral_map e.continuous.measurable.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    have := integral_exp_neg_mul_norm_sq (finrank_real_euclideanSpace_complex ι) one_pos
    rw [div_one] at this
    rw [← this]
    refine integral_congr_ae (.of_forall fun z => ?_)
    simp only
    rw [← exp_sum, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    rfl
  rw [hc, integral_smul_nnreal_measure, h1, NNReal.smul_def, smul_eq_mul,
    mul_eq_right₀ (by positivity)] at h2
  rw [hc, show c = 1 by exact_mod_cast h2, one_smul]

end Monomials

section Fin

end Fin

end GlobalTheory
end

section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace GlobalTheory

section OpNorm

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]


theorem norm_dotProduct_mulVec_star_le (A : Matrix n n ℂ) (x : n → ℂ) :
    ‖x ⬝ᵥ A *ᵥ star x‖ ≤ ‖A‖ * ∑ k, ‖x k‖ ^ 2 := by
  set y : EuclideanSpace ℂ n := WithLp.toLp 2 (star x) with hy
  have h := l2_opNorm_mulVec A y
  have h1 := norm_inner_le_norm (𝕜 := ℂ) y ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ y))
  have h2 : ‖y‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := by simp [hy, EuclideanSpace.norm_sq_eq]
  have h3 : inner ℂ y ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ y)) = x ⬝ᵥ A *ᵥ star x := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp [hy]
  rw [← h3, ← h2]
  refine h1.trans ?_
  nlinarith [norm_nonneg y]

end OpNorm

section LogDet

variable {n : Type*} [Fintype n] [DecidableEq n]

end LogDet

section Inertia

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
theorem dotProduct_diagonal_mulVec_star (d x : n → ℂ) :
    x ⬝ᵥ diagonal d *ᵥ star x = ∑ k, d k * ((‖x k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [Complex.star_def]
  ring

theorem le_re_dotProduct_diagonal_add_of_support {j : n → ℂ} (E : Matrix n n ℂ) {x : n → ℂ}
    (hx : ∀ k, x k ≠ 0 → j k = 1) :
    (1 - ‖E‖) * ∑ k, ‖x k‖ ^ 2 ≤ (x ⬝ᵥ (diagonal j + E) *ᵥ star x).re := by
  have h1 : (x ⬝ᵥ diagonal j *ᵥ star x).re = ∑ k, ‖x k‖ ^ 2 := by
    rw [dotProduct_diagonal_mulVec_star, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : x k = 0
    · simp [h]
    · rw [hx k h, one_mul, Complex.ofReal_re]
  have h2 := norm_dotProduct_mulVec_star_le E x
  have h3 := abs_le.1 (Complex.abs_re_le_norm (x ⬝ᵥ E *ᵥ star x))
  rw [add_mulVec, dotProduct_add, Complex.add_re, h1]
  linarith [h3.1]

theorem sum_norm_sq_pos {x : n → ℂ} (hx : x ≠ 0) : 0 < ∑ k, ‖x k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  exact Finset.sum_pos' (fun _ _ => by positivity)
    ⟨k, Finset.mem_univ k, by have : x k ≠ 0 := hk; positivity⟩

theorem re_dotProduct_diagonal_add_pos_of_support {j : n → ℂ} {E : Matrix n n ℂ} (hE : ‖E‖ < 1)
    {x : n → ℂ} (hx0 : x ≠ 0) (hx : ∀ k, x k ≠ 0 → j k = 1) :
    0 < (x ⬝ᵥ (diagonal j + E) *ᵥ star x).re :=
  (mul_pos (by linarith) (sum_norm_sq_pos hx0)).trans_le
    (le_re_dotProduct_diagonal_add_of_support E hx)

theorem posDef_one_add {E : Matrix n n ℂ} (hE : E.IsHermitian) (hE1 : ‖E‖ < 1) :
    (1 + E).PosDef := by
  have hH : (1 + E).IsHermitian := isHermitian_one.add hE
  refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h := re_dotProduct_diagonal_add_pos_of_support (j := fun _ => 1) hE1
    (star_ne_zero.2 hx) fun _ _ => rfl
  rw [star_star, diagonal_one] at h
  rw [Complex.pos_iff]
  exact ⟨h, (hH.im_star_dotProduct_mulVec_self x).symm⟩

end Inertia

section Exp

open NormedSpace

theorem norm_exp_sub_one_sub_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (x : A) : ‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ := by
  have h1 := (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℂ) x)
  have h2 := (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one, one_smul, zero_add,
    ← sub_sub] at h1 h2
  rw [← Real.exp_eq_exp_ℝ] at h2
  refine h1.norm_le_of_bounded h2 fun k => ?_
  rw [norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
  gcongr
  exact norm_pow_le' x (by omega)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Exp

end GlobalTheory
end
