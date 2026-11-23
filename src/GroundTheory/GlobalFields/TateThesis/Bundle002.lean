module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Basic.Real.Sign
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

namespace GroundTheory.Global

open Complex MeasureTheory Set Real
open scoped FourierTransform

noncomputable section

theorem mellin_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {a : ℂ} (ha : 0 < a.re) :
    mellin (fun t : ℝ ↦ ((Real.exp (-(b * t ^ 2)) : ℝ) : ℂ)) a =
      (1 / 2 : ℂ) * (b : ℂ) ^ (-(a / 2)) * Complex.Gamma (a / 2) := by
  have h1 := mellin_comp_rpow (fun u : ℝ ↦ ((Real.exp (-(b * u)) : ℝ) : ℂ)) a 2
  simp only [Real.rpow_two] at h1
  rw [h1, mellin_comp_mul_left (fun u : ℝ ↦ ((Real.exp (-u) : ℝ) : ℂ)) _ hb,
    ← GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral (by simpa using div_pos ha two_pos)]
  simp only [abs_two, ofReal_ofNat, smul_eq_mul]
  ring_nf
  norm_num
  ring

def realGaussian (x : ℝ) : ℂ := Complex.exp (-π * (x : ℂ) ^ 2)

def realGaussianOdd (x : ℝ) : ℂ := (x : ℂ) * Complex.exp (-π * (x : ℂ) ^ 2)

theorem realGaussian_eq_ofReal (x : ℝ) :
    realGaussian x = ((Real.exp (-(π * x ^ 2)) : ℝ) : ℂ) := by
  simp [realGaussian, ofReal_exp]

theorem fourier_realGaussian : 𝓕 realGaussian = realGaussian := by
  have h := fourier_gaussian_pi (b := 1) (by simp)
  simp only [mul_one, one_cpow, div_one, one_mul] at h
  unfold realGaussian
  rw [h]

theorem integrable_realGaussian : Integrable realGaussian := by
  exact integrable_cexp_neg_mul_sq (b := (π : ℂ)) (by simpa using Real.pi_pos)

theorem integrable_realGaussianOdd : Integrable realGaussianOdd := by
  exact integrable_mul_cexp_neg_mul_sq (b := (π : ℂ)) (by simpa using Real.pi_pos)

theorem hasDerivAt_realGaussian (x : ℝ) :
    HasDerivAt realGaussian (-2 * π * x * realGaussian x) x := by
  have h : HasDerivAt (fun y : ℝ ↦ -π * (y : ℂ) ^ 2) (-π * (2 * (x : ℂ))) x := by
    have := ((hasDerivAt_id x).ofReal_comp).pow 2
    simpa using this.const_mul (-(π : ℂ))
  unfold realGaussian
  convert h.cexp using 1
  ring

theorem fourier_realGaussianOdd : 𝓕 realGaussianOdd = fun y ↦ -I * realGaussianOdd y := by
  have hxf : Integrable (fun x : ℝ ↦ x • realGaussian x) := by
    refine integrable_realGaussianOdd.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [realGaussianOdd, realGaussian, Complex.real_smul]
  funext y
  have hd := hasDerivAt_fourier integrable_realGaussian hxf y
  rw [fourier_realGaussian] at hd
  have h2 := (hasDerivAt_realGaussian y).unique hd
  have h3 : 𝓕 (fun x : ℝ ↦ (-2 * π * I * x) • realGaussian x) y =
      (-2 * π * I) * 𝓕 realGaussianOdd y := by
    rw [fourier_real_eq, fourier_real_eq, ← integral_const_mul]
    congr 1; funext x
    simp only [realGaussianOdd, realGaussian, Circle.smul_def, smul_eq_mul]
    ring
  rw [h3] at h2
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : 𝓕 realGaussianOdd y = (-2 * π * y * realGaussian y) / (-2 * π * I) := by
    rw [h2]; field_simp
  rw [this, realGaussianOdd, realGaussian]
  field_simp
  ring_nf
  simp [I_sq]

theorem integral_comp_abs_complex (f : ℝ → ℂ) :
    ∫ x : ℝ, f |x| = 2 * ∫ y in Ioi (0 : ℝ), f y := by
  have h := integral_fun_norm_addHaar (volume : Measure ℝ) f
  simp only [Real.norm_eq_abs] at h
  rw [h]
  simp [Complex.real_smul]

theorem mellin_exp_neg_pi_mul_sq {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ ((Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) s = Gammaℝ s / 2 := by
  rw [mellin_exp_neg_mul_sq Real.pi_pos hs, Gammaℝ_def]
  ring_nf

theorem ofReal_cpow_div_self {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (y : ℂ) ^ s / (y : ℂ) = (y : ℂ) ^ (s - 1) := by
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  rw [cpow_sub _ _ hy', cpow_one]

theorem integral_realGaussian_mul_abs_cpow {s : ℂ} (hs : 0 < s.re) :
    ∫ x : ℝ, realGaussian x * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ) = Gammaℝ s := by
  have h : (fun x : ℝ ↦ realGaussian x * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ)) =
      fun x ↦ (fun y : ℝ ↦ ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ)) |x| := by
    funext x
    simp only [realGaussian_eq_ofReal, sq_abs]
  rw [h, integral_comp_abs_complex
    (fun y : ℝ ↦ ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ))]
  have : ∫ y in Ioi (0 : ℝ), ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ) =
      mellin (fun t : ℝ ↦ ((Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) s := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    rw [mul_div_assoc, ofReal_cpow_div_self hy, smul_eq_mul, mul_comm]
  rw [this, mellin_exp_neg_pi_mul_sq hs]
  ring

theorem integral_realGaussianOdd_mul_sign_mul_abs_cpow {s : ℂ} (hs : -1 < s.re) :
    ∫ x : ℝ, realGaussianOdd x * (Real.sign x : ℂ) * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ) =
      Gammaℝ (s + 1) := by
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have h : (fun x : ℝ ↦ realGaussianOdd x * (Real.sign x : ℂ) * ((|x| : ℝ) : ℂ) ^ s /
        ((|x| : ℝ) : ℂ)) =
      fun x ↦ (fun y : ℝ ↦ (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s /
        (y : ℂ)) |x| := by
    funext x
    have hx : (x : ℂ) * (Real.sign x : ℂ) = ((|x| : ℝ) : ℂ) := by
      rw [← ofReal_mul]
      congr 1
      rcases lt_trichotomy x 0 with h | h | h
      · rw [Real.sign_of_neg h, abs_of_neg h]; ring
      · simp [h]
      · rw [Real.sign_of_pos h, abs_of_pos h]; ring
    rw [realGaussianOdd, ← realGaussian, realGaussian_eq_ofReal]
    simp only [sq_abs]
    rw [← hx]
    ring
  rw [h, integral_comp_abs_complex
    (fun y : ℝ ↦ (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ))]
  have : ∫ y in Ioi (0 : ℝ), (y : ℂ) * ((Real.exp (-(π * y ^ 2)) : ℝ) : ℂ) * (y : ℂ) ^ s / (y : ℂ)
      = mellin (fun t : ℝ ↦ ((Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) (s + 1) := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
    rw [add_sub_cancel_right, smul_eq_mul]
    field_simp
  rw [this, mellin_exp_neg_pi_mul_sq hs1]
  ring

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def mixedTrace : mixedSpace K →ₗ[ℝ] ℝ where
  toFun x := ∑ w, x.1 w + ∑ w, 2 * (x.2 w).re
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.re_ofReal_mul, RingHom.id_apply, Finset.mul_sum, mul_add]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem mixedTrace_apply (x : mixedSpace K) :
    mixedTrace K x = ∑ w, x.1 w + ∑ w, 2 * (x.2 w).re := rfl

theorem mixedTrace_mixedEmbedding (x : K) :
    mixedTrace K (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by
  have h1 : ((Algebra.trace ℚ K x : ℚ) : ℝ) = ∑ φ : K →+* ℂ, (φ x).re := by
    have h := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := x))
    rw [Complex.re_sum] at h
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => (φ x).re)
      (fun σ => (σ x).re) (fun _ => rfl)]
    simpa using h
  have h2 : ∀ φ : K →+* ℂ, (φ x).re = ((mk φ).embedding x).re := by
    intro φ
    rcases embedding_mk_eq φ with h | h <;> rw [h]
    simp [ComplexEmbedding.conjugate_coe_eq]
  have h3 : ∀ w : InfinitePlace K,
      ∑ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => mk φ = w), (φ x).re =
        mult w * (w.embedding x).re := by
    intro w
    rw [Finset.sum_congr rfl (fun φ hφ => by rw [h2, (Finset.mem_filter.mp hφ).2]),
      Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]
  rw [h1, ← Finset.sum_fiberwise Finset.univ (fun φ : K →+* ℂ => mk φ) (fun φ => (φ x).re)]
  simp_rw [h3]
  rw [sum_eq_sum_add_sum, mixedTrace_apply]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isReal, Nat.cast_one, one_mul, mixedEmbedding_apply_isReal,
      ← embedding_of_isReal_apply w.2, Complex.ofReal_re]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isComplex, mixedEmbedding_apply_isComplex]
    norm_num

def mixedTraceForm : LinearMap.BilinForm ℝ (mixedSpace K) :=
  (LinearMap.mul ℝ (mixedSpace K)).compr₂ (mixedTrace K)

theorem mixedTraceForm_apply (x y : mixedSpace K) :
    mixedTraceForm K x y = mixedTrace K (x * y) := rfl

theorem mixedTraceForm_apply' (x y : mixedSpace K) :
    mixedTraceForm K x y = ∑ w, x.1 w * y.1 w + ∑ w, 2 * (x.2 w * y.2 w).re := rfl

theorem mixedTraceForm_comm (x y : mixedSpace K) :
    mixedTraceForm K x y = mixedTraceForm K y x := by
  rw [mixedTraceForm_apply, mixedTraceForm_apply, mul_comm]

theorem mixedTraceForm_mixedEmbedding (a b : K) :
    mixedTraceForm K (mixedEmbedding K a) (mixedEmbedding K b) = (Algebra.trace ℚ K (a * b) : ℝ) := by
  rw [mixedTraceForm_apply, ← map_mul, mixedTrace_mixedEmbedding]

theorem mixedTraceForm_separatingLeft : (mixedTraceForm K).SeparatingLeft := by
  intro x hx
  have h := hx (x.1, fun w => conj (x.2 w))
  rw [mixedTraceForm_apply'] at h
  simp only [Complex.mul_conj, Complex.ofReal_re] at h
  have h1 : 0 ≤ ∑ w, x.1 w * x.1 w := Finset.sum_nonneg fun w _ => mul_self_nonneg _
  have h2 : 0 ≤ ∑ w, 2 * Complex.normSq (x.2 w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg _)
  have e1 : ∑ w, x.1 w * x.1 w = 0 := by linarith
  have e2 : ∑ w, 2 * Complex.normSq (x.2 w) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun w _ => mul_self_nonneg _)] at e1
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg _))] at e2
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · simpa using e1 w (Finset.mem_univ _)
  · simpa using e2 w (Finset.mem_univ _)

theorem mixedTraceForm_nondegenerate : (mixedTraceForm K).Nondegenerate :=
  ⟨mixedTraceForm_separatingLeft K, fun y hy =>
    mixedTraceForm_separatingLeft K y fun x => by rw [mixedTraceForm_comm]; exact hy x⟩

end

end GroundTheory.Global
end
