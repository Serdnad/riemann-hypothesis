module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Real.Sign
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import GroundTheory.GlobalFields.TateThesis.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GroundTheory.Global

open _root_.Complex

theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (u : ℂ) :
    (r : ℂ) ^ u = Complex.exp (u * (Real.log r : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le,
    mul_comm]

theorem existsUnique_cpow_of_pos (χ : {x : ℝ // 0 < x} →ₜ* ℂˣ) :
    ∃! s : ℂ, ∀ x : {x : ℝ // 0 < x}, (χ x : ℂ) = ((x : ℝ) : ℂ) ^ s := by
  let e : ℝ → {x : ℝ // 0 < x} := fun t => ⟨Real.exp t, Real.exp_pos t⟩
  have econt : Continuous e := Real.continuous_exp.subtype_mk _
  have hlog : ∀ x : {x : ℝ // 0 < x}, e (Real.log x) = x :=
    fun x => Subtype.ext (Real.exp_log x.2)
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Subtype.ext (Real.exp_add a b))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs
  refine ⟨s, fun x => ?_, fun s' h' => eq_of_forall_exp_mul_eq fun t => ?_⟩
  · rw [ofReal_cpow_eq_exp x.2, ← hs', hlog]
  · have h1 := h' (e t)
    rw [ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
    rw [← h1, hs']

theorem existsUnique_realUnits (χ : ℝˣ →ₜ* ℂˣ) :
    ∃! p : Fin 2 × ℂ, ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ p.2 := by
  let e : ℝ → ℝˣ := fun t => Units.mk0 (Real.exp t) (Real.exp_pos t).ne'
  have econt : Continuous e := Units.isEmbedding_val₀.continuous_iff.mpr Real.continuous_exp
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Units.ext (Real.exp_add a b))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs
  have hpos : ∀ (r : ℝ) (hr : 0 < r), (χ (Units.mk0 r hr.ne') : ℂ) = (r : ℂ) ^ s := by
    intro r hr
    have : Units.mk0 r hr.ne' = e (Real.log r) := Units.ext (Real.exp_log hr).symm
    rw [this, hs', ofReal_cpow_eq_exp hr]

  set c : ℂ := (χ (-1) : ℂ) with hc
  have hcc : c * c = 1 := by
    rw [hc, ← Units.val_mul, ← map_mul]
    simp
  let a : Fin 2 := if c = 1 then 0 else 1
  have ha : c = (-1 : ℂ) ^ (a : ℕ) := by
    rcases mul_self_eq_one_iff.mp hcc with h | h
    · simp [a, h]
    · have hne : (-1 : ℂ) ≠ 1 := by norm_num
      simp [a, h, hne]
  have hneg1 : ∀ x : ℝˣ, x = -1 * Units.mk0 (-(x : ℝ)) (neg_ne_zero.mpr x.ne_zero) := by
    intro x
    ext
    simp
  refine ⟨(a, s), fun x => ?_, ?_⟩
  · rcases lt_or_gt_of_ne x.ne_zero with hx | hx
    · conv_lhs => rw [hneg1 x]
      rw [map_mul, Units.val_mul, ← hc, hpos _ (neg_pos.mpr hx), ha, Real.sign_of_neg hx, abs_of_neg hx]
      push_cast
      ring
    · have : x = Units.mk0 (x : ℝ) hx.ne' := by ext; simp
      conv_lhs => rw [this]
      rw [hpos _ hx, Real.sign_of_pos hx, abs_of_pos hx]
      simp
  · rintro ⟨a', s'⟩ h'
    have hs's : s' = s := eq_of_forall_exp_mul_eq fun t => by
      have h1 := h' (e t)
      have he : ((e t : ℝˣ) : ℝ) = Real.exp t := rfl
      rw [he, Real.sign_of_pos (Real.exp_pos t), abs_of_pos (Real.exp_pos t),
        ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
      simp only [Complex.ofReal_one, one_pow, one_mul] at h1
      rw [← h1, hs']
    have ha' : (-1 : ℂ) ^ (a' : ℕ) = (-1 : ℂ) ^ (a : ℕ) := by
      have h1 := h' (-1)
      simp only [Units.val_neg, Units.val_one, abs_neg, abs_one, Complex.ofReal_one,
        Complex.one_cpow, mul_one, Real.sign_of_neg (show (-1 : ℝ) < 0 by norm_num)] at h1
      rw [← ha, hc, h1]
      push_cast
      ring
    have haa : a' = a := by
      revert ha'
      generalize a = b
      fin_cases a' <;> fin_cases b <;> norm_num
    simp [haa, hs's]

theorem existsUnique_circle_zpow (χ : Circle →ₜ* ℂˣ) :
    ∃! m : ℤ, ∀ z : Circle, (χ z : ℂ) = (z : ℂ) ^ m := by
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (Circle.exp t))
    (χ.continuous.comp Circle.exp.continuous)
    (fun a b => by simp only [Circle.exp_add, map_mul])
  have hs' : ∀ t : ℝ, (χ (Circle.exp t) : ℂ) = Complex.exp (s * t) := hs

  obtain ⟨n, hn⟩ : ∃ n : ℤ, s = n * I := by
    have h1 : Complex.exp (s * (2 * Real.pi : ℝ)) = 1 := by
      rw [← hs', Circle.exp_two_pi, map_one, Units.val_one]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    refine ⟨n, ?_⟩
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  have hval : ∀ t : ℝ, (χ (Circle.exp t) : ℂ) = (Circle.exp t : ℂ) ^ n := by
    intro t
    rw [hs', Circle.coe_exp, ← Complex.exp_int_mul, hn]
    congr 1
    ring
  refine ⟨n, fun z => ?_, fun m hm => ?_⟩
  · rw [← Circle.exp_arg z, hval]
  · have hmn : (m : ℂ) * I = n * I := eq_of_forall_exp_mul_eq fun t => by
      have h1 := hm (Circle.exp t)
      rw [hval, Circle.coe_exp, ← Complex.exp_int_mul, ← Complex.exp_int_mul] at h1
      calc Complex.exp (m * I * t) = Complex.exp (m * (t * I)) := by ring_nf
        _ = Complex.exp (n * (t * I)) := h1.symm
        _ = Complex.exp (n * I * t) := by ring_nf
    exact_mod_cast mul_right_cancel₀ I_ne_zero hmn

noncomputable def circleToUnits : Circle →ₜ* ℂˣ where
  toMonoidHom := Circle.toUnits
  continuous_toFun :=
    Units.isEmbedding_val₀.continuous_iff.mpr (continuous_subtype_val.congr fun _ => rfl)

@[simp] theorem coe_circleToUnits (z : Circle) : ((circleToUnits z : ℂˣ) : ℂ) = z := rfl

theorem existsUnique_complexUnits (χ : ℂˣ →ₜ* ℂˣ) :
    ∃! p : ℤ × ℂ, ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ p.2 := by

  let e : ℝ → ℂˣ := fun t => Units.mk0 (Real.exp t : ℂ) (by exact_mod_cast (Real.exp_pos t).ne')
  have econt : Continuous e :=
    Units.isEmbedding_val₀.continuous_iff.mpr (Complex.continuous_ofReal.comp Real.continuous_exp)
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Units.ext (by simp [e, Complex.exp_add]))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs

  obtain ⟨n, hn, hnu⟩ := existsUnique_circle_zpow (χ.comp circleToUnits)
  have hn' : ∀ w : Circle, (χ (circleToUnits w) : ℂ) = (w : ℂ) ^ n := hn
  have hnorm : ∀ z : ℂˣ, 0 < ‖(z : ℂ)‖ := fun z => norm_pos_iff.mpr z.ne_zero
  refine ⟨(n, s), fun z => ?_, ?_⟩
  · have hz : z = e (Real.log ‖(z : ℂ)‖) * circleToUnits (Circle.exp (Complex.arg z)) := by
      ext
      rw [Units.val_mul, coe_circleToUnits, Circle.coe_exp]
      show (z : ℂ) = (Real.exp (Real.log ‖(z : ℂ)‖) : ℂ) * _
      rw [Real.exp_log (hnorm z), Complex.norm_mul_exp_arg_mul_I]
    have hw : (Circle.exp (Complex.arg z) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := by
      rw [Circle.coe_exp, eq_div_iff (by exact_mod_cast (hnorm z).ne'), mul_comm,
        Complex.norm_mul_exp_arg_mul_I]
    conv_lhs => rw [hz]
    rw [map_mul, Units.val_mul, hs', hn', hw, ofReal_cpow_eq_exp (hnorm z), mul_comm]
  · rintro ⟨m, s'⟩ h'
    have hs's : s' = s := eq_of_forall_exp_mul_eq fun t => by
      have h1 := h' (e t)
      have he : ((e t : ℂˣ) : ℂ) = (Real.exp t : ℂ) := rfl
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t),
        div_self (by exact_mod_cast (Real.exp_pos t).ne'), one_zpow, one_mul,
        ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
      rw [← h1, hs']
    have hmn : m = n := hnu m fun w => by
      have h1 := h' (circleToUnits w)
      rw [coe_circleToUnits, Circle.norm_coe] at h1
      simpa using h1
    simp [hmn, hs's]

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open _root_.Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform ENNReal

noncomputable section

def traceFormℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).comp (ContinuousLinearMap.mul ℝ ℂ)

@[simp] theorem traceFormℂ_apply (z w : ℂ) : traceFormℂ z w = 2 * (z * w).re := by
  simp [traceFormℂ]

def complexPlaceMeasure : Measure ℂ := (2 : ℝ≥0∞) • volume

def complexFourier (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ z, 𝐞 (-(2 * (z * w).re)) • f z ∂complexPlaceMeasure

theorem complexFourier_eq_fourierIntegral (f : ℂ → ℂ) :
    complexFourier f =
      VectorFourier.fourierIntegral 𝐞 complexPlaceMeasure traceFormℂ.toLinearMap₁₂ f := by
  funext w
  simp [complexFourier, VectorFourier.fourierIntegral]

def complexGaussian (m : ℤ) (z : ℂ) : ℂ :=
  (if 0 ≤ m then z ^ m.natAbs else conj z ^ m.natAbs) * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)

theorem complexGaussian_zero (z : ℂ) :
    complexGaussian 0 z = Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  simp [complexGaussian]

theorem complexFourier_eq_two_mul_fourier (f : ℂ → ℂ) (w : ℂ) :
    complexFourier f w = 2 * 𝓕 f (2 * conj w) := by
  rw [complexFourier, complexPlaceMeasure, integral_smul_measure, fourier_eq]
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, ofReal_ofNat]
  congr 2
  funext z
  congr 3
  rw [Complex.inner]
  simp [Complex.mul_re]
  ring

theorem complexFourier_complexGaussian_zero :
    complexFourier (complexGaussian 0) = complexGaussian 0 := by
  funext w
  rw [complexFourier_eq_two_mul_fourier]
  have hb : 0 < ((2 * π : ℝ) : ℂ).re := by simp [Real.pi_pos]
  have h := fourier_gaussian_innerProductSpace (V := ℂ) hb (2 * conj w)
  have e : complexGaussian 0 = fun v : ℂ ↦ Complex.exp (-((2 * π : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v; rw [complexGaussian_zero]; push_cast; ring_nf
  rw [e, h, Complex.finrank_real_complex]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : ‖2 * conj w‖ = 2 * ‖w‖ := by simp
  rw [hn]
  have h1 : ((π : ℂ) / ((2 * π : ℝ) : ℂ)) ^ (((2 : ℕ) : ℂ) / 2) = 1 / 2 := by
    have : ((2 : ℕ) : ℂ) / 2 = 1 := by norm_num
    rw [this, cpow_one]; push_cast; field_simp
  rw [h1]
  push_cast
  rw [← mul_assoc, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_mul]
  congr 1
  field_simp

theorem integrable_norm_pow_mul_exp_neg_two_pi_mul_sq (k : ℕ) :
    Integrable (fun z : ℂ ↦ ‖z‖ ^ k * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
  have h := (integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun y : ℝ ↦ y ^ k * Real.exp (-(2 * π) * y ^ 2))).2
  refine h ?_
  rw [Complex.finrank_real_complex]
  have h2 := integrableOn_rpow_mul_exp_neg_mul_sq (b := 2 * π) (by positivity)
    (s := ((k + 1 : ℕ) : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) (k + 1); linarith)
  refine h2.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, smul_eq_mul]
  ring

theorem integrable_norm_pow_smul_complexGaussian (m : ℤ) (k : ℕ) :
    Integrable (fun z : ℂ ↦ (‖z‖ ^ k : ℝ) • complexGaussian m z) := by
  refine (integrable_norm_pow_mul_exp_neg_two_pi_mul_sq (k + m.natAbs)).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    unfold complexGaussian
    split_ifs <;> fun_prop
  · refine Filter.Eventually.of_forall fun z ↦ ?_
    rw [norm_smul, complexGaussian, norm_mul, norm_exp]
    have : (-2 * π * (‖z‖ : ℂ) ^ 2).re = -(2 * π) * ‖z‖ ^ 2 := by
      rw [← ofReal_pow, ← ofReal_ofNat, ← ofReal_neg, ← ofReal_mul, ← ofReal_mul, ofReal_re]
      ring
    rw [this]
    split_ifs <;> simp [pow_add, mul_assoc]

theorem integrable_norm_pow_smul_complexGaussian' (m : ℤ) (k : ℕ) :
    Integrable (fun z : ℂ ↦ (‖z‖ ^ k : ℝ) • complexGaussian m z) complexPlaceMeasure :=
  (integrable_norm_pow_smul_complexGaussian m k).smul_measure (by simp)

theorem integrable_complexGaussian (m : ℤ) :
    Integrable (complexGaussian m) complexPlaceMeasure := by
  simpa using integrable_norm_pow_smul_complexGaussian' m 0

theorem complexGaussian_mul_zpow {z : ℂ} (hz : z ≠ 0) (m : ℤ) :
    complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) =
      (‖z‖ : ℂ) ^ m.natAbs * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
  rw [complexGaussian]
  split_ifs with hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    simp only [Int.natAbs_natCast, zpow_neg, zpow_natCast, div_pow]
    field_simp
  · obtain ⟨n, hn'⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    subst hn'
    simp only [Int.natAbs_neg, Int.natAbs_natCast, neg_neg, zpow_natCast, div_pow]
    have hc : conj z * z = (‖z‖ : ℂ) ^ 2 := by
      rw [mul_comm, mul_conj, normSq_eq_norm_sq]; push_cast; ring
    have : conj z ^ n * z ^ n = (‖z‖ : ℂ) ^ n * (‖z‖ : ℂ) ^ n := by
      rw [← mul_pow, hc, ← pow_mul, ← pow_add]; ring_nf
    field_simp
    linear_combination this

theorem integral_comp_norm_complexPlaceMeasure (f : ℝ → ℂ) :
    ∫ z, f ‖z‖ ∂complexPlaceMeasure = 4 * π * ∫ y in Ioi (0 : ℝ), (y : ℂ) * f y := by
  rw [complexPlaceMeasure, integral_smul_measure, integral_fun_norm_addHaar volume f,
    Complex.finrank_real_complex]
  have hb : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  rw [hb]
  simp only [ENNReal.toReal_ofNat, pow_one, Complex.real_smul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.add_one_sub_one]
  push_cast
  ring

theorem integral_complexGaussian_mul_zpow_mul_cpow (m : ℤ) {s : ℂ}
    (hs : 0 < s.re + m.natAbs / 2) :
    ∫ z, complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s /
        ((‖z‖ ^ 2 : ℝ) : ℂ) ∂complexPlaceMeasure =
      π * Gammaℂ (s + m.natAbs / 2) := by
  set n := m.natAbs with hn
  have h : (fun z : ℂ ↦ complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) *
        ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s / ((‖z‖ ^ 2 : ℝ) : ℂ)) =
      fun z ↦ (fun y : ℝ ↦ (y : ℂ) ^ n * ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) *
        ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ)) ‖z‖ := by
    funext z
    by_cases hz : z = 0
    · subst hz; simp
    · simp only
      rw [complexGaussian_mul_zpow hz, ofReal_exp, ← hn]
      push_cast
      ring_nf
  rw [h, integral_comp_norm_complexPlaceMeasure (fun y : ℝ ↦ (y : ℂ) ^ n *
    ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) * ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ))]
  have ha : 0 < (2 * s + n).re := by simp; linarith
  have : ∫ y in Ioi (0 : ℝ), (y : ℂ) * ((y : ℂ) ^ n * ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) *
        ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ)) =
      mellin (fun t : ℝ ↦ ((Real.exp (-(2 * π * t ^ 2)) : ℝ) : ℂ)) (2 * s + n) := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
    have e1 : ((y ^ 2 : ℝ) : ℂ) ^ s = (y : ℂ) ^ (((2 : ℝ) : ℂ) * s) := by
      rw [cpow_mul_ofReal_nonneg (le_of_lt hy), Real.rpow_two]
    have e2 : (y : ℂ) ^ (2 * s + n - 1) = (y : ℂ) ^ (((2 : ℝ) : ℂ) * s) * (y : ℂ) ^ n / y := by
      rw [cpow_sub _ _ hy0, cpow_add _ _ hy0, cpow_natCast, cpow_one]; push_cast; ring
    rw [e1, e2, smul_eq_mul]
    push_cast
    field_simp
  rw [this, mellin_exp_neg_mul_sq (by positivity) ha, Gammaℂ_def]
  have e3 : (2 * s + n) / 2 = s + n / 2 := by ring
  rw [e3]
  push_cast
  ring

end

end GroundTheory.Global
end
