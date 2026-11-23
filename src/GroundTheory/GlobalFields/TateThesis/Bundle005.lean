module

public import GroundTheory.GlobalFields.TateThesis.Bundle003
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Real.Sign
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import GroundTheory.GlobalFields.TateThesis.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ENNReal nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

theorem coe_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

theorem coeToSubmodule_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
      Submodule.traceDual ℤ ℚ (I : Submodule (𝓞 K) K) :=
  FractionalIdeal.coe_dual ℤ ℚ I.ne_zero

theorem traceDualIdeal_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) =
      ((I : FractionalIdeal (𝓞 K)⁰ K) *
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [coe_traceDualIdeal, FractionalIdeal.dual_eq_mul_inv,
    coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K), mul_inv, inv_inv, mul_comm]

theorem dualSubmodule_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (mixedTraceForm K).dualSubmodule (idealLattice K I) = idealLattice K (traceDualIdeal K I) := by
  set b := basisOfFractionalIdeal K I
  have hdual : (mixedTraceForm K).dualBasis (mixedTraceForm_nondegenerate K)
      (fractionalIdealLatticeBasis K I) = fun i => mixedEmbedding K (b.traceDual i) := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro i j
    rw [fractionalIdealLatticeBasis_apply, mixedTraceForm_mixedEmbedding,
      Module.Basis.trace_traceDual_mul]
    split_ifs <;> simp
  have hspan : (Submodule.traceDual ℤ ℚ (I : Submodule (𝓞 K) K)).restrictScalars ℤ =
      Submodule.span ℤ (Set.range b.traceDual) :=
    Submodule.traceDual_span_of_basis ℤ (I : Submodule (𝓞 K) K) b (by
      ext x
      rw [Submodule.restrictScalars_mem, mem_span_basisOfFractionalIdeal]
      rfl)
  ext y
  rw [← span_idealLatticeBasis, LinearMap.BilinForm.dualSubmodule_span_of_basis _
    (mixedTraceForm_nondegenerate K), hdual, mem_idealLattice,
    show Set.range (fun i => mixedEmbedding K (b.traceDual i)) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' Set.range b.traceDual by
        rw [← Set.range_comp]; rfl,
    ← Submodule.map_span, Submodule.mem_map, ← hspan]
  simp only [Submodule.restrictScalars_mem, ← coeToSubmodule_traceDualIdeal]
  rfl

theorem mem_idealLattice_traceDualIdeal_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedSpace K) :
    y ∈ idealLattice K (traceDualIdeal K I) ↔
      ∀ x ∈ idealLattice K I, ∃ n : ℤ, mixedTraceForm K y x = n := by
  rw [← dualSubmodule_idealLattice, LinearMap.BilinForm.mem_dualSubmodule]
  simp only [Submodule.mem_one, algebraMap_int_eq, eq_intCast]
  exact forall₂_congr fun _ _ => exists_congr fun _ => eq_comm

theorem covolume_idealLattice_selfDualMeasure (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (idealLattice K I) (selfDualMeasure K) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|(discr K : ℝ)| := by
  have h := covolume_idealLattice K I
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice K I)]
    at h
  have hF : IsAddFundamentalDomain (idealLattice K I)
      (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K I)) (selfDualMeasure K) :=
    (fundamentalDomain_idealLattice K I).mono Measure.smul_absolutelyContinuous
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF, selfDualMeasure, measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ← measureReal_def, h, ENNReal.toReal_pow, ENNReal.toReal_ofNat, inv_pow]
  field_simp

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open _root_.Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform

noncomputable section

theorem complexFourier_mul_self {f : ℂ → ℂ} (hf : Integrable f complexPlaceMeasure)
    (hf' : Integrable (fun z ↦ ‖z‖ * ‖f z‖) complexPlaceMeasure) {w : ℂ} {D : ℂ →L[ℝ] ℂ}
    (hD : HasFDerivAt (complexFourier f) D w) :
    -4 * π * I * complexFourier (fun z ↦ z * f z) w = D 1 - I * D I := by
  have h := VectorFourier.hasFDerivAt_fourierIntegral traceFormℂ hf hf' w
  rw [← complexFourier_eq_fourierIntegral] at h
  rw [hD.unique h]
  have hint : Integrable (fun z ↦ VectorFourier.fourierSMulRight traceFormℂ f z)
      complexPlaceMeasure := by
    refine ((hf'.const_mul (2 * π * ‖traceFormℂ‖))).mono' hf.1.fourierSMulRight ?_
    refine Filter.Eventually.of_forall fun z ↦ ?_
    have := VectorFourier.norm_fourierSMulRight_le traceFormℂ f z
    simpa [mul_assoc] using this
  rw [fourierIntegral_continuousLinearMap_apply' hint,
    fourierIntegral_continuousLinearMap_apply' hint]
  have hL : ∀ v : ℂ, traceFormℂ.toLinearMap₁₂ v w = 2 * (v * w).re :=
    fun v ↦ traceFormℂ_apply v w
  simp only [VectorFourier.fourierIntegral, VectorFourier.fourierSMulRight_apply, hL,
    traceFormℂ_apply]
  have i1 : ∀ h : ℂ, Integrable (fun z ↦ 𝐞 (-(2 * (z * w).re)) •
      (-(2 * π * I) • (2 * (z * h).re) • f z)) complexPlaceMeasure := by
    intro h
    have : Integrable (fun z ↦ (-(2 * π * I) • (2 * (z * h).re) • f z)) complexPlaceMeasure := by
      have := (hint.apply_continuousLinearMap h)
      simpa [VectorFourier.fourierSMulRight_apply] using this
    have := (fourierIntegral_convergent_iff' (μ := complexPlaceMeasure) traceFormℂ w).2 this
    simpa using this
  rw [← integral_const_mul, ← integral_sub (i1 1) ((i1 I).const_mul I), complexFourier,
    ← integral_const_mul]
  congr 1
  funext z
  simp only [Circle.smul_def, smul_eq_mul, Complex.real_smul, mul_I_re]
  push_cast
  have hz : (z : ℂ) = z.re + z.im * I := (re_add_im z).symm
  linear_combination (norm := skip) (-4 * π * I * (𝐞 (-(2 * (z * w).re)) : ℂ) * f z) * hz
  ring_nf

theorem cexp_neg_two_pi_norm_sq (w : ℂ) :
    Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2) = Complex.exp (-2 * π * (w * conj w)) := by
  congr 2
  rw [mul_conj, normSq_eq_norm_sq]
  push_cast
  ring

theorem exists_hasFDerivAt_conj_pow_mul_gaussian (n : ℕ) (w : ℂ) :
    ∃ D : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun w : ℂ ↦ conj w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) D w ∧
      D 1 - I * D I = -4 * π * (conj w ^ (n + 1) * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  simp only [cexp_neg_two_pi_norm_sq]
  have hc : HasFDerivAt (fun w : ℂ ↦ conj w) (conjCLE : ℂ →L[ℝ] ℂ) w :=
    (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
  have hid : HasFDerivAt (fun w : ℂ ↦ w) (ContinuousLinearMap.id ℝ ℂ) w := hasFDerivAt_id w
  have hq := (hid.fun_mul hc).const_mul (-2 * π : ℂ)
  have hexp := hq.cexp
  have hp := hc.pow n
  refine ⟨_, hp.fun_mul hexp, ?_⟩
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_id', id, ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_one,
    conj_I, smul_eq_mul, nsmul_eq_mul]
  rw [pow_succ]
  linear_combination (conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * (-2 * π) * (-w) +
    Complex.exp (-2 * π * (w * conj w)) * (n * conj w ^ (n - 1)) +
    2 * conj w * conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * π -
    4 * conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * π * w) * I_sq

theorem complexGaussian_natCast (n : ℕ) :
    complexGaussian n = fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  funext z
  simp [complexGaussian]

theorem complexGaussian_neg_natCast (n : ℕ) :
    complexGaussian (-(n : ℤ)) = fun z ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  funext z
  rw [complexGaussian]
  split_ifs with h
  · have : n = 0 := by omega
    subst this; simp
  · simp

theorem complexFourier_pow_mul_gaussian (n : ℕ) :
    complexFourier (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun w ↦ (-I) ^ n * (conj w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  induction n with
  | zero =>
    have h := complexFourier_complexGaussian_zero
    simp only [funext complexGaussian_zero] at h
    simpa using h
  | succ n ih =>
    funext w
    obtain ⟨D, hD, hD1⟩ := exists_hasFDerivAt_conj_pow_mul_gaussian n w
    have hF : HasFDerivAt (complexFourier (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)))
        ((-I) ^ n • D) w := by
      rw [ih]; exact hD.const_mul _
    have hf : Integrable (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2))
        complexPlaceMeasure := by
      simpa [complexGaussian_natCast] using integrable_complexGaussian n
    have hf' : Integrable (fun z ↦ ‖z‖ * ‖z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)‖)
        complexPlaceMeasure := by
      have := (integrable_norm_pow_smul_complexGaussian' n 1).norm
      refine this.congr (Filter.Eventually.of_forall fun z ↦ ?_)
      simp [complexGaussian_natCast]
    have key := complexFourier_mul_self hf hf' hF
    have e : (fun z : ℂ ↦ z * (z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2))) =
        fun z ↦ z ^ (n + 1) * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
      funext z; ring
    rw [e] at key
    have hne : (-4 * π * I : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      simp [this, I_ne_zero]
    apply mul_left_cancel₀ hne
    rw [key]
    simp only [smul_apply, smul_eq_mul]
    have hD1' : (-I) ^ n * D 1 - I * ((-I) ^ n * D I) = (-I) ^ n * (D 1 - I * D I) := by ring
    rw [hD1', hD1]
    rw [pow_succ]
    linear_combination (-4 * π * (-I) ^ n * (conj w ^ (n + 1) *
      Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2))) * I_sq

theorem complexFourier_conj (f : ℂ → ℂ) (w : ℂ) :
    complexFourier (fun z ↦ conj (f z)) w = conj (complexFourier f (-w)) := by
  rw [complexFourier, complexFourier, ← integral_conj]
  congr 1
  funext z
  simp [Circle.smul_def, Real.fourierChar_apply, ← exp_conj, map_ofNat, neg_re, neg_im,
    mul_re, ofReal_sub, ofReal_mul]
  congr 2 <;> try ring <;> simp

theorem conj_cexp_neg_two_pi_norm_sq (z : ℂ) :
    conj (Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) = Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  rw [← exp_conj]
  simp [map_mul, conj_ofReal, map_ofNat]

theorem complexFourier_conj_pow_mul_gaussian (n : ℕ) :
    complexFourier (fun z ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun w ↦ (-I) ^ n * (w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  funext w
  have e : (fun z : ℂ ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun z ↦ conj (z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) := by
    funext z
    rw [map_mul, map_pow, conj_cexp_neg_two_pi_norm_sq]
  rw [e, complexFourier_conj, complexFourier_pow_mul_gaussian]
  simp only [map_mul, map_pow, map_neg, conj_I, conj_conj, conj_cexp_neg_two_pi_norm_sq,
    norm_neg]
  ring

theorem complexFourier_complexGaussian (m : ℤ) :
    complexFourier (complexGaussian m) = fun w ↦ (-I) ^ m.natAbs * complexGaussian (-m) w := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [complexGaussian_natCast, complexFourier_pow_mul_gaussian, complexGaussian_neg_natCast]
    simp
  · rw [complexGaussian_neg_natCast, complexFourier_conj_pow_mul_gaussian, neg_neg,
      complexGaussian_natCast]
    simp

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open _root_.Complex

theorem re_eq_zero_of_norm_exp_one_cpow {s : ℂ}
    (h : ‖((Real.exp 1 : ℝ) : ℂ) ^ s‖ = 1) : s.re = 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos 1), Real.exp_one_rpow] at h
  exact Real.exp_eq_one_iff _ |>.mp h

theorem existsUnique_mul_I_of_re_eq_zero {P : ℂ → Prop} (h : ∃! s, P s)
    (hre : ∀ s, P s → s.re = 0) : ∃! τ : ℝ, P ((τ : ℂ) * I) := by
  obtain ⟨s, hs, hu⟩ := h
  have hs' : s = (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre s hs]
  refine ⟨s.im, by show P ((s.im : ℂ) * I); rw [← hs']; exact hs, fun τ hτ => ?_⟩
  have := congrArg Complex.im (hu _ hτ)
  simpa using this

theorem existsUnique_prod_mul_I_of_re_eq_zero {α : Type*} {P : α × ℂ → Prop}
    (h : ∃! p, P p) (hre : ∀ p, P p → p.2.re = 0) :
    ∃! q : α × ℝ, P (q.1, (q.2 : ℂ) * I) := by
  obtain ⟨p, hp, hu⟩ := h
  have hp' : p = (p.1, (p.2.im : ℂ) * I) := by
    refine Prod.ext rfl ?_
    apply Complex.ext <;> simp [hre p hp]
  refine ⟨(p.1, p.2.im), by show P (p.1, (p.2.im : ℂ) * I); rw [← hp']; exact hp,
    fun q hq => ?_⟩
  have := hu _ hq
  refine Prod.ext ?_ ?_
  · simpa using congrArg Prod.fst this
  · simpa using congrArg (fun r : α × ℂ => r.2.im) this

theorem existsUnique_cpow_of_pos_circle (χ : {x : ℝ // 0 < x} →ₜ* Circle) :
    ∃! τ : ℝ, ∀ x : {x : ℝ // 0 < x}, (χ x : ℂ) = ((x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  apply existsUnique_mul_I_of_re_eq_zero (existsUnique_cpow_of_pos (circleToUnits.comp χ))
  intro s hs
  apply re_eq_zero_of_norm_exp_one_cpow
  have h : (χ ⟨Real.exp 1, Real.exp_pos 1⟩ : ℂ) = ((Real.exp 1 : ℝ) : ℂ) ^ s :=
    hs ⟨Real.exp 1, Real.exp_pos 1⟩
  rw [← h, Circle.norm_coe]

theorem existsUnique_realUnits_circle (χ : ℝˣ →ₜ* Circle) :
    ∃! p : Fin 2 × ℝ, ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  apply existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : Fin 2 × ℂ => ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ p.2)
    (existsUnique_realUnits (circleToUnits.comp χ))
  intro p hp
  apply re_eq_zero_of_norm_exp_one_cpow
  have h := hp (Units.mk0 (Real.exp 1) (Real.exp_pos 1).ne')
  simp only [Units.val_mk0, Real.sign_of_pos (Real.exp_pos 1), abs_of_pos (Real.exp_pos 1),
    Complex.ofReal_one, one_pow, one_mul] at h
  rw [← h, Circle.norm_coe]

theorem existsUnique_complexUnits_circle (χ : ℂˣ →ₜ* Circle) :
    ∃! p : ℤ × ℝ, ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  apply existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : ℤ × ℂ => ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ p.2)
    (existsUnique_complexUnits (circleToUnits.comp χ))
  intro p hp
  apply re_eq_zero_of_norm_exp_one_cpow
  have hne : ((Real.exp 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos 1).ne'
  have h := hp (Units.mk0 _ hne)
  rw [Units.val_mk0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1),
    div_self hne, one_zpow, one_mul] at h
  rw [← h, Circle.norm_coe]

theorem existsUnique_addChar_real_units (χ : AddChar ℝ ℂˣ) (hχ : Continuous χ) :
    ∃! s : ℂ, ∀ t : ℝ, (χ t : ℂ) = Complex.exp (s * t) :=
  existsUnique_exp_of_continuous χ hχ χ.map_add_eq_mul

end GroundTheory.Global
end
