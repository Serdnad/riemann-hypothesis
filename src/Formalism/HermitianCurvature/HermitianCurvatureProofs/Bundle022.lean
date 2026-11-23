module

public import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AddedBlockKernelSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelExplicitFormula
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle021
public import Formalism.HermitianCurvature.StatementG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CuspidalIrreducibleSubrep
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EtaleIntegralityFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle017
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitTailEstimates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionCriticalPoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionDerivatives
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardCharacterExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StationaryPhaseEstimates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StationaryPhaseModel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakApproximationGL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WhittakerVanishingImpliesZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts
public import Formalism.HermitianCurvature.StatementWd
public import Mathlib.CategoryTheory.Category.Basic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle015
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QEFirstMulSecondEqSwap
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CharacterOrthogonalityDual
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P

theorem second_gram_property : Formalism.FourierDecayAlt.A5.BlockKernelPosSemidef := second_gram_of_gram_and_modulus kernel_gram_property modulus_positive_multiplicative

namespace FirstKernelProperties

theorem first_kernel_periodic_gram_parseval :
    Formalism.FourierDecayAlt.A5.SingleBlockPeriodic ∧ Formalism.FourierDecayAlt.A5.SingleBlockPosSemidef ∧ Formalism.FourierDecayAlt.A5.SingleBlockParseval :=
  first_kernel_properties_of_hypotheses first_kernel_explicit_formula integral_points_finite characterOrthogonalityDual
    characterOrthogonality cokernel_card_inverse_modulus second_gram_property

end FirstKernelProperties

theorem first_kernel_periodic : Formalism.FourierDecayAlt.A5.SingleBlockPeriodic := A5x6.first_kernel_periodic_of_formula first_kernel_explicit_formula

theorem first_kernel_gram_property : Formalism.FourierDecayAlt.A5.SingleBlockPosSemidef := A5x6.first_kernel_gram_of_second second_gram_property

theorem first_kernel_parseval : Formalism.FourierDecayAlt.A5.SingleBlockParseval := FirstKernelProperties.first_kernel_periodic_gram_parseval.2.2

namespace FirstKernelProperties

end FirstKernelProperties

theorem first_theta_kernel_equality : Formalism.FourierDecayAlt.A5.Th1Eq := A5x6.first_theta_eq_of_equality (A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval
    added_block_kernel_support added_block_kernel_block_diagonal)

theorem first_theta_equals_first_kernel : Formalism.FourierDecayAlt.A5.SingleBlockThetaProps := A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval
    added_block_kernel_support added_block_kernel_block_diagonal

end Formalism.FourierDecayAlt.P
end

section

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def ug (TT : ℝ) (α : ℂ → ℂ) (s : Bool) (z : ℂ) : ℂ := Complex.exp (I * (th TT α (br s z) : ℂ))

theorem hasFDerivAt_br_real (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) :
    HasFDerivAt (br s) ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹) ζ := by
  have h : HasFDerivAt (br s)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ζ⁻¹).restrictScalars ℝ) ζ :=
    (hasDerivAt_br s hs).hasFDerivAt.restrictScalars ℝ
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp [mul_comm]

theorem hasFDerivAt_ug (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s)
    (hζ : ζ ∈ An TT) :
    HasFDerivAt (ug TT α s)
      (((ContinuousLinearMap.mul ℝ ℂ) (ug TT α s ζ)).comp
        (I • Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹)))) ζ := by
  have h1 : HasFDerivAt (fun z => th TT α (br s z))
      ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹)) ζ :=
    (hasFDerivAt_th hTT hα hcurv (br_mem_Hh s hTT hζ)).comp ζ (hasFDerivAt_br_real s hs)
  have h2 : HasFDerivAt (fun z => ((th TT α (br s z) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹))) ζ :=
    Complex.ofRealCLM.hasFDerivAt.comp ζ h1
  have h3 : HasFDerivAt (fun z => I * ((th TT α (br s z) : ℝ) : ℂ))
      (I • Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹))) ζ :=
    h2.const_smul I
  have h4 := h3.cexp
  show HasFDerivAt (fun z => Complex.exp (I * (th TT α (br s z) : ℂ))) _ ζ
  refine h4.congr_fderiv ?_
  ext v
  simp [ug]

theorem fderiv_uu_apply (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) {ζ : ℂ} (hζ : ζ ∈ An TT) (v : ℂ) :
    fderiv ℝ (uu TT α) ζ v = uu TT α ζ * (I * ((2 * (α ζ * v).im : ℝ) : ℂ)) := by
  have hne := ne_zero_of_An hTT hζ
  obtain ⟨s, hs⟩ := exists_br hne
  have hev : uu TT α =ᶠ[𝓝 ζ] ug TT α s := by
    filter_upwards [(isOpen_An TT).mem_nhds hζ] with z hz
    exact uu_eq_br hTT hα hcurv hhol s hz
  have hu : ug TT α s ζ = uu TT α ζ := (uu_eq_br hTT hα hcurv hhol s hζ).symm
  rw [hev.fderiv_eq, (hasFDerivAt_ug hTT hα hcurv s hs hζ).fderiv]
  have hb : α ζ * ζ * (ζ⁻¹ * v) = α ζ * v := by field_simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, om_apply, bet, exp_br s hne,
    smul_eq_mul, hu, hb]

theorem wZ_uu (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) {ζ : ℂ} (hζ : ζ ∈ An TT) :
    wZ (uu TT α) ζ = uu TT α ζ * α ζ ∧ wZb (uu TT α) ζ = -(uu TT α ζ * (starRingEnd ℂ) (α ζ)) := by
  have h1 := fderiv_uu_apply hTT hα hcurv hhol hζ 1
  have h2 := fderiv_uu_apply hTT hα hcurv hhol hζ I
  have e1 : (1 / 2 : ℂ) * (I * ((2 * (α ζ * 1).im : ℝ) : ℂ) - I * (I * ((2 * (α ζ * I).im : ℝ) : ℂ)))
      = α ζ := by
    apply Complex.ext <;> simp
  have e2 : (1 / 2 : ℂ) * (I * ((2 * (α ζ * 1).im : ℝ) : ℂ) + I * (I * ((2 * (α ζ * I).im : ℝ) : ℂ)))
      = -(starRingEnd ℂ) (α ζ) := by
    apply Complex.ext <;> simp
  refine ⟨?_, ?_⟩
  · rw [wZ, h1, h2]
    linear_combination (uu TT α ζ) * e1
  · rw [wZb, h1, h2]
    linear_combination (uu TT α ζ) * e2

theorem contDiffOn_uu (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uu TT α) (An TT) := by
  intro ζ hζ
  obtain ⟨s, hs⟩ := exists_br (ne_zero_of_An hTT hζ)
  have hev : uu TT α =ᶠ[𝓝 ζ] fun z => Complex.exp (I * (th TT α (br s z) : ℂ)) := by
    filter_upwards [(isOpen_An TT).mem_nhds hζ] with z hz
    exact uu_eq_br hTT hα hcurv hhol s hz
  have hth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (th TT α) (br s ζ) :=
    (contDiffOn_th hTT hα hcurv).contDiffAt ((isOpen_Hh TT).mem_nhds (br_mem_Hh s hTT hζ))
  have hbr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ :=
    (contDiffAt_br s hs).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ((th TT α (br s z) : ℝ) : ℂ)) ζ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp ζ (hth.comp ζ hbr)
  exact ((contDiffAt_const.mul h2).cexp.congr_of_eventuallyEq hev).contDiffWithinAt

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

section

namespace Formalism.FourierDecayAlt.P

theorem orbit_tail_estimate : Formalism.FourierDecayAlt.G.TailStep :=
  tail_estimate_of_bound tailBound_statement matrix_cutoff_spec cutoff_phase_bound

theorem change_of_variables_xy : Formalism.FourierDecayAlt.G.InnerXY :=
  inner_xy_of_reduced orbital_integral_reduced reduced_integrand_integrable split_xy_coordinates amplitude_eq

theorem nonstationary_estimate : Formalism.FourierDecayAlt.G.NonStatStep :=
  nonstationary_estimate_of_parts nonstationary_phase gradient_lower_bound phase_function_deriv phase_relative_deriv
    critical_cutoff_spec amplitude_bound_far orbital_integral_converges_abs cutoff_phase_bound change_of_variables_xy

theorem stationary_estimate : Formalism.FourierDecayAlt.G.StatStep :=
  stationary_estimate_of_parts stationary_phase_holomorphic phase_function_deriv phase_function_critical_points hessian_at_critical hessian_determinant
    phase_near_critical critical_cutoff_spec amplitude_bound_critical amplitude_continuous_at_critical majorant_y
    orbital_integral_converges_abs cutoff_phase_bound change_of_variables_xy

theorem germ_rate : Formalism.FourierDecayAlt.G.GermRate :=
  germ_rate_of_estimates orbital_integral_converges_abs cutoff_phase_bound critical_cutoff_spec exists_small_delta
    root_set_characterization orbit_tail_estimate change_of_variables_xy nonstationary_estimate stationary_estimate amplitude_limit
    limit_integral stationary_leading_constant germ_large_parameter

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.Wd5

open Matrix Formalism.FourierDecayAlt.Wd

section Free

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem eU_apply (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if x a = i ∧ y = Function.update x a j then 1 else 0 := by
  have key : (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (x a = i ∧ y = Function.update x a j) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, funext fun b => ?_⟩
      by_cases hb : b = a
      · subst hb
        simp [h2]
      · simp only [Function.update_apply, if_neg hb]
        exact (h3 b hb).symm
    · rintro ⟨h1, rfl⟩
      exact ⟨h1, by simp, fun b hb => by simp [Function.update_apply, hb]⟩
  simp only [eU, Matrix.of_apply, key]

theorem eU_mul_apply (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((eU a i j : SlopeTestRemainingChoices S A) * B) x y = if x a = i then B (Function.update x a j) y else 0 := by
  rw [Matrix.mul_apply]
  simp only [eU_apply]
  by_cases h : x a = i
  · simp [h, ite_mul, Finset.sum_ite_eq']
  · simp [h]

theorem eU_comm_of_ne {a c : S} (hc : c ≠ a) (i j k l : Fin 2) :
    Commute (eU c i j : SlopeTestRemainingChoices S A) (eU a k l) := by
  show (eU c i j : SlopeTestRemainingChoices S A) * eU a k l = eU a k l * eU c i j
  ext x y
  rw [eU_mul_apply, eU_mul_apply, eU_apply, eU_apply]
  have h1 : Function.update x c j a = x a := by simp [Function.update_apply, Ne.symm hc]
  have h2 : Function.update x a l c = x c := by simp [Function.update_apply, hc]
  have h3 : Function.update (Function.update x c j) a l = Function.update (Function.update x a l) c j :=
    Function.update_comm hc j l x
  rw [h1, h2, h3]
  by_cases hx : x c = i <;> by_cases hy : x a = k <;> simp [hx, hy]

theorem free_io (c : S) (x : A) : FreeOf c (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * io x = io x * eU c i j
  ext p q
  simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, eU, Matrix.of_apply]
  split_ifs <;> simp

theorem free_one (c : S) : FreeOf c (1 : SlopeTestRemainingChoices S A) := fun i j => Commute.one_right _

theorem free_zero (c : S) : FreeOf c (0 : SlopeTestRemainingChoices S A) := fun i j => Commute.zero_right _

theorem free_mul {c : S} {b b' : SlopeTestRemainingChoices S A} (h : FreeOf c b) (h' : FreeOf c b') : FreeOf c (b * b') := fun i j => (h i j).mul_right (h' i j)

theorem free_sub {c : S} {b b' : SlopeTestRemainingChoices S A} (h : FreeOf c b) (h' : FreeOf c b') : FreeOf c (b - b') := fun i j => (h i j).sub_right (h' i j)

theorem free_smul {c : S} {b : SlopeTestRemainingChoices S A} (k : K) (h : FreeOf c b) : FreeOf c (k • b) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * (k • b) = (k • b) * eU c i j
  rw [Matrix.mul_smul, Matrix.smul_mul, (h i j).eq]

theorem free_eU {a c : S} (hc : c ≠ a) (k l : Fin 2) : FreeOf c (eU a k l : SlopeTestRemainingChoices S A) := fun i j => eU_comm_of_ne hc i j k l

theorem freeOf2_mul {c : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) (hN : FreeOf2 c N) :
    FreeOf2 c (M * N) := by
  intro i j p q
  rw [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun k _ => (hM i k p q).mul_right (hN k j p q)

theorem freeOf2_transpose {c : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) : FreeOf2 c Mᵀ := fun i j => hM j i

theorem freeOf2_one (c : S) : FreeOf2 c (1 : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact free_one c
  · exact free_zero c

theorem freeOf2_rmatrix {a c : S} (hc : c ≠ a) (D : K) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  simp only [Rh0, Matrix.smul_apply, Matrix.sub_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc j i))

theorem freeOf2_rmatrix_transpose {a c : S} (hc : c ≠ a) (d : K) : FreeOf2 c (Rht0 a d : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  simp only [Rht0, Matrix.smul_apply, Matrix.sub_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc i j))

theorem free_ins {a c : S} (hc : c ≠ a) {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) :
    FreeOf c (ins a M) := by
  intro p q
  unfold ins
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
    (eU_comm_of_ne hc p q i j).mul_right (hM i j p q)

theorem freeOf2_lift (c : S) (M : M2 A) : FreeOf2 c (lift0 M : M2 (SlopeTestRemainingChoices S A)) := fun i j => free_io c (M i j)

theorem word_free (QQ : K → M2 A) (w : List (Letter K S)) (c : S)
    (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) : FreeOf c (RRw QQ w) ∧ ∀ Y, FreeOf2 c (TTw QQ w Y) := by
  induction w with
  | nil => exact ⟨free_one c, fun Y => freeOf2_lift c (QQ Y)⟩
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    obtain ⟨hcl, hcw⟩ := hc
    obtain ⟨hR, hT⟩ := ih hcw
    have hT' : ∀ Y, FreeOf2 c (TTw QQ (l :: w) Y) := by
      intro Y
      simp only [TTw]
      split_ifs
      · exact freeOf2_mul (hT Y) (freeOf2_rmatrix hcl _)
      · exact freeOf2_mul (freeOf2_rmatrix_transpose hcl _) (hT Y)
    refine ⟨?_, hT'⟩
    simp only [RRw]
    apply free_mul hR
    apply free_ins hcl
    split_ifs
    · exact hT _
    · exact freeOf2_transpose (hT _)

end Free

theorem wordModule_of (hS : StartModule) (hP : LetterPlus) (hM : LetterMinus) (hF : WordFree) :
    WordModule := by
  intro K A S _ _ _ _ _ _ _ _ QQ q w hQ hw
  induction w with
  | nil =>
    have hset : {Y : K | Reg ([] : List (Letter K S)) Y} = Set.univ := by
      ext Y
      simp [Reg]
    rw [hset]
    exact hS K A S QQ q hQ
  | cons l w ih =>
    obtain ⟨hnd, hreal, hpw⟩ := hw
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    have hMod := ih ⟨hnd.2, fun l' hl' => hreal l' (List.mem_cons_of_mem _ hl'), hpw.2⟩
    obtain ⟨hFR, hFT⟩ := hF K A S QQ w l.intersection_update_fsHerm_neg_one hnd.1
    have hmem : l.pt ∈ {Y : K | Reg w Y} := fun l' hl' => hpw.1 l' hl'
    have hstar : star l.pt = l.pt := hreal l (by simp)
    cases hpl : l.plus
    · have key := hM K A S _ _ _ _ l.intersection_update_fsHerm_neg_one l.pt hMod hFR hFT hmem hstar
      convert key using 1
      all_goals first
        | (simp [RRw, hpl]; done)
        | (ext Y; simp [Reg, RegL, TTw, qw, hpl, and_comm]; done)
        | (funext Y; simp [TTw, qw, hpl])
    · have key := hP K A S _ _ _ _ l.intersection_update_fsHerm_neg_one l.pt hMod hFR hFT hmem hstar
      convert key using 1
      all_goals first
        | (simp [RRw, hpl]; done)
        | (ext Y; simp [Reg, RegL, TTw, qw, hpl, and_comm]; done)
        | (funext Y; simp [TTw, qw, hpl])

end Formalism.FourierDecayAlt.P.Wd5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.Wd

theorem word_free_of_unused_positions : Formalism.FourierDecayAlt.Wd.WordFree := by
  intro K A S _ _ _ _ _ _ _ _ QQ w c hc
  exact Formalism.FourierDecayAlt.P.Wd5.word_free QQ w c hc

theorem word_module_structure : Formalism.FourierDecayAlt.Wd.WordModule := Formalism.FourierDecayAlt.P.Wd5.wordModule_of initial_module_structure letter_module_plus letter_module_minus
  word_free_of_unused_positions

end Formalism.FourierDecayAlt.P
end
