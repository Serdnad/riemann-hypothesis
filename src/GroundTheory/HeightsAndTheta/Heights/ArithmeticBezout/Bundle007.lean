module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

theorem HermNorm.continuous_pointOf (h : HermNorm n) : Continuous h.pointOf := by
  unfold HermNorm.pointOf
  exact Continuous.matrix_mulVec continuous_const (continuous_pi fun i => by fun_prop)

theorem HermNorm.pointOf_eq_zero (h : HermNorm n) {y : EuclideanSpace ℂ (Fin n)}
    (hy : h.pointOf y = 0) : y = 0 := by
  have hu : IsUnit h.matᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_transpose]; exact h.isUnit_det)
  have hv : (fun i => y i) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hu (by simpa [HermNorm.pointOf] using hy)
  ext i
  simpa using congrFun hv i

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ClosedPointChartField.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (i : Fin n),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((1 : ℕ) : WithBot ℕ∞) → X i ∉ I →
      IsField (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1})) ∧
        Module.Finite F (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1}))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

def AreaFormulaInj.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U A : Set E) (f : E → F) (g : F → ℝ≥0∞),
      IsOpen U → ContDiffOn ℝ 1 f U → A ⊆ U → MeasurableSet A → Set.InjOn f A → Measurable g →
        ∫⁻ y in f '' A, g y ∂(μH[(k : ℝ)]) =
          ∫⁻ x in A, g (f x) * ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F))
            ∂(μH[(k : ℝ)])

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

def AreaFormulaInjSet.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U A : Set E) (f : E → F),
      IsOpen U → ContDiffOn ℝ 1 f U → A ⊆ U → MeasurableSet A → Set.InjOn f A →
        μH[(k : ℝ)] (f '' A) =
          ∫⁻ x in A, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)])

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

def AreaFormulaLocal.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U : Set E) (f : E → F) (x₀ : E),
      IsOpen U → ContDiffOn ℝ 1 f U → x₀ ∈ U → Function.Injective (fderiv ℝ f x₀) →
        ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧ ∀ B ⊆ V, MeasurableSet B →
          μH[(k : ℝ)] (f '' B) =
            ∫⁻ x in B, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)])

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix

section Objects

variable {n : ℕ}



def specFirst {R : Type*} [CommRing R] {e : ℕ} (u : Fin n → R) :
    MvPolynomial (Fin (e + 1) × Fin n) R →ₐ[R] MvPolynomial (Fin e × Fin n) R :=
  aeval fun p => Fin.cases (motive := fun _ => MvPolynomial (Fin e × Fin n) R) (C (u p.2))
    (fun k => X (k, p.2)) p.1


end Objects


end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set Real

noncomputable section

namespace SphereMean

theorem integral_disc_radial (g : ℝ → ℝ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator g ‖z‖ = 2 * π * ∫ y in (0 : ℝ)..1, y * g y := by
  rw [integral_fun_norm_addHaar volume (fun r => (Iio (1 : ℝ)).indicator g r),
    Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]
  have h1 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y =
      ∫ y in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun y => y * g y) y := by
    congr 1
    funext y
    by_cases hy : y < 1 <;> simp [indicator, hy]
  rw [h1, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  simp [nsmul_eq_mul]
  ring

theorem integrable_disc_radial (g : ℝ → ℝ) (hg : ContinuousOn (fun y => y * g y) (Icc 0 1)) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator g ‖z‖) := by
  rw [integrable_fun_norm_addHaar volume (f := fun r => (Iio (1 : ℝ)).indicator g r),
    Complex.finrank_real_complex]
  have h1 : (fun y : ℝ => y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y) =
      (Iio (1 : ℝ)).indicator (fun y => y * g y) := by
    funext y
    by_cases hy : y < 1 <;> simp [indicator, hy]
  rw [h1, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  exact (hg.integrableOn_Icc).mono_set Ioo_subset_Icc_self

theorem integral_disc_pow (m : ℕ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖ = π / (m + 1) := by
  rw [integral_disc_radial, integral_disc_weight]
  field_simp

theorem integral_disc_log_pow (m : ℕ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖ =
      π * harmonic (m + 1) / (2 * (m + 1)) := by
  rw [integral_disc_radial]
  have h : ∫ y in (0 : ℝ)..1, y * (-log y * (1 - y ^ 2) ^ m) =
      -∫ y in (0 : ℝ)..1, y * log y * (1 - y ^ 2) ^ m := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext y
    ring
  rw [h, integral_disc_log_weight]
  field_simp
  ring

theorem integrable_disc_pow (m : ℕ) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖) :=
  integrable_disc_radial _ (by fun_prop)

theorem integrable_disc_log_pow (m : ℕ) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖) := by
  apply integrable_disc_radial
  have : (fun y : ℝ => y * (-log y * (1 - y ^ 2) ^ m)) =
      fun y => -(y * log y) * (1 - y ^ 2) ^ m := by
    funext y; ring
  rw [this]
  exact (continuous_mul_log.neg.mul (by fun_prop)).continuousOn

end SphereMean

end

end GroundTheory.Heights₂.Heights
end
