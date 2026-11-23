module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongLimitOnZero.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (p : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → p ∈ zeroSet J → linEval u p = 0 →
      ∃ N ∈ 𝓝 p, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
          (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
              (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
            (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongMassNearSmall.Statement : Prop :=
  ∀ (n d : ℕ) (J I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (f : (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → J ⊔ Ideal.span {linForm u} ≤ I →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ δ > 0, ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧
        (∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧ ∀ x ∈ U, χ x = 1) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ),
          |varInt J (d + 1) (fun x => χ x * f x) (vecCons (logReg u ε) φ)| ≤ δ) ∧
        |∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
            (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d (fun x => χ x * f x) φ| ≤ δ

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def LocalDimComponentBound.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), q ∈ zeroSet I →
    ∃ W : Ideal (MvPolynomial (Fin n) ℂ), W.IsPrime ∧ I ≤ W ∧ q ∈ zeroSet W ∧
      ringKrullDim (curveLocalRing I q) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def LocalDimDomain.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (e : ℕ) → ∀ q ∈ zeroSet J,
      ringKrullDim (localRingAt J q) = (e : ℕ)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def MinimalPrimePlace.Statement : Prop :=
  ∀ (n : ℕ) (I J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → J ∈ I.minimalPrimes → J ≤ RingHom.ker (eval q) →
    ∀ P' : MaximalSpectrum (curveNormalisation J q), ∃ P : MaximalSpectrum (curveNormalisation I q),
      ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
        Ring.ord (Localization.AtPrime P'.asIdeal)
          (algebraMap (curveNormalisation J q) (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveLocalRing J q) (curveNormalisation J q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def OrdDeterminesPlace.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P P' : MaximalSpectrum (curveNormalisation I q),
        (∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
          Ring.ord (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)))) →
        P = P'

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def OrdFiniteNonZeroDivisor.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    (∀ P : MaximalSpectrum (curveNormalisation I q),
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) ≠ ⊤) →
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ nonZeroDivisors (curveLocalRing I q)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def PlaceOnComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation I q), ∃ J : Ideal (MvPolynomial (Fin n) ℂ),
        J ∈ I.minimalPrimes ∧ J ≤ RingHom.ker (eval q) ∧ ringKrullDim (curveLocalRing J q) = 1 ∧
        ∃ P' : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
          Ring.ord (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P'.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PuncturedCurveDiscInverse.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    ∃ ε > 0, ∀ (φ : ℂ → Fin n → ℂ) (σ₀ : ℂ) (δ : ℝ), 0 < δ →
      DifferentiableOn ℂ φ (Metric.ball σ₀ δ) → Set.InjOn φ (Metric.ball σ₀ δ) →
      Set.MapsTo φ (Metric.ball σ₀ δ) (zeroSet I) → φ σ₀ ∈ Metric.ball q ε → φ σ₀ ≠ q →
      ∃ U : Set (Fin n → ℂ), IsOpen U ∧ φ σ₀ ∈ U ∧ ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ U ∧
        ∀ z ∈ zeroSet I ∩ U, ∃ σ ∈ Metric.ball σ₀ δ, φ σ = z ∧ ψ z = σ

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegBallMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (K : Set (Fin n → ℂ)),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    linForm u ∉ J → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ x ∈ K, ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        Integrable (chartDens J A ((Metric.ball x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot)) ∧
          ∫ y, chartDens J A ((Metric.ball x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y ≤ C * r ^ (2 * d)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ),
    0 < ε → IsSheetAt J A x s →
      0 ≤ ReciprocityTheory.AnForm.maDens
        (fun k => (vecCons (logReg u ε) fun _ => euclPot : Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ s) (A *ᵥ x)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegFixedBallMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    linForm u ∉ J →
      ∃ M : ℝ, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        Integrable (chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot)) ∧
          ∫ y, chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y ≤ M

end

end GroundTheory.Heights₂.Heights
end
