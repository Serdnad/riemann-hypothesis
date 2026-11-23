module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
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

def CutOffLimit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧
        (∀ k, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
          ∀ x ∈ U ∩ zeroSet J, χ k x = 0) ∧
        ∀ (F G : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
          SmoothNear (zeroSet J) F → SmoothNear (zeroSet J) G → (∀ i, SmoothNear (zeroSet J) (φ i)) →
          HasCompactSupport F →
            Tendsto (fun k => chartInt J A (fun x => χ k x * F x) (vecCons G φ)) atTop
                (𝓝 (chartInt J A F (vecCons G φ))) ∧
              Tendsto (fun k => chartInt J A G (vecCons (fun x => χ k x * F x) φ)) atTop
                (𝓝 (chartInt J A G (vecCons F φ)))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def DivisorBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ (m : ℕ) (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ)
              (π : Matrix (Fin d) (Fin n) ℂ),
              (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
              (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → ∀ b, x ∈ (γ b).slice) ∧
              (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) ∧
              (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
              ∀ b, Function.Bijective
                (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def DivisorGeneralPointBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W ∧
            (∀ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W' → W' = W) ∧
            (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W) ∧
            ∃ (m : ℕ) (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ)
              (π : Matrix (Fin d) (Fin n) ℂ),
              (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
              (∃ N ∈ 𝓝 q, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) ∧
              (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) ∧
              (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
              ∀ b, Function.Bijective
                (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

def DivisorOneComponent.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W ∧
            (∀ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W' → W' = W) ∧
            ∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LeadIdealDim.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ leadIdeal J) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LinearFormCut.Statement : Prop :=
  ∀ (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
      ∃ B : Matrix (Fin 1) (Fin n) ℂ,
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (I ⊔ linIdeal B)) ≤ (e : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamChartInt.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r r' : ℝ) (N : Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    DifferentiableOn ℂ σ (Metric.ball 0 r) → Set.InjOn σ (Metric.ball 0 r) →
    IsOpen N → r' < r →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r') →
    zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
      ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
      (∀ i, SmoothNear (zeroSet W) (φ i)) →
        chartInt W A f φ =
          ∫ w in Metric.ball (0 : Fin d → ℂ) r, f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamDensIntegrable.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (σ : (Fin d → ℂ) → Fin n → ℂ) (r r' : ℝ)
    (N : Set (Fin n → ℂ)),
    DifferentiableOn ℂ σ (Metric.ball 0 r) → r' < r →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r') →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
      Continuous f → tsupport f ⊆ N → (∀ i, SmoothNear (zeroSet W) (φ i)) →
        IntegrableOn (fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w)
          (Metric.ball (0 : Fin d → ℂ) r)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamOffRegularZero.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r : ℝ) (N : Set (Fin n → ℂ)),
    DifferentiableOn ℂ σ (Metric.ball 0 r) → zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), tsupport f ⊆ N →
      chartInt W A ((σ '' {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0})ᶜ.indicator f)
        φ = 0

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamPieceInt.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r r' : ℝ) (N : Set (Fin n → ℂ)),
    DifferentiableOn ℂ σ (Metric.ball 0 r) → Set.InjOn σ (Metric.ball 0 r) →
    IsOpen N → r' < r →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r') →
    zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (P : Set (Fin d → ℂ)),
      (∀ i, SmoothNear (zeroSet W) (φ i)) → MeasurableSet P → P ⊆ Metric.ball 0 r →
      (∀ w ∈ P, σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0) →
      Set.InjOn (fun v => A *ᵥ σ v) P →
        chartInt W A ((σ '' P).indicator f) φ =
          ∫ w in P, f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

variable {n d : ℕ}

def chartPosDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => max (f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y

def PosPartIndep.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    IsFiniteProjection J A' → Measurable f → (∀ k, SmoothNear (zeroSet J) (φ k)) →
      ∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y) = ∫⁻ y, ENNReal.ofReal (chartPosDens J A' f φ y)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Matrix

noncomputable section

def SheetOnlyNull.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    IsFiniteProjection J A' →
      volume ((fun x => A *ᵥ x) ''
        {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ ¬ ∃ s', IsSheetAt J A' x s'}) = 0

end

end GroundTheory.Heights₂.Heights
end
