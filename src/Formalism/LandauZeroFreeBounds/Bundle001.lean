module

public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
public import Formalism.LandauZeroFreeBounds.Statement
public import Formalism.ZeroFreeRegion.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Complex
open scoped ComplexOrder

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def IsProdChar {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (ψ : DirichletCharacter ℂ (q₁ * q₂)) : Prop :=
  ∀ n : ℕ, ψ (n : ZMod (q₁ * q₂)) = χ₁ (n : ZMod q₁) * χ₂ (n : ZMod q₂)

def Fbq {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)) (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
    DirichletCharacter.LFunction ψ s

def lamBq {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)) : ℂ :=
  DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 * DirichletCharacter.LFunction ψ 1

def ProdCharExists : Prop :=
  ∀ (q₁ q₂ : ℕ) (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂),
    ∃ ψ : DirichletCharacter ℂ (q₁ * q₂), IsProdChar χ₁ χ₂ ψ

def BqCoeff : Prop :=
  ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)),
    χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → IsProdChar χ₁ χ₂ ψ →
    ∃ a : ℕ → ℂ, (∀ n, 0 ≤ a n) ∧ a 1 = 1 ∧ LSeries.abscissaOfAbsConv a ≤ 1 ∧
      ∀ s : ℂ, 1 < s.re → Fbq χ₁ χ₂ ψ s = LSeries a s

def BqEntire : Prop :=
  ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)), χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 →
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ s : ℂ, s ≠ 1 → Fbq χ₁ χ₂ ψ s = G s + lamBq χ₁ χ₂ ψ / (s - 1)

def BqGrowth : Prop :=
  ∃ C K : ℝ, ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)), χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 →
    ∀ s : ℂ, ‖s - 2‖ = 3 / 2 → ‖Fbq χ₁ χ₂ ψ s‖ ≤ C * ((q₁ * q₂ : ℕ) : ℝ) ^ K

def LFunctionOneUpperBound : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ‖DirichletCharacter.LFunction χ 1‖ ≤ C * Real.log (3 * q)

def BqKey : Prop :=
  ∃ C K : ℝ, 0 ≤ K ∧ ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)),
    χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 → IsProdChar χ₁ χ₂ ψ →
    ∀ σ : ℝ, 7 / 8 ≤ σ → σ < 1 →
      1 / 2 - C * ‖lamBq χ₁ χ₂ ψ‖ * ((q₁ * q₂ : ℕ) : ℝ) ^ (K * (1 - σ)) / (1 - σ) ≤ (Fbq χ₁ χ₂ ψ σ).re

def ZetaNegReal : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 → (riemannZeta σ).im = 0 ∧ (riemannZeta σ).re < 0

def LRealPos : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 → ∀ σ₀ : ℝ,
    (∀ σ : ℝ, σ₀ ≤ σ → DirichletCharacter.LFunction χ σ ≠ 0) →
    ∀ σ : ℝ, σ₀ ≤ σ → (DirichletCharacter.LFunction χ σ).im = 0 ∧ 0 < (DirichletCharacter.LFunction χ σ).re

def SameCharacterLFunctionOne : Prop :=
  ∀ (q₁ q : ℕ) [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q),
    χ₁ ≠ 1 → χ ≠ 1 → (∀ n : ℕ, Nat.Coprime n (q₁ * q) → χ₁ (n : ZMod q₁) = χ (n : ZMod q)) →
    ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ (((q₁ * q).primeFactors.card : ℝ) + 1) ^ 2 *
      ‖DirichletCharacter.LFunction χ 1‖

def RealCharExists : Prop :=
  ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 ∧ χ ≠ 1

def BqKeyOf : Prop := BqCoeff → BqEntire → BqGrowth → LFunctionOneUpperBound → BqKey

def SiegelOf : Prop :=
  ProdCharExists → RealCharExists → BqKey → LFunctionOneUpperBound → ZetaNegReal → LRealPos → SameCharacterLFunctionOne → SiegelLower

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def negLD {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)

def LandauLocal2 : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ), 0 < r → 1 ≤ M →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    (∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ = 0 → 2 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r

def LGrowth : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
    ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖)

def LInvBound : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 1 < s.re →
    ‖DirichletCharacter.LFunction χ s‖⁻¹ ≤ s.re / (s.re - 1)

def LLogDerivRight : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 1 < s.re →
    ‖negLD χ s‖ ≤ 1 / (s.re - 1) + C

def Positivity : Prop :=
  ∀ (q : ℕ) [NeZero q] (σ : ℝ), 1 < σ →
    (∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      0 ≤ 3 * (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re + 4 * (negLD χ ((σ : ℂ) + t * I)).re
        + (negLD (χ ^ 2) ((σ : ℂ) + 2 * t * I)).re) ∧
    (∀ χ : DirichletCharacter ℂ q, χ ^ 2 = 1 →
      0 ≤ (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re + (negLD χ (σ : ℂ)).re) ∧
    (∀ χ₁ χ₂ : DirichletCharacter ℂ q, χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 →
      0 ≤ (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re + (negLD χ₁ (σ : ℂ)).re
        + (negLD χ₂ (σ : ℂ)).re + (negLD (χ₁ * χ₂) (σ : ℂ)).re)

def TrivLogDeriv : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 →
    (negLD (1 : DirichletCharacter ℂ q) ((σ : ℂ) + t * I)).re ≤
      (1 / ((σ : ℂ) - 1 + t * I)).re + C * Real.log ((q : ℝ) * (|t| + 2))

def TrivZeros : Prop :=
  ∀ (q : ℕ) [NeZero q] (s : ℂ), 0 < s.re → s ≠ 1 →
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s = 0 → riemannZeta s = 0

def RealConj : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 → ∀ s : ℂ,
    DirichletCharacter.LFunction χ (starRingEnd ℂ s) = starRingEnd ℂ (DirichletCharacter.LFunction χ s)

def LocalZeros : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ,
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔
        (ρ ∈ Metric.closedBall ((11 / 10 : ℂ) + t * I) (1 / 5) ∧ DirichletCharacter.LFunction χ ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ = 0 → 2 ≤ m ρ) ∧
      ∀ σ : ℝ, 1 < σ → σ ≤ 6 / 5 →
        (negLD χ ((σ : ℂ) + t * I)).re ≤
          C * Real.log ((q : ℝ) * (|t| + 2)) - ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + t * I - ρ)).re

def NoZeroComplex : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    χ ^ 2 ≠ 1 → InRegion c q s → DirichletCharacter.LFunction χ s ≠ 0

def RealLargeT : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    χ ^ 2 = 1 → χ ≠ 1 → δ / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ |s.im| → InRegion c q s →
      DirichletCharacter.LFunction χ s ≠ 0

def RealSmallT : Prop :=
  ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
    ∀ s s' : ℂ, |s.im| < δ / Real.log ((q : ℝ) * (|s.im| + 2)) →
      |s'.im| < δ / Real.log ((q : ℝ) * (|s'.im| + 2)) →
      InRegion c q s → InRegion c q s' →
      DirichletCharacter.LFunction χ s = 0 → DirichletCharacter.LFunction χ s' = 0 →
      s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧ s' = s

def TwoReal : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q), χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 →
    χ₁ ≠ 1 → χ₂ ≠ 1 → χ₁ ≠ χ₂ → ∀ β₁ β₂ : ℝ, InRegion c q (β₁ : ℂ) → InRegion c q (β₂ : ℂ) →
      DirichletCharacter.LFunction χ₁ (β₁ : ℂ) ≠ 0 ∨ DirichletCharacter.LFunction χ₂ (β₂ : ℂ) ≠ 0

def LocalZerosOf : Prop := LandauLocal2 → LGrowth → LInvBound → LocalZeros

def NoZeroComplexOf : Prop := LocalZeros → LLogDerivRight → Positivity → NoZeroComplex

def RealLargeTOf : Prop := LocalZeros → LLogDerivRight → Positivity → TrivLogDeriv → RealLargeT

def RealSmallTOf : Prop := LocalZeros → LLogDerivRight → Positivity → RealConj → RealSmallT

def TwoRealOf : Prop := LocalZeros → LLogDerivRight → Positivity → TwoReal

def ZFRDirichletOf : Prop :=
  Formalism.ZF.ZeroFreeRegion → TrivZeros → NoZeroComplex → RealLargeT → RealSmallT → TwoReal → ZFRDirichlet

end Formalism.ZeroFreeDirichlet
end
end
