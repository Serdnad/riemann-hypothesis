module

public import Formalism.FrobeniusOrbits.Bundle001
public import Formalism.GL3MeanSquares.Bundle002
public import Formalism.HermitianLattices.Bundle003
public import Formalism.LogVandermondeBounds.Bundle001
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

open NumberField IntermediateField Ideal IsDedekindDomain
open scoped Pointwise TensorProduct

noncomputable section

namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

def PartnerFormula : Prop :=
  ∀ (e : ℕ) (h t : HGrp e),
    cc e * ((c0, h) : GG e) * ((1, t) : GG e) = ((1, h * t) : GG e) ∧
    cc e * ((c0, h) : GG e) * (((sg e).1, t) : GG e) = (((sg e).1, h * t) : GG e) ∧
    cc e * ((((1 : ℤˣ), (-1 : ℤˣ)), h) : GG e) * ((1, t) : GG e) = (((sg e).1, h * t) : GG e) ∧
    cc e * ((((1 : ℤˣ), (-1 : ℤˣ)), h) : GG e) * (((sg e).1, t) : GG e) = ((1, h * t) : GG e)

def FrobArith : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (u : (ZMod (2 ^ (e + 2)))ˣ), (u : ZMod (2 ^ (e + 2))) = (p : ZMod (2 ^ (e + 2))) →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
    ((∀ x : 𝓞 (hostE ζ a b), σ • x - x ^ p ∈ P) ↔
      ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
        (galE e ζ a b σ).2 = hcl e u)) ∧
    ((∀ x : 𝓞 (hostE ζ a b), σ⁻¹ • x - x ^ p ∈ P) ↔
      ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
        (galE e ζ a b σ).2 = (hcl e u)⁻¹))






def DiffStable : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
    σ • differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) =
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))

def PrincipalStable : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b c = cc e →
  ∀ 𝔭₂ 𝔭q : Ideal (𝓞 (KinE ζ a b)), 𝔭₂.IsPrime → 𝔭q.IsPrime →
    ((2 : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂ → ((q : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭q →
    ∃ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (c • 𝔟) ∧
      (∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ∣ 𝔟 →
        P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭₂ ∨
        P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭q) ∧
      𝔟 ⊔ c • 𝔟 = ⊤ ∧
      (∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ ∈ Psi e → σ • 𝔟 = 𝔟) ∧
      ∀ 𝔟' : Ideal (𝓞 (hostE ζ a b)),
        differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟' * (c • 𝔟') →
        (∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ∣ 𝔟' →
          P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭₂ ∨
          P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭q) →
        𝔟' = 𝔟

end Formalism.HermitianLattices.FiltrationBoundaryCriterion
end
end

section

open Finset Filter Topology ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.GlobalBoundRefinements


open Formalism.HermitianLattices.GL2PrimeSums in
def ShortIntervalLowerBound : Prop :=
  ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb →
    ∃ C₀' c : ℝ, C₀ ≤ C₀' ∧ 0 < c ∧
      ∀ (B G β : ℝ) (θ : ℤ) (π₁ π₂ : ℝ → ℕ) (η' : ℝ → ℝ),
        4 ≤ B → 1 ≤ G → G ≤ B → θ ∈ ({-1, 0, 1} : Set ℤ) →
        (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β) →
        (∀ Y : ℝ, 1 ≤ Y → (π₂ Y : ℝ) ≤ 2 * Real.sqrt Y) →
        (∀ Y : ℝ, 0 ≤ η' Y ∧ η' Y ≤ 3 * Real.log B) →
        (∀ Y : ℝ, B ^ C₀ ≤ Y →
          |G * ((π₁ Y : ℝ) + π₂ Y + η' Y) - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y) →
        ∀ X : ℝ, B ^ C₀' ≤ X →
          c * B ^ (-5 : ℝ) * X / Real.log X ≤ Emain θ β X ∧
          ∀ h : ℝ, h ≤ 1 → rhoErr Cr cr B X ≤ h / 100 → B ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
            c * h * B ^ (-6 : ℝ) * X / Real.log X ≤ (π₁ (X * (1 + h)) : ℝ) - π₁ X



open Formalism.HermitianLattices.GL2PrimeSums in
def PrimeCountAsymptoticInProgressions (C₀ Cr cr cb : ℝ) : Prop :=
  ∀ m a : ℕ, 3 ≤ m → Nat.Coprime a m → ∃ (θ : ℤ) (β : ℝ) (η' : ℝ → ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
    (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / ((4 * (m : ℝ)) ^ 2 * Real.log (4 * m)) ≤ 1 - β) ∧
    (∀ Y : ℝ, 0 ≤ η' Y ∧ η' Y ≤ 3 * Real.log (4 * m)) ∧
    ∀ Y : ℝ, (4 * (m : ℝ)) ^ C₀ ≤ Y →
      |(m.totient : ℝ) * ((((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card : ℝ) + η' Y) - Emain θ β Y|
        ≤ rhoErr Cr cr (4 * m) Y * Emain θ β Y


open Formalism.HermitianLattices.GL2PrimeSums in
def ShortIntervalImpliesProgressions : Prop :=
  ShortIntervalLowerBound → ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb → PrimeCountAsymptoticInProgressions C₀ Cr cr cb →
    ∃ C₀' c : ℝ, 0 < C₀' ∧ 0 < c ∧ PrimesAPInterval C₀' Cr cr c




open Formalism.LogVandermondeBounds.StandardLattice in
def LogLFunctionEulerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ M : ℕ, 2 ≤ M →
    Multipliable (fun P : {P : Ideal (NumberField.RingOfIntegers K) // P.IsMaximal} =>
      Formalism.HermitianLatticesTheory.eulerFac K M P.1) ∧
    0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
    |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log (zetaR M)

end Formalism.HermitianLattices.GlobalBoundRefinements
end
end

section

open NumberField Finset

namespace Formalism.HermitianLattices.SiegelMassBounds

def SiegelMassRatioThm : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

end Formalism.HermitianLattices.SiegelMassBounds
end
