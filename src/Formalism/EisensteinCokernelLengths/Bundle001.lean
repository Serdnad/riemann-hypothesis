module

public import Formalism.GaussValuationBounds.GaussUnit
public import Formalism.WindowSums.Statement
public import Mathlib.RingTheory.Length
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
import Formalism.FrobeniusContraction.Bundle001

@[expose] public section

section

noncomputable section

open scoped ENNReal

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

def sigUp (ℓ E M j : ℕ) : ℕ :=
  ⌈((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌉₊ + 1

def SigBoundUp : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (g h j : ℕ), 1 ≤ j →
    (sigUp ℓ (3 * g) ((h + 2 * g) / (ℓ - 1) + 1) j : ℝ) ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4

def EisE {O : Type} [CommRing O] (ϖ : O) (e : ℕ) (E : Polynomial O) (N : ℕ) : Prop :=
  E.Monic ∧ E.natDegree = N ∧ (∀ i < N, E.coeff i ∈ Ideal.span {ϖ ^ e}) ∧ E.coeff 0 ∉ Ideal.span {ϖ ^ (e + 1)}

def GaussEisRam : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℕ), 1 ≤ e → ∀ (x : ℝ), 0 ≤ x → ∀ (E : Polynomial O) (N : ℕ), 1 ≤ N → EisE ϖ e E N →
      Formalism.NOK.gaussV x (E : PowerSeries O) = ENNReal.ofReal (min (e : ℝ) (x * N))

def LemmaCValRam : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℕ), 1 ≤ e → ∀ (ℓ : ℕ), 2 ≤ ℓ →
    ∀ (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O),
      (∀ s, EisE ϖ e (E s) (ℓ ^ s)) → (∀ s, IsUnit (u s)) →
      ∀ (ell g a b₀ b₁ s₀ s₁ k : ℕ), s₀ < s₁ →
        2 * ((a : ℝ) + 2 * e * g * ell) < e * b₁ → 2 * b₀ ≤ ℓ * b₁ →
        PowerSeries.C (ϖ ^ a) *
            (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
            (u s₀ * (E s₀ : PowerSeries O)) ^ b₀ ∈
          Ideal.span {PowerSeries.C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b₁} →
        (k : ℝ) ≤ ((a : ℝ) + 2 * e * g * ell) * b₁ / (b₁ - b₀ / ℓ) ∧
          (k : ℝ) ≤ 2 * ((a : ℝ) + 2 * e * g * ell)

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
end
end

section

noncomputable section

namespace Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

open Polynomial

def FirstRelationTorsion : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (X u : A) (B r : ℕ),
      (ℓ : A) ^ (⌊(B : ℝ) / ((ℓ : ℝ) - 1)⌋₊ + 1) * (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r ∈
        Ideal.span {(ℓ : A) ^ ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊, X * (X + (ℓ : A)) ^ B}

def FirstRelationModule : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (X u : A) (M η r : ℕ), 1 ≤ M →
      (ℓ : A) ^ (⌊((M : ℝ) + η) / ((ℓ : ℝ) - 1)⌋₊ + 1) * (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r ∈
        Ideal.span {(ℓ : A) ^ ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊, X ^ M * (X + (ℓ : A)) ^ η}

def SecondRelationTorsion : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (ε u' w : PowerSeries O) (b r : ℕ),
      PowerSeries.C ((ℓ : O) ^ (⌊(b : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌋₊ + 1)) *
          (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1) *
            (Formalism.WindowSums.p1 ℓ ε u') ^ (ℓ - 1)) ^ r ∈
        Ideal.span {PowerSeries.C ((ℓ : O) ^ ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊),
          (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ b}

def GapG : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V]
    (T : Module.End ℤ_[ℓ] V) (c : ℤ → ℤ_[ℓ]),
    (∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧ PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j')) →
    ∀ (a S η b E : ℕ) (R₁ R₂ : Finset ℤ) (x : V),
      2 * a + η ≤ b →
      R₁ ⊆ Finset.Icc ((b : ℤ) - a + 1) b →
      R₂ ⊆ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) →
      aeval T (∏ j ∈ R₁, (X - C (c j))) x = 0 →
      aeval T (∏ j ∈ R₂, (X - C (c j))) x = 0 →
      ((3 * a + S + 2 * η : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ ((b + η : ℕ) : ℝ) ≤ E →
      ((ℓ : ℤ_[ℓ]) ^ E) • x = 0

def RRVal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ → ℤ_[ℓ]), c 0 = 0 →
    (∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧ PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j')) →
    ∀ (a S η b : ℕ),
      let J := (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) ∪
        Finset.Icc (1 - ((b : ℤ) + S)) ((a : ℤ) - b)).erase 0
      (∏ j ∈ J, c j) ≠ 0 ∧
        (PadicInt.valuation (∏ j ∈ J, c j) : ℝ) ≤
          ((2 * a + 2 * η + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ ((η + a : ℕ) : ℝ) +
            Real.logb ℓ ((b + S : ℕ) : ℝ)

def ExponentChainBound : Prop :=
  ∀ (ℓ b b' S E lam σ₂ h'' c' : ℝ), 2 ≤ ℓ → 0 ≤ b → 0 ≤ S → 0 ≤ E → 0 ≤ σ₂ → 0 ≤ lam →
    c' ≤ b' + S - b / ℓ + 2 + lam →
    max 0 ((((b + S) + 1) / (ℓ - 1) + 1 + E + σ₂ + h'' - b') + σ₂ + c' - h'') ≤
      b / (ℓ * (ℓ - 1)) + E + 2 * σ₂ + 2 * S + 5 + lam

def NumC : Prop :=
  ∀ ℓ : ℝ, 11 ≤ ℓ →
    8 * (2 * ℓ - 1) / (ℓ - 1) ^ 3 + 8 / (ℓ - 1) ^ 2 + 1 / (ℓ * (ℓ - 1)) ≤ 31.11 / ℓ ^ 2

end Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria
end
end

section

noncomputable section

open Classical

namespace Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts

open Formalism.WachCohomologyFacts Formalism.WachCohomologyFacts.V2

def LenBound2 : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) (s s₀ : Finset M),
    s.card ≤ g → Submodule.span O (s : Set M) ⊔ Bc = Z → Bc ≤ I →
    s₀.card ≤ g₀ → (s₀ : Set M) ⊆ Z →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (ℓ ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g : ℕ∞) * (e : ℕ∞) + (g₀ : ℕ∞) * (e' : ℕ∞)) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

end Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts
end
end
