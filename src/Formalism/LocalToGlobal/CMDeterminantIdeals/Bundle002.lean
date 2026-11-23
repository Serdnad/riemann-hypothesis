module

public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle001
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.SemistableReduction.Bundle010
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

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

def CMNumbers0 {K : Type} [Field K] [NumberField K] {g : ℕ} (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K)
    (La logOm : ℝ) : Prop :=
  abelian₂.Good ∧ (∀ j, (ℓ j).Good) ∧ de.Good ∧ 1 ≤ La ∧
  ∑ j, (ℓ j).deg - (g : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ abelian₂.deg ∧ (∀ j, (ℓ j).ndeg = logOm / 2) ∧
  de.ndeg ≤ (1 / 2) * abelian₂.dual.ndeg + (g : ℝ) / 4 * Real.log (2 * Real.pi)

def DegDe0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K) (La logOm : ℝ),
    CMNumbers0 abelian₂ ℓ de La logOm → de.ndeg ≤ (g : ℝ) * (pDeg logOm + (1 / 2) * Real.log La)

def DegNN0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K) (La logOm : ℝ)
    (V : Type) [Fintype V] (c : V → Fin g) (μ : V → ℕ) (n : ℕ), CMNumbers0 abelian₂ ℓ de La logOm →
    (lineNN de ℓ c μ n).Good ∧
    (lineNN de ℓ c μ n).ndeg ≤ (pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)

def LamNumber0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K) (La logOm : ℝ)
    (V : Type) [Fintype V] (c : V → Fin g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ),
    CMNumbers0 abelian₂ ℓ de La logOm → AddMonoidAlgebra.coeff G μ ≠ 0 → AddMonoidAlgebra.coeff G μ ∈ (lineNN de ℓ c μ n).I →
    (∀ σ, 0 < S σ) → 0 < Rr →
    (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * de.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) →
    - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤
      (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)

def HadamardLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (B : HeightOneSpectrum (𝓞 K) → Matrix (Fin g) (Fin g) K) (H : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (La : ℝ),
    abelian₂.I ≠ 0 → (∀ j, (ℓ j).Good) → LinearIndependent K u → 0 < La → (∀ σ, (H σ).PosDef) →
    (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p, IsLocGen p (B p).det abelian₂.I) →
    (∀ p j, ∃ c : K, IsLocGen p c (ℓ j).I ∧ ∀ i, p.valuation K (((B p)⁻¹.mulVec (c • u j)) i) ≤ 1) →
    (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (u j)) ≤ (La * (ℓ j).n σ) ^ 2) →
    ∑ j, (ℓ j).deg - (g : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ abelian₂.deg

def CoeffMemOfLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (ℓ : Fin g → MLine K) (de : MLine K) (V : Type) [Fintype V] (c : V → Fin g)
    (μ : V → ℕ) (n : ℕ) (cf : K), de.Good → (∀ j, (ℓ j).Good) →
    (∀ p : HeightOneSpectrum (𝓞 K), ∃ (t : K) (cl : Fin g → K), IsLocGen p t de.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧
      p.valuation K (cf * ∏ v, cl (c v) ^ μ v) ≤ p.valuation K (t ^ n)) →
    cf ∈ (lineNN de ℓ c μ n).I

end Formalism.L2.LamCM
end
end

section

noncomputable section

namespace Formalism.L2.LamCM

open IsLocalRing
open scoped ComplexOrder

abbrev FrVar {B : Type} (m : B → ℕ) : Type := Σ b : B, Fin (m b) × Fin (m b)

variable {B : Type} {m : B → ℕ}

def evalFr {R : Type} [CommRing R] (P : MvPolynomial (FrVar m) R) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) : R :=
  MvPolynomial.eval (fun v : FrVar m => X v.1 v.2.2 v.2.1) P

def substFr {R : Type} [CommRing R] (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) (P : MvPolynomial (FrVar m) R) :
    MvPolynomial (FrVar m) R :=
  MvPolynomial.bind₁ (fun v : FrVar m => ∑ j, MvPolynomial.C (U v.1 j v.2.2) * MvPolynomial.X (⟨v.1, (v.2.1, j)⟩ : FrVar m)) P

def LemmaGCore : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K),
    (Infinite (ResidueField R) ∨ P.totalDegree + ∑ b, m b < Nat.card (ResidueField R)) →
    (∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R, (∀ b, IsUnit (X b).det) →
      evalFr P (fun b => (X b).map (algebraMap R K)) ∈ Set.range (algebraMap R K)) →
    ∀ μ, AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap R K)

def BigResExt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V →
    Finite (ResidueField V) → ∀ N : ℕ,
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra V W),
      IsAdicComplete (maximalIdeal W) W ∧ Finite (ResidueField W) ∧ N < Nat.card (ResidueField W) ∧
      Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W)

def LemmaG : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K),
    IsAdicComplete (maximalIdeal V) V → Finite (ResidueField V) →
    (∀ (W KW : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field KW] [Algebra W KW] [IsFractionRing W KW]
      [Algebra V W] (f : K →+* KW), IsAdicComplete (maximalIdeal W) W → Finite (ResidueField W) →
      IsLocalHom (algebraMap V W) → (∀ a : V, f (algebraMap V K a) = algebraMap W KW (algebraMap V W a)) →
      ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) W, (∀ b, IsUnit (X b).det) →
        evalFr (MvPolynomial.map f P) (fun b => (X b).map (algebraMap W KW)) ∈ Set.range (algebraMap W KW)) →
    ∀ μ, AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap V K)

def SubstGauss : Prop :=
  ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K)
    (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (c : ∀ b, Fin (m b) → K),
    (∀ μ, AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap R K)) →
    (∀ b j k, c b j * U b j k ∈ Set.range (algebraMap R K)) →
    ∀ μ : FrVar m →₀ ℕ, AddMonoidAlgebra.coeff (substFr U P) μ * ∏ v : FrVar m, c v.1 v.2.2 ^ μ v ∈ Set.range (algebraMap R K)

def IsEquiv [DecidableEq B] (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ) : Prop :=
  ∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) ℂ),
    (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
    evalFr P (Function.update X b (X b * t)) = ReciprocityTheory.MultiplicativeHeights.triChar (a b) t * evalFr P X

def ArchTie : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ)
    (Hm U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) (nn : ∀ b, Fin (m b) → ℝ) (C La : ℝ) (r : ℕ),
    (∀ b, (Hm b).PosDef) → IsEquiv a P →
    (∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ, (∀ b, (X b).conjTranspose * Hm b * X b = 1) → ‖evalFr P X‖ ≤ C) →
    (∀ b j, 0 < nn b j) → 0 ≤ La → (∀ b, m b ≤ r) →
    (∀ b j, ReciprocityTheory.MultiplicativeHeights.hq (Hm b) (U b j) ≤ (La * nn b j) ^ 2) →
    ∀ z : FrVar m → ℂ, (∀ v : FrVar m, ‖z v‖ * nn v.1 v.2.2 ≤ 1) →
      ‖MvPolynomial.eval z (substFr U P)‖ ≤ C * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i)

def SubstHomog : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ)
    (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ), IsEquiv a P →
    ∀ μ : FrVar m →₀ ℕ, AddMonoidAlgebra.coeff (substFr U P) μ ≠ 0 → ∑ v : FrVar m, μ v = ∑ b, ∑ i, a b i

end Formalism.L2.LamCM
end
end
