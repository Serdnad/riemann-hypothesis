module

public import Mathlib.Algebra.Group.End
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.Continuity
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.ReesAlgebra
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace CutByFormField

theorem vecCons_comp_finRotate {α : Type*} {n : ℕ} (c : α) (bs : Fin n → α) :
    Matrix.vecCons c bs ∘ finRotate (n + 1) = Fin.snoc (α := fun _ => α) bs c := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · rw [Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.snoc_castSucc,
      Matrix.cons_val_succ]

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

end CutByFormField

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

section Lemmas

def PowSpanFinrankBounded.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A],
    ringKrullDim A = 1 → ∀ I : Ideal A, ∃ e : ℕ, ∀ n : ℕ, (I ^ n).spanFinrank ≤ e

def PrincipalReductionOfBoundedGens.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A),
    (∃ e : ℕ, ∀ n : ℕ, (I ^ n).spanFinrank ≤ e) →
      ∃ k : ℕ, 1 ≤ k ∧ ∃ y ∈ I ^ k, ∃ n : ℕ, I ^ (n + k) = Ideal.span {y} * I ^ n

end Lemmas

section Examples

end Examples

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PairConeLinesIndep.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (Φ : Type) [Field Φ] [Algebra Ω Φ] (K : Type) (N : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (e : Module.Basis (Fin N) Ω E) (ψ : Fin N → Module.Dual Ω E),
    LinearIndependent Ω ψ → ∀ (t : Fin N → Φ), AlgebraicIndependent Ω t → ∀ g : Φ, g ≠ 0 →
      AlgebraicIndependent
        (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
        (Sum.elim (fun i : Fin N => C (∑ j, t j * algebraMap Ω Φ (ψ i (e j))) * X (some none))
          (fun _ : Unit => (C g * X none : MvPolynomial (Option (Option K)) Φ)))

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def AdjoinTrdegAdd.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (L : Type) [CommRing L] [IsDomain L] [Algebra R L],
    Function.Injective (algebraMap R L) →
    ∀ (s t : Set L) (ι : Type) [Fintype ι] (x : ι → L), Set.range x ⊆ t →
      AlgebraicIndependent (Algebra.adjoin R s) x →
      (∀ a ∈ t, IsAlgebraic (Algebra.adjoin R (s ∪ Set.range x)) a) →
      Algebra.trdeg R (Algebra.adjoin R (s ∪ t)) =
        Algebra.trdeg R (Algebra.adjoin R s) + (Fintype.card ι : Cardinal)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

def DimensionInequality.Statement : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.FiniteType A B], Function.Injective (algebraMap A B) →
    ∀ (P : Ideal B) [P.IsPrime],
      Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (B ⧸ P) ≤
        Cardinal.ofENat (P.under A).height + Algebra.trdeg A B

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

open Polynomial

def PolynomialPrimeOverZeroHeight.Statement : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] (Q : Ideal D[X]) [Q.IsPrime],
    Q.comap (C : D →+* D[X]) = ⊥ → Q.height ≤ 1

def QuotientHeightAddOne.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (I : Ideal R), I ≠ ⊥ →
    ∀ (P : Ideal (R ⧸ I)) [P.IsPrime], P.height + 1 ≤ (P.comap (Ideal.Quotient.mk I)).height

def PolynomialDimensionInequality.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (P : Ideal A[X]) [P.IsPrime],
    Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P) ≤
      Cardinal.ofENat (P.under A).height + 1

def DimensionInequalityOneGenerator.Statement : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (x : B), Algebra.adjoin A {x} = ⊤ → Function.Injective (algebraMap A B) →
    ∀ (P : Ideal B) [P.IsPrime],
      Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (B ⧸ P) ≤
        Cardinal.ofENat (P.under A).height + Algebra.trdeg A B

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

def MaximalIdealHeightFG.Statement : Prop :=
  ∀ (F : Type u) [Field F] (A : Type u) [CommRing A] [IsDomain A] [Algebra F A]
    [Algebra.FiniteType F A] (m : Ideal A), m.IsMaximal → (m.height : WithBot ℕ∞) = ringKrullDim A

section Examples

end Examples

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

def ReesAlgebraDim.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (I : Ideal A), I ≠ ⊥ →
    ∀ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) → ringKrullDim (reesAlgebra I) = ((n + 1 : ℕ) : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
