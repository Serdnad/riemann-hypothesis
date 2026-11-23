module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Localization.FractionRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

abbrev Form (R : Type*) (n : ℕ) := Finset (Fin n) → R

def sg {n : ℕ} (I : Finset (Fin n)) (m : Fin n) : ℤ := (-1) ^ (I.filter fun j => m < j).card

variable {R : Type*} [CommRing R] {n : ℕ}

def oneF : Form R n := fun I => if I = ∅ then 1 else 0

def wedgeF (K : Form R n) (X : Fin n → R) : Form R n :=
  fun I => ∑ m ∈ I, ((sg I m : ℤ) : R) * K (I.erase m) * X m

def contrF (K : Form R n) (X : Fin n → R) : Form R n :=
  fun I => ∑ m ∈ Iᶜ, ((sg I m : ℤ) : R) * X m * K (insert m I)

def stepF (up : Bool) (K : Form R n) (X : Fin n → R) : Form R n :=
  if up then wedgeF K X else contrF K X

variable {ι : Type*}

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def HStrip {n : ℕ} (ν μ : Fin n → ℤ) (b : ℕ) : Prop :=
  (∀ m, μ m ≤ ν m) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → ν m' ≤ μ m) ∧ ∑ m, ν m - ∑ m, μ m = (b : ℤ)

def IsPath (n : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (N : ℕ) : Prop :=
  μ 0 = 0 ∧ (∀ i ≤ N, Antitone (μ i)) ∧
    ∀ i < N, if isVec i then HStrip (μ (i + 1)) (μ i) (B i) else HStrip (μ i) (μ (i + 1)) (B i)

def colHeight {n : ℕ} (μ : Fin n → ℤ) (c : ℤ) : ℕ := (univ.filter fun m => c ≤ μ m).card

variable {ι : Type*}

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

variable {ι ζ : Type*} {n : ℕ}

abbrev LVar (ι ζ : Type*) (n : ℕ) := (ι × Fin n) ⊕ ζ

def diagS (A : Type*) [CommRing A] (n : ℕ) (last : Bool) (e : ℤ) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial A) :=
  Matrix.diagonal fun a =>
    if (if last then a.val + 1 = n else a.val = 0) then LaurentPolynomial.T e else 1

def conjS {L : Type*} [CommRing L] (τ : Type*) (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (e : ℤ) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial (MvPolynomial τ L)) :=
  g.map (fun c => LaurentPolynomial.C (C c)) * diagS (MvPolynomial τ L) n last e *
    gi.map (fun c => LaurentPolynomial.C (C c))

def conjAct {k L : Type*} [CommRing k] [CommRing L] (φ : k →+* L) (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) :
    MvPolynomial (LVar ι ζ n) k →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L) :=
  eval₂Hom ((LaurentPolynomial.C).comp ((C).comp φ)) fun x =>
    match x with
    | Sum.inl (i, a) =>
      if i ∈ S then
        (if isVec i then
          Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b)))) (conjS _ g gi last 1) a
        else
          Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b))))
            (conjS _ g gi last (-1)).transpose a)
      else LaurentPolynomial.C (X (Sum.inl (i, a)))
    | Sum.inr z => LaurentPolynomial.C (X (Sum.inr z))

abbrev GenField (k : Type*) [Field k] (n : ℕ) := FractionRing (MvPolynomial (Fin n × Fin n) k)

def genMat (k : Type*) [Field k] (n : ℕ) : Matrix (Fin n) (Fin n) (GenField k n) :=
  Matrix.of fun a b => algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n) (X (a, b))

def genAct (k : Type*) [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool) :
    MvPolynomial (LVar ι ζ n) k →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) (GenField k n)) :=
  conjAct ((algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C) isVec S
    (genMat k n) (genMat k n)⁻¹ last

def valS {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : WithTop ℤ :=
  (genAct k isVec S true G).coeff.support.min

def lam1S {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : WithBot ℤ :=
  (genAct k isVec S false G).coeff.support.max

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end
