module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.HermitianLattices.StatementLat
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

open Matrix TensorProduct

namespace Formalism.UG

def nablaRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Representation O (GL n O) (nabla O n k) where
  toFun g := (polyAct O n g).toLinearMap.restrict (fun P hP => Formalism.UG.P.nabla_subspace_stable O n k g P hP)
  map_one' := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n 1 (P : MvPolynomial n O) = (P : MvPolynomial n O)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n (g * h) (P : MvPolynomial n O) = polyAct O n g (polyAct O n h P)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n g h).1]
    rfl

def ratEquiv {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n]
    [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R]
    [Nontrivial R] : UJ (σ : E →+* E) J ≃* ratPts σ J R :=
  Subgroup.equivMapOfInjective (UJ (σ : E →+* E) J) (bc (inclE (F := F) R))
    (Formalism.UG.P.UG_inclusion_injective F E n R inferInstance)

end Formalism.UG
end
end

section

noncomputable section

open Matrix

namespace Formalism.UG

variable {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]

def gram (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) : Matrix n n K :=
  fun i j => h (Pi.single i 1) (Pi.single j 1)

def glEquiv (g : GL n K) : (n → K) ≃ₗ[K] (n → K) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K) (Matrix.GeneralLinearGroup.toLin g)

def GlEquivApply : Prop :=
  ∀ (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] (g : GL n K) (x : n → K),
    glEquiv g x = (g : Matrix n n K) *ᵥ x

def HformGram : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (x y : n → K),
    h x y = hform (starRingEnd K) (gram h) x y

def HermBridge : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (g : GL n K),
    g ∈ UJ (starRingEnd K) (gram h) ↔ glEquiv g ∈ Formalism.HermitianLatticesTheory.isom h

def HermBridgeSurj : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K), ∀ u ∈ Formalism.HermitianLatticesTheory.isom h, ∃ g : GL n K, glEquiv g = u

end Formalism.UG
end
end
