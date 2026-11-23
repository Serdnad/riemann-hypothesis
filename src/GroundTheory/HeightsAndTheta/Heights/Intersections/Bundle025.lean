module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle022
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.RingHom.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
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
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle021
public import Mathlib.RingTheory.LocalRing.Length

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def AddAt {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (W : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A C : HermLine ι),
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm C →
    I W (n + 1) (Fin.snoc L (A.tensor C)) = I W (n + 1) (Fin.snoc L A) + I W (n + 1) (Fin.snoc L C)

def RPositionAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A C B : HermLine ι) (s : MRing ι),
    AddAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSmoothHerm C → IsSmoothHerm B → IsSectionOn P B s →
    recR I P (Fin.snoc L (A.tensor C)) B s = recR I P (Fin.snoc L A) B s + recR I P (Fin.snoc L C) B s

def WellDefined.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin (n + 1) → HermLine ι) (B : HermLine ι) (s t : MRing ι),
    HasRAt I n → AddAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
    IsSectionOn P B s → IsSectionOn P B t → recR I P L B s = recR I P L B t

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityRelativeClosedPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    IsArithVar P 1 → IsMultiProjPrime W → P ≤ W → W ≠ P → IsClosedPt W

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityDivisorSupportClosed.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (s : MRing ι) (a : K → ℕ)
    (W : Ideal (MRing ι)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → (W ∈ divSupp P s ↔ IsClosedPt W ∧ P ≤ W ∧ s ∈ W)

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial IsLocalRing
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

noncomputable section

namespace BCMultProof

theorem length_quot_map_of_flat {A L : Type*} [CommRing A] [IsLocalRing A] [CommRing L]
    [IsLocalRing L] (φ : A →+* L) [IsLocalHom φ] (hflat : φ.Flat)
    (hmax : (maximalIdeal A).map φ = maximalIdeal L) (J : Ideal A) :
    Module.length L (L ⧸ J.map φ) = Module.length A (A ⧸ J) := by
  let _ := φ.toAlgebra
  have : Module.Flat A L := hflat
  have : IsLocalHom (algebraMap A L) := ‹IsLocalHom φ›
  have key := IsLocalRing.length_baseChange A L (A ⧸ J)
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L J).toLinearEquiv.length_eq,
    RingHom.algebraMap_toAlgebra, hmax] at key
  have h1 : Module.length L (L ⧸ maximalIdeal L) = 1 :=
    Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩)
  rw [h1, mul_one] at key
  exact key

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]


end BCMultProof

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalFormDivisor

set_option linter.unusedSectionVars false

section Generic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

theorem aeval_scale (u : K → Φ) (c : (Σ k, ι k) → Φ) (s : MRing ι) (β : K → ℕ) (hs : IsMultiHomog s β) :
    aeval (fun p => u p.1 * c p) s = (∏ k, u k ^ β k) * aeval c s := by
  have h1 := congrArg (MvPolynomial.eval u) (DiagRAux.multiConeMap_of_homog c s β hs)
  have h2 : (MvPolynomial.eval u).comp (T.multiConeMap c) =
      (aeval (fun p => u p.1 * c p) : MRing ι →ₐ[ℤ] Φ).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp [T.multiConeMap]) (fun p => by simp [T.multiConeMap, mul_comm])
  rw [← RingHom.comp_apply, h2, map_mul, eval_C, map_prod] at h1
  simp only [map_pow, eval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
  rw [h1, mul_comm]

end Generic

section Geometry

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
  [Algebra Ω Φ]

end Geometry

end DiagonalFormDivisor


end

end GroundTheory.Heights₂.Heights.Inter
end
