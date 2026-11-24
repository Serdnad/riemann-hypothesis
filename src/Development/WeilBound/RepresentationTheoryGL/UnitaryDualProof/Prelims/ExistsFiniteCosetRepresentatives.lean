module

import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.Prelims.ExistsCosetRepsOpenInCompact
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.OpenSubgroupTransversal

theorem finite_transversal {X : Type} [TopologicalSpace X] [AddCommGroup X]
    [IsTopologicalAddGroup X] (A H : AddSubgroup X) (hA : IsCompact (A : Set X))
    (hH : IsOpen (H : Set X)) (_hHA : H ≤ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  intros
  apply _root_.GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen <;> assumption

theorem main : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A →
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H :=
  fun A H hA hH hHA => GlobalTheory.CompanionTheory.OpenSubgroupTransversal.finite_transversal A H hA hH hHA

end GlobalTheory.CompanionTheory.OpenSubgroupTransversal
