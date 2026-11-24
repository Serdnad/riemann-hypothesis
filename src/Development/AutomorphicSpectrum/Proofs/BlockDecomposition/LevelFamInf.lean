module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FinConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv

@[expose] public section

noncomputable section

open NumberField GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.FC

namespace GlobalTheory.CompanionTheory.FamClP

section Generic

variable {H : Type} [Group H]

theorem mem_rStab' {u : H → ℂ} {r : H} : r ∈ rStab u ↔ ∀ x, u (x * r) = u x := Iff.rfl

theorem hint_zero (K : Subgroup H) : hint K (fun _ => (0 : ℂ)) = 0 := by
  simp [hint]

theorem rStab_left (u : H → ℂ) (k : H) : rStab (fun z => u (k * z)) = rStab u := by
  ext r
  rw [mem_rStab', mem_rStab']
  constructor
  · intro h x
    simpa [mul_assoc] using h (k⁻¹ * x)
  · intro h x
    simpa [mul_assoc] using h (k * x)

theorem hint_left (K : Subgroup H) (u : H → ℂ) (k : H) :
    hint K (fun z => u (k * z)) = hint K u := by
  apply _root_.PositivityTheory.Rg.BcB.F.FinConv.hint_left <;> assumption

theorem rStab_ind (K : Subgroup H) : rStab ((K : Set H).indicator (1 : H → ℂ)) = K := by
  ext r
  rw [mem_rStab']
  constructor
  · intro h
    by_contra hr
    have := h 1
    simp [Set.indicator, hr, one_mem] at this
  · intro hr x
    by_cases hx : x ∈ K
    · have hxr : x * r ∈ K := mul_mem hx hr
      simp [Set.indicator, hx, hxr]
    · have hxr : x * r ∉ K := fun h => hx (by simpa using mul_mem h (inv_mem hr))
      simp [Set.indicator, hx, hxr]

theorem hint_ind (K : Subgroup H) : hint K ((K : Set H).indicator (1 : H → ℂ)) = 1 := by
  apply _root_.PositivityTheory.Rg.BcB.F.FinConv.hint_ind <;> assumption

variable [TopologicalSpace H]

variable [IsTopologicalGroup H]

end Generic

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

end Fam

end GlobalTheory.CompanionTheory.FamClP

end
