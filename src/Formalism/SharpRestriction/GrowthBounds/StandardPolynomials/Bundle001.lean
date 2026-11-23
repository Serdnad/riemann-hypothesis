module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle001
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def usedX (X : Loc) (β : GlobalTheory X) (a0 : Fin (numSeg X.TT) → ℕ) (j0 j : Fin (numSeg X.TT)) : ℕ :=
  X.p ^ segG X.TT j * a0 j + X.p ^ segG X.TT j * (∑ i : Fin (segS X.TT j), (β j).sg i) +
    (∑ i : Fin (segS X.TT j), X.p ^ (segDists X.TT j).get i * ((∑ c : Fin X.m, (β j).rz i c.succ) + (β j).ry i 0)) +
    X.c * (X.m * (X.p ^ segG X.TT j - 1)) + (if j = j0 then X.c else 0)

def RoomAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc), D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ a0 : Fin (numSeg X.TT) → ℕ,
      (∀ j, (a0 j : ℤ) + ∑ i : Fin (segS X.TT j),
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg i : ℤ) else 0) ≤ (X.seg C0 CE1 CE2 j).A0 X.p) →
    ∀ j0 j : Fin (numSeg X.TT),
      usedX X β a0 j0 (rot _ j) ≤ segAPlus X.TT X.aT j - (β j).oPlus

def RestRoom : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => RoomAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def ColumnNumericsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc), D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j b →
      (∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (b.sg l : ℤ) else 0)) ≤
          ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - (mm + (n : ℝ) * ka1 X)⌋ ∧
      ∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
        (∑ l : Fin (segS X.TT j), (if (l : ℕ) ≤ (i : ℕ) then (b.w l : ℤ) else 0)) +
          (∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (b.sg l : ℤ) else 0)) ≤
          ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - (mm + (n : ℝ) * ka1 X)⌋

def ColumnNumericsBeyond : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ColumnNumericsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def NumCoreAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc), D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c → ∀ e : ℕ, 1 ≤ e → e < n →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j b →
      (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ (i : ℕ) →
        1 + 2 * (X.p ^ X.G' * e) + b.o i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b i) ∧
      ∀ b' : SegBlock (segS X.TT j) X.m,
        DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b' →
        (∀ i, coarseA X.p (X.seg C0 CE1 CE2 j) b i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b' i + (X.m + 1)) →
        (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ (i : ℕ) →
          b'.o i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b' i ∧ b'.o i ≤ b.o i + 2 * ((X.m + 1) + X.p ^ X.G' * e) ∧
          b'.w i = 0 ∧ b'.sg i = 0) →
        (∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
          b'.o i = 0 ∧ b'.w i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b' i ∧
          b'.sg i ≤ coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b' i ∧
          b'.sg i ≤ b.sg i + ((X.m + 1) + X.p ^ X.G' * e) ∧ b'.w i ≤ b.w i + ((X.m + 1) + X.p ^ X.G' * e)) →
        b'.oPlus ≤ segAPlus X.TT X.aT j → b'.oPlus ≤ b.oPlus + X.p ^ X.G' * e →
        BLk C0 Cde CE1 CE2 X (((X.c - (n - e) : ℕ) : ℝ) * ka1 X) j b' ∧
        ∀ (l : ℕ) (V : ℤ), V ≤ ((X.N1 : ℤ) + 1) * (((X.m : ℤ) + 1) + (X.p : ℤ) ^ X.G' * e) →
          ⌊((cap X.p (X.seg C0 CE1 CE2 j) b l : ℤ) : ℝ) - (mm + (n : ℝ) * ka1 X)⌋ + ((X.N1 * e : ℕ) : ℤ) + V ≤
            ⌊((cap X.p (X.seg C0 CE1 CE2 j) b' l : ℤ) : ℝ) - (mm + ((n - e : ℕ) : ℝ) * ka1 X)⌋

def RestNumCore : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => NumCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end
