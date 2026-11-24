module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
public import Formalism.HermitianCurvature.StatementG
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

open Matrix
open Formalism.FourierDecayAlt.G

namespace Formalism.FourierDecayAlt.P.G4

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  simp [blk, h]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  apply _root_.Formalism.FourierDecayAlt.P.G2.blk_cl <;> assumption

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  apply _root_.Formalism.FourierDecayAlt.P.G2.blk_lc <;> assumption

theorem blk_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  apply _root_.Formalism.FourierDecayAlt.P.G2.blk_mul <;> assumption

theorem upperUni_det {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : u.det = 1 := by
  have h : u.BlockTriangular id := fun i j hij => hu.2 i j hij
  rw [Matrix.det_of_isUpperTriangular h]
  simp [hu.1]

theorem superSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    superSum (blk A b a e) = superSum A + b (Fin.last m) := by
  unfold superSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_cl]

theorem subSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    subSum (blk A b a e) = subSum A + a (Fin.last m) := by
  unfold subSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_lc]

end Formalism.FourierDecayAlt.P.G4

namespace Formalism.FourierDecayAlt.P

open G4

end Formalism.FourierDecayAlt.P
