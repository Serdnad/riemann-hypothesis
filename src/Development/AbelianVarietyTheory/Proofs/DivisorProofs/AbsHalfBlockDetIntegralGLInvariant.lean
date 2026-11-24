module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AntitoneZeroOneEqOfSumEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.AbsHalfInv

theorem v_det_KGL {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v (k.val.det) = 1 := by
  apply _root_.GlobalTheory.valued_det_eq_one_of_glint <;> assumption

theorem v_det_mul_left {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k m : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v ((k * m).val.det) = Valued.v m.val.det := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_det_KGL hk, one_mul]

theorem v_det_mul_right {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k m : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v ((m * k).val.det) = Valued.v m.val.det := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_det_KGL hk, mul_one]

theorem absHalf_congr {E : Type} [Field E] [NumberField E] {w : Pl E} {x y : w.adicCompletion E}
    (h : Valued.v x = Valued.v y) : absHalf w x = absHalf w y := by
  have : ordL x = ordL y := by unfold ordL; simp only [h]
  unfold absHalf
  rw [this]

end GlobalTheory.BCT.AbsHalfInv

open GlobalTheory.BCT.AbsHalfInv in
theorem GlobalTheory.BCT.absHalf_blockDet_KGL_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m k : GLw a w × GLw b w),
    k.1 ∈ GlobalTheory.LFun.KGL w (n := a) → k.2 ∈ GlobalTheory.LFun.KGL w (n := b) →
    absHalf w ((k * m).1.val.det ^ b / (k * m).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) ∧
      absHalf w ((m * k).1.val.det ^ b / (m * k).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
  intro E _ _ _ a b w m k h1 h2
  refine ⟨absHalf_congr ?_, absHalf_congr ?_⟩
  · rw [map_div₀, map_div₀, map_pow, map_pow, map_pow, map_pow, Prod.fst_mul, Prod.snd_mul,
      v_det_mul_left h1, v_det_mul_left h2]
  · rw [map_div₀, map_div₀, map_pow, map_pow, map_pow, map_pow, Prod.fst_mul, Prod.snd_mul,
      v_det_mul_right h1, v_det_mul_right h2]
