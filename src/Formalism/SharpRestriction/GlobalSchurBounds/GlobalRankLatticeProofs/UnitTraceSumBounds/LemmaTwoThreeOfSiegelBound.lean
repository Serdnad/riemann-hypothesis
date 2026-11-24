module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmInverseHalfDifferentMulRelativeDifferent
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainNotions.Ext

open Polynomial Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.UnusedSlot33.HK

variable {R : Ranks} (H : Host R)

theorem exists_gen_K : ∃ x : H.K, x ^ 2 = ((-(H.d : ℤ) : ℤ) : H.K) ∧ IntermediateField.adjoin ℚ {x} = ⊤ := by
  have hb2 : H.sqd ^ 2 = ((-(H.d : ℤ) : ℤ) : H.E) := by
    push_cast
    exact H.sqd_sq
  obtain ⟨x, hxdef⟩ : ∃ x : H.K, (x : H.E) = H.sqd :=
    ⟨⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩, rfl⟩
  refine ⟨x, ?_, gen_top H x hxdef⟩
  apply Subtype.ext
  push_cast
  rw [hxdef, hb2]
  push_cast
  rfl

theorem finrank_K : Module.finrank ℚ H.K = 2 := by
  apply _root_.GlobalTheory.Mem.PerField.finrank_K <;> assumption

theorem no_real_K : IsEmpty (H.K →+* ℝ) := by
  refine ⟨fun σ => ?_⟩
  obtain ⟨x, hx, -⟩ := exists_gen_K H
  have h := congrArg σ hx
  rw [map_pow, map_intCast] at h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have h2 := sq_nonneg (σ x)
  rw [h] at h2
  push_cast at h2
  linarith

end Formalism.MainNotions.Ext
