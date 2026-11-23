module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularRowLatticeTriangularBasis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle083
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledLatticePrimitiveIsotropicFrameCompletion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRadicalCosetCountOfHeisenberg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle660
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle086

@[expose] public section

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.span_equality : SpanEq :=
  @_root_.GlobalTheory.InertZeta.RowSpan.spanEq_holds
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.fraction_exists_of_smith : Smith → FracExists :=
  @_root_.GlobalTheory.InertZeta.fracExists_of_smith
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.recursion_identity : Step :=
  @_root_.GlobalTheory.InertZeta.step
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.levi_decomposition_exists : LeviExists :=
  @_root_.GlobalTheory.InertZeta.leviExists
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.small_rank_bound : SmallRank :=
  @_root_.GlobalTheory.InertZeta.smallRank
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.spherical_transitive_of_levi : LeviExists → SphTrans :=
  @_root_.GlobalTheory.InertZeta.sphTrans
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.completion_exists : Completion :=
  @_root_.GlobalTheory.FrameCompletion.completion
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.count_of_heisenberg_index : Heis → LatIndex → TraceIndex → Count :=
  GlobalTheory.InertZeta.count_of_heis
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.lattice_index_of_smith : Smith → LatIndex :=
  @_root_.GlobalTheory.InertZeta.latIndex_of_smith
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.coset_surjective_of_levi : LeviExists → CosetSurj :=
  @_root_.GlobalTheory.InertZeta.cosetSurj_of_leviExists
end
