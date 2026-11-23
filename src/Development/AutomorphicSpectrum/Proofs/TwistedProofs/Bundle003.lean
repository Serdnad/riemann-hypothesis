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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle091
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle658
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle092
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle090

@[expose] public section

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.double_coset_swap : DosetSwap :=
  @_root_.GlobalTheory.T.biInvariant_replace_same_double_coset_sums
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.generating_function_identity : GenFun :=
  @_root_.GlobalTheory.T.length_count_generating_series_formula
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.heisenberg_matrix_facts : Heis :=
  @_root_.GlobalTheory.T.unitary_heisenberg_radical_coordinates
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.additive_vector_exists : AddVec :=
  @_root_.GlobalTheory.T.lattice_add_vector_det_valuation
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.cosetIntegral' : CosetIntegral :=
  @_root_.GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.dual_pairing_exists : Dual :=
  @_root_.GlobalTheory.T.dual_inter_eq_sum'
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.small_corner_of_heisenberg_dual : Heis → Dual → SmallCorner :=
  @_root_.GlobalTheory.T.small_corner_of_heisenberg_duality
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.coset_injective : CosetInj :=
  @_root_.GlobalTheory.T.unitary_iwasawa_cells_disjoint
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.pointwise_of_span_heisenberg : AddVec → Dual → SpanEq → Heis → Pointwise :=
  @_root_.GlobalTheory.T.leviRadicalProductLength_of_lattice_steps
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.trace_index_formula : TraceIndex :=
  @_root_.GlobalTheory.T.traceZero_integers_index_in_uniformizer_multiples
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.smith_normal_form_exists : Smith :=
  @_root_.GlobalTheory.T.elementaryDivisors_exist_discretelyValued
end
