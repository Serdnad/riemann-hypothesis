module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle578
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle580
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle591
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle579
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle593
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle592
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle601
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle602
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle003
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

namespace PositivityTheory.SiegelWeilFormula.Gunr

theorem almostGood : AlmostGood :=
  almostGood_ofE GlobalTheory.T.unramified_finite_integral GlobalTheory.T.basic_character_unramified GlobalTheory.T.character_conductor_condition
    (locRingE_of GlobalTheory.T.residue_ring_structure GlobalTheory.T.fixed_field_structure GlobalTheory.T.uniformizer_existence
      (quadAt_of GlobalTheory.T.unramified_quadratic_condition_one GlobalTheory.T.unramified_quadratic_condition_two GlobalTheory.T.unramified_quadratic_condition_three GlobalTheory.T.unramified_quadratic_condition_four GlobalTheory.T.unramified_quadratic_condition_five) GlobalTheory.T.trace_dual_at_place) GlobalTheory.T.local_matrix_integral

end PositivityTheory.SiegelWeilFormula.Gunr
