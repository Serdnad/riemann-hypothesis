module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle085
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle107
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle111
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle099
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle002
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle018
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSectionNotMem
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

section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorLength : GroundTheory.Heights₂.Heights.Targets.ChartDivisorLength.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartDivisorLength.proof GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem.proof GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorComponents GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartSectionLength

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeAverage : GroundTheory.Heights₂.Heights.ConeAverage.Statement :=
  @GroundTheory.Heights₂.Heights.ConeAverage.proof GroundTheory.Heights₂.Heights.ConeIntegralMass.full GroundTheory.Heights₂.Heights.ChowDegreePos.proof GroundTheory.Heights₂.Heights.AutoClose.ConeFubini GroundTheory.Heights₂.Heights.AutoClose.FsLogAverage GroundTheory.Heights₂.Heights.FsLogMeasurable.proof
end

section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.IsolatedPointsCountPrime : GroundTheory.Heights₂.Heights.IsolatedPointsCountPrime.Statement :=
  @GroundTheory.Heights₂.Heights.IsolatedPointsCountPrime.proof GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly.full GroundTheory.Heights₂.Heights.AutoClose.DominantFibreBound GroundTheory.Heights₂.Heights.ImageDimLe.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.SameOrdersLiftCentre : GroundTheory.Heights₂.Heights.SameOrdersLiftCentre.Statement :=
  @GroundTheory.Heights₂.Heights.SameOrdersLiftCentre.proof GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds
end
