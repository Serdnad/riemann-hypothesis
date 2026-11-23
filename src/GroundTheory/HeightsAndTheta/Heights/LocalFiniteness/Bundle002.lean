module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle112
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle084
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCentredDiscCoverCurve
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle094
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle097
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle108
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle109
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle077
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle083
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
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

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartSectionLength : GroundTheory.Heights₂.Heights.Targets.ChartSectionLength.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartSectionLength.proof GroundTheory.Heights₂.Heights.Targets.ChartConeComponent.proof GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartConeLength

theorem GroundTheory.Heights₂.Heights.AutoClose.FsLogAverage : GroundTheory.Heights₂.Heights.FsLogAverage.Statement :=
  @GroundTheory.Heights₂.Heights.FsLogAverage.proof GroundTheory.Heights₂.Heights.BallAverageLinear.proof GroundTheory.Heights₂.Heights.FsLogPointOf.proof GroundTheory.Heights₂.Heights.AutoClose.SphereMeanLinearBall GroundTheory.Heights₂.Heights.BallVolume.proof
end

section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LogIntegrable : GroundTheory.Heights₂.Heights.LogIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.LogIntegrable.proof GroundTheory.Heights₂.Heights.SheetSumMeasurable.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompare GroundTheory.Heights₂.Heights.VarSlabMeasure.full GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite

theorem GroundTheory.Heights₂.Heights.AutoClose.VarIntAdd : GroundTheory.Heights₂.Heights.VarIntAdd.Statement :=
  @GroundTheory.Heights₂.Heights.VarIntAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.BranchGermDimOne : GroundTheory.Heights₂.Heights.BranchGermDimOne.Statement :=
  @GroundTheory.Heights₂.Heights.BranchGermDimOne.proof GroundTheory.Heights₂.Heights.LocalDimComponentBound.proof GroundTheory.Heights₂.Heights.ZeroDimIsolated.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.full

theorem GroundTheory.Heights₂.Heights.AutoClose.DominantFibreBound : GroundTheory.Heights₂.Heights.DominantFibreBound.Statement :=
  @GroundTheory.Heights₂.Heights.DominantFibreBound.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full

theorem GroundTheory.Heights₂.Heights.AutoClose.branchFillDimension_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.centredDiscCoverCurve_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.full

theorem GroundTheory.Heights₂.Heights.AutoClose.PlaceOnComponent : GroundTheory.Heights₂.Heights.PlaceOnComponent.Statement :=
  @GroundTheory.Heights₂.Heights.PlaceOnComponent.proof GroundTheory.Heights₂.Heights.ReducedNormalisationPlace.proof GroundTheory.Heights₂.Heights.CurveMinimalPrimeQuotient.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem GroundTheory.Heights₂.Heights.AutoClose.LelongLimitOffZero : GroundTheory.Heights₂.Heights.LelongLimitOffZero.Statement :=
  @GroundTheory.Heights₂.Heights.LelongLimitOffZero.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.VarMassNearSmall : GroundTheory.Heights₂.Heights.VarMassNearSmall.Statement :=
  @GroundTheory.Heights₂.Heights.VarMassNearSmall.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact
end
