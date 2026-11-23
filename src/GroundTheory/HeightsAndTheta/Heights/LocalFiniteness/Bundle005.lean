module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjGenericRank
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalChartLength
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocalChart
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartTrdeg
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalIntegral
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartSpecCount
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

theorem GroundTheory.Heights₂.Heights.AutoClose.MahlerSectionOfConst : GroundTheory.Heights₂.Heights.MahlerSectionOfConst.Statement :=
  @GroundTheory.Heights₂.Heights.MahlerSectionOfConst.proof GroundTheory.Heights₂.Heights.AutoClose.DefectAverage GroundTheory.Heights₂.Heights.AutoClose.AdmissibleAENrm GroundTheory.Heights₂.Heights.BallVolume.proof
end

section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_ChartSpecCount : GroundTheory.Heights₂.Heights.Inter.ChartSpecCount.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.ChartSpecCount.proof GroundTheory.Heights₂.Heights.Inter.ChartPrimElt.proof GroundTheory.Heights₂.Heights.Inter.LocAwaySpec.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_R1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.full

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartLocDim.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof GroundTheory.Heights₂.Heights.FieldNumbers.MChartDehomog.proof GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocNoetherian.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocNoetherian.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocNoetherian.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarNumerator.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarNumerator.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocLocal.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocal.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalIntegral.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.ValuativeCentre.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingIsLocal.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingIsLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingIsLocal.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffLocal.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffLocal.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleSpanMul.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocCyclePos.proof GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimesSpanSingleton.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocalDomainDimTwo.proof GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg.proof GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingNoetherian.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocCycleLocalQuot.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleLocalQuot.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleLocalQuot.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpDecomposition.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpDecomposition.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpModel.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpStrictTransform.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpOrderLe.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpOrderLe.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpOrderLe.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalizedQuotLength.proof GroundTheory.Heights₂.Heights.NumbersDVR.LengthMapIdealLe.proof GroundTheory.Heights₂.Heights.NumbersDVR.IntermediateRingQuotLength.proof GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpLocalChart.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalMult.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMult.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMult.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMinimal.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalChartLength.full

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalQuotFinsum.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotFinsum.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotFinsum.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof
end
