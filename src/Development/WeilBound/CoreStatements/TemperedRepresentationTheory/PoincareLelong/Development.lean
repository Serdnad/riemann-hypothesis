module

public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle094
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle096
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle103
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepAreaCount
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle098
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepRankOne
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle089
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVarIntGraphX
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle031
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSectionNotMem
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle013
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsBilinear
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle038
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle009
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
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle010

@[expose] public section

namespace PositivityTheory.Tls2.Pl

open GroundTheory.Heights₂.Heights

theorem stokesOnVariety : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement := by
  have hDeep : TubeDeepMass.Statement :=
    TubeDeepMass.proof TubeDeepRankOne.proof
      (TubeDeepAreaCount.proof AutoClose.IsolatedPointsCount)
      HilbertSamuel.Closed.TubeDeepWeightMass
  exact StokesOnVariety.of_open HilbertSamuel.Closed.SheetImageAreaSet
    (TubeEuclMass.proof HilbertSamuel.Closed.TubeCollarMass hDeep)

theorem lelongLimit (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) :
    GroundTheory.Heights₂.Heights.LelongLimit.Statement := by
  have hGood : LelongLimitGoodPoints.Statement := LelongLimitGoodPoints.proof hBr hLim hOrd
  have hMass : LelongMassNearSmall.Statement :=
    LelongMassNearSmall.proof hReg AutoClose.VarMassNearSmall
  exact LelongLimit.proof AutoClose.LelongLimitOffZero
    (LelongLimitOnZero.proof AutoClose.LelongLimitOffZero hGood hMass AutoClose.VarIntAdd)
    AutoClose.VarIntAdd

theorem lelongPolyLimit (hL : GroundTheory.Heights₂.Heights.LelongLimit.Statement) :
    GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.Statement :=
  GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.of_mult_weight GroundTheory.Heights₂.Heights.Targets.LocalMultComap.proof
    (GroundTheory.Heights₂.Heights.Targets.LelongWeightLimit.proof hL stokesOnVariety
      GroundTheory.Heights₂.Heights.AutoClose.Targets_LelongWeightDiff)

theorem ptsAbsMeasurable (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement) :
    GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.Statement :=
  fun K _ ι _ P e Ψ L A s h1 h2 h3 h4 h5 => (hAbs K ι P e Ψ L A s h1 h2 h3 h4 h5).aestronglyMeasurable

theorem poincareLelong_of (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hLPL : GroundTheory.Heights₂.Heights.Targets.LelongPolyLimit.Statement) : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong := by
  have hPI : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement :=
    PtsIntegrable.of_found hAbs HilbertSamuel.Closed.PtsSumMeasurable
  have hStk : ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement :=
    StokesStatement.of_found (PtsBilinear.proof hAbs HilbertSamuel.Closed.PtsSumMeasurable)
      HilbertSamuel.Closed.SegrePartition
      (SegreChart.proof HilbertSamuel.Closed.SegreChartDim hSCI) stokesOnVariety
  have hChart : Targets.LelongChartLimit.Statement :=
    Targets.LelongChartLimit.proof hSCI HilbertSamuel.Closed.SegreChartDim
      Targets.ChartSectionNotMem.proof hLPL hCDC
  exact Targets.PoincareLelongAlt.of_found hStk (Targets.PoincareLelongRegularised.proof hPI (ptsAbsMeasurable hAbs))
    (Targets.PoincareLelongLimit.proof hPI (Targets.LelongSectionLimit.proof hPI hChart))

theorem poincareLelong_of_leaves (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong :=
  poincareLelong_of hAbs hSCI hCDC (lelongPolyLimit (lelongLimit hBr hLim hOrd hReg))

theorem poincareLelongInv_of_leaves (hAbs : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (hSCI : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement)
    (hCDC : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement)
    (hBr : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement)
    (hLim : GroundTheory.Heights₂.Heights.LelongLimitAtBranches.Statement)
    (hOrd : GroundTheory.Heights₂.Heights.LocalOrder.Statement)
    (hReg : GroundTheory.Heights₂.Heights.RegMassNearSmall.Statement) : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv := by
  intro K _ ι _ P n L A B s hP hL hA hB _ _ _ hB0 hs
  have h : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula :=
    poincareLelong_of_leaves hAbs hSCI hCDC hBr hLim hOrd hReg
  exact h K ι P n L A B s hP hL hA hB hB0 hs

end PositivityTheory.Tls2.Pl
