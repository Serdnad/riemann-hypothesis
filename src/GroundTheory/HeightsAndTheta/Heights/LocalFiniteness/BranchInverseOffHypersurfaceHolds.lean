module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle084
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMLengthParameters
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle080
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle103
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle091
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle074
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle085
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle096
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.InjectiveHolomorphicJacobianNeZeroHolds
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.ParametrisationSheetsConnectedHolds
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

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.DivisorRegularGeneric : GroundTheory.Heights₂.Heights.DivisorRegularGeneric.Statement :=
  @GroundTheory.Heights₂.Heights.DivisorRegularGeneric.proof GroundTheory.Heights₂.Heights.AutoClose.FrameGraphGeneric

theorem GroundTheory.Heights₂.Heights.AutoClose.CMLengthParameters.{u} : GroundTheory.Heights₂.Heights.CMLengthParameters.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.CMLengthParameters.proof.{u} GroundTheory.Heights₂.Heights.CMRegularElement.proof GroundTheory.Heights₂.Heights.AutoClose.LengthLocalizedQuotient

theorem GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffFinite : GroundTheory.Heights₂.Heights.CurveRegularOffFinite.Statement :=
  @GroundTheory.Heights₂.Heights.CurveRegularOffFinite.proof GroundTheory.Heights₂.Heights.AutoClose.FrameGraphGeneric GroundTheory.Heights₂.Heights.CurveProperClosedFinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.regular_off_hypersurface_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularOffHypersurface.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularOffHypersurface.proof GroundTheory.Heights₂.Heights.AutoClose.FrameGraphGeneric

theorem GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationLength : GroundTheory.Heights₂.Heights.CurveNormalisationLength.Statement :=
  @GroundTheory.Heights₂.Heights.CurveNormalisationLength.proof GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationFinite GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationQuotientLength GroundTheory.Heights₂.Heights.ExtensionQuotientLength.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.SliceCMUnmixed : GroundTheory.Heights₂.Heights.SliceCMUnmixed.Statement :=
  @GroundTheory.Heights₂.Heights.SliceCMUnmixed.proof GroundTheory.Heights₂.Heights.AutoClose.CMQuotientUnmixed

theorem GroundTheory.Heights₂.Heights.AutoClose.UniformiserLocallyInjective : GroundTheory.Heights₂.Heights.UniformiserLocallyInjective.Statement :=
  @GroundTheory.Heights₂.Heights.UniformiserLocallyInjective.proof GroundTheory.Heights₂.Heights.AutoClose.UniformiserGradientIndependent GroundTheory.Heights₂.Heights.PolynomialChartInjective.full

theorem GroundTheory.Heights₂.Heights.AutoClose.CMLocusOpen : GroundTheory.Heights₂.Heights.CMLocusOpen.Statement :=
  @GroundTheory.Heights₂.Heights.CMLocusOpen.proof GroundTheory.Heights₂.Heights.AutoClose.CMProjDimCriterion GroundTheory.Heights₂.Heights.ProjDimSpread.proof GroundTheory.Heights₂.Heights.IdealHeightSpread.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NormalModelDisc : GroundTheory.Heights₂.Heights.NormalModelDisc.Statement :=
  @GroundTheory.Heights₂.Heights.NormalModelDisc.proof GroundTheory.Heights₂.Heights.AutoClose.NormalCurveRegularPoint

theorem GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadical : GroundTheory.Heights₂.Heights.GenericFibreRadical.Statement :=
  @GroundTheory.Heights₂.Heights.GenericFibreRadical.proof GroundTheory.Heights₂.Heights.AutoClose.GenericFibreTor GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadicalPrime

theorem GroundTheory.Heights₂.Heights.AutoClose.injective_holomorphic_open_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicOpen.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicOpen.proof GroundTheory.Heights₂.Heights.AutoClose.invariance_of_domain_holds

theorem GroundTheory.Heights₂.Heights.AutoClose.branch_inverse_off_hypersurface_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchInverseOffHypersurface.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchInverseOffHypersurface.proof GroundTheory.Heights₂.Heights.AutoClose.injective_holomorphic_inverse_holds GroundTheory.Heights₂.Heights.AutoClose.projection_injective_off_hypersurface_holds
