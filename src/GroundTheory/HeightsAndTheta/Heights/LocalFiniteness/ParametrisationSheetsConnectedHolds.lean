module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle084
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle086
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle080
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle077
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle067
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFibreRadicalPrime
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHypersurfacePresentation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInvarianceOfDomain
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle102
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle098
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle083
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle099
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.InjectiveHolomorphicJacobianNeZeroHolds
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

theorem GroundTheory.Heights₂.Heights.AutoClose.FrameGraphGeneric : GroundTheory.Heights₂.Heights.FrameGraphGeneric.Statement :=
  @GroundTheory.Heights₂.Heights.FrameGraphGeneric.proof GroundTheory.Heights₂.Heights.AutoClose.FrameJacobianGeneric GroundTheory.Heights₂.Heights.FrameImplicitGraph.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.OrdDeterminesPlace : GroundTheory.Heights₂.Heights.OrdDeterminesPlace.Statement :=
  @GroundTheory.Heights₂.Heights.OrdDeterminesPlace.proof GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationFinite

theorem GroundTheory.Heights₂.Heights.AutoClose.parametrisation_sheets_connected_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ParametrisationSheetsConnected.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ParametrisationSheetsConnected.proof GroundTheory.Heights₂.Heights.AutoClose.sheet_product_analytic_holds GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceReachesCentre.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LengthLocalizedQuotient.{u} : GroundTheory.Heights₂.Heights.LengthLocalizedQuotient.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.LengthLocalizedQuotient.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.LengthCutLocalizedModule

theorem GroundTheory.Heights₂.Heights.AutoClose.CMProjDimCriterion : GroundTheory.Heights₂.Heights.CMProjDimCriterion.Statement :=
  @GroundTheory.Heights₂.Heights.CMProjDimCriterion.proof GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower.proof GroundTheory.Heights₂.Heights.AuslanderBuchsbaumProjDimUpper.proof GroundTheory.Heights₂.Heights.RegularSequenceLengthLeDim.proof GroundTheory.Heights₂.Heights.AutoClose.CMHeightAddDim

theorem GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadicalPrime : GroundTheory.Heights₂.Heights.GenericFibreRadicalPrime.Statement :=
  @GroundTheory.Heights₂.Heights.GenericFibreRadicalPrime.proof GroundTheory.Heights₂.Heights.AutoClose.GenericFibreTor GroundTheory.Heights₂.Heights.HypersurfacePresentation.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationQuotientLength : GroundTheory.Heights₂.Heights.CurveNormalisationQuotientLength.Statement :=
  @GroundTheory.Heights₂.Heights.CurveNormalisationQuotientLength.proof GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationFinite

theorem GroundTheory.Heights₂.Heights.AutoClose.invariance_of_domain_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain.proof GroundTheory.Heights₂.Heights.AutoClose.brouwer_fixed_point_holds

theorem GroundTheory.Heights₂.Heights.AutoClose.injective_holomorphic_inverse_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof GroundTheory.Heights₂.Heights.AutoClose.injective_holomorphic_jacobian_ne_zero_holds

theorem GroundTheory.Heights₂.Heights.AutoClose.ChartIntSumOffHyperplane : GroundTheory.Heights₂.Heights.ChartIntSumOffHyperplane.Statement :=
  @GroundTheory.Heights₂.Heights.ChartIntSumOffHyperplane.proof GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof GroundTheory.Heights₂.Heights.AutoClose.ChartChangeSheetNull

theorem GroundTheory.Heights₂.Heights.AutoClose.CMQuotientUnmixed : GroundTheory.Heights₂.Heights.CMQuotientUnmixed.Statement :=
  @GroundTheory.Heights₂.Heights.CMQuotientUnmixed.proof GroundTheory.Heights₂.Heights.AutoClose.CMParameterQuotient GroundTheory.Heights₂.Heights.CMRingUnmixed.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NormalCurveRegularPoint : GroundTheory.Heights₂.Heights.NormalCurveRegularPoint.Statement :=
  @GroundTheory.Heights₂.Heights.NormalCurveRegularPoint.proof GroundTheory.Heights₂.Heights.AutoClose.NormalCurveJacobian

theorem GroundTheory.Heights₂.Heights.AutoClose.UniformiserGradientIndependent : GroundTheory.Heights₂.Heights.UniformiserGradientIndependent.Statement :=
  @GroundTheory.Heights₂.Heights.UniformiserGradientIndependent.proof GroundTheory.Heights₂.Heights.AutoClose.NormalCurveJacobian GroundTheory.Heights₂.Heights.NormalCurvePointDVR.proof
