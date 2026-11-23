module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle070
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle059
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle066
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle096
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockComplexGramMetricChange
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockDefectMetricChange
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageDatum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle082
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockRealGramComparison
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle069
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexGramMetricChange
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle052
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle058
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle073
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseTop
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle009
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem TheoremHSMBlock.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionImageSup.Statement)
    (h11 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionDegreeIntegral.Statement)
    (h12 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.Statement)
    (h13 : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (h14 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.Statement)
    (h15 : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel.Statement)
    (h16 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphDeg.Statement)
    (h17 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGramMono.Statement)
    (h18 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphDeg.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSMBlock.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSMBlock.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjectiveBlock.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockMetricChange.proof BlockMeasureChange.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockDefectMetricChange.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockRealGramComparison.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionSupBound.proof h10 NonvanishingDense.full) SupBoundBlock.full
  SupBoundCount.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockComplexGramMetricChange.proof MetricChange.full
  BlockResolutionMetricPair.full BlockResolutionFormsIndependent.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionDegree.proof BlockSectionsRank.full h11))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedIntegral.proof h12 BlockResolutionInterpIntegral.full)
  (GroundTheory.Heights₂.Heights.PtsIntegrable.of_found h13 Closed.PtsSumMeasurable)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageDatum.proof BlockImageArith.full h14 AnResNullForm.full
  BlockImageMetrics.full BlockImageChi.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageTop.proof h15
  BlockGraphImage.full h16) BlockImageGenDeg.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SecondVeronese.proof VeroneseArith.full VeroneseSemipos.full
  VeroneseResolution.full (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseChi.proof VeroneseMonoBasis.full h17)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseTop.proof h15 VeroneseArith.full VeroneseGraphImage.full h18)
  VeroneseGenDeg.full) PointHeightFS.full) SupBoundBlock.full)

end GroundTheory.Heights₂.Heights.HilbertSamuel
