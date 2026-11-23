module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle036
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAvoidFormFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle091
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomCharpolyForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomNormPIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle052
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormMax
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle083
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjAvoidingForm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle076
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle086
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle077
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle089
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle033
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001

@[expose] public section

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

namespace MultiProjectiveCoordinates

theorem pull_ratios_algebraic : PullRatiosAlgebraic.Statement :=
  PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof

theorem pull_forms_generic : PullFormsGeneric.Statement := PullFormsGeneric.proof pull_ratios_algebraic

theorem fibre_pull_integral : FibreNormPullback.Statement :=
  FibreNormPullback.proof_dehom pull_forms_generic
    (FibreNormDehomCharpoly.proof pull_forms_generic pull_ratios_algebraic PullSectionIntegral.proof
      DehomCharpolyForms.proof)
    (FibreNormDehomIntegral.proof FibreNormBadPrimesFinite.proof
      (FibreNormGoodPrimeIntegral.proof GlobalTheory.T.pullback_cone_null_mod_p_holds PullConeDegreeInt.proof PullSectionIntegralInt.proof
        DehomNormPIntegral.proof)
      (FibreNormPrimeBound.proof pull_forms_generic GlobalTheory.T.norm_form_gauss_bound_holds ChartPrimePowerInverse.proof))
    FibreNormDehomRoots.full

theorem grid_separation : GridSeparation.Statement :=
  GridSeparation.proof NormalLocusRep.proof
    (FibreNormBound.proof (ProjAvoidingForm.proof SegreArith.proof)
      (FibreRepresentatives.proof AvoidFormFinite.proof)
      (FibreNormMax.proof fibre_pull_integral) MetricMaxComparison.proof)
    RootGridLower.proof

end MultiProjectiveCoordinates

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology in
theorem MultiProjectiveCoordinates.packing_statement : PackingStatement :=
  SmallPacking.proof
    (NmSectionsRankBound.proof (NmSectionsFinite.proof (Conductor.proof SecEq.proof)) SecMRankBound.full)
    (SmallSectionsSeparated.proof MultiProjectiveCoordinates.grid_separation)
