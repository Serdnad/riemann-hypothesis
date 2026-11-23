module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodNonvanishingAscentOfDepthData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle653
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle483
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle516
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle487
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle575
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchPeriod
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle025
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle012
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle011
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle013
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle093
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section
namespace UpperTheory.Lit
theorem real_functionals_separate_of_hypothesis
    (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent)
    (realIn : Branch.RealInputE) :
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate := by
  have rowModels := _root_.GlobalTheory.T.exists_models_of_separating_data P
  have rowStep := _root_.GlobalTheory.T.separating_family_extend_by_twist P (_root_.GlobalTheory.T.exists_seesaw_pair_of_theta_data P) rowModels
  have rowTower := GlobalTheory.T.firstRowTower_multiplicitySpaces_of_arrow rowModels rowStep
  have conv := _root_.GlobalTheory.T.convergence_of_separating_family P rowTower
  have per := Branch.periodNe_of_eigen P.harishChandraModules P.casselmanWallach P.cuspRapidDecay realIn
  have onto := _root_.GlobalTheory.T.twist_core_surjective P P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover
    P.harishChandraModules P.casselmanWallach hHowe P.weilRepresentationUnitaryPair
    P.weilSiegelFormulaUnitary hSW P.doublingMethod P.unramifiedDoublingGL
  have weak := GlobalTheory.T.rowSeparation_by_realFunctionals_of_chain_steps GlobalTheory.T.largeScaleSizes_imply_gapConditions (_root_.GlobalTheory.T.exists_separating_models P) (_root_.GlobalTheory.T.rapid_decay_of_separating_family P rowTower) per onto
    (GlobalTheory.T.bessel_period_nonvanishing_ascent_of_depth_data GlobalTheory.T.dependence_fixed)
  exact _root_.UpperTheory.Lit.bessel_separate_of_step_gap P rowTower GlobalTheory.T.largeScaleSizes_imply_gapConditions GlobalTheory.T.goodRows_principalLevel_are_rows conv weak
end UpperTheory.Lit
end
