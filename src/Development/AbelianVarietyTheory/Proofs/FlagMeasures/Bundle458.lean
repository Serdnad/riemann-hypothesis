module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Bundle002
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle457
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle444
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle431
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle298
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle299
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle354
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle434
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Bundle005
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
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017

@[expose] public section

section

namespace GlobalTheory

theorem uniqGap_and_besselOfW : GlobalTheory.GapIn.UniqGap ∧ Formalism.L2.SG.LocWSOf.BesselOfW :=
  ⟨CompanionTheory.Lime.BM.uniqGap_holds, Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds⟩

end GlobalTheory
end

section

namespace GlobalTheory.TypeAsm.TopGap

theorem typeBound_of_gap :
    GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → Formalism.L2.SG.RowsPos.TypeP := by
  intro hH hBW

  have hAmp : GlobalTheory.TypeAsm.AmpP :=
    GlobalTheory.T.amplitudeBound_at_terms_of_localData (GlobalTheory.TypeAsm.locDatC_of_besselOfW hBW) (GlobalTheory.T.localDataTailBound_closedForm_largeGaps hH)

  have hPairs : GlobalTheory.TypeAsm.PairsP :=
    GlobalTheory.T.termPairCountBound_of_siegelMassRatios GlobalTheory.Mass.MaxFormula.main GlobalTheory.Mass.siegelMassRatio_holds
  exact GlobalTheory.TypeAsm.typeBound_of_amplitude_pairs hAmp hPairs

end GlobalTheory.TypeAsm.TopGap
end

section


theorem _root_.GlobalTheory.T.familyRowWeightSumUnfoldingIdentity : GlobalTheory.SnFam.FamilyWeightSumUnfoldingIdentity := by
  first | exact @GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof | exact GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof | (intros; apply GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof <;> assumption)
end

section

namespace GlobalTheory

theorem wuDecayOfGap : Formalism.L2.SG.Pf.WuDecayOfGap := CompanionTheory.Lime.BM.wuDecayOfGap_holds'

end GlobalTheory
end
