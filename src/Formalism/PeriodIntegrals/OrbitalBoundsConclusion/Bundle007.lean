module

public import Formalism.PeriodIntegrals.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.DiffLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.DualFunctionalsExist
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.Bundle001
public import Formalism.PeriodIntegrals.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeArea.ImConjMulCombo
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NonzeroDiscriminants.DiscMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingIdentity.FoldUnfoldMain
public import Formalism.PeriodIntegrals.Bundle013
public import Formalism.PeriodIntegrals.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SymmetricDistance.SymDistOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.T2SpaceOfNonarchimedeanLocalField
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TraceDualLocal.Imports
public import Formalism.PeriodIntegrals.Bundle014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BallQuotientLength.LengthBallQuotientEqSumMulFdeg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeSaturation.LocLatSat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.EfRankSumMain
public import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.BlockDiagonalPreservesDegree
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.FockInnerEqSumRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

theorem locFramePrim : PI.LocFramePrim.Statement :=
  PI.LocFramePrimWork.Steps_top PI.LocFramePrimWork.localDifferentPowerSpan PI.LocFramePrimWork.dualFunctionalsExist
    PI.LocFramePrimWork.primitiveOfDualFunctionals
end

section

theorem weak_approximation_dvr : PI.WeakApproxDVR :=
  PI.WA.weakApproxDVR_of PI.WA.big_existence_holds PI.WA.rho_projection_assembly
end

section

theorem area_lattice_formula : PI.AreaLat := PI.AreaLatWork.areaLat
end

section

theorem discrNe' : PI.DiscrNe := DiscrNeWork.discrNe_all
end

section

theorem lintegralTransversalSum : PI.FoldUnfold.FoldUnfold :=
  PI.FoldUnfold.UnitaryGroupMassFormula.foldUnfold_main
end

section

theorem symDist_of : PI.ExpTri → PI.SymDist := PI.SymDistWork.symDist_of
end

section

theorem trace_dual_local : PI.TrDualLoc.Stmt := by
  intro K _ _ p _ Fp _ _ _ _ _ hc hfin ι hd _ t ht c hcO
  haveI : CharZero Fp :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp).injective
  exact PI.TrDualLocW.main hc hfin ι (PI.CntNotIntW.tensorLiftSurjective K _ Fp hc hfin ι hd) t ht c hcO
end

section

theorem ball_quotient_length : PI.BallQuotLen := PI.UnitaryGroupMassFormula.BallQuotLen.ballQuotLen_main
end

section

theorem inf_eq_inter_span : PI.LocLatSat.Stmt := PI.LocLatSat.UnitaryGroupMassFormula.locLatSat
end

section

theorem ramificationDegreeSum : PI.EfRankSum := PI.UnitaryGroupMassFormula.EfRankSum.efRankSum_main
end

section

theorem gradedOscillatorProperty : FockH1Action.H1 :=
  FockRL.gradedOscillatorProperty_of FockRL.blockDiagonalPreservesDegree
    (FockRL.pcStep_of FockRaiseLowGrade.raisingLoweringSplit)
    (FockRL.adjStep_of FockRaiseLowGrade.raisingLoweringSplit FockRaiseLowInner.fischerConjLinearLeft
      FockRaiseLowInner.fischerLinearRight FockRaiseLowInner.fischerXAdjoint)
    FockRL.kroneckerProperties
end
