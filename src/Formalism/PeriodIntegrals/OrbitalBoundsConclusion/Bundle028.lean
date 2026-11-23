module

public import Formalism.HermitianCurvature.StatementU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.DegPderivMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Expand
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ContinuousBlockDiagEmbedRingHom
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Smooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.UnitarySumCostOfParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNCut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv
public import Formalism.PeriodIntegrals.Bundle017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.FieldCountHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.LocDensCorankOfCounts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.ResidueEqZeroIff
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Development

@[expose] public section

section

theorem differential_operator_compose : Formalism.FourierDecayAlt.U.ComposeDD :=
  PI.UnitaryGroupMassFormula.UsCompose.composeDD_of (fun _ X q => PI.UnitaryGroupMassFormula.UsCompose.degDP X q)
    (fun k j ρ => PI.UnitaryGroupMassFormula.UsCompose.degD k j ρ) PI.UnitaryGroupMassFormula.UsCompose.expand
end

section

theorem operator_word_cost : Formalism.FourierDecayAlt.U.DerivativeCostFromComponents :=
  PI.UnitaryGroupMassFormula.UsCost.unitarySum_cost_of_parts PI.UnitaryGroupMassFormula.UsCost.wordsId PI.UnitaryGroupMassFormula.UsCost.letterSize PI.UnitaryGroupMassFormula.UsCost.starScale
    PI.UnitaryGroupMassFormula.UsCost.commLR PI.UnitaryGroupMassFormula.UsCost.offK PI.UnitaryGroupMassFormula.UsCost.zSmooth
    (PI.UnitaryGroupMassFormula.UsCost.zCost_of PI.UnitaryGroupMassFormula.UsCost.zSmooth PI.UnitaryGroupMassFormula.UsCost.zDeriv PI.UnitaryGroupMassFormula.UsCost.dirSize)
end

section

theorem chi_n_bilinear {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Formalism.L2.SG.NormCut.ChiNBi X :=
  PIW.NormChiNBi.chiNBi_holds X
end

section

theorem local_density_corank : PI.LocDensCorank.LocDensCorank :=
  PI.UnitaryGroupMassFormula.LocDensCorank.locDensCorank_of_counts PI.UnitaryGroupMassFormula.LocDensCorank.fieldCount_holds
    PI.UnitaryGroupMassFormula.LocDensCorank.splitCount_holds
end
