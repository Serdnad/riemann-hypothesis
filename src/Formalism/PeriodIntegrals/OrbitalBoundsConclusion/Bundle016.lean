module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCardinality.UniMatUpper
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalPointsComparison.BridgeApplyEqOfComp
public import Formalism.PeriodIntegrals.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.CcPrEq
public import Formalism.PeriodIntegrals.Bundle018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
public import Formalism.PeriodIntegrals.Bundle019
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle011
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderSignIdentity.SkipOneEqSuccAbove
public import Formalism.PeriodIntegrals.Bundle023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalInclusion.SmulMemIdealSmul
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

@[expose] public section

section

theorem mirabolic_card_unipotent : Formalism.L2.SG.GGMirabolic.CardUni := PI.GGCardUniWork.cardUni
end

section

theorem adelic_rational_points : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeGF I :=
  Formalism.L2.SG.AdBridge.adBridgeGF_main
end

section

theorem formal_group_tri_factor : PI.FglTriFactor.Lemma := PI.FglTriFactor.Wk.main
end

section

theorem algebraic_values_finite (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  PI.AlgValsFin.W.algValsFin_main L

theorem algValsFin (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  algebraic_values_finite L
end

section

theorem quantum_minor_border_es : PI.QmBorderES := PI.UnitaryGroupMassFormula.QmBorderES.qmBorderES_of quantum_minor_column_expansion quantum_minor_row_expansion
end

section

theorem sc_psi_exists : PI.ScPsiExists.Target :=
  PI.ScPsiExists.UnitaryGroupMassFormula.norm_units_of_calculation
end

section

namespace PI

theorem local_global_inclusion' : PI.LocGlobIncl := PI.LocGlobInclWork.main

end PI
end
