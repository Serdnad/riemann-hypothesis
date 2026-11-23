module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientIntegralBound.QuotientLIntegralLeMultiplicityLIntegral
public import Formalism.PeriodIntegrals.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CauchyBinet.WwCauchyBinetMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.WittOf
public import Formalism.PeriodIntegrals.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOfHorn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.NormDetConjExp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.Bundle001
public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaussianUniqueness.GaussUniqMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.EqZeroOfMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.Bundle001
public import Formalism.PeriodIntegrals.Bundle005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactTensorDensity.TensCpctDenOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.Bundle001
public import Formalism.PeriodIntegrals.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.Gval
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.Development

@[expose] public section

section

theorem poincareSeries_finite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesFinite G μ :=
  PI.PoincareSeriesFinite.UnitaryGroupMassFormula.poincareSeriesFinite G μ
end

section

theorem cauchy_binet_minors : PI.WwCauchyBinet.WwCauchyBinet := PI.WwCauchyBinetWork.wwCauchyBinet_main
end

section

theorem row_letter_rule : PI.RowLetter :=
  PI.RL.W.rowLetter_of PI.RL.W.chainRule PI.RL.W.vecX PI.RL.W.keyCov PI.RL.W.hdHom
end

section

theorem witt_extension_theorem : PI.WittExtension :=
  PI.Witt.witt_of PI.Witt.one_vector_holds PI.Witt.anisotropic'
end

section

theorem exp_triangle_inequality : PI.ExpTri := PI.ET.expTri_of_horn (PI.ET.horn_of PI.ET.kyFanDet)
end

section

theorem gauss_sum_unique : PI.SwBig.GaussUniq := PI.SwBig.GU.gaussUniq_main
end

section

theorem quotient_invariant : PI.QuotInv := PI.QuotInvW.quotInv
end

section

theorem unit_kronecker : PI.UnitKron :=
  PI.UnitKronW.unitKron_of PI.UnitKronW.stepA PI.UnitKronW.stepB PI.UnitKronW.stepC
end

section

theorem tensor_compact_dense : PI.TensCpctDen := PI.tensCpctDen_of compactBounded
end

section

theorem minor_identity : PI.WwMain.WwMain :=
  PI.WwMainW.wwMain_of PI.WwMainW.evalH PI.WwMainW.lH PI.WwMainW.lLin
    (PI.WwMainW.deXCB_of PI.WwMainW.cbSorted)
end

section

theorem positive_definite_form : PI.DefPosDef :=
  PI.DefPosDefWork.defPosDef_of PI.DefPosDefWork.splitting_of_extension PI.DefPosDefWork.positive_definite_second
end

section

theorem flag_gram_nonneg : PI.FlagGramNonneg := PI.UnitaryGroupMassFormula.FlagGramNonneg.main
end
