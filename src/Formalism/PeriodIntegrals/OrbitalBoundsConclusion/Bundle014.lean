module

public import Formalism.PeriodIntegrals.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Skeleton
public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianLatticeFiniteness.HermLatFinMain
public import Formalism.PeriodIntegrals.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.AntitoneStar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.Bundle001
public import Formalism.PeriodIntegrals.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsOfCalculation
public import Formalism.PeriodIntegrals.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.SigmaStarEx
public import Formalism.PeriodIntegrals.Bundle016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.HighestWeightExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.KernelHarmonic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.KroneckerOneRightSwap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.SameBlockOfPosC
public import Formalism.PeriodIntegrals.Bundle019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowFormPermutationSplit.Bundle001
public import Formalism.PeriodIntegrals.Bundle021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGroupIntegrability.IsPositiveDefiniteMatrixCoefficientOfMemAlgA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaUnitary.NatWCastReal
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowFormPermutationSplit.Development

@[expose] public section

section

theorem transference_covering : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
end

section

theorem transference_successive_minima : PI.TransferenceMinima :=
  PI.Tr.transferenceMinima_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
end

section

theorem hermitian_lattice_finite : PI.HermLatFin.HermLatFin :=
  PI.HermLatFin.UnitaryGroupMassFormula.hermLatFin_main
end

section

theorem blockRatReal : PI.BlockRatReal.Stmt :=
  PI.BlockRatReal.stmt_of PI.BlockRatReal.UnitaryGroupMassFormula.evenStep PI.BlockRatReal.UnitaryGroupMassFormula.Odd.oddStep
end

section

theorem phase_norm_units : PI.PhNormUnits.Target := PI.PhNormUnits.UnitaryGroupMassFormula.norm_units_of_calculation
end

section

theorem sigma_star_exists : PI.SigmaStarEx := PI.SSE.sigmaStarEx
end

section

theorem fock_degree_one : PI.FockDegreeTwoParts.OneDeg :=
  PI.FockOneDegW.oneDeg_of
    (PI.FockOneDegW.Core.hwHarmDeg_of PI.FockOneDegW.fock_operators_kernel PI.FockOneDegW.harmIff)
    (PI.FockOneDegW.reduction_of PI.FockOneDegW.fock_inner_facts PI.FockOneDegW.kernel_highest_weight
      PI.FockOneDegW.kernel_harmonic PI.FockOneDegW.highest_weight_harmonic PI.FockOneDegW.harmonic_submodule
      PI.FockOneDegW.fock_kernel_adjoint PI.FockOneDegW.hwExist)
    PI.FockOneDegW.Swap.fock_swap_groups
end

section

theorem quantum_minor_row_form : PI.QmRowForm :=
  PI.UnitaryGroupMassFormula.QmRowForm.qmRowForm_of PI.UnitaryGroupMassFormula.QmRowForm.double_row_decreasing PI.UnitaryGroupMassFormula.QmRowForm.double_row_increasing
    PI.UnitaryGroupMassFormula.QmRowForm.double_row_permutation
end

section

theorem polynomial_coefficients : PI.PolyCoef := PI.UnitaryGroupMassFormula.PolyCoef.polyCoef
end

section

theorem weylForU_of : PI.ModelIso → PI.NablaDim → PI.WeylForU := PI.WeylForUWork.weylForU_of
end
