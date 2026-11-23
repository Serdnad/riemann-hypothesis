module

public import Formalism.PeriodIntegrals.Bundle016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselLeviAction.MulVecBvecApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.AdditiveCharacterNontrivial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExInst
public import Formalism.PeriodIntegrals.Bundle018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LargeStabilizerInverse.GLeftInv
public import Formalism.PeriodIntegrals.Bundle023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.AdelClassFinOfSvReal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorReal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.MeasureContractionFormula
public import Formalism.PeriodIntegrals.Bundle026
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.QnCovHat2OfLin
public import Formalism.PeriodIntegrals.Bundle027
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.ContinuousRootCoords
public import Formalism.PeriodIntegrals.HwFixedLine
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightFixedVectors.HwFixedExMain
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.Development

@[expose] public section

section

theorem bessel_levi_formula : PI.BesselLevi.BesselLevi :=
  PI.UnitaryGroupMassFormula.BesselLevi.main
end

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

theorem omUnique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : ℕ) :
    PI.OmFibreUniq.OmUnique σ J ψ v a :=
  PI.OmFibreUniq.W.omUnique_of_sdEx
    (PI.OmFibreUniq.W.SdInst.sdEx_of_psiNT PI.OmFibreUniq.W.Sd.additive_character_nontrivial) σ J ψ v a
end

section

theorem stabilizer_large : PI.StabBig := PI.StabBigW.stabBig
end

section

theorem adelic_class_set_finite : PI.AdelClassFin.AdelClassFin :=
  PIW.AdelClassFin.adelClassFin_of_svReal PIW.AdelClassFin.successive_vector_real
end

section

theorem lattice_count_all : PI.LatCountG.LatCountAll :=
  PI.UnitaryGroupMassFormula.LCG.latCountAll_of_idx PI.UnitaryGroupMassFormula.LCG.determinant_index_formula PI.UnitaryGroupMassFormula.LCG.lattice_indexOf
end

section

namespace PI

theorem n_measure_invariant : PI.NMeasInv.Target :=
  PI.NMeasInv.UnitaryGroupMassFormula.nMeasInv_of PI.NMeasInv.UnitaryGroupMassFormula.measure_contraction_formula

end PI
end

section

theorem covariant_hat_sq_of_lin : PI.QnCovLin → PI.QnCovHat2 := PI.QnCovHat2W.qnCovHat2_of_lin
end

section

theorem amplifier_root_jacobian : PI.AmpRoot.RootJac := PI.AmpRootJacW.rootJac
end

section

theorem highest_weight_fixed_exists : PI.HwFix.HwFixedEx := PI.HwFix.UnitaryGroupMassFormula.hwFixedEx_main
end
