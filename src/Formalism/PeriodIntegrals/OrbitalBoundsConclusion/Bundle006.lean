module

public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.Bundle001
public import Formalism.PeriodIntegrals.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.PrimeLogOverPTop
public import Formalism.PeriodIntegrals.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.MinkowskiBoundOfSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.QLiftIsMulLeftInvariant
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.Weight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.WqUniqueOf
public import Formalism.PeriodIntegrals.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.IsExpIntegralParallelogramOfNe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.Bundle001
public import Formalism.PeriodIntegrals.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ClassNumberIntegrality.HalfIntegral
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ExistsDenomBackward
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Bundle001
public import Formalism.PeriodIntegrals.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitPrimeIntegers.ExistsUnitDiff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.TwChrOneMain
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.ConvProjOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Development

@[expose] public section

section

theorem convolution_projection : PI.PhConvProj.ConvProj :=
  PI.UnitaryGroupMassFormula.PhConvProj.Defs.convProj_of PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.selfAdj PI.UnitaryGroupMassFormula.PhConvProj.Sand.sand
end

section

theorem sum_log_p_over_p : PI.PrimeLogOverP := PI.PrimeLogOverPWork.sum_log_div_prime_le
end

section

theorem card_dvd_minkowskiNumber : PI.MinkowskiBound :=
  PI.Mk.minkowskiBound_of_steps PI.Mk.traceStep PI.Mk.powerSumStep
end

section

namespace PI

theorem wqUnique : PI.WeilQuotMeas.WqUnique :=
  PI.QuotMeasUniqW.wqUnique_of PI.QuotMeasUniqW.qmuWeight PI.QuotMeasUniqW.qmuLift

end PI
end

section

theorem cube_relation_of_parallelogram : PI.FglGram.CubeRelationOfParallelogram := PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.cubeRelationOfParallelogram
end

section

theorem formal_group_add_generation : PI.FglPtW.AddGen := PI.FglPtW.Wk.addGen_thm

theorem formal_group_mul_generation : PI.FglPtW.MulGen := PI.FglPtW.Wk.mulGen_thm

private theorem cc_subst_lemma {K : Type*} [CommRing K] {σ : Type*} {a : MvPowerSeries σ K}
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, ha, zero_pow hd]

private theorem subst_subst_eq_of_subst_eq_X {K : Type*} [CommRing K] {l ex : PowerSeries K}
    (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {σ : Type*} {u : MvPowerSeries σ K} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst (PowerSeries.subst u ex) l = u := by
  have hexS : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have huS : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [← PowerSeries.subst_comp_subst_apply hexS huS, hl, PowerSeries.subst_X huS]
end

section

theorem imag_quadratic_integral_basis : PI.ClassNumImQ.IntBasis :=
  PI.UnitaryGroupMassFormula.ClassNumImQInt.intBasis
end

section

theorem ordRelativeDet_finite : PI.KerIso.DetOrdFin := PI.KerDetFinW.detOrdFin
end

section

theorem power_bounded_integral : PI.PowBddInt :=
  PI.PowBddIntWork.powBddInt_of PI.PowBddIntWork.stepA PI.PowBddIntWork.stepB
end

section

theorem expIntegralWitt : PI.ExpIntW :=
  PI.ExpIntWProof.expIntW_of_key PI.ExpIntWProof.stepI PI.ExpIntWProof.keyW
end

section

theorem split_integral_local : PI.SplitIntLoc := PI.SplitIntLoc.Proof.main
end

section

theorem TwChrOne : PI.TwChrOne.TwChrOne := PI.TwChrOne.Pf.twChrOne_main
end
