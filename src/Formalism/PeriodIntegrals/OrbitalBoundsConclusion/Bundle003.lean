module

public import Formalism.PeriodIntegrals.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PrimeLogarithmTail.SumLogDivSqLeDiv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SpectralGapLarge.ScGapBigMain
public import Formalism.PeriodIntegrals.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicIndex.RowMulOfMirab
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmithNormalForm.ExistsMoveRow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentValuation.VwIntEqZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.WittUnramMain
public import Formalism.PeriodIntegrals.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditiveCubes.ConstantCoeffLogEqZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramUnitMultiplication.BeMulByZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TaylorInversePower.SumMultinomialSub
public import Formalism.PeriodIntegrals.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelOrder.ValNatCastEqOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalRank.DetOneSubPNe
public import Formalism.PeriodIntegrals.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMTraceSurjective.IsTrMulConjOfMem
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

theorem prime_log_over_sq_tail : PI.PrimeLogOverPSqTail :=
  fun X hX Q hQ => PI.TailWork.sum_log_div_sq_le_div X hX Q hQ
end

section

theorem scGapBig : PI.ScGapBig.ScGapBig := PI.UnitaryGroupMassFormula.ScGapBig.scGapBig_main
end

section

theorem mirabolic_index : PI.MirabIndex.MirabIndex := PI.MirabolicIndex₂.mirabIndex
end

section

theorem smith_normal_form_theory.{u} : PI.SmithMat.{u} := by
  intro R _ _ _ n A
  obtain ⟨d, ⟨U, V, hU, hV, h⟩, hd⟩ := PI.SmithWork.smith n A
  exact ⟨U, V, d, hU, hV, h, hd⟩

theorem smith_diagonal_entries.{u} : PI.SmithDiag.{u} := by
  intro R _ _ _ n A
  obtain ⟨U, V, d, hU, hV, h, -⟩ := smith_normal_form_theory R n A
  exact ⟨U, V, d, hU, hV, h⟩
end

section

theorem unipVal : PI.UnipVal.UnipVal := fun _ _ _ w =>
  ⟨fun n hn => PI.UnitaryGroupMassFormula.UnipVal.Main.part1 w n hn,
    fun g₁ g₂ a h1 h2 h12 => PI.UnitaryGroupMassFormula.UnipVal.Main.part2 w g₁ g₂ a h1 h2 h12⟩
end

section

theorem witt_unramified : PI.WittUnram :=
  PI.WittUnramWork.wittUnram_main
end

section

theorem biadditiveOfCube_holds : PI.BiaddOfCube.Target := by
  intro p _ l ex ph hex h hC
  have hxz : PI.BiaddOfCube.add l ex (PI.BiaddOfCube.Xv (p := p) 0 : MvPowerSeries (Fin 3) ℂ_[p])
      (PI.BiaddOfCube.Xv 2) = PI.BiaddOfCube.add l ex (PI.BiaddOfCube.Xv 2) (PI.BiaddOfCube.Xv 0) :=
    PI.BiaddOfCubeWork.add_comm' l ex _ _
  have has := PI.BiaddOfCubeWork.add_assoc' hex h
    (PI.BiaddOfCube.Xv (p := p) 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.BiaddOfCube.Xv 1) (PI.BiaddOfCube.Xv 2)
    (PI.BiaddOfCubeWork.cc_Xv 0) (PI.BiaddOfCubeWork.cc_Xv 1) (PI.BiaddOfCubeWork.cc_Xv 2)
  constructor
  · refine PI.BiaddOfCubeWork.simeq_of_sub_eq ?_ hC
    simp only [PI.BiaddOfCube.be, hxz]
    ring
  · refine PI.BiaddOfCubeWork.simeq_of_sub_eq ?_ hC
    simp only [PI.BiaddOfCube.be, hxz, ← has]
    ring
end

section

theorem gramExpansion_orthonormal : PI.FglGram.GramUnit := PI.UnitaryGroupMassFormula.GramUnit.gramUnit
end

section

theorem coeffInversePowerFacts.{u, v} : PI.TayInvPow.{u, v} := PI.UnitaryGroupMassFormula.TayInvPow.main
end

section

theorem ordRelativeDet_independence : PI.KerIso.DetOrdIndep :=
  PI.KerIso.DetOrdW.detOrdIndep
end

section

theorem diagonal_rank_bound : PI.DiagRank := PI.UnitaryGroupMassFormula.DiagRank.diagRank
end

section

theorem traceSurjective_holds : PI.CMTraceOnto := by
  intro K _ _ _ hK a ha

  have hfix : PI.CMT.conj a = a := by
    apply NumberField.RingOfIntegers.ext
    rw [PI.CMT.coe_conj, ha]
  obtain ⟨x, hx⟩ := PI.CMT.isTr_mul_fixed hfix (PI.CMT.isTr_one hK.2.2)
  refine ⟨x, PI.CMT.conj x, PI.CMT.coe_conj x, ?_⟩
  rw [hx, mul_one]
end
