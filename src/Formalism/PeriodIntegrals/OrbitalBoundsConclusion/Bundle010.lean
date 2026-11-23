module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoincareSeriesMeasurability.FoldL2DoubleCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.AnisoPeel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.HermitianDiagonalization
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.IsoPeel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.Bundle002
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.PvLocalSelf
public import Formalism.PeriodIntegrals.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.Bundle002
public import Formalism.PeriodIntegrals.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.LocBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.SelfDualLocOfLocBasis
public import Formalism.PeriodIntegrals.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiTorsionFree.Lattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle002
public import Formalism.PeriodIntegrals.Bundle013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.LocDualGenOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.UnramifiedDualGenerator
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittLogarithm.FormalLogarithmHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittLogarithm.WfLogOf
public import Formalism.PeriodIntegrals.Bundle014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.CoreFgOfLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.Bundle001
public import Formalism.PeriodIntegrals.Bundle015
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalProductFormula.LocProdFormulaOf
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

theorem fold_l2_bound_b (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesMemLp G μ :=
  PI.PoincareSeriesMemLp.UnitaryGroupMassFormula.fold_L2_double_coset G μ
end

section

theorem density_exact_inert : Formalism.L2.SG.DensExact.DensExactInert :=
  DensInertW.densExactInert_of DensInertW.hermitianDiagonalization DensInertW.repCountCongruenceInvariant
    DensInertW.anisotropic_valuation_peel DensInertW.isotropic_valuation_peel DensInertW.quadraticDifferenceArith
end

section

theorem hecke_product_rule : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), χ.ProductRule :=
  fun _ _ _ χ => PI.HeckeProdW.productRule χ
end

section

theorem unit_det_root_of_unity : PI.UnitDetRoot :=
  PI.UnitaryGroupMassFormula.UnitDetRoot.unitDetRoot_of_global PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit
end

section

theorem self_dual_local : PI.SelfDualLoc :=
  PI.SelfDualLoc.W.selfDualLoc_of_locBasis PI.SelfDualLoc.W.locBasis
end

section

theorem ideal_lattice_basis : PI.IdealLattice :=
  PI.IdealLatticeWork.idealLattice_of PI.IdealLatticeWork.okArea PI.IdealLatticeWork.idealBasis
end

section

theorem minkowski_bound_rat : PI.MinkowskiBoundQ := PI.MkQ.minkowskiBoundQ
end

section

theorem unitary_approximation_finite : PI.UnitaryApproxFin.UnitaryApproxFin :=
  PI.UnitaryApproxFinWork.unitaryApproxFin_of PI.UnitaryApproxFinWork.topStep
    PI.UnitaryApproxFinWork.cayleyStep PI.UnitaryApproxFinWork.approxEStep
    PI.UnitaryApproxFinWork.weak_approximation_finite_unitary PI.UnitaryApproxFinWork.bounded_rational_unitary
    PI.UnitaryApproxFinWork.unitary_scalars PI.UnitaryApproxFinWork.eigenvalue_avoidance
end

section

theorem local_dual_generation : PI.LocDualGen.Stmt :=
  PI.LocDualGen.Of.locDualGen_of PI.LocDualGen.FpU.unramified_dual_generator
end

section

private lemma inv_series_sub : PI.InvSerSub := by
  intro K _ S l ex hl hl0 hl1 hex0 hsub n
  obtain ⟨c, hc⟩ := PowerSeries.X_dvd_iff.2 hex0
  have hpow : ∀ d m, PowerSeries.coeff m (ex ^ d) =
      if d ≤ m then PowerSeries.coeff (m - d) (c ^ d) else 0 := by
    intro d m
    rw [hc, mul_pow, PowerSeries.coeff_X_pow_mul']
  have hcoef : ∀ j, PowerSeries.coeff j c = PowerSeries.coeff (j + 1) ex := by
    intro j
    rw [hc, PowerSeries.coeff_succ_X_mul]
  have hHS : PowerSeries.HasSubst ex := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hex0]; exact IsNilpotent.zero)
  have key : ∀ m, PowerSeries.coeff m (PowerSeries.X : PowerSeries K) =
      ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l * PowerSeries.coeff m (ex ^ d) := by
    intro m
    have hfin : (∑ᶠ d, PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d)) =
        ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d) := by
      apply finsum_eq_sum_of_support_subset
      intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [hpow, if_neg (by omega), smul_zero]
    rw [← hsub, PowerSeries.coeff_subst' hHS, hfin]
    simp only [smul_eq_mul]

  have hB : ∀ N, (∀ j ≤ N, PowerSeries.coeff j c ∈ S) →
      ∀ d, ∀ i ≤ N, PowerSeries.coeff i (c ^ d) ∈ S := by
    intro N hN d
    induction d with
    | zero =>
      intro i _
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    | succ d ihd =>
      intro i hi
      rw [pow_succ, PowerSeries.coeff_mul]
      apply Subring.sum_mem
      intro p hp
      have h : p.1 + p.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      exact S.mul_mem (ihd _ (by omega)) (hN _ (by omega))
  have hl0' : PowerSeries.coeff 0 l = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hl0]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hex0]
      exact S.zero_mem
    · have k := key (n + 1)
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at k
      simp only [zero_add, pow_one, hl1, one_mul, hl0', zero_mul, add_zero] at k
      have he : PowerSeries.coeff (n + 1) ex = PowerSeries.coeff (n + 1) (PowerSeries.X : PowerSeries K) -
          ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1 + 1) l *
            PowerSeries.coeff (n + 1) (ex ^ (i + 1 + 1)) := by
        rw [k]
        ring
      rw [he]
      apply S.sub_mem
      · rw [PowerSeries.coeff_X]
        split_ifs
        · exact S.one_mem
        · exact S.zero_mem
      · apply Subring.sum_mem
        intro i hi
        rw [Finset.mem_range] at hi
        apply S.mul_mem (hl _)
        rw [hpow]
        split_ifs with hle
        · apply hB (n - 1) _ (i + 1 + 1) _ (by omega)
          intro j hj
          rw [hcoef]
          exact ih _ (by omega)
        · exact S.zero_mem

theorem witt_logarithm : PI.WfLog :=
  PI.WfLogWork.wfLog_of inv_series_sub PI.WfLogWork.formal_logarithm_holds
end

section

theorem eq_iff_locallyEq : PI.LocLatEq.Stmt :=
  PI.LocLatEq.W.locLatEq_of PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP
    (PI.LocLatEq.W.coreP_of_unitP_avoidP_intP PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP PI.LocLatEq.W.intP)
end

section

theorem local_product_formula : PI.LocProdFormula :=
  PI.LocProdFormulaW.locProdFormula_of product_formula_e
end
