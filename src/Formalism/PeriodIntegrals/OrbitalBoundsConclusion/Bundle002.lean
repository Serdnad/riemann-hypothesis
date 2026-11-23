module

public import Formalism.LocalToGlobal.AdelicCompactOpens.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
public import Formalism.PeriodIntegrals.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowWeightSpan.RowWtSpanOfBideterminant
public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.PeriodIntegrals.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LinearProgramLowerBound.LpFeasibleLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.VacuumEntire.AnalyticAtHfLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylProduct.WeylProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.InstFintypeColChoice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BigCellConjugation.Monomial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PhiBigCellForm.BigCellEqW0BMulTM
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PhiDerivative.StarinvDeriv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurConvolution.MapMulApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Bundle002
public import Formalism.PeriodIntegrals.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PeriodPairIndependence.IndepOfImNe
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

theorem finiteAdeleIntegers_compactOpen : Formalism.L2.Props.IntAdelesCompactOpen := PI.IntAdCpctOpenWork.main
end

section

theorem lp_lower_bound : PI.LpLower := PI.lpLower_main
end

section

theorem entireStatements_holds : PI.VacEntire.Target :=
  ⟨PI.VacEntire.UnitaryGroupMassFormula.iopEntire, PI.VacEntire.UnitaryGroupMassFormula.tensEntire⟩
end

section

theorem weyl_product_formula : PI.WeylProd := PI.WeylProdWork.weylProd
end

section

theorem rowWtSpan_of (h1 : PI.RW.BideterminantMem) (h2 : PI.RW.BideterminantSpan) : PI.RowWtSpan :=
  PI.RWS.rowWtSpan_of_bideterminant h1 h2
end

section

theorem wwInjective_of (h : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective :=
  PI.WwInjectiveWork.wwInjective_of h
end

section

theorem big_cell_g : PI.SwBig.BigCellG := PI.SwBig.BigCellGProof.bigCellG
end

section

theorem phi_form' : PI.SwBig.PhiForm := PI.SwBig.PhiFormProof.phiForm
end

section

theorem phiDeriv_of (hW : PI.SwBig.LongWeylElementSquare) : PI.SwBig.PhiDeriv :=
  fun k r => PI.SwBig.PhiDerivW.main k r hW
end

section

theorem schur_orthogonality_idempotent : PI.PhSchurConv.SchurConv := by
  open MeasureTheory in
  open scoped InnerProductSpace in
  intro G _ _ _ _ _ _ μ _ _ _ Hσ _ _ σ d w hU hF hw
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hF.1)
  have hstard : star (d : ℂ) = d := Complex.conj_ofReal d
  have hinv : (d : ℂ) * (d : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hd
  have h1 : σ 1 = 1 := hU.1
  refine ⟨?_, ?_⟩
  · unfold PI.PhSchurConv.PhConv
    refine ⟨?_, ?_, ?_⟩
    · simp only [PI.PhSchurConv.coefM]
      rw [h1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hw]
      simp
    · intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_inv hU)]
      simp only [star_mul', star_star, hstard]
      try ring
    · intro x y
      have key : ∀ g, PI.PhSchurConv.phOf σ w d g * PI.PhSchurConv.phOf σ w d (x⁻¹ * g⁻¹ * y)
          = ((d : ℂ) * d) * (⟪σ y w, σ g (σ x w)⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
        intro g
        simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
        rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_conv hU), PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner (σ g (σ x w)) (σ y w)]
        ring
      obtain ⟨hi, he⟩ := hF.2 (σ x w) (σ y w) w w
      simp_rw [key]
      refine ⟨hi.const_mul _, ?_⟩
      rw [integral_const_mul, he]
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner w (σ y w), div_eq_mul_inv]
      linear_combination (⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ * d) * hinv
  · intro u u'
    have key : ∀ g, PI.PhSchurConv.phOf σ w d g * ⟪u', σ g u⟫_ℂ
        = (d : ℂ) * (⟪u', σ g u⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
      intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      ring
    obtain ⟨hi, he⟩ := hF.2 u u' w w
    simp_rw [key]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul, he, div_eq_mul_inv]
    linear_combination (⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ) * hinv
end

section

theorem productFramesDense_holds : PI.FramesDense := PI.UD.framesDense_of PI.UD.svdStep PI.UD.gramStep

theorem unitaryGroupDense_holds : PI.UnitaryDense := unitaryDense_of productFramesDense_holds
end

section

theorem exists_periodPairOfIdeal : PI.KerLat.PerPair := PI.KerLat.PerPairProof.perPair
end
