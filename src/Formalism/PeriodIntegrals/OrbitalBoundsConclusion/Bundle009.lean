module

public import Formalism.PeriodIntegrals.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.ChartZeroEqOneOfLongWeylSq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.Bundle001
public import Formalism.PeriodIntegrals.Bundle015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle007
public import Formalism.PeriodIntegrals.Bundle016
public import Formalism.PeriodIntegrals.Bundle013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittSubstitution.CoeffMapMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.MinusPartOfMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockWeightDegree.ExistsMonomialWeight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.Bundle002
public import Formalism.PeriodIntegrals.Bundle017
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EntrywiseSandwichCommute.BlockEmbeddingMulEntrySwap
public import Formalism.YangianSpanCharacter.YangianRTTProofs.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuarticIndependence.QmIndep
public import Formalism.PeriodIntegrals.TwNormLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.TwNormLatMain
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.CoordBaseChange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.FinrankIInfKerEquiv
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

theorem sandwich_of_chart : PI.SwSand.SandwichOf :=
  PI.SwSandwichOfWork.sandwichOf_of_charts PI.SwSandwichOfWork.normRL PI.SwSandwichOfWork.logG
    PI.SwSandwichOfWork.chartFwd PI.SwSandwichOfWork.chartBwd PI.SwSandwichOfWork.sideB
    PI.SwSandwichOfWork.sideA
end

section

theorem witt_substitution : PI.WfSubst := PI.WfSubstProof.wfSubst
end

section

theorem product_formula_e : PI.ProdFormulaE.ProdFormulaE :=
  PI.ProdFormulaE.Assemble.prodFormulaE_of_haar PI.ProdFormulaE.HaarAlgP.haarScaling
end

section

theorem low_smooth_of_k_finite : PI.KFinSmooth → PI.LowSmooth := PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth
end

section

theorem fold_dc_unfold : PI.FoldDCUnfold.FoldDCUnfold :=
  PI.FoldDCUnfold.W.foldDCUnfold_of PI.FoldDCUnfold.W.translation_exists
    PI.FoldDCUnfold.W.translation_independent PI.FoldDCUnfold.W.translation_product
    PI.FoldDCUnfold.W.double_coset_translation lintegralTransversalSum
end

section

theorem harmonicSplitting_holds : PI.FockDegreeTwoParts.HarmSplit := PI.FHS.harmSplit
end

section

theorem highestWeightDegree_le : PI.FockDegreeTwoParts.WtDeg := PI.FockWtDegWork.wtDeg
end

section

theorem local_cartan_pair : PI.SqPair.LocCartanPair :=
  PI.SqPair.LCP.locCartanPair_of PI.SqPair.LCP.pair_dichotomy PI.SqPair.LCP.base_lagrangian
    (PI.SqPair.LCP.step_of PI.SqPair.LCP.pair_selection PI.SqPair.LCP.hyperbolic_plane
      PI.SqPair.LCP.pair_split')
end

section

private theorem rtt_commutator_sandwich_eq_of_relations {M : Type} [Ring M] (R e2b e1b' e1q' e2q e1a' e2a : M)
    (h1 : e2q * e1a' = e1a' * e2q) (h2 : e2b * e1q' = e1q' * e2b) (h3 : e2b * e1a' = e1a' * e2b)
    (h4 : e2a * e1b' = e1b' * e2a) (h5 : e2q * e1b' = e1b' * e2q) (h6 : e2a * e1q' = e1q' * e2a)
    (hP : R * e1b' * e2b = e2b * e1b' * R) (hU : R * e1a' * e2a = e2a * e1a' * R) :
    e2b * e1b' * (R * e1q' * e2q - e2q * e1q' * R) * (e1a' * e2a) =
      R * (e1b' * e1q' * e1a' * (e2b * e2q * e2a)) - e2b * e2q * e2a * (e1b' * e1q' * e1a') * R := by
  rw [mul_sub, sub_mul]
  congr 1
  · calc e2b * e1b' * (R * e1q' * e2q) * (e1a' * e2a)
        = e2b * e1b' * R * e1q' * (e2q * e1a') * e2a := by simp only [mul_assoc]
      _ = R * e1b' * e2b * e1q' * (e1a' * e2q) * e2a := by rw [← hP, h1]
      _ = R * e1b' * (e2b * e1q') * e1a' * e2q * e2a := by simp only [mul_assoc]
      _ = R * e1b' * e1q' * (e2b * e1a') * e2q * e2a := by rw [h2]; simp only [mul_assoc]
      _ = R * (e1b' * e1q' * e1a' * (e2b * e2q * e2a)) := by rw [h3]; simp only [mul_assoc]
  · calc e2b * e1b' * (e2q * e1q' * R) * (e1a' * e2a)
        = e2b * e1b' * e2q * e1q' * (R * e1a' * e2a) := by simp only [mul_assoc]
      _ = e2b * e1b' * e2q * e1q' * (e2a * e1a' * R) := by rw [hU]
      _ = e2b * (e1b' * e2q) * (e1q' * e2a) * e1a' * R := by simp only [mul_assoc]
      _ = e2b * (e2q * e1b') * (e2a * e1q') * e1a' * R := by rw [← h5, ← h6]
      _ = e2b * e2q * (e1b' * e2a) * e1q' * e1a' * R := by simp only [mul_assoc]
      _ = e2b * e2q * e2a * (e1b' * e1q' * e1a') * R := by rw [← h4]; simp only [mul_assoc]

theorem rtt_sandwich' : PI.RTTSandwich := by
  intro A _ _ QQ p c ci p' c' ci' hW hW' hcomm hQ Y Y'
  dsimp only
  have hbu : ∀ (y : ℂ) (i j : Fin 2), ∀ u ∈ ({p, c, ci} : Set A), Commute (Formalism.YangianSpanCharacter.T.Tm y p' c' ci' i j) u := by
    intro y i j u hu
    exact PI.QmSandwichWork.tm_entry_comm y (hcomm u hu p' (by simp)).symm (hcomm u hu c' (by simp)).symm
      (hcomm u hu ci' (by simp)).symm i j
  have hab : ∀ (y y' : ℂ) (i j k l : Fin 2),
      Commute (Formalism.YangianSpanCharacter.T.Tm y p c ci i j) (Formalism.YangianSpanCharacter.T.Tm y' p' c' ci' k l) := by
    intro y y' i j k l
    exact PI.QmSandwichWork.tm_entry_comm y (hbu y' k l p (by simp)).symm (hbu y' k l c (by simp)).symm
      (hbu y' k l ci (by simp)).symm i j
  have haq : ∀ (y y' : ℂ) (i j k l : Fin 2), Commute (Formalism.YangianSpanCharacter.T.Tm y p c ci i j) (QQ y' k l) :=
    fun y y' i j k l => PI.QmSandwichWork.tm_entry_comm y (hQ p (by simp) y' k l) (hQ c (by simp) y' k l)
      (hQ ci (by simp) y' k l) i j
  have hbq : ∀ (y y' : ℂ) (i j k l : Fin 2), Commute (Formalism.YangianSpanCharacter.T.Tm y p' c' ci' i j) (QQ y' k l) :=
    fun y y' i j k l => PI.QmSandwichWork.tm_entry_comm y (hQ p' (by simp) y' k l) (hQ c' (by simp) y' k l)
      (hQ ci' (by simp) y' k l) i j
  have h1 : Formalism.YangianSpanCharacter.T.E2 (QQ Y) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (QQ Y) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => haq Y' Y i j k l).symm
  have h2 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (QQ Y') =
      Formalism.YangianSpanCharacter.T.E1 (QQ Y') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (hbq Y Y' k l i j).symm).symm
  have h3 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => hab Y' Y i j k l).symm
  have h4 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (hab Y Y' k l i j).symm).symm
  have h5 : Formalism.YangianSpanCharacter.T.E2 (QQ Y) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (QQ Y) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => hbq Y' Y i j k l).symm
  have h6 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (QQ Y') =
      Formalism.YangianSpanCharacter.T.E1 (QQ Y') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (haq Y Y' k l i j).symm).symm
  have hP : ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) *
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') =
      Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) :=
    Formalism.YangianSpanCharacter.P.rttRelation ℂ A p' c' ci' Y Y' hW'
  have hU : ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) *
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) =
      Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) :=
    Formalism.YangianSpanCharacter.P.rttRelation ℂ A p c ci Y Y' hW
  have hmat := rtt_commutator_sandwich_eq_of_relations _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 hP hU
  change _ = (Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') *
    (_ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) *
    (Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci))) (0, 0) (0, 0)
  rw [hmat, Matrix.sub_apply, PI.QmSandwichWork.flip_row, PI.QmSandwichWork.flip_col, ← Formalism.FourierDecayAlt.P.W.first_embedding_mul,
    ← Formalism.FourierDecayAlt.P.W.first_embedding_mul, ← Formalism.FourierDecayAlt.P.W.entries_mem_mul, ← Formalism.FourierDecayAlt.P.W.entries_mem_mul, PI.QmSandwichWork.block_embedding_mul_entry,
    PI.QmSandwichWork.block_embedding_mul_entry_swap, mul_sub]
end

section

theorem rtt_independence' : PI.RTTIndependence := PI.QmIndepW.qmIndep
end

section

theorem TwNormLat : PI.TwNormLat.TwNormLat := PI.TwNormLat.W.twNormLat_main
end

section

theorem coefficient_crystal_generation : Formalism.MainNotions.N.GlobalTheory.CoefCrysGen :=
  PI.CoefExt.coefCrysGen_of PI.CoefExt.invBaseChange
end
