module

public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.ColsConjTranspose
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.QBuild
public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.OfFnProdIntertwine
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.Bundle002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.SubsetUpperHessenberg
public import Formalism.PeriodIntegrals.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.Bridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.UnimodLocalOfLocDual
public import Formalism.PeriodIntegrals.Bundle023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.TargetOfInstDecomp
public import Formalism.PeriodIntegrals.Bundle027
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.FlagMatLower
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.NegOnePowMulSelf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.Bundle001
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

theorem frameInd : Formalism.FourierDecayAlt.C2.GramIndependentSignature :=
  PI.FrameInd.frame_induction_of PI.FrameInd.signStep (PI.FrameInd.UPosW.uPos_of PI.FrameInd.negative_bound)
end

section

theorem operators_commute_translations : Formalism.FourierDecayAlt.C3.OperatorsCommuteTranslations :=
  AAInvW.operators_commute_translations_of_left_right AAInvW.left_aa
    (AAInvW.rightAA_of AAInvW.operator_model AAInvW.algebra_aa AAInvW.algebra_aa_vector AAInvW.hpk_involution
      AAInvW.subset_upper_hessenberg AAInvW.subset_inverse_column AAInvW.subset_row_star)
    AAInvW.subset_upper_hessenberg
end

section

theorem unimodular_genus_unique : PI.UnimodGenus :=
  PI.UG.W.unimodGenus_of PI.UG.W.unimodLocal PI.UG.W.isomLocStd
end

section

namespace PI

theorem sc_mu_exists : PI.ScMuExists.Target :=
  PI.ScMuExists.UnitaryGroupMassFormula.target_of_instDecomp PI.ScMuExists.UnitaryGroupMassFormula.place_decomposition_instance

end PI
end

section

open Matrix

noncomputable section

namespace PI.AmpRelAtPt

open Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem ell_eq {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z g = ∑ a : Fin r, flagMat k r z g a.castSucc a.succ := by
  unfold ell
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold flagMat fvec
  rw [dite_eq_left (show (Fin.castSucc a).val < r by simp)]
  by_cases h : a.val + 1 < r
  · rw [dite_eq_left h, dite_eq_left (show (Fin.succ a).val < r by simpa using h), bvec, Matrix.mulVec_single_one,
      Matrix.col_apply]
    rfl
  · rw [dite_eq_right h, dite_eq_right (show ¬ (Fin.succ a).val < r by simpa using h)]
    rfl

end PI.AmpRelAtPt

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon PI.AmpRelAtPt in
theorem amplifier_relation_at_point : PI.AmpRoot.RelAtPt := by
  intro k r L p g₀ hc hP hG a ha
  have key := sum_super (ptσ_invol p) (zhat_pt hP.2) (ptζ_ne p) (pt_adj p)
    (flagMat_upper ha.1) (flagMat_diag ha.1) (flagMat_upper ha.2) (flagMat_diag ha.2)
    (flag_rel L.hz.1 L.hz'.1 hP.1 ha)
  have hre : ∀ X : ℂ, (L.c * star X).re = (L.c * X).re := by
    intro X
    calc (L.c * star X).re = (star L.c * star X).re := by rw [hc]
      _ = (star (L.c * X)).re := by rw [star_mul']
      _ = (L.c * X).re := by rw [Complex.star_def, Complex.conj_re]
  unfold psi
  rw [ell_eq L.z a, ell_eq L.z' (g₀⁻¹ * a * g₀), key, hre]
end
end
