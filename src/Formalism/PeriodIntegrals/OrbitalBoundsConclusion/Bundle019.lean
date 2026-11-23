module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DerivativePreservation.EabPresMain
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle016
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle018
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.Bundle003
public import Formalism.PeriodIntegrals.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSpanComplement.RenameInitMinor
public import Formalism.PeriodIntegrals.Bundle016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle005
public import Formalism.PeriodIntegrals.Bundle018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle008
public import Formalism.PeriodIntegrals.Bundle019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DensityFirstBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GeneralLinearReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStepSubstitution
public import Formalism.PeriodIntegrals.Bundle024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.FrameHolds
public import Formalism.PeriodIntegrals.Bundle026
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantDeterminantScaling.IntCastMulEqSmul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatDecomposition.SkipOneEqSuccAbove
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantLinearProduct.OfFnProdSmul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GeneralLinearCardBound.ZeroLogBound
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

theorem qnEabPres : Formalism.FourierDecayAlt.Q.EabPres := by
  intro E _ _ k r z i D a b f f₂ s hD hf hf₂
  refine ⟨Formalism.FourierDecayAlt.Q.EabLie.eab_smooth i D a b f hf, fun _ hL => ?_, fun g hg => ?_⟩
  · exact Formalism.FourierDecayAlt.Q.EabLie.eab_left i z D hD a b f hf hL
  · exact Formalism.FourierDecayAlt.Q.EabLie.eab_lin i D a b f f₂ s hf hf₂ g hg
end

section

theorem gg_matrix_bound : Formalism.L2.SG.GGMirabolic.GGMatrixBoundOfLit :=
  PI.GGMatBoundW.ggMatrixBoundOfLit_of PI.GGMatBoundW.matrix_coefficient_equation PI.GGMatBoundW.totally_hermitian_form
    (PI.GGMatBoundW.eigBound_of PI.GGMatBoundW.local_place_bound PI.GGMatBoundW.joint_eigenvector_exists
      PI.GGMatBoundW.prod_formula')
    PI.GGMatBoundW.spectrum_positive_semidefinite convolution_scalar generic_ratio_bound mirabolic_card_unipotent
end

section

theorem minor_span_complement : PI.MinorSpanCompl := PI.MSC.minorSpanCompl
end

section

theorem fock_joint_multiplicity : PI.FockDegreeTwoParts.JointMult := PI.FJM.fockJointMult_of_cauchy PI.FJM.cauchy_highest_weight
end

section

theorem level_s_all_split : PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.Top6.levelSplitting_of_heisenberg_levi PI.LevelKSplit.W.NCH.heisenberg_parabolic_all
    PI.LevelKSplit.W.NCL.levi_part_all
end

section

theorem algebraic_weight_highest_unique (L : Type) [Field L] [NumberField L] [NumberField.IsCMField L] (n : ℕ) : PI.AlgWtHwUnq.Stmt L n :=
  fun a τ lam lam' h1 h2 =>
    PI.UnitaryGroupMassFormula.HwConjInf.glue_holds_var PI.UnitaryGroupMassFormula.HwConjInf.density_induction PI.UnitaryGroupMassFormula.HwConjInf.general_linear_reduction L n a τ lam lam' h1 h2
end

section

theorem sc_pi_frame : PI.ScPiExists.Frame := PI.ScPiFrameW.frame_holds
end

section

theorem covariant_det_of_lin : PI.QnCovLin → PI.QnCovDet :=
  PI.QnCovDetW.qnCovDet_of_lin
end

section

theorem covariant_hat_of_lin : PI.QnCovLin → PI.QnCovHat :=
  PI.QnCovHatW.qnCovHat_of_lin
end

section

theorem covariant_linear : PI.QnCovLin :=
  PI.QnCovLinW.qnCovLin
end

section

theorem GZeroLogBound : PI.GZeroLogBound.Target := PI.GZeroLogBound.UnitaryGroupMassFormula.target
end
