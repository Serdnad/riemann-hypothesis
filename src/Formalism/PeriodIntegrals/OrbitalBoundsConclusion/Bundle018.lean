module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdaptedCharacterForm.SecondCapelliMinorStandardBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelImageArithmetic.GlevImageOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylConjugationFixedColumn.ReflectionScalarDualIsotropic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.IntertwinerRankLeOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MaximalCompactConjugacy.Assembly
public import Formalism.PeriodIntegrals.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupChords.FormalGroupChordFactor
public import Formalism.PeriodIntegrals.Bundle024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorFrameConstruction.InnerOfNorm
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

theorem contraction_adapted : Formalism.FourierDecayAlt.Q.ContractionsCovariant → Formalism.FourierDecayAlt.Q.ChatAdapted ∧ Formalism.FourierDecayAlt.Q.Chat2Adapted := by
  intro hcov
  exact ⟨Formalism.FourierDecayAlt.Q.Adapted.chatAdapted_of hcov, Formalism.FourierDecayAlt.Q.Adapted.chat2Adapted_of hcov⟩
end

section

theorem gl_level_image : Formalism.QuantumDeterminants.LevHom → Formalism.QuantumDeterminants.LevUH → Formalism.FourierDecayAlt.Q.GlevImage :=
  QnGlevImageW.glevImage_of
end

section

theorem weyl_level_element_properties' : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts :=
  PI.IsotropicReflections.isotropic_reflection_properties
end

section

theorem convolution_scalar : Formalism.L2.SG.GGMirabolic.ConvScalarOfLit :=
  PI.GGConvScalarW.convScalarOfLit_of PI.GGConvScalarW.representation_conjugate_gamma PI.GGConvScalarW.representation_commutes_gamma
    PI.GGConvScalarW.averaging_operator_idempotent PI.GGConvScalarW.generic_iff_criterion PI.GGConvScalarW.intertwiner_rank_le_one
    PI.GGConvScalarW.schur_lemma_complex PI.GGConvScalarW.trace_representation_gamma PI.GGConvScalarW.idempotent_trace_formula
    PI.GGConvScalarW.representation_dimension_pos
end

section

theorem adelic_maximal_compact : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeK I :=
  PI.BridgeMaxCptWork.bridgeMaxCpt_of adelic_compact_real_places adelic_compact_finite_places
end

section

theorem fglChordFactor : PI.FglChordFactor.Lemma := PI.FglChordFactor.Wk.formal_group_chord_factor
end

section

theorem sc_pi_construction : PI.ScPiExists.Build :=
  PI.ScPiBuildW.Asm.build
end
