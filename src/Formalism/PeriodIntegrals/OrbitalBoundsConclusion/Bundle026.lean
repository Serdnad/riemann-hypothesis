module

public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Bundle001
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle021
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle012
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle015
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle019
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Bundle003
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSmoothness.SecondCapelliMinorContinuousLinear
public import Formalism.PeriodIntegrals.Bundle029
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.OrbitsAddAtConjugate
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitSumCount.SizeGe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.PeriodIntegrals.Bundle026

@[expose] public section

section

theorem stabPairs : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  PI.StabPairsW.stabPairs_of_converse (PI.StabPairs.Conv.converseStep_of PI.StabPairsW.gram_matrix_invariance)
end

section

theorem qnHermHaar : Formalism.FourierDecayAlt.Q.HermHaar :=
  PI.QnHermHaar.qnHermHaar_of_alg PI.QnHermHaar.hermitian_algebra_generation qnRdSkew quantum_minor_star
    (PI.contractionsCovariant_iff.2
      ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩)
    quantum_minor_move.1 quantum_minor_move.2 qnYLeibniz qnEabGl qnEabPres
end

section

theorem qnTPres : Formalism.FourierDecayAlt.Q.TPreservesFF := Formalism.FourierDecayAlt.Q.TPresMain.qnTPres_of qnTInv
end

section

theorem PI.OrbAddOne : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddAtConjugate E :=
  PI.OrbJet.AO.orbitsAddAtConjugate
end

section

theorem PI.SumOrbC : ∀ (D : Formalism.BasicNotions.D7) (L : Formalism.BasicNotions.SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (K : Formalism.MainNotions.G.Consts) (ce : Formalism.BasicNotions.ErrC) (E : Formalism.MainNotions.OrbitPlaces.Ent D) (C6 C : ℝ), Formalism.MainNotions.OrbitPlaces.Shape D L X E → Formalism.MainNotions.OrbitPlaces.CLarge C6 C K ce → Formalism.MainNotions.OrbitPlaces.ValuationSumBound E L ce C :=
  fun D L X K ce E C6 C hS hC => SumOrbCW.sumOrbC D L X K ce E C6 C hS hC
end
