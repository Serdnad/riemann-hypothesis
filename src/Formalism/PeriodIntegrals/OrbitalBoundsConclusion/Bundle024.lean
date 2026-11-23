module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle021
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle019
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle011
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle023
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusInvariance.QnTInvOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelevantCarrierNonempty.InSCarrierNonempty
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion
public import Formalism.PeriodIntegrals.Bundle027
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupHaar.RootHaarMain
public import Formalism.PeriodIntegrals.Bundle028
public import Development.AutomorphicArithmetic.OrbitLabellings.Bundle004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.SizeDel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bridge
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.EntAtDOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.LapForms
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.SDegMul
public import Formalism.PeriodIntegrals.Bundle029
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.OrbitRestriction
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
public import Formalism.PeriodIntegrals.Bundle026

@[expose] public section

section

theorem qnTInv : Formalism.FourierDecayAlt.Q.TInvariant :=
  Formalism.FourierDecayAlt.Q.TInvW.qnTInv_of
    (PI.contractionsCovariant_iff.2
      ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩)
    qnEabPres qnEabGl qnMinorLeft
end

section

theorem split_pair_generation : Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen := square_pair_glue square_pair_local
end

section

theorem in_s_relevant (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermInSRel D u u' :=
  PI.UnitaryGroupMassFormula.InSRelevantW.termInSRel_main D u u'
end

section

theorem infinite_measure_transfer : Formalism.L2.SG.Pf.MeasInf.InfTransfer :=
  Formalism.L2.SG.Pf.MeasInfW.measInfXfer_of Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity
    Formalism.L2.SG.Pf.MeasInfW.nilpotent_measure_recursion Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion
    Formalism.L2.SG.Pf.MeasInfW.nilpotent_measure_closed_form Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_closed_form
end

section

theorem amplifier_root_haar : PI.AmpRootH.RootHaar := PI.AmpRootHaarW.rootHaar_main
end

section

theorem sz_eat_identity : PI.SzEatI.SzEatI := UpperTheory.G2.szEatI_of_stepA PI.SzEatI.W.stepA
end

section

theorem jet_bound_ramified_prime : PI.EntAtD.EntAtD :=
  PI.EntAtD.W.entAtD_of PI.EntAtD.W.pExpCoeff PI.EntAtD.W.pBridge PI.EntAtD.W.pLapComm
    PI.EntAtD.W.pMinorAff PI.EntAtD.W.pSDegMul PI.EntAtD.W.pLapForms
end

section

theorem PI.OrbRestr : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestriction E :=
  PI.OrbJet.OrbW.orbitRestriction
end
