module

public import Formalism.PeriodIntegrals.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Bundle001
public import Formalism.PeriodIntegrals.Bundle002
public import Formalism.PeriodIntegrals.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.ChebyshevPrimeBoundsLogFact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiLowerBoundHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.FirstJetIntegralGeneralHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle003
public import Formalism.PeriodIntegrals.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.ContinuousLmulM
public import Formalism.PeriodIntegrals.Bundle005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicFiniteOrder.Assembly
public import Formalism.PeriodIntegrals.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.CoeffMulCharIdem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.EntryEmbedMatrix
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Bundle004
public import Formalism.PeriodIntegrals.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.OkpInertMain
public import Formalism.PeriodIntegrals.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Bundle001
public import Formalism.PeriodIntegrals.Bundle012
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SigmaStarUniqOf
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Development

@[expose] public section

section

theorem adjointTensorOfSingle_valid : PI.TenOp :=
  PI.TOW.tenOp_of_steps PI.TOW.DegW.stepDeg
    (PI.TOW.stepPure_of PI.TOW.LiftW.stepLift PI.TOW.MonoW.stepMonoFactor) PI.TOW.stepSpan
end

section

theorem zerosWindow_of : PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow :=
  fun hL hZ hI => PI.ZW.zerosWindow_of_transfer PI.ZW.transfer hL hZ hI
end

section

theorem prime_count_bound : PI.PrimeCountBound :=
  PI.PC.primeCountBound_of 131072 (PI.PC.pcLarge_of PI.PC.psiUpperBound_holds) PI.PC.pcSmall
end

section

theorem jets_high_generation : PI.JetsPhW.HighG :=
  PI.JetsPhW.W.highG_of PI.JetsPhW.W.derivative_chain_rule PI.JetsPhW.W.derivative_self
    PI.JetsPhW.W.pderiv_subst_ne PI.JetsPhW.W.pderiv_subst_self PI.JetsPhW.W.evaluation_at_zero
    PI.JetsPhW.W.jet_derivative_integrality PI.JetsPhW.W.log_derivative_integral_jet_integrality PI.JetsPhW.W.derivative_integral

theorem jets_phase_weights : PI.JetsPhW.Target :=
  PI.JetsPhW.W.glue_holds_var PI.JetsPhW.Inv.inverse_omega_holds jets_high_generation
    PI.JetsPhW.Low.firstJetIntegralGeneral_holds PI.JetsPhW.Low.secondJetIntegralGeneral_holds

theorem jets_high : PI.JetsPhW.High :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).1

theorem jets_one : PI.JetsPhW.One :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.1

theorem jets_two : PI.JetsPhW.Two :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.2
end

section

theorem exists_gaugeNormalizedStabilizer : PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank := fun r => ⟨PI.ExistsGaugeMeasureForEachRank.W.μG r, PI.ExistsGaugeMeasureForEachRank.W.gauge r⟩
end

section

theorem finite_order_adelic : PI.FinOrdAd :=
  PI.finOrdAd_of unit_kronecker power_bounded_integral tensor_compact_dense positive_definite_form
end

section

theorem orthogonalCentral : PI.CharIdem.CharIdem :=
  PI.CharIdemW.charIdem_of PI.CharIdemW.central PI.CharIdemW.scalar
    (PI.CharIdemW.mulEq_of PI.CharIdemW.scalar)
end

section

theorem support_oneCoset : PI.OneCosetSharp.OneCosetSharp :=
  PI.OneCosetSharp.W.oneCosetSharp_of_patClosed PI.OneCosetSharp.W.patClosed PI.OneCosetSharp.W.kappaZero
    PI.OneCosetSharp.W.nElem PI.OneCosetSharp.W.gaStep PI.OneCosetSharp.W.C2.claim2
end

section

theorem ssAscent : PI.SSAscent :=
  PI.SSAscent.UnitaryGroupMassFormula.ssAscent_of
    (PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent)
    PI.SSAscent.UnitaryGroupMassFormula.traceFormNondegenerate_baseChange
    PI.SSAscent.UnitaryGroupMassFormula.semisimpleOfTraceFormNondegenerate
end

section

theorem integers_inert_prime : PI.OkpInert := PI.OkpW.okpInert_main
end

section

theorem local_endomorphism_homeomorph : PI.LocalEndHomeo :=
  PI.LocalEndW.localEndHomeo_of_three PI.LocalEndW.henselRoot PI.LocalEndW.intOfHensel PI.LocalEndW.valOfInt
end

section

theorem sigma_star_unique : PI.SigmaStarUniq := PI.SSU.sigmaStarUniq_of area_lattice_formula
end
