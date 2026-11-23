module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.LeftMultiplicationRule
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.LzOutRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.SecondCapelliMinorLevel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RightSingleRule.EllSingleZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting
public import Formalism.PeriodIntegrals.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.AdelicBounds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.LatticeClassesFiniteRefinement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.PosDefOfDefiniteSignatureHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle003
public import Formalism.PeriodIntegrals.Bundle019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.GramMatrixDuality
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaGram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaOperatorBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.StdSlopeLowOf
public import Formalism.PeriodIntegrals.Bundle023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.IndexEqOfTraceInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPowD
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.TargetOfWframe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WFrameOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WeilBasisExistence
public import Formalism.PeriodIntegrals.Bundle027
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.MeasurableStabActOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.ContinuousAtInvOfDet
public import Formalism.PeriodIntegrals.Bundle028
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.FirstCoordinateLeThreeScale
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Bundle001
public import Formalism.PeriodIntegrals.Bundle029
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitRestrictionDegreeOne.RestrictedSingleJetEquation
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitRestrictionDegreeOne.Lemmas

@[expose] public section

section

theorem qnRuleLeft : Formalism.FourierDecayAlt.Q.RuleLeft := Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.left_multiplication_rule
end

section

theorem level_transfer_of_levHom : Formalism.QuantumDeterminants.LevHom → Formalism.FourierDecayAlt.Q.LevelTransfer := by
  open PIQnLT Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q in
  intro hL E _ _ k i r' z z' Y p q f g hg
  have hinv : (ιLev k i r' g)⁻¹ = ιLev k i r' g⁻¹ := ιLev_inv hL g (isUnit_det_of_UH g hg)
  have hm := mdim_lev k i r'
  have hP : ∀ j, posL k (i + r') ⟨i, by omega⟩ j = levPos k i r' (posL k r' 0 (Fin.cast hm j)) :=
    posL_lev k i r'
  have hx : ∀ j, xv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j = xv k r' z' 0 (Fin.cast hm j) := by
    intro j
    simp only [xv]
    rw [fvec_lift, hP, liftVec_lev]
  have hxb : ∀ j, xbv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j =
      xbv k r' z' 0 (Fin.cast hm j) := by
    intro j
    simp only [xbv]
    rw [fvec_lift, hP, bvec_lev, herm_liftVec]
  have hy : ∀ j, yv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j =
      yv k r' z 0 g (Fin.cast hm j) := by
    intro j
    simp only [yv]
    rw [hinv, fvec_lift, mulVec_liftVec, hP, liftVec_lev]
  have hyb : ∀ j, ybv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j =
      ybv k r' z 0 g (Fin.cast hm j) := by
    intro j
    simp only [ybv]
    rw [fvec_lift, hP, bvec_lev, mulVec_liftVec, herm_liftVec]
  have hu := uC_lev k i r' Y
  fin_cases p <;> fin_cases q
  · simp only [tL, capL]
    rw [hu]
    exact capL_cast hL hm _ _ hP _ f g
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hx j) (fun j => hyb j)
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hy j) (fun j => hxb j)
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact second_capelli_minor_cast hL hm _ _ hP _ _ _ _ _ _ _ _ _ f g (fun j => hy j) (fun j => hx j)
      (fun j => hyb j) (fun j => hxb j)
end

section

theorem qnRuleRight : Formalism.FourierDecayAlt.Q.RuleRight := Formalism.FourierDecayAlt.Q.QRR.ruleRight_main
end

section

theorem weil_measure_compat : Formalism.L2.SG.Pf.MeasCore.MWCore :=
  PI.UnitaryGroupMassFormula.MeasWCore.measWCore_main
end

section

theorem unitary_class_set_finite : PI.UJClassFin.UJClassFin :=
  PI.UnitaryGroupMassFormula.UJClassFin.uJClassFin_of_latFin PI.UnitaryGroupMassFormula.UJClassFin.posDefOfDefiniteSignature_holds
    PI.UnitaryGroupMassFormula.UJClassFin.adelic_bounds PI.UnitaryGroupMassFormula.UJClassFin.lattice_classes_finite_refinement
end

section

theorem standard_slope_lower : PI.StdSlopeLow :=
  PI.SlopeSteps.stdSlopeLow_of PI.SlopeSteps.nabla_gram_lower_bound PI.SlopeSteps.gram_matrix_duality
    PI.SlopeSteps.nabla_operator_basis
end

section

noncomputable section

namespace PI

theorem adelic_index_eq : PI.AdIndexEq.IndexEq :=
  PI.UnitaryGroupMassFormula.AdIndexEq.indexEq_of_traceInt PI.UnitaryGroupMassFormula.AdIndexEq.trace_integral'

end PI

end
end

section

theorem sc_reference_exists : PI.ScRefExists.Target :=
  PI.ScRefExists.Top.target_of_wframe
    (PI.ScRefExists.WF.wFrame_of PI.ScRefExists.ApP.principal_ideal_ring_at_prime PI.ScRefExists.WB.weil_basis_existence)
end

section

open Matrix MeasureTheory Measure
open scoped ENNReal

noncomputable section

namespace PI.AmpOrbQuot

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon

theorem muN_smul {k r : ℕ} (L : LocBessel k r) : L.μN = L.κN • _root_.Formalism.MainNotions.S.haarLie (Nset k r) 1 := by
  rw [LocBessel.μN]
  unfold _root_.Formalism.MainNotions.S.haarLie
  rw [one_smul]

theorem exists_isOrbQuot_of_isHaarOn {k r : ℕ} (L : LocBessel k r) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μR : Measure (Mt k r)) (hg : g ∈ UH (Hpk k r)) (hμ : IsHaarOn (RStab k r g) μR)
    [SFinite L.μN] (hN : ∀ s ∈ Nset k r, L.μN.map (lmulM s) = L.μN) (hc : L.μN (NS k r)ᶜ = 0) :
    ∃ ν : Measure (PairSp k r), IsOrbQuot L g μR ν := by
  have : SigmaFinite μR := hμ.1
  have : IsFiniteMeasure L.μW := ⟨by rw [L.hμW.2]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  have : SFinite (pairMeas L) := by unfold pairMeas; infer_instance
  obtain ⟨θ, hθ, hθ1⟩ := cutoff_exists hg hμ
  refine ⟨(pairMeas L).withDensity θ, fun f hf => ?_⟩
  have hJ : Measurable (fun p : Mt k r × PairSp k r => f (stabAct g (Matrix.of p.1) p.2)) :=
    hf.comp (measurable_stabAct g)
  have hin : Measurable (fun x : PairSp k r => ∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR) :=
    hJ.lintegral_prod_left'
  rw [lintegral_withDensity_eq_lintegral_mul _ hθ hin]
  have step1 : ∀ x : PairSp k r, (θ * fun x => ∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR) x =
      ∫⁻ a, θ x * f (stabAct g (Matrix.of a) x) ∂μR := by
    intro x
    simp only [Pi.mul_apply]
    have hmx : Measurable fun a : Mt k r => f (stabAct g (Matrix.of a) x) :=
      hJ.comp (f := fun a : Mt k r => (a, x)) (measurable_id.prodMk measurable_const)
    rw [lintegral_const_mul _ hmx]
  simp_rw [step1]
  have hm1 : Measurable (Function.uncurry fun (x : PairSp k r) (a : Mt k r) => θ x * f (stabAct g (Matrix.of a) x)) :=
    (hθ.comp measurable_fst).mul (hJ.comp (f := Prod.swap) measurable_swap)
  rw [lintegral_lintegral_swap hm1.aemeasurable]
  have step2 : ∀ a : Mt k r, Matrix.of a ∈ RStab k r g →
      ∫⁻ x, θ x * f (stabAct g (Matrix.of a) x) ∂(pairMeas L) =
        ∫⁻ y, θ (stabAct g (Matrix.of a)⁻¹ y) * f y ∂(pairMeas L) := by
    intro a ha
    have hh : Measurable fun y : PairSp k r => θ (stabAct g (Matrix.of a)⁻¹ y) * f y :=
      (hθ.comp (measurable_stabAct_one g _)).mul hf
    conv_rhs => rw [← pairMeas_inv L hN ha]
    rw [lintegral_map hh (measurable_stabAct_one g _)]
    refine lintegral_congr fun x => ?_
    rw [stabAct_inv_cancel hg ha.1.1]
  have hR : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r g := ae_iff.2 hμ.2.2.1
  rw [lintegral_congr_ae (hR.mono step2)]
  have hm2 : Measurable (Function.uncurry fun (a : Mt k r) (y : PairSp k r) => θ (stabAct g (Matrix.of a)⁻¹ y) * f y) :=
    (hθ.comp (measurable_stabAct_inv g)).mul (hf.comp measurable_snd)
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  have hNae : ∀ᵐ y ∂(pairMeas L), y.1.2 ∈ NS k r := ae_iff.2 (by
    have := pairMeas_null L hc
    simpa using this)
  refine lintegral_congr_ae (hNae.mono fun y hy => ?_)
  have hmy : Measurable fun a : Mt k r => θ (stabAct g (Matrix.of a)⁻¹ y) :=
    hθ.comp ((measurable_stabAct_inv g).comp (f := fun a : Mt k r => (a, y)) (measurable_id.prodMk measurable_const))
  show f y = ∫⁻ a, θ (stabAct g (Matrix.of a)⁻¹ y) * f y ∂μR
  rw [lintegral_mul_const _ hmy, hθ1 y hy, one_mul]

end PI.AmpOrbQuot

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon PI.AmpOrbQuot in
theorem orbQuotEx_of_haarLieN (h : PI.AmpOrbQ.HaarLieN) : PI.AmpOrbQ.OrbQuotEx := by
  intro k r L p g₀ μR hpt _ hμ
  obtain ⟨hsf, _, hnull, hinv⟩ := h k r 1 one_ne_zero ENNReal.one_ne_top
  have e := muN_smul L
  haveI := hsf
  haveI : SFinite L.μN := by rw [e]; infer_instance
  refine exists_isOrbQuot_of_isHaarOn L g₀ μR hpt.1 hμ ?_ ?_
  · intro s hs
    rw [e, Measure.map_smul, hinv s hs]
    exact (show Continuous (lmulM (k := k) (r := r) s) from by
      unfold lmulM
      exact continuous_const.matrix_mul continuous_id).measurable.aemeasurable
  · rw [e, Measure.smul_apply]
    have h0 : _root_.Formalism.MainNotions.S.haarLie (Nset k r) 1 (NS k r)ᶜ = 0 := hnull
    rw [h0, smul_eq_mul, mul_zero]
end
end

section

theorem sz_constant_term : PI.SzCt.SzCt :=
  PI.SzCt.UnitaryGroupMassFormula.szCt_of PI.SzCt.UnitaryGroupMassFormula.rowA PI.SzCt.UnitaryGroupMassFormula.rowB PI.SzCt.UnitaryGroupMassFormula.rowC
    PI.SzCt.UnitaryGroupMassFormula.sizeFacts PI.SzCt.UnitaryGroupMassFormula.placeFacts
end

section

theorem PI.OrbRestrOne : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestrictionAtConjugate E := by
  intro D E p _ h5 hn u i Th hTh z
  obtain ⟨ep0, hep0, be, hbe, ep, hep, sg, hsg, U, hU, hEq⟩ := hTh
  have hc : ∀ w, MvPowerSeries.constantCoeff (be w) = 0 := fun w =>
    PI.OrbJet.constantCoeff_zero_of_jet_bound p 2 (be w) (hbe w).2.2.1
  have key := PI.OrbJet.restricted_single_jet_equation (D := D) p hn z Th U ep0 be hc ep sg hEq
  dsimp only [PI.OrbJet.oneLoc, PI.OrbJet.OJ.Loc1.AdmB, PI.OrbJet.OJ.Loc1.B0, PI.OrbJet.OJ.Loc1.Tht]
  refine ⟨ep0, hep0, be z, ⟨ep z, hep z, sg z, hsg z, _, ?_, key⟩,
    (hbe z).1, (hbe z).2.1, (hbe z).2.2.1, (hbe z).2.2.2⟩
  intro m
  rw [MvPowerSeries.coeff_killCompl]
  exact hU _
end
