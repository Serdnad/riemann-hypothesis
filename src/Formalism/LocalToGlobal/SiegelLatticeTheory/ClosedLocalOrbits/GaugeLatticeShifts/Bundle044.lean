module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHGlue
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle041
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle042
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle032
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB Formalism.L2.SG.Pf.Jac

variable {k r : ℕ}

def gA (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r) : Mt k r :=
  fun i j => ((Matrix.of a)⁻¹ * E * Matrix.of b) i j

def gB (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r) : Mt k r :=
  fun i j => (Matrix.of a * E * (Matrix.of b)⁻¹) i j

theorem meas_gA (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {f : Mt k r → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun p : Mt k r × Mt k r => f (gA E p.1 p.2) := by
  have e : (fun p : Mt k r × Mt k r => gA E p.1 p.2) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => ((Matrix.of p.1)⁻¹) i j : Mt k r) *
        Matrix.of (E : Mt k r)) i j : Mt k r) * Matrix.of p.2) i j : Mt k r) := by
    funext p; rfl
  have : Measurable fun p : Mt k r × Mt k r => gA E p.1 p.2 := by
    rw [e]
    exact mulMt_meas (mulMt_meas (invMt_meas measurable_fst) measurable_const) measurable_snd
  exact hf.comp this

theorem measurable_comp_group_action (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a0 : Mt k r) {f : Mt k r → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun b : Mt k r => f (gA E a0 b) := by
  let P : Mt k r → Mt k r := fun b =>
    ((Matrix.of a0)⁻¹ * E * Matrix.of b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
  have hP : Continuous P := by
    show Continuous fun b : Mt k r =>
      ((Matrix.of a0)⁻¹ * E * Matrix.of b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    fun_prop
  exact hf.comp hP.measurable

theorem gA_inv (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r)
    (ha : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det) :
    gA E (Formalism.FourierDecayAlt.B2.invM a) (Formalism.FourierDecayAlt.B2.invM b) = gB E a b := by
  have h1 : ((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ = Matrix.of a :=
    Matrix.nonsing_inv_nonsing_inv _ ha
  show (fun i j => (((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ * E *
      (Matrix.of b)⁻¹) i j : Mt k r) = fun i j => (Matrix.of a * E * (Matrix.of b)⁻¹) i j
  rw [h1]

theorem prod_to_iter {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z')
    (hT' : 0 < Tz k r z') {μW μW' : Measure (Mt k r)} (hW : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW)
    (hW' : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z') μW') (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    {f : Mt k r → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p : Mt k r × Mt k r, f ((Matrix.of p.1)⁻¹ * E * Matrix.of p.2) ∂(μW.prod μW') =
      ∫⁻ h, ∫⁻ h', f (fun i j => (Matrix.of h * E * (Matrix.of h')⁻¹) i j) ∂μW' ∂μW := by
  have sW := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW
  have sW' := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW'
  have hinv : μW.map Formalism.FourierDecayAlt.B2.invM = μW :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z) μW (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hW
  have hinv' : μW'.map Formalism.FourierDecayAlt.B2.invM = μW' :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z') μW' (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z') hW'
  have hA := meas_gA (k := k) (r := r) E hf
  have e0 : (fun p : Mt k r × Mt k r => f ((Matrix.of p.1)⁻¹ * E * Matrix.of p.2)) = fun p => f (gA E p.1 p.2) := by
    funext p; rfl
  rw [e0, lintegral_prod (fun p : Mt k r × Mt k r => f (gA E p.1 p.2)) hA.aemeasurable]
  have key : ∀ (ν : Measure (Mt k r)), ν.map Formalism.FourierDecayAlt.B2.invM = ν → ∀ F : Mt k r → ℝ≥0∞, Measurable F →
      ∫⁻ a, F a ∂ν = ∫⁻ a, F (Formalism.FourierDecayAlt.B2.invM a) ∂ν := by
    intro ν hν F hF
    conv_lhs => rw [← hν]
    exact lintegral_map hF Formalism.FourierDecayAlt.P.B2x1.invM_meas
  refine (key μW hinv _ hA.lintegral_prod_right').trans ?_
  have hae : ∀ᵐ a ∂μW, (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z :=
    ae_iff.2 hW.conc
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with a ha
  have hau : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det := unit_of_UH ha.1
  refine (key μW' hinv' _ (measurable_comp_group_action E (Formalism.FourierDecayAlt.B2.invM a) hf)).trans ?_
  refine lintegral_congr fun b => ?_
  rw [gA_inv E a b hau]
  rfl

theorem rhsWHaar : RhsWHaar := by
  intro k r z z' μW μW' a a' μsec D
  obtain ⟨μb0, hb0⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  have hW := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 k r z μW D.z_mem D.T_pos D.haarW
  have hW' := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 k r z' μW' D.z'_mem D.T'_pos D.haarW'
  obtain ⟨C, hC, hI⟩ := Formalism.FourierDecayAlt.P.rank_one_integration_formula k r z z' μsec μb0 μW μW' D.k_pos D.z_mem D.z'_mem
    D.T_pos D.T'_pos D.sec hb0 hW hW'
  refine ⟨C⁻¹ • μb0, isHaarOn_smul (skHaar_of_cs hb0) (inv_pos.2 hC), fun φ hφ => ?_⟩
  rw [lintegral_smul_measure, hI φ hφ]
  unfold rhsW
  simp_rw [prod_to_iter D.z_mem D.T_pos D.z'_mem D.T'_pos hW hW' _ hφ]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hC.ne', ENNReal.coe_one, one_mul]

theorem mBase_mem {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (hsec : IsSection k r z z' μsec) :
    mBase k r z z' μsec ∈ Formalism.FourierDecayAlt.B2.UWb k r := by
  have hlt : Tz k r z * Tz k r z' < Complex.normSq (zeta0 k r z z') := by
    have hp : 0 < Tz k r z * Tz k r z' := mul_pos hT hT'
    unfold zeta0
    rw [Complex.normSq_ofReal]
    have hs := Real.mul_self_sqrt hp.le
    have e : (2 * Real.sqrt (Tz k r z * Tz k r z')) * (2 * Real.sqrt (Tz k r z * Tz k r z')) =
        4 * (Real.sqrt (Tz k r z * Tz k r z') * Real.sqrt (Tz k r z * Tz k r z')) := by ring
    rw [e, hs]
    linarith
  exact (Formalism.FourierDecayAlt.P.unipotent_weyl_properties k r).1 ▸ ⟨_, (hsec.2 _ hlt).1, rfl⟩

theorem gaugeShiftW : GaugeShiftW := by
  intro k r z z' μb μW μW' a a' μsec D hμb ρ hρ
  have hg : MeasurableSet (bBall k r ρ) := measurableSet_expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) ρ hρ
  have hmem : (mBase k r z z' μsec)⁻¹ ∈ Formalism.FourierDecayAlt.B2.UWb k r :=
    (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r).inv_mem _ (mBase_mem D.T_pos D.T'_pos D.sec)
  have hl : Measurable (lmulM (k := k) (r := r) (mBase k r z z' μsec)⁻¹) := by
    have : Continuous (lmulM (k := k) (r := r) (mBase k r z z' μsec)⁻¹) := by
      show Continuous fun x : Mt k r =>
        ((mBase k r z z' μsec)⁻¹ * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      exact continuous_const.matrix_mul continuous_id
    exact this.measurable
  have e : mBall k r z z' μsec ρ = lmulM (mBase k r z z' μsec)⁻¹ ⁻¹' bBall k r ρ := rfl
  refine ⟨e ▸ hl hg, ?_⟩
  rw [e, ← Measure.map_apply hl hg, hμb.2.2.2 _ hmem]

theorem wbDataEx : WbDataEx := by
  intro k r hk
  set z : Fin (2 * r + k + 1) → ℂ := Formalism.L2.SG.Pf.WFL.zBv k r 1 with hz
  have hzW : inWb k r z := Formalism.L2.SG.Pf.WFL.inWb_zB 1
  have hzT : Tz k r z = 1 := Formalism.L2.SG.Pf.WFL.Tz_zB zero_le_one
  have hT : 0 < Tz k r z := by rw [hzT]; exact one_pos
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hzW hT
  have hcpt := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hzW hT
  have hfin : μ Set.univ < ⊤ := by
    have h1 : μ Set.univ ≤ μ (UWset k r z : Set (Mt k r)) + μ (UWset k r z : Set (Mt k r))ᶜ := by
      have := measure_union_le (μ := μ) (UWset k r z : Set (Mt k r)) (UWset k r z : Set (Mt k r))ᶜ
      rwa [Set.union_compl_self] at this
    have h2 : μ (UWset k r z : Set (Mt k r))ᶜ = 0 := hμ.conc
    have h3 : μ (UWset k r z : Set (Mt k r)) < ⊤ := hμ.finite_compact _ hcpt
    rw [h2, add_zero] at h1
    exact lt_of_le_of_lt h1 h3
  have h0 : μ Set.univ ≠ 0 := fun h => hμ.ne_zero (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨μsec, hsec⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k r z z hk hzW hzW hT hT
  have ha : 0 < (μ Set.univ).toReal := ENNReal.toReal_pos h0 hfin.ne
  have hm : μ Set.univ = ENNReal.ofReal (μ Set.univ).toReal := (ENNReal.ofReal_toReal hfin.ne).symm
  exact ⟨z, z, μ, μ, _, _, μsec, ⟨hk, hzW, hzW, hT, hT, skHaar_of_cs hμ, skHaar_of_cs hμ, ha, ha, hm, hm, hsec⟩⟩

end Formalism.L2.SG.Pf.GE
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem ballDim : BallDim := by
  intro E _ _ _ _ _ s
  let f := (stdOrthonormalBasis ℝ E).repr
  have hf : MeasurePreserving f := f.measurePreserving
  have e : f ⁻¹' Metric.ball 0 s = Metric.ball 0 s := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  rw [← e, hf.measure_preimage measurableSet_ball.nullMeasurableSet]

variable {k r : ℕ}

theorem measurableSet_expImage_univ (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :
    MeasurableSet ((fun x : Formalism.MainNotions.S.lieE S =>
      fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j : Formalism.MainNotions.S.lieE S → Mt k r) '' Set.univ) := by
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) S
  have hU : (Set.univ : Set (Formalism.MainNotions.S.lieE S)) = ⋃ n : ℕ, Metric.closedBall 0 (n : ℝ) := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, Metric.mem_closedBall, dist_zero_right, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact ⟨n, hn⟩
  rw [hU, Set.image_iUnion]
  exact MeasurableSet.iUnion fun n => ((isCompact_closedBall _ _).image hE).isClosed.measurableSet

theorem rhoMeas : RhoMeas := by
  intro k r S
  refine measurable_of_Iio fun t => ?_
  have e : rhoS k r S ⁻¹' Set.Iio t = (fun x : Formalism.MainNotions.S.lieE S =>
      fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j : Formalism.MainNotions.S.lieE S → Mt k r) ''
        {Y | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞) < t} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, rhoS, iInf_lt_iff, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨Y, hY, hlt⟩; exact ⟨Y, hlt, hY⟩
    · rintro ⟨Y, hlt, hY⟩; exact ⟨Y, hY, hlt⟩
  rw [e]
  rcases eq_or_ne t ⊤ with rfl | ht
  · have : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
        < ⊤} = Set.univ := by
      ext Y; simp
    rw [this]
    exact measurableSet_expImage_univ S
  · rcases eq_or_ne t 0 with rfl | ht0
    · have : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
          < 0} = ∅ := by ext Y; simp
      rw [this, Set.image_empty]; exact MeasurableSet.empty
    · have hb : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
          < t} = Metric.ball 0 t.toReal := by
        ext Y
        simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
        rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) ht]
        rfl
      have hpos : 0 < t.toReal := ENNReal.toReal_pos ht0 ht
      rw [hb]
      exact measurableSet_expBall (k := k) (r := r) S t.toReal hpos

theorem rhoN : RhoN := by
  intro k r Y
  have hinj : ∀ Y' : Formalism.MainNotions.S.lieE (Nset k r), expL k r (Nset k r) Y' = expL k r (Nset k r) Y → Y' = Y := by
    intro Y' h
    have hY : (Y : EuclideanSpace ℝ _) ∈ (Formalism.MainNotions.BridgeCSB.lieNS k r).map Formalism.MainNotions.BridgeCSB.RL := by
      rw [← Formalism.MainNotions.BridgeCSB.lieE_N]; exact Y.2
    have hY' : (Y' : EuclideanSpace ℝ _) ∈ (Formalism.MainNotions.BridgeCSB.lieNS k r).map Formalism.MainNotions.BridgeCSB.RL := by
      rw [← Formalism.MainNotions.BridgeCSB.lieE_N]; exact Y'.2
    obtain ⟨X, hX, hXY⟩ := hY
    obtain ⟨X', hX', hXY'⟩ := hY'
    have e1 : Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _) = X := by
      rw [← hXY]; exact Formalism.MainNotions.BridgeCSB.unrealify_RL X
    have e2 : Formalism.MainNotions.S.unrealify (Y' : EuclideanSpace ℝ _) = X' := by
      rw [← hXY']; exact Formalism.MainNotions.BridgeCSB.unrealify_RL X'
    have hexp : NormedSpace.exp X' = NormedSpace.exp X := by
      have h2 : (fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y' : EuclideanSpace ℝ _)) i j : Mt k r) =
          fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j := h
      rw [e1, e2] at h2
      ext i j
      exact congrFun (congrFun h2 i) j
    have hXX : X' = X := Formalism.MainNotions.BridgeCSB.exp_injOn hX'.1 hX.1 hexp
    apply Subtype.ext
    rw [← hXY, ← hXY', hXX]
  unfold rhoS
  refine le_antisymm (iInf_le_of_le Y (iInf_le_of_le rfl le_rfl)) (le_iInf₂ fun Y' hY' => ?_)
  rw [hinj Y' hY']
  exact le_of_eq rfl

end Formalism.L2.SG.Pf.BH
end
end

section

noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem good_eq {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) :
    Good X u u' = Set.univ.pi fun _ => GoodLoc (r := D.R.rS) (Tw u) (Tw u') := by
  ext y
  first
  | (simp only [Good, GoodLoc, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq])
  | (simp only [Good, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]; rfl)
  | (simp [Good, GoodLoc])
  | (show _ ↔ _; exact Iff.rfl)

theorem product_formula_holds : P5 := by
  intro hJac hDC hSM hU hNH hR D X u u' sc hsc
  have hep : ∀ v a b, hJ (X.B.I.ε v) (eV X v a) (pV X v b) = if a = b then 1 else 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
  have hpp : ∀ v a b, hJ (X.B.I.ε v) (pV X v a) (pV X v b) = 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ff]; simp)
  have hzp : ∀ w v b, hJ (X.B.I.ε v) (zV X w v) (pV X v b) = 0 := fun w v b => by
    have h0 : hJ (X.B.I.ε v) (pV X v b) (zV X w v) = 0 :=
      (hJ_X X v _ _).trans (by rw [(X.zu_orth w b).2]; simp)
    rw [hJ_cj, h0, map_zero]
  have hSH : ∀ w v, IsHaarS (SLoc (X.B.I.ε v) (eV X v) (zV X w v)) (muSv X w v) := fun w v =>
    hNH _ _ _ _ _ _ _ _ _ _ (frameLoc_X X w u v) (hep v) (hpp v) (hzp w v) _ _ (muNv_haar X w v) (muHv_haar X w v)
  haveI : ∀ w v, SigmaFinite (muSv X w v) := fun w v => (hSH w v).1.1
  obtain ⟨κ, hκ0, hκT, hκ⟩ := muS_eq X u (fun v => inferInstance)
  obtain ⟨κ', hκ'0, hκ'T, hκ'⟩ := muS_eq X u' (fun v => inferInstance)
  have hsec := fun v => hSM _ _ _ _ _ _ _ _ _ sc (frameLoc_X X u u' v) hsc
  choose hs hsm hss using hsec
  have hjl := fun v => hJac _ _ _ _ _ _ _ _ _ sc (frameLoc_X X u u' v) hsc _ _ (hSH u v) (hSH u' v) (hs v) (hss v)
  choose Cv hCv hDis using hjl
  have hloc : ∀ v, Formalism.REAL.muG (X.B.I.ε v) =
      ((nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v)).prod ((muSv X u v).prod (muSv X u' v))).map
        (phiLoc (X.B.I.ε v) (hs v)) := fun v =>
    muG_eq_map _ _ _ _ _ _ _ (hsm v) _ (hDis v)
  set Cp : ℝ := ∏ v, Cv v with hCp
  have hCp0 : 0 < Cp := Finset.prod_pos fun v _ => hCv v
  have hκr : 0 < κ.toReal := ENNReal.toReal_pos hκ0 hκT
  have hκr' : 0 < κ'.toReal := ENNReal.toReal_pos hκ'0 hκ'T
  refine ⟨Cp / (κ.toReal * κ'.toReal), div_pos hCp0 (mul_pos hκr hκr'), fun φ hφ => ?_⟩
  have hpf := prod_formula (fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v))
    (muSv X u) (muSv X u') hs hsm hloc φ hφ
  change ∫⁻ x, φ x ∂(Measure.pi fun v => Formalism.REAL.muG (X.B.I.ε v)) = _
  rw [hpf]

  have hwm : ∀ v, Measurable fun c : Fin (D.R.rS + 1) → ℂ => ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') c) :=
    fun v => ENNReal.measurable_ofReal.comp (measurable_const.mul (wtLoc_cont D.R.k (Tw u) (Tw u')).measurable)
  have hν : Measure.pi (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v)) =
      ((dcInf X).restrict (Good X u u')).withDensity
        (fun c => ∏ v, ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') (c v))) := by
    unfold nuLoc
    haveI : SigmaFinite (dcLoc (r := D.R.rS)) := by unfold dcLoc; infer_instance
    rw [PiM.pi_withDensity _ _ hwm (fun v x => ENNReal.ofReal_ne_top), ← Measure.restrict_pi_pi, good_eq]
    rfl
  set H : (Cinf X) → X.B.I.Ginf := fun c v => hs v (c v) with hHd
  have hHm : Measurable H := Measurable.of_eval fun v => (hsm v).comp (measurable_pi_apply v)
  set Fc : Cinf X → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * H c * s'⁻¹) ∂Measure.pi (muSv X u') ∂Measure.pi (muSv X u)
    with hFc
  have hFm : Measurable Fc := by
    have h1 : Measurable fun q : (Cinf X × X.B.I.Ginf) × X.B.I.Ginf => φ (q.1.2 * H q.1.1 * q.2⁻¹) :=
      hφ.comp (((measurable_snd.comp measurable_fst).mul (hHm.comp (measurable_fst.comp measurable_fst))).mul
        measurable_snd.inv)
    exact h1.lintegral_prod_right'.lintegral_prod_right'
  rw [show (∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => hs v (c v)) * s'⁻¹) ∂Measure.pi (muSv X u') ∂Measure.pi (muSv X u)
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v)) = ∫⁻ c, Fc c
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v) from rfl,
    hν, lintegral_withDensity_eq_lintegral_mul _
      (f := fun c : Cinf X => ∏ v, ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') (c v)))
      (Finset.measurable_prod _ fun v _ => (hwm v).comp (measurable_pi_apply v)) hFm]
  have hGm : MeasurableSet (Good X u u') := by
    rw [good_eq]; exact MeasurableSet.univ_pi fun v => measurableSet_goodLoc _ _
  refine setLIntegral_congr_fun hGm fun c hc => ?_
  simp only [Pi.mul_apply]
  have hcv : ∀ v, c v ∈ GoodLoc (r := D.R.rS) (Tw u) (Tw u') := fun v => by
    rw [good_eq, Set.mem_univ_pi] at hc; exact hc v

  have hW : ∏ v, ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') (c v)) = ENNReal.ofReal (Cp * wt X u u' c) := by
    rw [← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (hCv v).le (wtLoc_nonneg _ _ _ (hcv v)),
      Finset.prod_mul_distrib]
    rfl

  have hex := hR D X u u' sc hsc c hc
  have hh : HasDiag X u u' sc c (hOf X u u' sc c) := by
    unfold hOf; rw [dite_eq_left hex]; exact hex.choose_spec
  have hdc := fun v => hDC _ _ _ _ _ _ _ _ _ sc (frameLoc_X X u u' v) (c v) (hcv v) (hs v (c v)) (hOf X u u' sc c v)
    (hss v (c v) (hcv v)) (hh v)
  choose t ht t' ht' htt using hdc
  have hofe : hOf X u u' sc c = t * H c * t'⁻¹ := funext fun v => htt v
  have hrt : (Measure.pi (muSv X u)).map (fun x => x * t) = Measure.pi (muSv X u) :=
    PiM.pi_map_mul_right _ t fun v => hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u u' v) _ (hSH u v) (t v) (ht v)
  have hrt' : (Measure.pi (muSv X u')).map (fun x => x * t') = Measure.pi (muSv X u') :=
    PiM.pi_map_mul_right _ t' fun v => hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u' u v) _ (hSH u' v) (t' v) (ht' v)
  have hsw : ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' sc c * s'⁻¹) ∂Measure.pi (muSv X u') ∂Measure.pi (muSv X u) = Fc c := by
    rw [hofe]; exact dc_switch _ _ φ hφ (H c) t t' hrt hrt'

  have hinner : ∀ s, Measurable fun s' : X.B.I.Ginf => φ (s * hOf X u u' sc c * s'⁻¹) := fun s =>
    hφ.comp (measurable_const.mul measurable_inv)
  have hG2 : Measurable fun s : X.B.I.Ginf => ∫⁻ s', φ (s * hOf X u u' sc c * s'⁻¹) ∂Measure.pi (muSv X u') :=
    (hφ.comp ((measurable_fst.mul measurable_const).mul measurable_snd.inv)).lintegral_prod_right'
  have hmu : ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' sc c * s'⁻¹) ∂muS X u' ∂muS X u = κ * κ' * Fc c := by
    rw [hκ, hκ', lintegral_smul_measure]
    simp only [lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_const_mul' _ _ hκ'T, hsw]
    ring
  have hwc : 0 ≤ wt X u u' c := by
    unfold wt
    exact Finset.prod_nonneg fun v _ => wtLoc_nonneg D.R.k _ _ (hcv v)
  have hk : κ * κ' = ENNReal.ofReal (κ.toReal * κ'.toReal) := by
    rw [ENNReal.ofReal_mul hκr.le, ENNReal.ofReal_toReal hκT, ENNReal.ofReal_toReal hκ'T]
  rw [hmu, hW, hk, ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (div_pos hCp0 (mul_pos hκr hκr')).le hwc)]
  congr 2
  field_simp

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end
