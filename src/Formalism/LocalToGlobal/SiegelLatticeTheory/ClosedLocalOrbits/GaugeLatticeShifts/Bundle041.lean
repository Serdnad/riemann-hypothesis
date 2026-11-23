module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActMass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle040
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.PRhoRw
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB

theorem isHaarOn_smul {k r : ℕ} {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    {ν : Measure (Mt k r)} (h : Formalism.MainNotions.S.IsHaarOn S ν) {c : NNReal} (hc : 0 < c) :
    Formalism.MainNotions.S.IsHaarOn S (c • ν) := by
  obtain ⟨hσ, h0, hconc, hl⟩ := h
  have := hσ
  refine ⟨inferInstance, ?_, ?_, fun s hs => ?_⟩
  · intro h
    apply h0
    exact (smul_eq_zero.1 h).resolve_left hc.ne'
  · rw [Measure.smul_apply, hconc, smul_zero]
  · have hmeas := (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont (k := k) (r := r) s).measurable
    rw [Measure.map_smul c hmeas.aemeasurable, hl s hs]

theorem toReal_smul_apply {α : Type*} [MeasurableSpace α] (c : NNReal) (ν : Measure α) (A : Set α) :
    ((c • ν) A).toReal = (c : ℝ) * (ν A).toReal := by
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

theorem gaugeWb_of (hRW : RhsWHaar) (hD : WbDataEx) (hU : ExistsGaugeMeasureForEachRank) (hSW : GaugeShiftW) (hLW : RhsWLim) :
    ∀ k r : ℕ, ∃ μ : Measure (Mt k r), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μ := by
  intro k r
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hU r
  obtain ⟨z, z', μW, μW', a, a', μsec, D⟩ := hD k r hk
  obtain ⟨ν, hν, hνφ⟩ := hRW k r z z' μW μW' a a' μsec D
  have hw := wbConst_pos (k := k) D.T_pos D.T'_pos D.a_pos D.a'_pos
  set w := wbConst k (Tz k r z) (Tz k r z') a a' with hwdef
  refine ⟨(Real.toNNReal w) • ν, isHaarOn_smul hν (Real.toNNReal_pos.2 hw), ?_⟩
  have hlim := (hLW k r z z' μW μW' a a' μsec D).const_mul w
  rw [mul_inv_cancel₀ hw.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  obtain ⟨hm, he⟩ := hSW k r z z' ν μW μW' a a' μsec D hν ρ hρ
  have h1 : ∫⁻ x, (mBall k r z z' μsec ρ).indicator 1 x ∂ν = ν (mBall k r z z' μsec ρ) :=
    lintegral_indicator_one hm
  have h2 := hνφ _ (measurable_one.indicator hm)
  rw [h1, he] at h2
  show _ = ((Real.toNNReal w • ν) (bBall k r ρ)).toReal / bVol k r ρ
  rw [toReal_smul_apply, h2, Real.coe_toNNReal _ hw.le, mul_div_assoc]

theorem gaugeExists_of (hR : RhsHaar) (hRW : RhsWHaar) (hD : WbDataEx) (hU : ExistsGaugeMeasureForEachRank) (hS : GaugeShift)
    (hSW : GaugeShiftW) (hL : RhsLim) (hLW : RhsWLim) : GaugeExists := by
  intro k r
  have hb := gaugeWb_of hRW hD hU hSW hLW k r
  refine ⟨?_, hb⟩
  obtain ⟨μb, hμb⟩ := hb
  obtain ⟨ν, hν, hνφ⟩ := hR k r μb hμb
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  refine ⟨(Real.toNNReal (2 ^ r)) • ν, isHaarOn_smul hν (Real.toNNReal_pos.2 h2r), ?_⟩
  have hlim := (hL k r μb hμb).const_mul ((2 : ℝ) ^ r)
  rw [mul_inv_cancel₀ h2r.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  obtain ⟨hm, he⟩ := hS k r ν hν ρ hρ
  have h1 : ∫⁻ x, (wBall k r ρ).indicator 1 x ∂ν = ν (wBall k r ρ) := lintegral_indicator_one hm
  have h2 := hνφ _ (measurable_one.indicator hm)
  rw [h1, he] at h2
  show _ = ((Real.toNNReal (2 ^ r) • ν) (gBall k r ρ)).toReal / gVol k r ρ
  rw [toReal_smul_apply, h2, Real.coe_toNNReal _ h2r.le, mul_div_assoc]

theorem iterGauge_of (hR : RhsHaar) : IterGauge := by
  intro k r μ μb hμ hμb
  obtain ⟨ν, hν, hνφ⟩ := hR k r μb hμb
  obtain ⟨ν0, h0⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨c1, hc1, hc1', e1⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) h0 hμ.1
  obtain ⟨c2, hc2, hc2', e2⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) h0 hν
  have hne : c1 / c2 ≠ ∞ := (ENNReal.div_lt_top hc1' hc2).ne
  refine ⟨(c1 / c2).toNNReal, ENNReal.toNNReal_pos (ENNReal.div_pos_iff.2 ⟨hc1, hc2'⟩).ne' hne,
    fun φ hφ => ?_⟩
  rw [ENNReal.coe_toNNReal hne, ← hνφ φ hφ, e1, e2, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.div_mul_cancel hc2 hc2']

theorem rankGauge_of (hRW : RhsWHaar) : RankGauge := by
  intro k r z z' μb μW μW' a a' μsec D hμb
  obtain ⟨ν, hν, hνφ⟩ := hRW k r z z' μW μW' a a' μsec D
  obtain ⟨ν0, h0⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  obtain ⟨c1, hc1, hc1', e1⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) h0 hμb.1
  obtain ⟨c2, hc2, hc2', e2⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) h0 hν
  have hne : c1 / c2 ≠ ∞ := (ENNReal.div_lt_top hc1' hc2).ne
  refine ⟨(c1 / c2).toNNReal, ENNReal.toNNReal_pos (ENNReal.div_pos_iff.2 ⟨hc1, hc2'⟩).ne' hne,
    fun φ hφ => ?_⟩
  rw [ENNReal.coe_toNNReal hne, ← hνφ φ hφ, e1, e2, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.div_mul_cancel hc2 hc2']

theorem bruhatHaar_of_rhsHaar (hR : RhsHaar) (hS : GaugeShift) (hW : Sandwich) (hV : VolLim) : BruhatHaar :=
  bruhatHaar_of_iterGauge (iterGauge_of hR) hS hW hV

theorem wbHaar_of_rhsWHaar (hRW : RhsWHaar) (hSW : GaugeShiftW) (hLW : RhsWLim) : WbHaar :=
  wbHaar_of (rankGauge_of hRW) hSW hLW

end Formalism.L2.SG.Pf.GE
end
end

section

namespace Formalism.L2.SG.Pf

theorem massAC_holds : Formalism.L2.SG.NormCut.MassAC :=
  massAC_of Formalism.L2.SG.Closed.NeatC_holds

end Formalism.L2.SG.Pf
end

section

noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped InnerProductSpace

namespace Formalism.L2.SG.RealObj.EnergyIntTor

variable {k r : ℕ}

theorem cont_conj (A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous fun x : Mt k r => (fun i j => (A * Matrix.of x * B) i j : Mt k r) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply_apply i j).comp ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

def conjE {μ : ℂ} (hμ : μ ≠ 0) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (torS μ⁻¹ k r * Matrix.of x * torS μ k r) i j
  invFun x := fun i j => (torS μ k r * Matrix.of x * torS μ⁻¹ k r) i j
  left_inv x := by
    funext i j
    show (torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r) i j = x i j
    rw [show torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r =
      (torS μ k r * torS μ⁻¹ k r) * Matrix.of x * (torS μ k r * torS μ⁻¹ k r) by simp only [Matrix.mul_assoc],
      torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one]
    rfl
  right_inv x := by
    funext i j
    show (torS μ⁻¹ k r * (torS μ k r * Matrix.of x * torS μ⁻¹ k r) * torS μ k r) i j = x i j
    rw [show torS μ⁻¹ k r * (torS μ k r * Matrix.of x * torS μ⁻¹ k r) * torS μ k r =
      (torS μ⁻¹ k r * torS μ k r) * Matrix.of x * (torS μ⁻¹ k r * torS μ k r) by simp only [Matrix.mul_assoc],
      torS_inv_mul μ hμ, Matrix.one_mul, Matrix.mul_one]
    rfl
  measurable_toFun := (cont_conj _ _).measurable
  measurable_invFun := (cont_conj _ _).measurable

theorem conjE_apply {μ : ℂ} (hμ : μ ≠ 0) (x : Mt k r) :
    Matrix.of (conjE (k := k) (r := r) hμ x) = torS μ⁻¹ k r * Matrix.of x * torS μ k r := rfl

theorem conjE_mem_N {μ : ℂ} (hμ : μ ≠ 0) (x : Mt k r) :
    Matrix.of (conjE (k := k) (r := r) hμ x) ∈ Nset k r ↔ Matrix.of x ∈ Nset k r := by
  rw [conjE_apply]
  constructor
  · intro h
    have := tor_conj_N hμ h
    rwa [show torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r =
      (torS μ k r * torS μ⁻¹ k r) * Matrix.of x * (torS μ k r * torS μ⁻¹ k r) by simp only [Matrix.mul_assoc],
      torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one] at this
  · intro h
    have := tor_conj_N (inv_ne_zero hμ) h
    rwa [inv_inv] at this

theorem haarN_tor {μ : ℂ} (hμ : μ ≠ 0) {μN : Measure (Mt k r)} (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN) :
    Formalism.MainNotions.S.IsHaarOn (Nset k r) (μN.map (conjE hμ)) := by
  obtain ⟨hsf, hne, hconc, hleft⟩ := hN
  refine ⟨(conjE hμ).sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · intro h0
    apply hne
    have h1 := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h1
    rw [MeasurableEquiv.map_apply, Set.preimage_univ] at h1
    exact Measure.measure_univ_eq_zero.mp h1
  · rw [MeasurableEquiv.map_apply]
    have e : (conjE (k := k) (r := r) hμ) ⁻¹' {x : Mt k r | Matrix.of x ∉ Nset k r} =
        {x : Mt k r | Matrix.of x ∉ Nset k r} := by
      ext x; simp only [Set.mem_preimage, Set.mem_ofPred_eq, conjE_mem_N]
    rw [e]; exact hconc
  · have hs' : torS μ k r * s * torS μ⁻¹ k r ∈ Nset k r := tor_conj_N hμ hs
    have hmeas : Measurable (lmulM (k := k) (r := r) s) := by
      unfold lmulM
      exact (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply i j).comp (continuous_const.matrix_mul continuous_id)).measurable
    have hmeas' : Measurable (lmulM (k := k) (r := r) (torS μ k r * s * torS μ⁻¹ k r)) := by
      unfold lmulM
      exact (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply i j).comp (continuous_const.matrix_mul continuous_id)).measurable
    rw [Measure.map_map hmeas (conjE hμ).measurable]
    have e : lmulM (k := k) (r := r) s ∘ (conjE hμ) = (conjE hμ) ∘ lmulM (torS μ k r * s * torS μ⁻¹ k r) := by
      funext x
      simp only [Function.comp_apply]
      change (s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
        (torS μ⁻¹ k r * (torS μ k r * s * torS μ⁻¹ k r * Matrix.of x) * torS μ k r :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      calc s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r)
          = (torS μ⁻¹ k r * torS μ k r) * s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) := by
            rw [torS_inv_mul μ hμ, Matrix.one_mul]
        _ = torS μ⁻¹ k r * (torS μ k r * s * torS μ⁻¹ k r * Matrix.of x) * torS μ k r := by
            simp only [Matrix.mul_assoc]
    rw [e, ← Measure.map_map (conjE hμ).measurable hmeas', hleft _ hs']

theorem be_tor {μ : ℂ} (hμ : μ ≠ 0) {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ)
    (π π' : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)) (σ σ' : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H))
    (hσ : ∀ m, σ' m = σ (torS μ k r * m * torS μ⁻¹ k r)) (hπ : ∀ h ∈ UWset k r z, π' h = π h)
    (μW μN : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN]
    (hW : μW {x : Mt k r | Matrix.of x ∉ UWset k r z} = 0) (x y : H) :
    Formalism.FourierDecayAlt.ThreeDimData.be z (c * μ) π' σ' μW (μN.map (conjE hμ)) x y = Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN x y := by
  unfold Formalism.FourierDecayAlt.ThreeDimData.be
  have : SigmaFinite (μN.map (conjE hμ)) := (conjE hμ).sigmaFinite_map
  have e : (μW.prod μN).map (Prod.map id (conjE hμ)) = μW.prod (μN.map (conjE hμ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (conjE hμ).measurable, Measure.map_id]
  have hme : MeasurableEmbedding (Prod.map id (conjE (k := k) (r := r) hμ)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Mt k r)) (conjE hμ)).measurableEmbedding
  rw [← e, hme.integral_map]
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    have es : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} =
        {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
      ext p; simp
    rw [es, Measure.prod_prod, hW, zero_mul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with p hp
  unfold Formalism.FourierDecayAlt.ThreeDimData.beInt
  simp only [Prod.map, id]
  have h1 : σ' (Matrix.of p.1 * Matrix.of (conjE hμ p.2)) = σ (Matrix.of p.1 * Matrix.of p.2) := by
    rw [hσ, conjE_apply]
    congr 1
    calc torS μ k r * (Matrix.of p.1 * (torS μ⁻¹ k r * Matrix.of p.2 * torS μ k r)) * torS μ⁻¹ k r
        = (torS μ k r * Matrix.of p.1 * torS μ⁻¹ k r) * Matrix.of p.2 * (torS μ k r * torS μ⁻¹ k r) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.of p.1 * Matrix.of p.2 := by rw [tor_conj_uw hμ hp, torS_mul_inv μ hμ, Matrix.mul_one]
  have h2 : psi k r z (c * μ) (Matrix.of (conjE hμ p.2)) = psi k r z c (Matrix.of p.2) := by
    rw [← psi_tor hμ hz c, conjE_apply]
    congr 1
    calc torS μ k r * (torS μ⁻¹ k r * Matrix.of p.2 * torS μ k r) * torS μ⁻¹ k r
        = (torS μ k r * torS μ⁻¹ k r) * Matrix.of p.2 * (torS μ k r * torS μ⁻¹ k r) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.of p.2 := by rw [torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one]
  have h3 : π' (Matrix.of p.1)⁻¹ = π (Matrix.of p.1)⁻¹ := hπ _ (PI.UnitaryGroupMassFormula.JCC.uwset_inv hp)
  rw [h1, h2, h3]

end Formalism.L2.SG.RealObj.EnergyIntTor
end
end

section

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyIntLoc

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem scale_eq (D : D7) : Formalism.L2.SG.Pf.WuBL.cS D * muT D = Formalism.QuantumDeterminants.cStd := by
  have h1 := Formalism.L2.SG.Pf.WuBL.cS_ne D
  unfold Formalism.L2.SG.Pf.WuBL.cS at h1
  have hka : D.host.ka ≠ 0 := by rintro h; apply h1; simp [h]
  have hg : ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≠ 0 := by intro h; apply h1; simp [h]
  have hg0 : (D.host.g 0 : ℂ) ≠ 0 := by
    have := (mul_ne_zero_iff.1 hg).1; exact_mod_cast this
  have hg1 : (D.host.g 1 : ℂ) ≠ 0 := by
    have := (mul_ne_zero_iff.1 hg).2; exact_mod_cast this
  have hka' : (D.host.ka : ℂ) ≠ 0 := by exact_mod_cast hka
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold Formalism.L2.SG.Pf.WuBL.cS muT cfS frS Formalism.QuantumDeterminants.cStd
  push_cast
  field_simp

theorem transpC' (C : Choice X θ) (τ : D.what₂.Tau) :
    IsTranspC X (vOf X τ) (cfS D) D.R.k D.R.rS (Qcs C τ) (Qics C τ) :=
  Formalism.L2.SG.Pf.torTie X _ _ _ (C.isT τ)

theorem zc_eq (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Qics C τ *ᵥ rv X.B.I (vOf X τ) (X.zR u) = zB X (C.Qi τ) u τ := by
  have hw := (Formalism.L2.SG.Pf.zTr C u τ).1
  unfold Qics
  rw [← Matrix.mulVec_mulVec]
  change torS (muT D)⁻¹ D.R.k D.R.rS *ᵥ zB X (C.Qi τ) u τ = zB X (C.Qi τ) u τ
  funext i
  simp only [torS, Matrix.mulVec_diagonal]
  split_ifs with h1 h2
  · rw [hw i (Or.inl h1), mul_zero]
  · rw [hw i (Or.inr h2), mul_zero]
  · rw [one_mul]

theorem sigC_eq (C : Choice X θ) (τ : D.what₂.Tau) (m : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) :
    sigB X (Qcs C τ) (Qics C τ) τ m =
      sigB X (C.Q τ) (C.Qi τ) τ (torS (muT D) D.R.k D.R.rS * m * torS (muT D)⁻¹ D.R.k D.R.rS) := by
  unfold sigB Qcs Qics
  simp only [Matrix.mul_assoc]

theorem piC_eq (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau)
    {h : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (hh : h ∈ Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    piB X (Qcs C τ) (Qics C τ) u τ h = piB X (C.Q τ) (C.Qi τ) u τ h := by
  unfold piB Qcs Qics
  have e : C.Q τ * torS (muT D) D.R.k D.R.rS * h * (torS (muT D)⁻¹ D.R.k D.R.rS * C.Qi τ)
      = C.Q τ * (torS (muT D) D.R.k D.R.rS * h * torS (muT D)⁻¹ D.R.k D.R.rS) * C.Qi τ := by
    simp only [Matrix.mul_assoc]
  rw [e, tor_conj_uw (Formalism.L2.SG.Pf.muT_ne D) hh]

theorem inUJ_tr {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {m : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : Formalism.REAL.inUJ (X.B.I.ε v) (Q * m * Qi) := by
  obtain ⟨h1, h2, h3, -⟩ := hQ
  unfold Formalism.REAL.inUJ
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  have hJ : Formalism.REAL.Jm (X.B.I.ε v) = Qiᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Qi := by
    rw [← h3]
    calc Formalism.REAL.Jm (X.B.I.ε v) = (Q * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * Qi) := by
          rw [h2]; simp
      _ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  calc (Q * m * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * m * Qi)
      = Qiᴴ * (mᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * m) * Qi := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε v) := by rw [h3, hm', hJ]

private theorem conj_mem_lemma (D : D7)
    {a : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have hμ := Formalism.L2.SG.Pf.muT_ne D
  have g1 := Formalism.L2.SG.Pf.Choice.torS_gram (k := D.R.k) (r := D.R.rS) (muT D)⁻¹ (inv_ne_zero hμ)
  have g2 := Formalism.L2.SG.Pf.Choice.torS_gram (k := D.R.k) (r := D.R.rS) (muT D) hμ
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * a = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := ha
  show (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  calc (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS)
      = (torS (muT D)⁻¹ D.R.k D.R.rS)ᴴ * (aᴴ * ((torS (muT D) D.R.k D.R.rS)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * torS (muT D) D.R.k D.R.rS) * a) * torS (muT D)⁻¹ D.R.k D.R.rS := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by rw [g2, ha', g1]

theorem sigC_mul (C : Choice X θ) (τ : D.what₂.Tau)
    {a b : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS))
    (x : X.B.H (vOf X τ)) :
    sigB X (Qcs C τ) (Qics C τ) τ a (sigB X (Qcs C τ) (Qics C τ) τ b x) = sigB X (Qcs C τ) (Qics C τ) τ (a * b) x := by
  rw [sigC_eq, sigC_eq, sigC_eq]
  have hrep := (Formalism.L2.SG.Pf.WuBL.sigB_rep C τ).1.2 _ (conj_mem_lemma D ha) _ (conj_mem_lemma D hb)
  have hi := Formalism.L2.SG.Pf.Choice.torS_inv_mul (k := D.R.k) (r := D.R.rS) (muT D) (Formalism.L2.SG.Pf.muT_ne D)
  have e : torS (muT D) D.R.k D.R.rS * (a * b) * torS (muT D)⁻¹ D.R.k D.R.rS = (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS) * (torS (muT D) D.R.k D.R.rS * b * torS (muT D)⁻¹ D.R.k D.R.rS) := by
    calc torS (muT D) D.R.k D.R.rS * (a * b) * torS (muT D)⁻¹ D.R.k D.R.rS
        = torS (muT D) D.R.k D.R.rS * a * (torS (muT D)⁻¹ D.R.k D.R.rS * torS (muT D) D.R.k D.R.rS) * b * torS (muT D)⁻¹ D.R.k D.R.rS := by
          rw [hi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS) * (torS (muT D) D.R.k D.R.rS * b * torS (muT D)⁻¹ D.R.k D.R.rS) := by simp only [Matrix.mul_assoc]
  rw [e, hrep]
  rfl

theorem sigC_norm (C : Choice X θ) (τ : D.what₂.Tau)
    {a : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (x : X.B.H (vOf X τ)) :
    ‖sigB X (Qcs C τ) (Qics C τ) τ a x‖ = ‖x‖ := by
  rw [sigC_eq]
  exact (Formalism.L2.SG.Pf.WuBL.sigB_rep C τ).2 _ (conj_mem_lemma D ha) x

private theorem mul_mem_UH_Hpk' (D : D7) {a b : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * a = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * b = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (a * b) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by rw [ha', hb']

theorem dd_sub (C : Choice X θ) (τ : D.what₂.Tau)
    {yc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (hyc : yc ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Formalism.FourierDecayAlt.ThreeDimData.DDsp (sigB X (Qcs C τ) (Qics C τ) τ) (sigB X (Qcs C τ) (Qics C τ) τ yc (X.B.w (vOf X τ))) ≤
      Formalism.FourierDecayAlt.ThreeDimData.DDsp (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ) := by
  have hy := C.y_mem τ
  obtain ⟨hyi, -, hyy⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hy
  have hrep := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  unfold Formalism.FourierDecayAlt.ThreeDimData.DDsp
  apply Submodule.span_le.2
  rintro _ ⟨g, hg, rfl⟩
  beta_reduce
  rw [sigC_mul C τ hg hyc, sigC_eq]
  have hg'm : torS (muT D) D.R.k D.R.rS * (g * yc) * torS (muT D)⁻¹ D.R.k D.R.rS ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := conj_mem_lemma D (mul_mem_UH_Hpk' D hg hyc)
  have e : sigB X (C.Q τ) (C.Qi τ) τ (torS (muT D) D.R.k D.R.rS * (g * yc) * torS (muT D)⁻¹ D.R.k D.R.rS * (C.y τ)⁻¹) (v0Of C τ)
      = sigB X (C.Q τ) (C.Qi τ) τ (torS (muT D) D.R.k D.R.rS * (g * yc) * torS (muT D)⁻¹ D.R.k D.R.rS) (X.B.w (vOf X τ)) := by
    unfold v0Of
    rw [← ContinuousLinearMap.comp_apply, ← hrep.1.2 _ (mul_mem_UH_Hpk' D hg'm hyi) _ hy,
      Matrix.mul_assoc, hyy, Matrix.mul_one]
  rw [← e]
  exact Submodule.subset_span ⟨_, mul_mem_UH_Hpk' D hg'm hyi, rfl⟩

end Formalism.L2.SG.RealObj.EnergyIntLoc
end
end
