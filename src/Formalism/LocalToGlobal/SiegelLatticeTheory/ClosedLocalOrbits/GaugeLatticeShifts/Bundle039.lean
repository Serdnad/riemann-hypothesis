module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.ElementaryGeneratorAdjoint
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle010
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle008
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DistinctWordsDistinctParameters
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKeyPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolColPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolIndexPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle038
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib

@[expose] public section

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem exp_mulVec_of_zero {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (h : A *ᵥ v = 0) :
    NormedSpace.exp A *ᵥ v = v := by
  apply PI.QnHermHaar.HermitianAdjointLemmas.exp_mulVec_fix <;> assumption

theorem adjH_def {k r : ℕ} (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.MainNotions.BridgeCSB.adjH X = Hpk k r * Xᴴ * Hpk k r := rfl

theorem exp_mem_UH {k r : ℕ} {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : Hpk k r * Xᴴ * Hpk k r + X = 0) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) := by
  rw [Formalism.MainNotions.BridgeCSB.mem_UH_iff, Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul]
  have ha : Formalism.MainNotions.BridgeCSB.adjH X = -X := eq_neg_of_add_eq_zero_left hX
  rw [ha, Complex.star_def, Complex.conj_ofReal, smul_neg, ← Matrix.exp_add_of_commute]
  · rw [neg_add_cancel, NormedSpace.exp_zero]
  · exact (Commute.refl _).neg_left

theorem adj_of_lie {k r : ℕ} {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r)) : Hpk k r * Xᴴ * Hpk k r + X = 0 := by
  have hadj : Formalism.MainNotions.BridgeCSB.adjH X = -X := by
    apply Formalism.MainNotions.BridgeCSB.exp_smul_inj
    intro t
    have hU := hX t
    have h1 : Formalism.MainNotions.BridgeCSB.adjH (NormedSpace.exp ((t : ℂ) • X)) = (NormedSpace.exp ((t : ℂ) • X))⁻¹ :=
      (Matrix.inv_eq_left_inv ((Formalism.MainNotions.BridgeCSB.mem_UH_iff _).1 hU)).symm
    rw [Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul, Complex.star_def, Complex.conj_ofReal,
      ← Matrix.exp_neg] at h1
    rw [h1, smul_neg]
  rw [← adjH_def, hadj, neg_add_cancel]

theorem lieG : LieG := by
  intro k r
  ext X
  constructor
  · intro hX
    exact adj_of_lie hX
  · intro hX t
    exact exp_mem_UH hX t

theorem col_zero {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (j : Fin d)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j = bvec j) : X *ᵥ bvec j = 0 := by
  funext i
  have hij : X i j = 0 := by
    refine Formalism.MainNotions.BridgeCSB.entry_zero_of_const' X i j (bvec j i) fun t => ?_
    have := congrFun (h t) i
    rw [← this, Matrix.mulVec, dotProduct]
    simp [bvec, Pi.single_apply]
  rw [Matrix.mulVec, dotProduct]
  simp [bvec, Pi.single_apply, hij]

theorem lieWb : LieWb := by
  intro k r
  ext X
  constructor
  · intro hX
    refine ⟨adj_of_lie fun t => (hX t).1, fun a => ⟨?_, ?_⟩⟩
    · exact col_zero _ fun t => ((hX t).2 a).1
    · exact col_zero _ fun t => ((hX t).2 a).2
  · rintro ⟨hX, hk⟩ t
    refine ⟨exp_mem_UH hX t, fun a => ⟨?_, ?_⟩⟩
    · exact exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).1, smul_zero])
    · exact exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).2, smul_zero])

end Formalism.L2.SG.Pf.BH
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {k r : ℕ}

def mulF (p : Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

theorem meas_mulF : Measurable (mulF (k := k) (r := r)) :=
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.meas_mulP

theorem muS_eq (μW μN : Measure (Mt k r)) : Formalism.MainNotions.S.muS μW μN = (μW.prod μN).map mulF := rfl

theorem muS_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {μW μN : Measure (Mt k r)}
    (hW : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW) (hN : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN) :
    (Formalism.MainNotions.S.muS μW μN).map Formalism.FourierDecayAlt.B2.invM = Formalism.MainNotions.S.muS μW μN := by
  have sW := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.sigmaFinite_of_b hW
  have sN := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.sigmaFinite_of_b hN
  have hinvm : Measurable (Formalism.FourierDecayAlt.B2.invM : Mt k r → Mt k r) := Formalism.FourierDecayAlt.P.B2x2.invM_meas
  have hWi : μW.map Formalism.FourierDecayAlt.B2.invM = μW :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z) μW (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hW
  have hNi : μN.map Formalism.FourierDecayAlt.B2.invM = μN :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (Nset k r) μN (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN
  have hNc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN := Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hN

  let g : Mt k r → Mt k r → Mt k r := fun h n => mulF (mulF (h, Formalism.FourierDecayAlt.B2.invM n), Formalism.FourierDecayAlt.B2.invM h)
  have hgm : Measurable (Function.uncurry g) :=
    meas_mulF.comp ((meas_mulF.comp (measurable_fst.prodMk (hinvm.comp measurable_snd))).prodMk
      (hinvm.comp measurable_fst))
  have hW0 : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by rw [ae_iff]; exact hW.conc
  have hg : ∀ᵐ h ∂μW, μN.map (g h) = μN := by
    filter_upwards [hW0] with h hh
    have e : g h = conjM (Matrix.of h) ∘ Formalism.FourierDecayAlt.B2.invM := rfl
    rw [e, ← Measure.map_map (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.meas_conj _) hinvm, hNi, hNc _ hh]
  have hmp : MeasurePreserving (fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2))
      (μW.prod μN) (μW.prod μN) :=
    MeasurePreserving.skew_product (μb := μW) (μd := μN) ⟨hinvm, hWi⟩ hgm hg
  have hFm : Measurable (fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2)) :=
    (hinvm.comp measurable_fst).prodMk hgm
  have hae : (Formalism.FourierDecayAlt.B2.invM ∘ mulF) =ᵐ[μW.prod μN]
      (mulF ∘ fun p : Mt k r × Mt k r => (Formalism.FourierDecayAlt.B2.invM p.1, g p.1 p.2)) := by
    have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
      rw [ae_iff]
      have es : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} =
          {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
        ext p; simp
      rw [es, Measure.prod_prod]
      have : μW {x : Mt k r | Matrix.of x ∉ UWset k r z} = 0 := hW.conc
      rw [this, zero_mul]
    filter_upwards [h1] with p hp
    have hu : IsUnit (Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det :=
      Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI.det_unit_of_UH hp.1
    have hii : (Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ * Matrix.of p.1 = 1 :=
      Matrix.nonsing_inv_mul _ hu
    show ((Matrix.of p.1 * Matrix.of p.2 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹)
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hii, Matrix.one_mul]
  rw [muS_eq, Measure.map_map hinvm meas_mulF, Measure.map_congr hae, ← Measure.map_map meas_mulF hFm, hmp.map_eq]

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Classical
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

abbrev dG (k r : ℕ) : ℕ := Module.finrank ℝ (Formalism.MainNotions.S.lieE (UH (Hpk k r)))

theorem gVol_mul (k r : ℕ) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    gVol k r (a * s) = a ^ dG k r * gVol k r s := by
  unfold gVol
  rw [Measure.addHaar_ball_mul_of_pos volume _ ha, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem gVol_pos (k r : ℕ) {s : ℝ} (hs : 0 < s) : 0 < gVol k r s := by
  unfold gVol
  exact ENNReal.toReal_pos (Metric.measure_ball_pos _ _ hs).ne' measure_ball_lt_top.ne

theorem rhs_bounds (hW : Sandwich) (k r : ℕ) (μb : Measure (Mt k r))
    (hμb : IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
      Vol k r μb ((1 - ε) * ρ) ≤ rhs k r μb ((wBall k r ρ).indicator 1) ∧
      rhs k r μb ((wBall k r ρ).indicator 1) ≤ Vol k r μb ((1 + ε) * ρ) := by
  obtain ⟨δ, hδ, hW'⟩ := hW k r ε hε0 hε1
  refine ⟨δ, hδ, fun ρ hρ hρδ => ?_⟩
  have hN : ∀ᵐ x ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1), Matrix.of x ∈ Nset k r :=
    ae_iff.2 (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top).2.2.1
  have hB : ∀ᵐ x ∂μb, Matrix.of x ∈ Formalism.FourierDecayAlt.B2.UWb k r := ae_iff.2 hμb.1.2.2.1
  constructor
  · unfold Vol rhs
    refine lintegral_mono fun c => mul_le_mul_of_nonneg_left ?_ (zero_le)
    refine lintegral_mono_ae (hN.mono fun n hn => ?_)
    refine lintegral_mono_ae (hB.mono fun m hm => ?_)
    refine lintegral_mono_ae (hN.mono fun n' hn' => ?_)
    split_ifs with hQ
    · have hx : (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j : Mt k r) ∈
          wBall k r ρ := (hW' ρ hρ hρδ n c m n' hn hm hn').2 hQ
      rw [Set.indicator_apply, if_pos hx, Pi.one_apply]
    · exact zero_le
  · unfold Vol rhs
    refine lintegral_mono fun c => mul_le_mul_of_nonneg_left ?_ (zero_le)
    refine lintegral_mono_ae (hN.mono fun n hn => ?_)
    refine lintegral_mono_ae (hB.mono fun m hm => ?_)
    refine lintegral_mono_ae (hN.mono fun n' hn' => ?_)
    by_cases hx : (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j : Mt k r) ∈
        wBall k r ρ
    · have hQ := (hW' ρ hρ hρδ n c m n' hn hm hn').1 hx
      rw [Set.indicator_apply, if_pos hx, Pi.one_apply, if_pos hQ]
    · rw [Set.indicator_apply, if_neg hx]
      exact zero_le

theorem scale_lim (hV : VolLim) (k r : ℕ) (μb : Measure (Mt k r))
    (hμb : IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ρ : ℝ => (Vol k r μb (a * ρ)).toReal / gVol k r ρ) (𝓝[>] 0)
      (𝓝 (((2 : ℝ) ^ r)⁻¹ * a ^ dG k r)) := by
  have hsc : Tendsto (fun ρ : ℝ => a * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := ((continuous_const_mul a).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact mul_pos ha hρ
  have h1 := ((hV k r μb hμb).comp hsc).mul_const (a ^ dG k r)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  have hg := gVol_pos k r (s := ρ) hρ
  have ha' : a ^ dG k r ≠ 0 := pow_ne_zero _ ha.ne'
  simp only [Function.comp]
  rw [gVol_mul k r ha ρ]
  field_simp

theorem rhsLim_of (hW : Sandwich) (hV : VolLim) : RhsLim := by
  intro k r μb hμb
  set L : ℝ := ((2 : ℝ) ^ r)⁻¹ with hLdef
  have hL : 0 < L := by positivity

  have hfin : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), rhs k r μb ((wBall k r ρ).indicator 1) ≠ ∞ := by
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := 1 / 2) (by norm_num) (by norm_num)
    have h := scale_lim hV k r μb hμb (a := 1 + 1 / 2) (by norm_num)
    have hpos := (tendsto_order.1 h).1 0 (by positivity)
    filter_upwards [hpos, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h1 h2 h3
    have hg := gVol_pos k r (s := ρ) h2
    have h4 : 0 < (Vol k r μb ((1 + 1 / 2) * ρ)).toReal := by
      by_contra hc
      replace hc := not_lt.1 hc
      have : (Vol k r μb ((1 + 1 / 2) * ρ)).toReal / gVol k r ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hg.le
      linarith
    exact ne_top_of_le_ne_top (ENNReal.toReal_pos_iff.1 h4).2.ne (hb ρ h2 h3).2
  rw [tendsto_order]
  constructor
  · intro a haL
    have hc : Tendsto (fun ε : ℝ => L * (1 - ε) ^ dG k r) (𝓝[>] 0) (𝓝 L) := by
      have : Continuous (fun ε : ℝ => L * (1 - ε) ^ dG k r) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, ⟨h1, h2⟩, h0⟩ :=
      (((tendsto_order.1 hc).1 a haL).and ((eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds)
        |>.and self_mem_nhdsWithin).exists
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := ε) h0 h2
    have h := scale_lim hV k r μb hμb (a := 1 - ε) (by linarith)
    have hlo := (tendsto_order.1 h).1 a (by simpa [mul_comm] using h1)
    filter_upwards [hlo, hfin, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h3 h4 h5 h6
    have hg := gVol_pos k r (s := ρ) h5
    refine lt_of_lt_of_le h3 (div_le_div_of_nonneg_right ?_ hg.le)
    exact ENNReal.toReal_mono h4 (hb ρ h5 h6).1
  · intro b hbL
    have hc : Tendsto (fun ε : ℝ => L * (1 + ε) ^ dG k r) (𝓝[>] 0) (𝓝 L) := by
      have : Continuous (fun ε : ℝ => L * (1 + ε) ^ dG k r) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, ⟨h1, h2⟩, h0⟩ :=
      (((tendsto_order.1 hc).2 b hbL).and ((eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds)
        |>.and self_mem_nhdsWithin).exists
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := ε) h0 h2
    have h := scale_lim hV k r μb hμb (a := 1 + ε) (by linarith)
    have hup := (tendsto_order.1 h).2 b (by simpa [mul_comm] using h1)
    have hpos := (tendsto_order.1 h).1 0 (by positivity)
    filter_upwards [hup, hpos, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h3 h3' h5 h6
    have hg := gVol_pos k r (s := ρ) h5
    have h4 : 0 < (Vol k r μb ((1 + ε) * ρ)).toReal := by
      by_contra hc
      replace hc := not_lt.1 hc
      have : (Vol k r μb ((1 + ε) * ρ)).toReal / gVol k r ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hg.le
      linarith
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ hg.le) h3
    exact ENNReal.toReal_mono (ENNReal.toReal_pos_iff.1 h4).2.ne (hb ρ h5 h6).2

end Formalism.L2.SG.Pf.BH
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.IdMeet

theorem volColC_holds : VolColC :=
  volColC_of noinfEqC_holds nocolEqC_holds gcCountC_holds fundMeasEqC_holds indexVolC_holds indexTransferC_holds
    conjUC_holds gcFundC_holds gcConjC_holds hinfConjC_holds

theorem idMeetOneC_holds : IdMeetOneC := idMeetOneC_of idMeetKeyC_holds

theorem idMeetPhaseC_holds : IdMeetPhaseC := idMeetPhaseC_of idMeetKeyC_holds

theorem idMeetVolC_holds : IdMeetVolC := idMeetVolC_of idMeetKeyC_holds volColC_holds

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.Pf.Slab

theorem neatKu_full : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u : D.what₂.Word), NeatKu X u Y.hK :=
  fun _ X Y u => neatKu_of_gamUnipKu X u Y.hK (latOfLattice_holds X u) (gamUnipKu_holds X u Y.hK)

theorem rInvC_holds : RInvC := rInvC_of nilradical_conj_level'

theorem ooLintSumC_holds_slab (hMaj : MajPtC) (hCnt : CountC) : OOLintSumC :=
  ooLintSumC_of_parts Formalism.L2.SG.Pf.RegroupPf.slabCoverC_holds hMaj rInvC_holds hCnt neatKu_full

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

def Mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def uH (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq] at *
    rw [adjH_add, show adjH X + adjH Y + (X + Y) = (adjH X + X) + (adjH Y + Y) by abel, hX, hY, add_zero]
  zero_mem' := by simp [adjH]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_ofPred_eq] at *
    rw [← Complex.coe_smul, adjH_smul, Complex.star_def, Complex.conj_ofReal, ← smul_add, hX, smul_zero]

def uWb (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0 ∧ ∀ i j, ¬ (Mid k r i ∧ Mid k r j) → X i j = 0}
  add_mem' := by
    intro X Y hX hY
    refine ⟨(uH k r).add_mem hX.1 hY.1, fun i j h => ?_⟩
    simp [hX.2 i j h, hY.2 i j h]
  zero_mem' := ⟨(uH k r).zero_mem, fun i j _ => rfl⟩
  smul_mem' := by
    intro c X hX
    refine ⟨(uH k r).smul_mem c hX.1, fun i j h => ?_⟩
    simp [hX.2 i j h]

def tv (k r : ℕ) (c : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if h : i.val < r then c ⟨i.val, h⟩
  else if h2 : i.val ≤ r + k then 1
  else (star (c ⟨2 * r + k - i.val, by have := i.isLt; omega⟩))⁻¹

def tM (k r : ℕ) (c : Fin r → ℂ) : Mat k r := Matrix.diagonal (tv k r c)

def dv (k r : ℕ) (x : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if h : i.val < r then x ⟨i.val, h⟩
  else if h2 : i.val ≤ r + k then 0
  else -star (x ⟨2 * r + k - i.val, by have := i.isLt; omega⟩)

def tD (k r : ℕ) (x : Fin r → ℂ) : Mat k r := Matrix.diagonal (dv k r x)

def Phi (k r : ℕ) (X : Mat k r) (x : Fin r → ℂ) (Z X' : Mat k r) : Mat k r :=
  w0B k r * NormedSpace.exp X * w0B k r * tM k r (1 + x) * NormedSpace.exp Z * NormedSpace.exp (-X')

def LmL (k r : ℕ) : (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) →ₗ[ℝ] Mat k r where
  toFun p := w0B k r * p.1 * w0B k r + tD k r p.2.1 + p.2.2.1 - p.2.2.2
  map_add' p q := by
    have : tD k r (p.2.1 + q.2.1) = tD k r p.2.1 + tD k r q.2.1 := by
      unfold tD; rw [Matrix.diagonal_add]; congr 1; funext i; unfold dv
      split_ifs <;> simp [star_add] <;> ring
    simp only [Prod.fst_add, Prod.snd_add, this, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c p := by
    have : tD k r (c • p.2.1) = c • tD k r p.2.1 := by
      have hd : ∀ i, dv k r (c • p.2.1) i = (c : ℂ) * dv k r p.2.1 i := by
        intro i; unfold dv; split_ifs <;> simp [Complex.real_smul]
      unfold tD; ext i j; simp only [Matrix.diagonal_apply, Matrix.smul_apply, hd]
      split_ifs <;> simp [Complex.real_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, this, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, smul_add,
      smul_sub]

def Lm (k r : ℕ) : (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (LmL k r)

def Vs (k r : ℕ) : Submodule ℝ (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) :=
  (lieNS k r).prod ((⊤ : Submodule ℝ (Fin r → ℂ)).prod ((uWb k r).prod (lieNS k r)))

def LieG : Prop := ∀ k r : ℕ, Formalism.MainNotions.S.lieE (UH (Hpk k r)) = (uH k r).map RL

def LieWb : Prop := ∀ k r : ℕ, (∀ Z ∈ uWb k r, NormedSpace.exp Z ∈ Formalism.FourierDecayAlt.B2.UWb k r) ∧
  Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r) = (uWb k r).map RL

def LIso : Prop := ∀ k r : ℕ, (∀ v ∈ Vs k r, Lm k r v ∈ uH k r) ∧ (∀ Y ∈ uH k r, ∃ v ∈ Vs k r, Lm k r v = Y) ∧
  ∀ v ∈ Vs k r, ‖RL (Lm k r v)‖ ^ 2 = ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2

end Formalism.L2.SG.Pf.BH.Sw
end
end
