module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle037
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle019
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle005
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle007
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle041
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.IsHaarOnUWsetOfIsHaarOnOfUnivEqOne
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle040
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem pairAmpConst_holds (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y)
    (hOI : ∀ w w', OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w')) : PairAmpConst Y :=
  pairAmpConst_of (fun w => Formalism.L2.SG.Closed.NeatKu_holds X w Y.hK) hRF Formalism.L2.SG.Pf.iotaRepC_holds
    Formalism.L2.SG.Pf.ampRepNC_holds (fun _ X => chi_n_bilinear X) hOI

variable {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF))

theorem pvalForm_exists_rf (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y)
    (hOI : ∀ w w', OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w')) (hN : FibreCountEq hF) :
    ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists' W hI (AmpCov_holds Y) (pairAmpConst_holds hRF hOI) hN

theorem rowFree_holds : Formalism.L2.SG.Pf.FibreCounting.RowFree Y :=
  Formalism.L2.SG.Pf.Act.rowFree_of (fun w => Formalism.L2.SG.Closed.NeatKu_holds X w Y.hK) Formalism.L2.SG.Pf.iotaRepC_holds

theorem pvalForm_exists_oi (hOI : ∀ w w', OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w'))
    (hN : FibreCountEq hF) : ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists_rf W hI rowFree_holds hOI hN

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (v : InfinitePlace X.B.I.F)

theorem map_span_G (g : Formalism.REAL.UJ (X.B.I.ε v)) (Fp : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ)
    (S : Set (Fin (D.R.rS + 1))) (y : Fin X.B.I.n → ℂ)
    (hy : y ∈ Submodule.span ℂ ((fun b => uMat g *ᵥ Fp b) '' S)) :
    uMat g⁻¹ *ᵥ y ∈ Submodule.span ℂ (Fp '' S) := by
  have e : Submodule.span ℂ ((fun b => uMat g *ᵥ Fp b) '' S) =
      (Submodule.span ℂ (Fp '' S)).map (Matrix.mulVecLin (uMat g)) := by
    rw [Submodule.map_span, Set.image_image]
    rfl
  rw [e] at hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  have h1 : uMat g⁻¹ * uMat g = 1 := by simp [uMat]
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  exact hz

section Main

variable (hw : OkPt X u u' w)

def yU (c : FreeE w → ℂ) (hw : OkPt X u u' w) : Formalism.REAL.UJ (X.B.I.ε v) :=
  mkUJ _ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c)) (yM_unit X u u' w v hw c)

theorem T_sub (c : FreeE w → ℂ) (x : Fin X.B.I.n → ℂ) :
    (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) - 1) *ᵥ x =
      uMat (gamW X u u' w v)⁻¹ *ᵥ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ
        (uMat (gamW X u u' w v) *ᵥ x) - uMat (gamW X u u' w v) *ᵥ x) := by
  have hc : uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) =
      uMat (gamW X u u' w v)⁻¹ * uMat (yU X u u' w v c hw) * uMat (gamW X u u' w v) := rfl
  have hy : uMat (yU X u u' w v c hw) = Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) := rfl
  have h1 : uMat (gamW X u u' w v)⁻¹ * uMat (gamW X u u' w v) = 1 := by simp [uMat]
  rw [hc, hy, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem G_eq (b : Fin (D.R.rS + 1)) : Gw X u u' w v b = uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v b := rfl

include hw in
theorem TG_comb (c : FreeE w → ℂ) (b : Fin (D.R.rS + 1)) :
    uMat (gamW X u u' w v)⁻¹ *ᵥ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Gw X u u' w v b -
      Gw X u u' w v b) = ∑ b', (Cw w c - 1) b' b • frm X u' D.host.rdE v b' := by
  have h1 : uMat (gamW X u u' w v)⁻¹ * uMat (gamW X u u' w v) = 1 := by simp [uMat]
  have hA : ∀ x, uMat (gamW X u u' w v)⁻¹ *ᵥ (uMat (gamW X u u' w v) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [yM_G X u u' w v hw c b]
  simp only [G_eq, Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_smul, hA, Matrix.sub_apply, sub_smul,
    Finset.sum_sub_distrib, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

include hw in
theorem inN_u' (c : FreeE w → ℂ) :
    InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))
      (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v)) := by
  have hC := isUB_Cw w c
  refine ⟨⟨fun a => ?_, ?_⟩, fun x hx => ?_⟩
  · show (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) - 1) *ᵥ rv X.B.I v (X.eR a) ∈ _
    rw [T_sub, e_eq X u' v a, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub, Matrix.mulVec_smul,
      ← G_eq, TG_comb X u u' w v hw c]
    exact Submodule.smul_mem _ _ (span_frm_le X u' v a.1 a.2.le (comb_mem X u' v hC a.castSucc))
  · rw [T_sub, ← frm_last X u' v, ← G_eq, TG_comb X u u' w v hw c]
    exact span_frm_le X u' v D.R.rS le_rfl (comb_mem X u' v hC (Fin.last D.R.rS))
  · rw [T_sub]
    have hperp := Yc_perpG _ _ _ (Tw u) (Tw u') (piW w) (blkW w) (gram_frm X v u _) (hGG_w X u u' w v) (piW_invol w)
      (piW_blk w) (piW_anti w) (hZ_w X u u' w hw v) (hgap_w X u u' w v hw) hC (uMat (gamW X u u' w v) *ᵥ x)
      (fun b hb => by
        obtain ⟨b0, rfl⟩ : ∃ b0 : Fin D.R.rS, b = b0.castSucc := ⟨⟨b.1, Fin.val_lt_last hb⟩, Fin.ext rfl⟩
        rw [G_eq, Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj (gamW X u u' w v), Matrix.mulVec_mulVec,
          Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul', Matrix.one_mulVec, frm_castSucc, hJs_l, hx b0, mul_zero])
    have h2 := map_span_G X v (gamW X u u' w v) (frm X u' D.host.rdE v) _ _ hperp
    rw [lt_last_set] at h2
    exact span_frm_le X u' v D.R.rS le_rfl h2

end Main

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section

noncomputable section

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

theorem torS_eq (δ : ℝ) :
    Formalism.L2.SG.LocWSOf.torS (-Complex.I * (δ : ℂ)) k r = (Complex.I ^ r)⁻¹ • (tT k r * dM k r δ 1) := by
  unfold Formalism.L2.SG.LocWSOf.torS tT dM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  by_cases h1 : i.val < r
  · simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, if_true, one_mul]
    obtain ⟨n, hn⟩ : ∃ n, r = i.val + n := ⟨r - i.val, by omega⟩
    have hn' : r - i.val = n := by omega
    have hIr : Complex.I ^ r = Complex.I ^ i.val * Complex.I ^ n := by rw [← pow_add, ← hn]
    rw [hn', hIr, ← Complex.inv_I]
    push_cast
    field_simp
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hI0)]
  · by_cases h2 : r + k < i.val
    · have h2' : ¬ (i.val ≤ r + k) := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, h2, h2', if_true, if_false, one_mul]
      obtain ⟨n, hn⟩ : ∃ n, r = (2 * r + k - i.val) + n := ⟨r - (2 * r + k - i.val), by omega⟩
      have hn' : r - (2 * r + k - i.val) = n := by omega
      have hIr : Complex.I ^ r = Complex.I ^ (2 * r + k - i.val) * Complex.I ^ n := by rw [← pow_add, ← hn]
      rw [hn', hIr]
      simp only [star_pow, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal, neg_neg]
      push_cast
      rw [mul_pow]
      field_simp
    · have h2' : i.val ≤ r + k := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, h1, h2, h2', if_true, if_false]
      push_cast
      rw [mul_one, inv_mul_cancel₀ (pow_ne_zero _ hI0)]

theorem torS_inv_eq (δ : ℝ) (hδ : 0 < δ) :
    Formalism.L2.SG.LocWSOf.torS (-Complex.I * (δ : ℂ))⁻¹ k r = (Complex.I ^ r) • (dMi k r δ 1 * tTi k r) := by
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  unfold Formalism.L2.SG.LocWSOf.torS tTi dMi
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h1 : i.val < r
  · simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, if_true, one_mul]
    obtain ⟨n, hn⟩ : ∃ n, r = i.val + n := ⟨r - i.val, by omega⟩
    have hn' : r - i.val = n := by omega
    have hIr : Complex.I ^ r = Complex.I ^ i.val * Complex.I ^ n := by rw [← pow_add, ← hn]
    rw [hn', hIr, star_pow, Complex.star_def, Complex.conj_I, ← Complex.inv_I]
    push_cast
    field_simp
    rw [div_pow, div_pow, one_pow]
    field_simp
  · by_cases h2 : r + k < i.val
    · have h2' : ¬ (i.val ≤ r + k) := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, h2, h2', if_true, if_false, one_mul]
      obtain ⟨n, hn⟩ : ∃ n, r = (2 * r + k - i.val) + n := ⟨r - (2 * r + k - i.val), by omega⟩
      have hn' : r - (2 * r + k - i.val) = n := by omega
      have hIr : Complex.I ^ r = Complex.I ^ (2 * r + k - i.val) * Complex.I ^ n := by rw [← pow_add, ← hn]
      rw [hn', hIr]
      simp only [star_pow, star_inv₀, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
        neg_neg, inv_inv]
      rw [← Complex.inv_I]
      push_cast
      rw [inv_pow]
      field_simp
      rw [div_pow, one_pow, mul_pow]
      field_simp
    · have h2' : i.val ≤ r + k := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, h1, h2, h2', if_true, if_false]
      push_cast
      rw [star_pow, Complex.star_def, Complex.conj_I, ← Complex.inv_I]
      field_simp
      rw [div_pow, one_pow]
      field_simp

theorem nLeft_holds : Formalism.MainNotions.MeasFS.NLeft := fun k r κ h0 h1 a ha =>
  (Formalism.MainNotions.BridgeCSB.haarLieN k r κ h0 h1).2.2.2 a ha

theorem muN_eq_haarLie (k r : ℕ) :
    ∃ κ₀ : ENNReal, κ₀ ≠ 0 ∧ κ₀ ≠ ⊤ ∧ Formalism.FourierDecayAlt.D.muN k r = haarLie (Nset k r) κ₀ := by
  have hH := Formalism.MainNotions.MeasFS.haar_lie_measure_on_nilpotent (k := k) (r := r) nLeft_holds 1 one_ne_zero ENNReal.one_ne_top
  have hM := Formalism.FourierDecayAlt.Final.d_muNHaar k r
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (Nset k r) _ _ (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hH
    hM.conc hM.left hM.finite_compact
  refine ⟨(c : ENNReal), fun h => hM.ne_zero ?_, ENNReal.coe_ne_top, ?_⟩
  · rw [hc, ENNReal.coe_eq_zero.mp h, zero_smul]
  · rw [hc, show ((c : ENNReal)) = (c : ENNReal) * 1 from (mul_one _).symm, haarLie_smul, ENNReal.smul_def]

def kaB (D : Formalism.BasicNotions.D7) : ℝ := D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))

theorem kaB_pos (D : Formalism.BasicNotions.D7) : 0 < kaB D := by
  have hka : 0 < D.host.ka := by
    have hrd : 0 < D.host.rdE := by
      unfold Formalism.BasicNotions.Host.rdE
      exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  exact div_pos hka (mul_pos hg0 hg1)

theorem muT_eq (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.LocWSOf.muT D = -Complex.I * (((kaB D)⁻¹ : ℝ) : ℂ) := by
  have hka : 0 < D.host.ka := by
    have hrd : 0 < D.host.rdE := by
      unfold Formalism.BasicNotions.Host.rdE
      exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hkac : (D.host.ka : ℂ) ≠ 0 := by exact_mod_cast hka.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  unfold Formalism.L2.SG.LocWSOf.muT Formalism.L2.SG.LocWSOf.cfS Formalism.L2.SG.LocWSOf.frS kaB
  push_cast
  field_simp

theorem torS_muT (D : Formalism.BasicNotions.D7) (k r : ℕ) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r = (Complex.I ^ r)⁻¹ • (tT k r * dM k r (kaB D)⁻¹ 1) := by
  rw [muT_eq, torS_eq]

theorem torS_muT_inv (D : Formalism.BasicNotions.D7) (k r : ℕ) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r = (Complex.I ^ r) • (dMi k r (kaB D)⁻¹ 1 * tTi k r) := by
  rw [muT_eq, torS_inv_eq _ (inv_pos.mpr (kaB_pos D))]

theorem torS_conj (D : Formalism.BasicNotions.D7) (k r : ℕ) (M : Mx k r) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r * M * Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r =
      gStd (kaB D) M := by
  rw [torS_muT, torS_muT_inv, gStd]
  have hI : (Complex.I ^ r) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hI, mul_inv_cancel₀ hI, one_smul]
  simp only [cj, Matrix.mul_assoc]

theorem torS_conjI (D : Formalism.BasicNotions.D7) (k r : ℕ) (M : Mx k r) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r * M * Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r =
      tT k r * cjI k r (kaB D)⁻¹ 1 M * tTi k r := by
  rw [torS_muT, torS_muT_inv]
  have hI : (Complex.I ^ r) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hI, mul_inv_cancel₀ hI, one_smul]
  simp only [cjI, Matrix.mul_assoc]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section

noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.ThresholdLevels

variable (C0 : ℝ)

theorem thrRow_holds {𝒞 : FamClass} : ∀ CA : ℝ, 1 ≤ CA → Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
    AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
      ∀ u u' : (Fm.D x i).what₂.Word, u ≠ u' → Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces CA (Fm.D x i) u u' := by
  intro CA hCA

  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 40⟩, fun Fm CH _ hL => ?_⟩⟩
  have h40 : (40 : ℝ) ≤ sCl Fm := (le_sC'_sCl hL).2
  refine ⟨0, fun x _ i hH u u' _ => ?_⟩
  obtain ⟨hD, hHy, _⟩ := hH
  exact ThresholdOrder.thrAt_of_pos CA (Fm.D x i) u u' (ThresholdAtPlaceBounds.thrSet_pos_at hD hHy h40 _ hCA u u')

end Formalism.L2.SG.Pf.ThresholdLevels
end
end
