module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTFr
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle046
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictLat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOf

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def GNonNeg (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf), IsPtRep X u u' w γ → ∀ v, 0 ≤ GX X u u' D.host.rdE γ v

theorem lZero_of (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hG : GNonNeg X u u') :
    LZero X u u' sc i0 i0' FdN FdN' νq := by
  intro p w hp hng
  unfold VtPt
  rw [hp]
  simp only
  by_cases hrep : ∃ γ, IsPtRep X u u' w γ
  · have h1 : ¬ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v := fun h => hng ⟨hrep, h⟩
    push_neg at h1
    obtain ⟨v, hv⟩ := h1
    have hrepw : IsPtRep X u u' w (gamW X u u' w) := by
      unfold gamW; rw [dite_eq_left hrep]; exact hrep.choose_spec
    have h0 : GX X u u' D.host.rdE (gamW X u u' w) v = 0 := le_antisymm hv (hG w _ hrepw v)
    have hk := Formalism.MainNotions.BridgeLemma.five_le_k D
    have hn : nW X u u' w = 0 := by
      unfold nW
      refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
      rw [h0, zero_pow (by omega), zero_mul]
    rw [hn, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
  · have hV : unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq w = 0 := by
      unfold unscaledOperatorAtPointRepresentative; rw [if_neg hrep]
    rw [hV, map_zero, smul_zero]

theorem gX_nonneg {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ) (u u' : D.what₂.Word) (γ : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) : 0 ≤ GX X u u' D.host.rdE γ v := by
  obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := Formalism.L2.SG.Pf.CarrierT.isTransp_Qcs X C v
  set Qm := Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)
  set Qim := Formalism.L2.SG.LocWSOf.Qics C (X.pl v)
  set gg : ℕ := D.host.g 0 * D.host.g 1
  have hTr : Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v) Qm Qim (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ1, hQ2, hQ3, fun a => (hQ4 a a rfl).1, fun a => (hQ4 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v) Qm Qim (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ1, hQ2, hQ3, fun a => (hQ4 a a rfl).1, fun a => (hQ4 a a rfl).2⟩
  have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
  have hz := Formalism.L2.SG.Pf.BaseOf.zc_spec X C u v
  have hz' := Formalism.L2.SG.Pf.BaseOf.zc_spec X C u' v
  have hgv := Bridge.delta_GV hTr (Formalism.L2.SG.Pf.Carrier.uMat_unitary (γ v))
  have hG := Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS _ _ hz.1 hz'.1 (Formalism.L2.SG.Pf.BaseOf.zc_pos X C u v)
    (Formalism.L2.SG.Pf.BaseOf.zc_pos X C u' v) _ hgv
  have h1 := Bridge.zhat_cs hTr hTr' (sc := D.host.rdE) hrd.ne' (Formalism.MainNotions.S.uMat (γ v))
  set Zr := Formalism.L2.SG.RealObj.Zhat (X.B.I.ε v)
    (famSc D.host.rdE (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v).e (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v).z)
    (famSc D.host.rdE (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v).e (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v).z)
    (Formalism.MainNotions.S.uMat (γ v)) with hZr
  have h1' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.zc X C u v) (Formalism.L2.SG.Pf.BaseOf.zc X C u' v)
      (Qim * Formalism.MainNotions.S.uMat (γ v) * Qm) =
      Matrix.diagonal (fun a => star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a)) * Zr *
        Matrix.diagonal (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE) := h1
  unfold Formalism.QuantumDeterminants.Gf Formalism.QuantumDeterminants.Dmin at hG
  rw [hz.2, hz'.2, h1'] at hG
  have hgg0 : (0 : ℝ) < gg := by
    show (0 : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)
    exact_mod_cast Nat.mul_pos (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1 (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2
  set κ : ℂ := -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ) with hκ
  have hc : ∀ a : Fin D.R.rS, cTor (gg : ℝ) D.R.rS a = κ ^ (D.R.rS - a.val) := by
    intro a; unfold cTor; congr 1; rw [hκ]; push_cast; field_simp
  have hκ0 : κ ≠ 0 := by
    rw [hκ]; refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    exact_mod_cast (div_pos hgg0 (by positivity)).ne'
  have hlamne : ∀ a : Fin (D.R.rS + 1), Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a ≠ 0 := by
    intro a h0
    have := (Bridge.cS_lam hc hrd.ne' a).1
    rw [h0, mul_zero] at this
    exact pow_ne_zero _ hκ0 this.symm
  have hlast : Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE (Fin.last D.R.rS) = 1 := by
    have := (Bridge.cS_lam hc hrd.ne' (Fin.last D.R.rS)).1
    have hcl : Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.last D.R.rS) = 1 := by
      simp [Formalism.L2.SG.Pf.CarrierTop.cS]
    rw [hcl, one_mul] at this
    rw [this]; simp
  have hD1 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ,
      (M.submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt))).det = RealObj.Dl M (D.R.rS + 1) :=
    fun M => by unfold RealObj.Dl; rw [dite_eq_left le_rfl]
  have hD2 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ,
      (M.submatrix (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt))).det = RealObj.Dl M D.R.rS :=
    fun M => by unfold RealObj.Dl; rw [dite_eq_left (Nat.le_succ _)]
  rw [hD1, hD2, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hG
  have hGd := Bridge.G_diag D.R.rS Zr
    (fun a => star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a))
    (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE) (Tr D u * Tr D u') (by rw [hlast]; simp)
  rw [hGd] at hG
  have hne1 : (∏ i : Fin D.R.rS, star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE
      (Fin.castLE (Nat.le_succ D.R.rS) i))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => star_ne_zero.mpr (hlamne _)
  have hne2 : (∏ i : Fin D.R.rS, Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE
      (Fin.castLE (Nat.le_succ D.R.rS) i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hlamne _
  have hpos := pow_pos (mul_pos (norm_pos_iff.mpr hne1) (norm_pos_iff.mpr hne2)) 2
  have := (mul_nonneg_iff_of_pos_left hpos).mp hG
  unfold GX Gv
  exact this

theorem lZero_of_choice {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : LZero X u u' sc i0 i0' FdN FdN' νq :=
  lZero_of X u u' sc i0 i0' FdN FdN' νq fun _ γ _ v => gX_nonneg X C u u' γ v

end Formalism.L2.SG.Pf.Carrier.CarPinVt
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Finset
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx
  Formalism.L2.SG.Pf.AllRowsKpp Formalism.MainNotions.ArithmeticCylinders

variable {D : D7} (X : HidaSetting D)

def argC (x : X.B.I.Gf) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a)) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0

theorem quadratic_character_eq_additive (x : X.B.I.Gf) : X.chi2 x = X.psiEf (divN X.B.I X.B.g (argC X x)) := rfl

theorem argC_int {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) : argC X x ∈ IntAf X.B.I.F X.B.I.E := by
  unfold argC
  refine add_mem (sum_mem fun a _ => ?_) (sum_mem fun i _ => ?_)
  · refine dual_hat_integral X.B.I _ (X.vectorsInLattice.1 a).2 _ (K_mv X.B.I hx ?_)
    unfold nxt; split_ifs
    · exact (X.vectorsInLattice.1 _).1
    · exact X.vectorsInLattice.2.1
  · split_ifs
    · exact dual_hat_integral X.B.I _ (X.vectorsInLattice.2.2 i).2 _ (K_mv X.B.I hx (X.vectorsInLattice.2.2 _).1)
    · exact zero_mem _

theorem sg_swap (x : X.B.I.Gf) (u v : VA X.B.I) :
    sg X.B.I (hhat X.B.I u (X.B.I.fmat x *ᵥ v)) = hhat X.B.I v (X.B.I.fmat x⁻¹ *ᵥ u) := by
  rw [hhat_conj]
  have := hhat_fmat X.B.I x v (X.B.I.fmat x⁻¹ *ᵥ u)
  rw [Matrix.mulVec_mulVec, ← fmat_mul, mul_inv_cancel, fmat_one, Matrix.one_mulVec] at this
  exact this

variable {w : HeightOneSpectrum (𝓞 X.B.I.E)} {p : ℕ}

def tW (ob : Bool) (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)) : ZMod p :=
  (∑ a : Fin D.R.rS, if h : a.1 + 1 < D.R.rS then N (xI (hrD D) a) (xI (hrD D) ⟨a.1 + 1, h⟩)
      else N (xI (hrD D) a) (zI (hrD D))) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then (if ob then N (wI (hrD D) i) (wI (hrD D) ⟨i.1 + 1, h⟩) else 0) else 0

def tWc (ob : Bool) (N' : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)) : ZMod p :=
  (∑ a : Fin D.R.rS, if h : a.1 + 1 < D.R.rS then N' (yI (hrD D) (rv ⟨a.1 + 1, h⟩)) (yI (hrD D) (rv a))
      else -N' (zI (hrD D)) (yI (hrD D) (rv a))) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then
      (if ob then 0 else N' (wI (hrD D) (rv ⟨i.1 + 1, h⟩)) (wI (hrD D) (rv i))) else 0

theorem bw_Lq (hew : X.ew ∈ Wq X.B.I w) (i : Fin D.R.k) : X.bw i ∈ Lq X.B.I w := by
  rw [X.bw_w i]; exact Wq_smul hew (X.vectorsInLattice.2.2 i).1

theorem bwd_Lq (hsew : sg X.B.I X.ew ∈ Wq X.B.I w) (i : Fin D.R.k) : X.bwd i ∈ Lq X.B.I w := by
  rw [X.bwd_w i]; exact Wq_smul hsew (X.vectorsInLattice.2.2 i).2

theorem congC (ob : Bool) (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset)
    {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hN : ∀ i j, CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x *ᵥ fr X ob j)) (N i j)) :
    CongW (w := w) p (argC X x) (tW (D := D) ob N) := by
  unfold argC tW
  refine congW_add (congW_sum _ fun a _ => ?_) (congW_sum _ fun i _ => ?_)
  · unfold nxt
    split_ifs with h
    · have := hN (xI (hrD D) a) (xI (hrD D) ⟨a.1 + 1, h⟩)
      rwa [dual_frame_isotropic, frame_isotropic] at this
    · have := hN (xI (hrD D) a) (zI (hrD D))
      rwa [dual_frame_isotropic, frame_anisotropic] at this
  · split_ifs with h hob
    · have := hN (wI (hrD D) i) (wI (hrD D) ⟨i.1 + 1, h⟩)
      rw [hob] at this
      rwa [frd_wt, fr_wt] at this
    · refine congW_zero_of (hhat_Lq_right (X.vectorsInLattice.2.2 i).2 (stab_w X.B.I w hx (bw_Lq X ?_ _)))
      simp only [hob, Bool.false_eq_true, if_false, sub_zero] at hew
      exact hew
    · exact congW_zero_of (zero_mem _)

theorem congW_of_sg {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {m : ZMod p} (h : CongW (w := w) p (sg X.B.I t) m) :
    CongW (w := wc X.B.I w) p t m := by
  have := (congW_sg (I := X.B.I) (w := w) (t := sg X.B.I t) (m := m)).2 h
  rwa [sg_sg] at this

theorem congCc (ob : Bool) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w) {x : X.B.I.Gf}
    (hx : x ∈ X.B.I.Kset) {N' : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hN' : ∀ i j, CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x⁻¹ *ᵥ fr X ob j)) (N' i j)) :
    CongW (w := wc X.B.I w) p (argC X x) (tWc (D := D) ob N') := by
  refine congW_of_sg X ?_
  unfold argC tWc

  rw [map_add (f := _), map_sum, map_sum]
  refine congW_add (congW_sum _ fun a _ => ?_) (congW_sum _ fun i _ => ?_)
  · unfold nxt
    split_ifs with h
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      have := hN' (yI (hrD D) (rv ⟨a.1 + 1, h⟩)) (yI (hrD D) (rv a))
      rwa [frd_y, fr_y, rv_rv, rv_rv] at this
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      have := congW_neg (hN' (zI (hrD D)) (yI (hrD D) (rv a)))
      rwa [dual_frame_anisotropic, fr_y, rv_rv, hhat_neg_left, neg_neg] at this
  · split_ifs with h hob
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      refine congW_zero_of (hhat_Lq_right (X.vectorsInLattice.2.2 _).1 (stab_w X.B.I w (K_inv X.B.I hx) (bwd_Lq X ?_ i)))
      simp only [hob, if_true, sub_zero] at hsew
      exact hsew
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      have := hN' (wI (hrD D) (rv ⟨i.1 + 1, h⟩)) (wI (hrD D) (rv i))
      simp only [hob, Bool.false_eq_true] at this ⊢
      rwa [frd_wf, fr_wf, rv_rv, rv_rv] at this
    · rw [map_zero]; exact congW_zero_of (zero_mem _)

theorem entN_eq {r : ℕ} (M : Matrix (Fin r) (Fin r) (ZMod p)) (i j : Fin r) {a b : ℕ} (ha : i.1 = a) (hb : j.1 = b) :
    M i j = entN M a b := by
  subst ha hb
  unfold entN
  rw [dite_eq_left ⟨i.2, j.2⟩]

theorem sum_eq (ob : Bool) {N N' : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hinv : ∀ i, i + 1 < D.R.r → entN N' i (i + 1) = -entN N i (i + 1)) :
    tW (D := D) ob N + tWc (D := D) ob N' = phiJ D.R.k D.R.rS (dM D.R.rS D.R.k ob * N * dM D.R.rS D.R.k ob) := by
  have hr := hrD D
  rw [phi_key hr ob hinv]
  unfold tW tWc
  have e1 : ∑ a : Fin D.R.rS, ((if h : a.1 + 1 < D.R.rS then N (xI hr a) (xI hr ⟨a.1 + 1, h⟩)
        else N (xI hr a) (zI hr)) + (if h : a.1 + 1 < D.R.rS then N' (yI hr (rv ⟨a.1 + 1, h⟩)) (yI hr (rv a))
        else -N' (zI hr) (yI hr (rv a)))) =
      ∑ a ∈ range D.R.rS, (if a + 1 < D.R.rS then entN N a (a + 1) +
        entN N' (D.R.rS + D.R.k + 1 + (D.R.rS - 2 - a)) (D.R.rS + D.R.k + 1 + (D.R.rS - 1 - a))
        else entN N a (D.R.rS + D.R.k) - entN N' (D.R.rS + D.R.k) (D.R.rS + D.R.k + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · have q1 : N (xI hr a) (xI hr ⟨a.1 + 1, h⟩) = entN N a.1 (a.1 + 1) := entN_eq N _ _ rfl rfl
      have q2 : N' (yI hr (rv ⟨a.1 + 1, h⟩)) (yI hr (rv a)) =
          entN N' (D.R.rS + D.R.k + 1 + (D.R.rS - 2 - a.1)) (D.R.rS + D.R.k + 1 + (D.R.rS - 1 - a.1)) :=
        entN_eq N' _ _ (by dsimp [yI, wI, rv]; omega) (by rfl)
      rw [q1, q2]
    · have q1 : N (xI hr a) (zI hr) = entN N a.1 (D.R.rS + D.R.k) := entN_eq N _ _ rfl rfl
      have q2 : N' (zI hr) (yI hr (rv a)) = entN N' (D.R.rS + D.R.k) (D.R.rS + D.R.k + 1) :=
        entN_eq N' _ _ rfl (by dsimp [yI, wI, rv]; omega)
      rw [q1, q2]; ring
  have e2 : ∑ i : Fin D.R.k, ((if h : i.1 + 1 < D.R.k then (if ob then N (wI hr i) (wI hr ⟨i.1 + 1, h⟩) else 0) else 0) +
        (if h : i.1 + 1 < D.R.k then (if ob then 0 else N' (wI hr (rv ⟨i.1 + 1, h⟩)) (wI hr (rv i))) else 0)) =
      ∑ i ∈ range D.R.k, (if i + 1 < D.R.k then (if ob then entN N (D.R.rS + i) (D.R.rS + i + 1)
        else entN N' (D.R.rS + (D.R.k - 2 - i)) (D.R.rS + (D.R.k - 1 - i))) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h hob
    · have q1 : N (wI hr i) (wI hr ⟨i.1 + 1, h⟩) = entN N (D.R.rS + i.1) (D.R.rS + i.1 + 1) :=
        entN_eq N _ _ rfl (by dsimp [yI, wI, rv]; omega)
      rw [q1, add_zero]
    · have q1 : N' (wI hr (rv ⟨i.1 + 1, h⟩)) (wI hr (rv i)) =
          entN N' (D.R.rS + (D.R.k - 2 - i.1)) (D.R.rS + (D.R.k - 1 - i.1)) :=
        entN_eq N' _ _ (by dsimp [yI, wI, rv]; omega) (by rfl)
      rw [q1, zero_add]
    · simp
  rw [← e1, ← e2, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

end Formalism.L2.SG.Pf.KppLoc
end
end
