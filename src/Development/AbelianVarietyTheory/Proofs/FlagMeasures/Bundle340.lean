module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle138
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle331
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle333
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle332
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem GCoord.c_mul_gS_eq_delta_theta : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → gS D ≠ 0 ∧ ∀ p, (G.c p : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) * (gS D : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) = (show ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp from Y.δ p) * (G.S p).th := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ _ G c t₀ ρ U U' _
  have hg : gS D ≠ 0 := by
    show D.host.g 0 * D.host.g 1 ≠ 0
    exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  refine ⟨hg, fun p => ?_⟩

  have hE : ((gS D : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  let cp : (D.s.atP p).Fp := (G.c p).val
  have hc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep cp =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) * (D.s.atP p).ιE (uP p : D.host.E) := c.c_eq p
  have hu : ((uP p : ℚ) : D.host.E) * ((gS D : ℕ) : D.host.E) = ((gpart p : ℕ) : D.host.E) := by
    rw [uP, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, div_mul_cancel₀ _ hE]
  have h1 : cp * ((gS D : ℕ) : (D.s.atP p).Fp) = (Y.δ p) * ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    apply (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective
    rw [map_mul, map_mul, map_natCast, map_natCast, hc, mul_assoc]
    congr 1
    rw [← map_natCast (D.s.atP p).ιE, ← map_natCast (D.s.atP p).ιE, ← map_mul, hu]

  have h2 : ((G.S p).th : (D.s.atP p).Fp) = ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    have hA := (Y.agree p).2.2.2.2.2
    have hs := D.s_split p
    have wc := c.c p
    rcases hM : (Y.M p).split with _ | g <;> rcases hD : (D.s.atP p).split with _ | sg
    ·
      have hgg : (G.S p).gg = false := wc.gg_none hM
      have hn : Loc.resChar p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have hgp : gpart p = 1 := by unfold gpart; rw [if_neg hn.1, if_neg hn.2]
      rw [Frames.th, hgg, hgp]
      exact (if_neg (by decide)).trans Nat.cast_one.symm
    · simp [hM, hD] at hA
    · simp [hM, hD] at hA
    · have hgs := wc.gg_some g hM
      simp only [hM, hD] at hA
      have hn : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      have hq := sg.q_eq
      have hgp : gpart p = Loc.resChar p := by
        unfold gpart
        rcases hn with h | h
        · rw [if_pos h, h]
        · by_cases h0 : Loc.resChar p = D.host.g 0
          · rw [if_pos h0, h0]
          · rw [if_neg h0, if_pos h, h]
      simp only [Frames.th, hgs.1, if_true, hgs.2, hA.2, hgp]
      exact hq
  exact h1.trans (congrArg (Y.δ p * ·) h2.symm)

end GlobalTheory.HL
end

section


theorem _root_.GlobalTheory.T.realPointGramMinorsAgree_proof : GlobalTheory.TypeAsm.GramC := by
  first | exact @GlobalTheory.TypeAsm.gramC_holds | exact GlobalTheory.TypeAsm.gramC_holds | (intros; apply GlobalTheory.TypeAsm.gramC_holds <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unitaryHostFieldArithmeticConditions : GlobalTheory.TypeAsm.HostC := by
  first | exact @GlobalTheory.TypeAsm.hostC | exact GlobalTheory.TypeAsm.hostC | (intros; apply GlobalTheory.TypeAsm.hostC <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St

variable {D : D7}

theorem hspace_gram_det_ne {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : S.frame.equivFun.symm v = 0 := by
    refine S.nondeg.2 _ fun x => ?_
    have hx : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := fun i => by
      have := congrFun h0 i
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    rw [← S.frame.sum_repr x]

    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_zero,
    Finset.sum_const_zero]
  exact (LinearEquiv.map_eq_zero_iff _).1 this

theorem hform_crd_setting (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w)) = (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  Formalism.UG.hform, map_mul, HidaSetting.crd, crdOf, starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply,
  X.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem gram_entry {A : Type} [CommRing A] {n ι : Type} [Fintype n] (σ : A →+* A) (Q : Matrix n ι A)
    (J : Matrix n n A) (k l : ι) :
    ((Q.map σ)ᵀ * J * Q) k l = Formalism.UG.hform σ J (fun i => Q i k) (fun i => Q i l) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Formalism.UG.hform, Finset.sum_mul]
  exact Finset.sum_comm

def famQ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) → (VS D).V :=
  Sum.elim (qFr wt) (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u))

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem hT_symm_zero {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [← (VS D).herm.eq x y, h, map_zero]

theorem hT_wt_symm (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y)
    (x y : (VS D).V) : (VS D).hT (wt.symm x) y = (VS D).hT x (wt y) := by
  rw [← hiso, LinearEquiv.apply_symm_apply]

theorem hT_qFr_qFr (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y)
    (a b : Fin (D.R.N 0)) : (VS D).hT (qFr wt a) (qFr wt b) = Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) a b := by
  rw [qFr, hT_wt_symm wt hiso, qFr, LinearEquiv.apply_symm_apply, xFr, xFr,
    D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)]
  rfl

theorem hT_qFr_rest (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hw : WittX X u wt)
    (a : Fin (D.R.N 0)) (k : Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) :
    (VS D).hT (qFr wt a) (famQ X u wt (Sum.inr k)) = 0 := by
  obtain ⟨hiso, he, hf, hz⟩ := hw
  rw [qFr, hT_wt_symm wt hiso]
  rcases k with b | b | b
  · simp only [famQ, Sum.elim_inr, Sum.elim_inl, he]; exact (D.sp.hyp_orthX b _).1
  · simp only [famQ, Sum.elim_inr, Sum.elim_inl, hf]; exact (D.sp.hyp_orthX b _).2
  · simp only [famQ, Sum.elim_inr, hz, Formalism.BasicNotions.D7.zmOf, LinearMap.map_smul]
    rw [xFr, D.sp.zm_orth, smul_zero]

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem hT_fe (X : HidaSetting D) (a b : Fin D.R.rS) :
    (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  rw [← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
  split_ifs <;> simp

theorem hT_ze (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS) : (VS D).hT (X.zu u) (X.eX b) = 0 :=
  hT_symm_zero (X.zu_orth u b).1

theorem hT_zf (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS) : (VS D).hT (X.zu u) (X.fY b) = 0 :=
  hT_symm_zero (X.zu_orth u b).2

theorem hT_zz_ne (X : HidaSetting D) (u : D.what₂.Word) : (VS D).hT (X.zu u) (X.zu u) ≠ 0 := by
  rw [X.zu_norm, neg_ne_zero, Nat.cast_ne_zero]
  exact ((D.mem u).A.T_prime).ne_zero

def gramR (X : HidaSetting D) (u : D.what₂.Word) :
    Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E :=
  Matrix.of fun k l => X.ιE.symm ((VS D).hT (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u) k)
    (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u) l))

def gramRinv (X : HidaSetting D) (u : D.what₂.Word) :
    Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E :=
  Matrix.of fun k l => match k, l with
    | Sum.inl a, Sum.inr (Sum.inl b) => if a = b then 1 else 0
    | Sum.inr (Sum.inl a), Sum.inl b => if a = b then 1 else 0
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => (X.ιE.symm ((VS D).hT (X.zu u) (X.zu u)))⁻¹
    | _, _ => 0

theorem gramR_mul_inv (X : HidaSetting D) (u : D.what₂.Word) : gramR X u * gramRinv X u = 1 := by
  have ht : X.ιE.symm ((VS D).hT (X.zu u) (X.zu u)) ≠ 0 := by
    rw [Ne, RingEquiv.map_eq_zero_iff]; exact hT_zz_ne X u
  ext (a | a | a) (b | b | b) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, gramR, gramRinv, X.ee, X.ff, X.ef, hT_fe, hT_ze, hT_zf,
      X.zu_orth, Matrix.one_apply, ht, eq_comm]

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem qFrame_basis_gram : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ (Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E) (Qi : Matrix (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) (Fin X.B.I.n) X.B.I.E) (G' : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E), Q * Qi = 1 ∧ Qi * Q = 1 ∧ (∀ j i, Q i (Sum.inl j) = X.crd (qFr wt j) i) ∧ (∀ a i, Q i (Sum.inr (Sum.inl a)) = X.eR a i) ∧ (∀ a i, Q i (Sum.inr (Sum.inr (Sum.inl a))) = X.fR a i) ∧ (∀ i, Q i (Sum.inr (Sum.inr (Sum.inr ()))) = X.zR u i) ∧ IsUnit G'.det ∧ (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 G' := by
  intro D X u wt hw
  classical
  let Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E :=
    Matrix.of fun i k => X.crd (famQ X u wt k) i
  have hiso := hw.1

  have hM : (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q =
      Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 (gramR X u) := by
    ext k l
    rw [gram_entry]
    apply X.ιE.injective
    rw [show (fun i => Q i k) = X.crd (famQ X u wt k) from rfl, show (fun i => Q i l) = X.crd (famQ X u wt l) from rfl,
      hform_crd_setting]
    rcases k with a | k <;> rcases l with b | l
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.map_apply, RingEquiv.apply_symm_apply]
      exact hT_qFr_qFr wt hiso a b
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, map_zero]
      exact hT_qFr_rest X u wt hw a l
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, map_zero]
      exact hT_symm_zero (hT_qFr_rest X u wt hw b k)
    · simp only [Matrix.fromBlocks_apply₂₂, gramR, Matrix.of_apply, RingEquiv.apply_symm_apply]
      rfl

  have hA : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det ≠ 0 := by
    have h1 : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det =
        X.ιE.symm.toRingHom (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det := by
      rw [RingHom.map_det]; rfl
    rw [h1]
    refine (map_ne_zero _).2 ?_
    unfold Formalism.L2.Forms.gramN
    rw [Matrix.det_reindex_self]
    exact hspace_gram_det_ne _
  have hG : IsUnit (gramR X u).det := Matrix.isUnit_det_of_right_inverse (gramR_mul_inv X u)
  have hMu : IsUnit ((Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q).det := by
    rw [hM, Matrix.det_fromBlocks_zero₂₁]
    exact (isUnit_iff_ne_zero.2 hA).mul hG

  have hcard : Fintype.card (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) = X.B.I.n := by
    rw [X.n_eq, ← dimS_eq, Formalism.BasicNotions.Ranks.N_zero]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  let σ := Fintype.equivFinOfCardEq hcard
  let P := Q.submatrix σ id
  have hQ : Q = P.submatrix σ.symm id := by
    ext i k; simp [P]
  have hconj : (Q.map (starRingEnd X.B.I.E))ᵀ = Qᴴ := by
    ext i k
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
    exact starRingEnd_apply _
  have hPJ : (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Pᴴ * X.B.I.J.submatrix σ σ * P := by
    have hJ : X.B.I.J = (X.B.I.J.submatrix σ σ).submatrix σ.symm σ.symm := by
      simp [Matrix.submatrix_submatrix]
    rw [hconj, hQ, Matrix.conjTranspose_submatrix]
    conv_lhs => rw [hJ]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hP : IsUnit P.det := by
    rw [hPJ, Matrix.det_mul, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_right hMu
  refine ⟨Q, (P⁻¹).submatrix id σ.symm, gramR X u, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, hG, hM⟩
  · rw [hQ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_nonsing_inv _ hP,
      Matrix.submatrix_one_equiv]
  · rw [hQ, Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hP, Matrix.submatrix_id_id]

end GlobalTheory.St
end
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.St

theorem repF_of_rational : ∀ (D : D7) (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsAdeleIso X ιA → ∀ (h : X.B.I.Gf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), X.B.I.fmat h = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), y.1.1 = (y₀.map X.ιE).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) → RepF X wt ιA h y := by
  intro D X wt ιA hA h γ₀ y₀ hf hq y hy j
  have hs : ∀ i, ιA.symm (y.1.1 i j) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y₀ i j) := by
    intro i
    rw [hy, RingEquiv.symm_apply_eq, Matrix.map_apply, Matrix.map_apply, hA.1]
  simp_rw [hs]
  have hl : X.B.I.fmat h *ᵥ qA X wt j =
      fun k => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((γ₀ *ᵥ X.crd (qFr wt j)) k) := by
    rw [hf]
    funext k
    show (γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
      ((Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∘ X.crd (qFr wt j))) k = _
    rw [← RingHom.map_mulVec]
  rw [hl, hq j]
  funext k

  simp [qA, incl, Finset.sum_apply, map_sum, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.St
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.St.G

theorem latTransport : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ w : Fin X.B.I.n → D.host.E ⊗[D.host.F] Ad D.host.F, w ∈ hat D.host.F ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) ↔ (fun i => ιA.symm (w i)) ∈ X.B.I.Lf := by
  intro D X ιA hA w
  obtain ⟨h1, h2⟩ := hA
  have hgen : ∀ x : X.B.I.E, ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) (X.ιE x)) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x := by
    intro x; rw [RingEquiv.symm_apply_eq]; exact (h1 x).symm
  have hgen' : ∀ x : X.B.I.E, ιA (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) (X.ιE x) := h1
  have hint : ∀ a, a ∈ IntAf X.B.I.F X.B.I.E ↔ ιA a ∈ OAd D.host.F D.host.E := h2
  have hL' : ∀ c : Fin X.B.I.n → D.host.E,
      c ∈ (VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E)) ↔
        (fun i => X.ιE.symm (c i)) ∈ X.B.I.L := by
    intro c
    rw [X.L_eq, Submodule.mem_comap]
    simp [Fintype.linearCombination_apply]
  constructor
  · intro hw
    change w ∈ Submodule.span _ _ at hw
    change (fun i => ιA.symm (w i)) ∈ Submodule.span _ _
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine Submodule.subset_span ⟨⟨fun i => X.ιE.symm (c i), (hL' c).1 hc⟩, ?_⟩
      funext i
      simp only
      rw [← hgen, RingEquiv.apply_symm_apply]
    | zero =>
      convert Submodule.zero_mem _ using 1
      funext i; simp
    | add x y _ _ hx hy =>
      have : (fun i => ιA.symm ((x + y) i)) = (fun i => ιA.symm (x i)) + (fun i => ιA.symm (y i)) := by
        funext i; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hr : ιA.symm (r : D.host.E ⊗[D.host.F] Ad D.host.F) ∈ IntAf X.B.I.F X.B.I.E := by
        rw [hint, RingEquiv.apply_symm_apply]; exact r.2
      have : (fun i => ιA.symm ((r • x) i)) = (⟨_, hr⟩ : IntAf X.B.I.F X.B.I.E) • (fun i => ιA.symm (x i)) := by
        funext i; simp [Subring.smul_def, smul_eq_mul, map_mul]
      rw [this]; exact Submodule.smul_mem _ _ hx
  · intro hw
    change _ ∈ Submodule.span _ _ at hw
    change w ∈ Submodule.span _ _
    have key : ∀ v, v ∈ Submodule.span (IntAf X.B.I.F X.B.I.E)
        (Set.range fun x : X.B.I.L => fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((x : Fin X.B.I.n → X.B.I.E) i)) →
        (fun i => ιA (v i)) ∈ hat D.host.F ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
      intro v hv
      change _ ∈ Submodule.span _ _
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        refine Submodule.subset_span ⟨fun i => X.ιE ((x : Fin X.B.I.n → X.B.I.E) i), (hL' _).2 ?_, ?_⟩
        · simpa using x.2
        · funext i; simp only; rw [hgen']
      | zero =>
      convert Submodule.zero_mem _ using 1
      funext i; simp
      | add x y _ _ hx hy =>
        have : (fun i => ιA ((x + y) i)) = (fun i => ιA (x i)) + (fun i => ιA (y i)) := by
          funext i; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        have hr : ιA (r : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ OAd D.host.F D.host.E := (hint _).1 r.2
        have : (fun i => ιA ((r • x) i)) = (⟨_, hr⟩ : OAd D.host.F D.host.E) • (fun i => ιA (x i)) := by
          funext i; simp [Subring.smul_def, smul_eq_mul, map_mul]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have := key _ hw
    have e : (fun i => ιA (ιA.symm (w i))) = w := funext fun i => by simp
    rw [e] at this
    exact this

end GlobalTheory.St.G
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.IotaSigmaCompatibility

theorem iotaA_sigA : ∀ (D : D7) (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA →
    ∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a) := by
  intro D X ιA h a
  have he : ∀ x : X.B.I.E, X.ιE (X.B.I.cm.sig x) = Formalism.L2.Forms.sigD D (X.ιE x) := by
    intro x
    have h1 : X.B.I.cm.sig x = star x := rfl
    have h2 : Formalism.L2.Forms.sigD D (X.ιE x) = star (X.ιE x) := rfl
    rw [h1, h2, X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]
  exact GlobalTheory.St.G.IotaConj.iota_sigR X.B.I.F X.B.I.E D.host.F D.host.E X.B.I.cm.sig
    (Formalism.L2.Forms.sigD D) X.ιE ιA he h.1 h.2 a

end GlobalTheory.St.G.IotaSigmaCompatibility
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.sobolev_inequality_at_identity_besselModelUnitaryGroup : ∀ (k r : ℕ) (μG : Measure (Mt k r)), IsHaarOn (GG k r) μG → ∃ (C : ℝ) (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsCompact K₀ ∧ (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C * (Ws.map fun ws => ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum := by
  first | exact @GlobalTheory.SobAtOne.sobolev_at_one_G | exact GlobalTheory.SobAtOne.sobolev_at_one_G | (intros; apply GlobalTheory.SobAtOne.sobolev_at_one_G <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bigCellChartDifferential_surjective_skew : ∀ (k r : ℕ) (Z : Mat k r), Zᴴ * Hpk k r + Hpk k r * Z = 0 → ∃ v : EE k r, dchart k r v = Z := by
  first | exact @GlobalTheory.CellDens.Onto.dchart_onto | exact GlobalTheory.CellDens.Onto.dchart_onto | (intros; apply GlobalTheory.CellDens.Onto.dchart_onto <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalIsometry_coordinateMatrix_realPlace : ∀ {D : D7} (X : HidaSetting D) {x : X.B.I.GA} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ∀ τ : D.what₂.Tau, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (x.1 (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X) := by
  first | exact @GlobalTheory.CovDomGrp.coordMat_place | exact GlobalTheory.CovDomGrp.coordMat_place | (intros; apply GlobalTheory.CovDomGrp.coordMat_place <;> assumption)
end
