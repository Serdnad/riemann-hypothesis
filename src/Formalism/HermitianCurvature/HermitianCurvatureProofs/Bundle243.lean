module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle229
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle211
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle222
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle241
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBPts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle237
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle223
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle228
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle233
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointLevelZeroEqEmbedding
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle239
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle212
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle031
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterpolationInverseMatrixSumIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle030
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

theorem side1Zero_of (hC : CutOffStep) (hE : CutOffExists) (h0 : CutHB.Side0Zero) (hW : PartialBesselProperness.PbWords)
    (hPr : PBQ.ProperDomP) : CutHB.Side1Zero := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hj1 hF hw hγ hΩ t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  obtain ⟨Fc, hFc, hag⟩ := hE Wp Wq P p F j hj w h hh hF hw t ht e
  rw [hC Wp Wq P p F j hj w h hh γ hF hw hγ hΩ t ht e Fc hFc hag]
  rw [h0 Wp Wq P p Fc j hj [] h hh γ hj1 hFc ⟨fun a => a.elim0, fun a => a.elim0⟩ hγ hΩ (fun a => a.elim0) t ht0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show ellH h v (CutHB.phf p Fc j hj [] h hh.2 γ v (fun a => a.elim0) t) = ellH h v _
  congr 1
  have hpt := CutHB.pts Wp Wq P p j hj h hh γ hγ hΩ v
  have hyD := hpt.2 t ht0
  have hyG := x0_GV hj hpt.1 ht0 hγ

  obtain ⟨R, hR⟩ := hF.2.1
  set Cs : Set (B.Mat P.k P.r) := {g | B.gN g ≤ R} with hCs
  have hCc : IsCompact Cs := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have e' : j + (P.r - j) = P.r := by omega
  have hz : p.T.base.z = D.castV e' (liftVec P.k j (P.r - j) (p.T.bs j).z) := (p.T.z_lev j (by omega)).symm
  have hPW := hW P.k j (P.r - j) P.r Wp Wq (p.T.bs j) p.T.base e' hz (j + 1) hj F Cs (fun g hg _ => hF.1 g hg) hCc
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (domP P.k P.r j p.T.base.z p.T.base.z') (isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨j + 1, by omega⟩ (show j ≤ j + 1 by omega) (show j + 1 ≤ P.r by omega))
    (hPr Wp Wq P p j (by omega) Cs hCc) w e _ hyD hyG
  show pbT p j (by omega) Fc (x0 P.k P.r j hj (zxH h j hh.2 v) t γ) =
    D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) (j + 1) hj w e (x0 P.k P.r j hj (zxH h j hh.2 v) t γ)
  unfold pbT
  rw [hPW]
  have hDv : Dmin P.k P.r p.T.base.z p.T.base.z' (x0 P.k P.r j hj (zxH h j hh.2 v) t γ) ⟨j + 1, by omega⟩ = aVal h t := by
    rw [(CutHL.leading_minors_at_base_point P.k P.r j hj p.T.base.z p.T.base.z' (zxH h j hh.2 v) t γ hpt.1 ht0 hγ).2, zxH_det h j hh v]
    rfl
  exact pbT_agree P p j hj (aVal h t) Fc _ (fun g _ hg => hag g hg) _ hyG hDv

end Formalism.FourierDecayAlt.P.LevelPointCoordinates

namespace Formalism.FourierDecayAlt.P

theorem side_one_zero : CutHB.Side1Zero :=
  LevelPointCoordinates.side1Zero_of smooth_truncation_induction smooth_truncation_exists
    (SliceIntegralLemmas.side0Zero_of letters_pass_partial_bessel proper_left_variables_domain CutHB.pts) letters_pass_partial_bessel proper_left_variables_domain

theorem head_germ_smooth_extension : LevelPointCoordinates.HeadBridge :=
  CutHB.headBridge_of_rest proper_left_variables_domain word_smooth_partial_bessel
    (CutHB.side_one_of_positive_and_zero side_one_positive side_one_zero)

theorem head_jacquet : LevelPointCoordinates.HeadJ := head_jacquet_of_letter_and_head head_letter_identity head_germ_smooth_extension

theorem head_picture : PBP.HeadPic := PBP.headPic_of head_jacquet

theorem radial_head : KB.RadHead := radial_head_of_letter_and_head head_letter_identity head_germ_smooth_extension

end Formalism.FourierDecayAlt.P
end
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem rdb_glev0_inter_om (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Q.Glev k r 0 ∩ JF.Om k r z z' = Q.Glev k r 0 ∩ Q.OmPlus k r z z' := by
  ext g
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h1.1, h2⟩

theorem rdb_ffl_om_eq (k r : ℕ) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) :
    Q.FFl k r z z' π π' 0 (JF.Om k r z z') = Q.FFl k r z z' π π' 0 (Q.OmPlus k r z z') := by
  simp only [Q.FFl, Q.SmoothLev, Q.LeftEq, Q.RightEq, rdb_glev0_inter_om]

private theorem conjTranspose_mul_H_mul_preserved_of_preserved {n : ℕ} (H a b : Matrix (Fin n) (Fin n) ℂ)
    (ha : a.conjTranspose * H * a = H) (hb : b.conjTranspose * H * b = H) :
    (a * b).conjTranspose * H * (a * b) = H := by
  rw [Matrix.conjTranspose_mul]
  calc b.conjTranspose * a.conjTranspose * H * (a * b)
      = b.conjTranspose * (a.conjTranspose * H * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = H := by
        rw [ha, hb]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem radial_residue_formula : RDResRad := by
  classical
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD J hJ
  have hz := hD.1.2.1
  have hz' := hD.1.2.2.1
  rw [rdb_ffl_om_eq] at hJ
  obtain ⟨hS, -, -, hE⟩ := hJ
  have huh : ∀ a b : Mx P.k P.r, a ∈ UH (Hpk P.k P.r) → b ∈ UH (Hpk P.k P.r) →
      a * b ∈ UH (Hpk P.k P.r) :=
    fun a b ha hb => conjTranspose_mul_H_mul_preserved_of_preserved _ a b ha hb
  have hcell : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c ∈ UH (Hpk P.k P.r) := by
    intro c hc
    refine List.prod_induction _ huh ?_ ?_
    · show (1 : Mx P.k P.r).conjTranspose * Hpk P.k P.r * 1 = Hpk P.k P.r
      simp
    · intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      exact Qx3.weyl_cell_mem_unitary a (hc a)
  have hcomm : ∀ (c : Fin P.r → ℂ) (h : Mx P.k P.r), h ∈ UWset P.k P.r z →
      Commute (wCell P.k P.r (Fin.last P.r) c) h := by
    intro c h hh
    refine Commute.list_prod_left _ _ ?_
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact Qx3.w1_commute_of_mem_Glev a (c a) ⟨hh.1, fun b _ => hh.2.1 b⟩
  have hin : ∀ x ∈ DomR P.k P.r z z',
      wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ Glev P.k P.r 0 ∩ OmPlus P.k P.r z z' :=
    fun x hx => ⟨Rad.glev0 (huh _ _ (hcell _ hx.1) hx.2.1.1),
      Rad.wCell_mem_omPlus hz hz' hx.1 hx.2.1 hx.2.2⟩
  let Φ0 : Fn P.k P.r (Wq →L[ℂ] Wp) := fun c g =>
    if (c, g) ∈ DomR P.k P.r z z' then resG P.k P.r (Fin.last P.r) J c g else 0
  have hmem : Φ0 ∈ RadSp P.k P.r z z' π π' := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact if_neg hx
    · intro x₀ hx₀
      obtain ⟨U, F, hU, hxU, hF, hag⟩ :=
        Rad.sf_resG hS x₀ ⟨hx₀.1, (hin x₀ hx₀).2⟩ hx₀.2.1
      refine ⟨U ∩ (Prod.fst ⁻¹' OmX P.r ∩ Prod.snd ⁻¹' {g | 0 < GGl P.k P.r z z' g}), F,
        hU.inter (((Qx3.isOpen_OmX _).preimage continuous_fst).inter
          (isOpen_lt continuous_const ((Qx5.GGl_continuous _ _ _ _).comp continuous_snd))),
        ⟨hxU, hx₀.1, hx₀.2.2⟩, hF.mono Set.inter_subset_left, ?_⟩
      intro x hx hg
      have hxD : x ∈ DomR P.k P.r z z' := ⟨hx.2.1, hg, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) = _
      rw [if_pos hxD]
      exact hag x hx.1 hg
    · intro x hx h hh h' hh'
      have hx' := Rad.domR_uw hx hh hh'
      show (if (x.1, h * x.2 * h') ∈ DomR P.k P.r z z' then _ else _) =
        π h ∘SL (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) ∘SL π' h'
      rw [if_pos hx', if_pos hx]
      simp only [resG]
      rw [show wCell P.k P.r (Fin.last P.r) x.1 * (h * x.2 * h') =
          h * (wCell P.k P.r (Fin.last P.r) x.1 * x.2) * h' by
        simp only [← mul_assoc, (hcomm x.1 h hh).eq]]
      rw [hE _ (hin x hx) h hh h' hh']
      simp [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨⟨Φ0, hmem⟩, fun x hx => ?_⟩
  show (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) = _
  rw [if_pos hx]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
open scoped ComplexConjugate

section PairSub

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem rdw_sub_fst (a b : Pr V) : (a - b).1 = a.1 - b.1 := rfl
theorem rdw_sub_snd (a b : Pr V) : (a - b).2.unop = a.2.unop - b.2.unop := rfl

end PairSub

theorem radial_wave_radial : RDWaveRad := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hr s hD Wv Wv' hW hW'
  obtain ⟨-, -, hL, hQ, -⟩ := hD
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hG, hGi, -⟩ := hL
  obtain ⟨hWave, hWc, hWci, hWp⟩ := waveSiteAll Wp Wq P z z' π π' X L hL' ⟨0, hr⟩ s Wv Wv' hW hW'
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hop : ∀ (l : Fin P.r) i (Φ : RadSp P.k P.r z z' π π'),
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) :=
    fun l i Φ => X.op_apply l i Φ
  have hcomm : ∀ (W : Module.End ℂ (RadSp P.k P.r z z' π π')) (u : ℂ → ℂ),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        u (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ i : Fin 6, (i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5) → Commute W (X.op ⟨0, hr⟩ i) := by
    intro W u hWu i hi
    show W * X.op ⟨0, hr⟩ i = X.op ⟨0, hr⟩ i * W
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, hWu, hop, crd]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [opL, cOp, ciOp, cbOp, cbiOp] <;> exact smul_comm _ _ _
  have hoth : ∀ (t : ℂ) (W : Module.End ℂ (RadSp P.k P.r z z' π π')),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        fsv t (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ l : Fin P.r, l ≠ ⟨0, hr⟩ → ∀ i : Fin 6, Commute W (X.op l i) :=
    fun t W hWt l hl i => mulOp_comm_op X W t ⟨0, hr⟩ hWt hl i
  refine ⟨hWave, hWc, hWci, ?_, ?_, hWp, ?_, ?_, ?_, ?_⟩
  · rw [hcb]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hcomm Wv _ hW1 4 (by decide)) (hcomm Wv' _ hW2 1 (by decide))
  · rw [hcbi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hcomm Wv _ hW1 5 (by decide)) (hcomm Wv' _ hW2 2 (by decide))
  · rw [hpb, hcb]
    refine pr_ext ?_ ?_
    · change X.op ⟨0, hr⟩ 3 * Wv = Wv * X.op ⟨0, hr⟩ 3 -
        algebraMap ℂ _ (starRingEnd ℂ s) * Wv * X.op ⟨0, hr⟩ 4
      apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
      obtain ⟨hd, h0⟩ := radSp_regular Φ g c
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
        Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, hop, crd, hW1, opL]
      have e := pbOp_fsv_smul (-s) ⟨0, hr⟩ _ c hd h0
      simp only [neg_neg] at e
      rw [e]
      simp only [cbOp, map_neg]
      module
    · change Wv' * (-X.op ⟨0, hr⟩ 0) = (-X.op ⟨0, hr⟩ 0) * Wv' -
        X.op ⟨0, hr⟩ 1 * Wv' * algebraMap ℂ _ (starRingEnd ℂ (starRingEnd ℂ s))
      apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
      obtain ⟨hd, h0⟩ := radSp_regular Φ g c
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
        Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, hop,
        crd, hW2, opL]
      rw [pOp_fsv_smul (-s) ⟨0, hr⟩ _ c hd h0]
      simp only [cOp, Complex.conj_conj]
      module
  · intro l hl x hx
    simp only [coordOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 0) (hoth (-s) Wv' hW2 l hl 3).neg_right
    · rw [hpb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 3) (hoth (-s) Wv' hW2 l hl 0).neg_right
    · rw [hc l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 1) (hoth (-s) Wv' hW2 l hl 4)
    · rw [hci l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 2) (hoth (-s) Wv' hW2 l hl 5)
    · rw [hcb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 4) (hoth (-s) Wv' hW2 l hl 1)
    · rw [hcbi l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 5) (hoth (-s) Wv' hW2 l hl 2)
  · have hf : ∀ j : Fin 6, Commute Wv (X.fn j) ∧ Commute Wv' (X.fn j) := fun j =>
      ⟨TwistedTransfer.mulOp_comm_fn X Wv _ hW j, TwistedTransfer.mulOp_comm_fn X Wv' _ hW' j⟩
    intro x hx
    simp only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 0).1 (hf 2).2
    · rw [hzi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 1).1 (hf 3).2
    · rw [hzb]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 2).1 (hf 0).2
    · rw [hzbi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 3).1 (hf 1).2
    · rw [hG]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 4).1 (hf 4).2
    · rw [hGi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 5).1 (hf 5).2
  · intro Y a b
    rw [hQ Y, Matrix.smul_apply, Formalism.FourierDecayAlt.P.NFx3.QQ_apply]
    exact (Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (comm_xt_of_fsv_smul_endomorphism X Wv s ⟨0, hr⟩ hW1 Y a b)
      (comm_xt_of_fsv_smul_endomorphism X Wv' (-s) ⟨0, hr⟩ hW2 (star Y) b a)).smul_right _

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_group_residue : RDGqRes := by
  intro k r Wp Wq _ _ _ _ _ _ D q hq
  obtain ⟨hq1, hq2⟩ := hq
  have hsec := (D.sec.2 q.2 hq2).1
  have hU : B2.embWb k r (D.μsec q.2) ∈ B2.UWb k r :=
    TwoByOneBlock.emb_mem_UWb (k := k) (r := r) hsec
  have hv := TwoByOneBlock.sec_vec D.z_mem D.z'_mem D.sec hq2
  refine ⟨(q.1, B2.embWb k r (D.μsec q.2)), ?_, ?_⟩
  · refine ⟨hq1, ⟨hU.1, fun a _ => hU.2 a⟩, ?_⟩
    show 0 < Complex.normSq (zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2))) - Tz k r D.z * Tz k r D.z'
    have hz : zetaL k r D.z D.z' (Fin.last r) (B2.embWb k r (D.μsec q.2)) = q.2 := by
      unfold zetaL fvec
      simpa using hv.2.2
    rw [hz]
    linarith
  · refine ⟨((∏ a : Fin r, if (a : ℕ) < ((Fin.last r : Fin (r + 1)) : ℕ) then ‖q.1 a‖ ^ (Mdim k r a - 1) else 1 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Complex.ofReal_ne_zero]
      refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
      split_ifs
      · exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hq1 a))
      · exact one_ne_zero
    · intro J _
      have hcell : wCell k r (Fin.last r) q.1 * B2.embWb k r (D.μsec q.2) = B.gq D q := by
        rw [Rad.wCell_last_eq]
        exact ((TwoByOneBlock.bigCellFactor k r q.1 (D.μsec q.2)).1).symm
      unfold resG
      rw [hcell]

end Formalism.FourierDecayAlt.P.CutSE
end
end
