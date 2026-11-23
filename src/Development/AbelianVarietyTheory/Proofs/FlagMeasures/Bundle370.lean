module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle350
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle089
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle353
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle354
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle355
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle356
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.CFrame

theorem hJ_rv_gen (I : AutInst) (v : InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  have hPi : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hJv : I.J.map (I.φ v) = ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ := by
    rw [← I.P_spec v]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hPi, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hPi, Matrix.conjTranspose_one, Matrix.one_mul]
  unfold hJ rv
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hJv]

  simp only [dotProduct, mulVec, Pi.star_apply, Matrix.map_apply, Formalism.UG.hform, map_sum, map_mul,
  starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [I.cm.cmUnram.2.1]
  simp only [RCLike.star_def]
  ring

theorem hform_cols {A : Type} [CommRing A] {n ι : Type} [Fintype n] [Fintype ι] (σ : A →+* A)
    (J : Matrix n n A) (Q : Matrix n ι A) (α β : ι) :
    Formalism.UG.hform σ J (fun i => Q i α) (fun i => Q i β) = ((Q.map σ)ᵀ * J * Q) α β := by
  simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

variable {D : D7} (X : HidaSetting D)

theorem hJ_crd' (v : InfinitePlace X.B.I.F) (a b : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd a)) (rv X.B.I v (X.crd b)) = X.B.I.φ v (X.ιE.symm ((VS D).hT a b)) := by
  rw [hJ_rv_gen, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X a b, RingEquiv.symm_apply_apply]

theorem card_eq : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  rw [X.n_eq]
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

end GlobalTheory.St.CFrame

namespace GlobalTheory.St.CFrame

variable {D : D7} (X : HidaSetting D)

theorem gram_blocks (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hw : WittX X u wt) :
    (∀ v a b, hJ (X.B.I.ε v) (rvV X v (qFr wt a)) (rvV X v (qFr wt b)) =
        X.B.I.φ v (X.ιE.symm (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) a b))) ∧
    (∀ v c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (rvV X v (qFr wt a)) = 0 ∧
        hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (rvV X v (qFr wt a)) = 0) ∧
    (∀ v a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rvV X v (qFr wt a)) = 0) ∧
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hz, _, hblk⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hw
  have hent : ∀ α β, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (fun i => Q i α) (fun i => Q i β) =
      Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 G' α β := by
    intro α β
    rw [hform_cols, hblk]
  have colq : ∀ j, (fun i => Q i (Sum.inl j)) = X.crd (qFr wt j) := fun j => funext fun i => hq j i
  have cole : ∀ a, (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := fun a => funext fun i => he a i
  have colf : ∀ a, (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := fun a => funext fun i => hf a i
  have colz : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext fun i => hz i
  refine ⟨fun v a b => ?_, fun v c a => ⟨?_, ?_⟩, fun v a => ?_, ?_⟩
  · have h := hent (Sum.inl a) (Sum.inl b)
    rw [colq, colq] at h
    rw [rvV, rvV, hJ_rv_gen, h]
    rfl
  · have h := hent (Sum.inr (Sum.inl c)) (Sum.inl a)
    rw [cole, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · have h := hent (Sum.inr (Sum.inr (Sum.inl c))) (Sum.inl a)
    rw [colf, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · have h := hent (Sum.inr (Sum.inr (Sum.inr ()))) (Sum.inl a)
    rw [colz, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · intro h0
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.2 X.B.I.J_det
    have e1 : (Q.map (starRingEnd X.B.I.E))ᵀ * (Qi.map (starRingEnd X.B.I.E))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hinv : ((Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q) *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J X.B.I.J⁻¹,
        Matrix.mul_nonsing_inv _ hJu, Matrix.one_mul, e1]
    rw [hblk] at hinv
    have hd := congrArg Matrix.det hinv
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one] at hd
    have hA : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det = 0 := by
      rw [show ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det =
          X.ιE.symm.toRingHom (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det from
          (RingHom.map_det X.ιE.symm.toRingHom _).symm, h0, map_zero]
    rw [hA, zero_mul, zero_mul] at hd
    exact zero_ne_one hd

end GlobalTheory.St.CFrame

namespace GlobalTheory.St.CFrame

theorem frame_of_type : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ o : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), (∀ τ, (o.1 τ)ᴴ * Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) τ * o.1 τ = 1) ∧ ∀ s ∈ Hinf X u, ∃ m : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ, ∀ τ, m τ ∈ Matrix.unitaryGroup (Fin (D.R.N 0)) ℂ ∧ (m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm) = matW X.B.I (X.wfr u (X.pl.symm τ)) (X.pl.symm τ) s ∧ sTil X wt s τ = o.1 τ * m τ * (o.1 τ)⁻¹ := by
  intro D X u wt hw
  obtain ⟨hqq, hqef, hqz, hdet⟩ := gram_blocks X u wt hw
  have hgQ : ∀ v, gramQ X wt v = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map (Formalism.L2.Forms.embT D (X.pl v)) := by
    intro v
    ext a b
    simp only [gramQ, Matrix.of_apply, Matrix.map_apply]
    rw [hqq, X.φ_eq, RingEquiv.apply_symm_apply]
    rfl
  have hGu : ∀ v, IsUnit (gramQ X wt v).det := by
    intro v
    rw [hgQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hdet)
  have hJm : ∀ v, IsUnit (Formalism.REAL.Jm (X.B.I.ε v)).det :=
    fun v => Matrix.isUnit_det_of_left_inverse (Formalism.REAL.Jm_mul_self _)
  have key := fun v => GlobalTheory.frame_complement_change_of_basis X.B.I.n D.R.rS D.R.k (D.R.N 0) D.R.N_zero.symm (Formalism.REAL.Jm (X.B.I.ε v))
    (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v)
    (fun a => rvV X v (qFr wt a)) (card_eq X) (Formalism.REAL.Jm_conjTranspose _) (hJm v)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.eX a) (X.eX b)).trans ?_
      rw [X.ee]; simp)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.fY a) (X.fY b)).trans ?_
      rw [X.ff]; simp)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = _
      refine (hJ_crd' X v (X.eX a) (X.fY b)).trans ?_
      rw [X.ef]; split_ifs <;> simp)
    (fun a => ⟨by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.eX a) (X.zu u)).trans ?_
      rw [(X.zu_orth u a).1]; simp, by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.fY a) (X.zu u)).trans ?_
      rw [(X.zu_orth u a).2]; simp⟩)
    (by
      show hJ (X.B.I.ε v) _ _ ≠ 0
      refine (hJ_crd' X v (X.zu u) (X.zu u)).trans_ne ?_
      rw [X.zu_norm]
      have hT : (((D.mem u).A.T : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
      simpa using hT)
    (X.wfr_on u v) (X.wfr_perp u v)
    (fun a => ⟨fun c => ⟨(hqef v c a).1, (hqef v c a).2⟩, hqz v a⟩)
    (gramQ X wt v) (fun a b => rfl) (hGu v)
  choose oo hoo using key
  refine ⟨⟨fun τ => oo (X.pl.symm τ), fun τ => (hoo _).1⟩, fun τ => ?_, fun s hs => ?_⟩
  · have h := (hoo (X.pl.symm τ)).2.1
    rw [hgQ, Equiv.apply_symm_apply] at h
    exact h
  · have hfix : ∀ v, ∀ x ∈ fixSet X u, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v x := hs
    have hm := fun τ => (hoo (X.pl.symm τ)).2.2 (uMat (s (X.pl.symm τ))) (s (X.pl.symm τ)).2
      (fun a => ⟨hfix _ _ (Or.inl (Or.inl ⟨a, rfl⟩)), hfix _ _ (Or.inl (Or.inr ⟨a, rfl⟩))⟩)
      (hfix _ _ (Or.inr rfl))
    choose m hmU hmW hmT using hm
    exact ⟨m, fun τ => ⟨hmU τ, hmW τ, hmT τ⟩⟩

end GlobalTheory.St.CFrame
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces : ∀ (D : D7) (T : D.host.E) (F G : LFlag (D.sp.Y 0) D.R.rS T) (g : GV D), Adapt g F G → (∀ j : ℕ, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j) ∧ (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  first | exact @GlobalTheory.adapt_map_flag | exact GlobalTheory.adapt_map_flag | (intros; apply GlobalTheory.adapt_map_flag <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalUnipotent_frameAdapted_and_inv_mem : ∀ (D : D7) (T : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T) (n : GV D), n ∈ NRat F → Adapt n F F ∧ n⁻¹ ∈ NRat F := by
  first | exact @GlobalTheory.NRatInv.adapt_and_inv_mem | exact GlobalTheory.NRatInv.adapt_and_inv_mem | (intros; apply GlobalTheory.NRatInv.adapt_and_inv_mem <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.innerLatticeIdentification_compat_of_graph_eq : ∀ (D : D7) (T T' : D.host.E) (F₀ B : LFlag (D.sp.Y 0) D.R.rS T) (P₁ P₂ B' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D) (ψ₀ ψ₁ β : GV D), ψ₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ψ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (Xsp F₀).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp F₀).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B → (Xsp P₁).map (ψ₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (Xsp P₂).map (ψ₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B' → (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₀ Λ)).2.2 = (gdat B B' (Formalism.HermitianLatticesTheory.gmap ψ₁ Λ)).2.2 → β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (Xsp P₁).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp P₂ → (∀ l ∈ Lrep Λ F₀, (ψ₁⁻¹ * ψ₀) l - l ∈ Xsp F₀) → (∀ x' ∈ Lrep Λ P₁, (ψ₁⁻¹ * ψ₀) x' - β x' ∈ Xsp P₂) → IotaCompat Λ F₀ P₁ P₂ β (gS D) := by
  first | exact @GlobalTheory.iotaCompat_of_graph_eq | exact GlobalTheory.iotaCompat_of_graph_eq | (intros; apply GlobalTheory.iotaCompat_of_graph_eq <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.relevantTerm_norms_ge_one_and_bounded : ∀ (Cg cb Cw cT CT C0 CH C' Cl : ℝ), 0 ≤ CH → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word), HostC → NFExC → LabC → TermC → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
    ∀ t ∈ relSet Y u, 1 ≤ k2Del D (jT t) (labT t) ∧ 1 ≤ DbL D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 ∧
      DbL D (jT t) (labT t) ≤ (Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2) ^ D.R.rS := by
  first | exact @GlobalTheory.TypeAsm.PairsLab.norms_of_relevant | exact GlobalTheory.TypeAsm.PairsLab.norms_of_relevant | (intros; apply GlobalTheory.TypeAsm.PairsLab.norms_of_relevant <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weightedTermPairs_sum_le_via_rows_genusMeans : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → CompatC → PerRowC →
    RowsMeanC → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
    GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    (∀ (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (M : Submodule (𝓞 D.host.E) W) (x x' : ℕ),
      (GlobalTheory.DegCnt.Trip HW (gS D) (s • M) D.R.rS x x').encard = (GlobalTheory.DegCnt.Trip HW (gS D) M D.R.rS x x').encard) →
    ∀ B : ℕ → ℕ → ℝ, (∀ x x', 0 ≤ B x x') →
    (∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) * B x x')) →
    ∀ (j' j'' : ℕ) (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ENNReal.ofReal (∑ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) ≤
      ∑ x ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊,
        ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x') *
        ENNReal.ofReal (massC Y u * B x x') := by
  first | exact @GlobalTheory.TypeAsm.PairsSum.pairs_sum_le | exact GlobalTheory.TypeAsm.PairsSum.pairs_sum_le | (intros; apply GlobalTheory.TypeAsm.PairsSum.pairs_sum_le <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.completion_lattice_inf_orth_eq_orth_part : ∀ (D : D7) (Z : LocDat D) (U : Submodule D.host.E (VS D).V), (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) → (∀ (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → ∀ (p : PlF D) (t : Vp D p), t ∈ lattice₂ D Z.M p Λ → (∀ u ∈ U, LocFacts₂ Z.M p t (baseChange₂ D p u) = 0) → t ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) := by
  first | exact @GlobalTheory.Unfold.OrthLoc.mem_localLattice_inf_orthogonal | exact GlobalTheory.Unfold.OrthLoc.mem_localLattice_inf_orthogonal | (intros; apply GlobalTheory.Unfold.OrthLoc.mem_localLattice_inf_orthogonal <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_lattice_representative_normalised : ∀ (D : D7) (T : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D), IsRowLat D F0 Λ → ∃ σ ∈ Lrep Λ (lf D F0), (VS D).hT σ F0.z = 1 := by
  first | exact @GlobalTheory.RowPartner.exists_partner_rowLat | exact GlobalTheory.RowPartner.exists_partner_rowLat | (intros; apply GlobalTheory.RowPartner.exists_partner_rowLat <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianLattice_local_global_principle : ∀ (D : D7) (Z : LocDat D), (∀ Λ₁ Λ₂ : LV D, Submodule.IsFullLattice D.host.E Λ₁ → Submodule.IsFullLattice D.host.E Λ₂ → {p | lattice₂ D Z.M p Λ₁ ≠ lattice₂ D Z.M p Λ₂}.Finite ∧ ((∀ p, lattice₂ D Z.M p Λ₁ = lattice₂ D Z.M p Λ₂) → Λ₁ = Λ₂)) ∧ ∀ (Λ₀ : LV D), Submodule.IsFullLattice D.host.E Λ₀ → ∀ Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p), (∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤) → {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite → ∃ Λ : LV D, Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ = Lp p := by
  first | exact @GlobalTheory.Unfold.LatLoc.lattices_local_global | exact GlobalTheory.Unfold.LatLoc.lattices_local_global | (intros; apply GlobalTheory.Unfold.LatLoc.lattices_local_global <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → (∀ (g : GV D) (p : PlF D), ∃! g', Ext p g g') ∧ (∀ h ∈ H0 F F', ∀ p g', Ext p h g' → g' ∈ (FP p).UW0) ∧ (∀ (g : GV D) p g' (Λ : LV D), Ext p g g' → lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap g Λ) = LocNG.img g' (lattice₂ D Z.M p Λ)) ∧ ∀ h ∈ H0 F F', ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ y', LocOver (Formalism.HermitianLatticesTheory.gmap h Λ) y' ∧ RMoves h y y' := by
  first | exact @GlobalTheory.RatLocMove.rat_ext_moves | exact GlobalTheory.RatLocMove.rat_ext_moves | (intros; apply GlobalTheory.RatLocMove.rat_ext_moves <;> assumption)
end

section


theorem _root_.GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label : GlobalTheory.TypeAsm.LabC := by
  first | exact @GlobalTheory.TypeAsm.labC | exact GlobalTheory.TypeAsm.labC | (intros; apply GlobalTheory.TypeAsm.labC <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_adaptedNormalForm_relevantTerm : GlobalTheory.TypeAsm.NFExC := by
  first | exact @GlobalTheory.TypeAsm.nfExC_holds | exact GlobalTheory.TypeAsm.nfExC_holds | (intros; apply GlobalTheory.TypeAsm.nfExC_holds <;> assumption)
end
