module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle127
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle005
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle337
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd

@[expose] public section

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDom.ModelIso

variable {D : D7} (X : HidaSetting D)

theorem pl_vOf (τ : D.what₂.Tau) : X.pl (vOf X τ) = τ := by
  simp [vOf]

theorem qi_gram {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) :
    (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
  obtain ⟨-, h2, h3, -⟩ := C.isT τ
  rw [← h3]
  calc (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ
      = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem pinv_gram (v : InfinitePlace X.B.I.F) :
    ((X.B.I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (X.B.I.P v)⁻¹ = X.B.I.J.map (X.B.I.φ v) := by
  have hu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have h1 : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  rw [← X.B.I.P_spec v]
  calc ((X.B.I.P v)⁻¹)ᴴ * ((X.B.I.P v)ᴴ * X.B.I.J.map (X.B.I.φ v) * X.B.I.P v) * (X.B.I.P v)⁻¹
      = (X.B.I.P v * (X.B.I.P v)⁻¹)ᴴ * X.B.I.J.map (X.B.I.φ v) * (X.B.I.P v * (X.B.I.P v)⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem besselModelTransportMatrix_gram_eq {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    (A0 X C w)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * A0 X C w = (Jc X).map (embS D (tauOf D w)) := by
  set τ := tauOf D w
  set B := C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ with hBdef
  have hB : Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B = X.B.I.J.map (X.B.I.φ (vOf X τ)) := by
    rw [← pinv_gram X (vOf X τ), ← qi_gram X C τ, hBdef, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hA : A0 X C w = B.submatrix id (ci X) := rfl
  have hAt : (A0 X C w)ᴴ = Bᴴ.submatrix (ci X) id := by rw [hA, conjTranspose_submatrix]
  have hprod : Bᴴ.submatrix (ci X) id * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B.submatrix id (ci X) =
      (Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B).submatrix (ci X) (ci X) := by
    symm
    rw [submatrix_mul (Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) B (ci X) id (ci X) Function.bijective_id,
      submatrix_mul Bᴴ (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) (ci X) id id Function.bijective_id, submatrix_id_id]
  rw [hAt, hA, hprod, hB]
  ext i j
  simp only [submatrix_apply, map_apply, Jc, X.φ_eq, X.J_eq, pl_vOf]

theorem embedding_of_not_direct (w : InfinitePlace D.host.E) (h : ¬ Direct D w) :
    w.embedding = ComplexEmbedding.conjugate (embS D (tauOf D w)) := by
  have hw : InfinitePlace.mk (embS D (tauOf D w)) = w := (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec
  rcases InfinitePlace.embedding_mk_eq (embS D (tauOf D w)) with h1 | h1
  · rw [hw] at h1; exact (h h1).elim
  · rwa [hw] at h1

theorem isModel {θ : ℝ} (C : Choice X θ) : GlobalTheory.SnMass.IsModelAt (Jc X) (Ac X C) := by
  intro w
  unfold Ac
  split_ifs with h
  · rw [besselModelTransportMatrix_gram_eq, show w.embedding = embS D (tauOf D w) from h]
  · rw [embedding_of_not_direct w h]
    have hH : (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS).map (starRingEnd ℂ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
      ext i j; simp only [map_apply, Formalism.QuantumDeterminants.Hpk]; split_ifs <;> simp
    have hc : ((A0 X C w).map (starRingEnd ℂ))ᴴ = ((A0 X C w)ᴴ).map (starRingEnd ℂ) := by
      ext i j; simp [conjTranspose_apply]
    show ((A0 X C w).map (starRingEnd ℂ))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (A0 X C w).map (starRingEnd ℂ) = _
    rw [hc, ← hH, ← Matrix.map_mul, ← Matrix.map_mul, besselModelTransportMatrix_gram_eq]
    ext i j
    simp [ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.CovDom.ModelIso

namespace GlobalTheory.CovDom.ModelIso

variable {D : D7} (X : HidaSetting D)

theorem v_pos : 0 < D.host.v := by
  have := GlobalTheory.RealPlaces.one_le_rdE D
  unfold Host.v; linarith

theorem frS_ne_zero : frS D ≠ 0 := by
  have hv := v_pos (D := D)
  unfold frS Host.ka
  have : Real.pi / D.host.v / (2 * Real.pi) ≠ 0 := by positivity
  exact_mod_cast this

theorem frS_pow_inv (m : ℕ) : ((frS D) ^ m)⁻¹ = (((2 * D.host.v) ^ m : ℝ) : ℂ) := by
  have hv := v_pos (D := D)
  have h : D.host.ka / (2 * Real.pi) = (2 * D.host.v)⁻¹ := by
    unfold Host.ka; field_simp
  rw [frS, h]; push_cast; rw [inv_pow, inv_inv]

theorem star_frS : star (frS D) = frS D := by
  unfold frS; exact Complex.conj_ofReal _

theorem besselModelTransportMatrix_mulVec_coordinates {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) (y : (VS D).V) :
    (A0 X C w *ᵥ fun i => embS D (tauOf D w) (crdH X y i)) =
      C.Qi (tauOf D w) *ᵥ rv X.B.I (vOf X (tauOf D w)) (X.crd y) := by
  have hx : (fun i => embS D (tauOf D w) (crdH X y i)) =
      (fun j => embS D (tauOf D w) (X.bas.repr y j)) ∘ (ci X) := rfl
  have hx2 : ((fun j => embS D (tauOf D w) (X.bas.repr y j)) ∘ (ci X)) ∘ (ci X).symm =
      fun j => embS D (tauOf D w) (X.bas.repr y j) := by
    funext j; simp
  rw [hx, A0, submatrix_mulVec_equiv, hx2, Function.comp_id, ← mulVec_mulVec]
  congr 1
  unfold rv
  congr 1
  funext i
  rw [X.φ_eq, pl_vOf]
  simp [HidaSetting.crd, crdOf]

theorem qi_e {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    C.Qi τ *ᵥ rv X.B.I (vOf X τ) (X.eR a) =
      (((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) := by
  obtain ⟨h1, -, -, h4⟩ := C.isT τ
  have he := congrArg (fun x => C.Qi τ *ᵥ x) (h4 a a rfl).1
  simp only [mulVec_mulVec, h1, one_mulVec, mulVec_smul] at he
  rw [← frS_pow_inv, Formalism.QuantumDeterminants.bvec, he, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ frS_ne_zero), one_smul]

theorem qi_f {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    C.Qi τ *ᵥ rv X.B.I (vOf X τ) (X.fR a) =
      ((((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ))⁻¹ • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨h1, -, -, h4⟩ := C.isT τ
  have he := congrArg (fun x => C.Qi τ *ᵥ x) (h4 a a rfl).2
  simp only [mulVec_mulVec, h1, one_mulVec, mulVec_smul] at he
  have hs : star (frS D ^ (D.R.rS - (a : ℕ))) = frS D ^ (D.R.rS - (a : ℕ)) := by
    rw [star_pow, star_frS]
  rw [hs] at he
  rw [← frS_pow_inv, inv_inv, Formalism.QuantumDeterminants.bvec, he, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero _ frS_ne_zero), one_smul]

theorem Ac_mulVec {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) (y : (VS D).V) (c : ℝ)
    (j' : Fin (2 * D.R.rS + D.R.k + 1))
    (h : (A0 X C w *ᵥ fun i => embS D (tauOf D w) (crdH X y i)) = (c : ℂ) • Formalism.QuantumDeterminants.bvec j') :
    (Ac X C w *ᵥ fun i => w.embedding (crdH X y i)) = (c : ℂ) • Formalism.QuantumDeterminants.bvec j' := by
  unfold Ac
  split_ifs with hd
  · rw [show w.embedding = embS D (tauOf D w) from hd]; exact h
  · rw [embedding_of_not_direct w hd]
    have e1 : (fun i => (ComplexEmbedding.conjugate (embS D (tauOf D w))) (crdH X y i)) =
        ⇑(starRingEnd ℂ) ∘ (fun i => embS D (tauOf D w) (crdH X y i)) := by
      funext i; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [e1]
    funext i
    rw [show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← RingHom.map_mulVec, h]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, Formalism.QuantumDeterminants.bvec]
    congr 1
    rcases eq_or_ne i j' with rfl | hij
    · simp
    · simp [hij]

end GlobalTheory.CovDom.ModelIso

namespace GlobalTheory.CovDom.ModelIso

theorem model_adapted : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word),
    GlobalTheory.SnMass.IsModelAt (Jc X) (Ac X C) ∧ GlobalTheory.SnMass.Adapted (Ac X C) (Pc X u) (fc X) (sc D) := by
  intro D X θ C u
  refine ⟨isModel X C, fun w a => ⟨?_, ?_⟩⟩
  · have hP : (fun i => w.embedding (Pc X u i a.castSucc)) = fun i => w.embedding (crdH X (X.eX a) i) := by
      funext i; simp [Pc]
    rw [hP]
    exact Ac_mulVec X C w _ _ _ (by rw [besselModelTransportMatrix_mulVec_coordinates]; exact qi_e X C _ a)
  · have hf : (fun i => w.embedding (fc X i a)) = fun i => w.embedding (crdH X (X.fY a) i) := rfl
    rw [hf]
    have := Ac_mulVec X C w (X.fY a) ((2 * D.host.v) ^ (D.R.rS - (a : ℕ)))⁻¹ (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a)
      (by rw [besselModelTransportMatrix_mulVec_coordinates]; have := qi_f X C (tauOf D w) a; push_cast at this ⊢; exact this)
    unfold sc; push_cast at this ⊢; exact this

end GlobalTheory.CovDom.ModelIso
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.FrameCrd

variable {D : D7} (X : HidaSetting D)

theorem sig_apply (x : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) x = starRingEnd D.host.E x := rfl

theorem vecOf_sum (x : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X x = ∑ i, x i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply]
  rw [← Equiv.sum_comp (ci X).symm]
  simp

theorem vecOf_crdH (y : (VS D).V) : vecOf X (crdH X y) = y := by
  rw [vecOf_sum]
  simp only [crdH]
  rw [Equiv.sum_comp (ci X) (fun j => X.bas.repr y j • X.bas j)]
  exact X.bas.sum_repr y

theorem pairM_apply {α β : Type} [Fintype α] [Fintype β]
    (P : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) α D.host.E) (Q : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) β D.host.E)
    (a : α) (b : β) :
    GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) Q P a b =
      (VS D).hT (vecOf X fun i => P i a) (vecOf X fun i => Q i b) := by
  rw [vecOf_sum, vecOf_sum]

  simp only [GlobalTheory.SgAlg.pairM, GlobalTheory.SgAlg.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Jc,
  map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
  Finset.mul_sum, sig_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply]
  ring

theorem col_last (u : D.what₂.Word) : (fun i => Pc X u i (Fin.last D.R.rS)) = crdH X (X.zu u) := by
  funext i; simp [Pc]

theorem col_cs (u : D.what₂.Word) (a : Fin D.R.rS) : (fun i => Pc X u i a.castSucc) = crdH X (X.eX a) := by
  funext i; simp [Pc]

theorem col_f (a : Fin D.R.rS) : (fun i => fc X i a) = crdH X (X.fY a) := by
  funext i; simp [fc]

theorem hT_swap_zero {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [← (VS D).herm.eq x y, h, map_zero]

theorem T_ne_zero (u : D.what₂.Word) : ((((D.mem u).A.T : ℕ) : D.host.E)) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

theorem gram_frame (u : D.what₂.Word) :
    GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (Pc X u) =
      GlobalTheory.SgAlg.TF D.R.rS (algebraMap D.host.F D.host.E (Tc u)) := by
  ext a b
  rw [pairM_apply]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rw [col_last, vecOf_crdH, X.zu_norm]; simp [GlobalTheory.SgAlg.TF, Tc]
    | cast b =>
      rw [col_last, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]
      simp [GlobalTheory.SgAlg.TF, (Fin.castSucc_ne_last b).symm]
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [col_last, col_cs, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).1]
      simp [GlobalTheory.SgAlg.TF, Fin.castSucc_ne_last a]
    | cast b =>
      rw [col_cs, col_cs, vecOf_crdH, vecOf_crdH, X.ee]
      simp [GlobalTheory.SgAlg.TF, Matrix.diagonal_apply, Fin.castSucc_ne_last a]

theorem free_frame (u : D.what₂.Word) : GlobalTheory.SgAlg.Free (Pc X u) := by
  have hT0 := T_ne_zero u
  let Y : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    Matrix.of fun i c => Fin.lastCases (crdH X (X.zu u) i) (fun a => crdH X (X.fY a) i) c
  let Dg : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    Matrix.diagonal fun c => Fin.lastCases (-(((D.mem u).A.T : ℕ) : D.host.E))⁻¹ (fun _ => 1) c
  refine ⟨Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X), ?_⟩
  have h : Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X) * Pc X u =
      Dg * GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) Y := by
    simp only [GlobalTheory.SgAlg.pairM, Matrix.mul_assoc]
  rw [h]
  ext c d
  rw [Matrix.diagonal_mul, pairM_apply]
  induction c using Fin.lastCases with
  | last =>
    have hy : (fun i => Y i (Fin.last D.R.rS)) = crdH X (X.zu u) := by funext i; simp [Y]
    induction d using Fin.lastCases with
    | last => rw [hy, col_last, vecOf_crdH, X.zu_norm]; simp [hT0]
    | cast b =>
      rw [hy, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]
      simp [(Fin.castSucc_ne_last b).symm]
  | cast a =>
    have hy : (fun i => Y i a.castSucc) = crdH X (X.fY a) := by funext i; simp [Y]
    induction d using Fin.lastCases with
    | last =>
      rw [hy, col_last, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).2]
      simp [Fin.castSucc_ne_last a]
    | cast b =>
      rw [hy, col_cs, vecOf_crdH, vecOf_crdH, ← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]

theorem dual_frame (u : D.what₂.Word) :
    GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) := by
  refine ⟨?_, ?_⟩
  · ext a b
    rw [pairM_apply, col_f, vecOf_crdH]
    induction a using Fin.lastCases with
    | last =>
      rw [col_last, vecOf_crdH, hT_swap_zero (X.zu_orth u b).2]
      simp [(Fin.castSucc_ne_last b).symm]
    | cast a =>
      rw [col_cs, vecOf_crdH, X.ef]
      simp
  · ext a b
    rw [pairM_apply, col_f, col_f, vecOf_crdH, vecOf_crdH, X.ff]
    simp

theorem aaD_eq (a : Fin D.R.rS) : aaD D a = GlobalTheory.SgGlob.dInv D.host.E (D.R.rS - a) := by
  rw [aaD, GlobalTheory.IntTerm.Conv.ddS_eq, GlobalTheory.SgGlob.dInv, ← Nat.cast_sub a.2.le, _root_.zpow_neg, _root_.zpow_natCast,
    inv_pow]

theorem tupLat_le (u : D.what₂.Word) :
    GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X := by
  rw [GlobalTheory.SnMass.tupLat, Submodule.span_le]
  rintro _ ⟨b, x, hx, rfl⟩
  show vecOf X (x • fun i => GlobalTheory.SnMass.sideM (Pc X u) (fc X) i b) ∈ (VS D).L0
  rw [LinearMap.map_smul, X.Lam_split]
  induction b using Fin.addCases with
  | left c =>
    simp only [GlobalTheory.SnMass.sideM, Fin.append_left]
    simp only [GlobalTheory.SnMass.id1, Fin.append_left] at hx
    induction c using Fin.lastCases with
    | last =>
      simp only [Fin.val_last, Nat.sub_self, GlobalTheory.SgGlob.dInv, pow_zero] at hx
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      rw [col_last, vecOf_crdH, algebraMap_smul]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.Lb.smul_mem o (X.zu_Lb u)))
    | cast a =>
      simp only [Fin.val_castSucc] at hx
      rw [← aaD_eq] at hx
      rw [col_cs, vecOf_crdH]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, x, hx, rfl⟩))
  | right a =>
    simp only [GlobalTheory.SnMass.sideM, Fin.append_right]
    simp only [GlobalTheory.SnMass.id1, Fin.append_right] at hx
    rw [← aaD_eq] at hx
    rw [col_f, vecOf_crdH]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, x, hx, rfl⟩)

end GlobalTheory.CovDom.FrameCrd

namespace GlobalTheory.CovDom


open GlobalTheory.CovDom.FrameCrd in
theorem frame_dual_lat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    GlobalTheory.SgAlg.IsFrame (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (algebraMap D.host.F D.host.E (Tc u)) (Pc X u) ∧
    GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) ∧
    GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X :=
  fun _ X u => ⟨⟨free_frame X u, gram_frame X u⟩, dual_frame X u, tupLat_le X u⟩

end GlobalTheory.CovDom
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory

theorem columnLevel_stabTriv :
    ∀ (D : D7) (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
      Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) := by
  intro D X hK u h γ hγ

  have hfin : IsOfFinOrder γ :=
    Formalism.L2.SG.PoincareInHH.Cut.gamFinKu_of X u hK
      (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) h γ hγ
  exact Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK h γ hγ hfin

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.RankVolume

theorem definiteSpaceVolume_eq_mass_of_volumeComparison (hU : ∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) :
    ∀ D : D7, Formalism.L2.Theta.RealTied D → StandardLattice.volY0 D = StandardLattice.massI D D.R.r := fun D h =>
  have hT : StandardLattice.VolTie D := Formalism.L2.Theta.VolTieG.volTie h.vol
  StandardLattice.volume_eq_mass_at_rank D (StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU D hT))
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
      (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D)))

end GlobalTheory.RankVolume
end
