module

public import Formalism.LocalToGlobal.HermitianForms.Bundle009
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle006
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.HformSmulRightB
public import Formalism.LocalToGlobal.GlobalTheory.Bundle002
import Formalism.LocalToGlobal.HermitianForms.Bundle004
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle004
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
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

@[expose] public section

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

theorem span_of_cols {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hA : Function.Injective A.mulVec) (hz : ∀ x, A *ᵥ x ≠ z) :
    ∀ y, ∃ (x : Fin n → E) (s : E), y = A *ᵥ x + s • z := by
  subst hN
  intro y
  have hB := isUnit_det_cols rfl A z hA hz
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
    Matrix.of (fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) with hBdef
  set w := B⁻¹ *ᵥ y with hw
  have hy : B *ᵥ w = y := by rw [hw, mulVec_mulVec, mul_nonsing_inv _ hB, one_mulVec]
  refine ⟨fun i => w (Fin.castSucc i), w (Fin.last n), ?_⟩
  rw [← hy]
  funext a
  simp only [hBdef, mulVec, dotProduct, Fin.sum_univ_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, of_apply,
    Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, Fin.eta]
  ring

variable (D : D7)

theorem conj_sigD (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ ((sigD D : D.host.E →+* D.host.E) x) = (starRingEnd ℂ) (φ x) := by
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram.2.1 φ x

theorem zc_not_range (x : Fin (D.R.N D.R.m - 1) → D.host.E) : iXm D *ᵥ x ≠ zc D := by
  letI := D.host.cmStar
  intro h
  have h1 := hform_iXc_zc D x
  simp only [iXm, LinearMap.toMatrix'_mulVec] at h
  rw [h, zc_eq, hform_crdM] at h1
  exact D.sp.z_anis h1

theorem span_iXc_zc : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • zc D := by
  intro y
  obtain ⟨x, s, h⟩ := span_of_cols (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (zc D) (iXm_mulVec_injective D) (zc_not_range D) y
  refine ⟨x, s, ?_⟩
  rw [h]
  simp only [iXm, LinearMap.toMatrix'_mulVec]

variable {D}

theorem defN_of_fact {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (C : GL (Fin n) D.host.E)
    (hC : cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = J) (φ : D.host.E →+* ℂ) (x : Fin n → D.host.E) :
    ∃ r : ℝ, 0 ≤ r ∧ φ (hform (sigD D : D.host.E →+* D.host.E) J x x) = r ∧ (r = 0 → x = 0) := by
  have e1 : hform (sigD D : D.host.E →+* D.host.E) J x x =
      ∑ a, (sigD D : D.host.E →+* D.host.E) ((C.1 *ᵥ x) a) * (C.1 *ᵥ x) a := by
    rw [← hC, ← Matrix.mul_one (cT (sigD D : D.host.E →+* D.host.E) C.1), ← Formalism.L2.GlobalTheoryTheory.Comp.hform_mulVec_rect]
    simp only [hform, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨∑ a, Complex.normSq (φ ((C.1 *ᵥ x) a)), Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _), ?_, ?_⟩

  · rw [e1, map_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_mul, conj_sigD, Complex.normSq_eq_conj_mul_self]
  · intro h0
    have hz : C.1 *ᵥ x = 0 := by
      funext a
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).mp h0 a (Finset.mem_univ _)
      rw [Complex.normSq_eq_zero, map_eq_zero] at this
      exact this
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    calc x = C.1⁻¹ *ᵥ (C.1 *ᵥ x) := by rw [mulVec_mulVec, nonsing_inv_mul _ hCi, one_mulVec]
      _ = 0 := by rw [hz, mulVec_zero]

variable {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem crdFacts_of (Tf : FormsTiedSym D u Ch chOf) : CrdFacts D := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  exact
    { conj := conj_sigD D
      defN := fun φ x => defN_of_fact (gramN D D.R.m le_rfl) C hC φ x
      iso := hform_iXc D
      orth := fun x => ⟨hform_iXc_zc D x, hform_zc_iXc D x⟩
      span := span_iXc_zc D }

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

section Gen

theorem inJSym_restrict {κ : Type} [Field κ] {n : ℕ} {k rS t : ℕ} {zl : Bool} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ)
    (R : Matrix (Fin n) (Fin n) κ) (hR : ∀ x y, R x y = M x.castSucc y.castSucc) (h : InJSym k rS t zl M) :
    InJSym k rS t false R := by
  obtain ⟨h1, h2, h3, -⟩ := h
  refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun h => absurd h Bool.false_ne_true⟩
  · rw [hR]; exact h1 _ _ (by simpa only [Fin.val_castSucc] using hxy)
  · rw [hR]; exact h2 _ (by simpa only [Fin.val_castSucc] using hx)
  · rw [hR]; exact h3 _ _ (by simpa only [Fin.val_castSucc] using hx) (by simpa only [Fin.val_castSucc] using hy)

theorem jsym_of_blk {κ : Type} [Field κ] {n N : ℕ} (hN : n + 1 = N) {k rS t : ℕ} (Mm : GL (Fin N) κ)
    (hMm : Mm ∈ JSymG κ N k rS t true) (R : Matrix (Fin n) (Fin n) κ)
    (hR : ∀ x y : Fin n, R x y = Mm.1 ⟨x, by omega⟩ ⟨y, by omega⟩) :
    ∃ M ∈ JSymG κ n k rS t false, M.1 = R := by
  subst hN
  obtain ⟨h1, h2⟩ := hMm
  have hRc : ∀ x y : Fin n, R x y = Mm.1 x.castSucc y.castSucc := fun x y => hR x y
  set R' : Matrix (Fin n) (Fin n) κ := fun x y => (Mm⁻¹ : GL (Fin (n + 1)) κ).1 x.castSucc y.castSucc with hR'
  have hl : ∀ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ), InJSym k rS t true M → ∀ x : Fin n,
      M x.castSucc (Fin.last n) = 0 := by
    intro M hM x
    have := (hM.2.2.2 rfl x.castSucc (Fin.last n) (by simp)).1
    simpa [Fin.castSucc_ne_last] using this
  have hmul : ∀ (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) κ), InJSym k rS t true A → ∀ x y : Fin n,
      (A * B) x.castSucc y.castSucc = ∑ j : Fin n, A x.castSucc j.castSucc * B j.castSucc y.castSucc := by
    intro A B hA x y
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, hl A hA x, zero_mul, add_zero]
  have e1 : R * R' = 1 := by
    ext x y
    have := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ => M x.castSucc y.castSucc)
      (show Mm.1 * (Mm⁻¹).1 = 1 from Mm.mul_inv)
    rw [hmul _ _ h1] at this
    rw [Matrix.mul_apply]
    simp only [hRc, hR']
    rw [this]
    change (if x.castSucc = y.castSucc then (1 : κ) else 0) = (if x = y then 1 else 0)
    simp only [Fin.castSucc_inj]
  have e2 : R' * R = 1 := by
    ext x y
    have := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ => M x.castSucc y.castSucc)
      (show (Mm⁻¹).1 * Mm.1 = 1 from Mm.inv_mul)
    rw [hmul _ _ h2] at this
    rw [Matrix.mul_apply]
    simp only [hRc, hR']
    rw [this]
    change (if x.castSucc = y.castSucc then (1 : κ) else 0) = (if x = y then 1 else 0)
    simp only [Fin.castSucc_inj]
  refine ⟨⟨R, R', e1, e2⟩, ⟨?_, ?_⟩, rfl⟩
  · exact inJSym_restrict _ R hRc h1
  · exact inJSym_restrict _ R' (fun x y => rfl) h2

theorem blk_conj {K : Type} [CommRing K] {n N : ℕ} (hN : n + 1 = N) (gm Fm Fm' : Matrix (Fin N) (Fin N) K) (hFm : Fm' * Fm = 1)
    (A : Matrix (Fin N) (Fin n) K) (Fp gk M' : Matrix (Fin n) (Fin n) K) (hM' : Fp * M' = gk * Fp)
    (hgA : gm * A = A * gk) (w : Fin N → K) (hgw : gm *ᵥ w = w)
    (hF1 : ∀ x (b : Fin n) (b' : Fin N), (b : ℕ) = b' → Fm x b' = (A * Fp) x b)
    (hF2 : ∀ x (l : Fin N), (l : ℕ) + 1 = N → Fm x l = w x) :
    ∀ x y : Fin n, (Fm' * gm * Fm) ⟨x, by omega⟩ ⟨y, by omega⟩ = M' x y := by
  subst hN
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of (fun x y : Fin (n + 1) =>
    if h : (x : ℕ) < n ∧ (y : ℕ) < n then M' ⟨x, h.1⟩ ⟨y, h.2⟩ else if (x : ℕ) = y then 1 else 0) with hB
  have hne : ∀ j : Fin n, (j : ℕ) ≠ n := fun j => j.is_lt.ne
  have key : gm * Fm = Fm * B := by
    ext x y
    refine Fin.lastCases ?_ (fun y' => ?_) y
    · have e1 : (gm * Fm) x (Fin.last n) = w x := by
        rw [← congrFun hgw x, Matrix.mul_apply]
        simp only [mulVec, dotProduct]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF2 j (Fin.last n) (by simp)])
      rw [e1, Matrix.mul_apply, Fin.sum_univ_castSucc]
      simp [hB, hne, hF2 x (Fin.last n) (by simp)]
    · have eL : (gm * Fm) x y'.castSucc = (A * (Fp * M')) x y' := by
        rw [hM', ← Matrix.mul_assoc, ← hgA, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF1 j y' y'.castSucc (by simp)])
      have eR : (Fm * B) x y'.castSucc = ((A * Fp) * M') x y' := by
        rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mul_apply]
        have hlast : B (Fin.last n) y'.castSucc = 0 := by
          simp [hB, (hne y').symm]
        rw [hlast, mul_zero, add_zero]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hF1 x j j.castSucc (by simp)]
        simp [hB]
      rw [eL, eR, Matrix.mul_assoc]
  intro x y
  have e : Fm' * gm * Fm = B := by rw [Matrix.mul_assoc, key, ← Matrix.mul_assoc, hFm, Matrix.one_mul]
  rw [e]
  simp [hB]

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem redM_entry {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m m' : ℕ}
    (X : Matrix (Fin m) (Fin m) (v.adicCompletion F)) (Y : Matrix (Fin m') (Fin m') (v.adicCompletion F))
    (a b : Fin m) (a' b' : Fin m') (h : X a b = Y a' b') : redM F v X a b = redM F v Y a' b' := by
  simp only [redM, h]
  by_cases hY : Y a' b' ∈ v.adicCompletionIntegers F
  · rw [dite_eq_left (by rw [h]; exact hY), dite_eq_left hY]
  · rw [dite_eq_right (by rw [h]; exact hY), dite_eq_right hY]



theorem lev_bad (Tf : FormsTiedSym D u Ch chOf) (K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) K.1 G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hlev : bc (prV (E := D.host.E) v) K ∈ levelVL (sigD D) (gramP D) v Tf.clsP.lev.Lb)
    (i : Fin 2) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal) :
    bc (prV (E := D.host.E) v) K ∈ Tf.clsP.lev.Uloc v := by
  set Km := (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev
  rw [Tf.glevP.mem i v h _ hlev]
  have hGv : bc (prV (E := D.host.E) v) G ∈ Km.Uloc v := ((Km.U_eq G).1 hG).2 v
  obtain ⟨Mm, hMm, hMmeq⟩ := (Tf.glevM.mem i v h _ (Km.Uloc_lev v hGv)).1 hGv
  obtain ⟨hEv1, hEv2⟩ := isExt_prV v hE
  obtain ⟨hF1, hF2⟩ := Tf.frExt i v h
  have hmatG : Tf.gl.mat i v h (Tf.glevM.fr i v h) (bc (prV (E := D.host.E) v) G) =
      ((Tf.glevM.fr i v h)⁻¹ : GL _ _).1 * (G.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevM.fr i v h).1 := by
    simp only [GLoc.mat, Units.val_mul]; rfl
  have hmatK : Tf.gl.mat i v h (Tf.glevP.fr i v h) (bc (prV (E := D.host.E) v) K) =
      ((Tf.glevP.fr i v h)⁻¹ : GL _ _).1 * (K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevP.fr i v h).1 := by
    simp only [GLoc.mat, Units.val_mul]; rfl
  have hb := blk_conj (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R)
    ((G.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h)) (Tf.glevM.fr i v h).1 ((Tf.glevM.fr i v h)⁻¹ : GL _ _).1
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    ((iXm D).map ((Tf.gl.phi i v h).comp (inclE (F := D.host.F) (v.adicCompletion D.host.F))))
    (Tf.glevP.fr i v h).1 ((K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h))
    (((Tf.glevP.fr i v h)⁻¹ : GL _ _).1 * (K.1.map (prV (E := D.host.E) v)).map (Tf.gl.phi i v h) * (Tf.glevP.fr i v h).1)
    (by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul])
    (by
      have := congrArg (fun M => M.map (Tf.gl.phi i v h)) hEv1
      simp only [Matrix.map_mul, Matrix.map_map] at this
      rw [RingHom.coe_comp]
      exact this)
    (fun a => Tf.gl.phi i v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) (Tf.til.z0 a)))
    (by
      funext a
      exact (RingHom.map_mulVec (Tf.gl.phi i v h) _ _ a).symm.trans (congrArg (fun w => Tf.gl.phi i v h (w a)) hEv2))
    hF1 hF2
  refine jsym_of_blk (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) Mm hMm _ (fun x y => ?_)
  rw [hMmeq]
  refine redM_entry v _ _ _ _ _ _ ?_
  rw [hmatK, hmatG]
  exact (hb x y).symm



theorem lev_mem (Tf : FormsTiedSym D u Ch chOf) (K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) K.1 G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) : K ∈ Tf.clsP.lev.U := by
  have hU : K ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := lev_unit Tf K.1 G hE hG
  rw [Tf.clsP.lev.U_eq]
  refine ⟨hU, fun v => ?_⟩
  have hu := Formalism.UG.P.base_change_mem_holds _ _ _ (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (sigR (sigD D) (v.adicCompletion D.host.F)) (prV (E := D.host.E) v)
    (Formalism.UG.P.afsplit_prV_comp_sigR (sigD D) v) _ K hU
  have e : ((gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))).map (prV (E := D.host.E) v) =
      (gramP D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) := by
    rw [Matrix.map_map]; rfl
  rw [e] at hu
  have hlev : bc (prV (E := D.host.E) v) K ∈ levelVL (sigD D) (gramP D) v Tf.clsP.lev.Lb :=
    Subgroup.mem_inf.mpr ⟨hu, fun x => lev_lat Tf K.1 G hE hG v x⟩
  by_cases hv : v ∈ badG D
  · obtain ⟨i, hi⟩ : ∃ i : Fin 2, (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal := by
      rcases hv with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
    exact lev_bad Tf K G hE hG v hlev i hi
  · have h1 : ((1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
      rw [Nat.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    rw [Tf.clsP.lev.Uloc_hyp v hv h1]
    exact hlev

end Formalism.L2.GlobalTheoryTheory.Br
end
end
