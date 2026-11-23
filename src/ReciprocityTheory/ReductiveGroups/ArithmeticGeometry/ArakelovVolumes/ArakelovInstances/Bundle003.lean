module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LminorMapConj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Dsg : Fin r → ℝ := fun a => sgn X.p0 (a : ℕ)

theorem Dsg_ne (a : Fin r) : Dsg X a ≠ 0 := by
  unfold Dsg sgn
  split_ifs <;> norm_num

def Xd (z u : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (mat (nmat X z) τ)⁻¹ * KapPf.Lin X τ u

def Yd (b : Frame X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (mat b τ)⁻¹ * Xd X z u τ * mat b τ

theorem nmat_det_unit (z : V (nd X)) (τ : X.Ψ) : IsUnit (mat (nmat X z) τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (KapPf.isUnit_nmat X τ z)

theorem mat_line (x0 b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) (ζ : ℂ) :
    mat (cpt X x0 (z + ζ • u)) τ =
      mat (rmul (cpt X x0 z) b) τ * ((1 + ζ • Yd X b z u τ) * (mat b τ)⁻¹) := by
  have hBu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (hb τ).1
  have hNu := nmat_det_unit X z τ
  show mat x0 τ * mat (nmat X (z + ζ • u)) τ =
    mat x0 τ * mat (nmat X z) τ * mat b τ *
      ((1 + ζ • ((mat b τ)⁻¹ * ((mat (nmat X z) τ)⁻¹ * KapPf.Lin X τ u) * mat b τ)) * (mat b τ)⁻¹)
  rw [KapPf.nmat_eq X (z + ζ • u) τ, map_add (f := _), map_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hBu, Matrix.mul_nonsing_inv _ hBu,
    Matrix.mul_nonsing_inv_cancel_left _ _ hNu]
  rw [KapPf.nmat_eq X z τ]
  simp only [Matrix.mul_add, Matrix.mul_one]
  abel

theorem upper_inv (B : Matrix (Fin r) (Fin r) ℂ) (hBd : B.det ≠ 0) (hB : ∀ a c : Fin r, c < a → B a c = 0) :
    ∀ a c : Fin r, c < a → B⁻¹ a c = 0 := by
  intro a c hca
  have := B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hBd)
  have hBT : B.BlockTriangular id := fun i j h => hB i j h
  exact (Matrix.blockTriangular_inv_of_blockTriangular hBT) hca

theorem det_sub_map_conj (M : Matrix (Fin r) (Fin r) ℂ) {m : ℕ} (hm : m ≤ r) :
    ((M.map (starRingEnd ℂ)).submatrix (Fin.castLE hm) (Fin.castLE hm)).det =
      starRingEnd ℂ (M.submatrix (Fin.castLE hm) (Fin.castLE hm)).det := by
  rw [Matrix.submatrix_map]
  exact (RingHom.map_det _ _).symm

theorem dmin_line (x0 b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (z u : V (nd X)) (τ : X.Ψ)
    (hgram : gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (ζ : ℂ) (k : Fin (r + 1)) :
    dmin X.Gm (cpt X x0 (z + ζ • u)) τ k =
      ((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det *
        starRingEnd ℂ (Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) ζ).det *
        starRingEnd ℂ ((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
          (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det := by
  have hk := Nat.le_of_lt_succ k.isLt
  have hL : ∀ a c : Fin r, c < a → (mat b τ)⁻¹ a c = 0 :=
    upper_inv (mat b τ) (hb τ).1 (fun a c h => (hb τ).2 a c h)
  have hU : ∀ a c : Fin r, c < a → ((mat b τ)⁻¹.map (starRingEnd ℂ)) a c = 0 := by
    intro a c h
    rw [Matrix.map_apply, hL a c h, map_zero]
  have hgram' : gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) = diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ) := hgram
  have hre : ((1 + ζ • Yd X b z u τ) * (mat b τ)⁻¹)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
        ((1 + ζ • Yd X b z u τ) * (mat b τ)⁻¹).map (starRingEnd ℂ) =
      ((mat b τ)⁻¹)ᵀ * ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
        (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) * (mat b τ)⁻¹.map (starRingEnd ℂ) := by
    rw [Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  calc dmin X.Gm (cpt X x0 (z + ζ • u)) τ k
      = lminor (((mat b τ)⁻¹)ᵀ * ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
          (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) * (mat b τ)⁻¹.map (starRingEnd ℂ)) k := by
        show lminor (gram τ.1 X.Gm (mat (cpt X x0 (z + ζ • u)) τ)) k = _
        rw [mat_line X x0 b hb z u τ ζ, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, hgram', hre]
    _ = ((mat b τ)⁻¹.submatrix (Fin.castLE hk) (Fin.castLE hk)).det *
          lminor ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
            (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) k *
          (((mat b τ)⁻¹.map (starRingEnd ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det :=
        lminor_LMU _ _ _ hL hU k
    _ = _ := by
        rw [tr_D_conj, lminor_map_conj, det_sub_map_conj (mat b τ)⁻¹ hk]
        rfl

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nmat_lower (w : V (nd X)) (τ : X.Ψ) : (mat (nmat X w) τ).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := hij
  simp [mat, nmat, hij'.ne, not_lt.mpr hij'.le]

theorem ninv_lower (w : V (nd X)) (τ : X.Ψ) (x y : Fin r) (hxy : x < y) :
    Ring.inverse (mat (nmat X w) τ) x y = 0 := by
  have : Invertible (mat (nmat X w) τ) := (isUnit_nmat X τ w).invertible
  have h := Matrix.blockTriangular_inv_of_blockTriangular (nmat_lower X w τ)
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact h hxy

theorem ninv_diag (w : V (nd X)) (τ : X.Ψ) (a : Fin r) : Ring.inverse (mat (nmat X w) τ) a a = 1 := by
  have hu : IsUnit (mat (nmat X w) τ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_nmat X τ w)

  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv _ hu) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · rw [← Matrix.nonsing_inv_eq_ringInverse]
    simpa [mat, nmat] using h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have h0 : (mat (nmat X w) τ)⁻¹ k a = 0 := by
        rw [Matrix.nonsing_inv_eq_ringInverse]
        exact ninv_lower X w τ k a hlt
      rw [h0, mul_zero]
    · rw [nmat_lower X w τ hgt, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

def ninvF (w : V (nd X)) : Frame X.Ψ r := fun τ a c => Ring.inverse (mat (nmat X w) τ) a c

theorem det_lmulL_ninv (w : V (nd X)) : LinearMap.det (lmulL X (ninvF X w)) = 1 :=
  det_lmulL_unit X (ninvF X w) (fun τ a x h => ninv_lower X w τ a x h) (fun τ a => ninv_diag X w τ a)

theorem embF_lmulL (w : V (nd X)) (τ : X.Ψ) (v : V (nd X)) (x c : Fin r) :
    embF X (lmulL X (ninvF X w) (vecOf X v)) τ x c =
      (Ring.inverse (mat (nmat X w) τ) * Lin X τ v) x c := by
  have hl : ∀ (N : Frame X.Ψ r) (u : Ent X → ℂ) (e : Ent X),
      lmulL X N u e = ∑ k, N e.1 e.2.1.1 k * embF X u e.1 k e.2.1.2 := fun _ _ _ => rfl
  have hL : ∀ k c' : Fin r, Lin X τ v k c' = embF X (vecOf X v) τ k c' := fun _ _ => rfl
  rw [Matrix.mul_apply]
  by_cases h : c < x
  · rw [embF, dite_eq_left h, hl]
    rfl
  ·
    rw [embF, dite_eq_right h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : c < k
    · rw [ninv_lower X w τ x k (lt_of_le_of_lt (not_lt.mp h) hk), zero_mul]
    · rw [hL, embF, dite_eq_right hk, mul_zero]

def vecL : V (nd X) ≃ₗ[ℂ] (Ent X → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin (Ent X)))

theorem vecL_apply (v : V (nd X)) : vecL X v = vecOf X v := rfl

theorem kappa_statement_holds : KapGGStatement (E := E) := by
  intro r X x0 x1 γ U Φ bf hU hdiff hrel z hz
  obtain ⟨hdom, hbor, -⟩ := hrel z hz
  set Φ' := fderiv ℂ Φ z with hΦ'
  have hΦ : HasFDerivAt Φ Φ' z := ((hdiff z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt

  have hmat : ∀ z' ∈ U, ∀ τ : X.Ψ, mat x0 τ * mat (nmat X z') τ =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ) *
        (mat (nmat X (Φ z')) τ * mat (bf z') τ) := by
    intro z' hz' τ
    have h := congrFun (hrel z' hz').2.2 τ
    change mat x0 τ * mat (nmat X z') τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((mat x1 τ * mat (nmat X (Φ z')) τ) * mat (bf z') τ) at h
    rw [h]
    simp only [Matrix.mul_assoc]

  have hG : ∀ τ : X.Ψ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ).det := by
    intro τ
    have h0 : (mat x0 τ * mat (nmat X z) τ).det ≠ 0 := (hdom τ).1
    rw [hmat z hz τ, Matrix.det_mul] at h0
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h0)
  have hrel' : ∀ τ : X.Ψ, ∀ z' ∈ U, mat (nmat X (Φ z')) τ * mat (bf z') τ =
      (((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ)⁻¹ * mat x0 τ) * mat (nmat X z') τ := by
    intro τ z' hz'
    rw [Matrix.mul_assoc, hmat z' hz' τ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hG τ),
      Matrix.one_mul]
  have hup : ∀ τ : X.Ψ, ∀ z' ∈ U, ∀ a c : Fin r, c < a → mat (bf z') τ a c = 0 :=
    fun τ z' hz' a c h => ((hrel z' hz').2.1 τ).2 a c h
  set b := bf z with hb

  have key : (rmulL X b) ∘ₗ (lmulL X (ninvF X (Φ z))) ∘ₗ
      ((vecL X : V (nd X) →ₗ[ℂ] (Ent X → ℂ)) ∘ₗ (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ
        ((vecL X).symm : (Ent X → ℂ) →ₗ[ℂ] V (nd X))) =
      (lmulL X b) ∘ₗ (lmulL X (ninvF X z)) := by
    refine LinearMap.ext fun u => funext fun e => ?_
    obtain ⟨h, rfl⟩ : ∃ h, vecL X h = u := ⟨(vecL X).symm u, (vecL X).apply_symm_apply u⟩
    rcases e with ⟨τ, ⟨⟨a, c⟩, hca⟩⟩
    have hld := lower_deriv X τ _ U hU Φ (fun z' => mat (bf z') τ) (hrel' τ) (hup τ) z hz Φ' hΦ h a c hca
    rw [Matrix.sub_apply, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply] at hld
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe]
    simp only [vecL_apply]
    show ∑ y, embF X (lmulL X (ninvF X (Φ z)) (vecOf X (Φ' h))) τ a y * b τ y c =
      ∑ x, b τ a x * embF X (lmulL X (ninvF X z) (vecOf X h)) τ x c
    simp only [embF_lmulL]
    exact hld.symm
  have hdet := congrArg LinearMap.det key
  simp only [LinearMap.det_comp, LinearMap.det_conj, det_lmulL_ninv, one_mul] at hdet
  have hupb : ∀ τ a x, x < a → b τ a x = 0 := fun τ a x h => (hbor τ).2 a x h
  rw [det_lmulL_upper X b hupb, det_rmulL_upper X b hupb] at hdet

  have hd : ∀ τ a, b τ a a ≠ 0 := by
    intro τ a
    have h0 := (hbor τ).1
    rw [Matrix.det_of_isUpperTriangular (M := mat b τ) (fun i j h => (hbor τ).2 i j h)] at h0
    exact Finset.prod_ne_zero_iff.mp h0 a (Finset.mem_univ a)
  have hcol : ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e _ => hd _ _
  rw [bchar_kap X b hd]
  show LinearMap.det (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) = _
  exact eq_div_of_mul_eq hcol (by rw [mul_comm, hdet, mul_one])

end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
end
end
