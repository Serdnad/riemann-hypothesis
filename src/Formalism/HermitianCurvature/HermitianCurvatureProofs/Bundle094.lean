module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle088
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.AdjugateLastEntrySum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.FixOfPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HermBvecEI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

set_option linter.unusedSimpArgs false

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellDiagonalMap

variable {k j ρ : ℕ}

theorem leviElement_mul_mMap (W Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) (hW : IsUnit W.det) :
    muP k j ρ W * mMap k j ρ Z γ = mMap k j ρ (Wᴴ⁻¹ * Z) γ := by
  unfold mMap muP
  rw [Ux3.block3_mul]
  have h13 : W * (Zᴴ⁻¹ * G.wMat j) = (Wᴴ⁻¹ * Z)ᴴ⁻¹ * G.wMat j := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hW, Matrix.mul_assoc]
  have h31 : G.wMat j * Wᴴ⁻¹ * G.wMat j * (G.wMat j * Z) = G.wMat j * (Wᴴ⁻¹ * Z) := by
    rw [Matrix.mul_assoc, Ux4.w_w_mul, Matrix.mul_assoc]
  congr 1 <;> simp [h13, h31]

theorem leviElement_nset (p : Matrix (Fin j) (Fin j) ℂ) (hp : Formalism.DoubleCosetMeasures.IsUpUni p) : muP k j ρ p ∈ Nset k (j + ρ) := by
  have hdet : p.det ≠ 0 := by rw [Formalism.DoubleCosetMeasures.isUpUni_det ℂ hp]; exact one_ne_zero
  refine ⟨(Formalism.FourierDecayAlt.P.slice_membership k j ρ).2.1 p hdet, ?_, ?_⟩
  · intro a i hai
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, hy⟩ := (eB k j ρ).surjective (eI k (j + ρ) a)
    unfold muP
    rw [← hy, Ux3.block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    have hv := congrArg Fin.val hy
    have ha := a.isLt
    simp only [eI] at hv
    rw [← hv] at hai
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hv hai
    all_goals first
      | (exfalso; have := x.isLt; have := y.isLt; omega)
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | skip

    simp only [Matrix.fromBlocks_apply₁₁, Sum.inl.injEq]
    rcases eq_or_lt_of_le hai with h | h
    · have : x = y := Fin.ext h.symm
      subst this; simp [hp.2]
    · have hne : x ≠ y := fun e => by subst e; omega
      rw [if_neg hne]
      exact hp.1 (show y < x from h)
  · intro i c hc1 hc2 hi
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, rfl⟩ := (eB k j ρ).surjective c
    unfold muP
    rw [Ux3.block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hc1 hc2 hi <;>
      first
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | (exfalso; have := x.isLt; have := y.isLt; omega)

def eW (k : ℕ) : Fin (2 * 0 + k + 1) ≃ Fin (k + 1) := finCongr (by omega)

def muOf (γ : B.Mat k 0) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.reindex (eW k) (eW k) γ

theorem hb_eq (k : ℕ) : Hb k = Matrix.reindex (eW k) (eW k) (Hpk k 0) := by
  ext i j
  simp only [Hb, Hpk, eW, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, finCongr_symm,
    finCongr_apply, Fin.coe_cast, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | omega

theorem muOf_mem (γ : B.Mat k 0) (hγ : γ ∈ B.GV k 0) : (muOf γ)ᴴ * Hb k * muOf γ = Hb k := by
  have h : γᴴ * Hpk k 0 * γ = Hpk k 0 := hγ
  rw [hb_eq]
  simp only [muOf, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, h]

theorem inv_diag {r : ℕ} (v : Fin r → ℂ) (hv : ∀ a, v a ≠ 0) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun a => (v a)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  exact inv_mul_cancel₀ (hv a)

theorem mMap_diag (r : ℕ) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ : B.Mat k 0) :
    (mMap k r 0 (Matrix.diagonal d) γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      bigCell k r d (muOf γ) := by
  ext i l
  obtain ⟨x, rfl⟩ := (eB k r 0).surjective i
  obtain ⟨y, rfl⟩ := (eB k r 0).surjective l
  unfold mMap
  rw [Matrix.diagonal_conjTranspose, inv_diag (star d) (fun a => by simpa [Pi.star_apply] using hd a), Ux3.block3_apply]
  have v1 := @Ux3.block_index_first_val k r 0
  have v2 := @Ux3.block_index_middle_val k r 0
  have v3 := @Ux3.block_index_last_val k r 0
  rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
    simp only [bigCell, v1, v2, v3, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply]
  all_goals
    have hx := x.isLt
    have hy := y.isLt
    simp only [Fin.ext_iff, v1, v2, v3, esI, G.wMat, Matrix.of_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Ring.inverse_eq_inv', Pi.star_apply, Fin.val_rev, Pi.inv_apply, Complex.star_def, mul_one,
      one_mul, mul_zero, zero_mul]
    split_ifs <;> first
      | rfl
      | (exfalso; omega)
      | (congr 1; ext; simp only [Fin.val_mk]; omega)
      | (congr 2; ext; simp only [Fin.val_mk]; omega)
      | (intro h; exfalso; omega)
      | (simp; done)
      | (simp only [mul_one]; congr 3; ext; simp only [Fin.val_mk]; omega)
      | (simp only [muOf, eW, Matrix.reindex_apply, Matrix.submatrix_apply]; congr 1 <;> (ext; simp))
      | skip

theorem dmin_lead {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (l : ℕ) (hl : l ≤ r) : Dmin k r z z' g ⟨l, by omega⟩ = Formalism.FourierDecayAlt.S3.lead (Zh k r 0 g) l hl := by
  unfold Dmin Formalism.FourierDecayAlt.S3.lead
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  rw [Ux3.zhat_apply_low]
  · rfl
  · simp; omega
  · simp; omega

theorem cellDecomp : BigCellDecomposition.CellDecomp := by
  intro k r z z' g hg hD
  have hDl : ∀ (l : ℕ) (hl : l ≤ r), Formalism.FourierDecayAlt.S3.lead (Zh k r 0 g) l hl ≠ 0 := fun l hl => by
    rw [← dmin_lead z z' g l hl]; exact hD ⟨l, by omega⟩ hl
  have hDj : DjU k r 0 g ≠ 0 := by
    have h := Formalism.FourierDecayAlt.P.hat_z_minimum_degree k r 0 z z' g
    rw [← h]; exact hD ⟨r, by omega⟩ le_rfl
  obtain ⟨x, x', Z, γ, _hZ, hγ, hgeq⟩ := Ux3.bigCell_exists (k := k) (j := r) (ρ := 0) g hg hDj
  have hZh : Zh k r 0 g = Z := by rw [hgeq]; exact Formalism.FourierDecayAlt.P.hat_z_on_slice k r 0 x x' Z γ
  have hDZ : ∀ (l : ℕ) (hl : l ≤ r), Formalism.FourierDecayAlt.S3.lead Z l hl ≠ 0 := by rw [← hZh]; exact hDl
  obtain ⟨L, U, d, hL, hU, hLDU, hlead⟩ :=
    Formalism.FourierDecayAlt.P.ldu_decomposition_exists ℂ r Z (fun l hl => (hDZ l hl.le).isUnit)
  have hd : ∀ a, d a ≠ 0 := fun a h0 => by
    have h1 := hlead a.val a.isLt
    rw [h0, zero_mul] at h1
    exact hDZ (a.val + 1) a.isLt h1
  have hLh : Formalism.DoubleCosetMeasures.IsUpUni Lᴴ := by
    refine ⟨fun i j hij => ?_, fun a => ?_⟩
    · rw [Matrix.conjTranspose_apply, hL.1 hij, star_zero]
    · rw [Matrix.conjTranspose_apply, hL.2 a, star_one]
  have hLu : IsUnit L.det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det ℂ hL]; exact isUnit_one
  have hLhu : IsUnit Lᴴ.det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det ℂ hLh]; exact isUnit_one
  have hP : muP k r 0 Lᴴ ∈ Nset k (r + 0) := leviElement_nset _ hLh
  have hPu : IsUnit (muP k r 0 Lᴴ).det := Ux3.gv_det hP.1
  have h1 : muP k r 0 Lᴴ * mMap k r 0 Z γ = mMap k r 0 (Matrix.diagonal d) γ * muP k r 0 U := by
    rw [leviElement_mul_mMap _ _ _ hLhu, Ux4.mMap_mul_muP, hLDU, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu, Matrix.one_mul]
  have key : mMap k r 0 Z γ = (muP k r 0 Lᴴ)⁻¹ * (mMap k r 0 (Matrix.diagonal d) γ * muP k r 0 U) := by
    rw [← h1, Matrix.nonsing_inv_mul_cancel_left _ _ hPu]
  refine ⟨muP k r 0 Lᴴ * Rn k r 0 x, WeylGroupFacts.mem_n_mul hP (Ux3.rn_nset x),
    muP k r 0 U * Rn k r 0 x', WeylGroupFacts.mem_n_mul (leviElement_nset _ hU) (Ux3.rn_nset x'), d, hd, muOf γ, muOf_mem γ hγ, ?_⟩
  rw [hgeq, key, ← mMap_diag r d hd γ, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.BigCellDiagonalMap

namespace Formalism.FourierDecayAlt.P

theorem big_cell_decomposition : BigCellDecomposition.CellDecomp := by
  exact BigCellDiagonalMap.cellDecomp

theorem psiOnto_true : Formalism.FourierDecayAlt.JF.PsiOnto := jf_psiOnto_of_cellDecomp BigCellDiagonalMap.cellDecomp

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

namespace DU

variable {k r : ℕ}

theorem hadd_l {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (x y w : Fin m → ℂ) :
    herm H (x + y) w = herm H x w + herm H y w := by
  simp [herm, Matrix.mulVec_add]

theorem hadd_r {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (x w w' : Fin m → ℂ) :
    herm H x (w + w') = herm H x w + herm H x w' := by
  simp [herm, add_dotProduct]

theorem hsmul_l {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (x w : Fin m → ℂ) :
    herm H (c • x) w = c * herm H x w := by
  simp [herm, Matrix.mulVec_smul]

theorem hsmul_r {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (x w : Fin m → ℂ) :
    herm H x (c • w) = conj c * herm H x w := by
  simp [herm, smul_dotProduct, Complex.star_def]

private theorem herm_swap_eq_zero_of_eq_zero {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : ∀ i j, H i j = star (H j i))
    (v w : Fin m → ℂ) : herm H w v = conj (herm H v w) := by

  simp only [herm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hH b a]
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_conj]
  ring

private theorem Hpk_apply_eq_star_apply_swap : ∀ i j : Fin (2 * r + k + 1), Hpk k r i j = star (Hpk k r j i) := by
  intro i j
  simp only [Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | (exfalso; omega)

theorem hswap (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) w v = conj (herm (Hpk k r) v w) := by
  exact herm_swap_eq_zero_of_eq_zero _ Hpk_apply_eq_star_apply_swap v w

theorem blockProjection_of_mem_block {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : SSn.wbP k r v = v := by
  funext i
  simp only [SSn.wbP]
  split_ifs with h
  · rfl
  · exact (hv i (by omega)).symm

theorem prWv_of {z v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    SSn.prWv k r z v = v + (herm (Hpk k r) v z / (Tz k r z : ℂ)) • z := by
  simp only [SSn.prWv, blockProjection_of_mem_block hv]

theorem prWv_fix {z x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (h0 : herm (Hpk k r) x z = 0) :
    SSn.prWv k r z x = x := by
  rw [prWv_of hx, h0]
  simp

private theorem herm_Hpk_self_eq_neg_Tz (z : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := hswap (k := k) (r := r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.conj_im] at h2
    simp
    linarith

theorem prWv_perp {z y : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hy : inWb k r y) :
    herm (Hpk k r) (SSn.prWv k r z y) z = 0 := by
  have hT0 : (Tz k r z : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [prWv_of hy, hadd_l, hsmul_l, herm_Hpk_self_eq_neg_Tz]
  have h1 : herm (Hpk k r) y z / (Tz k r z : ℂ) * -(Tz k r z : ℂ) = -herm (Hpk k r) y z := by
    rw [div_mul_eq_mul_div, mul_neg, neg_div, mul_div_assoc, div_self hT0, mul_one]
  rw [h1]
  ring

theorem prWv_inWb {z y : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hy : inWb k r y) :
    inWb k r (SSn.prWv k r z y) := by
  intro i hi
  have h1 : SSn.wbP k r y i = 0 := by
    simp only [SSn.wbP]
    rw [if_neg]
    omega
  simp only [SSn.prWv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz i hi, h1, mul_zero, add_zero]

private theorem herm_Hpk_self_self_eq_neg_ofReal_Tz (z : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := hswap (k := k) (r := r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.conj_im] at h2
    simp
    linarith

theorem prWv_norm {z y : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hy : inWb k r y) {ζ : ℂ} {T' : ℝ}
    (hyy : herm (Hpk k r) y y = -(T' : ℂ)) (hyz : herm (Hpk k r) y z = ζ) :
    herm (Hpk k r) (SSn.prWv k r z y) (SSn.prWv k r z y) =
      ((Complex.normSq ζ / Tz k r z - T' : ℝ) : ℂ) := by
  have hT0 : (Tz k r z : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [prWv_of hy]
  simp only [hadd_l, hadd_r, hsmul_l, hsmul_r, herm_Hpk_self_self_eq_neg_ofReal_Tz, hyy, hyz]
  rw [hswap y z, hyz, map_div₀, Complex.conj_ofReal]
  push_cast
  rw [← Complex.mul_conj]
  field_simp
  ring

theorem unitH_facts {z x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (h0 : herm (Hpk k r) x z = 0) {s : ℝ}
    (hs : 0 < s) (hxx : herm (Hpk k r) x x = (s : ℂ)) :
    SSn.prWv k r z (SSn.unitH k r x) = SSn.unitH k r x ∧ herm (Hpk k r) (SSn.unitH k r x) (SSn.unitH k r x) = 1 := by
  have hu : SSn.unitH k r x = (((Real.sqrt s)⁻¹ : ℝ) : ℂ) • x := by
    simp only [SSn.unitH, hxx, Complex.ofReal_re]
  have hin : inWb k r (SSn.unitH k r x) := by
    intro i hi
    rw [hu]
    simp [hx i hi]
  refine ⟨prWv_fix hin ?_, ?_⟩
  · rw [hu, hsmul_l, h0, mul_zero]
  · rw [hu, hsmul_l, hsmul_r, hxx, Complex.conj_ofReal]
    have key : (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * s) = 1 := by
      rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hs.le, inv_mul_cancel₀ hs.ne']
    exact_mod_cast key

theorem base {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    SSn.prWv k r z (SSn.nu0 k r z z' μsec ζ) = SSn.nu0 k r z z' μsec ζ ∧
      herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) (SSn.nu0 k r z z' μsec ζ) = 1 ∧
      SSn.prWv k r z' (SSn.nu0' k r z z' μsec ζ) = SSn.nu0' k r z z' μsec ζ ∧
      herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) (SSn.nu0' k r z z' μsec ζ) = 1 := by
  have hm := NFRadRedA.muZ_uwb hsec hζ
  have hG := NFRadRedA.uwb_glev hm
  have hU : NF.muZ k r μsec ζ ∈ UH (Hpk k r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hUi : (NF.muZ k r μsec ζ)⁻¹ ∈ UH (Hpk k r) := hGi.1
  have hyz : herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') z = ζ := by
    rw [← NFRadRedA.zeta_eq]; exact NFRadRedA.zeta_muZ hz hz' hsec hζ
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hyy : herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') (NF.muZ k r μsec ζ *ᵥ z') = -((Tz k r z' : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hU, FrameEntries.herm_self]
  have hyyi : herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) =
      -((Tz k r z : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hUi, FrameEntries.herm_self]
  have hyzi : herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) z' = conj ζ := by
    rw [hswap, ← FrameEntries.herm_inv hU, hyz]
  have hpos : 0 < Complex.normSq ζ / Tz k r z - Tz k r z' := by
    rw [sub_pos, lt_div_iff₀ hT]; linarith
  have hposi : 0 < Complex.normSq (conj ζ) / Tz k r z' - Tz k r z := by
    rw [Complex.normSq_conj, sub_pos, lt_div_iff₀ hT']; linarith
  obtain ⟨h1, h2⟩ := unitH_facts (prWv_inWb hz hy) (prWv_perp hT hy) hpos (prWv_norm hT hy hyy hyz)
  obtain ⟨h3, h4⟩ := unitH_facts (prWv_inWb hz' hyi) (prWv_perp hT' hyi) hposi (prWv_norm hT' hyi hyyi hyzi)
  exact ⟨h1, h2, h3, h4⟩

end DU

theorem datum_unit_norm_holds : DatumUnit := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v ζ hζ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hζ' : Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' < Complex.normSq ζ := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; exact hζ
  exact DU.base hPl.2.1 hPl.2.2.1 (T v).base.T_pos (T v).base.T'_pos (T v).base.sec hζ'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.GsFr
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S2

variable {k r : ℕ}

private theorem herm_hpk_mulVec_of_mem_uh {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v w := by
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show star (h *ᵥ w) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (h *ᵥ v)) = star w ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']

lemma unitH_UH {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v : Fin (2 * r + k + 1) → ℂ) :
    unitH k r (h *ᵥ v) = h *ᵥ unitH k r v := by
  show ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ v)).re)⁻¹ : ℝ) : ℂ) • (h *ᵥ v)) =
    h *ᵥ ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ : ℝ) : ℂ) • v)
  rw [herm_hpk_mulVec_of_mem_uh hh, Matrix.mulVec_smul]

lemma omW_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (g : B.Mat k r) :
    omW k r z z' (n * g * n') = omW k r z z' g := by
  show prW k r z (xcof k r z z' (n * g * n')) = prW k r z (xcof k r z z' g)
  rw [xcof_N hz hz' hn hn' g]
  exact prW_N hn (fun a => xcof_esI z z' g a)

lemma omW'_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    omW' k r z z' (n * g * n') = omW' k r z z' g := by
  have hh : nᴴ * Hpk k r * n = Hpk k r := hn.1
  have hleft : (Hpk k r * nᴴ * Hpk k r) * n = 1 := by
    calc (Hpk k r * nᴴ * Hpk k r) * n = Hpk k r * (nᴴ * Hpk k r * n) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh, WeylGroupFacts.hpk_sq]
  have hnn : n⁻¹ * n = 1 := by
    rw [Matrix.inv_eq_left_inv hleft]
    exact hleft
  show prW k r z' ((n * g * n')⁻¹ *ᵥ xcofL k r z z' (n * g * n')) = prW k r z' (g⁻¹ *ᵥ xcofL k r z z' g)
  rw [xcofL_N hz hz' hn hn' g, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.mul_assoc, hnn, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  exact prW_N (WeylGroupFacts.mem_n_inv hn') (fun a => ginv_xcofL_esI z z' hg a)

end S2

open S2 in
theorem geometry_equivariance_first_vector : GeomEqvNu := by
  intro k r z z' _ hz hz' h hh n hn h' hh' n' hn' g hg
  have hy : h⁻¹ * n⁻¹ * g * n' * h' = h⁻¹ * (n⁻¹ * g * n') * h' := by simp only [Matrix.mul_assoc]
  have hhi := WeylGroupFacts.uw_inv hh
  have hhi' := WeylGroupFacts.uw_inv hh'
  have hni := WeylGroupFacts.mem_n_inv hn
  have hu : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h (RankOneEmbeddings.In.uw_unit hh)
  have hu' : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv h' (RankOneEmbeddings.In.uw_unit hh')
  constructor
  · show unitH k r (omW k r z z' g) = h *ᵥ unitH k r (omW k r z z' (h⁻¹ * n⁻¹ * g * n' * h'))
    rw [hy, omW_UW hz hhi hh', omW_N hz hz' hni hn', unitH_UH hhi.1, Matrix.mulVec_mulVec, hu,
      Matrix.one_mulVec]
  · show unitH k r (omW' k r z z' g) = h' *ᵥ unitH k r (omW' k r z z' (h⁻¹ * n⁻¹ * g * n' * h'))
    rw [hy, omW'_UW hz hz' hhi hh', omW'_N hz hz' hni hn' hg.1, unitH_UH hhi'.1, Matrix.mulVec_mulVec,
      hu', Matrix.one_mulVec]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end
