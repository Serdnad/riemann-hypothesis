module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Wedge

theorem updateRow_submatrix_eq {K ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι κ K) (s : κ → ι) (k : κ) (i : ι) :
    (U.submatrix s id).updateRow k (U i) = U.submatrix (Function.update s k i) id := by
  ext j l
  by_cases h : j = k
  · subst h
    simp [Matrix.updateRow_apply, Function.update_self]
  · simp [Matrix.updateRow_apply, h, Function.update_of_ne h]

theorem eq_mul_of_det_ne_zero {K ι κ : Type} [Field K] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ K) (s : κ → ι) (hd : (U.submatrix s id).det ≠ 0) :
    U = (Matrix.of fun i k => (U.submatrix s id).det⁻¹ *
      (U.submatrix (Function.update s k i) id).det) * U.submatrix s id := by
  ext i l
  rw [Matrix.mul_apply]
  have key : ∀ k, (U.submatrix (Function.update s k i) id).det
      = Matrix.cramer (U.submatrix s id).transpose (U i) k := by
    intro k
    rw [← updateRow_submatrix_eq, Matrix.cramer_apply, Matrix.updateCol_transpose,
      Matrix.det_transpose]
  have hv := Matrix.mulVec_cramer (U.submatrix s id).transpose (U i)
  rw [Matrix.mulVec_transpose, Matrix.det_transpose] at hv
  have hl := congrFun hv l
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at hl
  simp only [Matrix.of_apply, key, mul_assoc]
  rw [← Finset.mul_sum, hl, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

theorem pairF_of_mulF : MulF → PairF := by
  intro hM
  unfold PairF
  intro K ι κ _ _ _ _ _ U W
  classical
  have hsz0 : ∀ {a b : Type} (g : Matrix a b K), 0 ≤ sz g := by
    intro a b g
    unfold sz
    exact Real.iSup_nonneg (fun p => norm_nonneg _)
  have hnF0 : ∀ (X : Matrix ι κ K), 0 ≤ nF X := by
    intro X
    unfold nF
    exact Real.iSup_nonneg (fun s => norm_nonneg _)
  have hdetT : (Uᵀ * W).det = (Wᵀ * U).det := by
    rw [← Matrix.det_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  by_cases h : ∃ s : κ → ι, (U.submatrix s id).det ≠ 0
  · haveI : Nonempty (κ → ι) := ⟨h.choose⟩
    obtain ⟨s₀, hs₀⟩ := Finite.exists_max (fun s : κ → ι => ‖(U.submatrix s id).det‖)
    have hd : (U.submatrix s₀ id).det ≠ 0 := by
      obtain ⟨s, hs⟩ := h
      intro h0
      have h1 := hs₀ s
      simp only [h0, norm_zero] at h1
      exact hs (norm_le_zero_iff.mp h1)
    have hnU : nF U = ‖(U.submatrix s₀ id).det‖ := by
      unfold nF
      apply le_antisymm
      · exact ciSup_le hs₀
      · exact le_ciSup (f := fun s : κ → ι => ‖(U.submatrix s id).det‖)
          (Set.finite_range _).bddAbove s₀
    set G : Matrix ι κ K := Matrix.of fun i k => (U.submatrix s₀ id).det⁻¹ *
      (U.submatrix (Function.update s₀ k i) id).det with hG
    have hUG : U = G * U.submatrix s₀ id := eq_mul_of_det_ne_zero U s₀ hd
    have hszG : sz Gᵀ ≤ 1 := by
      unfold sz
      apply Real.iSup_le ?_ zero_le_one
      intro p
      simp only [Matrix.transpose_apply, hG, Matrix.of_apply, norm_mul, norm_inv]
      rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hd), mul_one]
      exact hs₀ _
    have hmain : ‖(Gᵀ * W).det‖ ≤ nF W := by
      have h1 := (hM K ι κ κ W).1 Gᵀ
      have h2 := (hM K ι κ κ W).2.2 (Gᵀ * W)
      rw [h2] at h1
      calc ‖(Gᵀ * W).det‖ ≤ sz Gᵀ ^ Fintype.card κ * nF W := h1
        _ ≤ 1 * nF W := by
          apply mul_le_mul_of_nonneg_right _ (hnF0 W)
          exact pow_le_one₀ (hsz0 _) hszG
        _ = nF W := one_mul _
    have hfac : (Uᵀ * W).det = (U.submatrix s₀ id).det * (Gᵀ * W).det := by
      conv_lhs => rw [hUG]
      rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.det_mul, Matrix.det_transpose]
    rw [hfac, norm_mul, hnU]
    exact mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
  · simp only [not_exists, not_not] at h
    have hnU : nF U = 0 := by
      unfold nF
      simp only [h, norm_zero]
      first
        | exact Real.iSup_const_zero
        | simp
    have h1 := (hM K ι κ κ U).1 Wᵀ
    have h2 := (hM K ι κ κ U).2.2 (Wᵀ * U)
    rw [h2, hnU, mul_zero] at h1
    rw [hdetT, hnU, zero_mul]
    exact h1

end GlobalTheory.CompanionTheory.Wedge
end

section

open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.WedgeNorm

theorem wedge_fromCols_le {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {N : Fam K ι}
    (h : IsWedge N) (κ κ' : Type) [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (X : Matrix ι κ K) (Z : Matrix ι κ' K) :
    N (κ ⊕ κ') (fromCols X Z) ≤ N κ X * N κ' Z := by
  by_cases hX : LinearIndependent K Xᵀ
  · obtain ⟨Y, hY⟩ := h.quot κ X hX
    obtain ⟨h1, h2, -⟩ := hY κ' Z
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (h.nonneg κ X)
  · have h0 : N (κ ⊕ κ') (fromCols X Z) = 0 := by
      by_contra hne
      have hli := (h.ne_zero _ _).1 hne
      apply hX
      have hc := hli.comp Sum.inl Sum.inl_injective
      have he : (((fromCols X Z)ᵀ : (κ ⊕ κ') → ι → K) ∘ Sum.inl) = (Xᵀ : κ → ι → K) := by
        funext i j
        rfl
      rwa [he] at hc
    rw [h0]
    exact mul_nonneg (h.nonneg _ _) (h.nonneg _ _)

theorem wedgeSub : WedgeSub := by
  intro K ι _ _ _ N h κ₀ κ₁ κ₂ _ _ _ _ _ _ B A C
  by_cases hB : LinearIndependent K Bᵀ
  · obtain ⟨Y, hY⟩ := h.quot κ₀ B hB
    obtain ⟨h1, -, -⟩ := hY (κ₁ ⊕ κ₂) (fromCols A C)
    obtain ⟨h2, -, -⟩ := hY κ₁ A
    obtain ⟨h3, -, -⟩ := hY κ₂ C
    rw [h1, h2, h3, Matrix.mul_fromCols]
    have hle := wedge_fromCols_le h κ₁ κ₂ ((1 - B * Y) * A) ((1 - B * Y) * C)
    have hn := h.nonneg κ₀ B
    calc N κ₀ B * N (κ₁ ⊕ κ₂) (fromCols ((1 - B * Y) * A) ((1 - B * Y) * C)) * N κ₀ B
        ≤ N κ₀ B * (N κ₁ ((1 - B * Y) * A) * N κ₂ ((1 - B * Y) * C)) * N κ₀ B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hn) hn
      _ = N κ₀ B * N κ₁ ((1 - B * Y) * A) * (N κ₀ B * N κ₂ ((1 - B * Y) * C)) := by ring
  · have h0 : N κ₀ B = 0 := by
      by_contra hne
      exact hB ((h.ne_zero _ _).1 hne)
    rw [h0, mul_zero]
    exact mul_nonneg (h.nonneg _ _) (h.nonneg _ _)

end GlobalTheory.CompanionTheory.WedgeNorm
end

section

open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DetMonotone

private theorem exists_unitary_diagonal_eigenvalues_of_isHermitian {κ : Type} [Fintype κ] [DecidableEq κ] {A : Matrix κ κ ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix κ κ ℂ, U * star U = 1 ∧ star U * U = 1 ∧
      A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U := by
  refine ⟨(hA.eigenvectorUnitary : Matrix κ κ ℂ), Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2,
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, ?_⟩
  conv_lhs => rw [hA.spectral_theorem]
  rfl

theorem detMono : DetMono := by
  open ComplexOrder in (
    have one_le_re_det_lemma_2 : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] {Q : Matrix κ κ ℂ},
        Q.PosSemidef → 1 ≤ ((1 + Q).det).re := by
      intro κ _ _ Q hQ
      obtain ⟨U, h1, h2, hU⟩ := exists_unitary_diagonal_eigenvalues_of_isHermitian hQ.1
      have hsum : 1 + Q = U * diagonal (fun i => 1 + (hQ.1.eigenvalues i : ℂ)) * star U := by
        conv_lhs => rw [hU]
        rw [← diagonal_add, diagonal_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
      have hdet : (1 + Q).det = ∏ i, (1 + (hQ.1.eigenvalues i : ℂ)) := by
        rw [hsum, det_mul, det_mul, det_diagonal, mul_comm, ← mul_assoc, ← det_mul, h2, det_one, one_mul]
      rw [hdet, show (∏ i, (1 + (hQ.1.eigenvalues i : ℂ))) = ((∏ i, (1 + hQ.1.eigenvalues i) : ℝ) : ℂ) by
        push_cast; rfl, Complex.ofReal_re]
      calc (1 : ℝ) = ∏ _i : κ, (1 : ℝ) := by rw [Finset.prod_const_one]
        _ ≤ ∏ i, (1 + hQ.1.eigenvalues i) :=
          Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => le_add_of_nonneg_right (hQ.eigenvalues_nonneg i)
    intro κ _ _ X Y hX hP
    have hY : Y = X + (Y - X) := by abel
    by_cases h0 : X.det = 0
    · rw [h0, Complex.zero_re]
      have hnn := (hX.add hP).det_nonneg
      rw [← hY] at hnn
      exact (Complex.le_def.1 hnn).1
    · obtain ⟨U, h1, h2, hU⟩ := exists_unitary_diagonal_eigenvalues_of_isHermitian hX.1
      have hpos : ∀ i, 0 < hX.1.eigenvalues i := by
        intro i
        refine lt_of_le_of_ne (hX.eigenvalues_nonneg i) fun h => h0 ?_
        rw [hX.1.det_eq_prod_eigenvalues]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← h]; simp)
      set s : κ → ℂ := fun i => ((Real.sqrt (hX.1.eigenvalues i) : ℝ) : ℂ) with hs
      have hs0 : ∀ i, s i ≠ 0 := fun i => by
        simp only [hs, ne_eq, Complex.ofReal_eq_zero]
        exact (Real.sqrt_pos.2 (hpos i)).ne'
      have hss : ∀ i, s i * s i = (hX.1.eigenvalues i : ℂ) := fun i => by
        simp only [hs]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]
      have hstar : ∀ i, star (s i) = s i := fun i => by simp [hs]
      set B : Matrix κ κ ℂ := diagonal s * star U with hB
      set C : Matrix κ κ ℂ := U * diagonal (fun i => (s i)⁻¹) with hC
      have hCB : C * B = 1 := by
        rw [hB, hC, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal,
          show (fun i => (s i)⁻¹ * s i) = fun _ => (1 : ℂ) from funext fun i => inv_mul_cancel₀ (hs0 i),
          diagonal_one, Matrix.one_mul, h1]
      have hXB : X = Bᴴ * B := by
        rw [hB, conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose, conjTranspose_conjTranspose,
          show star s = s from funext hstar, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s),
          diagonal_mul_diagonal, show (fun i => s i * s i) = fun i => (hX.1.eigenvalues i : ℂ) from funext hss,
          ← Matrix.mul_assoc, ← star_eq_conjTranspose]
        exact hU
      have hsplit : Y = Bᴴ * (1 + Cᴴ * (Y - X) * C) * B := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hXB, Matrix.mul_assoc, Matrix.mul_assoc, hCB,
          Matrix.mul_one, ← Matrix.mul_assoc, ← conjTranspose_mul, hCB, conjTranspose_one, Matrix.one_mul]
        abel
      have hQ : (Cᴴ * (Y - X) * C).PosSemidef := hP.conjTranspose_mul_mul_same C
      have hdX : X.det = Bᴴ.det * B.det := by rw [hXB, det_mul]
      clear_value B C
      have hdY : Y.det = (1 + Cᴴ * (Y - X) * C).det * X.det := by
        conv_lhs => rw [hsplit]
        rw [det_mul, det_mul, hdX]
        ring
      have hXnn := Complex.le_def.1 hX.det_nonneg
      have hQnn := Complex.le_def.1 (PosSemidef.one.add hQ).det_nonneg
      rw [hdY, Complex.mul_re, ← hXnn.2, ← hQnn.2]
      simp only [Complex.zero_im, mul_zero, sub_zero]
      have ha : 0 ≤ X.det.re := by simpa using hXnn.1
      exact le_mul_of_one_le_left ha (one_le_re_det_lemma_2 hQ))

end GlobalTheory.CompanionTheory.DetMonotone
end

section

noncomputable section

open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Wedge

variable {ι κ κ' : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

theorem gram_det_nonneg (A : Matrix ι κ ℂ) : 0 ≤ (Aᴴ * A).det := by
  exact (Matrix.posSemidef_conjTranspose_mul_self A).det_nonneg

theorem gram_det_im (A : Matrix ι κ ℂ) : (Aᴴ * A).det.im = 0 := by
  exact (Complex.nonneg_iff.1 (gram_det_nonneg A)).2.symm

theorem nI_nonneg (A : Matrix ι κ ℂ) : 0 ≤ nI A := by
  exact (Complex.nonneg_iff.1 (gram_det_nonneg A)).1

theorem nI_ne_zero_iff_det (A : Matrix ι κ ℂ) : nI A ≠ 0 ↔ (Aᴴ * A).det ≠ 0 := by
  have him := gram_det_im A
  show (Aᴴ * A).det.re ≠ 0 ↔ _
  constructor
  · intro h h0
    apply h
    rw [h0, Complex.zero_re]
  · intro h h0
    apply h
    exact Complex.ext (by rw [h0, Complex.zero_re]) (by rw [him, Complex.zero_im])

theorem gram_det_ne_zero_iff (A : Matrix ι κ ℂ) :
    (Aᴴ * A).det ≠ 0 ↔ LinearIndependent ℂ Aᵀ := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit,
    ← Matrix.coe_mulVecLin, ← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_conjTranspose_mul_self,
    LinearMap.ker_eq_bot, Matrix.coe_mulVecLin]
  exact Matrix.mulVec_injective_iff

theorem nI_submatrix (e : κ' ≃ κ) (A : Matrix ι κ ℂ) : nI (A.submatrix id e) = nI A := by
  show ((A.submatrix id e)ᴴ * A.submatrix id e).det.re = (Aᴴ * A).det.re
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul Aᴴ A (⇑e) id (⇑e) Function.bijective_id,
    Matrix.det_submatrix_equiv_self]

theorem nI_fromCols_of_orth (B : Matrix ι κ ℂ) (D : Matrix ι κ' ℂ) (h : Bᴴ * D = 0) :
    nI (fromCols B D) = nI B * nI D := by
  have h' : Dᴴ * B = 0 := by
    have h2 := congrArg Matrix.conjTranspose h
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h2
    exact h2
  show ((fromCols B D)ᴴ * fromCols B D).det.re = (Bᴴ * B).det.re * (Dᴴ * D).det.re
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols, h, h',
    Matrix.det_fromBlocks_zero₂₁, Complex.mul_re, gram_det_im B, gram_det_im D, mul_zero, sub_zero]

theorem exists_proj (B : Matrix ι κ ℂ) (hB : LinearIndependent ℂ Bᵀ) :
    ∃ Y : Matrix κ ι ℂ, Y * B = 1 ∧ (B * Y)ᴴ = B * Y := by
  have hu : IsUnit (Bᴴ * B).det := isUnit_iff_ne_zero.2 ((gram_det_ne_zero_iff B).2 hB)
  have hG : (Bᴴ * B)ᴴ = Bᴴ * B := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  refine ⟨(Bᴴ * B)⁻¹ * Bᴴ, ?_, ?_⟩
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hG, Matrix.mul_assoc]

theorem commGroup_mul_mul_eq_mul_inv_mul_mul_mul [DecidableEq ι] (hD : DetMono) (hM : MulI) (B : Matrix ι κ ℂ) (Y : Matrix κ ι ℂ)
    (hYB : Y * B = 1) (hQ : (B * Y)ᴴ = B * Y) (C : Matrix ι κ' ℂ) :
    nI (fromCols B C) = nI B * nI ((1 - B * Y) * C) ∧ nI ((1 - B * Y) * C) ≤ nI C ∧
      (1 - B * Y) * B = 0 := by
  have hPP : B * Y * (B * Y) = B * Y := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Y, hYB, Matrix.one_mul]
  have hQB : (1 - B * Y) * B = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYB, Matrix.mul_one, sub_self]
  have hQh : (1 - B * Y)ᴴ = 1 - B * Y := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQ]
  have hQQ : (1 - B * Y) * (1 - B * Y) = 1 - B * Y := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, sub_zero]
  have hPh : (B * Y)ᴴ * (B * Y) = B * Y := by
    rw [hQ, hPP]
  refine ⟨?_, ?_, hQB⟩
  · have hcols : fromCols B C = (fromCols B ((1 - B * Y) * C) : Matrix ι (κ ⊕ κ') ℂ) *
        (fromBlocks (1 : Matrix κ κ ℂ) (Y * C) (0 : Matrix κ' κ ℂ) (1 : Matrix κ' κ' ℂ)) := by
      rw [Matrix.fromCols_mul_fromBlocks]
      congr 1
      · rw [Matrix.mul_one, Matrix.mul_zero, add_zero]
      · rw [Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
        abel
    have horth : Bᴴ * ((1 - B * Y) * C) = 0 := by
      rw [← Matrix.mul_assoc, ← hQh, ← Matrix.conjTranspose_mul, hQB, Matrix.conjTranspose_zero,
        Matrix.zero_mul]
    rw [hcols, (hM ι ι (κ ⊕ κ') (fromCols B ((1 - B * Y) * C))).2.1, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, Matrix.det_one, mul_one, norm_one, one_pow, mul_one, nI_fromCols_of_orth B _ horth]
  · have hX : ((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C) = Cᴴ * ((1 - B * Y) * C) := by
      rw [Matrix.conjTranspose_mul, hQh, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - B * Y), hQQ]
    have hYX : Cᴴ * C - ((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C) = (B * Y * C)ᴴ * (B * Y * C) := by
      rw [hX, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (B * Y)ᴴ, hPh,
        Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, sub_sub_cancel]
    exact hD κ' (((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C)) (Cᴴ * C)
      (Matrix.posSemidef_conjTranspose_mul_self _)
      (by rw [hYX]; exact Matrix.posSemidef_conjTranspose_mul_self _)

theorem wedgeI_of_detMono_mulI : DetMono → MulI → WedgeI := by
  intro hD hM ι _ _
  refine ⟨fun κ _ _ A => nI_nonneg A, fun κ _ _ A => (nI_ne_zero_iff_det A).trans (gram_det_ne_zero_iff A),
    fun κ κ' _ _ _ _ e A => nI_submatrix e A, fun κ _ _ B hB => ?_⟩
  obtain ⟨Y, hYB, hQ⟩ := exists_proj B hB
  exact ⟨Y, fun κ' _ _ C => commGroup_mul_mul_eq_mul_inv_mul_mul_mul hD hM B Y hYB hQ C⟩

end GlobalTheory.CompanionTheory.Wedge

end
end

section

open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.WedgeMinor

theorem det_mul_submatrix_expand {K ι ι' κ : Type} [CommRing K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ((g * A).submatrix t id).det =
      ∑ s : κ → ι, (∏ i, g (t i) (s i)) * (A.submatrix s id).det := by
  have h : ((g * A).submatrix t id : κ → κ → K) = fun i => ∑ k, g (t i) k • A k := by
    funext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  have key : ∀ M : Matrix κ κ K,
      M.det = (detRowAlternating (R := K) (n := κ)).toMultilinearMap M := fun _ => rfl

  rw [key, h, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem sz_nonneg {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem le_sz {K ι κ : Type} [NormedField K] [Finite ι] [Finite κ] (g : Matrix ι κ K)
    (i : ι) (j : κ) : ‖g i j‖ ≤ sz g :=
  le_ciSup (f := fun p : ι × κ => ‖g p.1 p.2‖) (Set.finite_range _).bddAbove (i, j)

theorem nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem le_nF {K ι κ : Type} [NormedField K] [Finite ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : κ → ι) : ‖(A.submatrix s id).det‖ ≤ nF A :=
  le_ciSup (f := fun s : κ → ι => ‖(A.submatrix s id).det‖) (Set.finite_range _).bddAbove s

theorem norm_minor_mul_le {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ‖((g * A).submatrix t id).det‖ ≤ sz g ^ Fintype.card κ * nF A := by
  rw [det_mul_submatrix_expand]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A)) fun s _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_mul ?_ (le_nF A s) (norm_nonneg _) (pow_nonneg (sz_nonneg g) _)
  calc ∏ i, ‖g (t i) (s i)‖ ≤ ∏ _i : κ, sz g :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => le_sz g _ _
    _ = sz g ^ Fintype.card κ := by simp

theorem nF_mul_le {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) :
    nF (g * A) ≤ sz g ^ Fintype.card κ * nF A :=
  Real.iSup_le (fun t => norm_minor_mul_le g A t)
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A))

theorem nF_mul_right {K ι κ : Type} [NormedField K] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : Matrix κ κ K) : nF (A * s) = nF A * ‖s.det‖ := by
  unfold nF
  rw [Real.iSup_mul_of_nonneg (norm_nonneg _)]
  refine iSup_congr fun t => ?_
  have h : (A * s).submatrix t id = A.submatrix t id * s := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, det_mul, norm_mul]

theorem nF_square {K κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) : nF s = ‖s.det‖ := by
  refine le_antisymm (Real.iSup_le (fun t => ?_) (norm_nonneg _)) ?_
  · by_cases ht : Function.Injective t
    · have hb : Function.Bijective t := Finite.injective_iff_bijective.mp ht
      have h := Matrix.det_permute (Equiv.ofBijective t hb) s
      have h' : (s.submatrix t id).det = _ := h
      rw [h', norm_mul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective t hb)) with h1 | h1 <;>
        simp [h1]
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, t i = t j ∧ i ≠ j := by
        simpa [Function.Injective] using ht
      rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hij])]
      simp
  · simpa using le_nF s id

theorem mulF : MulF := by
  intro K ι ι' κ _ _ _ _ _ _ A
  exact ⟨fun g => nF_mul_le g A, fun s => nF_mul_right A s, fun s => nF_square s⟩

end GlobalTheory.CompanionTheory.WedgeMinor
end
