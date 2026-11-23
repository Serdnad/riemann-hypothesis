module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section

section

open Matrix Complex

namespace GlobalTheory.CompanionTheory.Ar.Flat

private lemma sr_entry {g : ℕ} (A B Hm : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    (A * Hm * Bᴴ) i j = A i ⬝ᵥ Hm *ᵥ star (B j) := by
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private lemma sr_im_left {g : ℕ} (S : Matrix (Fin g) (Fin g) ℝ) (T : Matrix (Fin g) (Fin g) ℂ) :
    (S.map ofReal * T).map im = S * T.map im := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum]

private lemma sr_re_left {g : ℕ} (S : Matrix (Fin g) (Fin g) ℝ) (T : Matrix (Fin g) (Fin g) ℂ) :
    (S.map ofReal * T).map re = S * T.map re := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum]

private lemma sr_im_mul {g : ℕ} (U T : Matrix (Fin g) (Fin g) ℂ) :
    (U * T).map im = U.map re * T.map im + U.map im * T.map re := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum, Complex.mul_im, Finset.sum_add_distrib]

theorem siegel_of_riemann : ∀ (g : ℕ) (A Bm Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → (∀ i j, (A i ⬝ᵥ Hm *ᵥ star (A j)).im = 0 ∧ (Bm i ⬝ᵥ Hm *ᵥ star (Bm j)).im = 0 ∧ (A i ⬝ᵥ Hm *ᵥ star (Bm j)).im = if i = j then -1 else 0) → A.det ≠ 0 ∧ (Bm * A⁻¹)ᵀ = Bm * A⁻¹ ∧ ((Bm * A⁻¹).map im).PosDef ∧ A * Hm * Aᴴ = (((Bm * A⁻¹).map im)⁻¹).map ofReal := by
  intro g A Bm Hm hH hpos hrel
  have hPij : ∀ i j, ((A * Hm * Aᴴ) i j).im = 0 := fun i j => by
    rw [sr_entry]
    exact (hrel i j).1
  have hAA : ∀ u v : Fin g → ℝ,
      (((fun i => (u i : ℂ)) ᵥ* A) ⬝ᵥ Hm *ᵥ star ((fun i => (v i : ℂ)) ᵥ* A)).im = 0 := by
    intro u v
    rw [Matrix.star_vecMul, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc]
    simp [dotProduct, Matrix.mulVec, Complex.im_sum, Complex.mul_im, hPij]
  have hAAre : ∀ u v : Fin g → ℝ,
      (((fun i => (u i : ℂ)) ᵥ* A) ⬝ᵥ Hm *ᵥ star ((fun i => (v i : ℂ)) ᵥ* A)).re =
        u ⬝ᵥ ((A * Hm * Aᴴ).map re) *ᵥ v := by
    intro u v
    rw [Matrix.star_vecMul, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc]
    simp [dotProduct, Matrix.mulVec, Complex.re_sum, Complex.mul_re, hPij, Finset.mul_sum]
  have hAB : ∀ (a : Fin g → ℝ) (j : Fin g),
      (((fun i => (a i : ℂ)) ᵥ* A) ⬝ᵥ Hm *ᵥ star (Bm j)).im = -a j := by
    intro a j
    rw [← Matrix.dotProduct_mulVec]
    have e : ∀ i, (A *ᵥ Hm *ᵥ star (Bm j)) i = A i ⬝ᵥ Hm *ᵥ star (Bm j) := fun i => rfl
    rw [dotProduct, Complex.im_sum]
    simp only [Complex.im_ofReal_mul, e, (hrel _ j).2.2]
    simp
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    obtain ⟨a, ha⟩ : ∃ a : Fin g → ℝ, ∀ i, a i = (c i).re := ⟨fun i => (c i).re, fun i => rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : Fin g → ℝ, ∀ i, b i = (c i).im := ⟨fun i => (c i).im, fun i => rfl⟩
    have hcab : c = (fun i => (a i : ℂ)) + Complex.I • (fun i => (b i : ℂ)) := by
      funext i
      apply Complex.ext <;> simp [ha, hb]
    have hxa : (fun i => (a i : ℂ)) ᵥ* A = 0 := by
      by_contra hne
      have hp := hpos _ hne
      have hsplit : (fun i => (a i : ℂ)) ᵥ* A = -(Complex.I • ((fun i => (b i : ℂ)) ᵥ* A)) := by
        have h := hc
        rw [hcab, Matrix.add_vecMul, Matrix.smul_vecMul] at h
        exact eq_neg_of_add_eq_zero_left h
      have him := hAA b a
      have e : ((fun i => (a i : ℂ)) ᵥ* A) ⬝ᵥ Hm *ᵥ star ((fun i => (a i : ℂ)) ᵥ* A) =
          -(Complex.I * (((fun i => (b i : ℂ)) ᵥ* A) ⬝ᵥ Hm *ᵥ star ((fun i => (a i : ℂ)) ᵥ* A))) := by
        nth_rewrite 1 [hsplit]
        rw [neg_dotProduct, smul_dotProduct, smul_eq_mul]
      rw [e] at hp
      simp [Complex.mul_re, him] at hp
    have hxb : (fun i => (b i : ℂ)) ᵥ* A = 0 := by
      have h := hc
      rw [hcab, Matrix.add_vecMul, Matrix.smul_vecMul, hxa, zero_add] at h
      exact (smul_eq_zero.1 h).resolve_left Complex.I_ne_zero
    have ha0 : ∀ j, a j = 0 := fun j => by
      have h := hAB a j
      rw [hxa, zero_dotProduct] at h
      simpa using h
    have hb0 : ∀ j, b j = 0 := fun j => by
      have h := hAB b j
      rw [hxb, zero_dotProduct] at h
      simpa using h
    apply hc0
    funext i
    apply Complex.ext
    · rw [← ha i, ha0 i]
      simp
    · rw [← hb i, hb0 i]
      simp
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  set Z := Bm * A⁻¹ with hZ
  have hB : Bm = Z * A := by
    rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
  have hR : A * Hm * Bmᴴ = A * Hm * Aᴴ * Zᴴ := by
    rw [hB, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hPc : A * Hm * Aᴴ = ((A * Hm * Aᴴ).map re).map ofReal := by
    ext i j
    apply Complex.ext
    · simp
    · simp [hPij i j]
  have hPH : (A * Hm * Aᴴ)ᴴ = A * Hm * Aᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq,
      Matrix.mul_assoc]
  have hPrT : ((A * Hm * Aᴴ).map re)ᵀ = (A * Hm * Aᴴ).map re := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    have h := congrFun (congrFun hPH j) i
    rw [Matrix.conjTranspose_apply] at h
    rw [← h]
    simp [Complex.star_def]
  have hRim : (A * Hm * Bmᴴ).map im = -1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
    rw [sr_entry, (hrel i j).2.2]
    split_ifs <;> simp
  have hZH : (Zᴴ).map im = -(Z.map im)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply, Complex.star_def]
  have hZHre : (Zᴴ).map re = (Z.map re)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply, Complex.star_def]
  have hPY : (A * Hm * Aᴴ).map re * (Z.map im)ᵀ = 1 := by
    have h := hRim
    rw [hR, hPc, sr_im_left, hZH, Matrix.mul_neg] at h
    exact neg_inj.1 h
  have hPu : IsUnit ((A * Hm * Aᴴ).map re).det := Matrix.isUnit_det_of_right_inverse hPY
  have hYT : (Z.map im)ᵀ = ((A * Hm * Aᴴ).map re)⁻¹ := (Matrix.inv_eq_right_inv hPY).symm
  have hY : Z.map im = ((A * Hm * Aᴴ).map re)⁻¹ := by
    rw [← Matrix.transpose_transpose (Z.map im), hYT, Matrix.transpose_nonsing_inv, hPrT]
  have hPrpos : ((A * Hm * Aᴴ).map re).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hPrT
    · have hne : (fun i => (x i : ℂ)) ᵥ* A ≠ 0 := by
        intro h0
        apply hx
        have h1 : (fun i => (x i : ℂ)) = 0 := by
          have h2 := congrArg (fun v => v ᵥ* A⁻¹) h0
          simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hAu, Matrix.vecMul_one,
            Matrix.zero_vecMul] at h2
          exact h2
        funext i
        have h3 := congrFun h1 i
        simpa using h3
      have h := hpos _ hne
      rw [hAAre] at h
      simpa using h
  have hPinv : ((A * Hm * Aᴴ).map re)⁻¹ * (A * Hm * Aᴴ).map re = 1 :=
    Matrix.nonsing_inv_mul _ hPu
  have hQ : Bm * Hm * Bmᴴ = Z * (A * Hm * Bmᴴ) := by
    calc Bm * Hm * Bmᴴ = Z * A * Hm * Bmᴴ := by rw [← hB]
      _ = Z * (A * Hm * Bmᴴ) := by simp only [Matrix.mul_assoc]
  have hQim : (Bm * Hm * Bmᴴ).map im = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [sr_entry]
    exact (hrel i j).2.1
  have hX : (Z.map re)ᵀ = Z.map re := by
    have h := hQim
    rw [hQ, sr_im_mul, hRim, hR, hPc, sr_re_left, hZHre, hY, ← Matrix.mul_assoc, hPinv, Matrix.one_mul,
      Matrix.mul_neg, Matrix.mul_one] at h
    exact (neg_add_eq_zero.1 h).symm
  have hYsym : (Z.map im)ᵀ = Z.map im := by rw [hYT, hY]
  have hZT : Zᵀ = Z := by
    ext i j
    apply Complex.ext
    · have h := congrFun (congrFun hX i) j
      simpa using h
    · have h := congrFun (congrFun hYsym i) j
      simpa using h
  refine ⟨hdet, hZT, ?_, ?_⟩
  · rw [hY]
    exact hPrpos.inv
  · rw [hY, Matrix.nonsing_inv_nonsing_inv _ hPu]
    exact hPc

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.AdaptedFrame

variable {Φ : Type} [Field Φ] {r : ℕ}

def revMatrix (Φ : Type) [Field Φ] (r : ℕ) : Matrix (Fin r) (Fin r) Φ :=
  Matrix.of fun a b => if a = Fin.rev b then 1 else 0

theorem mul_revMatrix_apply (A : Matrix (Fin r) (Fin r) Φ) (a b : Fin r) :
    (A * revMatrix Φ r) a b = A a (Fin.rev b) := by
  simp [Matrix.mul_apply, revMatrix]

theorem revMatrix_mul_apply (A : Matrix (Fin r) (Fin r) Φ) (a b : Fin r) :
    (revMatrix Φ r * A) a b = A (Fin.rev a) b := by
  have : ∀ x : Fin r, (a = Fin.rev x) ↔ (x = Fin.rev a) := fun x => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [Matrix.mul_apply, revMatrix, this]

theorem revMatrix_mul_self : revMatrix Φ r * revMatrix Φ r = 1 := by
  ext a b
  rw [mul_revMatrix_apply]
  simp [revMatrix, Matrix.one_apply, Fin.rev_rev]

theorem revMatrix_transpose : (revMatrix Φ r)ᵀ = revMatrix Φ r := by
  ext a b
  simp only [revMatrix, Matrix.transpose_apply, Matrix.of_apply]
  have : (b = Fin.rev a) ↔ (a = Fin.rev b) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [this]

theorem inv_diag (U : Matrix (Fin r) (Fin r) Φ) (hU : U.BlockTriangular id)
    (hd : ∀ l, U l l ≠ 0) (l : Fin r) : U⁻¹ l l = (U l l)⁻¹ := by
  have hdet : IsUnit U.det := by
    rw [Matrix.det_of_upperTriangular hU]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have hinv : U⁻¹.BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet U hdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU
  have h1 : (U * U⁻¹) l l = 1 := by
    rw [Matrix.mul_nonsing_inv U hdet]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single l] at h1
  · exact eq_inv_of_mul_eq_one_right h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hU (show id k < id l from h)]; simp
    · rw [hinv (show id l < id k from h)]; simp
  · simp

theorem reversed_dual_frame :
    ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (r : ℕ) (u T U Rm Rm' : Matrix (Fin r) (Fin r) Φ),
      IsUnit u.det → IsUnit T.det → U.BlockTriangular id → (∀ l, U l l ≠ 0) →
      (∀ a b, Rm a b ∈ R) → (∀ a b, Rm' a b ∈ R) → Rm * Rm' = 1 →
      (Matrix.of fun a b => uᵀ⁻¹ a (Fin.rev b)) * U = Tᵀ⁻¹ * Rm →
      ∃ U₂ R₂ R₂' : Matrix (Fin r) (Fin r) Φ, U₂.BlockTriangular id ∧
        (∀ l, U₂ l l = (U l.rev l.rev)⁻¹) ∧ (∀ a b, R₂ a b ∈ R) ∧ (∀ a b, R₂' a b ∈ R) ∧
        R₂ * R₂' = 1 ∧ u * U₂ = T * R₂ := by
  intro Φ _ R r u T U Rm Rm' hu hT hU hd hRm hRm' hmul h
  have hUdet : IsUnit U.det := by
    rw [Matrix.det_of_upperTriangular hU]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have hUinv : U⁻¹.BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet U hUdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU
  have hutdet : IsUnit (uᵀ).det := by rwa [Matrix.det_transpose]
  have hTtdet : IsUnit (Tᵀ).det := by rwa [Matrix.det_transpose]
  have hUtdet : IsUnit (Uᵀ).det := by rwa [Matrix.det_transpose]
  set P := revMatrix Φ r with hP
  have hPP : P * P = 1 := revMatrix_mul_self
  have hPt : Pᵀ = P := revMatrix_transpose
  have hrev : (Matrix.of fun a b => uᵀ⁻¹ a (Fin.rev b)) = uᵀ⁻¹ * P := by
    ext a b
    rw [mul_revMatrix_apply]; rfl
  rw [hrev] at h

  have e1 : Tᵀ * (uᵀ⁻¹ * P * U * Rm') = 1 := by
    rw [h, Matrix.mul_assoc (Tᵀ⁻¹), hmul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hTtdet]
  have e2 : Rm'ᵀ * Uᵀ * P * u⁻¹ * T = 1 := by
    have := congrArg Matrix.transpose e1
    simp only [Matrix.transpose_mul, Matrix.transpose_one, hPt, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv] at this
    simpa [Matrix.mul_assoc] using this
  have e3 : T * (Rm'ᵀ * Uᵀ * P * u⁻¹) = 1 := mul_eq_one_comm.1 e2
  have e4 : T * Rm'ᵀ = u * P * Uᵀ⁻¹ := by
    have hk : (Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹) = 1 := by
      calc (Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹)
          = Uᵀ * P * (u⁻¹ * u) * P * Uᵀ⁻¹ := by simp only [Matrix.mul_assoc]
        _ = Uᵀ * (P * P) * Uᵀ⁻¹ := by
            rw [Matrix.nonsing_inv_mul _ hu]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = 1 := by rw [hPP, Matrix.mul_one, Matrix.mul_nonsing_inv _ hUtdet]
    calc T * Rm'ᵀ = T * Rm'ᵀ * ((Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹)) := by rw [hk, Matrix.mul_one]
      _ = (T * (Rm'ᵀ * Uᵀ * P * u⁻¹)) * (u * P * Uᵀ⁻¹) := by simp only [Matrix.mul_assoc]
      _ = u * P * Uᵀ⁻¹ := by rw [e3, Matrix.one_mul]
  have hent : ∀ a b, (P * Uᵀ⁻¹ * P) a b = U⁻¹ (Fin.rev b) (Fin.rev a) := by
    intro a b
    rw [hP, mul_revMatrix_apply, revMatrix_mul_apply, ← Matrix.transpose_nonsing_inv,
      Matrix.transpose_apply]
  refine ⟨P * Uᵀ⁻¹ * P, Rm'ᵀ * P, P * Rmᵀ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : b < a := hab
    rw [hent]
    exact hUinv (show id (Fin.rev a) < id (Fin.rev b) from Fin.rev_lt_rev.2 hab')
  · intro l
    rw [hent]
    exact inv_diag U hU hd _
  · intro a b
    rw [mul_revMatrix_apply]; exact hRm' _ _
  · intro a b
    rw [revMatrix_mul_apply]; exact hRm _ _
  · calc Rm'ᵀ * P * (P * Rmᵀ) = Rm'ᵀ * (P * P) * Rmᵀ := by simp only [Matrix.mul_assoc]
      _ = (Rm * Rm')ᵀ := by rw [hPP, Matrix.mul_one, Matrix.transpose_mul]
      _ = 1 := by rw [hmul, Matrix.transpose_one]
  · calc u * (P * Uᵀ⁻¹ * P) = (u * P * Uᵀ⁻¹) * P := by simp only [Matrix.mul_assoc]
      _ = T * (Rm'ᵀ * P) := by rw [← e4, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.AdaptedFrame
end
