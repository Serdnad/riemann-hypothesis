module

public import GroundTheory.HeightsAndTheta.Heights.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle001
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KCoord

variable {m n : Type*} [Fintype m] [Fintype n]

theorem posDef_fromBlocks_diag {A : Matrix m m ℝ} {D : Matrix n n ℝ} (hA : A.PosDef)
    (hD : D.PosDef) : (fromBlocks A 0 0 D).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (hA.1.fromBlocks (by simp) hD.1) fun x hx => ?_
  have hsplit : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
    simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hsplit]
  have h1 := hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have h2 := hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  by_cases hl : x ∘ Sum.inl = 0
  · have hr : x ∘ Sum.inr ≠ 0 := by
      intro hr
      apply hx
      funext i
      cases i with
      | inl i => exact congrFun hl i
      | inr i => exact congrFun hr i
    have := hD.dotProduct_mulVec_pos hr
    linarith
  · have := hA.dotProduct_mulVec_pos hl
    linarith

end KCoord

variable {g : ℕ}

namespace KCoord

def unip (X : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks 1 X 0 1

noncomputable def diagInv (Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ 0 0 Y

theorem siegelGram_eq (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    siegelGram X Y = (unip X)ᵀ * diagInv Y * unip X := by
  have hXt : Xᵀ = X := hX
  simp [siegelGram, unip, diagInv, fromBlocks_transpose, fromBlocks_multiply, hXt, add_comm]

theorem unip_mem (X : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    unip X ∈ symplecticGroup (Fin g) ℝ := by
  have hXt : Xᵀ = X := hX
  rw [SymplecticGroup.mem_iff]
  simp [unip, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hXt]

theorem diagInv_mem (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) :
    diagInv Y ∈ symplecticGroup (Fin g) ℝ := by
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit
  have hYt : Yᵀ = Y := by
    have := hY.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hYit : Y⁻¹ᵀ = Y⁻¹ := by rw [Matrix.transpose_nonsing_inv, hYt]
  rw [SymplecticGroup.mem_iff]
  simp [diagInv, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hYt, hYit,
    Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet]

theorem unip_isUnit (X : Matrix (Fin g) (Fin g) ℝ) : IsUnit (unip X) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [unip]

theorem siegelGram_mem_posDef (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) (hY : Y.PosDef) :
    siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef := by
  rw [siegelGram_eq X Y hX]
  refine ⟨Submonoid.mul_mem _ (Submonoid.mul_mem _
    (SymplecticGroup.transpose_mem (unip_mem X hX)) (diagInv_mem Y hY)) (unip_mem X hX), ?_⟩
  have hD : (diagInv Y).PosDef := posDef_fromBlocks_diag hY.inv hY
  have hinj : Function.Injective (unip X).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (unip_isUnit X)
  have := hD.conjTranspose_mul_mul_same hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

end KCoord

namespace KCoord

theorem existsUnique_siegelGram (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)
    (hS : G ∈ symplecticGroup (Fin g) ℝ) (hG : G.PosDef) :
    ∃! XY : Matrix (Fin g) (Fin g) ℝ × Matrix (Fin g) (Fin g) ℝ,
      XY.1.IsSymm ∧ XY.2.PosDef ∧ G = siegelGram XY.1 XY.2 := by
  have hGt : Gᵀ = G := by
    have := hG.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hS' := hS
  rw [SymplecticGroup.mem_iff, hGt] at hS'
  have hGb := Matrix.fromBlocks_toBlocks G
  set A := G.toBlocks₁₁ with hAdef
  set B := G.toBlocks₁₂ with hBdef
  set C := G.toBlocks₂₁ with hCdef
  set D := G.toBlocks₂₂ with hDdef
  have hGt' := hGt
  rw [← hGb] at hS' hGt'
  simp only [fromBlocks_transpose, Matrix.J, fromBlocks_multiply] at hS' hGt'
  obtain ⟨e1, e2, -, -⟩ := Matrix.fromBlocks_inj.mp hS'
  obtain ⟨t1, -, t3, -⟩ := Matrix.fromBlocks_inj.mp hGt'
  simp at e1 e2
  have hBA : B * A = A * C := by
    have := e1
    rwa [add_neg_eq_zero] at this
  have hAD : A * D = 1 + B * B := by
    have h1 : A * D = B * B - (B * B + -(A * D)) := by abel
    rw [h1, e2]; abel
  have hA : A.PosDef := hG.submatrix Sum.inl_injective
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hAiA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAdet
  have hAAi : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAdet
  have hAit : A⁻¹ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, t1]
  have hCt : Bᵀ = C := t3
  have k : A⁻¹ * B = C * A⁻¹ := by
    calc A⁻¹ * B = A⁻¹ * B * (A * A⁻¹) := by rw [hAAi, Matrix.mul_one]
      _ = A⁻¹ * (B * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * C) * A⁻¹ := by rw [hBA]
      _ = C * A⁻¹ := by rw [← Matrix.mul_assoc A⁻¹ A C, hAiA, Matrix.one_mul]
  have hX : (A⁻¹ * B).IsSymm := by
    show (A⁻¹ * B)ᵀ = A⁻¹ * B
    rw [Matrix.transpose_mul, hAit, hCt, k]
  have hY : (A⁻¹).PosDef := hA.inv
  have hYinv : (A⁻¹)⁻¹ = A := Matrix.nonsing_inv_nonsing_inv A hAdet
  refine ⟨(A⁻¹ * B, A⁻¹), ⟨hX, hY, ?_⟩, ?_⟩
  · show G = siegelGram (A⁻¹ * B) A⁻¹
    rw [siegelGram, hYinv]
    conv_lhs => rw [← hGb]
    congr 1
    · rw [← Matrix.mul_assoc, hAAi, Matrix.one_mul]
    · rw [k, Matrix.mul_assoc, hAiA, Matrix.mul_one]
    · have hD : D = A⁻¹ * (1 + B * B) := by
        rw [← hAD, ← Matrix.mul_assoc, hAiA, Matrix.one_mul]
      rw [hD, k, Matrix.mul_add, Matrix.mul_one]
      congr 1
      calc A⁻¹ * (B * B) = A⁻¹ * B * (A * A⁻¹) * B := by
            rw [hAAi, Matrix.mul_one, Matrix.mul_assoc]
        _ = C * A⁻¹ * A * A⁻¹ * B := by rw [← k]; simp only [Matrix.mul_assoc]
        _ = C * A⁻¹ * A * (A⁻¹ * B) := by simp only [Matrix.mul_assoc]
        _ = C * A⁻¹ * A * (C * A⁻¹) := by rw [k]
  · rintro ⟨X', Y'⟩ ⟨hX', hY', hG'⟩
    have hY'det : IsUnit Y'.det := (Matrix.isUnit_iff_isUnit_det Y').1 hY'.isUnit
    have h11 : A = Y'⁻¹ := by
      rw [hAdef, hG']; simp [siegelGram]
    have h12 : B = Y'⁻¹ * X' := by
      rw [hBdef, hG']; simp [siegelGram]
    have hYY : Y' = A⁻¹ := by
      rw [h11, Matrix.nonsing_inv_nonsing_inv Y' hY'det]
    have hXX : X' = A⁻¹ * B := by
      rw [h12, ← hYY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y' hY'det, Matrix.one_mul]
    simp only [Prod.mk.injEq]
    exact ⟨hXX, hYY⟩

end KCoord

theorem SiegelCoordinates.intersectionNumber_baseChange : SiegelCoordinates.Statement := fun _ =>
  ⟨fun X Y hX hY => KCoord.siegelGram_mem_posDef X Y hX hY,
    fun G hS hG => KCoord.existsUnique_siegelGram G hS hG⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset

noncomputable section

namespace KAlt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def permTerm (e : ι → ℕ) (π : Equiv.Perm ι) : MvPolynomial ι ℚ := ∏ i, X (π i) ^ e i

def sgnP (π : Equiv.Perm ι) : MvPolynomial ι ℚ := ((Equiv.Perm.sign π : ℤ) : MvPolynomial ι ℚ)

theorem alternant_eq_sum (e : ι → ℕ) : alternant e = ∑ π, sgnP π * permTerm e π := by
  simp [alternant, Matrix.det_apply', permTerm, sgnP]

theorem antisym_eq_sum (H : MvPolynomial ι ℚ) : antisym H = ∑ w, sgnP w * rename w H := by
  unfold antisym
  refine sum_congr rfl fun w _ => ?_
  rw [Algebra.smul_def, map_intCast]
  rfl

omit [DecidableEq ι] in
theorem rename_permTerm (e : ι → ℕ) (w π : Equiv.Perm ι) :
    rename w (permTerm e π) = permTerm e (w * π) := by
  simp [permTerm, map_prod, rename_X, Equiv.Perm.mul_apply]

theorem permSign_mul₂ (a b : Equiv.Perm ι) : sgnP (a * b) = sgnP a * sgnP b := by
  simp [sgnP, Equiv.Perm.sign_mul]

theorem permSign_inv₂ (a : Equiv.Perm ι) : sgnP a⁻¹ = sgnP a := by
  simp [sgnP, Equiv.Perm.sign_inv]

theorem permSign_mul_self₂ (a : Equiv.Perm ι) : sgnP a * sgnP a = 1 := by
  unfold sgnP
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem antisym_permTerm (e : ι → ℕ) (π : Equiv.Perm ι) :
    antisym (permTerm e π) = sgnP π * alternant e := by
  rw [antisym_eq_sum, alternant_eq_sum, mul_sum]
  simp_rw [rename_permTerm]
  refine (Equiv.sum_comp (Equiv.mulRight π⁻¹) _).symm.trans ?_
  refine sum_congr rfl fun u _ => ?_
  simp only [Equiv.coe_mulRight, inv_mul_cancel_right, permSign_mul₂, permSign_inv₂]
  ring

theorem antisym_sum {κ : Type*} (s : Finset κ) (f : κ → MvPolynomial ι ℚ) :
    antisym (∑ x ∈ s, f x) = ∑ x ∈ s, antisym (f x) := by

  simp only [antisym, map_sum, smul_sum]
  rw [sum_comm]

theorem antisym_sign_mul (a : Equiv.Perm ι) (p : MvPolynomial ι ℚ) :
    antisym (sgnP a * p) = sgnP a * antisym p := by
  simp only [antisym_eq_sum, map_mul, sgnP, map_intCast, mul_sum]
  refine sum_congr rfl fun w _ => ?_
  ring

variable {r s : ℕ}

theorem rename_mul_rename (α : Fin r → ℕ) (β : Fin s → ℕ) :
    rename (Sum.inl : Fin r → Fin r ⊕ Fin s) (alternant α) *
        rename (Sum.inr : Fin s → Fin r ⊕ Fin s) (alternant β) =
      ∑ σ : Equiv.Perm (Fin r), ∑ τ : Equiv.Perm (Fin s),
        sgnP (Equiv.Perm.sumCongr σ τ) * permTerm (Sum.elim α β) (Equiv.Perm.sumCongr σ τ) := by

  rw [alternant_eq_sum, alternant_eq_sum, map_sum, map_sum, sum_mul_sum]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun τ _ => ?_
  simp only [sgnP, permTerm, map_mul, map_intCast, map_prod, map_pow, rename_X,
    Equiv.Perm.sign_sumCongr, Units.val_mul, Int.cast_mul, Fintype.prod_sum_type,
    Equiv.Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr]
  ring

theorem antisym_rename_mul_rename (α : Fin r → ℕ) (β : Fin s → ℕ) :
    antisym (rename (Sum.inl : Fin r → Fin r ⊕ Fin s) (alternant α) *
        rename (Sum.inr : Fin s → Fin r ⊕ Fin s) (alternant β)) =
      ((r.factorial : ℚ) * s.factorial) • alternant (Sum.elim α β) := by
  rw [rename_mul_rename, antisym_sum]
  simp_rw [antisym_sum, antisym_sign_mul, antisym_permTerm, ← mul_assoc, permSign_mul_self₂, one_mul]
  simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

end KAlt

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def symplOmega {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (u v : l ⊕ l → R) : R :=
  u ⬝ᵥ (J l R *ᵥ v)

def symplCons {R : Type*} {n : ℕ} (p q : R) (w : Fin n ⊕ Fin n → R) :
    Fin (n + 1) ⊕ Fin (n + 1) → R :=
  Sum.elim (vecCons p fun j => w (Sum.inl j)) (vecCons q fun j => w (Sum.inr j))

def symplTail {R : Type*} {n : ℕ} (u : Fin (n + 1) ⊕ Fin (n + 1) → R) : Fin n ⊕ Fin n → R :=
  fun x => u (Sum.map Fin.succ Fin.succ x)

def symplExt {R : Type*} [Zero R] {n : ℕ} (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) R :=
  Matrix.of (Sum.elim (vecCons (symplCons α β 0) fun i => symplCons 0 0 (Q (Sum.inl i)))
    (vecCons (symplCons γ δ 0) fun i => symplCons 0 0 (Q (Sum.inr i))))

def symplReduce {n : ℕ} (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fun a b => H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) -
    H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) /
      H (Sum.inl 0) (Sum.inl 0)

def symplGram {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) : Matrix l l ℝ :=
  P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ

def SymplOmegaMem.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (l : Type) [Fintype l] [DecidableEq l]
    (M : Matrix (l ⊕ l) (l ⊕ l) R),
    M ∈ symplecticGroup l R ↔ ∀ x y, symplOmega (M x) (M y) = J l R x y

def SymplCons.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ),
    (∀ u : Fin (n + 1) ⊕ Fin (n + 1) → R,
      symplCons (u (Sum.inl 0)) (u (Sum.inr 0)) (symplTail u) = u) ∧
    ∀ (p q p' q' : R) (w w' : Fin n ⊕ Fin n → R),
      symplOmega (symplCons p q w) (symplCons p' q' w') = q * p' - p * q' + symplOmega w w'

def SymplExtMem.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R),
    α * δ - β * γ = 1 → Q ∈ symplecticGroup (Fin n) R →
    symplExt α β γ δ Q ∈ symplecticGroup (Fin (n + 1)) R

def SymplExtVecMul.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (α β γ δ p q : R)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (w : Fin n ⊕ Fin n → R),
    symplCons p q w ᵥ* symplExt α β γ δ Q = symplCons (p * α + q * γ) (p * β + q * δ) (w ᵥ* Q)

def SymplTwoRow.Statement : Prop :=
  ∀ (n : ℕ) (c d x y : ℤ), x * c + y * d = 1 →
    ∃ P ∈ symplecticGroup (Fin (n + 1 + 1)) ℤ, P (Sum.inl 0) = symplCons c 0 (symplCons d 0 0)

def SymplGcd.Statement : Prop :=
  ∀ a b : ℤ, ∃ c a' b' x y : ℤ, a = c * a' ∧ b = c * b' ∧ x * a' + y * b' = 1

def SymplOrbit.Statement : Prop :=
  ∀ (n : ℕ) (v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ),
    ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, ∃ m : ℤ, v = m • P (Sum.inl 0)

def SymplQuadDiag.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∃ (O : Matrix ι ι ℝ) (lam : ι → ℝ), (∀ i, 0 < lam i) ∧ |O.det| = 1 ∧ ∏ i, lam i = G.det ∧
      ∀ x : ι → ℝ, qf G x = ∑ i, lam i * (O *ᵥ x) i ^ 2

def SymplBoxVolume.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ), A.det ≠ 0 →
    (∀ i, 0 < a i) →
    MeasureTheory.volume {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      ENNReal.ofReal ((∏ i, 2 * a i) / |A.det|)

def SymplMinkowskiBox.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ), |A.det| = 1 →
    (∀ i, 0 < a i) → 1 < ∏ i, a i →
    ∃ v : ι → ℤ, v ≠ 0 ∧ ∀ i, |(A *ᵥ intVec v) i| < a i

def SymplMinExists.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∃ m : ℝ, IsLeast {t | ∃ v : ι → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} m

def SymplMinBound.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef → G.det = 1 →
    ∀ m : ℝ, IsLeast {t | ∃ v : ι → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} m → m ≤ Fintype.card ι

def SymplShortPrim.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∀ (v w : ι → ℤ) (m : ℤ), v = m • w → v ≠ 0 →
    (∀ u : ι → ℤ, u ≠ 0 → qf G (intVec v) ≤ qf G (intVec u)) → m = 1 ∨ m = -1

def SymplGramMem.Statement : Prop :=
  ∀ (n : ℕ) (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    P ∈ symplecticGroup (Fin n) ℤ → G ∈ symplecticGroup (Fin n) ℝ → G.PosDef →
    symplGram P G ∈ symplecticGroup (Fin n) ℝ ∧ (symplGram P G).PosDef ∧
      (∀ Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ,
        symplGram (Q * P) G = symplGram Q (symplGram P G)) ∧
      ∀ x, symplGram P G x x = qf G (intVec (P x))

def SymplFirstRow.Statement : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    G ∈ symplecticGroup (Fin (n + 1)) ℝ → G.PosDef →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      0 < ρsq ∧ ρsq ≤ 2 * ((n : ℝ) + 1) ∧
      ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, symplGram P G (Sum.inl 0) (Sum.inl 0) = ρsq

def SymplReduceMem.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    H ∈ symplecticGroup (Fin (n + 1)) ℝ → H (Sum.inl 0) (Sum.inl 0) ≠ 0 →
    symplReduce H ∈ symplecticGroup (Fin n) ℝ

def SymplReducePosDef.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    H.PosDef → (symplReduce H).PosDef

def SymplReduceConj.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    (symplExt 1 0 0 1 Q * H * (symplExt 1 0 0 1 Q)ᵀ) (Sum.inl 0) (Sum.inl 0) =
        H (Sum.inl 0) (Sum.inl 0) ∧
      symplReduce (symplExt 1 0 0 1 Q * H * (symplExt 1 0 0 1 Q)ᵀ) = Q * symplReduce H * Qᵀ

def SymplDetSchur.Statement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), A 0 0 ≠ 0 →
    A.det = A 0 0 * (Matrix.of fun i j : Fin n => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0).det

def SymplReduceStep.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
    H (Sum.inl 0) (Sum.inl 0) ≠ 0 → Q ∈ symplecticGroup (Fin n) ℤ →
    ∃ Q' ∈ symplecticGroup (Fin (n + 1)) ℤ,
      symplGram Q' H (Sum.inl 0) (Sum.inl 0) = H (Sum.inl 0) (Sum.inl 0) ∧
      (symplGram Q' H).toBlocks₁₁.det =
        H (Sum.inl 0) (Sum.inl 0) * (symplGram Q (symplReduce H)).toBlocks₁₁.det

def SymplStep.Statement : Prop :=
  ∀ (n : ℕ) (B : ℝ) (G : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    G ∈ symplecticGroup (Fin (n + 1)) ℝ → G.PosDef →
    (∀ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, H ∈ symplecticGroup (Fin n) ℝ → H.PosDef →
      ∃ P ∈ symplecticGroup (Fin n) ℤ, (symplGram P H).toBlocks₁₁.det ≤ B) →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      0 < ρsq ∧ ρsq ≤ 2 * ((n : ℝ) + 1) ∧
      ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, symplGram P G (Sum.inl 0) (Sum.inl 0) = ρsq ∧
        (symplGram P G).toBlocks₁₁.det ≤ ρsq * B

def SymplDetBound.Statement : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    G ∈ symplecticGroup (Fin n) ℝ → G.PosDef →
    ∃ P ∈ symplecticGroup (Fin n) ℤ, (symplGram P G).toBlocks₁₁.det ≤ (2 * (n : ℝ)) ^ n

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem PlueckerKernel.proof (h₁ : PlueckerNormSq.Statement) (h₂ : PlueckerUnitBound.Statement) :
    PlueckerKernel.Statement := by
  intro j m Z hZ
  set S : ℝ := ∑ I : {I : Finset (Fin (j + m)) // I.card = j}, ‖(colsOf (onePipe Z) I).det‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun I _ => by positivity
  have hnorm : ‖((S : ℝ) : ℂ)‖ = S := Complex.norm_of_nonneg hS0
  have heq : ((S : ℝ) : ℂ) = (1 + Z * Zᴴ).det := h₁ j m Z
  calc S = ‖((S : ℝ) : ℂ)‖ := hnorm.symm
    _ = ‖(1 + Z * Zᴴ).det‖ := by rw [heq]
    _ ≤ (1 + m : ℝ) ^ j := h₂ j m Z hZ

end GroundTheory.Heights₂.Heights
end
