module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
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
import Mathlib.RingTheory.PiTensorProduct
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

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.LocOpA

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [← fromBlocks_one, fromBlocks_neg]
  simp [JJ, fromBlocks_multiply]

theorem inG_blocks {g : M2 n} (h : InG g) :
    -(g.toBlocks₂₁ᴴ * g.toBlocks₁₁) + g.toBlocks₁₁ᴴ * g.toBlocks₂₁ = 0 ∧
    -(g.toBlocks₂₁ᴴ * g.toBlocks₁₂) + g.toBlocks₁₁ᴴ * g.toBlocks₂₂ = 1 ∧
    -(g.toBlocks₂₂ᴴ * g.toBlocks₁₁) + g.toBlocks₁₂ᴴ * g.toBlocks₂₁ = -1 ∧
    -(g.toBlocks₂₂ᴴ * g.toBlocks₁₂) + g.toBlocks₁₂ᴴ * g.toBlocks₂₂ = 0 := by
  have h' := h
  unfold InG at h'
  rw [← fromBlocks_toBlocks g] at h'
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, Matrix.neg_mul] at h'
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h'
  exact ⟨h1, h2, h3, h4⟩

theorem key_identity {g : M2 n} (h : InG g) (s : ℂ) (hs : star s = -s) :
    (s • g.toBlocks₁₁ + g.toBlocks₁₂)ᴴ * (s • g.toBlocks₂₁ + g.toBlocks₂₂) -
      (s • g.toBlocks₂₁ + g.toBlocks₂₂)ᴴ * (s • g.toBlocks₁₁ + g.toBlocks₁₂) = (-(2 * s)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨h1, h2, h3, h4⟩ := inG_blocks h
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set C := g.toBlocks₂₁
  set D := g.toBlocks₂₂
  have e1 : Aᴴ * C = Cᴴ * A := by rw [← sub_eq_zero, sub_eq_neg_add]; exact h1
  have e2 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h2]; abel
  have e3 : Bᴴ * C = -1 + Dᴴ * A := by rw [← h3]; abel
  have e4 : Bᴴ * D = Dᴴ * B := by rw [← sub_eq_zero, sub_eq_neg_add]; exact h4
  simp only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul]
  rw [e1, e2, e3, e4, hs]
  module

theorem det_ne_zero_of_key {P Q : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hc : c ≠ 0) (hk : Pᴴ * Q - Qᴴ * P = c • 1) :
    Q.det ≠ 0 := by
  intro h0
  obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  have e : star x ⬝ᵥ ((Pᴴ * Q - Qᴴ * P) *ᵥ x) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero,
      dotProduct_zero, dotProduct_mulVec, ← Matrix.star_mulVec, hx, star_zero, zero_dotProduct, sub_zero]
  rw [hk] at e
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at e
  rcases e with e | e
  · exact hc e
  · exact hx0 (dotProduct_star_self_eq_zero.1 e)

theorem det_first_block_ne_zero_group {g : M2 n} (h : InG g) : (u1 g).det ≠ 0 := by
  have hk := key_identity h Complex.I (by simp)
  refine det_ne_zero_of_key (c := -(2 * Complex.I)) (P := Complex.I • g.toBlocks₁₁ + g.toBlocks₁₂) (by simp) ?_
  unfold u1
  exact hk

theorem det_second_cayley_block_ne {g : M2 n} (h : InG g) : (u2 g).det ≠ 0 := by
  have hk := key_identity h (-Complex.I) (by simp)
  refine det_ne_zero_of_key (c := -(2 * -Complex.I)) (P := (-Complex.I) • g.toBlocks₁₁ + g.toBlocks₁₂) (by simp) ?_
  unfold u2
  rw [← neg_smul]
  exact hk

def linv (M : M2 n) : M2 n := -(JJ n * Mᴴ * JJ n)

theorem linv_mul {M : M2 n} (h : InG M) : linv M * M = 1 := by
  unfold linv InG at *
  rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, h, JJ_mul_JJ, neg_neg]

theorem mul_linv {M : M2 n} (h : InG M) : M * linv M = 1 := mul_eq_one_comm.1 (linv_mul h)

def mkG (M : M2 n) (h : InG M) : GR n := ⟨⟨M, linv M, mul_linv h, linv_mul h⟩, h⟩

@[simp] theorem mR_mkG (M : M2 n) (h : InG M) : mR (mkG M h) = M := rfl

theorem inG_of (g : GR n) : InG (mR g) := g.2

theorem continuous_mR : Continuous (fun g : GR n => mR g) := by unfold mR; fun_prop

theorem continuous_mkG {X : Type} [TopologicalSpace X] {f : X → M2 n} (hf : Continuous f) (h : ∀ x, InG (f x)) :
    Continuous (fun x => mkG (f x) (h x)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact hf
  change Continuous fun x => linv (f x)
  unfold linv
  fun_prop

theorem herm_isHermitian (x : Fin n → Fin n → ℝ) : (herm x).IsHermitian := by
  ext i j
  refine Complex.ext ?_ ?_ <;> (simp [herm, conjTranspose_apply]; try ring)

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG nU JJ
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_one, conjTranspose_zero, hb.eq]
  simp

theorem continuous_herm : Continuous (herm (n := n)) := by
  unfold herm
  fun_prop

def nbEl (x : Fin n → Fin n → ℝ) : GR n := mkG (nU (herm x)) (inG_nU (herm_isHermitian x))

theorem continuous_nbEl : Continuous (nbEl (n := n)) := by
  unfold nbEl
  refine continuous_mkG ?_ _
  unfold nU
  exact Continuous.matrix_fromBlocks continuous_const continuous_herm continuous_const continuous_const

end PositivityTheory.Rg.Sw.AbsSt.LocOpA
end
end

section

noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def Dm (X : Fin n → ℝ) (s : ℝ) : M2 n :=
  fromBlocks (diagonal fun j => ((Real.exp (s * X j) : ℝ) : ℂ)) 0 0 (diagonal fun j => ((Real.exp (-(s * X j)) : ℝ) : ℂ))

theorem Dm_mul (X : Fin n → ℝ) (s t : ℝ) : Dm X s * Dm X t = Dm X (s + t) := by
  simp only [Dm, fromBlocks_multiply, diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 2
  · funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

theorem Dm_zero (X : Fin n → ℝ) : Dm X 0 = 1 := by
  simp [Dm, fromBlocks_one]

def dGL (X : Fin n → ℝ) (s : ℝ) : GL (Fin n ⊕ Fin n) ℂ :=
  ⟨Dm X s, Dm X (-s), by rw [Dm_mul, add_neg_cancel, Dm_zero], by rw [Dm_mul, neg_add_cancel, Dm_zero]⟩

theorem diag_conjT_mul (f g : Fin n → ℝ) :
    (diagonal fun j => ((f j : ℝ) : ℂ))ᴴ * diagonal (fun j => ((g j : ℝ) : ℂ)) = diagonal fun j => ((f j * g j : ℝ) : ℂ) := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  congr 1
  funext j
  simp [Complex.conj_ofReal]

theorem inG_blocks (A B : Matrix (Fin n) (Fin n) ℂ) (h : Aᴴ * B = 1) : InG (fromBlocks A 0 0 B) := by
  have h' : Bᴴ * A = 1 := by
    have := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul] using this
  unfold InG JJ
  rw [fromBlocks_conjTranspose]
  simp only [conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_zero]
  rw [h, h']

theorem inG_Dm (X : Fin n → ℝ) (s : ℝ) : InG (Dm X s) := by
  apply inG_blocks
  rw [diag_conjT_mul, ← diagonal_one]
  congr 1
  funext j
  rw [← Real.exp_add]
  simp

def aD (X : Fin n → ℝ) (s : ℝ) : GR n := ⟨dGL X s, inG_Dm X s⟩

theorem isDil_aD (X : Fin n → ℝ) (s : ℝ) : IsDil X s (aD X s) := rfl

theorem isDil_unique (X : Fin n → ℝ) (s : ℝ) (a a' : GR n) (h : IsDil X s a) (h' : IsDil X s a') : a = a' := by
  apply Subtype.ext
  apply Units.ext
  exact h.trans h'.symm

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem form_inv (g : M2 n) (hg : InG g) (V : Fin n ⊕ Fin n → ℂ) :
    star (g *ᵥ V) ⬝ᵥ (JJ n *ᵥ (g *ᵥ V)) = star V ⬝ᵥ (JJ n *ᵥ V) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold InG at hg
  rw [hg]

theorem JJ_mulVec (y z : Fin n → ℂ) : JJ n *ᵥ Sum.elim y z = Sum.elim z (-y) := by
  funext i
  rcases i with i | i <;> simp [JJ, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq]

theorem dot_elim (a b c d : Fin n → ℂ) : Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem star_elim (a b : Fin n → ℂ) : star (Sum.elim a b) = Sum.elim (star a) (star b) := by
  funext i
  rcases i with i | i <;> rfl

theorem mulVec_elim (g : M2 n) (y z : Fin n → ℂ) :
    g *ᵥ Sum.elim y z = Sum.elim (g.toBlocks₁₁ *ᵥ y + g.toBlocks₁₂ *ᵥ z) (g.toBlocks₂₁ *ᵥ y + g.toBlocks₂₂ *ᵥ z) := by
  funext i
  rcases i with i | i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁,
    toBlocks₂₂]

theorem u_det_ne (g : M2 n) (hg : InG g) (w : ℂ) (hw : w = Complex.I ∨ w = -Complex.I) :
    (w • g.toBlocks₂₁ + g.toBlocks₂₂).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have key := form_inv g hg (Sum.elim (w • x) x)
  rw [mulVec_elim] at key
  have hl : g.toBlocks₂₁ *ᵥ (w • x) + g.toBlocks₂₂ *ᵥ x = 0 := by
    rw [Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.add_mulVec]
    exact hx
  rw [hl, JJ_mulVec, JJ_mulVec, star_elim, star_elim, dot_elim, dot_elim] at key
  have hs : star (w • x) = star w • star x := by
    funext j; simp [mul_comm]
  rw [hs] at key
  simp only [dotProduct_zero, zero_add, Pi.star_apply, star_zero, zero_dotProduct, dotProduct_neg, smul_dotProduct,
    dotProduct_smul, smul_eq_mul] at key
  have hxx : star x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_star_self_eq_zero.mp h)
  rcases hw with rfl | rfl
  · apply hxx
    have h2 : star Complex.I = -Complex.I := by simp [Complex.star_def]
    rw [h2] at key
    have : (-(2 * Complex.I)) * (star x ⬝ᵥ x) = 0 := by linear_combination -key
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact h
  · apply hxx
    have h2 : star (-Complex.I) = Complex.I := by simp [Complex.star_def]
    rw [h2] at key
    have : (2 * Complex.I) * (star x ⬝ᵥ x) = 0 := by linear_combination -key
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact h

theorem automorphy_first_det_ne_zero (h : GR n) : (u1 (mR h)).det ≠ 0 := u_det_ne _ h.2 _ (Or.inl rfl)

theorem automorphy_second_det_ne_zero (h : GR n) : (u2 (mR h)).det ≠ 0 := by
  have : u2 (mR h) = (-Complex.I) • (mR h).toBlocks₂₁ + (mR h).toBlocks₂₂ := by
    simp [u2, neg_smul]
  rw [this]
  exact u_det_ne _ h.2 _ (Or.inr rfl)

theorem det_mR_ne (h : GR n) : (mR h).det ≠ 0 := by
  have := (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit h.1)
  exact this.ne_zero

theorem continuous_mR : Continuous (mR (n := n)) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_group_lower_left_block : Continuous fun h : GR n => (mR h).toBlocks₂₁ :=
  continuous_mR.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inl j : Fin n ⊕ Fin n))

theorem continuous_group_lower_right_block : Continuous fun h : GR n => (mR h).toBlocks₂₂ :=
  continuous_mR.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inr j : Fin n ⊕ Fin n))

theorem spherical_section_continuous_ne_zero (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) ∧ ∀ k : GR n, F0 p q e k ≠ 0 := by
  have c1 : Continuous fun h : GR n => (mR h).det := continuous_mR.matrix_det
  have c2 : Continuous fun h : GR n => (u1 (mR h)).det := by
    have : Continuous fun h : GR n => Complex.I • (mR h).toBlocks₂₁ + (mR h).toBlocks₂₂ :=
      (continuous_group_lower_left_block.const_smul Complex.I).add continuous_group_lower_right_block
    unfold u1
    exact this.matrix_det
  have c3 : Continuous fun h : GR n => (u2 (mR h)).det := by
    have : Continuous fun h : GR n => -(Complex.I • (mR h).toBlocks₂₁) + (mR h).toBlocks₂₂ :=
      (continuous_group_lower_left_block.const_smul Complex.I).neg.add continuous_group_lower_right_block
    unfold u2
    exact this.matrix_det
  refine ⟨?_, fun k => ?_⟩
  · unfold F0 f0
    exact (c1.zpow₀ e fun h => Or.inl (det_mR_ne h)).mul
      ((c2.zpow₀ _ fun h => Or.inl (automorphy_first_det_ne_zero h)).mul (c3.zpow₀ _ fun h => Or.inl (automorphy_second_det_ne_zero h)))
  · unfold F0 f0
    exact mul_ne_zero (zpow_ne_zero _ (det_mR_ne k))
      (mul_ne_zero (zpow_ne_zero _ (automorphy_first_det_ne_zero k)) (zpow_ne_zero _ (automorphy_second_det_ne_zero k)))

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open Matrix Filter Topology Set
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

lemma JJ_mul_JJ (n : ℕ) : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  congr 1 <;> simp

lemma det_JJ_ne (n : ℕ) : (JJ n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (JJ_mul_JJ n)
  rw [det_mul, h, zero_mul, det_neg, det_one] at this
  simp at this

lemma exists_of_InG {M : M2 n} (h : InG M) : ∃ g : GR n, mR g = M := by
  have h' : Mᴴ * JJ n * M = JJ n := h
  have hdet : M.det ≠ 0 := by
    intro h0
    have hd := congrArg det h'
    rw [det_mul, det_mul, h0, mul_zero] at hd
    exact det_JJ_ne n hd.symm
  exact ⟨⟨GeneralLinearGroup.mkOfDetNeZero M hdet, h⟩, rfl⟩

lemma InG_JJ_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (JJ n * nU b) := by
  show (JJ n * nU b)ᴴ * JJ n * (JJ n * nU b) = JJ n
  simp [JJ, nU, fromBlocks_multiply, fromBlocks_conjTranspose, hb.eq]

lemma InG_lower (s : ℝ) : InG (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1) := by
  show (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1)ᴴ * JJ n *
    fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1 = JJ n
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose]

lemma yJyH {M : M2 n} (h : InG M) : M * JJ n * Mᴴ = JJ n := by
  have h' : Mᴴ * JJ n * M = JJ n := h
  have hJ := JJ_mul_JJ n
  have h1 : (-(JJ n * Mᴴ * JJ n)) * M = 1 := by
    have e : (-(JJ n * Mᴴ * JJ n)) * M = -(JJ n * (Mᴴ * JJ n * M)) := by
      simp [Matrix.mul_assoc]
    rw [e, h', hJ, neg_neg]
  have h2 := mul_eq_one_comm.mpr h1
  calc M * JJ n * Mᴴ = (M * (-(JJ n * Mᴴ * JJ n))) * JJ n := by
        simp [Matrix.mul_assoc, hJ]
    _ = JJ n := by rw [h2, Matrix.one_mul]

lemma lowerDiagonalBlockAsGL {M : M2 n} (h : InG M) : M.toBlocks₂₁ * M.toBlocks₂₂ᴴ = M.toBlocks₂₂ * M.toBlocks₂₁ᴴ := by
  have h2 := congrArg toBlocks₂₂ (yJyH h)
  rw [← fromBlocks_toBlocks M] at h2
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at h2
  exact (neg_add_eq_zero.mp h2).symm

end PositivityTheory.Rg.Sw.AbsSt.SZ
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def KR (n : ℕ) : Subgroup (GR n) where
  carrier := {k | InK (mR k)}
  one_mem' := by
    refine ⟨(GR n).one_mem, ?_⟩
    simp [mR]
  mul_mem' := by
    intro a b ha hb
    refine ⟨(a * b).2, ?_⟩
    simp only [mR, Subgroup.coe_mul, Units.val_mul, Matrix.conjTranspose_mul] at *
    calc b.1.1ᴴ * a.1.1ᴴ * (a.1.1 * b.1.1) = b.1.1ᴴ * (a.1.1ᴴ * a.1.1) * b.1.1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha.2, Matrix.mul_one, hb.2]
  inv_mem' := by
    intro a ha
    refine ⟨(a⁻¹).2, ?_⟩
    have h1 : a.1.1 * (a⁻¹).1.1 = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
    have ha2 : a.1.1ᴴ * a.1.1 = 1 := ha.2
    have h2 : (a⁻¹).1.1 = a.1.1ᴴ := by
      calc (a⁻¹).1.1 = (a.1.1ᴴ * a.1.1) * (a⁻¹).1.1 := by rw [ha2, Matrix.one_mul]
        _ = a.1.1ᴴ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    simp only [mR]
    rw [h2, Matrix.conjTranspose_conjTranspose]
    calc a.1.1 * a.1.1ᴴ = a.1.1 * (a⁻¹).1.1 := by rw [h2]
      _ = 1 := h1

def IsUp (p : GR n) : Prop := (mR p).toBlocks₂₁ = 0

def Iwa : Prop := ∀ (n : ℕ) (y : GR n), ∃ p k : GR n, IsUp p ∧ k ∈ KR n ∧ y = p * k

def CayleyBlocksInvertible : Prop := ∀ (n : ℕ) (y : GR n), (u1 (mR y)).det ≠ 0 ∧ (u2 (mR y)).det ≠ 0

def KAK : Prop := ∀ (n : ℕ) (y : GR n), ∃ (k₁ k₂ a : GR n) (X : Fin n → ℝ), k₁ ∈ KR n ∧ k₂ ∈ KR n ∧ IsDil X 1 a ∧ y = k₁ * a * k₂

def Mult : Prop := ∀ (n p q : ℕ) (e : ℤ),
  (∀ (g : GR n) (k : GR n), k ∈ KR n → F0 p q e (g * k) = F0 p q e g * F0 p q e k ∧ hLoc (g * k) = hLoc g) ∧
  ∀ (y g : GR n), IsUp y → F0 p q e (y * g) = F0 p q e y * F0 p q e g ∧ hLoc (y * g) = hLoc y * hLoc g

def SecZero : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ P, NullSec ε c P ↔ ∀ y, sL P y = 0

def DerivativeVacuumDilations : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
    ∀ (y : GR n) (r : ℕ), HasDerivAt (fun s : ℝ => iteratedDeriv r (fun s' : ℝ => F0 p q e (y * a s')) s)
      (sL ((dil c X ^ (r + 1)) 1) y) 0 ∧ iteratedDeriv r (fun s : ℝ => F0 p q e (y * a s)) 0 = sL ((dil c X ^ r) 1) y

def CycSec : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ L : C(KR n, ℂ) →L[ℂ] ℂ, (∀ y : GR n, ∀ h : C(KR n, ℂ), (∀ k, h k = F0 p q e ((k : GR n) * y)) → L h = 0) →
      ∀ P (h : C(KR n, ℂ)), (∀ k, h k = sL P (k : GR n)) → L h = 0

def Sph : Prop := ∀ (n p q : ℕ) (e : ℤ) [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure]
  [IsProbabilityMeasure μ] (y z : GR n),
  ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e (y * (k : GR n) * z) ∂μ =
    F0 p q e y * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * z) ∂μ

def LocOp : Prop := ∀ (n p q : ℕ) (e : ℤ), GoodSig n p q → ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n))
  [μ.IsHaarMeasure] [IsProbabilityMeasure μ],
  ∃ (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : GR n) (nb : (Fin n → Fin n → ℝ) → GR n) (cz : ℂ → ℂ),
    IsSingTest ψ ∧ (∀ x, mR (nb x) = nU (herm x)) ∧ Continuous nb ∧ Differentiable ℂ cz ∧ cz 0 ≠ 0 ∧
    ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y)

def HolParam : Prop := ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  [IsFiniteMeasure μ] (C : Set X), IsCompact C → μ Cᶜ = 0 → ∀ (U : Set ℂ) (F : X → ℂ → ℂ), IsOpen U →
    ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U) → (∀ x ∈ C, DifferentiableOn ℂ (F x) U) →
    DifferentiableOn ℂ (fun z => ∫ x, F x z ∂μ) U ∧
      ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ x, F x z ∂μ) z = ∫ x, iteratedDeriv r (F x) z ∂μ

def RightConn : Prop := ∀ U : Set ℂ, IsOpen U → GlobalTheory.Cont.IsRightDomain U → IsPreconnected U

def Glue : Prop := ∀ (U : Set ℂ) (f h : ℂ → ℂ) (σ : ℝ) (s₀ : ℂ), IsOpen U → GlobalTheory.Cont.IsRightDomain U → s₀ ∈ U →
  MeromorphicOn f U → AnalyticAt ℂ f s₀ → GlobalTheory.Cont.rightOf σ ⊆ U → DifferentiableOn ℂ h (GlobalTheory.Cont.rightOf σ) →
  (∀ z ∈ GlobalTheory.Cont.rightOf σ, ∀ᶠ w in 𝓝[≠] z, f w = h w) → GlobalTheory.Cont.HolValueAt h s₀ (f s₀)

end PositivityTheory.Rg.Sw.AbsSt
end
end
