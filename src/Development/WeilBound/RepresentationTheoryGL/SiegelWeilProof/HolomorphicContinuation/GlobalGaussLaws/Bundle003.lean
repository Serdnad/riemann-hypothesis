module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDense
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.LocInstH

variable {σ : Type}

def reP (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (AddMonoidAlgebra.coeff p m).re

def imaginary (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (AddMonoidAlgebra.coeff p m).im

theorem coeff_reP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (reP p) m = (AddMonoidAlgebra.coeff p m).re := by
  classical
  unfold reP
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : AddMonoidAlgebra.coeff p m = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem coeff_imP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (imaginary p) m = (AddMonoidAlgebra.coeff p m).im := by
  classical
  unfold imaginary
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : AddMonoidAlgebra.coeff p m = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem eq_map_re_add_im (p : MvPolynomial σ ℂ) :
    p = map (algebraMap ℝ ℂ) (reP p) + C Complex.I * map (algebraMap ℝ ℂ) (imaginary p) := by
  ext m
  rw [MvPolynomial.coeff_add, coeff_C_mul, coeff_map, coeff_map, coeff_reP, coeff_imP]
  apply Complex.ext <;> simp

theorem eq_zero_of_eval_real (p : MvPolynomial σ ℂ) (h : ∀ y : σ → ℝ, eval (fun i => (y i : ℂ)) p = 0) : p = 0 := by
  apply GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_real <;> assumption

end PositivityTheory.Rg.Sw.Glob.LocInstH
end
end

section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.DecH

variable {n : ℕ}

theorem det_sub_I_smul_ne_zero {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D))
    (hu : IsUnit (fromBlocks A B C D).det) : (A - Complex.I • C).det ≠ 0 := by
  classical
  have hrel : Cᴴ * A = Aᴴ * C := by
    have h' := h
    unfold PositivityTheory.Rg.Sw.InG PositivityTheory.Rg.Sw.JJ at h'
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h'
    have h1 := (fromBlocks_inj.1 h').1
    simp at h1
    exact neg_add_eq_zero.1 h1
  have hM : (A - Complex.I • C)ᴴ * (A - Complex.I • C) = Aᴴ * A + Cᴴ * C := by
    simp only [conjTranspose_sub, conjTranspose_smul, Complex.star_def, Complex.conj_I,
      sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, hrel]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  have hv2 : (Aᴴ * A + Cᴴ * C) *ᵥ v = 0 := by
    rw [← hM, ← mulVec_mulVec, hv, mulVec_zero]
  set V : Fin n ⊕ Fin n → ℂ := Sum.elim v 0 with hV
  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fromBlocks A 0 C 0 with hPdef
  have hP : (Pᴴ * P) *ᵥ V = 0 := by
    rw [hPdef, fromBlocks_conjTranspose, fromBlocks_multiply]
    simp [hV, fromBlocks_mulVec, hv2]
  have hP2 := (conjTranspose_mul_self_mulVec_eq_zero _ _).1 hP
  have hg : fromBlocks A B C D *ᵥ V = 0 := by
    have := hP2
    simp [hV, hPdef, fromBlocks_mulVec] at this ⊢
    exact this
  have hV0 : V ≠ 0 := by
    intro h0
    apply hv0
    funext i
    have := congrFun h0 (Sum.inl i)
    simpa [hV] using this
  exact hu.ne_zero (exists_mulVec_eq_zero_iff.1 ⟨V, hV0, hg⟩)

theorem exists_real_det_ne_zero {A C : Matrix (Fin n) (Fin n) ℂ} (h : (A - Complex.I • C).det ≠ 0) :
    ∃ t : ℝ, (A - (t : ℂ) • C).det ≠ 0 := by
  classical
  by_contra hne
  push_neg at hne
  set p : Polynomial ℂ :=
    ((Polynomial.X : Polynomial ℂ) • (-C).map Polynomial.C + A.map Polynomial.C).det with hp
  have heval : ∀ z : ℂ, p.eval z = (A - z • C).det := by
    intro z
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro _ ⟨t, rfl⟩
    rw [Set.mem_setOf_eq, Polynomial.IsRoot, heval]
    exact hne t
  apply h
  have := heval Complex.I
  rw [hp0, Polynomial.eval_zero] at this
  exact this.symm

end PositivityTheory.Rg.Sw.Glob.DecH
end
end

section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.DecH

variable {n : ℕ}

theorem jj_mul_jj : JJ n * JJ n = -1 := by
  unfold JJ
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add, neg_zero]
  rw [← fromBlocks_one, fromBlocks_neg]
  simp

theorem inG_dual {g : M2 n} (h : InG g) : g * JJ n * gᴴ = JJ n := by
  have h' : gᴴ * (JJ n * g) = JJ n := by
    rw [← Matrix.mul_assoc]
    exact h
  have hK : (-(JJ n * gᴴ * JJ n)) * g = 1 := by
    simp only [Matrix.neg_mul, Matrix.mul_assoc, h', jj_mul_jj, neg_neg]
  have hK' : g * (-(JJ n * gᴴ * JJ n)) = 1 := mul_eq_one_comm.mp hK
  calc g * JJ n * gᴴ = g * JJ n * gᴴ * (-(JJ n * JJ n)) := by
        rw [jj_mul_jj, neg_neg, Matrix.mul_one]
    _ = (g * -(JJ n * gᴴ * JJ n)) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [hK', Matrix.one_mul]

theorem inG_blocks {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D)) :
    Aᴴ * C = Cᴴ * A ∧ Aᴴ * D - Cᴴ * B = 1 ∧ Bᴴ * D = Dᴴ * B := by
  unfold InG JJ at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  obtain ⟨h1, h2, -, h4⟩ := h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add] at h1 h2 h4
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← h1]
    abel
  · rw [← h2]
    abel
  · rw [← sub_eq_zero, ← h4]
    abel

theorem inG_blocks_dual {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D)) :
    A * Bᴴ = B * Aᴴ ∧ A * Dᴴ - B * Cᴴ = 1 ∧ C * Bᴴ - D * Aᴴ = -1 ∧ C * Dᴴ = D * Cᴴ := by
  have h' : InG (fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ) := by
    have hd := inG_dual h
    unfold InG
    rw [← fromBlocks_conjTranspose, conjTranspose_conjTranspose]
    exact hd
  obtain ⟨h1, h2, h3⟩ := inG_blocks h'
  simp only [conjTranspose_conjTranspose] at h1 h2 h3
  refine ⟨h1, h2, ?_, h3⟩
  have h4 := congrArg conjTranspose h2
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_one] at h4
  rw [← neg_sub, h4]

end PositivityTheory.Rg.Sw.Glob.DecH
end
end

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem inG_rel {g : M2 n} (hg : InG g) :
    g.toBlocks₁₁ᴴ * g.toBlocks₂₁ = g.toBlocks₂₁ᴴ * g.toBlocks₁₁ ∧
    g.toBlocks₁₂ᴴ * g.toBlocks₂₂ = g.toBlocks₂₂ᴴ * g.toBlocks₁₂ ∧
    g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂ = 1 := by
  have h := hg
  unfold InG JJ at h
  rw [← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul,
    Matrix.one_mul, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂] at h
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h
  refine ⟨?_, ?_, ?_⟩
  · have := h1; rw [neg_add_eq_sub, sub_eq_zero] at this; exact this
  · have := h4; rw [neg_add_eq_sub, sub_eq_zero] at this; exact this
  · have := h2; rw [neg_add_eq_sub] at this; exact this

theorem inK_blocks {g : M2 n} (hg : InK g) : g.toBlocks₂₁ = -g.toBlocks₁₂ ∧ g.toBlocks₂₂ = g.toBlocks₁₁ := by
  obtain ⟨hG, hU⟩ := hg
  have hinv : g * gᴴ = 1 := mul_eq_one_comm.1 hU
  have hc : JJ n * g = g * JJ n := by
    calc JJ n * g = (g * gᴴ) * JJ n * g := by rw [hinv, Matrix.one_mul]
      _ = g * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
      _ = g * JJ n := by rw [hG]
  unfold JJ at hc
  rw [← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hc
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul,
    Matrix.one_mul, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂] at hc
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 hc
  exact ⟨h1, h2⟩

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end
