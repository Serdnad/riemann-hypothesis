module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle002
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
import Mathlib.RingTheory.TotallySplit
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

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DRealH

variable {n : ℕ}

theorem blocks_of_inG {g : M2 n} (hg : InG g) :
    (g.toBlocks₁₁)ᴴ * g.toBlocks₂₁ = (g.toBlocks₂₁)ᴴ * g.toBlocks₁₁ ∧
    (g.toBlocks₁₂)ᴴ * g.toBlocks₂₂ = (g.toBlocks₂₂)ᴴ * g.toBlocks₁₂ ∧
    (g.toBlocks₁₁)ᴴ * g.toBlocks₂₂ - (g.toBlocks₂₁)ᴴ * g.toBlocks₁₂ = 1 ∧
    (g.toBlocks₁₂)ᴴ * g.toBlocks₂₁ - (g.toBlocks₂₂)ᴴ * g.toBlocks₁₁ = -1 := by
  have h := hg
  unfold InG JJ at h
  rw [← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero,
    Matrix.fromBlocks_inj] at h
  obtain ⟨h11, h12, h21, h22⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (· + (g.toBlocks₂₁)ᴴ * g.toBlocks₁₁) h11
    simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  · have := congrArg (· + (g.toBlocks₂₂)ᴴ * g.toBlocks₁₂) h22
    simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  · simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm] using h12
  · simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm] using h21

variable {A B C D : Matrix (Fin n) (Fin n) ℂ}

theorem smul_one_conj (w : ℂ) : ((w • (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ = (star w) • 1 := by
  rw [conjTranspose_smul, conjTranspose_one]

theorem cross_self (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) : (w • A + B)ᴴ * (w • C + D) - (w • C + D)ᴴ * (w • A + B) = (star w - w) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e3 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h3]; abel
  have e4 : Bᴴ * C = -1 + Dᴴ * A := by rw [← h4]; abel
  simp only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, e3, e4, h1, h2]
  module

theorem cross_conj (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) : (w • A + B)ᴴ * ((star w) • C + D) = (w • C + D)ᴴ * ((star w) • A + B) := by
  have e3 : Aᴴ * D = 1 + Cᴴ * B := eq_add_of_sub_eq h3
  have e4 : Bᴴ * C = -1 + Dᴴ * A := eq_add_of_sub_eq h4
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [h1, h2, e3, e4]
  module

theorem det_ne_zero (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) (hw : star w ≠ w) : (w • C + D).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have key := cross_self h1 h2 h3 h4 w
  have e := congrArg (fun M => star v ⬝ᵥ (M *ᵥ v)) key
  have l1 : ((w • A + B)ᴴ * (w • C + D) - (w • C + D)ᴴ * (w • A + B)) *ᵥ v
      = -((w • C + D)ᴴ *ᵥ ((w • A + B) *ᵥ v)) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, zero_sub]
  have l2 : ((star w - w) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v = (star w - w) • v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  simp only [l1, l2] at e
  rw [dotProduct_neg, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hv, star_zero, zero_dotProduct, neg_zero,
    dotProduct_smul, smul_eq_mul] at e
  have hne : star w - w ≠ 0 := sub_ne_zero.mpr hw
  have : star v ⬝ᵥ v = 0 := (mul_eq_zero.mp e.symm).resolve_left hne
  exact hv0 (dotProduct_star_self_eq_zero.mp this)

theorem conj_frac (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) (hw : star w ≠ w) :
    ((w • A + B) * (w • C + D)⁻¹)ᴴ = ((star w) • A + B) * ((star w) • C + D)⁻¹ := by
  have hw' : star (star w) ≠ star w := by
    rw [star_star]
    exact fun h => hw h.symm
  have d1 := det_ne_zero h1 h2 h3 h4 w hw
  have d2 := det_ne_zero h1 h2 h3 h4 (star w) hw'
  have u1 : IsUnit (w • C + D)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact (star_ne_zero.mpr d1).isUnit
  have u2 : IsUnit ((star w) • C + D).det := d2.isUnit
  have cc := cross_conj h1 h2 h3 h4 w
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  calc ((w • C + D)ᴴ)⁻¹ * (w • A + B)ᴴ
      = ((w • C + D)ᴴ)⁻¹ * ((w • A + B)ᴴ * ((star w) • C + D)) * ((star w) • C + D)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ u2]
    _ = ((w • C + D)ᴴ)⁻¹ * ((w • C + D)ᴴ * ((star w) • A + B)) * ((star w) • C + D)⁻¹ := by rw [cc]
    _ = ((star w) • A + B) * ((star w) • C + D)⁻¹ := by
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ u1]

end DRealH

open DRealH in
theorem dReal : DReal := by
  intro m n ε t c e y X a ha s
  funext u
  have hA : aC X (s : ℂ) = mR (a s) := by
    rw [ha s]
    unfold aC
    congr 1
    · congr 1
      funext j
      rw [Complex.ofReal_exp, Complex.ofReal_mul]
    · congr 1
      funext j
      rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
  have hmul : mR y * aC X (s : ℂ) = mR (y * a s) := by
    rw [hA]
    rfl
  have hG : InG (mR (y * a s)) := (y * a s).2
  obtain ⟨h1, h2, h3, h4⟩ := blocks_of_inG hG
  have hIs : star Complex.I ≠ Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
    intro h
    have := congrArg Complex.im h
    simp at this
    norm_num at this
  have key := conj_frac h1 h2 h3 h4 Complex.I hIs
  have sI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  rw [sI] at key
  have cI : ((Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ = (-Complex.I) • 1 := by
    rw [smul_one_conj, sI]
  unfold famC jF gZf gC jC ptZ actZ
  simp only [hmul, cI, Matrix.mul_smul, Matrix.mul_one]
  rw [key]

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilAH

variable {D : D7} {n : ℕ}

theorem cLoc_pos {l : D.what₂.Tau → ℝ} {τ : D.what₂.Tau} (h : l τ ≠ 0) : 0 < cLoc l τ := by
  unfold cLoc; have := abs_pos.2 h; positivity

theorem abs_tLoc (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : |tLoc l τ| = cLoc l τ := by
  unfold tLoc cLoc; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem trace_gramB_real {m : ℕ} (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (gramB ε b u).trace = ((∑ a ∈ Finset.univ.filter (fun a => ε a = b), ∑ j, ‖u a j‖ ^ 2 : ℝ) : ℂ) := by

  simp only [gramB, evX, Qb, map_sum, map_mul, MvPolynomial.eval_X, if_true, Bool.false_eq_true, if_false,
  Matrix.trace, Matrix.diag]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_mul', Complex.star_def]

theorem sum_filter_bool {m : ℕ} (ε : Fin m → Bool) (f : Fin m → ℝ) :
    ∑ a ∈ Finset.univ.filter (fun a => ε a = true), f a + ∑ a ∈ Finset.univ.filter (fun a => ε a = false), f a =
      ∑ a, f a := by
  rw [← Finset.sum_union]
  · congr 1; ext a; cases ε a <;> simp
  · rw [Finset.disjoint_filter]; intro a _ h; simp [h]

theorem gC_gauss {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) (δ : ℝ) (u : Fin m → Fin n → ℂ) :
    gC ε t c ((Complex.I * (δ / c : ℝ)) • 1) ((-(Complex.I * (δ / c : ℝ))) • 1) u =
      Complex.exp (-((δ * ∑ a, ∑ j, ‖u a j‖ ^ 2 : ℝ) : ℂ)) := by
  unfold gC
  congr 1
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, trace_gramB_real]
  have h := sum_filter_bool (epsT t ε) (fun a => ∑ j, ‖u a j‖ ^ 2)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← h]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem fP_one {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) :
    fP c (1 : PX m n) = gZf ε t c (Complex.I • 1) := by
  funext u
  have e1 : gZf ε t c (Complex.I • 1) u = gC ε t c ((Complex.I * (c / c : ℝ)) • 1) ((-(Complex.I * (c / c : ℝ))) • 1) u := by
    unfold gZf gC
    rw [div_self hc.ne', Complex.ofReal_one, mul_one, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_I]
  rw [e1, gC_gauss ε t c hc c u]
  simp [fP, evX, gs]

end PositivityTheory.Rg.Sw.Glob.DilAH
end
end

section

noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacG

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacU

variable {n : ℕ}

theorem inK_blocks (k : M2 n) (hk : InK k) :
    k.toBlocks₂₁ = -k.toBlocks₁₂ ∧ k.toBlocks₂₂ = k.toBlocks₁₁ := by
  unfold InK InG at hk
  obtain ⟨hG, hU⟩ := hk
  have hU' : k * kᴴ = 1 := mul_eq_one_comm.mp hU
  have hc : JJ n * k = k * JJ n := by
    calc JJ n * k = (k * kᴴ) * JJ n * k := by rw [hU', Matrix.one_mul]
      _ = k * (kᴴ * JJ n * k) := by simp only [Matrix.mul_assoc]
      _ = k * JJ n := by rw [hG]
  rw [← fromBlocks_toBlocks k] at hc
  unfold JJ at hc
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hc
  simp at hc
  exact ⟨hc.1, hc.2.1⟩

theorem mM_unitary (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) : mM u = fromBlocks u 0 0 u := by
  rw [mM, Matrix.inv_eq_right_inv hu]

theorem dR_cos_add_sin (θ : Fin n → ℝ) :
    (dR fun j => Real.cos (θ j)) + I • (dR fun j => Real.sin (θ j)) = diagonal fun j => cexp (I * (θ j : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [dR, Matrix.diagonal_apply_eq, Complex.ofReal_cos, Complex.ofReal_sin, mul_comm I, Complex.exp_mul_I]
  · simp [dR, Matrix.diagonal_apply_ne _ h]

theorem dR_cos_sub_sin (θ : Fin n → ℝ) :
    (dR fun j => Real.cos (θ j)) - I • (dR fun j => Real.sin (θ j)) = diagonal fun j => cexp (-(I * (θ j : ℂ))) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [dR, Matrix.diagonal_apply_eq, Complex.ofReal_cos, Complex.ofReal_sin, ← neg_mul, mul_comm I,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  · simp [dR, Matrix.diagonal_apply_ne _ h]

theorem uni_I (A B : Matrix (Fin n) (Fin n) ℂ) (e11 : Aᴴ * A + Bᴴ * B = 1) (e12 : Aᴴ * B + -(Bᴴ * A) = 0) :
    (A + I • B)ᴴ * (A + I • B) = 1 := by
  have hs : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
  simp only [conjTranspose_add, conjTranspose_smul, hs, add_mul, mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← e11, ← sub_eq_zero]
  have hI : I * (-I) = (1 : ℂ) := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  have h2 : Aᴴ * B = Bᴴ * A := by rw [← sub_eq_zero, sub_eq_add_neg]; exact e12
  rw [hI, one_smul, h2, neg_smul]
  abel

theorem uni_mI (A B : Matrix (Fin n) (Fin n) ℂ) (e11 : Aᴴ * A + Bᴴ * B = 1) (e12 : Aᴴ * B + -(Bᴴ * A) = 0) :
    (A - I • B)ᴴ * (A - I • B) = 1 := by
  have hs : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
  simp only [conjTranspose_sub, conjTranspose_smul, hs, sub_mul, mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← e11, ← sub_eq_zero]
  have hI : I * (-I) = (1 : ℂ) := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  have h2 : Aᴴ * B = Bᴴ * A := by rw [← sub_eq_zero, sub_eq_add_neg]; exact e12
  rw [hI, one_smul, h2, neg_smul]
  abel

theorem kak (k : M2 n) (hk : InK k) :
    ∃ (u u' : Matrix (Fin n) (Fin n) ℂ) (θ : Fin n → ℝ), uᴴ * u = 1 ∧ u'ᴴ * u' = 1 ∧
      (∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) ∧ k = mM u * kth θ * mM u' := by
  obtain ⟨h21, h22⟩ := inK_blocks k hk
  have hU : kᴴ * k = 1 := hk.2
  set A := k.toBlocks₁₁ with hA0
  set B := k.toBlocks₁₂ with hB0
  have hkA : k = fromBlocks A B (-B) A := by
    conv_lhs => rw [← fromBlocks_toBlocks k]
    rw [h21, h22]
  have hE : Aᴴ * A + Bᴴ * B = 1 ∧ Aᴴ * B + -(Bᴴ * A) = 0 := by
    rw [hkA, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hU
    obtain ⟨h1, h2, -, -⟩ := hU
    refine ⟨?_, ?_⟩
    · simpa [conjTranspose_neg] using h1
    · simpa [conjTranspose_neg] using h2
  set W := A + I • B with hW0
  set V := A - I • B with hV0
  have hW : Wᴴ * W = 1 := uni_I A B hE.1 hE.2
  have hV : Vᴴ * V = 1 := uni_mI A B hE.1 hE.2
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  have hX : (W * Vᴴ)ᴴ * (W * Vᴴ) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW,
      Matrix.one_mul, hV']
  obtain ⟨P, w, hP, hP', hw, hXd⟩ := VacU.unitary_diag (W * Vᴴ) hX
  set θ : Fin n → ℝ := fun j => Complex.arg (w j) / 2 with hθ
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => cexp (I * (θ j : ℂ)) with hD
  set Db : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => cexp (-(I * (θ j : ℂ))) with hDb
  have hDDb : D * Db = 1 := by
    rw [hD, hDb, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext j
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hDbH : Dbᴴ = D := by
    rw [hD, hDb, diagonal_conjTranspose]
    congr 1; funext j
    simp only [Pi.star_apply]
    rw [Complex.star_def, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
      neg_mul, neg_neg]
  have hDb2 : Db * Db = (diagonal w)ᴴ := by
    rw [hDb, diagonal_mul_diagonal, diagonal_conjTranspose]
    congr 1; funext j
    simp only [Pi.star_apply]
    have hwj : w j = cexp (↑(Complex.arg (w j)) * I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (w j)]
      rw [hw j, Complex.ofReal_one, one_mul]
    rw [← Complex.exp_add]
    conv_rhs => rw [hwj]
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    simp only [hθ]
    push_cast
    ring
  set u' := Db * Pᴴ * W with hu0
  have hu' : u'ᴴ * u' = 1 := by
    rw [hu0, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hDbH]
    calc Wᴴ * (P * D) * (Db * Pᴴ * W) = Wᴴ * (P * (D * Db) * Pᴴ) * W := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDDb, Matrix.mul_one, hP', Matrix.mul_one, hW]
  have hPD : P * D * u' = W := by
    calc P * D * u' = P * (D * Db) * Pᴴ * W := by simp only [hu0, Matrix.mul_assoc]
      _ = W := by rw [hDDb, Matrix.mul_one, hP', Matrix.one_mul]
  have hPDb : P * Db * u' = V := by
    calc P * Db * u' = (P * (Db * Db) * Pᴴ) * W := by simp only [hu0, Matrix.mul_assoc]
      _ = (W * Vᴴ)ᴴ * W := by
          rw [hDb2, hXd, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
            Matrix.mul_assoc]
          simp only [Matrix.mul_assoc]
      _ = V := by
          rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, hW, Matrix.mul_one]
  have hCS := dR_cos_add_sin θ
  have hCSm := dR_cos_sub_sin θ
  rw [← hD] at hCS
  rw [← hDb] at hCSm
  set C := dR fun j => Real.cos (θ j) with hC0
  set S := dR fun j => Real.sin (θ j) with hS0
  have e1 : P * C * u' + I • (P * S * u') = W := by
    rw [← hPD, ← hCS, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : P * C * u' - I • (P * S * u') = V := by
    rw [← hPDb, ← hCSm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hXA : P * C * u' = A := by
    have h := congrArg₂ (· + ·) e1 e2
    simp only [hW0, hV0] at h
    have h2 : (2 : ℂ) • (P * C * u') = (2 : ℂ) • A := by
      rw [two_smul, two_smul]
      convert h using 1 <;> abel
    exact smul_right_injective _ two_ne_zero h2
  have hYB : P * S * u' = B := by
    have h := congrArg₂ (· - ·) e1 e2
    simp only [hW0, hV0] at h
    have h2 : (2 * I) • (P * S * u') = (2 * I) • B := by
      rw [mul_smul, mul_smul, two_smul, two_smul]
      convert h using 1 <;> abel
    exact smul_right_injective _ (mul_ne_zero two_ne_zero Complex.I_ne_zero) h2
  refine ⟨P, u', θ, hP, hu', fun j => ⟨?_, ?_⟩, ?_⟩
  · have := Complex.neg_pi_lt_arg (w j)
    simp only [hθ]
    linarith
  · have := Complex.arg_le_pi (w j)
    simp only [hθ]
    linarith
  · refine hkA.trans ?_
    rw [mM_unitary P hP, mM_unitary u' hu', kth_eq, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul]
    rw [← hC0, ← hS0]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_zero, add_zero, hXA, hYB]

end PositivityTheory.Rg.Sw.Glob.VacG
end
end
