module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
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

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcH

variable {m n : ℕ}

def vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) : Fin m → Fin n → ℂ :=
  fun a j => u a j * (Real.exp (s * X j) : ℂ)

def crd (v : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ℂ := if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1

theorem evX_eq (P : PX m n) (v : Fin m → Fin n → ℂ) : evX P v = MvPolynomial.eval (crd v) P := rfl

theorem crd_vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (k : Fin m × Fin n × Bool) (s : ℝ) :
    crd (vS u X s) k = crd u k * ((Real.exp (s * X k.2.1) : ℝ) : ℂ) := by
  unfold crd vS
  split_ifs
  · rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  · rfl

theorem hasDerivAt_expX (x s : ℝ) :
    HasDerivAt (fun s : ℝ => ((Real.exp (s * x) : ℝ) : ℂ)) ((x : ℂ) * ((Real.exp (s * x) : ℝ) : ℂ)) s := by
  have h := ((hasDerivAt_id s).mul_const x).exp
  simp only [id, one_mul] at h
  have h2 := h.ofReal_comp
  have e : ((x : ℂ) * ((Real.exp (s * x) : ℝ) : ℂ)) = ((Real.exp (s * x) * x : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  exact h2

theorem crd_hasDeriv (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (k : Fin m × Fin n × Bool) (s : ℝ) :
    HasDerivAt (fun s : ℝ => crd (vS u X s) k) ((X k.2.1 : ℂ) * crd (vS u X s) k) s := by
  have h := (hasDerivAt_expX (X k.2.1) s).const_mul (crd u k)
  have e1 : (fun s : ℝ => crd (vS u X s) k) = fun s => crd u k * ((Real.exp (s * X k.2.1) : ℝ) : ℂ) :=
    funext fun s => crd_vS u X k s
  rw [e1, crd_vS]
  exact h.congr_deriv (by ring)

theorem pderiv_mul_X (p : PX m n) (k i : Fin m × Fin n × Bool) :
    pderiv i (p * MvPolynomial.X k) = pderiv i p * MvPolynomial.X k + if i = k then p else 0 := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : i = k
  · subst h; simp [add_comm, mul_comm]
  · simp [h, Ne.symm h, mul_comm]

theorem eval_hasDeriv (P : PX m n) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => evX P (vS u X s))
      (∑ k, evX (pderiv k P) (vS u X s) * ((X k.2.1 : ℂ) * crd (vS u X s) k)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [evX_eq, eval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [evX_eq, map_add (f := _), add_mul, Finset.sum_add_distrib] at *
    exact hp.add hq
  | mul_X p k hp =>
    have h := hp.mul (crd_hasDeriv u X k s)
    simp only [evX_eq] at *
    have efun : (fun s : ℝ => eval (crd (vS u X s)) (p * MvPolynomial.X k)) =
        fun s => eval (crd (vS u X s)) p * crd (vS u X s) k := by
      funext s'; simp [eval_mul, eval_X]
    rw [efun]
    refine h.congr_deriv ?_
    symm
    set D : Fin m × Fin n × Bool → ℂ := fun i => (X i.2.1 : ℂ) * crd (vS u X s) i with hD
    calc (∑ i, eval (crd (vS u X s)) (pderiv i (p * MvPolynomial.X k)) * D i)
        = ∑ i, (eval (crd (vS u X s)) (pderiv i p) * D i * crd (vS u X s) k +
            (if i = k then eval (crd (vS u X s)) p * D i else 0)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pderiv_mul_X]
          split_ifs with hik
          · simp [eval_mul, eval_X]; ring
          · simp [eval_mul, eval_X]; ring
      _ = (∑ i, eval (crd (vS u X s)) (pderiv i p) * D i) * crd (vS u X s) k + eval (crd (vS u X s)) p * D k := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_ite_eq']
          simp

theorem crd_false (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : crd v (a, j, false) = v a j := rfl

theorem crd_true (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : crd v (a, j, true) = star (v a j) := rfl

theorem evX_dil (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (v : Fin m → Fin n → ℂ) :
    evX (dil c X P) v = ((m : ℂ) * ∑ j, (X j : ℂ)) * evX P v +
      ∑ k, evX (pderiv k P) v * ((X k.2.1 : ℂ) * crd v k) -
      (2 * c : ℂ) * (∑ a, ∑ j, (X j : ℂ) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) * evX P v := by
  have hnorm : ∀ a j, ((‖v a j‖ ^ 2 : ℝ) : ℂ) = v a j * star (v a j) := by
    intro a j
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

  simp only [dil, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
  LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply,
  Derivation.coeFn_coe, evX_eq, map_sum, map_add, map_sub, map_mul, MvPolynomial.smul_eval, eval_X, smul_eq_mul]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, crd_false, crd_true, hnorm]
  set E := (eval (crd v)) P with hE
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun a j => (eval (crd v)) ((pderiv (a, j, true)) P) * ((X j : ℂ) * star (v a j)) +
        (eval (crd v)) ((pderiv (a, j, false)) P) * ((X j : ℂ) * v a j)),
    Finset.sum_comm (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun a j => (X j : ℂ) * (v a j * star (v a j)))]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun a _ => ?_
    ring

end DCalcH

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {n : ℕ}

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem inG_mR (g : GR n) : InG (mR g) := g.2

theorem neg_one_blocks : (-1 : M2 n) = fromBlocks (-1) 0 0 (-1) := by
  rw [← fromBlocks_one, fromBlocks_neg, neg_zero]

theorem JJ_sq : JJ n * JJ n = -1 := by
  rw [neg_one_blocks]; simp [JJ, fromBlocks_multiply]

theorem JJ_conjTranspose : (JJ n)ᴴ = -JJ n := by
  simp [JJ, fromBlocks_conjTranspose, fromBlocks_neg]

theorem flip_of_inG {M : M2 n} (h : InG M) : M * JJ n * Mᴴ = JJ n := by
  have h' : Mᴴ * JJ n * M = JJ n := h
  have h1 : (Mᴴ * JJ n) * (-(M * JJ n)) = 1 := by
    rw [mul_neg, ← mul_assoc, h', JJ_sq, neg_neg]
  have h2 := mul_eq_one_comm.mp h1
  have h3 : M * JJ n * (Mᴴ * JJ n) = -1 := by
    rw [neg_mul] at h2
    exact neg_eq_iff_eq_neg.mp h2
  calc M * JJ n * Mᴴ = -(M * JJ n * (Mᴴ * JJ n) * JJ n) := by
        simp only [mul_assoc, JJ_sq, mul_neg, mul_one, neg_neg]
    _ = JJ n := by rw [h3]; simp

theorem lagr (g : GR n) :
    (mR g).toBlocks₂₁ * ((mR g).toBlocks₂₂)ᴴ = (mR g).toBlocks₂₂ * ((mR g).toBlocks₂₁)ᴴ := by
  have h := flip_of_inG (inG_mR g)
  have h22 := congrArg Matrix.toBlocks₂₂ h
  rw [← Matrix.fromBlocks_toBlocks (mR g)] at h22
  simp only [JJ, fromBlocks_multiply, fromBlocks_conjTranspose, toBlocks_fromBlocks₂₂, mul_zero, zero_add,
    add_zero, mul_one, mul_neg, neg_mul] at h22
  exact (neg_add_eq_zero.mp h22).symm

theorem vec_zero (g : GR n) (z : ℂ) (hz : z.im ≠ 0) (v : Fin n → ℂ)
    (hv : v ᵥ* (z • (mR g).toBlocks₂₁ + (mR g).toBlocks₂₂) = 0) : v = 0 := by
  have hl := lagr g
  rw [Matrix.vecMul_add, Matrix.vecMul_smul] at hv
  have hW : v ᵥ* (mR g).toBlocks₂₂ = -(z • (v ᵥ* (mR g).toBlocks₂₁)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hv
  have key : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (v ᵥ* A) ⬝ᵥ star (v ᵥ* B) = (v ᵥ* (A * Bᴴ)) ⬝ᵥ star v := by
    intro A B
    rw [Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have hsym : (v ᵥ* (mR g).toBlocks₂₁) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₂) =
      (v ᵥ* (mR g).toBlocks₂₂) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₁) := by
    rw [key, key, hl]
  rw [hW] at hsym
  simp only [star_neg, star_smul, dotProduct_neg, neg_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul] at hsym
  have hz' : z - star z ≠ 0 := by
    intro h0
    apply hz
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hY0 : (v ᵥ* (mR g).toBlocks₂₁) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₁) = 0 := by
    have : (z - star z) * ((v ᵥ* (mR g).toBlocks₂₁) ⬝ᵥ star (v ᵥ* (mR g).toBlocks₂₁)) = 0 := by
      linear_combination hsym
    exact (mul_eq_zero.mp this).resolve_left hz'
  have hY : v ᵥ* (mR g).toBlocks₂₁ = 0 := dotProduct_self_star_eq_zero.mp hY0
  have hD : v ᵥ* (mR g).toBlocks₂₂ = 0 := by
    rw [hW, hY, smul_zero, neg_zero]
  have hu : (Sum.elim 0 v : Fin n ⊕ Fin n → ℂ) ᵥ* mR g = 0 := by
    ext j
    cases j with
    | inl k =>
      have := congrFun hY k
      simpa [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, toBlocks₂₁] using this
    | inr k =>
      have := congrFun hD k
      simpa [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, toBlocks₂₂] using this
  have hinv : mR g * ((g : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ).val = 1 := by
    simp [mR]
  have hu0 : (Sum.elim 0 v : Fin n ⊕ Fin n → ℂ) = 0 := by
    have := congrArg (fun w => w ᵥ* ((g : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ).val) hu
    simp only [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one, Matrix.zero_vecMul] at this
    exact this
  ext i
  simpa using congrFun hu0 (Sum.inr i)

theorem automorphy_first_det_ne_zero (g : GR n) : (u1 (mR g)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := (exists_vecMul_eq_zero_iff).mpr h
  exact hv0 (vec_zero g Complex.I (by simp) v (by simpa [u1] using hv))

theorem automorphy_second_det_ne_zero (g : GR n) : (u2 (mR g)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := (exists_vecMul_eq_zero_iff).mpr h
  exact hv0 (vec_zero g (-Complex.I) (by simp) v (by simpa [u2, neg_smul] using hv))

theorem det_ne (g : GR n) : (mR g).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit).ne_zero

theorem cont_mR : Continuous (mR : GR n → M2 n) := Units.continuous_val.comp continuous_subtype_val

theorem continuous_vacuum_lower_left_block : Continuous (fun g : GR n => (mR g).toBlocks₂₁) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply (Sum.inl j)).comp ((continuous_apply (Sum.inr i)).comp cont_mR)

theorem continuous_vacuum_lower_right_block : Continuous (fun g : GR n => (mR g).toBlocks₂₂) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply (Sum.inr j)).comp ((continuous_apply (Sum.inr i)).comp cont_mR)

theorem continuous_vacuum_section (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have hdet : Continuous fun g : GR n => (mR g).det := cont_mR.matrix_det
  have h1 : Continuous fun g : GR n => (u1 (mR g)).det := by
    refine Continuous.matrix_det ?_
    unfold u1; exact (continuous_vacuum_lower_left_block.const_smul Complex.I).add continuous_vacuum_lower_right_block
  have h2 : Continuous fun g : GR n => (u2 (mR g)).det := by
    refine Continuous.matrix_det ?_
    unfold u2; exact (continuous_vacuum_lower_left_block.const_smul Complex.I).neg.add continuous_vacuum_lower_right_block
  have : F0 (n := n) p q e = fun g => (mR g).det ^ e * ((u1 (mR g)).det ^ (-(p : ℤ)) * (u2 (mR g)).det ^ (-(q : ℤ))) := rfl
  rw [this]
  exact (hdet.zpow₀ e fun g => Or.inl (det_ne g)).mul
    ((h1.zpow₀ _ fun g => Or.inl (automorphy_first_det_ne_zero g)).mul (h2.zpow₀ _ fun g => Or.inl (automorphy_second_det_ne_zero g)))

theorem lower_left_block_mul {Y G : M2 n} (hY : Y.toBlocks₂₁ = 0) : (Y * G).toBlocks₂₁ = Y.toBlocks₂₂ * G.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks Y, ← fromBlocks_toBlocks G]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁, hY, zero_mul, zero_add]

theorem lower_right_block_mul {Y G : M2 n} (hY : Y.toBlocks₂₁ = 0) : (Y * G).toBlocks₂₂ = Y.toBlocks₂₂ * G.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks Y, ← fromBlocks_toBlocks G]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₂, hY, zero_mul, zero_add]

theorem vacuum_section_mul_parabolic (p q : ℕ) (e : ℤ) (y g : GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    F0 p q e (y * g) = F0 p q e y * F0 p q e g := by
  have e1 : u1 (mR y * mR g) = (mR y).toBlocks₂₂ * u1 (mR g) := by
    simp only [u1, lower_left_block_mul hy, lower_right_block_mul hy, Matrix.mul_add, Matrix.mul_smul]
  have e2 : u2 (mR y * mR g) = (mR y).toBlocks₂₂ * u2 (mR g) := by
    simp only [u2, lower_left_block_mul hy, lower_right_block_mul hy, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]
  have e1' : u1 (mR y) = (mR y).toBlocks₂₂ := by
    simp [u1, hy]
  have e2' : u2 (mR y) = (mR y).toBlocks₂₂ := by
    simp [u2, hy]
  simp only [F0, f0, mR_mul, e1, e2, e1', e2', det_mul, mul_zpow]
  ring

theorem weight_factor_one (p q : ℕ) (e : ℤ) : F0 p q e (1 : GR n) = 1 := by
  have h21 : (1 : M2 n).toBlocks₂₁ = 0 := by rw [← fromBlocks_one, toBlocks_fromBlocks₂₁]
  have h22 : (1 : M2 n).toBlocks₂₂ = 1 := by rw [← fromBlocks_one, toBlocks_fromBlocks₂₂]
  simp [F0, f0, u1, u2, mR_one, h21, h22]

theorem JJ_nU (b : Matrix (Fin n) (Fin n) ℂ) : JJ n * nU b = fromBlocks 0 1 (-1) (-b) := by
  simp [JJ, nU, fromBlocks_multiply]

theorem det_JJ : (JJ n).det = 1 := by
  have : JJ n = fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 := by
    simp [JJ, fromBlocks_multiply]
  rw [this, det_mul, det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁]
  simp

theorem det_nU (b : Matrix (Fin n) (Fin n) ℂ) : (nU b).det = 1 := by
  rw [nU, det_fromBlocks_zero₂₁]; simp

theorem vacuum_section_big_cell (p q : ℕ) (e : ℤ) (h : GR n) (b : Matrix (Fin n) (Fin n) ℂ) (hh : mR h = JJ n * nU b) :
    F0 p q e h = ((-Complex.I) ^ n * (1 - Complex.I • b).det) ^ (-(p : ℤ)) *
      (Complex.I ^ n * (1 + Complex.I • b).det) ^ (-(q : ℤ)) := by
  have e1 : u1 (JJ n * nU b) = (-Complex.I) • (1 - Complex.I • b) := by
    rw [JJ_nU]
    ext i j
    simp [u1, Matrix.one_apply]
    split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  have e2 : u2 (JJ n * nU b) = Complex.I • (1 + Complex.I • b) := by
    rw [JJ_nU]
    ext i j
    simp [u2, Matrix.one_apply]
    split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  simp only [F0, f0, hh, det_mul, det_JJ, det_nU, one_mul, _root_.one_zpow, e1, e2, det_smul,
    Fintype.card_fin]

end PositivityTheory.Rg.Sw.Glob.Vac
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem isUnit_det_of_inG {g : M2 n} (hg : InG g) : IsUnit g.det := by
  have hJ : JJ n * JJ n = -1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp [JJ, Matrix.fromBlocks_multiply]
  have h1 : (JJ n).det * (JJ n).det = (-1 : ℂ) ^ (Fintype.card (Fin n ⊕ Fin n)) := by
    rw [← Matrix.det_mul, hJ, Matrix.det_neg, Matrix.det_one, mul_one]
  have hJd : (JJ n).det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1.symm
  have e := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul] at e
  refine isUnit_iff_ne_zero.2 fun h0 => hJd ?_
  rw [h0, mul_zero] at e
  exact e.symm

def mkGR (g : M2 n) (hg : InG g) : GR n :=
  ⟨⟨g, g⁻¹, Matrix.mul_nonsing_inv g (isUnit_det_of_inG hg), Matrix.nonsing_inv_mul g (isUnit_det_of_inG hg)⟩, hg⟩

def IsNElt (g : GR n) : Prop := ∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR g = nU b

def IsMElt (g : GR n) : Prop :=
  ∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR g = fromBlocks a 0 0 (a⁻¹)ᴴ

def IsWElt (g : GR n) : Prop := mR g = JJ n

def GenSt : Prop :=
  ∀ n : ℕ, ∀ g : GR n, g ∈ Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h}

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end

section

noncomputable section

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def SigAtLeast (D : D7) (V : HSp D) (k : ℕ) : Prop :=
  ∀ τ : D.what₂.Tau, ∃ (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsUnit fr.det ∧ frᴴ * gramAt D V τ * fr = Matrix.diagonal (sgn ε) ∧ k ≤ cnt ε true ∧ k ≤ cnt ε false

def WittLBlt : Prop :=
  ∀ (D : D7) (V : HSp D) (k : ℕ), 2 * k < V.rank → SigAtLeast D V k → k ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V

def WittLBeq : Prop :=
  ∀ (D : D7) (V : HSp D) (k : ℕ), 2 * k = V.rank → SigAtLeast D V k → k ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def genSet (D : D7) (n : ℕ) : Set (G D n) :=
  {g | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1)}

def blkDm {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

def eI {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if i ∈ I then 1 else 0

def wIm {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 (1 - eI I) (eI I) (-eI I) (1 - eI I)

def J2 (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R := blk4 0 1 (-1) 0

def UnitD : Prop :=
  ∀ (D : D7) (n : ℕ) (g : G D n), IsUnit (blkDm (mat g)).det → g ∈ Subgroup.closure (genSet D n)

def PIn : Prop := ∀ (D : D7) (n : ℕ), ∀ p ∈ P D n, p ∈ Subgroup.closure (genSet D n)

def LocRedField : Prop :=
  ∀ (k : Type) [Field k] (σ : k →+* k), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (g : GL (Fin (n + n)) k),
    g ∈ Formalism.UG.UJ σ (J2 k n) → ∃ I : Finset (Fin n), IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * wIm I)).det

def LocRedSplit : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (g : GL (Fin (n + n)) k), ∃ (a d : GL (Fin n) k) (I : Finset (Fin n)),
    IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * blk4 a.1 0 0 d.1 * wIm I)).det

def KInInf : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (mat k).map (finPart D) = 1 → k ∈ Subgroup.closure (genSet D n)

def KInFin : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (∀ τ, (mat k).map (Formalism.IndefR.Eqv.psiT D τ) = 1) → k ∈ Subgroup.closure (genSet D n)

end PositivityTheory.Rg.Sw.Glob
end
end
