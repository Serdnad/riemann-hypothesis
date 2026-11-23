module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZIterA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZIterB
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
import Mathlib.Order.CompletePartialOrder
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.DB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA

lemma leviDifferential_add (k j ρ : ℕ) (Q Q' : Matrix (Fin j) (Fin j) ℂ) :
    dmuP k j ρ (Q + Q') = dmuP k j ρ Q + dmuP k j ρ Q' := by
  unfold dmuP
  rw [P.Ux4.block3_add]
  simp only [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, add_zero, neg_add]

lemma leviDifferential_smul (k j ρ : ℕ) (c : ℝ) (Q : Matrix (Fin j) (Fin j) ℂ) :
    dmuP k j ρ (c • Q) = c • dmuP k j ρ Q := by
  unfold dmuP
  apply P.Ux4.ext_eB
  rintro (((a | a) | a)) (((b | b) | b)) <;>
    simp [P.Ux4.block3_apply, Matrix.conjTranspose_smul]

lemma block_matrix_two_zero_add {p s : ℕ} (e e' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (e + e') = blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 e + blk2 0 0 0 e' := by
  ext i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;> simp

lemma block_matrix_two_zero_smul {p s : ℕ} (c : ℝ) (e : Matrix (Fin s) (Fin s) ℂ) :
    blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (c • e) = c • blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 e := by
  ext i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;> simp

lemma symmetricScalarBlockMatrix_one_zero {p s : ℕ} : blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
  simp [blk2, Matrix.fromBlocks_one]

lemma block_matrix_two_line {p s : ℕ} (t : ℝ) (A : Matrix (Fin s) (Fin s) ℂ) :
    blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 + t • A) = 1 + t • blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 A := by
  rw [← symmetricScalarBlockMatrix_one_zero]
  ext i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;> simp

def lamZ (k : ℕ) {p s : ℕ} (ρ : ℕ) {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) (e : Matrix (Fin s) (Fin s) ℂ) :
    B.Mat k (p + s + ρ) :=
  (Rn k (p + s) ρ ξ.1.2)⁻¹ *
    dmuP k (p + s) ρ ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
      blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 e * blk2 1 (Matrix.of ξ.2.1.2) 0 1) *
    Rn k (p + s) ρ ξ.1.2

def lamL (k : ℕ) {p s : ℕ} (ρ : ℕ) {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) :
    Matrix (Fin s) (Fin s) ℂ →ₗ[ℝ] B.Mat k (p + s + ρ) where
  toFun := lamZ k ρ ξ
  map_add' e e' := by
    simp only [lamZ, block_matrix_two_zero_add, Matrix.mul_add, Matrix.add_mul, leviDifferential_add]
  map_smul' c e := by
    simp only [lamZ, block_matrix_two_zero_smul, Matrix.mul_smul, Matrix.smul_mul, leviDifferential_smul, RingHom.id_apply]

lemma coef_sum {s : ℕ} (Z W : G.Mat s) :
    ∑ i : Fin s × Fin s × Bool, coefZ Z W i • eMat i.1 i.2.1 i.2.2 = (Matrix.of Z)⁻¹ * Matrix.of W := by
  ext x y
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, eMat, Matrix.of_apply]
  simp [Fintype.sum_prod_type, smul_ite, ite_and, Finset.sum_ite_eq, coefZ,
    Complex.real_smul, Complex.re_add_im]

lemma sum_dirZ {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) (Z W : G.Mat s) :
    ∑ i : Fin s × Fin s × Bool, coefZ Z W i • dirZ k ρ ξ i = lamZ k ρ ξ ((Matrix.of Z)⁻¹ * Matrix.of W) := by
  rw [← coef_sum Z W]
  change _ = lamL k ρ ξ _

  rw [map_sum]
  simp only [map_smul]
  rfl

lemma rn_mem (hRad : RadicalParam) (k j ρ : ℕ) (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  have h : Rn k j ρ x ∈ Rset k j ρ := (hRad k j ρ).2.1 ▸ Set.mem_range_self x
  exact h.1

lemma ga_mem (hMem : SliceMem) (hRad : RadicalParam) {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
    (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) {Z : G.Mat s} {γ : B.Mat k ρ} (hZ : G.detM Z ≠ 0)
    (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by
  have hdet : (ZjH σ d ξ.2 Z).det ≠ 0 := by
    rw [P.level_determinant_z]
    refine mul_ne_zero ?_ hZ
    rw [hMat, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (P.Ux5.det_permutationMatrix_ne_zero σ) (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  exact P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_inv (rn_mem hRad _ _ _ _)) ((hMem k (p + s) ρ).1 _ γ hdet hγ))
    (rn_mem hRad _ _ _ _)

variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}

lemma phi_rep (hSZ : SliceZ) (ξ : Xi k p s ρ σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) (γ : B.Mat k ρ) (Z' : G.Mat s) :
    gaXi k ρ σ d ξ Z' γ = gaXi k ρ σ d ξ Z γ * ((Rn k (p + s) ρ ξ.1.2)⁻¹ *
      muP k (p + s) ρ ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
        blk2 1 0 0 ((Matrix.of Z)⁻¹ * Matrix.of Z') * blk2 1 (Matrix.of ξ.2.1.2) 0 1) *
      Rn k (p + s) ρ ξ.1.2) := by
  have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ
  have := hSZ k p s ρ σ d ξ Z ((Matrix.of Z)⁻¹ * Matrix.of Z') γ
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZu, Matrix.one_mul] at this
  exact this

lemma U_inv_mul {p s : ℕ} (b : Fin p → Fin s → ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of b) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
      blk2 1 (Matrix.of b) 0 1 = 1 := by
  apply Matrix.nonsing_inv_mul
  rw [P.Ux4.block2_det_upper_triangular]
  simp

lemma line_rep (hSZ : SliceZ) (ξ : Xi k p s ρ σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) (γ : B.Mat k ρ) (W : G.Mat s)
    (t : ℝ) :
    gaXi k ρ σ d ξ (Z + t • W) γ = gaXi k ρ σ d ξ Z γ * ((Rn k (p + s) ρ ξ.1.2)⁻¹ *
      muP k (p + s) ρ (1 + t • ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
        blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 ((Matrix.of Z)⁻¹ * Matrix.of W) * blk2 1 (Matrix.of ξ.2.1.2) 0 1)) *
      Rn k (p + s) ρ ξ.1.2) := by
  rw [phi_rep hSZ ξ hZ γ (Z + t • W)]
  have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ
  have e1 : (Matrix.of Z)⁻¹ * Matrix.of (Z + t • W) = 1 + t • ((Matrix.of Z)⁻¹ * Matrix.of W) := by
    have : Matrix.of (Z + t • W) = Matrix.of Z + t • Matrix.of W := rfl
    rw [this, Matrix.mul_add, Matrix.nonsing_inv_mul _ hZu, Matrix.mul_smul]
  rw [e1, block_matrix_two_line, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, U_inv_mul, Matrix.mul_smul, Matrix.smul_mul]

end PI.UnitaryGroupMassFormula.UsCost.DB
end
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

theorem list_prod_le_pow (l : List ℝ) (lam : ℝ) (h : ∀ x ∈ l, 0 ≤ x ∧ x ≤ lam) :
    l.prod ≤ lam ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hp : 0 ≤ l.prod := List.prod_nonneg (fun y hy => (h y (List.mem_cons_of_mem x hy)).1)
    rw [List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul hx.2 ih' hp (hx.1.trans hx.2)

theorem max_one_le (c t : ℝ) (ht : 1 ≤ t) (x : ℝ) (hx : x ≤ c * t) : max 1 x ≤ (1 + |c|) * t := by
  have ht0 : 0 ≤ t := by linarith
  have h1 : c * t ≤ |c| * t := mul_le_mul_of_nonneg_right (le_abs_self c) ht0
  have h2 : 0 ≤ |c| * t := mul_nonneg (abs_nonneg c) ht0
  refine max_le ?_ ?_ <;> nlinarith

theorem zeta_cost_of_smooth_deriv (hS : ZSmooth) (hD : ZDeriv) (hDS : DirSize) : ZCost := by
  intro hSM hRP hSZ hDP hS21 k p s ρ σ d hd hs K hK hK0 q
  obtain ⟨C₁, hC₁⟩ := hDS hDP k p s ρ σ
  obtain ⟨C₂, hC₂⟩ := hS21 k p s ρ σ d hd hs K hK hK0
  obtain ⟨Kc, hKc0, hKc⟩ := ZI.cF_bound s q
  obtain ⟨C, hC1, hC⟩ := ZI.iter_words (V := G.Mat s) (I := Fin s × Fin s × Bool) q Kc hKc0
  have hE'0 : (0 : ℝ) ≤ max 1 ‖ZI.eA s‖ := zero_le_one.trans (le_max_left _ _)
  set A : ℝ := (1 + |(|C₁| * C₂ ^ 4)|) * (max 1 ‖ZI.eA s‖ * (1 + |‖ZI.eA s‖ * C₂|)) with hA
  have hA0 : 0 ≤ A := mul_nonneg (by positivity) (mul_nonneg hE'0 (by positivity))
  refine ⟨C * A ^ q, ?_⟩
  intro E _ _ H β hH ξ Z γ hZ hγ hKg hw
  have hZ' : (Matrix.of Z).det ≠ 0 := hZ
  refine ⟨(hS hSM hRP k p s ρ σ d hd E H q hH ξ Z γ hZ hγ).2.2, ?_⟩
  obtain ⟨hg1, -, hRn, -, -, -, hb, -, -, -, -, hinv⟩ := hC₂ ξ Z γ hγ hKg
  set g := gaXi k ρ σ d ξ Z γ with hg
  set lam := max 1 (C₁ * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) with hlam
  set M := max 1 ‖ZI.eA s‖ * max 1 ‖Ring.inverse (ZI.eA s Z)‖ with hM
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  have hβ : 0 ≤ β := by
    have := hw [] (by simp) (by simp)
    simp only [List.map_nil, List.prod_nil, mul_one] at this
    exact (norm_nonneg _).trans this
  have hlet : ∀ i, inLieP k (p + s) ρ (dirZ k ρ ξ i) ∧ lsz (dirZ k ρ ξ i) ≤ lam := fun i =>
    ⟨(hC₁ ξ i).1, (hC₁ ξ i).2.trans (le_max_right _ _)⟩
  have key := hC (α := B.Mat k (p + s + ρ)) (E := E)
    (fun b H' => B.CkOn (b : ℕ∞) (B.GV k (p + s + ρ)) H')
    (fun i H' => RdV (dirZ k ρ ξ i) H') (fun Z' => gaXi k ρ σ d ξ Z' γ)
    {Z' : G.Mat s | (Matrix.of Z').det ≠ 0} (fun i => ZI.cF s i) Z M lam
    (ZI.isOpen_det s) hZ' hM1 hlam1
    (fun b H' h => P.BetaSesquilinearity.CkOn_mono (by exact_mod_cast Nat.le_succ b) h)
    (fun b H' i h => by
      have h' : B.CkOn ((b : ℕ∞) + 1) (B.GV k (p + s + ρ)) H' := by simpa using h
      have := P.BetaSesquilinearity.CkOn_Dx (x := (false, dirZ k ρ ξ i)) (hlet i).1.1 h'
      simpa [P.BetaSesquilinearity.Dx] using this)
    (fun b H' h z hz => (hS hSM hRP k p s ρ σ d hd E H' b h ξ z γ hz hγ).2.2)
    (fun b H' h z hz => by
      ext1 W
      rw [hD hSM hRP hSZ k p s ρ σ d hd E H'
        (P.BetaSesquilinearity.CkOn_mono (by exact_mod_cast Nat.le_add_left 1 b) h) ξ z γ hz hγ W]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ZI.cF_apply s i hz]
      rfl)
    (fun i n => ZI.contDiffOn_cF s i n)
    (fun i a ha => hKc Z hZ' i a ha)
    q le_rfl H β hH (fun w hwl => by
      have e : w.foldr (fun i H' => RdV (dirZ k ρ ξ i) H') H = B.Rw (w.map (dirZ k ρ ξ)) H := by
        simp [B.Rw, List.foldr_map]
      rw [e]
      refine (hw (w.map (dirZ k ρ ξ)) (fun X hX => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX
          exact (hlet i).1) (by rw [List.length_map]; exact hwl)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hβ
      have := list_prod_le_pow ((w.map (dirZ k ρ ξ)).map lsz) lam (by
        intro x hx
        obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX
        exact ⟨zero_le_one.trans (le_max_left _ _), (hlet i).2⟩)
      simpa using this)

  have hg0 : 0 ≤ B.gN g := by linarith
  have hR0 : 0 ≤ B.gN (Rn k (p + s) ρ ξ.1.2) := Real.sqrt_nonneg _
  have hlamb : lam ≤ (1 + |(|C₁| * C₂ ^ 4)|) * B.gN g ^ (2 * (p + s) + 2 * p) := by
    refine max_one_le _ _ (one_le_pow₀ hg1) _ ?_
    have h1 : B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 ≤ (C₂ * B.gN g ^ (p + s)) ^ 2 := pow_le_pow_left₀ hR0 hRn 2
    have h2 : (1 + ‖ξ.2.1.2‖) ^ 2 ≤ (C₂ * B.gN g ^ p) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
    have hpow : B.gN g ^ (2 * (p + s) + 2 * p) = (B.gN g ^ (p + s)) ^ 2 * (B.gN g ^ p) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    calc C₁ * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2
        = C₁ * (B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) := by ring
      _ ≤ |C₁| * (B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C₁| * ((C₂ * B.gN g ^ (p + s)) ^ 2 * (C₂ * B.gN g ^ p) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) (abs_nonneg _)
      _ = (|C₁| * C₂ ^ 4) * B.gN g ^ (2 * (p + s) + 2 * p) := by rw [hpow]; ring
  have hMb : M ≤ max 1 ‖ZI.eA s‖ * ((1 + |‖ZI.eA s‖ * C₂|) * B.gN g ^ (p + s - 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ hE'0
    refine max_one_le _ _ (one_le_pow₀ hg1) _ ?_
    calc ‖Ring.inverse (ZI.eA s Z)‖ ≤ ‖ZI.eA s‖ * ‖ZI.invF s Z‖ := ZI.norm_inverse_le s hZ'
      _ ≤ ‖ZI.eA s‖ * (C₂ * B.gN g ^ (p + s - 1)) := mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = ‖ZI.eA s‖ * C₂ * B.gN g ^ (p + s - 1) := by ring
  have hLM : lam * M ≤ A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1)) := by
    calc lam * M ≤ ((1 + |(|C₁| * C₂ ^ 4)|) * B.gN g ^ (2 * (p + s) + 2 * p)) *
          (max 1 ‖ZI.eA s‖ * ((1 + |‖ZI.eA s‖ * C₂|) * B.gN g ^ (p + s - 1))) :=
          mul_le_mul hlamb hMb (by linarith) (by positivity)
      _ = A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1)) := by rw [hA, pow_add]; ring
  have hexp : (2 * (p + s) + 2 * p + (p + s - 1)) * q ≤ 5 * (p + s + ρ) * q :=
    Nat.mul_le_mul_right q (by omega)
  have hrp : B.gN g ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) = B.gN g ^ (5 * (p + s + ρ) * q) := by
    rw [← Real.rpow_natCast]; congr 1; push_cast; ring
  rw [hrp]
  calc ‖iteratedFDeriv ℝ q (fun Z' => H (gaXi k ρ σ d ξ Z' γ)) Z‖ ≤ C * β * (lam * M) ^ q := key
    _ ≤ C * β * (A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1))) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hLM q) (by positivity)
    _ = C * β * (A ^ q * B.gN g ^ ((2 * (p + s) + 2 * p + (p + s - 1)) * q)) := by rw [mul_pow, pow_mul]
    _ ≤ C * β * (A ^ q * B.gN g ^ (5 * (p + s + ρ) * q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg1 hexp) (by positivity))
          (by positivity)
    _ = C * A ^ q * β * B.gN g ^ (5 * (p + s + ρ) * q) := by ring

end PI.UnitaryGroupMassFormula.UsCost
end
end
