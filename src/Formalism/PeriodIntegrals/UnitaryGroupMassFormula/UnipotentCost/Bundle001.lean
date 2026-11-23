module

public import Formalism.HermitianCurvature.StatementU
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.DA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cd

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x : X}

lemma cm_iff {a b : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} :
    ContDiffAt ℝ n F x ↔ ∀ i j, ContDiffAt ℝ n (fun y => F y i j) x :=
  (contDiffAt_pi (Φ := F)).trans (forall_congr' fun _ => contDiffAt_pi)

lemma cm_mul {a b c : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} {G : X → Matrix (Fin b) (Fin c) ℂ}
    (hF : ContDiffAt ℝ n F x) (hG : ContDiffAt ℝ n G x) : ContDiffAt ℝ n (fun y => F y * G y) x := by
  rw [cm_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hF i l).mul (hG l j)

lemma c_det {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) :
    ContDiffAt ℝ n (fun y => (F y).det) x := by
  rw [cm_iff] at hF
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hF _ _)

lemma cm_updateRow {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) (j : Fin a)
    (b : Fin a → ℂ) : ContDiffAt ℝ n (fun y => (F y).updateRow j b) x := by
  rw [cm_iff] at hF ⊢
  intro i l
  by_cases hi : i = j
  · subst hi; simp only [updateRow_self]; exact contDiffAt_const
  · simp only [updateRow_ne hi]; exact hF i l

lemma cm_inv {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) (hu : (F x).det ≠ 0) :
    ContDiffAt ℝ n (fun y => (F y)⁻¹) x := by
  rw [cm_iff]
  intro i j
  have e : (fun y => (F y)⁻¹ i j)
      = fun y => ((F y).det)⁻¹ * ((F y).updateRow j (Pi.single i 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  exact ((c_det hF).inv hu).mul (c_det (cm_updateRow hF j _))

lemma cm_conjT {a b : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} (hF : ContDiffAt ℝ n F x) :
    ContDiffAt ℝ n (fun y => (F y)ᴴ) x := by
  rw [cm_iff] at hF ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp x (hF j i)

lemma contDiffAt_block_matrix_two {p s : ℕ} {A : X → Matrix (Fin p) (Fin p) ℂ} {B' : X → Matrix (Fin p) (Fin s) ℂ}
    {C : X → Matrix (Fin s) (Fin p) ℂ} {D : X → Matrix (Fin s) (Fin s) ℂ}
    (hA : ContDiffAt ℝ n A x) (hB : ContDiffAt ℝ n B' x) (hC : ContDiffAt ℝ n C x) (hD : ContDiffAt ℝ n D x) :
    ContDiffAt ℝ n (fun y => blk2 (A y) (B' y) (C y) (D y)) x := by
  rw [cm_iff] at hA hB hC hD ⊢
  intro i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂] <;>
    first | exact hA _ _ | exact hB _ _ | exact hC _ _ | exact hD _ _

lemma contDiffAt_block_matrix_three {k j ρ : ℕ} {A11 : X → Matrix (Fin j) (Fin j) ℂ} {A12 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : X → Matrix (Fin j) (Fin j) ℂ} {A21 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : X → B.Mat k ρ}
    {A23 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : X → Matrix (Fin j) (Fin j) ℂ}
    {A32 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : X → Matrix (Fin j) (Fin j) ℂ}
    (h11 : ContDiffAt ℝ n A11 x) (h12 : ContDiffAt ℝ n A12 x) (h13 : ContDiffAt ℝ n A13 x)
    (h21 : ContDiffAt ℝ n A21 x) (h22 : ContDiffAt ℝ n A22 x) (h23 : ContDiffAt ℝ n A23 x)
    (h31 : ContDiffAt ℝ n A31 x) (h32 : ContDiffAt ℝ n A32 x) (h33 : ContDiffAt ℝ n A33 x) :
    ContDiffAt ℝ n (fun y => blk3 (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y) (A33 y)) x := by
  rw [cm_iff] at h11 h12 h13 h21 h22 h23 h31 h32 h33 ⊢
  intro i i'
  obtain ⟨a, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨b, rfl⟩ := (eB k j ρ).surjective i'
  simp only [P.Ux4.block3_apply]
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr] <;>
    first | exact h11 _ _ | exact h12 _ _ | exact h13 _ _ | exact h21 _ _ | exact h22 _ _ | exact h23 _ _ | exact h31 _ _ | exact h32 _ _ | exact h33 _ _

end cd

section hd

variable {t : ℝ}

lemma hd_iff {a b : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {F' : Matrix (Fin a) (Fin b) ℂ} :
    HasDerivAt F F' t ↔ ∀ i j, HasDerivAt (fun y => F y i j) (F' i j) t :=
  (hasDerivAt_pi (φ := F)).trans (forall_congr' fun _ => hasDerivAt_pi)

lemma hd_mul {a b c : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {G : ℝ → Matrix (Fin b) (Fin c) ℂ}
    {F' : Matrix (Fin a) (Fin b) ℂ} {G' : Matrix (Fin b) (Fin c) ℂ}
    (hF : HasDerivAt F F' t) (hG : HasDerivAt G G' t) :
    HasDerivAt (fun y => F y * G y) (F' * G t + F t * G') t := by
  rw [hd_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun l _ => (hF i l).mul (hG l j)

lemma hasDerivAt_block_matrix_three {k j ρ : ℕ} {A11 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A12 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A21 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : ℝ → B.Mat k ρ}
    {A23 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {A32 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {ToralGalois : Matrix (Fin j) (Fin j) ℂ} {cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {B13 : Matrix (Fin j) (Fin j) ℂ} {B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B22 : B.Mat k ρ}
    {B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B31 : Matrix (Fin j) (Fin j) ℂ}
    {B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {B33 : Matrix (Fin j) (Fin j) ℂ}
    (h11 : HasDerivAt A11 ToralGalois t) (h12 : HasDerivAt A12 cocyclesToWachVectorsExponent t) (h13 : HasDerivAt A13 B13 t)
    (h21 : HasDerivAt A21 B21 t) (h22 : HasDerivAt A22 B22 t) (h23 : HasDerivAt A23 B23 t)
    (h31 : HasDerivAt A31 B31 t) (h32 : HasDerivAt A32 B32 t) (h33 : HasDerivAt A33 B33 t) :
    HasDerivAt (fun y => blk3 (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y) (A33 y))
      (blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33) t := by
  rw [hd_iff] at h11 h12 h13 h21 h22 h23 h31 h32 h33 ⊢
  intro i i'
  obtain ⟨a, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨b, rfl⟩ := (eB k j ρ).surjective i'
  simp only [P.Ux4.block3_apply]
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr] <;>
    first | exact h11 _ _ | exact h12 _ _ | exact h13 _ _ | exact h21 _ _ | exact h22 _ _ | exact h23 _ _ | exact h31 _ _ | exact h32 _ _ | exact h33 _ _

lemma hd_invT {a : ℕ} (B : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) (-Bᴴ) 0 := by
  have hL : HasDerivAt (fun t : ℝ => (1 + t • B)ᴴ) Bᴴ 0 := by
    have e : (fun t : ℝ => (1 + t • B)ᴴ) = fun t => 1 + t • Bᴴ := by
      funext t; simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
    rw [e]
    exact (((hasDerivAt_id' (0 : ℝ)).smul_const Bᴴ).const_add (1 : Matrix (Fin a) (Fin a) ℂ)).congr_deriv (one_smul _ _)
  have hC : ContDiffAt ℝ 1 (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) 0 :=
    cm_inv (cm_conjT (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))) (by simp)
  have hCd := (hC.differentiableAt one_ne_zero).hasDerivAt
  have hP := hd_mul hCd hL
  have hcont : ContinuousAt (fun t : ℝ => ((1 + t • B)ᴴ).det) 0 :=
    (c_det (n := 0) (cm_conjT (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)))).continuousAt
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), ((1 + t • B)ᴴ).det ≠ 0 := hcont.eventually_ne (by simp)
  have hev : (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹ * (1 + t • B)ᴴ) =ᶠ[𝓝 0] fun _ => 1 := by
    filter_upwards [hne] with t ht
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)
  have h0 : HasDerivAt (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹ * (1 + t • B)ᴴ) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin a) (Fin a) ℂ)).congr_of_eventuallyEq hev
  have hu := h0.unique hP
  simp only [zero_smul, add_zero, Matrix.conjTranspose_one, inv_one, Matrix.mul_one, Matrix.one_mul] at hu
  have : deriv (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) 0 = -Bᴴ := eq_neg_of_add_eq_zero_left hu.symm
  exact hCd.congr_deriv this

end hd

end PI.UnitaryGroupMassFormula.UsCost.DA
end
end

section

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Ux5

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

lemma inv_eq_hpk {k r : ℕ} (n : B.Mat k r) (hu : nᴴ * Hpk k r * n = Hpk k r) :
    n⁻¹ = Hpk k r * nᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc nᴴ, hu, Formalism.QuantumDeterminants.GBasic.Hpk_sq]

lemma EB_inv_hpk {k r : ℕ} (n : B.Mat k r) (hu : nᴴ * Hpk k r * n = Hpk k r) :
    EB n⁻¹ (((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * B.gN n) := by
  rw [inv_eq_hpk n hu]
  have h1 : EB nᴴ (B.gN n) := EB_conjTranspose fun i j => entry_le_gN n i j
  have h2 := EB_mulF (EB_mulF (EB_Hpk k r) h1) (EB_Hpk k r)
  refine h2.mono (le_of_eq ?_)
  ring

lemma one_le_gN_sq {k r : ℕ} (n : B.Mat k r) (hu : nᴴ * Hpk k r * n = Hpk k r) :
    1 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 * B.gN n ^ 2 := by
  have hinv : n⁻¹ * n = 1 := by
    rw [inv_eq_hpk n hu, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc nᴴ, hu, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have h := EB_mulF (EB_inv_hpk n hu) (fun i j => entry_le_gN n i j)
  have i0 : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  have := h i0 i0
  rw [hinv, Matrix.one_apply_eq, norm_one] at this
  refine this.trans (le_of_eq ?_)
  ring

lemma lsz_conj_le {k r : ℕ} (n M : B.Mat k r) (hu : nᴴ * Hpk k r * n = Hpk k r) {c : ℝ} (hM : EB M c)
    (hc : 0 ≤ c) :
    lsz (n⁻¹ * M * n) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 4 * (1 + c) * B.gN n ^ 2 := by
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)
  have hN : 1 ≤ N := Nat.one_le_cast.mpr (by omega)
  have hg : 0 ≤ B.gN n := Real.sqrt_nonneg _
  have h := EB_mulF (EB_mulF (EB_inv_hpk n hu) hM) (fun i j => entry_le_gN n i j)
  have hmx : mx (n⁻¹ * M * n) ≤ N ^ 4 * c * B.gN n ^ 2 := by
    refine mx_le (h.mono (le_of_eq (by simp only [N]; ring))) (by positivity)
  have h1 : 1 ≤ N ^ 3 * B.gN n ^ 2 := one_le_gN_sq n hu
  have h3 : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
  have h4 : 0 ≤ B.gN n ^ 2 := sq_nonneg _
  have h5 : N ^ 3 * B.gN n ^ 2 ≤ N ^ 4 * B.gN n ^ 2 := mul_le_mul_of_nonneg_right h3 h4
  have h6 : 0 ≤ N ^ 4 * B.gN n ^ 2 * c := by positivity
  unfold lsz
  refine max_le ?_ ?_
  · nlinarith
  · nlinarith

lemma EB_hat {k j ρ : ℕ} (Y : B.Mat k ρ) {c : ℝ} (hY : EB Y c) (hc : 0 ≤ c) :
    EB (blk3 (0 : Matrix (Fin j) (Fin j) ℂ) 0 0 0 Y 0 0 0 0 : B.Mat k (j + ρ)) c := by
  unfold EB blk3 at *
  intro a b
  show ‖fromBlocks (fromBlocks 0 0 0 Y) (fromRows 0 0) (fromCols 0 0) 0
    ((eB k j ρ).symm a) ((eB k j ρ).symm b)‖ ≤ c
  rcases (eB k j ρ).symm a with (a' | a') | a' <;> rcases (eB k j ρ).symm b with (b' | b') | b' <;>
    simp [hc, hY]

theorem letterSize : LetterSize := by
  intro k j ρ
  refine ⟨((2 * (j + ρ) + k + 1 : ℕ) : ℝ) ^ 4 * (1 + 1), fun x Y hY => ?_⟩
  have hb : EB (blk3 (0 : Matrix (Fin j) (Fin j) ℂ) 0 0 0 Y 0 0 0 0 : B.Mat k (j + ρ)) 1 := EB_hat Y hY zero_le_one
  exact lsz_conj_le (Rn k j ρ x) _ (Formalism.FourierDecayAlt.P.Ux4.Rn_unitary x) hb zero_le_one

lemma entry_bound_block_matrix_two {p s : ℕ} {A : Matrix (Fin p) (Fin p) ℂ} {B' : Matrix (Fin p) (Fin s) ℂ}
    {C' : Matrix (Fin s) (Fin p) ℂ} {D : Matrix (Fin s) (Fin s) ℂ} {c : ℝ}
    (hA : EB A c) (hB : EB B' c) (hC : EB C' c) (hD : EB D c) : EB (blk2 A B' C' D) c := by
  intro i j
  show ‖fromBlocks A B' C' D (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)‖ ≤ c
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b
  · exact hA a b
  · exact hB a b
  · exact hC a b
  · exact hD a b

lemma block_matrix_two_unipotent_inv {p s : ℕ} (b : Matrix (Fin p) (Fin s) ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) b 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ = blk2 1 (-b) 0 1 := by
  apply Matrix.inv_eq_left_inv
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

lemma EB_eMat {s : ℕ} (a b : Fin s) (ε : Bool) : EB (eMat a b ε) 1 := by
  unfold EB eMat
  intro i j
  simp only [Matrix.of_apply]
  split_ifs <;> simp

lemma EB_of_pi {p s : ℕ} (b : Fin p → Fin s → ℂ) : EB (Matrix.of b) (1 + ‖b‖) := by
  intro i j
  simp only [Matrix.of_apply]
  exact ((norm_le_pi_norm (b i) j).trans (norm_le_pi_norm b i)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem dirSize : DirSize := by
  intro hD k p s ρ σ
  refine ⟨((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) ^ 4 *
    (1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * ((p + s : ℕ) : ℝ) ^ 2), fun ξ i => ⟨?_, ?_⟩⟩
  · unfold dirZ dmuP
    exact (hD k (p + s) ρ ξ.1.2).2 _
  · have ht : 1 ≤ 1 + ‖ξ.2.1.2‖ := by linarith [norm_nonneg ξ.2.1.2]
    have h0 : (0 : ℝ) ≤ 1 + ‖ξ.2.1.2‖ := by linarith
    have hb := EB_of_pi ξ.2.1.2
    have hU : EB (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))
        (1 + ‖ξ.2.1.2‖) :=
      entry_bound_block_matrix_two (EB_one.mono ht) hb (EB_zero.mono h0) (EB_one.mono ht)
    have hUi : EB (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹
        (1 + ‖ξ.2.1.2‖) := by
      rw [block_matrix_two_unipotent_inv]
      exact entry_bound_block_matrix_two (EB_one.mono ht) (EB_neg hb) (EB_zero.mono h0) (EB_one.mono ht)
    have hE : EB (blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (eMat i.1 i.2.1 i.2.2)) 1 :=
      entry_bound_block_matrix_two (EB_zero.mono zero_le_one) (EB_zero.mono zero_le_one) (EB_zero.mono zero_le_one)
        (EB_eMat _ _ _)
    have hQ := EB_mulF (EB_mulF hUi hE) hU
    have hW := EB_mulF (EB_mulF (EB_wMat (p + s)) (EB_conjTranspose hQ)) (EB_wMat (p + s))
    have hJ : (0 : ℝ) ≤ ((p + s : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcQ : (0 : ℝ) ≤ ((p + s : ℕ) : ℝ) * (((p + s : ℕ) : ℝ) * ((1 + ‖ξ.2.1.2‖) * 1) * (1 + ‖ξ.2.1.2‖)) := by
      positivity
    have hc1 : ((p + s : ℕ) : ℝ) * (((p + s : ℕ) : ℝ) * ((1 + ‖ξ.2.1.2‖) * 1) * (1 + ‖ξ.2.1.2‖)) ≤
        (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) := by
      have : (0 : ℝ) ≤ ((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2 := by positivity
      nlinarith
    have hc2 : ((p + s : ℕ) : ℝ) * (((p + s : ℕ) : ℝ) * (1 * (((p + s : ℕ) : ℝ) * (((p + s : ℕ) : ℝ) * ((1 + ‖ξ.2.1.2‖) * 1) * (1 + ‖ξ.2.1.2‖)))) * 1) ≤
        (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) := by
      have : (0 : ℝ) ≤ ((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2 := by positivity
      nlinarith
    have hc : (0 : ℝ) ≤ (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) := by
      positivity
    have hM := entry_bound_block3 (k := k) (ρ := ρ) (hQ.mono hc1) (EB_zero.mono hc) (EB_zero.mono hc) (EB_zero.mono hc)
      (EB_zero.mono hc) (EB_zero.mono hc) (EB_zero.mono hc) (EB_zero.mono hc) (EB_neg (hW.mono hc2))
    have key := lsz_conj_le (Rn k (p + s) ρ ξ.1.2) _ (Formalism.FourierDecayAlt.P.Ux4.Rn_unitary ξ.1.2) hM hc
    unfold dirZ dmuP
    refine key.trans ?_
    have hg : (0 : ℝ) ≤ ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) ^ 4 * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 := by
      positivity
    have ht2 : 1 ≤ (1 + ‖ξ.2.1.2‖) ^ 2 := one_le_pow₀ ht
    have hJ2 : (0 : ℝ) ≤ (((p + s : ℕ) : ℝ) ^ 2 + 1) * ((p + s : ℕ) : ℝ) ^ 2 := by positivity
    have hin : 1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) ≤
        (1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * ((p + s : ℕ) : ℝ) ^ 2) * (1 + ‖ξ.2.1.2‖) ^ 2 := by
      nlinarith
    calc ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) ^ 4 *
          (1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2)) *
          B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2
        = ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) ^ 4 * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 *
          (1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2)) := by ring
      _ ≤ ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) ^ 4 * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 *
          ((1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * ((p + s : ℕ) : ℝ) ^ 2) * (1 + ‖ξ.2.1.2‖) ^ 2) :=
          mul_le_mul_of_nonneg_left hin hg
      _ = _ := by ring

end PI.UnitaryGroupMassFormula.UsCost
end
end
