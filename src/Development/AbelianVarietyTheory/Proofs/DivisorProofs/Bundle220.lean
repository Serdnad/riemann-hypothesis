module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle098
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle075
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle100
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_skew_lift_mod_maximalIdeal : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  first | exact @GlobalTheory.lift_mod_maximal_skew | exact GlobalTheory.lift_mod_maximal_skew | (intros; apply GlobalTheory.lift_mod_maximal_skew <;> assumption)
end

section

open scoped Classical

theorem _root_.GlobalTheory.T.esymm_mul_det_pow_eq_sum_det_shifted : ∀ (n : ℕ) (m : Fin n → ℕ) (j : ℕ), MvPolynomial.esymm (Fin n) ℤ j * Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m k) = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (m k + if k ∈ J then 1 else 0)) := by
  first | exact @GlobalTheory.JSW.esymm_mul_alternant | exact GlobalTheory.JSW.esymm_mul_alternant | (intros; apply GlobalTheory.JSW.esymm_mul_alternant <;> assumption)
end

section

open Matrix Polynomial

namespace GlobalTheory

theorem unitary_conj_ker_basis_gram {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K)
    (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1)
    (Q : K[X]) {ι : Type} (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hspan : Submodule.span K (Set.range u) =
      LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))) :
    LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧
    Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
      LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧
    (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) *
        ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) = Matrix.of fun i j => ∑ k, σ (u i k) * u j k := by
  first
  | exact @_root_.GlobalTheory.ConjugateAlgebraLemmas.main
  | exact _root_.GlobalTheory.ConjugateAlgebraLemmas.main
  | (apply _root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateAlgebraLemmas.main ..)

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_det_one_mul_stdBlock' : ∀ {K : Type} [Field K] {n r : ℕ}, r < n → ∀ y : Matrix (Fin n) (Fin r) K, y.rank = r → ∃ g : GL (Fin n) K, Matrix.GeneralLinearGroup.det g = 1 ∧ g.val * (Matrix.of fun (a : Fin n) (b : Fin r) => if (a : ℕ) = (b : ℕ) then (1 : K) else 0) = y := by
  first | exact @GlobalTheory.exists_det_one_mul_stdBlock | exact GlobalTheory.exists_det_one_mul_stdBlock | (intros; apply GlobalTheory.exists_det_one_mul_stdBlock <;> assumption)
end

section

open Matrix Kronecker

namespace GlobalTheory

section
variable {n q : Type} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q]

theorem zarhinBlock_real_posDef_det (B A : Matrix n n ℝ) (x : Matrix q q ℝ) (s : ℝ)
    (hB : B.PosDef) (hA : A = (1 + s) • B⁻¹) (hx : xᵀ * x = s • (1 : Matrix q q ℝ)) :
    (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) ((1 : Matrix n n ℝ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℝ))).PosDef ∧
      (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) ((1 : Matrix n n ℝ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℝ))).det = 1 := by
  have hdet : IsUnit B.det := hB.det_pos.ne'.isUnit
  have hK : (B ⊗ₖ (1 : Matrix q q ℝ)).PosDef := hB.kronecker PosDef.one
  have hKi : (B⁻¹ ⊗ₖ (1 : Matrix q q ℝ)).PosDef := hB.inv.kronecker PosDef.one
  letI := hK.isUnit.invertible
  have hinv : (B ⊗ₖ (1 : Matrix q q ℝ))⁻¹ = B⁻¹ ⊗ₖ (1 : Matrix q q ℝ) := by
    apply Matrix.inv_eq_left_inv
    rw [← mul_kronecker_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, one_kronecker_one]
  have hS : A ⊗ₖ (1 : Matrix q q ℝ) - ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) * (B ⊗ₖ (1 : Matrix q q ℝ))⁻¹ *
      ((1 : Matrix n n ℝ) ⊗ₖ x) = B⁻¹ ⊗ₖ (1 : Matrix q q ℝ) := by
    rw [hinv, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_one, hx, hA, kronecker_smul, smul_kronecker, add_smul, one_smul,
      add_sub_cancel_right]
  have hT : ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)ᴴ = (1 : Matrix n n ℝ) ⊗ₖ x := by
    rw [conjTranspose_eq_transpose_of_trivial, ← kroneckerMap_transpose, transpose_one,
      transpose_transpose]
  have hd : (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)
      ((1 : Matrix n n ℝ) ⊗ₖ x) (B ⊗ₖ (1 : Matrix q q ℝ))).det = 1 := by
    rw [det_fromBlocks₂₂, invOf_eq_nonsing_inv, hS, ← det_mul, ← mul_kronecker_mul,
      Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, one_kronecker_one, det_one]
  refine ⟨?_, hd⟩
  have hps : (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)
      ((1 : Matrix n n ℝ) ⊗ₖ x) (B ⊗ₖ (1 : Matrix q q ℝ))).PosSemidef := by
    have := (PosDef.fromBlocks₂₂ (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) hK).mpr
      (by rw [hT, hS]; exact hKi.posSemidef)
    rwa [hT] at this
  exact hps.posDef_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (by rw [hd]; exact isUnit_one))

def zarhinAction {R : Type} [CommRing R] (σ : R →+* R) (ρ0 : R →+* Matrix n n ℤ) :
    R →+* Matrix ((n × q) ⊕ (n × q)) ((n × q) ⊕ (n × q)) ℤ where
  toFun a := fromBlocks ((ρ0 (σ a))ᵀ ⊗ₖ (1 : Matrix q q ℤ)) 0 0 (ρ0 a ⊗ₖ (1 : Matrix q q ℤ))
  map_one' := by simp
  map_mul' a b := by
    rw [fromBlocks_multiply, mul_comm a b, map_mul σ, map_mul ρ0, transpose_mul, mul_comm b a,
      map_mul ρ0]
    simp [← mul_kronecker_mul]
  map_zero' := by simp
  map_add' a b := by
    simp [fromBlocks_add, add_kronecker, transpose_add]

theorem zarhinAction_adjoint {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a)
    (ρ0 : R →+* Matrix n n ℤ) (B A : Matrix n n ℤ) (x : Matrix q q ℤ)
    (hB : ∀ a, (ρ0 a)ᵀ * B = B * ρ0 (σ a)) (hA : ∀ a, ρ0 (σ a) * A = A * (ρ0 a)ᵀ) (a : R) :
    (zarhinAction (q := q) σ ρ0 a)ᵀ *
      fromBlocks (A ⊗ₖ (1 : Matrix q q ℤ)) ((1 : Matrix n n ℤ) ⊗ₖ xᵀ) ((1 : Matrix n n ℤ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℤ)) =
      fromBlocks (A ⊗ₖ (1 : Matrix q q ℤ)) ((1 : Matrix n n ℤ) ⊗ₖ xᵀ) ((1 : Matrix n n ℤ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℤ)) * zarhinAction (q := q) σ ρ0 (σ a) := by
  simp only [zarhinAction, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, fromBlocks_transpose,
    fromBlocks_multiply, ← kroneckerMap_transpose, transpose_transpose, transpose_one,
    transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hσ]
  simp only [← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hA, hB]

theorem mul_adjugate_eq_adjugate_mul_of_adjoint (B P Q : Matrix n n ℤ) (hd : B.det ≠ 0)
    (h : P * B = B * Q) : Q * B.adjugate = B.adjugate * P := by
  have h1 : B.adjugate * (P * B) * B.adjugate = B.adjugate * (B * Q) * B.adjugate := by rw [h]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ B, mul_adjugate, adjugate_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at h1
  exact (smul_right_injective _ hd h1).symm

end

theorem exists_unimodular_posDef_adjoint_action (R : Type) [CommRing R] (σ : R →+* R)
    (hσ : ∀ a, σ (σ a) = a) (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ)
    (ρ0 : R →+* Matrix (Fin m) (Fin m) ℤ) (hm : 1 ≤ m) (hs : B0.transpose = B0)
    (hp : (B0.map (Int.cast : ℤ → ℝ)).PosDef)
    (hadj : ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (σ a)) :
    ∃ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℤ) (ρ : R →+* Matrix (Fin r) (Fin r) ℤ),
      1 ≤ r ∧ b.transpose = b ∧ (b.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit b.det ∧
        ∀ a, (ρ a).transpose * b = b * ρ (σ a) := by
  have hcast : ∀ {k : Type} [Fintype k] [DecidableEq k] (M : Matrix k k ℤ),
      (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := fun M => by
    simpa using ((Int.castRingHom ℝ).map_det M).symm
  have hDR : (0 : ℝ) < (B0.det : ℝ) := hcast B0 ▸ hp.det_pos
  have hD : 0 < B0.det := by exact_mod_cast hDR
  obtain ⟨s, hsD⟩ : ∃ s : ℕ, B0.det = 1 + s := ⟨(B0.det - 1).toNat, by omega⟩
  obtain ⟨x, hx, -⟩ := exists_int_matrix_transpose_mul_eq_smul_one s
  set b := fromBlocks (B0.adjugate ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℤ))
    ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ xᵀ) ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ x)
    (B0 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℤ)) with hb
  have hsym : bᵀ = b := by
    simp only [hb, fromBlocks_transpose, ← kroneckerMap_transpose, transpose_transpose,
      transpose_one, adjugate_transpose, hs]
  have hk : ∀ (M : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin 4) (Fin 4) ℤ),
      (M ⊗ₖ N).map (Int.cast : ℤ → ℝ) = M.map (Int.cast : ℤ → ℝ) ⊗ₖ N.map (Int.cast : ℤ → ℝ) := by
    intro M N
    ext i j
    simp [kroneckerMap_apply]
  have hxR : (x.map (Int.cast : ℤ → ℝ))ᵀ * x.map (Int.cast : ℤ → ℝ) = (s : ℝ) • 1 := by
    have := congrArg (fun M => (Int.castRingHom ℝ).mapMatrix M) hx
    simp only [map_mul, map_zsmul, map_one] at this
    rw [← Int.cast_smul_eq_zsmul ℝ] at this
    simpa [transpose_map] using this
  have hAR : (B0.adjugate).map (Int.cast : ℤ → ℝ) =
      (1 + (s : ℝ)) • (B0.map (Int.cast : ℤ → ℝ))⁻¹ := by
    have h1 : (B0.adjugate).map (Int.cast : ℤ → ℝ) = (B0.map (Int.cast : ℤ → ℝ)).adjugate := by
      simpa using (Int.castRingHom ℝ).map_adjugate B0
    have h2 : (1 + (s : ℝ)) = (B0.det : ℝ) := by rw [hsD]; push_cast; rfl
    rw [h1, h2, Matrix.inv_def, hcast, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hDR.ne',
      one_smul]
  have hreal := zarhinBlock_real_posDef_det _ _ _ _ hp hAR hxR
  have hbR : b.map (Int.cast : ℤ → ℝ) =
      fromBlocks (B0.adjugate.map (Int.cast : ℤ → ℝ) ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ))
        ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ (x.map (Int.cast : ℤ → ℝ))ᵀ)
        ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ x.map (Int.cast : ℤ → ℝ))
        (B0.map (Int.cast : ℤ → ℝ) ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by
    rw [hb, fromBlocks_map, hk, hk, hk, hk, Matrix.map_one _ Int.cast_zero Int.cast_one,
      Matrix.map_one _ Int.cast_zero Int.cast_one, transpose_map]
  rw [← hbR, hcast] at hreal
  have hdet : b.det = 1 := by exact_mod_cast hreal.2
  have hact := zarhinAction_adjoint σ hσ ρ0 B0 B0.adjugate x hadj
    (fun a => mul_adjugate_eq_adjugate_mul_of_adjoint _ _ _ hD.ne' (hadj a))
  rw [← hb] at hact
  let e := Fintype.equivFin ((Fin m × Fin 4) ⊕ (Fin m × Fin 4))
  refine ⟨_, reindex e e b, ((reindexAlgEquiv ℤ ℤ e).toRingEquiv.toRingHom).comp
    (zarhinAction σ ρ0), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; omega
  · rw [transpose_reindex, hsym]
  · exact hreal.1.submatrix e.symm.injective
  · rw [det_reindex_self, hdet]; exact isUnit_one
  · intro a
    change (reindex e e (zarhinAction σ ρ0 a))ᵀ * _ = _ * reindex e e (zarhinAction σ ρ0 (σ a))
    simp only [reindex_apply, transpose_submatrix, submatrix_mul_equiv, hact]

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm : ∀ {X : Type} [AddCommGroup X] {r : ℕ} (b : LinearMap.BilinForm ℤ X), (∀ y z, b y z = b z y) → (∀ y, 0 ≤ b y y) → ∀ v : Fin r → X, (Matrix.of fun i j => (b (v i) (v j) : ℝ)).PosSemidef := by
  first | exact @GlobalTheory.gram_posSemidef_of_int_form | exact GlobalTheory.gram_posSemidef_of_int_form | (intros; apply GlobalTheory.gram_posSemidef_of_int_form <;> assumption)
end

section


theorem _root_.GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef : ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef → 0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  first | exact @GlobalTheory.sum_hadamard_posDef_posSemidef | exact GlobalTheory.sum_hadamard_posDef_posSemidef | (intros; apply GlobalTheory.sum_hadamard_posDef_posSemidef <;> assumption)
end

section

namespace GlobalTheory.CasimirOrder

open Matrix

variable {O : Type} [Ring O]

def form (s : O →+ O) (φ : O →+ ℤ) : LinearMap.BilinForm ℤ O :=
  LinearMap.mk₂ ℤ (fun u v => φ (s u * v))
    (fun u₁ u₂ v => by simp [map_add (f := _), add_mul])
    (fun c u v => by rw [map_zsmul, smul_mul_assoc, map_zsmul])
    (fun u v₁ v₂ => by simp [mul_add, map_add (f := _)])
    (fun c u v => by rw [mul_smul_comm, map_zsmul])

@[simp] theorem form_apply (s : O →+ O) (φ : O →+ ℤ) (u v : O) : form s φ u v = φ (s u * v) := rfl

variable {r : ℕ}

def gram (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j => φ (s (x i) * x j)

def casimir (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) : O :=
  ∑ i, ∑ j, (gram x s φ).adjugate i j • (s (x i) * x j)

theorem det_smul_eq_sum (x : Module.Basis (Fin r) ℤ O) (b : LinearMap.BilinForm ℤ O)
    (hb : ∀ u v, b u v = b v u) (v : O) :
    (Matrix.of fun i j => b (x i) (x j)).det • v =
      ∑ i, ∑ j, ((Matrix.of fun i j => b (x i) (x j)).adjugate i j * b (x i) v) • x j := by
  classical
  set G : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => b (x i) (x j) with hG
  have hGt : Gᵀ = G := by ext i j; simp [hG, hb]
  have hA : ∀ i j, G.adjugate i j = G.adjugate j i := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M i j) (adjugate_transpose G)
    rw [hGt] at h
    simpa using h.symm
  have hv : v = ∑ k, x.repr v k • x k := (x.sum_repr v).symm
  have hb' : ∀ i, b (x i) v = ∑ k, G i k * x.repr v k := by
    intro i; conv_lhs => rw [hv]

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul, mul_comm]; rfl
  have key : ∀ j, ∑ i, G.adjugate i j * b (x i) v = G.det * x.repr v j := by
    intro j
    have e : ∑ i, G.adjugate i j * b (x i) v = ∑ k, (G.adjugate * G) j k * x.repr v k := by
      simp_rw [hb', Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      rw [hA]; ring
    rw [e, adjugate_mul]
    simp [Matrix.smul_apply, Matrix.one_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, key]
  conv_lhs => rw [hv]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]


open scoped MatrixOrder in
theorem trace_mul_pos_real {n : ℕ} {P H : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) (hH : H.PosSemidef)
    (h0 : H ≠ 0) : 0 < (P * H).trace := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hP.isStrictlyPositive
  have e : (star C * C * H).trace = (C * H * Cᴴ).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]; rfl
  have hs := hH.mul_mul_conjTranspose_same C
  rw [e]
  refine hs.trace_nonneg.lt_of_ne fun h => h0 ?_
  have h1 := hs.trace_eq_zero_iff.1 h.symm
  rwa [show Cᴴ = star C from rfl, hC.star.mul_left_eq_zero, hC.mul_right_eq_zero] at h1

theorem posDef_of_int {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hs : Gᵀ = G)
    (hp : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < v ⬝ᵥ G *ᵥ v) : (G.map (Int.cast : ℤ → ℝ)).PosDef := by
  classical
  have hsym : ∀ y z, Matrix.toBilin' G y z = Matrix.toBilin' G z y := by
    intro y z
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs,
      dotProduct_comm]
  have hnn : ∀ y, 0 ≤ Matrix.toBilin' G y y := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · rw [Matrix.toBilin'_apply']; exact (hp y hy).le
  have hpsd : (G.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    have h := GlobalTheory.gram_posSemidef_of_int_form (Matrix.toBilin' G) hsym hnn (fun u => Pi.single u 1)
    convert h using 1
    ext u v
    simp [Matrix.toBilin'_apply']
  rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← Int.cast_det]
  intro h
  obtain ⟨z, hz, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (by exact_mod_cast h)
  have h1 := hp z hz
  rw [hGz, dotProduct_zero] at h1
  exact lt_irrefl _ h1

theorem adjugate_posDef {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) : P.adjugate.PosDef := by
  have hd := hP.det_pos
  have e : P.adjugate = P.det • P⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hd.ne', one_smul]
  rw [e]
  exact hP.inv.smul hd

theorem form_symm {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a)
    (hφs : ∀ a, φ (s a) = φ a) (u v : O) : form s φ u v = form s φ v u := by
  simp only [form_apply]
  rw [← hφs (s u * v), hs, hss]

theorem gram_eq (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) :
    gram x s φ = Matrix.of fun i j => form s φ (x i) (x j) := rfl

theorem gram_transpose {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) : (gram x s φ)ᵀ = gram x s φ := by
  ext i j
  simp only [transpose_apply, gram_eq, of_apply]
  exact form_symm hs hss hφs _ _

theorem adjugate_gram_symm {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) (i j : Fin r) :
    (gram x s φ).adjugate i j = (gram x s φ).adjugate j i := by
  have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M i j) (adjugate_transpose (gram x s φ))
  rw [gram_transpose hs hss hφs] at h
  simpa using h.symm

theorem casimir_star {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) : s (casimir x s φ) = casimir x s φ := by
  unfold casimir

  simp only [map_sum, map_zsmul, hs, hss]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [adjugate_gram_symm hs hss hφs]

theorem quad_eq (x : Fin r → O) (b : LinearMap.BilinForm ℤ O) (v : Fin r → ℤ) :
    v ⬝ᵥ (Matrix.of fun i j => b (x i) (x j)) *ᵥ v = b (∑ i, v i • x i) (∑ j, v j • x j) := by

  simp only [dotProduct, mulVec, of_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smul,
  LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem posDef_gram (x : Module.Basis (Fin r) ℤ O) (b : LinearMap.BilinForm ℤ O) (hb : ∀ u v, b u v = b v u)
    (hpos : ∀ w, w ≠ 0 → 0 < b w w) :
    ((Matrix.of fun i j => b (x i) (x j)).map (Int.cast : ℤ → ℝ)).PosDef := by
  refine posDef_of_int _ (by ext i j; simp [hb]) fun v hv => ?_
  rw [quad_eq]
  refine hpos _ fun h => hv ?_
  have := (Fintype.linearIndependent_iff.1 x.linearIndependent) v h
  exact funext this

end GlobalTheory.CasimirOrder
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_nonzero_minor_of_rank : ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D, (Y.submatrix S τ).det ≠ 0 := by
  first | exact @GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | exact GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | (intros; apply GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank <;> assumption)
end

section

open ValuativeRel Matrix


theorem _root_.GlobalTheory.T.matrix_rank_normal_form : ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (X : Matrix A D K), ∃ (H : Matrix (Fin X.rank) A K) (Q : Matrix D (Fin X.rank) K), H * X * Q = 1 := by
  first | exact @GlobalTheory.rank_frame_exists | exact GlobalTheory.rank_frame_exists | (intros; apply GlobalTheory.rank_frame_exists <;> assumption)
end

section

open ValuativeRel Matrix


theorem _root_.GlobalTheory.T.rows_in_span_of_rank_normal_form : ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (r : ℕ) (X : Matrix A D K) (H : Matrix (Fin r) A K) (Q : Matrix D (Fin r) K), X.rank ≤ r → IsUnit (H * X * Q) → ∀ i, ∃ s : Fin r → K, X i = s ᵥ* (H * X) := by
  first | exact @GlobalTheory.rows_mem_span_of_isUnit_mul | exact GlobalTheory.rows_mem_span_of_isUnit_mul | (intros; apply GlobalTheory.rows_mem_span_of_isUnit_mul <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.rational_matrix_eigenspace_image_spanned_rational : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K) (lam : ι → K) (e : Matrix (Fin n) (Fin n) K), (∀ y : Fin n → L, (∀ p, ((A p).map (algebraMap K L)).mulVec y = algebraMap K L (lam p) • y) ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x})) ∧ ∀ y : Fin n → L, y ∈ LinearMap.range (e.map (algebraMap K L)).mulVecLin ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) := by
  first | exact @GlobalTheory.rational_eigen_image_span | exact GlobalTheory.rational_eigen_image_span | (intros; apply GlobalTheory.rational_eigen_image_span <;> assumption)
end
