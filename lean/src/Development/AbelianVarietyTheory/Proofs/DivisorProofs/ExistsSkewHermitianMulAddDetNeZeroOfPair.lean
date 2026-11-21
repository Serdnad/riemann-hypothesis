import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleLagrangianTransverseField

open scoped Matrix

namespace GlobalTheory

/-- Transposing the two block maps reduces the row-kernel problem to the
rank-one correction theorem for the skew form `ε • 1`. -/
theorem skewHermitian_det_mul_add_ne_zero {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι]
    (σ : k →+* k) (ε : k) (hε : ε ≠ 0) (hσε : σ ε = -ε)
    (C D : Matrix ι ι k) (hCD : C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0)
    (hrank : ∀ a : ι → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) :
    ∃ V : Matrix ι ι k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  let S : Matrix ι ι k := ε • (1 : Matrix ι ι k)
  have hSu : IsUnit S.det := by
    simp only [S, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.mpr hε).pow _
  have hS : Sᵀ = -S.map σ := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [S, hσε]
    · simp [S, hij, Ne.symm hij]
  have hker : ∀ a : ι → k, Dᵀ *ᵥ a = 0 → Cᵀ *ᵥ a = 0 → a = 0 := by
    intro a hD hC
    apply hrank a
    · rwa [← Matrix.vecMul_transpose, Matrix.transpose_transpose] at hC
    · rwa [← Matrix.vecMul_transpose, Matrix.transpose_transpose] at hD
  have hiso : Dᵀᵀ * S * Cᵀ.map σ + Cᵀᵀ * S * Dᵀ.map σ = 0 := by
    simp only [S, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.transpose_map, ← smul_add]
    rw [add_comm, hCD, smul_zero]
  obtain ⟨X, hX, hdet⟩ := KSp.transv_field σ S hSu hS Dᵀ Cᵀ hker hiso
  refine ⟨Xᵀ, ?_, ?_⟩
  · have hzero : ε • (Xᵀ + X.map σ) = 0 := by
      simpa only [S, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_add]
        using hX
    have hsum := (smul_eq_zero.mp hzero).resolve_left hε
    simpa only [Matrix.transpose_map, Matrix.transpose_transpose]
      using eq_neg_of_add_eq_zero_right hsum
  · have htranspose : (Dᵀ + X * Cᵀ)ᵀ = C * Xᵀ + D := by
      simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, add_comm]
    rw [← htranspose, Matrix.det_transpose]
    exact hdet.ne_zero

theorem exists_skewHermitian_mul_add_det_ne_zero_of_pair :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  intro k _ σ _ ε hε hσε n C D hCD hrank
  exact skewHermitian_det_mul_add_ne_zero σ ε hε hσε C D hCD hrank

end GlobalTheory
