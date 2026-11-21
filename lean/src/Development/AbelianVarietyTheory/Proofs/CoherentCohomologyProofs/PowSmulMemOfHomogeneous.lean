import Mathlib.Algebra.DirectSum.Decomposition

namespace GlobalTheory

/-- Every vector can be moved into a submodule by a power of a scalar if each
homogeneous vector can be moved into it by some power. -/
theorem exists_pow_smul_mem_of_homogeneous {ι A M σ : Type*} [DecidableEq ι]
    [Semiring A] [AddCommMonoid M] [Module A M] [SetLike σ M] [AddSubmonoidClass σ M]
    (ℳ : ι → σ) [DirectSum.Decomposition ℳ] (K : Submodule A M) (x : A)
    (h : ∀ n y, y ∈ ℳ n → ∃ k : ℕ, x ^ k • y ∈ K) (y : M) :
    ∃ k : ℕ, x ^ k • y ∈ K := by
  induction y using DirectSum.Decomposition.inductionOn ℳ with
  | zero => exact ⟨0, by simp⟩
  | @homogeneous n y => exact h n y y.property
  | add y z hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p + q, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact K.smul_mem _ hp
    · rw [pow_add, mul_smul]
      exact K.smul_mem _ hq

end GlobalTheory
