import Mathlib

namespace GlobalTheory.VolBr

structure IsBallFam {G : Type} [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G) : Prop where

  subset : ∀ r, B r ⊆ Λ

  zero_mem : ∀ r, 0 ≤ r → (0 : G) ∈ B r

  sub_mem : ∀ r r' x y, x ∈ B r → y ∈ B r' → x - y ∈ B (r + r')

  nsmul_iff : ∀ (n : ℕ) (r : ℝ) (x : G), 0 < n → x ∈ Λ → (n • x ∈ B (n * r) ↔ x ∈ B r)

theorem IsBallFam.mono {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (hB : IsBallFam Λ B) {r r' : ℝ} (h : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  simpa using hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.2 h))

theorem isBallFam_int : IsBallFam (⊤ : AddSubgroup ℤ) fun r => {x | |(x : ℝ)| ≤ r} where
  subset _ _ _ := AddSubgroup.mem_top _
  zero_mem r hr := by simpa using hr
  sub_mem r r' x y hx hy := by
    simp only [Set.mem_setOf_eq, Int.cast_sub] at hx hy ⊢
    exact (abs_sub _ _).trans (add_le_add hx hy)
  nsmul_iff n r x hn _ := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Set.mem_setOf_eq, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, abs_mul, Nat.abs_cast]
    exact ⟨fun h => le_of_mul_le_mul_left h hn', fun h => mul_le_mul_of_nonneg_left h hn'.le⟩

end GlobalTheory.VolBr
