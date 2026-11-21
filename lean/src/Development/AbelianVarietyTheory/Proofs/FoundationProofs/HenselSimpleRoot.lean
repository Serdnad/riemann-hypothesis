import Mathlib

open Polynomial

namespace GlobalTheory

/-- In an adically complete ring, a simple root modulo the ideal lifts to a root.
The polynomial may have any leading coefficient. -/
theorem exists_simple_root_of_isAdicComplete {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b =>
    b - f.eval b * Ring.inverse (f.derivative.eval b)
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f.derivative.eval (c n)) :=
    fun n => rfl
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f.derivative.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
    | succ n ih =>
      obtain ⟨k, hk⟩ := exists_mul_sq_add_linear_part_eq_eval_add f (c n)
        (-(f.eval (c n) * Ring.inverse (f.derivative.eval (c n))))
      have hu := Ring.mul_inverse_cancel _ (hf'c n)
      have e : f.eval (c (n + 1)) =
          k * (Ring.inverse (f.derivative.eval (c n))) ^ 2 * (f.eval (c n)) ^ 2 := by
        rw [hc, sub_eq_add_neg, ← hk]
        linear_combination (-f.eval (c n)) * hu
      rw [e]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (show n + 1 + 1 ≤ (n + 1) * 2 by omega) ?_)
      rw [pow_mul]
      exact Ideal.pow_mem_pow ih _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · specialize ha (0 + 1)
    rw [zero_add, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha
    rw [← SModEq.sub_mem]
    exact ha.symm.trans (hc_mod 1)

end GlobalTheory
