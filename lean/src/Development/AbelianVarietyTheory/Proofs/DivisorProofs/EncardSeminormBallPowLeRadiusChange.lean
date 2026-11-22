import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallMulLeConvexity

namespace GlobalTheory.VolBr

theorem encard_ball_pow_le : ∀ (G : Type) [AddCommGroup G]
    (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (R : ℝ) (Q e : ℕ),
    1 ≤ R → 2 * R + 1 ≤ Q → (B R).Finite →
    (B R).encard ^ e ≤ (B 1).encard ^ e * (B (R * Q ^ e)).encard := by
  intro G _ Λ B hB R Q e hR hQ hfin
  have h1 : (B 1).Finite := hfin.subset (hB.mono hR)
  have hQ₂ : 2 ≤ Q := by exact_mod_cast (show (2 : ℝ) ≤ Q by linarith)
  have hQ₁ : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hcast : ((Q - 1 : ℕ) : ℝ) = (Q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one]
  have hB1 : (B 1).encard ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Set.one_le_encard_iff_nonempty.2 ⟨0, hB.zero_mem 1 zero_le_one⟩))
  induction e with
  | zero =>
    simpa using Set.one_le_encard_iff_nonempty.2 ⟨0, hB.zero_mem R (by linarith)⟩
  | succ e ih =>
    by_cases hbig : (B (R * (Q : ℝ) ^ (e + 1))).Finite
    · have hbase : R ≤ R * (Q : ℝ) ^ e := le_mul_of_one_le_right (by linarith) (one_le_pow₀ hQ₁)
      have hinc : R * (Q : ℝ) ^ e ≤ R * Q ^ (e + 1) := by
        rw [pow_succ, ← mul_assoc]
        exact le_mul_of_one_le_right (by positivity) hQ₁
      have hstep := hB.encard_mul_le (a := R * Q ^ e) (b := R) (m := Q - 1) (by omega)
        (by rw [hcast]; linarith) (hbig.subset (hB.mono hinc)) hfin h1
      have hr : ((Q - 1 : ℕ) : ℝ) * (R * Q ^ e) + R ≤ R * Q ^ (e + 1) := by
        rw [hcast, pow_succ]
        linarith only [hbase]
      rw [pow_succ, pow_succ (B 1).encard, mul_assoc]
      calc (B R).encard ^ e * (B R).encard
          ≤ ((B 1).encard ^ e * (B (R * Q ^ e)).encard) * (B R).encard := by gcongr
        _ = _ := mul_assoc _ _ _
        _ ≤ _ := mul_le_mul_right (hstep.trans (mul_le_mul_right (Set.encard_le_encard (hB.mono hr)) _)) _
    · rw [Set.Infinite.encard_eq hbig, ENat.mul_top (pow_ne_zero _ hB1)]
      exact le_top

end GlobalTheory.VolBr
