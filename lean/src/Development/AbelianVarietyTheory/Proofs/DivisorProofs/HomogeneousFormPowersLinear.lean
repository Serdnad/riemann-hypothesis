import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots

open MvPolynomial GlobalTheory.ArInt

namespace GlobalTheory.IntLinPow

/-- Every homogeneous polynomial in finitely many variables is a linear
combination of powers of linear forms with integer coefficients. -/
theorem homogeneous_eq_sum_intLinearPowers {ι : Type} [Fintype ι] {D : ℕ}
    {F : MvPolynomial ι ℝ} (hF : F.IsHomogeneous D) :
    ∃ (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D := by
  classical
  let powers := Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ D
  have hmem : F ∈ Submodule.span ℝ powers := by
    refine PowLinSpan.mem_span_of_linearPowers_on_grid hF powers
      (fun _ => (Finset.range (D + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
    · intro i
      rw [Finset.card_image_of_injective _ Nat.cast_injective]
      simpa using Nat.lt_succ_self D
    · intro u hu
      choose k _ hk using fun i => Finset.mem_image.mp (hu i)
      apply Submodule.subset_span
      refine ⟨fun i => (k i : ℤ), ?_⟩
      simp only [Int.cast_natCast, hk]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  exact ⟨c.support, c, by simpa [Finsupp.sum] using hc.symm⟩

theorem homog_eq_sum_pow_intLin : ∀ (D : ℕ) (F : MvPolynomial (Fin 5) ℝ), F.IsHomogeneous D →
    ∃ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D :=
  fun _ _ hF => homogeneous_eq_sum_intLinearPowers hF

end GlobalTheory.IntLinPow
