import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormPowersLinear

open MvPolynomial GlobalTheory.ArInt

theorem GlobalTheory.T.homogeneous_form_powers_linear : ∀ (D : ℕ) (F : MvPolynomial (Fin 5) ℝ), F.IsHomogeneous D →
    ∃ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D :=
  GlobalTheory.IntLinPow.homog_eq_sum_pow_intLin
