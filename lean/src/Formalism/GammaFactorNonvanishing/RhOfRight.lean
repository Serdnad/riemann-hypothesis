import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex

theorem Formalism.VW.rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hzero htriv hs1
  rcases lt_trichotomy s.re (1 / 2) with hleft | hline | hright
  · exfalso
    have hs0 : s ≠ 0 := by
      rintro rfl
      norm_num [riemannZeta_zero] at hzero
    have hreflect : (1 : ℂ) - s ≠ 1 := fun h => hs0 (sub_eq_self.mp h)
    have hreflect0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
    have hre : 1 / 2 < (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hzero
    rcases hzero with hcompleted | hgamma
    · apply hz (1 - s) hre hreflect
      rw [riemannZeta_def_of_ne_zero hreflect0, completedRiemannZeta_one_sub, hcompleted, zero_div]
    · obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hgamma
      cases n with
      | zero => exact hs0 (by simpa using hn)
      | succ n =>
        apply htriv
        exact ⟨n, by simpa [Nat.cast_succ, neg_mul] using hn⟩
  · exact hline
  · exact (hz s hright hs1 hzero).elim
