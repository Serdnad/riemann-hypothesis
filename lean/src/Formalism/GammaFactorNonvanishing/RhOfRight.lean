import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex

namespace Formalism.VW

/-- A nontrivial zero of zeta reflects to a zero away from the pole at one. -/
theorem zeta_zero_reflect {s : ℂ} (hzero : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)) (hs1 : s ≠ 1) :
    riemannZeta (1 - s) = 0 ∧ 1 - s ≠ 1 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num [riemannZeta_zero] at hzero
  have hgamma : Gammaℝ s ≠ 0 := by
    intro hz
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hz
    cases n with
    | zero => exact hs0 (by simpa using hn)
    | succ n => exact htriv ⟨n, by simpa [Nat.cast_succ, neg_mul] using hn⟩
  rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hzero
  refine ⟨?_, fun h => hs0 (sub_eq_self.mp h)⟩
  rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr hs1.symm),
    completedRiemannZeta_one_sub, hzero.resolve_right hgamma, zero_div]

theorem rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hzero htriv hs1
  refine le_antisymm (le_of_not_gt fun hright => hz s hright hs1 hzero) ?_
  refine le_of_not_gt fun hleft => ?_
  have hre : 1 / 2 < (1 - s).re := by rw [sub_re, one_re]; linarith
  obtain ⟨hreflect, hreflect1⟩ := zeta_zero_reflect hzero htriv hs1
  exact hz (1 - s) hre hreflect1 hreflect

/-- The Riemann hypothesis is equivalent to nonvanishing in the right half-plane
away from the pole at one. -/
theorem rh_iff_right_nonvanishing :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  refine ⟨?_, rh_of_right⟩
  intro h s hright hs1 hzero
  refine hright.ne' (h s hzero ?_ hs1)
  rintro ⟨n, rfl⟩
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  norm_num [mul_re, add_re, add_im, neg_re, neg_im] at hright
  linarith

end Formalism.VW
