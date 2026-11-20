import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacterStatement

open Complex DirichletCharacter

theorem Formalism.VW.gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

theorem Formalism.VW.critLine (h : UpperTheory.EveryCharacter) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 := by
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · have hre : 1 / 2 < (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    have hs0 : s ≠ 0 := fun e => by simp [e] at h0
    have hreflect : (1 : ℂ) - s ≠ 1 := fun e => hs0 (sub_eq_self.mp e)
    exact (h N χ⁻¹ (1 - s) hre (Or.inr hreflect) (Claim.prim_reflect χ hχ h0 h1 hz)).elim
  · exact heq
  · have hs1 : s ≠ 1 := fun e => by simp [e] at h1
    exact (h N χ s hgt (Or.inr hs1) hz).elim

theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=
  Claim.zeta h
