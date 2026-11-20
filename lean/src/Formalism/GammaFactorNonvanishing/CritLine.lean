import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip

open Complex DirichletCharacter

set_option linter.unusedVariables false in
/-- The primitive conclusion is a specialization of the all-character strip theorem. -/
theorem Formalism.VW.critLine (h : UpperTheory.EveryCharacter) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 :=
  Claim.strip h N χ s h0 h1 hz

theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=
  Claim.zeta h
