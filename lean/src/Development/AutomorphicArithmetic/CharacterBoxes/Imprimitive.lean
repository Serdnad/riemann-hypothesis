import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip

open Formalism.HC

theorem UpperTheory.Top.imprimitive :
    ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h
  apply Claim.halfPlane_iff_primitive_right_strip.mpr
  intro N _ χ hχ s hs _
  exact h (PChar.mk N χ hχ) trivial s hs
