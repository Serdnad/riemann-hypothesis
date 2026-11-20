import Mathlib
import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacterStatement

def Claim.HalfPlane : Prop := UpperTheory.EveryCharacter

def Claim.Strip : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def Claim.Zeta : Prop := RiemannHypothesis
