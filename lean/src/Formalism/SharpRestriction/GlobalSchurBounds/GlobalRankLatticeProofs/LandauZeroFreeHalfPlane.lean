import Formalism.SizeWindowBrackets.ChainSlopeWindows.RiemannHypothesisOfPowerBound

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.SlopeTestRemainingChoices

open Formalism

def LandauZeroFreeHalfPlane : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ y₀ : ℝ, (∀ y : ℝ, y₀ ≤ y → Gz y ≤ y ^ θ) →
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

theorem landau_zero_free_half_plane : LandauZeroFreeHalfPlane :=
  Formalism.LFunctionChainParameters.ConditionalMainTheorem.landau_zero_free_half_plane

end Formalism.MainNotions.ZetaZeroFreeRegion.SlopeTestRemainingChoices

end
