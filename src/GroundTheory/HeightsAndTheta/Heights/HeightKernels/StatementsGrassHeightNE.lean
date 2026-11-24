module

import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootAnchorNonzero
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

def PtsIntegralZeroLowerNE.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ),
    IsMultiHomogIdeal W → Finite (McClasses W) →
    (∀ (u : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, u k ≠ 0) → z ∈ mcPts W →
      g (fun p => u p.1 * z p) = g z) →
    (∀ z ∈ mcPts W, c ≤ g z) →
    c * degC W ≤ ptsIntegral (e := 0) W φ g

theorem anchor_minor {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by
  apply _root_.GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt.anchorMinor_eq_one <;> assumption

end

end GroundTheory.Heights₂.Heights
