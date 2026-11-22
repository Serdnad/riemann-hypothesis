import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA

open MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.GraphTrick

variable {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ρ : G → H →L[ℂ] H}

/-- For an irreducible unitary action, square integrability of a single matrix coefficient
of two nonzero vectors implies square integrability of every matrix coefficient. -/
theorem memLp_matrixCoefficients_of_one
    (hR : ∀ h : G, MeasurePreserving (fun g => g * h) μ μ)
    (hInv : MeasurePreserving (Inv.inv : G → G) μ μ)
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    {w₀ x₀ : H} (hw₀ : w₀ ≠ 0) (hx₀ : x₀ ≠ 0)
    (h₀ : MemLp (fun g => ⟪w₀, ρ g x₀⟫_ℂ) 2 μ) (w x : H) :
    MemLp (fun g => ⟪w, ρ g x⟫_ℂ) 2 μ := by
  have hrow := memLp_of_ne hR hone hmul hiso hirr w₀ x₀ hx₀ h₀ w
  have hcol := (hrow.comp_measurePreserving hInv).star
  refine memLp_of_ne hR hone hmul hiso hirr w w₀ hw₀ ?_ x
  convert hcol using 1
  funext g
  change ⟪w, ρ g w₀⟫_ℂ = star ⟪w₀, ρ g⁻¹ w⟫_ℂ
  rw [← star_eq hone hmul hiso g, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm w _).symm

end ReciprocityTheory.ChartRestriction.DS.GraphTrick
