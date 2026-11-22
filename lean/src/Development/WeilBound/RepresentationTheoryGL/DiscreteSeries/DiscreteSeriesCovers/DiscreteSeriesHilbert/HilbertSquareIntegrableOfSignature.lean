import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MatrixCoefficientPropagation

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

section SquareIntegrability

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem hq_umem (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat g ∈ UJset ε := by
  rw [← mir_UJset_eq]
  exact g.2

theorem hq_one (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w)) :
    sigLam ε Ψ T.w (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) = 1 := by
  have e : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  rw [e]
  exact hrep.1.1

theorem hq_mul (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w)) (a b : Formalism.REAL.UJ ε) :
    sigLam ε Ψ T.w (Formalism.MainNotions.S.umat (a * b)) =
      (sigLam ε Ψ T.w (Formalism.MainNotions.S.umat a)).comp (sigLam ε Ψ T.w (Formalism.MainNotions.S.umat b)) := by
  have e : Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl
  rw [e]
  exact hrep.1.2 _ (hq_umem a) _ (hq_umem b)

theorem hq_iso (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w)) (g : Formalism.REAL.UJ ε) (v : Hlam ε Ψ T.w) :
    ‖sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) v‖ = ‖v‖ :=
  hrep.2.1 _ (hq_umem g) v

theorem hq_memLp_of_ne (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w))
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w)) (w₀ x₀ : Hlam ε Ψ T.w) (hx₀ : x₀ ≠ 0)
    (h0 : MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) x₀⟫_ℂ) 2 (Formalism.REAL.muG ε))
    (x : Hlam ε Ψ T.w) :
    MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) x⟫_ℂ) 2 (Formalism.REAL.muG ε) :=
  GraphTrick.memLp_of_ne (μ := Formalism.REAL.muG ε) (ρ := fun g : Formalism.REAL.UJ ε => sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g))
    (measurePreserving_mul_right ε) (hq_one hrep) (hq_mul hrep) (hq_iso hrep)
    (Formalism.MainNotions.BridgeCSchur.irr_of hirr) w₀ x₀ hx₀ h0 x

theorem hq_inner
    (hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x)
    (y z : Hlam ε Ψ T.w) (g : Formalism.REAL.UJ ε) :
    ⟪y, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) z⟫_ℂ = inner ℂ (y : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) (z : L2 ε)) := by
  rw [Submodule.coe_inner, hcoe _ (hq_umem g)]

theorem hq_w_ne (hP : IsPsiFor ε lam T Ψ) : uniformisationL2 ε Ψ T.w T.w ≠ 0 := by
  have hw : T.w ≠ 0 := by
    intro h
    have h1 : ‖T.w‖ = 1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  exact datumEmbedding_self_ne_zero hP hw

private theorem hq_highest_coefficient_memLp (hP : IsPsiFor ε lam T Ψ)
    (hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w,
      ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x)
    (hF : ∀ g ∈ UJset ε,
      inner ℂ (uniformisationL2 ε Ψ T.w T.w) (rreg ε g (uniformisationL2 ε Ψ T.w T.w)) =
        ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ T.w (Ψ g T.w))
    (w₀ : Hlam ε Ψ T.w) (hw₀ : (w₀ : L2 ε) = uniformisationL2 ε Ψ T.w T.w) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      ⟪w₀, sigLam ε Ψ T.w (Formalism.MainNotions.S.umat g) w₀⟫_ℂ) 2 (Formalism.REAL.muG ε) := by
  convert (dt_memLp hP T.w T.w).const_mul ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) using 1
  funext g
  rw [hq_inner hcoe, hw₀, hF _ (hq_umem g)]
  rfl

theorem hq_coef_all (hP : IsPsiFor ε lam T Ψ)
    (hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x)
    (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w))
    (hF : ∀ g ∈ UJset ε, ∀ v v' : T.V,
      inner ℂ (uniformisationL2 ε Ψ T.w v') (rreg ε g (uniformisationL2 ε Ψ T.w v)) =
        ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v))
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w)) (x : Hlam ε Ψ T.w) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      inner ℂ (uniformisationL2 ε Ψ T.w T.w) (rreg ε (Formalism.MainNotions.S.umat g) (x : L2 ε))) 2 (Formalism.REAL.muG ε) := by
  let w₀ : Hlam ε Ψ T.w := ⟨_, datumEmbedding_mem_Hlam hP T.w⟩
  have hne : w₀ ≠ 0 := fun h => hq_w_ne hP (congrArg Subtype.val h)
  have h₀ := hq_highest_coefficient_memLp hP hcoe (fun g hg => hF g hg T.w T.w) w₀ rfl
  have h := hq_memLp_of_ne hrep hirr w₀ w₀ hne h₀ x
  convert h using 1
  exact funext fun g => (hq_inner hcoe w₀ x g).symm

/-- The highest-weight diagonal coefficient alone suffices for square integrability. -/
theorem hq_sqInt_of_highest_coefficient (hP : IsPsiFor ε lam T Ψ)
    (hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w,
      ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x)
    (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w))
    (hF : ∀ g ∈ UJset ε,
      inner ℂ (uniformisationL2 ε Ψ T.w T.w) (rreg ε g (uniformisationL2 ε Ψ T.w T.w)) =
        ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ T.w (Ψ g T.w))
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w)) :
    Formalism.MainNotions.S.IsSqIntOn ε (sigLam ε Ψ T.w) := by
  intro v w
  let w₀ : Hlam ε Ψ T.w := ⟨_, datumEmbedding_mem_Hlam hP T.w⟩
  have hne : w₀ ≠ 0 := fun h => hq_w_ne hP (congrArg Subtype.val h)
  exact GraphTrick.memLp_matrixCoefficients_of_one (measurePreserving_mul_right ε)
    (Measure.measurePreserving_inv (Formalism.REAL.muG ε)) (hq_one hrep) (hq_mul hrep) (hq_iso hrep)
    (Formalism.MainNotions.BridgeCSchur.irr_of hirr)
    hne hne (hq_highest_coefficient_memLp hP hcoe hF w₀ rfl) w v

theorem hq_sqInt (hP : IsPsiFor ε lam T Ψ)
    (hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x)
    (hrep : IsURepOn (UJset ε) (sigLam ε Ψ T.w))
    (hF : ∀ g ∈ UJset ε, ∀ v v' : T.V,
      inner ℂ (uniformisationL2 ε Ψ T.w v') (rreg ε g (uniformisationL2 ε Ψ T.w v)) =
        ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v))
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w)) :
    Formalism.MainNotions.S.IsSqIntOn ε (sigLam ε Ψ T.w) :=
  hq_sqInt_of_highest_coefficient hP hcoe hrep (fun g hg => hF g hg T.w T.w) hirr

end SquareIntegrability

theorem hilbert_square_integrable_of_signature : StepSig → StepSqInt := by
  intro hS n ε lam T Ψ hP hst hF hirr
  obtain ⟨hcoe, hrep, -⟩ := hS n ε lam T Ψ hP hst
  exact hq_sqInt hP hcoe hrep hF hirr

end PositivityTheory.RgDs.Hilb
