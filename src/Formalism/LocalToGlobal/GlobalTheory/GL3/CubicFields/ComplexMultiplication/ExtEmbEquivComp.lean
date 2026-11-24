module

import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlaceB
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.RingTheory.Algebraic.Cardinality

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical Cardinal
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

theorem extEmb_equiv_comp {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  apply _root_.ReciprocityTheory.ChartRestriction.B3.iop_extEmb <;> assumption

theorem extendEmb_holds : ExtendEmb := by
  intro M hM ρ
  haveI := hM
  have hR : Cardinal.mk M ≤ Cardinal.aleph0 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ M).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  obtain ⟨σ, hσ⟩ := extEmb_equiv_comp (M.val.toRingHom : M →+* ℂ) (ρ.toRingHom : M →+* ℂ) hR
    (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum) rfl
  exact ⟨σ, fun x => hσ x⟩

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
