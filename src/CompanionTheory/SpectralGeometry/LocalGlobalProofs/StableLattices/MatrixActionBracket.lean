module
public import Formalism.RealPlaceAnalysis.StatementA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep


@[expose] public section

open scoped BigOperators

namespace GlobalTheory.CompanionTheory.MatrixAction

open Formalism.REAL ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The linear extension of matrix units satisfying `GlRel` preserves commutators. -/
theorem bracket (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (P Q : Matrix (Fin n) (Fin n) ℂ) :
    actM E P * actM E Q - actM E Q * actM E P = actM E (P * Q - Q * P) := by
  classical
  let action : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ V :=
    { toFun := actM E
      map_add' := by intro X Y; simp [actM, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro z X; simp [actM, Matrix.smul_apply, mul_smul, Finset.smul_sum] }
  have action_single (i j : Fin n) : action (Matrix.single i j 1) = E i j := by
    change actM E (Matrix.single i j 1) = E i j
    simp only [actM, Matrix.single_apply, ite_smul, one_smul, zero_smul]
    simp [ite_and, Finset.sum_ite_irrel]
  have action_mul_single (i j k l : Fin n) :
      action (Matrix.single i j 1 * Matrix.single k l 1) = if j = k then E i l else 0 := by
    by_cases h : j = k
    · subst k
      simp [action_single]
    · rw [Matrix.single_mul_single_of_ne (1 : ℂ) i j k h 1]
      simp [h]
  let m := LinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)
  let e := LinearMap.mul ℂ (Module.End ℂ V)
  have h : (e - e.flip).compl₁₂ action action = (m - m.flip).compr₂ action := by
    apply (Matrix.stdBasis ℂ (Fin n) (Fin n)).ext
    rintro ⟨i, j⟩
    apply (Matrix.stdBasis ℂ (Fin n) (Fin n)).ext
    rintro ⟨k, l⟩
    simp only [m, e, Matrix.stdBasis_eq_single, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
      LinearMap.sub_apply, LinearMap.flip_apply]
    change action (Matrix.single i j 1) * action (Matrix.single k l 1) -
      action (Matrix.single k l 1) * action (Matrix.single i j 1) =
      action (Matrix.single i j 1 * Matrix.single k l 1 - Matrix.single k l 1 * Matrix.single i j 1)
    rw [map_sub, action_single, action_single, action_mul_single, action_mul_single]
    exact hE i j k l
  exact congrArg (fun f => f P Q) h

end GlobalTheory.CompanionTheory.MatrixAction
