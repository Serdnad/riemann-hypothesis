import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccDAdjB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdjA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDTensKStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def adjSg (ε : Fin n → Bool) (c : Fin n) : ℂ := if ε c then 1 else -1

theorem adjSg_mul_self (ε : Fin n → Bool) (c : Fin n) : adjSg ε c * adjSg ε c = 1 := by
  unfold adjSg; split_ifs <;> norm_num

theorem adjSg_conj (ε : Fin n → Bool) (c : Fin n) : (starRingEnd ℂ) (adjSg ε c) = adjSg ε c := by
  unfold adjSg; split_ifs <;> simp

theorem adjSign_eq_adjSg (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b = adjSg ε a * adjSg ε b := by
  unfold adjSign adjSg
  cases ε a <;> cases ε b <;> norm_num

section R

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def adjR (ε : Fin n → Bool) (M : Submodule ℂ X) (ps : (Fin n → X) →ₗ[ℂ] X) (x : X) (u : Fin n → X) : Prop :=
  u ∈ tensSub M ∧ ∀ c, ∀ y ∈ M, inner ℂ (u c) y = adjSg ε c * inner ℂ x (ps (Pi.single c y))

variable {ε : Fin n → Bool} {M : Submodule ℂ X} {ps : (Fin n → X) →ₗ[ℂ] X}

theorem adjR_inv {x : X} {u : Fin n → X} (h : adjR ε M ps x u) (c : Fin n) {y : X} (hy : y ∈ M) :
    inner ℂ x (ps (Pi.single c y)) = adjSg ε c * inner ℂ (u c) y := by
  rw [h.2 c y hy, ← mul_assoc, adjSg_mul_self, one_mul]

theorem adjR_unique {x : X} {u u' : Fin n → X} (h : adjR ε M ps x u) (h' : adjR ε M ps x u') : u = u' := by
  exact ReciprocityTheory.ChartRestriction.DS.adjR_unique h h'

theorem adjR_add {x x' : X} {u u' : Fin n → X} (h : adjR ε M ps x u) (h' : adjR ε M ps x' u') :
    adjR ε M ps (x + x') (u + u') := by
  refine ⟨(tensSub M).add_mem h.1 h'.1, fun c y hy => ?_⟩
  rw [Pi.add_apply, inner_add_left, inner_add_left, h.2 c y hy, h'.2 c y hy, mul_add]

theorem adjR_smul {x : X} {u : Fin n → X} (h : adjR ε M ps x u) (r : ℂ) : adjR ε M ps (r • x) (r • u) := by
  exact ReciprocityTheory.ChartRestriction.DS.adjR_smul h r

theorem adjR_linear {M' : Submodule ℂ X} (hex : ∀ x ∈ M', ∃ u, adjR ε M ps x u) :
    ∃ ι : X →ₗ[ℂ] (Fin n → X), ∀ x ∈ M', adjR ε M ps x (ι x) := by
  exact ReciprocityTheory.ChartRestriction.DS.adjR_linear hex

end R

section Amb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem adjB_tensF_mem (dual : Bool) {M : Submodule ℂ D} (hME : ∀ a b, ∀ v ∈ M, E a b v ∈ M)
    {u : Fin n → D} (hu : u ∈ tensSub M) (a b : Fin n) : tensF dual E a b u ∈ tensSub M := by
  exact ReciprocityTheory.ChartRestriction.DS.adjB_tensF_mem dual hME hu a b

theorem adjB_E (dual : Bool) (hU : IsInfUnitary ε E) {M : Submodule ℂ D} (hME : ∀ a b, ∀ v ∈ M, E a b v ∈ M)
    {ps : (Fin n → D) →ₗ[ℂ] D} (hps2 : ∀ a b, ∀ f ∈ tensSub M, ps (tensF dual E a b f) = E a b (ps f))
    {x : D} {u : Fin n → D} (h : adjR ε M ps x u) (a b : Fin n) :
    adjR ε M ps (E a b x) (tensF dual E a b u) := by
  exact ReciprocityTheory.ChartRestriction.DS.adjB_E dual hU hME hps2 h a b

theorem adjB_block {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {c d : Fin n} (h : ε c ≠ ε d) :
    k c d = 0 := by
  exact ReciprocityTheory.ChartRestriction.DS.adjB_block hk h

theorem adjB_sgn {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (dual : Bool) (c d : Fin n) :
    (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) * (adjSg ε c * adjSg ε d) =
      (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) := by
  exact ReciprocityTheory.ChartRestriction.DS.adjB_sgn hk dual c d

theorem adjB_star_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : kᴴ ∈ Kset ε := by
  exact ReciprocityTheory.ChartRestriction.DS.adjB_star_Kset hk

theorem adjB_inner (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v w : H) :
    inner ℂ (σ k v) w = inner ℂ v (σ kᴴ w) := by
  exact ReciprocityTheory.ChartRestriction.DS.adjB_inner hσ hk v w

end Amb

end ReciprocityTheory.ChartRestriction.DS.G2
