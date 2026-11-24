module

import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import Mathlib.Algebra.Group.ForwardDiff

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Finset
open ReciprocityTheory.ChartRestriction.G.Geo (mixedDisc)

theorem ChartGram.sum_neg_one_pow_card_pow (D : ℕ) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D = D.factorial := by
  have h1 := fwdDiff_iter_eq_sum_shift (h := (1 : ℂ)) (fun r : ℂ => r ^ D) D 0
  rw [fwdDiff_iter_eq_factorial] at h1
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (f := fun m => (-1 : ℂ) ^ (D - m) * (m : ℂ) ^ D)]
  simp only [Finset.card_univ, Fintype.card_fin]
  have h2 : ((D.factorial : ℂ → ℂ) 0) = (D.factorial : ℂ) := rfl
  rw [← h2, h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [zsmul_eq_mul, nsmul_eq_mul]
  ring

theorem ChartGram.mixedDisc_const {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun _ => A) = A.det := by
  apply _root_.ReciprocityTheory.AnForm.A.mdisc_const <;> assumption

end GroundTheory.Heights₂.Heights
