module


import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PHermitianDetMono
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Lemma
@[expose] public section

namespace Bl.DetMonotoneStarMulSelf

open Matrix
open scoped ComplexOrder

private lemma det_diagonal_add_le {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, 0 ≤ d i)
    (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosSemidef) :
    (diagonal d).det ≤ (C + diagonal d).det := by
  classical
  let D := (detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ)
  -- Expand by choosing which rows come from C. Each term is a principal minor
  -- of C times nonnegative diagonal entries at the remaining indices.
  have hexpand : (C + diagonal d).det =
      ∑ s : Finset (Fin n), D (s.piecewise C (diagonal d)) :=
    D.map_add_univ C (diagonal d)
  have hterm (s : Finset (Fin n)) : 0 ≤ D (s.piecewise C (diagonal d)) := by
    let a : Fin n → ℂ := fun i => if i ∈ s then 1 else d i
    have hrows : s.piecewise C (diagonal d) =
        fun i => a i • s.piecewise C (1 : Matrix (Fin n) (Fin n) ℂ) i := by
      funext i j
      by_cases hi : i ∈ s
      · simp [Finset.piecewise, a, hi]
      · have hone : (1 : Matrix (Fin n) (Fin n) ℂ) i j = if i = j then 1 else 0 :=
          Matrix.one_apply
        simp only [Finset.piecewise, hi, ite_false, Pi.smul_apply, smul_eq_mul, a, diagonal_apply, hone]
        split <;> simp
    have hminor : 0 ≤ D (s.piecewise C (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      change 0 ≤ (Matrix.of (s.piecewise C.row (1 : Matrix (Fin n) (Fin n) ℂ).row)).det
      rw [det_piecewise_one_eq_submatrix_det]
      exact (hC.submatrix Subtype.val).det_nonneg
    rw [hrows, D.map_smul_univ]
    exact mul_nonneg (Finset.prod_nonneg fun i _ => by
      by_cases hi : i ∈ s <;> simp [a, hi, hd]) hminor
  rw [hexpand]
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Finset (Fin n))))
    (f := fun s => D (s.piecewise C (diagonal d))) (fun s _ => hterm s) (Finset.mem_univ ∅)
  have hempty : (∅ : Finset (Fin n)).piecewise (fun i => C i) (fun i => diagonal d i)
      = fun i => diagonal d i := Finset.piecewise_empty _ _
  calc
    (diagonal d).det = D ((∅ : Finset (Fin n)).piecewise C (diagonal d)) :=
      congrArg D hempty.symm
    _ ≤ _ := h

private lemma det_mono {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef)
    (hAB : (A - B).PosSemidef) : B.det.re ≤ A.det.re := by
  apply _root_.GroundTheory.Heights₂.Heights.FourB.HermitianDetMono.proof <;> assumption

theorem goal1 :
  ∀ (n : Nat), ReciprocityTheory.L2DbarEstimates.DetMonoStatement n := by
  intro n
  unfold ReciprocityTheory.L2DbarEstimates.DetMonoStatement
  intro A B hB hAB
  exact det_mono A B hB hAB

end Bl.DetMonotoneStarMulSelf
