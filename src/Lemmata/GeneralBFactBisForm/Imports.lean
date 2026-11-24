module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Normed.Operator.Basic
import Lemmata.GeneralBFactSecondBisForm.Goal1

@[expose] public section

universe u_1

namespace Bl.general_b_fact_bis_form

theorem goal1 {F : Type u_1} [NormedAddCommGroup F] [NormedSpace ℂ F] {U : Set F}
    (hU : IsOpen U) {G : F → ℂ} (hG : DifferentiableOn ℂ G U) {y : F} {R C : ℝ}
    (hR : 0 < R) (hsub : Metric.closedBall y R ⊆ U)
    (hC : ∀ z ∈ Metric.closedBall y R, ‖G z‖ ≤ C) :
    ‖fderiv ℂ G y‖ ≤ C / R := by
  refine Bl.general_b_fact_second_bis_form.goal1 hR
    (hG.mono (Metric.ball_subset_closedBall.trans hsub)) ?_
  exact fun z hz => hC z (Metric.ball_subset_closedBall hz)

end Bl.general_b_fact_bis_form
