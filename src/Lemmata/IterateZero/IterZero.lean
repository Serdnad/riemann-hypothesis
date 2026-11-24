module

import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Tactic.Lemma
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

namespace Bl.IterateZero

theorem goal1 :
  ∀ (k : Nat) (g : Complex → Complex) (A : Real),
  Differentiable.{0, 0, 0} Complex g →
    (∀ (t : Complex),
        LE.le.{0} (Norm.norm.{0} (g t))
          (HMul.hMul.{0, 0, 0} A (HPow.hPow.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (Norm.norm.{0} t)) k))) →
      Exists.{1} fun (P : Polynomial.{0} Complex) ↦
        And (LE.le.{0} (Polynomial.natDegree.{0} P) k) (∀ (t : Complex), Eq.{1} (g t) (Polynomial.eval.{0} t P)) := by
  intros
  apply _root_.GlobalTheory.entire_exists_polynomial_of_poly_bound <;> assumption

end Bl.IterateZero
