module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOrderCentralizerStable
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

namespace Bl.general_b_fact_left

theorem goal1 :
  ∀ {k : Type} [inst : Field.{0} k] [Fintype.{0} k] (t m e : k),
  Ne.{1} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 2) (HMul.hMul.{0, 0, 0} 4 m)) 0 →
    Exists.{1} fun (x : k) ↦
      Exists.{1} fun (y : k) ↦
        Eq.{1}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} x 2) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t x) y))
            (HMul.hMul.{0, 0, 0} m (HPow.hPow.{0, 0, 0} y 2)))
          e := by
  intros
  apply @_root_.GlobalTheory.FieldCaseReduction.field_case <;> assumption

end Bl.general_b_fact_left
