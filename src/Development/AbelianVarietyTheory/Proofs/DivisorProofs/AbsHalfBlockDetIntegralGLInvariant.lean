module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AntitoneZeroOneEqOfSumEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.AbsHalfInv

theorem v_det_KGL {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v (k.val.det) = 1 := by
  apply _root_.GlobalTheory.valued_det_eq_one_of_glint <;> assumption

theorem v_det_mul_left {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k m : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v ((k * m).val.det) = Valued.v m.val.det := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_det_KGL hk, one_mul]

theorem v_det_mul_right {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k m : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v ((m * k).val.det) = Valued.v m.val.det := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_det_KGL hk, mul_one]

theorem absHalf_congr {E : Type} [Field E] [NumberField E] {w : Pl E} {x y : w.adicCompletion E}
    (h : Valued.v x = Valued.v y) : absHalf w x = absHalf w y := by
  have : ordL x = ordL y := by unfold ordL; simp only [h]
  unfold absHalf
  rw [this]

end GlobalTheory.BCT.AbsHalfInv

open GlobalTheory.BCT.AbsHalfInv in
theorem GlobalTheory.BCT.absHalf_blockDet_KGL_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m k : GLw a w × GLw b w),
    k.1 ∈ GlobalTheory.LFun.KGL w (n := a) → k.2 ∈ GlobalTheory.LFun.KGL w (n := b) →
    absHalf w ((k * m).1.val.det ^ b / (k * m).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) ∧
      absHalf w ((m * k).1.val.det ^ b / (m * k).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
  intro E _ _ _ a b w m k h1 h2
  refine ⟨absHalf_congr ?_, absHalf_congr ?_⟩
  · rw [map_div₀, map_div₀, map_pow, map_pow, map_pow, map_pow, Prod.fst_mul, Prod.snd_mul,
      v_det_mul_left h1, v_det_mul_left h2]
  · rw [map_div₀, map_div₀, map_pow, map_pow, map_pow, map_pow, Prod.fst_mul, Prod.snd_mul,
      v_det_mul_right h1, v_det_mul_right h2]
