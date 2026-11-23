module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.StatementU

@[expose] public section

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pb

variable {k r : ℕ}

def PG (e : ℝ) (f : B.Mat k r → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ w : List (Bool × B.Mat k r),
    (∀ x ∈ w, B.unitLie k r x.2) → w.length ≤ n → ∀ g ∈ B.GV k r, ‖Dw w f g‖ ≤ C * B.gN g ^ e

lemma pb_ck {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (m : ℕ∞) :
    B.CkOn m (B.GV k r) f := by
  intro g₀ _
  exact ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn, fun _ _ _ => rfl⟩

lemma pb_nonneg {e : ℝ} {f : B.Mat k r → ℂ} (h : PG e f) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ w : List (Bool × B.Mat k r), (∀ x ∈ w, B.unitLie k r x.2) → w.length ≤ n →
      ∀ g ∈ B.GV k r, ‖Dw w f g‖ ≤ C * B.gN g ^ e := by
  obtain ⟨C, hC⟩ := h.2 n
  refine ⟨max C 0, le_max_right _ _, fun w hw hl g hg => (hC w hw hl g hg).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (by unfold B.gN; positivity) _)

lemma pb_mono {e e' : ℝ} {f : B.Mat k r → ℂ} (h : PG e f) (he : e ≤ e') : PG e' f := by
  refine ⟨h.1, fun n => ?_⟩
  obtain ⟨C, hC0, hC⟩ := pb_nonneg h n
  exact ⟨C, fun w hw hl g hg => (hC w hw hl g hg).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (gN_ge_one hg) he) hC0)⟩

private theorem Dw_const_zero (w : List (Bool × B.Mat k r)) :
    Dw w (fun _ : B.Mat k r => (0 : ℂ)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have h' : List.foldr Dx (fun _ : B.Mat k r => (0 : ℂ)) w = fun _ => 0 := ih
    simp only [Dw, List.foldr, Dx, h']
    split_ifs <;> funext g <;> simp [B.LdV, RdV]

lemma pb_zero (e : ℝ) : PG e (fun _ : B.Mat k r => (0 : ℂ)) := by
  unfold PG
  refine ⟨contDiff_const, fun n => ⟨0, fun w _ _ g _ => ?_⟩⟩
  rw [Dw_const_zero]
  simp

lemma pb_Dw_const (c : ℂ) (w : List (Bool × B.Mat k r)) :
    ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ Dw w (fun _ => c) = fun _ => c' := by
  induction w with
  | nil => exact ⟨c, le_rfl, rfl⟩
  | cons x w ih =>
    obtain ⟨c', -, h⟩ := ih
    refine ⟨0, by simp, ?_⟩
    have h' : List.foldr Dx (fun _ => c) w = fun _ => c' := h
    simp only [Dw, List.foldr, Dx, h']
    split_ifs <;> funext g <;> simp [B.LdV, RdV]

lemma pb_const (c : ℂ) : PG 0 (fun _ : B.Mat k r => c) := by
  unfold PG
  refine ⟨contDiff_const, fun n => ⟨‖c‖, fun w _ _ g _ => ?_⟩⟩
  obtain ⟨c', hc', h⟩ := pb_Dw_const (k := k) (r := r) c w
  rw [h, Real.rpow_zero, mul_one]
  exact hc'

lemma pb_add {e : ℝ} {f h : B.Mat k r → ℂ} (hf : PG e f) (hh : PG e h) :
    PG e (fun g => f g + h g) := by
  refine ⟨hf.1.add hh.1, fun n => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hf.2 n
  obtain ⟨C₂, hC₂⟩ := hh.2 n
  refine ⟨C₁ + C₂, fun w hw hl g hg => ?_⟩
  have hw' : ∀ x ∈ w, B.inLie k r x.2 := fun x hx => (hw x hx).1
  rw [Dw_add hw' (pb_ck hf.1 _) (pb_ck hh.1 _) g hg, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC₁ w hw hl g hg) (hC₂ w hw hl g hg))

lemma pb_Dw_mulL {w : List (Bool × B.Mat k r)} (hw : ∀ x ∈ w, B.inLie k r x.2) {f : B.Mat k r → ℂ}
    (hf : B.CkOn w.length (B.GV k r) f) :
    ∀ g ∈ B.GV k r, Dw w (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) g =
      ContinuousLinearMap.mul ℂ ℂ (Dw w f g) := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hle : ((w.length : ℕ) : ℕ∞) ≤ ((x :: w).length : ℕ) := by exact_mod_cast Nat.le_succ _
    have e : (1 : ℕ∞) + (w.length : ℕ∞) = ((x :: w).length : ℕ) := by
      push_cast [List.length_cons]; ring
    intro g hg
    show Dx x (Dw w _) g = ContinuousLinearMap.mul ℂ ℂ (Dx x (Dw w f) g)
    rw [Dx_congr (hw x (by simp)) (ih hw' (sCkOn_mono hle hf)) g hg]
    have h1 := CkOn_diff (hw x (by simp)) (CkOn_Dw hw' (m := 1) (by rw [e]; exact hf)) hg hg
    have h2 := ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [Dx_eq]
    exact h2.deriv

lemma pb_mul {e₁ e₂ : ℝ} {f h : B.Mat k r → ℂ} (hf : PG e₁ f) (hh : PG e₂ h) :
    PG (e₁ + e₂) (fun g => f g * h g) := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) :=
    ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ).contDiff.comp hf.1
  refine ⟨hf.1.mul hh.1, fun n => ?_⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := pb_nonneg hf n
  obtain ⟨C₂, hC₂0, hC₂⟩ := pb_nonneg hh n
  refine ⟨2 ^ n * (C₁ * C₂), fun w hw hl g hg => ?_⟩
  have hw' : ∀ x ∈ w, B.inLie k r x.2 := fun x hx => (hw x hx).1
  have hP : Pr (∅ : Set (B.Mat k r)) (B.GV k r) w.length
      (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) h :=
    ⟨pb_ck hcd _, pb_ck hh.1 _, fun _ _ hg => hg.elim⟩
  have hp := gN_pos hg
  have hp1 : 0 ≤ B.gN g ^ e₁ := Real.rpow_nonneg hp.le _
  have hp2 : 0 ≤ B.gN g ^ e₂ := Real.rpow_nonneg hp.le _
  have hM : 0 ≤ C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂) :=
    mul_nonneg (mul_nonneg hC₁0 hp1) (mul_nonneg hC₂0 hp2)
  have hb := leib_bound isOpen_empty (fun g hg => Or.inr hg) g hg (C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂)) w
    (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) h hw' hP (by
      intro w₁ w₂ h₁ h₂ _
      have u1 : ∀ x ∈ w₁, B.unitLie k r x.2 := fun x hx => hw x (h₁.subset hx)
      have u2 : ∀ x ∈ w₂, B.unitLie k r x.2 := fun x hx => hw x (h₂.subset hx)
      rw [pb_Dw_mulL (fun x hx => (u1 x hx).1) (pb_ck hf.1 _) g hg]
      exact mul_le_mul ((ContinuousLinearMap.opNorm_mul_apply_le _ _ _).trans
          (hC₁ w₁ u1 (h₁.length_le.trans hl) g hg))
        (hC₂ w₂ u2 (h₂.length_le.trans hl) g hg) (norm_nonneg _) (mul_nonneg hC₁0 hp1))
  have e1 : (fun g => f g * h g) = ap (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) h := by
    funext g; simp [ap]
  rw [e1]
  refine hb.trans ?_
  rw [Real.rpow_add hp]
  have h2 : (2 : ℝ) ^ w.length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hl
  calc (2 : ℝ) ^ w.length * (C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂))
      ≤ 2 ^ n * (C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂)) := mul_le_mul_of_nonneg_right h2 hM
    _ = 2 ^ n * (C₁ * C₂) * (B.gN g ^ e₁ * B.gN g ^ e₂) := by ring

end pb

end PI.UnitaryCorollaryDerivatives
end
end

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem mx_le_one {k r : ℕ} {X : B.Mat k r} (h : B.unitLie k r X) : mx X ≤ 1 := by
  show ‖Matrix.of.symm X‖ ≤ 1
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  exact h.2 i j

theorem dw_dj (h1 : DjCurve) (k j ρ : ℕ) : ∀ w : List (Bool × B.Mat k (j + ρ)),
    (∀ x ∈ w, inLieP k j ρ x.2 ∧ mx x.2 ≤ 1) →
    ∃ K : ℂ, ‖K‖ ≤ (j : ℝ) ^ w.length ∧ ∀ g, Dw w (DjU k j ρ) g = K * DjU k j ρ g := by
  intro w
  induction w with
  | nil => intro _; exact ⟨1, by simp, fun g => by simp [Dw]⟩
  | cons x w ih =>
    intro hw
    obtain ⟨K, hK, hD⟩ := ih fun y hy => hw y (by simp [hy])
    obtain ⟨hxP, hxm⟩ := hw x (by simp)
    obtain ⟨c₁, c₂, hc₁, hc₂, hcur⟩ := h1 k j ρ x.2 hxP
    have hderiv : ∀ (c D : ℂ), HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c) * D) (c * D) 0 := by
      intro c D
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * c) (1 * c) 0 :=
        (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const c
      have := (h0.cexp).mul_const D
      simpa using this
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    obtain ⟨b, X⟩ := x
    cases b
    · refine ⟨c₁ * K, ?_, fun g => ?_⟩
      · rw [norm_mul, List.length_cons, pow_succ']
        exact mul_le_mul (hc₁.trans (mul_le_of_le_one_right hj hxm)) hK (norm_nonneg _) hj
      · have e : Dw ((false, X) :: w) (DjU k j ρ) = Dx (false, X) (fun g => K • DjU k j ρ g) := by
          show Dx (false, X) (Dw w (DjU k j ρ)) = _
          congr 1; funext g; rw [hD g, smul_eq_mul]
        rw [e, Dx_smul]
        show K • Dx (false, X) (DjU k j ρ) g = _
        rw [Dx_eq]
        have e2 : (fun t : ℝ => DjU k j ρ (crv (false, X) g t)) =
            fun t : ℝ => Complex.exp ((t : ℂ) * c₁) * DjU k j ρ g := by
          funext t; exact (hcur g t).1
        simp only [e2, (hderiv c₁ _).deriv, smul_eq_mul]
        ring
    · refine ⟨c₂ * K, ?_, fun g => ?_⟩
      · rw [norm_mul, List.length_cons, pow_succ']
        exact mul_le_mul (hc₂.trans (mul_le_of_le_one_right hj hxm)) hK (norm_nonneg _) hj
      · have e : Dw ((true, X) :: w) (DjU k j ρ) = Dx (true, X) (fun g => K • DjU k j ρ g) := by
          show Dx (true, X) (Dw w (DjU k j ρ)) = _
          congr 1; funext g; rw [hD g, smul_eq_mul]
        rw [e, Dx_smul]
        show K • Dx (true, X) (DjU k j ρ) g = _
        rw [Dx_eq]
        have e2 : (fun t : ℝ => DjU k j ρ (crv (true, X) g t)) =
            fun t : ℝ => Complex.exp ((t : ℂ) * c₂) * DjU k j ρ g := by
          funext t; exact (hcur g t).2
        simp only [e2, (hderiv c₂ _).deriv, smul_eq_mul]
        ring

theorem djWB_of (h1 : DjCurve) (h2 : PolyB) (h3 : DjPoly) (h4 : CompC) : DjWB := by
  intro k j ρ χ n hχ
  obtain ⟨hcD, hB⟩ := h2 k (j + ρ) j (DjU k j ρ) (h3 k j ρ)
  obtain ⟨CP, hCP⟩ := hB n
  refine ⟨hχ.1.comp hcD, ?_⟩
  obtain ⟨R, hR⟩ := (hχ.2.1 : IsCompact (tsupport χ)).isBounded.exists_norm_le
  refine h4 k (j + ρ) (DjU k j ρ) χ (costP k j ρ) n (|CP| + (max 1 (j : ℝ)) ^ n * |R|) hcD hχ.1 hχ.2.1 ?_
  intro u v hu hv hl hne g hg hgs
  have hg1 := gN_ge_one hg
  have hS0 : (0 : ℝ) ≤ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ |CP| := abs_nonneg _
  have hBn : 0 ≤ (max 1 (j : ℝ)) ^ n * |R| := by positivity
  by_cases hall : ∀ X ∈ u ++ v, inLieP k j ρ X
  ·
    have hw : ∀ x ∈ wL u ++ wR v, inLieP k j ρ x.2 ∧ mx x.2 ≤ 1 := by
      intro x hx
      simp only [wL, wR, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact ⟨hall X (List.mem_append_left _ hX), mx_le_one (hu X hX)⟩
      · exact ⟨hall X (List.mem_append_right _ hX), mx_le_one (hv X hX)⟩
    obtain ⟨K, hK, hD⟩ := dw_dj h1 k j ρ _ hw
    rw [dLR_eq, hD g, norm_mul]
    have hlen : (wL u ++ wR v).length ≤ n := by rw [len_LR]; exact hl
    have hK' : ‖K‖ ≤ (max 1 (j : ℝ)) ^ n :=
      hK.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hlen))
    have hDR : ‖DjU k j ρ g‖ ≤ |R| := (hR _ hgs).trans (le_abs_self _)
    have h1' : 1 ≤ B.gN g ^ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := Real.one_le_rpow hg1 hS0
    calc ‖K‖ * ‖DjU k j ρ g‖ ≤ (max 1 (j : ℝ)) ^ n * |R| :=
          mul_le_mul hK' hDR (norm_nonneg _) (by positivity)
      _ ≤ (|CP| + (max 1 (j : ℝ)) ^ n * |R|) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h1' (by positivity)
  · obtain ⟨X, hX, hXP⟩ : ∃ X ∈ u ++ v, ¬ inLieP k j ρ X := by
      by_contra hc; exact hall (fun X hX => by by_contra h; exact hc ⟨X, hX, h⟩)
    have hcX : costP k j ρ X = j := by simp [costP, hXP]
    have hjS : (j : ℝ) ≤ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := costP k j ρ) hX)
      rw [hcX] at this; exact_mod_cast this
    have hb := hCP u v hu hv hl g hg
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero, Nat.cast_zero, add_zero] at hb
    calc ‖B.dLR u v (DjU k j ρ) g‖ ≤ CP * B.gN g ^ (j : ℝ) := hb
      _ ≤ |CP| * B.gN g ^ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) :=
          mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hg1 hjS) (by positivity) hA
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end PI.UnitaryCorollaryDerivatives
end
end

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem gfWB_of (h1 : GfPoly) (h2 : PolyB) (h3 : CompR) : GfWB := by
  intro k r z z' χε ε n hχ
  obtain ⟨hχs, hχd, -⟩ := hχ
  obtain ⟨hsmC, hwb⟩ :=
    h2 k r (2 * (r + 1)) (fun g => ((Gf k r z z' g : ℝ) : ℂ)) (h1 k r z z')
  have hsmR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => Gf k r z z' g) := by
    have h := Complex.reCLM.contDiff.comp hsmC
    simpa [Function.comp_def] using h
  refine ⟨?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (hχs.comp hsmR)
  · obtain ⟨C₀, hC₀⟩ := hwb n
    refine h3 k r (fun g => Gf k r z z' g) χε (fun _ => 2 * (r + 1)) n C₀ hsmR hχs hχd ?_
    intro u v hu hv hlen hne g hg
    have hb := hC₀ u v hu hv hlen g hg
    have h1g : 1 ≤ B.gN g := gN_ge_one hg
    have hexp : ((2 * (r + 1) : ℕ) : ℝ) + ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ) ≤
        ((((u ++ v).map (fun _ => 2 * (r + 1))).sum : ℕ) : ℝ) := by
      have hl : 1 ≤ (u ++ v).length := List.length_pos_iff.mpr hne
      simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero, Nat.cast_zero,
        add_zero]
      exact_mod_cast Nat.le_mul_of_pos_left _ hl
    have hpos : 0 < B.gN g ^ (((2 * (r + 1) : ℕ) : ℝ) +
        ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos h1g) _
    have hC : 0 ≤ C₀ := (mul_nonneg_iff_of_pos_right hpos).mp ((norm_nonneg _).trans hb)
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1g hexp) hC)

end PI.UnitaryCorollaryDerivatives
end
end
