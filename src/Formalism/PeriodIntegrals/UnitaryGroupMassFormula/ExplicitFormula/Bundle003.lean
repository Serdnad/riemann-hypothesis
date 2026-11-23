module

public import Formalism.PeriodIntegrals.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectIntEqZeroOfDifferentiableOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.EF

open Complex DirichletCharacter

theorem zeta_one_sub_le {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5) (h : w ≠ 1) :
    ‖riemannZeta (1 - w)‖ ≤ 6 * ‖w + 1‖ ^ 5 * ‖riemannZeta w‖ := by
  have hp : (1 : DirichletCharacter ℂ 1).IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
  have h0 := norm_L_one_sub_le (N := 1) hp h1 h2 (Or.inr h)
  simpa [DirichletCharacter.LFunction_modOne_eq] using h0

theorem zeta_right (hZ : PI.ZetaBoundRight) {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 8) :
    ‖(s - 1) * riemannZeta s‖ ≤ 51 * (|s.im| + 2) ^ 2 := by
  by_cases hs : s = 1
  · subst hs
    simp only [sub_self, zero_mul, norm_zero]
    positivity
  have hre : 0 < s.re := by linarith
  have hb := hZ s hre hs
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hs)
  have ht := abs_nonneg s.im
  have hs_le : ‖s‖ ≤ 8 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [abs_of_pos hre]
    linarith
  have hs1_le : ‖s - 1‖ ≤ 7 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    have : |s.re - 1| ≤ 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hinv : 1 / s.re ≤ 2 := by rw [div_le_iff₀ hre]; linarith
  rw [norm_mul]
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖s - 1‖ + 1 + ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by
        rw [mul_add, mul_add, mul_one_div_cancel hn1.ne']
        ring
    _ ≤ (7 + |s.im|) + 1 + (7 + |s.im|) * (8 + |s.im|) * (1 + 2) := by gcongr
    _ ≤ 51 * (|s.im| + 2) ^ 2 := by nlinarith

theorem zeta_left (hZ : PI.ZetaBoundRight) {s : ℂ} (h1 : -4 ≤ s.re) (h2 : s.re < 1 / 2)
    (h3 : 1 / 2 ≤ ‖s‖) : ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (|s.im| + 2) ^ 7 := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h3
    norm_num at h3
  have hw1 : 1 / 2 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw2 : (1 - s).re ≤ 5 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw : (1 - s) ≠ 1 := by
    intro h0
    apply hs0
    linear_combination -h0
  have hz1 := zeta_one_sub_le hw1 hw2 hw
  rw [sub_sub_cancel] at hz1
  have hwre : 0 < (1 - s).re := by linarith
  have hz2 := hZ (1 - s) hwre hw
  have ht := abs_nonneg s.im
  have hwim : |(1 - s).im| = |s.im| := by simp
  have hn : ‖1 - s - 1‖ = ‖s‖ := by rw [show 1 - s - 1 = -s by ring, norm_neg]
  have hinv1 : 1 / ‖1 - s - 1‖ ≤ 2 := by
    rw [hn, div_le_iff₀ (by linarith)]
    linarith
  have hinv2 : 1 / (1 - s).re ≤ 2 := by rw [div_le_iff₀ hwre]; linarith
  have hw_le : ‖1 - s‖ ≤ 5 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hwim, abs_of_pos hwre]
    linarith
  have hw1_le : ‖1 - s + 1‖ ≤ 6 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e : |(1 - s + 1).im| = |s.im| := by simp
    have e2 : (1 - s + 1).re = (1 - s).re + 1 := by simp
    rw [e, e2, abs_of_pos (by linarith)]
    linarith
  have hzw : ‖riemannZeta (1 - s)‖ ≤ 18 + 3 * |s.im| := by
    calc ‖riemannZeta (1 - s)‖ ≤ 1 + 1 / ‖1 - s - 1‖ + ‖1 - s‖ * (1 + 1 / (1 - s).re) := hz2
      _ ≤ 1 + 2 + (5 + |s.im|) * (1 + 2) := by gcongr
      _ = 18 + 3 * |s.im| := by ring
  have hsn : ‖s - 1‖ = ‖1 - s‖ := norm_sub_rev _ _
  rw [norm_mul, hsn]
  calc ‖1 - s‖ * ‖riemannZeta s‖ ≤ ‖1 - s‖ * (6 * ‖1 - s + 1‖ ^ 5 * ‖riemannZeta (1 - s)‖) := by gcongr
    _ ≤ (5 + |s.im|) * (6 * (6 + |s.im|) ^ 5 * (18 + 3 * |s.im|)) := by gcongr
    _ ≤ (3 * (|s.im| + 2)) * (6 * (3 * (|s.im| + 2)) ^ 5 * (9 * (|s.im| + 2))) := by
        gcongr <;> linarith
    _ = 39366 * (|s.im| + 2) ^ 7 := by ring
    _ ≤ 48114 * (|s.im| + 2) ^ 7 := by gcongr; norm_num

theorem zetaGrowth_of (hZ : PI.ZetaBoundRight) : ZetaGrowth 300000 := by
  intro s hs1 hs2
  have ht := abs_nonneg s.im
  have h2 : (2 : ℝ) ≤ |s.im| + 2 := by linarith
  by_cases hr : 1 / 2 ≤ s.re
  · have hp7 : (|s.im| + 2) ^ 2 ≤ (|s.im| + 2) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc ‖(s - 1) * riemannZeta s‖ ≤ 51 * (|s.im| + 2) ^ 2 := zeta_right hZ hr hs2
      _ ≤ 300000 * (|s.im| + 2) ^ 7 := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ |s.im| + 2) 2]
  · push_neg at hr
    by_cases hn : 1 / 2 ≤ ‖s‖
    · calc ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (|s.im| + 2) ^ 7 := zeta_left hZ hs1 hr hn
        _ ≤ 300000 * (|s.im| + 2) ^ 7 := by gcongr; norm_num
    · push_neg at hn
      have hK : ∀ z ∈ frontier (Metric.ball (0 : ℂ) (1 / 2)),
          ‖(z - 1) * riemannZeta z‖ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by
        intro z hz
        rw [frontier_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0), mem_sphere_zero_iff_norm] at hz
        have hre : |z.re| ≤ 1 / 2 := (Complex.abs_re_le_norm z).trans hz.le
        have him : |z.im| ≤ 1 / 2 := (Complex.abs_im_le_norm z).trans hz.le
        have hzi := abs_nonneg z.im
        rcases lt_or_ge z.re (1 / 2) with hlt | hge
        · calc ‖(z - 1) * riemannZeta z‖ ≤ 48114 * (|z.im| + 2) ^ 7 :=
                zeta_left hZ (by linarith [(abs_le.1 hre).1]) hlt (by rw [hz])
            _ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by gcongr; linarith
        · calc ‖(z - 1) * riemannZeta z‖ ≤ 51 * (|z.im| + 2) ^ 2 :=
                zeta_right hZ hge (by linarith [(abs_le.1 hre).2])
            _ ≤ 51 * (5 / 2 : ℝ) ^ 2 := by gcongr; linarith
            _ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by norm_num
      have hd : DiffContOnCl ℂ (fun z => (z - 1) * riemannZeta z) (Metric.ball (0 : ℂ) (1 / 2)) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
        intro z hz
        have hz1 : z ≠ 1 := by
          intro h
          rw [h, Metric.mem_closedBall, dist_zero_right, norm_one] at hz
          norm_num at hz
        exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz1)).differentiableWithinAt
      have hmem : s ∈ closure (Metric.ball (0 : ℂ) (1 / 2)) := subset_closure (mem_ball_zero_iff.2 hn)
      have hb := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hK hmem
      calc ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := hb
        _ ≤ 300000 * 2 ^ 7 := by norm_num
        _ ≤ 300000 * (|s.im| + 2) ^ 7 := by gcongr

end PI.EF
end
end

section

namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries

lemma LSeries_twist_eq_neg_logDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) s =
      -logDeriv (DirichletCharacter.LFunction χ) s := by
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have e : (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) =
      ((fun n : ℕ => χ (n : ZMod N)) * fun n : ℕ => ((Λ n : ℝ) : ℂ)) := by
    funext n
    simp only [Pi.mul_apply]
    exact mul_comm _ _
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds s] LSeries (fun n : ℕ => χ (n : ZMod N)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  rw [e, h, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, neg_div]

theorem perronL_of {C : ℝ} (hC : 0 ≤ C) (h : PerronTrunc C) : PerronL C := by
  unfold PerronL psiRaw vertInt Err
  intro N _ χ u T T' hT hTu hTT' hT'
  have hu : 2 ≤ u := le_trans hT hTu
  have hc : 1 < cLine u := by
    unfold cLine
    have hlog := Real.log_pos (show (1:ℝ) < u by linarith)
    first
      | (have := one_div_pos.mpr hlog; linarith)
      | (norm_num; positivity)
      | done
  have hΛ : ∀ n : ℕ, ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N)‖ ≤ Λ n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)
  have key := h (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) hΛ u T' hu (by linarith)
  have hint : ∀ t : ℝ, LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) (↑(cLine u) + ↑t * I) =
      -logDeriv (DirichletCharacter.LFunction χ) (↑(cLine u) + ↑t * I) := by
    intro t
    apply LSeries_twist_eq_neg_logDeriv
    simpa using hc
  simp only [hint] at key
  refine key.trans ?_
  have hN : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hl0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have h1 : u ≤ N * u := le_mul_of_one_le_left hu0.le hN
  have h2 : N * u ≤ N * u * T := le_mul_of_one_le_right (by positivity) (by linarith)
  have hl1 : Real.log u ≤ Real.log (N * u * T) := Real.log_le_log hu0 (h1.trans h2)
  have hl2 : Real.log u ≤ Real.log (N * u) := Real.log_le_log hu0 h1
  have hsq : Real.log u ^ 2 ≤ Real.log (N * u * T) ^ 2 := by nlinarith
  have hA : u * Real.log u ^ 2 / T' ≤ u * Real.log (N * u * T) ^ 2 / T := by
    calc u * Real.log u ^ 2 / T' ≤ u * Real.log u ^ 2 / T :=
          div_le_div_of_nonneg_left (by positivity) hT0 hTT'
      _ ≤ u * Real.log (N * u * T) ^ 2 / T :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hu0.le) hT0.le
  exact mul_le_mul_of_nonneg_left (add_le_add hA hl2) hC

end PI.EF.PK
end

section

noncomputable section

namespace PI.EF

open Complex DirichletCharacter

theorem norm_root_number_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ‖eps0 χ‖ ≤ 1 := by
  unfold PI.EF.eps0
  split_ifs <;> simp

theorem norm_character_correction_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ‖del1 χ‖ ≤ 1 := by
  unfold PI.EF.del1
  split_ifs <;> simp

theorem norm_near_sum_le {C : ℝ} (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ)‖ ≤
      C * Real.log (N * (|s.im| + 2)) / d := by
  have hf := (hC N χ hχ s.im).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hf]
  calc ‖∑ ρ ∈ hf.toFinset, (mult χ ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ hf.toFinset, ‖(mult χ ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hf.toFinset, (mult χ ρ : ℝ) / d := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd (h ρ ((Set.Finite.mem_toFinset hf).mp hρ))
    _ = (∑ ρ ∈ hf.toFinset, (mult χ ρ : ℝ)) / d := by rw [Finset.sum_div]
    _ ≤ C * Real.log (N * (|s.im| + 2)) / d := by
        apply div_le_div_of_nonneg_right _ hd.le
        rw [← finsum_mem_eq_finite_toFinset_sum _ hf]
        exact (hC N χ hχ s.im).2

private lemma norm_le_add_add_four_of_norm_sub_le {a b c e : ℂ} {x y : ℝ} (h1 : ‖a - b - c + e‖ ≤ x) (h2 : ‖b‖ ≤ y)
    (h3 : ‖c‖ ≤ 2) (h4 : ‖e‖ ≤ 2) : ‖a‖ ≤ x + y + 4 := by
  have e1 : a = (a - b - c + e) + b + c - e := by ring
  rw [e1]
  have k1 := norm_sub_le ((a - b - c + e) + b + c) e
  have k2 := norm_add_le ((a - b - c + e) + b) c
  have k3 := norm_add_le (a - b - c + e) b
  linarith

theorem norm_logDeriv_le {Cw Cl : ℝ} (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3)
    (h0 : LFunction χ s ≠ 0) (hs0 : 1 / 2 ≤ ‖s‖) (hs1 : 1 / 2 ≤ ‖s - 1‖) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖logDeriv (LFunction χ) s‖ ≤
      Cl * Real.log (N * (|s.im| + 2)) + Cw * Real.log (N * (|s.im| + 2)) / d + 4 := by
  have hs1' : s ≠ 1 := by
    rintro rfl
    norm_num at hs1
  have hmain := hL N χ hχ s h1 h2 h0 hs1'
  have hsum := norm_near_sum_le hW χ hχ s hd h
  have hE : ‖eps0 χ / s‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith [norm_root_number_le_one χ]
  have hD : ‖del1 χ / (s - 1)‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith [norm_character_correction_le χ]
  exact norm_le_add_add_four_of_norm_sub_le hmain hsum hE hD

theorem log_two_le_log {N : ℕ} [NeZero N] {x : ℝ} (hx : 2 ≤ x) : Real.log 2 ≤ Real.log (N * x) := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  exact Real.log_le_log (by norm_num) (by nlinarith)

theorem logDerivLeft_of {Cw Cl : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hW : ZerosWindowWith Cw)
    (hL : LocalLemma Cl) (hZ : ZeroLocus) : LogDerivLeft (Cl + 2 * Cw + 6) := by
  unfold PI.EF.LogDerivLeft PI.EF.ZeroLocus at *
  intro N _ χ hχ t
  have hre : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).re = -1 / 2 := by norm_num
  have him : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im = t := by norm_num
  have hne1 : ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro a
    have := congrArg Complex.re a
    rw [hre] at this
    norm_num at this
  have hL0 : LFunction χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h0
    rcases hZ N χ hχ _ (by rw [hre]; norm_num) hne1 h0 with ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩
    · rw [hre] at a
      norm_num at a
    · have := congrArg Complex.re a
      rw [hre] at this
      norm_num at this
    · have := congrArg Complex.re a
      rw [hre] at this
      norm_num at this
  have hs0 : 1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ :=
    le_trans (by rw [hre]; norm_num) (Complex.abs_re_le_norm _)
  have hs1 : 1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I - 1‖ :=
    le_trans (by rw [Complex.sub_re, hre, Complex.one_re]; norm_num) (Complex.abs_re_le_norm _)
  have hnear : ∀ ρ ∈ ZerosNear χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im,
      1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I - ρ‖ := by
    intro ρ hρ
    unfold PI.ZerosNear at hρ
    simp only [Set.mem_setOf_eq] at hρ
    obtain ⟨a1, a2, -, -⟩ := hρ
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, hre, abs_of_neg (by linarith)]
    linarith
  have key := norm_logDeriv_le hW hL χ hχ _ hre.symm.le (by rw [hre]; norm_num) hL0 hs0 hs1
    (by norm_num : (0 : ℝ) < 1 / 2) hnear
  rw [him] at key
  have hlog2 : Real.log 2 ≤ Real.log (N * (|t| + 2)) := log_two_le_log (by linarith [abs_nonneg t])
  have hl2 := Real.log_two_gt_d9
  refine le_trans key ?_
  calc Cl * Real.log (N * (|t| + 2)) + Cw * Real.log (N * (|t| + 2)) / (1 / 2) + 4
        = Cl * Real.log (N * (|t| + 2)) + 2 * Cw * Real.log (N * (|t| + 2)) + 4 := by ring
    _ ≤ Cl * Real.log (N * (|t| + 2)) + 2 * Cw * Real.log (N * (|t| + 2)) +
          6 * Real.log (N * (|t| + 2)) := by linarith
    _ = (Cl + 2 * Cw + 6) * Real.log (N * (|t| + 2)) := by ring

theorem norm_logDeriv_horiz {Cw Cl κ : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hκ : 0 < κ)
    (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) (hZ : ZeroLocus) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T' : ℝ} (hT' : 2 ≤ T')
    (hg : GoodHeight χ κ T') (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3) (him : |s.im| = T') :
    ‖logDeriv (LFunction χ) s‖ ≤ (4 * Cl + 2 * Cw * κ + 16) * Real.log (N * T') ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hℓ2 : Real.log 2 ≤ Real.log (N * T') := log_two_le_log hT'
  have hl2 := Real.log_two_gt_d9
  have hlogT2 : Real.log (N * (T' + 2)) ≤ 2 * Real.log (N * T') := by
    have e : 2 * Real.log (N * T') = Real.log ((N * T') ^ 2) := by
      rw [Real.log_pow]
      norm_num
    rw [e]
    apply Real.log_le_log (by nlinarith)
    have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hT2 : T' + 2 ≤ T' ^ 2 := by nlinarith
    calc (N : ℝ) * (T' + 2) ≤ N * T' ^ 2 := mul_le_mul_of_nonneg_left hT2 (by linarith)
      _ ≤ N ^ 2 * T' ^ 2 := mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ = (N * T') ^ 2 := by ring
  have hlogpos2 : 0 ≤ Real.log (N * (T' + 2)) := Real.log_nonneg (by nlinarith)
  unfold PI.EF.GoodHeight at hg
  set ℓ := Real.log (N * T') with hℓ
  have hℓpos : 0 < ℓ := by linarith
  have hd : 0 < 1 / (κ * ℓ) := one_div_pos.mpr (mul_pos hκ hℓpos)
  have hsim : 2 ≤ |s.im| := by rw [him]; exact hT'
  have hs0 : 1 / 2 ≤ ‖s‖ := by linarith [Complex.abs_im_le_norm s]
  have hs1 : 1 / 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hs1' : s ≠ 1 := by
    rintro rfl
    norm_num at hsim
  have hL0 : LFunction χ s ≠ 0 := by
    intro h0
    rcases hZ N χ hχ s (by linarith) hs1' h0 with ⟨a1, a2⟩ | ⟨a, _⟩ | ⟨a, _⟩
    · have := hg s a1 a2 h0
      rw [him, sub_self, abs_zero] at this
      linarith
    · rw [a] at hsim
      norm_num at hsim
    · rw [a] at hsim
      norm_num at hsim
  have hnear : ∀ ρ ∈ ZerosNear χ s.im, 1 / (κ * ℓ) ≤ ‖s - ρ‖ := by
    intro ρ hρ
    unfold PI.ZerosNear at hρ
    simp only [Set.mem_setOf_eq] at hρ
    obtain ⟨a1, a2, -, a4⟩ := hρ
    have hgρ := hg ρ a1 a2 a4
    have k1 : |(|ρ.im|) - T'| ≤ |s.im - ρ.im| := by
      rw [← him, abs_sub_comm]
      exact abs_abs_sub_abs_le_abs_sub s.im ρ.im
    have k2 : |s.im - ρ.im| ≤ ‖s - ρ‖ := by
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    linarith
  have key := norm_logDeriv_le hW hL χ hχ s h1 h2 hL0 hs0 hs1 hd hnear
  rw [him, div_div_eq_mul_div, div_one] at key
  refine le_trans key ?_
  have h_a : Cl * Real.log (N * (T' + 2)) ≤ Cl * (2 * ℓ) := mul_le_mul_of_nonneg_left hlogT2 hCl
  have h_b : 2 * ℓ ≤ 4 * ℓ ^ 2 := by nlinarith
  have h_c : Cl * (2 * ℓ) ≤ Cl * (4 * ℓ ^ 2) := mul_le_mul_of_nonneg_left h_b hCl
  have h_d : Cw * Real.log (N * (T' + 2)) * (κ * ℓ) ≤ Cw * (2 * ℓ) * (κ * ℓ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogT2 hCw) (mul_pos hκ hℓpos).le
  have h_e : 4 ≤ 16 * ℓ ^ 2 := by nlinarith
  nlinarith [h_a, h_c, h_d, h_e]

theorem logDerivHoriz_of {Cw Cl κ : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hκ : 0 < κ)
    (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) (hZ : ZeroLocus) :
    LogDerivHoriz κ (4 * Cl + 2 * Cw * κ + 16) := by
  unfold PI.EF.LogDerivHoriz
  intro N _ χ hχ T' hT' hg σ h1 h2
  have hT0 : (0 : ℝ) ≤ T' := by linarith
  constructor
  · exact norm_logDeriv_horiz hCw hCl hκ hW hL hZ χ hχ hT' hg _ (by simpa using h1) (by simpa using h2)
      (by simp [abs_of_nonneg hT0])
  · exact norm_logDeriv_horiz hCw hCl hκ hW hL hZ χ hχ hT' hg _ (by simpa using h1) (by simpa using h2)
      (by simp [abs_of_nonneg hT0])

end PI.EF
end
end

section

namespace PI.EF

open Complex

theorem rectResidue : RectResidue := by
  intro x₀ x₁ y₀ y₁ H Z wt e u hu h1 h2 h3 h4 hH hZ
  exact Rect.rect_residue (z := ⟨x₀, y₀⟩) (w := ⟨x₁, y₁⟩) Z wt e hu
    ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩ hH
    (fun ρ hρ => ⟨(hZ ρ hρ).1, (hZ ρ hρ).2⟩)

end PI.EF
end
