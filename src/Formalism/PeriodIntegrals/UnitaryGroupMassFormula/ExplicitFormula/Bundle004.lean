module

public import Formalism.PeriodIntegrals.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.EF

open Complex DirichletCharacter

variable {N : ℕ} [NeZero N]

theorem L_right (hB : PI.LBoundRight) {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 8) :
    ‖LFunction χ w‖ ≤ 37 * ((N : ℝ) * (|w.im| + 2)) := by
  have hre : 0 < w.re := by linarith
  have hb := hB N χ hχ1 w hre
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ht := abs_nonneg w.im
  have hw : ‖w‖ ≤ 8 + |w.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_pos hre]
    linarith
  have hq : ‖w‖ / w.re ≤ 2 * (8 + |w.im|) := by
    rw [div_le_iff₀ hre]
    nlinarith [norm_nonneg w]
  calc ‖LFunction χ w‖ ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + ‖w‖ / w.re) := hb
    _ ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + 2 * (8 + |w.im|)) := by gcongr
    _ ≤ 37 * ((N : ℝ) * (|w.im| + 2)) := by nlinarith

theorem L_nontriv_growth (hB : PI.LBoundRight) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {s : ℂ} (h1 : -4 ≤ s.re) (h2 : s.re ≤ 8) :
    ‖LFunction χ s‖ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ht := abs_nonneg s.im
  have hX : (1 : ℝ) ≤ (N : ℝ) * (|s.im| + 2) := one_le_mul_of_one_le_of_one_le hN (by linarith)
  by_cases hr : 1 / 2 ≤ s.re
  · calc ‖LFunction χ s‖ ≤ 37 * ((N : ℝ) * (|s.im| + 2)) := L_right hB hχ1 hr h2
      _ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
        have : (N : ℝ) * (|s.im| + 2) ≤ ((N : ℝ) * (|s.im| + 2)) ^ 7 := le_self_pow₀ hX (by norm_num)
        nlinarith
  · push_neg at hr
    have h0 : χ 0 = 0 := by
      by_cases hN1 : N = 1
      · subst hN1
        exfalso
        apply hχ1
        exact MulChar.ext fun a => by rw [Subsingleton.elim a 1]; simp
      · haveI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 hN1
        exact χ.map_nonunit not_isUnit_zero
    have hw1 : 1 / 2 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hw2 : (1 - s).re ≤ 5 := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hL1 := norm_L_one_sub_le hχ hw1 hw2 (Or.inl h0)
    rw [sub_sub_cancel] at hL1
    have hinv : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ1
    have hL2 := L_right hB hinv hw1 (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    have hwim : |(1 - s).im| = |s.im| := by simp
    rw [hwim] at hL2
    have hw1_le : ‖1 - s + 1‖ ≤ 6 + |s.im| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e : |(1 - s + 1).im| = |s.im| := by simp
      have e2 : (1 - s + 1).re = (1 - s).re + 1 := by simp
      rw [e, e2, abs_of_pos (by linarith)]
      linarith
    calc ‖LFunction χ s‖ ≤ 6 * (N : ℝ) ^ 5 * ‖1 - s + 1‖ ^ 5 * ‖LFunction χ⁻¹ (1 - s)‖ := hL1
      _ ≤ 6 * (N : ℝ) ^ 5 * (6 + |s.im|) ^ 5 * (37 * ((N : ℝ) * (|s.im| + 2))) := by gcongr
      _ ≤ 6 * (N : ℝ) ^ 5 * (3 * (|s.im| + 2)) ^ 5 * (37 * ((N : ℝ) * (|s.im| + 2))) := by
          gcongr
          linarith
      _ = 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 6 := by ring
      _ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (by norm_num)) (by norm_num)

theorem lGrowth_of (hB : PI.LBoundRight) {C : ℝ} (hZ : ZetaGrowth C) :
    LGrowth 7 (max C 53946) := by
  intro N _ χ hχ s h1 h2
  have e7 : ∀ x : ℝ, x ^ (7 : ℝ) = x ^ (7 : ℕ) := fun x => by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e7]
  by_cases hc : χ = 1
  · subst hc
    have hN : N = 1 := by
      have h0 := hχ
      rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at h0
      exact h0.symm
    subst hN
    simp only [del1, ↓reduceIte, one_mul]
    rw [show (1 : ℂ) + (s - 2) = s - 1 by ring, DirichletCharacter.LFunction_modOne_eq]
    refine le_trans (hZ s h1 h2) ?_
    simp only [Nat.cast_one, one_mul]
    gcongr
    exact le_max_left _ _
  · simp only [del1, hc, ↓reduceIte, zero_mul, add_zero, one_mul]
    calc ‖LFunction χ s‖ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := L_nontriv_growth hB hχ hc h1 h2
      _ ≤ max C 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
          gcongr
          exact le_max_right _ _

end PI.EF
end
end

section

noncomputable section

namespace PI.EF

open Complex DirichletCharacter

theorem shiftBound_of {κ Cs Cr : ℝ} (hκ : 0 < κ) (hCs : 0 ≤ Cs) (hCr : 0 ≤ Cr) (hRP : RegularPart)
    (hCI : ContourIdentity) (hS : SidesBound κ Cs) (hR : RegAtZero Cr) :
    ShiftBound κ (Cs + Cr + 3) := by
  intro N _ χ hχ u T T' hT hTu hTT' hT'T hg
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hu2 : (2 : ℝ) ≤ u := hT.trans hTu
  have hT'2 : (2 : ℝ) ≤ T' := hT.trans hTT'
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogNT : 0 < Real.log (N * T') := Real.log_pos (by nlinarith)
  have hNO : NoOrdinate χ T' := by
    intro ρ h1 h2 h3 heq
    have h4 := hg ρ h1 h2 h3
    rw [heq, sub_self, abs_zero] at h4
    have h5 : 0 < 1 / (κ * Real.log (N * T')) := by positivity
    linarith
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hx1 : 1 < cLine u := by
    unfold cLine
    have := one_div_pos.mpr hlogu
    linarith
  obtain ⟨H, hH⟩ := hRP N χ hχ (cLine u) T' hx1 (by linarith) hNO
  have hCIe := hCI N χ hχ u T' H hu2 hT'2 hNO hH
  have hSe := hS N χ hχ u T T' hT hTu hTT' hT'T hg
  have hRe := hR N χ hχ (cLine u) T' H hx1 hT'2 hH
  set R := rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s))
    (-1 / 2) (cLine u) (-T') T' with hRdef
  set Z := ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ with hZ
  set c : ℂ := 2 * Real.pi * I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hcn : ‖c‖ = 2 * Real.pi := by
    rw [hc, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  have hA : vertInt χ u T' - del1 χ * u + zsum χ T' u =
      (R + c * vertInt χ u T') / c + (Z - H 0) - eps0 χ * (Real.log u : ℂ) - del1 χ := by
    rw [hCIe]
    field_simp
    ring
  rw [hA]
  have hE1 : ‖eps0 χ‖ ≤ 1 := by
    unfold eps0
    split_ifs <;> simp
  have hD1 : ‖del1 χ‖ ≤ 1 := by
    unfold del1
    split_ifs <;> simp
  have hS1 : 0 ≤ S1 χ := by
    unfold S1
    exact finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hNu : Real.log u ≤ Real.log (N * u) := Real.log_le_log (by positivity) (by nlinarith)
  have h2N : Real.log (2 * N) ≤ Real.log (N * u) := Real.log_le_log (by positivity) (by nlinarith)
  have hL : 1 ≤ u * Real.log (N * u * T) ^ 2 / T := by
    have h4 : (4 : ℝ) ≤ N * u * T := by
      calc (4 : ℝ) = 1 * 2 * 2 := by norm_num
        _ ≤ N * u * T := mul_le_mul (mul_le_mul hN1 hu2 (by norm_num) (by linarith)) hT (by norm_num)
          (by positivity)
    have hl4 : 1 ≤ Real.log (N * u * T) := by
      have h5 : Real.log 4 ≤ Real.log (N * u * T) := Real.log_le_log (by norm_num) h4
      have h6 : 1 < Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        linarith [Real.log_two_gt_d9]
      linarith
    have hsq : 1 ≤ Real.log (N * u * T) ^ 2 := by nlinarith
    rw [le_div_iff₀ hT0]
    nlinarith [mul_le_mul hTu hsq (by norm_num) (by linarith)]
  have hlogNu : 0 ≤ Real.log (N * u) := by linarith
  have hErr1 : 1 ≤ Err N u T := by unfold Err; linarith
  have hErr2 : Real.log u ≤ Err N u T := by unfold Err; linarith
  have hErr3 : Real.log (2 * N) ≤ Err N u T := by unfold Err; linarith
  have hmain : ‖(R + c * vertInt χ u T') / c‖ ≤ Cs * Err N u T := by
    rw [norm_div, hcn, div_le_iff₀ (by positivity)]
    calc ‖R + c * vertInt χ u T'‖ ≤ Cs * Err N u T := hSe
      _ ≤ Cs * Err N u T * (2 * Real.pi) :=
        le_mul_of_one_le_right (by positivity) (by linarith [Real.pi_gt_three])
  have heps : ‖eps0 χ * (Real.log u : ℂ)‖ ≤ Real.log u := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogu]
    exact mul_le_of_le_one_left hlogu.le hE1
  calc ‖(R + c * vertInt χ u T') / c + (Z - H 0) - eps0 χ * (Real.log u : ℂ) - del1 χ‖
      ≤ ‖(R + c * vertInt χ u T') / c‖ + ‖Z - H 0‖ + ‖eps0 χ * (Real.log u : ℂ)‖ + ‖del1 χ‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ Cs * Err N u T + (Cr * Real.log (2 * N) + S1 χ) + Real.log u + 1 := by
        gcongr
    _ ≤ (Cs + Cr + 3) * (Err N u T + S1 χ) := by
        nlinarith [mul_nonneg hCs hS1, mul_nonneg hCr hS1, mul_le_mul_of_nonneg_left hErr3 hCr]

end PI.EF
end
end

section

namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries

lemma one_lt_cLine {u : ℝ} (hu : 2 ≤ u) : 1 < cLine u := by
  have h := Real.log_pos (by linarith : (1:ℝ) < u)
  have h2 := one_div_pos.mpr h
  show 1 < 1 + 1 / Real.log u
  linarith

lemma kernel_le_kb (hK : PerronKernel) (y c T : ℝ) (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronK y c T - (if 1 ≤ y then 1 else 0)‖ ≤ y ^ c * kb T y := by
  obtain ⟨h1, h2⟩ := hK y c T hy hc hT
  by_cases h : T * |Real.log y| ≤ 1
  · rw [kb, if_pos h]
    linarith
  · rw [kb, if_neg h]
    push_neg at h
    rw [mul_one_div, le_div_iff₀ (by linarith)]
    linarith

lemma term_mul_kernel (a : ℕ → ℂ) (u : ℝ) (hu : 0 < u) (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    term a s n * ((u : ℂ) ^ s / s) = a n * (((u / n : ℝ) : ℂ) ^ s / s) := by
  rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hu.le (Nat.cast_nonneg n)]
  push_cast
  ring

theorem perronTrunc_of {C : ℝ} (hK : PerronKernel) (hS : PerronSumBound C) : PerronTrunc C := by
  intro a ha u T hu hT
  have hc1 : 1 < cLine u := one_lt_cLine hu
  set c := cLine u with hcdef
  have hc0 : 0 < c := by linarith
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hSs, hSle⟩ := hS u T hu hT
  have ha0 : a 0 = 0 := by
    have h := ha 0
    rw [ArithmeticFunction.map_zero] at h
    exact norm_le_zero_iff.mp h

  have hΛsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc1)
    refine Complex.summable_ofReal.mp (h.congr (fun n => ?_))
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _)]
      push_cast
      rfl
  have hterm : ∀ (n : ℕ) (s : ℂ), s.re = c →
      ‖LSeries.term a s n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c := by
    intro n s hs
    rw [LSeries.norm_term_eq, hs]
    split_ifs with hn
    · subst hn
      simp
    · exact div_le_div_of_nonneg_right (ha n) (by positivity)
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := by intro t; simp
  have hkern : ∀ t : ℝ, ‖(u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)‖ ≤ u ^ c / c := by
    intro t
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0, hre]
    apply div_le_div_of_nonneg_left (by positivity) hc0
    have h := Complex.abs_re_le_norm ((c : ℂ) + t * I)
    rw [hre, abs_of_pos hc0] at h
    exact h

  have hDC := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := -T) (b := T)
    (F := fun (n : ℕ) (t : ℝ) => LSeries.term a ((c : ℂ) + t * I) n *
      ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (f := fun t : ℝ => LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (fun n _ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c * (u ^ c / c))
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero, zero_mul]
        exact MeasureTheory.aestronglyMeasurable_const
      · simp only [LSeries.term_of_ne_zero hn]
        apply Measurable.aestronglyMeasurable
        fun_prop)
    (fun n => Filter.Eventually.of_forall (fun t _ => by
      rw [norm_mul]
      exact mul_le_mul (hterm n _ (hre t)) (hkern t) (norm_nonneg _)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))))
    (Filter.Eventually.of_forall (fun t _ => hΛsum.mul_right _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ => by
      have hsum : LSeriesSummable a ((c : ℂ) + t * I) :=
        Summable.of_norm_bounded hΛsum (fun n => hterm n _ (hre t))
      exact hsum.hasSum.mul_right _))

  have hG : HasSum (fun n : ℕ => a n * perronK (u / n) c T)
      ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T)..T, LSeries a ((c : ℂ) + t * I) *
        ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) := by
    have hfun : (fun n : ℕ => a n * perronK (u / n) c T) = fun n : ℕ => (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n *
          ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
      funext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [ha0, LSeries.term_zero]
      · have h1 : (∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n *
              ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) =
            a n * ∫ t : ℝ in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          funext t
          exact term_mul_kernel a u hu0 n hn _
        rw [h1, perronK]
        ring
    rw [hfun]
    exact hDC.mul_left _

  have hind : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n) := by
    have h : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
        (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) := by
      apply hasSum_sum_of_ne_finset_zero
      intro n hn
      rw [Finset.mem_Icc, not_and_or] at hn
      rcases hn with hn | hn
      · have hn0 : n = 0 := by omega
        subst hn0
        simp [ha0]
      · push_neg at hn
        have hlt : u < n := by
          have h1 := Nat.lt_floor_add_one u
          have h2 : (⌊u⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
          linarith
        have h3 : ¬ (1 ≤ u / n) := by
          rw [not_le, div_lt_one (by linarith)]
          exact hlt
        simp [h3]
    convert h using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnu : (n : ℝ) ≤ u := le_trans (by exact_mod_cast hn.2) (Nat.floor_le hu0.le)
    have h4 : 1 ≤ u / n := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    simp [h4]
  have hdiff := hind.sub hG
  rw [← hdiff.tsum_eq]
  calc _ ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (u / n) ^ c * kb T (u / n) := by
        apply tsum_of_norm_bounded hSs.hasSum
        intro n
        rw [← mul_sub, norm_mul]
        rcases eq_or_ne n 0 with rfl | hn
        · simp [ha0]
        · have hy : 0 < u / n := div_pos hu0 (by exact_mod_cast Nat.pos_of_ne_zero hn)
          have h1 := kernel_le_kb hK (u / n) c T hy hc0 hT0
          rw [norm_sub_rev] at h1
          rw [mul_assoc]
          exact mul_le_mul (ha n) h1 (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := hSle

end PI.EF.PK
end

section

noncomputable section

namespace PI.EF

open Complex

theorem fractionFieldToGenericStalk_algebraMap_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u : ℝ) :
    psi0 χ u = psiRaw χ u - del1 χ * u := by
  unfold psi0 psiRaw del1
  split_ifs <;> simp

theorem first_character_sum_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : 0 ≤ S1 χ := by
  unfold S1
  exact finsum_nonneg (fun ρ => finsum_nonneg (fun _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))

theorem explicitFormula_of_perron_shift (κ : ℝ) (h1 : ∃ C, 0 < C ∧ PerronL C)
    (h2 : ∃ C, 0 < C ∧ ShiftBound κ C) (h3 : GoodHeightExists κ)
    (h4 : ∃ C, 0 < C ∧ TruncChange C) (h5 : ZerosFinite) : PI.ExplicitFormula := by
  obtain ⟨C1, hC1, H1⟩ := h1
  obtain ⟨C2, hC2, H2⟩ := h2
  obtain ⟨C4, hC4, H4⟩ := h4
  refine ⟨C1 + C2 + C4, by positivity, ?_⟩
  intro N _ χ hχ u T hT hTu
  refine ⟨h5 N χ hχ T, ?_⟩
  obtain ⟨T', hT1, hT2, hg⟩ := h3 N χ hχ T hT
  have e1 := H1 N χ u T T' hT hTu hT1 hT2
  have e2 := H2 N χ hχ u T T' hT hTu hT1 hT2 hg
  have e4 := H4 N χ hχ u T T' hT hTu hT1 hT2
  have hS : 0 ≤ S1 χ := first_character_sum_nonneg χ
  have key : psi0 χ u + zsum χ T u = (psiRaw χ u - vertInt χ u T') +
      (vertInt χ u T' - del1 χ * u + zsum χ T' u) - (zsum χ T' u - zsum χ T u) := by
    rw [fractionFieldToGenericStalk_algebraMap_eq]; ring
  show ‖psi0 χ u + zsum χ T u‖ ≤ (C1 + C2 + C4) * (Err N u T + S1 χ)
  rw [key]
  calc ‖(psiRaw χ u - vertInt χ u T') + (vertInt χ u T' - del1 χ * u + zsum χ T' u) -
        (zsum χ T' u - zsum χ T u)‖
      ≤ ‖psiRaw χ u - vertInt χ u T'‖ + ‖vertInt χ u T' - del1 χ * u + zsum χ T' u‖ +
        ‖zsum χ T' u - zsum χ T u‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ C1 * Err N u T + C2 * (Err N u T + S1 χ) + C4 * Err N u T := by gcongr
    _ ≤ (C1 + C2 + C4) * (Err N u T + S1 χ) := by
        nlinarith [mul_nonneg hC1.le hS, mul_nonneg hC4.le hS]

def GlueLocalLemma : Prop :=
  LocalAbstract → (∃ A C, 0 < A ∧ 0 < C ∧ LGrowth A C) → ZeroLocus → PI.ZerosWindow →
    ∃ C, 0 < C ∧ LocalLemma C

def GlueContour : Prop := RectResidue → ZeroLocus → ZerosFinite → ContourIdentity

def GlueSides : Prop :=
  ∀ κ, 0 < κ → (∃ C, 0 < C ∧ LogDerivHoriz κ C) → (∃ C, 0 < C ∧ LogDerivLeft C) →
    ∃ C, 0 < C ∧ SidesBound κ C

end PI.EF
end
end
