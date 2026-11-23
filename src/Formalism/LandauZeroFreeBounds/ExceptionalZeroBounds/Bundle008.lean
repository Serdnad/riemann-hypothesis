module

public import Formalism.LandauZeroFreeBounds.Bundle001
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle001
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle003
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormCpowSubLePoint
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RiemannZetaOneEqOneSubOfRePos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle002

@[expose] public section

section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma euler_factor_logDeriv_bound (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1 < s.re) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 ∧ DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ∧
    ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hw : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hx : (p : ℝ) ^ (-s.re) ≤ 1 / 2 := by
    have h1 : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hx0 : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (by linarith) _
  have hden : 1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one, hw] at this
    linarith
  have hne : (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    linarith
  have hder : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
      ((p : ℂ) ^ (-s) * Complex.log p) s := by
    have h1 : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
      (hasDerivAt_id s).neg.const_cpow (Or.inl hp0)
    have h2 := (hasDerivAt_const s (1 : ℂ)).sub h1
    exact h2.congr_deriv (by ring)
  refine ⟨hne, hder.differentiableAt, ?_⟩
  have hL : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := Complex.natCast_log.symm
  rw [logDeriv_apply, hder.deriv, norm_div, norm_mul, hw, hlog, Complex.norm_of_nonneg hL]
  have hdpos : 0 < ‖1 - (p : ℂ) ^ (-s)‖ := by linarith
  rw [div_le_iff₀ hdpos]
  have hxd : (p : ℝ) ^ (-s.re) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hxd hL]

lemma re_negLogDeriv_le (q : ℕ) [NeZero q] (s : ℂ) (hs : 1 < s.re) :
    (negLD (1 : DirichletCharacter ℂ q) s).re ≤
      (-(deriv riemannZeta s / riemannZeta s)).re + Real.log q := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hfac : ∀ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) ≠ 0 ∧
      DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ∧
      ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p :=
    fun p hp => euler_factor_logDeriv_bound p (Nat.prime_of_mem_primeFactors hp) s hs
  have heq : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
      fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q)
      (Set.mem_compl_singleton_iff.mp hz)
  have hPne : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (hfac p hp).1
  have hPd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s :=
    DifferentiableAt.fun_finsetProd fun p hp => (hfac p hp).2.1
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hmul : logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s =
      logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s +
        logDeriv riemannZeta s :=
    logDeriv_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z)))
      (g := riemannZeta) s hPne hζ hPd hζd
  have hprod : logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s =
      ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    by
      have hfun : (∏ p ∈ q.primeFactors, fun z : ℂ => 1 - (p : ℂ) ^ (-z)) =
          fun z => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z)) := by
        funext z
        exact Finset.prod_apply (s := q.primeFactors)
          (g := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) (a := z)
      rw [← hfun]
      exact logDeriv_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z))
        (fun p hp => (hfac p hp).1) (fun p hp => (hfac p hp).2.1)
  have hneg : negLD (1 : DirichletCharacter ℂ q) s =
      -(logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s) := rfl
  have hS : ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤
      Real.log q := by
    calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
        ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, Real.log p := Finset.sum_le_sum fun p hp => (hfac p hp).2.2
      _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      _ ≤ Real.log q := by
          apply Real.log_le_log
          · exact Finset.prod_pos fun p hp => by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
          · rw [← Nat.cast_prod]
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
              (Nat.prod_primeFactors_dvd q)
  have hre := RCLike.abs_re_le_norm
    (∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s)
  have hre' := neg_abs_le
    (∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s).re
  rw [hneg, (logDeriv_congr_nhds heq).eq_of_nhds, hmul, hprod, logDeriv_apply]
  simp only [Complex.neg_re, Complex.add_re]
  simp only [RCLike.re_to_complex] at hre
  linarith

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex Finset

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma character_sum_range_modulus_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  have hbij : Function.Bijective (fun i : Fin q => ((i : ℕ) : ZMod q)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => Fin.ext ?_, by simp [ZMod.card]⟩
    have h1 := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h1
  rw [Finset.sum_range, Fintype.sum_bijective _ hbij (fun i => χ ((i : ℕ) : ZMod q)) χ (fun _ => rfl)]
  exact MulChar.sum_eq_zero_of_ne_one hχ

lemma character_sum_range_add_modulus {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ range (q + M), χ (n : ZMod q) = ∑ n ∈ range M, χ (n : ZMod q) := by
  rw [Finset.sum_range_add, character_sum_range_modulus_eq_zero χ hχ, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Nat.cast_add, ZMod.natCast_self, zero_add]

lemma norm_character_sum_range_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤ q := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    by_cases hM : M < q
    · calc ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤ ∑ n ∈ range M, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ range M, (1 : ℝ) := Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ _
        _ = M := by simp
        _ ≤ q := by exact_mod_cast hM.le
    · obtain ⟨M', rfl⟩ : ∃ M', M = q + M' := ⟨M - q, by omega⟩
      rw [character_sum_range_add_modulus χ hχ M']
      exact ih M' (by have := NeZero.pos q; omega)

lemma norm_character_sum_Icc_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ Icc 1 M, χ (n : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have h1 : ∑ n ∈ range (M + 1), χ (n : ZMod q) =
      χ ((0 : ℕ) : ZMod q) + ∑ n ∈ Icc 1 M, χ (n : ZMod q) := by
    have hI : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos M), zero_add, hI]
  have h2 : ∑ n ∈ Icc 1 M, χ (n : ZMod q) =
      ∑ n ∈ range (M + 1), χ (n : ZMod q) - χ ((0 : ℕ) : ZMod q) := by
    rw [h1]; ring
  rw [h2]
  calc _ ≤ ‖∑ n ∈ range (M + 1), χ (n : ZMod q)‖ + ‖χ ((0 : ℕ) : ZMod q)‖ := norm_sub_le _ _
    _ ≤ q + 1 := add_le_add (norm_character_sum_range_le χ hχ _) (DirichletCharacter.norm_le_one χ _)

theorem lfunction_polynomial_growth : LGrowth := by
  refine ⟨9, ?_⟩
  intro q _ χ hχ s hs
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hσ : 0 < s.re := by linarith
  have hB := norm_character_sum_Icc_le χ hχ
  have hP := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1) hB s hσ 1 le_rfl
  simp only [Nat.cast_one, Real.one_rpow, mul_one, Finset.Icc_self, Finset.sum_singleton] at hP
  have h1 : ‖χ (1 : ZMod q) * (1 : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [one_cpow, mul_one]; exact DirichletCharacter.norm_le_one χ _
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hdiv : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    rw [div_le_iff₀ hσ]; nlinarith
  have hL : ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re) := by
    have := norm_le_insert' (DirichletCharacter.LFunction χ s) (χ (1 : ZMod q) * (1 : ℂ) ^ (-s))
    linarith
  calc ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re) := hL
    _ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + 2 * ‖s‖) := by gcongr
    _ ≤ 9 * q * (1 + ‖s‖) := by nlinarith

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex
open scoped ComplexOrder Nat

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma norm_le_of_log_bound {z : ℂ} {CL : ℝ} (q : ℕ) [NeZero q] (h : ‖z‖ ≤ CL * Real.log (3 * q)) :
    ‖z‖ ≤ |CL| * (3 * q) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h3 : (0 : ℝ) ≤ 3 * q := by positivity
  have hl0 : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
  have hl : Real.log (3 * q) ≤ 3 * q := Real.log_le_self h3
  calc ‖z‖ ≤ CL * Real.log (3 * q) := h
    _ ≤ |CL| * Real.log (3 * q) := mul_le_mul_of_nonneg_right (le_abs_self CL) hl0
    _ ≤ |CL| * (3 * q) := mul_le_mul_of_nonneg_left hl (abs_nonneg CL)

lemma exists_taylor_truncation_order (T : ℝ) (hT : 1 ≤ T) :
    ∃ M : ℕ, 1 ≤ M ∧ T * (3 / 4 : ℝ) ^ M ≤ 1 ∧ (M : ℝ) ≤ Real.log T / Real.log (4 / 3) + 2 := by
  have hl43 : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hT0 : 0 < T := by linarith
  have hx0 : 0 ≤ Real.log T / Real.log (4 / 3) := div_nonneg (Real.log_nonneg hT) hl43.le
  refine ⟨⌈Real.log T / Real.log (4 / 3)⌉₊ + 1, by omega, ?_, ?_⟩
  · have hM : Real.log T / Real.log (4 / 3) ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (Real.log T / Real.log (4 / 3))]
    have hlog : Real.log T ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) * Real.log (4 / 3) := by
      have h := mul_le_mul_of_nonneg_right hM hl43.le
      rwa [div_mul_cancel₀ _ hl43.ne'] at h
    have hT' : T ≤ (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by
      calc T = Real.exp (Real.log T) := (Real.exp_log hT0).symm
        _ ≤ Real.exp (((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) * Real.log (4 / 3)) :=
          Real.exp_le_exp.mpr hlog
        _ = (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by
          rw [← Real.log_pow, Real.exp_log (by positivity)]
    have h34 : (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hp : 0 < (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by positivity
    calc T * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1)
        ≤ (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) :=
          mul_le_mul_of_nonneg_right hT' hp.le
      _ = 1 := h34
  · push_cast
    linarith [Nat.ceil_lt_add_one hx0]

lemma two_sub_pow_le_exp {A P σ : ℝ} {M : ℕ} (hA : 0 ≤ A) (hσ1 : 7 / 8 ≤ σ) (hσ2 : σ < 1)
    (hM : (M : ℝ) ≤ A + P) : (2 - σ) ^ M ≤ Real.exp A * Real.exp (P * (1 - σ)) := by
  have h1 : 0 < 1 - σ := by linarith
  have hb : 2 - σ ≤ Real.exp (1 - σ) := by
    have := Real.add_one_le_exp (1 - σ); linarith
  have hb0 : 0 ≤ 2 - σ := by linarith
  calc (2 - σ) ^ M ≤ Real.exp (1 - σ) ^ M := pow_le_pow_left₀ hb0 hb M
    _ = Real.exp (M * (1 - σ)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (A + P * (1 - σ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hM h1.le, mul_nonneg hA (by linarith : (0 : ℝ) ≤ σ)]
    _ = Real.exp A * Real.exp (P * (1 - σ)) := Real.exp_add _ _

theorem product_lfunction_key_inequality : BqKeyOf := by
  intro hCoeff hEnt hGrow hL1
  obtain ⟨Cg, Kg, hg⟩ := hGrow
  obtain ⟨CL, hL⟩ := hL1
  obtain ⟨c0, hc0def⟩ : ∃ c : ℝ, c = |Cg| + 54 * |CL| ^ 3 + 1 := ⟨_, rfl⟩
  obtain ⟨K', hK'def⟩ : ∃ k : ℝ, k = max Kg 2 := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ l : ℝ, l = Real.log (4 / 3) := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Real.log_pos (by norm_num)
  have hc0 : 1 ≤ c0 := by
    rw [hc0def]; have := abs_nonneg Cg; have := pow_nonneg (abs_nonneg CL) 3; linarith
  have hKgK : Kg ≤ K' := by rw [hK'def]; exact le_max_left _ _
  have h2K : (2 : ℝ) ≤ K' := by rw [hK'def]; exact le_max_right _ _
  refine ⟨Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)), K' / ℓ,
    div_nonneg (by linarith) hℓ.le, ?_⟩
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 h1ne h2ne hψne hψ σ hσ1 hσ2
  have h1σ : 0 < 1 - σ := by linarith
  have hq₁ : (1 : ℝ) ≤ q₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hq₂ : (1 : ℝ) ≤ q₂ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
  have hN : ((q₁ * q₂ : ℕ) : ℝ) = (q₁ : ℝ) * q₂ := by push_cast; ring
  have hN1 : (1 : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by rw [hN]; nlinarith
  obtain ⟨a, ha0, ha1, habs, hFa⟩ := hCoeff q₁ q₂ χ₁ χ₂ ψ h1 h2 hψ
  obtain ⟨G, hG, hFG⟩ := hEnt q₁ q₂ χ₁ χ₂ ψ h1ne h2ne hψne
  have hlam : ‖lamBq χ₁ χ₂ ψ‖ ≤ 27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2 := by
    have e1 := norm_le_of_log_bound q₁ (hL q₁ χ₁ h1ne)
    have e2 := norm_le_of_log_bound q₂ (hL q₂ χ₂ h2ne)
    have e3 := norm_le_of_log_bound (q₁ * q₂) (hL (q₁ * q₂) ψ hψne)
    simp only [lamBq, norm_mul]
    calc _ ≤ (|CL| * (3 * q₁)) * (|CL| * (3 * q₂)) * (|CL| * (3 * ((q₁ * q₂ : ℕ) : ℝ))) :=
          mul_le_mul (mul_le_mul e1 e2 (norm_nonneg _) (by positivity)) e3 (norm_nonneg _) (by positivity)
      _ = 27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2 := by rw [hN]; ring
  have hKg : ((q₁ * q₂ : ℕ) : ℝ) ^ Kg ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' :=
    Real.rpow_le_rpow_of_exponent_le hN1 hKgK
  have hK2 : ((q₁ * q₂ : ℕ) : ℝ) ^ (2 : ℕ) ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num; linarith)
  have hNK0 : 0 ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by positivity
  have hB : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
    intro s hs
    rw [mem_sphere_iff_norm] at hs
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
    have hd : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
      have h := norm_sub_le (s - 1) (1 : ℂ)
      have e : s - 1 - 1 = s - 2 := by ring
      rw [e, hs, norm_one] at h
      linarith
    have hGs : G s = Fbq χ₁ χ₂ ψ s - lamBq χ₁ χ₂ ψ / (s - 1) := by rw [hFG s hs1]; ring
    have hF := hg q₁ q₂ χ₁ χ₂ ψ h1ne h2ne hψne s hs
    have hdiv : ‖lamBq χ₁ χ₂ ψ / (s - 1)‖ ≤ 2 * ‖lamBq χ₁ χ₂ ψ‖ := by
      rw [norm_div, div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (lamBq χ₁ χ₂ ψ)]
    have hc3 : 0 ≤ 54 * |CL| ^ 3 := by positivity
    calc ‖G s‖ ≤ ‖Fbq χ₁ χ₂ ψ s‖ + ‖lamBq χ₁ χ₂ ψ / (s - 1)‖ := by rw [hGs]; exact norm_sub_le _ _
      _ ≤ Cg * ((q₁ * q₂ : ℕ) : ℝ) ^ Kg + 2 * (27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2) := by linarith
      _ ≤ c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
        rw [hc0def]
        nlinarith [mul_le_mul_of_nonneg_right (le_abs_self Cg) (by positivity : (0 : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ Kg),
          mul_le_mul_of_nonneg_left hKg (abs_nonneg Cg), mul_le_mul_of_nonneg_left hK2 hc3]
  have hNK1 : 1 ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := Real.one_le_rpow hN1 (by linarith)
  have hT : 1 ≤ 8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K') := by
    nlinarith [mul_le_mul hc0 hNK1 zero_le_one (by linarith)]
  obtain ⟨M, hM1, hTM, hMle⟩ := exists_taylor_truncation_order _ hT
  rw [← hℓdef] at hMle
  have hcore := lseries_taylor_lower_bound ha0 ha1 habs hG hFa hFG hB hσ1 hσ2 hM1
  have hpow := two_sub_pow_le_exp (A := 2) (P := Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) / ℓ)
    (M := M) (by norm_num) hσ1 hσ2 (by linarith)
  have hlogT : Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) =
      Real.log (8 * c0) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) := by
    rw [← mul_assoc, Real.log_mul (by positivity) (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_rpow (by linarith)]
  have hlogc : 0 ≤ Real.log (8 * c0) := Real.log_nonneg (by linarith)
  have hexp : Real.exp (Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) / ℓ * (1 - σ)) ≤
      Real.exp (Real.log (8 * c0) / (8 * ℓ)) * ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) := by
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < ((q₁ * q₂ : ℕ) : ℝ) by linarith) (K' / ℓ * (1 - σ)),
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hlogT]
    have eL : (Real.log (8 * c0) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ)) / ℓ * (1 - σ) =
        (Real.log (8 * c0) * (1 - σ) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) * (1 - σ)) / ℓ := by ring
    have eR : Real.log (8 * c0) / (8 * ℓ) + Real.log ((q₁ * q₂ : ℕ) : ℝ) * (K' / ℓ * (1 - σ)) =
        (Real.log (8 * c0) / 8 + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) * (1 - σ)) / ℓ := by ring
    rw [eL, eR]
    apply div_le_div_of_nonneg_right _ hℓ.le
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 - σ ≤ 1 / 8) hlogc]
  have hpow' : (2 - σ) ^ M ≤ Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)) *
      ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) :=
    hpow.trans ((mul_le_mul_of_nonneg_left hexp (Real.exp_pos 2).le).trans_eq (by ring))
  have h34 : 4 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K') * (3 / 4 : ℝ) ^ M ≤ 1 / 2 := by linarith
  have hlam0 := norm_nonneg (lamBq χ₁ χ₂ ψ)
  have hdiv : ‖lamBq χ₁ χ₂ ψ‖ * (2 - σ) ^ M / (1 - σ) ≤
      Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)) * ‖lamBq χ₁ χ₂ ψ‖ *
        ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) / (1 - σ) := by
    apply div_le_div_of_nonneg_right _ h1σ.le
    nlinarith [mul_le_mul_of_nonneg_left hpow' hlam0]
  linarith

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma exponential_integral_nonneg_real {σ a : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) :
    ∃ r : ℝ, 0 ≤ r ∧ Formalism.ZF.ComplexPowerDifferenceIntegral.eint (σ : ℂ) a = (r : ℂ) := by
  refine ⟨∫ x in a..(a + 1), (x ^ (-σ) - (a + 1) ^ (-σ)), ?_, ?_⟩
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1 := Real.rpow_le_rpow_of_nonpos hx0 hx.2 (by linarith : -σ ≤ 0)
    linarith
  · unfold Formalism.ZF.ComplexPowerDifferenceIntegral.eint
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx0 : 0 ≤ x := le_trans ha.le hx.1
    simp only [Complex.ofReal_sub]
    rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ a + 1)]
    push_cast
    ring

theorem zeta_negative_real_axis : ZetaNegReal := by
  intro σ hσ0 hσ1
  have hre : 0 < (σ : ℂ).re := by simpa using hσ0
  have hz1 := Formalism.ZF.ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos hre
  have hne : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne' : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hζ := riemannZeta_eq_inv_sub_mul hne
  choose r hr0 hr using fun n : ℕ =>
    exponential_integral_nonneg_real (σ := σ) (a := (n : ℝ) + 1) hσ0.le (by positivity)
  have hdz : ∀ n : ℕ, Formalism.ZF.ComplexPowerDifferenceIntegral.dz (σ : ℂ) n = ((σ : ℂ) - 1) * ((r n : ℝ) : ℂ) := by
    intro n
    rw [← hr n]
    exact Formalism.ZF.ComplexPowerDifferenceIntegral.d_eq (by positivity) _
  have hsum : Summable r := by
    have hs := Formalism.ZF.ComplexPowerDifferenceIntegral.summable_norm_dz hre
    have hs' : Summable (fun n => ‖((σ : ℂ) - 1)‖⁻¹ * ‖Formalism.ZF.ComplexPowerDifferenceIntegral.dz (σ : ℂ) n‖) := hs.mul_left _
    refine hs'.congr (fun n => ?_)
    rw [hdz n, norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne'), one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 n)]
  have hDz : Formalism.ZF.ComplexPowerDifferenceIntegral.Dz (σ : ℂ) = ((σ : ℂ) - 1) * ((∑' n, r n : ℝ) : ℂ) := by
    unfold Formalism.ZF.ComplexPowerDifferenceIntegral.Dz
    simp_rw [hdz]
    rw [tsum_mul_left, Complex.ofReal_tsum]
  set R := ∑' n, r n with hRdef
  have hR0 : 0 ≤ R := tsum_nonneg hr0
  have hval : riemannZeta (σ : ℂ) = ((σ / (σ - 1) - R : ℝ) : ℂ) := by
    rw [hζ, hz1, hDz]
    have hσ1' : (σ - 1 : ℝ) ≠ 0 := by intro h; linarith
    push_cast
    field_simp
  rw [hval, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  have : σ / (σ - 1) < 0 := div_neg_of_pos_of_neg hσ0 (by linarith)
  linarith

end Formalism.ZeroFreeDirichlet
end
end
