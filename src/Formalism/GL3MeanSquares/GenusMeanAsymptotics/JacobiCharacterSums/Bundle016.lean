module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle013
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle005
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle002

@[expose] public section

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

lemma dhPos_iter_logMul (f : ℕ → ℂ) (k n : ℕ) :
    (logMul^[k] f) n = (Complex.log n) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih]
    ring

lemma dhPos_abscissa {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv (↗ψ * ↗Λ) < s.re := by
  have h : abscissaOfAbsConv (↗ψ * ↗Λ) ≤ ((1 : ℝ) : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt ψ (by simp only [Complex.ofReal_re]; exact_mod_cast hy)
  exact lt_of_le_of_lt h (by exact_mod_cast hs)

lemma dhPos_iter {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    (-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s = LSeries (logMul^[k] (↗ψ * ↗Λ)) s := by
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hEq : ∀ z : ℂ, 1 < z.re → negLD ψ z = LSeries (↗ψ * ↗Λ) z := by
    intro z hz
    have hev : DirichletCharacter.LFunction ψ =ᶠ[nhds z] LSeries (fun n => ψ n) := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact DirichletCharacter.LFunction_eq_LSeries ψ hw
    unfold negLD
    rw [hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries ψ hz,
      DirichletCharacter.LSeries_twist_vonMangoldt_eq ψ hz]
    ring
  have heq : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact hEq z hz
  rw [heq.iteratedDeriv_eq, LSeries_iteratedDeriv k (dhPos_abscissa ψ hs), ← mul_assoc, ← mul_pow]
  norm_num

lemma dhPos_hasSum {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun n ↦ (term (logMul^[k] (↗ψ * ↗Λ)) s n).re)
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s).re := by
  rw [dhPos_iter ψ k hs]
  have habs : abscissaOfAbsConv (logMul^[k] (↗ψ * ↗Λ)) < s.re := by
    have e : ∀ j : ℕ, abscissaOfAbsConv (logMul^[j] (↗ψ * ↗Λ)) = abscissaOfAbsConv (↗ψ * ↗Λ) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]
    rw [e]
    exact dhPos_abscissa ψ hs
  have hs2 := (LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).LSeriesHasSum
  exact Complex.reCLM.hasSum hs2

lemma dhPos_term {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) (σ u : ℝ) (n : ℕ) :
    term (logMul^[k] (↗ψ * ↗Λ)) ((σ : ℂ) + u * I) n =
      (((Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) : ℝ) : ℂ) * (ψ n / (n : ℂ) ^ ((u : ℂ) * I)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg n)]
      simp
    have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    have hpos : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'
    have hu : (n : ℂ) ^ ((u : ℂ) * I) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn')
    rw [LSeries.term_of_ne_zero hn, dhPos_iter_logMul, Complex.cpow_add _ _ hn', hpow, hlog]
    simp only [Pi.mul_apply]
    push_cast
    field_simp

lemma dhPos_term_real {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) (σ : ℝ) (n : ℕ) :
    term (logMul^[k] (↗ψ * ↗Λ)) (σ : ℂ) n =
      (((Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) : ℝ) : ℂ) * ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg n)]
      simp
    have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    have hpos : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'
    rw [LSeries.term_of_ne_zero hn, dhPos_iter_logMul, hpow, hlog]
    simp only [Pi.mul_apply]
    push_cast
    field_simp

lemma dhPos_term_nonneg {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (h1 : χ₁ ^ 2 = 1)
    (k : ℕ) (σ γ : ℝ) (n : ℕ) :
    0 ≤ (term (logMul^[k] (↗(1 : DirichletCharacter ℂ q) * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ₁ * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ * ↗Λ)) ((σ : ℂ) + γ * I) n).re
      + (term (logMul^[k] (↗(χ * χ₁) * ↗Λ)) ((σ : ℂ) + γ * I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [dhPos_term_real, dhPos_term_real, dhPos_term, dhPos_term]
  simp only [Complex.re_ofReal_mul]
  have hA0 : 0 ≤ (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) :=
    mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
  have hz1 : ‖(n : ℂ) ^ ((γ : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    simp
  have hw : -1 ≤ (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re := by
    have hnorm : ‖χ n / (n : ℂ) ^ ((γ : ℂ) * I)‖ ≤ 1 := by
      rw [norm_div, hz1, div_one]
      exact DirichletCharacter.norm_le_one χ _
    have h2 := Complex.abs_re_le_norm (χ n / (n : ℂ) ^ ((γ : ℂ) * I))
    linarith [(abs_le.1 h2).1]
  have key : 0 ≤ ((1 : DirichletCharacter ℂ q) n).re + (χ₁ n).re + (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re +
      ((χ * χ₁) n / (n : ℂ) ^ ((γ : ℂ) * I)).re := by
    by_cases hu : IsUnit (n : ZMod q)
    · have h1n : (1 : DirichletCharacter ℂ q) n = 1 := MulChar.one_apply hu
      have hsq : χ₁ n * χ₁ n = 1 := by
        have e := congrArg (fun ψ : DirichletCharacter ℂ q => ψ n) h1
        simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply hu] using e
      have hχ₁ : χ₁ n = 1 ∨ χ₁ n = -1 := by
        have h' : (χ₁ n - 1) * (χ₁ n + 1) = 0 := by linear_combination hsq
        rcases mul_eq_zero.1 h' with h | h
        · left
          linear_combination h
        · right
          linear_combination h
      rw [MulChar.mul_apply, h1n]
      rcases hχ₁ with h | h
      · rw [h, mul_one]
        simp only [Complex.one_re]
        linarith
      · rw [h]
        simp only [Complex.one_re, Complex.neg_re, mul_neg, mul_one, neg_div]
        linarith
    · have h0 : ∀ ψ : DirichletCharacter ℂ q, ψ n = 0 := fun ψ => MulChar.map_nonunit ψ hu
      simp [h0]
  nlinarith [mul_nonneg hA0 key]

theorem deuring_heilbronn_positivity : DHPos := by
  intro M _ χ₁ χ γ σ k h1 hσ
  have hs1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + γ * I).re := by simpa using hσ
  have H1 := dhPos_hasSum (1 : DirichletCharacter ℂ M) k hs1
  have H2 := dhPos_hasSum χ₁ k hs1
  have H3 := dhPos_hasSum χ k hs2
  have H4 := dhPos_hasSum (χ * χ₁) k hs2
  have Hall := ((H1.add H2).add H3).add H4
  rw [mul_add, mul_add, mul_add, Complex.add_re, Complex.add_re, Complex.add_re]
  exact Hall.nonneg (fun n => dhPos_term_nonneg χ₁ χ h1 k σ γ n)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhl_prod_le (M : ℕ) [NeZero M] (s : ℂ) (hs : 0 ≤ s.re) :
    ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ M := by
  rw [norm_prod]
  have h1 : ∀ p ∈ M.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
    have hn : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp'.pos]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      simpa using hs
    calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ ≤ p := by rw [norm_one]; linarith
  calc ∏ p ∈ M.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ ≤ ∏ p ∈ M.primeFactors, (p : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) h1
    _ = ((∏ p ∈ M.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ M := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos M) (Nat.prod_primeFactors_dvd M)

lemma dhl_triv_growth (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.LFunctionTrivChar₁ M s‖ ≤ 4 * M * (1 + ‖s‖) ^ 2 := by
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
  have hs0 := norm_nonneg s
  by_cases h1 : s = 1
  · subst h1
    have := dhl_prod_le M 1 (by simp)
    simp only [Function.update_self]
    have e : ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) = ∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ))) := by
      refine Finset.prod_congr rfl (fun p _ => ?_)
      rw [cpow_neg_one]
    rw [e]
    refine this.trans ?_
    rw [norm_one]
    nlinarith
  · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne h1,
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta h1, norm_mul, norm_mul]
    have hP := dhl_prod_le M s (by linarith)
    have hz := Formalism.ZF.growthBound s (by linarith) h1
    have hpos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
    have hle : ‖s - 1‖ ≤ 1 + ‖s‖ := by
      have := norm_sub_le s 1; rw [norm_one] at this; linarith
    have hb : 1 / s.re ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hz2 : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 4 * (1 + ‖s‖) ^ 2 := by
      calc ‖s - 1‖ * ‖riemannZeta s‖
          ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) := by gcongr
        _ = ‖s - 1‖ + 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by field_simp
        _ ≤ (1 + ‖s‖) + 1 + (1 + ‖s‖) * (‖s‖ * (1 + 2)) := by gcongr
        _ ≤ 4 * (1 + ‖s‖) ^ 2 := by nlinarith
    calc ‖s - 1‖ * (‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * ‖riemannZeta s‖)
        = ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * (‖s - 1‖ * ‖riemannZeta s‖) := by ring
      _ ≤ M * (4 * (1 + ‖s‖) ^ 2) := by gcongr
      _ = 4 * M * (1 + ‖s‖) ^ 2 := by ring

lemma dhl_pole (k : ℕ) (s : ℂ) (hs : s ≠ 1) :
    (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z : ℂ => 1 / (z - 1)) s
      = 1 / (s - 1) ^ (k + 1) := by
  have h := congrFun (iter_deriv_inv_linear_sub k (1 : ℂ) 1) s
  have e : (fun z : ℂ => 1 / (z - 1)) = fun x : ℂ => (1 * x - 1)⁻¹ := by
    funext z; simp
  rw [iteratedDeriv_eq_iterate, e, h]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have e2 : (1 * s - 1) ^ (-1 - (k : ℤ)) = ((s - 1) ^ (k + 1))⁻¹ := by
    rw [one_mul, show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [e2, one_pow]
  have h1 : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow]; simp
  field_simp
  linear_combination h1

lemma dhl_log (K X : ℝ) (hK : 1 ≤ K) (hX : 3 ≤ X) :
    Real.log (K * X ^ 2) ≤ (Real.log K + 2) * Real.log X := by
  have hl : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hk : 0 ≤ Real.log K := Real.log_nonneg hK
  rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
  push_cast
  nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
