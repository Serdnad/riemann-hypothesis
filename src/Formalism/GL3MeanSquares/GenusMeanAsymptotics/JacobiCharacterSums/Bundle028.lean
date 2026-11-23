module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle026
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHFinish
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle024
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle025
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiC
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

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

lemma dhDom_hasSum {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun n ↦ term (logMul^[k] (↗ψ * ↗Λ)) s n)
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s) := by
  have habs : abscissaOfAbsConv (↗ψ * ↗Λ) < s.re := by
    refine lt_of_le_of_lt (abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) ?_) ?_
    · intro y hy
      exact LSeriesSummable_twist_vonMangoldt ψ hy
    · exact_mod_cast hs
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hU : LFunction ψ =ᶠ[nhds z] LSeries (↗ψ) := by
      filter_upwards [hopen.mem_nhds hz'] with w hw
      exact DirichletCharacter.LFunction_eq_LSeries ψ hw
    simp only [negLD]
    rw [Filter.EventuallyEq.deriv_eq hU, DirichletCharacter.LFunction_eq_LSeries ψ hz',
      LSeries_twist_vonMangoldt_eq ψ hz', neg_div]
  have hit : iteratedDeriv k (negLD ψ) s = iteratedDeriv k (LSeries (↗ψ * ↗Λ)) s := by
    simp only [← iteratedDerivWithin_univ]
    refine Filter.EventuallyEq.iteratedDerivWithin_eq ?_ hev.eq_of_nhds
    simpa [nhdsWithin_univ] using hev
  rw [hit, LSeries_iteratedDeriv k habs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (by simpa using habs)).LSeriesHasSum

private theorem logMul_iterate_apply_eq_log_pow_mul (f : ℕ → ℂ) (k n : ℕ) :
    logMul^[k] f n = Complex.log n ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', logMul, ih]
    ring

lemma dhDom_term_le {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (h1 : χ₁ ^ 2 = 1)
    (k : ℕ) (σ γ : ℝ) (n : ℕ) :
    ‖term (logMul^[k] (↗χ * ↗Λ)) ((σ : ℂ) + γ * I) n
      + term (logMul^[k] (↗(χ * χ₁) * ↗Λ)) ((σ : ℂ) + γ * I) n‖ ≤
    (term (logMul^[k] (↗(1 : DirichletCharacter ℂ q) * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ₁ * ↗Λ)) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set A : ℝ := Real.log n ^ k * Λ n with hA
  have hA0 : 0 ≤ A :=
    mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k) ArithmeticFunction.vonMangoldt_nonneg
  have e1 : ∀ c : ℂ, Complex.log n ^ k * (c * ((Λ n : ℝ) : ℂ)) = (A : ℂ) * c := by
    intro c
    rw [hA, ← Complex.natCast_log]
    push_cast
    ring
  have hN : ‖(n : ℂ) ^ ((σ : ℂ) + γ * I)‖ = (n : ℝ) ^ σ := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hR : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnpos.le]
  have hp : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
  have hre : ∀ c : ℝ, ((A : ℂ) * (c : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)).re = A * c / (n : ℝ) ^ σ := by
    intro c
    rw [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [term_of_ne_zero hn, logMul_iterate_apply_eq_log_pow_mul, Pi.mul_apply, MulChar.coeToFun_mul, e1, hR]
  by_cases hu : IsUnit (n : ZMod q)
  · obtain ⟨u, hu'⟩ := hu
    rw [← hu', MulChar.one_apply_coe]
    have hχ : ‖χ u‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
    have h1u : χ₁ u * χ₁ u = 1 := by
      rw [← pow_two, ← MulChar.pow_apply_coe, h1, MulChar.one_apply_coe]
    rcases mul_self_eq_one_iff.mp h1u with h | h
    · rw [h]
      have := hre 1
      push_cast at this
      rw [this]
      have e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * 1) /
          (n : ℂ) ^ ((σ : ℂ) + γ * I) = ((2 * A : ℝ) : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) := by
        push_cast
        ring
      rw [e2, norm_div, norm_mul, hχ, hN, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      apply le_of_eq
      ring
    · rw [h]
      have := hre 1
      have h' := hre (-1)
      push_cast at this h'
      rw [this, h']
      have e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * -1) /
          (n : ℂ) ^ ((σ : ℂ) + γ * I) = 0 := by
        ring
      rw [e2, norm_zero]
      apply le_of_eq
      ring
  · simp [MulChar.map_nonunit _ hu]

theorem deuring_heilbronn_dominant : DHDom := by
  intro M _ χ₁ χ γ σ k h1 hσ
  have hs : 1 < ((σ : ℂ) + γ * I).re := by simpa using hσ
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hA := dhDom_hasSum χ k hs
  have hB := dhDom_hasSum (χ * χ₁) k hs
  have hC := dhDom_hasSum (1 : DirichletCharacter ℂ M) k hs0
  have hD := dhDom_hasSum χ₁ k hs0
  have hbound := HasSum.norm_le_of_bounded (hA.add hB) (Complex.hasSum_re (hC.add hD))
    (fun n ↦ by
      rw [Complex.add_re]
      exact dhDom_term_le χ₁ χ h1 k σ γ n)
  have e1 : ‖iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
      + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ =
      ‖(-1 : ℂ) ^ k * iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
        + (-1 : ℂ) ^ k * iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ := by
    rw [← mul_add, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [e1, mul_add]
  exact hbound

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet


theorem deuring_heilbronn_finish_turan : DHFinish2Of := by
  intro hTur hIneq hPrime
  obtain ⟨CT, a, hCT, ha, hT2⟩ := hTur
  obtain ⟨CF, hCF, hF⟩ := hIneq
  obtain ⟨CP, hCP, hP⟩ := hPrime
  obtain ⟨cS, hcS, hE⟩ := excBound (1 / 2) (by norm_num)
  obtain ⟨cZ, hcZ, hG⟩ := DHF.region_gap
  have hD0 : 0 ≤ Real.log (max CT 1) := Real.log_nonneg (le_max_right _ _)
  obtain ⟨c₁, hc₁pos, hc₁Z, hc₁20⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ cZ / 4 ∧ c ≤ 1 / 20 :=
    ⟨min (cZ / 4) (1 / 20), lt_min (by linarith) (by norm_num), min_le_left _ _, min_le_right _ _⟩
  have hrr : 16 < TuranPowerSumBounds.rr a := TuranPowerSumBounds.rr_gt a
  obtain ⟨c₂, hc₂pos, hc₂k, hc₂t, hc₂K⟩ : ∃ c : ℝ, 0 < c ∧
      c ≤ TuranPowerSumBounds.kap a (Real.log (max CT 1)) / (25 * CF) ∧
      c ≤ TuranPowerSumBounds.th a / (2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a) ∧
      c * (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) ≤ cZ := by
    have hk := div_pos (TuranPowerSumBounds.kap_pos a ha _ hD0) (by positivity : (0 : ℝ) < 25 * CF)
    have ht := div_pos (TuranPowerSumBounds.th_pos a) (by positivity : (0 : ℝ) < 2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a)
    have hq : (0 : ℝ) < 2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) := by positivity
    refine ⟨min (min (TuranPowerSumBounds.kap a (Real.log (max CT 1)) / (25 * CF))
      (TuranPowerSumBounds.th a / (2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a)))
      (cZ / (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1))),
      lt_min (lt_min hk ht) (div_pos hcZ hq),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _), ?_⟩
    rw [← le_div_iff₀ hq]
    exact min_le_right _ _
  have hc0pos : 0 < TuranPowerSumBounds.c0 a := by
    have := TuranPowerSumBounds.twentyFive_mul_smallConstant a
    have : 0 < 1 / TuranPowerSumBounds.rr a := by positivity
    linarith
  have hc0 : TuranPowerSumBounds.c0 a ≤ 1 / 25 := by
    have := TuranPowerSumBounds.twentyFive_mul_smallConstant a
    have h1 : 1 / TuranPowerSumBounds.rr a ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  refine ⟨TuranPowerSumBounds.c0 a, c₁, c₂, 3, hc0pos, hc₁pos, hc₂pos, ?_⟩
  intro M _ χ₁ χ β₁ T ρ hM hT hsq hne1 hL hβ hβ1 hρ hre hIm hne
  have hL1 : 1 ≤ Real.log ((M : ℝ) * T) := DHF.logMT_ge_one M T hM hT
  have hLpos : 0 < Real.log ((M : ℝ) * T) := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hgap := hG M χ₁ χ β₁ T c₁ ρ hM hT hne1 hL hc₁pos (by linarith) hβ hρ hIm hne
  have hη : 0 < 1 - ρ.re := by
    by_contra h
    push_neg at h
    nlinarith
  have hηZ : cZ / (2 * Real.log ((M : ℝ) * T)) ≤ 1 - ρ.re := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hηc0 : 1 - ρ.re ≤ TuranPowerSumBounds.c0 a := by linarith
  have hlam : 0 < 1 - β₁ := by linarith
  have hEx := hE M χ₁ β₁ hsq hne1 hL
  have hs : 0 < √(M : ℝ) := Real.sqrt_pos.mpr hMpos
  have hmm : √(M : ℝ) * √(M : ℝ) = M := Real.mul_self_sqrt hMpos.le
  have hsqrt : (M : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / √(M : ℝ) := by
    rw [Real.rpow_neg hMpos.le, ← Real.sqrt_eq_rpow, one_div]
  have hcs : cS ≤ (1 - β₁) * √(M : ℝ) := by
    rw [hsqrt] at hEx
    have h1 : cS * (1 / √(M : ℝ)) ≤ 1 - β₁ := by linarith
    rw [mul_one_div, div_le_iff₀ hs] at h1
    exact h1
  have hℓ0 : 0 ≤ Real.log (3 * (M : ℝ)) := Real.log_nonneg (by linarith)
  have hℓpos : 0 < Real.log (3 * (M : ℝ)) := Real.log_pos (by linarith)
  have hℓL : Real.log (3 * (M : ℝ)) ≤ 2 * Real.log ((M : ℝ) * T) := by
    have hT4 : (4 : ℝ) ≤ T ^ 2 := by nlinarith
    have h3 : 3 * (M : ℝ) ≤ ((M : ℝ) * T) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hT4 (sq_nonneg (M : ℝ))]
    calc Real.log (3 * (M : ℝ)) ≤ Real.log (((M : ℝ) * T) ^ 2) :=
          Real.log_le_log (by linarith) h3
      _ = 2 * Real.log ((M : ℝ) * T) := by
          rw [Real.log_pow]
          push_cast
          ring
  have hℓM : Real.log (3 * (M : ℝ)) ^ 2 / (M : ℝ) ≤ 32 * (1 - β₁) / cS := by
    rw [div_le_div_iff₀ hMpos hcS]
    have hls := TuranPowerSumBounds.log_sq_bound (M : ℝ) (by linarith)
    calc Real.log (3 * (M : ℝ)) ^ 2 * cS ≤ 32 * √(M : ℝ) * cS :=
          mul_le_mul_of_nonneg_right hls hcS.le
      _ ≤ 32 * √(M : ℝ) * ((1 - β₁) * √(M : ℝ)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = 32 * (1 - β₁) * (M : ℝ) := by linear_combination (32 * (1 - β₁)) * hmm
  rw [div_le_iff₀ hLpos]
  by_contra hcon
  push_neg at hcon
  have hKK0 : TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁ <
      Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)) := by
    by_contra h
    push_neg at h
    have h1 : c₂ * Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)) ≤
        c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self (TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁)])
        hc₂pos.le
    have h3 : c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) ≤ cZ / 2 := by
      have e : c₂ * (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) =
          2 * (c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) := by ring
      linarith
    linarith
  have hpos : 0 < c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3) := by positivity
  have hexp : (1 - β₁) * Real.log ((M : ℝ) * T) ^ 3 =
      c₁ * Real.exp (-Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3))) := by
    rw [Real.exp_neg, Real.exp_log hpos]
    field_simp
  have hρre : (22 / 25 : ℝ) ≤ ρ.re := by linarith
  have hβ20 : (19 / 20 : ℝ) ≤ β₁ := by
    have : c₁ / Real.log ((M : ℝ) * T) ≤ 1 / 20 := by
      rw [div_le_iff₀ hLpos]
      nlinarith
    linarith
  obtain ⟨N, w, hwre, hwex, hwsum, hwj⟩ := hF M χ₁ χ β₁ T (1 - ρ.re) ρ hM hT hsq hne1 hL hβ20 hβ1
    hρ hρre hIm hne hη (by linarith)
  have hβP : 1 - 1 / Real.log (3 * (M : ℝ)) ≤ β₁ := by
    have : c₁ / Real.log ((M : ℝ) * T) ≤ 1 / Real.log (3 * (M : ℝ)) := by
      rw [div_le_div_iff₀ hLpos hℓpos]
      nlinarith
    linarith
  refine TuranPowerSumBounds.core2 CT a hCT ha hT2 CF CP cZ cS c₁ c₂ hCF hCP hcZ hcS hc₁pos hc₁Z hc₂pos hc₂k hc₂t
    (Real.log ((M : ℝ) * T)) (Real.log (3 * (M : ℝ))) (1 - β₁) (1 - ρ.re) (M : ℝ)
    (Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)))
    hL1 hℓ0 hℓL hlam hηZ hηc0 hcon hMpos hℓM hexp hKK0 N w hwre hwex hwsum ?_
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 := hwj (i + 1) hj
  have h2 := hP M χ₁ β₁ (1 + (1 - ρ.re)) i hM hsq hne1 hL hβP hβ1 (by linarith) (by linarith)
  simp only [Nat.add_sub_cancel] at h1 ⊢
  have e1 : (1 + (1 - ρ.re)) - 1 = 1 - ρ.re := by ring
  rw [e1] at h2
  have hA : CP * (1 - β₁) * Real.log (3 * (M : ℝ)) ^ 2 * ((i : ℝ) + 2) ^ 2 / (1 - ρ.re) ^ (i + 2) =
      CP * (1 - β₁) * Real.log (3 * (M : ℝ)) ^ 2 * (((i + 1 : ℕ) : ℝ) + 1) ^ 2 /
        (1 - ρ.re) ^ (i + 1 + 1) := by
    push_cast
    ring_nf
  have hC : CP * ((i : ℝ) + 2) * Real.log (3 * (M : ℝ)) ^ 2 / ((M : ℝ) * (1 - ρ.re) ^ (i + 1)) =
      CP * (((i + 1 : ℕ) : ℝ) + 1) * Real.log (3 * (M : ℝ)) ^ 2 / ((M : ℝ) * (1 - ρ.re) ^ (i + 1)) := by
    push_cast
    ring_nf
  rw [hA, hC] at h2
  exact h1.trans (add_le_add (add_le_add h2 le_rfl) le_rfl)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem turan_power_sum_bound : DHTuran2 := by
  refine ⟨1600, 1, by norm_num, le_rfl, fun n m z hn hz hz1 => ?_⟩
  obtain ⟨k, h1, h2, h3⟩ := T2.turan2Main n m z hn hz hz1
  exact ⟨k, h1, by simpa using h2, by simpa using h3⟩

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem prime_count_of_psi : PiOf := by
  rintro ⟨c, A, C₀, hc, hP⟩
  obtain ⟨c₁, hc₁, hηl⟩ := etaOf_lower 1 one_pos
  refine ⟨min (c / 2) (c ^ 2 / 2), 10 * |A| + 5632 * Real.exp (2 * min (c / 2) (c ^ 2 / 2)) / c₁,
    max (2 * C₀) 16, lt_min (by positivity) (by positivity), ?_⟩
  intro M _ h8
  refine ⟨eOf M, fun p hp => eOf_exc M p hp, fun h χ₁ β₁ => eOf_none M h χ₁ β₁, ?_⟩
  intro X b hX2 hrange hb
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM8n : 8 ≤ M := Nat.le_of_dvd hMpos h8
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast hM8n
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl : 2 ≤ Real.log M := by
    have h88 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hM8
    linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hll : 1 ≤ Real.log (Real.log M + 2) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ Real.log M + 2)
    linarith
  have hprod : Real.log M ≤ Real.log M * Real.log (Real.log M + 2) := by nlinarith
  have hprod0 : 0 ≤ Real.log M * Real.log (Real.log M + 2) := by linarith
  have hrange' : max (2 * C₀) 16 * (Real.log M * Real.log (Real.log M + 2)) ≤ Real.log X := by
    rw [← mul_assoc]; exact hrange
  have hL16 : 16 * Real.log M ≤ Real.log X := by
    have := mul_le_mul_of_nonneg_right (le_max_right (2 * C₀) 16) hprod0
    linarith
  have hLC : C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X / 2 := by
    have := mul_le_mul_of_nonneg_right (le_max_left (2 * C₀) 16) hprod0
    have e : C₀ * Real.log M * Real.log (Real.log M + 2) =
        2 * C₀ * (Real.log M * Real.log (Real.log M + 2)) / 2 := by ring
    rw [e]
    linarith
  have hX0 : 0 < X := by linarith
  have hX4 : 4 ≤ X := by
    rw [← Real.log_le_log_iff (by norm_num) hX0]
    linarith
  have hs2 : 2 ≤ √X := by
    rw [Real.le_sqrt' (by norm_num)]; linarith
  have hη0 : 0 ≤ etaOf M := (etaOf_pos M (by omega)).le
  have hη1 := etaOf_le_one M
  have hηl' := hηl M (by omega)
  have hP' : ∀ y : ℝ, √X ≤ y → y ≤ X →
      ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      |A| * y * etaOf M *
        (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y)))) := by
    intro y h1 h2
    have hy2 : 2 ≤ y := hs2.trans h1
    have hly : Real.log X / 2 ≤ Real.log y := by
      rw [← Real.log_sqrt hX0.le]
      exact Real.log_le_log (by linarith) h1
    refine (hP M h8 y hy2 (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)) hη0) (by positivity)
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [he] at hP'
    have e0 : mainAP (none : Option (DirichletCharacter ℂ M × ℝ)) b X =
        (liX X - 0 * liX (X ^ (1 : ℝ))) / (M.totient : ℝ) := by simp [mainAP]
    rw [e0]
    exact pi_core M h8 b hb none (by simp) (by norm_num) le_rfl
      (fun t _ => mainPsi_sum_none M b hb t 1) hη0 hη1 (Or.inl le_rfl) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'
  · rw [he] at hP'
    obtain ⟨_, _, _, hβlo, hβ1⟩ := eOf_exc M _ he
    have hχ := eOf_char_sq M χ₁ β₁ he b ((ZMod.isUnit_iff_coprime b M).mpr hb)
    have hθ : |(χ₁ (b : ZMod M)).re| ≤ 1 := by rcases hχ with h | h <;> simp [h]
    have hβ : 1 / 2 ≤ β₁ := by
      have : 1 / (8 * Real.log M) ≤ 1 / 16 := by
        apply one_div_le_one_div_of_le (by norm_num); linarith
      simp only [] at hβlo
      linarith
    have hηe := etaOf_some M χ₁ β₁ he
    have e1 : mainAP (some (χ₁, β₁)) b X =
        (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ) := rfl
    rw [e1]
    exact pi_core M h8 b hb (some (χ₁, β₁)) hθ hβ hβ1.le
      (fun t ht => mainPsi_sum_some M b hb χ₁ β₁ t ht hχ) hη0 hη1
      (Or.inr (by rw [hηe]; exact min_le_right _ _)) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
