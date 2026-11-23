module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle001
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle002
public import Formalism.LFunctionBounds.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Field.Basic

@[expose] public section

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

private theorem norm_inv_pow_sub_inv_pow_le (a b : ℂ) (η δ : ℝ) (hη : 0 < η) (ha : η ≤ ‖a‖) (hb : η ≤ ‖b‖)
    (hab : ‖b - a‖ ≤ δ) (n : ℕ) : ‖1 / a ^ n - 1 / b ^ n‖ ≤ n * δ / η ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, norm_zero] at ha
      linarith
    have hb0 : b ≠ 0 := by
      intro h
      rw [h, norm_zero] at hb
      linarith
    have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hab
    have key : 1 / a ^ (n + 1) - 1 / b ^ (n + 1) =
        (1 / a) * (1 / a ^ n - 1 / b ^ n) + (1 / b ^ n) * ((b - a) / (a * b)) := by
      field_simp
      ring
    rw [key]
    have h1 : ‖1 / a‖ ≤ 1 / η := by
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hη ha
    have h2 : ‖1 / b ^ n‖ ≤ 1 / η ^ n := by
      rw [norm_div, norm_one, norm_pow]
      exact one_div_le_one_div_of_le (pow_pos hη n) (pow_le_pow_left₀ hη.le hb n)
    have h3 : ‖(b - a) / (a * b)‖ ≤ δ / (η * η) := by
      rw [norm_div, norm_mul]
      exact div_le_div₀ hδ hab (mul_pos hη hη) (mul_le_mul ha hb hη.le (norm_nonneg _))
    calc _ ≤ ‖1 / a‖ * ‖1 / a ^ n - 1 / b ^ n‖ + ‖1 / b ^ n‖ * ‖(b - a) / (a * b)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 / η * (n * δ / η ^ (n + 1)) + 1 / η ^ n * (δ / (η * η)) := by gcongr
      _ = _ := by
        push_cast
        field_simp
        ring

theorem dhfShiftPoleN (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : β₁ < 1) (k : ℕ) (c : Prop) [Decidable c]
    (hc : ¬ c → 1 / 8 ≤ |γ|) (s : ℂ) (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) :
    ‖1 / (s - 1) ^ (k + 1) - (if c then 1 / (s - β₁) ^ (k + 1) else 0)‖ ≤
      ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
  have hre1 : (s - 1).re = η := by
    rw [hs]
    simp
  have hre2 : (s - (β₁ : ℂ)).re = 1 + η - β₁ := by
    rw [hs]
    simp
  have him : (s - 1).im = γ := by
    rw [hs]
    simp
  have hsa : η ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [hre1, abs_of_pos hη] at this
    exact this
  have hsb : η ≤ ‖s - (β₁ : ℂ)‖ := by
    have := Complex.re_le_norm (s - (β₁ : ℂ))
    rw [hre2] at this
    linarith
  have hd : ‖(s - (β₁ : ℂ)) - (s - 1)‖ ≤ 1 - β₁ := by
    have e : (s - (β₁ : ℂ)) - (s - 1) = ((1 - β₁ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have h8 : (0 : ℝ) ≤ 8 ^ (k + 1) := by positivity
  have hpos : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
    apply div_nonneg
    · apply mul_nonneg
      · positivity
      · linarith
    · positivity
  split_ifs with h
  · have := norm_inv_pow_sub_inv_pow_le (s - 1) (s - β₁) η (1 - β₁) hη hsa hsb hd (k + 1)
    push_cast at this
    linarith
  · have hγ : 1 / 8 ≤ |γ| := hc h
    have hs1 : 1 / 8 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [him] at this
      linarith
    rw [sub_zero, norm_div, norm_one, norm_pow]
    have hb : 1 / ‖s - 1‖ ^ (k + 1) ≤ 8 ^ (k + 1) := by
      rw [div_le_iff₀ (by positivity)]
      calc (1 : ℝ) = 8 ^ (k + 1) * (1 / 8) ^ (k + 1) := by
            rw [← mul_pow]
            norm_num
        _ ≤ 8 ^ (k + 1) * ‖s - 1‖ ^ (k + 1) := by gcongr
    linarith

private theorem one_eighth_le_abs_of_not_mem_pole_disc (γ β₁ : ℝ) (hβ1 : 19 / 20 ≤ β₁) (hβ2 : β₁ < 1)
    (h : ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25) : 1 / 8 ≤ |γ| := by
  by_contra hlt
  push_neg at hlt
  apply h
  have hg : γ ^ 2 < 1 / 64 := by
    have := abs_lt.mp hlt
    nlinarith
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith

theorem dhfPoles {M : ℕ} (χ₁ χ : DirichletCharacter ℂ M) (hχ₁2 : χ₁ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1)
    (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : 19 / 20 ≤ β₁) (hβ2 : β₁ < 1) (k : ℕ) (s : ℂ)
    (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) [Decidable (χ = 1)] [Decidable (χ * χ₁ = 1)]
    (c3 c4 : Prop) [Decidable c3] [Decidable c4]
    (h3 : χ = χ₁ → ¬ c3 → ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25)
    (h4 : χ = 1 → ¬ c4 → ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25)
    (h3' : c3 → χ = χ₁) (h4' : c4 → χ = 1) :
    ‖(if χ = 1 then 1 / (s - 1) ^ (k + 1) else 0) + (if χ * χ₁ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
      - (if c3 then 1 / (s - β₁) ^ (k + 1) else 0) - (if c4 then 1 / (s - β₁) ^ (k + 1) else 0)‖
      ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
  have hpos : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
    have : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
      apply div_nonneg
      · apply mul_nonneg
        · positivity
        · linarith
      · positivity
    exact add_nonneg this (by positivity)
  by_cases h1 : χ = 1
  · have h2 : ¬ (χ * χ₁ = 1) := by
      rw [h1, one_mul]
      exact hχ₁1
    have h3n : ¬ c3 := fun h => hχ₁1 ((h3' h).symm.trans h1)
    simp only [if_pos h1, if_neg h2, if_neg h3n, add_zero, sub_zero]
    exact dhfShiftPoleN η γ β₁ hη hβ2 k c4 (fun h => one_eighth_le_abs_of_not_mem_pole_disc γ β₁ hβ1 hβ2 (h4 h1 h)) s hs
  · by_cases h2 : χ * χ₁ = 1
    · have hχ : χ = χ₁ := by
        have e : χ = χ * χ₁ * χ₁ := by rw [mul_assoc, ← sq, hχ₁2, mul_one]
        rw [e, h2, one_mul]
      have h4n : ¬ c4 := fun h => h1 (h4' h)
      simp only [if_neg h1, if_pos h2, if_neg h4n, zero_add, sub_zero]
      exact dhfShiftPoleN η γ β₁ hη hβ2 k c3 (fun h => one_eighth_le_abs_of_not_mem_pole_disc γ β₁ hβ1 hβ2 (h3 hχ h)) s hs
    · have h3n : ¬ c3 := fun h => h2 (by rw [h3' h, ← sq, hχ₁2])
      have h4n : ¬ c4 := fun h => h1 (h4' h)
      simp only [if_neg h1, if_neg h2, if_neg h3n, if_neg h4n, add_zero, sub_zero, norm_zero]
      exact hpos

theorem dhfReNonneg (S : Multiset ℂ) (h : ∀ x ∈ S, 0 < x.re) :
    0 ≤ ((S.map (fun x : ℂ => 1 / x)).sum).re := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_re]
    have ha := h a (Multiset.mem_cons_self a S)
    have h1 : 0 ≤ (1 / a).re := by
      rw [one_div, Complex.inv_re]
      exact div_nonneg ha.le (Complex.normSq_nonneg a)
    exact add_nonneg h1 (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

theorem dhfEraseSum (Z : Finset ℂ) (m : ℂ → ℕ) (s b : ℂ) (c : Prop) [Decidable c]
    (hb : c → b ∈ dhFam Z m s) (k : ℕ) :
    ((if c then (dhFam Z m s).erase b else dhFam Z m s).map (fun x : ℂ => 1 / x ^ (k + 1))).sum =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) - (if c then 1 / b ^ (k + 1) else 0) := by
  have key : ((dhFam Z m s).map (fun x : ℂ => 1 / x ^ (k + 1))).sum =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
    unfold dhFam
    rw [Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum]
    congr 1
    apply Multiset.map_congr rfl
    intro ρ _
    rw [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    ring
  split_ifs with h
  · rw [← key, ← Multiset.sum_map_erase (hb h)]
    ring
  · rw [key, sub_zero]

theorem dhfNormArith (D3 D4 P3 P4 S3 S4 I3 I4 A B : ℂ) (k : ℕ) (e3 e4 Dom X : ℝ)
    (h3 : ‖D3 - P3 + S3‖ ≤ e3) (h4 : ‖D4 - P4 + S4‖ ≤ e4)
    (hD3 : D3 = (-1 : ℂ) ^ k / (k.factorial : ℂ) * A) (hD4 : D4 = (-1 : ℂ) ^ k / (k.factorial : ℂ) * B)
    (hdom : ‖A + B‖ ≤ Dom) (hP : ‖P3 + P4 - I3 - I4‖ ≤ X) :
    ‖(S3 - I3) + (S4 - I4)‖ ≤ Dom / (k.factorial : ℝ) + X + e3 + e4 := by
  have hnf : ‖(-1 : ℂ) ^ k / (k.factorial : ℂ)‖ = 1 / (k.factorial : ℝ) := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hD : ‖D3 + D4‖ ≤ Dom / (k.factorial : ℝ) := by
    rw [hD3, hD4, ← mul_add, norm_mul, hnf, div_mul_eq_mul_div, one_mul]
    gcongr
  have e : (S3 - I3) + (S4 - I4) =
      ((D3 - P3 + S3) + (D4 - P4 + S4) - (D3 + D4)) + (P3 + P4 - I3 - I4) := by ring
  rw [e]
  have n1 := norm_add_le ((D3 - P3 + S3) + (D4 - P4 + S4) - (D3 + D4)) (P3 + P4 - I3 - I4)
  have n2 := norm_sub_le ((D3 - P3 + S3) + (D4 - P4 + S4)) (D3 + D4)
  have n3 := norm_add_le (D3 - P3 + S3) (D4 - P4 + S4)
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem dhReBound (A P S : ℂ) (E : ℝ) (h : ‖A - P + S‖ ≤ E) : S.re ≤ P.re - A.re + E := by
  have h1 : (A - P + S).re ≤ ‖A - P + S‖ := by
    first
      | exact Complex.re_le_norm _
      | exact Complex.re_le_abs _
  simp only [Complex.add_re, Complex.sub_re] at h1
  linarith

theorem logMulAbsAddTwoLeTwoMulLog (M : ℕ) (T t : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) (ht : |t| ≤ T) :
    Real.log ((M : ℝ) * (|t| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hta := abs_nonneg t
  have hpos : 0 < (M : ℝ) * (|t| + 2) := by positivity
  have h1 : (M : ℝ) * (|t| + 2) ≤ (M : ℝ) * (T + 2) := by nlinarith
  have h2 : (M : ℝ) * (T + 2) ≤ ((M : ℝ) * T) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (M : ℝ) - 3) (by linarith : (0 : ℝ) ≤ T - 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (M : ℝ)) (by linarith : (0 : ℝ) ≤ T - 2)]
  calc Real.log ((M : ℝ) * (|t| + 2)) ≤ Real.log (((M : ℝ) * T) ^ 2) :=
        Real.log_le_log hpos (h1.trans h2)
    _ = 2 * Real.log ((M : ℝ) * T) := by rw [Real.log_pow]; norm_num

theorem dhLogOne (M : ℕ) (T : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) : 1 ≤ Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : (6 : ℝ) ≤ M * T := by nlinarith
  have he := Real.exp_one_lt_d9
  have h1 : Real.exp 1 ≤ (M : ℝ) * T := by linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) h1

theorem dhPair (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : β₁ < 1) (k : ℕ) (s : ℂ)
    (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) :
    (1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)).re ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
  have hδ : 0 < 1 - β₁ := by linarith
  have hare : (s - 1).re = η := by rw [hs]; simp
  have hbre : (s - β₁).re = η + (1 - β₁) := by rw [hs]; simp; ring
  have hna : η ≤ ‖s - 1‖ := hare ▸ Complex.re_le_norm (s - 1)
  have hnb : η ≤ ‖s - β₁‖ := le_trans (by linarith) (hbre ▸ Complex.re_le_norm (s - β₁))
  have ha0 : s - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hna; linarith
  have hb0 : s - β₁ ≠ 0 := fun h => by rw [h, norm_zero] at hnb; linarith
  have hba : (s - β₁) - (s - 1) = ((1 - β₁ : ℝ) : ℂ) := by push_cast; ring
  have hid : 1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1) =
      ((s - β₁) - (s - 1)) * (∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)) /
        ((s - 1) ^ (k + 1) * (s - β₁) ^ (k + 1)) := by
    rw [mul_comm ((s - β₁) - (s - 1)), geom_sum₂_mul]
    field_simp
  have hsum : ‖∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ ≤
      ((k + 1 : ℕ) : ℝ) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2)) := by
    calc _ ≤ ∑ i ∈ Finset.range (k + 1), ‖(s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (k + 1), ‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [norm_mul, norm_pow, norm_pow, le_div_iff₀ (by positivity)]
          have e1 : η ^ (k + 2) = η ^ (i + 1) * η ^ (k + 1 - i) := by rw [← pow_add]; congr 1; omega
          have e2 : ‖s - 1‖ ^ (k + 1) = ‖s - 1‖ ^ (k + 1 - 1 - i) * ‖s - 1‖ ^ (i + 1) := by
            rw [← pow_add]; congr 1; omega
          have e3 : ‖s - β₁‖ ^ (k + 1) = ‖s - β₁‖ ^ i * ‖s - β₁‖ ^ (k + 1 - i) := by
            rw [← pow_add]; congr 1; omega
          rw [e1, e2, e3]
          have p1 : η ^ (i + 1) ≤ ‖s - 1‖ ^ (i + 1) := pow_le_pow_left₀ hη.le hna _
          have p2 : η ^ (k + 1 - i) ≤ ‖s - β₁‖ ^ (k + 1 - i) := pow_le_pow_left₀ hη.le hnb _
          have p12 := mul_le_mul p1 p2 (by positivity) (by positivity)
          calc ‖s - β₁‖ ^ i * ‖s - 1‖ ^ (k + 1 - 1 - i) * (η ^ (i + 1) * η ^ (k + 1 - i))
              ≤ ‖s - β₁‖ ^ i * ‖s - 1‖ ^ (k + 1 - 1 - i) * (‖s - 1‖ ^ (i + 1) * ‖s - β₁‖ ^ (k + 1 - i)) :=
                mul_le_mul_of_nonneg_left p12 (by positivity)
            _ = _ := by ring
      _ = ((k + 1 : ℕ) : ℝ) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfinal : ‖1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)‖ ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
    rw [hid, norm_div, norm_mul, hba, Complex.norm_real, Real.norm_of_nonneg hδ.le, norm_mul, norm_pow, norm_pow]
    have hpos : 0 < ‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) := by
      have := norm_pos_iff.mpr ha0
      have := norm_pos_iff.mpr hb0
      positivity
    rw [div_le_div_iff₀ hpos (by positivity)]
    have h3 := mul_le_mul_of_nonneg_left hsum hδ.le
    push_cast at h3
    calc (1 - β₁) * ‖∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ * η ^ (k + 2)
        ≤ (1 - β₁) * (((k : ℝ) + 1) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2))) * η ^ (k + 2) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ((k : ℝ) + 1) * (1 - β₁) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1)) := by
          field_simp
  have hre : (1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)).re ≤
      ‖1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)‖ := Complex.re_le_norm _
  exact hre.trans hfinal

theorem dhAssemble {β : Type*} [AddCommGroup β] (F1 F2 F3 F4 : Multiset ℂ) (b2 b3 b4 : ℂ)
    (c3 c4 : Prop) [Decidable c3] [Decidable c4] (h2 : b2 ∈ F2) (h3 : c3 → b3 ∈ F3) (h4 : c4 → b4 ∈ F4)
    (g : ℂ → β) :
    ((F1 + F2.erase b2 + (if c3 then F3.erase b3 else F3) + (if c4 then F4.erase b4 else F4)).map g).sum
      = (F1.map g).sum + (F2.map g).sum + (F3.map g).sum + (F4.map g).sum - g b2
        - (if c3 then g b3 else 0) - (if c4 then g b4 else 0) := by
  classical
  have e : ∀ (F : Multiset ℂ) (b : ℂ), b ∈ F → ((F.erase b).map g).sum = (F.map g).sum - g b := by
    intro F b hb
    rw [← Multiset.sum_map_erase hb]
    abel
  simp only [Multiset.map_add (f := _), Multiset.sum_add, e _ _ h2]
  by_cases hc3 : c3 <;> by_cases hc4 : c4
  · simp only [if_pos hc3, if_pos hc4, e _ _ (h3 hc3), e _ _ (h4 hc4)]
    abel
  · simp only [if_pos hc3, if_neg hc4, e _ _ (h3 hc3)]
    abel
  · simp only [if_neg hc3, if_pos hc4, e _ _ (h4 hc4)]
    abel
  · simp only [if_neg hc3, if_neg hc4]
    abel

theorem dhFam_re (Z : Finset ℂ) (m : ℂ → ℕ) (s x : ℂ) (η : ℝ) (hZ : ∀ ρ ∈ Z, ρ.re < 1)
    (hs : s.re = 1 + η) (hx : x ∈ dhFam Z m s) : η ≤ x.re := by
  unfold dhFam at hx
  rw [Multiset.mem_bind] at hx
  obtain ⟨ρ, hρ, hx⟩ := hx
  rw [Multiset.eq_of_mem_replicate hx, Complex.sub_re, hs]
  linarith [hZ ρ hρ]

theorem dhMemIte (F : Multiset ℂ) (c : Prop) [Decidable c] (b x : ℂ) (h : x ∈ (if c then F.erase b else F)) :
    x ∈ F := by
  split_ifs at h
  · exact Multiset.mem_of_mem_erase h
  · exact h

theorem dhFamPow (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) (k : ℕ) :
    ((dhFam Z m s).map (fun x => 1 / x ^ (k + 1))).sum = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
  unfold dhFam
  rw [Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun ρ _ => ?_
  simp [Multiset.map_replicate, Multiset.sum_replicate, div_eq_mul_inv]

theorem dhFinalArith (S1 S2 S3 S4 P1 P3 P4 A1 A2 A3 A4 E0 Eγ g2 I3 I4 X F G Hc H e8 : ℝ)
    (t1 : S1 + S2 + S3 + S4 ≤ P1 - A1 + E0 + (0 - A2 + E0) + (P3 - A3 + Eγ) + (P4 - A4 + Eγ))
    (hA : 0 ≤ A1 + A2 + A3 + A4) (hp : P1 - g2 ≤ X) (hs : P3 + P4 - I3 - I4 ≤ X + e8)
    (h0 : E0 ≤ F) (hγ : Eγ ≤ F) (t3 : F ≤ 2 * G) (t2 : e8 ≤ H) (nn : 0 ≤ Hc) :
    S1 + S2 + S3 + S4 - g2 - I3 - I4 ≤ 2 * X + (8 * G + 8 * Hc + H) := by
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

abbrev PC := Σ N : ℕ, DirichletCharacter ℂ (N + 1)

def cv (p : PC) (n : ℕ) : ℂ := p.2 (n : ZMod (p.1 + 1))

def s0 : ℝ := 1 - 1 / 400

def mco (Y N n : ℕ) : ℂ :=
  ∑ p ∈ (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n), (((μ p.1 : ℤ)) : ℂ)

def blk (Y N U : ℕ) (p : PC) (s : ℂ) : ℂ :=
  ∑ n ∈ Ioc U (2 * U), mco Y N n * cv p n * (n : ℂ) ^ (-s)

def DualIneq : Prop :=
  ∀ (ι κ : Type) (S : Finset ι) (I : Finset κ) (b : κ → ℂ) (v : ι → κ → ℂ) (Δ : ℝ), 0 ≤ Δ →
    (∀ i ∈ S, ∑ j ∈ S, ‖∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n)‖ ≤ Δ) →
    ∑ i ∈ S, ‖∑ n ∈ I, b n * v i n‖ ^ 2 ≤ (∑ n ∈ I, ‖b n‖ ^ 2) * Δ

def PairSum : Prop :=
  ∀ p p' : PC, p.2.IsPrimitive → p'.2.IsPrimitive → p ≠ p' → ∀ M : ℕ,
    ‖∑ n ∈ range M, cv p n * (starRingEnd ℂ) (cv p' n)‖ ≤ (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ)

def PairTwist : Prop :=
  ∀ p p' : PC, p.2.IsPrimitive → p'.2.IsPrimitive → p ≠ p' → ∀ w : ℂ, 0 < w.re → ∀ U : ℕ, 1 ≤ U →
    ‖∑ n ∈ Ioc U (2 * U), cv p n * (starRingEnd ℂ) (cv p' n) * (n : ℂ) ^ (-w)‖ ≤
      2 * (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ) * (1 + ‖w‖)

def MollId : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (Y N K : ℕ), 1 ≤ Y → Y ≤ N → Y * N ≤ K →
    (∑ n ∈ Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) *
        (∑ d ∈ Icc 1 Y, (((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)) =
      1 + ∑ n ∈ Ioc Y K, mco Y N n * χ (n : ZMod q) * (n : ℂ) ^ (-s)

def CoeffSq : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ Y N U : ℕ, 1 ≤ U →
    ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ))

def q0 (Q : ℝ) : ℕ := ⌈Q⌉₊
def pY (Q : ℝ) : ℕ := q0 Q ^ 4
def pJ (Q : ℝ) : ℕ := 8 * (Nat.log 2 (q0 Q) + 1)
def pN (Q : ℝ) : ℕ := 2 ^ pJ Q

def Detect : Prop :=
  ∀ (Q : ℝ), 20 ≤ Q → ∀ p : PC, p.2.IsPrimitive → p.1 ≠ 0 → ((p.1 + 1 : ℕ) : ℝ) ≤ Q →
    ∀ ρ : ℂ, s0 < ρ.re → |ρ.im| ≤ Q → DirichletCharacter.LFunction p.2 ρ = 0 →
      ∃ j ∈ range (pJ Q), 1 / (2 * (pJ Q : ℝ)) ≤ ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) p ρ‖

def BlockCount : Prop :=
  ∀ C : ℝ, 0 ≤ C → (∀ Y N U : ℕ, 1 ≤ U →
      ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ))) →
  ∀ (Q : ℝ), 3 ≤ Q → ∀ (Y N U J : ℕ), 1 ≤ U → 1 ≤ J →
    8 * Q ^ 3 * C * (U : ℝ) ^ (-(197 / 200 : ℝ)) ≤ 1 / (8 * (J : ℝ) ^ 2) →
    ∀ (T : Finset PC) (ρ : PC → ℂ),
      (∀ p ∈ T, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ s0 < (ρ p).re ∧ (ρ p).re < 1 ∧
        |(ρ p).im| ≤ Q ∧ 1 / (2 * (J : ℝ)) ≤ ‖blk Y N U p (ρ p)‖) →
      (T.card : ℝ) ≤ 8 * (J : ℝ) ^ 2 * C * (U : ℝ) ^ (3 / 200 : ℝ)

def Num : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ Q₀ C' : ℝ, 20 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
    (∀ j ∈ range (pJ Q), 8 * Q ^ 3 * C * ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤
      1 / (8 * (pJ Q : ℝ) ^ 2)) ∧
    1 + (pJ Q : ℝ) * (8 * (pJ Q : ℝ) ^ 2 * C * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ)) ≤ C' * Q ^ (1 / 4 : ℝ)

def PairTwistOf : Prop := PairSum → PairTwist
def CoeffSqOf : Prop := Formalism.FX.DivisorBound → CoeffSq
def DetectOf : Prop := MollId → Detect
def BlockCountOf : Prop := DualIneq → PairTwist → BlockCount
def FinalOf : Prop := CoeffSq → Detect → BlockCount → Num → ZeroDensityBox

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end
