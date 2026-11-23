module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

section

namespace GlobalTheory

theorem gammaℝ_functional_constant_even :
    ∀ (d : ℝ), 0 < d → ∀ (f s : ℕ), 1 ≤ s → ∀ A B : ℂ,
      (d : ℂ) ^ (((2 * s : ℕ) : ℂ) / 2) * Complex.Gammaℝ ((2 * s : ℕ) : ℂ) ^ f * A =
        (d : ℂ) ^ ((1 - ((2 * s : ℕ) : ℂ)) / 2) * Complex.Gammaℝ (1 - ((2 * s : ℕ) : ℂ)) ^ f * B →
      (((2 * s - 1).factorial : ℕ) : ℂ) ^ f * ((d ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) *
        ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * f))⁻¹ * A = (2 : ℂ)⁻¹ ^ f * B := by
  intro d hd f s hs A B hAB
  set k : ℂ := ((2 * s : ℕ) : ℂ) with hk
  have hk' : k = 2 * (s : ℂ) := by rw [hk]; push_cast; ring
  have hh : Complex.Gammaℝ (1 - k) ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have h1 : ((1 : ℤ) : ℂ) = ((2 * s - 2 * n : ℤ) : ℂ) := by
      push_cast; rw [hk'] at hn; linear_combination hn
    have h2 := Int.cast_injective h1
    omega
  have hodd : ∀ n : ℕ, k ≠ -(2 * n + 1) := by
    intro n hn
    have h1 : ((2 * s : ℤ) : ℂ) = ((-(2 * n + 1) : ℤ) : ℂ) := by
      push_cast; rw [← hk']; exact hn
    have h2 := Int.cast_injective h1
    omega
  have hratio := Complex.Gammaℝ_div_Gammaℝ_one_sub hodd
  have hΓ : Complex.Gamma k = (((2 * s - 1).factorial : ℕ) : ℂ) := by
    have : k = ((2 * s - 1 : ℕ) : ℂ) + 1 := by
      rw [hk]; norm_cast; omega
    rw [this, Complex.Gamma_nat_eq_factorial]
  have hcos : Complex.cos ((Real.pi : ℂ) * k / 2) = (-1) ^ s := by
    rw [hk', show (Real.pi : ℂ) * (2 * s) / 2 = (s : ℂ) * Real.pi by ring]
    rw [show (s : ℂ) * Real.pi = (((s : ℝ) * Real.pi : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
    push_cast; ring
  have hpow : (2 * (Real.pi : ℂ)) ^ (-k) = ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ := by
    rw [Complex.cpow_neg, hk, Complex.cpow_natCast]
  have hg : Complex.Gammaℝ k = Complex.Gammaℝ (1 - k) *
      (2 * ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ * (((2 * s - 1).factorial : ℕ) : ℂ) * (-1) ^ s) := by
    rw [div_eq_iff hh, Complex.Gammaℂ_def, hΓ, hcos, hpow] at hratio
    rw [hratio]; ring
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hE : ((d ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) = (d : ℂ) ^ (k - 1 / 2) := by
    rw [Complex.ofReal_cpow hd.le]; congr 1; rw [hk]; push_cast; ring
  have hD : (d : ℂ) ^ (k / 2) = (d : ℂ) ^ ((1 - k) / 2) * (d : ℂ) ^ (k - 1 / 2) := by
    rw [← Complex.cpow_add _ _ hd0]; congr 1; ring
  have hD2 : (d : ℂ) ^ ((1 - k) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hB : B = (d : ℂ) ^ (k - 1 / 2) *
      (2 * ((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹ * (((2 * s - 1).factorial : ℕ) : ℂ) * (-1) ^ s) ^ f * A := by
    rw [hD, hg, mul_pow] at hAB
    have hne : (d : ℂ) ^ ((1 - k) / 2) * Complex.Gammaℝ (1 - k) ^ f ≠ 0 :=
      mul_ne_zero hD2 (pow_ne_zero _ hh)
    apply mul_left_cancel₀ hne
    rw [← hAB]; ring
  rw [hE, hB]
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * f) =
      ((2 * (Real.pi : ℂ)) ^ (2 * s)) ^ f * ((-1 : ℂ) ^ s) ^ f := by
    rw [pow_mul, ← mul_pow, mul_pow (2 * (Real.pi : ℂ)) Complex.I, pow_mul Complex.I 2 s, Complex.I_sq]
  have hm : (((-1 : ℂ) ^ s) ^ f)⁻¹ = ((-1 : ℂ) ^ s) ^ f := by
    rw [← inv_pow, ← inv_pow, inv_neg_one]
  rw [hI, mul_inv, hm, ← inv_pow]
  have h2 : (2 : ℂ)⁻¹ ^ f * (2 : ℂ) ^ f = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  linear_combination (-((((2 * s - 1).factorial : ℕ) : ℂ) ^ f * (d : ℂ) ^ (k - 1 / 2) *
    (((2 * (Real.pi : ℂ)) ^ (2 * s))⁻¹) ^ f * ((-1 : ℂ) ^ s) ^ f * A)) * h2

end GlobalTheory
end

section

namespace GlobalTheory

theorem digit_le_logb_succ (p d : ℕ) (hp : 1 < p) (hd : d < p) :
    (d : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((d : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hdle : (d : ℝ) ≤ (p : ℝ) - 1 := by
    have h : ((d : ℝ) + 1) ≤ p := by exact_mod_cast hd
    linarith
  set t : ℝ := (d : ℝ) / ((p : ℝ) - 1) with ht
  have ht0 : 0 ≤ t := div_nonneg (by positivity) hpm.le
  have ht1 : t ≤ 1 := (div_le_one hpm).2 hdle
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).2
    (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) (by simp only [Set.mem_Ioi]; linarith : (p : ℝ) ∈ Set.Ioi 0)
    (sub_nonneg.2 ht1) ht0 (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hconc
  have heq : (1 - t) + t * p = (d : ℝ) + 1 := by
    rw [ht]; field_simp; ring
  rw [heq] at hconc
  have hmul : (d : ℝ) * Real.log p = ((p : ℝ) - 1) * (t * Real.log p) := by
    rw [ht]; field_simp
  rw [Real.logb, ← mul_div_assoc, le_div_iff₀ hlogp, hmul]
  exact mul_le_mul_of_nonneg_left hconc hpm.le

theorem digits_sum_le_logb (p n : ℕ) (hp : p.Prime) :
    (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' hp.one_lt hn, List.sum_cons, Nat.cast_add]
      have hdiv := Nat.div_add_mod n p
      have hdp : n % p < p := Nat.mod_lt n hp.pos
      have ihq := ih (n / p) (Nat.div_lt_self hn hp.one_lt)
      have hd := digit_le_logb_succ p (n % p) hp.one_lt hdp
      have hprod : (((n / p : ℕ) : ℝ) + 1) * (((n % p : ℕ) : ℝ) + 1) ≤ (n : ℝ) + 1 := by
        have h1 : (n / p + 1) * (n % p + 1) ≤ n + 1 := by
          have : (n / p) * (n % p + 1) ≤ (n / p) * p := Nat.mul_le_mul_left _ hdp
          nlinarith
        exact_mod_cast h1
      have hlog : Real.logb p (((n / p : ℕ) : ℝ) + 1) + Real.logb p (((n % p : ℕ) : ℝ) + 1)
          ≤ Real.logb p ((n : ℝ) + 1) := by
        rw [← Real.logb_mul (by positivity) (by positivity)]
        exact Real.logb_le_logb_of_le hp1 (by positivity) hprod
      nlinarith [mul_le_mul_of_nonneg_left hlog hpm]

end GlobalTheory
end

section

namespace GlobalTheory

theorem lamLow_numerical_end : ∀ (f n r : ℕ) (L' dmax mass Lq lam : ℝ) (H dt dk dD : Fin f → ℝ), 8 ≤ n → 2 * r ≤ n → 1 ≤ r → 1 ≤ f → (5.5 : ℝ) ≤ L' → Real.log n ≤ L' → 0 ≤ dmax → Real.log (dmax + 2) ≤ 2 * L' → 1 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≤ mass → 0 < Lq → |Real.log Lq| ≤ f * r / 4 → (∀ ρ, 0 < H ρ ∧ 1 ≤ dt ρ ∧ 1 ≤ dk ρ ∧ 0 < dD ρ ∧ Real.log (dD ρ) ≤ 2 + (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2))) → lam = mass * Lq * ∏ ρ, (H ρ * dt ρ * dk ρ / dD ρ) → ∑ ρ, Real.log (H ρ) - 2 * f * (n : ℝ) ^ 2 * L' ≤ Real.log lam := by
  intro f n r L' dmax mass Lq lam H dt dk dD hn hr hr1 hf hL' hlogn hdmax hlogd hmass hLq hlogLq hρ hlam
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr2 : 2 * (r : ℝ) ≤ n := by exact_mod_cast hr
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hnpos : (0 : ℝ) < n := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hmpos : 0 < mass := lt_of_lt_of_le (by positivity) hmass
  have hlogmass : -((n : ℝ) * Real.log 2 + (n : ℝ) * Real.log n) ≤ Real.log mass := by
    have h1 := Real.log_le_log (by positivity) hmass
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    have hfac : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.factorial_le_pow n
    linarith
  have hX : Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ 5 * L' := by
    have hd : (0 : ℝ) < dmax + 2 := by linarith
    have h3 : 3 * (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hle : 3 * (r : ℝ) ^ 2 * n * (dmax + 2) ≤ (n : ℝ) ^ 3 * (dmax + 2) := by
      calc 3 * (r : ℝ) ^ 2 * n * (dmax + 2) ≤ (n : ℝ) ^ 2 * n * (dmax + 2) := by gcongr
        _ = (n : ℝ) ^ 3 * (dmax + 2) := by ring
    have hpos : 0 < 3 * (r : ℝ) ^ 2 * n * (dmax + 2) :=
      mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hrpos 2)) hnpos) hd
    have h4 := Real.log_le_log hpos hle
    rw [Real.log_mul (pow_pos hnpos 3).ne' hd.ne', Real.log_pow] at h4
    push_cast at h4
    linarith
  have hsq : (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / 4 := by nlinarith
  have hdD : (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ 5 / 4 * (n : ℝ) ^ 2 * L' := by
    calc (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ (r : ℝ) ^ 2 * (5 * L') :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ ≤ (n : ℝ) ^ 2 / 4 * (5 * L') := mul_le_mul_of_nonneg_right hsq (by linarith)
      _ = 5 / 4 * (n : ℝ) ^ 2 * L' := by ring
  have hfac_pos : ∀ ρ, 0 < H ρ * dt ρ * dk ρ / dD ρ := fun ρ => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hρ ρ
    have ht : 0 < dt ρ := by linarith
    have hk : 0 < dk ρ := by linarith
    exact div_pos (mul_pos (mul_pos h1 ht) hk) h4
  have hprodpos : 0 < ∏ ρ, (H ρ * dt ρ * dk ρ / dD ρ) := Finset.prod_pos (fun ρ _ => hfac_pos ρ)
  have e1 : Real.log lam = Real.log mass + Real.log Lq + ∑ ρ, Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    rw [hlam, Real.log_mul (mul_pos hmpos hLq).ne' hprodpos.ne', Real.log_mul hmpos.ne' hLq.ne',
      Real.log_prod (fun ρ _ => (hfac_pos ρ).ne')]
  have e2 : ∀ ρ, Real.log (H ρ) - (2 + 5 / 4 * (n : ℝ) ^ 2 * L') ≤ Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    intro ρ
    obtain ⟨h1, h2, h3, h4, h5⟩ := hρ ρ
    have ht : 0 < dt ρ := by linarith
    have hk : 0 < dk ρ := by linarith
    rw [Real.log_div (mul_pos (mul_pos h1 ht) hk).ne' h4.ne', Real.log_mul (mul_pos h1 ht).ne' hk.ne',
      Real.log_mul h1.ne' ht.ne']
    have := Real.log_nonneg h2
    have := Real.log_nonneg h3
    linarith
  have hsum : ∑ ρ, Real.log (H ρ) - (f : ℝ) * (2 + 5 / 4 * (n : ℝ) ^ 2 * L') ≤
      ∑ ρ, Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    have := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => e2 ρ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hLqlow : -((f : ℝ) * r / 4) ≤ Real.log Lq := by
    have := neg_abs_le (Real.log Lq)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hfL : 1 ≤ (f : ℝ) * L' := by nlinarith
  have hP1 : (n : ℝ) ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_left hfL hnpos.le]
  have hnL : 0 ≤ (n : ℝ) * L' := by positivity
  have hP2 : (n : ℝ) * L' ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_right hf1 hnL]
  have hP3 : (f : ℝ) * r / 4 ≤ f * n * L' := by
    have hrn : (r : ℝ) / 4 ≤ n * L' := by nlinarith
    linarith [mul_le_mul_of_nonneg_left hrn (by linarith : (0 : ℝ) ≤ f)]
  have hnL2 : (2 : ℝ) ≤ n * L' := by nlinarith [mul_le_mul hn8 hL' (by norm_num) hnpos.le]
  have hP4 : 2 * (f : ℝ) ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_left hnL2 (by linarith : (0 : ℝ) ≤ f)]
  have hbig : 8 * ((f : ℝ) * n * L') ≤ f * (n : ℝ) ^ 2 * L' := by
    have h0 : 0 ≤ (f : ℝ) * n * L' := by positivity
    linarith [mul_le_mul_of_nonneg_right hn8 h0]
  have hm1 := mul_le_mul_of_nonneg_left hlog2 hnpos.le
  have hm2 := mul_le_mul_of_nonneg_left hlogn hnpos.le
  rw [e1]
  linarith

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory

theorem le_add_mul_log_sq_of_le_add_mul_log :
    ∀ (α β r s : ℝ), 0 ≤ α → 0 ≤ β → 1 ≤ r → r ≤ s → s ≤ α + β * Real.log r →
      s ≤ α + β * Real.log ((α + 2 * β + 1) ^ 2) := by
  intro α β r s hα hβ hr hrs hs
  have hr0 : 0 < r := by linarith
  set t := Real.sqrt r with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg r
  have htt : t * t = r := Real.mul_self_sqrt hr0.le
  have ht1 : 1 ≤ t := by
    by_contra h
    push_neg at h
    nlinarith
  have htpos : 0 < t := by linarith
  have hlog : Real.log r ≤ 2 * t - 2 := by
    have h1 : Real.log r = 2 * Real.log t := by
      rw [← htt, Real.log_mul htpos.ne' htpos.ne']; ring
    have h2 := Real.log_le_sub_one_of_pos htpos
    linarith
  have hle : t ≤ α + 2 * β + 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_left h htpos, mul_nonneg hα (sub_nonneg.mpr ht1),
      mul_le_mul_of_nonneg_left hlog hβ]
  have hrc : r ≤ (α + 2 * β + 1) ^ 2 := by
    rw [← htt]; nlinarith
  have hl : Real.log r ≤ Real.log ((α + 2 * β + 1) ^ 2) := Real.log_le_log hr0 hrc
  nlinarith [mul_le_mul_of_nonneg_left hl hβ]

end GlobalTheory
end

section

open Real

namespace GlobalTheory

theorem log_theta_weight_size_le (f r Lb S sz : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ Lb)
    (hlog : Real.log (f * r) ≤ Lb) (hS : ∃ N : ℕ, S = N) (hlogS : Real.log S ≤ 10 * Lb)
    (hsz0 : 0 ≤ sz) (hsz : sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1)) :
    Real.log sz ≤ 20 * Lb := by
  obtain ⟨N, rfl⟩ := hS
  have hx : 0 < f * r := by positivity
  have hE : 2 ≤ Real.exp Lb := by have := Real.add_one_le_exp Lb; linarith
  have hxE : f * r ≤ Real.exp Lb := by
    rw [← Real.exp_log hx]; exact Real.exp_le_exp.mpr hlog
  have hpow : ∀ n : ℕ, Real.exp Lb ^ n = Real.exp (n * Lb) := fun n => (Real.exp_natCast_mul n Lb).symm
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hSE : (N:ℝ) ≤ Real.exp Lb ^ 10 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp; positivity
    · have hNp : (0:ℝ) < N := by exact_mod_cast h
      rw [hpow, ← Real.exp_log hNp]
      exact Real.exp_le_exp.mpr (by push_cast; linarith)
  set E := Real.exp Lb with hEdef
  set x := f * r with hxdef
  have hE1 : 1 ≤ E := by linarith
  have hr1 : 1 + r ≤ 2 * x := by rw [hxdef]; nlinarith
  have h1 : (1 + r) * (N:ℝ) ≤ 2 * E ^ 11 := by
    calc (1 + r) * (N:ℝ) ≤ (2 * x) * N := mul_le_mul_of_nonneg_right hr1 hN0
      _ ≤ (2 * E) * E ^ 10 := by
          apply mul_le_mul (by linarith) hSE hN0 (by positivity)
      _ = 2 * E ^ 11 := by ring
  have h2 : r * f * (4 * (f * r + 1) + 1) ≤ 9 * E ^ 2 := by
    have : r * f * (4 * (f * r + 1) + 1) = x * (4 * x + 5) := by rw [hxdef]; ring
    rw [this]
    have hx1 : 1 ≤ x := by rw [hxdef]; nlinarith
    nlinarith
  have h3 : E ^ 2 ≤ E ^ 11 := pow_le_pow_right₀ hE1 (by norm_num)
  have h4 : (2:ℝ) ^ 9 ≤ E ^ 9 := pow_le_pow_left₀ (by norm_num) hE 9
  have h5 : 11 * E ^ 11 ≤ E ^ 20 := by
    have : E ^ 20 = E ^ 9 * E ^ 11 := by ring
    rw [this]
    have : (0:ℝ) ≤ E ^ 11 := by positivity
    nlinarith
  have key : sz ≤ Real.exp (20 * Lb) := by
    have : Real.exp (20 * Lb) = E ^ 20 := by rw [hEdef, hpow]; norm_num
    rw [this]; linarith
  rcases hsz0.eq_or_lt with h | h
  · subst h; simp; linarith
  · exact (Real.log_le_iff_le_exp h).mpr key

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory

theorem rank_le_of_growth_in_radius : ∀ (D : ℕ) (f : ℝ → ℕ → ℝ) (α γ ρ t₀ t₁ : ℝ), 0 ≤ ρ →
    (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => f t m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + γ * t))) →
    (∀ (t : ℝ) (m Q : ℕ), 0 < m → 0 < Q → ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) →
      ρ * (m : ℝ) ^ D * Real.log Q ≤ f t m) → ρ ≤ γ := by
  intro D f α γ ρ t₀ t₁ hρ hlim hbd
  have hev : ∀ᶠ m : ℕ in atTop, ρ * (m : ℝ) ^ D * Real.exp (-(m : ℝ)) ≤ 1 := by
    have h1 : Tendsto (fun x : ℝ => x ^ D * Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero D
    have h2 : Tendsto (fun m : ℕ => ρ * ((m : ℝ) ^ D * Real.exp (-(m : ℝ)))) atTop (𝓝 (ρ * 0)) :=
      (h1.comp tendsto_natCast_atTop_atTop).const_mul ρ
    rw [mul_zero] at h2
    filter_upwards [h2.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with m hm
    rw [mul_assoc]; exact hm.le
  have key : ∀ t, max t₀ (t₁ + 2) ≤ t → ρ * (t - t₁ - 2) ≤ α + γ * t := by
    intro t ht
    have ht0 : t₀ ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : t₁ + 2 ≤ t := le_trans (le_max_right _ _) ht
    refine ge_of_tendsto (hlim t ht0) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
    have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hm1
    set x := Real.exp ((t - t₁ - 1) * m) with hx
    have hx2 : 2 ≤ x := by
      have : 1 ≤ (t - t₁ - 1) * m := by nlinarith
      have h := Real.add_one_le_exp ((t - t₁ - 1) * m)
      linarith
    set Q := ⌊x⌋₊ with hQ
    have hQle : (Q : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hQgt : x < Q + 1 := Nat.lt_floor_add_one x
    have hQpos : 0 < Q := by
      rw [hQ]; exact Nat.floor_pos.mpr (by linarith)
    have e2 : Real.exp (-(m:ℝ)) ≤ 1 / 2 := by
      have h := Real.add_one_le_exp (m:ℝ)
      have hp : Real.exp (-(m:ℝ)) * Real.exp m = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-(m:ℝ))]
    have hQge : Real.exp ((t - t₁ - 2) * m) ≤ Q := by
      have e1 : Real.exp ((t - t₁ - 2) * m) = x * Real.exp (-(m:ℝ)) := by
        rw [hx, ← Real.exp_add]; congr 1; ring
      rw [e1]
      have : x * Real.exp (-(m:ℝ)) ≤ x * (1 / 2) := mul_le_mul_of_nonneg_left e2 (by linarith)
      linarith
    have e3 : x * Real.exp (t₁ * m) = Real.exp (-(m:ℝ)) * Real.exp (t * m) := by
      rw [hx, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hρm : 0 ≤ ρ * (m : ℝ) ^ D := mul_nonneg hρ (pow_nonneg hmpos.le _)
    have hcond : ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) := by
      calc ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m)
          ≤ ρ * (m : ℝ) ^ D * x * Real.exp (t₁ * m) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQle hρm) (Real.exp_pos _).le
        _ = (ρ * (m : ℝ) ^ D * Real.exp (-(m:ℝ))) * Real.exp (t * m) := by
            rw [mul_assoc (ρ * (m : ℝ) ^ D) x, e3]; ring
        _ ≤ 1 * Real.exp (t * m) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
        _ = Real.exp (t * m) := one_mul _
    have hb := hbd t m Q (by omega) hQpos hcond
    have hlog : (t - t₁ - 2) * (m : ℝ) ≤ Real.log Q :=
      calc (t - t₁ - 2) * (m : ℝ) = Real.log (Real.exp ((t - t₁ - 2) * m)) := (Real.log_exp _).symm
        _ ≤ Real.log Q := Real.log_le_log (Real.exp_pos _) hQge
    rw [le_div_iff₀ (by positivity)]
    calc ρ * (t - t₁ - 2) * (m : ℝ) ^ (D + 1) = ρ * (m : ℝ) ^ D * ((t - t₁ - 2) * m) := by ring
      _ ≤ ρ * (m : ℝ) ^ D * Real.log Q := mul_le_mul_of_nonneg_left hlog hρm
      _ ≤ f t m := hb
  by_contra h
  push_neg at h
  have hd : 0 < ρ - γ := sub_pos.mpr h
  set T := max (max t₀ (t₁ + 2)) ((α + ρ * (t₁ + 2)) / (ρ - γ) + 1) with hTdef
  have hk := key T (le_max_left _ _)
  have hT : (α + ρ * (t₁ + 2)) / (ρ - γ) + 1 ≤ T := le_max_right _ _
  have hlt : (α + ρ * (t₁ + 2)) / (ρ - γ) < T := by linarith
  have h3 : α + ρ * (t₁ + 2) < T * (ρ - γ) := (div_lt_iff₀ hd).mp hlt
  nlinarith

end GlobalTheory
end

section

open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory

theorem abs_log_inv_one_sub_le_two_mul_abs (y : ℝ) (hy : |y| ≤ 1 / 2) :
    |Real.log (1 - y)⁻¹| ≤ 2 * |y| := by
  have h1 := le_abs_self y
  have h2 := neg_abs_le y
  have h0 := abs_nonneg y
  have hpos : 0 < 1 - y := by linarith
  rw [abs_le]
  constructor
  · rw [Real.log_inv]
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have h3 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    have h4 : (1 - y)⁻¹ ≤ 1 + 2 * |y| := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith [mul_nonneg h0 (show (0:ℝ) ≤ |y| - y by linarith), mul_nonneg h0 (show (0:ℝ) ≤ 1 / 2 - |y| by linarith)]
    linarith

theorem tprod_inv_one_sub_pos_and_le_exp :
    ∀ {ι : Type} (y : ι → ℝ) (B : ℝ), (∀ a, |y a| ≤ 1 / 2) → Summable (fun a => |y a|) →
      ∑' a, |y a| ≤ B →
      0 < ∏' a, (1 - y a)⁻¹ ∧ ∏' a, (1 - y a)⁻¹ ≤ Real.exp (2 * B) := by
  intro ι y B hy hs hB
  have hb : ∀ a, |Real.log (1 - y a)⁻¹| ≤ 2 * |y a| :=
    fun a => abs_log_inv_one_sub_le_two_mul_abs _ (hy a)
  have hs2 : Summable (fun a => 2 * |y a|) := hs.mul_left 2
  have hsl : Summable (fun a => Real.log (1 - y a)⁻¹) :=
    Summable.of_norm_bounded hs2 (fun a => by simpa only [Real.norm_eq_abs] using hb a)
  have hp := hsl.hasSum.rexp
  have he : (Real.exp ∘ fun a => Real.log (1 - y a)⁻¹) = fun a => (1 - y a)⁻¹ := by
    funext a
    have h1 := le_abs_self (y a)
    have h2 := hy a
    exact Real.exp_log (inv_pos.mpr (by linarith))
  rw [he] at hp
  rw [hp.tprod_eq]
  refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr ?_⟩
  calc ∑' a, Real.log (1 - y a)⁻¹ ≤ ∑' a, 2 * |y a| :=
        hsl.tsum_le_tsum (fun a => (le_abs_self _).trans (hb a)) hs2
    _ = 2 * ∑' a, |y a| := tsum_mul_left
    _ ≤ 2 * B := by linarith

end GlobalTheory
end
