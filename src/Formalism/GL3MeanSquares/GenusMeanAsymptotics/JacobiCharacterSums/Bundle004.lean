module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

section

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem num_alg (M y C D Pt t lg lm : ℝ) (hM : 1 ≤ M) (hy : M ^ 5 ≤ y) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hPt : Pt ≤ (M ^ 8)⁻¹) (ht : t ≤ (M ^ 2)⁻¹) (hlg : lg ≤ D * M ^ 2)
    (hlm0 : 0 ≤ lm) (hlm : lm ≤ 13 * M) :
    M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹ + 4 * ((M ^ 5)⁻¹ * y + 1) * lg)
        + 20 * (M ^ 5)⁻¹ * y + 2 * y * t ≤ (4 * C + 676 * C * D + 8 * D + 22) * y * (M ^ 2)⁻¹ := by
  have hM0 : 0 < M := by linarith
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  have hA : M ^ 6 * Pt ≤ (M ^ 2)⁻¹ := by
    calc M ^ 6 * Pt ≤ M ^ 6 * (M ^ 8)⁻¹ := mul_le_mul_of_nonneg_left hPt (by positivity)
      _ = (M ^ 2)⁻¹ := by field_simp
  have hB : lg * lm ^ 2 / M ^ 6 ≤ 169 * D * (M ^ 2)⁻¹ := by
    have hlm2 : lm ^ 2 ≤ 169 * M ^ 2 := by nlinarith
    have h2 : lg * lm ^ 2 ≤ D * M ^ 2 * (169 * M ^ 2) :=
      calc lg * lm ^ 2 ≤ D * M ^ 2 * lm ^ 2 := mul_le_mul_of_nonneg_right hlg (sq_nonneg _)
        _ ≤ D * M ^ 2 * (169 * M ^ 2) := mul_le_mul_of_nonneg_left hlm2 (by positivity)
    calc lg * lm ^ 2 / M ^ 6 ≤ D * M ^ 2 * (169 * M ^ 2) / M ^ 6 :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ = 169 * D * (M ^ 2)⁻¹ := by field_simp <;> ring
  have e1 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
      = 4 * C * y * (M ^ 6 * Pt + lg * lm ^ 2 / M ^ 6) := by
    field_simp <;> ring
  have h1 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
      ≤ 4 * C * y * ((M ^ 2)⁻¹ + 169 * D * (M ^ 2)⁻¹) := by
    rw [e1]; exact mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
  have hM3 : M ^ 3 ≤ y * (M ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]; calc M ^ 3 * M ^ 2 = M ^ 5 := by ring
      _ ≤ y := hy
  have h2 : M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) ≤ 8 * D * y * (M ^ 2)⁻¹ := by
    have hc : 0 ≤ 4 * M * ((M ^ 5)⁻¹ * y + 1) := by positivity
    calc M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) = 4 * M * ((M ^ 5)⁻¹ * y + 1) * lg := by ring
      _ ≤ 4 * M * ((M ^ 5)⁻¹ * y + 1) * (D * M ^ 2) := mul_le_mul_of_nonneg_left hlg hc
      _ = 4 * D * (y * (M ^ 2)⁻¹ + M ^ 3) := by field_simp <;> ring
      _ ≤ 4 * D * (y * (M ^ 2)⁻¹ + y * (M ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 8 * D * y * (M ^ 2)⁻¹ := by ring
  have h5 : (M ^ 5)⁻¹ ≤ (M ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hM (by norm_num))
  have h3 : 20 * (M ^ 5)⁻¹ * y ≤ 20 * (M ^ 2)⁻¹ * y := by
    have := mul_le_mul_of_nonneg_right h5 hy0; linarith
  have h4 : 2 * y * t ≤ 2 * y * (M ^ 2)⁻¹ := mul_le_mul_of_nonneg_left ht (by positivity)
  have e2 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹ + 4 * ((M ^ 5)⁻¹ * y + 1) * lg)
      = M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
        + M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) := by ring
  rw [e2]
  have e3 : (4 * C + 676 * C * D + 8 * D + 22) * y * (M ^ 2)⁻¹
      = 4 * C * y * ((M ^ 2)⁻¹ + 169 * D * (M ^ 2)⁻¹) + 8 * D * y * (M ^ 2)⁻¹
        + 20 * (M ^ 2)⁻¹ * y + 2 * y * (M ^ 2)⁻¹ := by ring
  rw [e3]
  linarith

theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have h3 : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) h3

theorem inv_pow_eq_exp {M : ℝ} (hM : 0 < M) (n : ℕ) : (M ^ n)⁻¹ = Real.exp (-(n * Real.log M)) := by
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos hM n)]

theorem logy_lt {cA M y : ℝ} (hcA : 0 < cA) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) : cA ^ 2 * Real.log y < Real.log M ^ 2 := by
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hs := Real.sq_sqrt hl
  have h0 : 0 ≤ cA * Real.sqrt (Real.log y) := by positivity
  have h2 : (cA * Real.sqrt (Real.log y)) ^ 2 < Real.log M ^ 2 := by nlinarith
  calc cA ^ 2 * Real.log y = (cA * Real.sqrt (Real.log y)) ^ 2 := by rw [mul_pow, hs]
    _ < Real.log M ^ 2 := h2

theorem inv_le_exp {cA c M y : ℝ} (hcA : 0 < cA) (hc : 0 < c) (hc' : c ≤ cA ^ 2) (hM : 8 ≤ M) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) :
    M⁻¹ ≤ Real.exp (-(c * Real.log y / Real.log M)) := by
  have hM0 : 0 < M := by linarith
  have hlM : 0 < Real.log M := Real.log_pos (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have h2 := logy_lt hcA hy h
  have h3 : c * Real.log y ≤ Real.log M ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hc' hly]
  have h4 : c * Real.log y / Real.log M ≤ Real.log M := by
    rw [div_le_iff₀ hlM]; nlinarith
  calc M⁻¹ = Real.exp (-Real.log M) := by rw [Real.exp_neg, Real.exp_log hM0]
    _ ≤ Real.exp (-(c * Real.log y / Real.log M)) := Real.exp_le_exp.mpr (by linarith)

theorem num_main (cA κ C : ℝ) (hcA : 0 < cA) (hκ : 0 < κ) (hC : 0 < C) :
    ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧ ∀ M y : ℝ, 8 ≤ M → 2 ≤ y →
      C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y →
      cA * Real.sqrt (Real.log y) < Real.log M →
      M * (4 * y * (C * ((M * M ^ (12 : ℝ)) ^ C * y ^ (-(κ / 2))
          + Real.log (2 * y) * Real.log (M * M ^ (12 : ℝ)) ^ 2 / M ^ (12 : ℝ))) / (M ^ 5)⁻¹
          + 4 * ((M ^ 5)⁻¹ * y + 1) * Real.log (2 * y))
        + 20 * (M ^ 5)⁻¹ * y + 2 * y * y ^ (-(κ / 2)) ≤ B * y * (M⁻¹ * M⁻¹) := by
  set D : ℝ := 1 + (cA ^ 2)⁻¹ with hDdef
  have hD : 0 ≤ D := by positivity
  refine ⟨5 + (26 * C + 20) / κ, 4 * C + 676 * C * D + 8 * D + 22, by positivity, by positivity, ?_⟩
  intro M y hM hy hlog hsq
  have hM0 : 0 < M := by linarith
  have hy0 : 0 < y := by linarith
  have hL1 : 1 ≤ Real.log M := one_le_log_of_three_le (by linarith)
  have hl1 : 1 ≤ Real.log (Real.log M + 2) := one_le_log_of_three_le (by linarith)
  have hLM : Real.log M ≤ M := by linarith [Real.log_le_sub_one_of_pos hM0]
  have hC0 : 0 ≤ 5 + (26 * C + 20) / κ := by positivity
  have hlog' : (5 + (26 * C + 20) / κ) * Real.log M ≤ Real.log y := by
    have : (5 + (26 * C + 20) / κ) * Real.log M * 1
        ≤ (5 + (26 * C + 20) / κ) * Real.log M * Real.log (Real.log M + 2) :=
      mul_le_mul_of_nonneg_left hl1 (by positivity)
    linarith
  have hkC : κ * (5 + (26 * C + 20) / κ) = 5 * κ + (26 * C + 20) := by field_simp
  have hK : (26 * C + 20) * Real.log M ≤ κ * Real.log y := by
    have := mul_le_mul_of_nonneg_left hlog' hκ.le
    have h5 : 0 ≤ 5 * κ * Real.log M := by positivity
    nlinarith
  have hy5 : M ^ 5 ≤ y := by
    rw [← Real.log_le_log_iff (by positivity) hy0, Real.log_pow]
    have : 5 * Real.log M ≤ (5 + (26 * C + 20) / κ) * Real.log M := by
      have : 0 ≤ (26 * C + 20) / κ * Real.log M := by positivity
      nlinarith
    push_cast; linarith
  have h12 : M ^ (12 : ℝ) = M ^ 12 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h12]
  have hlm : Real.log (M * M ^ 12) = 13 * Real.log M := by
    rw [show M * M ^ 12 = M ^ 13 by ring, Real.log_pow]; push_cast; ring
  have hpow : (M * M ^ 12) ^ C = Real.exp (13 * C * Real.log M) := by
    rw [Real.rpow_def_of_pos (by positivity), hlm]; ring_nf
  have hyk : y ^ (-(κ / 2)) = Real.exp (-(κ / 2 * Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]; ring_nf
  have hPt : (M * M ^ 12) ^ C * y ^ (-(κ / 2)) ≤ (M ^ 8)⁻¹ := by
    rw [hpow, hyk, ← Real.exp_add, inv_pow_eq_exp hM0]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have ht : y ^ (-(κ / 2)) ≤ (M ^ 2)⁻¹ := by
    rw [hyk, inv_pow_eq_exp hM0]
    apply Real.exp_le_exp.mpr
    push_cast
    have : 0 ≤ 26 * C * Real.log M := by positivity
    nlinarith
  have hlg : Real.log (2 * y) ≤ D * M ^ 2 := by
    have hq := logy_lt hcA hy hsq
    have hq' : Real.log y ≤ Real.log M ^ 2 * (cA ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]; linarith
    have hLM2 : Real.log M ^ 2 ≤ M ^ 2 := by nlinarith
    have hq'' : Real.log M ^ 2 * (cA ^ 2)⁻¹ ≤ M ^ 2 * (cA ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hLM2 (by positivity)
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    have hM1 : 1 ≤ M ^ 2 := by nlinarith
    rw [Real.log_mul (by norm_num) hy0.ne', hDdef]
    nlinarith
  have hlm0 : 0 ≤ Real.log (M * M ^ 12) := by rw [hlm]; linarith
  have hlm13 : Real.log (M * M ^ 12) ≤ 13 * M := by rw [hlm]; linarith
  have key := num_alg M y C D ((M * M ^ 12) ^ C * y ^ (-(κ / 2))) (y ^ (-(κ / 2)))
    (Real.log (2 * y)) (Real.log (M * M ^ 12)) (by linarith) hy5 hC.le hD hPt ht hlg hlm0 hlm13
  refine key.trans (le_of_eq ?_)
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

theorem log_pow_five_le_sqrt (c : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → c * Real.log q ^ 5 ≤ Real.sqrt q := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 10)).bound
    (c := 1 / (c ^ 2 + 1)) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 h
  refine ⟨⌈x₀⌉₊, fun q hq => ?_⟩
  have hqx : x₀ ≤ (q : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hq)
  have h1 := hx₀ q hqx
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hq0] at h1
  have h2 : Real.log q ^ 10 ≤ 1 / (c ^ 2 + 1) * q := (le_abs_self _).trans h1
  have h3 : (c ^ 2 + 1) * Real.log q ^ 10 ≤ q := by
    have hp : (0 : ℝ) < c ^ 2 + 1 := by positivity
    calc (c ^ 2 + 1) * Real.log q ^ 10 ≤ (c ^ 2 + 1) * (1 / (c ^ 2 + 1) * q) := by gcongr
      _ = (q : ℝ) := by field_simp
  have h4 : (c * Real.log q ^ 5) ^ 2 ≤ q := by
    have : (0 : ℝ) ≤ Real.log q ^ 10 := by positivity
    nlinarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt h4)

theorem one_le_log_of_three_le_second {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem dyadic_index_le_log_second (q : ℕ) (hq : 3 ≤ q) : ((8 * (Nat.log 2 q + 1) : ℕ) : ℝ) ≤ 24 * Real.log q := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 q ≤ q := by exact_mod_cast h1
  have h3 : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2
  have h4 := Real.log_two_gt_d9
  have h5 := one_le_log_of_three_le_second hq'
  have h6 : (0 : ℝ) ≤ (Nat.log 2 q : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith

theorem dyadic_size_le_pow_twelve_second (q : ℕ) (hq : 256 ≤ q) : q ^ 3 * 2 ^ (8 * (Nat.log 2 q + 1)) ≤ q ^ 12 := by
  have h1 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h2 : 2 ^ (8 * (Nat.log 2 q + 1)) = 256 * (2 ^ Nat.log 2 q) ^ 8 := by
    rw [← pow_mul]; rw [show 8 * (Nat.log 2 q + 1) = 8 + Nat.log 2 q * 8 by ring, pow_add]; norm_num
  rw [h2]
  calc q ^ 3 * (256 * (2 ^ Nat.log 2 q) ^ 8) ≤ q ^ 3 * (q * q ^ 8) := by gcongr
    _ = q ^ 12 := by ring

theorem second_small_condition (u l K J q s Lq : ℝ) (hq : 0 < q) (hs : 0 < s) (hu : u ≤ 1 / (q * s))
    (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 48 * q) (hJ0 : 0 < J) (hJ : J ≤ 24 * Lq)
    (hc : 971882496 * Lq ^ 5 ≤ s) : 2 * u * l ^ 3 * K ≤ (1 / (2 * J)) ^ 2 / 2 := by
  have hL : 0 < Lq := by nlinarith
  have h1 : 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) := by
    have : 0 ≤ 1 / (q * s) := by positivity
    calc 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * l ^ 3 * K := by gcongr
      _ ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) := by gcongr
  have h2 : 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) = 210912 * Lq ^ 3 / s := by
    field_simp; ring
  have h3 : 1 / (4608 * Lq ^ 2) ≤ (1 / (2 * J)) ^ 2 / 2 := by
    have : (1 / (2 * J)) ^ 2 / 2 = 1 / (8 * J ^ 2) := by field_simp; ring
    rw [this]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h4 : 210912 * Lq ^ 3 / s ≤ 1 / (4608 * Lq ^ 2) := by
    rw [div_le_div_iff₀ hs (by positivity)]
    nlinarith
  linarith

theorem rpow_neg_exponent_bound_second (q U : ℕ) (σ : ℝ) (hq : 1 ≤ q) (hσ : 3 / 4 ≤ σ) (hU : q ^ 3 ≤ U) :
    (U : ℝ) ^ (1 - 2 * σ) ≤ 1 / ((q : ℝ) * Real.sqrt q) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq'
  have hU' : (q : ℝ) ^ 3 ≤ U := by exact_mod_cast hU
  have h1 : (U : ℝ) ^ (1 - 2 * σ) ≤ (U : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hU' (by norm_num)
  have h3 : ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) = 1 / ((q : ℝ) * Real.sqrt q) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    congr 1
    rw [show (q : ℝ) ^ 3 = (q : ℝ) ^ 2 * q by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  linarith

theorem rpow_pos_exponent_bound_second (q U : ℕ) (x σ : ℝ) (hx : 0 < x) (hqx : (q : ℝ) ≤ 2 * x) (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : U ≤ q ^ 12) : (U : ℝ) ^ (2 - 2 * σ) ≤ 64 * x ^ (24 * (1 - σ)) := by
  have hU' : (U : ℝ) ≤ (2 * x) ^ 12 := by
    calc (U : ℝ) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU
      _ ≤ (2 * x) ^ 12 := by gcongr
  have h1 : (U : ℝ) ^ (2 - 2 * σ) ≤ ((2 * x) ^ 12) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hU' (by linarith)
  have h2 : ((2 * x) ^ 12) ^ (2 - 2 * σ) = (2 * x) ^ (24 * (1 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  have h3 : (2 * x) ^ (24 * (1 - σ)) = 2 ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) :=
    Real.mul_rpow (by norm_num) hx.le
  have h4 : (2 : ℝ) ^ (24 * (1 - σ)) ≤ 64 := by
    have : (2 : ℝ) ^ (6 : ℝ) = 64 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [← this]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h5 : 0 ≤ x ^ (24 * (1 - σ)) := by positivity
  rw [h2, h3] at h1
  nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

section

open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

theorem log_pow_seven_le_sqrt (c : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → c * Real.log q ^ 7 ≤ Real.sqrt q := by
  have h := isLittleO_log_rpow_rpow_atTop (7 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have hb := h.bound (show (0 : ℝ) < 1 / (|c| + 1) by positivity)
  have hn := tendsto_natCast_atTop_atTop.eventually hb
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp (hn.and (Filter.eventually_ge_atTop 1))
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨h1, h2⟩ := hq₀ q hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h2
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at h1
  have e7 : Real.log q ^ (7 : ℝ) = Real.log q ^ 7 := by
    exact_mod_cast Real.rpow_natCast (Real.log q) 7
  rw [e7, ← Real.sqrt_eq_rpow] at h1
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  calc c * Real.log q ^ 7 ≤ |c| * Real.log q ^ 7 :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    _ ≤ |c| * (1 / (|c| + 1) * Real.sqrt q) := by gcongr
    _ ≤ Real.sqrt q := by
        rw [← mul_assoc]
        apply mul_le_of_le_one_left hs
        rw [mul_one_div, div_le_one (by positivity)]
        linarith

theorem one_le_log_of_three_le' {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem dyadic_index_le_log (q : ℕ) (hq : 3 ≤ q) :
    ((8 * (Nat.log 2 q + 1) : ℕ) : ℝ) + 1 ≤ 25 * Real.log q := by
  have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h1 : ((2 : ℝ) ^ Nat.log 2 q) ≤ q := by exact_mod_cast hpow
  have h2 : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have hl2 := Real.log_two_gt_d9
  have hlq : 1 ≤ Real.log q := one_le_log_of_three_le' (by exact_mod_cast hq)
  have hn0 : (0 : ℝ) ≤ Nat.log 2 q := Nat.cast_nonneg _
  have h3 : 0.6931471803 * (Nat.log 2 q : ℝ) ≤ Real.log q := by nlinarith
  push_cast
  linarith

theorem dyadic_size_le_pow_twelve (q : ℕ) (hq : 512 ≤ q) :
    2 * (q ^ 3 * 2 ^ (8 * (Nat.log 2 q + 1))) ≤ q ^ 12 := by
  have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  generalize Nat.log 2 q = n at hpow ⊢
  have h8 : 2 ^ (8 * (n + 1)) = 256 * (2 ^ n) ^ 8 := by
    rw [show 8 * (n + 1) = n * 8 + 8 by ring, pow_add, pow_mul]
    ring
  have h9 : (2 ^ n) ^ 8 ≤ q ^ 8 := Nat.pow_le_pow_left hpow 8
  rw [h8]
  calc 2 * (q ^ 3 * (256 * (2 ^ n) ^ 8)) ≤ 2 * (q ^ 3 * (256 * q ^ 8)) := by gcongr
    _ = 512 * q ^ 11 := by ring
    _ ≤ q * q ^ 11 := by gcongr
    _ = q ^ 12 := by ring

theorem first_small_condition (u l K J q s Lq c : ℝ) (hq : 0 < q) (hs : 0 < s) (hc0 : 0 < c)
    (hu : u ≤ 1 / (q * s)) (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 16 * q)
    (hJ0 : 0 < J) (hJ : J ≤ 25 * Lq) (hc : 87880000 / c ^ 2 * Lq ^ 7 ≤ s) :
    2 * u * l ^ 3 * K ≤ (c / (J * Lq)) ^ 2 / 2 := by
  have hL : 0 < Lq := by linarith
  have hlK : 0 ≤ l ^ 3 * K := by positivity
  have step1 : 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * l ^ 3 * K := by
    have := mul_le_mul_of_nonneg_right hu hlK
    nlinarith
  have step2 : 2 * (1 / (q * s)) * l ^ 3 * K ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q) := by
    gcongr
  have step3 : 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q) = 70304 * Lq ^ 3 / s := by
    field_simp
    ring
  have hJL : (c / (25 * Lq * Lq)) ^ 2 / 2 ≤ (c / (J * Lq)) ^ 2 / 2 := by
    gcongr
  have hc' : 87880000 * Lq ^ 7 ≤ s * c ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hc
    exact hc
  have step4 : 70304 * Lq ^ 3 / s ≤ (c / (25 * Lq * Lq)) ^ 2 / 2 := by
    have e : (c / (25 * Lq * Lq)) ^ 2 / 2 = c ^ 2 / (1250 * Lq ^ 4) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ hs (by positivity)]
    nlinarith
  linarith

theorem rpow_neg_exponent_bound (q U : ℕ) (σ : ℝ) (hq : 1 ≤ q) (hσ : 3 / 4 ≤ σ) (hU : q ^ 3 ≤ U) :
    (U : ℝ) ^ (1 - 2 * σ) ≤ 1 / ((q : ℝ) * Real.sqrt q) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq'
  have hU' : (q : ℝ) ^ 3 ≤ U := by exact_mod_cast hU
  have h1 : (U : ℝ) ^ (1 - 2 * σ) ≤ (U : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hU' (by norm_num)
  have h3 : ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) = 1 / ((q : ℝ) * Real.sqrt q) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    congr 1
    rw [show (q : ℝ) ^ 3 = (q : ℝ) ^ 2 * q by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  linarith

theorem rpow_pos_exponent_bound (q U : ℕ) (x σ : ℝ) (hx : 0 < x) (hqx : (q : ℝ) ≤ 2 * x) (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : U ≤ q ^ 12) : (U : ℝ) ^ (2 - 2 * σ) ≤ 64 * x ^ (24 * (1 - σ)) := by
  have he : 0 ≤ 2 - 2 * σ := by linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hUq : (U : ℝ) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU
  have s1 : (U : ℝ) ^ (2 - 2 * σ) ≤ ((q : ℝ) ^ 12) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hUq he
  have s2 : ((q : ℝ) ^ 12) ^ (2 - 2 * σ) ≤ ((2 * x) ^ 12) ^ (2 - 2 * σ) := by
    apply Real.rpow_le_rpow (by positivity) _ he
    gcongr
  have s3 : ((2 * x) ^ 12) ^ (2 - 2 * σ) = (2 : ℝ) ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hx.le]
    rw [show ((12 : ℕ) : ℝ) * (2 - 2 * σ) = 24 * (1 - σ) by push_cast; ring]
  have s4 : (2 : ℝ) ^ (24 * (1 - σ)) ≤ 64 := by
    calc (2 : ℝ) ^ (24 * (1 - σ)) ≤ (2 : ℝ) ^ ((6 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 64 := by rw [Real.rpow_natCast]; norm_num
  have hx' : 0 ≤ x ^ (24 * (1 - σ)) := by positivity
  calc (U : ℝ) ^ (2 - 2 * σ) ≤ (2 : ℝ) ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) := by
        rw [← s3]; exact s1.trans s2
    _ ≤ 64 * x ^ (24 * (1 - σ)) := by gcongr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end
