module

public import Formalism.LandauZeroFreeBounds.Bundle001
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
public import Mathlib.NumberTheory.LSeries.Nonvanishing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos_bis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h) hρ
  have hw : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ).re = σ - ρ.re := by simp
  have hwpos : 0 < ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ).re := by rw [hw]; linarith
  rw [one_div, Complex.inv_re]
  apply div_pos hwpos
  rw [Complex.normSq_pos]
  intro h0
  rw [h0] at hwpos
  simp at hwpos

lemma sum_re_one_div_sub_zero_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : Finset ℂ)
    (m : ℂ → ℕ) (hZ : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
  apply Finset.sum_nonneg
  intro ρ hρ
  exact mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_bis χ hχ ρ (hZ ρ hρ) σ hσ).le

lemma re_negLogDeriv_le_of_real_zero (C : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔
        (ρ ∈ Metric.closedBall ((11 / 10 : ℂ) + ((0 : ℝ) : ℂ) * I) (1 / 5) ∧
          DirichletCharacter.LFunction χ ρ = 0))
    (hm1 : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (β σ : ℝ) (hσ : 1 < σ) (hβσ : β < σ) (hβ9 : 9 / 10 ≤ β) (hβ1 : β < 1)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hb : (negLD χ ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re ≤
      C * Real.log ((q : ℝ) * (|(0 : ℝ)| + 2)) -
        ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re) :
    (negLD χ (σ : ℂ)).re ≤ C * Real.log ((q : ℝ) * 2) - 1 / (σ - β) := by
  have hs0 : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) = (σ : ℂ) := by simp
  have hl : (negLD χ ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re = (negLD χ (σ : ℂ)).re := by
    rw [hs0]
  have h02 : |(0 : ℝ)| + 2 = 2 := by norm_num
  rw [h02] at hb
  have hβZ : (β : ℂ) ∈ Z := by
    rw [hZ]
    refine ⟨?_, hzero⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h' : (β : ℂ) - ((11 / 10 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((β - 11 / 10 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h', Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hterm : (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))).re = 1 / (σ - β) := by
    have h' : (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))) = ((1 / (σ - β) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h', Complex.ofReal_re]
  have hrest : 0 ≤ ∑ ρ ∈ Z.erase (β : ℂ), (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρZ := ((hZ ρ).1 (Finset.mem_of_mem_erase hρ)).2
    exact mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_bis χ hχ ρ hρZ σ hσ).le
  have hsplit : (m (β : ℂ) : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))).re +
      ∑ ρ ∈ Z.erase (β : ℂ), (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re =
      ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re :=
    Finset.add_sum_erase Z (fun ρ => (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re) hβZ
  rw [hterm] at hsplit
  have hpos : 0 < 1 / (σ - β) := one_div_pos.mpr (sub_pos.mpr hβσ)
  have hm : (1 : ℝ) ≤ (m (β : ℂ) : ℝ) := by exact_mod_cast hm1 _ hβZ
  have hbig : 1 / (σ - β) ≤ (m (β : ℂ) : ℝ) * (1 / (σ - β)) := by nlinarith
  linarith

theorem twoRealCharNoCommonZeroOfBounds : TwoRealOf := by
  intro hZS hLD hPos
  obtain ⟨C, hC⟩ := hZS
  obtain ⟨C', hC'0, hC'⟩ := hLD
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 3 * |C| + 2 * C' + 1 := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by have := abs_nonneg C; linarith
  have hA0 : 0 < A := by linarith
  refine ⟨1 / (20 * A), one_div_pos.mpr (mul_pos (by norm_num) hA0), ?_⟩
  intro q hq0 χ₁ χ₂ h₁ h₂ h₁1 h₂1 h12 β₁ β₂ hr₁ hr₂
  by_contra hcon
  obtain ⟨hz₁', hz₂'⟩ := not_or.mp hcon
  have hz₁ := not_not.mp hz₁'
  have hz₂ := not_not.mp hz₂'
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * 2) := ⟨_, rfl⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL2 : Real.log 2 ≤ L := by
    rw [hL]; exact Real.log_le_log (by norm_num) (by linarith)
  have hLhalf : 1 / 2 < L := by have := Real.log_two_gt_d9; linarith
  have hL0 : 0 < L := by linarith
  have hAL0 : 0 < 20 * A * L := mul_pos (mul_pos (by norm_num) hA0) hL0
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 1 / (20 * A * L) := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; exact one_div_pos.mpr hAL0
  have hE : 20 * A * L * e = 1 := by rw [he]; exact mul_one_div_cancel hAL0.ne'
  have hAL : A * L = 3 * |C| * L + 2 * C' * L + L := by rw [hA]; ring
  have hAL10 : 10 ≤ 20 * A * L := by nlinarith
  have he10 : e ≤ 1 / 10 := by
    have := mul_le_mul_of_nonneg_left hAL10 he0.le
    linarith
  have hreg : ∀ β : ℝ, InRegion (1 / (20 * A)) q (β : ℂ) → 1 - e ≤ β := by
    intro β hr
    simp only [InRegion, Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add] at hr
    have : 1 / (20 * A) / Real.log ((q : ℝ) * 2) = e := by rw [he, hL, div_div]
    linarith
  have hσ : (1 : ℝ) < 1 + 2 * e := by linarith
  have hσ6 : 1 + 2 * e ≤ 6 / 5 := by linarith
  have hβlt : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β < 1 := by
    intro χ hχ β hz
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using not_lt.mp h) hz
  have hbound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      InRegion (1 / (20 * A)) q (β : ℂ) → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      (negLD χ ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L - 20 * A * L / 3 := by
    intro χ hχ β hr hz
    have hb1 := hβlt χ hχ β hz
    have hb0 := hreg β hr
    obtain ⟨Z, m, hZ, hm, -, hb⟩ := hC q χ hχ 0
    have key := re_negLogDeriv_le_of_real_zero C χ hχ Z m hZ hm β (1 + 2 * e) hσ
      (by linarith) (by linarith) hb1 hz (hb (1 + 2 * e) hσ hσ6)
    rw [← hL] at key
    have h3 : 1 / (3 * e) = 20 * A * L / 3 := by
      rw [div_eq_iff (mul_pos (by norm_num) he0).ne']
      linear_combination -hE
    have hinv : 1 / (3 * e) ≤ 1 / (1 + 2 * e - β) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have h0b : (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ)).re ≤ 10 * A * L + C' := by
    have h := hC' q 1 ((1 + 2 * e : ℝ) : ℂ) (by rw [Complex.ofReal_re]; exact hσ)
    rw [Complex.ofReal_re] at h
    have h2 : 1 / (1 + 2 * e - 1) = 10 * A * L := by
      rw [div_eq_iff (show (0 : ℝ) < 1 + 2 * e - 1 by linarith).ne']
      linear_combination -hE
    rw [h2] at h
    have := Complex.re_le_norm (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ))
    linarith
  have h12ne : χ₁ * χ₂ ≠ 1 := by
    intro h
    apply h12
    calc χ₁ = χ₁ * χ₂ ^ 2 := by rw [h₂, mul_one]
      _ = χ₁ * χ₂ * χ₂ := by rw [pow_two, mul_assoc]
      _ = χ₂ := by rw [h, one_mul]
  have h12b : (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L := by
    obtain ⟨Z, m, hZ, -, -, hb⟩ := hC q (χ₁ * χ₂) h12ne 0
    have hb' := hb (1 + 2 * e) hσ hσ6
    have hs := sum_re_one_div_sub_zero_nonneg (χ₁ * χ₂) h12ne Z m
      (fun ρ hρ => ((hZ ρ).1 hρ).2) (1 + 2 * e) hσ
    have hs0 : (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((1 + 2 * e : ℝ) : ℂ) := by simp
    have hl : (negLD (χ₁ * χ₂) (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)).re =
        (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re := by rw [hs0]
    have h02 : |(0 : ℝ)| + 2 = 2 := by norm_num
    rw [h02, ← hL] at hb'
    linarith
  have hpos := (hPos q (1 + 2 * e) hσ).2.2 χ₁ χ₂ h₁ h₂
  have k1 := hbound χ₁ h₁1 β₁ hr₁ hz₁
  have k2 := hbound χ₂ h₂1 β₂ hr₂ hz₂
  have hCL : C * L ≤ |C| * L := mul_le_mul_of_nonneg_right (le_abs_self C) hL0.le
  have hC'L : C' * (1 / 2) ≤ C' * L := mul_le_mul_of_nonneg_left hLhalf.le hC'0
  have hCL0 : 0 ≤ |C| * L := mul_nonneg (abs_nonneg C) hL0.le
  have hC'L0 : 0 ≤ C' * L := mul_nonneg hC'0 hL0.le
  linarith

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem real_character_apply_sq_eq_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n.Coprime q) : χ (n : ZMod q) * χ (n : ZMod q) = 1 := by
  have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hn
  have h := congrArg (fun f : DirichletCharacter ℂ q => f (n : ZMod q)) hsq
  simp only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply hu] at h
  rw [← sq]
  exact h

theorem product_real_characters_sq_eq_one {q₁ q : ℕ} [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ (q₁ * q)) (h1 : χ₁ ^ 2 = 1) (h2 : χ ^ 2 = 1) (hψ : IsProdChar χ₁ χ ψ) :
    ψ ^ 2 = 1 := by
  ext a
  have hm : (((a : ZMod (q₁ * q)).val : ℕ) : ZMod (q₁ * q)) = a := ZMod.natCast_zmod_val _
  set m := (a : ZMod (q₁ * q)).val with hmdef
  have hcop : m.Coprime (q₁ * q) :=
    (ZMod.isUnit_iff_coprime m (q₁ * q)).mp (by rw [hm]; exact a.isUnit)
  have c1 : m.Coprime q₁ := Nat.Coprime.coprime_dvd_right (dvd_mul_right q₁ q) hcop
  have c2 : m.Coprime q := Nat.Coprime.coprime_dvd_right (dvd_mul_left q q₁) hcop
  rw [MulChar.one_apply_coe, MulChar.pow_apply' ψ two_ne_zero, ← hm, hψ m, mul_pow,
    ← MulChar.pow_apply' χ₁ two_ne_zero, ← MulChar.pow_apply' χ two_ne_zero, h1, h2,
    MulChar.one_apply ((ZMod.isUnit_iff_coprime m q₁).mpr c1),
    MulChar.one_apply ((ZMod.isUnit_iff_coprime m q).mpr c2), one_mul]

theorem agree_coprime_of_product_principal {q₁ q : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ (q₁ * q)) (h2 : χ ^ 2 = 1) (hψ : IsProdChar χ₁ χ ψ) (hψ1 : ψ = 1) :
    ∀ n : ℕ, Nat.Coprime n (q₁ * q) → χ₁ (n : ZMod q₁) = χ (n : ZMod q) := by
  intro n hn
  have hu : IsUnit (n : ZMod (q₁ * q)) := (ZMod.isUnit_iff_coprime n (q₁ * q)).mpr hn
  have e1 : χ₁ (n : ZMod q₁) * χ (n : ZMod q) = 1 := by
    rw [← hψ n, hψ1, MulChar.one_apply hu]
  have e2 := real_character_apply_sq_eq_one χ h2 (Nat.Coprime.coprime_dvd_right (dvd_mul_left q q₁) hn)
  calc χ₁ (n : ZMod q₁) = χ₁ (n : ZMod q₁) * (χ (n : ZMod q) * χ (n : ZMod q)) := by
        rw [e2, mul_one]
    _ = (χ₁ (n : ZMod q₁) * χ (n : ZMod q)) * χ (n : ZMod q) := by ring
    _ = χ (n : ZMod q) := by rw [e1, one_mul]

private theorem two_pow_card_primeFactors_le_self (n : ℕ) (hn : n ≠ 0) : 2 ^ n.primeFactors.card ≤ n := by
  calc 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

private theorem card_primeFactors_add_one_sq_le_rpow {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : n ≠ 0) :
    ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ (2 / (ε * Real.log 2) + 1) ^ 2 * (n : ℝ) ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have h2 : (2 : ℝ) ^ n.primeFactors.card ≤ n := by exact_mod_cast two_pow_card_primeFactors_le_self n hn
  have hcard : (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at this
  have hlog : Real.log n ≤ (n : ℝ) ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div (by linarith) (by linarith)
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < ε / 2)] at hlog
  have hR1 : 1 ≤ (n : ℝ) ^ (ε / 2) := Real.one_le_rpow hn1 (by linarith)
  have hc : (n.primeFactors.card : ℝ) ≤ 2 / (ε * Real.log 2) * (n : ℝ) ^ (ε / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hε hl2)]
    nlinarith [mul_le_mul_of_nonneg_right hcard (by linarith : (0 : ℝ) ≤ ε / 2)]
  have hb : (n.primeFactors.card : ℝ) + 1 ≤ (2 / (ε * Real.log 2) + 1) * (n : ℝ) ^ (ε / 2) := by
    nlinarith
  have h0 : 0 ≤ (n.primeFactors.card : ℝ) + 1 := by positivity
  calc ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ ((2 / (ε * Real.log 2) + 1) * (n : ℝ) ^ (ε / 2)) ^ 2 :=
        pow_le_pow_left₀ h0 hb 2
    _ = (2 / (ε * Real.log 2) + 1) ^ 2 * (n : ℝ) ^ ε := by
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (ε / 2)) 2, ← Real.rpow_mul (by positivity)]
        norm_num

private theorem div_le_mul_of_main_bound_caseA {σ ε C L₁ X Lψ Nk M Q Pc A : ℝ} (hε : 0 < ε) (h1σ : 0 < 1 - σ)
    (hL₁ : 0 < L₁) (hX : 0 ≤ X) (hA : 0 < A) (hNk0 : 0 ≤ Nk) (hLψ0 : 0 ≤ Lψ) (hM0 : 0 ≤ M)
    (hmain : (1 - σ) / 2 ≤ C * (L₁ * X * Lψ) * Nk) (hLψ : Lψ ≤ A * (M / (ε / 2))) (hNk : Nk ≤ M)
    (hMM : M * M = Pc * Q) (hPc : 0 < Pc) :
    (1 - σ) / (2 * max C 1 * L₁ * A * (2 / ε) * Pc) ≤ X * Q := by
  have hCp : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hden : 0 < 2 * max C 1 * L₁ * A * (2 / ε) * Pc :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos two_pos hCp) hL₁) hA) (div_pos two_pos hε)) hPc
  have hLX : 0 ≤ L₁ * X := mul_nonneg hL₁.le hX
  have hp : 0 ≤ L₁ * X * Lψ * Nk := mul_nonneg (mul_nonneg hLX hLψ0) hNk0
  have s1 : C * (L₁ * X * Lψ) * Nk ≤ max C 1 * (L₁ * X * Lψ * Nk) := by
    have := mul_le_mul_of_nonneg_right (le_max_left C 1) hp
    linarith
  have hAM : 0 ≤ A * (M / (ε / 2)) := mul_nonneg hA.le (div_nonneg hM0 (by linarith))
  have s2 : L₁ * X * Lψ * Nk ≤ L₁ * X * (A * (M / (ε / 2))) * M :=
    mul_le_mul (mul_le_mul_of_nonneg_left hLψ hLX) hNk hNk0 (mul_nonneg hLX hAM)
  have s3 := mul_le_mul_of_nonneg_left s2 hCp.le
  have e : max C 1 * (L₁ * X * (A * (M / (ε / 2))) * M) =
      max C 1 * L₁ * A * (2 / ε) * X * (M * M) := by ring
  rw [hMM] at e
  rw [div_le_iff₀ hden]
  linarith

private theorem div_le_mul_of_chain_caseB {L₁ X W D Nε Pc Q : ℝ} (hL₁ : 0 < L₁) (hX : 0 ≤ X) (hD : 0 < D)
    (hPc : 0 < Pc) (hS : L₁ ≤ W * X) (hW : W ≤ D * Nε) (hN : Nε ≤ Pc * Q) :
    L₁ / (D * Pc) ≤ X * Q := by
  rw [div_le_iff₀ (mul_pos hD hPc)]
  calc L₁ ≤ W * X := hS
    _ ≤ D * Nε * X := mul_le_mul_of_nonneg_right hW hX
    _ ≤ D * (Pc * Q) * X := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hD.le) hX
    _ = X * Q * (D * Pc) := by ring

theorem siegel_product_character_inequality (hP : ProdCharExists) (hS : SameCharacterLFunctionOne) {C K CL : ℝ}
    (hKey : ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
      (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)),
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 → IsProdChar χ₁ χ₂ ψ →
      ∀ σ : ℝ, 7 / 8 ≤ σ → σ < 1 →
        1 / 2 - C * ‖lamBq χ₁ χ₂ ψ‖ * ((q₁ * q₂ : ℕ) : ℝ) ^ (K * (1 - σ)) / (1 - σ) ≤ (Fbq χ₁ χ₂ ψ σ).re)
    (hL : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖DirichletCharacter.LFunction χ 1‖ ≤ CL * Real.log (3 * q))
    {ε : ℝ} (hε : 0 < ε) {q₁ : ℕ} [NeZero q₁] (χ₁ : DirichletCharacter ℂ q₁) (h1sq : χ₁ ^ 2 = 1)
    (h1ne : χ₁ ≠ 1) {σ : ℝ} (hσ78 : 7 / 8 ≤ σ) (hσ1 : σ < 1) (hKa : K * (1 - σ) ≤ ε / 2)
    (hneg : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ (q₁ * q)),
      χ ^ 2 = 1 → χ ≠ 1 → ψ ≠ 1 → IsProdChar χ₁ χ ψ → (Fbq χ₁ χ ψ σ).re ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
      c * (q : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  have h1σ : 0 < 1 - σ := by linarith
  have hL₁ : 0 < ‖DirichletCharacter.LFunction χ₁ 1‖ :=
    norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero h1ne)
  have hA : 0 < |CL| + 1 := by positivity
  have hq₁ : (1 : ℝ) ≤ q₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hPc : 0 < ((3 : ℝ) * q₁) ^ ε := Real.rpow_pos_of_pos (by positivity) ε
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hD : 0 < (2 / (ε * Real.log 2) + 1) ^ 2 :=
    pow_pos (by have := div_pos two_pos (mul_pos hε hl2); linarith) 2
  have hCp : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hden : 0 < 2 * max C 1 * ‖DirichletCharacter.LFunction χ₁ 1‖ * (|CL| + 1) * (2 / ε) *
      ((3 : ℝ) * q₁) ^ ε :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos two_pos hCp) hL₁) hA) (div_pos two_pos hε)) hPc
  refine ⟨min ((1 - σ) / (2 * max C 1 * ‖DirichletCharacter.LFunction χ₁ 1‖ * (|CL| + 1) * (2 / ε) *
      ((3 : ℝ) * q₁) ^ ε))
    (‖DirichletCharacter.LFunction χ₁ 1‖ / ((2 / (ε * Real.log 2) + 1) ^ 2 * ((3 : ℝ) * q₁) ^ ε)),
    lt_min (div_pos h1σ hden) (div_pos hL₁ (mul_pos hD hPc)), ?_⟩
  intro q _ χ hsq hne
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hQ : 0 < (q : ℝ) ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.rpow_neg hq0, ← div_eq_mul_inv, div_le_iff₀ hQ]
  have hN : ((q₁ * q : ℕ) : ℝ) = (q₁ : ℝ) * q := by push_cast; ring
  have hN1 : (1 : ℝ) ≤ ((q₁ * q : ℕ) : ℝ) := by rw [hN]; nlinarith
  have hNε : ((q₁ * q : ℕ) : ℝ) ^ ε ≤ ((3 : ℝ) * q₁) ^ ε * (q : ℝ) ^ ε := by
    rw [hN, Real.mul_rpow (by linarith) hq0]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) (by linarith) hε.le) hQ.le
  obtain ⟨ψ, hψ⟩ := hP q₁ q χ₁ χ
  by_cases hψ1 : ψ = 1
  ·
    refine le_trans (min_le_right _ _) ?_
    exact div_le_mul_of_chain_caseB hL₁ (norm_nonneg _) hD hPc
      (hS q₁ q χ₁ χ h1ne hne (agree_coprime_of_product_principal χ₁ χ ψ hsq hψ hψ1))
      (card_primeFactors_add_one_sq_le_rpow hε (q₁ * q) (Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q))) hNε
  ·
    refine le_trans (min_le_left _ _) ?_
    have hk := hKey q₁ q χ₁ χ ψ h1sq hsq h1ne hne hψ1 hψ σ hσ78 hσ1
    have hn := hneg q χ ψ hsq hne hψ1 hψ
    have hmain : (1 - σ) / 2 ≤ C * (‖DirichletCharacter.LFunction χ₁ 1‖ * ‖DirichletCharacter.LFunction χ 1‖ *
        ‖DirichletCharacter.LFunction ψ 1‖) * ((q₁ * q : ℕ) : ℝ) ^ (K * (1 - σ)) := by
      have h2 : 1 / 2 ≤ C * ‖lamBq χ₁ χ ψ‖ * ((q₁ * q : ℕ) : ℝ) ^ (K * (1 - σ)) / (1 - σ) := by linarith
      rw [le_div_iff₀ h1σ] at h2
      have hlam : ‖lamBq χ₁ χ ψ‖ = ‖DirichletCharacter.LFunction χ₁ 1‖ * ‖DirichletCharacter.LFunction χ 1‖ *
          ‖DirichletCharacter.LFunction ψ 1‖ := by simp only [lamBq, norm_mul]
      rw [hlam] at h2
      linarith
    have h3N : (1 : ℝ) ≤ 3 * ((q₁ * q : ℕ) : ℝ) := by linarith
    have hM0 : 0 ≤ (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) := by positivity
    have hlogb : Real.log (3 * ((q₁ * q : ℕ) : ℝ)) ≤ (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) / (ε / 2) :=
      Real.log_le_rpow_div (by linarith) (by linarith)
    have hLψ : ‖DirichletCharacter.LFunction ψ 1‖ ≤
        (|CL| + 1) * ((3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) / (ε / 2)) := by
      calc ‖DirichletCharacter.LFunction ψ 1‖ ≤ CL * Real.log (3 * ((q₁ * q : ℕ) : ℝ)) := hL (q₁ * q) ψ hψ1
        _ ≤ (|CL| + 1) * Real.log (3 * ((q₁ * q : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self CL]) (Real.log_nonneg h3N)
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogb hA.le
    have hNk : ((q₁ * q : ℕ) : ℝ) ^ (K * (1 - σ)) ≤ (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) :=
      (Real.rpow_le_rpow_of_exponent_le hN1 hKa).trans
        (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
    have hMM : (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) * (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) =
        ((3 : ℝ) * q₁) ^ ε * (q : ℝ) ^ ε := by
      rw [← Real.rpow_add (by linarith), add_halves, hN, ← mul_assoc, Real.mul_rpow (by positivity) hq0]
    exact div_le_mul_of_main_bound_caseA hε h1σ hL₁ (norm_nonneg _) hA (by positivity) (norm_nonneg _) hM0
      hmain hLψ hNk hMM hPc

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex
noncomputable section
namespace Formalism.ZeroFreeDirichlet

theorem isProdChar_changeLevel_mul {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    IsProdChar χ₁ χ₂ (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
      DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) := by
  intro n
  rw [MulChar.mul_apply]
  by_cases h : IsUnit (n : ZMod (q₁ * q₂))
  · have h1 : ∀ {q : ℕ} (hq : q ∣ q₁ * q₂) (χ : DirichletCharacter ℂ q),
        DirichletCharacter.changeLevel hq χ (n : ZMod (q₁ * q₂)) = χ (n : ZMod q) := by
      intro q hq χ
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ := χ) hq h.unit
      rw [IsUnit.unit_spec] at this
      rw [this]
      congr 1
      first
        | exact ZMod.cast_natCast hq n
        | exact ZMod.cast_natCast hq _ n
        | exact ZMod.cast_nat_cast hq n
    rw [h1, h1]
  · rw [MulChar.map_nonunit _ h]
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right] at h
    rcases not_and_or.mp h with h' | h'
    · rw [MulChar.map_nonunit χ₁ (by rwa [ZMod.isUnit_iff_coprime])]
      simp
    · rw [MulChar.map_nonunit χ₂ (by rwa [ZMod.isUnit_iff_coprime])]
      simp

theorem exists_product_character : ProdCharExists :=
  fun _ _ χ₁ χ₂ => ⟨_, isProdChar_changeLevel_mul χ₁ χ₂⟩

def characterModFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem characterModFour_apply (a : ZMod 4) :
    characterModFour a = ((ZMod.χ₄ a : ℤ) : ℂ) := rfl

theorem characterModFour_sq : characterModFour ^ 2 = 1 := by
  first
    | exact (ZMod.isQuadratic_χ₄.comp _).sq_eq_one
    | exact (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

theorem characterModFour_ne_one : characterModFour ≠ 1 := by
  intro h
  have hu : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  have h3 := DFunLike.congr_fun h (3 : ZMod 4)
  rw [characterModFour_apply, MulChar.one_apply hu] at h3
  have hv : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [hv] at h3
  norm_num at h3

theorem exists_real_nontrivial_character : RealCharExists :=
  ⟨4, ⟨by norm_num⟩, characterModFour, characterModFour_sq, characterModFour_ne_one⟩

end Formalism.ZeroFreeDirichlet
end
end
