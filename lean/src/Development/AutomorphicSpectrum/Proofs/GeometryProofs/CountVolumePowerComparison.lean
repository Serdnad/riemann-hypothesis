import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

open Filter Topology GlobalTheory.CompHt
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem logCard_pow (x : ℕ∞) (d : ℕ) : logCard (x ^ d) = (d : ℝ≥0∞) * logCard x := by
  unfold logCard
  rw [ENat.toENNReal_pow, ENNReal.log_pow,
    EReal.toENNReal_mul (by positivity : (0 : EReal) ≤ (d : EReal)),
    ← EReal.coe_natCast, EReal.real_coe_toENNReal, ENNReal.ofReal_natCast]

theorem logCard_mono {x y : ℕ∞} (h : x ≤ y) : logCard x ≤ logCard y :=
  EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 h))

theorem sample_power_shift (a D j k : ℕ) (hk : 0 < k) :
    ((a * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1) =
      ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) * ((a * k : ℕ) : ℝ≥0∞) ^ (D + 1) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hj : (0 : ℝ) ≤ 1 + (j : ℝ) / k := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ← ENNReal.ofReal_pow (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  congr 2
  push_cast
  field_simp

theorem tendsto_shift_ratio (D j : ℕ) :
    Tendsto (fun k : ℕ => ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1))) atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => (j : ℝ) / k) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have h' : Tendsto (fun k : ℕ => (1 + (j : ℝ) / k) ^ (D + 1)) atTop (𝓝 ((1 + 0) ^ (D + 1))) :=
    (tendsto_const_nhds.add h).pow _
  simpa using ENNReal.tendsto_ofReal h'

theorem counting_term_le_of_shift_pow (a D n d j k : ℕ) (hd : 0 < d) (hk : 0 < k)
    {x y : ℕ∞} (h : x ≤ y ^ d) :
    (D.factorial : ℝ≥0∞) * logCard x / (((n * d : ℕ) : ℝ≥0∞) * ((a * k : ℕ) : ℝ≥0∞) ^ (D + 1)) ≤
      (D.factorial : ℝ≥0∞) * logCard y / ((n : ℝ≥0∞) * ((a * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1)) *
        ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) := by
  let A : ℝ≥0∞ := ((a * k : ℕ) : ℝ≥0∞) ^ (D + 1)
  let c := ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1))
  let B := (D.factorial : ℝ≥0∞) * logCard y
  have hc : c ≠ 0 := ENNReal.ofReal_pos.2 (by positivity : 0 < (1 + (j : ℝ) / k) ^ (D + 1)) |>.ne'
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcast : ((n * d : ℕ) : ℝ≥0∞) * A = d * ((n : ℝ≥0∞) * A) := by push_cast; ac_rfl
  change (D.factorial : ℝ≥0∞) * logCard x / (((n * d : ℕ) : ℝ≥0∞) * A) ≤
    B / ((n : ℝ≥0∞) * ((a * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1)) * c
  rw [hcast, sample_power_shift _ _ _ _ hk, mul_left_comm (n : ℝ≥0∞) c A]
  have log_le : logCard x ≤ (d : ℝ≥0∞) * logCard y := (logCard_mono h).trans_eq (logCard_pow y d)
  calc
    _ ≤ d * B / (d * ((n : ℝ≥0∞) * A)) := by
      rw [mul_left_comm _ _ (logCard y)]
      exact ENNReal.div_le_div_right (mul_le_mul_right log_le _) _
    _ = B / ((n : ℝ≥0∞) * A) :=
      ENNReal.mul_div_mul_left _ _ (Nat.cast_ne_zero.2 hd.ne') (ENNReal.natCast_ne_top _)
    _ = _ := by
      symm
      rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
      calc
        _ = B * ((n : ℝ≥0∞) * A)⁻¹ * (c⁻¹ * c) := by ac_rfl
        _ = _ := by rw [ENNReal.inv_mul_cancel hc hct, mul_one, ← div_eq_mul_inv]

/-- The counting-volume bound survives any fixed shift along its sampling
progression and any positive power bound on the counts. -/
theorem countVol_le_of_le_shift_pow_stride (D n d a k₀ : ℕ) (m m' : ℕ → ℕ∞)
    (ha : 0 < a) (hd : 0 < d) (hk₀ : a ∣ k₀)
    (h : ∀ᶠ τ : ℕ in atTop, m τ ≤ m' (τ + k₀) ^ d) :
    countVol D (n * d) a m ≤ countVol D n a m' := by
  obtain ⟨j, rfl⟩ := hk₀
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  let b : ℕ → ℝ≥0∞ := fun k => (D.factorial : ℝ≥0∞) * logCard (m' (a * k)) /
    ((n : ℝ≥0∞) * ((a * k : ℕ) : ℝ≥0∞) ^ (D + 1))
  let c : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1))
  have hlim : limsup c atTop = 1 := (tendsto_shift_ratio D j).limsup_eq
  have hle : countVol D (n * d) a m ≤ limsup ((fun k => b (k + j)) * c) atTop := by
    refine limsup_le_limsup ?_
    filter_upwards [eventually_ge_atTop (N + 1)] with k hk
    have hx := hN (a * k) (le_trans (by omega) (Nat.le_mul_of_pos_left k ha))
    rw [← Nat.mul_add] at hx
    exact counting_term_le_of_shift_pow a D n d j k hd (by omega) hx
  refine hle.trans ((ENNReal.limsup_mul_le' (Or.inr (by simp [hlim]))
    (Or.inr (by simp [hlim]))).trans ?_)
  rw [hlim, mul_one, Filter.limsup_nat_add b j]
  rfl

/-- Both real Hilbert–Samuel counts and the extended-real count use the
same normalization after changing the sampling stride. -/
theorem count_term_natCard_at_dilation (D d a k number : ℕ) (hd : 0 < d)
    (ha : 0 < a) (hk : 0 < k) :
    ENNReal.ofReal ((Real.log (number : ℝ) / ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) /
      (((D : ℝ) + 1) * d * (a : ℝ) ^ (D + 1))) =
    ((D.factorial : ℝ≥0∞) * logCard number) /
      ((d : ℝ≥0∞) * ((a * k : ℕ) : ℝ≥0∞) ^ (D + 1)) := by
  rw [logCard_coe, ← ENNReal.ofReal_natCast D.factorial,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_natCast (a * k),
    ← ENNReal.ofReal_pow (Nat.cast_nonneg _), ← ENNReal.ofReal_natCast d, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem logCard_pow_le (x : ℕ∞) {d : ℕ} (hd : 0 < d) :
    GlobalTheory.CompHt.logCard (x ^ d) ≤ (d : ℝ≥0∞) * GlobalTheory.CompHt.logCard x :=
  (logCard_pow x d).le

theorem natCast_shift_pow (D j k : ℕ) (hk : 0 < k) :
    ((8 * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1) =
      ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) * ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1) :=
  sample_power_shift 8 D j k hk

theorem term_le_shift (D n d j k : ℕ) (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) {x y : ℕ∞} (h : x ≤ y ^ d) :
    (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard x / (((n * d : ℕ) : ℝ≥0∞) * ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1)) ≤
      (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard y / ((n : ℝ≥0∞) * ((8 * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1)) *
        ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) :=
  counting_term_le_of_shift_pow 8 D n d j k hd hk h

theorem countVol_le_of_le_shift_pow : ∀ (D n d k₀ : ℕ) (m m' : ℕ → ℕ∞), 0 < n → 0 < d → 8 ∣ k₀ →
    (∀ᶠ τ : ℕ in atTop, m τ ≤ m' (τ + k₀) ^ d) →
    GlobalTheory.CompHt.countVol D (n * d) 8 m ≤ GlobalTheory.CompHt.countVol D n 8 m' :=
  fun D n d k₀ m m' _ hd hk₀ h =>
    countVol_le_of_le_shift_pow_stride D n d 8 k₀ m m' (by decide) hd hk₀ h

end GlobalTheory.CompanionTheory.Ar.Plug
