module

public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.Bundle001
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle008
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle003
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
public import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.LFunctionEqGOfOneLt

@[expose] public section

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma log_le_const_mul_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → Real.log (3 * x) ≤ K * x ^ δ := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨Real.log 3 + 1 / δ, add_pos hl3 (div_pos one_pos hδ), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h1 : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ.le
  have h2 : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ
  have h4 : Real.log 3 ≤ Real.log 3 * x ^ δ := by nlinarith
  have h5 : (Real.log 3 + 1 / δ) * x ^ δ = Real.log 3 * x ^ δ + x ^ δ / δ := by ring
  rw [Real.log_mul (by norm_num) hx0.ne', h5]
  linarith

lemma rpow_neg_eq_inv_pow (x ε : ℝ) (hx : 0 < x) (k : ℕ) (hk : 0 < k) :
    x ^ (-ε) = ((x ^ (ε / k)) ^ k)⁻¹ := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← Real.rpow_mul_natCast hx.le, div_mul_cancel₀ ε hk', Real.rpow_neg hx.le]

theorem exceptional_zero_bound_of : ExcBoundOf := by
  unfold ExcBoundOf ExcBound
  intro hS hL ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨c0, hc0, hS'⟩ := hS (ε / 3) hε3
  obtain ⟨C, hC⟩ := hL
  obtain ⟨K, hK, hKb⟩ := log_le_const_mul_rpow (ε / 3) hε3
  obtain ⟨M, hM, hCM⟩ : ∃ M : ℝ, 0 < M ∧ C ≤ M := ⟨max C 1, lt_max_of_lt_right one_pos, le_max_left _ _⟩
  have hcpos : 0 < min (1 / K) (c0 / (M * K ^ 2)) :=
    lt_min (div_pos one_pos hK) (div_pos hc0 (mul_pos hM (pow_pos hK 2)))
  refine ⟨min (1 / K) (c0 / (M * K ^ 2)), hcpos, ?_⟩
  intro q _ χ β hχ2 hχ1 hβ
  have hcK : min (1 / K) (c0 / (M * K ^ 2)) ≤ 1 / K := min_le_left _ _
  have hc2 : min (1 / K) (c0 / (M * K ^ 2)) ≤ c0 / (M * K ^ 2) := min_le_right _ _
  generalize min (1 / K) (c0 / (M * K ^ 2)) = c at hcpos hcK hc2 ⊢
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hu1 : 1 ≤ (q : ℝ) ^ (ε / 3) := Real.one_le_rpow hq1 hε3.le
  have hqε : (q : ℝ) ^ (-ε) = (((q : ℝ) ^ (ε / 3)) ^ 3)⁻¹ := by
    have h := rpow_neg_eq_inv_pow (q : ℝ) ε hq0 3 (by norm_num)
    simpa using h
  have hq3 : (q : ℝ) ^ (-(ε / 3)) = ((q : ℝ) ^ (ε / 3))⁻¹ := Real.rpow_neg hq0.le _
  have hlogK : Real.log (3 * q) ≤ K * (q : ℝ) ^ (ε / 3) := hKb q hq1
  have hlog_pos : 0 < Real.log (3 * q) := Real.log_pos (by linarith)
  have hβ1 : β < 1 := by
    by_contra hge
    simp only [not_lt] at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simpa using hge) hβ
  have hlow := hS' q χ hχ2 hχ1
  rw [hq3] at hlow
  rw [hqε]
  generalize (q : ℝ) ^ (ε / 3) = u at hu1 hlogK hlow ⊢
  have hu0 : 0 < u := by linarith
  by_cases hcase : β ≤ 1 - 1 / Real.log (3 * q)
  · have key : c * Real.log (3 * q) ≤ u ^ 3 := by
      have hu3 : u ≤ u ^ 3 := le_self_pow₀ hu1 (by norm_num)
      calc c * Real.log (3 * q) ≤ (1 / K) * (K * u) :=
            mul_le_mul hcK hlogK hlog_pos.le (div_pos one_pos hK).le
        _ = u := by field_simp
        _ ≤ u ^ 3 := hu3
    have h1 : c * (u ^ 3)⁻¹ ≤ 1 / Real.log (3 * q) := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hu0 3) hlog_pos, one_mul]
      exact key
    linarith
  · simp only [not_le] at hcase
    have hdiff := DirichletCharacter.differentiable_LFunction hχ1
    have hmvt : ‖(fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) 1 -
        (fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) β‖ ≤
        (C * Real.log (3 * q) ^ 2) * (1 - β) := by
      refine norm_image_sub_le_of_norm_deriv_le_segment'
        (f := fun t : ℝ => DirichletCharacter.LFunction χ (t : ℂ)) (a := β) (b := 1)
        (f' := fun t : ℝ => deriv (DirichletCharacter.LFunction χ) (t : ℂ)) ?_ ?_ 1 ⟨hβ1.le, le_refl _⟩
      · intro t _
        exact ((hdiff (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
      · intro t ht
        exact hC q χ hχ1 t (by linarith [ht.1]) ht.2.le
    simp only [hβ, sub_zero, Complex.ofReal_one] at hmvt
    have h1β : 0 < 1 - β := by linarith
    have hlog2 : Real.log (3 * q) ^ 2 ≤ (K * u) ^ 2 := pow_le_pow_left₀ hlog_pos.le hlogK 2
    have hCle : C * Real.log (3 * q) ^ 2 ≤ M * (K * u) ^ 2 :=
      mul_le_mul hCM hlog2 (sq_nonneg _) hM.le
    have hmain : c0 * u⁻¹ ≤ M * (K * u) ^ 2 * (1 - β) :=
      le_trans hlow (le_trans hmvt (mul_le_mul_of_nonneg_right hCle h1β.le))
    have hc0' : c0 ≤ M * K ^ 2 * u ^ 3 * (1 - β) := by
      have h := mul_le_mul_of_nonneg_right hmain hu0.le
      have e1 : c0 * u⁻¹ * u = c0 := by field_simp
      have e2 : M * (K * u) ^ 2 * (1 - β) * u = M * K ^ 2 * u ^ 3 * (1 - β) := by ring
      linarith
    have hMKu : 0 < M * K ^ 2 * u ^ 3 := mul_pos (mul_pos hM (pow_pos hK 2)) (pow_pos hu0 3)
    have hfin : c * (u ^ 3)⁻¹ ≤ 1 - β := by
      calc c * (u ^ 3)⁻¹ ≤ c0 / (M * K ^ 2) * (u ^ 3)⁻¹ :=
            mul_le_mul_of_nonneg_right hc2 (inv_nonneg.2 (pow_pos hu0 3).le)
        _ = c0 / (M * K ^ 2 * u ^ 3) := by field_simp
        _ ≤ 1 - β := by
          rw [div_le_iff₀ hMKu]
          linarith
    linarith

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex Finset

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma three_le_modulus_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : 3 ≤ q := by
  by_contra h
  push_neg at h
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  interval_cases q
  all_goals
    apply hχ
    ext a
    have ha : a = 1 := by revert a; decide
    rw [ha]
    simp

lemma two_le_log_three_mul (q : ℕ) (hq : 3 ≤ q) : 2 ≤ Real.log (3 * q) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; try norm_num
  rw [Real.le_log_iff_exp_le (by positivity), e2]
  nlinarith

private lemma rpow_le_exp_three_halves_of_le_log (q : ℕ) (hq : 3 ≤ q) (x t : ℝ) (hx : 1 ≤ x) (hxq : x ≤ 3 * q)
    (ht : t ≤ 3 / (2 * Real.log (3 * q))) : x ^ t ≤ Real.exp (3 / 2) := by
  have hL : 2 ≤ Real.log (3 * q) := two_le_log_three_mul q hq
  have hLpos : 0 < Real.log (3 * q) := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlxL : Real.log x ≤ Real.log (3 * q) := Real.log_le_log hx0 hxq
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.2
  have h1 : Real.log x * t ≤ Real.log x * (3 / (2 * Real.log (3 * q))) := mul_le_mul_of_nonneg_left ht hlx
  have h2 : Real.log x * (3 / (2 * Real.log (3 * q))) ≤ Real.log (3 * q) * (3 / (2 * Real.log (3 * q))) :=
    mul_le_mul_of_nonneg_right hlxL (by positivity)
  have h3 : Real.log (3 * q) * (3 / (2 * Real.log (3 * q))) = 3 / 2 := by field_simp; try ring
  linarith

lemma rpow_neg_le_exp_inv_near_one (q : ℕ) (hq : 3 ≤ q) (x : ℝ) (hx : 1 ≤ x) (hxq : x ≤ q) (r : ℝ)
    (hr : 1 - 3 / (2 * Real.log (3 * q)) ≤ r) :
    x ^ (-r) ≤ Real.exp (3 / 2) * x⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hqR : (0 : ℝ) ≤ q := by positivity
  have e : x ^ (-r) = x ^ (1 - r) * x⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]
    congr 1
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (rpow_le_exp_three_halves_of_le_log q hq x (1 - r) hx (by linarith) (by linarith))
    (inv_nonneg.2 hx0.le)

lemma partial_sum_norm_le_near_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (w : ℂ)
    (hw : 1 - 3 / (2 * Real.log (3 * q)) ≤ w.re) :
    ‖∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-w)‖ ≤ Real.exp (3 / 2) * (1 + Real.log (3 * q)) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Icc 1 q, ‖χ (n : ZMod q) * (n : ℂ) ^ (-w)‖ ≤ Real.exp (3 / 2) * (n : ℝ)⁻¹ := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    have hχn : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hr := rpow_neg_le_exp_inv_near_one q hq n (by exact_mod_cast h1) (by exact_mod_cast h2) w.re hw
    calc ‖χ (n : ZMod q)‖ * (n : ℝ) ^ (-w.re) ≤ 1 * (Real.exp (3 / 2) * (n : ℝ)⁻¹) :=
          mul_le_mul hχn hr (by positivity) zero_le_one
      _ = _ := one_mul _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hH : ∑ n ∈ Icc 1 q, ((n : ℝ))⁻¹ = (harmonic q : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [hH]
  refine (harmonic_le_one_add_log q).trans ?_
  have : Real.log q ≤ Real.log (3 * q) := Real.log_le_log (by positivity) (by linarith)
  linarith

lemma lfunction_norm_le_near_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (w : ℂ)
    (hw : 1 - 3 / (2 * Real.log (3 * q)) ≤ w.re) (hw4 : 1 / 4 ≤ w.re) (hw2 : ‖w‖ ≤ 2) :
    ‖DirichletCharacter.LFunction χ w‖ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) := by
  have hq := three_le_modulus_of_ne_one χ hχ
  have hL := two_le_log_three_mul q hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hre0 : 0 < w.re := by linarith
  have hB : ∀ M, ‖Formalism.FX.LFunctionPartialSum.Ap χ M‖ ≤ (q : ℝ) + 1 := fun M => norm_character_sum_Icc_le χ hχ M
  have hpos : (0 : ℝ) < (q : ℝ) + 1 := by linarith
  have hx1 : (1 : ℝ) ≤ (q : ℝ) + 1 := by linarith
  have hx3 : (q : ℝ) + 1 ≤ 3 * q := by linarith
  have hpow : ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re) ≤ Real.exp (3 / 2) := by
    have := rpow_le_exp_three_halves_of_le_log q hq ((q : ℝ) + 1) (1 - w.re) hx1 hx3 (by linarith)
    rwa [sub_eq_add_neg, Real.rpow_add hpos, Real.rpow_one] at this
  rw [Formalism.FX.LFunctionPartialSum.LFunction_eq_G (χ := χ) hχ hB hre0]
  unfold Formalism.FX.LFunctionPartialSum.G
  rw [← Summable.sum_add_tsum_nat_add (q + 1) (Formalism.FX.LFunctionPartialSum.summable_dterm (χ := χ) hB hre0),
    eq_sub_of_add_eq (Formalism.FX.LFunctionPartialSum.partial_identity (χ := χ) w q)]
  have h1 := partial_sum_norm_le_near_one χ hq w hw
  have h2 : ‖Formalism.FX.LFunctionPartialSum.Ap χ q * ((q : ℂ) + 1) ^ (-w)‖ ≤ Real.exp (3 / 2) := by
    rw [norm_mul]
    have e : ((q : ℂ) + 1) = ((q + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    push_cast
    calc ‖Formalism.FX.LFunctionPartialSum.Ap χ q‖ * ((q : ℝ) + 1) ^ (-w.re) ≤ ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re) :=
          mul_le_mul_of_nonneg_right (hB q) (by positivity)
      _ ≤ _ := hpow
  have h3 : ‖∑' i, Formalism.FX.LFunctionPartialSum.dterm χ w (i + (q + 1))‖ ≤ 8 * Real.exp (3 / 2) := by
    refine (Formalism.FX.LFunctionPartialSum.norm_tail_le χ hB hre0 q).trans ?_
    have hw' : ‖w‖ / w.re ≤ 8 := by rw [div_le_iff₀ hre0]; linarith
    calc ((q : ℝ) + 1) * (‖w‖ / w.re) * ((q : ℝ) + 1) ^ (-w.re)
        = (‖w‖ / w.re) * (((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re)) := by ring
      _ ≤ 8 * Real.exp (3 / 2) := mul_le_mul hw' hpow (by positivity) (by norm_num)
  have hsub := norm_sub_le (∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-w)) (Formalism.FX.LFunctionPartialSum.Ap χ q * ((q : ℂ) + 1) ^ (-w))
  refine (norm_add_le _ _).trans ?_
  have he := Real.exp_pos (3 / 2)
  have hk := mul_le_mul_of_nonneg_left (show 10 + Real.log (3 * q) ≤ 38 * Real.log (3 * q) by linarith) he.le
  nlinarith

theorem lfunction_deriv_near_one : LDerivNearOne := by
  refine ⟨76 * Real.exp (3 / 2), fun q _ χ hχ σ hσ1 hσ2 => ?_⟩
  have hq := three_le_modulus_of_ne_one χ hχ
  have hL := two_le_log_three_mul q hq
  have hLpos : 0 < Real.log (3 * q) := by linarith
  have hρ : 0 < 1 / (2 * Real.log (3 * q)) := by positivity
  have hd : DiffContOnCl ℂ (DirichletCharacter.LFunction χ) (Metric.ball (σ : ℂ) (1 / (2 * Real.log (3 * q)))) :=
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
  have hC : ∀ z ∈ Metric.sphere (σ : ℂ) (1 / (2 * Real.log (3 * q))),
      ‖DirichletCharacter.LFunction χ z‖ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hre : |(z - σ).re| ≤ 1 / (2 * Real.log (3 * q)) := by rw [← hz]; exact Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    have h1 : 1 / Real.log (3 * q) ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    have h2 : 1 / (2 * Real.log (3 * q)) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
    have e3 : 3 / (2 * Real.log (3 * q)) = 1 / Real.log (3 * q) + 1 / (2 * Real.log (3 * q)) := by
      field_simp
      try ring
    have hab := abs_le.1 hre
    apply lfunction_norm_le_near_one χ hχ z
    · rw [e3]; linarith
    · linarith
    · calc ‖z‖ = ‖(z - σ) + σ‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - σ‖ + ‖(σ : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 / 4 + 1 := by
          rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith
        _ ≤ 2 := by norm_num
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd hC
  calc _ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) / (1 / (2 * Real.log (3 * q))) := this
    _ = 76 * Real.exp (3 / 2) * Real.log (3 * q) ^ 2 := by field_simp; try ring

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma landau_lemma_lfunction_zeros (hLL : LandauLocal3) {C : ℝ}
    (hC : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖))
    (hInv : LInvBound) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hσ1 : 26 / 27 ≤ s.re) (hσ2 : s.re < 11 / 10) (hfs : DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall ((21 / 20 : ℂ) + s.im * I) (11 / 20 / 3) ∧
        DirichletCharacter.LFunction χ ρ = 0)) ∧
      (∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m ρ = 1) ∧
      (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
        Real.log ((q : ℝ) * (|s.im| + 2)) / Real.log 2 ∧
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
          Real.log ((q : ℝ) * (|s.im| + 2))) := by
  set z₀ : ℂ := (21 / 20 : ℂ) + s.im * I with hz₀
  have hz₀re : z₀.re = 21 / 20 := by simp [hz₀]
  set A : ℝ := 21 * (|C| + 1) with hAdef
  have hq1 := one_le_modulus_real q
  have hX : (0 : ℝ) < (q : ℝ) * (|s.im| + 2) := by positivity
  set M : ℝ := 2 * A * ((q : ℝ) * (|s.im| + 2)) with hMdef
  have hA1 : 1 ≤ A := by
    have := abs_nonneg C
    rw [hAdef]
    nlinarith
  have hM1 : 1 ≤ M := by
    have h2 : 2 ≤ (q : ℝ) * (|s.im| + 2) := by nlinarith [abs_nonneg s.im]
    rw [hMdef]
    nlinarith
  have hf0 : DirichletCharacter.LFunction χ z₀ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hz₀re]; norm_num)
  have hinv := hInv q χ z₀ (by rw [hz₀re]; norm_num)
  rw [hz₀re] at hinv
  have h21 : ‖DirichletCharacter.LFunction χ z₀‖⁻¹ ≤ 21 := by
    have e : (21 / 20 : ℝ) / (21 / 20 - 1) = 21 := by norm_num
    linarith
  have hlow : 1 ≤ 21 * ‖DirichletCharacter.LFunction χ z₀‖ := by
    have hp : 0 < ‖DirichletCharacter.LFunction χ z₀‖ := norm_pos_iff.2 hf0
    have := mul_le_mul_of_nonneg_right h21 hp.le
    rwa [inv_mul_cancel₀ hp.ne'] at this
  have hbound : ∀ z ∈ Metric.closedBall z₀ (11 / 20),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := by
    intro z hz
    have hre := re_ge_of_mem_closedBall hz
    rw [hz₀re] at hre
    have h1 := hC q χ hχ z (by linarith)
    have hn := norm_le_norm_add_of_mem_closedBall' hz
    have hn0 := norm_disc_center_le s.im
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hz1 : 1 + ‖z‖ ≤ 2 * (|s.im| + 2) := by linarith [abs_nonneg s.im]
    have hY : 0 ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) := by positivity
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ C * q * (1 + ‖z‖) := h1
      _ ≤ |C| * q * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hq0)
            (by positivity)
      _ ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hq0) hz1 (by positivity)
          positivity
      _ = (|C| + 1) * q * (2 * (|s.im| + 2)) * 1 := by ring
      _ ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) * (21 * ‖DirichletCharacter.LFunction χ z₀‖) :=
          mul_le_mul_of_nonneg_left hlow hY
      _ = M * ‖DirichletCharacter.LFunction χ z₀‖ := by
          rw [hMdef, hAdef]
          ring
  obtain ⟨Z, m, hZ, -, -, hm1, hsum, hder⟩ := hLL (DirichletCharacter.LFunction χ) z₀ (11 / 20) M
    (by norm_num) hM1 (DirichletCharacter.differentiable_LFunction hχ).differentiableOn hf0 hbound
  have hlogM : Real.log M ≤ (Real.log (2 * A) / Real.log 2 + 1) * Real.log ((q : ℝ) * (|s.im| + 2)) :=
    log_le_of_le_exp_log_conductor hA1 hM1 (log_two_le_log_analytic_conductor q s.im) (Real.exp_pos _)
      (by rw [Real.exp_log hX, hMdef])
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Z, m, hZ, hm1, ?_, ?_⟩
  · push_cast at hsum
    calc ∑ ρ ∈ Z, (m ρ : ℝ) ≤ Real.log M / Real.log 2 := hsum
      _ ≤ _ := div_le_div_of_nonneg_right hlogM hl2.le
  · have hs6 : s ∈ Metric.closedBall z₀ (11 / 20 / 6) := by
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have e : s - z₀ = ((s.re - 21 / 20 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hz₀]
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc _ ≤ 72 * Real.log M / (11 / 20) := hder s hs6 hfs
      _ = 1440 / 11 * Real.log M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogM (by norm_num)

end Formalism.ZeroFreeDirichlet
end
end
