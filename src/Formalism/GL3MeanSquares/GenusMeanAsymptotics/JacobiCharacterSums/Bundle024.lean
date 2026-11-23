module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle015
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower
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
import Mathlib.NumberTheory.LSeries.Nonvanishing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma sharp_zero_term {ρ : ℂ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re < 1) {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖((y * ((1 + δ) / δ) : ℝ) : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ‖ ≤ 2 * δ * y * y ^ (ρ.re - 1) := by
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at h1; norm_num at h1
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h2; norm_num at h2
  have hs : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hpow : (y : ℂ) ^ ρ = (y : ℂ) * (y : ℂ) ^ (ρ - 1) := by
    rw [Complex.cpow_sub _ _ hyc, Complex.cpow_one]; field_simp
  have e : ((y * ((1 + δ) / δ) : ℝ) : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ =
      (y : ℂ) ^ ρ / ρ *
        ((((1 + δ) / δ : ℝ) : ℂ) * ((((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) - 1) := by
    rw [Complex.ofReal_mul (1 + δ) y, Complex.mul_cpow_ofReal_nonneg (by linarith) hy.le, hpow]
    generalize ((1 + δ : ℝ) : ℂ) ^ (ρ - 1) = a
    generalize (y : ℂ) ^ (ρ - 1) = b
    push_cast
    field_simp
  rw [e, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hk := sharp_kernel hρ0 hρ1 h2.le hδ hδ2
  have hn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  have hr : y ^ ρ.re = y * y ^ (ρ.re - 1) := by
    rw [Real.rpow_sub_one hy.ne']; field_simp
  calc y ^ ρ.re / ‖ρ‖ * _ ≤ y ^ ρ.re / ‖ρ‖ * (2 * δ * ‖ρ‖) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
    _ = 2 * δ * y * y ^ (ρ.re - 1) := by rw [hr]; field_simp

lemma sharp_log_term {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ) :
    |y * ((1 + δ) / δ) * ((Real.log ((1 + δ) * y) - 1) - (Real.log y - 1)) - y| ≤ δ * y := by
  have h1 : (0 : ℝ) < 1 + δ := by linarith
  rw [Real.log_mul h1.ne' hy.ne']
  have hup : Real.log (1 + δ) ≤ δ := by
    have := Real.log_le_sub_one_of_pos h1; linarith
  have hlo : δ / (1 + δ) ≤ Real.log (1 + δ) := by
    have := Real.one_sub_inv_le_log_of_pos h1
    have e : 1 - (1 + δ)⁻¹ = δ / (1 + δ) := by field_simp; ring
    linarith
  have e : y * ((1 + δ) / δ) * ((Real.log (1 + δ) + Real.log y - 1) - (Real.log y - 1)) - y =
      y * ((1 + δ) / δ * Real.log (1 + δ) - 1) := by ring
  rw [e, abs_mul, abs_of_pos hy, mul_comm δ y]
  refine mul_le_mul_of_nonneg_left ?_ hy.le
  have hc : 0 < (1 + δ) / δ := by positivity
  rw [abs_le]
  constructor
  · have : (1 + δ) / δ * (δ / (1 + δ)) ≤ (1 + δ) / δ * Real.log (1 + δ) :=
      mul_le_mul_of_nonneg_left hlo hc.le
    have e2 : (1 + δ) / δ * (δ / (1 + δ)) = 1 := by field_simp
    linarith
  · have : (1 + δ) / δ * Real.log (1 + δ) ≤ (1 + δ) / δ * δ := mul_le_mul_of_nonneg_left hup hc.le
    have e2 : (1 + δ) / δ * δ = 1 + δ := by field_simp
    linarith

theorem differenced_explicit_formula : SharpenS := by
  intro M _ χ Z m K E y δ hZ hy hδ hδ2 hE
  have hy0 : 0 < y := by linarith
  have hEu := hE ((1 + δ) * y) (Or.inr rfl)
  have hEy := hE y (Or.inl rfl)
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hEy
  have huy : y < (1 + δ) * y := by nlinarith
  have hR := sharp_arith χ (by linarith : (1 : ℝ) ≤ y) huy
  have hc : y * ((1 + δ) * y) / ((1 + δ) * y - y) = y * ((1 + δ) / δ) := by
    have : (1 + δ) * y - y = δ * y := by ring
    rw [this]; field_simp
  rw [hc] at hR
  set c : ℝ := y * ((1 + δ) / δ) with hcdef
  have hc0 : 0 < c := by positivity
  have hcle : c ≤ 3 / 2 * y / δ := by
    rw [hcdef, show y * ((1 + δ) / δ) = (1 + δ) * y / δ by ring]
    exact div_le_div_of_nonneg_right (by nlinarith) hδ.le
  set T : ℂ → ℂ := fun ρ => (c : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ with hT
  have hsum : ∑ ρ ∈ Z, (m ρ : ℂ) * T ρ =
      (c : ℂ) * (∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
        ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [hT]; ring
  have hTb : ‖∑ ρ ∈ Z, (m ρ : ℂ) * T ρ‖ ≤ 2 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) := by
    rw [Finset.mul_sum]
    refine norm_sum_le_of_le _ fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_natCast]
    have := sharp_zero_term (hZ ρ hρ).1 (hZ ρ hρ).2 hy0 hδ hδ2
    calc (m ρ : ℝ) * ‖T ρ‖ ≤ (m ρ : ℝ) * (2 * δ * y * y ^ (ρ.re - 1)) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = 2 * δ * y * ((m ρ : ℝ) * y ^ (ρ.re - 1)) := by ring
  have hS0 : 0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) :=
    Finset.sum_nonneg fun ρ _ => by positivity
  have hP : ‖(c : ℂ) * ((if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) -
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0)) - (if χ = 1 then (y : ℂ) else 0)‖ ≤ δ * y := by
    by_cases hχ : χ = 1
    · simp only [hχ, if_true]
      rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      exact sharp_log_term hy0 hδ
    · simp only [hχ, if_false]
      simp; positivity
  have hlog1 : 1 ≤ Real.log (2 * y) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogu : Real.log ((1 + δ) * y) ≤ Real.log (2 * y) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hD : ‖(c : ℂ) * ((Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - K -
        (if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) +
          ∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
      (Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - K - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))))‖ ≤ c * (2 * E) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) hc0.le
    linarith
  have key : psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ =
      (c : ℂ) * ((Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - K -
        (if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) +
          ∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
      (Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - K - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))))
      - ((c : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y)
      + ((c : ℂ) * ((if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) -
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0)) - (if χ = 1 then (y : ℂ) else 0))
      - ∑ ρ ∈ Z, (m ρ : ℂ) * T ρ := by
    rw [hsum]; ring
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add hD hR)) hP)) hTb).trans ?_
  have b1 : c * (2 * E) ≤ 4 * y * E / δ := by
    calc c * (2 * E) ≤ 3 / 2 * y / δ * (2 * E) := mul_le_mul_of_nonneg_right hcle (by positivity)
      _ = 3 * y * E / δ := by ring
      _ ≤ 4 * y * E / δ := div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hy0.le hE0]) hδ.le
  have hdy : 0 < δ * y := by positivity
  have b2 : ((1 + δ) * y - y + 1) * Real.log ((1 + δ) * y) ≤ (δ * y + 1) * Real.log (2 * y) := by
    rw [show (1 + δ) * y - y + 1 = δ * y + 1 by ring]
    exact mul_le_mul_of_nonneg_left hlogu (by positivity)
  have b3 : δ * y ≤ (δ * y + 1) * Real.log (2 * y) := by nlinarith
  have b4 : 2 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) ≤
      20 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hS0
  have b5 : 0 ≤ (δ * y + 1) * Real.log (2 * y) := by positivity
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem cZ_pos : 0 < cZ :=
  lt_min (Classical.choose_spec Formalism.ZeroFreeDirichlet.zFRDirichlet).1 (by norm_num)

theorem cZ_le : cZ ≤ 1 / 20 :=
  min_le_right _ _

theorem inRegion_mono {c c' : ℝ} (hc : c ≤ c') (q : ℕ) [NeZero q] (s : ℂ) (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at hs ⊢
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_pos (by nlinarith [abs_nonneg s.im])
  have h1 : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c' / Real.log ((q : ℝ) * (|s.im| + 2)) :=
    div_le_div_of_nonneg_right hc hlog.le
  linarith

theorem zfr_cZ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : InRegion cZ q s)
    (hz : IsLZero χ s) :
    χ ^ 2 = 1 ∧ χ ≠ 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
      ∀ (χ' : DirichletCharacter ℂ q) (s' : ℂ), InRegion cZ q s' → IsLZero χ' s' → χ' = χ ∧ s' = s := by
  have hZ := Classical.choose_spec Formalism.ZeroFreeDirichlet.zFRDirichlet
  have hle : cZ ≤ Classical.choose Formalism.ZeroFreeDirichlet.zFRDirichlet := min_le_left _ _
  obtain ⟨h1, h2, h3, h4, h5⟩ := hZ.2 q χ s (inRegion_mono hle q s hs) hz
  exact ⟨h1, h2, h3, h4, fun χ' s' hs' hz' => h5 χ' s' (inRegion_mono hle q s' hs') hz'⟩

theorem eOf_cases (M : ℕ) [NeZero M] :
    (∃ p : DirichletCharacter ℂ M × ℝ, eOf M = some p ∧ IsExcPair p.1 p.2 ∧ InRegion cZ M (p.2 : ℂ)) ∨
    (∃ p : DirichletCharacter ℂ M × ℝ, eOf M = some p ∧ IsExcPair p.1 p.2 ∧
      ∀ p' : DirichletCharacter ℂ M × ℝ, IsExcPair p'.1 p'.2 → ¬ InRegion cZ M (p'.2 : ℂ)) ∨
    (eOf M = none ∧ ∀ p' : DirichletCharacter ℂ M × ℝ, ¬ IsExcPair p'.1 p'.2) := by
  unfold eOf
  split_ifs with h h'
  · exact Or.inl ⟨h.choose, rfl, h.choose_spec.1, h.choose_spec.2⟩
  · exact Or.inr (Or.inl ⟨h'.choose, rfl, h'.choose_spec, fun p' hp' hr => h ⟨p', hp', hr⟩⟩)
  · exact Or.inr (Or.inr ⟨rfl, fun p' hp' => h' ⟨p', hp'⟩⟩)

theorem eOf_exc (M : ℕ) [NeZero M] (p : DirichletCharacter ℂ M × ℝ) (h : eOf M = some p) :
    IsExcPair p.1 p.2 := by
  rcases eOf_cases M with ⟨q, hq, hex, _⟩ | ⟨q, hq, hex, _⟩ | ⟨hn, _⟩
  · rw [h] at hq
    cases hq
    exact hex
  · rw [h] at hq
    cases hq
    exact hex
  · rw [h] at hn
    cases hn

theorem eOf_none (M : ℕ) [NeZero M] (h : eOf M = none) (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) :
    ¬ IsExcPair χ₁ β₁ := by
  rcases eOf_cases M with ⟨q, hq, _, _⟩ | ⟨q, hq, _, _⟩ | ⟨_, hno⟩
  · rw [h] at hq
    cases hq
  · rw [h] at hq
    cases hq
  · exact hno (χ₁, β₁)

theorem inRegion_ofReal (c : ℝ) (q : ℕ) (β : ℝ) :
    InRegion c q (β : ℂ) ↔ 1 - c / Real.log ((q : ℝ) * 2) ≤ β := by
  unfold InRegion
  rw [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add]

theorem log_two_mul_le (M : ℕ) (hM : 2 ≤ M) : Real.log ((M : ℝ) * 2) ≤ 2 * Real.log M := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.log_mul (by positivity) (by norm_num)]
  have h1 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM'
  linarith

theorem log_pos_of_two_le (M : ℕ) (hM : 2 ≤ M) : 0 < Real.log M := by
  apply Real.log_pos
  exact_mod_cast (show 1 < M by omega)

theorem isExcPair_of_region (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (β : ℝ)
    (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1) (hz : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hr : InRegion cZ M (β : ℂ)) : IsExcPair χ β := by
  refine ⟨h2, h1, hz, ?_, ?_⟩
  · rw [inRegion_ofReal] at hr
    have hlogM := log_pos_of_two_le M hM
    have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hlogge : Real.log M ≤ Real.log ((M : ℝ) * 2) := Real.log_le_log (by positivity) (by nlinarith)
    have hcz := cZ_le
    have hcz0 := cZ_pos
    have hlog2pos : 0 < Real.log ((M : ℝ) * 2) := lt_of_lt_of_le hlogM hlogge
    have h3 : cZ / Real.log ((M : ℝ) * 2) < 1 / (8 * Real.log M) := by
      rw [div_lt_div_iff₀ hlog2pos (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hcz hlogM.le]
    linarith
  · by_contra hge
    push_neg at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl h1) (by simpa using hge) hz

theorem zero_in_region (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (s : ℂ)
    (hs : InRegion cZ M s) (hz : IsLZero χ s) :
    ∃ β₁ : ℝ, eOf M = some (χ, β₁) ∧ s = (β₁ : ℂ) ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨h2, h1, him, hder, huniq⟩ := zfr_cZ M χ s hs hz
  have hs' : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hzr : DirichletCharacter.LFunction χ ((s.re : ℝ) : ℂ) = 0 := by rw [← hs']; exact hz.2
  have hrr : InRegion cZ M ((s.re : ℝ) : ℂ) := by rw [← hs']; exact hs
  have hex : IsExcPair χ s.re := isExcPair_of_region M hM χ s.re h2 h1 hzr hrr
  rcases eOf_cases M with ⟨p, hp, hpex, hpr⟩ | ⟨p, hp, hpex, hno⟩ | ⟨hn, hno⟩
  · have hz' : IsLZero p.1 (p.2 : ℂ) := ⟨Or.inl hpex.2.1, hpex.2.2.1⟩
    obtain ⟨e1, e2⟩ := huniq p.1 (p.2 : ℂ) hpr hz'
    refine ⟨p.2, ?_, e2.symm, hder⟩
    rw [hp, ← e1]
  · exact absurd hrr (hno (χ, s.re) hex)
  · exact absurd hex (hno (χ, s.re))

theorem etaOf_some (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) (h : eOf M = some (χ₁, β₁)) :
    etaOf M = min 1 ((1 - β₁) * Real.log M) := by
  unfold etaOf
  rw [h]

theorem etaOf_none (M : ℕ) [NeZero M] (h : eOf M = none) : etaOf M = 1 := by
  unfold etaOf
  rw [h]

theorem etaOf_pos (M : ℕ) [NeZero M] (hM : 2 ≤ M) : 0 < etaOf M := by
  rcases hE : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [etaOf_none M hE]
    exact one_pos
  · rw [etaOf_some M χ₁ β₁ hE]
    have hex := eOf_exc M (χ₁, β₁) hE
    exact lt_min one_pos (mul_pos (by linarith [hex.2.2.2.2]) (log_pos_of_two_le M hM))

theorem etaOf_le_one (M : ℕ) [NeZero M] : etaOf M ≤ 1 := by
  rcases hE : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [etaOf_none M hE]
  · rw [etaOf_some M χ₁ β₁ hE]
    exact min_le_left _ _

theorem etaOf_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → c * (M : ℝ) ^ (-ε) ≤ etaOf M := by
  obtain ⟨c, hc, hb⟩ := Formalism.ZeroFreeDirichlet.excBound ε hε
  refine ⟨min 1 (c * Real.log 3), lt_min one_pos (mul_pos hc (Real.log_pos (by norm_num))), fun M _ hM => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hpow : (M : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM1 (by linarith)
  have hpow0 : 0 < (M : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hle1 : min 1 (c * Real.log 3) * (M : ℝ) ^ (-ε) ≤ 1 := by
    calc min 1 (c * Real.log 3) * (M : ℝ) ^ (-ε) ≤ 1 * 1 :=
          mul_le_mul (min_le_left _ _) hpow hpow0.le zero_le_one
      _ = 1 := one_mul 1
  rcases hE : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [etaOf_none M hE]
    exact hle1
  · rw [etaOf_some M χ₁ β₁ hE]
    have hex := eOf_exc M (χ₁, β₁) hE
    have hβ := hb M χ₁ β₁ hex.1 hex.2.1 hex.2.2.1
    have hlog3 : Real.log 3 ≤ Real.log M := Real.log_le_log (by norm_num) (by exact_mod_cast hM)
    have hlogM : 0 ≤ Real.log M := le_trans (Real.log_nonneg (by norm_num)) hlog3
    have h1 : c * (M : ℝ) ^ (-ε) ≤ 1 - β₁ := by linarith
    apply le_min hle1
    calc min 1 (c * Real.log 3) * (M : ℝ) ^ (-ε) ≤ (c * Real.log 3) * (M : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hpow0.le
      _ ≤ (c * Real.log M) * (M : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog3 hc.le) hpow0.le
      _ = (c * (M : ℝ) ^ (-ε)) * Real.log M := by ring
      _ ≤ (1 - β₁) * Real.log M := mul_le_mul_of_nonneg_right h1 hlogM

theorem etaOf_far (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ)
    (h : eOf M = some (χ₁, β₁)) (hr : ¬ InRegion cZ M (β₁ : ℂ)) : cZ / 2 ≤ etaOf M := by
  rw [etaOf_some M χ₁ β₁ h]
  rw [inRegion_ofReal] at hr
  push_neg at hr
  have hlogM := log_pos_of_two_le M hM
  have hlog2 := log_two_mul_le M hM
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogge : Real.log M ≤ Real.log ((M : ℝ) * 2) := Real.log_le_log (by positivity) (by nlinarith)
  have hlog2pos : 0 < Real.log ((M : ℝ) * 2) := lt_of_lt_of_le hlogM hlogge
  have hcz := cZ_le
  have hcz0 := cZ_pos
  have h1 : cZ / Real.log ((M : ℝ) * 2) < 1 - β₁ := by linarith
  have hb : 0 < 1 - β₁ := lt_trans (div_pos hcz0 hlog2pos) h1
  rw [div_lt_iff₀ hlog2pos] at h1
  have h2 : cZ / 2 ≤ (1 - β₁) * Real.log M := by
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hb.le]
  exact le_min (by linarith) h2

theorem eOf_char_sq (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) (h : eOf M = some (χ₁, β₁))
    (b : ZMod M) (hb : IsUnit b) : χ₁ b = 1 ∨ χ₁ b = -1 := by
  have hex := eOf_exc M (χ₁, β₁) h
  have h2 : (χ₁ ^ 2) b = 1 := by
    rw [hex.1]
    exact MulChar.one_apply hb
  rw [MulChar.pow_apply' χ₁ (by norm_num)] at h2
  exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
