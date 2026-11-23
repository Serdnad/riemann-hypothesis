module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle001
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle002
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RiemannZetaOneEqOneSubOfRePos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
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
import Mathlib.Tactic.Linter.Style
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

open Complex Filter Topology Metric

noncomputable section

namespace Formalism.ZF

private theorem hasDerivAt_sub_pow_of_sub_ne_zero (a z : ℂ) (n : ℕ) (h : z - a ≠ 0) :
    HasDerivAt (fun w => (w - a) ^ n) ((z - a) ^ n * ((n : ℂ) / (z - a))) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := by
    simpa using (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => (w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1) * 1) z :=
    (hasDerivAt_pow n (z - a)).comp z h1
  refine h2.congr_deriv ?_
  rcases n with _ | k
  · simp
  · rw [pow_succ, Nat.add_sub_cancel]
    have hinv : (z - a) * (z - a)⁻¹ = 1 := mul_inv_cancel₀ h
    linear_combination (-((z - a) ^ k * ((k + 1 : ℕ) : ℂ))) * hinv

private theorem hasDerivAt_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    HasDerivAt (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ)
      ((∏ ρ ∈ Z, (z - ρ) ^ m ρ) * ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) z := by
  classical
  revert hz
  induction Z using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty, Finset.sum_empty, mul_zero]
    exact hasDerivAt_const z (1 : ℂ)
  | insert =>
    rename_i a s ha ih
    intro hz
    have hs : ∀ ρ ∈ s, z - ρ ≠ 0 := fun ρ hρ => hz ρ (Finset.mem_insert_of_mem hρ)
    have hza : z - a ≠ 0 := hz a (Finset.mem_insert_self a s)
    have hd := (hasDerivAt_sub_pow_of_sub_ne_zero a z (m a) hza).mul (ih hs)
    beta_reduce at hd
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    refine hd.congr_deriv ?_
    ring

lemma landauLocal_logDeriv_prod (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_apply, (hasDerivAt_prod_sub_pow Z m z hz).deriv]
  have hP : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hz ρ hρ)
  exact (div_eq_iff hP).mpr (mul_comm _ _)

private theorem pow_le_pow_left_of_nonneg_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (le_trans (pow_nonneg ha k) ih)

private theorem norm_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (w : ℂ) :
    ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ = ∏ ρ ∈ Z, ‖w - ρ‖ ^ m ρ := by
  simp only [norm_prod, norm_pow]

private theorem div_add_div_sub_eq_div (P S H D : ℂ) (hP : P ≠ 0) (hH : H ≠ 0) :
    (P * S * H + P * D) / (P * H) - S = D / H := by
  rw [sub_eq_iff_eq_add, div_eq_iff (mul_ne_zero hP hH)]
  have hHH : H⁻¹ * H = 1 := inv_mul_cancel₀ hH
  linear_combination (-(P * D)) * hHH

theorem localZeroExpansionOfFactorization : LandauLocalOf := by
  unfold LandauLocalOf LandauLocal
  intro hfac hlog f z₀ r M hr hM hf hf0 hbound
  classical
  have hr3 : 0 < r / 3 := by positivity
  obtain ⟨Z, m, h, hZ, hm, hh, hh0, hfeq⟩ := hfac f z₀ r (r / 3) hr3 (by linarith) hf hf0
  have hZball : ∀ ρ ∈ Z, ‖ρ - z₀‖ ≤ r / 3 := fun ρ hρ => by
    have := ((hZ ρ).1 hρ).1
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hZzero : ∀ ρ ∈ Z, f ρ = 0 := fun ρ hρ => ((hZ ρ).1 hρ).2
  have hz₀mem : z₀ ∈ Metric.closedBall z₀ r := Metric.mem_closedBall_self hr.le
  have hfz₀ := hfeq z₀ hz₀mem
  have hhz₀ : h z₀ ≠ 0 := by
    intro h0; apply hf0; rw [hfz₀, h0, mul_zero]
  have hPz₀le : ‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
    rw [norm_prod_sub_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun ρ _ => pow_nonneg (norm_nonneg _) _) ?_
    intro ρ hρ
    have h1 : ‖z₀ - ρ‖ ≤ r / 3 := by rw [norm_sub_rev]; exact hZball ρ hρ
    exact pow_le_pow_left_of_nonneg_le (norm_nonneg _) h1 _
  have hPw : ∀ w : ℂ, ‖w - z₀‖ = r →
      (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ := by
    intro w hw
    rw [norm_prod_sub_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun ρ _ => pow_nonneg (by linarith) _) ?_
    intro ρ hρ
    have h2 := hZball ρ hρ
    have h3 : ‖w - z₀‖ ≤ ‖w - ρ‖ + ‖ρ - z₀‖ := by
      have := norm_add_le (w - ρ) (ρ - z₀)
      rwa [sub_add_sub_cancel] at this
    have h1 : 2 * r / 3 ≤ ‖w - ρ‖ := by linarith
    exact pow_le_pow_left_of_nonneg_le (by linarith) h1 _
  have key_sphere : ∀ w : ℂ, ‖w - z₀‖ = r →
      (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ ≤ M * ‖h z₀‖ := by
    intro w hw
    have hwmem : w ∈ Metric.closedBall z₀ r :=
      Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hw.le)
    have e1 := hbound w hwmem
    rw [hfeq w hwmem, hfz₀, norm_mul, norm_mul] at e1
    have e2 := hPw w hw
    have hq : 0 < (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by positivity
    have e3 : (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) = (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
      rw [mul_div_assoc, mul_pow]
    have e4 : (r / 3) ^ (∑ ρ ∈ Z, m ρ) * ((2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
        ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by
      calc (r / 3) ^ (∑ ρ ∈ Z, m ρ) * ((2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
          = (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ := by rw [e3]; ring
        _ ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ * ‖h w‖ := mul_le_mul_of_nonneg_right e2 (norm_nonneg _)
        _ ≤ M * (‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ * ‖h z₀‖) := e1
        _ ≤ M * ((r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h z₀‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            exact mul_le_mul_of_nonneg_right hPz₀le (norm_nonneg _)
        _ = (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by ring
    exact le_of_mul_le_mul_left e4 hq
  have hdc : DiffContOnCl ℂ h (Metric.ball z₀ r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z₀ hr.ne']
    exact hh
  have hmax : ∀ z ∈ Metric.closedBall z₀ r,
      ‖h z‖ ≤ M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    intro z hz
    have hz' : z ∈ closure (Metric.ball z₀ r) := by rwa [closure_ball z₀ hr.ne']
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc ?_ hz'
    intro w hw
    rw [frontier_ball z₀ hr.ne', mem_sphere_iff_norm] at hw
    rw [le_div_iff₀ (by positivity), mul_comm (‖h w‖)]
    exact key_sphere w hw
  have h2N : (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M := by
    have := hmax z₀ hz₀mem
    have hpos : 0 < ‖h z₀‖ := norm_pos_iff.mpr hhz₀
    rw [le_div_iff₀ (by positivity), mul_comm M] at this
    exact le_of_mul_le_mul_left this hpos
  have hsum : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
    exact Real.log_le_log (by positivity) h2N
  have h2N1 : (1 : ℝ) ≤ (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    simpa using pow_le_pow_left_of_nonneg_le (a := 1) (b := 2) zero_le_one one_le_two (∑ ρ ∈ Z, m ρ)
  have hhb : ∀ z ∈ Metric.closedBall z₀ (r / 3), ‖h z‖ ≤ M * ‖h z₀‖ := by
    intro z hz
    have hz' : z ∈ Metric.closedBall z₀ r := Metric.closedBall_subset_closedBall (by linarith) hz
    have h1 := hmax z hz'
    have h2 : M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M * ‖h z₀‖ :=
      div_le_self (mul_nonneg (by linarith) (norm_nonneg _)) h2N1
    linarith
  have hlogb := hlog h z₀ (r / 3) M hr3 hM
    (hh.mono (Metric.closedBall_subset_closedBall (by linarith))) hh0 hhb
  refine ⟨Z, m, hZ, hm, hsum, ?_⟩
  intro z hz hfz
  have hzr : z ∈ Metric.ball z₀ r := by
    rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
  have hnhds : Metric.closedBall z₀ r ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzr) Metric.ball_subset_closedBall
  have hev : f =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * h w :=
    Filter.mem_of_superset hnhds (fun w hw => hfeq w hw)
  have hfeqz := hfeq z (Metric.ball_subset_closedBall hzr)
  have hPz : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, zero_mul]
  have hhz : h z ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, mul_zero]
  have hzρ : ∀ ρ ∈ Z, z - ρ ≠ 0 := by
    intro ρ hρ h0; apply hfz; rw [sub_eq_zero.mp h0]; exact hZzero ρ hρ
  have hPd := hasDerivAt_prod_sub_pow Z m z hzρ
  have hhd : HasDerivAt h (deriv h z) z := (hh.differentiableAt hnhds).hasDerivAt
  have hd := (hPd.mul hhd).congr_of_eventuallyEq hev
  have hsplit : deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) = deriv h z / h z := by
    rw [hd.deriv, hfeqz]
    exact div_add_div_sub_eq_div _ _ _ _ hPz hhz
  rw [hsplit]
  have hz6 : z ∈ Metric.closedBall z₀ (r / 3 / 2) := by
    rw [Metric.mem_closedBall] at hz ⊢; linarith
  calc ‖deriv h z / h z‖ ≤ 24 * Real.log M / (r / 3) := hlogb z hz6
    _ = 72 * Real.log M / r := by rw [div_div_eq_mul_div]; ring

end Formalism.ZF
end
end

section

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZF

theorem logDerivBoundRightHalfPlane : LogDerivRight := by
  obtain ⟨B, hB⟩ := log_deriv_riemannZeta_add_inv_sub_bounded.bound
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hB)
  refine ⟨max (max B 0) (lamF (1 + ε / 2)), le_max_of_le_left (le_max_right _ _),
    fun s hs => (norm_logDeriv_le_lamF hs).trans ?_⟩
  have hσ1 : 0 < s.re - 1 := sub_pos.mpr hs
  have hpos : 0 < 1 / (s.re - 1) := by positivity
  rcases lt_or_ge s.re (1 + ε / 2) with hlt | hge
  · have hreal : ‖((s.re : ℂ) - 1)‖ = s.re - 1 := by
      rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hσ1.le]
    have hd : dist (s.re : ℂ) 1 < ε := by
      rw [Complex.dist_eq, hreal]; linarith
    have hne : (s.re : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_eq_one]; exact hs.ne'
    have hb := hball hd hne
    simp only [norm_one, mul_one] at hb
    have hL := LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (s.re : ℂ)) (by simpa using hs)
    rw [lamF_eq_norm hs, hL, neg_div, norm_neg]
    have htri : ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)‖ ≤
        ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ) + ((s.re : ℂ) - 1)⁻¹‖ +
          ‖((s.re : ℂ) - 1)⁻¹‖ := by
      have := norm_sub_le (deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ) +
        ((s.re : ℂ) - 1)⁻¹) (((s.re : ℂ) - 1)⁻¹)
      simpa using this
    rw [norm_inv, hreal] at htri
    have : B ≤ max (max B 0) (lamF (1 + ε / 2)) :=
      le_max_of_le_left (le_max_left _ _)
    rw [one_div]
    linarith
  · have h1 : lamF s.re ≤ lamF (1 + ε / 2) := lamF_anti (by linarith) hge
    have : lamF (1 + ε / 2) ≤ max (max B 0) (lamF (1 + ε / 2)) := le_max_right _ _
    linarith

end Formalism.ZF
end
end

section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

open ComplexPowerDifferenceIntegral in
lemma norm_Dz_le {s : ℂ} (hs : 0 < s.re) :
    ‖Dz s‖ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by
  set σ := s.re with hσ

  have hkey : ∀ x : ℝ, 1 ≤ x → σ * (x + 1) ^ (-σ - 1) ≤ x ^ (-σ) - (x + 1) ^ (-σ) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < x + 1 := by linarith
    have hA : 0 < (x + 1) ^ σ := Real.rpow_pos_of_pos hy0 σ
    have hB : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
    have hq : 0 < (x + 1) / x := div_pos hy0 hx0
    have hr : ((x + 1) / x) ^ σ = (x + 1) ^ σ / x ^ σ := Real.div_rpow hy0.le hx0.le σ
    have hlog : 1 / (x + 1) ≤ Real.log ((x + 1) / x) := by
      have := Real.one_sub_inv_le_log_of_pos hq
      have e : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
      linarith
    have hexp : 1 + σ / (x + 1) ≤ (x + 1) ^ σ / x ^ σ := by
      rw [← hr, Real.rpow_def_of_pos hq]
      have h1 := Real.add_one_le_exp (Real.log ((x + 1) / x) * σ)
      have h2 : σ / (x + 1) ≤ Real.log ((x + 1) / x) * σ := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_right hlog hs.le
      linarith
    rw [Real.rpow_sub_one hy0.ne', Real.rpow_neg hy0.le, Real.rpow_neg hx0.le]
    have e1 : σ * ((x + 1) ^ σ)⁻¹ / (x + 1) = σ / (x + 1) * ((x + 1) ^ σ)⁻¹ := by ring
    have e2 : (x ^ σ)⁻¹ - ((x + 1) ^ σ)⁻¹ = ((x + 1) ^ σ / x ^ σ - 1) * ((x + 1) ^ σ)⁻¹ := by
      field_simp
    rw [mul_div_assoc', e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hA.le)
  have hS : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), ((i : ℝ) + 1) ^ (-σ - 1)
      ≤ 1 + (1 - ((N : ℝ) + 1) ^ (-σ)) / σ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hk := hkey ((N : ℝ) + 1) (by linarith [N.cast_nonneg (α := ℝ)])
      have hk' : ((N : ℝ) + 1 + 1) ^ (-σ - 1) ≤ (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ := by
        rw [le_div_iff₀ hs]
        linarith
      push_cast
      have e : (1 - ((N : ℝ) + 1) ^ (-σ)) / σ + (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ
          = (1 - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ := by
        field_simp
        ring
      linarith
  have hT : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-σ - 1) ≤ 1 + 1 / σ := by
    intro n
    rcases n with _ | N
    · simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    · refine (hS N).trans ?_
      have h0 : 0 ≤ ((N : ℝ) + 1) ^ (-σ) := Real.rpow_nonneg (by positivity) _
      have : (1 - ((N : ℝ) + 1) ^ (-σ)) / σ ≤ 1 / σ := div_le_div_of_nonneg_right (by linarith) hs.le
      linarith
  have hC : 0 ≤ ‖s - 1‖ * ‖s‖ := by positivity
  show ‖∑' n, dz s n‖ ≤ _
  calc ‖∑' n, dz s n‖ ≤ ∑' n, ‖dz s n‖ := norm_tsum_le_tsum_norm (summable_norm_dz hs)
    _ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / σ) := by
      refine Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) fun n => ?_
      calc ∑ i ∈ Finset.range n, ‖dz s i‖
          ≤ ∑ i ∈ Finset.range n, ‖s - 1‖ * ‖s‖ * ((i : ℝ) + 1) ^ (-σ - 1) :=
            Finset.sum_le_sum fun i _ => norm_dz_le hs i
        _ = ‖s - 1‖ * ‖s‖ * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-σ - 1) := by
            rw [Finset.mul_sum]
        _ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / σ) := mul_le_mul_of_nonneg_left (hT n) hC

theorem growthBound : ZetaGrowth := by
  intro s hs hs1
  have h1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    unfold riemannZeta₁ riemannZeta₀
    rw [if_neg hs1, mul_sub, mul_inv_cancel₀ (sub_ne_zero.2 hs1)]
    ring
  have hD := norm_Dz_le hs
  have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hpos : 0 < ‖s - 1‖ := norm_pos_iff.2 hne
  have hz : riemannZeta s = (s - ComplexPowerDifferenceIntegral.Dz s) / (s - 1) := by
    rw [← ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos hs, h1]
    field_simp
  rw [hz, norm_div, div_le_iff₀ hpos]
  have hs' : ‖s‖ ≤ ‖s - 1‖ + 1 := by simpa using norm_add_le (s - 1) 1
  calc ‖s - ComplexPowerDifferenceIntegral.Dz s‖ ≤ ‖s‖ + ‖ComplexPowerDifferenceIntegral.Dz s‖ := norm_sub_le _ _
    _ ≤ (‖s - 1‖ + 1) + ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := add_le_add hs' hD
    _ = (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) * ‖s - 1‖ := by
        field_simp

end Formalism.ZF
end
end
