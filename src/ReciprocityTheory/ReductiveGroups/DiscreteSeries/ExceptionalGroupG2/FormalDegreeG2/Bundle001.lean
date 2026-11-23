module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdUpperB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdLowerA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacobianLeExp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle007
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle005

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdU_s_pos {t : ℕ} (ht : 1 ≤ t) : 0 < (Real.sqrt (t : ℝ))⁻¹ := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr ht))

theorem fdU_s_sq {t : ℕ} (ht : 1 ≤ t) : (Real.sqrt (t : ℝ))⁻¹ ^ 2 * t = 1 := by
  have ht0 : (t : ℝ) ≠ 0 := by
    have : (0 : ℝ) < t := by exact_mod_cast ht
    exact this.ne'
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact inv_mul_cancel₀ ht0

theorem fdU_major {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (t : ℕ)
    (ht : 16 * n * q0 ε + 1 ≤ t) (y : PCoord ε → ℂ) :
    ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) ≤
      ENNReal.ofReal (Real.exp ((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32) *
        ∏ ab : PCoord ε, Real.exp (-((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ)) /
            ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖)) := by
  have h0 : 1 ≤ 16 * n * q0 ε + 1 := by omega
  have ht1 : 1 ≤ t := le_trans h0 ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have hs0 : 0 < (Real.sqrt (t : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr htpos)
  have hst : (Real.sqrt (t : ℝ))⁻¹ ^ 2 * t = 1 := fdU_s_sq ht1
  have hfar := fdU_far hlam h0 ht hs0 hst y
  apply ENNReal.ofReal_le_ofReal
  refine hfar.trans ?_
  rw [sub_eq_add_neg, Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [← neg_mul]
  by_cases hn : n = 0
  · have hE : IsEmpty (PCoord ε) := ⟨fun ab => by have := ab.1.1.2; omega⟩
    have hh : hs (pmat y) = 0 := by rw [hs_pmat]; simp
    rw [hh, Real.sqrt_zero, mul_zero, Real.exp_zero]
    simp
  · apply fdU_exp_le_prod
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hm : |(n : ℝ) - 1| ≤ n := by rw [abs_of_nonneg (by linarith)]; linarith
    have hq : (0 : ℝ) ≤ q0 ε := Nat.cast_nonneg _
    have ha : 0 < Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.succ_pos _)
    have haa : Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) * Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) =
        16 * n * q0 ε + 1 := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; ring
    rcases (Real.sqrt_nonneg (2 * (q0 ε : ℝ))).eq_or_lt with hb | hb
    · rw [← hb]; simp
    · have hbb : Real.sqrt (2 * (q0 ε : ℝ)) * Real.sqrt (2 * (q0 ε : ℝ)) = 2 * q0 ε :=
        Real.mul_self_sqrt (by positivity)
      rw [sub_nonneg, div_div, div_le_div_iff₀ ha (by positivity)]
      have key : |(n : ℝ) - 1| * (Real.sqrt (2 * (q0 ε : ℝ)) * Real.sqrt (2 * (q0 ε : ℝ))) * 8 ≤
          Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) * Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) := by
        rw [hbb, haa]; nlinarith
      nlinarith [key]

theorem fdU_pointwise {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (T : ℕ) (hT : 1 ≤ T)
    (y : PCoord ε → ℂ) :
    limsup (fun t : ℕ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) atTop ≤
      ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) := by
  have hs_tend : Filter.Tendsto (fun t : ℕ => (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun t : ℕ => ((t + T : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat T)
    exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp h1)
  have hc : Continuous (fun u : ℝ => ENNReal.ofReal (Real.exp (-(1 - u * rhoP y) * Qf (0 : Fin n → ℝ) y +
      ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) * (u * Real.sqrt (hs (pmat y)))))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))
  have hg := ((hc.tendsto 0).comp hs_tend).limsup_eq
  simp only [Function.comp_def] at hg
  have hev : ∀ᶠ t : ℕ in atTop, (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ * rhoP y ≤ 1 := by
    have h := hs_tend.mul_const (rhoP y)
    rw [zero_mul] at h
    exact h (Iic_mem_nhds one_pos)
  refine (Filter.limsup_le_limsup (v := fun t : ℕ => ENNReal.ofReal (Real.exp
      (-(1 - (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ * rhoP y) * Qf (0 : Fin n → ℝ) y +
        ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) *
          ((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ * Real.sqrt (hs (pmat y))))))
      (hev.mono fun t ht => ?_)).trans (le_of_eq ?_)
  · have hT1 : 1 ≤ t + T := by omega
    have hpos : (0 : ℝ) < ((t + T : ℕ) : ℝ) := by exact_mod_cast hT1
    have hs0 : 0 < (Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hpos)
    have hst := fdU_s_sq hT1
    have h := fdU_near hlam hs0 hst y ht
    exact ENNReal.ofReal_le_ofReal h
  · rw [hg]
    simp

theorem formal_degree_limsup_upper_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) :
    Filter.limsup (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z)) Filter.atTop ≤
      ENNReal.ofReal (PiW ε 0) := by
  have hscale : ∀ t : ℕ, 1 ≤ t → ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t) (pmat z)) * Jac z) =
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) := by
    intro t ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    rw [lintegral_pcoord_smul _ (fdU_s_pos ht), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have e : (t : ℝ) ^ (pOf ε * qOf ε) * ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = 1 := by
      rw [inv_pow, pow_mul (Real.sqrt (t : ℝ)) 2, Real.sq_sqrt htpos.le, mul_inv_cancel₀ (pow_ne_zero _ htpos.ne')]
    rw [e, ENNReal.ofReal_one, one_mul]
  set T : ℕ := 16 * n * q0 ε + 1 with hT
  rw [← Filter.limsup_nat_add _ T]
  refine le_trans (le_of_eq (Filter.limsup_congr (Filter.Eventually.of_forall fun i => hscale (i + T) (by omega)))) ?_
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
      (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) := by
    intro t
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    have hc : Continuous (fun y : PCoord ε → ℂ => (((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y) :=
      continuous_const_smul _
    exact (Real.continuous_exp.comp (continuous_const.mul ((continuous_potential_pmat _).comp hc))).mul
      ((jac_continuous ε).comp hc)
  have hint := ((fdU_integrable_prod_exp (ε := ε)
    (c := (Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ)) /
            ((Fintype.card (PCoord ε) : ℝ) + 1))
    (fun ab => div_pos (fdU_c_pos ab) (by positivity))).const_mul
    (Real.exp ((Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32)))
  calc _ ≤ ∫⁻ y, limsup (fun t : ℕ => ENNReal.ofReal (Real.exp (-2 * Ph (lamT lam (t + T))
        (pmat ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) *
        Jac ((((Real.sqrt ((t + T : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) • y))) atTop :=
        limsup_lintegral_le _ hmeas
          (fun t => Filter.Eventually.of_forall fun y => fdU_major hlam (t + T) (by omega) y)
          hint.lintegral_lt_top.ne
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) :=
        lintegral_mono fun y => fdU_pointwise hlam T (by omega) y
    _ = _ := fdU_lintegral_gauss ε

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem formal_degree_liminf_lower_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (hlim : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ))) :
    ENNReal.ofReal (PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z))
      Filter.atTop := by
  have hscale : ∀ t : ℕ, 1 ≤ t → ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z) =
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2 * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have hs : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht')
    rw [lintegral_pcoord_smul _ hs, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have e : (t : ℝ) ^ (pOf ε * qOf ε) * ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = 1 := by
      rw [inv_pow, pow_mul (Real.sqrt _) 2, Real.sq_sqrt ht'.le, mul_inv_cancel₀ (pow_ne_zero _ ht'.ne')]
    rw [e, ENNReal.ofReal_one, one_mul]
  rw [Filter.liminf_congr (Filter.eventually_atTop.2 ⟨1, hscale⟩)]
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2 * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) := by
    intro t
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    exact ((continuous_norm.comp ((fdl_inner_continuous _ (T t) _ _).comp (continuous_const_smul _))).pow 2).mul
      ((jac_continuous ε).comp (continuous_const_smul _))
  refine le_trans ?_ (lintegral_liminf_le hmeas)
  rw [← fdl_gauss ε]
  refine lintegral_mono fun y => ?_
  have h1 : Filter.Tendsto (fun t : ℕ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
      (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) Filter.atTop
      (nhds (ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)))) := by
    have h2 : Filter.Tendsto (fun t : ℕ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) Filter.atTop
        (nhds (ENNReal.ofReal (‖((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)‖ ^ 2))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)).tendsto _).comp (hlim y)
    have e : ‖((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)‖ ^ 2 = Real.exp (-Qf (0 : Fin n → ℝ) y) := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sq, ← Real.exp_add]
      congr 1
      ring
    rw [e] at h2
    exact h2
  rw [← h1.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun t => ENNReal.ofReal_le_ofReal
    (le_mul_of_one_le_right (sq_nonneg _) (jac_ge_one _)))

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
