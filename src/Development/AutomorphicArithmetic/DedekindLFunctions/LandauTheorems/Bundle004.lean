module

public import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.MellinRamp
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem mellin_Gchi_modOne_sum {μ : Measure ℝ} (T : ℕ → ℝ → ℂ) (E : ℝ → ℂ)
    (hT : ∀ n, Integrable (T n) μ) (hE : Integrable E μ)
    (hs : Summable fun n => ∫ a, ‖T n a‖ ∂μ) (hp : ∀ a, Summable fun n => T n a) :
    ∫ a, (E a + ∑' n, T n a) ∂μ = ∫ a, E a ∂μ + ∑' n, ∫ a, T n a ∂μ := by
  let F : ℕ → ℝ → ℂ := fun n => Nat.casesOn n E T
  have hF : ∀ n, Integrable (F n) μ := fun n => by
    cases n with
    | zero => exact hE
    | succ n => exact hT n
  have hFs : Summable fun n => ∫ a, ‖F n a‖ ∂μ := (summable_nat_add_iff 1).mp hs
  have h := hasSum_integral_of_summable_integral_norm hF hFs
  have h2 : ∀ a, ∑' n, F n a = E a + ∑' n, T n a := fun a =>
    ((summable_nat_add_iff (f := fun n => F n a) 1).mp (hp a)).tsum_eq_zero_add
  simp_rw [h2] at h
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  rfl

theorem mellin_Gchi_modOne_int (n : ℕ) (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have ha : (-s).re < -1 := by simp; linarith
  have hb : (-s - 1).re < -1 := by simp; linarith
  refine Integrable.mono' (integrableOn_Ioi_norm_cpow_of_lt ha zero_lt_one) ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ (integrableOn_Ioi_cpow_of_lt hb zero_lt_one).1
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have hy1 : (1 : ℝ) < y := hy
    have hy0 : (0 : ℝ) < y := by linarith
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have h1 : y / n ≤ y := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hy0.le
      · exact div_le_self hy0.le (by exact_mod_cast hn)
    have h2 : max (y / n - 1) 0 ≤ y := max_le (by linarith) hy0.le
    rw [norm_mul, cpow_sub _ _ hyC, cpow_one, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (le_max_right _ _), Real.norm_of_nonneg hy0.le]
    calc _ ≤ y * (‖(y : ℂ) ^ (-s)‖ / y) := by gcongr
      _ = _ := by field_simp

theorem mellin_Gchi_modOne_term (n : ℕ) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) =
      LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n / (s * (s - 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [integral_const_mul, mellin_ramp n hn s hs, LSeries.term_of_ne_zero hn.ne', cpow_neg]
  ring

theorem mellin_Gchi_modOne_log_int (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) (Ioi 1) ∧
    Tendsto (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1)) atTop (𝓝 0) := by
  have ha : (-s).re < -1 := by simp; linarith
  set e : ℝ := (s.re - 1) / 2 with he
  have he0 : 0 < e := by linarith
  have key : ∀ (c : ℂ) (y : ℝ), 1 < y →
      ‖((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ c‖ ≤ y ^ (e + c.re) / e := by
    intro c y hy
    have hy0 : (0 : ℝ) < y := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hy.le),
      Complex.norm_cpow_eq_rpow_re_of_pos hy0, Real.rpow_add hy0]
    calc _ ≤ y ^ e / e * y ^ c.re := by
          gcongr
          exact Real.log_le_rpow_div hy0.le he0
      _ = _ := by ring
  constructor
  · have hc : e + (-s).re < -1 := by simp; linarith
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hc zero_lt_one).div_const e) ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).1
      exact (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => key _ y hy
  · have hc : 0 < -(e + (-s + 1).re) := by simp; linarith
    have h := (tendsto_rpow_neg_atTop hc).div_const e
    rw [neg_neg, zero_div] at h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_gt_atTop 1] with y hy using key _ y hy

theorem mellin_Gchi_modOne_log (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s) = 1 / (s - 1) ^ 2 := by
  have ha : (-s).re < -1 := by simp; linarith
  have hs1 : -s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  obtain ⟨hi, ht⟩ := mellin_Gchi_modOne_log_int s hs
  have hd : ∀ y ∈ Ici (1 : ℝ), HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1))
      ((-s + 1) * (((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) + (y : ℂ) ^ (-s)) y := by
    intro y hy
    have hy0 : y ≠ 0 := (zero_lt_one.trans_le hy).ne'
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
    refine ((Real.hasDerivAt_log hy0).ofReal_comp.mul
      (hasDerivAt_ofReal_cpow_const hy0 hs1)).congr_deriv ?_
    rw [add_sub_cancel_right, cpow_add _ _ hyC, cpow_one]
    push_cast
    field_simp
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    ((hi.const_mul _).add (integrableOn_Ioi_cpow_of_lt ha zero_lt_one)) ht
  rw [integral_add (hi.const_mul _) (integrableOn_Ioi_cpow_of_lt ha zero_lt_one),
    integral_const_mul, integral_Ioi_cpow_of_lt ha zero_lt_one] at h
  simp only [ofReal_one, one_cpow, Real.log_one, ofReal_zero, zero_mul, sub_zero] at h
  have e2 : (s - 1) ^ 2 = (-s + 1) ^ 2 := by ring
  rw [e2]
  field_simp at h ⊢
  linear_combination h

theorem mellin_Gchi_modOne (χ : DirichletCharacter ℂ 1) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) =
      -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1 - (1 + Real.eulerMascheroniConstant) * s) /
        (s * (s - 1)) := by
  have h1 : χ = 1 := DirichletCharacter.level_one χ
  have h2 : ∀ n : ℕ, χ n = 1 := fun n => by
    rw [h1]; exact MulChar.one_apply (isUnit_of_subsingleton _)
  have ha : (-s).re < -1 := by simp; linarith
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  let T : ℕ → ℝ → ℂ := fun n y => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))
  let E : ℝ → ℂ := fun y => (1 + Real.eulerMascheroniConstant) * (y : ℂ) ^ (-s) -
    ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)
  have hz : ∀ y : ℝ, ∀ n ∉ Finset.range (⌊y⌋₊ + 1), T n y = 0 := by
    intro y n hn
    have hn' : ⌊y⌋₊ + 1 ≤ n := by simpa using hn
    have hpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hlt : y < n := by
      have h1 := Nat.lt_floor_add_one y
      have h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
      push_cast at h2
      linarith
    have : max (y / n - 1) 0 = 0 := by
      apply max_eq_right
      have := (div_lt_one hpos).mpr hlt
      linarith
    simp [T, this]
  have hc : EqOn (fun y : ℝ => Gchi χ y * (y : ℂ) ^ (-s - 1))
      (fun y => E y + ∑' n, T n y) (Ioi 1) := by
    intro y hy
    have hy1 : (1 : ℝ) < y := hy
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hy1).ne'
    have h3 : (y : ℂ) ^ (-s) = y * (y : ℂ) ^ (-s - 1) := by
      rw [cpow_sub _ _ hyC, cpow_one]
      field_simp
    beta_reduce
    rw [tsum_eq_sum (hz y)]
    simp only [Gchi, if_pos h1, h2, ramp, T, E, h3, mul_one, ← mul_assoc,
      ← Finset.sum_mul]
    push_cast
    ring
  have hi := (mellin_Gchi_modOne_log_int s hs).1
  have hi2 := integrableOn_Ioi_cpow_of_lt ha zero_lt_one
  have hsum : Summable fun n => ∫ y in Ioi (1 : ℝ), ‖T n y‖ := by
    have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
    rw [← Complex.summable_ofReal]
    refine ((ArithmeticFunction.LSeriesSummable_vonMangoldt hσ).div_const
      ((s.re : ℂ) * (s.re - 1))).congr fun n => ?_
    rw [← mellin_Gchi_modOne_term n _ hσ, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := zero_lt_one.trans hy
    simp only [T]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.norm_of_nonneg (le_max_right _ _), Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have : (y : ℂ) ^ (-(s.re : ℂ) - 1) = ((y ^ (-s - 1).re : ℝ) : ℂ) := by
      rw [ofReal_cpow hy0.le]
      simp
    rw [this]
    simp
  rw [setIntegral_congr_fun measurableSet_Ioi hc,
    mellin_Gchi_modOne_sum T E (fun n => (mellin_Gchi_modOne_int n s hs).const_mul _)
      ((hi2.const_mul _).sub hi) hsum (fun y => summable_of_ne_finset_zero (hz y))]
  simp only [T, E, mellin_Gchi_modOne_term _ s hs]
  rw [tsum_div_const, integral_sub (hi2.const_mul _) hi, integral_const_mul,
    integral_Ioi_cpow_of_lt ha zero_lt_one, mellin_Gchi_modOne_log s hs]
  have h4 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [LSeries] at h4
  rw [h4, neg_div (riemannZeta s)]
  have e2 : -s + 1 = -(s - 1) := by ring
  rw [e2]
  generalize deriv riemannZeta s / riemannZeta s = D
  simp only [ofReal_one, one_cpow]
  field_simp
  ring

end Deduction

end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem eq_ofReal_sub_of_dist_le_of_le_sub_re {w : ℂ} {σ D : ℝ} (h1 : dist w (σ : ℂ) ≤ D) (h2 : D ≤ σ - w.re) :
    w = ((σ - D : ℝ) : ℂ) := by
  have hD0 : 0 ≤ D := dist_nonneg.trans h1
  rw [Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im] at h1
  have hq : (w.re - σ) ^ 2 + (w.im - 0) ^ 2 ≤ D ^ 2 := by
    have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ (w.re - σ) ^ 2 + (w.im - 0) ^ 2)
    have h0 := Real.sqrt_nonneg ((w.re - σ) ^ 2 + (w.im - 0) ^ 2)
    nlinarith
  have him : w.im = 0 := by nlinarith [sq_nonneg w.im]
  have hre : w.re = σ - D := by nlinarith [sq_nonneg w.im]
  apply Complex.ext
  · rw [Complex.ofReal_re]; exact hre
  · rw [Complex.ofReal_im]; exact him

theorem landau_dichotomy {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {σ θ : ℝ}
    (hle : ∀ ρ ∈ Z, ρ.re < σ) (hθ : 0 < θ) (hθσ : θ < σ) {ρ₀ : ℂ} (h₀ : ρ₀ ∈ Z) (hρ₀ : θ < ρ₀.re) :
    (∃ D : ℝ, D ≤ σ - θ ∧ (∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) D) ∧ ∃ ρ₁ ∈ Z, σ - ρ₁.re < D) ∨
    (∃ β : ℝ, (β : ℂ) ∈ Z ∧ θ < β ∧ ∃ r : ℝ, σ - β < r ∧ r ≤ σ - θ ∧
      ∀ w ∈ Z, w ∈ Metric.ball (σ : ℂ) r → w = β) := by
  have hfin : (Z ∩ Metric.closedBall (σ : ℂ) (σ - θ)).Finite :=
    landau_finite hiso (by rw [Complex.ofReal_re]; linarith)
  set F := Z ∩ Metric.closedBall (σ : ℂ) (σ - θ) with hFdef
  rcases F.eq_empty_or_nonempty with hF | hF
  · left
    refine ⟨σ - θ, le_rfl, ?_, ρ₀, h₀, by linarith⟩
    intro w hw hb
    have hwF : w ∈ F := ⟨hw, Metric.ball_subset_closedBall hb⟩
    rw [hF] at hwF
    exact hwF
  · obtain ⟨ρs, hρsF, hmin⟩ := Set.exists_min_image F (fun w => dist w (σ : ℂ)) hfin hF
    have hdle : dist ρs (σ : ℂ) ≤ σ - θ := Metric.mem_closedBall.mp hρsF.2
    have hball : ∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) (dist ρs (σ : ℂ)) := by
      intro w hw hb
      rw [Metric.mem_ball] at hb
      have hwF : w ∈ F := ⟨hw, Metric.mem_closedBall.mpr (by linarith)⟩
      have := hmin w hwF
      linarith
    by_cases hex : ∃ ρ₁ ∈ Z, σ - ρ₁.re < dist ρs (σ : ℂ)
    · left
      exact ⟨dist ρs (σ : ℂ), hdle, hball, hex⟩
    · right
      push_neg at hex
      set d := dist ρs (σ : ℂ) with hd
      have hreal : ∀ w ∈ F, dist w (σ : ℂ) = d → w = ((σ - d : ℝ) : ℂ) :=
        fun w hw he => eq_ofReal_sub_of_dist_le_of_le_sub_re (le_of_eq he) (hex w hw.1)
      have hρs := hreal ρs hρsF rfl
      have hdlt : d < σ - θ := by
        rcases lt_or_eq_of_le hdle with h | h
        · exact h
        · exfalso
          have := hex ρ₀ h₀
          linarith
      refine ⟨σ - d, hρs ▸ hρsF.1, by linarith, ?_⟩
      have hT : ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, d < dist t (σ : ℂ) := by
        intro t ht
        have hm : d ≤ dist t (σ : ℂ) := hmin t ht.1
        rcases lt_or_eq_of_le hm with h | h
        · exact h
        · exact absurd (hreal t ht.1 h.symm) ht.2
      obtain ⟨r, hr, hrT⟩ : ∃ r, d < r ∧ ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, r ≤ dist t (σ : ℂ) := by
        rcases (F \ {((σ - d : ℝ) : ℂ)}).eq_empty_or_nonempty with hTe | hTne
        · refine ⟨d + 1, by linarith, ?_⟩
          intro t ht
          rw [hTe] at ht
          exact absurd ht (Set.notMem_empty t)
        · obtain ⟨t₀, ht₀, htmin⟩ := Set.exists_min_image (F \ {((σ - d : ℝ) : ℂ)})
            (fun w => dist w (σ : ℂ)) (hfin.subset Set.diff_subset) hTne
          exact ⟨dist t₀ (σ : ℂ), hT t₀ ht₀, htmin⟩
      refine ⟨min r (σ - θ), ?_, min_le_right _ _, ?_⟩
      · rw [sub_sub_cancel]
        exact lt_min hr hdlt
      · intro w hw hb
        rw [Metric.mem_ball] at hb
        have hwF : w ∈ F := ⟨hw, Metric.mem_closedBall.mpr (le_trans hb.le (min_le_right _ _))⟩
        by_contra hne
        have h3 := hrT w ⟨hwF, hne⟩
        have h4 := min_le_left r (σ - θ)
        linarith

end Deduction

end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

lemma landau_nearest_equi {σ γ : ℝ} {a b : ℂ} (ha : a.re < σ) (hb : b.re < σ)
    (h : ‖(σ : ℂ) + γ * I - a‖ = ‖(σ : ℂ) + γ * I - b‖)
    (hγ : γ ≠ ((σ - a.re) ^ 2 + a.im ^ 2 - (σ - b.re) ^ 2 - b.im ^ 2) / (2 * (a.im - b.im))) :
    a = b := by
  have h2 : ‖(σ : ℂ) + γ * I - a‖ ^ 2 = ‖(σ : ℂ) + γ * I - b‖ ^ 2 := by rw [h]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im] at h2
  have him : a.im = b.im := by
    by_contra hne
    apply hγ
    have hne' : 2 * (a.im - b.im) ≠ 0 := by
      have := sub_ne_zero.mpr hne
      positivity
    rw [eq_div_iff hne']
    linear_combination -h2
  have hsq : (b.re - a.re) * ((σ - a.re) + (σ - b.re)) = 0 := by
    rw [him] at h2
    linear_combination h2
  rcases mul_eq_zero.mp hsq with h3 | h3
  · apply Complex.ext
    · linarith
    · exact him
  · exfalso
    linarith

theorem landau_nearest {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {σ D : ℝ}
    (hle : ∀ ρ ∈ Z, ρ.re < σ) (hD : D < σ) {ρ₁ : ℂ} (h₁ : ρ₁ ∈ Z) (hρ₁ : σ - ρ₁.re < D) :
    ∃ γ : ℝ, ∃ ρ ∈ Z, ∃ r : ℝ, ‖(σ : ℂ) + γ * I - ρ‖ < r ∧ r ≤ D ∧
      ∀ w ∈ Z, w ∈ Metric.ball ((σ : ℂ) + γ * I) r → w = ρ := by
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ (D - (σ - ρ₁.re)) / 2 ∧ ε ≤ (σ - D) / 2 := by
    refine ⟨min (D - (σ - ρ₁.re)) (σ - D) / 2, ?_, ?_, ?_⟩
    · have := lt_min (show 0 < D - (σ - ρ₁.re) by linarith) (show 0 < σ - D by linarith)
      linarith
    · have := min_le_left (D - (σ - ρ₁.re)) (σ - D)
      linarith
    · have := min_le_right (D - (σ - ρ₁.re)) (σ - D)
      linarith
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℂ, c₀ = (σ : ℂ) + ρ₁.im * I := ⟨_, rfl⟩
  have hc₀re : c₀.re = σ := by rw [hc₀]; simp
  have hF : (Z ∩ Metric.closedBall c₀ (D + ε)).Finite :=
    landau_finite hiso (by rw [hc₀re]; linarith)
  set F := Z ∩ Metric.closedBall c₀ (D + ε) with hFdef
  set B : Set ℝ := (fun p : ℂ × ℂ =>
      ((σ - p.1.re) ^ 2 + p.1.im ^ 2 - (σ - p.2.re) ^ 2 - p.2.im ^ 2) / (2 * (p.1.im - p.2.im))) ''
      (F ×ˢ F) with hB
  have hBfin : B.Finite := (hF.prod hF).image _
  obtain ⟨γ, hγI, hγB⟩ := ((Set.Ioo_infinite (show ρ₁.im - ε < ρ₁.im + ε by linarith)).diff hBfin).nonempty
  set c : ℂ := (σ : ℂ) + γ * I with hc
  have hγε : |γ - ρ₁.im| < ε := abs_sub_lt_iff.mpr ⟨by linarith [hγI.2], by linarith [hγI.1]⟩
  have hcc₀ : ‖c - c₀‖ = |γ - ρ₁.im| := by
    have e : c - c₀ = ((γ - ρ₁.im : ℝ) : ℂ) * I := by
      rw [hc, hc₀]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hc₀ρ₁ : ‖c₀ - ρ₁‖ = σ - ρ₁.re := by
    have e : c₀ - ρ₁ = ((σ - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc₀]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (hle ρ₁ h₁))]
  have hρ₁F : ρ₁ ∈ F := by
    refine ⟨h₁, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, hc₀ρ₁]
    linarith
  obtain ⟨ρ, hρF, hmin⟩ := Set.exists_min_image F (fun w => ‖c - w‖) hF ⟨ρ₁, hρ₁F⟩
  have hρ₁c : ‖c - ρ₁‖ < D := by
    have := norm_add_le (c - c₀) (c₀ - ρ₁)
    rw [sub_add_sub_cancel, hcc₀, hc₀ρ₁] at this
    linarith
  have hm : ‖c - ρ‖ ≤ ‖c - ρ₁‖ := hmin ρ₁ hρ₁F
  have hT : ∀ w ∈ F \ {ρ}, ‖c - ρ‖ < ‖c - w‖ := by
    intro w hw
    have hmw : ‖c - ρ‖ ≤ ‖c - w‖ := hmin w hw.1
    rcases lt_or_eq_of_le hmw with h | h
    · exact h
    · exfalso
      apply hw.2
      exact landau_nearest_equi (hle w hw.1.1) (hle ρ hρF.1) h.symm
        (fun hb => hγB ⟨(w, ρ), ⟨hw.1, hρF⟩, hb.symm⟩)
  obtain ⟨r, hr, hrT⟩ : ∃ r, ‖c - ρ‖ < r ∧ ∀ t ∈ F \ {ρ}, r ≤ ‖c - t‖ := by
    rcases (F \ {ρ}).eq_empty_or_nonempty with hTe | hTne
    · refine ⟨‖c - ρ‖ + 1, by linarith, ?_⟩
      intro t ht
      rw [hTe] at ht
      exact absurd ht (Set.notMem_empty t)
    · obtain ⟨t₀, ht₀, htmin⟩ := Set.exists_min_image (F \ {ρ}) (fun w => ‖c - w‖)
        (hF.subset Set.diff_subset) hTne
      exact ⟨‖c - t₀‖, hT t₀ ht₀, htmin⟩
  refine ⟨γ, ρ, hρF.1, min r D, lt_min hr (by linarith), min_le_right _ _, ?_⟩
  intro w hw hb
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hb
  have hwF : w ∈ F := by
    refine ⟨hw, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have := norm_add_le (w - c) (c - c₀)
    rw [sub_add_sub_cancel, norm_sub_rev w c, hcc₀] at this
    linarith [min_le_right r D]
  by_contra hne
  have h3 := hrT w ⟨hwF, hne⟩
  linarith [min_le_left r D]

end Deduction

end
end
