module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem logDeriv_local {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ) (hne : ¬ ∀ᶠ s in 𝓝 ρ, f s = 0) :
    ∃ m : ℕ, (m = 0 ↔ f ρ ≠ 0) ∧ (m : ℕ∞) = analyticOrderAt f ρ ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv f s / f s = (m : ℂ) / (s - ρ) + h s := by
  have htop : analyticOrderAt f ρ ≠ ⊤ := fun h => hne (analyticOrderAt_eq_top.mp h)
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp htop
  set m := analyticOrderNatAt f ρ with hm
  refine ⟨m, ?_, Nat.cast_analyticOrderNatAt htop, fun s => deriv g s / g s,
    hg.deriv.div hg hg0, ?_⟩
  · rw [← hf.analyticOrderAt_eq_zero, ← Nat.cast_analyticOrderNatAt htop]
    exact Nat.cast_eq_zero.symm
  · have hev : ∀ᶠ s in 𝓝 ρ, (∀ᶠ z in 𝓝 s, f z = (z - ρ) ^ m • g z) ∧ g s ≠ 0 ∧ AnalyticAt ℂ g s :=
      (Filter.Eventually.eventually_nhds hfg).and
        ((hg.continuousAt.eventually_ne hg0).and hg.eventually_analyticAt)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s hs hsne
    obtain ⟨hs1, hs2, hs3⟩ := hs
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hsne
    have hd : HasDerivAt (fun z => (z - ρ) ^ m * g z)
        (↑m * (s - ρ) ^ (m - 1) * 1 * g s + (s - ρ) ^ m * deriv g s) s :=
      (((hasDerivAt_id' s).sub_const ρ).pow m).mul hs3.differentiableAt.hasDerivAt
    have e1 : deriv f s = deriv (fun z => (z - ρ) ^ m * g z) s := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hs1] with z hz
      rw [hz, smul_eq_mul]
    have e2 : f s = (s - ρ) ^ m * g s := by simpa only [smul_eq_mul] using hs1.self_of_nhds
    rw [e1, hd.deriv, e2]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]
      simp
    · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]
      field_simp

end Deduction

end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_finite {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {z : ℂ} {r : ℝ}
    (hr : r < z.re) : (Z ∩ Metric.closedBall z r).Finite := by
  have hK : IsCompact (Metric.closedBall z r) := isCompact_closedBall z r
  have hpos : ∀ w ∈ Metric.closedBall z r, 0 < w.re := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r := by simpa [dist_eq_norm] using hw
    have h2 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    have h3 := (abs_le.mp (h2.trans h1)).1
    simp only [Complex.sub_re] at h3
    linarith
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun w => {v | v ∈ ({w}ᶜ : Set ℂ) → v ∉ Z})
    (fun w hw => eventually_nhdsWithin_iff.mp (hiso w (hpos w hw)))
  refine t.finite_toSet.subset ?_
  rintro v ⟨hvZ, hvK⟩
  obtain ⟨w, hw, hvw⟩ := Set.mem_iUnion₂.mp (ht hvK)
  by_cases h : v = w
  · rw [h]; exact hw
  · exact absurd hvZ (hvw h)

end Deduction

end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_cauchy {Φ : ℂ → ℂ} {z : ℂ} {r r' : ℝ} (hd : DifferentiableOn ℂ Φ (Metric.ball z r))
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ, ‖iteratedDeriv k Φ z / (k.factorial : ℂ)‖ ≤ M / r' ^ k := by
  set R : NNReal := ⟨r', h0.le⟩ with hRdef
  have hR : (R : ℝ) = r' := rfl
  refine ⟨(2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖Φ (circleMap z r' θ)‖, fun k => ?_⟩
  have hsub : Metric.closedBall z (R : ℝ) ⊆ Metric.ball z r := by
    rw [hR]; exact Metric.closedBall_subset_ball h1
  have hRpos : (0 : NNReal) < R := by
    show (0 : ℝ) < (R : ℝ); rw [hR]; exact h0
  have hp := (hd.mono hsub).hasFPowerSeriesOnBall hRpos
  have key := hp.factorial_smul (1 : ℂ) k
  have hderiv : iteratedDeriv k Φ z / (k.factorial : ℂ) = cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← key, nsmul_eq_mul]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  rw [hderiv]
  calc ‖cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1)‖
      ≤ ‖cauchyPowerSeries Φ z (R : ℝ) k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries Φ z (R : ℝ) k‖ := by simp
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖Φ (circleMap z (R : ℝ) θ)‖) * |(R : ℝ)|⁻¹ ^ k :=
        norm_cauchyPowerSeries_le _ _ _ _
    _ = _ := by
        rw [hR, abs_of_pos h0, inv_pow, div_eq_mul_inv]

end Deduction

end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem iteratedDeriv_laplace_int (n : ℕ) (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-b * u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := b)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hb
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one]

theorem iteratedDeriv_laplace_meas (g : ℝ → ℝ) (hg : Measurable g) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
      (volume.restrict (Ioi (0 : ℝ))) := by
  apply Measurable.aestronglyMeasurable
  fun_prop

theorem iteratedDeriv_laplace_bound (g : ℝ → ℝ) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)) (k : ℕ) (b : ℝ) (z : ℂ) (hz : 2 + b ≤ z.re)
    (u : ℝ) (hu : 0 < u) :
    ‖(g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u)‖ ≤ C * (u ^ k * Real.exp (-b * u)) := by
  have h1 : ‖(g u : ℂ)‖ ≤ C * Real.exp (2 * u) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hgC u hu.le
  have h2 : ‖((-u : ℝ) : ℂ) ^ k‖ = u ^ k := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu]
  have h3 : ‖cexp (-z * u)‖ ≤ Real.exp (-(2 + b) * u) := by
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, mul_zero, sub_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hC : 0 ≤ C * Real.exp (2 * u) := le_trans (norm_nonneg _) h1
  rw [norm_mul, norm_mul, h2]
  calc ‖(g u : ℂ)‖ * u ^ k * ‖cexp (-z * u)‖
      ≤ C * Real.exp (2 * u) * u ^ k * Real.exp (-(2 + b) * u) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h3 (norm_nonneg _)
          (mul_nonneg hC (by positivity))
    _ = C * (u ^ k * (Real.exp (2 * u) * Real.exp (-(2 + b) * u))) := by ring
    _ = C * (u ^ k * Real.exp (-b * u)) := by
        rw [← Real.exp_add]
        ring_nf

theorem iteratedDeriv_laplace_hasDerivAt (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)) (k : ℕ) (s : ℂ) (hs : 2 < s.re) :
    HasDerivAt (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
      (∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (k + 1) * cexp (-s * u)) s := by
  set δ := (s.re - 2) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hre : ∀ z ∈ Metric.ball s δ, 2 + δ ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - s)
    rw [Complex.sub_re] at h1
    have h2 := (abs_le.mp (h1.trans hz.le)).1
    linarith
  have hint : Integrable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-s * u))
      (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' (Integrable.const_mul (iteratedDeriv_laplace_int k δ hδpos) C)
      (iteratedDeriv_laplace_meas g hg k s) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    exact iteratedDeriv_laplace_bound g C hgC k δ s (hre s (Metric.mem_ball_self hδpos)) u hu
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
    (F' := fun z u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (k + 1) * cexp (-z * u))
    (Metric.ball_mem_nhds s hδpos)
    (Eventually.of_forall fun z => iteratedDeriv_laplace_meas g hg k z) hint
    (iteratedDeriv_laplace_meas g hg (k + 1) s) ?_
    (Integrable.const_mul (iteratedDeriv_laplace_int (k + 1) δ hδpos) C) ?_).2
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu z hz => ?_)
    exact iteratedDeriv_laplace_bound g C hgC (k + 1) δ z (hre z hz) u hu
  · refine Eventually.of_forall fun u z _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -w * (u : ℂ)) (-(u : ℂ)) z := by
      simpa using (hasDerivAt_id' z).neg.mul_const (u : ℂ)
    have h2 := h1.cexp.const_mul ((g u : ℂ) * ((-u : ℝ) : ℂ) ^ k)
    refine h2.congr_deriv ?_
    push_cast
    ring

theorem iteratedDeriv_laplace (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u))
    (k : ℕ) (s : ℂ) (hs : 2 < s.re) :
    iteratedDeriv k (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) s =
      ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-s * u) := by
  have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have key : ∀ j : ℕ, ∀ z : ℂ, 2 < z.re →
      iteratedDeriv j (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) z =
        ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-z * u) := by
    intro j
    induction j with
    | zero =>
      intro z _
      simp
    | succ j ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u))
          =ᶠ[𝓝 z] fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-w * u) :=
        Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => ih w hw
      rw [hev.deriv_eq]
      exact (iteratedDeriv_laplace_hasDerivAt g hg C hgC j z hz).deriv
  exact key k s hs

end Deduction

end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_growth_contra {c d e C : ℝ} (hc : 0 < c) (hd : 0 < d) (hde : d < e) :
    ∃ η : ℝ, 0 < η ∧ ∃ U₀ : ℝ, ∀ U ≥ U₀, ∀ k : ℕ, U ≤ k → C * Real.exp (η * U) / e ^ k < c / d ^ k := by
  have he : 0 < e := hd.trans hde
  have hL : 0 < Real.log (e / d) := Real.log_pos ((one_lt_div hd).mpr hde)
  set L := Real.log (e / d) with hLdef
  refine ⟨L / 2, by positivity, 2 * |C| / (c * L), ?_⟩
  intro U hU k hk
  have hdk : 0 < d ^ k := pow_pos hd k
  have hek : 0 < e ^ k := pow_pos he k
  have hpow : e ^ k = d ^ k * Real.exp (k * L) := by
    rw [Real.exp_nat_mul, hLdef, Real.exp_log (div_pos he hd), div_pow, mul_div_cancel₀ _ hdk.ne']
  rw [div_lt_div_iff₀ hek hdk, hpow]
  set X := Real.exp (L / 2 * U) with hXdef
  have hXpos : 0 < X := Real.exp_pos _
  have hcL : 0 < c * L := mul_pos hc hL
  rw [ge_iff_le, div_le_iff₀ hcL] at hU
  have h1 : L / 2 * U + 1 ≤ X := Real.add_one_le_exp _
  have hX : |C| < c * X := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]
  have hY : X * X ≤ Real.exp (k * L) := by
    rw [hXdef, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hk hL.le]
  have hCX : C * X * d ^ k ≤ |C| * X * d ^ k := by
    have := le_abs_self C
    have hXd : 0 < X * d ^ k := mul_pos hXpos hdk
    nlinarith
  have h2 : |C| * X < c * (X * X) := by nlinarith
  have h3 : c * (X * X) ≤ c * Real.exp (k * L) := mul_le_mul_of_nonneg_left hY hc.le
  calc C * X * d ^ k ≤ |C| * X * d ^ k := hCX
    _ < c * Real.exp (k * L) * d ^ k := mul_lt_mul_of_pos_right (h2.trans_le h3) hdk
    _ = c * (d ^ k * Real.exp (k * L)) := by ring

end Deduction

end
end

section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_kernel_max (k : ℕ) {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) ≤ 1 / a ^ k := by
  have h := Real.pow_div_factorial_le_exp (a * u) (mul_nonneg ha.le hu) k
  have hak : 0 < a ^ k := pow_pos ha k
  rw [le_div_iff₀ hak]
  calc u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) * a ^ k
      = (a * u) ^ k / (k.factorial : ℝ) * Real.exp (-(a * u)) := by
        rw [mul_pow, neg_mul]; ring
    _ ≤ Real.exp (a * u) * Real.exp (-(a * u)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

end Deduction

end
end
