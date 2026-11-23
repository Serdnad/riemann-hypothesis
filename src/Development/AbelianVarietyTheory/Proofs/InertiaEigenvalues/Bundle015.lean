module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory

theorem norm_mul_cexp_le_of_abs_le_on_support {s : ℂ} {f t : ℝ} {R : ℝ} (hf : 0 ≤ f) (hR : f ≠ 0 → |t| ≤ R) :
    ‖(f : ℂ) * Complex.exp (s * t)‖ ≤ f * Real.exp (‖s‖ * R) := by
  by_cases h0 : f = 0
  · simp [h0]
  have ht := hR h0
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]
  apply mul_le_mul_of_nonneg_left _ hf
  apply Real.exp_le_exp.mpr
  have h1 : (s * (t : ℂ)).re = s.re * t := by simp
  rw [h1]
  calc s.re * t ≤ |s.re * t| := le_abs_self _
    _ = |s.re| * |t| := abs_mul _ _
    _ ≤ ‖s‖ * R := mul_le_mul (Complex.abs_re_le_norm s) ht (abs_nonneg _) (norm_nonneg _)

theorem exp_integral_entire_real_pos {X : Type} [MeasurableSpace X] (ν : Measure X) (f t : X → ℝ)
    (hfm : Measurable f) (htm : Measurable t) (hf0 : ∀ y, 0 ≤ f y)
    (hfi : Integrable f ν) (hR : ∃ R : ℝ, ∀ y, f y ≠ 0 → |t y| ≤ R) :
    Differentiable ℂ (fun s : ℂ => ∫ y, (f y : ℂ) * Complex.exp (s * t y) ∂ν) ∧
    ∀ r : ℝ, (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).im = 0 ∧
      (0 < ∫ y, f y ∂ν → 0 < (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).re) := by
  obtain ⟨R, hR⟩ := hR
  have hmeas : ∀ s : ℂ, Measurable fun y => (f y : ℂ) * Complex.exp (s * t y) := by
    intro s; fun_prop
  have hint : ∀ s : ℂ, Integrable (fun y => (f y : ℂ) * Complex.exp (s * t y)) ν := by
    intro s
    refine Integrable.mono' (hfi.mul_const (Real.exp (‖s‖ * R))) (hmeas s).aestronglyMeasurable
      (ae_of_all _ fun y => norm_mul_cexp_le_of_abs_le_on_support (hf0 y) (hR y))
  refine ⟨?_, ?_⟩
  · intro s₀
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀)
      (F := fun s y => (f y : ℂ) * Complex.exp (s * t y))
      (F' := fun s y => (f y : ℂ) * (Complex.exp (s * t y) * t y))
      (bound := fun y => f y * R * Real.exp ((‖s₀‖ + 1) * R))
      (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable) (hint s₀)
      (by fun_prop : Measurable fun y => (f y : ℂ) * (Complex.exp (s₀ * t y) * t y)).aestronglyMeasurable
      (ae_of_all _ fun y s hs => ?_)
      ((hfi.mul_const R).mul_const _)
      (ae_of_all _ fun y s _ => ?_)
    · exact key.2.differentiableAt
    · by_cases h0 : f y = 0
      · simp [h0]
      have ht := hR y h0
      have hR0 : 0 ≤ R := (abs_nonneg _).trans ht
      have hs' : ‖s‖ ≤ ‖s₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' s s₀
        rw [Metric.mem_ball, dist_eq_norm] at hs
        linarith
      have e1 := norm_mul_cexp_le_of_abs_le_on_support (s := s) (hf0 y) (hR y)
      rw [← mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖(f y : ℂ) * Complex.exp (s * t y)‖ * |t y|
          ≤ (f y * Real.exp (‖s‖ * R)) * R := mul_le_mul e1 ht (abs_nonneg _) (mul_nonneg (hf0 y) (Real.exp_pos _).le)
        _ ≤ f y * R * Real.exp ((‖s₀‖ + 1) * R) := by
          have : Real.exp (‖s‖ * R) ≤ Real.exp ((‖s₀‖ + 1) * R) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs' hR0)
          have := mul_le_mul_of_nonneg_left this (mul_nonneg (hf0 y) hR0)
          nlinarith [this]
    · have := ((hasDerivAt_id s).mul_const (t y : ℂ)).cexp
      simp only [id, one_mul] at this
      exact this.const_mul (f y : ℂ)
  · intro r
    have hre : ∀ y, (f y : ℂ) * Complex.exp (r * t y) = ((f y * Real.exp (r * t y) : ℝ) : ℂ) := by
      intro y; push_cast; ring_nf
    simp_rw [hre]
    rw [integral_complex_ofReal]
    refine ⟨Complex.ofReal_im _, fun hpos => ?_⟩
    rw [Complex.ofReal_re]
    have gint : Integrable (fun y => f y * Real.exp (r * t y)) ν := by
      have := hint (r : ℂ)
      simp_rw [hre] at this
      exact this.re
    have hle : ∀ y, f y * Real.exp (-(|r| * R)) ≤ f y * Real.exp (r * t y) := by
      intro y
      by_cases h0 : f y = 0
      · simp [h0]
      apply mul_le_mul_of_nonneg_left _ (hf0 y)
      apply Real.exp_le_exp.mpr
      have ht := hR y h0
      have : |r * t y| ≤ |r| * R := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      linarith [neg_abs_le (r * t y)]
    calc 0 < (∫ y, f y ∂ν) * Real.exp (-(|r| * R)) := mul_pos hpos (Real.exp_pos _)
      _ = ∫ y, f y * Real.exp (-(|r| * R)) ∂ν := (integral_mul_const _ _).symm
      _ ≤ ∫ y, f y * Real.exp (r * t y) ∂ν := integral_mono (hfi.mul_const _) gint hle

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {ν : Measure G} [ν.IsHaarMeasure]
    {Γ : Subgroup G} [Countable Γ] {𝓖 : Set G}

theorem fundamentalDomain_lintegral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G) :
    ∫⁻ y in 𝓖, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂ν
      = ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν := by
  rw [lintegral_tsum (fun γ => by fun_prop)]
  set F : G → ENNReal := fun g => ‖P (x⁻¹ * g)‖ₑ * ‖a x‖ₑ * ‖b g‖ₑ with hF
  have key : ∀ γ : Γ, ∀ y, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = ‖P (x⁻¹ * ((γ : G)⁻¹ * y))‖ₑ * ‖a x‖ₑ * ‖b ((γ : G)⁻¹ * y)‖ₑ
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.lintegral_eq_tsum' F, ← lintegral_mul_left_eq_self _ x]
  simp [hF]

theorem fundamentalDomain_integral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G)
    (hfin : ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ≠ ⊤) :
    ∑' γ : Γ, ∫ y in 𝓖, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) ∂ν
      = ∫ g, star (a x) * b (x * g) * P g ∂ν := by
  set F : G → ℂ := fun g => star (a x) * b g * P (x⁻¹ * g) with hF
  have hFi : Integrable F ν := by
    refine ⟨by fun_prop, ?_⟩
    unfold HasFiniteIntegral
    rw [← lintegral_mul_left_eq_self _ x]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin.lt_top
    refine lintegral_congr (fun g => ?_)
    have hs : ‖star (a x)‖ₑ = ‖a x‖ₑ := by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
    simp only [hF, enorm_mul, hs, inv_mul_cancel_left]
    ring
  have key : ∀ γ : Γ, ∀ y, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = star (a x) * b ((γ : G)⁻¹ * y) * P (x⁻¹ * ((γ : G)⁻¹ * y))
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.integral_eq_tsum' F hFi, ← integral_mul_left_eq_self F x]
  simp [hF]

theorem unfold_tsum_fundamentalDomain (ν : Measure G) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (a b P : G → ℂ)
    (ha : Continuous a) (hbc : Continuous b) (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g)
    (hP : StronglyMeasurable P)
    (hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : Γ, ‖P (g₁⁻¹ * (γ : G)⁻¹ * g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤) :
    Integrable (fun g => P g * ∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ν ∧
    ∑' γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) =
      ∫ g, P g * (∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ∂ν := by
  have ham : Measurable a := ha.measurable
  have hbm : Measurable b := hbc.measurable
  have hPm : Measurable P := hP.measurable
  have hs : ∀ z : ℂ, ‖star z‖ₑ = ‖z‖ₑ := fun z => by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
  set μ := ν.restrict 𝓖 with hμ

  have hT : ∫⁻ x, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ∂μ ≠ ⊤ := by
    rw [← lintegral_congr (fun x => fundamentalDomain_lintegral_unfold_left h𝓖 hb hbm hPm (a := a) x)]
    exact hfin
  set k : G → G → ℂ := fun x g => star (a x) * b (x * g) * P g with hk
  have hkm : Measurable (Function.uncurry k) := by
    simp only [hk, Function.uncurry_def]; fun_prop
  have hki : Integrable (Function.uncurry k) (μ.prod ν) := by
    refine ⟨hkm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ (by fun_prop)]
    refine lt_of_le_of_lt (le_of_eq ?_) hT.lt_top
    refine lintegral_congr (fun x => lintegral_congr (fun g => ?_))
    simp only [hk, Function.uncurry_apply_pair, enorm_mul, hs]
    ring
  refine ⟨?_, ?_⟩
  · have h1 := hki.swap.integral_prod_left
    refine h1.congr (Filter.Eventually.of_forall (fun g => ?_))
    simp only [hk, Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]
    rw [integral_mul_const, mul_comm]

  · set f : Γ → G × G → ℂ := fun γ z => star (a z.1) * b z.2 * P (z.1⁻¹ * (γ : G)⁻¹ * z.2) with hf
    have hfm : ∀ γ, Measurable (f γ) := fun γ => by simp only [hf]; fun_prop
    have hfe : ∀ γ x y, ‖f γ (x, y)‖ₑ = ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ := by
      intro γ x y; simp only [hf, enorm_mul, hs]; ring
    have hsum : ∑' γ : Γ, ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ ≠ ⊤ := by
      rw [← lintegral_tsum (fun γ => ((hfm γ).enorm.lintegral_prod_right').aemeasurable)]
      have hx : ∀ x, ∑' γ : Γ, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ
          = ∫⁻ y, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂μ := fun x => by
        rw [← lintegral_tsum (f := fun γ y => ‖f γ (x, y)‖ₑ)
          (fun γ => ((hfm γ).comp measurable_prodMk_left).enorm.aemeasurable)]
        simp only [hfe]
      rw [lintegral_congr hx]
      exact hfin
    have hfi : ∀ γ, Integrable (f γ) (μ.prod μ) := fun γ =>
      ⟨(hfm γ).aestronglyMeasurable, by
        unfold HasFiniteIntegral
        rw [lintegral_prod _ (hfm γ).enorm.aemeasurable]
        exact lt_of_le_of_lt (ENNReal.le_tsum (f := fun γ : Γ => ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ) γ)
          hsum.lt_top⟩
    have lhs : ∀ γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν)
        = ∫ x, ∫ y, f γ (x, y) ∂μ ∂μ := by
      intro γ; rw [← Measure.prod_restrict, ← integral_prod _ (hfi γ)]
    rw [tsum_congr lhs, ← integral_tsum (fun γ => (hfi γ).integral_prod_left.aestronglyMeasurable)
      (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun γ =>
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm _))]
    have hae : ∀ᵐ x ∂μ, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν < ⊤ :=
      ae_lt_top (show Measurable (fun z : G × G => ‖P z.2‖ₑ * ‖a z.1‖ₑ * ‖b (z.1 * z.2)‖ₑ) by
        fun_prop).lintegral_prod_right' hT
    have step : (∫ x, ∑' γ : Γ, ∫ y, f γ (x, y) ∂μ ∂μ) = ∫ x, ∫ g, k x g ∂ν ∂μ :=
      integral_congr_ae (hae.mono fun x hx => fundamentalDomain_integral_unfold_left h𝓖 hb hbm hPm x hx.ne)
    rw [step, integral_integral_swap hki]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hk]
    rw [integral_mul_const, mul_comm]
end
end GlobalTheory
end

section

open MeasureTheory MulAction
open scoped Pointwise ENNReal

namespace GlobalTheory

section SlopeTestRemainingChoices
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem setIntegral_subgroup_mul_left (ν : Measure G) [ν.IsMulLeftInvariant] {Λ : Subgroup G}
    (c : Λ) (f : G → ℂ) (s : Set G) :
    ∫ g in s, f ((c : G) * g) ∂ν = ∫ g in c • s, f g ∂ν := by
  have hpre : (fun g : G => (c : G) * g) ⁻¹' (c • s) = s := by
    ext g
    simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  have h := (measurePreserving_mul_left ν (c : G)).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft (c : G)) f (c • s)
  rwa [hpre] at h

theorem setLIntegral_subgroup_mul_left (ν : Measure G) [ν.IsMulLeftInvariant] {Λ : Subgroup G}
    (c : Λ) (f : G → ℝ≥0∞) (s : Set G) :
    ∫⁻ g in s, f ((c : G) * g) ∂ν = ∫⁻ g in c • s, f g ∂ν := by
  have hpre : (fun g : G => (c : G) * g) ⁻¹' (c • s) = s := by
    ext g
    simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  have h := (measurePreserving_mul_left ν (c : G)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft (c : G)) f (c • s)
  rwa [hpre] at h

theorem isFundamentalDomain_iUnion_inv_smul {ν : Measure G} [ν.IsMulLeftInvariant]
    {Λ : Subgroup G} [Countable Λ] {𝓖 : Set G} (h : IsFundamentalDomain Λ 𝓖 ν)
    (S : Subgroup Λ) [Countable (Λ ⧸ S)] :
    IsFundamentalDomain (S.map Λ.subtype) (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ν := by
  refine ⟨.iUnion (fun q => h.nullMeasurableSet_smul q.out⁻¹), ?_, ?_⟩
  · filter_upwards [h.ae_covers] with g hg
    obtain ⟨l, hl⟩ := hg
    have hs : ((QuotientGroup.mk l : Λ ⧸ S).out)⁻¹ * l ∈ S :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
    refine ⟨⟨(((QuotientGroup.mk l : Λ ⧸ S).out⁻¹ * l : Λ) : G), ⟨_, hs, rfl⟩⟩,
      Set.mem_iUnion.2 ⟨QuotientGroup.mk l, ?_⟩⟩
    rw [Set.mem_inv_smul_set_iff]
    simpa [Subgroup.smul_def, mul_assoc] using hl
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
    have hsub : (⟨Λ.subtype s', hs⟩ : S.map Λ.subtype) • (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ∩
        (⟨Λ.subtype t', ht⟩ : S.map Λ.subtype) • (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ⊆
        ⋃ q : Λ ⧸ S, ⋃ r : Λ ⧸ S, ((s' * (q.out)⁻¹) • 𝓖 ∩ (t' * (r.out)⁻¹) • 𝓖) := by
      rintro x ⟨hx1, hx2⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_iUnion] at hx1 hx2
      obtain ⟨q, hq⟩ := hx1
      obtain ⟨r, hr⟩ := hx2
      rw [Set.mem_inv_smul_set_iff] at hq hr
      refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨r, ?_, ?_⟩⟩
      · rw [Set.mem_smul_set_iff_inv_smul_mem]
        simpa [Subgroup.smul_def, mul_assoc] using hq
      · rw [Set.mem_smul_set_iff_inv_smul_mem]
        simpa [Subgroup.smul_def, mul_assoc] using hr
    refine measure_mono_null hsub (measure_iUnion_null fun q => measure_iUnion_null fun r => ?_)
    apply h.aedisjoint
    intro he
    apply hst
    have he' : (q.out) * s'⁻¹ = (r.out) * t'⁻¹ := by
      have := congrArg (·⁻¹) he
      simpa [mul_inv_rev] using this
    have hqr : q = r := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r]
      apply QuotientGroup.eq.mpr
      have : (q.out)⁻¹ * r.out = s'⁻¹ * t' := by
        rw [← mul_inv_eq_iff_eq_mul.mpr he'.symm]
        group
      rw [this]
      exact S.mul_mem (S.inv_mem hs') ht'
    subst hqr
    have : s' = t' := by simpa using he'
    subst this
    rfl

end SlopeTestRemainingChoices

theorem tsum_setIntegral_eq_zero_of_stabilizer :
    ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G)
    [ν.IsMulLeftInvariant], SFinite ν → ∀ (Λ : Subgroup G), Countable Λ → ∀ 𝓖 : Set G,
    IsFundamentalDomain Λ 𝓖 ν → ∀ (a : Λ → X → X), (∀ x, a 1 x = x) →
    (∀ γ δ x, a (γ * δ) x = a γ (a δ x)) → ∀ F : X → G → ℂ,
    (∀ γ x g, F (a γ x) g = F x ((γ : G)⁻¹ * g)) → (∀ x, AEStronglyMeasurable (F x) ν) →
    ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν ≠ ⊤ →
    (∀ x (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x = x) → ∀ 𝓓 : Set G,
      IsFundamentalDomain Γ 𝓓 ν → IntegrableOn (F x) 𝓓 ν → ∫ g in 𝓓, F x g ∂ν = 0) →
    ∑' x, ∫ g in 𝓖, F x g ∂ν = 0 := by
  intro G X _ _ _ ν _ _ Λ hΛ 𝓖 h𝓖 a ha1 ham F hF hmeas hfin hzero
  letI : MulAction Λ X := { smul := a, one_smul := ha1, mul_smul := ham }
  have hsmul : ∀ (γ : Λ) (x : X), γ • x = a γ x := fun _ _ => rfl
  set T : X → ℂ := fun x => ∫ g in 𝓖, F x g ∂ν with hTdef
  have hT : ∀ (γ : Λ) x, T (γ • x) = ∫ g in γ⁻¹ • 𝓖, F x g ∂ν := by
    intro γ x
    rw [← setIntegral_subgroup_mul_left ν γ⁻¹]
    simp only [hTdef, hsmul, hF, Subgroup.coe_inv]
  have hL : ∀ (γ : Λ) x, ∫⁻ g in 𝓖, ‖F (γ • x) g‖ₑ ∂ν = ∫⁻ g in γ⁻¹ • 𝓖, ‖F x g‖ₑ ∂ν := by
    intro γ x
    rw [← setLIntegral_subgroup_mul_left ν γ⁻¹]
    simp only [hsmul, hF, Subgroup.coe_inv]
  have hsum : Summable T := by
    refine Summable.of_norm ?_
    have h1 : ∑' x, ‖T x‖ₑ ≠ ⊤ := ne_top_of_le_ne_top hfin
      (ENNReal.tsum_le_tsum fun x => enorm_integral_le_lintegral_enorm _)
    simpa using ENNReal.summable_toReal h1
  have horb : ∀ x₀ : X,
      HasSum (fun q : Λ ⧸ stabilizer Λ x₀ => T (ofQuotientStabilizer Λ x₀ q)) 0 := by
    intro x₀
    set S := stabilizer Λ x₀ with hSdef
    haveI : Countable (Λ ⧸ S) := QuotientGroup.mk_surjective.countable
    have hofq : ∀ q : Λ ⧸ S, ofQuotientStabilizer Λ x₀ q = q.out • x₀ := by
      intro q
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hinj : Function.Injective fun q : Λ ⧸ S => q.out • x₀ := by
      intro q r hqr
      exact injective_ofQuotientStabilizer Λ x₀ (by simpa only [hofq] using hqr)
    have hD := isFundamentalDomain_iUnion_inv_smul h𝓖 S
    have hdisj : Pairwise (Function.onFun (AEDisjoint ν) fun q : Λ ⧸ S => (q.out)⁻¹ • 𝓖) := by
      intro q r hqr
      refine h𝓖.aedisjoint fun e => hqr ?_
      exact Quotient.out_injective (inv_injective e)
    have hint : IntegrableOn (F x₀) (⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖) ν := by
      refine ⟨(hmeas x₀).restrict, ?_⟩
      show ∫⁻ g in ⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν < ⊤
      calc ∫⁻ g in ⋃ q : Λ ⧸ S, (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν
          ≤ ∑' q : Λ ⧸ S, ∫⁻ g in (q.out)⁻¹ • 𝓖, ‖F x₀ g‖ₑ ∂ν := lintegral_iUnion_le _ _
        _ = ∑' q : Λ ⧸ S, ∫⁻ g in 𝓖, ‖F (q.out • x₀) g‖ₑ ∂ν := by simp only [hL]
        _ ≤ ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun x => ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν)
        _ < ⊤ := hfin.lt_top
    have hmem : ∀ g, g ∈ S.map Λ.subtype ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x₀ = x₀ := by
      intro g
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h, hx⟩
        exact ⟨⟨g, h⟩, hx, rfl⟩
    have h0 := hzero x₀ (S.map Λ.subtype) hmem _ hD hint
    have hs := hasSum_integral_iUnion_ae (fun q => h𝓖.nullMeasurableSet_smul _) hdisj hint
    rw [h0] at hs
    simpa only [hofq, hT] using hs
  let e := selfEquivSigmaOrbitsQuotientStabilizer Λ X
  have h1 : HasSum (T ∘ e.symm) (∑' x, T x) := (e.symm.hasSum_iff).2 hsum.hasSum
  have h2 : HasSum (fun _ : Quotient (orbitRel Λ X) => (0 : ℂ)) (∑' x, T x) := by
    refine h1.sigma fun ω => ?_
    convert horb ω.out using 2 with q
    rfl
  exact h2.unique hasSum_zero

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem tsum_setIntegral_prod_eq_zero_of_inner :
    ∀ {G X : Type} [MeasurableSpace G], Countable X → ∀ (ν : Measure G), SFinite ν → ∀ (𝓖 : Set G) (H : X → G × G → ℂ), (∀ x, AEStronglyMeasurable (H x) (ν.prod ν)) → ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' x, ‖H x (g₁, g₂)‖ₑ ∂ν ∂ν ≠ ⊤ → (∀ g₂, ∑' x, ∫⁻ g₁ in 𝓖, ‖H x (g₁, g₂)‖ₑ ∂ν ≠ ⊤ → ∑' x, ∫ g₁ in 𝓖, H x (g₁, g₂) ∂ν = 0) → ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν) = 0 := by
  intro G X _ hX ν hν 𝓖 H hH hfin hslice
  set μ := ν.restrict 𝓖 with hμ
  have hprod : (ν.prod ν).restrict (𝓖 ×ˢ 𝓖) = μ.prod μ := (Measure.prod_restrict 𝓖 𝓖).symm
  have hHm : ∀ x, AEStronglyMeasurable (H x) (μ.prod μ) := fun x => by
    rw [← hprod]; exact (hH x).restrict
  have hFm : AEMeasurable (fun p => ∑' x, ‖H x p‖ₑ) (μ.prod μ) :=
    AEMeasurable.tsum fun x => (hHm x).enorm
  have hFint : ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) ≠ ⊤ := by
    rw [lintegral_prod _ hFm]; exact hfin
  have hsum : ∑' x, ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) = ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) :=
    (lintegral_tsum fun x => (hHm x).enorm).symm
  have hInt : ∀ x, Integrable (H x) (μ.prod μ) := fun x =>
    ⟨hHm x, by
      have : ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) ≤ ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) :=
        lintegral_mono fun p => ENNReal.le_tsum (f := fun x => ‖H x p‖ₑ) x
      exact lt_of_le_of_lt this (lt_top_iff_ne_top.2 hFint)⟩
  have hswap : ∀ x, ∫⁻ g₂, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ∂μ = ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) :=
    fun x => (lintegral_prod_symm _ (hHm x).enorm).symm
  have hLm : ∀ x, AEMeasurable (fun g₂ => ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ) μ := fun x =>
    ((hHm x).enorm.prod_swap).lintegral_prod_right'
  have hG2 : ∀ᵐ g₂ ∂μ, ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ≠ ⊤ := by
    have hm : AEMeasurable (fun g₂ => ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ) μ :=
      AEMeasurable.tsum hLm
    have hi : ∫⁻ g₂, ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum hLm, tsum_congr hswap, hsum]; exact hFint
    filter_upwards [ae_lt_top' hm hi] with g₂ h using h.ne
  have hKm : ∀ x, AEStronglyMeasurable (fun g₂ => ∫ g₁, H x (g₁, g₂) ∂μ) μ := fun x =>
    (hHm x).prod_swap.integral_prod_right'
  have hKfin : ∑' x, ∫⁻ g₂, ‖∫ g₁, H x (g₁, g₂) ∂μ‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hFint ?_
    rw [← hsum]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [← hswap x]
    exact lintegral_mono fun g₂ => enorm_integral_le_lintegral_enorm _
  have key := integral_tsum hKm hKfin
  have h0 : ∫ g₂, ∑' x, ∫ g₁, H x (g₁, g₂) ∂μ ∂μ = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hG2] with g₂ h using hslice g₂ h
  calc ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν)
        = ∑' x, ∫ g₂, ∫ g₁, H x (g₁, g₂) ∂μ ∂μ := by
          refine tsum_congr fun x => ?_
          rw [hprod]; exact integral_prod_symm _ (hInt x)
    _ = 0 := by rw [← key, h0]

end GlobalTheory
end
