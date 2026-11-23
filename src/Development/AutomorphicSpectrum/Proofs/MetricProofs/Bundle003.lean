module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

section

open MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.Conv

lemma fatou_real {α : Type} [MeasurableSpace α] {ν : Measure α} {g : ℕ → α → ℝ} {g0 : α → ℝ}
    {c : ℝ} (hi : ∀ k, Integrable (g k) ν) (hnn : ∀ k, ∀ᵐ y ∂ν, 0 ≤ g k y)
    (hlim : ∀ᵐ y ∂ν, Tendsto (fun k => g k y) atTop (𝓝 (g0 y)))
    (hc : ∀ k, ∫ y, g k y ∂ν ≤ c) :
    Integrable g0 ν ∧ ∫ y, g0 y ∂ν ≤ c := by
  have hm : AEStronglyMeasurable g0 ν :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hi k).aestronglyMeasurable) hlim
  have hnn0 : ∀ᵐ y ∂ν, 0 ≤ g0 y := by
    filter_upwards [ae_all_iff.2 hnn, hlim] with y h1 h2
    exact ge_of_tendsto' h2 h1
  have hc0 : 0 ≤ c := (integral_nonneg_of_ae (hnn 0)).trans (hc 0)
  have hk : ∀ k, ∫⁻ y, ENNReal.ofReal (g k y) ∂ν ≤ ENNReal.ofReal c := fun k => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi k) (hnn k)]
    exact ENNReal.ofReal_le_ofReal (hc k)
  have hle : ∫⁻ y, ENNReal.ofReal (g0 y) ∂ν ≤ ENNReal.ofReal c := by
    calc ∫⁻ y, ENNReal.ofReal (g0 y) ∂ν
        = ∫⁻ y, liminf (fun k => ENNReal.ofReal (g k y)) atTop ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hlim] with y hy
          exact ((ENNReal.continuous_ofReal.tendsto _).comp hy).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ y, ENNReal.ofReal (g k y) ∂ν) atTop :=
          lintegral_liminf_le' (fun k => (hi k).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal c := liminf_le_of_frequently_le' (Frequently.of_forall hk)
  have hint : Integrable g0 ν :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal hnn0).2 (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  have := hle
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn0] at this
  exact (ENNReal.ofReal_le_ofReal_iff hc0).1 this

lemma tail_bound {α : Type} [MeasurableSpace α] {μ : Measure α} {S E0 : Set α}
    (hS : MeasurableSet S) (hSE : S ⊆ E0ᶜ) {L ρ Γ : α → ℝ} {a c : ℝ} (ha : 0 ≤ a)
    (hρm : AEStronglyMeasurable ρ μ) (hΓm : AEStronglyMeasurable Γ μ)
    (hρ : ∀ᵐ y ∂μ, 0 ≤ ρ y) (hΓ : ∀ᵐ y ∂μ, y ∉ E0 → |Γ y| ≤ a * L y)
    (hi : IntegrableOn (fun y => L y * ρ y) S μ) (hc : ∫ y in S, L y * ρ y ∂μ ≤ c) :
    IntegrableOn (fun y => Γ y * ρ y) S μ ∧ |∫ y in S, Γ y * ρ y ∂μ| ≤ a * c := by
  have hb : ∀ᵐ y ∂μ.restrict S, ‖Γ y * ρ y‖ ≤ a * (L y * ρ y) := by
    rw [ae_restrict_iff' hS]
    filter_upwards [hρ, hΓ] with y h1 h2 hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (h2 (hSE hy)) h1
  have hi' : Integrable (fun y => a * (L y * ρ y)) (μ.restrict S) := Integrable.const_mul hi a
  refine ⟨Integrable.mono' hi' (hΓm.mul hρm).restrict hb, ?_⟩
  calc |∫ y in S, Γ y * ρ y ∂μ| = ‖∫ y in S, Γ y * ρ y ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y in S, a * (L y * ρ y) ∂μ := norm_integral_le_of_norm_le hi' hb
    _ = a * ∫ y in S, L y * ρ y ∂μ := integral_const_mul _ _
    _ ≤ a * c := mul_le_mul_of_nonneg_left hc ha

theorem tendsto_integral_of_exhaustion {α : Type} [MeasurableSpace α] (μ : Measure α)
    (l : Filter ℝ) [l.NeBot] [l.IsCountablyGenerated] (E : ℕ → Set α) (L : α → ℝ)
    (ρ Γ : ℝ → α → ℝ) (ρ0 Γ0 : α → ℝ) (a : ℝ) (b : ℕ → ℝ)
    (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E) (hfin : ∀ n, μ (E n) < ⊤)
    (hcov : ∀ᵐ y ∂μ, ∃ n, y ∈ E n) (hL : ∀ᵐ y ∂μ, 0 ≤ L y) (ha : 0 ≤ a)
    (hb : Tendsto b atTop (𝓝 0))
    (hρ : ∀ n, TendstoUniformlyOn ρ ρ0 l (E n)) (hΓ : ∀ n, TendstoUniformlyOn Γ Γ0 l (E n))
    (hM : ∀ n, ∃ M : ℝ, ∀ y ∈ E n, |ρ0 y| ≤ M ∧ |Γ0 y| ≤ M)
    (hev : ∀ᶠ t in l, AEStronglyMeasurable (ρ t) μ ∧ AEStronglyMeasurable (Γ t) μ ∧
      (∀ᵐ y ∂μ, 0 ≤ ρ t y) ∧ (∀ᵐ y ∂μ, y ∉ E 0 → |Γ t y| ≤ a * L y) ∧
      ∀ n, IntegrableOn (fun y => L y * ρ t y) (E n)ᶜ μ ∧ ∫ y in (E n)ᶜ, L y * ρ t y ∂μ ≤ b n) :
    Integrable (fun y => Γ0 y * ρ0 y) μ ∧ (∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ) ∧
      Tendsto (fun t => ∫ y, Γ t y * ρ t y ∂μ) l (𝓝 (∫ y, Γ0 y * ρ0 y ∂μ)) := by
  obtain ⟨u, hu⟩ := exists_seq_tendsto l
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hu.eventually hev)
  have hv : Tendsto (fun k => u (k + K)) atTop l := (tendsto_add_atTop_iff_nat K).2 hu
  have hG := fun k => hK (k + K) (Nat.le_add_left K k)
  have hpt : ∀ᵐ y ∂μ, Tendsto (fun k => ρ (u (k + K)) y) atTop (𝓝 (ρ0 y)) ∧
      Tendsto (fun k => Γ (u (k + K)) y) atTop (𝓝 (Γ0 y)) := by
    filter_upwards [hcov] with y hy
    obtain ⟨n, hn⟩ := hy
    exact ⟨((hρ n).tendsto_at hn).comp hv, ((hΓ n).tendsto_at hn).comp hv⟩
  have hρ0m : AEStronglyMeasurable ρ0 μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hG k).1) (hpt.mono fun _ h => h.1)
  have hΓ0m : AEStronglyMeasurable Γ0 μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hG k).2.1) (hpt.mono fun _ h => h.2)
  have hρ0nn : ∀ᵐ y ∂μ, 0 ≤ ρ0 y := by
    filter_upwards [ae_all_iff.2 (fun k => (hG k).2.2.1), hpt] with y h1 h2
    exact ge_of_tendsto' h2.1 h1
  have hΓ0b : ∀ᵐ y ∂μ, y ∉ E 0 → |Γ0 y| ≤ a * L y := by
    filter_upwards [ae_all_iff.2 (fun k => (hG k).2.2.2.1), hpt] with y h1 h2 hy
    exact le_of_tendsto' h2.2.abs (fun k => h1 k hy)
  have htail0 : ∀ n, IntegrableOn (fun y => L y * ρ0 y) (E n)ᶜ μ ∧
      ∫ y in (E n)ᶜ, L y * ρ0 y ∂μ ≤ b n := fun n =>
    fatou_real (g := fun k y => L y * ρ (u (k + K)) y)
      (fun k => ((hG k).2.2.2.2 n).1)
      (fun k => ae_restrict_of_ae (by
        filter_upwards [hL, (hG k).2.2.1] with y h1 h2
        exact mul_nonneg h1 h2))
      (ae_restrict_of_ae (by
        filter_upwards [hpt] with y h
        exact h.1.const_mul (L y)))
      (fun k => ((hG k).2.2.2.2 n).2)
  have hsub : ∀ n, (E n)ᶜ ⊆ (E 0)ᶜ := fun n =>
    Set.compl_subset_compl.2 (hmono (Nat.zero_le n))
  have htailLim : ∀ n, IntegrableOn (fun y => Γ0 y * ρ0 y) (E n)ᶜ μ ∧
      |∫ y in (E n)ᶜ, Γ0 y * ρ0 y ∂μ| ≤ a * b n := fun n =>
    tail_bound (hEm n).compl (hsub n) ha hρ0m hΓ0m hρ0nn hΓ0b (htail0 n).1 (htail0 n).2
  have htailT : ∀ᶠ t in l, ∀ n, IntegrableOn (fun y => Γ t y * ρ t y) (E n)ᶜ μ ∧
      |∫ y in (E n)ᶜ, Γ t y * ρ t y ∂μ| ≤ a * b n := hev.mono fun t h n =>
    tail_bound (hEm n).compl (hsub n) ha h.1 h.2.1 h.2.2.1 h.2.2.2.1
      (h.2.2.2.2 n).1 (h.2.2.2.2 n).2
  have hB : ∀ n, ∃ C : ℝ, (∀ y ∈ E n, |Γ0 y * ρ0 y| ≤ C) ∧
      ∀ᶠ t in l, ∀ y ∈ E n, |Γ t y * ρ t y| ≤ C := by
    intro n
    obtain ⟨M, hM'⟩ := hM n
    have hC : (0 : ℝ) ≤ |M| + 1 := by positivity
    have key : ∀ x z : ℝ, |x| ≤ |M| + 1 → |z| ≤ |M| + 1 → |x * z| ≤ (|M| + 1) * (|M| + 1) := by
      intro x z h1 h2
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hC
    have near : ∀ x z : ℝ, |z| ≤ M → dist z x < 1 → |x| ≤ |M| + 1 := by
      intro x z h1 h2
      rw [Real.dist_eq] at h2
      have h3 := abs_sub_abs_le_abs_sub x z
      rw [abs_sub_comm x z] at h3
      have h4 := le_abs_self M
      linarith
    refine ⟨(|M| + 1) * (|M| + 1), fun y hy => ?_, ?_⟩
    · have h4 := le_abs_self M
      exact key _ _ (by linarith [(hM' y hy).2]) (by linarith [(hM' y hy).1])
    · filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hρ n) 1 one_pos,
        Metric.tendstoUniformlyOn_iff.1 (hΓ n) 1 one_pos] with t h1 h2 y hy
      exact key _ _ (near _ _ (hM' y hy).2 (h2 y hy)) (near _ _ (hM' y hy).1 (h1 y hy))
  have hhead0 : ∀ n, IntegrableOn (fun y => Γ0 y * ρ0 y) (E n) μ := by
    intro n
    obtain ⟨C, hC, -⟩ := hB n
    exact Measure.integrableOn_of_bounded (hfin n).ne (hΓ0m.mul hρ0m) (M := C)
      (ae_restrict_of_forall_mem (hEm n) hC)
  have hheadT : ∀ n, ∀ᶠ t in l, IntegrableOn (fun y => Γ t y * ρ t y) (E n) μ := by
    intro n
    obtain ⟨C, -, hC⟩ := hB n
    filter_upwards [hev, hC] with t h1 h2
    exact Measure.integrableOn_of_bounded (hfin n).ne (h1.2.1.mul h1.1) (M := C)
      (ae_restrict_of_forall_mem (hEm n) h2)
  have hU : ∀ f : α → ℝ, IntegrableOn f (E 0) μ → IntegrableOn f (E 0)ᶜ μ → Integrable f μ := by
    intro f h1 h2
    have := h1.union h2
    rwa [Set.union_compl_self, integrableOn_univ] at this
  have hI0 : Integrable (fun y => Γ0 y * ρ0 y) μ := hU _ (hhead0 0) (htailLim 0).1
  have hIT : ∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ := by
    filter_upwards [htailT, hheadT 0] with t h1 h2
    exact hU _ h2 (h1 0).1
  refine ⟨hI0, hIT, ?_⟩
  have hconv : ∀ n, Tendsto (fun t => ∫ y in E n, Γ t y * ρ t y ∂μ) l
      (𝓝 (∫ y in E n, Γ0 y * ρ0 y ∂μ)) := by
    intro n
    obtain ⟨C, -, hC⟩ := hB n
    haveI : IsFiniteMeasure (μ.restrict (E n)) := ⟨by simpa using hfin n⟩
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_
      (integrable_const C) ?_
    · exact hev.mono fun t h => (h.2.1.mul h.1).restrict
    · exact hC.mono fun t h => ae_restrict_of_forall_mem (hEm n) h
    · exact ae_restrict_of_forall_mem (hEm n) fun y hy =>
        ((hΓ n).tendsto_at hy).mul ((hρ n).tendsto_at hy)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hbn : Tendsto (fun n => a * |b n|) atTop (𝓝 0) := by
    simpa using hb.abs.const_mul a
  obtain ⟨n, hn⟩ := (hbn.eventually (Iio_mem_nhds hε3)).exists
  have hn' : a * |b n| < ε / 3 := hn
  have hab : a * b n ≤ a * |b n| := mul_le_mul_of_nonneg_left (le_abs_self _) ha
  filter_upwards [Metric.tendsto_nhds.1 (hconv n) (ε / 3) hε3, htailT, hIT] with t h1 h2 h3
  have e1 : ∫ y in E n, Γ t y * ρ t y ∂μ + ∫ y in (E n)ᶜ, Γ t y * ρ t y ∂μ =
      ∫ y, Γ t y * ρ t y ∂μ := integral_add_compl (hEm n) h3
  have e2 : ∫ y in E n, Γ0 y * ρ0 y ∂μ + ∫ y in (E n)ᶜ, Γ0 y * ρ0 y ∂μ =
      ∫ y, Γ0 y * ρ0 y ∂μ := integral_add_compl (hEm n) hI0
  have A := (h2 n).2
  have B := (htailLim n).2
  rw [Real.dist_eq] at h1 ⊢
  rw [← e1, ← e2]
  rw [abs_lt] at h1 ⊢
  rw [abs_le] at A B
  constructor <;> linarith [h1.1, h1.2, A.1, A.2, B.1, B.2]

end GlobalTheory.CompanionTheory.Conv
end

section

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem limRate_log_inv_exp (s : ℝ) : Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) = (s ^ 2)⁻¹ := by
  rw [one_div, Real.log_inv, Real.log_exp, neg_neg]

theorem limRate_sq_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [mul_nonneg hx (sq_nonneg (x - 3 / 2))]

theorem limRate_mul_log_sq_le {s : ℝ} (hs : 0 < s) (h1 : s ≤ 1) : s * Real.log s ^ 2 ≤ 1 := by
  have h := limRate_sq_le_exp (x := -Real.log s) (by linarith [Real.log_nonpos hs.le h1])
  rw [Real.exp_neg, Real.exp_log hs, neg_sq] at h
  calc s * Real.log s ^ 2 ≤ s * s⁻¹ := mul_le_mul_of_nonneg_left h hs.le
    _ = 1 := mul_inv_cancel₀ hs.ne'

theorem limRate : Filter.Tendsto (fun t : ℝ => Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧ (∀ s : ℝ, 0 < s → s ≤ 1 → Real.log (Real.log (1 / Real.exp (-(s ^ 2)⁻¹))) ^ 2 / Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) ≤ 4 * s) ∧ (∀ s : ℝ, 0 < s → s ≤ 1 → Real.exp (-(s ^ 2)⁻¹) ^ ((1 : ℝ) / 3) ≤ 2 * s) ∧ ∀ C ε : ℝ, 0 < ε → ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → C * Real.log (Real.log (1 / Real.exp (-(s ^ 2)⁻¹))) / Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) ≤ ε * s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hl : Filter.Tendsto (fun t : ℝ => Real.log (1 / t)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      simp only [one_div]
      exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hl
    refine h.congr fun t => ?_
    simp
  · intro s hs h1
    rw [limRate_log_inv_exp, Real.log_inv, Real.log_pow, div_inv_eq_mul]
    have h3 := limRate_mul_log_sq_le hs h1
    push_cast
    have e : (-(2 * Real.log s)) ^ 2 * s ^ 2 = 4 * s * (s * Real.log s ^ 2) := by ring
    rw [e]
    nlinarith
  · intro s hs h1
    rw [← Real.exp_mul]
    set y := (s ^ 2)⁻¹ with hy
    have hys : y * s ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
    have hy0 : 0 ≤ y := by positivity
    have ha := Real.add_one_le_exp (y * (1 / 3))
    have hE : 0 < Real.exp (y * (1 / 3)) := Real.exp_pos _
    rw [show -y * (1 / 3) = -(y * (1 / 3)) by ring, Real.exp_neg]
    have hkey : 1 ≤ 2 * s * (1 + y * (1 / 3)) := by
      nlinarith [sq_nonneg (s - 1 / 4), mul_pos hs hs]
    calc (Real.exp (y * (1 / 3)))⁻¹ ≤ (1 + y * (1 / 3))⁻¹ :=
          inv_anti₀ (by positivity) (by linarith)
      _ ≤ 2 * s := by
          rw [inv_le_iff_one_le_mul₀ (by positivity)]
          linarith
  · intro C ε hε
    set K := 2 * |C| + 1 with hK
    have hKpos : 0 < K := by positivity
    refine ⟨min 1 ((ε / K) ^ 2), by positivity, ?_⟩
    intro s hs hs0
    have h1 : s ≤ 1 := le_trans hs0 (min_le_left _ _)
    have h2 : s ≤ (ε / K) ^ 2 := le_trans hs0 (min_le_right _ _)
    rw [limRate_log_inv_exp, Real.log_inv, Real.log_pow, div_inv_eq_mul]
    push_cast
    have h3 := limRate_mul_log_sq_le hs h1
    have hsq : (s * Real.log s) ^ 2 ≤ (ε / K) ^ 2 := by
      calc (s * Real.log s) ^ 2 = s * (s * Real.log s ^ 2) := by ring
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left h3 hs.le
        _ ≤ (ε / K) ^ 2 := by linarith
    have habs : |s * Real.log s| ≤ ε / K := abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))
    have hb : -2 * C * (s * Real.log s) ≤ ε := by
      calc -2 * C * (s * Real.log s) ≤ |-2 * C * (s * Real.log s)| := le_abs_self _
        _ = 2 * |C| * |s * Real.log s| := by
            rw [abs_mul, abs_mul, abs_neg, abs_two]
        _ ≤ 2 * |C| * (ε / K) := mul_le_mul_of_nonneg_left habs (by positivity)
        _ ≤ ε := by
            rw [mul_div_assoc', div_le_iff₀ hKpos, hK]
            nlinarith [abs_nonneg C]
    calc C * -(2 * Real.log s) * s ^ 2 = s * (-2 * C * (s * Real.log s)) := by ring
      _ ≤ s * ε := mul_le_mul_of_nonneg_left hb hs.le
      _ = ε * s := mul_comm _ _

end GlobalTheory.CompanionTheory.Ar.PB
end

section

namespace GlobalTheory.CompanionTheory.Ar.Exchange

theorem exists_completion_by_members (g m r : ℕ) (w : Fin r → Fin g → ℂ) (b : Fin m → Fin g → ℂ)
    (hw : LinearIndependent ℂ w) (hb : LinearIndependent ℂ b)
    (hwb : ∀ a, w a ∈ Submodule.span ℂ (Set.range b)) :
    ∃ (k : ℕ) (J : Fin k → Fin m), r + k = m ∧
      LinearIndependent ℂ (Fin.append w (fun j => b (J j))) := by
  classical
  let v : Fin r ⊕ Fin m → (Fin g → ℂ) := Sum.elim w b
  have hs : LinearIndepOn ℂ v (Set.range Sum.inl) := by
    rw [linearIndepOn_range_iff Sum.inl_injective]
    exact hw
  obtain ⟨B, -, hsB, hspan, hB⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  let S : Finset (Fin m) := Finset.univ.filter fun j => Sum.inr j ∈ B
  let J : Fin S.card → Fin m := S.orderEmbOfFin rfl
  let φ : Fin (r + S.card) → Fin r ⊕ Fin m := Fin.append Sum.inl (Sum.inr ∘ J)
  have hφ : Function.Injective φ :=
    Fin.append_injective_iff.mpr ⟨Sum.inl_injective,
      Sum.inr_injective.comp (S.orderEmbOfFin rfl).injective, fun _ _ => Sum.inl_ne_inr⟩
  have hJS : ∀ l, J l ∈ S := fun l => S.orderEmbOfFin_mem rfl l
  have hφB : Set.range φ ⊆ B := by
    rintro _ ⟨l, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun l => ?_) l
    · simp only [φ, Fin.append_left]
      exact hsB ⟨i, rfl⟩
    · simp only [φ, Fin.append_right, Function.comp_apply]
      have := hJS l
      simpa [S] using this
  have hBφ : B ⊆ Set.range φ := by
    rintro (i | j) hx
    · exact ⟨Fin.castAdd _ i, by simp [φ]⟩
    · have hj : j ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        simp [S, hx]
      obtain ⟨l, hl⟩ := hj
      exact ⟨Fin.natAdd _ l, by simp [φ, J, hl]⟩
  have hu : LinearIndependent ℂ (v ∘ φ) := by
    rw [← linearIndepOn_range_iff hφ]
    exact hB.mono hφB
  have hle1 : Submodule.span ℂ (Set.range (v ∘ φ)) ≤ Submodule.span ℂ (Set.range b) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    show v (φ l) ∈ _
    generalize φ l = x
    rcases x with i | j
    · exact hwb i
    · exact Submodule.subset_span ⟨j, rfl⟩
  have hle2 : Submodule.span ℂ (Set.range b) ≤ Submodule.span ℂ (Set.range (v ∘ φ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : b j ∈ Submodule.span ℂ (v '' B) := hspan ⟨Sum.inr j, Set.mem_univ _, rfl⟩
    have h2 : v '' B ⊆ Set.range (v ∘ φ) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨l, rfl⟩ := hBφ hx
      exact ⟨l, rfl⟩
    exact Submodule.span_mono h2 h1
  have hueq : (Fin.append w fun j => b (J j)) = v ∘ φ := by
    funext l
    refine Fin.addCases (fun i => ?_) (fun l => ?_) l
    · simp [φ, v]
    · simp [φ, v]
  refine ⟨S.card, J, ?_, ?_⟩
  · have e1 := finrank_span_eq_card hu
    have e2 := finrank_span_eq_card hb
    rw [le_antisymm hle1 hle2, e2] at e1
    simpa using e1.symm
  · rw [hueq]
    exact hu

end GlobalTheory.CompanionTheory.Ar.Exchange
end

section

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_isFundamentalDomain_of_relIndex_ne_zero :
    ∀ (G X : Type) [Group G] [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
      (μ : Measure X) [SMulInvariantMeasure G X μ] (Γ₀ Γ : Subgroup G) [Countable Γ] (s : Set X),
      Γ₀ ≤ Γ → Γ₀.relIndex Γ ≠ 0 → IsFundamentalDomain Γ s μ →
      ∃ t : Set X, IsFundamentalDomain Γ₀ t μ ∧ μ t = (Γ₀.relIndex Γ : ℝ≥0∞) * μ s := by
  intro G X _ _ _ _ μ _ Γ₀ Γ _ s hle hidx hs
  classical
  set H : Subgroup Γ := Γ₀.subgroupOf Γ with hH
  have : H.FiniteIndex := ⟨hidx⟩
  let _ : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let ρ : Γ ⧸ H → Γ := fun q => q.out
  have hout : ∀ q : Γ ⧸ H, ((ρ q : Γ) : Γ ⧸ H) = q := fun q => QuotientGroup.out_eq' q
  have hρ : ∀ γ : Γ, (ρ (γ : Γ ⧸ H))⁻¹ * γ ∈ H := fun γ => QuotientGroup.eq.mp (hout _)
  let ι : Γ₀ → Γ := fun g => ⟨g, hle g.2⟩
  have key : ∀ (g : Γ₀) (γ : Γ), g • (γ • s) = (ι g * γ) • s := by
    intro g γ
    rw [mul_smul]
    rfl
  let t : Set X := ⋃ q : Γ ⧸ H, (ρ q)⁻¹ • s
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) fun q : Γ ⧸ H => (ρ q)⁻¹ • s) := by
    intro q q' hqq'
    apply hs.aedisjoint
    intro heq
    apply hqq'
    have h1 : ρ q = ρ q' := inv_injective heq
    rw [← hout q, ← hout q', h1]
  refine ⟨t, ⟨NullMeasurableSet.iUnion fun q => hs.nullMeasurableSet_smul _, ?_, ?_⟩, ?_⟩
  · filter_upwards [hs.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    refine ⟨⟨(((ρ (γ : Γ ⧸ H))⁻¹ * γ : Γ) : G), Subgroup.mem_subgroupOf.mp (hρ γ)⟩, ?_⟩
    refine Set.mem_iUnion.2 ⟨(γ : Γ ⧸ H), ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    convert hγ using 1
    simp [Subgroup.smul_def, smul_smul]
  · intro g g' hgg'
    show AEDisjoint μ (g • t) (g' • t)
    simp only [t, Set.smul_set_iUnion]
    rw [AEDisjoint.iUnion_left_iff]
    intro q
    rw [AEDisjoint.iUnion_right_iff]
    intro q'
    rw [key, key]
    apply hs.aedisjoint
    intro heq
    apply hgg'
    have h1 : (ρ q')⁻¹ * ρ q = (ι g')⁻¹ * ι g := by
      calc (ρ q')⁻¹ * ρ q = (ι g')⁻¹ * (ι g' * (ρ q')⁻¹) * ρ q := by group
        _ = (ι g')⁻¹ * (ι g * (ρ q)⁻¹) * ρ q := by rw [heq]
        _ = (ι g')⁻¹ * ι g := by group
    have h2 : (ι g')⁻¹ * ι g ∈ H := by
      rw [Subgroup.mem_subgroupOf]
      simpa [ι] using Γ₀.mul_mem (Γ₀.inv_mem g'.2) g.2
    have h3 : q' = q := by
      rw [← hout q', ← hout q]
      exact QuotientGroup.eq.mpr (h1 ▸ h2)
    subst h3
    have h4 : ι g = ι g' := mul_right_cancel heq
    have h5 : ((ι g : Γ) : G) = ((ι g' : Γ) : G) := by rw [h4]
    exact Subtype.ext h5
  · rw [measure_iUnion₀ hdisj (fun q => hs.nullMeasurableSet_smul _)]
    have hm : ∀ q, μ ((ρ q)⁻¹ • s) = μ s := fun q => by
      show μ (((ρ q)⁻¹ : Γ) • s) = μ s
      rw [show ((ρ q)⁻¹ : Γ) • s = (((ρ q)⁻¹ : Γ) : G) • s from rfl]
      exact measure_smul μ _ _
    simp only [hm, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [← Nat.card_eq_fintype_card]
    rfl

end GlobalTheory.CompanionTheory.Ar.Cmp
end
