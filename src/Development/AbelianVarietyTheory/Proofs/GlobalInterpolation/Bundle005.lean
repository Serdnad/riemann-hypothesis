module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

section

namespace GlobalTheory.CharacterConductorBall

private lemma norm_sub_one_le_norm_mul_self_sub_one (w : ℂ) (h : ‖w - 1‖ < 1 / 2) :
    3 / 2 * ‖w - 1‖ ≤ ‖w * w - 1‖ := by
  have h1 : w * w - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (2 : ℝ) ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have := norm_sub_le (w + 1) (w - 1)
    have e : (w + 1) - (w - 1) = (2 : ℂ) := by ring
    rw [e] at this
    simpa using this
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (w - 1)]

theorem eq_one_of_norm_sub_one_lt {A : Type} [AddMonoid A] (ψ : AddChar A ℂ) (B : Set A)
    (hB : ∀ x ∈ B, x + x ∈ B) (hψ : ∀ x ∈ B, ‖ψ x - 1‖ < 1 / 2) : ∀ x ∈ B, ψ x = 1 := by

  have key : ∀ k : ℕ, ∀ x ∈ B, (3 / 2 : ℝ) ^ k * ‖ψ x - 1‖ < 1 / 2 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hψ x hx
    | succ k ih =>
      intro x hx
      have h2 := ih (x + x) (hB x hx)
      have h3 := norm_sub_one_le_norm_mul_self_sub_one (ψ x) (hψ x hx)
      rw [AddChar.map_add_eq_mul] at h2
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖ψ x - 1‖ = (3 / 2) ^ k * (3 / 2 * ‖ψ x - 1‖) := by ring
        _ ≤ (3 / 2) ^ k * ‖ψ x * ψ x - 1‖ := by gcongr
        _ < 1 / 2 := h2
  intro x hx
  by_contra hne
  have hpos : 0 < ‖ψ x - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖ψ x - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have := key k x hx
  rw [div_lt_iff₀ hpos] at hk
  linarith

theorem exists_ball_trivial {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous (ψ : K → ℂ)) :
    ∃ m : ℤ, ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1 := by

  have hnhds : (ψ : K → ℂ) ⁻¹' {w : ℂ | ‖w - 1‖ < 1 / 2} ∈ nhds (0 : K) := by
    apply hc.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hnhds
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc_def
  have hc0 : c ≠ 0 := by
    have := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (zero_lt_iff.2 γ.ne_zero)
    rw [map_zero] at this
    exact this.ne'

  have hlt : ∀ y ∈ {y : K | Valued.v y < c}, ψ y = 1 := by
    refine eq_one_of_norm_sub_one_lt ψ _ (fun y hy => ?_) (fun y hy => ?_)
    · exact lt_of_le_of_lt ((Valued.v.map_add y y).trans (max_self _).le) hy
    · apply hγ
      simpa [Valuation.restrict_lt_iff_lt_embedding] using hy
  refine ⟨WithZero.log c - 1, fun x hx => hlt x ?_⟩
  calc Valued.v x ≤ WithZero.exp (WithZero.log c - 1) := hx
    _ < WithZero.exp (WithZero.log c) := WithZero.exp_lt_exp.2 (by omega)
    _ = c := WithZero.exp_log hc0

private lemma addChar_trivial_mul_of_valuation_le {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) {t t' : K}
    (ht : ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1)
    (hle : Valued.v t' ≤ Valued.v t) :
    ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t' * s) = 1 := by
  intro s hs
  by_cases h0 : t = 0
  · subst h0
    have : t' = 0 := by simpa using hle
    simp [this, AddChar.map_zero_eq_one]
  · have hv : Valued.v t ≠ 0 := by simpa using h0
    have e : t' * s = t * (t' * t⁻¹ * s) := by field_simp
    rw [e]
    apply ht
    rw [map_mul, map_mul, map_inv₀]
    calc Valued.v t' * (Valued.v t)⁻¹ * Valued.v s ≤ Valued.v t * (Valued.v t)⁻¹ * 1 := by
          gcongr
      _ = 1 := by rw [mul_one, mul_inv_cancel₀ hv]

theorem exists_conductor {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous (ψ : K → ℂ)) (hψ : ∃ t : K, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K,
      (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
        Valued.v t ≤ WithZero.exp n := by
  classical
  obtain ⟨m, hm⟩ := exists_ball_trivial ψ hc
  obtain ⟨t₀, ht₀⟩ := hψ
  have ht₀0 : t₀ ≠ 0 := by rintro rfl; simp [AddChar.map_zero_eq_one] at ht₀
  have hnot : ¬ ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t₀ * s) = 1 :=
    fun h => ht₀ (by simpa using h 1 (by simp))

  have hmem : ∀ t : K, Valued.v t ≤ WithZero.exp m →
      ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1 := by
    intro t ht s hs
    apply hm
    rw [map_mul]
    calc Valued.v t * Valued.v s ≤ WithZero.exp m * 1 := by gcongr
      _ = WithZero.exp m := mul_one _
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, (∀ t : K, Valued.v t ≤ WithZero.exp k →
      ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) → k ≤ b := by
    refine ⟨WithZero.log (Valued.v t₀), fun k hk => ?_⟩
    by_contra hlt
    apply hnot
    apply hk
    have hv : Valued.v t₀ ≠ 0 := by simpa using ht₀0
    rw [← WithZero.exp_log hv]
    exact WithZero.exp_le_exp.2 (by omega)
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd ⟨m, hmem⟩
  refine ⟨n, fun t => ⟨fun hS => ?_, fun ht => hn t ht⟩⟩
  by_contra hgt
  rw [not_le] at hgt
  have hv : Valued.v t ≠ 0 := ne_of_gt (lt_trans WithZero.exp_pos hgt)
  have hj : WithZero.log (Valued.v t) ≤ n := by
    apply hmax
    intro t' ht'
    rw [WithZero.exp_log hv] at ht'
    exact addChar_trivial_mul_of_valuation_le ψ hS ht'
  have : Valued.v t ≤ WithZero.exp n := by
    rw [← WithZero.exp_log hv]
    exact WithZero.exp_le_exp.2 hj
  exact absurd hgt (not_lt.2 this)

end GlobalTheory.CharacterConductorBall
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem plane_lattice_reduction_step (e₁ e₂ : ℂ)
    (h : 2 * |((starRingEnd ℂ) e₁ * e₂).im| < ‖e₁‖ ^ 2) :
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      2 * ‖f₁‖ ^ 2 ≤ ‖e₁‖ ^ 2 := by
  have hN : 0 < ‖e₁‖ ^ 2 := lt_of_le_of_lt (by positivity) h
  set k : ℤ := round (((starRingEnd ℂ) e₁ * e₂).re / ‖e₁‖ ^ 2) with hk
  refine ⟨e₂ - k • e₁, e₁, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · have : x = (x - k • e₁) + k • e₁ := by ring
        rw [SetLike.mem_coe]
        nth_rewrite 2 [this]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · have : ((starRingEnd ℂ) (e₂ - k • e₁) * e₁).im = -((starRingEnd ℂ) e₁ * e₂).im := by
      simp
      ring
    rw [this, abs_neg]
  · have hr := abs_sub_round (((starRingEnd ℂ) e₁ * e₂).re / ‖e₁‖ ^ 2)
    rw [← hk] at hr
    have key : ‖e₁‖ ^ 2 * ‖e₂ - k • e₁‖ ^ 2 =
        (((starRingEnd ℂ) e₁ * e₂).re - k * ‖e₁‖ ^ 2) ^ 2 +
          ((starRingEnd ℂ) e₁ * e₂).im ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    generalize ((starRingEnd ℂ) e₁ * e₂).re = R at *
    generalize ((starRingEnd ℂ) e₁ * e₂).im = J at *
    generalize ‖e₁‖ ^ 2 = N at *
    generalize ‖e₂ - k • e₁‖ ^ 2 = M at *
    have h1 : (R - k * N) ^ 2 ≤ N ^ 2 / 4 := by
      have e : R - k * N = (R / N - k) * N := by field_simp
      have h2 : (R / N - k) ^ 2 ≤ 1 / 4 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (R / N - k)]
      rw [e, mul_pow]
      nlinarith [sq_nonneg N]
    have h3 : J ^ 2 ≤ N ^ 2 / 4 := by
      rw [← sq_abs J]
      nlinarith [abs_nonneg J]
    have h4 : N * (2 * M) ≤ N * N := by nlinarith
    exact le_of_mul_le_mul_left h4 hN

theorem plane_lattice_short_basis_of_bound_pow_two (n : ℕ) : ∀ e₁ e₂ : ℂ,
    ‖e₁‖ ^ 2 ≤ 2 ^ n * (2 * |((starRingEnd ℂ) e₁ * e₂).im|) →
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      ‖f₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by
  induction n with
  | zero =>
    intro e₁ e₂ h
    exact ⟨e₁, e₂, rfl, rfl, by simpa using h⟩
  | succ n ih =>
    intro e₁ e₂ h
    by_cases hc : ‖e₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im|
    · exact ⟨e₁, e₂, rfl, rfl, hc⟩
    · obtain ⟨g₁, g₂, hs, hi, hn⟩ := plane_lattice_reduction_step e₁ e₂ (not_le.mp hc)
      obtain ⟨f₁, f₂, hs', hi', hn'⟩ := ih g₁ g₂ (by
        rw [hi]
        rw [pow_succ (2 : ℝ) n] at h
        linarith)
      exact ⟨f₁, f₂, hs'.trans hs, hi'.trans hi, hi ▸ hn'⟩

theorem plane_lattice_short_basis : ∀ e₁ e₂ : ℂ, ((starRingEnd ℂ) e₁ * e₂).im ≠ 0 →
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      ‖f₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by
  intro e₁ e₂ h
  have hD : 0 < 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (‖e₁‖ ^ 2 / (2 * |((starRingEnd ℂ) e₁ * e₂).im|)) (one_lt_two (α := ℝ))
  exact plane_lattice_short_basis_of_bound_pow_two n e₁ e₂ ((div_lt_iff₀ hD).mp hn).le

end GlobalTheory
end

section

open MeasureTheory Topology

namespace GlobalTheory

theorem measure_eq_zero_of_finite_inter_lines
    (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (Z : Set V) (hZ : MeasurableSet Z) (y : V)
    (h : ∀ x : V, {t : K | x + t • y ∈ Z}.Finite) : μ Z = 0 := by
  let ν : Measure K := Measure.addHaar
  have hc : Continuous (fun p : V × K => p.1 + p.2 • y) := by fun_prop
  have hS : MeasurableSet {p : V × K | p.1 + p.2 • y ∈ Z} := hc.measurable hZ
  have h1 : (μ.prod ν) {p : V × K | p.1 + p.2 • y ∈ Z} = 0 := by
    rw [Measure.measure_prod_null hS]
    refine Filter.Eventually.of_forall fun x => ?_
    exact (h x).measure_zero ν
  rw [Measure.prod_apply_symm hS] at h1
  have h2 : ∀ t : K, μ ((fun x => (x, t)) ⁻¹' {p : V × K | p.1 + p.2 • y ∈ Z}) = μ Z := by
    intro t
    exact measure_preimage_add_right μ (t • y) Z
  simp only [h2, lintegral_const, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact h1
  · exact absurd h1 (by
      rw [Measure.measure_univ_eq_zero]
      exact NeZero.ne ν)

end GlobalTheory
end

section

open MeasureTheory Topology

namespace GlobalTheory

theorem addHaar_map_smul_of_norm_eq_one (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (c : K) (hc : ‖c‖ = 1) : Measure.map (fun x : V => c • x) μ = μ := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  let e : V ≃L[K] V := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc0)
  have he : (fun x : V => c • x) = e := by
    ext x
    simp [e]
  haveI : (Measure.map (fun x : V => c • x) μ).IsAddHaarMeasure := by
    rw [he]
    exact e.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (Measure.map (fun x : V => c • x) μ) μ
  set k := Measure.addHaarScalarFactor (Measure.map (fun x : V => c • x) μ) μ
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  let S : Set V := (fun p : K × V => p.1 • p.2) '' (Metric.sphere (0 : K) 1 ×ˢ C)
  have hS : IsCompact S :=
    ((isCompact_sphere (0 : K) 1).prod hC).image continuous_smul
  have hCS : C ⊆ S := fun x hx => ⟨(1, x), ⟨by simp, hx⟩, by simp⟩
  have hpos : μ S ≠ 0 :=
    ((Measure.measure_pos_of_mem_nhds μ hC0).trans_le (measure_mono hCS)).ne'
  have hfin : μ S ≠ ⊤ := hS.measure_lt_top.ne
  have hpre : (fun x : V => c • x) ⁻¹' S = S := by
    ext x
    constructor
    · rintro ⟨⟨a, y⟩, ⟨ha, hy⟩, h⟩
      refine ⟨(c⁻¹ * a, y), ⟨?_, hy⟩, ?_⟩
      · simp at ha
        simp [ha, hc]
      · simp only at h ⊢
        rw [mul_smul, h, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · rintro ⟨⟨a, y⟩, ⟨ha, hy⟩, h⟩
      refine ⟨(c * a, y), ⟨?_, hy⟩, ?_⟩
      · simp at ha
        simp [ha, hc]
      · simp only at h ⊢
        rw [mul_smul, h]
  have hm : Measure.map (fun x : V => c • x) μ S = μ S := by
    rw [Measure.map_apply (continuous_const_smul c).measurable hS.measurableSet, hpre]
  have hk1 : k = 1 := by
    rw [hk, Measure.smul_apply] at hm
    have h1 : (k : ENNReal) * μ S = 1 * μ S := by
      rw [one_mul]
      simpa [ENNReal.smul_def] using hm
    have := (ENNReal.mul_left_inj hpos hfin).1 h1
    exact_mod_cast this
  rw [hk, hk1, one_smul]

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.QuadFibre

open MeasureTheory
open scoped Pointwise

def IsSqrtOn {K : Type} [NormedField K] (U : Set K) (s : K → K) : Prop :=
  IsOpen U ∧ IsCompact U ∧ (1 : K) ∈ U ∧ (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧ (∀ a ∈ U, a⁻¹ ∈ U) ∧
    (∀ a ∈ U, ‖a‖ = 1) ∧ Continuous s ∧ ∀ a ∈ U, s a ^ 2 = a


open Classical in
def fibOf {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K)
    (t : K) : Measure V := by
  classical
  exact if t = 0 then 0 else
    (ν (t • U))⁻¹ • Measure.map (fun x => s (t / q x) • x) (μ.restrict (q ⁻¹' (t • U)))

theorem fibOf_zero {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K) :
    fibOf μ ν q U s 0 = 0 := by simp [fibOf]

theorem fibOf_ne {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K)
    {t : K} (ht : t ≠ 0) : fibOf μ ν q U s t =
      (ν (t • U))⁻¹ • Measure.map (fun x => s (t / q x) • x) (μ.restrict (q ⁻¹' (t • U))) := by
  simp [fibOf, ht]

end GlobalTheory.QuadFibre
end
end

section

open Real Filter Asymptotics

namespace GlobalTheory


open Real Filter Asymptotics in
theorem _root_.GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow :
    ∀ a b C : ℝ, ∀ p : ℕ, a < b →
      ∃ x0 : ℝ, ∀ x ≥ x0, C * x ^ a * Real.log x ^ p ≤ x ^ b := by
  intro a b C p hab
  have hlo : (fun x : ℝ => Real.log x ^ (p : ℝ)) =o[atTop] fun x => x ^ (b - a) :=
    isLittleO_log_rpow_rpow_atTop _ (sub_pos.mpr hab)
  have hc : (0 : ℝ) < 1 / (|C| + 1) := by positivity
  have hev := (hlo.bound hc).and (eventually_gt_atTop (0 : ℝ))
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp hev
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨hb, hxpos⟩ := hx0 x hx
  rw [Real.rpow_natCast] at hb
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hxpos a
  have hxba : 0 < x ^ (b - a) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxba] at hb
  have hsplit : x ^ b = x ^ a * x ^ (b - a) := by
    rw [← Real.rpow_add hxpos]; ring_nf
  have h1 : C * Real.log x ^ p ≤ |C| * |Real.log x ^ p| := by
    rw [← abs_mul]; exact le_abs_self _
  have h2 : |C| * |Real.log x ^ p| ≤ x ^ (b - a) := by
    calc |C| * |Real.log x ^ p| ≤ (|C| + 1) * |Real.log x ^ p| := by
          gcongr; linarith
      _ ≤ (|C| + 1) * (1 / (|C| + 1) * x ^ (b - a)) := by gcongr
      _ = x ^ (b - a) := by field_simp
  calc C * x ^ a * Real.log x ^ p = x ^ a * (C * Real.log x ^ p) := by ring
    _ ≤ x ^ a * x ^ (b - a) := by gcongr; linarith
    _ = x ^ b := hsplit.symm

end GlobalTheory
end

section

open Real Filter Asymptotics

namespace GlobalTheory


open Filter Asymptotics in
theorem log_add_rpow_mul_log_pow_le_rpow :
    ∀ a b c C κ : ℝ, ∀ p : ℕ, 0 ≤ a → a < b → 0 < κ → ∃ x0 : ℝ, ∀ x ≥ x0,
      c * Real.log x + C * x ^ a * Real.log x ^ p + C ≤ κ * x ^ b := by
  intro a b c C κ p ha hab hκ
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have h1 : (fun x : ℝ => c * Real.log x) =o[atTop] fun x => x ^ b :=
    (isLittleO_log_rpow_atTop hb).const_mul_left c
  have h2 : (fun x : ℝ => C * x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b := by
    have hl : (fun x : ℝ => Real.log x ^ p) =o[atTop] fun x => x ^ (b - a) := by
      have := isLittleO_log_rpow_rpow_atTop (p : ℝ) (sub_pos.2 hab)
      simpa [Real.rpow_natCast] using this
    have hm : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop]
        fun x => x ^ a * x ^ (b - a) :=
      (isBigO_refl (fun x : ℝ => x ^ a) atTop).mul_isLittleO hl
    have hm' : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b := by
      refine hm.congr' (Eventually.of_forall fun _ => rfl) ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]
      congr 1
      ring
    simpa [mul_assoc] using hm'.const_mul_left C
  have h3 : (fun _ : ℝ => C) =o[atTop] fun x => x ^ b := by
    rw [isLittleO_const_left]
    right
    exact tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hb)
  have h := (h1.add h2).add h3
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 ((h.bound hκ).and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨hbd, hxpos⟩ := hx0 x hx
  have hpos : 0 < x ^ b := Real.rpow_pos_of_pos hxpos b
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at hbd
  exact (le_abs_self _).trans hbd

end GlobalTheory
end
