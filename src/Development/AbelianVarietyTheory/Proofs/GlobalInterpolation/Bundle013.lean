module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle004
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle006
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle007
public import Mathlib.RingTheory.Unramified.Locus
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle008
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.MeasureTheory.Function.Floor
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology

namespace GlobalTheory.ZetaHalfPlane

noncomputable def fractInt (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))

noncomputable def cutFract : ℝ → ℂ := (Ioi (1 : ℝ)).indicator fun t => ((Int.fract t : ℝ) : ℂ)

lemma norm_fract_le (t : ℝ) : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
  exact (Int.fract_lt_one t).le

lemma norm_cutFract_le (t : ℝ) : ‖cutFract t‖ ≤ 1 :=
  (norm_indicator_le_norm_self _ _).trans (norm_fract_le t)

lemma measurable_fract_ofReal : Measurable fun t : ℝ => ((Int.fract t : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp measurable_fract

lemma measurable_cutFract : Measurable cutFract :=
  measurable_fract_ofReal.indicator measurableSet_Ioi

lemma fractInt_eq_mellin (s : ℂ) : fractInt s = mellin cutFract (-s) := by
  unfold fractInt mellin cutFract
  have h : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • (Ioi (1 : ℝ)).indicator
      (fun t => ((Int.fract t : ℝ) : ℂ)) t = (Ioi (1 : ℝ)).indicator
      (fun t => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul, mul_comm,
        show -s - 1 = -(s + 1) by ring]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  simp_rw [h]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

lemma differentiableAt_fractInt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ fractInt s := by
  have h1 : DifferentiableAt ℂ (mellin cutFract) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      refine (locallyIntegrable_const (1 : ℝ)).mono measurable_cutFract.aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => by simpa using norm_cutFract_le t
    · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
      simpa using norm_cutFract_le t
    · simpa using hs
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      have : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
      filter_upwards [this] with t ht
      have ht' : t ∉ Ioi (1 : ℝ) := fun h => lt_asymm (mem_Iio.1 ht) (mem_Ioi.1 h)
      rw [cutFract, indicator_of_notMem ht', norm_zero]
      positivity
    · simp
  have h2 : fractInt = fun s => mellin cutFract (-s) := funext fractInt_eq_mellin
  rw [h2]
  exact h1.comp s differentiableAt_id.neg

lemma norm_integrand_le (s : ℂ) {t : ℝ} (ht : t ∈ Ioi (1 : ℝ)) :
    ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ t ^ (-(s.re + 1)) := by
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  simp only [neg_re, add_re, one_re]
  exact mul_le_of_le_one_left (by positivity) (norm_fract_le t)

lemma norm_fractInt_le {s : ℂ} (hs : 0 < s.re) : ‖fractInt s‖ ≤ 1 / s.re := by
  have h : -(s.re + 1) < -1 := by linarith
  calc ‖fractInt s‖ ≤ ∫ t in Ioi (1 : ℝ), t ^ (-(s.re + 1)) := by
        refine norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt h one_pos) ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun t ht => norm_integrand_le s ht
    _ = 1 / s.re := by
        rw [integral_Ioi_rpow_of_lt h one_pos, Real.one_rpow,
          show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]

lemma integrableOn_integrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have h : (-(s + 1)).re < -1 := by simp; linarith
  exact (integrableOn_Ioi_cpow_of_lt h one_pos).bdd_mul (c := 1)
    measurable_fract_ofReal.aestronglyMeasurable (Eventually.of_forall norm_fract_le)

lemma zeta_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * fractInt s := by
  first
  | exact @_root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract
  | exact _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract
  | (apply _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract <;> assumption)
  | (intros; apply _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ZetaFractionalIntegral.zeta_eq_sub_integral_fract ..)

theorem zeta_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * fractInt s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hf : AnalyticOnNhd ℂ riemannZeta₀ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₀.differentiableOn.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun z => 1 - z * fractInt z) {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      ((differentiableAt_const _).sub
        (differentiableAt_id.mul (differentiableAt_fractInt hz))).differentiableWithinAt) hU
  have key : ∀ z : ℂ, z ≠ 1 → z / (z - 1) = (z - 1)⁻¹ + 1 := by
    intro z hz
    have := sub_ne_zero.2 hz
    field_simp
    ring
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp) (by
      have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
      filter_upwards [this] with z hz
      have hz1 : z ≠ 1 := by
        rintro rfl
        simp at hz
      have h1 := zeta_eq_of_one_lt hz
      rw [riemannZeta_eq_inv_sub_add hz1, key z hz1] at h1
      linear_combination h1)
  have h2 : riemannZeta₀ s = 1 - s * fractInt s := heq hs
  rw [riemannZeta_eq_inv_sub_add hs1, key s hs1, h2]
  ring

theorem norm_zeta_sub_le :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → ‖riemannZeta s - s / (s - 1)‖ ≤ ‖s‖ / s.re := by
  intro s hs hs1
  rw [zeta_eq hs hs1, sub_sub_cancel_left, norm_neg, norm_mul, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (norm_fractInt_le hs) (norm_nonneg s)

end GlobalTheory.ZetaHalfPlane
end

section

open MeasureTheory Topology

theorem _root_.GlobalTheory.T.measure_eq_zero_of_finite_inter_lines' : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Z : Set V), MeasurableSet Z → ∀ y : V, (∀ x : V, {t : K | x + t • y ∈ Z}.Finite) → μ Z = 0 := by
  first | exact @GlobalTheory.measure_eq_zero_of_finite_inter_lines | exact GlobalTheory.measure_eq_zero_of_finite_inter_lines | (intros; apply GlobalTheory.measure_eq_zero_of_finite_inter_lines <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_tsum_orbit_unfold_alt : ∀ (G G' V X : Type) [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul G'] [MulAction G V] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (μ' : Measure G') [SFinite μ'] [μ'.IsMulLeftInvariant] (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] [Countable Γ'] (𝓕 : Set G) (𝓕' : Set G'), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ' 𝓕' μ' → ∀ (φ : G' →* G), Measurable φ → Function.Injective φ → (∀ g, φ g ∈ Γ ↔ g ∈ Γ') → ∀ (x : V), φ.range = MulAction.stabilizer G x → ∀ (c : X → V), Function.Injective c → (∀ y, y ∈ Set.range c ↔ ∃ γ ∈ Γ, γ • x = y) → ∀ (u : G → ℝ≥0∞), Measurable u → ∀ (Φ : V → ℝ≥0∞), (∀ h : G, Φ (h⁻¹ • x) = ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ') → ∫⁻ h in 𝓕, ∑' i, Φ (h⁻¹ • c i) ∂μ = μ' 𝓕' * ∫⁻ h, u h ∂μ := by
  first | exact @GlobalTheory.lintegral_tsum_orbit_unfold | exact GlobalTheory.lintegral_tsum_orbit_unfold | (intros; apply GlobalTheory.lintegral_tsum_orbit_unfold <;> assumption)
end

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory

open MeasureTheory Topology in
open scoped ENNReal Pointwise in
private theorem exists_normalized_weight_of_closedEmbedding
    {T T' : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (j : T' →* T) (hj : IsClosedEmbedding j) (ν : Measure T') [ν.IsHaarMeasure] :
    ∃ φ : T → ℝ≥0∞, Measurable φ ∧ (∀ g, ∫⁻ s, φ (g * j s) ∂ν = 1) ∧
      ∀ K : Set T, IsCompact K → ∃ (K' : Set T) (C : ℝ≥0∞), IsCompact K' ∧ C < ⊤ ∧
        ∀ k ∈ K, ∀ s : T', φ (k * j s) ≤ C ∧ (φ (k * j s) ≠ 0 → k * j s ∈ K') := by
  classical
  haveI : LocallyCompactSpace T' := hj.locallyCompactSpace
  haveI : SecondCountableTopology T' := hj.isEmbedding.secondCountableTopology
  haveI : T2Space T' := hj.isEmbedding.t2Space
  have hjm : Measurable j := hj.continuous.measurable
  let E := CompactExhaustion.choice T
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set T, ∀ n x, x ∈ A n ↔ ∃ s : T', x * j s ∈ E n :=
    ⟨fun n => {x | ∃ s : T', x * j s ∈ E n}, fun _ _ => Iff.rfl⟩
  have hA_mono : ∀ {m n}, m ≤ n → A m ⊆ A n := fun hmn x hx => by
    obtain ⟨s, hs⟩ := (hA _ x).1 hx
    exact (hA _ x).2 ⟨s, E.subset hmn hs⟩
  have hA_mul : ∀ n x (s : T'), x * j s ∈ A n ↔ x ∈ A n := by
    intro n x s
    rw [hA, hA]
    constructor
    · rintro ⟨s', hs'⟩
      exact ⟨s * s', by simpa [mul_assoc] using hs'⟩
    · rintro ⟨s', hs'⟩
      exact ⟨s⁻¹ * s', by simpa [mul_assoc] using hs'⟩
  have hE_A : ∀ n, E n ⊆ A n := fun n x hx => (hA n x).2 ⟨1, by simpa using hx⟩
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    have hAn : A n = E n * Set.range j := by
      ext x
      rw [hA, Set.mem_mul]
      constructor
      · rintro ⟨s, hs⟩
        exact ⟨_, hs, j s⁻¹, ⟨s⁻¹, rfl⟩, by simp [mul_assoc]⟩
      · rintro ⟨k, hk, _, ⟨s, rfl⟩, rfl⟩
        exact ⟨s⁻¹, by simpa [mul_assoc] using hk⟩
    rw [hAn]
    exact (hj.isClosed_range.mul_left_of_isCompact (E.isCompact n)).measurableSet
  have hex : ∀ x, ∃ n, x ∈ A n := fun x => ⟨E.find x, hE_A _ (E.mem_find x)⟩
  obtain ⟨N, hNm, hN⟩ : ∃ N : T → ℕ, Measurable N ∧ ∀ x n, N x ≤ n ↔ x ∈ A n := by
    refine ⟨fun x => Nat.find (hex x), measurable_find hex hA_meas, fun x n => ?_⟩
    rw [Nat.find_le_iff]
    exact ⟨fun ⟨m, hm, hx⟩ => hA_mono hm hx, fun hx => ⟨n, le_rfl, hx⟩⟩
  have hN_mem : ∀ x, x ∈ A (N x) := fun x => (hN x _).1 le_rfl
  have hN_mul : ∀ x (s : T'), N (x * j s) = N x := fun x s =>
    le_antisymm ((hN _ _).2 ((hA_mul _ _ _).2 (hN_mem x)))
      ((hN _ _).2 ((hA_mul _ _ _).1 (hN_mem _)))
  obtain ⟨S, hS⟩ : ∃ S : Set T, ∀ x, x ∈ S ↔ x ∈ E (N x + 1) :=
    ⟨{x | x ∈ E (N x + 1)}, fun _ => Iff.rfl⟩
  have hS_meas : MeasurableSet S := by
    have hSU : S = ⋃ n, N ⁻¹' {n} ∩ E (n + 1) := by
      ext x
      rw [hS]
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hx => ⟨_, rfl, hx⟩, by rintro ⟨n, rfl, hx⟩; exact hx⟩
    rw [hSU]
    exact MeasurableSet.iUnion fun n =>
      (hNm (measurableSet_singleton n)).inter (E.isCompact _).isClosed.measurableSet
  obtain ⟨ψ, hψm, hψle, hψS, hψ1⟩ : ∃ ψ : T → ℝ≥0∞, Measurable ψ ∧ (∀ x, ψ x ≤ 1) ∧
      (∀ x, ψ x ≠ 0 → x ∈ S) ∧ (∀ x, x ∈ S → ψ x = 1) := by
    refine ⟨S.indicator fun _ => 1, measurable_const.indicator hS_meas, fun x => ?_,
      fun x hx => ?_, fun x hx => Set.indicator_of_mem hx _⟩
    · by_cases hx : x ∈ S <;> simp [hx]
    · by_contra hxS
      exact hx (by simp [hxS])
  obtain ⟨F, hFm, hF⟩ : ∃ F : T → ℝ≥0∞, Measurable F ∧ ∀ x, F x = ∫⁻ s, ψ (x * j s) ∂ν :=
    ⟨fun x => ∫⁻ s, ψ (x * j s) ∂ν,
      (hψm.comp (measurable_fst.mul (hjm.comp measurable_snd))).lintegral_prod_right',
      fun _ => rfl⟩
  have hF_mul : ∀ x (s : T'), F (x * j s) = F x := by
    intro x s
    rw [hF, hF]
    simpa [mul_assoc] using lintegral_mul_left_eq_self (μ := ν) (fun t => ψ (x * j t)) s
  have hF_pos : ∀ n, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ x, N x = n → c ≤ F x := by
    intro n
    obtain ⟨V, hV, hKV⟩ :=
      compact_open_separated_mul_right (E.isCompact n) isOpen_interior (E.subset_interior_succ n)
    have hVo : IsOpen (j ⁻¹' interior V) := isOpen_interior.preimage hj.continuous
    have hV1 : (1 : T') ∈ j ⁻¹' interior V := by
      simpa using mem_interior_iff_mem_nhds.2 hV
    refine ⟨ν (j ⁻¹' interior V), hVo.measure_pos ν ⟨1, hV1⟩, fun x hx => ?_⟩
    obtain ⟨s₀, hs₀⟩ := (hA n x).1 (hx ▸ hN_mem x)
    calc ν (j ⁻¹' interior V) = ∫⁻ s, (j ⁻¹' interior V).indicator 1 s ∂ν :=
          (lintegral_indicator_one hVo.measurableSet).symm
      _ ≤ ∫⁻ s, ψ (x * j s₀ * j s) ∂ν := by
          refine lintegral_mono fun s => ?_
          by_cases hs : s ∈ j ⁻¹' interior V
          · rw [Set.indicator_of_mem hs, Pi.one_apply, hψ1]
            rw [hS, hN_mul, hN_mul, hx]
            exact interior_subset (hKV (Set.mul_mem_mul hs₀ (interior_subset hs)))
          · simp [hs]
      _ = F x := by rw [← hF, hF_mul]
  choose c hc_pos hc using hF_pos
  have hF_ne : ∀ x, F x ≠ 0 := fun x => ((hc_pos (N x)).trans_le (hc _ x rfl)).ne'
  have hF_fin : ∀ x, F x ≠ ⊤ := by
    intro x
    have hK : IsCompact ((fun s : T' => x * j s) ⁻¹' E (N x + 1)) :=
      ((Homeomorph.mulLeft x).isClosedEmbedding.comp hj).isCompact_preimage (E.isCompact _)
    refine (lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := ν))).ne
    calc F x = ∫⁻ s, ψ (x * j s) ∂ν := hF x
      _ ≤ ∫⁻ s, ((fun s : T' => x * j s) ⁻¹' E (N x + 1)).indicator 1 s ∂ν := by
          refine lintegral_mono fun s => ?_
          by_cases hs : s ∈ (fun s : T' => x * j s) ⁻¹' E (N x + 1)
          · rw [Set.indicator_of_mem hs]
            exact hψle _
          · rw [Set.indicator_of_notMem hs]
            refine le_of_eq (by_contra fun hψs => ?_)
            have hmem := (hS _).1 (hψS _ hψs)
            rw [hN_mul] at hmem
            exact hs hmem
      _ = ν ((fun s : T' => x * j s) ⁻¹' E (N x + 1)) :=
          lintegral_indicator_one hK.isClosed.measurableSet
  refine ⟨fun x => ψ x * (F x)⁻¹, hψm.mul hFm.inv, fun g => ?_, fun K hK => ?_⟩
  · calc ∫⁻ s, ψ (g * j s) * (F (g * j s))⁻¹ ∂ν = ∫⁻ s, ψ (g * j s) * (F g)⁻¹ ∂ν := by
          simp_rw [hF_mul]
      _ = (∫⁻ s, ψ (g * j s) ∂ν) * (F g)⁻¹ :=
          lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hF_ne g))
      _ = 1 := by rw [← hF, ENNReal.mul_inv_cancel (hF_ne g) (hF_fin g)]
  · obtain ⟨M, hM⟩ := E.exists_superset_of_isCompact hK
    refine ⟨E (M + 1), ∑ n ∈ Finset.range (M + 1), (c n)⁻¹, E.isCompact _,
      ENNReal.sum_lt_top.2 fun n _ => ENNReal.inv_lt_top.2 (hc_pos n), fun k hk s => ⟨?_, ?_⟩⟩
    · have hNk : N k ≤ M := (hN k M).2 (hE_A M (hM hk))
      calc ψ (k * j s) * (F (k * j s))⁻¹ ≤ 1 * (c (N k))⁻¹ :=
            mul_le_mul' (hψle _) (ENNReal.inv_le_inv.2 (hc _ _ (hN_mul k s)))
        _ = (c (N k))⁻¹ := one_mul _
        _ ≤ ∑ n ∈ Finset.range (M + 1), (c n)⁻¹ :=
            Finset.single_le_sum (f := fun n => (c n)⁻¹) (fun _ _ => bot_le)
              (Finset.mem_range.2 (Nat.lt_succ_of_le hNk))
    · intro hne
      have hNk : N k ≤ M := (hN k M).2 (hE_A M (hM hk))
      have hmem := (hS _).1 (hψS _ (left_ne_zero_of_mul hne))
      rw [hN_mul] at hmem
      exact E.subset (Nat.succ_le_succ hNk) hmem


open MeasureTheory in
open scoped ENNReal in
theorem _root_.GlobalTheory.exists_bruhat_function_closed_subgroup
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure] :
    ∃ φ : G → ℝ≥0∞, Measurable φ ∧ (∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1) ∧
      ∀ K : Set G, IsCompact K → ∃ (K' : Set G) (C : ℝ≥0∞), IsCompact K' ∧ C < ⊤ ∧
        ∀ k ∈ K, ∀ h : H, φ (k * h) ≤ C ∧ (φ (k * h) ≠ 0 → k * h ∈ K') := by
  obtain ⟨φ, hφm, hφ, hφK⟩ :=
    exists_normalized_weight_of_closedEmbedding H.subtype hH.isClosedEmbedding_subtypeVal ν
  exact ⟨φ, hφm, hφ, hφK⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.valuation_eq_exp_neg_of_pow_eq_span_singleton : ∀ (K : Type) [Field K] [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K)) (n : ℕ) (π : 𝓞 K), 𝔭.asIdeal ^ n = Ideal.span {π} → 𝔭.valuation K (π : K) = WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.valuation_of_generator_of_pow | exact GlobalTheory.valuation_of_generator_of_pow | (intros; apply GlobalTheory.valuation_of_generator_of_pow <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.quadratic_field_at_most_two_primes_over_prime : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (q : ℕ), q.Prime → ∀ P₁ P₂ P₃ : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P₁.asIdeal → ((q : ℕ) : 𝓞 K) ∈ P₂.asIdeal → ((q : ℕ) : 𝓞 K) ∈ P₃.asIdeal → P₁ = P₂ ∨ P₁ = P₃ ∨ P₂ = P₃ := by
  first | exact @GlobalTheory.quadratic_at_most_two_primes_over | exact GlobalTheory.quadratic_at_most_two_primes_over | (intros; apply GlobalTheory.quadratic_at_most_two_primes_over <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.quadratic_unramified_iff_isPrime_map_or_ncard_primesOver_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), ((∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔ ((v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime ∨ (v.asIdeal.primesOver (𝓞 E)).ncard = 2)) := by
  first | exact @GlobalTheory.quadratic_unramified_iff_inert_or_split | exact GlobalTheory.quadratic_unramified_iff_inert_or_split | (intros; apply GlobalTheory.quadratic_unramified_iff_inert_or_split <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory


open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
theorem _root_.GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two (K : Type) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 2) :
    (NumberField.classNumber K : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
  have hb := _root_.GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K
  rw [h] at hb
  norm_num at hb
  have hs := _root_.GlobalTheory.one_le_sqrt_abs_discr K
  set s := √|(NumberField.discr K : ℝ)| with hs_def
  have hlog : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hsq : s * s = |(NumberField.discr K : ℝ)| :=
    Real.mul_self_sqrt (abs_nonneg _)
  calc (NumberField.classNumber K : ℝ) ≤ s * (1 + Real.log s) := hb
    _ ≤ s * s := by apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    _ = |(NumberField.discr K : ℝ)| := hsq


open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
theorem _root_.GlobalTheory.classNumber_le_four_mul_abs_discr :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      (NumberField.classNumber K : ℝ) ≤ 4 * |(NumberField.discr K : ℝ)| := by
  intro K _ _ h
  have := _root_.GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two K h
  have := abs_nonneg (NumberField.discr K : ℝ)
  linarith

end GlobalTheory
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.isField_adicCompletion_tensor_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime → IsField (v.adicCompletion F ⊗[F] E) := by
  first | exact @GlobalTheory.InertField.isField_of_inert | exact GlobalTheory.InertField.isField_of_inert | (intros; apply GlobalTheory.InertField.isField_of_inert <;> assumption)
end
