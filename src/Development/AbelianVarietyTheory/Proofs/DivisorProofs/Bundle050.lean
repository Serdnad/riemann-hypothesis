module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Aesop.Main
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
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory.LocRep

variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_zero (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) :
    ι 0 =ᵐ[μ] fun _ => 0 := by
  filter_upwards [hlin 1 0 0] with x hx
  simpa using hx

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_add (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (v w : K) :
    ι (v + w) =ᵐ[μ] fun x => ι v x + ι w x := by
  filter_upwards [hlin 1 v w] with x hx
  simpa using hx

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_smul (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (a : ℂ) (v : K) :
    ι (a • v) =ᵐ[μ] fun x => a * ι v x := by
  filter_upwards [hlin a v 0, _root_.GlobalTheory.LocRep.rep_zero hlin] with x hx h0
  simp only [add_zero] at hx
  rw [hx, h0, add_zero]

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_sub (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (v w : K) :
    ι (v - w) =ᵐ[μ] fun x => ι v x - ι w x := by
  filter_upwards [hlin (-1) w v] with x hx
  rw [show v - w = (-1 : ℂ) • w + v by rw [neg_one_smul]; abel, hx]
  ring

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_sum (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) {J : Type} (s : Finset J)
    (v : J → K) : ι (∑ j ∈ s, v j) =ᵐ[μ] fun x => ∑ j ∈ s, ι (v j) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using _root_.GlobalTheory.LocRep.rep_zero hlin
  · intro j s hj ih
    filter_upwards [_root_.GlobalTheory.LocRep.rep_add hlin (v j) (∑ i ∈ s, v i), ih] with x h1 h2
    rw [Finset.sum_insert hj, h1, h2, Finset.sum_insert hj]


open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.exists_pairing
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) {C : Set G} (hC : IsCompact C) :
    ∃ Λ : K →L[ℂ] ℂ, ∀ v, Λ v = ∫ x in C, ι v x ∂μ := by
  obtain ⟨M, hM⟩ := hloc C hC
  have hint : ∀ (a : ℂ) v w, ∫ x in C, ι (a • v + w) x ∂μ =
      a * ∫ x in C, ι v x ∂μ + ∫ x in C, ι w x ∂μ := by
    intro a v w
    rw [integral_congr_ae (ae_restrict_of_ae (hlin a v w)),
      integral_add ((hM v).1.const_mul a) (hM w).1, integral_const_mul]
  have hz : ∫ x in C, ι 0 x ∂μ = 0 := by
    rw [integral_congr_ae (ae_restrict_of_ae (_root_.GlobalTheory.LocRep.rep_zero hlin))]
    simp
  let L : K →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ x in C, ι v x ∂μ
      map_add' := fun v w => by simpa using hint 1 v w
      map_smul' := fun a v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        simpa [hz] using hint a v 0 }
  refine ⟨L.mkContinuous M fun v => ?_, fun v => rfl⟩
  exact (norm_integral_le_integral_norm _).trans (hM v).2

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.locallyIntegrable_rep [LocallyCompactSpace G]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) (v : K) :
    LocallyIntegrable (ι v) μ := by
  intro x
  obtain ⟨C, hC, hCx⟩ := exists_compact_mem_nhds x
  obtain ⟨M, hM⟩ := hloc C hC
  exact ⟨C, hCx, (hM v).1⟩


open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_of_pairing [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [BorelSpace G]
    [IsLocallyFiniteMeasure μ]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    {v : K} {φ : G → ℂ} (hφ : LocallyIntegrable φ μ)
    (h : ∀ C, IsCompact C → ∫ x in C, ι v x ∂μ = ∫ x in C, φ x ∂μ) : ι v =ᵐ[μ] φ := by
  have hv : LocallyIntegrable (ι v) μ := _root_.GlobalTheory.LocRep.locallyIntegrable_rep hloc v
  have hdiff : (ι v - φ) =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' (hv.sub hφ) fun C hC => ?_
    simp only [Pi.sub_apply]
    rw [integral_sub (hv.integrableOn_isCompact hC) (hφ.integrableOn_isCompact hC), h C hC, sub_self]
  filter_upwards [hdiff] with x hx
  simpa [sub_eq_zero] using hx

end GlobalTheory.LocRep
end

section

open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory.ClassIntegral

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]

def dcoset (Γ K : Subgroup G) (g : G) : Set G := {x | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * g * k}

theorem measurableSet_dcoset (Γ K : Subgroup G) [Countable Γ] (hK : MeasurableSet (K : Set G)) (g : G) :
    MeasurableSet (dcoset Γ K g) := by
  have : dcoset Γ K g = ⋃ γ : Γ, (fun y => ((γ : G) * g)⁻¹ * y) ⁻¹' (K : Set G) := by
    ext x
    simp only [dcoset, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, by simpa [mul_assoc] using hk⟩
    · rintro ⟨γ, h⟩
      exact ⟨γ, γ.2, _, h, by group⟩
  rw [this]
  exact MeasurableSet.iUnion fun γ => (measurable_const_mul _) hK

omit [MeasurableSpace G] [MeasurableMul G] in
theorem tsum_indicator_eq (Γ K : Subgroup G) (g x : G) :
    ∑' γ : Γ, ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x) =
      (∑' _ : {γ : Γ // g⁻¹ * (γ : G) * g ∈ K}, (1 : ENNReal)) * (dcoset Γ K g).indicator 1 x := by
  classical
  by_cases hx : x ∈ dcoset Γ K g
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    obtain ⟨δ, hδ, k, hk, rfl⟩ := hx
    rw [← (Equiv.mulRight (⟨δ, hδ⟩ : Γ)⁻¹).tsum_eq]
    have := tsum_subtype {γ : Γ | g⁻¹ * (γ : G) * g ∈ K} (fun _ => (1 : ENNReal))
    refine Eq.trans ?_ this.symm
    refine tsum_congr fun γ => ?_
    have e : g⁻¹ * ((γ : G) * δ⁻¹ * (δ * g * k)) = g⁻¹ * γ * g * k := by group
    simp only [Set.indicator, Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, Equiv.coe_mulRight,
      Subgroup.coe_mul, Subgroup.coe_inv, SetLike.mem_coe, Pi.one_apply, Set.mem_setOf_eq, e,
      K.mul_mem_cancel_right hk]
  · rw [Set.indicator_of_notMem hx, mul_zero, ENNReal.tsum_eq_zero]
    intro γ
    apply Set.indicator_of_notMem
    intro h
    apply hx
    refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, h, ?_⟩
    simp only [Subgroup.smul_def, smul_eq_mul]
    group

theorem measure_dcoset (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1) (g : G) {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (∑' _ : {γ : Γ // g⁻¹ * (γ : G) * g ∈ K}, (1 : ENNReal)) * μ.restrict 𝓕 (dcoset Γ K g) = 1 := by
  have i1 : MeasurableConstSMul Γ G :=
    ⟨fun γ => by simpa [Subgroup.smul_def, smul_eq_mul] using measurable_const_mul (γ : G)⟩
  have i2 : SMulInvariantMeasure Γ G μ :=
    ⟨fun γ s _ => by
      have : ((fun x => γ • x) ⁻¹' s) = ((fun x => (γ : G) * x) ⁻¹' s) := by
        ext x; simp [Subgroup.smul_def, smul_eq_mul]
      rw [this, measure_preimage_mul]⟩
  have hT : MeasurableSet ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)) := (measurable_const_mul _) hK
  have hf : Measurable (((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal)) :=
    measurable_one.indicator hT
  have hC := measurableSet_dcoset Γ K hK g
  rw [← lintegral_indicator_one hC, ← lintegral_const_mul _ (measurable_one.indicator hC)]
  simp only [← tsum_indicator_eq]
  have hmeas : ∀ γ : Γ, Measurable fun x : G =>
      ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x) :=
    fun γ => hf.comp (measurable_const_smul γ)
  rw [lintegral_tsum fun γ => (hmeas γ).aemeasurable,
    ← h𝓕.lintegral_eq_tsum'', lintegral_indicator_one hT, measure_preimage_mul, hK1]

theorem tsum_one_mul_eq_one {α : Type} {m : ENNReal} (h : (∑' _ : α, (1 : ENNReal)) * m = 1) :
    m ≠ ⊤ ∧ m.toReal = (Nat.card α : ℝ)⁻¹ := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at h
  have hN0 : (∑' _ : α, (1 : ENNReal)) ≠ 0 := by intro h0; rw [h0] at h; simp at h
  have hN : (∑' _ : α, (1 : ENNReal)) ≠ ⊤ := by
    intro h0; rw [h0, ENNReal.top_mul hm0] at h; simp at h
  have hm : m ≠ ⊤ := by
    intro h0; rw [h0, ENNReal.mul_top hN0] at h; simp at h
  have : Finite α := by
    by_contra hα
    have : Infinite α := not_finite_iff_infinite.mp hα
    exact hN (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero)
  refine ⟨hm, ?_⟩
  have := Fintype.ofFinite α
  rw [tsum_fintype] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_eq_nat_card] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at h'
  exact eq_inv_of_mul_eq_one_right h'

theorem integral_fundamentalDomain_eq_sum : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant], MeasurableSet (K : Set G) → μ K = 1 → ∀ {ι : Type} [Fintype ι] (g : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * g i * k) → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, (∀ γ ∈ Γ, ∀ k ∈ K, ∀ x, Φ (γ * x * k) = Φ x) → IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ∑ i, ((Nat.card {γ : Γ // (g i)⁻¹ * (γ : G) * g i ∈ K} : ℂ))⁻¹ * Φ (g i) := by
  intro G _ _ _ Γ K _ μ _ hK hK1 ι _ g hcov 𝓕 h𝓕 Φ hΦ
  have hm := fun i => tsum_one_mul_eq_one (measure_dcoset Γ K μ hK hK1 (g i) h𝓕)
  have hC := fun i => measurableSet_dcoset Γ K hK (g i)
  have hpt : Φ = fun x => ∑ i, (dcoset Γ K (g i)).indicator (fun _ => Φ (g i)) x := by
    funext x
    obtain ⟨j, hj, huniq⟩ := hcov x
    rw [Finset.sum_eq_single j]
    · rw [Set.indicator_of_mem (s := dcoset Γ K (g j)) hj]
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hj
      exact hΦ γ hγ k hk _
    · intro i _ hij
      have hx : x ∉ dcoset Γ K (g i) := fun h => hij (huniq i h)
      exact Set.indicator_of_notMem hx _
    · intro h; exact absurd (Finset.mem_univ j) h
  have hint : ∀ i, Integrable ((dcoset Γ K (g i)).indicator (fun _ => Φ (g i))) (μ.restrict 𝓕) :=
    fun i => (integrable_indicator_iff (hC i)).mpr (integrableOn_const (hm i).1)
  constructor
  · rw [IntegrableOn, hpt]
    exact MeasureTheory.integrable_finsetSum _ fun i _ => hint i
  · calc ∫ x in 𝓕, Φ x ∂μ
        = ∫ x in 𝓕, ∑ i, (dcoset Γ K (g i)).indicator (fun _ => Φ (g i)) x ∂μ := by
          conv_lhs => rw [hpt]
      _ = _ := by
          rw [MeasureTheory.integral_finsetSum _ fun i _ => hint i]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_indicator_const _ (hC i), Measure.real, (hm i).2, Complex.real_smul]
          push_cast
          rfl

end GlobalTheory.ClassIntegral
end

section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalTheory.QuotLocInt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}

open MeasureTheory Set in
open scoped ENNReal in
private theorem lintegral_compact_le_mul_lintegral_fundamentalDomain (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (C : Set G) (hC : IsCompact C) (n : ℝ)
    (hn : ∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n)
    (g : G → ℝ≥0∞) (hg : Measurable g) (hinv : ∀ (γ : Γ) x, g (γ • x) = g x) :
    ∫⁻ x in C, g x ∂μ ≤ ENNReal.ofReal n * ∫⁻ x in 𝓕, g x ∂μ := by
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hcount : ∀ x : G, ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x) ≤ ENNReal.ofReal n := by
    intro x
    have hS : ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x) =
        ∑' γ : Γ, {γ : Γ | (γ : G) * x ∈ C}.indicator 1 γ := rfl
    rw [hS, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    obtain ⟨hfin, hle⟩ := hn x
    have hE : ({γ : Γ | (γ : G) * x ∈ C}).encard ≤
        (({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℕ∞) := by
      rw [hfin.cast_ncard_eq, ← Subtype.val_injective.encard_image]
      apply Set.encard_le_encard
      rintro _ ⟨γ, hγ, rfl⟩
      exact ⟨γ.2, hγ⟩
    calc ((({γ : Γ | (γ : G) * x ∈ C}).encard : ℕ∞) : ℝ≥0∞)
        ≤ (((({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := ENat.toENNReal_le.mpr hE
      _ = (({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℝ≥0∞) := by simp
      _ ≤ ENNReal.ofReal n := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hle
  calc ∫⁻ x in C, g x ∂μ = ∫⁻ x, C.indicator g x ∂μ := (lintegral_indicator hCm _).symm
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, C.indicator g (γ⁻¹ • x) ∂μ := h𝓕.lintegral_eq_tsum' _
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, C.indicator (1 : G → ℝ≥0∞) (γ⁻¹ • x) * g x ∂μ := by
        congr 1; funext γ; congr 1; funext x
        by_cases hx : γ⁻¹ • x ∈ C <;> simp [hx, hinv]
    _ = ∫⁻ x in 𝓕, ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ⁻¹ • x) * g x ∂μ := by
        rw [lintegral_tsum]
        intro γ
        exact (((measurable_one.indicator hCm).comp (measurable_const_smul _)).mul hg).aemeasurable
    _ = ∫⁻ x in 𝓕, (∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x)) * g x ∂μ := by
        congr 1; funext x
        rw [ENNReal.tsum_mul_right]
        congr 1
        exact (Equiv.inv Γ).tsum_eq (fun γ => C.indicator (1 : G → ℝ≥0∞) (γ • x))
    _ ≤ ∫⁻ x in 𝓕, ENNReal.ofReal n * g x ∂μ :=
        lintegral_mono fun x => by gcongr ?_ * _; exact hcount x
    _ = _ := lintegral_const_mul _ hg


open MeasureTheory Set in
open scoped ENNReal in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G} in
theorem _root_.GlobalTheory.QuotLocInt.integrableOn_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ]
    (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ C : Set G, IsCompact C → ∀ n : ℝ,
    (∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n) →
    ∃ M : ℝ, ∀ F : Lp ℂ 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))),
      IntegrableOn (fun x => F (Quotient.mk _ x)) C μ ∧
        ∫ x in C, ‖F (Quotient.mk _ x)‖ ∂μ ≤ M * ‖F‖ := by
  intro G _ _ _ _ _ _ μ _ Γ _ 𝓕 h𝓕 C hC n hn
  refine ⟨(ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ)).toReal, fun F => ?_⟩
  have hπ : Measurable (Quotient.mk (QuotientGroup.rightRel Γ)) := fun _ hs => hs
  have hF := Lp.stronglyMeasurable F
  have hf : StronglyMeasurable fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x) :=
    hF.comp_measurable hπ
  have hL2 : eLpNorm (fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x)) 2 (μ.restrict C) ≤
      ENNReal.ofReal n ^ (1/2 : ℝ) *
        eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        hf.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        (Lp.aestronglyMeasurable F)]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ∫⁻ x in C, ‖F (Quotient.mk (QuotientGroup.rightRel Γ) x)‖ₑ ^ (2 : ℝ) ∂μ
        ≤ ENNReal.ofReal n * ∫⁻ x in 𝓕, ‖F (Quotient.mk (QuotientGroup.rightRel Γ) x)‖ₑ ^ (2 : ℝ) ∂μ :=
          lintegral_compact_le_mul_lintegral_fundamentalDomain G μ Γ 𝓕 h𝓕 C hC n hn _
            ((hF.measurable.eNorm.pow_const _).comp hπ) fun γ x => by
              rw [show Quotient.mk (QuotientGroup.rightRel Γ) (γ • x) = Quotient.mk _ x from
                Quotient.sound (QuotientGroup.rightRel_apply.2 (by simp [Subgroup.smul_def, mul_inv_rev]))]
      _ = _ := by rw [lintegral_map (hF.measurable.eNorm.pow_const _) hπ]
  have hL1 : eLpNorm (fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x)) 1 (μ.restrict C) ≤
      ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ) *
        eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) := by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hf.aestronglyMeasurable).trans ?_
    rw [Measure.restrict_apply_univ]
    simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
    rw [show (1 / 1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
    calc _ ≤ ENNReal.ofReal n ^ (1/2 : ℝ) *
          eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) *
            μ C ^ (1/2 : ℝ) := by gcongr
      _ = _ := by ring
  have hfin : ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ) *
      eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) < ⊤ := by
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) (Lp.eLpNorm_lt_top F)
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.measure_lt_top.ne
  refine ⟨memLp_one_iff_integrable.1 (hL1.trans_lt hfin), ?_⟩
  rw [integral_norm_eq_lintegral_eNorm hf.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_eNorm hf.aestronglyMeasurable, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono hfin.ne hL1

end GlobalTheory.QuotLocInt
end

section

noncomputable section

open MeasureTheory

namespace GlobalTheory.Pc3.RS

theorem exists_finset_sep {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∀ (m : ℕ) (K : Submodule ℂ W), Module.finrank ℂ K = m →
      ∃ S : Finset X, ∀ w ∈ K, (∀ s ∈ S, (w : X → ℂ) s = 0) → w = 0 := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro K hK
    by_cases h0 : K = ⊥
    · exact ⟨∅, fun w hw _ => by rw [h0] at hw; exact (Submodule.mem_bot ℂ).1 hw⟩
    · obtain ⟨w0, hw0K, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
      have : ∃ x0, (w0 : X → ℂ) x0 ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hw0 (Subtype.ext (funext hc))
      obtain ⟨x0, hx0⟩ := this
      let e : W →ₗ[ℂ] ℂ := (LinearMap.proj x0).comp W.subtype
      let K' : Submodule ℂ W := K ⊓ LinearMap.ker e
      have hlt : K' < K := by
        refine lt_of_le_of_ne inf_le_left fun heq => ?_
        have : w0 ∈ K' := heq ▸ hw0K
        exact hx0 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2)
      have hr : Module.finrank ℂ K' < m := hK ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨S, hS⟩ := ih _ hr K' rfl
      refine ⟨insert x0 S, fun w hw hv => hS w (Submodule.mem_inf.2 ⟨hw, ?_⟩) fun s hs => hv s (Finset.mem_insert_of_mem hs)⟩
      exact LinearMap.mem_ker.2 (hv x0 (Finset.mem_insert_self _ _))

theorem integral_mem {X Y : Type} [MeasurableSpace Y] (μ : Measure Y) (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] (G : Y → X → ℂ) (hG : ∀ y, G y ∈ W) (hi : ∀ x, Integrable (fun y => G y x) μ) :
    (fun x => ∫ y, G y x ∂μ) ∈ W := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_sep W _ ⊤ rfl
  let r : W →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun w s => (w : X → ℂ) s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact hS w Submodule.mem_top fun s hs => congrFun hw ⟨s, hs⟩
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective r hinj
  have key : ∀ (w : W) (x : X), (w : X → ℂ) x = ∑ s : S, (w : X → ℂ) s * ((L (Pi.single s 1) : W) : X → ℂ) x := by
    intro w x
    have h1 : L (r w) = w := by simpa using LinearMap.congr_fun hL w
    have h2 : r w = ∑ s : S, (w : X → ℂ) s • (Pi.single s 1 : S → ℂ) := by
      ext t
      simp [r, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [← h1, h2]

    simp [map_sum, map_smul, Finset.sum_apply]
  have hfun : (fun x => ∫ y, G y x ∂μ) =
      ((∑ s : S, (∫ y, G y s ∂μ) • L (Pi.single s 1) : W) : X → ℂ) := by
    funext x
    have e : ∀ y, G y x = ∑ s : S, G y s * ((L (Pi.single s 1) : W) : X → ℂ) x :=
      fun y => key ⟨G y, hG y⟩ x
    simp_rw [e]
    rw [integral_finsetSum (Finset.univ : Finset S) fun (s : S) _ =>
      (hi (s : X)).mul_const (((L (Pi.single s 1) : W) : X → ℂ) x)]
    simp only [integral_mul_const, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact Submodule.coe_mem _

end GlobalTheory.Pc3.RS
end
end
