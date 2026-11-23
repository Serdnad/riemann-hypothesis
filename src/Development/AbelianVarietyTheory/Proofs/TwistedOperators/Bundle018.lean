module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SimpleModule.Basic
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
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory.Twist

theorem lintegral_haar_eq_transversal (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace E] (μ mK : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
    [IsProbabilityMeasure mK] (lam : Measure E) [SFinite lam] (K : Set G) (e : E → G)
    (he : Measurable e) (hK : mK Kᶜ = 0)
    (hinv : ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK) (hlam : lam ≠ 0)
    (hfin : ∀ C : Set G, IsCompact C → lam {B | ∃ k ∈ K, k * e B ∈ C} < ⊤)
    (hact : ∀ g : G, ∃ ψ : E → E, Measurable ψ ∧ Measure.map ψ lam = lam ∧
      ∀ B, ∃ κ ∈ K, e B * g = κ * e (ψ B)) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂μ = ENNReal.ofReal c * ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
  have hm : Measurable (fun z : E × G => z.2 * e z.1) :=
    measurable_snd.mul (he.comp measurable_fst)
  set ν : Measure G := Measure.map (fun z : E × G => z.2 * e z.1) (lam.prod mK) with hν
  have hint : ∀ f : G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂ν = ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
    intro f hf
    rw [hν, lintegral_map hf hm]
    exact lintegral_prod (fun z : E × G => f (z.2 * e z.1)) (hf.comp hm).aemeasurable
  have hH : ∀ f : G → ENNReal, Measurable f →
      Measurable (fun B => ∫⁻ k, f (k * e B) ∂mK) := by
    intro f hf
    exact Measurable.lintegral_prod_right' (f := fun z : E × G => f (z.2 * e z.1)) (hf.comp hm)
  have hR : ν.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨ψ, hψ, hψl, hψe⟩ := hact g
    refine Measure.ext_of_lintegral _ (fun f hf => ?_)
    have hg : Measurable (fun x : G => x * g) := measurable_mul_const g
    rw [lintegral_map hf hg, hint (fun x => f (x * g)) (hf.comp hg), hint f hf]
    have h1 : ∀ B, ∫⁻ k, f (k * e B * g) ∂mK = ∫⁻ k, f (k * e (ψ B)) ∂mK := by
      intro B
      obtain ⟨κ, hκ, hk⟩ := hψe B
      have h2 := lintegral_map (μ := mK) (f := fun x => f (x * e (ψ B))) (g := fun x => x * κ)
        (hf.comp (measurable_mul_const _)) (measurable_mul_const κ)
      rw [hinv κ hκ] at h2
      rw [h2]
      simp only [mul_assoc, hk]
    simp only [h1]
    have h3 := lintegral_map (μ := lam) (hH f hf) hψ
    rw [hψl] at h3
    exact h3.symm
  have hF : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun C hC => ?_⟩
    have hCm : MeasurableSet C := hC.measurableSet
    have h1 := hint (C.indicator 1) (measurable_one.indicator hCm)
    rw [lintegral_indicator_one hCm] at h1
    rw [h1]
    set S := {B | ∃ k ∈ K, k * e B ∈ C} with hS
    refine lt_of_le_of_lt ?_ (hfin C hC)
    rw [← measure_toMeasurable, ← lintegral_indicator_one (measurableSet_toMeasurable _ _)]
    refine lintegral_mono (fun B => ?_)
    by_cases hB : B ∈ toMeasurable lam S
    · rw [Set.indicator_of_mem hB]
      calc ∫⁻ k, C.indicator (1 : G → ENNReal) (k * e B) ∂mK ≤ ∫⁻ _k, 1 ∂mK :=
            lintegral_mono (fun k => Set.indicator_le_self' (fun _ _ => zero_le_one) _)
        _ = 1 := by simp
    · rw [Set.indicator_of_notMem hB]
      have hB' : B ∉ S := fun h => hB (subset_toMeasurable _ _ h)
      have hae : ∀ᵐ k ∂mK, k ∈ K := hK
      have : ∫⁻ k, C.indicator (1 : G → ENNReal) (k * e B) ∂mK = ∫⁻ _k, 0 ∂mK := by
        refine lintegral_congr_ae (hae.mono fun k hk => ?_)
        exact Set.indicator_of_notMem (fun h => hB' ⟨k, hk, h⟩) _
      simp [this]
  have hν0 : ν ≠ 0 := by
    intro h
    have h1 := hint (fun _ => 1) measurable_const
    rw [h] at h1
    simp at h1
    exact hlam (Measure.measure_univ_eq_zero.mp h1.symm)
  have hmul := Measure.isMulLeftInvariant_eq_smul ν.inv μ
  set c := Measure.haarScalarFactor ν.inv μ with hc
  have hνc : ν = c • μ := by
    have : ν.inv.inv = (c • μ).inv := by rw [← hmul]
    rw [Measure.inv_inv] at this
    rw [this]
    change Measure.map _ (c • μ) = _
    rw [Measure.map_smul (c := c) (f := Inv.inv)
      (measurable_inv.aemeasurable : AEMeasurable Inv.inv μ), Measure.map_inv_eq_self μ]
  have hc0 : c ≠ 0 := by
    intro h
    apply hν0
    rw [hνc, h, zero_smul]
  refine ⟨((c⁻¹ : NNReal) : ℝ), by exact_mod_cast inv_pos.mpr (pos_iff_ne_zero.mpr hc0), fun f hf => ?_⟩
  rw [← hint f hf, hνc, lintegral_smul_measure, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul,
    ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0]
  simp

end GlobalTheory.Twist
end

section

open MeasureTheory
open scoped Pointwise NNReal ENNReal

namespace GlobalTheory

theorem haar_map_mul_right_of_mem_compact_subgroup {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hK : IsCompact (K : Set G))
    (k : G) (hk : k ∈ K) : Measure.map (fun g => g * k) μ = μ := by
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g => g * k) μ) μ
  set c := Measure.haarScalarFactor (Measure.map (fun g => g * k) μ) μ with hc
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have hS : IsCompact (C * (K : Set G)) := hC.mul hK
  have hsub : C ⊆ C * (K : Set G) := fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩
  have hpos : 0 < μ (C * (K : Set G)) :=
    Measure.measure_pos_of_mem_nhds μ (Filter.mem_of_superset hC1 hsub)
  have hfin : μ (C * (K : Set G)) < ⊤ := hS.measure_lt_top
  have hpre : (fun g => g * k) ⁻¹' (C * (K : Set G)) = C * (K : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      refine ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), ?_⟩
      simp only at hab ⊢
      rw [← mul_assoc, hab, mul_inv_cancel_right]
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, K.mul_mem hb hk, (mul_assoc _ _ _).symm⟩
  have h1 : Measure.map (fun g => g * k) μ (C * (K : Set G)) = μ (C * (K : Set G)) := by
    have := (MeasurableEquiv.mulRight k).map_apply (μ := μ) (C * (K : Set G))
    rw [MeasurableEquiv.coe_mulRight, hpre] at this
    exact this
  have h2 : (c : ℝ≥0∞) * μ (C * (K : Set G)) = 1 * μ (C * (K : Set G)) := by
    rw [one_mul]
    conv_rhs => rw [← h1, h]
    simp
  have h3 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h2
  have h4 : c = 1 := by exact_mod_cast h3
  rw [h, h4, one_smul]

end GlobalTheory
end

section

namespace GlobalTheory.SmulMemOfMemSpanExists

theorem exists_smul_mem_of_mem_span {Oe K'' T : Type} [CommRing Oe] [IsDomain Oe] [Field K'']
    [Algebra Oe K''] [IsFractionRing Oe K''] [AddCommGroup T] [Module K'' T] [Module Oe T]
    [IsScalarTower Oe K'' T] (M : Submodule Oe T) {x : T}
    (hx : x ∈ Submodule.span K'' (↑M : Set T)) : ∃ c : Oe, c ≠ (0 : Oe) ∧ c • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hay
    · rw [mul_smul]; exact M.smul_mem _ hbz
  | smul k y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := Oe) k
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap Oe K'' d ≠ 0 := fun h =>
      hd0 (IsFractionRing.injective Oe K'' (by rw [h, map_zero]))
    refine ⟨a * d, mul_ne_zero ha hd0, ?_⟩
    have key : (a * d) • ((algebraMap Oe K'' n / algebraMap Oe K'' d) • y) = n • (a • y) := by
      rw [← algebraMap_smul K'' (a * d), ← algebraMap_smul K'' n, ← algebraMap_smul K'' a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem _ hay

end GlobalTheory.SmulMemOfMemSpanExists
end

section

namespace GlobalTheory.SmulMemOfMemSpan

theorem exists_smul_mem_of_mem_span {R K V : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] (M : Submodule R V) {v : V}
    (hv : v ∈ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm a b, mul_smul]; exact M.smul_mem b hax
    · rw [mul_smul]; exact M.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) c
    dsimp only at hnd
    refine ⟨d * a, mul_ne_zero (nonZeroDivisors.ne_zero d.2) ha, ?_⟩
    have key : (d : R) • c • x = n • x := by
      rw [← algebraMap_smul K (d : R) (c • x), smul_smul, mul_comm, hnd, algebraMap_smul]
    rw [mul_comm (d : R) a, mul_smul, key, smul_comm a n x]
    exact M.smul_mem n hax

theorem main : ∀ {R K V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K] [inst_5 : AddCommGroup V] [inst_6 : Module R V] [inst_7 : Module K V] [IsScalarTower R K V] (M : Submodule R V) {v : V}, v ∈ Submodule.span K (↑M : Set V) → ∃ (a : R), a ≠ (0 : R) ∧ a • v ∈ M :=
  by
  intro R K V _ _ _ _ _ _ _ _ _ M v hv
  exact exists_smul_mem_of_mem_span M hv

end GlobalTheory.SmulMemOfMemSpan
end

section

universe u_1 u_2 u_3

namespace GlobalTheory.OrthogonalProjectionOnto

open Module

section

variable {R : Type u_1} [Ring R] {ι : Type u_2} [Fintype ι] [DecidableEq ι]
  (M : ι → Type u_3) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem endo_apply_eq (h : ∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = 0)
    (g : (Π i, M i) →ₗ[R] (Π i, M i)) (x : Π i, M i) (i : ι) :
    g x i = g (Pi.single i (x i)) i := by
  have hx : x = ∑ j, Pi.single j (x j) := (Finset.univ_sum_single x).symm
  conv_lhs => rw [hx]

  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · intro j _ hji
    have h0 := h j i hji ((LinearMap.proj i).comp (g.comp (LinearMap.single R M j)))
    exact LinearMap.congr_fun h0 (x j)
  · intro hi
    exact absurd (Finset.mem_univ i) hi

def projOnto (h : ∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = 0) (i₀ : ι) :
    End (End R (Π i, M i)) (Π i, M i) where
  toFun x := fun i => if i = i₀ then x i else 0
  map_add' x y := by
    funext i
    split_ifs <;> simp_all
  map_smul' g x := by
    funext i
    simp only [RingHom.id_apply, Module.End.smul_def]
    rw [endo_apply_eq M h g x i, endo_apply_eq M h g (fun i => if i = i₀ then x i else 0) i]
    split_ifs with hi
    · rfl
    · simp

end

theorem main : ∀ {R : Type u_1} [inst : Ring R] {ι : Type u_2} [Fintype ι] [inst_2 : DecidableEq ι]
    (M : ι → Type u_3) [inst_3 : (i : ι) → AddCommGroup (M i)] [inst_4 : (i : ι) → Module R (M i)]
    [∀ (i : ι), IsSimpleModule R (M i)],
    (∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = (0 : M i →ₗ[R] M j)) →
    ∀ (i₀ : ι) (s : (i : ι) → Finset (M i)), ∃ (r : R), ∀ (i : ι), ∀ m ∈ s i,
      r • m = if i = i₀ then m else (0 : M i) := by
  intro R _ ι _ _ M _ _ _ h i₀ s
  letI : DecidableEq (Π i, M i) := Classical.decEq _
  obtain ⟨r, hr⟩ := jacobson_density (R := R) (M := Π i, M i) (projOnto M h i₀)
    (Finset.univ.biUnion fun i => (s i).image (Pi.single i))
  refine ⟨r, fun i m hm => ?_⟩
  have hmem : Pi.single i m ∈ Finset.univ.biUnion fun i => (s i).image (Pi.single (M := M) i) := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    exact ⟨i, m, hm, rfl⟩
  have := congrFun (hr _ hmem) i
  simp only [projOnto, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same, Pi.smul_apply] at this
  exact this.symm

end GlobalTheory.OrthogonalProjectionOnto
end
