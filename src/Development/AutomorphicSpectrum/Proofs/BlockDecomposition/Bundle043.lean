module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

section

open Filter Topology
open scoped Classical

namespace GlobalTheory.CompanionTheory.ExpSums

theorem tendsto_one_add_pow_mul_pow {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (N : ℕ) :
    Tendsto (fun n : ℕ => (1 + (n : ℝ)) ^ N * t ^ n) atTop (𝓝 0) := by
  have ht : |t| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) ^ N * ((n : ℝ) ^ N * t ^ n)) atTop (𝓝 0) := by
    have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one N ht).const_mul ((2 : ℝ) ^ N)
    rwa [mul_zero] at h
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => mul_nonneg (by positivity) (pow_nonneg h0 n)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : (1 + (n : ℝ)) ^ N ≤ (2 * (n : ℝ)) ^ N := by
    gcongr
    linarith
  calc (1 + (n : ℝ)) ^ N * t ^ n ≤ (2 * (n : ℝ)) ^ N * t ^ n :=
        mul_le_mul_of_nonneg_right hle (pow_nonneg h0 n)
    _ = (2 : ℝ) ^ N * ((n : ℝ) ^ N * t ^ n) := by ring

theorem expSum_holds : PositivityTheory.Rg.BcB.F.ExpSum := by
  intro ι _ c lam ρ C N hρ hbound μ hμ
  obtain ⟨d, hd⟩ : ∃ d : ℂ → ℂ, ∀ ν, d ν = ∑ i with lam i = ν, c i := ⟨_, fun _ => rfl⟩
  rw [← hd]
  obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, S = Finset.univ.image lam := ⟨_, rfl⟩
  by_cases hμS : μ ∉ S
  · rw [hd]
    refine Finset.sum_eq_zero fun i hi => absurd ?_ hμS
    rw [hS, ← (Finset.mem_filter.mp hi).2]
    exact Finset.mem_image_of_mem lam (Finset.mem_univ i)
  push_neg at hμS
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι), lam i ∈ S := fun i _ => by
    rw [hS]; exact Finset.mem_image_of_mem lam (Finset.mem_univ i)
  have hsum : ∀ k : ℕ, ∑ i, c i * lam i ^ k = ∑ ν ∈ S, d ν * ν ^ k := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hd, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  obtain ⟨e, -⟩ : ∃ e : Fin S.card ≃ S, e = S.equivFin.symm := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : Fin S.card → ℂ, ∀ k, α k = (e k : ℂ) := ⟨_, fun _ => rfl⟩
  have hinj : Function.Injective α := by
    intro a b hab
    rw [hα, hα] at hab
    exact e.injective (Subtype.val_injective hab)
  have hpow : ∀ n : ℕ, ∑ k, d (α k) * α k ^ n = ∑ i, c i * lam i ^ n := by
    intro n
    rw [hsum n]
    simp only [hα]
    exact (Equiv.sum_comp e (fun x : S => d x * (x : ℂ) ^ n)).trans
      (Finset.sum_coe_sort S (fun ν => d ν * ν ^ n))
  obtain ⟨C', hC'⟩ := GlobalTheory.CompanionTheory.ExpSums.vandermonde_separation S.card α hinj
  obtain ⟨C1, hC1, hC'1⟩ : ∃ C1 : ℝ, 0 ≤ C1 ∧ C' ≤ C1 := ⟨max C' 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨C2, hC2, hCC2⟩ : ∃ C2 : ℝ, 0 ≤ C2 ∧ C ≤ C2 := ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ s : Fin S.card, (1 + ((s : ℕ) : ℝ)) ^ N * ρ ^ (s : ℕ) := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hbound
  have hK0' : ∀ k : ℕ, K0 ≤ k → ‖∑ i, c i * lam i ^ k‖ ≤ C2 * (1 + (k : ℝ)) ^ N * ρ ^ k := by
    intro k hk
    refine (hK0 k hk).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC2 (pow_nonneg (by positivity) N)) (pow_nonneg hρ k)
  obtain ⟨j, hj⟩ : ∃ j : Fin S.card, α j = μ := ⟨e.symm ⟨μ, hμS⟩, by rw [hα, Equiv.apply_symm_apply]⟩
  have key : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ * ‖μ‖ ^ m ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) := by
    intro m hm
    have h1 := hC' (fun k => d (α k) * α k ^ m) j
    have hinner : ∀ s : Fin S.card,
        ∑ k, d (α k) * α k ^ m * α k ^ (s : ℕ) = ∑ i, c i * lam i ^ (m + (s : ℕ)) := by
      intro s
      rw [← hpow (m + (s : ℕ))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add]
      ring
    simp only [hinner, hj, norm_mul, norm_pow] at h1
    have hT : 0 ≤ ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsb : ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ ≤
        C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have hk := hK0' (m + (s : ℕ)) (le_trans hm (Nat.le_add_right m _))
      rw [Nat.cast_add] at hk
      have hbase : 1 + ((m : ℝ) + ((s : ℕ) : ℝ)) ≤ (1 + (m : ℝ)) * (1 + ((s : ℕ) : ℝ)) := by
        have hms : (0 : ℝ) ≤ (m : ℝ) * ((s : ℕ) : ℝ) := by positivity
        nlinarith
      have hle : (1 + ((m : ℝ) + ((s : ℕ) : ℝ))) ^ N ≤ (1 + (m : ℝ)) ^ N * (1 + ((s : ℕ) : ℝ)) ^ N := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hbase N
      calc ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖
          ≤ C2 * (1 + ((m : ℝ) + ((s : ℕ) : ℝ))) ^ N * ρ ^ (m + (s : ℕ)) := hk
        _ ≤ C2 * ((1 + (m : ℝ)) ^ N * (1 + ((s : ℕ) : ℝ)) ^ N) * ρ ^ (m + (s : ℕ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hC2) (pow_nonneg hρ _)
        _ = C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * ((1 + ((s : ℕ) : ℝ)) ^ N * ρ ^ (s : ℕ)) := by
          rw [pow_add]
          ring
    calc ‖d μ‖ * ‖μ‖ ^ m ≤ C' * ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ := h1
      _ ≤ C1 * ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ :=
        mul_le_mul_of_nonneg_right hC'1 hT
      _ ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) := mul_le_mul_of_nonneg_left hsb hC1
  have hμpos : 0 < ‖μ‖ := lt_of_le_of_lt hρ hμ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ρ / ‖μ‖ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hρ (norm_nonneg _)
  have ht1 : t < 1 := by rw [ht, div_lt_one hμpos]; exact hμ
  have hlim := (tendsto_one_add_pow_mul_pow ht0 ht1 N).const_mul (C1 * (C2 * B))
  rw [mul_zero] at hlim
  have hle : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ ≤ C1 * (C2 * B) * ((1 + (m : ℝ)) ^ N * t ^ m) := by
    intro m hm
    have h := (le_div_iff₀ (pow_pos hμpos m)).mpr (key m hm)
    rw [ht, div_pow]
    calc ‖d μ‖ ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) / ‖μ‖ ^ m := h
      _ = C1 * (C2 * B) * ((1 + (m : ℝ)) ^ N * (ρ ^ m / ‖μ‖ ^ m)) := by ring
  have h0 : ‖d μ‖ ≤ 0 := ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨K0, hle⟩)
  exact norm_le_zero_iff.mp h0

end GlobalTheory.CompanionTheory.ExpSums
end

section

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.CellSumProof

noncomputable def hits (X : Ctx) (S : Set X.G) (x : X.G) : ℝ≥0∞ :=
  ∑' γ : X.Γ, S.indicator 1 ((γ : X.G) * x)

theorem measurable_hits (X : Ctx) {S : Set X.G} (hS : MeasurableSet S) :
    Measurable (hits X S) := by
  unfold hits
  refine Measurable.tsum fun γ => ?_
  exact (measurable_one.indicator hS).comp (measurable_const_mul (γ : X.G))

theorem lintegral_hits (X : Ctx) {S : Set X.G} (hS : MeasurableSet S) :
    ∫⁻ x, hits X S x ∂X.ν = X.μ S := by
  haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hm : ∀ γ : X.Γ, AEMeasurable (fun x : X.G => S.indicator (1 : X.G → ℝ≥0∞) ((γ : X.G) * x)) X.ν :=
    fun γ => ((measurable_one.indicator hS).comp (measurable_const_mul (γ : X.G))).aemeasurable
  have h1 : ∫⁻ x, hits X S x ∂X.ν
      = ∑' γ : X.Γ, ∫⁻ x in X.F, S.indicator (1 : X.G → ℝ≥0∞) ((γ : X.G) * x) ∂X.μ := by
    unfold hits
    exact lintegral_tsum hm
  have h2 := X.fd.lintegral_eq_tsum'' (S.indicator (1 : X.G → ℝ≥0∞))
  rw [h1]
  have h3 : ∫⁻ x, S.indicator (1 : X.G → ℝ≥0∞) x ∂X.μ = X.μ S := lintegral_indicator_one hS
  rw [← h3, h2]
  rfl

theorem cnt_le_hits (X : Ctx) {Ω₀ Ω : Set X.G} {δ a o x : X.G} (hδ : δ ∈ X.Γ) (ho : o ∈ Ω₀)
    (hx : δ * x = a * o) : cnt X.Γ Ω x ≤ hits X (a • (Ω₀ * Ω)) x := by
  unfold cnt hits
  let e : X.Γ ≃ X.Γ := Equiv.mulLeft (⟨δ, hδ⟩ : X.Γ)
  rw [← e.tsum_eq (fun γ : X.Γ => (a • (Ω₀ * Ω)).indicator (1 : X.G → ℝ≥0∞) ((γ : X.G) * x))]
  refine ENNReal.tsum_le_tsum fun γ => ?_
  by_cases h : x⁻¹ * (γ : X.G) * x ∈ Ω
  · have hmem : ((e γ : X.Γ) : X.G) * x ∈ a • (Ω₀ * Ω) := by
      refine Set.mem_smul_set.2 ⟨o * (x⁻¹ * (γ : X.G) * x), Set.mul_mem_mul ho h, ?_⟩
      have : ((e γ : X.Γ) : X.G) = δ * (γ : X.G) := rfl
      rw [this, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← hx]
      group
    rw [Set.indicator_of_mem h, Set.indicator_of_mem hmem]
    simp
  · rw [Set.indicator_of_notMem h]
    exact bot_le

theorem cellSum_holds : CellSum := by
  intro X ι _ a Ω₀ Ω w c h₀ hΩ hcov hw hc
  have hcomp : IsCompact (Ω₀ * Ω) := h₀.mul hΩ
  have hmeas : ∀ i, MeasurableSet (a i • (Ω₀ * Ω)) := fun i =>
    (hcomp.smul (a i)).measurableSet
  have hpt : ∀ x, w x * cnt X.Γ Ω x ≤ ∑' i, c i * hits X (a i • (Ω₀ * Ω)) x := by
    intro x
    obtain ⟨δ, hδ, i, o, ho, hx⟩ := hcov x
    have hwx : w x ≤ c i := by
      rw [← hw δ hδ x, hx]
      exact hc i o ho
    calc w x * cnt X.Γ Ω x ≤ c i * hits X (a i • (Ω₀ * Ω)) x :=
          mul_le_mul' hwx (cnt_le_hits X hδ ho hx)
      _ ≤ _ := le_tsum (fun j => c j * hits X (a j • (Ω₀ * Ω)) x) i
  calc ∫⁻ x, w x * cnt X.Γ Ω x ∂X.ν
      ≤ ∫⁻ x, ∑' i, c i * hits X (a i • (Ω₀ * Ω)) x ∂X.ν := lintegral_mono hpt
    _ = ∑' i, ∫⁻ x, c i * hits X (a i • (Ω₀ * Ω)) x ∂X.ν :=
        lintegral_tsum fun i => ((measurable_hits X (hmeas i)).const_mul _).aemeasurable
    _ = ∑' i, c i * X.μ (Ω₀ * Ω) := by
        refine tsum_congr fun i => ?_
        rw [lintegral_const_mul _ (measurable_hits X (hmeas i)), lintegral_hits X (hmeas i),
          measure_smul]
    _ = X.μ (Ω₀ * Ω) * ∑' i, c i := by
        rw [ENNReal.tsum_mul_right, mul_comm]

theorem cellSum_of_cntBasic : CntBasic → CellSum := fun _ => cellSum_holds

end GlobalTheory.CompanionTheory.CellSumProof
end

section

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelColumn

theorem colSq_of_kerBasic : KerBasic → ColSq := by
  intro hK X φ B Ω hT hB hΩ hS y
  letI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hker := (hK X φ hT).2.2.2.2.2
  have hBe : ∀ z, ‖φ z‖ₑ ≤ ENNReal.ofReal B := fun z => by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hB z)
  let A : X.G → ℝ≥0∞ := fun x => ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ
  have hterm : ∀ γ : X.Γ, Measurable fun x : X.G => ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ := fun γ =>
    (hT.1.comp (by fun_prop)).enorm.measurable
  have hAm : Measurable A := Measurable.tsum hterm
  have hAinv : ∀ (δ : X.Γ) (x : X.G), A ((δ : X.G) * x) = A x := by
    intro δ x
    simp only [A]
    rw [← (Equiv.mulLeft δ).tsum_eq (fun γ : X.Γ => ‖φ (((δ : X.G) * x)⁻¹ * (γ : X.G) * y)‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp [mul_assoc]
  let g : X.G → ℝ≥0∞ := fun x => ‖φ (x⁻¹ * y)‖ₑ * A x
  have hgm : Measurable g :=
    ((hT.1.comp (by fun_prop : Continuous fun x : X.G => x⁻¹ * y)).enorm.measurable).mul hAm
  have hsq : ∀ x, A x ^ 2 = ∑' γ : X.Γ, g (γ⁻¹ • x) := by
    intro x
    rw [sq]
    calc A x * A x = (∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ) * A x := rfl
      _ = ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ * A x := ENNReal.tsum_mul_right.symm
      _ = ∑' γ : X.Γ, g (γ⁻¹ • x) := by
        refine tsum_congr fun γ => ?_
        have e : γ⁻¹ • x = ((γ⁻¹ : X.Γ) : X.G) * x := rfl
        simp only [g]
        rw [e, hAinv]
        simp [mul_assoc]
  let c : ℝ≥0∞ := ENNReal.ofReal B * (ENNReal.ofReal B * cnt X.Γ (Ω⁻¹ * Ω) y)
  have hg : ∀ x, g x ≤ (y • Ω⁻¹).indicator (fun _ => c) x := by
    intro x
    by_cases h0 : φ (x⁻¹ * y) = 0
    · simp [g, h0]
    · have hω : x⁻¹ * y ∈ Ω := hS h0
      have hx : x ∈ y • Ω⁻¹ := by
        rw [Set.mem_smul_set]
        exact ⟨y⁻¹ * x, by simpa [Set.mem_inv] using hω, by simp⟩
      rw [Set.indicator_of_mem hx]
      have h2 : A x ≤ ENNReal.ofReal B * cnt X.Γ (Ω⁻¹ * Ω) y := by
        simp only [A, cnt]
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun γ => ?_
        by_cases h3 : φ (x⁻¹ * (γ : X.G) * y) = 0
        · simp [h3]
        · have hm : y⁻¹ * (γ : X.G) * y ∈ Ω⁻¹ * Ω :=
            Set.mem_mul.2 ⟨(x⁻¹ * y)⁻¹, Set.inv_mem_inv.2 hω, x⁻¹ * (γ : X.G) * y, hS h3, by group⟩
          rw [Set.indicator_of_mem hm]
          simpa using hBe _
      exact mul_le_mul' (hBe _) h2
  calc ∫⁻ x, ‖ker X.Γ φ x y‖ₑ ^ 2 ∂X.ν ≤ ∫⁻ x, A x ^ 2 ∂X.ν :=
        lintegral_mono fun x => pow_le_pow_left' (hker x y) 2
    _ = ∫⁻ x in X.F, ∑' γ : X.Γ, g (γ⁻¹ • x) ∂X.μ := by
        simp only [hsq]; rfl
    _ = ∑' γ : X.Γ, ∫⁻ x in X.F, g (γ⁻¹ • x) ∂X.μ :=
        lintegral_tsum fun γ => (hgm.comp (measurable_const_mul ((γ⁻¹ : X.Γ) : X.G))).aemeasurable
    _ = ∫⁻ x, g x ∂X.μ := (X.fd.lintegral_eq_tsum' g).symm
    _ ≤ ∫⁻ x, (y • Ω⁻¹).indicator (fun _ => c) x ∂X.μ := lintegral_mono hg
    _ ≤ c * X.μ (y • Ω⁻¹) := lintegral_indicator_const_le _ _
    _ = ENNReal.ofReal B ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y := by
        rw [measure_smul]
        simp only [c]
        ring

end GlobalTheory.CompanionTheory.KernelColumn
end

section

open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelOperators

theorem comp_key (hB : KerBasic) (hR : RowInt) (hL : KernelL2RowsColumns) (hS : SchurInt) (hM : KerMul)
    (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ) (hψ : Tst ψ) (x : X.G) (f : X.G → ℂ)
    (hf : MemLp f 2 X.ν) :
    Integrable (fun z => ker X.Γ φ x z * ∫ y, ker X.Γ ψ z y * f y ∂X.ν) X.ν ∧
    ∫ z, ker X.Γ φ x z * (∫ y, ker X.Γ ψ z y * f y ∂X.ν) ∂X.ν
      = ∫ y, ker X.Γ (cv X.μ φ ψ) x y * f y ∂X.ν := by
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  obtain ⟨A, hA, hrow, hcol⟩ := hR X ψ hψ
  have hmeas : Measurable (Function.uncurry (ker X.Γ ψ)) := (hB X ψ hψ).2.1.measurable
  have hint := hS X.G X.ν (ker X.Γ ψ) A hmeas hA hrow hcol (fun z => ker X.Γ φ x z) f
    ((hL X φ hφ).2 x) hf
  have e1 : ∀ z, ∫ y, ker X.Γ φ x z * ker X.Γ ψ z y * f y ∂X.ν
      = ker X.Γ φ x z * ∫ y, ker X.Γ ψ z y * f y ∂X.ν := by
    intro z
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  constructor
  · have h := hint.integral_prod_left
    simpa only [e1] using h
  · have h := integral_integral_swap
      (f := fun z y => ker X.Γ φ x z * ker X.Γ ψ z y * f y) hint
    simp only [e1] at h
    rw [h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [integral_mul_const]
    rw [hM X φ ψ hφ hψ x y]

theorem opMul : KerBasic → KerLin → RowInt → KernelL2RowsColumns → SchurInt → CvTest → KerMul → OpMul := by
  intro hB hLin hR hL hS hC hM X ι _ Φ₁ Φ₂ T₁ T₂ h₁ h₂ o₁ o₂
  have tcv : ∀ i j k, Tst (cv X.μ (Φ₁ i k) (Φ₂ k j)) :=
    fun i j k => (hC X _ _ (h₁ i k) (h₂ k j)).1
  have lin : ∀ i j, Tst (fun y => ∑ k, cv X.μ (Φ₁ i k) (Φ₂ k j) y) ∧
      ∀ x y, ker X.Γ (fun y => ∑ k, cv X.μ (Φ₁ i k) (Φ₂ k j) y) x y
        = ∑ k, ker X.Γ (cv X.μ (Φ₁ i k) (Φ₂ k j)) x y := by
    intro i j
    have h := hLin X ι (fun k => cv X.μ (Φ₁ i k) (Φ₂ k j)) (fun _ => 1) (fun k => tcv i j k)
    simpa only [mul_one] using h
  refine ⟨fun i j => (lin i j).1, ?_⟩
  intro f i
  have a1 := o₁ (T₂ f) i
  show ((T₁ (T₂ f)) i : X.G → ℂ) =ᵐ[X.ν] _
  filter_upwards [a1] with x hx
  rw [hx]
  have hfj : ∀ j, MemLp (f j : X.G → ℂ) 2 X.ν := fun j => Lp.memLp _
  have step : ∀ k, ∫ z, ker X.Γ (Φ₁ i k) x z * ((T₂ f) k : X.G → ℂ) z ∂X.ν
      = ∑ j, ∫ y, ker X.Γ (cv X.μ (Φ₁ i k) (Φ₂ k j)) x y * (f j : X.G → ℂ) y ∂X.ν := by
    intro k
    have e : (fun z => ker X.Γ (Φ₁ i k) x z * ((T₂ f) k : X.G → ℂ) z) =ᵐ[X.ν]
        fun z => ∑ j, ker X.Γ (Φ₁ i k) x z *
          ∫ y, ker X.Γ (Φ₂ k j) z y * (f j : X.G → ℂ) y ∂X.ν := by
      filter_upwards [o₂ f k] with z hz
      rw [hz, Finset.mul_sum]
    rw [integral_congr_ae e, MeasureTheory.integral_finsetSum _ fun j _ =>
      (comp_key hB hR hL hS hM X _ _ (h₁ i k) (h₂ k j) x _ (hfj j)).1]
    exact Finset.sum_congr rfl fun j _ =>
      (comp_key hB hR hL hS hM X _ _ (h₁ i k) (h₂ k j) x _ (hfj j)).2
  rw [Finset.sum_congr rfl fun k _ => step k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [(lin i j).2, Finset.sum_mul]
  have hi : ∀ k, Integrable
      (fun y => ker X.Γ (cv X.μ (Φ₁ i k) (Φ₂ k j)) x y * (f j : X.G → ℂ) y) X.ν :=
    fun k => MemLp.integrable_mul ((hL X _ (tcv i j k)).2 x) (hfj j)
  exact (MeasureTheory.integral_finsetSum _ fun k _ => hi k).symm

end GlobalTheory.CompanionTheory.KernelOperators
end

section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelComposition

theorem integral_ker_mul_eq_unfolded (hk : KerBasic) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ)
    (hψ : Tst ψ) (x y : X.G) :
    ∫ z, ker X.Γ φ x z * ker X.Γ ψ z y ∂X.ν = ∫ z, φ (x⁻¹ * z) * ker X.Γ ψ z y ∂X.μ := by
  haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set g : X.G → ℂ := fun z => φ (x⁻¹ * z) * ker X.Γ ψ z y with hg
  have hkc : Continuous fun z => ker X.Γ ψ z y :=
    (hk X ψ hψ).2.1.comp (continuous_id.prodMk continuous_const)
  have hgc : Continuous g := (hφ.1.comp (continuous_const.mul continuous_id)).mul hkc
  have hgs : HasCompactSupport g :=
    HasCompactSupport.mul_right (hφ.2.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hgi : Integrable g X.μ := hgc.integrable_of_hasCompactSupport hgs
  have hpt : ∀ z, ker X.Γ φ x z * ker X.Γ ψ z y = ∑' γ : X.Γ, g (γ • z) := by
    intro z
    have h1 : ∀ γ : X.Γ, g (γ • z) = φ (x⁻¹ * (γ : X.G) * z) * ker X.Γ ψ z y := by
      intro γ
      have h2 : γ • z = (γ : X.G) * z := rfl
      simp only [hg, h2, (hk X ψ hψ).2.2.1 γ γ.2 z y |>.1, mul_assoc]
    simp only [h1]
    rw [tsum_mul_right, ker, tsum_eq_finsum ((hk X φ hφ).1 x z)]
  have hmeas : ∀ γ : X.Γ, Continuous fun z => g (γ • z) := fun γ =>
    hgc.comp (continuous_const.mul continuous_id)
  have hfin : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν ≠ ∞ := by
    have h3 : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν = ∫⁻ z, ‖g z‖ₑ ∂X.μ :=
      (X.fd.lintegral_eq_tsum'' fun z => ‖g z‖ₑ).symm
    rw [h3]
    exact hgi.2.ne
  simp only [hpt]
  rw [integral_tsum (fun γ => (hmeas γ).aestronglyMeasurable) hfin]
  exact (X.fd.integral_eq_tsum'' g hgi).symm

theorem integral_shifted_eq_ker_cv (hc : CvTest) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ)
    (hψ : Tst ψ) (x y : X.G) :
    ∫ z, φ z * ker X.Γ ψ (x * z) y ∂X.μ = ker X.Γ (cv X.μ φ ψ) x y := by
  have hC : IsCompact ((fun w => x * w * y⁻¹) '' (tsupport φ * tsupport ψ)) :=
    (hφ.2.isCompact.mul hψ.2.isCompact).image (by fun_prop)
  have hfin := X.proper _ hC
  set s : Finset X.Γ := hfin.toFinset with hs
  have hmem : ∀ γ : X.Γ, x⁻¹ * (γ : X.G) * y ∈ tsupport φ * tsupport ψ → γ ∈ s := by
    intro γ h
    rw [hs, Set.Finite.mem_toFinset]
    exact ⟨_, h, by simp [mul_assoc]⟩
  have h1 : ∀ z, φ z * ker X.Γ ψ (x * z) y =
      ∑ γ ∈ s, φ z * ψ (z⁻¹ * (x⁻¹ * (γ : X.G) * y)) := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · rw [ker, finsum_eq_sum_of_support_subset (s := s), Finset.mul_sum]
      · refine Finset.sum_congr rfl fun γ _ => ?_
        simp only [mul_inv_rev, mul_assoc]
      · intro γ hγ
        refine Finset.mem_coe.2 (hmem γ ?_)
        have hγ' : (x * z)⁻¹ * (γ : X.G) * y ∈ tsupport ψ := subset_tsupport _ hγ
        refine ⟨z, hz, _, hγ', ?_⟩
        simp [mul_assoc]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hint : ∀ w : X.G, Integrable (fun z => φ z * ψ (z⁻¹ * w)) X.μ := by
    intro w
    have hcont : Continuous fun z => φ z * ψ (z⁻¹ * w) :=
      hφ.1.mul (hψ.1.comp (continuous_inv.mul continuous_const))
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.mul_right hφ.2)
  simp only [h1]
  rw [MeasureTheory.integral_finsetSum _ fun γ _ => hint _, ker,
    finsum_eq_sum_of_support_subset (s := s)]
  · rfl
  · intro γ hγ
    exact Finset.mem_coe.2 (hmem γ ((hc X φ ψ hφ hψ).2.1 hγ))

theorem kerMul_of_kerBasic_of_cvTest : KerBasic → CvTest → KerMul := by
  intro hk hc X φ ψ hφ hψ x y
  rw [integral_ker_mul_eq_unfolded hk X φ ψ hφ hψ x y,
    ← integral_shifted_eq_ker_cv hc X φ ψ hφ hψ x y,
    ← integral_mul_left_eq_self (fun z => φ (x⁻¹ * z) * ker X.Γ ψ z y) x]
  simp

end GlobalTheory.CompanionTheory.KernelComposition
end
