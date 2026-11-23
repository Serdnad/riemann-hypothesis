module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem ab_pow' {F : Type} [Field F] [NumberField F] (ρ : IdeleGroup F) (n : ℕ) :
    ab (ρ ^ n) = ab ρ ^ n := by
  induction n with
  | zero => simpa using M.ab_one (F := F)
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; exact M.ab_mul _ _

theorem UpperTheory.ConvolutionTheory.R2.M.ideleSum :
    ∀ (F : Type) [Field F] [NumberField F] (C : Set (IdeleGroup F)) (ρ : IdeleGroup F), IsCompact C → 1 < ab ρ → ∫⁻ a in ⋃ n : ℕ, (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F) < ⊤ := by
  intro F _ _ C ρ hC hρ
  have hcont : Continuous fun a : IdeleGroup F => (ab a)⁻¹ ^ 2 :=
    (M.continuous_ab.inv₀ fun a => (M.ab_pos a).ne').pow 2
  obtain ⟨B, hB⟩ := hC.bddAbove_image hcont.continuousOn
  have hBC : ∀ c ∈ C, (ab c)⁻¹ ^ 2 ≤ B := fun c hc => hB ⟨c, hc, rfl⟩
  set q : ℝ := (ab ρ)⁻¹ ^ 2 with hq
  have hρ0 : 0 < ab ρ := by linarith
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    have : (ab ρ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
    have h0 : 0 ≤ (ab ρ)⁻¹ := by positivity
    rw [hq]; nlinarith
  have hterm : ∀ n : ℕ, ∫⁻ a in (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F) ≤
      ENNReal.ofReal q ^ n * (ENNReal.ofReal B * ideleMeasure F C) := by
    intro n
    have hS : MeasurableSet ((ρ ^ n * ·) '' C) :=
      (hC.image (continuous_const_mul _)).measurableSet
    have hμ : ideleMeasure F ((ρ ^ n * ·) '' C) = ideleMeasure F C := by
      rw [Set.image_mul_left]; exact measure_preimage_mul _ _ _
    calc ∫⁻ a in (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F)
        ≤ ∫⁻ _ in (ρ ^ n * ·) '' C, ENNReal.ofReal q ^ n * ENNReal.ofReal B ∂(ideleMeasure F) := by
          refine setLIntegral_mono' hS ?_
          rintro _ ⟨c, hc, rfl⟩
          rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : (ab (ρ ^ n * c))⁻¹ ^ 2 = q ^ n * (ab c)⁻¹ ^ 2 := by
            rw [M.ab_mul, ab_pow', hq, mul_inv, mul_pow, inv_pow, inv_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
          rw [e]
          exact mul_le_mul_of_nonneg_left (hBC c hc) (by positivity)
      _ = ENNReal.ofReal q ^ n * (ENNReal.ofReal B * ideleMeasure F C) := by
          rw [setLIntegral_const, hμ, mul_assoc]
  have hr : ENNReal.ofReal q < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hq1
  have hfin : ENNReal.ofReal B * ideleMeasure F C < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top
  calc ∫⁻ a in ⋃ n : ℕ, (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F)
      ≤ ∑' n : ℕ, ∫⁻ a in (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F) := lintegral_iUnion_le _ _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal q ^ n * (ENNReal.ofReal B * ideleMeasure F C) := ENNReal.tsum_le_tsum hterm
    _ = (1 - ENNReal.ofReal q)⁻¹ * (ENNReal.ofReal B * ideleMeasure F C) := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 hr)) hfin
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.wtEx :
    ∀ (F : Type) [Field F] [NumberField F], ∃ β : G1 F → ℝ≥0∞, M.NWt β := by
  intro F _ _
  have hinj : Function.Injective (fun ξ : F => (nU (rt ξ : A F) : G1 F)) := by
    intro a b h
    have h1 : (nU (rt a : A F) : G1 F) 0 1 = (nU (rt b : A F) : G1 F) 0 1 := by
      rw [show (nU (rt a : A F) : G1 F) = nU (rt b : A F) from h]
    have h2 : (rt a : A F) = rt b := by simpa [nU] using h1
    exact AdeleRing.algebraMap_injective (𝓞 F) F h2
  let N : Subgroup (G1 F) :=
    { carrier := Set.range fun ξ : F => (nU (rt ξ : A F) : G1 F)
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by simp only [rt, map_add (f := _), M.nU_add]⟩
      one_mem' := ⟨0, by simp only [rt, map_zero, M.nU_zero]⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, by simp only [rt, map_neg, M.nU_neg]⟩ }
  have hle : N ≤ Gam F := by
    rintro _ ⟨ξ, rfl⟩
    exact M.nU_rt_mem ξ
  haveI : DiscreteTopology N :=
    DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  obtain ⟨D, hD, hu, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup N
  refine ⟨D.indicator 1, measurable_one.indicator hD, fun g => ?_⟩
  obtain ⟨n, hn, huniq⟩ := hu g
  obtain ⟨ξ₀, hξ₀⟩ := n.2
  have hn' : (nU (rt ξ₀ : A F) : G1 F) * g ∈ D := by
    have : (n : G1 F) * g ∈ D := hn
    rwa [← hξ₀] at this
  rw [tsum_eq_single ξ₀]
  · rw [Set.indicator_of_mem hn']
    rfl
  · intro ξ hξ
    refine Set.indicator_of_notMem (fun hmem => hξ ?_) _
    have h1 : (⟨nU (rt ξ : A F), ⟨ξ, rfl⟩⟩ : N) = n := huniq _ hmem
    have h2 : (nU (rt ξ : A F) : G1 F) = n := congrArg Subtype.val h1
    exact hinj (h2.trans hξ₀.symm)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.cdMeas :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (t : (A F)ˣ), MeasurePreserving (cD t) M₀.μ M₀.μ := by
  intro F _ _ M₀ t
  haveI := M₀.haar
  haveI := M₀.right
  have hm : ∀ s : (A F)ˣ, Measurable (cD s : G1 F → G1 F) := fun s => (M.continuous_cD s).measurable
  let e : G1 F ≃ₜ* G1 F :=
    { toFun := cD t
      invFun := cD t⁻¹
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      map_mul' := M.cD_mul t
      continuous_toFun := M.continuous_cD t
      continuous_invFun := M.continuous_cD t⁻¹ }
  haveI : (M₀.μ.map (cD t)).IsHaarMeasure := e.isHaarMeasure_map M₀.μ
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, M₀.μ.map (cD t) = c • M₀.μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (M₀.μ.map (cD t)) M₀.μ⟩
  have h2 : M₀.μ.map (cD (t * t)) = M₀.μ := by
    have : (cD (t * t) : G1 F → G1 F) = (fun g => g * mD t) ∘ (fun g => (mD t)⁻¹ * g) := by
      funext g; exact M.cD_sq t g
    rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _),
      map_mul_left_eq_self, map_mul_right_eq_self]
  have h3 : M₀.μ.map (cD (t * t)) = (c * c) • M₀.μ := by
    have : (cD (t * t) : G1 F → G1 F) = cD t ∘ cD t := by
      funext g; exact (M.cD_cD t t g).symm
    rw [this, ← Measure.map_map (hm t) (hm t), hc,
      Measure.map_smul c (hm t).aemeasurable, hc, smul_smul]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G1 F)
  have hpos : M₀.μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds M₀.μ hK1).ne'
  have hfin : M₀.μ K ≠ ∞ := hK.measure_lt_top.ne
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) * M₀.μ K = M₀.μ K := by
    have := congrArg (fun m : Measure (G1 F) => m K) (h3.symm.trans h2)
    simpa [ENNReal.smul_def] using this
  have h5 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := by
    have h6 : ((c * c : ℝ≥0) : ℝ≥0∞) * M₀.μ K = 1 * M₀.μ K := by rw [h4, one_mul]
    exact (ENNReal.mul_left_inj hpos hfin).1 h6
  have h7 : c * c = 1 := by exact_mod_cast h5
  have h8 : c = 1 := by
    have := (mul_self_eq_one_iff (a := (c : ℝ))).1 (by exact_mod_cast h7)
    rcases this with h | h
    · exact_mod_cast h
    · have := c.coe_nonneg; linarith
  refine ⟨hm t, ?_⟩
  rw [hc, h8, one_smul]
end
