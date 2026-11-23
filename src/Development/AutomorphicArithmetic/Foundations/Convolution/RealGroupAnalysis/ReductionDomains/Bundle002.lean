module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import GroundTheory.AutomorphicForms.RealIwasawaIntegration
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.sumSide :
    ∀ (X ι : Type) [MeasurableSpace X] [Countable ι] (m : Measure X) (e : ι → X → X), (∀ i, Measurable (e i)) → (∀ u : X → ℝ≥0∞, Measurable u → ∫⁻ x, u x ∂(Measure.sum fun i => m.map (e i)) = ∫⁻ x, ∑' i, u (e i x) ∂m) ∧ ∀ u : X → ℂ, Measurable u → Integrable u (Measure.sum fun i => m.map (e i)) → (∀ᵐ x ∂m, Summable fun i => ‖u (e i x)‖) ∧ Integrable (fun x => ∑' i, u (e i x)) m ∧ ∫ x, ∑' i, u (e i x) ∂m = ∫ x, u x ∂(Measure.sum fun i => m.map (e i)) := by
  intro X ι _ _ m e he
  have hL : ∀ u : X → ℝ≥0∞, Measurable u →
      ∫⁻ x, u x ∂(Measure.sum fun i => m.map (e i)) = ∫⁻ x, ∑' i, u (e i x) ∂m := by
    intro u hu
    have hm : ∀ i, AEMeasurable (fun x => u (e i x)) m := fun i => (hu.comp (he i)).aemeasurable
    rw [lintegral_sum_measure, lintegral_tsum hm]
    exact tsum_congr fun i => lintegral_map hu (he i)
  refine ⟨hL, fun u hu hint => ?_⟩
  have hum : Measurable fun x => ‖u x‖ₑ := hu.enorm
  have hfin : ∫⁻ x, ∑' i, ‖u (e i x)‖ₑ ∂m < ⊤ := by
    rw [← hL _ hum]
    exact hint.2
  have hmeas : Measurable fun x => ∑' i, ‖u (e i x)‖ₑ :=
    Measurable.tsum fun i => hum.comp (he i)
  have hsum : ∀ᵐ x ∂m, Summable fun i => ‖u (e i x)‖ := by
    filter_upwards [ae_lt_top hmeas hfin.ne] with x hx
    have h1 : ∑' i, ((‖u (e i x)‖₊ : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := hx.ne
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h1)
  have hsm : ∀ i, AEStronglyMeasurable (fun x => u (e i x)) m := fun i =>
    (hu.comp (he i)).aestronglyMeasurable
  have hlim : ∀ᵐ x ∂m, Tendsto (fun s : Finset ι => ∑ i ∈ s, u (e i x)) atTop
      (𝓝 (∑' i, u (e i x))) := by
    filter_upwards [hsum] with x hx
    exact hx.of_norm.hasSum
  have hae : AEStronglyMeasurable (fun x => ∑' i, u (e i x)) m :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s : Finset ι => Finset.aestronglyMeasurable_fun_sum s fun i _ => hsm i) hlim
  have hI : Integrable (fun x => ∑' i, u (e i x)) m := by
    refine ⟨hae, lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin⟩
    exact enorm_tsum_le_tsum_enorm
  refine ⟨hsum, hI, ?_⟩
  have hne : ∑' i, ∫⁻ x, ‖u (e i x)‖ₑ ∂m ≠ ⊤ := by
    have hm : ∀ i, AEMeasurable (fun x => ‖u (e i x)‖ₑ) m := fun i =>
      (hum.comp (he i)).aemeasurable
    rw [← lintegral_tsum hm]
    exact hfin.ne
  rw [integral_tsum hsm hne, integral_sum_measure hint]
  exact tsum_congr fun i => (integral_map (he i).aemeasurable hu.aestronglyMeasurable).symm
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.cptMeas :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G), IsCompact (K : Set G) → ∃ μK : Measure K, μK.IsHaarMeasure ∧ IsProbabilityMeasure μK ∧ (μK.map Subtype.val) (K : Set G)ᶜ = 0 ∧ (∀ k ∈ K, (μK.map Subtype.val).map (k * ·) = μK.map Subtype.val) ∧ ∀ k ∈ K, (μK.map Subtype.val).map (· * k) = μK.map Subtype.val := by
  intro G _ _ _ _ _ _ _ _ K hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hKm : MeasurableSet (K : Set G) := hK.isClosed.measurableSet
  have hval : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  let μ : Measure K := Measure.haarMeasure ⊤
  haveI hH : μ.IsHaarMeasure := inferInstance
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
    simpa using this
  haveI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  haveI : μ.IsMulRightInvariant := GroundTheory.Automorphic.isMulRightInvariant_of_compactSpace μ
  refine ⟨μ, hH, hprob, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hval hKm.compl]
    have : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x; simp
    simp [this]
  · intro k hk
    have hcomp : (fun x : G => k * x) ∘ (Subtype.val : K → G) = Subtype.val ∘ (fun x : K => (⟨k, hk⟩ : K) * x) := by
      ext x; simp
    rw [Measure.map_map (measurable_const_mul k) hval, hcomp,
      ← Measure.map_map hval (measurable_const_mul _), map_mul_left_eq_self]
  · intro k hk
    have hcomp : (fun x : G => x * k) ∘ (Subtype.val : K → G) = Subtype.val ∘ (fun x : K => x * (⟨k, hk⟩ : K)) := by
      ext x; simp
    rw [Measure.map_map (measurable_mul_const k) hval, hcomp,
      ← Measure.map_map hval (measurable_mul_const _), map_mul_right_eq_self]
end
