module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle047
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

open scoped ContDiff

namespace GlobalTheory

theorem hasDerivAt_of_continuous_additive_to_mul (χ : ℝ → ℂ) (hc : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) (h0 : χ 0 = 1) :
    ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := by
  first
  | exact @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
  | exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
  | (apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add ..)

end GlobalTheory
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.schwartz_inner_product_continuous : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (w : SchwartzMap V ℂ), ∃ Λ : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      Λ u = @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (w x)) := by
  first | exact @GlobalTheory.schwartz_pairing_conj_clm | exact GlobalTheory.schwartz_pairing_conj_clm | (intros; apply GlobalTheory.schwartz_pairing_conj_clm <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.schwartz_pairing_continuous_functional : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (k : SchwartzMap V ℂ),
    ∃ L : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ, L u = ∫ x, u x * starRingEnd ℂ (k x) ∂μ := by
  first | exact @GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace | exact GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace | (intros; apply GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace <;> assumption)
end

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal


theorem _root_.GlobalTheory.T.schwartz_weighted_sobolev_bound_of_finrank_eq_zero : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], finrank ℝ E = 0 → ∀ (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  first | exact @GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero | exact GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero | (intros; apply GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero <;> assumption)
end

section

open scoped ContDiff


theorem _root_.GlobalTheory.T.schwartz_iteratedFDeriv_shift_le_inv_pow_of_norm_le : ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : SchwartzMap V ℂ) (a : V) (p : E →L[ℝ] V) (n M : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖ ≤ C * ((1 + ‖y‖) ^ M)⁻¹ := by
  first | exact @GlobalTheory.schwartz_shift_iteratedFDeriv_bound | exact GlobalTheory.schwartz_shift_iteratedFDeriv_bound | (intros; apply GlobalTheory.schwartz_shift_iteratedFDeriv_bound <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.translation_isometry_schwartz_operator : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (a : V) (f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      ∫ x, T f' x * starRingEnd ℂ (T g' x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ) →
    ∀ (χ ψ h : SchwartzMap V ℂ), HasCompactSupport (χ : V → ℂ) → ∀ M : ℕ, ∃ C : ℝ,
      ∀ (v : V) (k ψv : SchwartzMap V ℂ), (∀ x, k x = χ (x - v) * h x) → (∀ x, ψv x = ψ (x - v)) →
        ‖∫ x, T k x * starRingEnd ℂ (T ψv x) ∂μ‖ ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  first | exact @GlobalTheory.TransDecay.decay | exact GlobalTheory.TransDecay.decay | (intros; apply GlobalTheory.TransDecay.decay <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.schwartz_integral_superposition : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Type) [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [OpensMeasurableSpace P] (ν : Measure P)
    (Φ : P → SchwartzMap E ℂ), Continuous Φ → ∀ (c : P → ℂ), AEStronglyMeasurable c ν →
    (∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν) →
    ∀ (u : SchwartzMap E ℂ), (∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) →
    ∀ (Λ : SchwartzMap E ℂ →L[ℂ] ℂ), Λ u = ∫ ξ, c ξ * Λ (Φ ξ) ∂ν := by
  first | exact @GlobalTheory.schwartz_clm_integral_comm | exact GlobalTheory.schwartz_clm_integral_comm | (intros; apply GlobalTheory.schwartz_clm_integral_comm <;> assumption)
end

section

open FourierTransform MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.schwartz_density_transport_linearEquiv_chirp : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : V ≃L[ℝ] E) (Q : V →L[ℝ] V →L[ℝ] ℂ) (N : Submodule ℂ (SchwartzMap V ℂ)),
    (∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re) →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ N₂ : Submodule ℂ (SchwartzMap E ℂ),
      (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N₂) ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N₂) ∧
      (∀ (g : SchwartzMap V ℂ) (G : SchwartzMap E ℂ), (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
        (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N₂) ∧
      (Dense (N₂ : Set (SchwartzMap E ℂ)) → Dense (N : Set (SchwartzMap V ℂ))) := by
  first | exact @GlobalTheory.GaussTransport.transport | exact GlobalTheory.GaussTransport.transport | (intros; apply GlobalTheory.GaussTransport.transport <;> assumption)
end

section

open scoped SchwartzMap

theorem _root_.GlobalTheory.T.schwartz_seminorm_smulLeft_linear_phase_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → ∀ f : 𝓢(V, ℂ), SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f) ≤ C * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m f := by
  first | exact @GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le | exact GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le | (intros; apply GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le <;> assumption)
end

section

open MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.summable_schwartz_of_summable_seminorms : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℕ → SchwartzMap E ℂ),
    (∀ k n, Summable (fun j => SchwartzMap.seminorm ℂ k n (t j))) → Summable t := by
  first | exact @GlobalTheory.ConvSeries.summable_of_summable_seminorm | exact GlobalTheory.ConvSeries.summable_of_summable_seminorm | (intros; apply GlobalTheory.ConvSeries.summable_of_summable_seminorm <;> assumption)
end

section


theorem _root_.GlobalTheory.T.summable_schwartz_series : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {ι : Type}
    (u : ι → SchwartzMap V ℂ), (∀ k n : ℕ, Summable (fun i => SchwartzMap.seminorm ℂ k n (u i))) →
    ∃ F : SchwartzMap V ℂ, (∀ x, HasSum (fun i => u i x) (F x)) ∧
      ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, HasSum (fun i => T (u i)) (T F) := by
  first | exact @GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms | exact GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms | (intros; apply GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.real_compact_partition_unity : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    ∃ ψ : SchwartzMap V ℂ, HasCompactSupport (ψ : V → ℂ) ∧ (∀ x, starRingEnd ℂ (ψ x) = ψ x) ∧
      ∃ v : (Fin (Module.finrank ℝ V) → ℤ) → V, (∀ x, HasSum (fun j => ψ (x - v j)) 1) ∧
        (∀ R : ℝ, {j | ‖v j‖ ≤ R}.Finite) ∧ ∃ M : ℕ, Summable (fun j => ((1 + ‖v j‖) ^ M)⁻¹) := by
  first | exact @GlobalTheory.LatticePartition.exists_lattice_partition | exact GlobalTheory.LatticePartition.exists_lattice_partition | (intros; apply GlobalTheory.LatticePartition.exists_lattice_partition <;> assumption)
end
