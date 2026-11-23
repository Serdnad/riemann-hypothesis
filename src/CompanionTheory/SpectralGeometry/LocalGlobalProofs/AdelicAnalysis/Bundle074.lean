module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle055
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle073
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle051
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle021
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.finite_volume_induction_compact_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ (M' : ℕ), M' < M → ∀ J' : Matrix (Fin M') (Fin M') E, IsHermND σ J' → FinVol F E σ M' J') → ∀ t : F, t ≠ 0 → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω → cntI σ J μ 𝓕 {X | gramE σ J X = fun _ _ => algebraMap F E t} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SW.CountGen.finite_count | exact GlobalTheory.CompanionTheory.SW.CountGen.finite_count | (intros; apply GlobalTheory.CompanionTheory.SW.CountGen.finite_count <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.hyperbolic_fundamental_domain_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (μ : Measure (HA (AF F) σ (hypJ J))) (𝓕 : Set (HA (AF F) σ (hypJ J))), IsHaarH F E σ (M + 2) (hypJ J) μ → IsFDH F E σ (M + 2) (hypJ J) μ 𝓕 → ∃ (Y : Set ((Fin 1 → Fin (M + 2) → AF F ⊗[F] E) × (Fin 1 → Fin (M + 2) → AF F ⊗[F] E))) (Kc : ℝ≥0∞), IsCompact Y ∧ Kc < ⊤ ∧ (∀ p ∈ Y, hR (AF F) σ (hypJ J) (p.2 0) (p.1 0) = 1) ∧ ∀ Φ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → (∀ (l : E) y, l ≠ 0 → Φ ((inclR (F := F) (AF F) l : AF F ⊗[F] E) • y) = Φ y) → ∀ g : ℤ → ℝ≥0∞, (∀ (j : ℤ), ∀ p ∈ Y, Φ (((τ (Multiplicative.ofAdd (-(j : ℝ))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • p.1) ≤ g j) → ∀ L : Set (Fin 1 → Fin (M + 2) → E), L ⊆ {X : Fin 1 → Fin (M + 2) → E | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} → (∀ X ∈ L, ∀ X' ∈ L, ∀ l : E, X' = l • X → X' = X) → cntI σ _ μ 𝓕 L Φ ≤ Kc * ∑' j : ℤ, g j * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ)))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum | exact GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum | (intros; apply GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem mass_fibre_summable :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) → (∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤) ∧ Summable fun v => |(m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn T hT hdet d b lam hlam m hm
  refine ⟨?_, ?_⟩
  · intro v
    have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
    obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
    haveI := hTR
    haveI := hLC
    haveI := hSC
    haveI := hT2
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    haveI hW := hh.2.1 n M
    haveI hH := hh.2.2 n
    have hlf := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ (Fv F v) hloc n _ _ (m v) hW hH (hm v)
      (hermOf (Fv F v) σ T hT)).1
    exact (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b n M v).1.measure_lt_top
  · obtain ⟨C, hC⟩ := GlobalTheory.T.local_densities_bounded_almost_all F E σ hCM M J hJ n hn T hT hdet d b
    refine Summable.of_norm_bounded_eventually
      (g := fun v : HeightOneSpectrum (𝓞 F) => C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
      ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C) ?_
    filter_upwards [hC] with v hv
    have := hv (lam v) (hlam v) (m v) (hm v)
    rw [Real.norm_eq_abs, abs_abs]
    simpa [div_eq_mul_inv] using this

end GlobalTheory.CompanionTheory.SW
end
