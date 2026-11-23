module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle058
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle061
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle054
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle063
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterOrthogonalIsRational
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
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle053

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.local_annihilator_self_dual_volume : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (c : ℝ≥0), GlobalTheory.CompanionTheory.SW.IsStdV v lam → SelfDual (c • lam) (fun s t => psiV F ψ v (s * t)) → ∀ U : AddSubgroup (Fv F v), IsCompact (U : Set (Fv F v)) → IsOpen (U : Set (Fv F v)) → annV ψ v (annV ψ v U) = U ∧ IsCompact (annV ψ v U) ∧ IsOpen (annV ψ v U) ∧ (c : ℝ) ^ 2 * (lam U).toReal * (lam (annV ψ v U)).toReal = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.localDual | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.localDual | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.localDual <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.mem_annihilator_small_ball_eventually : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v), ∀ᶠ k : ℕ in Filter.atTop, t ∈ annV ψ v (GlobalTheory.CompanionTheory.SW.PiV.ball v (-(k : ℤ)) : Set (Fv F v)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.eventually_mem_annV_ball | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.eventually_mem_annV_ball | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.eventually_mem_annV_ball <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.adelic_integral_product_subgroup : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (db : Measure (AF F)) (laminf : Measure (Ainf F)) (lf : Measure (Af F)), laminf.IsAddHaarMeasure → lf.IsAddHaarMeasure → ∀ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) → MeasurePreserving e (laminf.prod lf) db → ∀ (g : Ainf F → ℂ) (B : AddSubgroup (Af F)), MeasurableSet (B : Set (Af F)) → lf (B : Set (Af F)) ≠ ⊤ → ∀ b : AF F, ∫ y, (g (fstA F y) * (B : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F y)) * ψ (y * b) ∂db = (∫ x, g x * psiInf F ψ (x * fstA F b) ∂laminf) * ((lf (B : Set (Af F))).toReal : ℂ) * (annF ψ (B : Set (Af F))).indicator (fun _ => (1 : ℂ)) (sndA F b) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.integral_pure_indicator_char | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.integral_pure_indicator_char | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.integral_pure_indicator_char <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.number_field_approximate_identity : (∀ (P : Type) [Fintype P] (a : P → ℝ), (∀ w, a w ≠ 0) → ∃ g : ℕ → (P → ℝ) → ℝ, (∀ k, Continuous (g k) ∧ HasCompactSupport (g k) ∧ (∀ x, 0 ≤ g k x) ∧ 0 < ∫ x, g k x) ∧ (∀ k, tsupport (g k) ⊆ Metric.closedBall 0 (1 / ((k : ℝ) + 1))) ∧ ∀ k, Integrable (fun t : P → ℝ => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ)))) → ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∃ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧ ∀ k, Integrable (fouInf ψ laminf (ρ k)) laminf := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx.exists_bumps_inf | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx.exists_bumps_inf | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx.exists_bumps_inf <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.archimedean_fourier_approximate_identity : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∀ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets → ∀ t : Ainf F, Filter.Tendsto (fun k => fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) Filter.atTop (nhds 1) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim.tendsto_fouInf_div_integral | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim.tendsto_fouInf_div_integral | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim.tendsto_fouInf_div_integral <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.adelic_character_trivial_almost_everywhere : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) → (∀ v ∈ T, c v = 0) → psiF ψ c = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.psiF_eq_one_of_int_of_vanish | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.psiF_eq_one_of_int_of_vanish | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.psiF_eq_one_of_int_of_vanish <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix


theorem _root_.GlobalTheory.T.adelic_character_orthogonal_is_rational : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ x : AF F, (∀ t : F, ψ (algebraMap F (AF F) t * x) = 1) → ∃ c : F, x = algebraMap F (AF F) c := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq <;> assumption)
end
