module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import CompanionTheory.AutomorphicTheory.ThetaDilations.ActWSmul
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle069
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

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.small_box_gram_scalar_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (t : F) (Y : Fin 1 → Fin M → AF F ⊗[F] E), Y ∈ box b N r₀ → (gramR (AF F) σ J Y = fun _ _ => inclR (AF F) (algebraMap F E t)) → t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.SmallQ.small_length | exact GlobalTheory.CompanionTheory.SW.SmallQ.small_length | (intros; apply GlobalTheory.CompanionTheory.SW.SmallQ.small_length <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FNu

theorem exists_nu_siegel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∃ (P : Subgroup (HA (AF F) σ (hypJ J))) (ν : Measure (HA (AF F) σ (hypJ J))) (S : ℤ → Set (HA (AF F) σ (hypJ J))) (ω : Set (AF F ⊗[F] E)ˣ) (Kc : ℝ≥0∞), (∀ h, h ∈ P ↔ ∃ a : (AF F ⊗[F] E)ˣ, actW (AF F) σ _ h (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ SFinite ν ∧ (∀ p ∈ P, ν.map (fun g => p * g) = ν) ∧ (∀ U ∈ 𝓝 (1 : HA (AF F) σ (hypJ J)), ν U ≠ 0) ∧ IsCompact ω ∧ Kc < ⊤ ∧ (∀ j, MeasurableSet (S j)) ∧ (∀ j : ℤ, ν (S j) ≤ Kc * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ))))) ∧ (∀ j : ℤ, ∀ p ∈ S j, p ∈ P ∧ ∃ c ∈ ω, actW (AF F) σ _ p (eOne _ (M + 1)) = ((τ (Multiplicative.ofAdd (j : ℝ)) * c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ ∀ᵐ p ∂ν, ∃ γ ∈ P, HA.mat (AF F) σ (hypJ J) γ ∈ HFin (AF F) σ (hypJ J) ∧ ∃ j, γ * p ∈ S j :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.nu

end GlobalTheory.CompanionTheory.SW.FNu
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_orbit_compact_representative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : Fin n → Fin M → E), (gramE σ J X).det ≠ 0 → ∀ Ω : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact Ω → ∃ C : Set (HA (AF F) σ J), IsCompact C ∧ ∀ Y ∈ Ω, gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) → ∃ c ∈ C, actW (AF F) σ J c (ratTup (AF F) X) = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre | exact GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre | (intros; apply GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre <;> assumption)
end
