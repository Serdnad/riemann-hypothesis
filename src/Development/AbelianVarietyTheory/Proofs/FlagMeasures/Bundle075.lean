module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle064
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.existsUnique_prod_fundamentalDomain_of_extension : ∀ {V₁ V₂ : Type} [AddCommGroup V₁] [AddCommGroup V₂] (Λ : AddSubgroup (V₁ × V₂)) (D₁ : Set V₁) (D₂ : Set V₂), (∀ a : V₁, ∃! l, l ∈ {a : V₁ | (a, (0 : V₂)) ∈ Λ} ∧ a + l ∈ D₁) → (∀ b : V₂, ∃! l, l ∈ {b : V₂ | ∃ a : V₁, (a, b) ∈ Λ} ∧ b + l ∈ D₂) → ∀ v : V₁ × V₂, ∃! l, l ∈ Λ ∧ v + l ∈ D₁ ×ˢ D₂ := by
  first | exact @GlobalTheory.prod_fundamentalDomain_of_extension | exact GlobalTheory.prod_fundamentalDomain_of_extension | (intros; apply GlobalTheory.prod_fundamentalDomain_of_extension <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving : ∀ (K : Type) [Field K] [NumberField K] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W) (e : mixedEmbedding.mixedSpace K ≃L[ℝ] W), MeasurePreserving e volume μ → ∀ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ W), (Submodule.span ℤ (Set.range b) : Set W) = (fun x : K => e (mixedEmbedding K x)) '' {x : K | x ∈ (J : FractionalIdeal (𝓞 K)⁰ K)} ∧ μ (ZSpan.fundamentalDomain b) = ENNReal.ofReal (FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) * (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) := by
  first | exact @GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport | exact GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport | (intros; apply GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.covolumeQuotient_ofReal_identity : ∀ (d c : ℝ) (f t : ℕ) (m : ℝ≥0∞), 1 ≤ d → 0 < c → ENNReal.ofReal (((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2)) = ENNReal.ofReal ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) * m → ENNReal.ofReal ((2 * c) ^ f) * m = ENNReal.ofReal (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by
  first | exact @GlobalTheory.covolQuotient_arith | exact GlobalTheory.covolQuotient_arith | (intros; apply GlobalTheory.covolQuotient_arith <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.exists_fundamentalDomain_snd_of_two_smul_mem' : ∀ {ι : Type} [Fintype ι] (Λ : Submodule ℤ ((ι → ℝ) × (ι → ℝ))) [DiscreteTopology Λ], Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) = ⊤ → (∀ a b, (a, b) ∈ Λ → ((0 : ι → ℝ), (2 : ℝ) • b) ∈ Λ) → ∃ D : Set (ι → ℝ), MeasurableSet D ∧ ∀ y, ∃! l, l ∈ {b : ι → ℝ | ∃ a, (a, b) ∈ Λ} ∧ y + l ∈ D := by
  first | exact @GlobalTheory.exists_fundamentalDomain_snd_of_two_smul_mem | exact GlobalTheory.exists_fundamentalDomain_snd_of_two_smul_mem | (intros; apply GlobalTheory.exists_fundamentalDomain_snd_of_two_smul_mem <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.addFundamentalDomain_measure_eq_of_countable : ∀ {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (L : Submodule ℤ V) [Countable L] (D D' : Set V), MeasurableSet D → MeasurableSet D' → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D') → μ D = μ D' := by
  first | exact @GlobalTheory.addFundamentalDomains_measure_eq | exact GlobalTheory.addFundamentalDomains_measure_eq | (intros; apply GlobalTheory.addFundamentalDomains_measure_eq <;> assumption)
end
