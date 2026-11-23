module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicIntegralInvariantOpenSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarSplitsArchTimesFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle106
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralOrder
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralUnramified
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartCompactSupportContinuous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle456
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicLiftGivesHolomorphicSection
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core


theorem _root_.GlobalTheory.T.pairing_biadditive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
    (b : HermR (Af F) σ n),
    (∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b (X + X') Y =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X' Y) ∧
    (∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b X (Y + Y') =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X Y') := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd.pairB_add | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd.pairB_add | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd.pairB_add <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core


theorem _root_.GlobalTheory.T.phase_continuous_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n),
    Continuous (phaseB σ J (psiFin F ψ) b) ∧ (∀ X, ‖phaseB σ J (psiFin F ψ) b X‖ = 1) ∧
    ∀ X, Continuous (pairB σ J (psiFin F ψ) b X) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.phaseB_pairB_props | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.phaseB_pairB_props | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.phaseB_pairB_props <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ


theorem _root_.GlobalTheory.T.character_trace_pairing_eq_inner_psi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
  (b : HermR (AF F) σ n) (X : Fin n → Fin M → AF F ⊗[F] E),
  ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) =
    psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
        gramR (Ainf F) σ J (projInf X)))) *
    psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
      (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gramR (Af F) σ J (projFin X)))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.adelic_phase_split | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.adelic_phase_split | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.adelic_phase_split <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField


theorem _root_.GlobalTheory.T.finite_adelic_integral_invariant_open_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
    ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    ∃ U : AddSubgroup (HermR (Af F) σ n), IsOpen (U : Set (HermR (Af F) σ n)) ∧
      IsCompact (U : Set (HermR (Af F) σ n)) ∧
      ∀ b, ∀ u ∈ U, starLoc (Af F) σ J (psiFin F ψ) μ Q (b + u) = starLoc (Af F) σ J (psiFin F ψ) μ Q b := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Period.starLoc_periodic | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Period.starLoc_periodic | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Period.starLoc_periodic <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ


theorem _root_.GlobalTheory.T.hermitian_haar_splits_arch_times_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (n : ℕ) (db : Measure (HermR (AF F) σ n)), db.IsAddHaarMeasure →
  ∃ (ν₁ : Measure (HermR (Ainf F) σ n)) (ν₂ : Measure (HermR (Af F) σ n)) (c : ℝ≥0∞),
    ν₁.IsAddHaarMeasure ∧ ν₂.IsAddHaarMeasure ∧ SFinite ν₁ ∧ SFinite ν₂ ∧ c ≠ ⊤ ∧
    MeasurableEmbedding (fun b : HermR (AF F) σ n => (hermInf σ b, hermFin σ b)) ∧
    db.map (fun b => (hermInf σ b, hermFin σ b)) = c • ν₁.prod ν₂ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm.map_eq_smul_prod | exact GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm.map_eq_smul_prod | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm.map_eq_smul_prod <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass


theorem _root_.GlobalTheory.T.local_unit_scaling_norm_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (c : Fv F v ⊗[F] E) (t : Fv F v) (w : ℕ), IsUnit c → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = ((qv v : ℝ) ^ w)⁻¹ → (coordK (Fv F v) b lam).map (fun x => c * x) = (qv v ^ w) • coordK (Fv F v) b lam := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale.coordK_map_mul | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale.coordK_map_mul | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale.coordK_map_mul <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass


theorem _root_.GlobalTheory.T.quadratic_basis_integral_order : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (b₂ : Module.Basis (Fin 2) F E) (D : F), b₂ 0 = 1 → σ (b₂ 1) = -b₂ 1 → b₂ 1 * b₂ 1 = algebraMap F E D → ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (Fv F v) D) = 1 → Valued.v (algebraMap F (Fv F v) 2) = 1 → (∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈ v.adicCompletionIntegers F) → (∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈ v.adicCompletionIntegers F) → ∀ e : Fv F v, e ^ 2 = algebraMap F (Fv F v) D → ¬ IsField (Fv F v ⊗[F] E) ∧ ∃ c : ℕ × ℕ → Fv F v ⊗[F] E, (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧ (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧ ‖t‖ = ((qv v : ℝ) ^ (i.1 + i.2))⁻¹) ∧ (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧ (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j) := by
  first | exact @GlobalTheory.CompanionTheory.SW.SplitIdeals.split_content | exact GlobalTheory.CompanionTheory.SW.SplitIdeals.split_content | (intros; apply GlobalTheory.CompanionTheory.SW.SplitIdeals.split_content <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass


theorem _root_.GlobalTheory.T.quadratic_basis_integral_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (b₂ : Module.Basis (Fin 2) F E) (D : F), b₂ 0 = 1 → σ (b₂ 1) = -b₂ 1 → b₂ 1 * b₂ 1 = algebraMap F E D → ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (Fv F v) D) = 1 → Valued.v (algebraMap F (Fv F v) 2) = 1 → (∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈ v.adicCompletionIntegers F) → (∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈ v.adicCompletionIntegers F) → (¬ ∃ e : v.adicCompletionIntegers F, Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) < 1) → IsField (Fv F v ⊗[F] E) ∧ ∃ c : ℕ → Fv F v ⊗[F] E, (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧ (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧ ‖t‖ = ((qv v : ℝ) ^ (2 * i))⁻¹) ∧ (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧ (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j) := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadField.inert_content | exact GlobalTheory.CompanionTheory.SW.QuadField.inert_content | (intros; apply GlobalTheory.CompanionTheory.SW.QuadField.inert_content <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem _root_.GlobalTheory.T.chart_compact_support_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ), Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → Continuous (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ HasCompactSupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ ∀ p ∈ tsupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)), IsUnit (p.1 0 0) ∧ LinearIndependent (R ⊗[F] E) p.2.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart <;> assumption)
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix Topology

namespace GlobalTheory.CompanionTheory.CTFin.CapRes

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a b n : ℕ}

theorem map_emb₂ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (e : Fin a ⊕ Fin b ≃ Fin n)
    (g : GL (Fin a) R × GL (Fin b) R) :
    GeneralLinearGroup.map f (GlobalTheory.SmGL.emb₂ R e g) =
      GlobalTheory.SmGL.emb₂ S e (GeneralLinearGroup.map f g.1, GeneralLinearGroup.map f g.2) := by
  have val_emb₂ {c d : ℕ} (T : Type) [CommRing T] (ee : Fin c ⊕ Fin d ≃ Fin n)
      (g : GL (Fin c) T × GL (Fin d) T) :
      (GlobalTheory.SmGL.emb₂ T ee g).val =
        Matrix.reindex ee ee (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases ee.symm i with a | a <;> rcases ee.symm j with b | b <;> simp
  apply Units.ext
  ext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  change f ((GlobalTheory.SmGL.emb₂ R e g : Matrix _ _ R) (e p) (e q)) = (GlobalTheory.SmGL.emb₂ S e _ : Matrix _ _ S) (e p) (e q)
  rw [val_emb₂, val_emb₂]
  rcases p with p | p <;> rcases q with q | q <;> simp

theorem emb₂_swap {R : Type} [CommRing R] (e : Fin a ⊕ Fin b ≃ Fin n) (g₁ : GL (Fin a) R) (g₂ : GL (Fin b) R) :
    GlobalTheory.SmGL.emb₂ R ((Equiv.sumComm (Fin b) (Fin a)).trans e) (g₂, g₁) = GlobalTheory.SmGL.emb₂ R e (g₁, g₂) := by
  have val_emb₂ {c d : ℕ} (T : Type) [CommRing T] (ee : Fin c ⊕ Fin d ≃ Fin n)
      (g : GL (Fin c) T × GL (Fin d) T) :
      (GlobalTheory.SmGL.emb₂ T ee g).val =
        Matrix.reindex ee ee (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases ee.symm i with a | a <;> rcases ee.symm j with b | b <;> simp
  apply Units.ext
  rw [val_emb₂, val_emb₂]
  ext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  rcases p with p | p <;> rcases q with q | q <;> simp

theorem emb_infGL (e : Fin a ⊕ Fin b ≃ Fin n) (y : GL (Fin a) (Cinf E)) :
    GlobalTheory.SmGL.emb₂ (Ad E) e (infGL E a y, (1 : GL (Fin b) (Ad E))) =
      infGL E n (GlobalTheory.SmGL.emb₂ (Cinf E) e (y, 1)) := by
  refine ga_ext ?_ ?_
  · rw [pInf_infGL, map_emb₂]; simp
  · rw [pFin_infGL, map_emb₂, pFin_infGL, map_one]
    exact map_one _

def blockL (e : Fin a ⊕ Fin b ≃ Fin n) : Lie E a →L[ℝ] Lie E n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => toL (reindex e e (fromBlocks (Matrix.of x) 0 0 0))
      map_add' := fun x y => by
        funext p q
        obtain ⟨p, rfl⟩ := e.surjective p
        obtain ⟨q, rfl⟩ := e.surjective q
        rcases p with p | p <;> rcases q with q | q <;> simp
      map_smul' := fun c x => by
        funext p q
        obtain ⟨p, rfl⟩ := e.surjective p
        obtain ⟨q, rfl⟩ := e.surjective q
        rcases p with p | p <;> rcases q with q | q <;> simp }

theorem blockL_apply (e : Fin a ⊕ Fin b ≃ Fin n) (x : Lie E a) (p q : Fin a ⊕ Fin b) :
    blockL e x (e p) (e q) = fromBlocks (Matrix.of x) 0 0 0 p q := by
  simp [blockL]

def shift (e : Fin a ⊕ Fin b ≃ Fin n) (x : Lie E a) : Lie E n := (oneL E n - blockL e (oneL E a)) + blockL e x

theorem shift_one (e : Fin a ⊕ Fin b ≃ Fin n) : shift e (oneL E a) = oneL E n := by simp [shift]

theorem toL_emb (e : Fin a ⊕ Fin b ≃ Fin n) (y : GL (Fin a) (Cinf E)) :
    toL (GlobalTheory.SmGL.emb₂ (Cinf E) e (y, 1)).val = shift e (toL y.val) := by
  have val_emb₂ {c d : ℕ} (T : Type) [CommRing T] (ee : Fin c ⊕ Fin d ≃ Fin n)
      (g : GL (Fin c) T × GL (Fin d) T) :
      (GlobalTheory.SmGL.emb₂ T ee g).val =
        Matrix.reindex ee ee (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases ee.symm i with a | a <;> rcases ee.symm j with b | b <;> simp
  rw [val_emb₂]
  funext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  simp only [shift, Pi.add_apply, Pi.sub_apply, blockL_apply]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply]

theorem blockL_single (e : Fin a ⊕ Fin b ≃ Fin n) (i j : Fin a) (x : Cinf E) :
    blockL e (toL (Matrix.single i j x)) = toL (Matrix.single (e (.inl i)) (e (.inl j)) x) := by
  funext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  rw [blockL_apply]
  change fromBlocks (Matrix.single i j x) 0 0 0 p q = Matrix.single (e (.inl i)) (e (.inl j)) x (e p) (e q)
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.single_apply]

def iota (e : Fin a ⊕ Fin b ≃ Fin n) : GA E a →* GA E n :=
  (GlobalTheory.SmGL.emb₂ (Ad E) e).comp (MonoidHom.inl _ _)

theorem iota_apply (e : Fin a ⊕ Fin b ≃ Fin n) (m : GA E a) : iota e m = GlobalTheory.SmGL.emb₂ (Ad E) e (m, 1) := rfl

theorem chart_eq (e : Fin a ⊕ Fin b ≃ Fin n) {F : GA E n → ℂ} {G : GA E a → ℂ} (h : ∀ m, G m = F (iota e m))
    (m : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) : chart G m x = chart F (iota e m) (shift e x) := by
  obtain ⟨u, hu⟩ := id hx
  have e1 : x = toL u.val := hu.symm
  subst e1
  rw [chart_val, h, map_mul, ← toL_emb, chart_val, iota_apply e (infGL E a u), emb_infGL]

theorem lieD_eq (e : Fin a ⊕ Fin b ≃ Fin n) {F : GA E n → ℂ} (hF : F ∈ Sm E n) {G : GA E a → ℂ}
    (h : ∀ m, G m = F (iota e m)) (X : Lie E a) (m : GA E a) :
    lieD X G m = lieD (blockL e X) F (iota e m) := by
  have hd : HasFDerivAt (shift e) (blockL e : Lie E a →L[ℝ] Lie E n) (oneL E a) :=
    (blockL e).hasFDerivAt.const_add _
  have hc : HasFDerivAt (chart F (iota e m)) (fderiv ℝ (chart F (iota e m)) (oneL E n)) (shift e (oneL E a)) := by
    rw [shift_one]; exact (differentiableAt_chart hF _).hasFDerivAt
  have h2 := hc.comp (oneL E a) hd
  have h3 : chart G m =ᶠ[𝓝 (oneL E a)] chart F (iota e m) ∘ shift e := by
    filter_upwards [isOpen_invSet.mem_nhds (show oneL E a ∈ invSet E a from isUnit_one)] with x hx
    exact chart_eq e h m hx
  unfold lieD
  rw [h3.fderiv_eq, h2.fderiv]
  rfl

def relAlg (e : Fin a ⊕ Fin b ≃ Fin n) : Subalgebra ℂ (Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) where
  carrier := {p | ∀ (F : Sm E n) (G : Sm E a), (∀ m, G.1 m = F.1 (iota e m)) →
    ∀ m, (p.1 G).1 m = (p.2 F).1 (iota e m)}
  mul_mem' := fun hp hq F G h m => hp _ _ (hq F G h) m
  add_mem' := fun hp hq F G h m => congrArg₂ (· + ·) (hp F G h m) (hq F G h m)
  algebraMap_mem' := fun c F G h m => congrArg (c • ·) (h m)

theorem lie_mem (e : Fin a ⊕ Fin b ≃ Fin n) (X : Lie E a) :
    ((lie E a X, lie E n (blockL e X)) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e :=
  fun F _ h m => lieD_eq e F.2 h X m

theorem lieS_mem (e : Fin a ⊕ Fin b ≃ Fin n) (i j : Fin a) (x : Cinf E) :
    ((lieS E a i j x, lieS E n (e (.inl i)) (e (.inl j)) x) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈
      relAlg e := by
  have := lie_mem e (toL (Matrix.single i j x))
  rwa [blockL_single] at this

theorem Eop_mem (e : Fin a ⊕ Fin b ≃ Fin n) (τ : E →+* ℂ) (i j : Fin a) :
    ((Eop τ i j, Eop τ (e (.inl i)) (e (.inl j))) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e :=
  (relAlg e).smul_mem ((relAlg e).sub_mem (lieS_mem e i j _) ((relAlg e).smul_mem (lieS_mem e i j _) _)) _

theorem qdet_mem (e : Fin a ⊕ Fin b ≃ Fin n) (τ : E →+* ℂ) (v : ℂ) :
    ((Formalism.REAL.qdet (Eop τ) v, Formalism.REAL.qdet (fun i j : Fin a => Eop τ (e (.inl i)) (e (.inl j))) v) :
      Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e := by
  let P := Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)
  let Z : Fin a → Fin a → P := fun i j => (Eop τ i j, Eop τ (e (.inl i)) (e (.inl j)))
  have h1 := map_qdet (AlgHom.fst ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) Z v
  have h2 := map_qdet (AlgHom.snd ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) Z v
  have h3 : Formalism.REAL.qdet Z v ∈ relAlg e := by
    refine (relAlg e).sum_mem fun σ _ => (relAlg e).mul_mem (intCast_mem (relAlg e) _)
      ((relAlg e).list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine (relAlg e).add_mem ?_ (Eop_mem e τ _ _)
    split_ifs
    · exact (relAlg e).algebraMap_mem _
    · exact (relAlg e).zero_mem
  convert h3 using 1
  exact Prod.ext h1.symm h2.symm

theorem aeval_mem (e : Fin a ⊕ Fin b ≃ Fin n) {z : Module.End ℂ (Sm E a)} {z' : Module.End ℂ (Sm E n)}
    (hz : (z, z') ∈ relAlg e) (q : Polynomial ℂ) :
    (Polynomial.aeval z q, Polynomial.aeval z' q) ∈ relAlg e := by
  have h1 := Polynomial.aeval_algHom_apply (AlgHom.fst ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) (z, z') q
  have h2 := Polynomial.aeval_algHom_apply (AlgHom.snd ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) (z, z') q
  have h3 : Polynomial.aeval (z, z') q ∈ relAlg e := by
    rw [Polynomial.aeval_eq_sum_range]
    exact (relAlg e).sum_mem fun i _ => (relAlg e).smul_mem ((relAlg e).pow_mem hz i) _
  convert h3 using 1
  exact Prod.ext h1 h2

end GlobalTheory.CompanionTheory.CTFin.CapRes

namespace GlobalTheory.CompanionTheory.CTFin

open CapRes

theorem capelli_restrict : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (q : Polynomial ℂ) (F : Sm E (r + s)), (∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ m, (Polynomial.aeval (cap (a := r) τ u) q G).1 m = (Polynomial.aeval (capR r s τ u) q F).1 (lev (Ad E) r s (m, 1))) ∧ (∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ m, (Polynomial.aeval (cap (a := s) τ u) q G).1 m = (Polynomial.aeval (capS r s τ u) q F).1 (lev (Ad E) r s (1, m))) := by
  intro E _ _ _ r s τ u q F
  constructor
  · intro G h m
    exact aeval_mem (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (qdet_mem _ τ _) q F G h m
  · intro G h m
    have hι : ∀ m : GA E s, iota ((Equiv.sumComm (Fin s) (Fin r)).trans (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))) m =
        lev (Ad E) r s (1, m) := fun m => emb₂_swap _ _ _
    have := aeval_mem ((Equiv.sumComm (Fin s) (Fin r)).trans (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)))
      (qdet_mem _ τ (u + ((s : ℂ) - 1) / 2)) q F G (fun m => by rw [hι]; exact h m) m
    rw [hι] at this
    exact this

end GlobalTheory.CompanionTheory.CTFin

end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem _root_.GlobalTheory.T.complex_point_lifts_to_multicone : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀), ∃ z ∈ mcPts (ptIdeal (i (genericPoint X))), IsUnder (PtsOver.map i rfl _ y) z := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.exists_mem_mcPts_isUnder | exact GlobalTheory.CompanionTheory.MPDict.exists_mem_mcPts_isUnder | (intros; apply GlobalTheory.CompanionTheory.MPDict.exists_mem_mcPts_isUnder <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem _root_.GlobalTheory.T.holomorphic_lift_gives_holomorphic_section : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (O : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (s : (Fin D → ℂ) → GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀),
    IsOpen O → DifferentiableOn ℂ γ O → (∀ v ∈ O, IsUnder (PtsOver.map i rfl _ (s v)) (γ v)) →
    ContinuousOn s O ∧ ∀ (W : X.Opens) (f : Γ(X, W)),
      DifferentiableOn ℂ (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ s) (O ∩ s ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.Holo.holo | exact GlobalTheory.CompanionTheory.MixZ.Holo.holo | (intros; apply GlobalTheory.CompanionTheory.MixZ.Holo.holo <;> assumption)
end
