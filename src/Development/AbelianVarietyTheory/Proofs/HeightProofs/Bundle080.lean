module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle069
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finVol_and_exists_L2DefiniteCuspForms_of_pkgLaws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  first | exact @GlobalTheory.FinalJoin2.L2.petersson_squareIntegrable_definite_of_laws | exact GlobalTheory.FinalJoin2.L2.petersson_squareIntegrable_definite_of_laws | (intros; apply GlobalTheory.FinalJoin2.L2.petersson_squareIntegrable_definite_of_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClosureSeries

open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum

theorem hasTypeAll_of_closure : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsDS ε lam σ → ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.TypeSum.lieOf (Formalism.REAL.Jm ε)) (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ f := by
  intro hHC hCW n ε lam _ H _ _ σ hDS f hf hU happ
  haveI : CompleteSpace H := hDS.1
  have hstd : Std ε σ := std_of_isDS hHC hDS
  refine GlobalTheory.T.discreteSeriesCoeffSeries_of_kTypeProjections hHC hCW n ε H σ hstd f hf hU ?_
  intro e he hK
  obtain ⟨hc, hu⟩ := GlobalTheory.T.compactAverage_continuousOn_uniformModerateGrowth n ε f hf hU e he
  obtain ⟨d, w, hw, hap⟩ := GlobalTheory.T.kProjection_limit_discreteSeriesCoeffs n ε H σ hstd f hf happ e he hK
  obtain ⟨L, hL, heq⟩ := GlobalTheory.T.eq_matrixCoeff_of_locallyUniform_limit_kFinite hHC hCW n ε H σ hstd d w hw _ hc hu hap
  exact ⟨d, L, w, hL, hw, heq⟩

end GlobalTheory.ClosureSeries
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_compactFamily_average : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ), Continuous κ → (∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → ∀ e : K → ℂ, Continuous e → ∀ φ : GA D V → ℂ, IsAutFunSm θ V φ → IsAutFunSm θ V (fun x => ∫ k, e k * φ (x * atTau θ V τ (κ k)) ∂μ) := by
  first | exact @GlobalTheory.RealAverage.isAutFunSm_average | exact GlobalTheory.RealAverage.isAutFunSm_average | (intros; apply GlobalTheory.RealAverage.isAutFunSm_average <;> assumption)
end
