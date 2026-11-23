module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle095
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle078
import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle038
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle036
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OrderValuation
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.L2

theorem norm_complexEmbedding_traceElement_const (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

theorem petersson_squareIntegrable_definite_of_laws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  intro D H Dw l Xo c r U σ V hr ι Kf χ dict mu x₀ hs hσ hsup P
  obtain ⟨g, e, F, ik, φ, th, -, hd, -⟩ := P.dictLaws
  have hA : AdelAut V dict mu := P.adelAut
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hL : CuspL2 U σ V dict mu :=
    cusp_L2_of_measurable hσ (dict_dom_of hd) P.muUnit (adelMeas_of_aut Xo c hA)
  refine ⟨hV, fun k τ => ?_, hL, l2Def_of_cusp hσ hsup (aeDom_of hA hV hP P.muUnit hd) hL⟩
  exact (congrArg (fun z => ‖τ z‖) (P.modelW k).2).trans
    (by rw [map_neg, norm_neg]; exact norm_complexEmbedding_traceElement_const D τ)

end GlobalTheory.FinalJoin2.L2
end

section

noncomputable section

namespace GlobalTheory.TransferCompare

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.PjFree (valSet algCls cusp Unf regular₂ trivSet isVal_valSet DomWt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36 (algVal allVal ordVal Comb LeastLe Transfer TransferAt TransferInt TransferComb TransferLeast
  ordVal_smul)

section Order

end Order

section Approx

variable {K : Type} [Field K] [NumberField K]

end Approx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Objects

variable (Xo c)

variable {Xo c}

end Objects

section Joint

variable (Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, _root_.Formalism.L2.PjFree.Unf Xo c σ r)

variable {Xo c U}

variable (Xo c)

theorem evalWD_framed : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
  evalWD_fr (frChartF_of (GlobalTheory.T.chartCoverF_of_sectionBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c))

theorem frBC_framed : GlobalTheory.Reg.FrBC Xo c := fun S T _ _ _ _ φ y =>
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S T φ y

theorem allTest_framed : AllTest Xo c :=
  GlobalTheory.T.framedPoint_reduced_from_testRing GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c



variable (U)

end Joint

end GlobalTheory.TransferCompare
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.discreteSeriesCoeffSeries_of_kTypeProjections : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (x : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, IsKFin ε σ (x j)) ∧
        ∀ y ∈ UJset ε, (∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) = ∑ j, ℓ j (σ y (x j))) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.SmoothGlob.lieSet ε) (UJset ε) σ f := by
  first | exact @GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes | exact GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes | (intros; apply GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.eq_matrixCoeff_of_locallyUniform_limit_kFinite : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ h : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn h (UJset ε) → GlobalTheory.TypeSum.UMG ε h →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
        ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
          ∀ y ∈ C, y ∈ UJset ε → ‖h y - ∑ a, L a (σ y (w a))‖ < δ) →
    ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
      ∀ y ∈ UJset ε, h y = ∑ a, L a (σ y (w a)) := by
  first | exact @GlobalTheory.TypeSum.CoefClos.eq_coef_of_closure | exact GlobalTheory.TypeSum.CoefClos.eq_coef_of_closure | (intros; apply GlobalTheory.TypeSum.CoefClos.eq_coef_of_closure <;> assumption)
end
