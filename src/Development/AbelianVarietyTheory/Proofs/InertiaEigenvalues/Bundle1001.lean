module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoefficientsIntegralCoreForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1000
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle810
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle844
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.SeriesTie GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaSeries_base_twisted_universal_rational : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RealPin Rl cG ρ → ρ.LevelOf D.nexp → D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK → RatHyp T Rl F κ v₀ O i j hV → RatRow YS v₀ hρ i j b := by
  first | exact @GlobalTheory.SeriesTie.RatAll.ratRow | exact GlobalTheory.SeriesTie.RatAll.ratRow | (intros; apply GlobalTheory.SeriesTie.RatAll.ratRow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.universal_series_coefficients_integral_core_forms : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → (D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h, Y.Z.ρ.IsDatum i j b s h 0 → ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (Y.Z.ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∀ hV : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j, ∃ la : HeightOneSpectrum (𝓞 X.core.Q.c.F), (∀ x : X.core.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, Y.Z.ρ.eO i b o = X.core.σ₀ x) ∧ ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (X.core.V ((j : ℕ) + 1) X.core.σ₀) → ℂ)), (∀ k, ψ k ∈ GlobalTheory.CoverRead.baseInt X.core ((j : ℕ) + 1) X.core.σ₀ (Formalism.L2.Pj.wtA (X.geo.κ j)) (X.geo.κ j).n {la}) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = FWT.castDict hV (∑ k, Y.Z.ρ.eO i b (o k) • ψ k) := by
  first | exact @GlobalTheory.XiIntSteps.xi_int_core_forms | exact GlobalTheory.XiIntSteps.xi_int_core_forms | (intros; apply GlobalTheory.XiIntSteps.xi_int_core_forms <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceClassSum

theorem classSum_conj_place : ∀ (D : D7) (X : RealSide D) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → ∀ ψ ψ' : Twist D Circle, ψ.Good → ψ'.Good → B.admitted ψ.Q →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j B ψ ψ' →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u → ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc → κ ≠ 0 →
  ∀ τ : ℂ ≃+* ℂ, FixBase X.core X.R.toRealDat j τ → FixDat B τ → ConjChar τ ψ ψ' → ∀ ω ω' : PairRep (Vc D j) (Wc D j), B.IsWeil ψ.chi ω → B.IsWeil ψ'.chi ω' →
  ∃ ζ : ℂ, IsRoot1 ζ ∧ ∀ (I : Type) [Fintype I] (rep : I → GA D (Vc D j)), (∀ a, rep a ∈ GfC (Vc D j)) → ∀ F F' : Amb D j,
    ConjAt (X.R.ioP j (PiTensorProduct.tprod ℂ u) ∘ₗ cc) κ τ F F' →
    ConjFun (X.geo.O j) (X.geo.κ j) τ ζ (κ • B.classSum ω ψ rep F) (κ • B.classSum ω' ψ' rep F') := by
  intro D X j B hB ψ ψ' hψ hψ' hadm hT u cc κ hu hc hκ τ hτ hfd hcc ω ω' hω hω'
  obtain ⟨T0', A', R', F', v₀', O', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, t, t', ht, ht'⟩ := hT
  obtain ⟨c', u', hc', hu', hio⟩ := h11 cc u hc hu
  obtain ⟨ζ, hζ, H⟩ := GlobalTheory.T.conjugate_thetaSeries_flatVectors_twistedWeil GlobalTheory.chartIndependence_unconditional D _ _ T0' A' X.core R' F' X.geo.κ v₀' O' (fun _ => 1) X.size
    h1 h2 h3 h4 h5 j h6 h7 c' hc' u' hu' B hB h8 τ (h9 τ hτ) hfd ω ω' ψ ψ' t t' hω hω' hψ hψ' hadm ht ht' hcc
  have hz : GlobalTheory.ConjSpan.RelConj (O' j) (X.geo.κ j) τ :=
    GlobalTheory.ConjRelation.expands_zero_conj D _ _ T0' A' X.core R' F' X.geo.κ v₀' h1 h3 j Unit _ (O' j) h6.2 τ hτ.core
  refine ⟨ζ, hζ, fun I _ rep hrep F F' hF => h10 _ _ _ _ ?_⟩
  have := GlobalTheory.ConjSpan.classSum_conj (R'.ioP j (PiTensorProduct.tprod ℂ u')) c' hz hκ hcc.1 H I rep hrep F F' fun h => by
    obtain ⟨x, x', hx, e, e'⟩ := hF h
    exact ⟨x, x', hx, e.trans (hio x).symm, e'.trans (hio _).symm⟩
  rwa [one_mul] at this

end GlobalTheory.PlaceClassSum
end
