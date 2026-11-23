module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle613
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle614
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle615
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.CompanionTheory.AutCover

open scoped Pointwise

theorem integrable_descend_of_cover : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (S : Set (GA D V)),
    MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, ∃ s ∈ S, g = γ * s) → ∀ φ : GA D V → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ →
      Measurable φ → IntegrableOn φ S μ → Integrable (descend (GQ V) φ) (autMeasure V μ) := by
  intro D V μ _ S hS hcov φ hinv hφ hint
  have hmeas : AEStronglyMeasurable (descend (GQ V) φ) (autMeasure V μ) :=
    (GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift).2 (by
      rw [hinv.lift_descend]
      exact hφ.aestronglyMeasurable)
  refine ⟨hmeas, ?_⟩
  have hfin : ∫⁻ g in S, ‖φ g‖ₑ ∂μ < ⊤ := hint.2
  have hmf : AEMeasurable (S.indicator fun g => ‖φ g‖ₑ) μ := (hφ.enorm.indicator hS).aemeasurable
  have key := GlobalTheory.AutomorphicL2Unitary.lintegral_eq_lintegral_tsum (Γ := GQ V) (μ := μ) hmf
  rw [lintegral_indicator hS] at key
  show ∫⁻ q, ‖descend (GQ V) φ q‖ₑ ∂(autMeasure V μ) < ⊤
  refine lt_of_le_of_lt ?_ hfin
  rw [key]
  apply lintegral_mono
  intro q
  obtain ⟨γ, hγ, s, hs, hq⟩ := hcov q.out
  have e : (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out = s := by
    show γ⁻¹ * q.out = s
    rw [hq, inv_mul_cancel_left]
  have hmem : (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out ∈ S := by
    rw [e]
    exact hs
  have h1 : S.indicator (fun g => ‖φ g‖ₑ) ((((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out) = ‖φ q.out‖ₑ := by
    rw [Set.indicator_of_mem hmem, hinv _ (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V)).2]
  show ‖φ q.out‖ₑ ≤ _
  rw [← h1]
  exact ENNReal.le_tsum (f := fun γ : GQ V => S.indicator (fun g => ‖φ g‖ₑ) ((γ : GA D V) * q.out)) _

end GlobalTheory.CompanionTheory.AutCover
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem archMat_projArch_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J) (w : InfinitePlace F) (τ : EmbOver E w), cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) * J.map τ.1 * archMat σ J τ (projArch σ J w g) = J.map τ.1 := by
  intro F E _ _ _ _ _ σ hcm n J g w τ
  have h := GlobalTheory.HeisCoords.archMat_unitary hcm τ (projArch σ J w g)
  have e : cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) = (archMat σ J τ (projArch σ J w g))ᴴ := by
    ext i j
    simp [cT, Matrix.conjTranspose_apply]
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CFin
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.archimedean_rational_embedding_map : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : GRat σ J) (w : InfinitePlace F) (τ : EmbOver E w), archMat σ J τ (projArch σ J w (ratEmb σ J γ)) = γ.1.1.map τ.1 := by
  first | exact @GlobalTheory.CompanionTheory.CFin.archMat_projArch_ratEmb | exact GlobalTheory.CompanionTheory.CFin.archMat_projArch_ratEmb | (intros; apply GlobalTheory.CompanionTheory.CFin.archMat_projArch_ratEmb <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.compact_archimedean_entries_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (GAd σ J)), IsCompact C → ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ C, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n), ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.CFin.archMat_entries_bounded_of_isCompact | exact GlobalTheory.CompanionTheory.CFin.archMat_entries_bounded_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.CFin.archMat_entries_bounded_of_isCompact <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT bc UJ)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ClassFin

section Reduction

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem projFin_ratEmb_val (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (γ : GRat σ J) :
    (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J γ)).1 = bc (inclR (Af F)) γ.1 := by
  refine Units.ext (Matrix.ext fun r s => ?_)
  change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (γ.1.1 r s)) =
    (1 : Af F) ⊗ₜ[F] (γ.1.1 r s)
  simp

end Reduction

section Lattices

open GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume Module
open scoped Pointwise

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

end Lattices

end GlobalTheory.CompanionTheory.ClassFin
end
end

section

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix MeasureTheory GlobalTheory.SmoothGlob

namespace GlobalTheory.CompanionTheory.SmoothClosed

theorem smoothVec_sub {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {u v : H}
    (hu : SmoothVec Lie σ u) (hv : SmoothVec Lie σ v) : SmoothVec Lie σ (u - v) := by
  intro k Xs hX
  simpa only [map_sub] using (hu k Xs hX).sub (hv k Xs hX)

theorem tendsto_seminorm_sub {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {q : Seminorm ℂ E} (hq : Continuous q) {u : ℕ → E} {y : E} (hu : Filter.Tendsto u Filter.atTop (nhds y)) :
    Filter.Tendsto (fun k => q (u k - y)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun k => u k - y) Filter.atTop (nhds (y - y)) := hu.sub_const y
  rw [sub_self] at h
  simpa [Function.comp_def, map_zero] using (hq.tendsto 0).comp h

theorem isClosed_image_of_sobolev_lower : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)), IsSmoothModRep ε p π dπ → ∀ T : H →ₗ[ℂ] E, IsSmoothGMap ε σ p π T → (∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → sobNorm σ S w ≤ q (T w)) → IsClosed (T '' {w | SmoothVec (lieSet ε) σ w}) := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hmod T hT hlow
  haveI : FirstCountableTopology E := hmod.withSeminorms.firstCountableTopology
  refine IsSeqClosed.isClosed ?_
  intro x y hx hxy
  choose w hw hTw using hx
  have hcauchy : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) →
      ∀ δ > 0, ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ := by
    intro S hS δ hδ
    obtain ⟨q, hq, hqb⟩ := hlow S hS
    have ht := tendsto_seminorm_sub hq hxy
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds (half_pos hδ)))
    refine ⟨K, fun k hk m hm => ?_⟩
    calc sobNorm σ S (w k - w m) ≤ q (T (w k - w m)) := hqb _ (smoothVec_sub (hw k) (hw m))
      _ = q ((x k - y) - (x m - y)) := by rw [T.map_sub, hTw, hTw, sub_sub_sub_cancel_right]
      _ ≤ q (x k - y) + q (x m - y) := map_sub_le_add q _ _
      _ < δ / 2 + δ / 2 := add_lt_add (hK k hk) (hK m hm)
      _ = δ := add_halves δ
  obtain ⟨w0, hw0, hconv⟩ := GlobalTheory.CompanionTheory.SobComplete.smoothVec_complete n ε H σ hU hI w hw hcauchy
  refine ⟨w0, hw0, ?_⟩
  obtain ⟨-, hT2⟩ := hT
  have hT' : Filter.Tendsto (fun k => T (w k)) Filter.atTop (nhds (T w0)) := by
    refine (hmod.withSeminorms.tendsto_nhds _ _).2 ?_
    intro i δ hδ
    obtain ⟨S, C, hS, hb⟩ := hT2 i
    have hC : Filter.Tendsto (fun k => C * sobNorm σ S (w k - w0)) Filter.atTop (nhds 0) := by
      simpa using (hconv S hS).const_mul C
    filter_upwards [hC.eventually (gt_mem_nhds hδ)] with k hk
    calc p i (T (w k) - T w0) = p i (T (w k - w0)) := by rw [T.map_sub]
      _ ≤ C * sobNorm σ S (w k - w0) := hb _ (smoothVec_sub (hw k) hw0)
      _ < δ := hk
  have hx' : Filter.Tendsto (fun k => T (w k)) Filter.atTop (nhds y) := by
    simp only [hTw]
    exact hxy
  exact tendsto_nhds_unique hT' hx'

end GlobalTheory.CompanionTheory.SmoothClosed

end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

theorem _root_.GlobalTheory.T.normalised_cusp_form_L2_bounded : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 ∧ ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised | exact GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised | (intros; apply GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD

theorem _root_.GlobalTheory.T.cuspidal_eq_twist_normalised : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (π : CuspSub E a), ∃ (π₀ : CuspSub E a) (χ : HChar E), IsNormalised π₀ ∧ π = π₀.twist χ := by
  first | exact @GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised | exact GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised | (intros; apply GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.LocalInvariant

theorem exists_bijective_isNormalised :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
      [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
      ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      ∃ f : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r),
        Function.Bijective f ∧ IsNormalised ζ A v f := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA
  obtain ⟨e⟩ := GlobalTheory.T.local_brauer_roots_unity_equiv F Ω l r hr A v hA
  by_cases hN : IsNormalised ζ A v (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  · exact ⟨e, e.bijective, hN⟩
  · simp only [IsNormalised, not_forall] at hN
    obtain ⟨ϖ, y, κ, χ, z, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hN
    have hgen := GlobalTheory.T.local_invariant_cup_uniformizer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
    set c : H2 (muLoc F l r A) := Submodule.Quotient.mk z with hc

    obtain ⟨a, ha⟩ : ∃ a : ZMod (l ^ r), a * e c = 1 := by
      have hmem : e.symm 1 ∈ Submodule.span (ZMod (l ^ r)) {c} := by
        rw [hgen]; trivial
      obtain ⟨a, hac⟩ := Submodule.mem_span_singleton.1 hmem
      refine ⟨a, ?_⟩
      have := congrArg e hac
      simpa using this
    have ha' : e c * a = 1 := by rw [mul_comm]; exact ha
    refine ⟨a • (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), ⟨?_, ?_⟩, ?_⟩
    · intro x x' hxx
      have hxx' : a * e x = a * e x' := by simpa using hxx
      apply e.injective
      calc e x = e c * (a * e x) := by rw [← mul_assoc, ha', one_mul]
        _ = e c * (a * e x') := by rw [hxx']
        _ = e x' := by rw [← mul_assoc, ha', one_mul]
    · intro t
      refine ⟨e.symm (e c * t), ?_⟩
      simp [← mul_assoc, ha]
    · intro ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      have hz := GlobalTheory.T.local_invariant_cup_kummer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
        ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      rw [← hz]
      simpa using ha

end GlobalTheory.CompanionTheory.LocalInvariant
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


theorem _root_.GlobalTheory.T.phase_cocycle_bimultiplicative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n)
    (X Y : Fin n → Fin M → Af F ⊗[F] E),
    phaseB σ J (psiFin F ψ) b (X + Y) =
      phaseB σ J (psiFin F ψ) b X * phaseB σ J (psiFin F ψ) b Y * pairB σ J (psiFin F ψ) b X Y := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd.phaseB_add | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd.phaseB_add | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd.phaseB_add <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_homeomorph_hermR_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), ∃ e : HermR R σ n ≃ₜ+ (Idx n d → R), ∀ S, e S = hCo R σ b S := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_continuousAddEquiv | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_continuousAddEquiv | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_continuousAddEquiv <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.hermitian_pairing_in_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ) (S T : HermR R σ n), pairHerm R σ n S T = dotProduct (hCo R σ b S) (((coordForm σ b n).map (algebraMap F R)).mulVec (hCo R σ b T)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord.pairHerm_eq_coordForm | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord.pairHerm_eq_coordForm | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord.pairHerm_eq_coordForm <;> assumption)
end
