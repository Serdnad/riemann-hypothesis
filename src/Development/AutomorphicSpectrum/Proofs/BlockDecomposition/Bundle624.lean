module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle054
import Formalism.LocalRingCardinality.DataHost
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import GroundTheory.AutomorphicForms.Bundle012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle615
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSemisimpleFlagStabilizer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepConeWeightRatioBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle614
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductMeasureCovolumeOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle618
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002

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

noncomputable section
namespace GlobalTheory.CompanionTheory.EllTrace
open GlobalTheory.TruncKer

theorem countable_GF {D : D7} (V : HSp D) : Countable (GF V) := by
  haveI : Countable D.host.E :=
    (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
    (show Countable (Fin V.rank → Fin V.rank → D.host.E) from inferInstance)
  haveI : Countable (GL (Fin V.rank) D.host.E) := Units.val_injective.countable
  infer_instance

theorem kernel_diag_hasSum {D : D7} (V : HSp D) {f : GA D V → ℂ} (hf : f ∈ CcGA V) (x : GA D V) :
    (Function.support fun δ : GF V => f (x⁻¹ * rat V δ * x)).Finite ∧
    HasSum (fun δ : GF V => f (x⁻¹ * rat V δ * x)) (GlobalTheory.AutomorphicL2Unitary.kernel (GQ V) f x x) := by
  have hcs := continuous_of_mem_ccAd hf
  have hr : (ratEmb D.sp.cm.sig V.gram).range = GQ V := by rw [range_ratEmb]; rfl
  let e : GF V ≃* GQ V :=
    (MonoidHom.ofInjective (ratEmb_injective D.sp.cm.sig V.gram)).trans (MulEquiv.subgroupCongr hr)
  have he : ∀ δ : GF V, ((e δ : GQ V) : GA D V) = rat V δ := fun δ => rfl
  refine ⟨?_, ?_⟩
  · have hC : IsCompact ((fun g : GA D V => x * g * x⁻¹) '' tsupport f) :=
      hcs.2.isCompact.image (by fun_prop)
    have hfin := finite_mem_compact (Γ := GQ V) hC
    refine (hfin.preimage e.injective.injOn).subset fun δ hδ => ?_
    refine ⟨x⁻¹ * rat V δ * x, subset_tsupport _ hδ, ?_⟩
    simp only [he]
    group
  · have := hasSum_kernel (Γ := GQ V) hcs.2 x x
    exact (e.toEquiv.hasSum_iff (f := fun γ : GQ V => f (x⁻¹ * (γ : GA D V) * x))).2 this

theorem charpoly_eq_of_isConj {D : D7} {V : HSp D} {a b : GF V} (h : IsConj a b) :
    a.1.1.charpoly = b.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  change a.1.1.charpoly = ((c.1 : GL _ _) * a.1 * (c.1)⁻¹ : GL _ _).1.charpoly
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end GlobalTheory.CompanionTheory.EllTrace
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.witt_frame_rank_le_witt_index : ∀ (D : D7) (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  first | exact @GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx | exact GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx | (intros; apply GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.regular_semisimple_flag_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (γ : GRat σ J), GlobalTheory.Orb.IsRegSS γ.1.1 → (∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, γ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0)) → ∃ g : GRat σ J, (∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, g.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0)) ∧ ∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, (g⁻¹ * γ * g).1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) ∧ (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, (g⁻¹ * γ * g).1.1 *ᵥ (fun a => Y a l) = Y *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) := by
  first | exact @GlobalTheory.CompanionTheory.LeviConj.conj_into_levi | exact GlobalTheory.CompanionTheory.LeviConj.conj_into_levi | (intros; apply GlobalTheory.CompanionTheory.LeviConj.conj_into_levi <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Phase

def flat (S : Type) [AddCommGroup S] [TopologicalSpace S] (n M : ℕ) :
    (Fin n → Fin M → S) ≃ₜ+ (Fin 1 → Fin (n * M) → S) where
  toFun X _ p := X (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  invFun Y a i := Y 0 (finProdFinEquiv (a, i))
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext a p
    rw [Subsingleton.elim a 0]
    exact congrArg (Y 0) (finProdFinEquiv.apply_symm_apply p)
  map_add' X Y := by
    funext a p
    rfl
  continuous_toFun := continuous_pi fun _ => continuous_pi fun p =>
    (continuous_apply _).comp (continuous_apply _)
  continuous_invFun := continuous_pi fun _ => continuous_pi fun _ =>
    (continuous_apply _).comp (continuous_apply _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem projInf_flat_symm {n M : ℕ} (Y : Fin 1 → Fin (n * M) → AF F ⊗[F] E) :
    projInf ((flat _ n M).symm Y) = (flat _ n M).symm (projInf Y) := rfl

theorem projFin_flat_symm {n M : ℕ} (Y : Fin 1 → Fin (n * M) → AF F ⊗[F] E) :
    projFin ((flat _ n M).symm Y) = (flat _ n M).symm (projFin Y) := rfl

theorem isSchwartzBruhat_flat {n M : ℕ} {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ}
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ) :
    GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Φ ∘ (flat _ n M).symm) := by
  obtain ⟨k, P, Q, hP, hQ, hs⟩ := hΦ
  refine ⟨k, fun i => P i ∘ (flat _ n M).symm, fun i => Q i ∘ (flat _ n M).symm, fun i => ?_,
    fun i => ⟨(hQ i).1.comp_continuous (flat _ n M).symm.continuous,
      (hQ i).2.comp_homeomorph (flat _ n M).symm.toHomeomorph⟩, fun Y => ?_⟩
  · obtain ⟨N, e, c1, c2, f, hf⟩ := hP i
    refine ⟨N, (flat (Ainf F ⊗[F] E) n M).symm.toAddEquiv.trans e, c1.comp (flat _ n M).symm.continuous,
      (flat _ n M).continuous.comp c2, f, fun X => ?_⟩
    exact hf _
  · simp only [Function.comp_apply, hs, projInf_flat_symm, projFin_flat_symm]

theorem continuous_integrable [NumberField E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {n M : ℕ}
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : dx.IsAddHaarMeasure)
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ} (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ) :
    Continuous Φ ∧ Integrable Φ dx := by
  obtain ⟨h1, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor n M
  haveI := hBor 1 (n * M)
  let e := flat (AF F ⊗[F] E) n M
  haveI : (dx.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map _ e.toAddEquiv.toAddMonoidHom e.continuous e.surjective
      e.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  obtain ⟨c, hi⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt.continuous_integrable_of_isSchwartzBruhat F E σ hCM (n * M)
    (dx.map e) inferInstance _ (isSchwartzBruhat_flat hΦ)
  have hcomp : (Φ ∘ e.symm) ∘ e = Φ := by
    funext X
    simp
  refine ⟨hcomp ▸ c.comp e.continuous, ?_⟩
  have := (e.toHomeomorph.measurableEmbedding.integrable_map_iff).1 hi
  rwa [show (Φ ∘ (flat _ n M).symm) ∘ e.toHomeomorph = Φ from hcomp] at this

theorem integrable_mul_phase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), dx.IsAddHaarMeasure →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ b : HermR (AF F) σ n, Integrable (fun X => Φ X * ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)))) dx := by
  intro F E _ _ _ _ _ σ hCM M J n ψ hψ dx hdx Φ hΦ b
  obtain ⟨h1, -, -, -, -, htr, -, hBor, -, hgram⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor n M
  obtain ⟨hc, hi⟩ := continuous_integrable σ hCM dx hdx hΦ
  have hph : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E =>
      ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) := by
    refine hψ.1.comp (continuous_const.mul (htr.comp ?_))
    exact (continuous_const.matrix_mul (hgram n M J)).matrix_trace
  refine hi.mono (hc.mul hph).aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
  rw [norm_mul, hψ.2.1, mul_one]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Phase
end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.exists_witt_complement_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (Qi : Matrix (Idx r m) (Fin n) E), cT (σ : E →+* E) X * J * Z = 0 ∧ cT (σ : E →+* E) Y * J * Z = 0 ∧ Qi * frm X Z Y = 1 ∧ frm X Z Y * Qi = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CFin.exists_witt_basis | exact GlobalTheory.CompanionTheory.CFin.exists_witt_basis | (intros; apply GlobalTheory.CompanionTheory.CFin.exists_witt_basis <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.minimal_parabolic_archimedean_stabilizes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) (p : GAd σ J), p ∈ minParOne σ J X → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (j : Fin r), StabUpTo (X.map τ.1) (archMat σ J τ (projArch σ J w p)) j := by
  first | exact @GlobalTheory.CompanionTheory.CFin.stabUpTo_archMat_of_mem_minParOne | exact GlobalTheory.CompanionTheory.CFin.stabUpTo_archMat_of_mem_minParOne | (intros; apply GlobalTheory.CompanionTheory.CFin.stabUpTo_archMat_of_mem_minParOne <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.torus_archimedean_frame_conjugation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n r m : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (Z : Matrix (Fin n) (Fin m) E), cT (σ : E →+* E) X * J * Z = 0 → cT (σ : E →+* E) Y * J * Z = 0 → ∀ (t : Fin r → ℝ) (a : GAd σ J), IsTorusElt σ J X Y t a → ∀ (w : InfinitePlace F) (τ : EmbOver E w), archMat σ J τ (projArch σ J w a) * (frm X Z Y).map τ.1 = (frm X Z Y).map τ.1 * diagonal (fun u => ((wt m t u : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.CFin.torus_diag_witt | exact GlobalTheory.CompanionTheory.CFin.torus_diag_witt | (intros; apply GlobalTheory.CompanionTheory.CFin.torus_diag_witt <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.deep_cone_weight_ratio_bound : ∀ (r m : ℕ) (c t₁ : ℝ), 0 < c → 1 ≤ t₁ → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ cone r c, ∀ u v : Idx r m, lev m (deep t₁ t) u = lev m (deep t₁ t) v → wt m t u ≤ R * wt m t v := by
  first | exact @GlobalTheory.CompanionTheory.CFin.Ratio.ratio_bounded | exact GlobalTheory.CompanionTheory.CFin.Ratio.ratio_bounded | (intros; apply GlobalTheory.CompanionTheory.CFin.Ratio.ratio_bounded <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem _root_.GlobalTheory.T.lattice_stabilizer_volume_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ (m : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : HA (Fv F v) σ (hypOne J)), latStab σ (hypOne J) b v g → stageInt (Fv F v) σ J b lam m ((latV b v).indicator 1) g = m (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab.stageInt_latStab | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab.stageInt_latStab | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab.stageInt_latStab <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem _root_.GlobalTheory.T.euler_product_measure_covolume_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [DecidableEq (HeightOneSpectrum (𝓞 F))] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsEulerProd b dA 1 (coordW (Ainf F) b laminf 1 n) (fun v => coordW (Fv F v) b (lam v) 1 n) → ∀ (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₂ ⊆ S → ∀ (φinf : (Fin (n + 1) → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞) (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ G : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → (∀ g : HA (Ainf F) σ (hypOne J), Ψinf (actW (Ainf F) σ (hypOne J) g (e0 _ M)) = stageInt (Ainf F) σ J b laminf minf φinf g) → (∀ v, ∀ g : HA (Fv F v) σ (hypOne J), Ψ v (actW (Fv F v) σ (hypOne J) g (e0 _ M)) = stageInt (Fv F v) σ J b (lam v) (m v) (φ v) g) → (∀ v, ∀ g : HA (Fv F v) σ (hypOne J), G v (actW (Fv F v) σ (hypOne J) g (e0 _ M)) = stageInt (Fv F v) σ J b (lam v) (m v) ((latV b v).indicator 1) g) → ∀ h : HA (AF F) σ (hypOne J), ∃ Sh : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ Sh ∧ ∀ S', Sh ⊆ S' → ∫⁻ Y, ∫⁻ a, pureL b S φinf φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA ∂I = ENNReal.ofReal (∏' v : {v // v ∉ S'}, (m v.1 (latV b v.1)).toReal) * purePr σ J b S' Ψinf (fun v => if v ∈ S then Ψ v else G v) (actW (AF F) σ (hypOne J) h (e0 _ M)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Pure.inner_pure | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Pure.inner_pure | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Pure.inner_pure <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_compatible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ y₀, chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) ∂(m₁ (hermScal R σ (algebraMap F R t))) ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free | exact GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_lintegral_blockOne_eq_iterated : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S', ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF | exact GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF <;> assumption)
end
