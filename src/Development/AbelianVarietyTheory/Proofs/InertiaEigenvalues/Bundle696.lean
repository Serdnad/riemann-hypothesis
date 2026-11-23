module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import ReciprocityTheory.Automorphisms.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Formalism.GaloisCohomology.StatementLoc
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle673
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle412
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BlochKatoGeneratorBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle569
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle544
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle058
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle081
public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle674
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle671
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Formalism.AlgebraicWeights.IsAlgWeight
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.integralFrame_conj_unitaryIntegral_iff_GL_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ x, (p x ∈ Formalism.UG.KU σ n ↔ cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n)) := by
  first | exact @GlobalTheory.KUTransfer.ku_iff | exact GlobalTheory.KUTransfer.ku_iff | (intros; apply GlobalTheory.KUTransfer.ku_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inert_of_unramifiedIsometricInvolution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal ∧ ¬ IsSplitAt w ∧ q = Formalism.UG.qV (maximalRealSubfield L) v := by
  first | exact @GlobalTheory.InertOfUnramInv.inert_of_isUnramInv | exact GlobalTheory.InertOfUnramInv.inert_of_isUnramInv | (intros; apply GlobalTheory.InertOfUnramInv.inert_of_isUnramInv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_unitary_rational_matrix_of_first_presentation_point : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γQ : GQ L n), ∃ (γ : UA L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧ (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
  first | exact @GlobalTheory.RatPtsBridge.exists_ratGL | exact GlobalTheory.RatPtsBridge.exists_ratGL | (intros; apply GlobalTheory.RatPtsBridge.exists_ratGL <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

theorem _root_.GlobalTheory.T.ladicCharacter_restrict_cmField_eq_cyclotomicPow : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ν : Formalism.L2.Host.HChar E) (s : ℝ), ν.IsAbsPow s →
    ∀ ψ : Formalism.L2.Host.HChar (maximalRealSubfield E), compNorm E ψ = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ →
    ∀ (k : ℕ) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ), IsLAdicCharOf ι (ψ * quadChar E ^ k) μ →
    ∀ m : ℤ, (m : ℝ) = 2 * s → μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) = cycBar E Ω l ^ m := by
  first | exact @GlobalTheory.PolCharRes.restrict_eq_cycBar_pow | exact GlobalTheory.PolCharRes.restrict_eq_cycBar_pow | (intros; apply GlobalTheory.PolCharRes.restrict_eq_cycBar_pow <;> assumption)
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.localInertia_iff_mem_placeInertia : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      (i : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p)),
      (∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x)) →
      ∀ g : ↥(A.decompositionSubgroup F), i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A := by
  first | exact @GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | exact GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | (intros; apply GlobalTheory.DecInertia.inertiaK_iff_mem_Ine <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.exists_local_wach_functor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → FaithH AI → WachEx AI → ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) := by
  first | exact @GlobalTheory.HWL.Assembly.exists_wach | exact GlobalTheory.HWL.Assembly.exists_wach | (intros; apply GlobalTheory.HWL.Assembly.exists_wach <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoTied

theorem blochKatoDim_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    BlochKatoDim (P.PD K) ↥LL.1 := by
  intro l _ P AI hT K LL _
  refine GlobalTheory.blochKatoDim_of_bkADim_of_fontCore l P K LL ?_
    (GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI hT K)
    (GlobalTheory.LocalIntegers.good_integers l LL).1
  intro LL' _ _ _ O _ _ hO A hdr
  exact (GlobalTheory.SeqDim.h1f_finrank l P AI hT K LL' O hO A hdr).2

end GlobalTheory.BlochKatoTied
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.H1fGeneratorsAlt

section Eval

variable {G V LL : Type} [Field LL] [AddCommGroup V] [Module LL V]

theorem exists_finset_eval (W : Submodule LL (G → V)) [Module.Finite LL ↥W] :
    ∃ s : Finset G, ∀ c ∈ W, (∀ g ∈ s, c g = 0) → c = 0 := by
  classical
  let Ks : Finset G → Submodule LL (G → V) := fun s =>
    W ⊓ ⨅ g ∈ s, LinearMap.ker (LinearMap.proj (R := LL) (φ := fun _ : G => V) g)
  have hmem : ∀ s c, c ∈ Ks s ↔ c ∈ W ∧ ∀ g ∈ s, c g = 0 := by
    intro s c
    simp [Ks, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  obtain ⟨s, -, hs⟩ := (measure fun s => finrank LL ↥(Ks s)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨s, fun c hc h0 => ?_⟩
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, c g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hlt : Ks (insert g s) < Ks s := by
    refine lt_of_le_of_ne (fun x hx => ?_) fun heq => ?_
    · rw [hmem] at hx ⊢
      exact ⟨hx.1, fun g' hg' => hx.2 g' (Finset.mem_insert_of_mem hg')⟩
    · have h1 : c ∈ Ks s := (hmem s c).2 ⟨hc, h0⟩
      rw [← heq, hmem] at h1
      exact hg (h1.2 g (Finset.mem_insert_self g s))
  haveI : Module.Finite LL ↥(Ks s) := Submodule.finiteDimensional_of_le inf_le_left
  exact hs (insert g s) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem fg_of_le_of_values {O : Type} [CommRing O] [IsNoetherianRing O] [Algebra O LL] [Module O V]
    [IsScalarTower O LL V] (W : Submodule LL (G → V)) [Module.Finite LL ↥W]
    (T : Submodule O V) (hT : T.FG) (N : Submodule O (G → V)) (hNW : N ≤ W.restrictScalars O)
    (hNT : ∀ c ∈ N, ∀ g, c g ∈ T) : N.FG := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_eval W
  haveI : IsNoetherian O ↥T := isNoetherian_of_fg_of_noetherian T hT
  let φ : ↥N →ₗ[O] (↥s → ↥T) :=
    { toFun := fun c i => ⟨(c : G → V) i, hNT _ c.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro c c' h
    apply Subtype.ext
    rw [← sub_eq_zero]
    refine hs _ (W.sub_mem (hNW c.2) (hNW c'.2)) fun g hg => ?_
    have := congrArg (fun f => ((f ⟨g, hg⟩ : ↥T) : V)) h
    simpa [φ, sub_eq_zero] using this
  haveI : IsNoetherian O ↥N := isNoetherian_of_injective φ hφ
  exact Module.Finite.iff_fg.1 inferInstance

end Eval

section Cohomology

open GlobalTheory.H1fGeneratorBoundAlt GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}
    [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
    {O : Type} [CommRing O] [Algebra O LL] [IsDomain O] [IsDiscreteValuationRing O]
    [IsFractionRing O LL] [Module O V] [IsScalarTower O LL V]

theorem finite_Z1f_of_H1fV [FiniteDimensional LL V] (hρ : ∀ x, Continuous fun g => ρ g x)
    [Module.Finite LL (FiniteCohomology PD ρ)] : Module.Finite LL ↥(finiteCocycles PD ρ) := by
  have hle : B1 ρ ≤ finiteCocycles PD ρ := by
    rintro _ ⟨x, rfl⟩
    exact coboundary_mem_blochKatoCocycles PD hρ x
  haveI : Module.Finite LL ↥(B1 ρ) := LinearMap.finiteDimensional_range _
  haveI : Module.Finite LL ↥((B1 ρ).comap (finiteCocycles PD ρ).subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hle).symm
  haveI : IsNoetherian LL ↥(finiteCocycles PD ρ) :=
    isNoetherian_of_range_eq_ker ((B1 ρ).comap (finiteCocycles PD ρ).subtype).subtype
      (Submodule.mkQ _) (by rw [Submodule.range_subtype, Submodule.ker_mkQ])
  infer_instance

theorem finite_Z1fT_of (L : Lattice (O := O) ρ) [Module.Finite LL ↥(finiteCocycles PD ρ)] :
    Module.Finite O ↥(latticeFiniteCocycles PD L) :=
  Module.Finite.iff_fg.2 (fg_of_le_of_values (finiteCocycles PD ρ) L.T L.fg (latticeFiniteCocycles PD L) inf_le_right
    fun _ hc g => hc.1.2 g (Set.mem_univ g))

theorem exists_generators_H1fT' [FiniteDimensional LL V] (L : Lattice (O := O) ρ)
    (hρ : ∀ x, Continuous fun g => ρ g x) [Module.Finite LL (FiniteCohomology PD ρ)]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ m : ℕ, GeneratedByAtMost (latticeFiniteCohomology PD L) m ∧
      m + finrank LL ↥(H0V ρ) ≤ finrank LL (FiniteCohomology PD ρ) + h0ModResidueDim L ϖ := by
  classical
  haveI hI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  haveI := L.free
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  haveI := finite_Z1f_of_H1fV PD hρ
  haveI := finite_Z1fT_of PD L
  haveI : Module.IsTorsionFree O LL := inferInstance
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans LL
  haveI : Module.Free O ↥(latticeFiniteCocycles PD L) := inferInstance
  obtain ⟨m, z, hz, hm⟩ := _root_.GlobalTheory.H1fGeneratorBoundAlt.exists_generators (Ideal.span {ϖ}) (cobT PD L hρ)
  refine ⟨m, ⟨Finset.univ.image fun i => classT PD L (z i), ?_, ?_⟩, ?_⟩
  · have := congrArg (Submodule.map (classT PD L)) hz
    rw [Submodule.map_sup, ← ker_classT, Submodule.map_top, range_classT,
      (Submodule.map_le_iff_le_comap.2 le_rfl : (LinearMap.ker (classT PD L)).map (classT PD L) ≤ ⊥).antisymm bot_le,
      sup_bot_eq, Submodule.map_span, ← Set.range_comp] at this
    rw [← this, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  · simpa using Finset.card_image_le (s := Finset.univ) (f := fun i => classT PD L (z i))
  · haveI := finite_latMod L (Ideal.span {ϖ})
    have h1 := Submodule.finrank_mono (ker_redMap_le PD L hρ (Ideal.span {ϖ}))
    have h2 := finrank_bloch_kato_cocycles PD hρ
    have h3 := finrank_lattice L
    have h4 : finrank O ↥(latticeFiniteCocycles PD L) ≤ finrank LL ↥(finiteCocycles PD ρ) :=
      finrank_le_of_injective (W := ↥(finiteCocycles PD ρ))
        { toFun := fun c => ⟨c, c.2.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl } fun _ _ h =>
          Subtype.ext (congrArg (fun c : ↥(finiteCocycles PD ρ) => (c : G → V)) h)
    have h5 : finrank (O ⧸ Ideal.span {ϖ}) ↥(LinearMap.ker (redMap (Ideal.span {ϖ}) (cobT PD L hρ))) ≤
      h0ModResidueDim L ϖ := h1
    omega

end Cohomology

open GlobalTheory.H1fGeneratorBoundAlt GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions

theorem h1fT_generators : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ T : LocLat ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) T.ρ → ∃ s : Finset (LatticeCohomology T.L), Submodule.span O (s : Set (LatticeCohomology T.L)) = latticeFiniteCohomology (P.PD K) T.L ∧ s.card + finrank LL ↥(H0V T.ρ) ≤ finrank LL (FiniteCohomology (P.PD K) T.ρ) + finrank LL T.V := by
  intro l _ P AI hTied K LL _ _ _ O _ _ hO T hDR
  have hH1f := (GlobalTheory.SeqDim.h1f_finrank l P AI hTied K LL O hO (toGRep T) hDR).1
  obtain ⟨⟨hD, hDVR, hF⟩, -⟩ := hO
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V
  haveI : Module.Finite LL (FiniteCohomology (P.PD K) T.ρ) := hH1f
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, ⟨s, hs, hc⟩, hm⟩ := exists_generators_H1fT' (P.PD K) T.L T.cont hϖ
  have h5 := h0_mod_uniformizer_le_rank T.L hϖ
  have h3 := finrank_lattice T.L
  exact ⟨s, hs, by omega⟩

end GlobalTheory.H1fGeneratorsAlt
end
end

section

noncomputable section

namespace GlobalTheory.TwistRepCrys

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_fildR_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ' τ a) := by
  rw [GlobalTheory.HTW.FildR_eq_comap PD ρ ρ' e.toLinearMap e.injective he τ a]
  exact (LinearEquiv.ofSubmodule'
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)) (FildR PD ρ' τ a)).finrank_eq

theorem multV_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = multV PD ρ' τ a := by
  rw [multV, multV, finrank_fildR_of_equiv PD e he, finrank_fildR_of_equiv PD e he]

theorem multV_of_le_one (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL (DdRE PD ρ τ)] (h1 : finrank LL (DdRE PD ρ τ) ≤ 1) {b : ℤ}
    (hb : IsJumpV PD ρ τ b) (a : ℤ) : multV PD ρ τ a = if a = b then 1 else 0 := by
  haveI : ∀ a, FiniteDimensional LL (FildR PD ρ τ a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := DdRE PD ρ τ) inf_le_left
  have anti : Antitone (FildR PD ρ τ) := fun a a' haa =>
    inf_le_inf_left _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD haa)
  have mono : ∀ a a', a ≤ a' → finrank LL (FildR PD ρ τ a') ≤ finrank LL (FildR PD ρ τ a) :=
    fun a a' h => Submodule.finrank_mono (anti h)
  have le1 : ∀ a, finrank LL (FildR PD ρ τ a) ≤ 1 := fun a =>
    (Submodule.finrank_mono (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ)).trans h1
  have lt : finrank LL (FildR PD ρ τ (b + 1)) < finrank LL (FildR PD ρ τ b) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (anti (by omega)) hb)
  have := le1 a
  have := le1 b
  rw [multV]
  rcases lt_trichotomy a b with h | h | h
  · have := mono (a + 1) b (by omega)
    have := mono a (a + 1) (by omega)
    rw [if_neg h.ne]
    omega
  · subst h
    rw [if_pos rfl]
    omega
  · have := mono (b + 1) a (by omega)
    have := mono a (a + 1) (by omega)
    rw [if_neg h.ne']
    omega

def transport (e : V ≃ₗ[LL] V') (ρ' : Representation LL G V') : Representation LL G V where
  toFun g := e.symm.toLinearMap ∘ₗ ρ' g ∘ₗ e.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [Module Qp V] [IsScalarTower Qp LL V] [Module Qp V'] [IsScalarTower Qp LL V'] in
theorem transport_apply (e : V ≃ₗ[LL] V') (ρ' : Representation LL G V') (g : G) (x : V) :
    e (transport e ρ' g x) = ρ' g (e x) := by
  simp [transport]

end Generic

theorem isCrys_and_multV_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (χ : ↥(GK K) →* (↥LL.1)ˣ), IsTwistRep χ ρ ρ' → IsCrys (P.PD K) (charRep χ) → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a b : ℤ), IsJumpV (P.PD K) (charRep χ) τ b → multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' χ ⟨e, he⟩ cχ cρ
  let f : (Fin 1 → ↥LL.1) ≃ₗ[↥LL.1] ↥LL.1 := LinearEquiv.funUnique (Fin 1) ↥LL.1 ↥LL.1
  let ν := transport f (charRep χ)
  have hν : ∀ g x, ν g x = ((χ g : (↥LL.1)ˣ) : ↥LL.1) • x := fun g x => by
    apply f.injective
    rw [transport_apply, map_smul]
    rfl
  have hρ : ∀ g x, transport e ρ' g x = ((χ g : (↥LL.1)ˣ) : ↥LL.1) • ρ g x := fun g x => by
    apply e.injective
    rw [transport_apply, he, map_smul]
  have cν : IsCrys (P.PD K) ν :=
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K) f.symm (fun g x => by
      apply f.injective
      rw [transport_apply, f.apply_symm_apply, f.apply_symm_apply]) cχ
  refine ⟨GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K) e (transport_apply e ρ')
    ((GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T K LL V ρ _ ν _ hν hρ cν).1 cρ),
    fun τ a b hb => ?_⟩
  obtain ⟨hfin, hle, -⟩ := (GlobalTheory.T.deRhamComponents_crystallineLetters_finrank l P AI T K LL ↥LL.1 (charRep χ)).1 τ
  rw [finrank_self] at hle
  rw [← multV_of_equiv (P.PD K) e (transport_apply e ρ')]
  refine GlobalTheory.TwistJump.multV_twist_char l P AI T K LL V ρ _ ν _ hν hρ
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL _ ν cν).1 τ b (fun c => ?_) a
  rw [multV_of_equiv (P.PD K) f (transport_apply f (charRep χ))]
  exact multV_of_le_one (P.PD K) (charRep χ) τ hle hb c

end GlobalTheory.TwistRepCrys
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_H1f_de_rham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) A.ρ → Module.Finite LL (FiniteCohomology (P.PD K) A.ρ) ∧ (finrank LL (FiniteCohomology (P.PD K) A.ρ) : ℤ) = finrank LL ↥(H0V A.ρ) + ((finrank LL ↥(DdR (P.PD K) A.ρ) : ℤ) - finrank LL ↥(DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := LL) (V := A.V) 0)) := by
  first | exact @GlobalTheory.SeqDim.h1f_finrank | exact GlobalTheory.SeqDim.h1f_finrank | (intros; apply GlobalTheory.SeqDim.h1f_finrank <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.crystallineLattice_basis_span_invariants : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i := by
  first | exact @GlobalTheory.CrisCoord.lattice_basis_span_invariants | exact GlobalTheory.CrisCoord.lattice_basis_span_invariants | (intros; apply GlobalTheory.CrisCoord.lattice_basis_span_invariants <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hecke_representatives_split_place_smaller_level : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → ∀ (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ), (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1)) → i.2 ≤ V.rank → ∀ (x : Bridge.Gf V) (A : Finset (Bridge.Gf V)), isTEnv V pl ok i x → (∀ a ∈ A, isLocEnv V pl ok i a) → Bridge.IsDC (levEnv V β L).J x A → Bridge.IsDC (levEnv V β { L with Q := Q', xq := xq }).J x A := by
  first | exact @GlobalTheory.SmallerLevelHecke.isDC_smaller_level | exact GlobalTheory.SmallerLevelHecke.isDC_smaller_level | (intros; apply GlobalTheory.SmallerLevelHecke.isDC_smaller_level <;> assumption)
end
