module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle041
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdmissibleSmoothRepresentations
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.UniformSpace.Uniformizable
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.CuspMult GlobalTheory.PRep
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDec

section Abstract

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem mem_fixed {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ H X} {K : Subgroup H} {x : X} :
    x ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k x = x := by
  simp [fixed, eig]

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ρ : Representation ℂ H V}

theorem isSemisimple (ha : IsAdmissible ρ) (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) {K₀ : Subgroup H}
    (ho : IsOpen (K₀ : Set H)) (hc : IsCompact (K₀ : Set H)) : ρ.IsSemisimpleRepresentation :=
  _root_.UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.isSemisimple ha hu ho hc

theorem mem_irrSum {W X : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ H W}
    {ρ : Representation ℂ H X} {C : Submodule ℂ X} (h1 : σ.IsSemisimpleRepresentation) (h2 : IsAdmissible σ)
    {f : W →ₗ[ℂ] X} (hf : f ∈ homInto σ ρ C) (s : W) : f s ∈ irrSum ρ C := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 h1
  have hs : σ.asModuleEquiv.symm s ∈ sSup {m : Submodule (MonoidAlgebra ℂ H) σ.asModule |
      IsSimpleModule (MonoidAlgebra ℂ H) m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]
    trivial
  rw [sSup_eq_iSup'] at hs
  refine Submodule.iSup_induction _ (motive := fun x => f (σ.asModuleEquiv x) ∈ irrSum ρ C) hs ?_ ?_ ?_
  · rintro ⟨m, hm⟩ y hy
    obtain ⟨U, rfl⟩ := Subrepresentation.subrepresentationSubmoduleOrderIso.surjective m
    have hU : U.toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      haveI : IsSimpleModule (MonoidAlgebra ℂ H) U.asSubmodule := hm
      exact IsSimpleModule.congr (GlobalTheory.RepCount.subEquiv U)
    exact GlobalTheory.RepCount.apply_mem_irrSum hU
      (GlobalTheory.RepCount.isAdmissible_of_injective U.toSubmodule.subtype (fun _ _ => rfl) Subtype.val_injective h2)
      (f := f.comp U.toSubmodule.subtype) ⟨fun s => hf.1 _, fun g s => hf.2 g s⟩ ⟨σ.asModuleEquiv y, hy⟩
  · simp
  · intro a b ha hb
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ ha hb

theorem isDecomp_of_form {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (hC : ∀ g, ∀ x ∈ C, ρ g x ∈ C) (B : X → X → ℂ)
    (hl : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z ∧ B y x = star (B x y))
    (hp : ∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) (hi : ∀ g, ∀ x ∈ C, ∀ y ∈ C, B (ρ g x) (ρ g y) = B x y)
    (hf : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ ↥(C ⊓ fixed ρ K))
    {K₀ : Subgroup H} (ho : IsOpen (K₀ : Set H)) (hc : IsCompact (K₀ : Set H)) : IsDecomp ρ C := by
  intro x hx hx'
  let A : Subrepresentation ρ := ⟨C ⊓ smoothPart ρ, fun g v hv => ⟨hC g v hv.1, smoothPart_stable ρ g v hv.2⟩⟩
  have hsym : ∀ x ∈ C, ∀ y ∈ C, B y x = star (B x y) := fun x hx y hy => (hl x hx y hy y hy 0).2
  have h0 : ∀ x ∈ C, B x 0 = 0 := fun x hx => by simpa using (hl x hx 0 C.zero_mem 0 C.zero_mem 1).1
  let cd : InnerProductSpace.Core ℂ A.toSubmodule :=
    { inner := fun a b => B a b
      conj_inner_symm := fun a b => (hsym _ b.2.1 _ a.2.1).symm
      re_inner_nonneg := fun a => by
        by_cases h : (a : X) = 0
        · simp [h, h0 0 C.zero_mem]
        · exact (hp _ a.2.1 h).le
      add_left := fun a b c => by
        have := (hl _ c.2.1 _ a.2.1 _ b.2.1 1).1
        rw [one_smul, one_mul] at this
        show B (a + b) c = B a c + B b c
        rw [hsym _ c.2.1 _ (C.add_mem a.2.1 b.2.1), this, star_add, hsym _ c.2.1 _ a.2.1, hsym _ c.2.1 _ b.2.1]
      smul_left := fun a b r => by
        have := (hl _ b.2.1 _ C.zero_mem _ a.2.1 r).1
        rw [zero_add, h0 _ b.2.1, zero_add] at this
        show B (r • a) b = star r * B a b
        rw [hsym _ b.2.1 _ (C.smul_mem r a.2.1), this, star_mul', hsym _ b.2.1 _ a.2.1]
      definite := fun a h => by
        by_contra hn
        have := hp _ a.2.1 fun e => hn (Subtype.ext e)
        rw [show B a a = 0 from h] at this
        simp at this }
  have ha : IsAdmissible A.toRepresentation := by
    refine ⟨fun v => ?_, fun K hK _ => ?_⟩
    · have : {g : H | A.toRepresentation g v = v} = {g : H | ρ g v = v} := by
        ext g
        exact Subtype.ext_iff
      rw [this]
      exact v.2.2
    · haveI := hf K hK
      refine FiniteDimensional.of_injective (A.toSubmodule.subtype.restrict (p := fixed A.toRepresentation K)
        (q := C ⊓ fixed ρ K) fun v hv => ⟨v.2.1, fun k => congrArg Subtype.val (hv k)⟩) fun a b h => ?_
      have h' : (a.1 : X) = b.1 := congrArg (fun z : ↥(C ⊓ fixed ρ K) => (z : X)) h
      exact Subtype.ext (Subtype.ext h')
  have hs : A.toRepresentation.IsSemisimpleRepresentation := by
    letI := cd.toNormedAddCommGroup
    letI := InnerProductSpace.ofCore cd.toCore
    exact isSemisimple ha (fun g a b => hi g _ a.2.1 _ b.2.1) ho hc
  exact mem_irrSum hs ha (f := A.toSubmodule.subtype) ⟨fun s => s.2.1, fun _ _ => rfl⟩ ⟨x, hx, hx'⟩

end Abstract

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : DSModel V S}

theorem finRep_mem (g : GfC V) (T : MMap M) (hT : T ∈ allMaps θ M) : finRep M g T ∈ allMaps θ M := by
  have e : finRep M g T = heckeOn M {(g : GA D V)} T := by
    ext v x
    simp [heckeOn, postOn_apply, heckeLin_apply, finRep_apply]
  rw [e]
  exact Submodule.subset_span (GlobalTheory.SphericalOps.isMultMap_single ((GlobalTheory.MultMem.mem_mult_iff ..).1 hT) g.2)

theorem isMultiplicityInner_finRep {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (g : GfC V) {T T' : MMap M} (hT : T ∈ allMaps θ M) (hT' : T' ∈ allMaps θ M)
    {c : ℂ} (h : IsMultIP M μ 𝓕 T T' c) : IsMultIP M μ 𝓕 (finRep M g T) (finRep M g T') c := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  intro v v'
  have := GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (T v x) * T' v' x) g hF fun γ hγ x => by
    rw [(GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T hT v).2 γ hγ, (GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T' hT' v').2 γ hγ]
  exact ⟨this.1.1 (h v v').1, this.2.trans (h v v').2⟩

theorem finiteDimensional_fixed (hP : GlobalTheory.Published.HarishChandraFinite) (hθ : IsInfFam θ) (K : Subgroup (GfC V))
    (hK : IsOpen (K : Set (GfC V))) : FiniteDimensional ℂ ↥(allMaps θ M ⊓ fixed (finRep M) K) := by
  obtain ⟨N, hN, e⟩ := isOpen_induced_iff.1 hK
  have hmem : ∀ k : GfC V, (k : GA D V) ∈ N ↔ k ∈ K := fun k => Set.ext_iff.1 e k
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N (hN.mem_nhds ((hmem 1).2 K.one_mem))
  haveI := GlobalTheory.MultFinite.hcFinite (M := M) (J := N ∩ GfC V) (χ := fun _ => 1) hP hθ
    ⟨U, hU, fun k hk hf => ⟨⟨hUN k hk hf, hf⟩, rfl⟩⟩
  refine Submodule.finiteDimensional_of_le (S₂ := Mult θ M (N ∩ GfC V) fun _ => 1) fun T hT => Submodule.subset_span ?_
  have h := (GlobalTheory.MultMem.mem_mult_iff ..).1 hT.1
  refine ⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩
  have := congrArg (fun T : MMap M => T v g) (mem_fixed.1 hT.2 ⟨k, hk.2⟩ ((hmem ⟨k, hk.2⟩).1 hk.1))
  rw [one_mul]
  exact this

theorem exists_compact_open (V : HSp D) : ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) := by
  obtain ⟨_, _, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  obtain ⟨N, hN, h1⟩ := exists_compact_mem_nhds (1 : GA D V)
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N h1
  refine ⟨U.subgroupOf (GfC V), hU.preimage continuous_subtype_val, ?_⟩
  refine ((GlobalTheory.Ker.CongTop.isClosed_GfC V).isClosedEmbedding_subtypeVal.isCompact_preimage hN).of_isClosed_subset
    ((U.isClosed_of_isOpen hU).preimage continuous_subtype_val) fun k hk => hUN k hk k.2

theorem cuspDecomp : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, CuspDecomp D := by
  intro hP hQ D θ hθ V S M
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  have hμ : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
  obtain ⟨𝓕, hF⟩ := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V _ hμ).2
  have hS : SchurMult θ M ∅ (fun _ => 1) _ 𝓕 := GlobalTheory.MultFinite.schurMult hQ Measure.haar 𝓕
  obtain ⟨h1, h2⟩ := GlobalTheory.SchurConst.ipM_posDef D θ V S M _ _ _ 𝓕 hθ hμ hF hS (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  obtain ⟨K, ho, hc⟩ := exists_compact_open V
  refine isDecomp_of_form (finRep M) _ finRep_mem (ipM M Measure.haar 𝓕) h1 h2 (fun g T hT T' hT' => ?_)
    (finiteDimensional_fixed hP hθ) ho hc
  have h := isMultiplicityInner_finRep hμ hF g hT hT' (ipM_spec M _ 𝓕 T T' (hS hθ hμ hF T hT T' hT'))
  exact hasPeterssonInner_unique M _ 𝓕 _ _ v hv (ipM_spec M _ 𝓕 _ _ ⟨_, h⟩) h

end GlobalTheory.CuspDec

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

namespace GlobalTheory.HeisLatVac

theorem vacFn_hasCompactSupport_of_isCompact : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)))
    (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    IsCompact (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) → HasCompactSupport (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  intro F _ _ v κ _ ψ₀ Λ χ x₀ hΛ
  have hK : IsCompact ((fun u : (κ → Fv F v) × (κ → Fv F v) => x₀ + u.1) '' (Λ : Set _)) :=
    hΛ.image (continuous_const.add continuous_fst)
  refine HasCompactSupport.intro hK ?_
  intro x hx
  unfold vacFn
  rw [dite_eq_right]
  rintro ⟨u, hu, rfl⟩
  exact hx ⟨u, hu, rfl⟩

end GlobalTheory.HeisLatVac
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.HeisLatVac

theorem lc_pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IsotropicVectorExistence.main
  | exact _root_.GlobalTheory.IsotropicVectorExistence.main
  | (apply _root_.GlobalTheory.IsotropicVectorExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsotropicVectorExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsotropicVectorExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsotropicVectorExistence.main ..)

theorem lc_exists_open_ker {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ₀ : AddChar K ℂ) (hψ : Continuous ψ₀) : ∃ U₀ : OpenAddSubgroup K, ∀ t ∈ U₀, ψ₀ t = 1 := by
  have hV : {t : K | ‖ψ₀ t - 1‖ < 1 / 2} ∈ nhds (0 : K) :=
    (isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hV
  refine ⟨V, fun t ht => lc_pow_near_one fun n => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  exact hV (V.toAddSubgroup.nsmul_mem ht n)

theorem lc_val {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (hy : ∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y))
    (u : (κ → K) × (κ → K)) (hu : u ∈ Λ) :
    vacFn ψ₀ Λ χ x₀ (x₀ + u.1) = χ u * ψ₀ (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
  have h : ∃ u' ∈ Λ, x₀ + u.1 = x₀ + u'.1 := ⟨u, hu, rfl⟩
  rw [vacFn, dite_eq_left h]
  obtain ⟨hw, hwe⟩ := h.choose_spec
  generalize h.choose = w at hw hwe ⊢
  have h1 : w.1 = u.1 := (add_left_cancel hwe).symm
  have hyΛ : ((0 : κ → K), w.2 - u.2) ∈ Λ := by
    have e : ((0 : κ → K), w.2 - u.2) = w - u := Prod.ext (by simp [h1]) rfl
    rw [e]; exact Λ.sub_mem hw hu
  have hwu : w = u + (0, w.2 - u.2) := Prod.ext (by simp [h1]) (by simp)
  have e2 : χ w = χ u * χ (0, w.2 - u.2) * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ (w.2 - u.2) - (0 : κ → K) ⬝ᵥ u.2)) := by
    conv_lhs => rw [hwu]
    exact hco u hu _ hyΛ
  rw [e2, hy _ hyΛ, h1, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [zero_dotProduct, sub_zero, dotProduct_sub]
  ring

theorem isLocallyConstant_vacFn {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] [TopologicalSpace K]
    [IsTopologicalRing K] [NonarchimedeanAddGroup K] (ψ₀ : AddChar K ℂ) (hψ : Continuous ψ₀)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (hΛ : IsOpen (Λ : Set ((κ → K) × (κ → K))))
    (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (hy : ∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y))
    (h2 : ∀ u ∈ Λ, χ (u + u) = 1) : IsLocallyConstant (vacFn ψ₀ Λ χ x₀) := by
  obtain ⟨U₀, hU₀⟩ := lc_exists_open_ker ψ₀ hψ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  by_cases hx : ∃ u ∈ Λ, x = x₀ + u.1
  · obtain ⟨u, hu, rfl⟩ := hx
    have hN : {s : κ → K | (⅟(2 : K) • s, (0 : κ → K)) ∈ Λ ∧ s ⬝ᵥ u.2 ∈ (U₀ : Set K)} ∈ nhds (0 : κ → K) := by
      refine IsOpen.mem_nhds ?_ ?_
      · refine (hΛ.preimage ?_).inter (U₀.isOpen.preimage ?_)
        · exact (continuous_id.const_smul (⅟(2 : K))).prodMk (continuous_const : Continuous fun _ : κ → K => (0 : κ → K))
        · exact continuous_id.dotProduct continuous_const
      · refine ⟨?_, ?_⟩
        · show (⅟(2 : K) • (0 : κ → K), (0 : κ → K)) ∈ Λ
          rw [smul_zero, Prod.mk_zero_zero]; exact Λ.zero_mem
        · show (0 : κ → K) ⬝ᵥ u.2 ∈ (U₀ : Set K)
          rw [zero_dotProduct]; exact U₀.zero_mem
    filter_upwards [hN] with s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hs0 : (s, (0 : κ → K)) ∈ Λ := by
      have e : (s, (0 : κ → K)) = (⅟(2 : K) • s, (0 : κ → K)) + (⅟(2 : K) • s, (0 : κ → K)) := by
        refine Prod.ext ?_ (by simp)
        simp only [Prod.fst_add]
        rw [← add_smul, invOf_two_add_invOf_two, one_smul]
      rw [e]; exact Λ.add_mem hs1 hs1
    have hχs : χ (s, 0) = 1 := by
      have e : (s, (0 : κ → K)) = (⅟(2 : K) • s, (0 : κ → K)) + (⅟(2 : K) • s, (0 : κ → K)) := by
        refine Prod.ext ?_ (by simp)
        simp only [Prod.fst_add]
        rw [← add_smul, invOf_two_add_invOf_two, one_smul]
      rw [e]; exact h2 _ hs1
    have hx' : x₀ + u.1 + s = x₀ + (u + (s, 0)).1 := by simp [add_assoc]
    have hneg : ψ₀ (-(s ⬝ᵥ u.2)) = 1 := hU₀ _ (U₀.neg_mem hs2)
    rw [hx', lc_val ψ₀ Λ χ x₀ hco hy _ (Λ.add_mem hu hs0), lc_val ψ₀ Λ χ x₀ hco hy u hu,
      hco u hu _ hs0, hχs, mul_one, mul_assoc, ← AddChar.map_add_eq_mul]
    have key : ⅟(2 : K) * (u.1 ⬝ᵥ (s, (0 : κ → K)).2 - (s, (0 : κ → K)).1 ⬝ᵥ u.2) +
        (-(x₀ ⬝ᵥ (u + (s, 0)).2) - ⅟(2 : K) * ((u + (s, 0)).1 ⬝ᵥ (u + (s, 0)).2)) =
        -(s ⬝ᵥ u.2) + (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
      simp only [Prod.fst_add, Prod.snd_add, add_zero, dotProduct_zero, add_dotProduct]
      linear_combination (-(s ⬝ᵥ u.2)) * (invOf_two_add_invOf_two : ⅟(2 : K) + ⅟(2 : K) = 1)
    rw [key, AddChar.map_add_eq_mul, hneg, one_mul]
  · have h0 : vacFn ψ₀ Λ χ x₀ x = 0 := by rw [vacFn, dite_eq_right hx]
    have hN : {s : κ → K | (s, (0 : κ → K)) ∈ Λ} ∈ nhds (0 : κ → K) := by
      refine IsOpen.mem_nhds (hΛ.preimage (continuous_id.prodMk (continuous_const : Continuous fun _ : κ → K => (0 : κ → K)))) ?_
      show ((0 : κ → K), (0 : κ → K)) ∈ Λ
      rw [Prod.mk_zero_zero]; exact Λ.zero_mem
    filter_upwards [hN] with s hs
    rw [h0, vacFn, dite_eq_right]
    rintro ⟨u, hu, e⟩
    refine hx ⟨u - (s, 0), Λ.sub_mem hu hs, ?_⟩
    simp only [Prod.fst_sub]
    rw [← add_sub_assoc, ← e, add_sub_cancel_right]

end GlobalTheory.HeisLatVac


open GlobalTheory.HeisLatVac in
theorem GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    IsOpen (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : Fv F v) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → Fv F v, ((0 : κ → Fv F v), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, χ (u + u) = 1) → IsLocallyConstant (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  intro F _ _ v κ _ ψ₀ hψ Λ hΛ χ x₀ hco hy h2
  exact isLocallyConstant_vacFn ψ₀ hψ Λ hΛ χ x₀ hco hy h2
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer

theorem finsum_comp_eq_comp_finsum {ι V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : V →ₗ[ℂ] W) (g : ι → W →ₗ[ℂ] W) (h : ι → V →ₗ[ℂ] V) (hc : ∀ i, g i ∘ₗ T = T ∘ₗ h i)
    (hs : ∀ i, g i = 0 ↔ h i = 0) : (∑ᶠ i, g i) ∘ₗ T = T ∘ₗ ∑ᶠ i, h i := by
  have hg : Function.support g = Function.support h := by
    ext i; simp only [Function.mem_support, ne_eq, hs]
  by_cases hfin : (Function.support h).Finite
  · rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by rw [hg]; simp),
      finsum_eq_sum_of_support_subset h (s := hfin.toFinset) (by simp)]
    ext x

    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (hc i) x
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (by rwa [hg])]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem RF_apply' (x : finU (E := E) (n := n)) (φ : UA E n → ℂ) (g : UA E n) : RF E n x φ g = φ (g * x.1) := rfl

theorem RF_ne_zero (x : finU (E := E) (n := n)) : RF E n x ≠ 0 := by
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => (1 : ℂ))) 1
  simp at this
  exact one_ne_zero this

theorem rightReg_dual_ne_zero (lam : InfinitePlace E → DomWeight n) [Nontrivial (Wsp lam)] (x : finU (E := E) (n := n)) :
    rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) x ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Wsp lam)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (Wsp lam), φ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 hc)
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => φ)) 1
  have h2 : φ = 0 := by simpa [rightReg, LinearMap.funLeft] using this
  exact hφ (by rw [h2]; rfl)

theorem hop_phiFun (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam) :
    hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w := by
  rcases subsingleton_or_nontrivial (Wsp lam) with hW | hW
  · rw [Subsingleton.elim w 0]; simp
  set T : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (UA E n → ℂ) := (phiFun lam).flip w with hT
  have key : (∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out • (RF E n q.out ∘ₗ LinearMap.id)) ∘ₗ T =
      T ∘ₗ ∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out •
        (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id) := by
    refine finsum_comp_eq_comp_finsum T _ _ (fun q => ?_) (fun q => ?_)
    · ext G g
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, hT, LinearMap.flip_apply,
        LinearMap.map_smul, Pi.smul_apply]
      rw [RF_apply', phiFun_mul_fin]
    · rw [smul_eq_zero, smul_eq_zero, LinearMap.comp_id, LinearMap.comp_id]
      simp only [RF_ne_zero, rightReg_dual_ne_zero, or_false]
  have := LinearMap.congr_fun key F
  simp only [LinearMap.comp_apply, hT, LinearMap.flip_apply] at this
  simp only [hop, hopM, levOp, LinearMap.smul_apply, this, LinearMap.map_smul]

theorem hop_phiFun_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam), hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w :=
  fun _ _ _ _ _ S lam K' f F w => hop_phiFun S lam K' f F w

end GlobalTheory.BCT.TrKer
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical


theorem _root_.GlobalTheory.T.thetaTransform_inverseTransform_eq_quasiPeriodic : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, Continuous f → QuasiV ψ f → Decay (invV ψ ν 𝓓 f) → thV ψ (invV ψ ν 𝓓 f) = f := by
  first | exact @GlobalTheory.ThetaTransform.thV_invV_eq | exact GlobalTheory.ThetaTransform.thV_invV_eq | (intros; apply GlobalTheory.ThetaTransform.thV_invV_eq <;> assumption)
end
