module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3177
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle794
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.EmbeddingLemmas

theorem spMap_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    spMap (Desc.cst p) = gp X ≫ p := by
  have h : spMap (Desc.cst p) = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial) := rfl
  rw [h, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rfl

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (a : R →+* R') (b : R' →+* R'') :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  rw [← Spec.map_comp]; rfl

theorem cst_comp {X : Scheme.{0}} [IsIntegral X] {R R' : Type} [CommRing R] [CommRing R'] (q : X ⟶ Sp R') (ρ : R →+* R') :
    Desc.cst (q ≫ spMap ρ) = (Desc.cst q).comp ρ := by
  have e : spMap (Desc.cst (q ≫ spMap ρ)) = spMap ((Desc.cst q).comp ρ) := by
    rw [spMap_comp', spMap_cst, spMap_cst, Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem cst_inj {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] [IsDomain R] (p : X ⟶ Sp R) [Flat p] :
    Function.Injective (Desc.cst p) := by
  have h1 : Flat (gp X) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk X _
  have h2 : Flat (spMap (Desc.cst p)) := by rw [spMap_cst]; infer_instance
  have h3 : (Desc.cst p).Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h2
  algebraize [Desc.cst p]
  exact FaithfulSMul.algebraMap_injective R X.functionField

theorem baseIndexConstant_injective (σ : Setup) : Function.Injective σ.c₀ := by
  haveI := σ.ab.smooth
  exact cst_inj _

theorem abelianSchemeDescent_chart_baseConstants_comp (σ : Setup) (x : Sp σ.R) : (σ.θ x).comp σ.c₀ = (Desc.cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    rw [spMap_comp', spMap_comp', Setup.c₀, spMap_cst, spMap_cst, ← Category.assoc, ← hl', ← hl, Category.assoc,
      (σ.cart x).w]
    simp only [Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem linDisj_A (σ : Setup) : LinDisj σ.c₀ (Desc.cst σ.A.hom) (RingHom.id _) := by
  haveI := σ.ab.proper
  have hfl : (algebraMap σ.R (Localization.Away σ.f)).Flat := by
    rw [RingHom.flat_algebraMap_iff]; infer_instance
  refine (GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint σ.R _ _ hfl σ.A.left σ.A.left σ.A.left (σ.A.hom ≫ awayMap σ.f) σ.A.hom (𝟙 _) (𝟙 _)
    (RingHom.id _) inferInstance inferInstance ?_ ⟨gp _, by simp, ?_⟩ σ.D σ.D ?_).1
  · rw [Category.id_comp]
    exact IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  · have : spMap (RingHom.id σ.A.left.functionField) = 𝟙 _ := Spec.map_id _
    rw [this]; simp
  · intro v g h
    exact h

theorem linDisj_C (σ : Setup) (x : Sp σ.R) : LinDisj σ.c₀ (Desc.cst (σ.C x).G.hom) (σ.θ x) := by
  haveI := σ.ab.proper
  exact (GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint σ.R _ _ (σ.flat x) σ.A.left (σ.C x).G.left (σ.V x).toScheme (σ.A.hom ≫ awayMap σ.f) (σ.C x).G.hom
    (σ.V x).ι (σ.φ x) (σ.θ x) inferInstance inferInstance (σ.cart x) (σ.hθ x) σ.D (σ.D₁ x) (σ.pull x)).1

theorem compact_A (σ : Setup) : CompactSpace σ.A.left := by
  haveI := σ.ab.proper
  exact QuasiCompact.compactSpace_of_compactSpace σ.A.hom

theorem qsep_A (σ : Setup) : QuasiSeparatedSpace σ.A.left := by
  haveI := σ.ab.proper
  exact quasiSeparatedSpace_of_quasiSeparated σ.A.hom

theorem compact_C (σ : Setup) (x : Sp σ.R) : CompactSpace (σ.C x).G.left := by
  haveI := (σ.C x).semi.quasiCompact
  exact QuasiCompact.compactSpace_of_compactSpace (σ.C x).G.hom

theorem qsep_C (σ : Setup) (x : Sp σ.R) : QuasiSeparatedSpace (σ.C x).G.left := by
  haveI := (σ.C x).semi.separated
  exact quasiSeparatedSpace_of_quasiSeparated (σ.C x).G.hom

theorem cartA_of_openIn (σ : Setup) (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp σ.R) (hp : IsSeparated p)
    (i : σ.A.left ⟶ P) (h : OpenIn i σ.A.hom p (awayMap σ.f)) : IsPullback i σ.A.hom p (awayMap σ.f) := by
  obtain ⟨w, ho⟩ := h
  haveI := σ.ab.proper
  set g := pullback.lift i σ.A.hom w with hg
  have hsnd : g ≫ pullback.snd p (awayMap σ.f) = σ.A.hom := pullback.lift_snd _ _ _
  haveI : IsProper (g ≫ pullback.snd p (awayMap σ.f)) := by rw [hsnd]; infer_instance
  haveI : IsProper g := IsProper.of_comp g (pullback.snd p (awayMap σ.f))
  haveI : Nonempty (pullback p (awayMap σ.f) : Scheme.{0}) := ⟨g (genericPoint σ.A.left)⟩
  haveI : IsIntegral (pullback p (awayMap σ.f)) := isIntegral_of_isOpenImmersion (pullback.fst p (awayMap σ.f))
  have hclo : IsClopen (Set.range g) := ⟨g.isClosedMap.isClosed_range, g.isOpenEmbedding.isOpen_range⟩
  have hs : Surjective g := ⟨Set.range_eq_univ.1 (hclo.eq_univ (Set.range_nonempty _))⟩
  haveI : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).2 ⟨ho, hs⟩
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso g) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem onV_of (σ : Setup) (x : Sp σ.R) (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp σ.R) (hp : IsSeparated p)
    (ψ : P.functionField →+* σ.A.left.functionField) (i : σ.A.left ⟶ P) (hi : i ≫ p = σ.A.hom ≫ awayMap σ.f)
    (hfA : PFF (𝟙 _) i ψ) (e : (σ.C x).G.left ⟶ P) (he : e ≫ p = (σ.C x).G.hom ≫ spMap (σ.ρ x))
    (hf : PFF (𝟙 _) e ((σ.θ x).comp ψ)) : σ.φ x ≫ i = (σ.V x).ι ≫ e := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  obtain ⟨a, ha, ha'⟩ := hfA
  obtain ⟨b, hb, hb'⟩ := hf
  rw [Category.comp_id] at ha hb
  subst ha hb
  haveI : IsDominant (l ≫ (σ.V x).ι) := by
    rw [hl]
    refine ⟨?_⟩
    have hm : genericPoint (σ.C x).G.left ∈ Set.range (gp (σ.C x).G.left) :=
      ⟨closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    have hd : Dense {genericPoint (σ.C x).G.left} := by
      rw [dense_iff_closure_eq]; exact (genericPoint_spec _).def.trans rfl
    exact hd.mono (Set.singleton_subset_iff.2 hm)
  haveI : IsDominant l := IsDominant.of_comp_of_isOpenImmersion l (σ.V x).ι
  refine ext_of_isDominant_of_isSeparated p ?_ l ?_
  · rw [Category.assoc, Category.assoc, hi, he, (σ.cart x).w, Category.assoc]
  · rw [← Category.assoc, hl', ← Category.assoc, hl, hb', Category.assoc, ha', spMap_comp', Category.assoc]

end GlobalTheory.Desc.EmbeddingLemmas

namespace GlobalTheory.Desc


open GlobalTheory.Desc.EmbeddingLemmas in
theorem nonempty_emb : ∀ σ : Setup, σ.Common → Nonempty (Emb σ) := by
  intro σ _
  obtain ⟨hG, k₀, hk₀, b₀, hb₀, hb₀0⟩ := GlobalTheory.T.abelianSchemeDescent_gradedFamily_nonzero σ
  obtain ⟨P, hPi, p, ψ, Dp, hM⟩ := GlobalTheory.T.exists_integral_separated_projModel_gradedFunctions σ.R _ σ.c₀ σ.N hG ⟨k₀, hk₀, b₀, hb₀, hb₀0⟩
  have hinj := baseIndexConstant_injective σ

  haveI : IsDomain (Localization.Away σ.f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors σ.hf)
  have hcA : (RingHom.id _).comp σ.c₀ = (cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := by
    rw [RingHom.id_comp]; exact cst_comp σ.A.hom _
  have hspA : ∀ k, Sec σ.D k = spanBy (cst σ.A.hom) ((RingHom.id _) '' σ.N k) := by
    intro k; rw [RingHom.coe_id, Set.image_id]; exact GlobalTheory.T.cartierMultipleGlobalSections_eq_span_regularLattice σ k
  have hsecA : ∀ k, ∀ a ∈ σ.N k, (RingHom.id _) a ∈ Sec σ.D k := fun k a ha => ha.1
  have hcovA := GlobalTheory.T.exists_cartierSectionLocus_of_ample_span _ _ σ.A.left σ.A.hom (RingHom.id _) σ.N σ.D σ.amp hspA
  obtain ⟨m, hm, hmf, hml⟩ := GlobalTheory.T.exists_map_integral_scheme_to_graded_proj_model σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (Localization.Away σ.f)
    (algebraMap σ.R (Localization.Away σ.f)) σ.A.left σ.A.hom (RingHom.id _) σ.D hcA hsecA hcovA
  haveI := compact_A σ
  haveI := qsep_A σ
  have hflA : (algebraMap σ.R (Localization.Away σ.f)).Flat := by
    rw [RingHom.flat_algebraMap_iff]; infer_instance
  have hoA := GlobalTheory.T.isOpenImmersion_to_graded_model_flat_base_change σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (Localization.Away σ.f)
    (algebraMap σ.R (Localization.Away σ.f)) hflA hinj σ.A.left σ.A.hom (RingHom.id _) σ.D hcA (linDisj_A σ) σ.amp hspA
    m hm hmf hml
  have hcart := cartA_of_openIn σ P p hM.sep m hoA

  have hC : ∀ x, ∃ e : (σ.C x).G.left ⟶ P, e ≫ p = (σ.C x).G.hom ≫ spMap (σ.ρ x) ∧ PFF (𝟙 _) e ((σ.θ x).comp ψ) ∧
      OpenIn e (σ.C x).G.hom p (spMap (σ.ρ x)) := by
    intro x
    have hsp := GlobalTheory.T.cartierMultipleGlobalSections_chart_eq_span σ x
    have hsec : ∀ k, ∀ a ∈ σ.N k, σ.θ x a ∈ Sec (σ.D₁ x) k := fun k a ha => by
      rw [hsp k]; exact subset_spanBy _ _ (Set.mem_image_of_mem _ ha)
    have hcov := GlobalTheory.T.exists_cartierSectionLocus_of_ample_span _ _ (σ.C x).G.left (σ.C x).G.hom (σ.θ x) σ.N (σ.D₁ x) (σ.amp₁ x) hsp
    obtain ⟨e, he, hef, hel⟩ := GlobalTheory.T.exists_map_integral_scheme_to_graded_proj_model σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (σ.C x).R (σ.ρ x) (σ.C x).G.left
      (σ.C x).G.hom (σ.θ x) (σ.D₁ x) (abelianSchemeDescent_chart_baseConstants_comp σ x) hsec hcov
    haveI := compact_C σ x
    haveI := qsep_C σ x
    exact ⟨e, he, hef, GlobalTheory.T.isOpenImmersion_to_graded_model_flat_base_change σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (σ.C x).R (σ.ρ x) (σ.flat x) hinj (σ.C x).G.left
      (σ.C x).G.hom (σ.θ x) (σ.D₁ x) (abelianSchemeDescent_chart_baseConstants_comp σ x) (linDisj_C σ x) (σ.amp₁ x) hsp e he hef hel⟩
  choose e he hef heo using hC
  have hm' : m ≫ p = σ.A.hom ≫ awayMap σ.f := hm
  have hmf' : PFF (𝟙 _) m ψ := by simpa using hmf
  exact ⟨{
    P := P
    p := p
    sep := hM.sep
    ψ := ψ
    ιA := m
    cartA := hcart
    ffA := hmf'
    emb := e
    openIn := heo
    ff := hef
    onV := fun x => onV_of σ x P p hM.sep ψ m hm' hmf' (e x) (he x) (hef x) }⟩

end GlobalTheory.Desc
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTTors

open GlobalTheory.IwLevel GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S : Scheme.{0}} {s : S ⟶ Sp R}

def actF (o : Obj b N s) : Out.RingAct o.A (𝓞 D.F) :=
  ⟨fun c => o.act.act (algebraMap (𝓞 D.F) D.O c), fun _ => o.act.hom _,
   by rw [map_one]; exact o.act.one,
   fun _ _ => by rw [map_mul]; exact o.act.mul _ _,
   fun _ _ => by rw [map_add (f := _)]; exact o.act.add _ _⟩

theorem killedBy_map (o : Obj b N s) (w : Ideal (𝓞 D.F)) {T : Over S} (x : T ⟶ o.A) :
    KilledBy (htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x ↔ KilledBy (actF o) w x := by
  rw [Ideal.map, killedBy_span]
  exact Set.forall_mem_image

theorem inSub_ker {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] {T : Over S} (x : T ⟶ A) :
    InSub (pullback.fst f η[B]) x ↔ x ≫ f = 1 := by
  refine ⟨?_, fun h => ⟨KerGrp.lift f x h, KerGrp.lift_fst _ _ _⟩⟩
  rintro ⟨y, rfl⟩
  rw [Category.assoc, KerGrp.fst_comp, MonObj.comp_one]

theorem comp_lift_eq_one {A : Over S} [GrpObj A] {T : Over S} (x : T ⟶ A) (a c : A ⟶ A) :
    x ≫ lift a c = 1 ↔ x ≫ a = 1 ∧ x ≫ c = 1 := by
  constructor
  · intro h
    have h1 := congrArg (· ≫ fst A A) h
    have h2 := congrArg (· ≫ snd A A) h
    simp only [Category.assoc, lift_fst, lift_snd, MonObj.one_comp] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, h1, MonObj.one_comp]
    · rw [Category.assoc, lift_snd, h2, MonObj.one_comp]

theorem killedBy_pair {A : Over S} [GrpObj A] [IsCommMonObj A] (ρ : Out.RingAct A (𝓞 D.F)) (g e : 𝓞 D.F)
    {T : Over S} (x : T ⟶ A) :
    KilledBy ρ (Ideal.span {g, e}) x ↔ x ≫ lift (ρ.act g) (ρ.act e) = 1 := by
  rw [killedBy_span, comp_lift_eq_one]
  simp

theorem htTorsion : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (w : Ideal (𝓞 D.F)), w ≠ ⊥ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A), IsMonHom i ∧ Mono i ∧ GlobalTheory.IwLevel.IsIsogDeg (toUnit K) ((Ideal.absNorm w ^ D.m) ^ D.n) ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N S s o w hw
  obtain ⟨g, e, 𝔟, hg0, he, hf, hmul, hp⟩ := GlobalTheory.T.exists_coprime_ideal_mul_eq_span_numberField D.F p (Fact.out) w hw
  have hI2 := fun c hc => GlobalTheory.T.isIsogenyOfDegree_intAction_harrisTaylor p D R b N S s o c hc
  let ρ := actF o
  have hρ : ∀ c, IsMonHom (ρ.act c) := ρ.hom

  have hgw : g ∈ w * 𝔟 := by rw [hmul]; exact Ideal.mem_span_singleton_self g
  have hgw1 : g ∈ w := Ideal.mul_le_left (I := w) (J := 𝔟) hgw
  have hgw2 : g ∈ 𝔟 := Ideal.mul_le_right (I := w) (J := 𝔟) hgw
  have hw' : w = Ideal.span {g, e} := by
    apply le_antisymm
    · intro a ha
      have hsplit : a = a * (1 - e) + a * e := by ring
      rw [hsplit]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      have h1 : a * (1 - e) ∈ w * 𝔟 := Ideal.mul_mem_mul ha hf
      rw [hmul, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      rw [← ht]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hgw1, Set.singleton_subset_iff.2 he⟩)
  have h𝔟' : 𝔟 = Ideal.span {g, 1 - e} := by
    apply le_antisymm
    · intro a ha
      have hsplit : a = e * a + a * (1 - e) := by ring
      rw [hsplit]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      have h1 : e * a ∈ w * 𝔟 := Ideal.mul_mem_mul he ha
      rw [hmul, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      rw [← ht]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hgw2, Set.singleton_subset_iff.2 hf⟩)
  have hcop : w ⊔ 𝔟 = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 D.F) = e + (1 - e) := by ring
    rw [h1]
    exact Submodule.add_mem_sup he hf
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hmul
    exact hg0 hmul

  let f₁ : o.A ⟶ o.A ⊗ o.A := lift (ρ.act g) (ρ.act e)
  let f₂ : o.A ⟶ o.A ⊗ o.A := lift (ρ.act g) (ρ.act (1 - e))
  letI := KerGrp.grp f₁
  have h₁ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst f₁ η[o.A ⊗ o.A]) x ↔ KilledBy ρ w x := by
    intro T x; rw [inSub_ker, hw', killedBy_pair]
  have h₂ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst f₂ η[o.A ⊗ o.A]) x ↔ KilledBy ρ 𝔟 x := by
    intro T x; rw [inSub_ker, h𝔟', killedBy_pair]
  have h₃ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst (ρ.act g) η[o.A]) x ↔ KilledBy ρ (w * 𝔟) x := by
    intro T x; rw [inSub_ker, hmul, killedBy_span]; simp
  have d₃ : IsIsogDeg (toUnit (ker (ρ.act g)))
      (Ideal.absNorm w ^ (D.m * D.n) * Ideal.absNorm 𝔟 ^ (D.m * D.n)) := by
    rw [← mul_pow, ← map_mul, hmul, Ideal.absNorm_span_singleton]
    exact (hI2 g hg0).ker
  have d₂ : IsIsogDeg (toUnit (ker f₂)) (Ideal.absNorm 𝔟 ^ (D.m * D.n)) :=
    GlobalTheory.T.isIsogenyDegree_killedBy_primeToP_harrisTaylor p D R b N S s o hI2 𝔟 hp _ (pullback.fst f₂ η[o.A ⊗ o.A]) inferInstance
      (fun T x => by rw [h₂, killedBy_map])
  have hpos : 0 < Ideal.absNorm 𝔟 ^ (D.m * D.n) :=
    pow_pos (Nat.pos_of_ne_zero (fun h => h𝔟0 (Ideal.absNorm_eq_zero_iff.1 h))) _
  have d₁ := GlobalTheory.T.isIsogenyOfDegree_torsion_coprime_ideals_product S o.A (𝓞 D.F) ρ w 𝔟 hcop _ _ _ (pullback.fst f₁ η[o.A ⊗ o.A])
    (pullback.fst f₂ η[o.A ⊗ o.A]) (pullback.fst (ρ.act g) η[o.A]) inferInstance inferInstance inferInstance
    h₁ h₂ h₃ _ _ hpos d₃ d₂
  refine ⟨ker f₁, KerGrp.grp f₁, pullback.fst f₁ η[o.A ⊗ o.A], KerGrp.isMonHom_fst f₁, inferInstance,
    by rw [← pow_mul]; exact d₁, fun T x => by rw [h₁, killedBy_map]⟩

end GlobalTheory.HTTors
end
end
