module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle013
public import Development.EtaleCohomology.CohomologicalPurity.Bundle014
public import Development.EtaleCohomology.CohomologicalPurity.Bundle015
public import Development.EtaleCohomology.CohomologicalPurity.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.HtpyZeroPf

theorem eqv_of_iso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem off_bot_empty (B : Type) [CommRing B] (J : Ideal B) (hJ : J = ⊥) : IsEmpty (off B J) := by
  refine ⟨fun x => x.2 ?_⟩
  subst hJ
  change ((⊥ : Ideal B) : Set B) ⊆ ((x.1 : PrimeSpectrum B).asIdeal : Set B)
  intro a ha
  rw [SetLike.mem_coe, Ideal.mem_bot] at ha
  rw [SetLike.mem_coe, ha]
  exact Ideal.zero_mem _

theorem isIso_of_empty {X Y : Scheme.{0}} (f : X ⟶ Y) [IsEmpty X] [IsEmpty Y] : IsIso f :=
  ⟨⟨isInitialOfIsEmpty.to X, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩⟩

end HtpyZeroPf

theorem LeafHtpyZero_of : LeafHtpyZero := by
  intro _ q _ A _ h i
  have : IsEmpty (off A ⊥) := HtpyZeroPf.off_bot_empty A ⊥ rfl
  have : IsEmpty (off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C)) :=
    HtpyZeroPf.off_bot_empty _ _ (Ideal.map_bot)
  have : IsEmpty (off A ⊥).toScheme := inferInstanceAs (IsEmpty (off A ⊥))
  have : IsEmpty (off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C)).toScheme :=
    inferInstanceAs (IsEmpty (off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C)))
  have := HtpyZeroPf.isIso_of_empty
    ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)
  exact HtpyZeroPf.eqv_of_iso _ _

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

theorem le_of_comp {Y Z X : Scheme.{0}} {W : Y.Opens} {V : Z.Opens} (f : Y ⟶ Z) (g : Z ⟶ X) (U : X.Opens)
    (hV : V = g ⁻¹ᵁ U) (k : Y ⟶ X) (hk : f ≫ g = k) (hW : W ≤ k ⁻¹ᵁ U) : W ≤ f ⁻¹ᵁ V := by
  subst hV hk; intro w hw; exact hW hw

theorem pre_comp {Y Z X : Scheme.{0}} (f : Y ⟶ Z) (g : Z ⟶ X) (V : Z.Opens) (U : X.Opens) (hV : V = g ⁻¹ᵁ U) :
    f ⁻¹ᵁ V = (f ≫ g) ⁻¹ᵁ U := by
  subst hV; ext; rfl

theorem LeafPcGlue_pf : LeafPcGlue := by
  intro q X U m i hG A p s hcov H
  let E := fun a => Equiv.ofBijective _ (pc_bij (q := q) (p a) m i)
  obtain ⟨c, hc⟩ := hG A (fun a => (p a).j.opensRange) (fun a => (E a).symm (s a)) (fun x hx => hcov x hx) (by
    intro a b x hxa hxb hxU
    obtain ⟨y, rfl⟩ : x ∈ Set.range (p a).j := hxa
    obtain ⟨t, u, h, hcomm, ⟨z, rfl⟩, heq⟩ := H a b y hxU hxb
    let P : Pc U := ⟨t.Y, t.j ≫ (p a).j, inferInstance, t.V, t.hV.trans (pre_comp _ _ _ U (p a).hV)⟩
    have ha : P.j.opensRange ≤ (p a).j.opensRange := by rintro _ ⟨w, rfl⟩; exact ⟨t.j w, rfl⟩
    have hb : P.j.opensRange ≤ (p b).j.opensRange := by
      rintro _ ⟨w, rfl⟩
      refine ⟨u w, ?_⟩
      change (u ≫ (p b).j) w = (t.j ≫ (p a).j) w
      rw [hcomm]
    have ea : P.j.isoOpensRange.hom ≫ X.homOfLE ha = t.j ≫ (p a).j.isoOpensRange.hom := by
      rw [← cancel_mono ((p a).j.opensRange.ι)]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]; rfl
    have eb : P.j.isoOpensRange.hom ≫ X.homOfLE hb = u ≫ (p b).j.isoOpensRange.hom := by
      rw [← cancel_mono ((p b).j.opensRange.ι)]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]
      exact hcomm
    have hPV : P.V ≤ P.j ⁻¹ᵁ U := P.hV.le
    have ha' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE ha ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl
    have hb' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE hb ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl
    refine ⟨P.j.opensRange, ha, hb, ha', hb', ⟨z, rfl⟩, ?_⟩
    apply (pc_bij P m i).1
    have k1 : P.V ≤ (t.j ≫ (p a).j.isoOpensRange.hom) ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]) hPV
    have k2 : P.V ≤ (u ≫ (p b).j.isoOpensRange.hom) ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← hcomm]) hPV
    rw [pull_pull _ _ ea _ _ _ _ _ k1, pull_pull _ _ eb _ _ _ _ _ k2,
      ← pull_pull t.j _ rfl _ _ _ t.hV.le (pc_le (p a)) k1, ← pull_pull u _ rfl _ _ _ h (pc_le (p b)) k2]
    change Hs.pull q _ m i (E a ((E a).symm (s a))) = Hs.pull q _ m i (E b ((E b).symm (s b)))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact heq)
  refine ⟨c, fun a => ?_⟩
  rw [pc_res, hc a]
  exact (E a).apply_symm_apply (s a)

theorem LeafDesc_of' (hD : LeafDict) (hF : LeafFlq) (hS : LeafDescOSep) (hG : LeafDescOGlue) : LeafDesc :=
  LeafDesc_of hD hF hS hG LeafPcGlue_pf

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut.ChainsSumPf

universe v u
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

def zeroColim {D : Type*} [Category* D] {J : Type*} [Category* J] (G : D ⥤ C) (hG : ∀ X, IsZero (G.obj X))
    {K : J ⥤ D} (s : Cocone K) : IsColimit (G.mapCocone s) where
  desc _ := 0
  fac _ _ := (hG _).eq_of_src _ _
  uniq _ _ _ := (hG _).eq_of_src _ _

theorem presZero {D : Type*} [Category* D] {J : Type*} [Category* J] (G : D ⥤ C) (hG : ∀ X, IsZero (G.obj X)) :
    PreservesColimitsOfShape J G :=
  ⟨fun {_} => ⟨fun {s} _ => ⟨zeroColim G hG s⟩⟩⟩

theorem presExtend {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
    (J : Type*) [Category* J] [HasColimitsOfShape J C] : PreservesColimitsOfShape J (e.extendFunctor C) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro i'
  cases h : e.r i' with
  | none => exact presZero _ fun K => K.isZero_extend_X' e i' h
  | some p =>
    have hp : e.f p = i' := e.f_eq_of_r_eq_some h
    let φ : HomologicalComplex.eval C c p ≅ e.extendFunctor C ⋙ HomologicalComplex.eval C c' i' :=
      NatIso.ofComponents (fun K => (K.extendXIso e hp).symm) (fun {K L} f => by
        simp [ComplexShape.Embedding.extendFunctor, HomologicalComplex.extendMap_f _ e hp])
    exact preservesColimitsOfShape_of_natIso φ

theorem presAFM {C : Type*} [Category* C] [Preadditive C] (J : Type*) [Category* J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (AlgebraicTopology.alternatingFaceMapComplex C) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  let φ : (evaluation _ C).obj (op (SimplexCategory.mk n)) ≅
      AlgebraicTopology.alternatingFaceMapComplex C ⋙ HomologicalComplex.eval C _ n :=
    NatIso.ofComponents (fun X => Iso.refl _) (fun {X Y} f => (Category.comp_id _).trans (Category.id_comp _).symm)
  exact preservesColimitsOfShape_of_natIso φ

variable (R : Type) [CommRing R]

theorem presFree (A : Type) : PreservesColimitsOfShape (Discrete A) (free R) := by
  have h1 : PreservesColimitsOfSize.{0, 0} (ModuleCat.free (ULift.{1} R)) :=
    (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits
  have h2 : PreservesColimitsOfSize.{0, 0} (presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))) :=
    (sheafificationAdjunction _ _).leftAdjoint_preservesColimits
  unfold free freeP
  infer_instance

instance hasCoprodShv (A : Type) : HasColimitsOfShape (Discrete A) (Shv R) := by
  have : HasColimitsOfSize.{1, 1} (Shv R) := IsGrothendieckAbelian.hasColimits (Shv R)
  have : HasColimitsOfSize.{0, 0} (Shv R) := hasColimitsOfSizeShrink.{0, 0, 1, 1} _
  infer_instance

theorem presChains (A : Type) : PreservesColimitsOfShape (Discrete A) (chains R) := by
  have := presFree R A
  have : PreservesColimitsOfShape (Discrete A) ((SimplicialObject.whiskering PSh (Shv R)).obj (free R)) := by
    unfold SimplicialObject.whiskering; infer_instance
  have := presAFM (C := Shv R) (Discrete A)
  have := presExtend (C := Shv R) ComplexShape.embeddingDownNat (Discrete A)
  unfold chains chainsN
  infer_instance

end LateralTheory.CohomologicalPurity.TubeCut.SumCut.ChainsSumPf

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut

theorem LeafChainsSum_of : LeafChainsSum := by
  intro R _ A E c ⟨hc⟩
  have := ChainsSumPf.presChains R A
  exact ⟨isColimitCofanMkObjOfIsColimit (chains R) E c.inj hc⟩

end LateralTheory.CohomologicalPurity.TubeCut.SumCut
end
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

noncomputable section
namespace LateralTheory.CohomologicalPurity.TubeCut

instance sch_preservesPullbacks : PreservesLimitsOfShape WalkingCospan sch :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (yoneda ⋙ SimplicialObject.const PSh))

theorem pbRel_isIso_of {B G E' E Q₁ Q₀ : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π')
    {f₁ : Q₁ ⟶ E'} {z₁ : Q₁ ⟶ G} {f₀ : Q₀ ⟶ E} {z₀ : Q₀ ⟶ G} (h₁ : IsPullback f₁ z₁ π' g) (h₀ : IsPullback f₀ z₀ π g)
    (k : Q₁ ⟶ Q₀) [IsIso k] (kf : k ≫ f₀ = f₁ ≫ a) (kz : k ≫ z₀ = z₁) : IsIso (pbRel g a π' π h) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have e : h₁.isoPullback.hom ≫ pbRel g a π' π h = k ≫ h₀.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [pbRel, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, kf]
    · simp only [pbRel, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd, kz, Category.comp_id]
  have e' : pbRel g a π' π h = h₁.isoPullback.inv ≫ k ≫ h₀.isoPullback.hom := by
    rw [← e, Iso.inv_hom_id_assoc]
  rw [e']; infer_instance

theorem isIso_specMap_of_bij {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hb : Function.Bijective f) :
    IsIso (Spec.map (CommRingCat.ofHom f)) := by
  have : IsIso (CommRingCat.ofHom f) := (RingEquiv.ofBijective f hb).toCommRingCatIso.isIso_hom
  infer_instance

theorem quot_bij_of_eq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I J : Ideal A) (e : J = I) (K : Ideal B)
    (hK : K = I.map φ) (h : J ≤ K.comap φ) (hb : Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap K φ h) := by
  subst e; subst hK; exact hb

theorem LeafLocIso_of (hZ : LeafZ) (hQ : LeafQuot) : LeafLocIso := by
  intro H d P V h
  have := P.cl
  set A := Γ(P.X, V.1)
  set I := P.ι.ker.ideal V
  set φ : A →+* H.obj A I := eta H P V
  obtain ⟨⟨z₁, h₁⟩, -⟩ := hZ P.X P.Z P.ι V (H.obj A I) φ
  obtain ⟨⟨z₀, h₀'⟩, -⟩ := hZ P.X P.Z P.ι V A (RingHom.id A)
  have e₀ : Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ V.2.fromSpec = V.2.fromSpec := by simp
  rw [e₀] at h₀'
  have hle : I.map (RingHom.id A) ≤ (I.map φ).comap φ := by rw [Ideal.map_id]; exact Ideal.le_comap_map
  set qm := Ideal.quotientMap (I.map φ) φ hle
  have hb : Function.Bijective qm := quot_bij_of_eq φ I _ (Ideal.map_id I) _ rfl hle (hQ A (H.obj A I) φ I (H.ind A I))
  have hcomp : qm.comp (Ideal.Quotient.mk (I.map (RingHom.id A))) = (Ideal.Quotient.mk (I.map φ)).comp φ :=
    Ideal.quotientMap_comp_mk hle
  have kf : Spec.map (CommRingCat.ofHom qm) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (RingHom.id A)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp]
  have kz : Spec.map (CommRingCat.ofHom qm) ≫ z₀ = z₁ := by
    rw [← cancel_mono P.ι, Category.assoc, ← h₀'.w, ← h₁.w, ← Category.assoc, kf, Category.assoc]
  have := isIso_specMap_of_bij qm hb
  exact pbRel_isIso_of _ _ _ _ h (h₁.map sch) (h₀'.map sch) (sch.map (Spec.map (CommRingCat.ofHom qm)))
    (by rw [← sch.map_comp, kf, sch.map_comp]) (by rw [← sch.map_comp, kz])

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem opnMap_comp_RLocP {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens)
    (h : U'' ≤ f ⁻¹ᵁ U') (h' : U' ≤ g ⁻¹ᵁ U) (h'' : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap f U'' U' h ≫ opnMap g U' U h' = opnMap (f ≫ g) U'' U h'' := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp]

theorem hs_pull_id_RLocP (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1
  have e : dbl.map (𝟙 P) = 𝟙 _ := by
    set_option synthInstance.maxHeartbeats 200000 in
      apply pushout.hom_ext <;> (simp [dbl.map]; rfl)
  rw [e, pull_id]

theorem LeafLocPrd_of (hCl : LeafCl) (hPR : LeafPrdRing) (hZ : LeafZ) (hAbv : LeafAbv) (hAN : LeafActNat) : LeafLocPrd := by
  intro hyp H d P V q _ hq hG
  have a6 : DivisorNaturality := hyp.2.2.2.2.1
  haveI := P.cl
  have hcl : IsCl d (fcl d) := pick_spec (hCl hyp d)

  have hqA : IsUnit (q : Γ(P.X, V.1)) := by
    have := hq.map (P.X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
    simpa using this
  have hoff : ∀ (B : Type) [CommRing B] (φ : Γ(P.X, V.1) →+* B),
      off B ((P.ι.ker.ideal V).map φ) = (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ P.U :=
    fun B _ φ => (hZ P.X P.Z P.ι V B φ).2 P.U P.hU
  have e0 : off Γ(P.X, V.1) (P.ι.ker.ideal V) = V.2.fromSpec ⁻¹ᵁ P.U := by
    have e := hoff Γ(P.X, V.1) (RingHom.id _)
    rw [Ideal.map_id] at e
    rw [e]; rfl
  have h0 : off Γ(P.X, V.1) (P.ι.ker.ideal V) ≤ V.2.fromSpec ⁻¹ᵁ P.U := le_of_eq e0
  haveI : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  obtain ⟨c, hcdef⟩ : ∃ c, c = Hs.pull q (opnMap V.2.fromSpec _ _ h0) _ _ (fcl d q P) := ⟨_, rfl⟩
  have hc : ∀ (B : Type) [CommRing B] (φ : Γ(P.X, V.1) →+* B) (x : Fin d → B) hx h, φ.Etale →
      Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B ((P.ι.ker.ideal V).map φ)) (off _ (P.ι.ker.ideal V)) h) _ _ c
        = thom d q B ((P.ι.ker.ideal V).map φ) x hx := by
    intro B _ φ x hx h hφ
    obtain ⟨z, hz⟩ := (hZ P.X P.Z P.ι V B φ).1
    haveI : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr hφ
    have h' : off B ((P.ι.ker.ideal V).map φ) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ P.U :=
      le_of_eq (hoff B φ)
    rw [hcdef, ← hs_pull_comp, opnMap_comp_RLocP _ _ _ _ _ _ _ h']
    exact (hcl q).1 P hq B _ x hx _ z h' inferInstance hz
  have key := hPR hyp H d q Γ(P.X, V.1) (P.ι.ker.ideal V) hqA hG.1 hG.2 c hc

  have hU' := hoff _ (eta H P V)
  obtain ⟨e, he1, he2⟩ := hAbv _ P.X (hensTo H P V) _ P.U hU'
  intro n i
  have hh : off (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ((P.ι.ker.ideal V).map (eta H P V)) ≤
      Spec.map (CommRingCat.ofHom (eta H P V)) ⁻¹ᵁ off Γ(P.X, V.1) (P.ι.ker.ideal V) := by
    rw [hoff _ (eta H P V), e0]; intro x hx; exact hx
  have hk := key hh n i
  have hpe : Function.Bijective (Hs.pull q e.hom (n + 2 * d) (i + d)) :=
    Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv _ _,
      fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id_RLocP],
      fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id_RLocP]⟩
  have hcomp : ∀ a : Ht q (sch.obj (Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)))) n i,
      Hs.pull q e.hom _ _ (Hs.act q (P := abv P.U (sch.map (hensTo H P V))) a
        (Hs.pull q (abvMap P.U (sch.map (hensTo H P V))) _ _ (fcl d q P))) =
      Hs.act q (P := opn (off (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ((P.ι.ker.ideal V).map (eta H P V)))) a
        (Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom (eta H P V))) _ _ hh) _ _ c) := by
    intro a
    refine (hAN a6 q _ _ e.hom n (2 * d) i d a _).trans ?_
    rw [he1]
    erw [pull_id]
    rw [← hs_pull_comp, he2, hcdef, ← hs_pull_comp, opnMap_comp_RLocP]
  refine (Function.Bijective.of_comp_iff' hpe _).1 ?_
  have hf := funext hcomp
  rw [show (⇑(Hs.pull q e.hom (n + 2 * d) (i + d)) ∘ fun a : Ht q (sch.obj (Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)))) n i =>
      Hs.act q (P := abv P.U (sch.map (hensTo H P V))) a
        (Hs.pull q (abvMap P.U (sch.map (hensTo H P V))) _ _ (fcl d q P))) = _ from hf]
  exact hk

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

instance schPresPb : PreservesLimitsOfShape WalkingCospan sch :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (yoneda ⋙ disc))

theorem LeafLocFst_of (hZ : LeafZ) : LeafLocFst := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro hE H d P V q hq i
  have := P.cl
  obtain ⟨⟨z, hpb⟩, -⟩ := hZ P.X P.Z P.ι V (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) (eta H P V)
  have hpb' := hpb.map sch
  have := H.hens Γ(P.X, V.1) (P.ι.ker.ideal V)
  have hu : IsUnit (q : H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) := by
    simpa using hq.map ((eta H P V).comp (P.X.presheaf.map (homOfLE le_top).op).hom)
  have e : pullback.fst (sch.map (hensTo H P V)) (sch.map P.ι) = hpb'.isoPullback.inv ≫
      sch.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((P.ι.ker.ideal V).map (eta H P V))))) :=
    hpb'.isoPullback_inv_fst.symm
  rw [e]
  exact eqv_comp (eqv_iso _ _) (hE q _ _ hu i)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem hs_pull_id (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1
  have e : dbl.map (𝟙 P) = 𝟙 _ := by
    set_option synthInstance.maxHeartbeats 200000 in
      apply pushout.hom_ext <;> (simp [dbl.map]; try rfl)
  rw [e, pull_id]

theorem exc_iso (q : ℕ) {P' P : Arrow Spc} (e : P' ≅ P) : Exc q e.hom := fun n i =>
  Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv n i,
    fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id],
    fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id]⟩

theorem abv_ext {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {Q : Arrow Spc} (α β : Q ⟶ abv U π)
    (hr : α.right = β.right) (hm : α ≫ abvMap U π = β ≫ abvMap U π) : α = β := by
  apply Arrow.hom_ext _ _ _ hr
  set_option synthInstance.maxHeartbeats 200000 in
    apply pullback.hom_ext
  · have wa := Arrow.w α
    have wb := Arrow.w β
    change α.left ≫ pullback.fst π (sch.map U.ι) = Q.hom ≫ α.right at wa
    change β.left ≫ pullback.fst π (sch.map U.ι) = Q.hom ≫ β.right at wb
    rw [hr] at wa
    exact wa.trans wb.symm
  · exact congrArg CommaMorphism.left hm

theorem opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens)
    (h1 : U'' ≤ f ⁻¹ᵁ U') (h2 : U' ≤ g ⁻¹ᵁ U) (h3 : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap f U'' U' h1 ≫ opnMap g U' U h2 = opnMap (f ≫ g) U'' U h3 := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp]

theorem LeafLocHen_of (hI : LeafIndExc) (hZ : LeafZ) (hA : LeafAbv) : LeafLocHen := by
  intro hyp H d P V q hq hfg h
  obtain ⟨a1, -, -, a4, -, -, -, -, b1, -, -, -⟩ := hyp
  have := P.cl
  set A := Γ(P.X, V.1)
  set I := P.ι.ker.ideal V
  set φ := eta H P V
  set g := V.2.fromSpec
  set f : Spec (H.obj A I) ⟶ Spec A := Spec.map (CommRingCat.ofHom φ)
  have hqA : IsUnit (q : A) := by
    have := hq.map (P.X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
    simpa using this
  have zB := (hZ P.X P.Z P.ι V (H.obj A I) φ).2 P.U P.hU
  have zA := (hZ P.X P.Z P.ι V A (RingHom.id A)).2 P.U P.hU
  rw [Ideal.map_id] at zA
  have e1 : Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ g = g := by
    rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 _ from rfl, Spec.map_id, Category.id_comp]
  rw [e1] at zA
  have hle : off (H.obj A I) (I.map φ) ≤ f ⁻¹ᵁ (off A I) := by
    rw [zB, zA]; intro x hx; exact hx
  have ind := hI a1 a4 b1 q φ I hfg (H.ind A I) hqA hle
  obtain ⟨eA, eAr, eAm⟩ := hA _ _ g _ P.U zA
  obtain ⟨eB, eBr, eBm⟩ := hA _ _ (f ≫ g) _ P.U zB
  have sq : eB.hom ≫ abvRel P.U (sch.map f) (sch.map (f ≫ g)) (sch.map g) h = opnMap f _ _ hle ≫ eA.hom := by
    apply abv_ext
    · rw [Arrow.comp_right, Arrow.comp_right, eBr, eAr]
      exact (Category.id_comp (sch.map f)).trans (Category.comp_id (sch.map f)).symm
    · rw [Category.assoc, Category.assoc, abvRel_abvMap, eBm, eAm, opnMap_comp]
  have e : abvRel P.U (sch.map f) (sch.map (f ≫ g)) (sch.map g) h = eB.inv ≫ opnMap f _ _ hle ≫ eA.hom := by
    rw [Iso.eq_inv_comp, sq]
  rw [e]
  exact exc_comp q (exc_iso q eB.symm) (exc_comp q ind (exc_iso q eA))

end LateralTheory.CohomologicalPurity.TubeCut
end
end
