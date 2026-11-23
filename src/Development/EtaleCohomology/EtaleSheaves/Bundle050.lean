module

public import Development.EtaleCohomology.EtaleSheaves.Bundle035
public import Development.EtaleCohomology.EtaleSheaves.Bundle036
public import Development.EtaleCohomology.EtaleSheaves.Bundle037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.EtaleCohomology.TateTwists.Bundle007
public import Development.EtaleCohomology.EtaleSheaves.Bundle038
public import Development.EtaleCohomology.EtaleSheaves.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Lemma
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
open CategoryTheory Limits ZeroObject

namespace LateralTheory.E.trunc0Pf

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

lemma isZero_tr (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] (i : ℤ) (hi : i ≠ 0) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE 0)).X i) := by
  rcases lt_or_gt_of_ne hi with h | h
  · apply HomologicalComplex.isZero_stupidTrunc_X
    intro j; simp; omega
  · exact (K.isZero_of_isStrictlyLE 0 i h).of_iso
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := i.toNat) (by simp; omega))

lemma cochainComplex_singleFunctor_zero_map_f_zero {A B : C} (f : A ⟶ B) :
    ((CochainComplex.singleFunctor C 0).map f).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv :=
  HomologicalComplex.single_map_f_self _ _ f

def eIso (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE 0) ≅ (CochainComplex.singleFunctor C 0).obj (K.X 0) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => if h : i = 0 then (by
        subst h
        exact K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp) ≪≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).symm)
      else (isZero_tr K i h).iso (HomologicalComplex.isZero_single_obj_X _ 0 _ i h))
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      by_cases hj : j = 0
      · exact (isZero_tr K i (by omega)).eq_of_src _ _
      · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ j hj).eq_of_tgt _ _)

lemma stupidTruncGEZeroIsoSingle_hom_f_zero (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    (eIso K).hom.f 0 = (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp)).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).inv := by
  simp [eIso]

lemma nat {K L : CochainComplex C ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) :
    HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE 0) ≫ (eIso L).hom =
      (eIso K).hom ≫ (CochainComplex.singleFunctor C 0).map (g.f 0) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases h : i = 0
  · subst h
    simp only [HomologicalComplex.comp_f, stupidTruncGEZeroIsoSingle_hom_f_zero, cochainComplex_singleFunctor_zero_map_f_zero, Category.assoc, Iso.inv_hom_id_assoc]
    erw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ i h).eq_of_tgt _ _

theorem trunc0_of : LateralTheory.E.stupidPf.trunc0 := by
  intro R _ K L _ _ g
  exact ⟨eIso K, eIso L, nat g⟩

end LateralTheory.E.trunc0Pf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.SHLocPf

namespace LateralTheory.E.ColimPf

def Absorb : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (ψ : O →+* Ω), IE f ∧ ψ.comp f.hom = ι ∧
    (∀ x : O, ψ x ≠ 0 → IsUnit x) ∧
    ∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∀ φ : B →+* Ω, φ.comp g.hom = ι →
      ∃ h : B ⟶ O, g ≫ h = f ∧ ψ.comp h.hom = φ

def Rigid : Prop := ∀ (A B O : CommRingCat.{0}) (Ω : Type) [Field Ω] (ψ : O →+* Ω) (g : A ⟶ B), Et g →
  (∀ x : O, ψ x ≠ 0 → IsUnit x) → ∀ (u v : B ⟶ O), g ≫ u = g ≫ v → ψ.comp u.hom = ψ.comp v.hom → u = v

def Descend : Prop := ∀ (A O : CommRingCat.{0}) (f : A ⟶ O), IE f →
  ∀ (C : Type) [CommRing C] [Algebra O C] [Algebra.Etale O C],
  ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (d : B ⟶ O) (C' : CommRingCat.{0}) (e : B ⟶ C') (c : C' →+* C),
    Et g ∧ Et e ∧ g ≫ d = f ∧ c.comp e.hom = (algebraMap O C).comp d.hom ∧
    (∀ k : C' ⟶ O, e ≫ k = d → ∃ s : C →ₐ[O] O, s.toRingHom.comp c = k.hom) ∧
    (∀ (R : Type) [CommRing R] (α β : C →+* R), α.comp (algebraMap O C) = β.comp (algebraMap O C) →
      α.comp c = β.comp c → α = β)

theorem et_comp {A B C : CommRingCat.{0}} {g : A ⟶ B} {e : B ⟶ C} (hg : Et g) (he : Et e) : Et (g ≫ e) := by
  change (g ≫ e).hom.Etale
  rw [CommRingCat.hom_comp]
  exact RingHom.Etale.stableUnderComposition _ _ hg he

theorem Colim_of (hA : Absorb) (hR : Rigid) (hD : Descend) : Colim := by
  intro A Ω _ ι
  obtain ⟨O, f, ψ, hIE, hcomp, hloc, habs⟩ := hA A Ω ι
  refine ⟨O, f, ψ, hIE, hcomp, ?_⟩
  intro C _ _ _ χ hχ
  obtain ⟨B, g, d, C', e, c, hg, he, hgd, hce, hext, hgen⟩ := hD A O f hIE C
  have ce : ∀ y, c (e.hom y) = algebraMap O C (d.hom y) := fun y => DFunLike.congr_fun hce y
  have cχ : ∀ z, χ (algebraMap O C z) = ψ z := fun z => DFunLike.congr_fun hχ z
  have gd : ∀ x, d.hom (g.hom x) = f.hom x := fun x => by rw [← hgd]; rfl
  have hpt : (χ.comp c).comp (g ≫ e).hom = ι := by
    ext x
    simp only [RingHom.comp_apply, CommRingCat.hom_comp]
    rw [ce, cχ, gd, ← hcomp]; rfl
  obtain ⟨h, hh1, hh2⟩ := habs C' (g ≫ e) (et_comp hg he) (χ.comp c) hpt
  have hed : e ≫ h = d := by
    refine hR A B O Ω ψ g hg hloc (e ≫ h) d ?_ ?_
    · rw [← Category.assoc, hh1, hgd]
    · ext y
      have := DFunLike.congr_fun hh2 (e.hom y)
      simp only [RingHom.comp_apply, CommRingCat.hom_comp] at this ⊢
      rw [this, ce, cχ]
  obtain ⟨s, hs⟩ := hext h hed
  refine ⟨s, hgen Ω _ _ ?_ ?_⟩
  · ext x
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rw [cχ]; rfl
  · ext y
    have h1 := DFunLike.congr_fun hs y
    have h2 := DFunLike.congr_fun hh2 y
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]

end LateralTheory.E.ColimPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescIntPf

namespace LateralTheory.E.TruncationPieces

def RelK (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {K L : Cx R} (f : K ⟶ L) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (HK.pull R f F m)) ∧ Function.Injective (HK.pull R f F n)

def piece (R : Type) [CommRing R] {U E : Spc} (u : U ⟶ E) (p : ℕ) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (((chains R).obj U).X (-(p : ℤ))) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (((chains R).obj E).X (-(p : ℤ))) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (((chains R).map u).f (-(p : ℤ)))

def Piece : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (p : ℕ) (k : ℤ),
  RelZS R F k (disc.map (u.app (Opposite.op (SimplexCategory.mk p)))) → RelK R F (k + p) (piece R u p)

def Filt : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (n : ℤ),
  (∀ p : ℕ, RelK R F n (piece R u p)) → RelZS R F n u

theorem etale_relK_single_degree_pieces_of_piece_and_filtration (hP : Piece) (hF : Filt) : LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels := by
  intro R _ F U E u n hlow h0
  refine hF R F u n (fun p => ?_)
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have := hP R F u 0 n h0
    simpa using this
  · have hk : n - (p : ℤ) < n := by omega
    have := hP R F u p (n - p) (hlow p (n - p) hk)
    simpa using this

end LateralTheory.E.TruncationPieces
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescIntPf

namespace LateralTheory.E.CechSqPf

abbrev Ψ : CommRingCat.{0} ⥤ PShᵒᵖ := (Scheme.Spec ⋙ yoneda).rightOp

instance (n : ℕ) : PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ :=
  preservesColimitsOfShape_rightOp _ _

abbrev Sg {C D : CommRingCat.{0}} (g : C ⟶ D) : Spc := ((Arrow.mk g).cechConerve ⋙ Ψ).leftOp

abbrev ag {C D : CommRingCat.{0}} (g : C ⟶ D) : Sg g ⟶ sch.obj (Spec C) := lev Ψ (coAug g)

def sqHom {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') : Arrow.mk g ⟶ Arrow.mk (pushout.inr g φ') :=
  Arrow.homMk (u := φ') (v := pushout.inl g φ') pushout.condition.symm

theorem eqv_comp (R : Type) [CommRing R] (F : Shv R) {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'')
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := fun n => by
  have : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = (pull R f F n) ∘ (pull R g F n) := by
    funext x; exact pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

def IntegralSurjectiveRingCechAugmentationEtaleEqv : Prop := B4 → ∀ (q : ℕ) (i : ℤ) {C D : CommRingCat.{0}} (g : C ⟶ D), g.hom.IsIntegral → SpS g →
  IsUnit (q : C) → Eqv _ (cechAug (Spec.map g)) (tw q i)

def BaseChange : Prop := ∀ {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y'), g.hom.IsIntegral → SpS g →
  (pushout.inr g φ').hom.IsIntegral ∧ SpS (pushout.inr g φ')

def LevelPush : Prop := ∀ {A Y C D Y' : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) (w : Y ⟶ Y') (φ' : C ⟶ Y')
  (g : C ⟶ D), IsPushout φ c w φ' → ∀ n : SimplexCategory,
  IsPushout φ (c ≫ (coAug g).app n) (w ≫ (coAug (pushout.inr g φ')).app n) ((Arrow.mapCechConerve (sqHom g φ')).app n)

def LevelP : Prop := ∀ {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop), PushClosed P →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → ∀ n : SimplexCategory,
  P _ (c ≫ (coAug g).app n)

def Level0 : Prop := ∀ (q : ℕ) (i : ℤ) {A Y C D Y' : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) (w : Y ⟶ Y')
  (φ' : C ⟶ Y') (g : C ⟶ D), IsPushout φ c w φ' →
  ∃ (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : D ⟶ Z), IsPushout φ (c ≫ g) wz ψ ∧
    ∀ m, RelZ q i m ψ → RelZ q i m ((Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0))

theorem ag_eqv (q : ℕ) (i : ℤ) {C D : CommRingCat.{0}} (g : C ⟶ D)
    (h : Eqv _ (cechAug (Spec.map g)) (tw q i)) : Eqv _ (ag g) (tw q i) := by
  obtain ⟨e, he⟩ := LateralTheory.EtaleFoundations.etale_cech_conerve_image_iso_cech_nerve_of_preserves_wide_pushouts CommRingCat.{0} Ψ (fun n => inferInstance) C D g
  have h1 : (ag g) = e.hom ≫ cechAug (Spec.map g) := he
  rw [h1]
  exact eqv_comp _ _ _ _ (eqv_of_iso _ _ e) h

abbrev uMap {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') : Sg (pushout.inr g φ') ⟶ Sg g :=
  NatTrans.leftOp (Functor.whiskerRight (Arrow.mapCechConerve (sqHom g φ')) Ψ)

theorem u_sq {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') :
    uMap g φ' ≫ ag g = ag (pushout.inr g φ') ≫ sch.map (Spec.map φ') := by
  refine NatTrans.ext (funext fun n => ?_)
  have key : (coAug g).app n.unop ≫ (Arrow.mapCechConerve (sqHom g φ')).app n.unop =
      φ' ≫ (coAug (pushout.inr g φ')).app n.unop := by
    simp [coAug, sqHom]
    apply WidePushout.head_desc
  change (Ψ.map ((Arrow.mapCechConerve (sqHom g φ')).app n.unop)).unop ≫ (Ψ.map ((coAug g).app n.unop)).unop =
    (Ψ.map ((coAug (pushout.inr g φ')).app n.unop)).unop ≫ (Ψ.map φ').unop
  rw [← unop_comp, ← unop_comp, ← Ψ.map_comp, ← Ψ.map_comp, key]

theorem CechSq_of (h1 : IntegralSurjectiveRingCechAugmentationEtaleEqv) (h2 : BaseChange) (h3 : LevelPush) (h4 : LevelP) (h5 : Level0) : CechSq := by
  intro hH q _ i A Y φ hq P hP C D c g hCc hDc hgi hgs Y' w φ' hpo
  have hB4 : B4 := hH.2.2.2.2.2.2.2.2.1
  obtain ⟨hgi', hgs'⟩ := h2 g φ' hgi hgs
  have hqC : IsUnit (q : C) := by simpa using hq.map c.hom
  have hqY : IsUnit (q : Y') := by simpa using hqC.map φ'.hom
  refine ⟨_, _, uMap g φ', ag (pushout.inr g φ'), ag g, u_sq g φ', ag_eqv q i g (h1 hB4 q i g hgi hgs hqC),
    ag_eqv q i _ (h1 hB4 q i _ hgi' hgs' hqY), fun p => ?_, ?_⟩
  · exact ⟨_, c ≫ (coAug g).app (SimplexCategory.mk p), _, w ≫ (coAug (pushout.inr g φ')).app (SimplexCategory.mk p),
      _, h4 P hP c g hCc hDc _, h3 φ c w φ' g hpo _, fun m hm => hm⟩
  · obtain ⟨Z, wz, ψ, hpo0, hrel⟩ := h5 q i φ c w φ' g hpo
    exact ⟨Z, wz, ψ, hpo0, fun m hm => hrel m hm⟩

end LateralTheory.E.CechSqPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.ContStepPf

namespace LateralTheory.E.StepKPf

variable {J : Type} [SmallCategory J]

def lv (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J} (f : k ⟶ j0) :
    (D.obj k).Opens := (D.map f ≫ e.hom) ⁻¹ᵁ U

def lm {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) : c.pt.Opens :=
  (c.π.app j0 ≫ e.hom) ⁻¹ᵁ U

theorem lm_le {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J}
    (f : k ⟶ j0) : lm c e U ≤ (c.π.app k) ⁻¹ᵁ lv D e U f := by
  rw [lm, lv, ← Scheme.Hom.comp_preimage, ← Category.assoc, c.w f]

theorem lv_le (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : lv D e U (g ≫ f) ≤ (D.map g) ⁻¹ᵁ lv D e U f := by
  rw [lv, lv, ← Scheme.Hom.comp_preimage, ← Category.assoc, ← D.map_comp]

def rL {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J}
    (f : k ⟶ j0) : (lm c e U).toScheme ⟶ (lv D e U f).toScheme :=
  (c.π.app k).resLE _ _ (lm_le c e U f)

def rD (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : (lv D e U (g ≫ f)).toScheme ⟶ (lv D e U f).toScheme :=
  (D.map g).resLE _ _ (lv_le D e U f g)

def RC (q : ℕ) {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) : Prop :=
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj (lm c e U).toScheme) n i, ∃ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (lv D e U f).toScheme) n i), pull _ (sch.map (rL c e U f)) _ _ y = x) ∧
  ∀ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (lv D e U f).toScheme) n i), pull _ (sch.map (rL c e U f)) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map (rD D e U f g)) _ _ y = 0

def Restr : Prop := Hyp → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0})
  (e : D.obj j0 ≅ X) (U : X.Opens), IsCompact ((e.hom ⁻¹ᵁ U : (D.obj j0).Opens) : Set (D.obj j0)) →
  PC U.toScheme → RC q c e U

def DiagramChase₂ : Prop := Hyp → MV → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X) (U V : X.Opens), U ⊔ V = ⊤ →
  RC q c e U → RC q c e V → RC q c e (U ⊓ V) →
  ∀ (n i : ℤ) (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (D.obj k)) n i), pull _ (sch.map (c.π.app k)) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map (D.map g)) _ _ y = 0

theorem cpt_pre {Y X : Scheme.{0}} (e : Y ≅ X) (U : X.Opens) (hU : IsCompact (U : Set X)) :
    IsCompact ((e.hom ⁻¹ᵁ U : Y.Opens) : Set Y) :=
  (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isCompact_preimage.mpr hU

theorem StepK_of (hR : Restr) (hC : DiagramChase₂) : StepK := by
  intro h hmv X U V hU hV hUV pU pV pW q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i j y hy
  have := hqs j0
  have hU' := cpt_pre e U hU
  have hV' := cpt_pre e V hV
  have hW' : IsCompact ((e.hom ⁻¹ᵁ (U ⊓ V) : (D.obj j0).Opens) : Set (D.obj j0)) := by
    rw [Scheme.Hom.preimage_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ (e.hom ⁻¹ᵁ U).isOpen hU' (e.hom ⁻¹ᵁ V).isOpen hV'
  have rU := hR h q D c hc ha hcs hqs hu j0 X e U hU' pU
  have rV := hR h q D c hc ha hcs hqs hu j0 X e V hV' pV
  have rW := hR h q D c hc ha hcs hqs hu j0 X e (U ⊓ V) hW' pW
  let k := IsCofiltered.min j j0
  have hy' : pull _ (sch.map (c.π.app k)) _ _ (pull _ (sch.map (D.map (IsCofiltered.minToLeft j j0))) _ _ y) = 0 := by
    rw [← pull_comp, ← Functor.map_comp, c.w]; exact hy
  obtain ⟨l, g, hg⟩ := hC h hmv q D c hc j0 X e U V hUV rU rV rW n i k (IsCofiltered.minToRight j j0) _ hy'
  refine ⟨l, g ≫ IsCofiltered.minToLeft j j0, ?_⟩
  rw [D.map_comp, Functor.map_comp, pull_comp]; exact hg

end LateralTheory.E.StepKPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.StepSPf

def PO (q : ℕ) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D) (j0 : J) (W : (D.obj j0).Opens) : Prop :=
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj (c.π.app j0 ⁻¹ᵁ W).toScheme) n i, ∃ (k : J) (f : k ⟶ j0)
      (y : Ht q (sch.obj (D.map f ⁻¹ᵁ W).toScheme) n i),
      pull _ (sch.map ((c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, c.w]))) _ _ y = x) ∧
  ∀ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (D.map f ⁻¹ᵁ W).toScheme) n i),
    pull _ (sch.map ((c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, c.w]))) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map ((D.map g).resLE (D.map f ⁻¹ᵁ W) (D.map (g ≫ f) ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp]))) _ _ y = 0

def Restr : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X)
  (W : X.Opens), IsCompact (W : Set X) → PC W.toScheme → PO q D c j0 (e.hom ⁻¹ᵁ W)

def DiagramChase₂ : Prop := Hyp → MV → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X)
  (U V : X.Opens), U ⊔ V = ⊤ → PO q D c j0 (e.hom ⁻¹ᵁ U) → PO q D c j0 (e.hom ⁻¹ᵁ V) → PO q D c j0 (e.hom ⁻¹ᵁ (U ⊓ V)) →
  ∀ n i : ℤ, ∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x

theorem S_of_restr_chase (hR : Restr) (hC : DiagramChase₂) : LateralTheory.E.ContStepPf.StepS := by
  intro h hmv X U V hU hV hUV pU pV pW q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated e.inv
  have hW : IsCompact ((U ⊓ V : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU V.2 hV
  exact hC h hmv q D c hc ha hcs hqs hu j0 X e U V hUV (hR q D c hc ha hcs hqs hu j0 X e U hU pU)
    (hR q D c hc ha hcs hqs hu j0 X e V hV pV) (hR q D c hc ha hcs hqs hu j0 X e (U ⊓ V) hW pW) n i

theorem po_res_zero {q : ℕ} {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (A : Z.Opens) (B B' : Y.Opens) (hB : B = B')
    (h : B ≤ φ ⁻¹ᵁ A) (h' : B' ≤ φ ⁻¹ᵁ A) (n i : ℤ) (y : Ht q (sch.obj A.toScheme) n i) :
    pull _ (sch.map (φ.resLE A B h)) _ _ y = 0 → pull _ (sch.map (φ.resLE A B' h')) (tw q i) n y = 0 := by
  subst hB; exact id

theorem restr : Restr := by
  intro q J _ _ D c hc ha hcs hqs hu j0 X e W hWc pW
  have : ∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f) := ha
  set W' : (D.obj j0).Opens := e.hom ⁻¹ᵁ W with hW'def
  have hW' : IsCompact (W' : Set (D.obj j0)) := QuasiCompact.isCompact_preimage (f := e.hom) _ W.2 hWc
  have key := pW q (opensDiagram D j0 W') (opensCone D c j0 W') (isLimitOpensCone D c hc j0 W')
    (fun f => inferInstance)
    (fun j => isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := D.map j.hom) _ W'.2 hW'))
    (fun j => by have := hqs j.left; exact (D.map j.hom ⁻¹ᵁ W').ι.isOpenEmbedding.quasiSeparatedSpace)
    (fun j => by
      have h := (hu j.left).map ((D.map j.hom ⁻¹ᵁ W').ι.appTop.hom)
      simp only [map_natCast] at h
      exact h)
    (Over.mk (𝟙 j0)) ⟨(Scheme.isoOfEq _ (by simp [hW'def])) ≪≫ e.hom.preimageIso W⟩
  intro n i
  refine ⟨fun x => ?_, fun k f y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := (key n i).1 x
    exact ⟨j.left, j.hom, y, hy⟩
  · obtain ⟨k', g, hg⟩ := (key n i).2 (Over.mk f) y hy
    have hw : g.left ≫ f = k'.hom := Over.w g
    refine ⟨k'.left, g.left, ?_⟩
    exact po_res_zero (D.map g.left) _ _ _ (by rw [hw]) _ _ n i y hg

end LateralTheory.E.StepSPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigma_xy1Pf_Lev
open LateralTheory.E.CechSigmaProof

def sqS {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Arrow.mk (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j))) ⟶ Arrow.mk (cov O V hV) :=
  Arrow.homMk (Limits.Sigma.map fun j => g ∣_ V j) (g ∣_ O) (sq_cov g O V hV)

def wpMap {A B C D : Scheme.{0}} {p : A ⟶ B} {q : C ⟶ D} (s : Arrow.mk p ⟶ Arrow.mk q) (n : ℕ) :
    widePullback B (fun _ : Fin (n + 1) => A) (fun _ => p) ⟶ widePullback D (fun _ : Fin (n + 1) => C) (fun _ => q) :=
  WidePullback.lift (WidePullback.base _ ≫ s.right) (fun i => WidePullback.π _ i ≫ s.left)
    (fun i => by have := Arrow.w s; simp only [Arrow.mk_hom] at this; simp [this])

def CechYoneda : Prop := ∀ {A B C D : Scheme.{0}} {p : A ⟶ B} {q : C ⟶ D} (s : Arrow.mk p ⟶ Arrow.mk q) (n : ℕ),
  Nonempty (Arrow.mk ((Arrow.mapCechNerve (yoneda.mapArrow.map s)).app (op (SimplexCategory.mk n))) ≅
    Arrow.mk (yoneda.map (wpMap s n)))

def SchemeLevel : Prop := ∀ {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O)
  (n : ℕ), Nonempty (Arrow.mk (wpMap (sqS g O V hV) n) ≅
    Arrow.mk (Limits.Sigma.map fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k))))

theorem LevelIso_of (hY : CechYoneda) (hS : SchemeLevel) : LevelIso := by
  intro Y X g O ι V hV n
  obtain ⟨e1⟩ := hY (sqS g O V hV) n
  obtain ⟨e2⟩ := hS g O V hV n
  exact ⟨e1 ≪≫ yoneda.mapArrow.mapIso e2⟩

theorem CechSigma_of (hY : CechYoneda) (hS : SchemeLevel) : ZariskiLocalCech.CechSigma :=
  LateralTheory.E.CechSigmaProof.CechSigma_of (LevelIso_of hY hS)

end LateralTheory.E.CechSigma_xy1Pf_Lev
end
end
