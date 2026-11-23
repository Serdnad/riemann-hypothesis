module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle019
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Development.EtaleCohomology.CohomologicalPurity.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def UtsR (m : ℕ) : CommRingCat.{0} ⥤ Type where
  obj A := Fin m → Aˣ
  map f := TypeCat.ofHom fun u i => Units.map f.hom.toMonoidHom (u i)
  map_id A := by ext u i; rfl
  map_comp f g := by ext u i; rfl

def Uts (m : ℕ) : Scheme.{0}ᵒᵖ ⥤ Type := Scheme.Γ ⋙ UtsR m

def evP (n : SimplexCategoryᵒᵖ) (A B : Spc) : (A ⨯ B).obj n ≅ A.obj n ⨯ B.obj n :=
  PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ (Scheme.{0}ᵒᵖ ⥤ Type)).obj n) A B

@[reassoc] theorem evalProdIso_hom_naturality (n : SimplexCategoryᵒᵖ) {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') :
    (prod.map f g).app n ≫ (evP n A' B').hom = (evP n A B).hom ≫ prod.map (f.app n) (g.app n) := by
  simp only [evP, PreservesLimitPair.iso_hom]
  exact prodComparison_natural ((evaluation SimplexCategoryᵒᵖ (Scheme.{0}ᵒᵖ ⥤ Type)).obj n) f g

def LeafNerveSplit : Prop := ∀ (d : ℕ) (n : SimplexCategoryᵒᵖ),
  ∃ (a₁ : (Pj (d + 1) 1).obj n ≅ (Pj (d + 1) 1).obj (op (SimplexCategory.mk 0)) ⨯ Uts n.unop.len)
    (a₀ : (Pj d 0).obj n ≅ (Pj d 0).obj (op (SimplexCategory.mk 0)) ⨯ Uts n.unop.len),
    (Pj.tail d).app n ≫ a₀.hom = a₁.hom ≫ prod.map ((Pj.tail d).app (op (SimplexCategory.mk 0))) (𝟙 _)

def LeafUnitsRep : Prop := ∀ (R : Type) [CommRing R] (m : ℕ),
  ∃ (R' : Type) (_ : CommRing R') (_ : R →+* R'),
    Nonempty (Uts m ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (Spec (CommRingCat.of R')))

theorem evalProdIso_inv_naturality (n : SimplexCategoryᵒᵖ) {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') :
    (evP n A B).inv ≫ (prod.map f g).app n = prod.map (f.app n) (g.app n) ≫ (evP n A' B').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← evalProdIso_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem LeafTailNerve_of (hN : LeafNerveSplit) (hU : LeafUnitsRep) : LeafTailNerve := by
  intro d R _ n
  obtain ⟨R', _, ψ, ⟨r⟩⟩ := hU R n.unop.len
  obtain ⟨a₁, a₀, w⟩ := hN d n
  let r' : Uts n.unop.len ⨯ (sp R).obj n ≅ (sp R').obj (op (SimplexCategory.mk 0)) := r
  let f₁ : (PR (d + 1) 1 R).obj n ≅ (PR (d + 1) 1 R').obj (op (SimplexCategory.mk 0)) :=
    evP n _ _ ≪≫ prod.mapIso a₁ (Iso.refl _) ≪≫ prod.associator _ _ _ ≪≫ prod.mapIso (Iso.refl _) r' ≪≫
      (evP (op (SimplexCategory.mk 0)) (Pj (d + 1) 1) (sp R')).symm
  let f₀ : (PR d 0 R).obj n ≅ (PR d 0 R').obj (op (SimplexCategory.mk 0)) :=
    evP n _ _ ≪≫ prod.mapIso a₀ (Iso.refl _) ≪≫ prod.associator _ _ _ ≪≫ prod.mapIso (Iso.refl _) r' ≪≫
      (evP (op (SimplexCategory.mk 0)) (Pj d 0) (sp R')).symm
  have w1 : (Pj.tail d).app n ≫ a₀.hom ≫ prod.fst = a₁.hom ≫ prod.fst ≫ (Pj.tail d).app (op (SimplexCategory.mk 0)) := by
    rw [reassoc_of% w]; simp
  have w2 : (Pj.tail d).app n ≫ a₀.hom ≫ prod.snd = a₁.hom ≫ prod.snd := by
    rw [reassoc_of% w]; simp
  refine ⟨R', inferInstance, ψ, f₁, f₀, ?_⟩
  simp only [f₁, f₀, Iso.trans_hom, Iso.symm_hom, prod.mapIso_hom, Iso.refl_hom, Category.assoc]
  erw [evalProdIso_inv_naturality, evalProdIso_hom_naturality_assoc]
  congr 1
  simp only [← Category.assoc]
  congr 1
  apply prod.hom_ext
  · simp [w1, w2]
  · simp [w1, w2]

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

abbrev Uo (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)) : Scheme.{0} :=
  (off (MvPolynomial (Fin d) R) I).toScheme

abbrev Gm : Scheme.{0} := Spec (CommRingCat.of (LaurentPolynomial ℤ))

def gmU (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)) : Uo d R I ⨯ Gm ⟶ Uo d R I := prod.fst

def LeafWGm : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)),
  Smooth (gmU d R I) ∧ Surjective (gmU d R I)

def LeafWTors : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)),
  Ideal.span (Set.range MvPolynomial.X) = I →
  ∃ e : pullback (wb d R) (pr d R).hom ≅ cech (gmU d R I),
  ∀ g : (opn (off (MvPolynomial (Fin d) R) I)).left ⟶ pullback (wb d R) (pr d R).hom,
  g ≫ pullback.fst _ _ = (opn (off (MvPolynomial (Fin d) R) I)).hom ≫ wa d R → g ≫ e.hom ≫ cechAug (gmU d R I) = 𝟙 _

theorem eqv_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem eqv_comp (R : Type) [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : ⇑(pull R (f ≫ g) F n) = ⇑(pull R f F n) ∘ ⇑(pull R g F n) := funext fun x => pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_of_section (R : Type) [CommRing R] {E E' : Spc} (g : E ⟶ E') (s : E' ⟶ E) (F : Shv R)
    (h : g ≫ s = 𝟙 _) (hs : Eqv R s F) : Eqv R g F := by
  intro n
  have hid : ∀ x, pull R g F n (pull R s F n x) = x := fun x => by rw [← pull_comp, h, pull_id]
  have hsurj : Function.Surjective (pull R g F n) := fun x => ⟨_, hid x⟩
  refine ⟨fun a b hab => ?_, hsurj⟩
  obtain ⟨a', rfl⟩ := (hs n).2 a
  obtain ⟨b', rfl⟩ := (hs n).2 b
  rw [hid, hid] at hab; rw [hab]

theorem LeafWEqvL_of (hGm : LeafWGm) (hT : LeafWTors) : LeafWEqvL := by
  intro hH q _ d R _ I hI hq g hg i
  obtain ⟨e, he⟩ := hT d R I hI
  obtain ⟨hsm, hsu⟩ := hGm d R I
  have hA2 : Eqv _ (cechAug (gmU d R I)) (tw q i) := hH.2.1 _ (gmU d R I) (tw q i)
  exact eqv_of_section _ g _ _ (he g hg) (eqv_comp _ _ _ _ (eqv_of_iso _ e _) hA2)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def Vo (N k : ℕ) : PSh := vecCat N k ⋙ Cat.objects

def voTail (d : ℕ) : Vo (d + 1) 1 ⟶ Vo d 0 where
  app U := TypeCat.ofHom fun v => (Vec.tail d U.unop).obj v
  naturality _ _ _ := rfl

def nerve0 (N k : ℕ) : (Pj N k).obj (op (SimplexCategory.mk 0)) ≅ Vo N k :=
  NatIso.ofComponents (fun U =>
    { hom := TypeCat.ofHom fun (F : ComposableArrows (Vec N k U.unop) 0) => F.obj 0
      inv := TypeCat.ofHom fun v => ComposableArrows.mk₀ (C := Vec N k U.unop) v
      hom_inv_id := by
        ext F
        exact ComposableArrows.ext₀ rfl
      inv_hom_id := rfl })
    (fun _ => rfl)

def LeafRepVec : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : Vo (d + 1) 1 ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (off (Polynomial A) (I.map Polynomial.C)).toScheme)
      (e₂ : Vo d 0 ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (off A I).toScheme),
      prod.map (voTail d) (𝟙 _) ≫ e₂.hom =
        e₁.hom ≫ yoneda.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

theorem LeafTailRep0_of_vec (hV : LeafRepVec) : LeafTailRep0 := by
  intro d R _
  obtain ⟨A, _, I, φ, hI, h, f₁, f₂, w⟩ := hV d R
  let E := (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk 0))
  let sq : E.obj (sp R) ≅ yoneda.obj (Spec (CommRingCat.of R)) := Iso.refl _
  refine ⟨A, inferInstance, I, φ, hI, h,
    PreservesLimitPair.iso E _ _ ≪≫ prod.mapIso (nerve0 (d + 1) 1) sq ≪≫ f₁,
    PreservesLimitPair.iso E _ _ ≪≫ prod.mapIso (nerve0 d 0) sq ≪≫ f₂, ?_⟩
  simp only [Iso.trans_hom, PreservesLimitPair.iso_hom, prod.mapIso_hom, Category.assoc]
  change E.map (prod.map _ _) ≫ _ = _
  rw [prodComparison_natural_assoc, prod.map_map_assoc, ← w, prod.map_map_assoc]
  rfl

def LeafRepPt : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (E₁ : ∀ U : Scheme.{0}, Vec (d + 1) 1 U × (U ⟶ Spec (CommRingCat.of R)) ≃
        (U ⟶ (off (Polynomial A) (I.map Polynomial.C)).toScheme))
      (E₂ : ∀ U : Scheme.{0}, Vec d 0 U × (U ⟶ Spec (CommRingCat.of R)) ≃ (U ⟶ (off A I).toScheme)),
      (∀ {V U : Scheme.{0}} (f : V ⟶ U) v g, E₁ V ((Vec.map _ _ f).obj v, f ≫ g) = f ≫ E₁ U (v, g)) ∧
      (∀ {V U : Scheme.{0}} (f : V ⟶ U) v g, E₂ V ((Vec.map _ _ f).obj v, f ≫ g) = f ≫ E₂ U (v, g)) ∧
      ∀ (U : Scheme.{0}) v g, E₂ U ((Vec.tail d U).obj v, g) =
        E₁ U (v, g) ≫ (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h

def isoOfPt {F G : PSh} {X : Scheme.{0}} (E : ∀ U : Scheme.{0}, F.obj (op U) × G.obj (op U) ≃ (U ⟶ X))
    (hE : ∀ {V U : Scheme.{0}} (f : V ⟶ U) a b, E V (F.map f.op a, G.map f.op b) = f ≫ E U (a, b)) :
    F ⨯ G ≅ yoneda.obj X :=
  FunctorToTypes.binaryProductIso F G ≪≫
    NatIso.ofComponents (fun U => (E U.unop).toIso) (fun f => by
      ext ⟨a, b⟩
      exact hE f.unop a b)

theorem LeafRepVec_of (hP : LeafRepPt) : LeafRepVec := by
  intro d R _
  obtain ⟨A, _, I, φ, hI, h, E₁, E₂, n₁, n₂, sq⟩ := hP d R
  refine ⟨A, inferInstance, I, φ, hI, h, isoOfPt (F := Vo (d + 1) 1) E₁ (fun f a b => n₁ f a b),
    isoOfPt (F := Vo d 0) E₂ (fun f a b => n₂ f a b), ?_⟩
  have key : prod.map (voTail d) (𝟙 (yoneda.obj (Spec (CommRingCat.of R)))) ≫
      (FunctorToTypes.binaryProductIso _ _).hom = (FunctorToTypes.binaryProductIso _ _).hom ≫
      FunctorToTypes.prod.lift (FunctorToTypes.prod.fst ≫ voTail d) FunctorToTypes.prod.snd := by
    apply (cancel_mono (FunctorToTypes.binaryProductIso _ _).inv).1
    apply Limits.prod.hom_ext <;> simp <;> rw [← Category.assoc, FunctorToTypes.binaryProductIso_hom_comp_fst]
  simp only [isoOfPt, Iso.trans_hom]
  rw [reassoc_of% key, Category.assoc]
  congr 1
  ext U ⟨v, g⟩
  exact sq U.unop v g

theorem LeafTailRep0_of (hP : LeafRepPt) : LeafTailRep0 := LeafTailRep0_of_vec (LeafRepVec_of hP)

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC AlgebraicGeometry CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.EquivalenceOfExcision
variable (R : Type) [CommRing R]
instance i1 : PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1, 0} R)) :=
  haveI := (ModuleCat.adj (ULift.{1, 0} R)).leftAdjoint_preservesColimits; inferInstance
instance i2 : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free freeP; infer_instance
instance i3 : PreservesColimitsOfShape WalkingSpan (chainsN R) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  have e : chainsN R ⋙ HomologicalComplex.eval _ _ n ≅
      (evaluation SimplexCategoryᵒᵖ PSh).obj (Opposite.op (SimplexCategory.mk n)) ⋙ free R :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  exact preservesColimitsOfShape_of_natIso e.symm
instance i4 : PreservesColimitsOfShape WalkingSpan (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro m
  by_cases hm : ∃ k, ComplexShape.embeddingDownNat.f k = m
  · obtain ⟨k, hk⟩ := hm
    have e : ComplexShape.embeddingDownNat.extendFunctor (Shv R) ⋙ HomologicalComplex.eval _ _ m ≅
        HomologicalComplex.eval _ _ k :=
      NatIso.ofComponents (fun K => K.extendXIso _ hk) (by
        intro K L φ
        change (HomologicalComplex.extendMap φ _).f m ≫ (L.extendXIso _ hk).hom = (K.extendXIso _ hk).hom ≫ φ.f k
        rw [HomologicalComplex.extendMap_f φ _ hk]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    exact preservesColimitsOfShape_of_natIso e.symm
  · push Not at hm
    have hz : ∀ K : ChainComplex (Shv R) ℕ,
        IsZero ((ComplexShape.embeddingDownNat.extendFunctor (Shv R) ⋙ HomologicalComplex.eval _ _ m).obj K) :=
      fun K => K.isZero_extend_X _ m hm
    exact ⟨fun {K} => ⟨fun {c} _ => ⟨{
      desc := fun s => (hz _).to_ s.pt
      fac := fun s j => (hz _).eq_of_src _ _
      uniq := fun s _ _ => (hz _).eq_of_src _ _ }⟩⟩⟩
instance i5 : PreservesColimitsOfShape WalkingSpan (chains R) := by
  unfold chains; infer_instance

theorem hkc (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  unfold HK.pull HK.pre
  simp only [cpre]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]
theorem hki (R : Type) [CommRing R] {K : Cx R} (F : Shv R) (n : ℤ) (x : HK R K F n) :
    HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  unfold HK.pull HK.pre
  simp only [cpre]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem hkc' (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := hkc R f g F n x

section
variable {P' P : Arrow Spc} (φ : P' ⟶ P)
open LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut

abbrev jj : P.right ⟶ MM φ := pushout.inr P'.hom (P'.hom ≫ φ.right)
abbrev ii : P'.right ⟶ MM φ := pushout.inl P'.hom (P'.hom ≫ φ.right)
def rr : MM φ ⟶ P.right :=
  pushout.desc (f := P'.hom) (g := P'.hom ≫ φ.right) φ.right (𝟙 _) (by simp)
def hh : dbl P' ⟶ MM φ :=
  pushout.desc (f := P'.hom) (g := P'.hom) (ii φ) (φ.right ≫ jj φ) (by
    exact (pushout.condition (f := P'.hom) (g := P'.hom ≫ φ.right)).trans
      (Category.assoc _ _ _))
abbrev Jr : Arrow Spc := Arrow.mk (jj φ)

theorem jr : jj φ ≫ rr φ = 𝟙 _ :=
  pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _

def ss : dbl (Jr φ) ⟶ MM φ :=
  pushout.desc (f := jj φ) (g := jj φ) (𝟙 _) (rr φ ≫ jj φ) (by
    rw [← Category.assoc, jr, Category.id_comp, Category.comp_id])

theorem j_gM : jj φ ≫ gM φ = dbl.inr P :=
  pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
theorem gM_fold : gM φ ≫ dbl.fold P = rr φ := by
  refine pushout.hom_ext (C := Spc) (f := P'.hom) (g := P'.hom ≫ φ.right) ?_ ?_
  · change (ii φ ≫ gM φ) ≫ dbl.fold P = ii φ ≫ rr φ
    have hM : ii φ ≫ gM φ = φ.right ≫ dbl.inl P :=
      pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
    have hfold : dbl.inl P ≫ dbl.fold P = 𝟙 P.right :=
      pushout.inl_desc (f := P.hom) (g := P.hom) _ _ _
    have hrr : ii φ ≫ rr φ = φ.right :=
      pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
    rw [hM, Category.assoc, hfold, Category.comp_id, hrr]
  · change (jj φ ≫ gM φ) ≫ dbl.fold P = jj φ ≫ rr φ
    rw [j_gM, dbl.inr_fold, jr]
theorem inl_h : dbl.inl P' ≫ hh φ = ii φ :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _
theorem inr_h : dbl.inr P' ≫ hh φ = φ.right ≫ jj φ :=
  pushout.inr_desc (f := P'.hom) (g := P'.hom) _ _ _
theorem h_gM : hh φ ≫ gM φ = dbl.map φ := by
  refine pushout.hom_ext (C := Spc) (f := P'.hom) (g := P'.hom) ?_ ?_
  · change (dbl.inl P' ≫ hh φ) ≫ gM φ = dbl.inl P' ≫ dbl.map φ
    have hM : ii φ ≫ gM φ = φ.right ≫ dbl.inl P :=
      pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
    have hmap : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
      pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _
    rw [inl_h, hM, hmap]
  · change (dbl.inr P' ≫ hh φ) ≫ gM φ = dbl.inr P' ≫ dbl.map φ
    rw [inr_h, Category.assoc, j_gM, dbl.inr_map]
theorem etale_mapping_cylinder_double_section_inl_comp : dbl.inl (Jr φ) ≫ ss φ = 𝟙 _ :=
  pushout.inl_desc (f := jj φ) (g := jj φ) _ _ _
theorem etale_mapping_cylinder_double_section_inr_comp : dbl.inr (Jr φ) ≫ ss φ = rr φ ≫ jj φ :=
  pushout.inr_desc (f := jj φ) (g := jj φ) _ _ _

theorem key (hR : LeafRel) (q : ℕ) (i n : ℤ) (y : Ht q (MM φ) n i)
    (h1 : pull _ (jj φ) (tw q i) n y = 0) (h2 : pull _ (hh φ) (tw q i) n y = 0) : y = 0 := by
  obtain ⟨e, he⟩ := hR q i
  have PO : IsPushout ((chains (ZMod q)).map P'.hom) ((chains (ZMod q)).map (P'.hom ≫ φ.right)) ((chains (ZMod q)).map (ii φ)) ((chains (ZMod q)).map (jj φ)) :=
    (IsPushout.of_hasPushout P'.hom (P'.hom ≫ φ.right)).map _
  let pM : (chains (ZMod q)).obj (MM φ) ⟶ cokernel ((chains (ZMod q)).map P'.hom) := PO.desc (cokernel.π ((chains (ZMod q)).map P'.hom)) 0 (by simp)
  have pM1 : (chains (ZMod q)).map (ii φ) ≫ pM = cokernel.π _ := PO.inl_desc _ _ _
  have pM2 : (chains (ZMod q)).map (jj φ) ≫ pM = 0 := PO.inr_desc _ _ _
  have wκ : (chains (ZMod q)).map P'.hom ≫ (chains (ZMod q)).map (ii φ) ≫ cokernel.π ((chains (ZMod q)).map (jj φ)) = 0 := by
    have hc : P'.hom ≫ ii φ = (P'.hom ≫ φ.right) ≫ jj φ := pushout.condition
    rw [← Category.assoc, ← (chains (ZMod q)).map_comp, hc, (chains (ZMod q)).map_comp, Category.assoc, cokernel.condition, comp_zero]
  let κ : cokernel ((chains (ZMod q)).map P'.hom) ⟶ cokernel ((chains (ZMod q)).map (Jr φ).hom) := cokernel.desc _ _ wκ
  let κ' : cokernel ((chains (ZMod q)).map (Jr φ).hom) ⟶ cokernel ((chains (ZMod q)).map P'.hom) := cokernel.desc ((chains (ZMod q)).map (jj φ)) pM pM2
  have hπ : pM ≫ κ = cokernel.π ((chains (ZMod q)).map (Jr φ).hom) := by
    apply PO.hom_ext
    · rw [← Category.assoc, pM1]; exact cokernel.π_desc _ _ _
    · rw [← Category.assoc, pM2, zero_comp]; exact (cokernel.condition _).symm
  have hκ : κ' ≫ κ = 𝟙 _ := by
    apply coequalizer.hom_ext
    rw [Category.comp_id]; exact (cokernel.π_desc_assoc _ _ _ _).trans hπ
  let s : Hs q (Jr φ) n i := ⟨pull _ (ss φ) _ n y, by
    change pull _ (dbl.inr (Jr φ)) _ n (pull _ (ss φ) _ n y) = 0
    rw [← pull_comp, etale_mapping_cylinder_double_section_inr_comp, pull_comp, h1, map_zero]⟩
  let x := (e (Jr φ) n).symm s
  have hx : (e (Jr φ) n x).1 = HK.pull _ ((chains (ZMod q)).map (ss φ) ≫ cokernel.π _) (tw q i) n x := by
    apply he
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, etale_mapping_cylinder_double_section_inl_comp, (chains (ZMod q)).map_id, Category.id_comp]
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, etale_mapping_cylinder_double_section_inr_comp, (chains (ZMod q)).map_comp, Category.assoc]
      erw [cokernel.condition, comp_zero]
  have hs : (e (Jr φ) n x).1 = pull _ (ss φ) _ n y := by simp [x, s]
  have hy : y = pull _ (dbl.inl (Jr φ)) _ n (pull _ (ss φ) _ n y) := by
    rw [← pull_comp, etale_mapping_cylinder_double_section_inl_comp, pull_id]
  have hp : (e P' n (HK.pull _ κ (tw q i) n x)).1 = HK.pull _ ((chains (ZMod q)).map (hh φ) ≫ pM) (tw q i) n (HK.pull _ κ (tw q i) n x) := by
    apply he
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, inl_h, pM1]
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, inr_h, (chains (ZMod q)).map_comp, Category.assoc, pM2, comp_zero]
  have hh0 : pull _ (hh φ) _ n y = HK.pull _ ((chains (ZMod q)).map (hh φ) ≫ pM) (tw q i) n (HK.pull _ κ (tw q i) n x) := by
    rw [← hkc', Category.assoc, hπ, hy, ← pull_comp, ← hs, hx]
    change HK.pull _ ((chains (ZMod q)).map _) _ n _ = _
    have hhs : hh φ ≫ dbl.inl (Jr φ) ≫ ss φ = hh φ := by rw [etale_mapping_cylinder_double_section_inl_comp]; exact Category.comp_id _
    rw [← hkc', ← Category.assoc, ← (chains (ZMod q)).map_comp, Category.assoc, hhs]
  have hz : HK.pull _ κ (tw q i) n x = 0 := by
    apply (e P' n).injective
    rw [map_zero]; apply Subtype.ext; rw [hp, ← hh0, h2]; rfl
  have hx0 : x = 0 := by
    rw [← hki _ (tw q i) n x, ← hκ, hkc', hz, map_zero]
  rw [hy, ← hs, hx0, map_zero]; rfl

end

end LateralTheory.CohomologicalPurity.EquivalenceOfExcision

namespace LateralTheory.CohomologicalPurity.TubeCut
open LateralTheory.CohomologicalPurity.EquivalenceOfExcision

theorem LeafEqvOfExc_of (hR : LeafRel) : LeafEqvOfExc := by
  intro q P' P φ hE i n
  open LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut in
  constructor
  · intro a b hab
    rw [← sub_eq_zero] at hab ⊢
    rw [← map_sub] at hab
    set x := a - b
    have h1 : pull _ (dbl.inr P) (tw q i) n x = 0 := by
      rw [← j_gM φ, pull_comp, hab, map_zero]
    have h2 : Hs.pull q φ n i ⟨x, h1⟩ = 0 := by
      apply Subtype.ext
      change pull _ (dbl.map φ) _ n x = 0
      rw [← h_gM φ, pull_comp, hab, map_zero]
    have := (hE n i).1 (h2.trans (map_zero _).symm)
    exact congrArg Subtype.val this
  · intro y
    set y0 := y - pull _ (rr φ) (tw q i) n (pull _ (jj φ) (tw q i) n y)
    have hy0 : pull _ (jj φ) (tw q i) n y0 = 0 := by
      simp only [y0, map_sub]; rw [← pull_comp, jr, pull_id, sub_self]
    let z : Hs q P' n i := ⟨pull _ (hh φ) _ n y0, by
      change pull _ (dbl.inr P') _ n (pull _ (hh φ) _ n y0) = 0
      rw [← pull_comp, inr_h, pull_comp, hy0, map_zero]⟩
    obtain ⟨x, hx⟩ := (hE n i).2 z
    have hd : pull _ (gM φ) (tw q i) n x.1 - y0 = 0 := by
      apply key φ hR q i n
      · rw [map_sub, ← pull_comp, j_gM, hy0, sub_zero]; exact x.2
      · rw [map_sub, ← pull_comp, h_gM, sub_eq_zero]; exact congrArg Subtype.val hx
    refine ⟨x.1 + pull _ (dbl.fold P) (tw q i) n (pull _ (jj φ) (tw q i) n y), ?_⟩
    rw [map_add (f := _), ← pull_comp, gM_fold, sub_eq_zero.mp hd]
    simp [y0]

end LateralTheory.CohomologicalPurity.TubeCut
end
end
