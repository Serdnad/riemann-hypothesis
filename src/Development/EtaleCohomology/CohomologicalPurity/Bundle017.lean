module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
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

namespace LateralTheory.CohomologicalPurity.TubeCut
namespace PushPf

variable {J' J : Type} [SmallCategory J'] [SmallCategory J] {D' : J' ⥤ PSh} {D : J ⥤ PSh} {G : J' ⥤ J}

def phi (α : D' ⟶ G ⋙ D) (U : Scheme.{0}ᵒᵖ) : (D'.flip.obj U).Elements ⥤ (D.flip.obj U).Elements where
  obj e := (D.flip.obj U).elementsMk (G.obj e.obj) ((α.app e.obj).app U e.val)
  map {e e'} g := Functor.Elements.homMk (G.map g.hom) (by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality g.hom) U) e.val
    exact h.symm.trans (congrArg (fun y => (α.app e'.obj).app U y) g.map_val))
  map_id e := Functor.Elements.hom_ext (G.map_id e.obj)
  map_comp g g' := Functor.Elements.hom_ext (G.map_comp g.hom g'.hom)

theorem elem_ext {X : Type} [Category X] {F : J ⥤ Type} (A B : X ⥤ F.Elements) (ho : ∀ x, A.obj x = B.obj x)
    (hm : A ⋙ Functor.Elements.π F = B ⋙ Functor.Elements.π F) : A = B := by
  refine CategoryTheory.Functor.ext ho (fun x y g => ?_)
  apply (Functor.Elements.π F).map_injective
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hm g

theorem phi_nat (α : D' ⟶ G ⋙ D) {U U' : Scheme.{0}ᵒᵖ} (f : U ⟶ U') :
    phi α U ⋙ (D.flip.map f).mapElements = (D'.flip.map f).mapElements ⋙ phi α U' :=
  elem_ext _ _ (fun e => by
    refine Functor.Elements.ext _ _ rfl ?_
    change (D.flip.obj U').map (𝟙 (G.obj e.obj))
        ((D.obj (G.obj e.obj)).map f ((α.app e.obj).app U e.val)) =
      (α.app e.obj).app U' ((D'.obj e.obj).map f e.val)
    rw [(D.flip.obj U').map_id]
    exact (ConcreteCategory.congr_hom ((α.app e.obj).naturality f) e.val).symm) rfl

def bmap (α : D' ⟶ G ⋙ D) : hoc D' ⟶ hoc D where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => (chn x ⋙ phi α U : Fin (n.unop.len + 1) ⥤ _)
      naturality := fun U U' f => by
        ext x
        change (chn x ⋙ (D'.flip.map f).mapElements) ⋙ phi α U' = (chn x ⋙ phi α U) ⋙ (D.flip.map f).mapElements
        rw [Functor.assoc, Functor.assoc, phi_nat] }
  naturality n m θ := by
    ext U x
    rfl

theorem goal (α : D' ⟶ G ⋙ D) {Y' Y : PSh} (f : Y' ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y') (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, α.app j ≫ c (G.obj j) = c' j ≫ f) : bmap α ≫ aug c hc = aug c' hc' ≫ disc.map f := by
  ext n U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h ((chn x).obj 0).obj) U) ((chn x).obj 0).val

end PushPf

theorem LeafPush_of : LeafPush := fun _ _ _ _ _ _ _ α _ _ f c' c hc' hc h => ⟨PushPf.bmap α, PushPf.goal α f c' c hc' hc h⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem pull_iso_bij (R : Type) [CommRing R] {E E' : Spc} (i : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R i.hom F n) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R i.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, i.inv_hom_id, pull_id]
  · rw [← pull_comp, i.hom_inv_id, pull_id]

theorem eqv_of_arrowIso (R : Type) [CommRing R] {E' E G' G : Spc} {f : E' ⟶ E} {g : G' ⟶ G} (F : Shv R)
    (e : Arrow.mk f ≅ Arrow.mk g) (hf : Eqv R f F) : Eqv R g F := by
  intro n
  have w : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
  have k : (pull R e.hom.left F n) ∘ (pull R g F n) = (pull R f F n) ∘ (pull R e.hom.right F n) := by
    funext x
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, w]
  have hl : Function.Bijective (pull R e.hom.left F n) :=
    pull_iso_bij R ((Arrow.leftFunc).mapIso e) F n
  have hr : Function.Bijective (pull R e.hom.right F n) :=
    pull_iso_bij R ((Arrow.rightFunc).mapIso e) F n
  have hc : Function.Bijective ((pull R e.hom.left F n) ∘ (pull R g F n)) := by
    rw [k]; exact (hf n).comp hr
  exact (Function.Bijective.of_comp_iff' hl _).mp hc

theorem eqv_sum_RRelH (hS : LeafSum) (R : Type) [CommRing R] (F : Shv R) {A : Type} {E' E : A → Spc} (c' : Cofan E') (c : Cofan E)
    (hc' : Nonempty (IsColimit c')) (hc : Nonempty (IsColimit c)) (f : ∀ a, E' a ⟶ E a) (φ : c'.pt ⟶ c.pt)
    (hφ : ∀ a, c'.inj a ≫ φ = f a ≫ c.inj a) (hf : ∀ a, Eqv R (f a) F) : Eqv R φ F := by
  intro n
  have k : (fun (y : H R c'.pt F n) (a : A) => pull R (c'.inj a) F n y) ∘ (pull R φ F n) =
      (fun (z : ∀ a, H R (E a) F n) (a : A) => pull R (f a) F n (z a)) ∘
        (fun (x : H R c.pt F n) (a : A) => pull R (c.inj a) F n x) := by
    funext x a
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, hφ]
  have h1 := hS R F A E' c' hc' n
  have h2 := hS R F A E c hc n
  have hc3 : Function.Bijective ((fun (y : H R c'.pt F n) (a : A) => pull R (c'.inj a) F n y) ∘ (pull R φ F n)) := by
    rw [k]
    exact (Function.Bijective.piMap (fun a => hf a n)).comp h2
  exact (Function.Bijective.of_comp_iff' h1 _).mp hc3

def LeafRelLev : Prop := LeafLevel → ∀ (J : Type) [SmallCategory J] (D' D : J ⥤ PSh) (α : D' ⟶ D)
  (Y G : PSh) (g : G ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j)) (h' : (hocF J).map α ≫ aug c hc = aug c' hc')
  (n : SimplexCategoryᵒᵖ),
  ∃ (A : Type) (ι : A → J) (E' E : A → Spc) (k' : Cofan E') (k : Cofan E) (f : ∀ a, E' a ⟶ E a) (φ : k'.pt ⟶ k.pt),
    Nonempty (IsColimit k') ∧ Nonempty (IsColimit k) ∧ (∀ a, k'.inj a ≫ φ = f a ≫ k.inj a) ∧
    (∀ a, Nonempty (Arrow.mk (pbRel (disc.map g) (disc.map (α.app (ι a))) (disc.map (c' (ι a))) (disc.map (c (ι a)))
      (h (ι a))) ≅ Arrow.mk (f a))) ∧
    Nonempty (Arrow.mk φ ≅ Arrow.mk (disc.map ((pbRel (disc.map g) ((hocF J).map α) (aug c' hc') (aug c hc) h').app n)))

theorem LeafRelHoc_of (hL : LeafLevel) (hS : LeafSum) (hB : LeafRelLev) : LeafRelHoc := by
  intro hA3 R _ F J _ D' D α Y G g c' c hc' hc h h' hE
  apply hA3
  intro n
  obtain ⟨A, ι, E', E, k', k, f, φ, h1, h2, h3, h4, ⟨e⟩⟩ := hB hL J D' D α Y G g c' c hc' hc h h' n
  refine eqv_of_arrowIso R F e ?_
  exact eqv_sum_RRelH hS R F k' k h1 h2 f φ h3 fun a => eqv_of_arrowIso R F (h4 a).some (hE (ι a))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafChPush : Prop := ∀ (q : ℕ) (P : Arrow Spc),
  IsPushout ((chains (ZMod q)).map P.hom) ((chains (ZMod q)).map P.hom) ((chains (ZMod q)).map (dbl.inl P))
    ((chains (ZMod q)).map (dbl.inr P))

def LeafHKSplit : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B D : Cx R} (f : A ⟶ B) (l r : B ⟶ D)
  (s : D ⟶ B), IsPushout f f l r → r ≫ s = 𝟙 _ → ∀ p : D ⟶ cokernel f, l ≫ p = cokernel.π f → r ≫ p = 0 →
  Function.Injective (HK.pull R p F n) ∧ ∀ x, HK.pull R r F n x = 0 → ∃ y, HK.pull R p F n y = x

theorem hk_pull_pull {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R f F n (HK.pull R g F n x) = HK.pull R (f ≫ g) F n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem hk_pull_zero {R : Type} [CommRing R] {K L : Cx R} (F : Shv R) (n : ℤ) (x : HK R L F n) :
    HK.pull R (0 : K ⟶ L) F n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [← CohomologyClass.mk_zero]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem LeafRel_of (h1 : LeafChPush) (h2 : LeafHKSplit) : LeafRel := by
  intro q i
  have ex : ∀ P : Arrow Spc, ∃ p : (chains (ZMod q)).obj (dbl P) ⟶ cokernel ((chains (ZMod q)).map P.hom),
      (chains _).map (dbl.inl P) ≫ p = cokernel.π _ ∧ (chains _).map (dbl.inr P) ≫ p = 0 := fun P =>
    ⟨(h1 q P).desc (cokernel.π _) 0 (by simp), (h1 q P).inl_desc _ _ _, (h1 q P).inr_desc _ _ _⟩
  choose p hl hr using ex
  have hs : ∀ P : Arrow Spc, (chains (ZMod q)).map (dbl.inr P) ≫ (chains _).map (dbl.fold P) = 𝟙 _ := fun P => by
    rw [← Functor.map_comp, dbl.inr_fold, CategoryTheory.Functor.map_id]
  have mem : ∀ (P : Arrow Spc) (n : ℤ) x, HK.pull _ (p P) (tw q i) n x ∈ Hs q P n i := fun P n x => by
    change HK.pull _ ((chains _).map (dbl.inr P)) (tw q i) n (HK.pull _ (p P) (tw q i) n x) = 0
    rw [hk_pull_pull, hr, hk_pull_zero]
  refine ⟨fun P n => AddEquiv.ofBijective ((HK.pull _ (p P) (tw q i) n).codRestrict _ (mem P n)) ⟨fun x y h => ?_, fun x => ?_⟩,
    fun P n p' hl' hr' x => ?_⟩
  · exact (h2 _ (tw q i) n _ _ _ _ (h1 q P) (hs P) (p P) (hl P) (hr P)).1 (congrArg Subtype.val h)
  · obtain ⟨y, hy⟩ := (h2 _ (tw q i) n _ _ _ _ (h1 q P) (hs P) (p P) (hl P) (hr P)).2 x.1 x.2
    exact ⟨y, Subtype.ext hy⟩
  · have e : p' = p P := (h1 q P).hom_ext (hl'.trans (hl P).symm) (hr'.trans (hr P).symm)
    subst e; rfl

end LateralTheory.CohomologicalPurity.TubeCut
end
end
