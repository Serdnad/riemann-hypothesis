module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.EtaleCohomology.WeilConjectures.Bundle002
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Comma.LocallySmall
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.EtaleCohomology.EtaleSheaves.Bundle003

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Aff

structure RF where
  obj : ∀ (A : Type) [CommRing A], Type
  map : ∀ {A B : Type} [CommRing A] [CommRing B], (A →+* B) → obj A → obj B
  map_id : ∀ {A : Type} [CommRing A] (x : obj A), map (RingHom.id A) x = x
  map_comp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) (x : obj A),
    map (g.comp f) x = map g (map f x)
  rel : ∀ {A : Type} [CommRing A], obj A → obj A → Prop
  map_rel : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x y : obj A}, rel x y → rel (map f x) (map f y)

structure RF.Hom (X Y : RF) where
  app : ∀ (A : Type) [CommRing A], X.obj A → Y.obj A
  nat : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : X.obj A), app B (X.map f x) = Y.map f (app A x)

def RF.Hom.Rel {X Y : RF} (h : X.Hom Y) : Prop :=
  ∀ {A : Type} [CommRing A] {x y : X.obj A}, X.rel x y → Y.rel (h.app A x) (h.app A y)

def CN (X : RF) : Spc where
  obj n :=
    { obj := fun U => {x : Fin (n.unop.len + 1) → X.obj Γ(U.unop, ⊤) // ∀ i j, X.rel (x i) (x j)}
      map := fun f => TypeCat.ofHom fun x =>
        ⟨fun i => X.map f.unop.appTop.hom (x.1 i), fun i j => X.map_rel _ (x.2 i j)⟩
      map_id := fun U => by
        ext x i
        exact X.map_id (x.1 i)
      map_comp := fun f g => by
        ext x i
        exact X.map_comp f.unop.appTop.hom g.unop.appTop.hom (x.1 i) }
  map θ :=
    { app := fun U => TypeCat.ofHom fun x => ⟨fun i => x.1 (θ.unop.toOrderHom i), fun i j => x.2 _ _⟩
      naturality := fun U V f => rfl }
  map_id n := rfl
  map_comp θ θ' := rfl

def CN.map {X Y : RF} (h : X.Hom Y) (hr : h.Rel) : CN X ⟶ CN Y where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => ⟨fun i => h.app _ (x.1 i), fun i j => hr (x.2 i j)⟩
      naturality := fun U V f => by
        refine ConcreteCategory.hom_ext _ _ fun x => Subtype.ext (funext fun i => ?_)
        exact h.nat f.unop.appTop.hom (x.1 i) }
  naturality n m θ := rfl

def RF.sub (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) : RF where
  obj A _ := {x : X.obj A // P x}
  map f x := ⟨X.map f x.1, hP f x.2⟩
  map_id x := Subtype.ext (X.map_id x.1)
  map_comp f g x := Subtype.ext (X.map_comp f g x.1)
  rel x y := X.rel x.1 y.1
  map_rel f _ _ h := X.map_rel f h

def RF.subι (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) :
    (X.sub P hP).Hom X where
  app _ _ x := x.1
  nat _ _ := rfl

theorem RF.subι_rel (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) :
    (X.subι P hP).Rel := fun h => h

variable (D : Type) [CommRing D]

def Vec (N : ℕ) : RF where
  obj A _ := {x : (D →+* A) × (Fin N → A) // Ideal.span (Set.range x.2) = ⊤}
  map f x := ⟨(f.comp x.1.1, f ∘ x.1.2), by rw [Set.range_comp, ← Ideal.map_span, x.2, Ideal.map_top]⟩
  map_id _ := rfl
  map_comp _ _ _ := rfl
  rel {A} _ x y := x.1.1 = y.1.1 ∧ ∃ u : Aˣ, x.1.2 = fun j => (u : A) * y.1.2 j
  map_rel {A B} _ _ f x y h := by
    obtain ⟨h1, u, h2⟩ := h
    refine ⟨congrArg f.comp h1, Units.map (f : A →* B) u, funext fun j => ?_⟩
    simp [h2]

variable {D}

def P2 {d : ℕ} {A : Type} [CommRing A] (x : (Vec D (d + 1)).obj A) : Prop :=
  Ideal.span (Set.range fun j : Fin d => x.1.2 j.castSucc) = ⊤

def P1 {d : ℕ} {A : Type} [CommRing A] (x : (Vec D (d + 1)).obj A) : Prop := IsUnit (x.1.2 (Fin.last d))

theorem second_property_map {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : (Vec D (d + 1)).obj A} (h : P2 x) :
    P2 ((Vec D (d + 1)).map f x) := by
  have : (Set.range fun j : Fin d => ((Vec D (d + 1)).map f x).1.2 j.castSucc) =
      f '' (Set.range fun j : Fin d => x.1.2 j.castSucc) := by
    rw [← Set.range_comp]; rfl
  rw [P2, this, ← Ideal.map_span, h, Ideal.map_top]

theorem first_property_map {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : (Vec D (d + 1)).obj A} (h : P1 x) :
    P1 ((Vec D (d + 1)).map f x) := h.map f

variable (D)

abbrev L2 (d : ℕ) : RF := (Vec D (d + 1)).sub P2 second_property_map

abbrev L1 (d : ℕ) : RF := (Vec D (d + 1)).sub P1 first_property_map

def fstV (d : ℕ) : (L2 D d).Hom (Vec D d) where
  app _ _ x := ⟨(x.1.1.1, fun j => x.1.1.2 j.castSucc), x.2⟩
  nat _ _ := rfl


section Formal
open LateralTheory.E.t_E6Cut
variable {R : Type} [CommRing R] (F : Shv R)

end Formal

end UpperTheory.Aff

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Cb

open LateralTheory.EWeil.AcycPf

private lemma exact_filtered (R : Type) [CommRing R] (J : Type 1) [Category.{0} J] [IsFiltered J] :
    HasExactColimitsOfShape J (ModuleCat.{1} (ULift.{1} R)) := by
  let e : J ≌ ULiftHom.{1} J := ULiftHom.equiv
  haveI : IsFiltered (ULiftHom.{1} J) := IsFiltered.of_equivalence e
  exact HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{1} (ULift.{1} R)) e.symm

private lemma mono_of_isColimit {J : Type 1} [Category.{0} J] {A : Type 2} [Category.{1} A] [Abelian A]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] {K L : J ⥤ A} (τ : K ⟶ L) [Mono τ]
    {c : Cocone K} {d : Cocone L} (hc : IsColimit c) (hd : IsColimit d) (m : c.pt ⟶ d.pt)
    (hm : ∀ j, c.ι.app j ≫ m = τ.app j ≫ d.ι.app j) : Mono m := by
  have key : m = (hc.coconePointUniqueUpToIso (colimit.isColimit K)).hom ≫ colimMap τ ≫
      (hd.coconePointUniqueUpToIso (colimit.isColimit L)).inv := by
    refine hc.hom_ext fun j => ?_
    simp [hm]
  have hτ : Mono (colim.map τ) := inferInstance
  have hτ' : Mono (colimMap τ) := hτ
  rw [key]
  infer_instance

private lemma lan_mono {C D : Type 1} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) [RepresentablyFlat G]
    {A : Type 2} [Category.{1} A] [Abelian A]
    [∀ X, HasColimitsOfShape (CostructuredArrow G.op X) A]
    (hA : ∀ (J : Type 1) [Category.{0} J] [IsFiltered J] [HasColimitsOfShape J A], HasExactColimitsOfShape J A)
    {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) [Mono φ] : Mono ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ) := by
  have hφ : ∀ c, Mono (φ.app c) := fun c => inferInstance
  have key : ∀ X, Mono (((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X) := by
    intro X
    haveI : IsFiltered (CostructuredArrow G.op X) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence G (unop X))
    haveI := hA (CostructuredArrow G.op X)
    haveI : ∀ j, Mono ((Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ).app j) :=
      fun j => hφ _
    haveI : Mono (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ) :=
      NatTrans.mono_of_mono_app _
    refine mono_of_isColimit (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ)
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op P X)
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op Q X) _ ?_
    intro j
    have h₂ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app (G.op.obj j.left) =
        φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left :=
      (congr_app (G.op.lanUnit.naturality φ) j.left).symm
    have h₃ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj P).map j.hom ≫
        ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X =
        φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj Q).map j.hom := by
      rw [NatTrans.naturality, reassoc_of% h₂]
    first
      | exact (Category.assoc _ _ _).trans h₃
      | (dsimp only [Functor.LeftExtension.coconeAt_ι_app, Functor.whiskerLeft_app]
         simpa only [Category.assoc] using h₃)
  exact NatTrans.mono_of_mono_app _

set_option backward.isDefEq.respectTransparency false in
private lemma incl_flat (S : Scheme.{0}) : RepresentablyFlat (incl S) := by
  have : PreservesFiniteLimits (incl S) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Etale.forget S))
  exact flat_of_preservesFiniteLimits _

set_option backward.isDefEq.respectTransparency false in
private lemma incl_cont (S : Scheme.{0}) :
    (incl S).IsContinuous S.smallEtaleTopology (Scheme.etaleTopology.over S) := by
  have := incl_flat S
  haveI : (incl S).Full := inferInstanceAs (Scheme.Etale.forget S).Full
  haveI : (incl S).Faithful := inferInstanceAs (Scheme.Etale.forget S).Faithful
  haveI : (incl S).LocallyCoverDense (Scheme.etaleTopology.over S) :=
    Scheme.locallyCoverDense_of_le (P := @Etale) S le_rfl
  rw [Functor.isContinuous_iff_coverPreserving]
  exact Functor.coverPreserving_restrictedTopology (incl S) (Scheme.etaleTopology.over S)

private lemma restr_inj : RestrInj := by
  intro R _ S G _
  haveI := incl_cont S
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (incl S)
    (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology (Scheme.etaleTopology.over S)
  haveI : (Functor.sheafPullbackConstruction.sheafPullback (incl S) (ModuleCat.{1} (ULift.{1} R))
      S.smallEtaleTopology (Scheme.etaleTopology.over S)).PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    haveI := incl_flat S
    haveI : Mono ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f) :=
      inferInstance
    haveI : Mono (((incl S).op.lan : _ ⥤ (Over S)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)).map
        ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f)) :=
      lan_mono (incl S) (fun J _ _ _ => exact_filtered R J) _
    exact (presheafToSheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R))).map_mono _
  exact ⟨(((incl S).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology
    (Scheme.etaleTopology.over S)).obj G).property, adj.map_injective G inferInstance⟩

end UpperTheory.Cb

theorem UpperTheory.Cb.restrInj : LateralTheory.EWeil.AcycPf.RestrInj := UpperTheory.Cb.restr_inj
end
end
