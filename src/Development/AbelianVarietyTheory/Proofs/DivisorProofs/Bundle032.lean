module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section
namespace GlobalTheory.ColimitGlue


set_option backward.isDefEq.respectTransparency false in
theorem exists_glue {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens) (F : 𝒰 ⥤ Scheme.{0})
    [∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected]
    (X : Scheme.{0}) (G : B₀.Opens → X.Opens) (hG : Monotone G)
    (hbas : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ G U → x ∈ G V → ∃ W ∈ 𝒰, x ∈ G W ∧ W ≤ U ∧ W ≤ V)
    (hc : ∀ x : X, ∃ U ∈ 𝒰, x ∈ G U)
    (e : ∀ U : 𝒰, (G U.1).toScheme ⟶ F.obj U)
    (hnat : ∀ {U V : 𝒰} (h : U.1 ≤ V.1),
      X.homOfLE (hG h) ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) :
    ∃ j : X ⟶ colimit F, ∀ U : 𝒰, (G U.1).ι ≫ j = e U ≫ colimit.ι F U := by
  have hcov : TopologicalSpace.IsOpenCover (fun U : 𝒰 ↦ G U.1) :=
    eq_top_iff.2 fun x _ =>
      TopologicalSpace.Opens.mem_iSup.2 (by obtain ⟨U, hU, hx⟩ := hc x; exact ⟨⟨U, hU⟩, hx⟩)
  let 𝒱 : X.OpenCover := X.openCoverOfIsOpenCover (fun U : 𝒰 ↦ G U.1) hcov
  let j : X ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : (pullback.fst (𝒱.f U) (𝒱.f V) x).1 = (pullback.snd (𝒱.f U) (𝒱.f V) x).1 :=
      congr($(pullback.condition (f := 𝒱.f U) (g := 𝒱.f V)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (pullback.fst (𝒱.f U) (𝒱.f V) x).2
      (hx ▸ (pullback.snd (𝒱.f U) (𝒱.f V) x).2)
    let α : (G W).toScheme ⟶ pullback (𝒱.f U) (𝒱.f V) :=
      pullback.lift (X.homOfLE (hG h1)) (X.homOfLE (hG h2))
        ((X.homOfLE_ι (hG h1)).trans (X.homOfLE_ι (hG h2)).symm)
    have hα1 : α ≫ pullback.fst _ _ = X.homOfLE (hG h1) := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = X.homOfLE (hG h2) := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; infer_instance
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    refine ⟨α.opensRange, ⟨⟨_, hxW⟩, ?_⟩, ?_⟩
    · apply (pullback.fst (𝒱.f U) (𝒱.f V)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      rw [reassoc_of% hα1, reassoc_of% hα2, reassoc_of% (hnat (U := ⟨W, hW⟩) (V := U) h1),
        reassoc_of% (hnat (U := ⟨W, hW⟩) (V := V) h2), colimit.w, colimit.w])
  exact ⟨j, fun U ↦ 𝒱.ι_glueMorphisms _ _ U⟩

end GlobalTheory.ColimitGlue
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

abbrev str : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

def Good (r : ℕ) {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) : Prop :=
  IsFinite (I.subschemeι ≫ pullback.snd _ g) ∧ Flat (I.subschemeι ≫ pullback.snd _ g) ∧
    ∀ y, (I.subschemeι ≫ pullback.snd _ g).finrank y = r

abbrev bc {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) :
    pullback (str A B) (a ≫ g) ⟶ pullback (str A B) g :=
  pullback.map _ _ _ _ (𝟙 _) a (𝟙 _) (by simp) (by simp)

theorem isPullback_bc {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) :
    IsPullback (bc A B g a) (pullback.snd _ (a ≫ g)) (pullback.snd _ g) a :=
  by
    have h : bc A B g a ≫ pullback.fst (str A B) g = pullback.fst _ _ :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [h]
    exact IsPullback.of_hasPullback (str A B) (a ≫ g)

theorem good_comap (r : ℕ) {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T)
    (I : (pullback (str A B) g).IdealSheafData) (hI : Good A B r g I) :
    Good A B r (a ≫ g) (I.comap (bc A B g a)) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have H : IsPullback (pullback.snd (bc A B g a) I.subschemeι)
      (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g))
      (I.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) I.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have e : (I.comap (bc A B g a)).subschemeι ≫ pullback.snd _ (a ≫ g) =
      (I.comapIso (bc A B g a)).hom ≫ (pullback.fst (bc A B g a) I.subschemeι ≫
        pullback.snd _ (a ≫ g)) := by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have f1 : IsFinite (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H h1
  have f2 : Flat (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @Flat) H h2
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [e]; infer_instance
  · rw [e]; infer_instance
  · rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ H y, h3]

theorem sigma_eq (r : ℕ) {T : Scheme.{0}} {g₀ g : T ⟶ Spec (CommRingCat.of A)} (h : g₀ = g)
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I : (pullback (str A B) g).IdealSheafData}
    (hI : I₀ = I.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])))
    (h₀ : Good A B r g₀ I₀) (h₁ : Good A B r g I) :
    (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g, ⟨I, h₁⟩⟩ := by
  subst h
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id] at hI
  subst hI
  rfl

theorem comap_bc_comp {T T' T'' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T)
    (b : T'' ⟶ T') (I : (pullback (str A B) g).IdealSheafData) :
    I.comap (bc A B g (b ≫ a)) = ((I.comap (bc A B g a)).comap (bc A B (a ≫ g) b)).comap
      (pullback.map (str A B) ((b ≫ a) ≫ g) (str A B) (b ≫ a ≫ g) (𝟙 _) (𝟙 _) (𝟙 _)
        (by simp) (by simp)) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  congr 1
  apply pullback.hom_ext <;>
    simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]

def functor (r : ℕ) : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := Σ g : T.unop ⟶ Spec (CommRingCat.of A),
    {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}
  map {_ _} a := TypeCat.ofHom fun x => ⟨a.unop ≫ x.1, ⟨x.2.1.comap (bc A B x.1 a.unop),
    good_comap A B r x.1 a.unop x.2.1 x.2.2⟩⟩
  map_id T := by
    ext x : 3
    exact sigma_eq A B r (Category.id_comp _) rfl _ _
  map_comp {T T' T''} a b := by
    ext x : 3
    exact sigma_eq A B r (Category.assoc _ _ _) (comap_bc_comp A B x.1 a.unop b.unop x.2.1) _ _

theorem functor_map (r : ℕ) {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    (functor A B r).map a.op y =
      ⟨a ≫ y.1, ⟨y.2.1.comap (bc A B y.1 a), good_comap A B r y.1 a y.2.1 y.2.2⟩⟩ := rfl

def Basic {r N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : Prop :=
  ∀ U : T.affineOpens, Function.Bijective fun c : Fin r → Γ(T, U) =>
    ∑ k, ((y.2.1.subschemeι ≫ pullback.snd _ y.1).app U).hom (c k) *
      ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤
        ((y.2.1.subschemeι ≫ pullback.snd _ y.1) ⁻¹ᵁ U) (by simp)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (e (σ k)))

end GlobalTheory.HilbAff
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

def IsFinFlatRk {X Y : Scheme.{0}} (f : X ⟶ Y) (r : ℕ) : Prop :=
  IsFinite f ∧ Flat f ∧ ∀ y, f.finrank y = r

lemma IsFinFlatRk.of_isPullback {P X Y T : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ T} {f : X ⟶ Y}
    {g : T ⟶ Y} (h : IsPullback fst snd f g) {r : ℕ} (hf : IsFinFlatRk f r) : IsFinFlatRk snd r := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h h1,
    MorphismProperty.of_isPullback (P := @Flat) h h2, fun y => ?_⟩
  rw [Scheme.Hom.finrank_of_isPullback fst snd f g h y, h3]

lemma IsFinFlatRk.iso_comp {X X' Y : Scheme.{0}} (e : X' ⟶ X) [IsIso e] {f : X ⟶ Y} {r : ℕ}
    (hf : IsFinFlatRk f r) : IsFinFlatRk (e ≫ f) r :=
  IsFinFlatRk.of_isPullback (IsPullback.of_horiz_isIso (fst := e) (g := 𝟙 Y) ⟨by simp⟩) hf

lemma isPullback_comap {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    IsPullback (I.comap f).subschemeι (Scheme.IdealSheafData.subschemeMap _ _ f (I.le_map_comap f))
      f I.subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    (by simp [Scheme.IdealSheafData.ker_subschemeι])

variable {S Z : Scheme.{0}} (z : Z ⟶ S)

def bc {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    pullback z k ⟶ pullback z g :=
  pullback.map z k z g (𝟙 Z) c (𝟙 S) (by simp) (by rw [Category.comp_id, w])

lemma isPullback_bc {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    IsPullback (bc z c g k w) (pullback.snd z k) (pullback.snd z g) c := by
  subst w
  refine IsPullback.of_right ?_ (by simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]) (IsPullback.of_hasPullback z g)
  have e : bc z c g (c ≫ g) rfl ≫ pullback.fst z g = pullback.fst z (c ≫ g) := by simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]
  rw [e]
  exact IsPullback.of_hasPullback z (c ≫ g)

lemma bc_id {T : Scheme.{0}} (g : T ⟶ S) (w : 𝟙 T ≫ g = g) : bc z (𝟙 T) g g w = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [bc]

lemma bc_comp {R T T' : Scheme.{0}} (b : R ⟶ T') (a : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (m : R ⟶ S)
    (w : a ≫ g = k) (w' : b ≫ k = m) (w'' : (b ≫ a) ≫ g = m) :
    bc z (b ≫ a) g m w'' = bc z b k m w' ≫ bc z a g k w := by
  apply pullback.hom_ext <;> simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]

variable (r : ℕ)

abbrev HIdeal {T : Scheme.{0}} (g : T ⟶ S) : Type :=
  {I : (pullback z g).IdealSheafData // IsFinFlatRk (I.subschemeι ≫ pullback.snd z g) r}

abbrev HPt (T : Scheme.{0}) : Type := Σ g : T ⟶ S, HIdeal z r g

variable {z r}

def HIdeal.pull {T T' : Scheme.{0}} (c : T' ⟶ T) {g : T ⟶ S} {k : T' ⟶ S} (w : c ≫ g = k)
    (I : HIdeal z r g) : HIdeal z r k :=
  ⟨I.1.comap (bc z c g k w), IsFinFlatRk.of_isPullback
    ((isPullback_comap I.1 (bc z c g k w)).flip.paste_vert (isPullback_bc z c g k w)) I.2⟩

def HPt.map {T T' : Scheme.{0}} (c : T' ⟶ T) (x : HPt z r T) : HPt z r T' :=
  ⟨c ≫ x.1, x.2.pull c rfl⟩

lemma HPt.map_mk {T T' : Scheme.{0}} (c : T' ⟶ T) {g : T ⟶ S} {k : T' ⟶ S} (w : c ≫ g = k)
    (I : HIdeal z r g) : HPt.map c ⟨g, I⟩ = ⟨k, I.pull c w⟩ := by
  subst w; rfl

lemma HPt.mk_eq_mk_iff {T : Scheme.{0}} {g : T ⟶ S} (I J : HIdeal z r g) :
    (⟨g, I⟩ : HPt z r T) = ⟨g, J⟩ ↔ I.1 = J.1 := by
  rw [Sigma.mk.inj_iff, heq_iff_eq, Subtype.ext_iff]
  simp

lemma HPt.map_eq_mk_iff {T T' : Scheme.{0}} (c : T' ⟶ T) (x : HPt z r T) {k : T' ⟶ S}
    (w : c ≫ x.1 = k) (J : HIdeal z r k) :
    HPt.map c x = ⟨k, J⟩ ↔ x.2.1.comap (bc z c x.1 k w) = J.1 := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk c w, HPt.mk_eq_mk_iff]
  rfl

lemma HPt.map_id {T : Scheme.{0}} (x : HPt z r T) : HPt.map (𝟙 T) x = x := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk (𝟙 T) (Category.id_comp g), HPt.mk_eq_mk_iff]
  change I.1.comap (bc z (𝟙 T) g g _) = I.1
  rw [bc_id, Scheme.IdealSheafData.comap_id]

lemma HPt.map_comp {R T T' : Scheme.{0}} (b : R ⟶ T') (a : T' ⟶ T) (x : HPt z r T) :
    HPt.map (b ≫ a) x = HPt.map b (HPt.map a x) := by
  obtain ⟨g, I⟩ := x
  rw [HPt.map_mk (b ≫ a) (Category.assoc b a g), HPt.map_mk a rfl, HPt.map_mk b rfl, HPt.mk_eq_mk_iff]
  change I.1.comap (bc z (b ≫ a) g _ _) = (I.1.comap (bc z a g _ rfl)).comap (bc z b (a ≫ g) _ rfl)
  rw [← Scheme.IdealSheafData.comap_comp, bc_comp z b a g (a ≫ g) (b ≫ a ≫ g) rfl rfl]

variable (z r)

def hilbFunctor : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := HPt z r T.unop
  map c := TypeCat.ofHom (HPt.map c.unop)
  map_id T := ConcreteCategory.hom_ext _ _ fun x => HPt.map_id x
  map_comp a b := ConcreteCategory.hom_ext _ _ fun x => HPt.map_comp _ _ x

def hilbProj : hilbFunctor z r ⟶ yoneda.obj S where
  app T := TypeCat.ofHom fun x => x.1

variable {z r}

lemma IsFinFlatRk.ker_subschemeι {T V : Scheme.{0}} {g : T ⟶ S} (v : V ⟶ pullback z g)
    [IsClosedImmersion v] (hv : IsFinFlatRk (v ≫ pullback.snd z g) r) :
    IsFinFlatRk (v.ker.subschemeι ≫ pullback.snd z g) r := by
  have e : v.ker.subschemeι = inv v.toImage ≫ v := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [e, Category.assoc]
  exact hv.iso_comp _

def mkPt {T V : Scheme.{0}} (g : T ⟶ S) (v : V ⟶ pullback z g) [IsClosedImmersion v]
    (hv : IsFinFlatRk (v ≫ pullback.snd z g) r) : HPt z r T :=
  ⟨g, v.ker, hv.ker_subschemeι v⟩

theorem comap_eq_ker_iff {X Y V : Scheme.{0}} (m : X ⟶ Y) (I : Y.IdealSheafData) (v : V ⟶ X)
    [IsClosedImmersion v] : I.comap m = v.ker ↔ ∃ w : V ⟶ I.subscheme, IsPullback v w m I.subschemeι := by
  constructor
  · intro h
    have H : I.subschemeι.ker ≤ (v ≫ m).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.le_map_iff_comap_le, h]
    refine ⟨IsClosedImmersion.lift I.subschemeι (v ≫ m) H,
      isPullback_of_isClosedImmersion _ _ _ _ (IsClosedImmersion.lift_fac _ _ _).symm ?_⟩
    rw [Scheme.IdealSheafData.ker_subschemeι, h]
  · rintro ⟨w, hP⟩
    rw [← hP.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]

end GlobalTheory.HilbGlue
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem IdealSheafData.ideal_comap_top_of_isAffine (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) :
    (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  apply le_antisymm
  · have hle : J.comap f ≤ Scheme.IdealSheafData.ofIdealTop
        (Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩)) := by
      rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
      intro j hj
      rw [Ideal.mem_comap, Scheme.IdealSheafData.ofIdealTop_ideal]
      have h1 : (X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ (⊤ : Y.Opens) ≤ ⊤)).op) = 𝟙 _ :=
        X.presheaf.map_id _
      rw [h1]
      erw [CommRingCat.hom_id, Ideal.map_id]
      exact Ideal.mem_map_of_mem _ hj
    have := hle ⟨⊤, isAffineOpen_top X⟩
    simpa using this
  · rw [Ideal.map_le_iff_le_comap]
    intro j hj
    rw [Ideal.mem_comap, Scheme.IdealSheafData.comap, Scheme.Hom.ker_apply, RingHom.mem_ker]
    have hj' : J.subschemeι.appTop.hom j = 0 := by
      have := hj
      rw [← J.ker_subschemeι, Scheme.Hom.ker_apply, RingHom.mem_ker] at this
      exact this
    have hc := congrArg (fun g => g.hom j)
      (congrArg Scheme.Hom.appTop (pullback.condition (f := f) (g := J.subschemeι)))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hc
    change (pullback.fst f J.subschemeι).appTop.hom (f.appTop.hom j) = 0
    rw [hc, hj', map_zero]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem closedSub_flat_of_quotient_flat : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec (CommRingCat.of V)) (J : X.IdealSheafData), ((Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top X⟩)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat → Flat (J.subschemeι ≫ p) := by
  intro V _ X _ p J h
  have : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  set U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : (J.subschemeι ≫ p).appTop.hom =
      (J.subschemeObjIso U).inv.hom.comp
        (((Ideal.Quotient.mk (J.ideal U)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).comp
          (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom) := by
    have h2 := J.subschemeι_app U
    have h3 : J.subschemeι.appTop = CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U)) ≫ (J.subschemeObjIso U).inv := h2
    rw [Scheme.Hom.comp_appTop, h3]
    ext x
    change (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom x)) =
      (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom x))))
    rw [Iso.hom_inv_id_apply]
  rw [e]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (J.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.bijective)
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.bijective) h

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

theorem closedImmersion_baseChange_ker_mem_map : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → ∀ W : X.Opens, IsAffineOpen W → ∀ s : Γ(X', p ⁻¹ᵁ W), (i'.app (p ⁻¹ᵁ W)).hom s = 0 → s ∈ Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) := by
  intro X X' Z Z' p i i' p' h hp hi W hW s hs
  set J : Ideal Γ(X', p ⁻¹ᵁ W) := Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) with hJ
  have hU' : IsAffineOpen (p ⁻¹ᵁ W) := hW.preimage p
  have hZ : IsAffineOpen (i ⁻¹ᵁ W) := hW.preimage i
  have hsurj : Function.Surjective (i.app W).hom := i.app_surjective W hW
  let ψ : Γ(X, W) →+* (Γ(X', p ⁻¹ᵁ W) ⧸ J) := (Ideal.Quotient.mk J).comp (p.app W).hom
  have hker : RingHom.ker (i.app W).hom ≤ RingHom.ker ψ := by
    intro a ha
    simp only [RingHom.mem_ker, ψ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let φ : Γ(Z, i ⁻¹ᵁ W) →+* (Γ(X', p ⁻¹ᵁ W) ⧸ J) :=
    (i.app W).hom.liftOfSurjective hsurj ⟨ψ, hker⟩
  have hφ : φ.comp (i.app W).hom = ψ := (i.app W).hom.liftOfRightInverse_comp _ _ _
  let e : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ X' :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hU'.fromSpec
  let t : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ Z :=
    Spec.map (CommRingCat.ofHom φ) ≫ hZ.fromSpec
  have hw : e ≫ p = t ≫ i := by
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec p hW hU' le_rfl
    have h2 := IsAffineOpen.SpecMap_appLE_fromSpec i hW hZ le_rfl
    simp only [e, t, Category.assoc, ← h1, ← h2, ← Spec.map_comp, ← Scheme.Hom.app_eq_appLE]
    simp only [← Spec.map_comp_assoc]
    congr 2
    ext x
    exact (RingHom.congr_fun hφ x).symm
  let l := h.lift e t hw
  have hl : l ≫ i' = e := h.lift_fst e t hw
  have hle : (⊤ : (Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).Opens) ≤ e ⁻¹ᵁ (p ⁻¹ᵁ W) := by
    simp [e, Scheme.Hom.comp_preimage, hU'.fromSpec_preimage_self]
  have h0 : (e.appLE (p ⁻¹ᵁ W) ⊤ hle).hom s = 0 := by
    have key : ∀ (g : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ X') (hg : g = e) (hle' : ⊤ ≤ g ⁻¹ᵁ (p ⁻¹ᵁ W)),
        g.appLE (p ⁻¹ᵁ W) ⊤ hle' = e.appLE (p ⁻¹ᵁ W) ⊤ hle := by
      rintro g rfl _; rfl
    rw [← key (l ≫ i') hl (by rw [hl]; exact hle), Scheme.Hom.comp_appLE, CommRingCat.comp_apply, hs, map_zero]
  have h1 : (e.appLE (p ⁻¹ᵁ W) ⊤ hle).hom s = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).inv.hom (Ideal.Quotient.mk J s) := by
    simp only [e, Scheme.Hom.comp_appLE, hU'.fromSpec_app_self]
    rw [Category.assoc]
    erw [Scheme.Hom.map_appLE]
    rw [show ∀ hh, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appLE ⊤ ⊤ hh = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop from fun _ => (Scheme.Hom.app_eq_appLE _).symm]
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [h1] at h0
  have h2 : Ideal.Quotient.mk J s = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).hom.hom h0
    simpa using this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

end GlobalTheory
end
