module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle019
public import Development.EtaleCohomology.CohomologicalPurity.Bundle031
public import Development.EtaleCohomology.CohomologicalPurity.Bundle028
public import Development.EtaleCohomology.CohomologicalPurity.Bundle030
public import Development.EtaleCohomology.CohomologicalPurity.OffContStepPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
namespace LateralTheory.CohomologicalPurity

theorem exact_app_of_π {R : Type} [CommRing R] {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G)
    (V : Scheme.{0}ᵒᵖ) (m : G.obj V) (hm : (cokernel.π f).app V m = 0) : ∃ n, f.app V n = m := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f)
  have h2 := hS.map ((evaluation _ _).obj V)
  rw [ShortComplex.moduleCat_exact_iff] at h2
  exact h2 m hm

theorem mapDomain_apply_eq_sum {α β M : Type*} [AddCommMonoid M] [DecidableEq β] (v : α →₀ M) (f : α → β) (t : β) :
    Finsupp.mapDomain f v t = ∑ a ∈ v.support with f a = t, v a := by
  classical
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

theorem core {α β γ M : Type*} [AddCommMonoid M] (v : α →₀ M) (f : α → β) (r : α → γ)
    (Q : β → Prop) (P : γ → Prop)
    (hv : ∀ t, ¬ Q t → Finsupp.mapDomain f v t = 0)
    (hQ : ∀ a, Q (f a) → P (r a))
    (hP : ∀ a₁ a₂, f a₁ = f a₂ → P (r a₁) → P (r a₂))
    (h : ∀ a₁ ∈ v.support, ∀ a₂ ∈ v.support, f a₁ = f a₂ → r a₁ = r a₂ ∨ P (r a₁)) :
    ∀ z, ¬ P z → Finsupp.mapDomain r v z = 0 := by
  classical
  intro z hz
  rw [mapDomain_apply_eq_sum]
  set s' := v.support.filter (fun a => r a = z)
  rw [← Finset.sum_fiberwise_of_maps_to (s := s') (t := s'.image f) (g := f)
    (fun a ha => Finset.mem_image_of_mem f ha)]
  refine Finset.sum_eq_zero fun t ht => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 ht
  have ha₀' := Finset.mem_filter.1 ha₀
  have hQ0 : ¬ Q (f a₀) := fun hq => hz (ha₀'.2 ▸ hQ a₀ hq)
  have e : (s'.filter fun a => f a = f a₀) = v.support.filter (fun a => f a = f a₀) := by
    ext a
    simp only [s', Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rcases h a h1 a₀ ha₀'.1 h3 with e | p
      · rw [e, ha₀'.2]
      · exact absurd (ha₀'.2 ▸ hP a a₀ h3 p) hz
  rw [e]
  have := mapDomain_apply_eq_sum v f (f a₀)
  rw [hv _ hQ0] at this
  convert this.symm

theorem exists_covering_finset {T : Scheme.{0}} {ι : Type*} (s : Finset ι)
    (Pr : ι → ∀ ⦃V : Scheme.{0}⦄, (V ⟶ T) → Prop)
    (hPr : ∀ p ∈ s, ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g → Pr p g) :
    ∃ S ∈ Scheme.etaleTopology T, ∀ p ∈ s, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g → Pr p g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, Scheme.etaleTopology.top_mem T, by simp⟩
  | insert q s hq ih =>
    obtain ⟨S₁, h₁, H₁⟩ := ih (fun p hp => hPr p (Finset.mem_insert_of_mem hp))
    obtain ⟨S₂, h₂, H₂⟩ := hPr q (Finset.mem_insert_self q s)
    refine ⟨S₁ ⊓ S₂, Scheme.etaleTopology.intersection_covering h₁ h₂, ?_⟩
    intro p hp V g hg
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact H₂ g hg.2
    · exact H₁ p hp g hg.1

theorem mem_range_mapDomain {α β M : Type*} [AddCommMonoid M] (u : α → β) (w : β →₀ M)
    (hw : ∀ z, (¬ ∃ x, u x = z) → w z = 0) : ∃ n : α →₀ M, Finsupp.mapDomain u n = w := by
  have hmem : w ∈ Finsupp.supported M ℕ (u '' Set.univ) := by
    rw [Finsupp.mem_supported]
    intro z hz
    by_contra hc
    exact (Finsupp.mem_support_iff.1 hz) (hw z (fun ⟨x, hx⟩ => hc ⟨x, trivial, hx⟩))
  rw [← Finsupp.lmapDomain_supported] at hmem
  obtain ⟨n, _, hn⟩ := hmem
  exact ⟨n, hn⟩

theorem leafFreeCokInj : LeafFreeCokInj := by
  intro R _ A' B' A B i' i a b w h1 h3
  have key : ∀ (T : Scheme.{0}) (z : (cokernel ((freeP R).map i')).obj (op T)),
      (pcok R i' i a b w).app (op T) z = 0 → Presheaf.equalizerSieve z 0 ∈ Scheme.etaleTopology T := by
    intro T z hz
    obtain ⟨v, rfl⟩ := π_app_surj R i' (op T) z
    rw [pcok_π_apply] at hz
    obtain ⟨n, hn⟩ := exact_app_of_π _ _ _ hz
    have hn' : Finsupp.mapDomain (fun x : ULift.{1} (A.obj (op T)) => ULift.up (i.app (op T) x.down)) n =
        Finsupp.mapDomain (fun x : ULift.{1} (B'.obj (op T)) => ULift.up (b.app (op T) x.down)) v := hn
    let Pr : (ULift.{1} (B'.obj (op T)) × ULift.{1} (B'.obj (op T))) → ∀ ⦃V : Scheme.{0}⦄, (V ⟶ T) → Prop :=
      fun p V g => b.app (op T) p.1.down = b.app (op T) p.2.down →
        B'.map g.op p.1.down = B'.map g.op p.2.down ∨
          ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op p.1.down)
    obtain ⟨S, hS, HS⟩ := exists_covering_finset (v.support ×ˢ v.support) Pr (by
      intro p _
      by_cases he : b.app (op T) p.1.down = b.app (op T) p.2.down
      · obtain ⟨S, hS, H⟩ := h3 T p.1.down p.2.down he
        exact ⟨S, hS, fun V g hg _ => H g hg⟩
      · exact ⟨⊤, Scheme.etaleTopology.top_mem T, fun V g _ he' => absurd he' he⟩)
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    show (cokernel ((freeP R).map i')).map g.op _ = (cokernel ((freeP R).map i')).map g.op 0
    rw [map_zero, ← NatTrans.naturality_apply]
    have hcore := core v (fun x : ULift.{1} (B'.obj (op T)) => (ULift.up.{1} (b.app (op T) x.down) : ULift.{1} (B.obj (op T))))
      (fun x : ULift.{1} (B'.obj (op T)) => ULift.up (B'.map g.op x.down))
      (fun t : ULift.{1} (B.obj (op T)) => ∃ x, i.app (op T) x = t.down) (fun z => ∃ x', i'.app (op V) x' = z.down)
      (by
        intro t ht
        have := Finsupp.mapDomain_notin_range n t (by
          rintro ⟨x, hx⟩
          exact ht ⟨x.down, congrArg ULift.down hx⟩)
        exact (DFunLike.congr_fun hn' t).symm.trans this)
      (by
        rintro a₀ ⟨x, hx⟩
        obtain ⟨x', hx'⟩ := h1 T a₀.down x hx
        exact ⟨A'.map g.op x', by rw [NatTrans.naturality_apply, hx']⟩)
      (by
        rintro a₁ a₂ he ⟨x', hx'⟩
        have he' : b.app (op T) a₁.down = b.app (op T) a₂.down := congrArg ULift.down he
        refine h1 V (B'.map g.op a₂.down) (a.app (op V) x') ?_
        have := ConcreteCategory.congr_hom (NatTrans.congr_app w (op V)) x'
        simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
        rw [← this, hx', NatTrans.naturality_apply, NatTrans.naturality_apply, he'])
      (by
        intro a₁ ha₁ a₂ ha₂ he
        rcases HS (a₁, a₂) (Finset.mem_product.2 ⟨ha₁, ha₂⟩) g hg (congrArg ULift.down he) with e | ⟨x, hx⟩
        · left; exact congrArg ULift.up e
        · right; exact h1 V _ x hx)
    obtain ⟨n', hn''⟩ := mem_range_mapDomain (fun x : ULift.{1} (A'.obj (op V)) => ULift.up (i'.app (op V) x.down)) _
      (fun z hz => hcore z (fun ⟨x', hx'⟩ => hz ⟨ULift.up x', congrArg ULift.up hx' |>.trans rfl⟩))
    have e2 : ((freeP R).obj B').map g.op v = ((freeP R).map i').app (op V) n' := hn''.symm
    rw [e2]
    exact π_freeP_apply R i' (op V) n'
  constructor
  intro X x y hxy
  cases X with | op T =>
  refine Scheme.etaleTopology.superset_covering ?_ (key T (x - y) (by rw [map_sub, hxy, sub_self]))
  intro V g hg
  have hg' : (cokernel ((freeP R).map i')).map g.op (x - y) = (cokernel ((freeP R).map i')).map g.op 0 := hg
  rw [map_sub, map_zero, sub_eq_zero] at hg'
  exact hg'

theorem LeafFreeCokInj_of : LeafFreeCokInj := leafFreeCokInj

end LateralTheory.CohomologicalPurity
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem prod_elt_bij (A B : Spc) (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ) :
    Function.Bijective (fun z : ((A ⨯ B).obj n).obj X =>
      (((prod.fst : A ⨯ B ⟶ A).app n).app X z, ((prod.snd : A ⨯ B ⟶ B).app n).app X z)) := by
  let G : Spc ⥤ Type := (evaluation _ _).obj n ⋙ (evaluation _ _).obj X
  let f := (PreservesLimitPair.iso G A B).hom ≫ (Types.binaryProductIso _ _).hom
  have hf : Function.Bijective f := (isIso_iff_bijective f).1 inferInstance
  have h1 : f ≫ TypeCat.ofHom (Prod.fst : G.obj A × G.obj B → G.obj A) = G.map prod.fst := by
    simp [f, PreservesLimitPair.iso_hom]
  have h2 : f ≫ TypeCat.ofHom (Prod.snd : G.obj A × G.obj B → G.obj B) = G.map prod.snd := by
    simp [f, PreservesLimitPair.iso_hom]
  have e : (fun z : ((A ⨯ B).obj n).obj X =>
      (((prod.fst : A ⨯ B ⟶ A).app n).app X z, ((prod.snd : A ⨯ B ⟶ B).app n).app X z)) = ⇑(ConcreteCategory.hom f) := by
    funext z
    refine Prod.ext ?_ ?_
    · exact (congrArg (fun φ => φ z) h1).symm
    · exact (congrArg (fun φ => φ z) h2).symm
  rw [e]; exact hf

def liftW {C : Type} [Category C] {d : ℕ} {U : Scheme.{0}} (F : C ⥤ Vec (d + 1) 0 U)
    (h : ∀ c, IsUnit ((F.obj c).1 0)) : C ⥤ WVec d U where
  obj c := ⟨F.obj c, h c⟩
  map f := F.map f
  map_id c := F.map_id c
  map_comp f g := F.map_comp f g

def lift1 {C : Type} [Category C] {N : ℕ} {U : Scheme.{0}} (F : C ⥤ Vec N 0 U)
    (h : ∀ c (p : U), ∃ i : Fin N, 1 ≤ i.val ∧ p ∈ U.basicOpen ((F.obj c).1 i)) : C ⥤ Vec N 1 U where
  obj c := ⟨(F.obj c).1, h c⟩
  map f := F.map f
  map_id c := F.map_id c
  map_comp f g := F.map_comp f g

theorem bo_hom {N k : ℕ} {U : Scheme.{0}} {v w : Vec N k U} (u : v ⟶ w) (i : Fin N) :
    U.basicOpen (v.1 i) = U.basicOpen (w.1 i) := by
  obtain ⟨u, hu⟩ := u
  rw [hu i, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ u.isUnit, top_inf_eq]

theorem bo_chain {N k m : ℕ} {U : Scheme.{0}} (c : ComposableArrows (Vec N k U) m) (a : Fin (m + 1)) (i : Fin N) :
    U.basicOpen ((c.obj a).1 i) = U.basicOpen ((c.obj 0).1 i) :=
  (bo_hom (c.map (homOfLE (Fin.zero_le a))) i).symm

theorem mem_bo_map {N k : ℕ} {X : Scheme.{0}} (O : X.Opens) (v : Vec N k X) (i : Fin N) (p : (O : Scheme.{0})) :
    p ∈ (O : Scheme.{0}).basicOpen (((Vec.map N k O.ι).obj v).1 i) ↔ p.val ∈ X.basicOpen (v.1 i) := by
  change p ∈ (O : Scheme.{0}).basicOpen (O.ι.appTop.hom (v.1 i)) ↔ _
  rw [← Scheme.preimage_basicOpen_top]
  rfl

theorem isUnit_of_bo {Y : Scheme.{0}} (f : Γ(Y, ⊤)) (h : ∀ p : Y, p ∈ Y.basicOpen f) : IsUnit f :=
  Y.toRingedSpace.isUnit_of_isUnit_germ ⊤ f fun x _ => (Y.mem_basicOpen_top f x).1 (h x)

theorem fst_map {A B : Spc} (n : SimplexCategoryᵒᵖ) {X Y : Scheme.{0}ᵒᵖ} (f : X ⟶ Y) (z : ((A ⨯ B).obj n).obj X) :
    ((prod.fst : A ⨯ B ⟶ A).app n).app Y (((A ⨯ B).obj n).map f z) =
      (A.obj n).map f (((prod.fst : A ⨯ B ⟶ A).app n).app X z) :=
  NatTrans.naturality_apply ((prod.fst : A ⨯ B ⟶ A).app n) f z

theorem snd_map {A B : Spc} (n : SimplexCategoryᵒᵖ) {X Y : Scheme.{0}ᵒᵖ} (f : X ⟶ Y) (z : ((A ⨯ B).obj n).obj X) :
    ((prod.snd : A ⨯ B ⟶ B).app n).app Y (((A ⨯ B).obj n).map f z) =
      (B.obj n).map f (((prod.snd : A ⨯ B ⟶ B).app n).app X z) :=
  NatTrans.naturality_apply ((prod.snd : A ⨯ B ⟶ B).app n) f z

theorem map_fst_app {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ)
    (z : ((A ⨯ B).obj n).obj X) :
    ((prod.fst : A' ⨯ B' ⟶ A').app n).app X (((prod.map f g).app n).app X z) =
      (f.app n).app X (((prod.fst : A ⨯ B ⟶ A).app n).app X z) := by
  have := congrArg (fun φ => (φ.app n).app X z) (prod.map_fst f g)
  simp only [NatTrans.comp_app] at this
  exact this

theorem map_snd_app {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ)
    (z : ((A ⨯ B).obj n).obj X) :
    ((prod.snd : A' ⨯ B' ⟶ B').app n).app X (((prod.map f g).app n).app X z) =
      (g.app n).app X (((prod.snd : A ⨯ B ⟶ B).app n).app X z) := by
  have := congrArg (fun φ => (φ.app n).app X z) (prod.map_snd f g)
  simp only [NatTrans.comp_app] at this
  exact this

theorem prod_ext_app {A B : Spc} (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ) (z w : ((A ⨯ B).obj n).obj X)
    (h1 : ((prod.fst : A ⨯ B ⟶ A).app n).app X z = ((prod.fst : A ⨯ B ⟶ A).app n).app X w)
    (h2 : ((prod.snd : A ⨯ B ⟶ B).app n).app X z = ((prod.snd : A ⨯ B ⟶ B).app n).app X w) : z = w :=
  (prod_elt_bij A B n X).1 (Prod.ext h1 h2)

theorem LeafWLoc_of : LeafWLoc := by
  intro d R _ n X x
  let c : ComposableArrows (Vec (d + 1) 0 X) n.unop.len :=
    ((prod.fst : PR (d + 1) 0 R ⟶ Pj (d + 1) 0).app n).app (op X) x
  let s := ((prod.snd : PR (d + 1) 0 R ⟶ sp R).app n).app (op X) x
  refine ⟨Fin (d + 1), fun j => X.basicOpen ((c.obj 0).1 j), ?_, fun j => ?_⟩
  · refine eq_top_iff.2 fun p _ => ?_
    obtain ⟨j, -, hj⟩ := (c.obj 0).2 p
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩
  · let O := X.basicOpen ((c.obj 0).1 j)
    let cr : ComposableArrows (Vec (d + 1) 0 O) n.unop.len := c ⋙ Vec.map (d + 1) 0 O.ι
    let sr := ((sp R).obj n).map O.ι.op s
    have hbo : ∀ a i (p : (O : Scheme.{0})), p ∈ (O : Scheme.{0}).basicOpen ((cr.obj a).1 i) ↔
        p.val ∈ X.basicOpen ((c.obj 0).1 i) := fun a i p => by
      rw [← bo_chain c a i]; exact mem_bo_map O (c.obj a) i p
    by_cases hj : j = 0
    · left
      obtain ⟨y, hy⟩ := (prod_elt_bij (Wsp d) (sp R) n (op (O : Scheme.{0}))).2
        (liftW cr (fun a => isUnit_of_bo _ fun p => (hbo a 0 p).2 (hj ▸ p.2)), sr)
      refine ⟨y, prod_ext_app _ _ _ _ ?_ ?_⟩
      · change ((prod.fst : PR (d + 1) 0 R ⟶ _).app n).app _ (((prod.map (Wincl d) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_fst_app, fst_map]
        refine (congrArg (fun w => ((Wincl d).app n).app _ w) (congrArg Prod.fst hy)).trans ?_
        rfl
      · change ((prod.snd : PR (d + 1) 0 R ⟶ _).app n).app _ (((prod.map (Wincl d) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_snd_app, snd_map]
        refine (congrArg (fun w => ((𝟙 (sp R) : sp R ⟶ sp R).app n).app _ w) (congrArg Prod.snd hy)).trans ?_
        rfl
    · right
      have hj1 : 1 ≤ j.val := Nat.one_le_iff_ne_zero.2 fun h => hj (Fin.ext h)
      obtain ⟨y, hy⟩ := (prod_elt_bij (Pj (d + 1) 1) (sp R) n (op (O : Scheme.{0}))).2
        (lift1 cr (fun a p => ⟨j, hj1, (hbo a j p).2 p.2⟩), sr)
      refine ⟨y, prod_ext_app _ _ _ _ ?_ ?_⟩
      · change ((prod.fst : PR (d + 1) 0 R ⟶ _).app n).app _
          (((prod.map (Pj.incl (d + 1)) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_fst_app, fst_map]
        refine (congrArg (fun w => ((Pj.incl (d + 1)).app n).app _ w) (congrArg Prod.fst hy)).trans ?_
        rfl
      · change ((prod.snd : PR (d + 1) 0 R ⟶ _).app n).app _
          (((prod.map (Pj.incl (d + 1)) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_snd_app, snd_map]
        refine (congrArg (fun w => ((𝟙 (sp R) : sp R ⟶ sp R).app n).app _ w) (congrArg Prod.snd hy)).trans ?_
        rfl

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem intPoly_smooth : (algebraMap ℤ (Polynomial ℤ)).Smooth := by
  haveI : Algebra.FormallySmooth ℤ (Polynomial ℤ) :=
    inferInstance
  haveI : Algebra.Smooth ℤ (Polynomial ℤ) := ⟨inferInstance, inferInstance⟩
  exact RingHom.smooth_algebraMap.mpr inferInstance

theorem laurent_smooth : (algebraMap ℤ (LaurentPolynomial ℤ)).Smooth := by
  have h2 : (algebraMap (Polynomial ℤ) (LaurentPolynomial ℤ)).Smooth :=
    RingHom.Smooth.holdsForLocalizationAway (LaurentPolynomial ℤ) (Polynomial.X : Polynomial ℤ)
  have := RingHom.Smooth.comp intPoly_smooth h2
  convert this
  exact RingHom.ext_int _ _

theorem gm_from_smooth : Smooth (specZIsTerminal.from Gm) := by
  have e : specZIsTerminal.from Gm =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (LaurentPolynomial ℤ))) := specZIsTerminal.hom_ext _ _
  rw [e, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact laurent_smooth

theorem gmU_smooth (X : Scheme.{0}) : Smooth (prod.fst : X ⨯ Gm ⟶ X) := by
  have hp := IsPullback.of_is_product (limit.isLimit (pair X Gm)) specZIsTerminal
  have := gm_from_smooth
  exact MorphismProperty.of_isPullback (P := @Smooth) hp.flip this

theorem gmU_surj (X : Scheme.{0}) : Surjective (prod.fst : X ⨯ Gm ⟶ X) := by
  let pt : Spec (CommRingCat.of ℤ) ⟶ Gm :=
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id ℤ) 1))
  let s : X ⟶ X ⨯ Gm := prod.lift (𝟙 X) (specZIsTerminal.from X ≫ pt)
  have hs : s ≫ prod.fst = 𝟙 X := prod.lift_fst _ _
  have : Surjective (s ≫ prod.fst) := by rw [hs]; infer_instance
  exact Surjective.of_comp s prod.fst

theorem LeafWGm_of : LeafWGm := fun _ _ _ _ => ⟨gmU_smooth _, gmU_surj _⟩

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem pairFiveS_surj (bd : LeafBd) (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (F : Jᵒᵖ ⥤ Arrow Spc)
    (P : Arrow Spc) (c : ∀ j, P ⟶ F.obj (op j)) (hc : ∀ j k (f : j ⟶ k), c k ≫ F.map f.op = c j)
    (hm : ∀ j, Mono (F.obj (op j)).hom) (hP : Mono P.hom) (i : ℤ) (hL : ∀ m, ContL q F P c m i)
    (hR : ∀ m, ContR q F P c m i) (m : ℤ) (x : Hs q P (m + 1) i) :
    ∃ j, ∃ y, Hs.pull q (c j) (m + 1) i y = x := by
  obtain ⟨δ, hex, hnat, -⟩ := bd
  obtain ⟨j, y, hy⟩ := (hR (m + 1)).1 (Hs.fgt q P (m + 1) i x)
  have h0 : pull _ (c j).left (tw q i) (m + 1) (pull _ (F.obj (op j)).hom (tw q i) (m + 1) y) = 0 := by
    rw [← GlobalTheory.EtC.pull_comp, Arrow.w (c j), GlobalTheory.EtC.pull_comp, hy]
    exact ((hex q P hP (m + 1) i).1 _).mpr ⟨x, rfl⟩
  obtain ⟨k, f, hk⟩ := (hL (m + 1)).2 j _ h0
  have hk' : pull _ (F.obj (op k)).hom (tw q i) (m + 1) (pull _ (F.map f.op).right (tw q i) (m + 1) y) = 0 := by
    rw [← GlobalTheory.EtC.pull_comp, ← Arrow.w (F.map f.op), GlobalTheory.EtC.pull_comp, hk]
  obtain ⟨s, hs⟩ := ((hex q _ (hm k) (m + 1) i).1 _).mp hk'
  have hv : Hs.fgt q P (m + 1) i (x - Hs.pull q (c k) _ _ s) = 0 := by
    rw [map_sub, Hs.fgt_pull, hs, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_right, hc, hy, sub_self]
  obtain ⟨u, hu⟩ := ((hex q P hP m i).2.2 _).mp hv
  obtain ⟨l, a, ha⟩ := (hL m).1 u
  rw [← ha, ← hnat q _ _ (c l) hP (hm l)] at hu
  obtain ⟨M, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs k l
  refine ⟨M, Hs.pull q (F.map g1.op) _ _ s + Hs.pull q (F.map g2.op) _ _ (δ q _ m i a), ?_⟩
  rw [map_add (f := _), ← Hs.pullComp, ← Hs.pullComp, hc, hc, hu, add_sub_cancel]

theorem pairFiveS_inj (bd : LeafBd) (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (F : Jᵒᵖ ⥤ Arrow Spc)
    (P : Arrow Spc) (c : ∀ j, P ⟶ F.obj (op j)) (hc : ∀ j k (f : j ⟶ k), c k ≫ F.map f.op = c j)
    (hm : ∀ j, Mono (F.obj (op j)).hom) (hP : Mono P.hom) (i : ℤ) (hL : ∀ m, ContL q F P c m i)
    (hR : ∀ m, ContR q F P c m i) (m : ℤ) (j : J) (y : Hs q (F.obj (op j)) (m + 1) i)
    (hy : Hs.pull q (c j) (m + 1) i y = 0) :
    ∃ (k : J) (f : j ⟶ k), Hs.pull q (F.map f.op) (m + 1) i y = 0 := by
  obtain ⟨δ, hex, hnat, -⟩ := bd
  have h0 : pull _ (c j).right (tw q i) (m + 1) (Hs.fgt q _ (m + 1) i y) = 0 := by
    rw [← Hs.fgt_pull, hy, map_zero]
  obtain ⟨k, f, hk⟩ := (hR (m + 1)).2 j _ h0
  rw [← Hs.fgt_pull] at hk
  obtain ⟨a, ha⟩ := ((hex q _ (hm k) m i).2.2 _).mp hk
  have hz : δ q P m i (pull _ (c k).left (tw q i) m a) = 0 := by
    rw [← hnat q _ _ (c k) hP (hm k), ha, ← Hs.pullComp, hc, hy]
  obtain ⟨b, hb⟩ := ((hex q P hP m i).2.1 _).mp hz
  obtain ⟨l, e, he⟩ := (hR m).1 b
  obtain ⟨M, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs k l
  have hd : pull _ (c M).left (tw q i) m (pull _ (F.map g1.op).left (tw q i) m a -
      pull _ (F.obj (op M)).hom (tw q i) m (pull _ (F.map g2.op).right (tw q i) m e)) = 0 := by
    rw [map_sub, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_left, hc, ← hb, ← he, ← GlobalTheory.EtC.pull_comp,
      ← GlobalTheory.EtC.pull_comp, ← GlobalTheory.EtC.pull_comp, Category.assoc, ← Arrow.w (F.map g2.op), ← Category.assoc, ← Arrow.comp_left, hc,
      Arrow.w (c l), sub_self]
  obtain ⟨p, h, hp⟩ := (hL m).2 M _ hd
  rw [map_sub, sub_eq_zero, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_left, ← F.map_comp, ← op_comp,
    ← GlobalTheory.EtC.pull_comp, Arrow.w (F.map h.op), GlobalTheory.EtC.pull_comp] at hp
  refine ⟨p, f ≫ g1 ≫ h, ?_⟩
  have e1 : F.map (f ≫ g1 ≫ h).op = F.map (g1 ≫ h).op ≫ F.map f.op := by rw [op_comp, F.map_comp]
  rw [e1, Hs.pullComp, ← ha, hnat q _ _ _ (hm p) (hm k), hp]
  exact ((hex q _ (hm p) m i).2.1 _).mpr ⟨_, rfl⟩

theorem pairFiveS : PairFiveS := by
  intro bd q J _ _ F P c hc hm hP i hL hR n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact ⟨pairFiveS_surj bd q F P c hc hm hP i hL hR m,
    fun j y hy => pairFiveS_inj bd q F P c hc hm hP i hL hR m j y hy⟩

theorem etale_purity_continuity_off_closed_of_local_and_chase (hL : OffContLoc) (hG : OffChaseGeo) : OffContStep :=
  etale_complement_continuity_induction_of_localization_and_pair_lemmas hL pairFiveS hG

end LateralTheory.CohomologicalPurity
end
end
