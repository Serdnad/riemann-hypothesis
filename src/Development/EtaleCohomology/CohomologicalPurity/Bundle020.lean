module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle011
public import Development.EtaleCohomology.CohomologicalPurity.Bundle012
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity

theorem injGeo_fib {X' X Z : Scheme.{0}} (f : X' ⟶ X) (ι' : Z ⟶ X') (ι : Z ⟶ X)
    (hp : IsPullback ι' (𝟙 Z) f ι) :
    pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f =
      pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.snd f f := by
  have h1 : (pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f) ≫ f =
      pullback.snd (pullback.fst f f ≫ f) ι ≫ ι := by
    rw [Category.assoc]; exact pullback.condition
  have h2 : (pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.snd f f) ≫ f =
      pullback.snd (pullback.fst f f ≫ f) ι ≫ ι := by
    rw [Category.assoc, ← pullback.condition]; exact h1
  have e1 := hp.lift_fst _ _ h1
  have e2 := hp.lift_fst _ _ h2
  have s1 := hp.lift_snd _ _ h1
  have s2 := hp.lift_snd _ _ h2
  rw [Category.comp_id] at s1 s2
  rw [← e1, ← e2, s1, s2]

theorem injGeo_fib_diag {X' X Z : Scheme.{0}} (f : X' ⟶ X) (ι' : Z ⟶ X') (ι : Z ⟶ X)
    (hp : IsPullback ι' (𝟙 Z) f ι) :
    pullback.fst (pullback.fst f f ≫ f) ι =
      (pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f) ≫ pullback.diagonal f := by
  apply pullback.hom_ext
  · simp
  · simp [injGeo_fib f ι' ι hp]

theorem injGeo_mem {X' X Z : Scheme.{0}} (f : X' ⟶ X) (ι' : Z ⟶ X') (ι : Z ⟶ X)
    (hp : IsPullback ι' (𝟙 Z) f ι) (q : ↑(pullback f f))
    (hq : (pullback.fst f f ≫ f) q ∈ Set.range ι) : q ∈ Set.range (pullback.diagonal f) := by
  obtain ⟨r, rfl⟩ : q ∈ Set.range (pullback.fst (pullback.fst f f ≫ f) ι) := by
    rw [Scheme.Pullback.range_fst]; exact hq
  rw [injGeo_fib_diag f ι' ι hp]
  exact ⟨(pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f) r, rfl⟩

theorem LeafInjGeo_of : LeafInjGeo := by
  intro X' X Z f _ ι' ι _ hp U hU T y₁ y₂ hy
  classical
  let p : T ⟶ pullback f f := pullback.lift y₁ y₂ hy
  let W : T.Opens := p ⁻¹ᵁ (pullback.diagonal f).opensRange
  let V : T.Opens := (y₁ ≫ f) ⁻¹ᵁ U
  have hW : ∀ (O : T.Opens), O ≤ W → O.ι ≫ y₁ = O.ι ≫ y₂ := by
    intro O hO
    have H : Set.range (O.ι ≫ p) ⊆ Set.range (pullback.diagonal f) := by
      rintro _ ⟨t, rfl⟩
      have := hO (show O.ι t ∈ O by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨t, rfl⟩)
      simpa [W] using this
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) (O.ι ≫ p) H
    have a1 : O.ι ≫ y₁ = (O.ι ≫ p) ≫ pullback.fst f f := by simp only [p, Category.assoc, pullback.lift_fst]
    have a2 : O.ι ≫ y₂ = (O.ι ≫ p) ≫ pullback.snd f f := by simp only [p, Category.assoc, pullback.lift_snd]
    rw [a1, a2, ← hl, Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
  let O : T → T.Opens := fun τ => if (y₁ ≫ f) τ ∈ (U : Set X) then V else W
  have hO : ∀ τ, O τ ≤ W ∨ O τ ≤ V := by
    intro τ; simp only [O]; split_ifs
    · exact Or.inr le_rfl
    · exact Or.inl le_rfl
  have hcov : ∀ τ, τ ∈ O τ := by
    intro τ; simp only [O]; split_ifs with h
    · simpa [V] using h
    · have h' : (y₁ ≫ f) τ ∈ Set.range ι := by
        have : (y₁ ≫ f) τ ∉ (Set.range ι)ᶜ := by rw [← hU]; exact h
        simpa using this
      have hq : (pullback.fst f f ≫ f) (p τ) ∈ Set.range ι := by
        have : p ≫ pullback.fst f f ≫ f = y₁ ≫ f := by simp only [p, pullback.lift_fst_assoc]
        rw [← this] at h'; simpa using h'
      simpa [W] using injGeo_mem f ι' ι hp (p τ) hq
  refine ⟨Sieve.generate (Presieve.ofArrows (fun τ => (O τ).toScheme) (fun τ => (O τ).ι)),
    Precoverage.generate_mem_toGrothendieck ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ?_), ?_⟩
  · refine ⟨fun τ => ⟨τ, ?_⟩, fun τ => inferInstance⟩
    exact ⟨⟨τ, hcov τ⟩, rfl⟩
  · rintro Y g ⟨Y', h, _, ⟨τ⟩, rfl⟩
    rcases hO τ with h1 | h1
    · left
      simp only [Category.assoc, hW _ h1]
    · right
      refine ⟨h ≫ (y₁ ≫ f).resLE U (O τ) h1, ?_⟩
      simp [Scheme.Hom.resLE_comp_ι]
end CohomologicalPurity
end LateralTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem affSieve_mem (U : Scheme.{0}) (S : Sieve U)
    (h : ∀ (A : Type) [CommRing A] (f : Spec (CommRingCat.of A) ⟶ U), S f) : S ∈ Scheme.etaleTopology U := by
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_ (Scheme.Cover.mem_grothendieckTopology U.affineCover)
  rintro _ _ ⟨_, k, _, ⟨i⟩, rfl⟩
  exact S.downward_closed (h _ (U.affineCover.f i)) k

theorem locBij {R : Type} [CommRing R] {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (φ : F ⟶ G)
    (h : ∀ (A : Type) [CommRing A], IsIso (φ.app (op (Spec (CommRingCat.of A))))) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology φ ∧ Presheaf.IsLocallySurjective Scheme.etaleTopology φ := by
  have hb : ∀ (A : Type) [CommRing A], Function.Bijective (φ.app (op (Spec (CommRingCat.of A)))) :=
    fun A _ => ConcreteCategory.bijective_of_isIso _
  refine ⟨⟨fun {X} x y hxy => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · refine affSieve_mem _ _ fun A _ f => ?_
    apply (hb A).1
    change φ.app _ (F.map f.op x) = φ.app _ (F.map f.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  · refine affSieve_mem _ _ fun A _ f => ?_
    obtain ⟨t, ht⟩ := (hb A).2 (G.map f.op s)
    exact ⟨t, ht⟩

theorem freeIso (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q)
    (h : ∀ (A : Type) [CommRing A], Function.Bijective (g.app (op (Spec (CommRingCat.of A))))) :
    IsIso ((free R).map g) := by
  have h2 : ∀ (A : Type) [CommRing A], IsIso (((freeP R).map g).app (op (Spec (CommRingCat.of A)))) := by
    intro A _
    have : IsIso (g.app (op (Spec (CommRingCat.of A)))) := (isIso_iff_bijective _).2 (h A)
    change IsIso ((uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R)).map (g.app (op (Spec (CommRingCat.of A)))))
    infer_instance
  obtain ⟨h3, h4⟩ := locBij _ h2
  have hW : Scheme.etaleTopology.W ((freeP R).map g) := by
    rw [GrothendieckTopology.W_iff_isLocallyBijective]; exact ⟨h3, h4⟩
  exact (GrothendieckTopology.W_iff _ _).1 hW

theorem chainsIso (R : Type) [CommRing R] {E E' : Spc} (e : E ⟶ E')
    (h : ∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
      (fun x : Sx E n (Spec (CommRingCat.of A)) => (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)) :
    IsIso ((chains R).map e) := by
  have : IsIso (((SimplicialObject.whiskering _ _).obj (free R)).map e) := by
    have hh : ∀ n, IsIso ((((SimplicialObject.whiskering _ _).obj (free R)).map e).app n) := by
      intro n
      induction n using Opposite.rec with | op n => ?_
      induction n using SimplexCategory.rec with | _ n => ?_
      exact freeIso R _ (h n)
    exact NatIso.isIso_of_isIso_app _
  change IsIso ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map
    ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map e)))
  infer_instance

theorem LeafAffEqv_of : LeafAffEqv := by
  intro hA1 q _ E E' e h i n
  have := chainsIso (ZMod q) e h
  exact hA1 (ZMod q) ((chains (ZMod q)).map e) (tw q i) n

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

abbrev evNU (n : ℕ) (U : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation _ _).obj (op (SimplexCategory.mk n)) ⋙ (evaluation _ _).obj (op U)

theorem pb_ext {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) {n : ℕ} {U : Scheme.{0}} (x y : Sx (pullback f g) n U)
    (h1 : ((pullback.fst f g).app _).app _ x = ((pullback.fst f g).app _).app _ y)
    (h2 : ((pullback.snd f g).app _).app _ x = ((pullback.snd f g).app _).app _ y) : x = y := by
  let G := evNU n U
  let I := PreservesPullback.iso G f g ≪≫ Types.pullbackIsoPullback (G.map f) (G.map g)
  have hi : Function.Injective I.hom := (isIso_iff_bijective I.hom).1 inferInstance |>.1
  apply hi
  apply Subtype.ext
  have a1 := (ConcreteCategory.congr_hom (PreservesPullback.iso_hom_fst G f g))
  have a2 := (ConcreteCategory.congr_hom (PreservesPullback.iso_hom_snd G f g))
  refine Prod.ext ?_ ?_
  · simp only [I, Iso.trans_hom]
    rw [types_comp_apply, types_comp_apply, Types.pullbackIsoPullback_hom_fst, Types.pullbackIsoPullback_hom_fst]
    exact (a1 x).trans (h1.trans (a1 y).symm)
  · simp only [I, Iso.trans_hom]
    rw [types_comp_apply, types_comp_apply, Types.pullbackIsoPullback_hom_snd, Types.pullbackIsoPullback_hom_snd]
    exact (a2 x).trans (h2.trans (a2 y).symm)

theorem pb_mk {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) {n : ℕ} {U : Scheme.{0}} (a : Sx X n U) (b : Sx Y n U)
    (h : (f.app _).app _ a = (g.app _).app _ b) : ∃ x : Sx (pullback f g) n U,
    ((pullback.fst f g).app _).app _ x = a ∧ ((pullback.snd f g).app _).app _ x = b := by
  let G := evNU n U
  let z : Types.PullbackObj (G.map f) (G.map g) := ⟨(a, b), h⟩
  refine ⟨(PreservesPullback.iso G f g).inv ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z), ?_, ?_⟩
  · have := (ConcreteCategory.congr_hom (PreservesPullback.iso_inv_fst G f g))
      ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z)
    refine this.trans ?_
    exact (ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_fst (G.map f) (G.map g))) z
  · have := (ConcreteCategory.congr_hom (PreservesPullback.iso_inv_snd G f g))
      ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z)
    refine this.trans ?_
    exact (ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_snd (G.map f) (G.map g))) z

theorem pr_ext {X Y : Spc} {n : ℕ} {U : Scheme.{0}} (x y : Sx (X ⨯ Y) n U)
    (h1 : ((prod.fst : X ⨯ Y ⟶ X).app _).app _ x = ((prod.fst : X ⨯ Y ⟶ X).app _).app _ y)
    (h2 : ((prod.snd : X ⨯ Y ⟶ Y).app _).app _ x = ((prod.snd : X ⨯ Y ⟶ Y).app _).app _ y) : x = y := by
  let G := evNU n U
  let I := PreservesLimitPair.iso G X Y ≪≫ Types.binaryProductIso (G.obj X) (G.obj Y)
  have hi : Function.Injective I.hom := (isIso_iff_bijective I.hom).1 inferInstance |>.1
  apply hi
  have a1 := (ConcreteCategory.congr_hom (prodComparison_fst G X Y))
  have a2 := (ConcreteCategory.congr_hom (prodComparison_snd G X Y))
  have b1 := (ConcreteCategory.congr_hom (Types.binaryProductIso_hom_comp_fst (G.obj X) (G.obj Y)))
  have b2 := (ConcreteCategory.congr_hom (Types.binaryProductIso_hom_comp_snd (G.obj X) (G.obj Y)))
  refine Prod.ext ?_ ?_
  · simp only [I, Iso.trans_hom, types_comp_apply, PreservesLimitPair.iso_hom]
    exact (b1 _).trans ((a1 x).trans (h1.trans ((a1 y).symm.trans (b1 _).symm)))
  · simp only [I, Iso.trans_hom, types_comp_apply, PreservesLimitPair.iso_hom]
    exact (b2 _).trans ((a2 x).trans (h2.trans ((a2 y).symm.trans (b2 _).symm)))

theorem um_basic {U : Scheme.{0}} {N : ℕ} (v : Fin N → Γ(U, ⊤)) (hv : Ideal.span (Set.range v) = ⊤) (p : U) :
    ∃ i : Fin N, 0 ≤ i.val ∧ p ∈ U.basicOpen (v i) := by
  have h := iSup_basicOpen_of_span_eq_top (X := U) ⊤ (Set.range v) hv
  have hp : p ∈ (⊤ : U.Opens) := trivial
  rw [← h] at hp
  obtain ⟨_, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  obtain ⟨⟨i, rfl⟩, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  exact ⟨i, Nat.zero_le _, hi⟩

theorem basic_um {A : Type} [CommRing A] {N : ℕ} (v : Fin N → Γ(Spec (CommRingCat.of A), ⊤))
    (hv : ∀ p, ∃ i : Fin N, 0 ≤ i.val ∧ p ∈ (Spec (CommRingCat.of A)).basicOpen (v i)) :
    Ideal.span (Set.range v) = ⊤ := by
  rw [← (isAffineOpen_top (Spec (CommRingCat.of A))).iSup_basicOpen_eq_self_iff]
  apply le_antisymm le_top
  intro p _
  obtain ⟨i, -, hi⟩ := hv p
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨v i, i, rfl⟩, hi⟩

def cstV (N : ℕ) (E : Spc) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (Functor.const (Fin (n.unop.len + 1))).obj (SingleObj.star (GL (Fin N) Γ(U.unop, ⊤)))
      naturality := fun U U' g => by
        ext x
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq ?_)
        exact (map_one (Matrix.GeneralLinearGroup.map _)).symm }
  naturality n m f := rfl

def conv {N n : ℕ} {U : Scheme.{0}} (c : ComposableArrows (Um N Γ(U, ⊤)) n)
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1) : ComposableArrows (Vec N 0 U) n where
  obj i := ⟨(c.obj i).1, um_basic _ (c.obj i).2⟩
  map {i j} h := ⟨(c.map h).1.2, fun k => by
    have := congrFun (c.map h).2 k
    rw [hc h] at this
    simpa using this⟩
  map_id i := Subtype.ext (congrArg (fun p => (Subtype.val p).2) (c.map_id i))
  map_comp f g := Subtype.ext (congrArg (fun p => (Subtype.val p).2) (c.map_comp f g))

theorem conv_congr {N n : ℕ} {U : Scheme.{0}} {c c' : ComposableArrows (Um N Γ(U, ⊤)) n} (e : c = c')
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1)
    (hc' : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c'.map h).1.1 = 1) : conv c hc = conv c' hc' := by
  subst e; rfl

theorem pb_gl {N : ℕ} {E : Spc} {n : SimplexCategoryᵒᵖ} {U : Scheme.{0}ᵒᵖ}
    (x : ((pullback (cstV N E) (PGL.pr N)).obj n).obj U) {i j : Fin (n.unop.len + 1)} (h : i ⟶ j) :
    ((((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x : ComposableArrows (Um N Γ(U.unop, ⊤)) n.unop.len).map h).1.1
      = 1 := by
  have e0 := ConcreteCategory.congr_hom
    (congrArg (fun φ : pullback (cstV N E) (PGL.pr N) ⟶ ofCat (glCat N) => (φ.app n).app U) (pullback.condition (f := cstV N E) (g := PGL.pr N))) x
  have e : ((Functor.const (Fin (n.unop.len + 1))).obj (SingleObj.star (GL (Fin N) Γ(U.unop, ⊤))) :
      ComposableArrows (SingleObj (GL (Fin N) Γ(U.unop, ⊤))) n.unop.len) =
      (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x : ComposableArrows (Um N Γ(U.unop, ⊤)) n.unop.len) ⋙
        Um.toGL N Γ(U.unop, ⊤) := e0
  have := Functor.congr_hom e.symm h
  exact this.trans ((Category.id_comp _).trans (Category.comp_id _))

def fMap (N : ℕ) (E : Spc) : pullback (cstV N E) (PGL.pr N) ⟶ Pj N 0 where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        (conv (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) (pb_gl x) : ComposableArrows (Vec N 0 U.unop) n.unop.len)
      naturality := fun U U' g => by
        ext x
        have e1 : (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U' (((pullback (cstV N E) (PGL.pr N)).obj n).map g x) :
            ComposableArrows (Um N Γ(U'.unop, ⊤)) n.unop.len) =
            ((PGL N).obj n).map g (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) :=
          ConcreteCategory.congr_hom (((pullback.snd (cstV N E) (PGL.pr N)).app n).naturality g) x
        refine (conv_congr e1 (pb_gl _) (by intro i j h; rw [← e1]; exact pb_gl _ h)).trans ?_
        exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl)) }
  naturality n m f := by
    ext U x
    have e1 : (((pullback.snd (cstV N E) (PGL.pr N)).app m).app U (((pullback (cstV N E) (PGL.pr N)).map f).app U x) :
        ComposableArrows (Um N Γ(U.unop, ⊤)) m.unop.len) =
        ((PGL N).map f).app U (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) :=
      ConcreteCategory.congr_hom (congrArg (fun φ : (pullback (cstV N E) (PGL.pr N)).obj n ⟶ (PGL N).obj m => φ.app U) ((pullback.snd (cstV N E) (PGL.pr N)).naturality f)) x
    refine (conv_congr e1 (pb_gl _) (by intro i j h; rw [← e1]; exact pb_gl _ h)).trans ?_
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl))

def back {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n where
  obj i := ⟨(w.obj i).1, basic_um _ (w.obj i).2⟩
  map h := ⟨(1, (w.map h).1), by funext k; simpa using (w.map h).2 k⟩
  map_id i := Subtype.ext (Prod.ext rfl (congrArg Subtype.val (w.map_id i)))
  map_comp f g := Subtype.ext (Prod.ext (one_mul 1).symm (congrArg Subtype.val (w.map_comp f g)))

theorem back_conv {A : Type} [CommRing A] {N n : ℕ} (c : ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n)
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1) : back (conv c hc) = c :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ h => heq_of_eq (Subtype.ext (Prod.ext (hc h).symm rfl)))

theorem conv_back {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    conv (back w) (fun _ => rfl) = w :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl))

theorem back_gl {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    ((Functor.const (Fin (n + 1))).obj (SingleObj.star (GL (Fin N) Γ(Spec (CommRingCat.of A), ⊤))) :
      ComposableArrows (SingleObj (GL (Fin N) Γ(Spec (CommRingCat.of A), ⊤))) n) = back w ⋙ Um.toGL N _ :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

theorem conv_inj {A : Type} [CommRing A] {N n : ℕ} {c c' : ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n}
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1)
    (hc' : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c'.map h).1.1 = 1) (e : conv c hc = conv c' hc') : c = c' :=
  (back_conv c hc).symm.trans ((congrArg back e).trans (back_conv c' hc'))

theorem fMap_line (N : ℕ) (E : Spc) : fMap N E ≫ Pj.line N 0 = pullback.snd (cstV N E) (PGL.pr N) ≫ PGL.line N := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

theorem eMap_bij (N : ℕ) (R : Type) [CommRing R] (n : ℕ) (A : Type) [CommRing A] : Function.Bijective
      (fun x : Sx (pullback (cstV N (sp R)) (PGL.pr N)) n (Spec (CommRingCat.of A)) =>
        ((prod.lift (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)) : _ ⟶ PR N 0 R).app
          (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x) := by
  have k1 := fun z => ConcreteCategory.congr_hom (congrArg (fun φ : pullback (cstV N (sp R)) (PGL.pr N) ⟶ Pj N 0 =>
        (φ.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A)))) (prod.lift_fst (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)))) z
  have k2 := fun z => ConcreteCategory.congr_hom (congrArg (fun φ : pullback (cstV N (sp R)) (PGL.pr N) ⟶ sp R =>
        (φ.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A)))) (prod.lift_snd (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)))) z
  constructor
  · intro x y hxy
    apply pb_ext
    · exact (k2 x).symm.trans ((congrArg _ hxy).trans (k2 y))
    · exact conv_inj (pb_gl x) (pb_gl y) ((k1 x).symm.trans ((congrArg _ hxy).trans (k1 y)))
  · intro z
    obtain ⟨x, hx1, hx2⟩ := pb_mk (cstV N (sp R)) (PGL.pr N) (n := n) (U := Spec (CommRingCat.of A))
      (((prod.snd : PR N 0 R ⟶ _).app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) z)
      (back (((prod.fst : PR N 0 R ⟶ _).app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) z))
      (back_gl _)
    refine ⟨x, pr_ext _ _ ?_ ?_⟩
    · exact (k1 x).trans ((conv_congr hx2 (pb_gl x) (fun _ => rfl)).trans (conv_back _))
    · exact (k2 x).trans hx1

theorem LeafPBMap_of : LeafPBMap := by
  set_option synthInstance.maxHeartbeats 100000 in
    exact fun N R _ =>
      ⟨cstV N (sp R), prod.lift (fMap N (sp R)) (pullback.fst _ _), prod.lift_snd _ _,
        by rw [prod.lift_fst_assoc]; exact fMap_line N (sp R), fun n A _ => eMap_bij N R n A⟩

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

theorem HK.pull_sub' (R : Type) [CommRing R] {K L : Cx R} (f g : K ⟶ L) (F : Shv R) (n : ℤ)
    (x : HK R L F n) : HK.pull R (f - g) F n x = HK.pull R f F n x - HK.pull R g F n x := by
  rcases x.mk_surjective with ⟨z, rfl⟩
  simp only [HK.pull, HK.pre, cpre_mk]
  rw [← CohomologyClass.mk_sub]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_sub, Cochain.sub_comp]

theorem HK.pull_zero' (R : Type) [CommRing R] {K L : Cx R} (F : Shv R) (n : ℤ)
    (x : HK R L F n) : HK.pull R (0 : K ⟶ L) F n x = 0 := by
  have h := HK.pull_sub' R (0 : K ⟶ L) 0 F n x
  rw [sub_self, sub_self] at h
  exact h

def secC (q : ℕ) (P : Arrow Spc) :
    cokernel ((chains (ZMod q)).map (dbl.inr P)) ⟶ (chains (ZMod q)).obj (dbl P) :=
  cokernel.desc _ (𝟙 _ - (chains (ZMod q)).map (dbl.fold P) ≫ (chains (ZMod q)).map (dbl.inr P)) (by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ← Functor.map_comp, dbl.inr_fold,
      CategoryTheory.Functor.map_id, Category.id_comp, sub_self])

theorem pi_secC (q : ℕ) (P : Arrow Spc) :
    cokernel.π ((chains (ZMod q)).map (dbl.inr P)) ≫ secC q P =
      𝟙 _ - (chains (ZMod q)).map (dbl.fold P) ≫ (chains (ZMod q)).map (dbl.inr P) := by
  simp [secC]

theorem secC_pi (q : ℕ) (P : Arrow Spc) :
    secC q P ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr P)) = 𝟙 _ := by
  rw [← cancel_epi (cokernel.π _), ← Category.assoc, pi_secC, Category.comp_id, Preadditive.sub_comp,
    Category.id_comp, Category.assoc, cokernel.condition, Limits.comp_zero, sub_zero]

def eHom (q : ℕ) (n i : ℤ) (P : Arrow Spc) :
    HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n →+ Hs q P n i :=
  (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n).codRestrict _ fun x => by
    change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.inr P)) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) = 0
    rw [← HK.pull_comp', cokernel.condition, HK.pull_zero']

def eEquiv (q : ℕ) (n i : ℤ) (P : Arrow Spc) :
    HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hs q P n i where
  toFun := eHom q n i P
  invFun y := HK.pull (ZMod q) (secC q P) (tw q i) n y.1
  left_inv x := by
    change HK.pull (ZMod q) (secC q P) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) = x
    rw [← HK.pull_comp', secC_pi, HK.pull_id']
  right_inv y := by
    apply Subtype.ext
    change HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n
      (HK.pull (ZMod q) (secC q P) (tw q i) n y.1) = y.1
    have hy : HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.inr P)) (tw q i) n y.1 = 0 := y.2
    rw [← HK.pull_comp', pi_secC, HK.pull_sub', HK.pull_id', HK.pull_comp', hy, map_zero, sub_zero]
  map_add' := map_add _

theorem EtaleExcIdent : LeafExcIdent := by
  intro q n i
  refine ⟨eEquiv q n i, fun {P' P} φ x => ?_⟩
  apply Subtype.ext
  change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.map φ)) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) =
    HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P'))) (tw q i) n
      (HK.pull (ZMod q) (cokC q φ) (tw q i) n x)
  rw [← HK.pull_comp', ← HK.pull_comp']
  congr 2
  simp [cokC]

end LateralTheory.CohomologicalPurity
end
end
