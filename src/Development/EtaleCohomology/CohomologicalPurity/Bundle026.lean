module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle016
public import Development.EtaleCohomology.CohomologicalPurity.Bundle017
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option linter.unusedSimpArgs false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.LocBasePf

theorem isPullback_of_app {K C : Type*} [Category K] [Category C] [HasPullbacks C] {P X Y Z : K ⥤ C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (h : ∀ k, IsPullback (fst.app k) (snd.app k) (f.app k) (g.app k)) : IsPullback fst snd f g :=
  IsPullback.of_isLimit (c := PullbackCone.mk fst snd w)
    (evaluationJointlyReflectsLimits _ fun k =>
      (isLimitMapConePullbackConeEquiv ((evaluation K C).obj k) w).symm (h k).isLimit)

section
variable {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
  (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {Y : Scheme.{0}} (g : Y ⟶ X)

include hc in
theorem cw {j k : J} (f : j ⟶ k) : D.map f ≫ c k = c j :=
  yoneda.map_injective (by simpa using hc j k f)

def D' : J ⥤ Scheme.{0} where
  obj j := pullback (c j) g
  map {j k} f := pullback.map (c j) g (c k) g (D.map f) (𝟙 Y) (𝟙 X) (by simp [cw D c hc f]) (by simp)
  map_id j := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id]
    exact (congrArg (pullback.fst (c j) g ≫ ·) (D.map_id j)).trans (Category.comp_id _)
  map_comp f f' := by apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id]

def c' (j : J) : (D' D c hc g).obj j ⟶ Y := pullback.snd (c j) g

theorem hc' : Coc (D' D c hc g ⋙ yoneda) fun j => yoneda.map (c' D c hc g j) := by
  intro j k f
  rw [Functor.comp_map, ← yoneda.map_comp]
  congr 1
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

def α : D' D c hc g ⋙ yoneda ⟶ D ⋙ yoneda where
  app j := yoneda.map (pullback.fst (c j) g)
  naturality j k f := by
    have e : (D' D c hc g).map f ≫ pullback.fst (c k) g = pullback.fst (c j) g ≫ D.map f := pullback.lift_fst _ _ _
    exact (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map e).trans (yoneda.map_comp _ _))

theorem sq : (hocF J).map (α D c hc g) ≫ aug _ hc = aug _ (hc' D c hc g) ≫ sch.map g := by
  ext n U x
  have key : ∀ j (a : unop U ⟶ pullback (c j) g), (a ≫ pullback.fst (c j) g) ≫ c j = (a ≫ pullback.snd (c j) g) ≫ g :=
    fun j a => by rw [Category.assoc, Category.assoc, pullback.condition]
  exact key _ _

theorem snd_map {j k : J} (f : j ⟶ k) {V : Scheme.{0}} (a : V ⟶ (D' D c hc g).obj j) :
    (a ≫ (D' D c hc g).map f) ≫ c' D c hc g k = a ≫ c' D c hc g j := by
  rw [Category.assoc]
  congr 1
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem snd_chain {n : ℕ} {U : Scheme.{0}ᵒᵖ} (z : Fin (n + 1) ⥤ ((D' D c hc g ⋙ yoneda).flip.obj U).Elements)
    (i : Fin (n + 1)) : (z.obj i).2 ≫ c' D c hc g (z.obj i).1 = (z.obj 0).2 ≫ c' D c hc g (z.obj 0).1 := by
  have m := (z.map (homOfLE (Fin.zero_le i))).2
  rw [← m]
  exact snd_map D c hc g _ _

include hc in
theorem c_chain {n : ℕ} {U : Scheme.{0}ᵒᵖ} (z : Fin (n + 1) ⥤ ((D ⋙ yoneda).flip.obj U).Elements)
    (i : Fin (n + 1)) : (z.obj i).2 ≫ c (z.obj i).1 = (z.obj 0).2 ≫ c (z.obj 0).1 := by
  have m := (z.map (homOfLE (Fin.zero_le i))).2
  rw [← m]
  change ((z.obj 0).2 ≫ D.map _) ≫ _ = _
  rw [Category.assoc, cw D c hc]

theorem pt_ext {U : Scheme.{0}ᵒᵖ} (p q : Σ j, unop U ⟶ pullback (c j) g)
    (h1 : (⟨p.1, p.2 ≫ pullback.fst (c p.1) g⟩ : Σ j, unop U ⟶ D.obj j) = ⟨q.1, q.2 ≫ pullback.fst (c q.1) g⟩)
    (h2 : p.2 ≫ pullback.snd (c p.1) g = q.2 ≫ pullback.snd (c q.1) g) : p = q := by
  obtain ⟨j, a⟩ := p
  obtain ⟨k, b⟩ := q
  simp only [Sigma.mk.injEq] at h1
  obtain ⟨rfl, h⟩ := h1
  have h' := eq_of_heq h
  congr 1
  exact pullback.hom_ext h' h2

include hc in
theorem lift_map {j k : J} (f : j ⟶ k) {V : Scheme.{0}} (a : V ⟶ D.obj j) (b : V ⟶ D.obj k) (y : V ⟶ Y)
    (ha : a ≫ c j = y ≫ g) (hb : b ≫ c k = y ≫ g) (hab : a ≫ D.map f = b) :
    (pullback.lift a y ha : V ⟶ (D' D c hc g).obj j) ≫ (D' D c hc g).map f = pullback.lift b y hb := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id, D', hab]

theorem pb : IsPullback ((hocF J).map (α D c hc g)) (aug _ (hc' D c hc g)) (aug _ hc) (sch.map g) := by
  refine isPullback_of_app (sq D c hc g) fun n => isPullback_of_app ?_ fun U => ?_
  · exact NatTrans.congr_app (sq D c hc g) n
  have elem_ext {F : J ⥤ Type} (a b : F.Elements)
      (h : (⟨a.obj, a.val⟩ : Σ j, F.obj j) = ⟨b.obj, b.val⟩) : a = b := by
    cases a
    cases b
    cases h
    rfl
  refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · exact NatTrans.congr_app (NatTrans.congr_app (sq D c hc g) n) U
  · rintro x y ⟨h1, h2⟩
    change chn x = chn y
    refine CategoryTheory.Functor.ext ?_ (fun _ _ _ => Functor.Elements.hom_ext (Subsingleton.elim _ _))
    intro i
    have he : (⟨((chn x).obj i).obj, ((chn x).obj i).val⟩ : Σ j, unop U ⟶ pullback (c j) g) =
        ⟨((chn y).obj i).obj, ((chn y).obj i).val⟩ := by
      refine pt_ext D c g _ _ ?_ ?_
      · have hh := congrArg (fun z => (chn z).obj i) h1
        exact congrArg (fun z => (⟨z.obj, z.val⟩ : Σ j, unop U ⟶ D.obj j)) hh
      · exact (snd_chain D c hc g (chn x) i).trans (h2.trans (snd_chain D c hc g (chn y) i).symm)
    exact elem_ext _ _ he
  · intro x₂ x₃ h
    have e : ∀ i, ((chn x₂).obj i).2 ≫ c ((chn x₂).obj i).1 = x₃ ≫ g := fun i =>
      (c_chain D c hc (chn x₂) i).trans h
    refine ⟨mkChn (F := (D' D c hc g ⋙ yoneda).flip.obj U) (chn x₂ ⋙ CategoryOfElements.π _)
      (fun i => pullback.lift ((chn x₂).obj i).2 x₃ (e i)) (fun i k f => ?_), ?_, ?_⟩
    · exact lift_map D c hc g _ _ _ x₃ _ _ ((chn x₂).map f).2
    · change chn _ = chn x₂
      refine CategoryTheory.Functor.ext ?_ (fun _ _ _ => Functor.Elements.hom_ext (Subsingleton.elim _ _))
      intro i
      apply elem_ext
      refine Sigma.ext rfl (heq_of_eq ?_)
      change pullback.lift _ _ _ ≫ pullback.fst (c ((chn x₂).obj i).1) g = _
      exact pullback.lift_fst _ _ _
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ = x₃
      exact pullback.lift_snd _ _ _

end

theorem hr {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
    (ho : ∀ j, IsOpenImmersion (c j)) (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {Y : Scheme.{0}} (g : Y ⟶ X)
    (j : J) (y : Y) : y ∈ Set.range (c' D c hc g j) ↔ g y ∈ Set.range (c j) := by
  have := ho j
  change y ∈ Set.range (pullback.snd (c j) g) ↔ _
  rw [IsOpenImmersion.range_pullbackSnd]
  rfl

end LateralTheory.CohomologicalPurity.TubeCut.LocBasePf

namespace LateralTheory.CohomologicalPurity.TubeCut
open LocBasePf

theorem LeafLocBase_of : EtaleLocBase := by
  intro J _ D X c ho hcov hdir hc Y g
  refine ⟨D' D c hc g, c' D c hc g, ?_, ?_, ?_, hc' D c hc g, ⟨?_⟩⟩
  · intro j
    have := ho j
    change IsOpenImmersion (pullback.snd (c j) g)
    infer_instance
  · intro y
    obtain ⟨j, hj⟩ := hcov (g y)
    exact ⟨j, (hr D c ho hc g j y).2 hj⟩
  · intro y j k h1 h2
    obtain ⟨l, hl1, hl2, hl⟩ := hdir (g y) j k ((hr D c ho hc g j y).1 h1) ((hr D c ho hc g k y).1 h2)
    exact ⟨l, hl1, hl2, (hr D c ho hc g l y).2 hl⟩
  · exact Arrow.isoMk (pb D c hc g).isoPullback.symm (Iso.refl _)
      ((IsPullback.isoPullback_inv_snd _).trans (Category.comp_id _).symm)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.PbSumPf

theorem types_univ {A : Type} {F : Discrete A ⥤ Type} (c : Cocone F) (hc : IsColimit c) :
    IsUniversalColimit c := by
  intro F' c' α f e _ H
  let i' : Discrete.functor (fun a => F'.obj ⟨a⟩) ≅ F' := Discrete.natIso (fun _ => Iso.refl _)
  let i : Discrete.functor (fun a => F.obj ⟨a⟩) ≅ F := Discrete.natIso (fun _ => Iso.refl _)
  let d : Cofan (fun a => F'.obj ⟨a⟩) := (Cocone.precompose i'.hom).obj c'
  let b : Cofan (fun a => F.obj ⟨a⟩) := (Cocone.precompose i.hom).obj c
  have hb : IsColimit b := (IsColimit.precomposeHomEquiv i c).symm hc
  have hd : ∀ a z, d.inj a z = c'.ι.app ⟨a⟩ z := fun _ _ => rfl
  have hbi : ∀ a z, b.inj a z = c.ι.app ⟨a⟩ z := fun _ _ => rfl
  have e1 : ∀ j x, c.ι.app j (α.app j x) = f (c'.ι.app j x) := fun j x => by
    have := ConcreteCategory.congr_hom (NatTrans.congr_app e j) x
    simpa using this
  refine ⟨(IsColimit.precomposeHomEquiv i' c') ((Cofan.nonempty_isColimit_iff_bijective_fromSigma d).2 ⟨?_, ?_⟩).some⟩
  · rintro ⟨a, z⟩ ⟨a', w⟩ h
    change d.inj a z = d.inj a' w at h
    rw [hd, hd] at h
    have h2 : b.inj a (α.app ⟨a⟩ z) = b.inj a' (α.app ⟨a'⟩ w) := by
      rw [hbi, hbi, e1, e1, h]
    obtain rfl := Cofan.eq_of_inj_apply_eq_of_isColimit hb _ _ h2
    have h3 := Cofan.inj_injective_of_isColimit hb a h2
    have := Types.ext_of_isPullback (H ⟨a⟩) h h3
    subst this
    rfl
  · intro y
    obtain ⟨a, x, hx⟩ := Cofan.inj_jointly_surjective_of_isColimit hb (f y)
    rw [hbi] at hx
    obtain ⟨z, hz1, _⟩ := Types.exists_of_isPullback (H ⟨a⟩) y x hx.symm
    exact ⟨⟨a, z⟩, hz1⟩

theorem univ_of_eval {J C D : Type*} [Category J] [Category C] [Category D] [HasPullbacks D]
    (F : J ⥤ C ⥤ D) (c : Cocone F)
    (hc : ∀ x : C, IsUniversalColimit (((evaluation C D).obj x).mapCocone c)) : IsUniversalColimit c := by
  intro F' c' α f e hα H
  exact ⟨evaluationJointlyReflectsColimits _ fun x =>
    (hc x (((evaluation C D).obj x).mapCocone c') (Functor.whiskerRight α _) (((evaluation C D).obj x).map f)
      (by ext y; dsimp; exact NatTrans.congr_app (NatTrans.congr_app e y) x)
      (hα.whiskerRight _) fun j => (H j).map ((evaluation C D).obj x)).some⟩

theorem spc_univ {A : Type} (F : Discrete A ⥤ Spc) (c : Cocone F) (hc : IsColimit c) : IsUniversalColimit c :=
  univ_of_eval (C := SimplexCategoryᵒᵖ) (D := PSh) F c fun n =>
    univ_of_eval (C := Scheme.{0}ᵒᵖ) (D := Type) _ _ fun Y =>
      types_univ _ (isColimitOfPreserves _ (isColimitOfPreserves ((evaluation _ _).obj n) hc))

theorem pb_of_eq {C : Type*} [Category C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f f' : X ⟶ Z} {g : Y ⟶ Z}
    (e : f = f') (hp : IsPullback fst snd f' g) : IsPullback fst snd f g := by subst e; exact hp

theorem pb_of_eq_snd {C : Type*} [Category C] {P X Y Z : C} {fst : P ⟶ X} {snd snd' : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (e : snd = snd') (hp : IsPullback fst snd' f g) : IsPullback fst snd f g := by subst e; exact hp

end LateralTheory.CohomologicalPurity.TubeCut.PbSumPf

namespace LateralTheory.CohomologicalPurity.TubeCut
open PbSumPf

theorem LeafPbSum_of : LeafPbSum := by
  intro X U A E c hc π π' h
  have hS := (leafDiscSumH A E c hc).some
  have Uv := spc_univ _ _ hS
  let g := sch.map U.ι
  refine Uv (Cofan.mk (abv U (E := disc.obj c.pt) (disc.map π)).left
      fun a => (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left)
    (Discrete.natTrans fun a => pullback.fst (disc.map (π' a.as)) g)
    (pullback.fst (disc.map π) g) ?_ (.of_discrete _) ?_
  · apply NatTrans.ext; funext ⟨a⟩
    exact (pullback.lift_fst (f := disc.map π) (g := g) _ _ _).symm
  · rintro ⟨a⟩
    have outer : IsPullback (pullback.fst (disc.map (π' a)) g)
        ((abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left ≫ pullback.snd (disc.map π) g)
        (disc.map (c.inj a) ≫ disc.map π) g := by
      have e2 : (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left ≫ pullback.snd (disc.map π) g
          = pullback.snd (disc.map (π' a)) g := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
      exact pb_of_eq_snd e2 (pb_of_eq (h a) (IsPullback.of_hasPullback _ _))
    have sq := IsPullback.of_bot outer (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback (disc.map π) g)
    exact sq.flip

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

section
variable (R : Type) [CommRing R]

instance pcFreeP : PreservesColimitsOfShape WalkingSpan (freeP R) := by
  have : PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1} R)) :=
    (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} R)) :=
    inferInstance
  unfold freeP; infer_instance

instance pcFree : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free; infer_instance

instance pcWhisk : PreservesColimitsOfShape WalkingSpan ((SimplicialObject.whiskering _ _).obj (free R)) := by
  unfold SimplicialObject.whiskering; infer_instance

instance preservesSpanColimitsFaceMapComplex : PreservesColimitsOfShape WalkingSpan (AlgebraicTopology.alternatingFaceMapComplex (Shv R)) := by
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n => ?_)
  have e : AlgebraicTopology.alternatingFaceMapComplex (Shv R) ⋙ HomologicalComplex.eval _ _ n ≅
      (evaluation _ _).obj (op (SimplexCategory.mk n)) :=
    NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
      dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  exact preservesColimitsOfShape_of_natIso e.symm

instance pcExt : PreservesColimitsOfShape WalkingSpan
    (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) := by
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i => ?_)
  by_cases h : ∃ j, ComplexShape.embeddingDownNat.f j = i
  · obtain ⟨j, hj⟩ := h
    have e : ComplexShape.embeddingDownNat.extendFunctor (Shv R) ⋙ HomologicalComplex.eval _ _ i ≅
        HomologicalComplex.eval _ _ j :=
      NatIso.ofComponents (fun K => K.extendXIso _ hj) (fun f => by
        change (HomologicalComplex.extendMap f _).f i ≫ _ = _ ≫ f.f j
        rw [HomologicalComplex.extendMap_f _ _ hj]; simp)
    exact preservesColimitsOfShape_of_natIso e.symm
  · refine Functor.preservesColimitsOfShape_of_isZero _ ?_ _
    rw [Functor.isZero_iff]
    intro K
    exact K.isZero_extend_X _ i (fun j hj => h ⟨j, hj⟩)

instance pcChains : PreservesColimitsOfShape WalkingSpan (chains R) := by
  unfold chains chainsN; infer_instance

end

theorem LeafChPush_of : LeafChPush := by
  intro q P
  set_option synthInstance.maxHeartbeats 200000 in
    have h : IsPushout P.hom P.hom (dbl.inl P) (dbl.inr P) := IsPushout.of_hasPushout _ _
    exact (chains (ZMod q)).map_isPushout h

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

section Gen
variable {C : Type*} [Category C] [Abelian C] {A B D Q I : CochainComplex C ℤ}

def hsCok (f : A ⟶ B) (l r : B ⟶ D) (hpo : IsPushout f f l r) (p : D ⟶ cokernel f)
    (hl : l ≫ p = cokernel.π f) (hr : r ≫ p = 0) : IsColimit (CokernelCofork.ofπ p hr) :=
  CokernelCofork.IsColimit.ofπ p hr
    (fun g' _ => cokernel.desc f (l ≫ g') (by rw [← Category.assoc, hpo.w, Category.assoc]; simp [*]))
    (fun g' eq' => by
      apply hpo.hom_ext
      · rw [← Category.assoc, hl, cokernel.π_desc]
      · rw [← Category.assoc, hr, zero_comp, eq'])
    (fun g' eq' m hm => by
      apply (cancel_epi (cokernel.π f)).1
      rw [cokernel.π_desc, ← hl, Category.assoc, hm])

def hsCokDeg {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) (k : ℤ) :
    IsColimit ((CokernelCofork.ofπ p hr).map (HomologicalComplex.eval C _ k)) :=
  CokernelCofork.mapIsColimit _ hc _

def hsCokDeg' {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) (k : ℤ) :
    IsColimit (CokernelCofork.ofπ (f := r.f k) (p.f k) (by rw [← HomologicalComplex.comp_f, hr]; rfl)) :=
  hsCokDeg hr hc k

theorem hsFac {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) {m : ℤ}
    (z : Cochain D I m) (hz : (Cochain.ofHom r).comp z (zero_add m) = 0) :
    ∃ y : Cochain Q I m, (Cochain.ofHom p).comp y (zero_add m) = z := by
  have key : ∀ a b (h : a + m = b), r.f a ≫ z.v a b h = 0 := fun a b h => by
    have := congrArg (fun w => w.v a b h) hz
    simpa [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using this
  refine ⟨Cochain.mk (fun a b h => (CokernelCofork.IsColimit.desc' (hsCokDeg' hr hc a) (z.v a b h) (key a b h)).1), ?_⟩
  ext a b h
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  exact (CokernelCofork.IsColimit.desc' (hsCokDeg' hr hc a) (z.v a b h) (key a b h)).2

theorem hsCancel {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) {m : ℤ}
    (y₁ y₂ : Cochain Q I m) (h : (Cochain.ofHom p).comp y₁ (zero_add m) = (Cochain.ofHom p).comp y₂ (zero_add m)) :
    y₁ = y₂ := by
  ext a b hab
  have := congrArg (fun w => w.v a b hab) h
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at this
  have : Epi (p.f a) := epi_of_isColimit_cofork (hsCokDeg' hr hc a)
  exact (cancel_epi (p.f a)).1 ‹_›

theorem hsRS {r : B ⟶ D} {s : D ⟶ B} (hrs : r ≫ s = 𝟙 _) {m : ℤ} (z : Cochain B I m) :
    (Cochain.ofHom r).comp ((Cochain.ofHom s).comp z (zero_add m)) (zero_add m) = z := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hrs]
  ext a b h
  simp

theorem hsRP {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) {m : ℤ} (z : Cochain Q I m) :
    (Cochain.ofHom r).comp ((Cochain.ofHom p).comp z (zero_add m)) (zero_add m) = 0 := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hr, Cochain.ofHom_zero, Cochain.zero_comp]

theorem hsInj {r : B ⟶ D} {s : D ⟶ B} {p : D ⟶ Q} (hrs : r ≫ s = 𝟙 _) (hr : r ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p hr)) (n : ℤ) :
    Function.Injective (cpre (Cocycle.ofHom p) I n n (zero_add n)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
  obtain ⟨β, hβ⟩ := hx
  change δ (n - 1) n β = (Cochain.ofHom p).comp x.1 (zero_add n) at hβ
  obtain ⟨γ, hγ⟩ := hsFac hr hc (β - (Cochain.ofHom s).comp ((Cochain.ofHom r).comp β (zero_add _)) (zero_add _))
    (by rw [Cochain.comp_sub, hsRS hrs, sub_self])
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨γ, hsCancel hr hc _ _ ?_⟩
  rw [← δ_ofHom_comp, hγ, δ_sub, δ_ofHom_comp, δ_ofHom_comp, hβ, hsRP hr, Cochain.comp_zero, sub_zero]

theorem hsExact {r : B ⟶ D} {s : D ⟶ B} {p : D ⟶ Q} (hrs : r ≫ s = 𝟙 _) (hr : r ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p hr)) (n : ℤ) (x : CohomologyClass D I n)
    (hx : cpre (Cocycle.ofHom r) I n n (zero_add n) x = 0) :
    ∃ y, cpre (Cocycle.ofHom p) I n n (zero_add n) y = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
  obtain ⟨β, hβ⟩ := hx
  change δ (n - 1) n β = (Cochain.ofHom r).comp x.1 (zero_add n) at hβ
  obtain ⟨y, hy⟩ := hsFac hr hc (x.1 - δ (n - 1) n ((Cochain.ofHom s).comp β (zero_add _)))
    (by rw [Cochain.comp_sub, δ_ofHom_comp, hsRS hrs, hβ, sub_self])
  have hδ : δ n (n + 1) y = 0 := by
    apply hsCancel hr hc
    rw [← δ_ofHom_comp, hy, δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero, Cochain.comp_zero]
  refine ⟨CohomologyClass.mk (Cocycle.mk y (n + 1) rfl hδ), ?_⟩
  change CohomologyClass.mk _ = _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨-((Cochain.ofHom s).comp β (zero_add _)), ?_⟩
  change _ = (Cochain.ofHom p).comp y (zero_add n) - x.1
  rw [hy, δ_neg]; abel

end Gen

theorem LeafHKSplit_of : LeafHKSplit := by
  intro R _ F n A B D f l r s hpo hrs p hl hr
  have hc := hsCok f l r hpo p hl hr
  exact ⟨hsInj hrs hr hc n, fun x hx => hsExact hrs hr hc n x hx⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end
