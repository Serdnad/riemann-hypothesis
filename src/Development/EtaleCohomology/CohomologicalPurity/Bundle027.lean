module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle017
public import Development.EtaleCohomology.CohomologicalPurity.LeafDictPf
public import Development.EtaleCohomology.KummerTheory.Bundle011
public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
public import Development.EtaleCohomology.CohomologicalPurity.Bundle016
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
import Mathlib.Tactic.Linter.Style
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

instance discPC : PreservesColimitsOfSize.{0, 0} disc :=
  inferInstanceAs (PreservesColimitsOfSize.{0, 0} (Functor.const SimplexCategoryᵒᵖ : PSh ⥤ _))

def pbMapIso {C D : Type*} [Category C] [Category D] (Fn : C ⥤ D) {B G A' A : C} (g : G ⟶ B) (a : A' ⟶ A)
    (π' : A' ⟶ B) (π : A ⟶ B) (h : a ≫ π = π') [HasPullback π' g] [HasPullback π g]
    [HasPullback (Fn.map π') (Fn.map g)] [HasPullback (Fn.map π) (Fn.map g)]
    [PreservesLimit (cospan π' g) Fn] [PreservesLimit (cospan π g) Fn] :
    Arrow.mk (Fn.map (pullback.map π' g π g a (𝟙 _) (𝟙 _) (by simp [h]) (by simp))) ≅
    Arrow.mk (pullback.map (Fn.map π') (Fn.map g) (Fn.map π) (Fn.map g) (Fn.map a) (𝟙 _) (𝟙 _)
      (by simp [← Fn.map_comp, h]) (by simp)) :=
  Arrow.isoMk (PreservesPullback.iso Fn π' g) (PreservesPullback.iso Fn π g) (by
    apply pullback.hom_ext
    · simp only [Arrow.mk_hom, Category.assoc, pullback.lift_fst, PreservesPullback.iso_hom_fst,
        PreservesPullback.iso_hom_fst_assoc, ← Fn.map_comp]
    · simp only [Arrow.mk_hom, Category.assoc, pullback.lift_snd, PreservesPullback.iso_hom_snd, ← Fn.map_comp, Category.comp_id])

theorem types_pb {A : Type} {E : A → Type} {P Y G : Type} (ι : ∀ a, E a ⟶ P) (hP : Nonempty (IsColimit (Cofan.mk P ι)))
    (p : P ⟶ Y) (g : G ⟶ Y) (e : ∀ a, E a ⟶ Y) (he : ∀ a, ι a ≫ p = e a)
    {Q : Type} (fst : Q ⟶ P) (snd : Q ⟶ G) (w : fst ≫ p = snd ≫ g) (hQ : IsLimit (PullbackCone.mk fst snd w))
    {Q' : A → Type} (fst' : ∀ a, Q' a ⟶ E a) (snd' : ∀ a, Q' a ⟶ G) (w' : ∀ a, fst' a ≫ e a = snd' a ≫ g)
    (hQ' : ∀ a, IsLimit (PullbackCone.mk (fst' a) (snd' a) (w' a)))
    (j : ∀ a, Q' a ⟶ Q) (hj1 : ∀ a, j a ≫ fst = fst' a ≫ ι a) (hj2 : ∀ a, j a ≫ snd = snd' a) :
    Nonempty (IsColimit (Cofan.mk Q j)) := by
  rw [Cofan.nonempty_isColimit_iff_bijective_fromSigma] at hP ⊢
  have J1 : ∀ a y, fst (j a y) = ι a (fst' a y) := fun a y => ConcreteCategory.congr_hom (hj1 a) y
  have J2 : ∀ a y, snd (j a y) = snd' a y := fun a y => ConcreteCategory.congr_hom (hj2 a) y
  constructor
  · rintro ⟨a, y⟩ ⟨b, z⟩ hyz
    have hyz' : j a y = j b z := hyz
    have h1 : ι a (fst' a y) = ι b (fst' b z) := by rw [← J1, ← J1, hyz']
    have h2 : snd' a y = snd' b z := by rw [← J2, ← J2, hyz']
    have h3 := hP.1 (a₁ := ⟨a, fst' a y⟩) (a₂ := ⟨b, fst' b z⟩) h1
    obtain ⟨rfl, h4⟩ := Sigma.mk.inj_iff.mp h3
    have h4' : fst' a y = fst' a z := eq_of_heq h4
    have : y = z := PullbackCone.IsLimit.type_ext (hQ' a) h4' h2
    subst this; rfl
  · intro q
    obtain ⟨⟨a, u⟩, hu⟩ := hP.2 (fst q)
    have hu' : ι a u = fst q := hu
    have hc : e a u = g (snd q) := by
      rw [← ConcreteCategory.congr_hom (he a) u]
      change p (ι a u) = g (snd q)
      rw [hu']
      exact ConcreteCategory.congr_hom w q
    let y : Q' a := (PullbackCone.IsLimit.equivPullbackObj (hQ' a)).symm ⟨(u, snd q), hc⟩
    have y1 : fst' a y = u := PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst (hQ' a) _
    have y2 : snd' a y = snd q := PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd (hQ' a) _
    refine ⟨⟨a, y⟩, ?_⟩
    change j a y = q
    refine PullbackCone.IsLimit.type_ext hQ ?_ ?_
    · change fst (j a y) = fst q
      rw [J1, y1, hu']
    · change snd (j a y) = snd q
      rw [J2, y2]

theorem psh_pb {A : Type} {E : A → PSh} {P Y G : PSh} (ι : ∀ a, E a ⟶ P) (hP : Nonempty (IsColimit (Cofan.mk P ι)))
    (p : P ⟶ Y) (g : G ⟶ Y) (e : ∀ a, E a ⟶ Y) (he : ∀ a, ι a ≫ p = e a) :
    Nonempty (IsColimit (Cofan.mk (pullback p g) fun a =>
      pullback.map (e a) g p g (ι a) (𝟙 _) (𝟙 _) (by simp [he]) (by simp))) := by
  obtain ⟨hP⟩ := hP
  refine ⟨evaluationJointlyReflectsColimits _ fun U => (isColimitMapCoconeCofanMkEquiv _ _ _).symm ?_⟩
  have hPU := isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj U) _ _ hP
  have hQ := isLimitPullbackConeMapOfIsLimit ((evaluation _ _).obj U) pullback.condition (pullbackIsPullback p g)
  have hQ' := fun a => isLimitPullbackConeMapOfIsLimit ((evaluation _ _).obj U) pullback.condition
    (pullbackIsPullback (e a) g)
  exact (types_pb _ ⟨hPU⟩ _ _ _ (fun a => congrArg (fun t => NatTrans.app t U) (he a)) _ _ _ hQ _ _ _ hQ' _
    (fun a => by rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst])
    (fun a => by rw [← Functor.map_comp, pullback.lift_snd, Category.comp_id])).some

theorem inj_aug_RRelL {J : Type} [SmallCategory J] {Y : PSh} (Dx : J ⥤ PSh) (cx : ∀ j, Dx.obj j ⟶ Y) (hcx : Coc Dx cx)
    (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) : inj Dx n σ ≫ (aug cx hcx).app n = cx (σ.obj 0) := by
  ext U x
  have e : (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1))) : (0 : Fin _) ⟶ 0) = 𝟙 _ := Subsingleton.elim _ _
  change (cx (σ.obj 0)).app U ((Dx.map (σ.map (homOfLE (Fin.zero_le 0)))).app U x) = (cx (σ.obj 0)).app U x
  rw [e, σ.map_id, Dx.map_id]; rfl

theorem inj_nat {J : Type} [SmallCategory J] {D' D : J ⥤ PSh} (α : D' ⟶ D) (n : SimplexCategoryᵒᵖ)
    (σ : Fin (n.unop.len + 1) ⥤ J) : inj D' n σ ≫ ((hocF J).map α).app n = α.app (σ.obj 0) ≫ inj D n σ := by
  ext U x
  exact mkChn_congr (F := D.flip.obj U) σ
    (funext fun i => ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality (σ.map (homOfLE (Fin.zero_le i)))) U) x) _ _

theorem LeafRelLev_of : LeafRelLev := by
  intro hL J _ D' D α Y G g c' c hc' hc h h' n
  have hj : ∀ j, α.app j ≫ c j = c' j := fun j => congrArg (fun t => NatTrans.app t (op (SimplexCategory.mk 0))) (h j)
  have hn : ((hocF J).map α).app n ≫ (aug c hc).app n = (aug c' hc').app n := congrArg (fun t => NatTrans.app t n) h'
  refine ⟨Fin (n.unop.len + 1) ⥤ J, fun σ => σ.obj 0, fun σ => disc.obj (pullback (c' (σ.obj 0)) g),
    fun σ => disc.obj (pullback (c (σ.obj 0)) g),
    Cofan.mk (disc.obj (pullback ((aug c' hc').app n) g)) (fun σ => disc.map (pullback.map _ _ _ _ (inj D' n σ)
      (𝟙 _) (𝟙 _) (by simp [inj_aug_RRelL]) (by simp))),
    Cofan.mk (disc.obj (pullback ((aug c hc).app n) g)) (fun σ => disc.map (pullback.map _ _ _ _ (inj D n σ)
      (𝟙 _) (𝟙 _) (by simp [inj_aug_RRelL]) (by simp))),
    fun σ => disc.map (pullback.map _ _ _ _ (α.app (σ.obj 0)) (𝟙 _) (𝟙 _) (by simp [hj]) (by simp)),
    disc.map (pullback.map _ _ _ _ (((hocF J).map α).app n) (𝟙 _) (𝟙 _) (by simp [hn]) (by simp)),
    ⟨isColimitCofanMkObjOfIsColimit disc _ _ (psh_pb _ (hL J D' n) _ g _ (inj_aug_RRelL D' c' hc' n)).some⟩,
    ⟨isColimitCofanMkObjOfIsColimit disc _ _ (psh_pb _ (hL J D n) _ g _ (inj_aug_RRelL D c hc n)).some⟩, ?_, ?_, ?_⟩
  · intro σ
    change disc.map _ ≫ disc.map _ = disc.map _ ≫ disc.map _
    rw [← disc.map_comp, ← disc.map_comp]
    congr 1
    apply pullback.hom_ext <;>
      simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, Category.comp_id]
    rw [inj_nat]
  · intro σ
    exact ⟨(pbMapIso disc g (α.app (σ.obj 0)) (c' (σ.obj 0)) (c (σ.obj 0)) (hj _)).symm⟩
  · have e := (pbMapIso ((evaluation _ _).obj n) (disc.map g) ((hocF J).map α) (aug c' hc') (aug c hc) h').symm
    exact ⟨disc.mapArrow.mapIso e⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.DictPf

theorem LeafDbl_pf : LeafDbl := by
  refine ⟨fun U => (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm, ?_, ?_, ?_⟩
  · intro X U
    exact PreservesPushout.inl_iso_inv disc _ _
  · intro X U
    exact PreservesPushout.inr_iso_inv disc _ _
  · intro X' X f U' U h
    dsimp only
    refine (Iso.inv_comp_eq _).1 ?_
    set_option synthInstance.maxHeartbeats 200000 in
      apply pushout.hom_ext
    · have a1 : pushout.inl (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom =
          disc.map (pushout.inl _ _) := PreservesPushout.inl_iso_hom disc _ _
      have a2 : disc.map (pushout.inl (yoneda.map U.ι) (yoneda.map U.ι)) ≫
          (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = pushout.inl (opn U).hom (opn U).hom :=
        PreservesPushout.inl_iso_inv disc _ _
      have il : pushout.inl _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inl _ _ := pushout.inl_desc _ _ _
      show pushout.inl (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom ≫
        disc.map (Qmap f U' U h) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = _
      erw [← Category.assoc, a1, ← Category.assoc, ← Functor.map_comp, il, Functor.map_comp, Category.assoc, a2]
      exact (pushout.inl_desc _ _ _).symm
    · have a1 : pushout.inr (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom =
          disc.map (pushout.inr _ _) := PreservesPushout.inr_iso_hom disc _ _
      have a2 : disc.map (pushout.inr (yoneda.map U.ι) (yoneda.map U.ι)) ≫
          (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = pushout.inr (opn U).hom (opn U).hom :=
        PreservesPushout.inr_iso_inv disc _ _
      have il : pushout.inr _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inr _ _ := pushout.inr_desc _ _ _
      show pushout.inr (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom ≫
        disc.map (Qmap f U' U h) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = _
      erw [← Category.assoc, a1, ← Category.assoc, ← Functor.map_comp, il, Functor.map_comp, Category.assoc, a2]
      exact (pushout.inr_desc _ _ _).symm

theorem LeafDict_of' (hD : Cl.LeafDisc) (hE : LeafEv) (hP : LeafPair) : Cl.LeafDict := LeafDict_of hD hE hP LeafDbl_pf

end LateralTheory.CohomologicalPurity.DictPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.KummerTheory.FlasquePf

namespace LateralTheory.CohomologicalPurity.LeafPairPf

instance presFreeMod (R : Type) [CommRing R] :
    PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1, 0} R)) :=
  (ModuleCat.adj (ULift.{1, 0} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape

instance presL (R : Type) [CommRing R] :
    PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1, 0} R)) :=
  inferInstance

instance presFreeP (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (freeP R) := by
  unfold freeP; infer_instance

instance presFree (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free; infer_instance

theorem gen_eq {R : Type} [CommRing R] {G : Shv R} {X V : Scheme.{0}} (m : (free R).obj (yoneda.obj X) ⟶ G)
    (g : V ⟶ X) : (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V g) = Sec.res g (DictPf.ev m) := by
  have nat := congrArg (fun k => k.hom (freeGen R (yoneda.obj X) X (𝟙 X))) (m.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at nat
  change _ = (G.obj.map g.op).hom ((m.hom.app (op X)).hom (freeGen R (yoneda.obj X) X (𝟙 X)))
  rw [← nat]
  change _ = (m.hom.app (op V)).hom (Sec.res g (freeGen R (yoneda.obj X) X (𝟙 X)))
  rw [freeGen_res]
  congr 2

theorem ext_gen {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (m m' : (free R).obj (yoneda.obj X) ⟶ G)
    (h : DictPf.ev m = DictPf.ev m') : m = m' := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  ext V : 2
  apply ModuleCat.free_hom_ext
  intro x
  change (m.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down) = (m'.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down)
  rw [gen_eq m x.down, gen_eq m' x.down, h]

theorem ev_ofSec {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (s : Sec G X) : DictPf.ev (ofSec G s) = s :=
  ofSec_gen G s

theorem ev_pre {R : Type} [CommRing R] {G : Shv R} {Y X : Scheme.{0}} (f : Y ⟶ X)
    (m : (free R).obj (yoneda.obj X) ⟶ G) : DictPf.ev ((free R).map (yoneda.map f) ≫ m) = Sec.res f (DictPf.ev m) := by
  rw [← gen_eq]
  change (m.hom.app (op Y)).hom ((((free R).map (yoneda.map f)).hom.app (op Y)).hom (freeGen R (yoneda.obj Y) Y (𝟙 Y))) = _
  rw [freeGen_map]
  congr 2

theorem LeafPair_of : DictPf.LeafPair := by
  intro R _ G X U
  refine ⟨fun s s' hs => ?_, fun m m' h1 h2 => ?_⟩
  · have w : (free R).map (yoneda.map U.ι) ≫ ofSec G s = (free R).map (yoneda.map U.ι) ≫ ofSec G s' := by
      apply ext_gen
      rw [ev_pre, ev_pre, ev_ofSec, ev_ofSec]; exact hs
    refine ⟨(PreservesPushout.iso (free R) (yoneda.map U.ι) (yoneda.map U.ι)).inv ≫ pushout.desc _ _ w, ?_, ?_⟩
    · rw [← Category.assoc, PreservesPushout.inl_iso_inv, pushout.inl_desc, ev_ofSec]
    · rw [← Category.assoc, PreservesPushout.inr_iso_inv, pushout.inr_desc, ev_ofSec]
  · apply (cancel_epi (PreservesPushout.iso (free R) (yoneda.map U.ι) (yoneda.map U.ι)).hom).1
    apply pushout.hom_ext
    · rw [← Category.assoc, ← Category.assoc, PreservesPushout.inl_iso_hom]; exact h1
    · rw [← Category.assoc, ← Category.assoc, PreservesPushout.inr_iso_hom]; exact h2

end LateralTheory.CohomologicalPurity.LeafPairPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.KummerTheory.FlasquePf

namespace LateralTheory.CohomologicalPurity.DictPf

section
variable {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}}

theorem ev_res' (m : (free R).obj (yoneda.obj X) ⟶ G) {V : Scheme.{0}} (h : V ⟶ X) :
    (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V h) = Sec.res h (ev m) := by
  calc (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V h)
      = (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V ((yoneda.obj X).map h.op (𝟙 X))) := by simp
    _ = (m.hom.app (op V)).hom (Sec.res h (freeGen R (yoneda.obj X) X (𝟙 X))) := by rw [freeGen_res]
    _ = Sec.res h (ev m) := by
      have := congrArg (fun φ => ModuleCat.Hom.hom φ (freeGen R (yoneda.obj X) X (𝟙 X))) (m.hom.naturality h.op)
      exact this

theorem eq_ofSec (m : (free R).obj (yoneda.obj X) ⟶ G) : m = ofSec G (ev m) := by
  apply ((sheafificationAdjunction _ _).homEquiv _ G).injective
  unfold ofSec
  rw [Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  apply ModuleCat.free_hom_ext
  intro x
  change (m.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down) = _
  rw [ev_res']
  unfold toG
  symm
  change ModuleCat.freeDesc _ (ModuleCat.freeMk x) = _
  refine (ModuleCat.freeDesc_apply _ _).trans ?_
  rfl

end

theorem LeafEv_of : LeafEv := by
  intro R _ G X
  refine ⟨?_, ?_, ?_⟩
  · intro m m' h
    rw [eq_ofSec m, eq_ofSec m', h]
  · intro m m'
    rfl
  · intro Y f m
    change (m.hom.app (op Y)).hom ((((free R).map (yoneda.map f)).hom.app (op Y)).hom
      (freeGen R (yoneda.obj Y) Y (𝟙 Y))) = _
    rw [freeGen_map]
    simp only [yoneda_map_app]
    exact ev_res' m f

end LateralTheory.CohomologicalPurity.DictPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem sq (AN : LeafActNat) (a6 : DivisorNaturality) (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (f : E' ⟶ E)
    (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X) (h : f ≫ π = π') {n m i k : ℤ} (x : Ht q E n i) (b : Hs q (opn U) m k) :
    Hs.pull q (abvRel U f π' π h) _ _ (Hs.act q (P := abv U π) x (Hs.pull q (abvMap U π) _ _ b)) =
      Hs.act q (P := abv U π') (pull _ f _ _ x) (Hs.pull q (abvMap U π') _ _ b) := by
  have e := AN a6 q _ _ (abvRel U f π' π h) n m i k x (Hs.pull q (abvMap U π) _ _ b)
  rw [← hs_pull_comp, abvRel_abvMap] at e
  exact e

theorem prd_sum (S : LeafSum) (HS : LeafHsSum) (AN : LeafActNat) (a6 : DivisorNaturality) (q : ℕ) [NeZero q] {X : Scheme.{0}}
    (U : X.Opens) {A : Type} (E : A → PSh) (P : PSh) (g : ∀ a, E a ⟶ P) (t : IsColimit (Cofan.mk P g))
    (π : P ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X) (h : ∀ a, g a ≫ π = π' a) {m k : ℤ} (b : Hs q (opn U) m k)
    (hb : ∀ a, Prd q U (E := disc.obj (E a)) (disc.map (π' a)) b) :
    Prd q U (E := disc.obj P) (disc.map π) b := by
  intro n i
  have h' : ∀ a, disc.map ((Cofan.mk P g).inj a) ≫ disc.map π = disc.map (π' a) := fun a => by
    rw [← disc.map_comp]; exact congrArg disc.map (h a)
  have tS : IsColimit (Cofan.mk (disc.obj P) fun a => disc.map (g a)) := isColimitCofanMkObjOfIsColimit disc E g t
  have hΦ := S (ZMod q) (tw q i) A (fun a => disc.obj (E a)) _ ⟨tS⟩ n
  have hΨ := HS q X U A E (Cofan.mk P g) ⟨t⟩ π π' h' (n + m) (i + k)
  have hP : Function.Bijective (Pi.map fun a (x : Ht q (disc.obj (E a)) n i) =>
      Hs.act q (P := abv U (disc.map (π' a))) x (Hs.pull q (abvMap U (disc.map (π' a))) _ _ b)) :=
    Function.Bijective.piMap fun a => hb a n i
  refine (Function.Bijective.of_comp_iff' hΨ _).1 ?_
  convert hP.comp hΦ using 1
  all_goals try rfl
  funext x
  funext a
  exact sq AN a6 q U _ _ _ (h' a) x b

theorem inj_aug_RPrdH {J : Type} [SmallCategory J] (D : J ⥤ PSh) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ yoneda.obj X)
    (hc : Coc D c) (N : SimplexCategoryᵒᵖ) (σ : Fin (N.unop.len + 1) ⥤ J) :
    inj D N σ ≫ ((aug c hc).app N : (hoc D).obj N ⟶ yoneda.obj X) = c (σ.obj 0) := by
  ext U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (hc _ _ (σ.map (homOfLE (Fin.zero_le 0)))) U) x

theorem LeafPrdHoc_of (lvl : LeafPrdLevel) (L : LeafLevel) (S : LeafSum) (HS : LeafHsSum) (AN : LeafActNat) :
    LeafPrdHoc := by
  intro hyp q _ J _ D X U c hc m k b hb
  refine lvl hyp q X U _ (aug c hc) m k b fun N => ?_
  exact prd_sum S HS AN hyp.2.2.2.2.1 q U (fun σ : Fin (N.unop.len + 1) ⥤ J => D.obj (σ.obj 0)) ((hoc D).obj N)
    (inj D N) (L J D N).some ((aug c hc).app N : (hoc D).obj N ⟶ yoneda.obj X)
    (fun σ : Fin (N.unop.len + 1) ⥤ J => c (σ.obj 0)) (inj_aug_RPrdH D c hc N) b
    (fun σ : Fin (N.unop.len + 1) ⥤ J => hb (σ.obj 0))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem five_bij {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type*} [AddCommGroup A1] [AddCommGroup A2] [AddCommGroup A3]
    [AddCommGroup A4] [AddCommGroup A5] [AddCommGroup B1] [AddCommGroup B2] [AddCommGroup B3] [AddCommGroup B4]
    [AddCommGroup B5] (f1 : A1 →+ A2) (f2 : A2 →+ A3) (f3 : A3 →+ A4) (f4 : A4 →+ A5)
    (g1 : B1 →+ B2) (g2 : B2 →+ B3) (g3 : B3 →+ B4) (g4 : B4 →+ B5)
    (v1 : A1 →+ B1) (v2 : A2 →+ B2) (v3 : A3 →+ B3) (v4 : A4 →+ B4) (v5 : A5 →+ B5)
    (hf2 : Function.Exact f1 f2) (hf3 : Function.Exact f2 f3) (hf4 : Function.Exact f3 f4)
    (hg2 : Function.Exact g1 g2) (hg3 : Function.Exact g2 g3) (hg4 : Function.Exact g3 g4)
    (c1 : ∀ x, g1 (v1 x) = v2 (f1 x)) (c2 : ∀ x, g2 (v2 x) = v3 (f2 x)) (c3 : ∀ x, g3 (v3 x) = v4 (f3 x))
    (c4 : ∀ x, g4 (v4 x) = v5 (f4 x))
    (h1 : Function.Surjective v1) (h2 : Function.Bijective v2) (h4 : Function.Bijective v4)
    (h5 : Function.Injective v5) : Function.Bijective v3 := by
  refine ⟨(injective_iff_map_eq_zero v3).2 fun a ha => ?_, fun b => ?_⟩
  · have e4 : f3 a = 0 := h4.1 (by rw [← c3, ha]; simp)
    obtain ⟨a2, rfl⟩ := (hf3 a).1 e4
    have e2 : g2 (v2 a2) = 0 := by rw [c2, ha]
    obtain ⟨b1, hb1⟩ := (hg2 _).1 e2
    obtain ⟨a1, rfl⟩ := h1 b1
    have e1 : f1 a1 = a2 := h2.1 (by rw [← c1, hb1])
    subst e1
    exact (hf2 _).2 ⟨a1, rfl⟩
  · obtain ⟨a4, ha4⟩ := h4.2 (g3 b)
    have e5 : f4 a4 = 0 := h5 (by rw [← c4, ha4, map_zero]; exact (hg4 _).2 ⟨b, rfl⟩)
    obtain ⟨a3, ha3⟩ := (hf4 a4).1 e5
    have e3 : g3 (b - v3 a3) = 0 := by rw [map_sub, c3, ha3, ha4, sub_self]
    obtain ⟨b2, hb2⟩ := (hg3 _).1 e3
    obtain ⟨a2, rfl⟩ := h2.2 b2
    refine ⟨a3 + f2 a2, ?_⟩
    rw [map_add (f := _), ← c2, hb2]
    abel

theorem mono_sch_open {X : Scheme.{0}} (U : X.Opens) : Mono (sch.map U.ι) := by
  have hy : Mono (yoneda.map U.ι) := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun T => ?_
    exact (mono_iff_injective _).2 fun a b h => (cancel_mono U.ι).1 h
  exact @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun _ => hy

theorem eqv_of_loc (a1 : A1) {X : Scheme.{0}} {E : Spc} {π : E ⟶ sch.obj X} (L : Loc π) (R : Type) [CommRing R]
    {Y : Scheme.{0}} (g : Y ⟶ X) (F : Shv R) : Eqv R (pullback.snd π (sch.map g)) F :=
  fun n => @a1 R _ _ _ _ (L R Y g) F n

theorem eqv_base (a1 : A1) {X : Scheme.{0}} {E : Spc} {π : E ⟶ sch.obj X} (L : Loc π) (R : Type) [CommRing R]
    (F : Shv R) : Eqv R π F := by
  have hi : IsIso (sch.map (𝟙 X)) := inferInstance
  have e : pullback.fst π (sch.map (𝟙 X)) ≫ π = pullback.snd π (sch.map (𝟙 X)) ≫ sch.map (𝟙 X) := pullback.condition
  have h1 : Eqv R (pullback.fst π (sch.map (𝟙 X)) ≫ π) F := by
    rw [e]; exact eqv_comp (eqv_of_loc a1 L R _ F) (eqv_iso _ F)
  have e' : π = inv (pullback.fst π (sch.map (𝟙 X))) ≫ pullback.fst π (sch.map (𝟙 X)) ≫ π :=
    (IsIso.inv_hom_id_assoc _ _).symm
  rw [e']
  exact eqv_comp (eqv_iso _ F) h1

theorem fgt_nat (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = pull _ φ.right _ _ (Hs.fgt q P n i x) := by
  have e : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P := pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _
  change pull _ (dbl.inl P') _ n (pull _ (dbl.map φ) _ n x.1) = pull _ φ.right _ n (pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, ← pull_comp, e]

theorem hom_nat (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Ht q P.right n i) :
    pull _ P'.hom (tw q i) n (pull _ φ.right _ _ x) = pull _ φ.left _ _ (pull _ P.hom _ n x) := by
  rw [← pull_comp, ← pull_comp, Arrow.w φ]

theorem LeafLocExc_of (bd : LeafBd) : LeafLocExc := by
  intro a1 q X U E π L
  obtain ⟨δ, ex, nat, -⟩ := bd
  have hm : Mono (opn U).hom := mono_sch_open U
  have hm' : Mono (abv U π).hom := by
    change Mono (pullback.fst π (sch.map U.ι)); have := mono_sch_open U; infer_instance
  have eR : ∀ i n, Function.Bijective (pull _ (abvMap U π).right (tw q i) n) := fun i =>
    eqv_base a1 L (ZMod q) (tw q i)
  have eL : ∀ i n, Function.Bijective (pull _ (abvMap U π).left (tw q i) n) := fun i =>
    eqv_of_loc a1 L (ZMod q) U.ι (tw q i)
  intro n i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact five_bij (pull _ (opn U).hom (tw q i) m) (δ q (opn U) m i) (Hs.fgt q (opn U) (m + 1) i)
    (pull _ (opn U).hom (tw q i) (m + 1))
    (pull _ (abv U π).hom (tw q i) m) (δ q (abv U π) m i) (Hs.fgt q (abv U π) (m + 1) i)
    (pull _ (abv U π).hom (tw q i) (m + 1))
    (pull _ (abvMap U π).right _ _) (pull _ (abvMap U π).left _ _) (Hs.pull q (abvMap U π) (m + 1) i)
    (pull _ (abvMap U π).right _ _) (pull _ (abvMap U π).left _ _)
    (ex q _ hm m i).2.1 (ex q _ hm m i).2.2 (ex q _ hm (m + 1) i).1
    (ex q _ hm' m i).2.1 (ex q _ hm' m i).2.2 (ex q _ hm' (m + 1) i).1
    (hom_nat q _ m i) (fun x => (nat q _ _ (abvMap U π) hm' hm m i x).symm) (fgt_nat q _ (m + 1) i)
    (hom_nat q _ (m + 1) i)
    (eR i m).2 (eL i m) (eR i (m + 1)) (eL i (m + 1)).1

end LateralTheory.CohomologicalPurity.TubeCut
end
end
