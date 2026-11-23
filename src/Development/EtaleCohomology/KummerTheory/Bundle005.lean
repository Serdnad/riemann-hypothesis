module

public import Development.EtaleCohomology.KummerTheory.Bundle001
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ForgetInjPf

universe w v u

variable {C : Type u} [Category.{v} C] {U : C} {A : Type w} [Category.{max u v} A]
  [HasCoproducts.{v} A]

abbrev zObj (P : (Over U)ᵒᵖ ⥤ A) (X : C) : A := ∐ (fun s : X ⟶ U => P.obj (op (Over.mk s)))

lemma zι_eq (P : (Over U)ᵒᵖ ⥤ A) {Y : C} {V : Over U} {t t' : Y ⟶ U} (h : t = t')
    (a : Over.mk t ⟶ V) (a' : Over.mk t' ⟶ V) (ha : a.left = a'.left) :
    P.map a.op ≫ Sigma.ι (fun s : Y ⟶ U => P.obj (op (Over.mk s))) t =
      P.map a'.op ≫ Sigma.ι (fun s : Y ⟶ U => P.obj (op (Over.mk s))) t' := by
  subst h
  have : a = a' := Over.OverMorphism.ext ha
  rw [this]

def zMap (P : (Over U)ᵒᵖ ⥤ A) {X Y : C} (g : Y ⟶ X) : zObj P X ⟶ zObj P Y :=
  Sigma.desc fun s => P.map (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s).op ≫
    Sigma.ι (fun s : Y ⟶ U => P.obj (op (Over.mk s))) (g ≫ s)

@[reassoc (attr := simp)]
lemma ι_zMap (P : (Over U)ᵒᵖ ⥤ A) {X Y : C} (g : Y ⟶ X) (s : X ⟶ U) :
    Sigma.ι (fun s : X ⟶ U => P.obj (op (Over.mk s))) s ≫ zMap P g =
      P.map (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s).op ≫
        Sigma.ι (fun s : Y ⟶ U => P.obj (op (Over.mk s))) (g ≫ s) := by
  simp [zMap]

lemma zMap_id (P : (Over U)ᵒᵖ ⥤ A) (X : C) : zMap P (𝟙 X) = 𝟙 _ := by
  apply Sigma.hom_ext; intro s
  rw [ι_zMap, Category.comp_id]
  rw [zι_eq P (Category.id_comp s) (Over.homMk (𝟙 X) rfl : Over.mk (𝟙 _ ≫ s) ⟶ Over.mk s)
      (𝟙 (Over.mk s)) (by simp)]
  simp

lemma zMap_comp (P : (Over U)ᵒᵖ ⥤ A) {X Y Z : C} (f : Z ⟶ Y) (g : Y ⟶ X) :
    zMap P (f ≫ g) = zMap P g ≫ zMap P f := by
  apply Sigma.hom_ext; intro s
  rw [ι_zMap, ι_zMap_assoc, ι_zMap, ← P.map_comp_assoc, ← op_comp]
  exact zι_eq P (Category.assoc _ _ _) _ _ (by simp)

def zPre (P : (Over U)ᵒᵖ ⥤ A) : Cᵒᵖ ⥤ A where
  obj X := zObj P X.unop
  map g := zMap P g.unop
  map_id X := zMap_id P X.unop
  map_comp f g := zMap_comp P g.unop f.unop

def zNatApp {P Q : (Over U)ᵒᵖ ⥤ A} (φ : P ⟶ Q) (X : C) : zObj P X ⟶ zObj Q X :=
  Sigma.desc fun s => φ.app (op (Over.mk s)) ≫ Sigma.ι (fun s : X ⟶ U => Q.obj (op (Over.mk s))) s

@[reassoc (attr := simp)]
lemma ι_zNatApp {P Q : (Over U)ᵒᵖ ⥤ A} (φ : P ⟶ Q) (X : C) (s : X ⟶ U) :
    Sigma.ι (fun s : X ⟶ U => P.obj (op (Over.mk s))) s ≫ zNatApp φ X =
      φ.app (op (Over.mk s)) ≫ Sigma.ι (fun s : X ⟶ U => Q.obj (op (Over.mk s))) s := by
  simp [zNatApp]

def zNat {P Q : (Over U)ᵒᵖ ⥤ A} (φ : P ⟶ Q) : zPre P ⟶ zPre Q where
  app X := zNatApp φ X.unop
  naturality X Y g := by
    show zMap P g.unop ≫ zNatApp φ _ = zNatApp φ _ ≫ zMap Q g.unop
    apply Sigma.hom_ext; intro s
    rw [ι_zMap_assoc, ι_zNatApp, ι_zNatApp_assoc, ι_zMap, ← φ.naturality_assoc]
    all_goals rfl

def zFun : ((Over U)ᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) where
  obj := zPre
  map := zNat
  map_id P := by
    ext X
    show zNatApp (𝟙 P) X.unop = 𝟙 _
    apply Sigma.hom_ext; intro s
    rw [ι_zNatApp]; simp
  map_comp φ ψ := by
    ext X
    show zNatApp (φ ≫ ψ) X.unop = zNatApp φ X.unop ≫ zNatApp ψ X.unop
    apply Sigma.hom_ext; intro s
    rw [ι_zNatApp, ι_zNatApp_assoc, ι_zNatApp]; simp

def zCoApp (Q : Cᵒᵖ ⥤ A) (X : C) : zObj ((Over.forget U).op ⋙ Q) X ⟶ Q.obj (op X) :=
  Sigma.desc fun _ => 𝟙 (Q.obj (op X))

@[reassoc (attr := simp)]
lemma ι_zCoApp (Q : Cᵒᵖ ⥤ A) (X : C) (s : X ⟶ U) :
    Sigma.ι (fun s : X ⟶ U => ((Over.forget U).op ⋙ Q).obj (op (Over.mk s))) s ≫ zCoApp Q X = 𝟙 _ := by
  unfold zCoApp; erw [colimit.ι_desc]; rfl

def zUnit (P : (Over U)ᵒᵖ ⥤ A) : P ⟶ (Over.forget U).op ⋙ zPre P where
  app V := Sigma.ι (fun s : V.unop.left ⟶ U => P.obj (op (Over.mk s))) V.unop.hom
  naturality V W f := by
    change _ = _ ≫ zMap P f.unop.left
    rw [ι_zMap]
    exact (zι_eq P (Over.w f.unop) (Over.homMk f.unop.left rfl : Over.mk (f.unop.left ≫ V.unop.hom) ⟶ Over.mk V.unop.hom)
      f.unop rfl).symm

def zCounit (Q : Cᵒᵖ ⥤ A) : zPre ((Over.forget U).op ⋙ Q) ⟶ Q where
  app X := zCoApp Q X.unop
  naturality X Y g := by
    show zMap _ g.unop ≫ zCoApp Q _ = zCoApp Q _ ≫ Q.map g
    apply Sigma.hom_ext; intro s
    rw [ι_zMap_assoc]
    erw [ι_zCoApp, ι_zCoApp_assoc]
    simp
    all_goals rfl

def zAdj : (zFun : ((Over U)ᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)) ⊣ (Functor.whiskeringLeft _ _ A).obj (Over.forget U).op :=
  Adjunction.mkOfUnitCounit
    { unit := { app P := zUnit P
                naturality P Q φ := by
                  ext V
                  change φ.app V ≫ Sigma.ι (fun s : V.unop.left ⟶ U => Q.obj (op (Over.mk s))) V.unop.hom =
                    Sigma.ι (fun s : V.unop.left ⟶ U => P.obj (op (Over.mk s))) V.unop.hom ≫ zNatApp φ V.unop.left
                  rw [ι_zNatApp]; all_goals rfl }
      counit := { app Q := zCounit Q
                  naturality P Q φ := by
                    ext X
                    show zNatApp _ X.unop ≫ zCoApp Q X.unop = zCoApp P X.unop ≫ φ.app X
                    apply Sigma.hom_ext; intro s
                    erw [ι_zNatApp_assoc, ι_zCoApp, ι_zCoApp_assoc]
                    simp
                    all_goals rfl }
      left_triangle := by
        ext P X
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
          NatTrans.id_app, Category.id_comp]
        erw [Category.id_comp]
        show zNatApp (zUnit P) X.unop ≫ zCoApp (zPre P) X.unop = 𝟙 _
        apply Sigma.hom_ext; intro s
        rw [ι_zNatApp_assoc]; erw [ι_zCoApp]; simp
        exact (Category.comp_id (Sigma.ι (fun s : X.unop ⟶ U => P.obj (op (Over.mk s))) s)).symm
      right_triangle := by
        ext Q V
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
          NatTrans.id_app, Category.id_comp]
        try erw [Category.id_comp]
        change Sigma.ι (fun s : V.unop.left ⟶ U => ((Over.forget U).op ⋙ Q).obj (op (Over.mk s))) V.unop.hom ≫
          zCoApp Q V.unop.left = 𝟙 _
        erw [ι_zCoApp]; all_goals rfl }

lemma zNatApp_eq_map {P Q : (Over U)ᵒᵖ ⥤ A} (φ : P ⟶ Q) (X : C) :
    zNatApp φ X = Limits.Sigma.map fun s : X ⟶ U => φ.app (op (Over.mk s)) := by
  apply Sigma.hom_ext; intro s; rw [ι_zNatApp]; simp

lemma sigmaMap_mono [HasFiniteLimits A] {T : Type v} [HasExactColimitsOfShape (Discrete T) A] {f g : T → A}
    (p : ∀ j, f j ⟶ g j) [∀ j, Mono (p j)] : Mono (Limits.Sigma.map p) := by
  let q : Discrete.functor f ⟶ Discrete.functor g := Discrete.natTrans (fun j => p j.as)
  have : ∀ j, Mono (q.app j) := fun j => (inferInstance : Mono (p j.as))
  have : Mono q := NatTrans.mono_of_mono_app _
  have := preservesMonomorphisms_of_preservesLimitsOfShape (colim : (Discrete T ⥤ A) ⥤ A)
  exact (colim : (Discrete T ⥤ A) ⥤ A).map_mono q

instance [HasFiniteLimits A] [∀ T : Type v, HasExactColimitsOfShape (Discrete T) A] : (zFun : ((Over U)ᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)).PreservesMonomorphisms where
  preserves {P Q} φ _ := by
    rw [NatTrans.mono_iff_mono_app]
    intro X
    change Mono (zNatApp φ X.unop)
    rw [zNatApp_eq_map]
    have : ∀ V, Mono (φ.app V) := fun V => (NatTrans.mono_iff_mono_app φ).1 inferInstance V
    exact sigmaMap_mono _

section Sheaf

variable (J : GrothendieckTopology C) [HasSheafify J A]

def sheafZ (U : C) : Sheaf (J.over U) A ⥤ Sheaf J A :=
  sheafToPresheaf _ _ ⋙ zFun ⋙ presheafToSheaf J A

def sheafZAdj (U : C) : sheafZ J U ⊣ J.overPullback A U :=
  ((zAdj (U := U)).comp (sheafificationAdjunction J A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

instance [HasFiniteLimits A] [∀ T : Type v, HasExactColimitsOfShape (Discrete T) A] (U : C) :
    (sheafZ (A := A) J U).PreservesMonomorphisms := by
  unfold sheafZ; infer_instance

end Sheaf

end LateralTheory.KummerTheory.ForgetInjPf

namespace LateralTheory.KummerTheory

open LateralTheory.KummerTheory.ForgetInjPf in
theorem ForgetInj_of : ForgetInj := by
  intro R _ F _ S
  refine ⟨((Scheme.etaleTopology.overPullback (ModuleCat.{1} (ULift.{1} R)) S).obj F).2, ?_⟩
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafZAdj (A := ModuleCat.{1} (ULift.{1} R)) Scheme.etaleTopology S)
  exact inferInstanceAs (Injective ((Scheme.etaleTopology.overPullback (ModuleCat.{1} (ULift.{1} R)) S).obj F))

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem sym_tot {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    rst p g ≫ (pullbackSymmetry p U.hom).hom = (pullbackSymmetry p V.hom).hom ≫ (tot p).map g := by
  change rst p g ≫ (pullbackSymmetry p U.hom).hom = (pullbackSymmetry p V.hom).hom ≫
    pullback.lift (pullback.fst V.hom p ≫ g.left) (pullback.snd V.hom p)
      (by rw [Category.assoc, Over.w g]; exact pullback.condition)
  apply pullback.hom_ext <;> simp only [rst, Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
  · erw [pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc]; simp only [pullback.map]; erw [pullback.lift_snd]
  · erw [pullback.lift_snd, pullbackSymmetry_hom_comp_snd]; simp only [pullback.map, Category.comp_id]; erw [pullback.lift_fst]

def prodSec {Λ : Type} [CommRing Λ] {S : Scheme.{0}} {ι : Type 1} (G : ι → SlShv Λ S) (U : Over S) :
    (∏ᶜ G).obj.obj (op U) →ₗ[ULift.{1} Λ] (∀ i, (G i).obj.obj (op U)) :=
  LinearMap.pi fun i => ((Pi.π G i).hom.app (op U)).hom

theorem prodSec_bij {Λ : Type} [CommRing Λ] {S : Scheme.{0}} {ι : Type 1} (G : ι → SlShv Λ S) (U : Over S) :
    Function.Bijective (prodSec G U) := by
  let F : SlShv Λ S ⥤ ModuleCat.{1} (ULift.{1} Λ) := sheafToPresheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} Λ)) ⋙
    (evaluation (Over S)ᵒᵖ (ModuleCat.{1} (ULift.{1} Λ))).obj (op U)
  let e := PreservesProduct.iso F G ≪≫ ModuleCat.piIsoPi.{1, 1, 0} (fun i => F.obj (G i))
  have : ∀ x, prodSec G U x = e.hom x := by
    intro x; funext i
    have h := congrArg (fun φ => φ.hom x) (congrArg (fun ψ => (PreservesProduct.iso F G).hom ≫ ψ)
      (ModuleCat.piIsoPi_hom_ker_subtype.{1, 1, 0} (fun i => F.obj (G i)) i))
    simp only [← Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π] at h
    exact h.symm
  have hb : Function.Bijective e.hom := e.toLinearEquiv.bijective
  have h2 : (prodSec G U : _ → _) = fun x => e.hom x := funext this
  rw [h2]; exact hb

theorem coneObj_of (h : InjSlice) : ConeObj := by
  intro Λ _ J K hJ hK X S p r M j
  let σ := Σ a : Fin (M + 1), Fin (r a)
  have hs : ∀ a : Fin (M + 1), ∃ hh : Presheaf.IsSheaf (Scheme.etaleTopology.over S)
      ((Over.forget S).op ⋙ (J.X (j + 1 - ((a : ℕ) : ℤ))).obj),
      Injective (⟨_, hh⟩ : SlShv Λ S) := fun a => (h Λ (J.X _) p).2
  obtain ⟨hk, ik⟩ := (h Λ (K.X j) p).1
  let G : ULift.{1} (Option σ) → SlShv Λ S := fun o => match o.down with
    | none => ⟨_, hk⟩
    | some ⟨a, _⟩ => ⟨_, (hs a).choose⟩
  have hG : ∀ o, Injective (G o) := by
    rintro ⟨o⟩; rcases o with _ | ⟨a, s⟩
    · exact ik
    · exact (hs a).choose_spec
  refine ⟨∏ᶜ G, inferInstance, ?_⟩
  let sy : ∀ U : Over S, (K.X j).obj.obj (op ((tot p).obj U)) ≃ₗ[ULift.{1} Λ] Sec (K.X j) (pullback p U.hom) :=
    fun U => ((K.X j).obj.mapIso (pullbackSymmetry p U.hom).op).toLinearEquiv
  let f2 : ∀ U : Over S, (∀ o, (G o).obj.obj (op U)) ≃ₗ[ULift.{1} Λ] Cone J K p r M j U := fun U =>
    { toFun := fun x => (fun a s => x ⟨some ⟨a, s⟩⟩, sy U (x ⟨none⟩))
      invFun := fun y o => match o with
        | ⟨none⟩ => (sy U).symm y.2
        | ⟨some ⟨a, s⟩⟩ => y.1 a s
      map_add' := fun x y => Prod.ext rfl ((sy U).map_add _ _)
      map_smul' := fun c x => Prod.ext rfl ((sy U).map_smul _ _)
      left_inv := by
        intro x; funext o; rcases o with ⟨_ | ⟨a, s⟩⟩
        · exact (sy U).symm_apply_apply _
        · rfl
      right_inv := by
        intro y; ext a s
        · rfl
        · exact (sy U).apply_symm_apply _ }
  refine ⟨fun U => (LinearEquiv.ofBijective (prodSec G U) (prodSec_bij G U)).trans (f2 U), ?_⟩
  intro V U g x
  have nat : ∀ o, ((Pi.π G o).hom.app (op V)).hom (((∏ᶜ G).obj.map g.op).hom x) =
      ((G o).obj.map g.op).hom (((Pi.π G o).hom.app (op U)).hom x) := fun o => by
    have := congrArg (fun φ => φ.hom x) ((Pi.π G o).hom.naturality g.op)
    simpa using this
  refine Prod.ext ?_ ?_
  · funext a s; exact nat ⟨some ⟨a, s⟩⟩
  · change (sy V) (((Pi.π G ⟨none⟩).hom.app (op V)).hom _) = Sec.res (rst p g) ((sy U) _)
    rw [nat ⟨none⟩]
    have key : (K.X j).obj.map ((tot p).op.map g.op) ≫ (K.X j).obj.map (pullbackSymmetry p V.hom).op.hom =
        (K.X j).obj.map ((pullbackSymmetry p U.hom).op.hom ≫ (rst p g).op) := by
      refine ((K.X j).obj.map_comp _ _).symm.trans ?_; congr 1; apply Quiver.Hom.unop_inj
      simp only [unop_comp, Iso.op_hom, Quiver.Hom.unop_op, Functor.op_map]
      exact (sym_tot p g).symm
    change ((K.X j).obj.map ((tot p).op.map g.op) ≫ (K.X j).obj.map (pullbackSymmetry p V.hom).op.hom).hom
      (((Pi.π G ⟨none⟩).hom.app (op U)).hom x) = _
    rw [key, (K.X j).obj.map_comp]; rfl

end LateralTheory.KummerTheory.LHCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def TwRes0 : Prop := ∀ (q : ℕ) [NeZero q] {U X : Scheme.{0}} (x : U ⟶ X) (ζ₀ : Prim q Γ(X, ⊤)) (ζ : Prim q Γ(U, ⊤)),
  Sec.res x (twGen 0 ζ₀) = twGen 0 ζ

def DegreeZeroSectionExists : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (s : Sec F X),
  ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    ∀ (U : Scheme.{0}) (x : U ⟶ X), ev (R := R) α.1 0 0 (by simp) U x = Sec.res x (Sec.map (resι R F) s)

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun f => f.hom s) h).symm

theorem OneEx_of (hT : TwSec) (hR : TwRes0) (hS : DegreeZeroSectionExists) : OneEx := by
  intro q _ A _ hA hq
  obtain ⟨⟨ζ₀⟩, -⟩ := hT q A hA hq
  obtain ⟨α, hα⟩ := hS (ZMod q) (tw q 0) (Spec (CommRingCat.of A)) (twGen 0 ζ₀)
  refine ⟨_, α, rfl, ?_⟩
  intro U x ζ
  refine (hα U x).trans ((sec_res_map (resι (ZMod q) (tw q 0)) (x : U ⟶ Spec (CommRingCat.of A)) (twGen 0 ζ₀)).trans ?_)
  rw [hR q (x : U ⟶ Spec (CommRingCat.of A)) ζ₀ ζ]
  rfl

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory.ValAICPf

variable {K : Type} [Field K] [IsAlgClosed K] (T : ValuationSubring K)

theorem mem_of_root (p : T[X]) (hp : p.Monic) (r : K) (hr : (p.map (algebraMap T K)).eval r = 0) : r ∈ T := by
  have hi : IsIntegral T r := ⟨p, hp, by rwa [eval_map] at hr⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := T) (K := K)).mp hi
  rw [← hy]; exact y.2

theorem aic : AIC T := by
  intro p hp hd
  have hd' : (p.map (algebraMap T K)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (IsFractionRing.injective T K)]
    intro h; rw [degree_eq_natDegree hp.ne_zero] at h; norm_cast at h; omega
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hd'
  have hrT := mem_of_root T p hp r hr
  refine ⟨⟨r, hrT⟩, ?_⟩
  apply IsFractionRing.injective T K
  rw [map_zero, ← eval₂_hom, ← eval_map]
  exact hr

theorem prod_lt (s : Multiset K) (hs : ∀ r ∈ s, T.valuation r ≤ 1) (h : T.valuation s.prod < 1) :
    ∃ r ∈ s, T.valuation r < 1 := by
  by_contra hc
  push_neg at hc
  have : T.valuation s.prod = 1 := by
    rw [map_multiset_prod]
    apply Multiset.prod_eq_one
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    exact le_antisymm (hs r hr) (hc r hr)
  rw [this] at h; exact lt_irrefl _ h

theorem hens : HenselianLocalRing T where
  is_henselian := by
    intro f hf a₀ h₁ _
    set q := f.map (algebraMap T K)
    have he : (algebraMap T K) (f.eval a₀) = (q.roots.map (fun r => (a₀ : K) - r)).prod := by
      rw [← eval₂_hom, ← eval_map]
      exact (IsAlgClosed.splits q).eval_eq_prod_roots_of_monic (hf.map _) _
    have hmem : ∀ r ∈ q.roots, r ∈ T := fun r hr =>
      mem_of_root T f hf r ((mem_roots (hf.map _).ne_zero).mp hr)
    have hlt : T.valuation (q.roots.map (fun r => (a₀ : K) - r)).prod < 1 := by
      rw [← he]; exact (T.valuation_lt_one_iff _).mp h₁
    obtain ⟨x, hx, hxv⟩ := prod_lt T _ (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      exact (T.valuation_le_one_iff _).mpr (T.sub_mem a₀.2 (hmem r hr))) hlt
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    refine ⟨⟨r, hmem r hr⟩, ?_, ?_⟩
    · have h0 := (mem_roots (hf.map _).ne_zero).mp hr
      apply IsFractionRing.injective T K
      rw [map_zero, ← eval₂_hom, ← eval_map]
      exact h0
    · rw [T.valuation_lt_one_iff]
      have hc : (((⟨r, hmem r hr⟩ : T) - a₀ : T) : K) = -((a₀ : K) - r) := by push_cast; ring
      rw [hc, Valuation.map_neg]
      exact hxv

end LateralTheory.KummerTheory.ValAICPf

theorem LateralTheory.KummerTheory.ValAIC_of : LateralTheory.KummerTheory.ValAIC := fun K _ _ T => ⟨LateralTheory.KummerTheory.ValAICPf.aic T, LateralTheory.KummerTheory.ValAICPf.hens T⟩

theorem LateralTheory.KummerTheory.Place_of_ex (h : LateralTheory.KummerTheory.PlaceEx) : LateralTheory.KummerTheory.Place :=
  LateralTheory.KummerTheory.Place_of h LateralTheory.KummerTheory.ValAIC_of
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

def AffNbhd : Prop := ∀ {R : CommRingCat.{0}} (U : Over (Spec R)) (u : U.left),
  ∃ (B : CommRingCat.{0}) (s : R ⟶ B) (ι : Spec B ⟶ U.left) (_ : IsOpenImmersion ι) (b : Spec B),
    ι ≫ U.hom = Spec.map s ∧ ι b = u

def CokAff : Prop := A2 → DivisorNaturality → B1 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
  [QuasiCompact p] [IsSeparated p], IsUnit (q : R) →
  ∀ (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ),
  (∀ (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsoUpTo N (lh q p (Spec.map s) i r c M n)) →
  ∀ (B : CommRingCat.{0}) (s : R ⟶ B) (b : Spec B) (x : Ht q (sch.obj (pullback p (Spec.map s))) n i),
  ∃ (C : CommRingCat.{0}) (t : B ⟶ C), t.hom.Etale ∧ (∃ w : Spec C, Spec.map t w = b) ∧
    ∃ y, lh q p (Spec.map (s ≫ t)) i r c M n y = N • pull _ (sch.map (bcMap p s (s ≫ t) t rfl)) _ _ x

theorem affNbhd : AffNbhd := by
  intro R U u
  obtain ⟨b, hb⟩ := U.left.affineCover.covers u
  exact ⟨_, Spec.preimage (U.left.affineCover.f (U.left.affineCover.idx u) ≫ U.hom),
    U.left.affineCover.f (U.left.affineCover.idx u), U.left.affineCover.map_prop _, b, by simp, hb⟩

theorem locCok_of (hA : AffNbhd) (hC : CokAff) : LocCok := by
  intro h2 h6 hb1 q _ X R p _ _ hq i r c M N n hiso U u x
  obtain ⟨B, s, ι, _, b, hs, hb'⟩ := hA U u
  let g0 : Over.mk (Spec.map s) ⟶ U := Over.homMk ι hs
  obtain ⟨C, t, ht, ⟨w, hw⟩, y, hy⟩ := hC h2 h6 hb1 q p hq i r c M N n hiso B s b
    (pull _ (sch.map (rst p g0)) _ _ x)
  have : Etale (Spec.map t) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 ht
  let g : Over.mk (Spec.map (s ≫ t)) ⟶ U := Over.homMk (Spec.map t ≫ ι) (by simp [hs, Spec.map_comp])
  refine ⟨Over.mk (Spec.map (s ≫ t)), g, ⟨?_, w, ?_⟩, y, ?_⟩
  · show Etale (Spec.map t ≫ ι); infer_instance
  · show (Spec.map t ≫ ι) w = u
    rw [Scheme.Hom.comp_apply, hw, hb']
  · show lh q p (Spec.map (s ≫ t)) i r c M n y = _
    have key : bcMap p s (s ≫ t) t rfl ≫ rst p g0 = rst p g := by
      apply pullback.hom_ext
      · simp only [bcMap, rst, g, g0, pullback.map, Over.homMk_left, Category.assoc, Category.comp_id]
        erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
        rfl
      · simp only [bcMap, rst, g, g0, pullback.map, Over.homMk_left, Category.assoc, Category.comp_id]
        erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
        simp only [Category.assoc]
        rfl
    rw [hy, ← pull_comp, ← Functor.map_comp, key]

theorem locCok_of_cokAff (hC : CokAff) : LocCok := locCok_of affNbhd hC

end LateralTheory.KummerTheory.LHCut
end
end
