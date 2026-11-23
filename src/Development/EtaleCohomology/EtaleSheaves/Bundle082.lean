module

public import Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration.CechLevelIso
public import Development.EtaleCohomology.EtaleSheaves.CechLevelIsomorphism.BaseChangeLimit
public import Development.EtaleCohomology.EtaleSheaves.EtaleEmbedding.EmbedOfLines
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.EtaleCohomology.EtaleSheaves.LocalSlices.LocSliceOf
import Aesop.Main
import Mathlib.Algebra.Category.ModuleCat.AB
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.TruncCokPf LateralTheory.E.LevelsPf.Tp Opposite LateralTheory.E.CechLevelIsoPf.Gen

namespace LateralTheory.E.CechLevelIsoPf

abbrev y {A B : CommRingCat.{0}} (f : A ⟶ B) := yoneda.map (Spec.map f)

lemma y_comp {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) : y (f ≫ g) = y g ≫ y f := by
  simp [y]

lemma ypb {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ P} {inr : C ⟶ P}
    (h : IsPushout f g inl inr) : IsPullback (y inl) (y inr) (y f) (y g) :=
  (isPullback_SpecMap_of_isPushout f g inl inr h).map yoneda

lemma mk_congr {C : Type*} [Category C] {ι : Type*} {S X W : C} {f : X ⟶ S} {b b' : W ⟶ S}
    {π π' : ι → (W ⟶ X)} (hb : b = b') (hπ : π = π') (h : ∀ i, π i ≫ f = b) (h' : ∀ i, π' i ≫ f = b') :
    WidePullbackCone.mk (f := fun _ : ι => f) b π h = WidePullbackCone.mk (f := fun _ : ι => f) b' π' h' := by
  subst hb; subst hπ; rfl

def lim0 {C : Type*} [Category C] {S X : C} (f : X ⟶ S) :
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin 1 => f) f (fun _ => 𝟙 X) (fun _ => Category.id_comp f)) := by
  refine WidePullbackCone.IsLimit.mk _ (fun t => t.π 0) ?_ ?_ ?_
  · intro t
    have : t.π 0 ≫ f = t.base := WidePullbackCone.condition t 0
    exact this
  · intro t i
    have : t.π 0 ≫ 𝟙 X = t.π i := by rw [Category.comp_id, Subsingleton.elim i 0]
    exact this
  · intro t m _ hπ
    have key : ∀ m : t.pt ⟶ X, m ≫ 𝟙 X = t.π 0 → m = t.π 0 := fun m h => by rwa [Category.comp_id] at h
    exact key m (hπ 0)

def ι {D E : CommRingCat.{0}} (e : D ⟶ E) : (p : ℕ) → Fin (p+1) → (E ⟶ (tp e p).1)
  | 0 => fun _ => 𝟙 E
  | p+1 => Fin.lastCases (pushout.inr (tp e p).2 e) (fun i => ι e p i ≫ pushout.inl (tp e p).2 e)

lemma ι_last {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) :
    ι e (p+1) (Fin.last _) = pushout.inr (tp e p).2 e := by
  first | rfl | (dsimp only [ι]; exact Fin.lastCases_last) | (dsimp only [ι]; rw [Fin.lastCases_last])

lemma ι_cast {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) (i : Fin (p+1)) :
    ι e (p+1) (Fin.castSucc i) = ι e p i ≫ pushout.inl (tp e p).2 e := by
  first | rfl | (dsimp only [ι]; exact Fin.lastCases_castSucc i) | (dsimp only [ι]; rw [Fin.lastCases_castSucc])

lemma ι_w {D E : CommRingCat.{0}} (e : D ⟶ E) : ∀ (p : ℕ) (i : Fin (p+1)), e ≫ ι e p i = (tp e p).2
  | 0, i => Category.comp_id e
  | p+1, i => by
    induction i using Fin.lastCases with
    | last => rw [ι_last]; exact pushout.condition.symm
    | cast i =>
      rw [ι_cast]
      show e ≫ ι e p i ≫ pushout.inl _ _ = (tp e p).2 ≫ pushout.inl _ _
      rw [← Category.assoc, ι_w e p i]

lemma hπE {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) (i : Fin (p+1)) : y (ι e p i) ≫ y e = y (tp e p).2 := by
  rw [← y_comp, ι_w]

def limE {D E : CommRingCat.{0}} (e : D ⟶ E) : ∀ p : ℕ,
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin (p+1) => y e) (y (tp e p).2) (fun i => y (ι e p i)) (hπE e p))
  | 0 => cast (congrArg IsLimit (mk_congr rfl (funext fun i => (show y (𝟙 E) = 𝟙 _ by simp [y]).symm) _ _)) (lim0 (y e))
  | p+1 => by
    have hpb := ypb (IsPushout.of_hasPushout (tp e p).2 e)
    have h' : ∀ i, (Fin.lastCases (y (pushout.inr (tp e p).2 e)) (fun i => y (pushout.inl (tp e p).2 e) ≫ y (ι e p i)) i :
        _ ⟶ _) ≫ y e = y (pushout.inl (tp e p).2 e) ≫ y (tp e p).2 := by
      intro i
      induction i using Fin.lastCases with
      | last => rw [Fin.lastCases_last]; exact hpb.w.symm
      | cast i => rw [Fin.lastCases_castSucc, Category.assoc, hπE]
    have := stepLimit (fun i => y (ι e p i)) (hπE e p) (limE e p) _ _ hpb h'
    refine cast (congrArg IsLimit (mk_congr ?_ ?_ _ _)) this
    · exact (y_comp _ _).symm
    · funext i
      induction i using Fin.lastCases with
      | last => rw [Fin.lastCases_last, ι_last]; rfl
      | cast i => rw [Fin.lastCases_castSucc, ι_cast]; exact (y_comp _ _).symm

section Y
variable {D E Y' Y'' : CommRingCat.{0}} {e : D ⟶ E} {φ' : D ⟶ Y'} {u : Y' ⟶ Y''} {φ'' : E ⟶ Y''}

def κ (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) : Y'' ⟶ pushout φ' (tp e p).2 :=
  hpo.desc (pushout.inl _ _) (ι e p i ≫ pushout.inr _ _) (by rw [← Category.assoc, ι_w]; exact pushout.condition)

lemma hπY (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) :
    y (κ hpo p i) ≫ y u = y (pushout.inl φ' (tp e p).2) := by
  rw [← y_comp, κ, hpo.inl_desc]

lemma hgi (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) :
    y (κ hpo p i) ≫ y φ'' = y (pushout.inr φ' (tp e p).2) ≫ y (ι e p i) := by
  rw [← y_comp, κ, hpo.inr_desc, y_comp]

def limY (hpo : IsPushout φ' e u φ'') (p : ℕ) :
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin (p+1) => y u) (y (pushout.inl φ' (tp e p).2))
      (fun i => y (κ hpo p i)) (hπY hpo p)) :=
  baseChangeLimit (fun i => y (ι e p i)) (hπE e p) (limE e p) (ypb hpo).flip
    (ypb (IsPushout.of_hasPushout φ' (tp e p).2)).flip (fun i => y (κ hpo p i)) (hπY hpo p) (hgi hpo p)

end Y

theorem CechLevelIso_of : LateralTheory.E.LevelsPf.Tp.CechLevelIso := by
  intro p D E Y' Y'' e φ' u φ'' hpo
  let R := (limE e p).conePointUniqueUpToIso (limit.isLimit _)
  let L := (limY hpo p).conePointUniqueUpToIso (limit.isLimit _)
  have hR : ∀ j, R.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y e) j = y (ι e p j) := fun j =>
    (limE e p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)
  have hRb : R.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y e) = y (tp e p).2 :=
    (limE e p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
  have hL : ∀ j, L.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y u) j = y (κ hpo p j) := fun j =>
    (limY hpo p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)
  have hLb : L.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y u) = y (pushout.inl φ' (tp e p).2) :=
    (limY hpo p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
  have hw : L.hom ≫ (Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p)) =
      y (pushout.inr φ' (tp e p).2) ≫ R.hom := by
    apply WidePullback.hom_ext
    · intro j
      simp only [Arrow.mapCechNerve_app, Category.assoc, WidePullback.lift_π]
      have key : (L.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y u) j) ≫ y φ'' =
          y (pushout.inr φ' (tp e p).2) ≫ R.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y e) j := by
        exact (congrArg (· ≫ y φ'') (hL j)).trans ((hgi hpo p j).trans
          (congrArg (y (pushout.inr φ' (tp e p).2) ≫ ·) (hR j).symm))
      rw [← Category.assoc]
      exact key
    · simp only [Arrow.mapCechNerve_app, Category.assoc, WidePullback.lift_base]
      have key : (L.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y u)) ≫ y φ' =
          y (pushout.inr φ' (tp e p).2) ≫ R.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y e) := by
        exact (congrArg (· ≫ y φ') hLb).trans (((ypb (IsPushout.of_hasPushout φ' (tp e p).2)).w).trans
          (congrArg (y (pushout.inr φ' (tp e p).2) ≫ ·) hRb.symm))
      rw [← Category.assoc]
      exact key
  exact ⟨(Arrow.isoMk (f := Arrow.mk (y (pushout.inr φ' (tp e p).2)))
    (g := Arrow.mk ((Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p)))) L R hw).symm⟩

end LateralTheory.E.CechLevelIsoPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.LineChartPf

attribute [local instance] MvPolynomial.gradedAlgebra

def eU : {j : Fin 2 // j ≠ 0} ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨1, by decide⟩
  left_inv := by
    rintro ⟨j, hj⟩
    apply Subtype.ext
    fin_cases j
    · exact absurd rfl hj
    · rfl
  right_inv := by intro; rfl

def awayEquiv : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) ≃+* Polynomial ℤ :=
  (GlobalTheory.ProjSpace.polyEquivAway ℤ 1 0).symm.trans
    ((MvPolynomial.renameEquiv ℤ eU).trans (MvPolynomial.uniqueAlgEquiv ℤ PUnit.{1})).toRingEquiv

def projectiveLineAffineChartOverIntegers : Spec (CommRingCat.of (Polynomial ℤ)) ⟶ P1 :=
  Spec.map awayEquiv.toCommRingCatIso.hom ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X 0)
      (MvPolynomial.isHomogeneous_X ℤ 0) one_pos

instance : IsOpenImmersion projectiveLineAffineChartOverIntegers := by
  unfold projectiveLineAffineChartOverIntegers
  haveI : IsIso (Spec.map awayEquiv.toCommRingCatIso.hom) := inferInstance
  haveI : IsOpenImmersion (Spec.map awayEquiv.toCommRingCatIso.hom) := IsOpenImmersion.of_isIso _
  exact IsOpenImmersion.comp (Spec.map awayEquiv.toCommRingCatIso.hom) (Proj.awayι _ _ _ _)

def zIso : Spec (CommRingCat.of ℤ) ≅ ⊤_ Scheme := specZIsTerminal.uniqueUpToIso terminalIsTerminal

theorem tensor_C (R : Type) [CommRing R] (a : R) :
    (polyEquivTensor ℤ R).symm (a ⊗ₜ[ℤ] (1 : Polynomial ℤ)) = Polynomial.C a := by
  rw [polyEquivTensor_symm_apply_tmul, ← Polynomial.C_1, Polynomial.sum_C_index (by simp)]
  simp

theorem LineChart_of : LateralTheory.E.EmbedPf.LineChart := by
  intro L S l hl R _ j0 hj0
  obtain ⟨_, f, hsq⟩ := hl
  let m := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Polynomial ℤ))))
    (terminal.from S) (terminal.from P1) j0 projectiveLineAffineChartOverIntegers zIso.hom
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  let E := (polyEquivTensor ℤ R).toRingEquiv.toCommRingCatIso
  refine ⟨Spec.map E.inv ≫ (pullbackSpecIso ℤ R (Polynomial ℤ)).inv ≫ m ≫ hsq.flip.isoPullback.inv,
    inferInstance, ?_⟩
  simp only [Category.assoc, IsPullback.isoPullback_inv_fst, m, pullback.lift_fst,
    pullbackSpecIso_inv_fst_assoc]
  have key : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := R) (B := Polynomial ℤ)) ≫ E.inv =
      CommRingCat.ofHom Polynomial.C := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact tensor_C R a
  rw [← Spec.map_comp_assoc, key]

end LateralTheory.E.LineChartPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.PullMonoPf

universe u
variable {X : Scheme.{0}} (V : Scheme.{0})

abbrev KK := CostructuredArrow (Over.forget X).op (op V)

def pt (c : KK (X := X) V) : ULift.{1} (V ⟶ X) := ⟨c.hom.unop ≫ c.left.unop.hom⟩

lemma pt_eq {c c' : KK (X := X) V} (g : c ⟶ c') : pt V c = pt V c' := by
  have h2 : (c.hom.unop : V ⟶ c.left.unop.left) = (c'.hom.unop : V ⟶ c'.left.unop.left) ≫ g.left.unop.left :=
    (congrArg Quiver.Hom.unop (CostructuredArrow.w g)).symm
  have h3 := congrArg (fun k => (c'.hom.unop : V ⟶ c'.left.unop.left) ≫ k) (Over.w g.left.unop)
  simp only at h3
  unfold pt; congr 1
  exact (congrArg (· ≫ c.left.unop.hom) h2).trans ((Category.assoc _ _ _).trans h3)

def P : KK (X := X) V ⥤ Discrete (ULift.{1} (V ⟶ X)) where
  obj c := ⟨pt V c⟩
  map g := Discrete.eqToHom (pt_eq V g)

def Iota : Discrete (ULift.{1} (V ⟶ X)) ⥤ KK (X := X) V :=
  Discrete.functor fun x => CostructuredArrow.mk (Y := op (Over.mk x.down)) (𝟙 (op V))

lemma sub (c : KK (X := X) V) (x) : Subsingleton (c ⟶ (Iota V).obj x) := by
  constructor
  intro a b
  apply CostructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  apply Over.OverMorphism.ext
  have ha := congrArg Quiver.Hom.unop (CostructuredArrow.w a)
  have hb := congrArg Quiver.Hom.unop (CostructuredArrow.w b)
  exact ((Category.id_comp _).symm.trans ha).trans ((Category.id_comp _).symm.trans hb).symm

lemma pt_iota (x : Discrete (ULift.{1} (V ⟶ X))) : pt V ((Iota V).obj x) = x.as := by
  obtain ⟨⟨x⟩⟩ := x
  apply ULift.ext
  exact Category.id_comp x

def uH (c : KK (X := X) V) : c ⟶ (Iota V).obj ⟨pt V c⟩ :=
  CostructuredArrow.homMk
    (Over.homMk (U := Over.mk (pt V c).down) (V := c.left.unop) (c.hom.unop : V ⟶ c.left.unop.left) rfl).op
    (by apply Quiver.Hom.unop_inj; exact Category.id_comp _)

def adj : P V ⊣ Iota (X := X) V := Adjunction.mkOfHomEquiv
  { homEquiv := fun c x =>
      { toFun := fun e => uH V c ≫ (Iota V).map e
        invFun := fun g => Discrete.eqToHom ((pt_eq V g).trans (pt_iota V x))
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => (sub V c x).elim _ _ }
    homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
    homEquiv_naturality_right := fun {c} {_} {x'} _ _ => (sub V c x').elim _ _ }

instance : (Iota (X := X) V).Final := Functor.final_of_adjunction (adj V)

lemma colimMono {S : Type 1} [Ring S] {F F' : KK (X := X) V ⥤ ModuleCat.{1} S} [HasColimit F] [HasColimit F']
    (φ : F ⟶ F') [Mono φ] : Mono (colimMap φ) := by
  have h : colimit.pre F (Iota V) ≫ colimMap φ = colimMap (Functor.whiskerLeft (Iota V) φ) ≫ colimit.pre F' (Iota V) := by
    apply colimit.hom_ext; intro j; simp
  have hm : Mono (colimMap (Functor.whiskerLeft (Iota V) φ)) := by
    have : Mono (Functor.whiskerLeft (Iota V) φ) := by
      rw [NatTrans.mono_iff_mono_app]; intro k; dsimp; infer_instance
    haveI : PreservesFiniteLimits (colim : (Discrete (ULift.{1} (V ⟶ X)) ⥤ ModuleCat.{1} S) ⥤ _) := inferInstance
    haveI : (colim : (Discrete (ULift.{1} (V ⟶ X)) ⥤ ModuleCat.{1} S) ⥤ _).PreservesMonomorphisms :=
      inferInstance
    exact (colim : (Discrete (ULift.{1} (V ⟶ X)) ⥤ ModuleCat.{1} S) ⥤ _).map_mono (Functor.whiskerLeft (Iota V) φ)
  have : colimMap φ = inv (colimit.pre F (Iota V)) ≫ colimMap (Functor.whiskerLeft (Iota V) φ) ≫ colimit.pre F' (Iota V) := by
    rw [← h, IsIso.inv_hom_id_assoc]
  rw [this]; infer_instance

lemma lanMono (R : Type) [CommRing R] (X : Scheme.{0}) :
    ((Over.forget X).op.lan : ((Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ⥤ _).PreservesMonomorphisms where
  preserves {F F'} f _ := by
    rw [NatTrans.mono_iff_mono_app]; intro V
    have key : ((Over.forget X).op.lan.map f).app V ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F' V).hom =
        ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom ≫
          colimMap (Functor.whiskerLeft (CostructuredArrow.proj (Over.forget X).op V) f) := by
      refine (Iso.inv_comp_eq _).mp ?_
      apply colimit.hom_ext; intro j
      erw [Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc, ι_colimMap]
      have hn := ((Over.forget X).op.lan.map f).naturality j.hom
      have hu := congrArg (fun t => t.app j.left) ((Over.forget X).op.lanUnit.naturality f)
      dsimp [Functor.lanUnit] at hu hn
      have hu' : ((Over.forget X).op.leftKanExtensionUnit F).app j.left ≫
          ((Over.forget X).op.lan.map f).app ((Over.forget X).op.obj j.left) =
          f.app j.left ≫ ((Over.forget X).op.leftKanExtensionUnit F').app j.left := hu.symm
      erw [reassoc_of% hn]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hu')).trans ((Category.assoc _ _ _).trans
        (congrArg (f.app j.left ≫ ·) (Functor.ι_leftKanExtensionObjIsoColimit_hom (Over.forget X).op F' V j)))
    have hm : Mono (colimMap (Functor.whiskerLeft (CostructuredArrow.proj (Over.forget X).op V) f)) := by
      have : Mono (Functor.whiskerLeft (CostructuredArrow.proj (Over.forget X).op V) f) := by
        rw [NatTrans.mono_iff_mono_app]; intro k; dsimp; infer_instance
      exact colimMono (X := X) V.unop _
    have : Mono (((Over.forget X).op.lan.map f).app V ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F' V).hom) := by
      rw [key]
      constructor; intro Z a b h
      have h2 : a ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom =
          b ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom :=
        hm.right_cancellation _ _ ((Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm))
      have h3 := congrArg (· ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).inv) h2
      have hc : ∀ c : Z ⟶ _, (c ≫ ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).hom) ≫
          ((Over.forget X).op.leftKanExtensionObjIsoColimit F V).inv = c := fun c =>
        (Category.assoc _ _ _).trans ((congrArg (c ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id c))
      exact (hc a).symm.trans (h3.trans (hc b))
    exact mono_of_mono _ ((Over.forget X).op.leftKanExtensionObjIsoColimit F' V).hom

theorem PullMono_of : LateralTheory.E.LocSlicePf.PullMono := by
  intro R _ X
  haveI := lanMono R X
  have h1 : (sheafToPresheaf (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R))).PreservesMonomorphisms :=
    inferInstance
  have h3 : (presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).PreservesMonomorphisms :=
    inferInstance
  have h4 : (sheafToPresheaf (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R)) ⋙
      (Over.forget X).op.lan ⋙ presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).PreservesMonomorphisms :=
    inferInstance
  exact Functor.PreservesMonomorphisms.of_iso (F := sheafToPresheaf (Scheme.etaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R)) ⋙
      (Over.forget X).op.lan ⋙ presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))
    (Functor.sheafPullbackConstruction.sheafPullbackIso (Over.forget X) (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.{0}.over X) Scheme.etaleTopology.{0}).symm

end LateralTheory.E.PullMonoPf
end
end
