module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
public import Development.EtaleCohomology.KummerTheory.InjSlice
public import Development.EtaleCohomology.WeilConjectures.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
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

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

noncomputable section

private def swapF {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.snd p U.hom ≫ U.hom) ι ⟶ pullback (pullback.fst p ι ≫ p) U.hom :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition, pullback.condition]))
    (pullback.fst _ _ ≫ pullback.snd _ _)
    (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition])

private def swapB {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.fst p ι ≫ p) U.hom ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition))
    (pullback.fst _ _ ≫ pullback.snd _ _)
    (by
      rw [pullback.lift_snd_assoc, ← pullback.condition, Category.assoc, pullback.condition])

private def swapI {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.snd p U.hom ≫ U.hom) ι ≅ pullback (pullback.fst p ι ≫ p) U.hom where
  hom := swapF p ι U
  inv := swapB p ι U
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

private def baseI {B : Scheme.{0}} (U : B.Etale) : U.left ≅ pullback (𝟙 B) U.hom where
  hom := pullback.lift U.hom (𝟙 _) (by simp)
  inv := pullback.snd _ _
  hom_inv_id := by simp [pullback.lift_snd]
  inv_hom_id := by
    apply pullback.hom_ext
    · have h := pullback.condition (f := 𝟙 B) (g := U.hom)
      simp only [Category.comp_id] at h
      simpa using h.symm
    · simp [pullback.lift_snd]

theorem UpperTheory.nonempty_iso_relativeEtaleFamily_baseChange :
    ∀ {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B), Nonempty (gYW p ι ≅ gY (pullback.fst p ι ≫ p)) ∧ Nonempty (gB B ≅ gY (𝟙 B)) ∧ Nonempty (gBW ι ≅ gY ι) := by
  intro B Y W p ι
  refine ⟨⟨NatIso.ofComponents (fun U => swapI p ι U) ?_⟩,
    ⟨NatIso.ofComponents (fun U => baseI U) ?_⟩,
    ⟨NatIso.ofComponents (fun U => pullbackSymmetry U.hom ι) ?_⟩⟩
  · intro U U' a
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [swapI, swapF, gYW, gY, resY, resYW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [swapI, swapF, gYW, gY, resY, resYW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · intro U U' a
    have hw : a.left ≫ U'.hom = U.hom := by simpa using a.w
    apply pullback.hom_ext <;> simp [baseI, gB, gY, resY, pullback.map, hw, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · intro U U' a
    apply pullback.hom_ext <;>
      simp [gBW, gY, resY, resBW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

noncomputable section

variable {B : Scheme.{0}} {q : ℕ}

private def prL (K I : Cx (ZMod q)) (n p : ℤ) :
    Cochain K I n →ₗ[ULift.{1} (ZMod q)] (K.X p ⟶ I.X (p + n)) where
  toFun α := α.v p (p + n) rfl
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private def mkC {K I : Cx (ZMod q)} {n : ℤ} (f : ∀ p, K.X p ⟶ I.X (p + n)) : Cochain K I n :=
  Cochain.mk fun p r h => f p ≫ eqToHom (by rw [h])

private theorem mkC_v {K I : Cx (ZMod q)} {n : ℤ} (f : ∀ p, K.X p ⟶ I.X (p + n)) (p : ℤ) :
    (mkC f).v p (p + n) rfl = f p := by
  simp [mkC]

private theorem coch_ext {K I : Cx (ZMod q)} {n : ℤ} {a b : Cochain K I n}
    (h : ∀ p, a.v p (p + n) rfl = b.v p (p + n) rfl) : a = b := by
  refine Cochain.ext _ _ fun p r hpr => ?_
  subst hpr
  exact h p

private def asm {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {K I : Cx (ZMod q)} {n : ℤ}
    (f : ∀ p, M →ₗ[ULift.{1} (ZMod q)] (K.X p ⟶ I.X (p + n))) :
    M →ₗ[ULift.{1} (ZMod q)] Cochain K I n where
  toFun x := mkC fun p => f p x
  map_add' x y := coch_ext fun p => by
    rw [Cochain.add_v, mkC_v, mkC_v, mkC_v, map_add (f := _)]
  map_smul' r x := coch_ext fun p => by
    rw [RingHom.id_apply, Cochain.smul_v, mkC_v, mkC_v, map_smul]

private theorem asm_v {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {K I : Cx (ZMod q)} {n : ℤ}
    (f : ∀ p, M →ₗ[ULift.{1} (ZMod q)] (K.X p ⟶ I.X (p + n))) (x : M) (p : ℤ) :
    (asm f x).v p (p + n) rfl = f p x :=
  mkC_v (fun p => f p x) p

private theorem preL_v {K K' I : Cx (ZMod q)} (f : K' ⟶ K) (n p : ℤ) (α : Cochain K I n) :
    (preL f I n α).v p (p + n) rfl = f.f p ≫ α.v p (p + n) rfl := by
  change ((Cochain.ofHom f).comp α (zero_add n)).v p (p + n) rfl = _
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]

private def fanTP (C : B.Etale ⥤ Cx (ZMod q)) (I : Cx (ZMod q)) (n : ℤ) :
    Fan (fun p : ℤ => HP (C ⋙ HomologicalComplex.eval _ _ p) (I.X (p + n))) :=
  Fan.mk (TP C I n) fun p =>
    { app := fun U => ModuleCat.ofHom (prL (C.obj U.unop) I n p)
      naturality := fun U V a => by
        refine ModuleCat.hom_ext (LinearMap.ext fun α => ?_)
        exact preL_v (C.map a.unop) n p α }

private def fanLim (C : B.Etale ⥤ Cx (ZMod q)) (I : Cx (ZMod q)) (n : ℤ) : IsLimit (fanTP C I n) :=
  Fan.IsLimit.mk _
    (fun s =>
      { app := fun U => ModuleCat.ofHom (asm (K := C.obj U.unop) (I := I) (n := n) fun p => ((s.proj p).app U).hom)
        naturality := fun U V a => by
          refine ModuleCat.hom_ext (LinearMap.ext fun x => coch_ext fun p => ?_)
          have h := congrArg (fun t => t.hom x) ((s.proj p).naturality a)
          exact (asm_v (K := C.obj V.unop) (I := I) (n := n) (fun p => ((s.proj p).app V).hom) _ p).trans
            (h.trans ((congrArg (fun t => (C.map a.unop).f p ≫ t)
              (asm_v (K := C.obj U.unop) (I := I) (n := n) (fun p => ((s.proj p).app U).hom) x p).symm).trans
              (preL_v (C.map a.unop) n p _).symm)) })
    (fun s p => by
      ext U x
      exact asm_v (K := C.obj U.unop) (I := I) (n := n) (fun p => ((s.proj p).app U).hom) x p)
    (fun s m hm => by
      ext U x
      refine coch_ext fun p => ?_
      refine Eq.trans ?_ (asm_v (K := C.obj U.unop) (I := I) (n := n) (fun p => ((s.proj p).app U).hom) x p).symm
      rw [← hm p]
      rfl)

theorem UpperTheory.totalHomPresheaf_isSheaf_injective_of_homAcyclic :
    ∀ (q : ℕ) {B : Scheme.{0}} (C : B.Etale ⥤ Cx (ZMod q)) (I : Cx (ZMod q)), (∀ p : ℤ, Good (C ⋙ HomologicalComplex.eval _ _ p)) → (∀ n, Injective (I.X n)) → ∀ n : ℤ, ∃ h : Presheaf.IsSheaf (EtTop B) (TP C I n), Injective (⟨TP C I n, h⟩ : SShv B q) := by
  intro q B C I hC hI n
  have hS := fun p : ℤ => hC p (I.X (p + n)) (hI _)
  let S : ℤ → SShv B q := fun p => ⟨HP (C ⋙ HomologicalComplex.eval _ _ p) (I.X (p + n)), (hS p).choose⟩
  have : ∀ p, Injective (S p) := fun p => (hS p).choose_spec
  let G := sheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))
  let e : G.obj (∏ᶜ S) ≅ TP C I n :=
    PreservesProduct.iso G S ≪≫ (limit.isLimit _).conePointUniqueUpToIso (fanLim C I n)
  have h : Presheaf.IsSheaf (EtTop B) (TP C I n) := (Presheaf.isSheaf_of_iso_iff e).1 (∏ᶜ S).property
  refine ⟨h, ?_⟩
  exact Injective.of_iso ((fullyFaithfulSheafToPresheaf _ _).preimageIso (Y := ⟨TP C I n, h⟩) e) inferInstance

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

private lemma res_val {R : Type} [CommRing R] {X : Scheme.{0}} {J : Shv R} (φ : (free R).obj (yoneda.obj X) ⟶ J)
    {V : Scheme.{0}} (x : V ⟶ X) :
    Sec.map φ (freeGen R (yoneda.obj X) V x) = Sec.res x (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) := by
  have h3 := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).2.2.1 V X x (𝟙 X)
  have nat : Sec.res x (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) =
      Sec.map φ (Sec.res x (freeGen R (yoneda.obj X) X (𝟙 X))) := by
    simp only [Sec.res, Sec.map]
    exact (congrArg (fun f => ModuleCat.Hom.hom f (freeGen R (yoneda.obj X) X (𝟙 X)))
      (φ.hom.naturality x.op)).symm
  rw [nat, h3]
  simp

private noncomputable def evE (R : Type) [CommRing R] (X : Scheme.{0}) (J : Shv R) :
    ((free R).obj (yoneda.obj X) ⟶ J) ≃ₗ[ULift.{1} R] Sec J X :=
  LinearEquiv.ofBijective
    { toFun := fun φ => Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨by
      intro φ ψ h
      refine (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).2.1 φ ψ fun U x => ?_
      rw [res_val φ x, res_val ψ x]
      exact congrArg (Sec.res x) h,
     by
      intro s
      obtain ⟨φ, hφ⟩ := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).1 (fun U x => Sec.res x s) (by
        intro V U g x
        simp [Sec.res])
      refine ⟨φ, ?_⟩
      refine (hφ X (𝟙 X)).trans ?_
      simp [Sec.res]⟩

private lemma pullbackSymmetry_lift_map_comm {A A' Y B : Scheme.{0}} (p : Y ⟶ B) (u : A ⟶ B) (u' : A' ⟶ B) (l : A' ⟶ A) (hl : l ≫ u = u') :
    pullback.lift (pullback.fst u' p ≫ l) (pullback.snd u' p)
        (by rw [Category.assoc, hl, pullback.condition]) ≫ (pullbackSymmetry p u).inv =
      (pullbackSymmetry p u').inv ≫ pullback.map p u' p u (𝟙 Y) l (𝟙 B) (by simp) (by simp [hl]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSymmetry_inv_comp_fst, pullback.lift_snd, Category.assoc, pullback.lift_fst]
    simp
  · rw [Category.assoc, pullbackSymmetry_inv_comp_snd, pullback.lift_fst, Category.assoc, pullback.lift_snd]
    simp

private lemma sym_nat {B Y : Scheme.{0}} (p : Y ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) :
    (LateralTheory.KummerTheory.tot p).map ((LateralTheory.EWeil.AcycPf.incl B).map a) ≫ (pullbackSymmetry p U.hom).inv =
      (pullbackSymmetry p U'.hom).inv ≫ resY p a := by
  have w : a.left ≫ U.hom = U'.hom := Over.w ((LateralTheory.EWeil.AcycPf.incl B).map a)
  exact pullbackSymmetry_lift_map_comm p U.hom U'.hom a.left w

private lemma res_res {R : Type} [CommRing R] {F : Shv R} {U V W : Scheme.{0}} (f : V ⟶ U) (g : W ⟶ V) (s : Sec F U) :
    Sec.res g (Sec.res f s) = Sec.res (g ≫ f) s := by
  simp [Sec.res]

private lemma ev_pre {R : Type} [CommRing R] {X X' : Scheme.{0}} {J : Shv R} (f : X' ⟶ X)
    (φ : (free R).obj (yoneda.obj X) ⟶ J) :
    Sec.map ((free R).map (yoneda.map f) ≫ φ) (freeGen R (yoneda.obj X') X' (𝟙 X')) =
      Sec.res f (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) := by
  have h4 := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X') J).2.2.2 (yoneda.obj X) (yoneda.map f) X' (𝟙 X')
  have hc : Sec.map ((free R).map (yoneda.map f) ≫ φ) (freeGen R (yoneda.obj X') X' (𝟙 X')) =
      Sec.map φ (Sec.map ((free R).map (yoneda.map f)) (freeGen R (yoneda.obj X') X' (𝟙 X'))) := rfl
  rw [hc, h4, ← res_val φ f]
  congr 2

private noncomputable def isoHP (q : ℕ) {B Y : Scheme.{0}} (p : Y ⟶ B) (J : Shv (ZMod q)) :
    HP (gY p ⋙ yoneda ⋙ free (ZMod q)) J ≅ (LateralTheory.EWeil.AcycPf.incl B).op ⋙ (LateralTheory.KummerTheory.tot p).op ⋙ J.obj :=
  NatIso.ofComponents (fun U => LinearEquiv.toModuleIso
      ((evE (ZMod q) (YU p U.unop) J).trans
        (J.obj.mapIso (pullbackSymmetry p U.unop.hom).symm.op).toLinearEquiv)) (by
    rintro ⟨U⟩ ⟨U'⟩ ⟨a⟩
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    have h := ev_pre (R := ZMod q) (J := J) (resY p a) φ
    change Sec.res (pullbackSymmetry p U'.hom).inv (Sec.map ((free (ZMod q)).map (yoneda.map (resY p a)) ≫ φ)
        (freeGen (ZMod q) (yoneda.obj (YU p U')) (YU p U') (𝟙 _))) =
      Sec.res ((LateralTheory.KummerTheory.tot p).map ((LateralTheory.EWeil.AcycPf.incl B).map a))
        (Sec.res (pullbackSymmetry p U.hom).inv (Sec.map φ (freeGen (ZMod q) (yoneda.obj (YU p U)) (YU p U) (𝟙 _))))
    rw [h]
    refine (res_res _ _ _).trans (Eq.trans ?_ (res_res _ _ _).symm)
    exact congrArg (fun t => Sec.res (F := J) t _) (sym_nat p a).symm)

theorem UpperTheory.homAcyclic_free_pullback_yoneda_of_injective_restriction :
    LateralTheory.KummerTheory.InjSlice → LateralTheory.EWeil.AcycPf.RestrInj → ∀ (q : ℕ) {B Y : Scheme.{0}} (p : Y ⟶ B), Good (gY p ⋙ yoneda ⋙ free (ZMod q)) := by
  intro hI hR q B Y p J hJ
  obtain ⟨h1, i1⟩ := (hI (ZMod q) J p).1
  obtain ⟨h2, i2⟩ := hR (ZMod q) B ⟨(LateralTheory.KummerTheory.tot p).op ⋙ J.obj, h1⟩
  have e := isoHP q p J
  refine ⟨(Presheaf.isSheaf_of_iso_iff e).2 h2, ?_⟩
  exact Injective.of_iso ((sheafToPresheaf _ _).preimageIso (X := ⟨_, h2⟩) e.symm) i2
end
