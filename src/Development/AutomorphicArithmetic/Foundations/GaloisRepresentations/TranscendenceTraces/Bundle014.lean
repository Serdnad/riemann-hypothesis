module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle565
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle040
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def postFam {Z S : Scheme.{0}} {p : Z ⟶ S} {R : Type} [CommRing R] {G K J : Shv R}
    (t : Fam0 p G K) (m : K ⟶ J) : Fam0 p G J where
  app A := ((m.hom.app (op A.U)).hom.toAddMonoidHom).comp (t.app A)
  nat {A B} s a := by
    change Sec.res s.g (Sec.map m (t.app B a)) = Sec.map m (t.app A (Sec.res s.k a))
    rw [← t.nat s a, map_res]

theorem UpperTheory.Gal.TranscendenceTraces.famHom_of :
    FamHom := by
  intro Q Z S p Φ _ e hrep I J
  constructor
  · intro m
    refine ⟨⟨fun n => postFam (e (I.X n)) (m.f n), fun A s t a => ?_⟩, fun n A a => rfl⟩
    have hc := congrArg (fun φ => Sec.map φ ((e (I.X s)).app A a)) (m.comm s t)
    exact hc.trans (congrArg (Sec.map (m.f t)) (hrep.nat (I.d s t) A a))
  · intro τ
    choose mm hmm _ using fun n => hrep.univ (I.X n) (J.X n) (τ.deg n)
    refine ⟨⟨mm, fun i j _ => ?_⟩, fun n A a => (hmm n A a).symm⟩
    apply (hrep.univ (I.X i) (J.X j) (postFam (τ.deg i) (J.d i j))).unique
    · intro A a
      exact congrArg (Sec.map (J.d i j)) (hmm i A a)
    · intro A a
      exact ((congrArg (Sec.map (mm j)) (hrep.nat (I.d i j) A a)).trans (hmm j A _)).trans
        (τ.comm A i j a).symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

theorem phiEx_of_parts (hU : PhiUniv) (hE : PhiExact) : PhiEx := by
  intro Q Z S p _
  refine ⟨phi p (ZMod Q), inferInstance, fun G => phiE p G, ⟨fun f A a => ?_, fun G J t => hU Q p G J t⟩,
    fun T hT => hE _ p T hT⟩
  rw [phiE_app, phiE_app, phiSec_map, DS.map_inc, map_res]

theorem fL_of_parts (hQ : PhiQis) (hX : ExtRes) (hH : FamHom) (hP : PhiEx) : FL := by
  intro Q Z S p _ F G t
  obtain ⟨Φ, _, e, hr, hex⟩ := hP Q p
  obtain ⟨ε, hq, hε⟩ := hQ _ Φ hex F
  obtain ⟨h1, h2⟩ := hX _ (Φ.obj F) G _ ε
  obtain ⟨k1, k2⟩ := hH Q p Φ e hr (res _ F) (res _ G)
  obtain ⟨a0, ha0, -⟩ := hr.univ F G t
  have key : ∀ (m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res _ F) ⟶ res _ G) (A : Sq p) (a : Sec F A.V),
      Sec.map (sglι (Φ.obj F) ≫ ε.f 0 ≫ m.f 0) ((e F).app A a) =
        Sec.map (F := Φ.obj ((res _ F).X 0)) (m.f 0) ((e _).app A (Sec.map (resι _ F) a)) := by
    intro m A a
    rw [← hr.nat, ← hε]
    rfl
  refine ⟨?_, fun τ τ' hτ hτ' A m n k hm hn a ha => ?_⟩
  · obtain ⟨m, hm⟩ := h1 a0
    obtain ⟨τ, hτ⟩ := k1 m
    refine ⟨τ, fun A a => ?_⟩
    rw [hτ, ← key, hm, ← ha0]
    rfl
  · obtain ⟨u, hu⟩ := k2 τ
    obtain ⟨u', hu'⟩ := k2 τ'
    let t' : Fam0 p F ((res _ G).X 0) :=
      { app := fun A => ((resι _ G).hom.app (op A.U)).hom.toAddMonoidHom.comp (t.app A)
        nat := fun s a => (map_res (resι _ G) s.g _).symm.trans (congrArg _ (t.nat s a)) }
    have e0 : sglι (Φ.obj F) ≫ ε.f 0 ≫ u.f 0 = sglι (Φ.obj F) ≫ ε.f 0 ≫ u'.f 0 :=
      (hr.univ F _ t').unique (fun A a => by rw [key, ← hu]; exact hτ A a) (fun A a => by rw [key, ← hu']; exact hτ' A a)
    have hy : Sec.map (((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res _ F)).d n k) ((e _).app A a) = 0 := by
      refine (hr.nat ((res _ F).d n k) A a).trans ?_
      rw [ha]
      exact map_zero _
    obtain ⟨c, hc⟩ := h2 u u' e0 A.U m n k hm hn _ hy
    exact ⟨c, by rw [hu, hu']; exact hc⟩

end UpperTheory.Gal.TranscendenceTraces
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem DS_map_apply {R : Type} [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) {G G' : Shv R} (f : G ⟶ G')
    (U : Scheme.{0}) (x : DS p G U) (u : U ⟶ S) :
    (DS.map p f U x) u = Sec.map f (x u) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp [Sec.map]
  | of v a =>
    have h := DS.map_inc p f v a
    simp only [inc, DirectSum.lof_eq_of] at h
    rw [h]
    by_cases hv : v = u
    · subst hv
      simp [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hv), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hv)]
      simp [Sec.map]
  | add x y hx hy => simp [map_add (f := _), hx, hy, Sec.map]

theorem UpperTheory.Gal.TranscendenceTraces.dSLoc_of :
    DSOne → DSLoc := by
  intro h1 R _ Z S p _ T hT U x hx
  classical
  have hz : ∀ u, Sec.map T.g (x u) = 0 := by
    intro u
    rw [← DS_map_apply, hx]
    rfl
  have hL := (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.1 U x.support
    (fun i V g => ∃ a, DS.map p T.f V a = DS.res p T.X₂ g (inc p T.X₂ i.1 (x i.1)))
    (fun i => h1 R p T hT U i.1 (x i.1) (hz i.1))
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ hL ?_
  intro V g hg
  choose a ha using hg
  refine ⟨∑ i : x.support, a i, ?_⟩

  rw [map_sum]
  simp only [ha]

  rw [← map_sum]
  congr 1
  conv_rhs => rw [← DirectSum.sum_support_of x]
  simp only [inc, DirectSum.lof_eq_of]
  exact Finset.sum_coe_sort x.support (fun i => DirectSum.of (fun i => Sec T.X₂ (pullback p i)) i (x i))
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped DirectSum Classical

namespace UpperTheory.Gal.TranscendenceTraces

private def famL {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J)
    {U : Scheme.{0}} (u : U ⟶ S) : Sec G (pullback p u) →ₗ[ULift.{1} (ZMod Q)] Sec J U where
  toFun := t.app (Sq.of p u)
  map_add' := map_add _
  map_smul' c a := by
    obtain ⟨c⟩ := c
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    have hc : (⟨(n : ZMod Q)⟩ : ULift.{1} (ZMod Q)) = ((n : ℤ) : ULift.{1} (ZMod Q)) :=
      ULift.ext (by simp)
    rw [hc, RingHom.id_apply, Int.cast_smul_eq_zsmul]
    exact (map_zsmul (t.app (Sq.of p u)) n a).trans (Int.cast_smul_eq_zsmul _ n _).symm

private def famS {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J)
    (U : Scheme.{0}) : DS p G U →ₗ[ULift.{1} (ZMod Q)] Sec J U :=
  DirectSum.toModule _ _ _ fun u => famL p t u

private theorem famS_inc {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J)
    {U : Scheme.{0}} (u : U ⟶ S) (a : Sec G (pullback p u)) :
    famS p t U (inc p G u a) = t.app (Sq.of p u) a :=
  DirectSum.toModule_lof _ _ _

private def famP {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J) :
    phiP p G ⟶ J.obj where
  app U := ModuleCat.ofHom (famS p t U.unop)
  naturality U V g := ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change famS p t _ (DS.res p G g.unop (inc p G u a)) = Sec.res g.unop (famS p t _ (inc p G u a))
    rw [DS.res_inc p G g.unop u _ rfl, famS_inc, famS_inc]
    exact (t.nat (A := Sq.of p (g.unop ≫ u)) (B := Sq.of p u)
      ⟨g.unop, pbm p g.unop u _ rfl, rfl, pbm_fst .., pbm_snd ..⟩ a).symm)

theorem phiUniv_of : PhiUniv := by
  intro Q Z S p G J t
  obtain ⟨ψ, hψ, huniq⟩ := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod Q) (phiP p G)).2.2 J (famP p t)
  have key : ∀ (U : Scheme) (y : DS p G U), Sec.map ψ (phiSec p G U y) = famS p t U y := by
    intro U y
    exact congrArg (fun φ => ModuleCat.Hom.hom (φ.app (op U)) y) hψ
  refine ⟨ψ, fun A a => ?_, fun m hm => huniq m ?_⟩
  · change Sec.map ψ (phiSec p G A.U (inc p G A.u (Sec.res A.cmp a))) = _
    rw [key, famS_inc]
    have hn : Sec.res (𝟙 A.U) (t.app A a) = t.app (Sq.of p A.u) (Sec.res A.cmp a) :=
      t.nat (A := Sq.of p A.u) (B := A)
        ⟨𝟙 _, A.cmp, Category.id_comp _, A.cmp_v, A.cmp_r.trans (Category.comp_id _).symm⟩ a
    rw [res_id] at hn
    exact hn.symm
  · apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply DS.hom_ext p
    intro u a
    change Sec.map m (phiSec p G U.unop (inc p G u a)) = famS p t U.unop (inc p G u a)
    rw [← phiE_of]
    exact (hm (Sq.of p u) a).trans (famS_inc p t u a).symm

end UpperTheory.Gal.TranscendenceTraces

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.extRes_of :
    ExtRes := by
  intro R _ F G T ε _
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G
  haveI := hKI
  haveI := hGE
  have key := GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective R F T (res R G) ε
  refine ⟨fun a => ?_, fun m m' h U i n k hin hnk y hy => ?_⟩
  · obtain ⟨m, hm⟩ := key.1 ((CochainComplex.singleFunctor (Shv R) 0).map a ≫ resAug G)
    refine ⟨m, ?_⟩
    have h0 : ε.f 0 ≫ m.f 0 = ((CochainComplex.singleFunctor (Shv R) 0).map a).f 0 ≫ (resAug G).f 0 := by
      rw [← HomologicalComplex.comp_f, hm, HomologicalComplex.comp_f]
    rw [h0, ← hι]
    change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫
        ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map a).f 0 ≫ (resAug G).f 0 =
      a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ (resAug G).f 0
    rw [HomologicalComplex.single_map_f_self]
    exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
      ((Iso.inv_hom_id_assoc _ _).trans (Category.assoc _ _ _))
  · have hε : ε ≫ m = ε ≫ m' := by
      refine HomologicalComplex.from_single_hom_ext (j := 0) ?_
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      exact (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F) _ _).1 h
    obtain ⟨H⟩ := key.2 m m' hε
    have hc := H.comm n
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n k from hnk),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel i n from hin)] at hc
    have e1 : Sec.map (T.d n k ≫ H.hom k n) y = 0 := by
      change Sec.map (H.hom k n) (Sec.map (T.d n k) y) = 0
      rw [hy]
      exact map_zero _
    have e2 : Sec.map (H.hom n i ≫ (res R G).d i n) y = Sec.map ((res R G).d i n) (Sec.map (H.hom n i) y) := rfl
    have e3 : ∀ {A B : Shv R} (f g : A ⟶ B) (x : Sec A U), Sec.map (f + g) x = Sec.map f x + Sec.map g x :=
      fun _ _ _ => rfl
    refine ⟨Sec.map (H.hom n i) y, ?_⟩
    rw [hc, e3, e3, e1, e2, zero_add, add_sub_cancel_right]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem single_key {R : Type} [CommRing R] (Φ : Shv R ⥤ Shv R) [Φ.Additive] (F : Shv R) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Φ.obj F)).inv ≫
      ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).inv.app F).f 0 =
    Φ.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv := by
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp

theorem UpperTheory.Gal.TranscendenceTraces.phiQis_of :
    PhiQis := by
  intro R _ Φ _ hΦ F
  obtain ⟨-, -, -, hq, hι, -, -, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  haveI : Φ.PreservesHomology := (Φ.exact_tfae.out 2 3).1 hΦ
  let e := (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).app F
  let φ : (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0 ⋙
      Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj F ⟶
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res R F) :=
    (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (resAug F)
  haveI hφ : QuasiIso φ :=
    (inferInstance : QuasiIso ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (resAug F)))
  haveI he : QuasiIso e.inv := inferInstance
  refine ⟨e.inv ≫ φ, quasiIso_comp e.inv φ, ?_⟩
  erw [HomologicalComplex.comp_f]
  rw [← Category.assoc]
  erw [single_key]
  exact (Φ.map_comp _ _).symm.trans (congrArg Φ.map hι)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem ring_sec (Ω C : Type) [Field Ω] [IsAlgClosed Ω] [CommRing C] [Nontrivial C] (φ : Ω →+* C)
    (h : φ.FiniteType) : ∃ ρ : C →+* Ω, ρ.comp φ = RingHom.id Ω :=
  _root_.UpperTheory.Reformulated.B.Qh66.ring_sec Ω C φ h

private theorem etale_sec (Ω : Type) [Field Ω] [IsAlgClosed Ω] {V : Scheme.{0}} [IsAffine V] (g : V ⟶ gp Ω) [Etale g]
    [Nonempty V] : ∃ σ : gp Ω ⟶ V, σ ≫ g = 𝟙 _ := by
  have hl : LocallyOfFiniteType g := inferInstance
  have hft : g.appTop.hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hl
  let e := Scheme.ΓSpecIso (CommRingCat.of Ω)
  haveI : Nontrivial Γ(V, ⊤) := by
    haveI : Nonempty (⊤ : V.Opens) := ⟨⟨Classical.arbitrary V, trivial⟩⟩
    exact Scheme.component_nontrivial V ⊤
  have hft' : (e.inv ≫ g.appTop).hom.FiniteType := by
    rw [CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso e.inv).2)
  obtain ⟨ρ, hρ⟩ := ring_sec Ω Γ(V, ⊤) (e.inv ≫ g.appTop).hom hft'
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv, ?_⟩
  have he : (gp Ω).isoSpec.hom ≫ Spec.map e.inv = 𝟙 _ := by
    rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp]
    simp [e]
  have h1 : g = V.isoSpec.hom ≫ Spec.map (e.inv ≫ g.appTop) := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, he, Category.comp_id]
  have h2 : (e.inv ≫ g.appTop) ≫ CommRingCat.ofHom ρ = 𝟙 _ := CommRingCat.hom_ext hρ
  calc (Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv) ≫ g
      = (Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv) ≫ V.isoSpec.hom ≫ Spec.map (e.inv ≫ g.appTop) := by rw [← h1]
    _ = Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (e.inv ≫ g.appTop) := by simp
    _ = Spec.map ((e.inv ≫ g.appTop) ≫ CommRingCat.ofHom ρ) := (Spec.map_comp _ _).symm
    _ = 𝟙 _ := by rw [h2, Spec.map_id]

private theorem loc_gp (Ω : Type) [Field Ω] [IsAlgClosed Ω] (P : ∀ V : Scheme.{0}, (V ⟶ gp Ω) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ gp Ω) (k : W ⟶ V), P V g → P W (k ≫ g)) (h : Loc (gp Ω) P) : P (gp Ω) (𝟙 _) := by
  obtain ⟨V, g, hV, hg, ⟨v, -⟩, hPg⟩ := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover (gp Ω) P hP).1 h (IsLocalRing.closedPoint Ω)
  haveI : Nonempty V := ⟨v⟩
  obtain ⟨σ, hσ⟩ := etale_sec Ω g
  simpa [hσ] using hP _ _ g σ hPg

@[reducible] private noncomputable def bcSq {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) {V : Scheme.{0}} (g : V ⟶ A.U) : Sq p :=
  ⟨V, pullback A.r g, g ≫ A.u, pullback.fst A.r g ≫ A.v, pullback.snd A.r g,
    (IsPullback.of_hasPullback A.r g).paste_horiz A.pb⟩

theorem UpperTheory.Gal.TranscendenceTraces.sumEx_of :
    SumExLoc → SumNat → PtInj → SumEx := by
  intro hLoc hNat hInj q _ i Z S p _ w hw hq A a
  have hqU : IsUnit (q : Γ(A.U, ⊤)) := by
    simpa using hq.map A.u.appTop.hom
  obtain ⟨T, hT, hTp⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q A.U).1 hqU
  have hex : ∀ (V : Scheme.{0}) (g : V ⟶ A.U), T.arrows g →
      ∃ b : Sec (tw q i) V, IsSum w (bcSq A g) (Sec.res (pullback.fst A.r g) a) b :=
    fun V g hg => hLoc q i p w hw (bcSq A g) (hTp V g hg) _
  have huniq : ∀ (B : Sq p) (a' : Sec (tw q i) B.V) (b b' : Sec (tw q i) B.U), IsSum w B a' b → IsSum w B a' b' → b = b' :=
    fun B a' b b' h h' => hInj q i B.U b b' fun Ω _ _ x => (h Ω x).trans (h' Ω x).symm
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ A.U), T.arrows g → Sec (tw q i) V := fun V g hg => (hex V g hg).choose
  have hs : ∀ (V : Scheme.{0}) (g : V ⟶ A.U) (hg : T.arrows g),
      IsSum w (bcSq A g) (Sec.res (pullback.fst A.r g) a) (s V g hg) := fun V g hg => (hex V g hg).choose_spec
  have hcomp : ∀ (V W : Scheme.{0}) (g : V ⟶ A.U) (k : W ⟶ V) (hg : T.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (T.downward_closed hg k) := by
    intro V W g k hg
    obtain ⟨L, hLf, hLs⟩ : ∃ L : pullback A.r (k ≫ g) ⟶ pullback A.r g,
        L ≫ pullback.fst A.r g = pullback.fst A.r (k ≫ g) ∧ L ≫ pullback.snd A.r g = pullback.snd A.r (k ≫ g) ≫ k :=
      ⟨pullback.lift (pullback.fst A.r (k ≫ g)) (pullback.snd A.r (k ≫ g) ≫ k)
        (by rw [pullback.condition, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    let t : (bcSq A (k ≫ g)).To (bcSq A g) :=
      { g := k
        k := L
        hu := by simp
        hv := by
          change L ≫ pullback.fst A.r g ≫ A.v = pullback.fst A.r (k ≫ g) ≫ A.v
          rw [← Category.assoc, hLf]
        hr := hLs }
    have h1 := hNat (ZMod q) (tw q i) w t _ _ (hs V g hg)
    have h2 : Sec.res t.k (Sec.res (pullback.fst A.r g) a) = Sec.res (pullback.fst A.r (k ≫ g)) a := by
      rw [res_res]
      change Sec.res (L ≫ pullback.fst A.r g) a = _
      rw [hLf]
    rw [h2] at h1
    exact huniq _ _ _ _ h1 (hs W (k ≫ g) (T.downward_closed hg k))
  obtain ⟨b, hb⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) A.U).2 T hT s hcomp
  refine ⟨b, fun Ω _ _ x => ?_⟩
  have hx : T.arrows x := by
    have hl : Loc (gp Ω) fun V g => T.arrows (g ≫ x) :=
      GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.1 A.U (gp Ω) x (fun V g => T.arrows g) ⟨T, hT, fun _ _ h => h⟩
    have h0 := loc_gp Ω (fun V g => T.arrows (g ≫ x))
      (fun V W g k h => by simpa using T.downward_closed h k) hl
    simpa using h0
  have h1 := (res_id _).symm.trans (hs _ x hx Ω (𝟙 _))
  rw [hb _ x hx, h1]
  have hbij := fib_bijOn (IsPullback.of_hasPullback A.r x) (𝟙 (gp Ω))
  rw [Category.id_comp] at hbij
  refine finsum_mem_eq_of_bijOn _ hbij fun z hz => ?_
  change w Ω (z ≫ pullback.fst A.r x ≫ A.v) • Sec.res z (Sec.res (pullback.fst A.r x) a) =
    w Ω ((z ≫ pullback.fst A.r x) ≫ A.v) • Sec.res (z ≫ pullback.fst A.r x) a
  rw [res_res, Category.assoc]
end
