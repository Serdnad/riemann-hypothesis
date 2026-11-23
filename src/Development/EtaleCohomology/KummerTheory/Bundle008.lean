module

public import Development.EtaleCohomology.KummerTheory.Bundle001
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Development.EtaleCohomology.KummerTheory.Bundle002
public import Development.EtaleCohomology.KummerTheory.Bundle003
public import Development.EtaleCohomology.KummerTheory.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
public import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.LHCut

theorem corep_of : Corep := by
  intro Λ _ S U
  let M : ModuleCat.{1} (ULift.{1} Λ) := ModuleCat.of (ULift.{1} Λ) (ULift.{1} Λ)
  let P : SlShv Λ S := Sheaf.freeYoneda (Scheme.etaleTopology.over S) U M
  have key : ∀ (F : SlShv Λ S) (φ : P ⟶ F),
      Sheaf.freeYonedaHomEquiv φ = Sheaf.freeYonedaHomEquiv (𝟙 P) ≫ φ.hom.app (op U) := by
    intro F φ
    conv_lhs => rw [← Category.id_comp φ]
    simp only [Sheaf.freeYonedaHomEquiv]
    rfl
  refine ⟨P, (Sheaf.freeYonedaHomEquiv (𝟙 P)).hom 1, fun F => ?_⟩
  have e : (fun φ : P ⟶ F => (φ.hom.app (op U)).hom ((Sheaf.freeYonedaHomEquiv (𝟙 P)).hom 1)) =
      (fun g : M ⟶ F.obj.obj (op U) => g.hom 1) ∘ Sheaf.freeYonedaHomEquiv := by
    funext φ
    simp only [Function.comp_apply, key F φ]
    rfl
  rw [e]
  refine Function.Bijective.comp ⟨fun g h hgh => ?_, fun n => ?_⟩ (Equiv.bijective _)
  · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have : x = x • (1 : ULift.{1} Λ) := (mul_one x).symm
    rw [this, map_smul, map_smul]
    exact congrArg (x • ·) hgh
  · exact ⟨ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} Λ) _ n), one_smul _ n⟩

end LateralTheory.KummerTheory.LHCut
end
end

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory.SHenCut

theorem satUnit : SatUnit := by
  intro J _ _ D c hc e hF hs x hx
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep D hc x
  let ej : D.obj j →+* e.pt := (e.ι.app j).hom
  have hy : (hc.desc e).hom ((c.ι.app j).hom y) = ej y := congrArg (fun t => t.hom y) (hc.fac e j)
  have hu : IsUnit (ej y) := by
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel (a := ej y) (fun h => hx (hy.trans h))
    exact IsUnit.of_mul_eq_one b hb
  obtain ⟨k, f, γ, h1, -⟩ := hs j (CommRingCat.of (Localization.Away y)) (CommRingCat.ofHom (algebraMap _ _))
    (CommRingCat.ofHom (IsLocalization.Away.lift y hu))
    (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway y))
    (CommRingCat.hom_ext (IsLocalization.Away.lift_comp y hu))
  have h2 : γ.hom (algebraMap _ (Localization.Away y) y) = (D.map f).hom y := congrArg (fun t => t.hom y) h1
  have h3 : (c.ι.app k).hom ((D.map f).hom y) = (c.ι.app j).hom y := congrArg (fun t => t.hom y) (c.w f)
  have h4 : IsUnit ((D.map f).hom y) := h2 ▸ (IsLocalization.Away.algebraMap_isUnit y).map γ.hom
  have h5 := h4.map (c.ι.app k).hom
  rw [h3] at h5
  exact h5

theorem exists_lift {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
    (f : Polynomial c.pt) : ∃ j, f ∈ lifts (show D.obj j →+* c.pt from (c.ι.app j).hom) := by
  classical
  choose j y hy using fun n => Concrete.isColimit_exists_rep D hc (f.coeff n)
  obtain ⟨S, hS⟩ := IsFiltered.sup_objs_exists (f.support.image j)
  refine ⟨S, (lifts_iff_coeff_lifts _).2 fun n => ?_⟩
  by_cases hn : n ∈ f.support
  · obtain ⟨g⟩ := hS (Finset.mem_image_of_mem j hn)
    exact ⟨(D.map g).hom (y n), (congrArg (fun t => t.hom (y n)) (c.w g)).trans (hy n)⟩
  · exact ⟨0, (map_zero _).trans (notMem_support_iff.1 hn).symm⟩

theorem satRoot : SatRoot := by
  intro J _ _ D c hc e hF hs f hf ω h0 h1
  obtain ⟨j, hj⟩ := exists_lift D c hc f
  obtain ⟨g, rfl, -, hg⟩ := lifts_and_natDegree_eq_and_monic hj hf
  let ej : D.obj j →+* e.pt := (e.ι.app j).hom
  let cj : D.obj j →+* c.pt := (c.ι.app j).hom
  have hy : (hc.desc e).hom.comp cj = ej := congrArg (fun t => t.hom) (hc.fac e j)
  change (g.map cj).eval₂ _ ω = 0 at h0
  change (g.map cj).derivative.eval₂ _ ω ≠ 0 at h1
  rw [eval₂_map, hy] at h0
  rw [derivative_map, eval₂_map, hy] at h1
  let P : StandardEtalePair (D.obj j) := ⟨g, hg, g.derivative, 1, 0, 1, by simp⟩
  let _ : Algebra (D.obj j) e.pt := ej.toAlgebra
  have hP : P.HasMap ω := by
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h1
    exact ⟨h0, IsUnit.of_mul_eq_one b hb⟩
  obtain ⟨k, t, γ, h2, h3⟩ := hs j (CommRingCat.of P.Ring) (CommRingCat.ofHom (algebraMap _ _))
    (CommRingCat.ofHom (P.lift ω hP).toRingHom) (RingHom.etale_algebraMap.2 inferInstance)
    (CommRingCat.hom_ext (P.lift ω hP).comp_algebraMap)
  let ck : D.obj k →+* c.pt := (c.ι.app k).hom
  let γ' : P.Ring →+* D.obj k := γ.hom
  have h4 : (ck.comp γ').comp (algebraMap (D.obj j) P.Ring) = cj := by
    have : (CommRingCat.ofHom (algebraMap (D.obj j) P.Ring) ≫ γ) ≫ c.ι.app k = c.ι.app j := by rw [h2]; exact c.w t
    exact congrArg (fun t => t.hom) this
  refine ⟨(ck.comp γ') P.X, ?_, ?_⟩
  · change (g.map cj).eval _ = 0
    have h5 : g.eval₂ (algebraMap (D.obj j) P.Ring) P.X = 0 := P.hasMap_X.1
    rw [Polynomial.eval_map, ← h4, ← hom_eval₂, h5, map_zero]
  · have h6 : (hc.desc e).hom (ck (γ' P.X)) = (e.ι.app k).hom (γ' P.X) := congrArg (fun t => t.hom (γ' P.X)) (hc.fac e k)
    have h7 : (e.ι.app k).hom (γ' P.X) = P.lift ω hP P.X := congrArg (fun t => t.hom P.X) h3
    exact h6.trans (h7.trans (P.lift_X ω hP))

theorem shOfLift : SHOfLift := by
  intro C Ω _ _ _ ε hu hr
  have : Nontrivial C := ε.domain_nontrivial
  have : IsLocalRing C := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : ε a = 0
    · exact Or.inr (hu _ (by simp [h]))
    · exact Or.inl (hu _ h)
  have hm : ∀ x, x ∈ IsLocalRing.maximalIdeal C ↔ ε x = 0 := fun x => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h => by_contra fun h' => h (hu x h'), fun h h' => (h'.map ε).ne_zero h⟩
  have : IsLocalHom ε := ⟨fun a ha => hu a ha.ne_zero⟩
  refine ⟨{ is_henselian := fun f hf a₀ h0 h1 => ?_ }, IsSepClosed.of_exists_root _ fun p hp hi hsep => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := hr f hf (ε a₀) (by rw [eval₂_at_apply]; exact (hm _).1 h0)
      (by rw [eval₂_at_apply]; exact (h1.map ε).ne_zero)
    exact ⟨a, ha, (hm _).2 (by rw [map_sub, ha', sub_self])⟩
  · let ι := IsLocalRing.ResidueField.lift ε
    have hι : ι.comp (IsLocalRing.residue C) = ε := IsLocalRing.ResidueField.lift_comp_residue ε
    obtain ⟨ω, hω⟩ := IsAlgClosed.exists_eval₂_eq_zero_of_injective ι ι.injective p hi.degree_pos.ne'
    have hd := hsep.eval₂_derivative_ne_zero ι hω
    obtain ⟨f, rfl, -, hf⟩ := lifts_and_natDegree_eq_and_monic (f := IsLocalRing.residue C)
      ((lifts_iff_coeff_lifts p).2 fun n => IsLocalRing.residue_surjective _) hp
    rw [eval₂_map, hι] at hω
    rw [derivative_map, eval₂_map, hι] at hd
    obtain ⟨a, ha, -⟩ := hr f hf ω hω hd
    exact ⟨IsLocalRing.residue C a, by rw [Polynomial.eval_map, eval₂_at_apply, ha.eq_zero, map_zero]⟩

theorem shen : LateralTheory.KummerTheory.StrictHenselization := goal_of satUnit satRoot shOfLift

end LateralTheory.KummerTheory.SHenCut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.AffRingPf

variable {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (p : X ⟶ Spec R)

def phi : R ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ p)

def Tf : Under R ⥤ CommRingCat.{0} := Under.pushout (phi p) ⋙ Under.forget _

theorem isPb (A : Under R) :
    IsPullback (Spec.map (pushout.inr A.hom (phi p)) ≫ X.isoSpec.inv) (Spec.map (pushout.inl A.hom (phi p)))
      p (Spec.map A.hom) := by
  have h := (isPullback_SpecMap_pushout A.hom (phi p)).flip
  refine IsPullback.of_iso h (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [phi]
  · simp

def eIso (A : Under R) : Spec (pushout A.hom (phi p)) ≅ pullback p (Spec.map A.hom) := (isPb p A).isoPullback

theorem eIso_fst (A : Under R) : (eIso p A).hom ≫ pullback.fst _ _ =
    Spec.map (pushout.inr A.hom (phi p)) ≫ X.isoSpec.inv :=
  (isPb p A).isoPullback_hom_fst

theorem eIso_snd (A : Under R) : (eIso p A).hom ≫ pullback.snd _ _ =
    Spec.map (pushout.inl A.hom (phi p)) :=
  (isPb p A).isoPullback_hom_snd

def tmap {A B : Under R} (h : A ⟶ B) : pushout A.hom (phi p) ⟶ pushout B.hom (phi p) :=
  pushout.desc (h.right ≫ pushout.inl B.hom (phi p)) (pushout.inr B.hom (phi p))
    (by rw [← Category.assoc, Under.w h, pushout.condition])

theorem nat {A B : Under R} (h : A ⟶ B) :
    (eIso p B).hom ≫ bcMap p A.hom B.hom h.right (Under.w h) = Spec.map (tmap p h) ≫ (eIso p A).hom := by
  have e1 : pushout.inr A.hom (phi p) ≫ tmap p h = pushout.inr B.hom (phi p) := pushout.inr_desc _ _ _
  have e2 : pushout.inl A.hom (phi p) ≫ tmap p h = h.right ≫ pushout.inl B.hom (phi p) := pushout.inl_desc _ _ _
  apply pullback.hom_ext
  · simp only [bcMap, pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id, eIso_fst]
    rw [← e1, Spec.map_comp, Category.assoc]
  · simp only [bcMap, pullback.map, Category.assoc, pullback.lift_snd, eIso_snd]
    rw [← Category.assoc, eIso_snd, ← Spec.map_comp, ← e2, Spec.map_comp]

theorem AffRing_of : LateralTheory.KummerTheory.ContCut.AffRing := by
  intro X _ R p
  refine ⟨Tf p, ⟨NatIso.ofComponents (fun A => (eIso p A).op) ?_⟩, fun A => ⟨A.hom ≫ pushout.inl A.hom (phi p)⟩, ?_⟩
  · intro A B h
    exact Quiver.Hom.unop_inj (nat p h)
  · intro J _ _ D c hc
    have : IsConnected J := IsFiltered.isConnected J
    have hc' : IsColimit c := isColimitOfReflects (Under.forget R) hc
    let _ : PreservesColimitsOfSize.{0, 0} (Under.pushout (phi p)) :=
      (Under.mapPushoutAdj (phi p)).leftAdjoint_preservesColimits
    have : PreservesColimit D (Tf p) :=
      inferInstanceAs (PreservesColimit D (Under.pushout (phi p) ⋙ Under.forget _))
    exact ⟨isColimitOfPreserves (Tf p) hc'⟩

end LateralTheory.KummerTheory.AffRingPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DeltaPf
open LateralTheory.KummerTheory LateralTheory.KummerTheory.ContCut

variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (a : V ⟶ U) (x : Sec F U) :
    Sec.res a (Sec.map φ x) = Sec.map φ (Sec.res a x) :=
  (congrArg (fun h => h.hom x) (φ.hom.naturality a.op)).symm

theorem sec_map_comp {F G K : Shv R} (φ : F ⟶ G) (ψ : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem res_add {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) (x y : Sec F U) :
    Sec.res a (x + y) = Sec.res a x + Sec.res a y := map_add _ _ _
theorem res_sub {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) (x y : Sec F U) :
    Sec.res a (x - y) = Sec.res a x - Sec.res a y := map_sub _ _ _
theorem res_neg {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) (x : Sec F U) :
    Sec.res a (-x) = -Sec.res a x := map_neg _ _
theorem res_zero {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) : Sec.res a (0 : Sec F U) = 0 := map_zero _
theorem smap_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ _ _
theorem smap_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ _ _
theorem smap_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map φ (-x) = -Sec.map φ x := map_neg _ _
theorem smap_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem dd (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (x : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) x) = 0 := by
  rw [← sec_map_comp, I.d_comp_d, sec_map_zero]

instance injRes (F : Shv R) (n : ℤ) : Injective ((res R F).X n) :=
  inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))

theorem mono_a {W U V X : Scheme.{0}} {a : W ⟶ U} {b : W ⟶ V} {f : U ⟶ X} {g : V ⟶ X}
    (h : IsMV a b f g) : Mono a := by
  obtain ⟨_, hg, hp, _⟩ := h
  haveI := hg
  refine ⟨fun x y e => hp.hom_ext e ?_⟩
  rw [← cancel_mono g, Category.assoc, Category.assoc, ← hp.w, reassoc_of% e]

variable {F : Shv R} {W U V X : Scheme.{0}} {a : W ⟶ U} {b : W ⟶ V} {f : U ⟶ X} {g : V ⟶ X} {n : ℤ}

theorem conn_total (hD : Dict) (hG : Glue) (hF : Flasque) (h : IsMV a b f g)
    (w : H R (sch.obj W) F n) : ∃ x, Conn F a f g n w x := by
  haveI := mono_a h
  obtain ⟨c, hc⟩ := (hD R (res R F) W n).2.1 w
  obtain ⟨s, rfl⟩ := hF R ((res R F).X n) a c
  have hcl := ((hD R (res R F) W n).2.2.1 w _ hc).1
  obtain ⟨-, hglue⟩ := hG R ((res R F).X (n + 1)) a b f g h
  obtain ⟨z, hz1, hz2⟩ := hglue (Sec.map ((res R F).d n (n + 1)) s) 0
    (by rw [sec_res_map, hcl, res_zero])
  have hzc : Sec.map ((res R F).d (n + 1) (n + 1 + 1)) z = 0 := by
    apply (hG R ((res R F).X (n + 1 + 1)) a b f g h).1
    · rw [sec_res_map, hz1, dd]
    · rw [sec_res_map, hz2, smap_zero]
  obtain ⟨x, hx⟩ := (hD R (res R F) X (n + 1)).1 z hzc
  exact ⟨x, s, z, hc, hx, hz1, hz2⟩

theorem conn_add (hD : Dict) {w w' x x'} (h1 : Conn F a f g n w x) (h2 : Conn F a f g n w' x') :
    Conn F a f g n (w + w') (x + x') := by
  obtain ⟨s, z, hs, hz, e1, e2⟩ := h1
  obtain ⟨s', z', hs', hz', e1', e2'⟩ := h2
  refine ⟨s + s', z + z', ?_, ((hD R _ X (n + 1)).2.2.2.1 _ _ _ _ hz hz').1, ?_, ?_⟩
  · rw [res_add]; exact ((hD R _ W n).2.2.2.1 _ _ _ _ hs hs').1
  · rw [res_add, smap_add, e1, e1']
  · rw [res_add, e2, e2', add_zero]

theorem conn_neg (hD : Dict) {w x} (h1 : Conn F a f g n w x) : Conn F a f g n (-w) (-x) := by
  obtain ⟨s, z, hs, hz, e1, e2⟩ := h1
  refine ⟨-s, -z, ?_, ((hD R _ X (n + 1)).2.2.2.1 _ _ _ _ hz hz).2, ?_, ?_⟩
  · rw [res_neg]; exact ((hD R _ W n).2.2.2.1 _ _ _ _ hs hs).2
  · rw [res_neg, smap_neg, e1]
  · rw [res_neg, e2, neg_zero]

theorem conn_zero (hD : Dict) (hG : Glue) (hF : Flasque) (h : IsMV a b f g) {x}
    (hx : Conn F a f g n 0 x) : x = 0 := by
  haveI := mono_a h
  obtain ⟨s, z, hs, hz, e1, e2⟩ := hx
  obtain ⟨c, hc⟩ := ((hD R (res R F) W n).2.2.1 0 _ hs).2.mp rfl
  obtain ⟨s', rfl⟩ := hF R ((res R F).X (n - 1)) a c
  beta_reduce at hc
  obtain ⟨-, hglue⟩ := hG R ((res R F).X n) a b f g h
  obtain ⟨t, ht1, ht2⟩ := hglue (s - Sec.map ((res R F).d (n - 1) n) s') 0
    (by rw [res_sub, sec_res_map, hc, sub_self, res_zero])
  have hzt : Sec.map ((res R F).d n (n + 1)) t = z := by
    refine sub_eq_zero.1 ((hG R ((res R F).X (n + 1)) a b f g h).1 _ ?_ ?_)
    · rw [res_sub, sec_res_map, ht1, e1, smap_sub, dd, sub_zero, sub_self]
    · rw [res_sub, sec_res_map, ht2, e2, smap_zero, sub_self]
  refine ((hD R (res R F) X (n + 1)).2.2.1 x z hz).2.mpr
    ⟨Sec.map ((res R F).XIsoOfEq (by ring : n = n + 1 - 1)).hom t, ?_⟩
  rw [← sec_map_comp, HomologicalComplex.XIsoOfEq_hom_comp_d, hzt]

theorem conn_unique (hD : Dict) (hG : Glue) (hF : Flasque) (h : IsMV a b f g) {w x x'}
    (h1 : Conn F a f g n w x) (h2 : Conn F a f g n w x') : x = x' := by
  have h3 := conn_add hD h1 (conn_neg hD h2)
  rw [add_neg_cancel] at h3
  have := conn_zero hD hG hF h h3
  rwa [← sub_eq_add_neg, sub_eq_zero] at this

end LateralTheory.KummerTheory.DeltaPf

namespace LateralTheory.KummerTheory.ContCut
open LateralTheory.KummerTheory.DeltaPf

theorem Delta_of (hD : Dict) (hG : Glue) (hF : Flasque) : Delta := by
  intro R _ F W U V X a b f g h n
  have tot := fun w => conn_total (F := F) (n := n) hD hG hF h w
  refine ⟨AddMonoidHom.mk' (fun w => Classical.choose (tot w)) (fun w w' =>
    conn_unique hD hG hF h (Classical.choose_spec (tot (w + w')))
      (conn_add hD (Classical.choose_spec (tot w)) (Classical.choose_spec (tot w')))), fun w x => ⟨fun hx =>
    conn_unique hD hG hF h (Classical.choose_spec (tot w)) hx, fun e => e ▸ Classical.choose_spec (tot w)⟩⟩

end LateralTheory.KummerTheory.ContCut
end
end

section

noncomputable section
open scoped TensorProduct

namespace LateralTheory.KummerTheory

section
variable {κ K : Type} [Field κ] [Field K] [Algebra κ K]

theorem shl_nontriv (B : Type) [CommRing B] [Nontrivial B] [Algebra κ B] : Nontrivial (B ⊗[κ] K) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_right κ B K (Algebra.linearMap κ B)
    (algebraMap κ B).injective

variable [IsPurelyInseparable κ K] {A : Type} [CommRing A] [Algebra κ A]

theorem shl_pow (q : ℕ) [ExpChar κ q] [ExpChar (A ⊗[κ] K) q] (y : A ⊗[κ] K) :
    ∃ n : ℕ, ∃ a : A, y ^ q ^ n = algebraMap A (A ⊗[κ] K) a := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a k =>
    obtain ⟨n, c, hc⟩ := (isPurelyInseparable_iff_pow_mem κ q).1 inferInstance k
    refine ⟨n, c • a ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      Algebra.TensorProduct.algebraMap_apply]
    simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨n, a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := hy
    refine ⟨n + m, a ^ q ^ m + b ^ q ^ n, ?_⟩
    rw [add_pow_expChar_pow, map_add (f := _), map_pow, map_pow, ← ha, ← hb, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add, add_comm m n]

end

theorem SHInsepLoc_of : SHInsepLoc := by
  intro κ K A _ _ _ _ _ _ hA
  obtain ⟨hH, _⟩ := hA
  have : IsLocalRing A := hH.toIsLocalRing
  obtain ⟨q, hq⟩ := ExpChar.exists κ
  have : Nontrivial (A ⊗[κ] K) := shl_nontriv A
  have : ExpChar (A ⊗[κ] K) q := expChar_of_injective_algebraMap (algebraMap κ _).injective q
  have hqpos : ∀ n : ℕ, q ^ n ≠ 0 := fun n => pow_ne_zero _ (expChar_pos κ q).ne'

  have hm : ∀ a ∈ IsLocalRing.maximalIdeal A, ¬ IsUnit (algebraMap A (A ⊗[κ] K) a) := by
    intro a ha hu
    have : Nontrivial ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[κ] K) := shl_nontriv _
    let φ := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ κ (IsLocalRing.maximalIdeal A)) (AlgHom.id κ K)
    have h0 : φ (algebraMap A (A ⊗[κ] K) a) = 0 := by
      simp [φ, Algebra.TensorProduct.algebraMap_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    have := hu.map φ
    rw [h0] at this
    exact not_isUnit_zero this
  have hkey : ∀ y : A ⊗[κ] K, ¬ IsUnit y →
      ∃ n : ℕ, ∃ a ∈ IsLocalRing.maximalIdeal A, y ^ q ^ n = algebraMap A (A ⊗[κ] K) a := by
    intro y hy
    obtain ⟨n, a, ha⟩ := shl_pow q y
    refine ⟨n, a, ?_, ha⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hy ((isUnit_pow_iff (hqpos n)).1 (ha ▸ hu.map _))
  refine IsLocalRing.of_nonunits_add ?_
  intro x y hx hy hxy
  obtain ⟨n, a, ha, hxa⟩ := hkey x hx
  obtain ⟨m, b, hb, hyb⟩ := hkey y hy
  apply hm (a ^ q ^ m + b ^ q ^ n)
  · exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ ha _ (Nat.pos_of_ne_zero (hqpos m)))
      (Ideal.pow_mem_of_mem _ hb _ (Nat.pos_of_ne_zero (hqpos n)))
  · have : (x + y) ^ q ^ (n + m) = algebraMap A (A ⊗[κ] K) (a ^ q ^ m + b ^ q ^ n) := by
      rw [add_pow_expChar_pow, map_add (f := _), map_pow, map_pow, ← hxa, ← hyb, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm m n]
    rw [← this]
    exact hxy.pow _

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ZHomPf

def linOf {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} ℤ) M] [Module (ULift.{1} ℤ) N]
    (f : M →+ N) : M →ₗ[ULift.{1} ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    have h : ((r.down : ℤ) : ULift.{1} ℤ) = r := by ext; simp
    simp only [RingHom.id_apply]
    rw [← h, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]

theorem ZHom_of : LateralTheory.KummerTheory.BockCut.ZHom := by
  intro F G f hf
  refine ⟨⟨{ app := fun U => ModuleCat.ofHom (linOf (f U.unop)), naturality := ?_ }⟩, ?_⟩
  · intro X Y g
    ext a
    exact (hf Y.unop X.unop g.unop a).symm
  · intro U a
    rfl

end LateralTheory.KummerTheory.ZHomPf
end
end
