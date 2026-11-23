module

public import Development.EtaleCohomology.KummerTheory.Bundle003
public import Development.EtaleCohomology.KummerTheory.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle005
public import Development.EtaleCohomology.TateTwists.Bundle004
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
import Mathlib.Tactic.Linter.HaveILetI
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

namespace LateralTheory.KummerTheory.ExactPf

open LateralTheory.KummerTheory LateralTheory.KummerTheory.ContCut

variable {R : Type} [CommRing R]

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  change (F.obj.map g.op ≫ φ.hom.app (op V)).hom x = (φ.hom.app (op U) ≫ G.obj.map g.op).hom x
  rw [φ.hom.naturality]

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (a : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res a (Sec.res g x) = Sec.res (a ≫ g) x := by
  change _ = (F.obj.map (a ≫ g).op).hom x
  rw [op_comp, Functor.map_comp]
  rfl

theorem dd (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (s : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) s) = 0 := by
  change (Sec.map (I.d i j ≫ I.d j k) s) = 0
  rw [I.d_comp_d]
  rfl

theorem mneg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec.map φ (-x) = -Sec.map φ x :=
  map_neg _ _

theorem mzero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem rneg {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) : Sec.res g (-x) = -Sec.res g x :=
  map_neg _ _

theorem msub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ _ _

theorem rsub {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) : Sec.res g (x - y) = Sec.res g x - Sec.res g y :=
  map_sub _ _ _

theorem rzero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem inj (F : Shv R) (m : ℤ) : Injective ((res R F).X m) := by
  unfold res; infer_instance

theorem tr (I : Cx R) {X : Scheme.{0}} (m k j : ℤ) (h : m = k) (a : Sec (I.X j) X) :
    (∃ b : Sec (I.X m) X, Sec.map (I.d m j) b = a) → ∃ b : Sec (I.X k) X, Sec.map (I.d k j) b = a := by
  subst h; exact id

theorem cls_eq (hD : Dict) (F : Shv R) {Y : Scheme.{0}} (m : ℤ) {x y : H R (sch.obj Y) F m}
    {s t : Sec ((res R F).X m) Y} (hx : IsCls x s) (hy : IsCls y t)
    (h : ∃ b : Sec ((res R F).X (m - 1)) Y, Sec.map ((res R F).d (m - 1) m) b = s - t) : x = y := by
  obtain ⟨-, -, D3, D4, -⟩ := hD R (res R F) Y m
  have h3 := (D4 x (-y) s (-t) hx (D4 y y t t hy hy).2).1
  rw [← sub_eq_add_neg, ← sub_eq_add_neg] at h3
  exact sub_eq_zero.mp ((D3 _ _ h3).2.mpr h)

theorem Exact_of (hD : Dict) (hG : Glue) (hF : Flasque) : Exact := by
  intro R _ F W U V X a b f g hmv n
  have hpb := hmv.2.2.1
  haveI : IsOpenImmersion g := hmv.2.1
  haveI : Mono a := hpb.mono_fst_of_mono
  have hw : a ≫ f = b ≫ g := hpb.w
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    obtain ⟨u0, hu0⟩ := (hD R (res R F) U n).2.1 u
    obtain ⟨v0, hv0⟩ := (hD R (res R F) V n).2.1 v
    have hau : IsCls (pull R (sch.map a) F n u) (Sec.res a u0) := (hD R (res R F) U n).2.2.2.2 a u u0 hu0
    have hbv : IsCls (pull R (sch.map b) F n v) (Sec.res b v0) := (hD R (res R F) V n).2.2.2.2 b v v0 hv0
    rw [huv] at hau
    have hu0c := ((hD R (res R F) U n).2.2.1 u u0 hu0).1
    have hv0c := ((hD R (res R F) V n).2.2.1 v v0 hv0).1
    obtain ⟨r, hr⟩ : ∃ r : Sec ((res R F).X (n - 1)) W,
        Sec.map ((res R F).d (n - 1) n) r = Sec.res a u0 - Sec.res b v0 := by
      have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ hau ((hD R (res R F) W n).2.2.2.1 _ _ _ _ hbv hbv).2).1
      rw [add_neg_cancel, ← sub_eq_add_neg] at h3
      exact ((hD R (res R F) W n).2.2.1 _ _ h3).2.mp rfl
    haveI := inj F (n - 1)
    obtain ⟨r', hr'⟩ := hF R ((res R F).X (n - 1)) a r
    change Sec.res a r' = r at hr'
    have hu1 : Sec.res a (u0 - Sec.map ((res R F).d (n - 1) n) r') = Sec.res b v0 := by
      rw [rsub]
      rw [← map_res, hr', hr]
      abel
    obtain ⟨z, hzf, hzg⟩ := (hG R ((res R F).X n) a b f g hmv).2 _ v0 hu1
    have hdz : Sec.map ((res R F).d n (n + 1)) z = 0 := by
      apply (hG R ((res R F).X (n + 1)) a b f g hmv).1
      · rw [← map_res, hzf, msub, hu0c, dd, sub_zero]
      · rw [← map_res, hzg, hv0c]
    obtain ⟨x, hx⟩ := (hD R (res R F) X n).1 z hdz
    refine ⟨x, ?_, ?_⟩
    · have hfx : IsCls (pull R (sch.map f) F n x) (Sec.res f z) := (hD R (res R F) X n).2.2.2.2 f x z hx
      rw [hzf] at hfx
      refine cls_eq hD F n hfx hu0 ⟨-r', ?_⟩
      rw [mneg]
      abel
    · have hgx : IsCls (pull R (sch.map g) F n x) (Sec.res g z) := (hD R (res R F) X n).2.2.2.2 g x z hx
      rw [hzg] at hgx
      exact cls_eq hD F n hgx hv0 ⟨0, by rw [mzero, sub_self]⟩
  · intro x hfx hgx
    obtain ⟨z0, hz0⟩ := (hD R (res R F) X (n + 1)).2.1 x
    have hz0c := ((hD R (res R F) X (n + 1)).2.2.1 x z0 hz0).1
    have hgz : IsCls (pull R (sch.map g) F (n + 1) x) (Sec.res g z0) :=
      (hD R (res R F) X (n + 1)).2.2.2.2 g x z0 hz0
    rw [hgx] at hgz
    obtain ⟨t, ht⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
      (((hD R (res R F) V (n + 1)).2.2.1 _ _ hgz).2.mp rfl)
    haveI := inj F n
    obtain ⟨t', ht'⟩ := hF R ((res R F).X n) g t
    change Sec.res g t' = t at ht'
    have hzg : Sec.res g (z0 - Sec.map ((res R F).d n (n + 1)) t') = 0 := by
      rw [rsub, ← map_res, ht', ht, sub_self]
    obtain ⟨x', hx'⟩ := (hD R (res R F) X (n + 1)).1 (z0 - Sec.map ((res R F).d n (n + 1)) t')
      (by rw [msub, hz0c, dd, sub_zero])
    have hxx : x' = x := cls_eq hD F (n + 1) hx' hz0
      (tr (res R F) n (n + 1 - 1) (n + 1) (by ring) _ ⟨-t', by rw [mneg]; abel⟩)
    rw [hxx] at hx'
    have hfz : IsCls (pull R (sch.map f) F (n + 1) x) (Sec.res f (z0 - Sec.map ((res R F).d n (n + 1)) t')) :=
      (hD R (res R F) X (n + 1)).2.2.2.2 f x _ hx'
    rw [hfx] at hfz
    obtain ⟨s, hs⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
      (((hD R (res R F) U (n + 1)).2.2.1 _ _ hfz).2.mp rfl)
    have hsc : Sec.map ((res R F).d n (n + 1)) (Sec.res a s) = 0 := by
      rw [map_res, hs, res_res, hw, ← res_res, hzg, rzero]
    obtain ⟨w, hw'⟩ := (hD R (res R F) W n).1 _ hsc
    exact ⟨w, s, _, hw', hx', hs.symm, hzg⟩
  · intro w
    constructor
    · rintro ⟨s, z, hws, hz0, hfz, hgz⟩
      obtain ⟨t, ht⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
        (((hD R (res R F) X (n + 1)).2.2.1 _ _ hz0).2.mp rfl)
      have hu : Sec.map ((res R F).d n (n + 1)) (s - Sec.res f t) = 0 := by
        rw [msub, map_res, ht, hfz, sub_self]
      have hv : Sec.map ((res R F).d n (n + 1)) (-Sec.res g t) = 0 := by
        rw [mneg, map_res, ht, hgz, neg_zero]
      obtain ⟨u, hu'⟩ := (hD R (res R F) U n).1 _ hu
      obtain ⟨v, hv'⟩ := (hD R (res R F) V n).1 _ hv
      refine ⟨u, v, ?_⟩
      have h1 : IsCls (pull R (sch.map a) F n u) (Sec.res a (s - Sec.res f t)) :=
        (hD R (res R F) U n).2.2.2.2 a u _ hu'
      have h2 : IsCls (pull R (sch.map b) F n v) (Sec.res b (-Sec.res g t)) :=
        (hD R (res R F) V n).2.2.2.2 b v _ hv'
      have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h1 ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h2 h2).2).1
      have hA : Sec.res a (s - Sec.res f t) + -Sec.res b (-Sec.res g t) = Sec.res a s := by
        rw [rsub, rneg, res_res, res_res, hw]
        abel
      rw [hA, ← sub_eq_add_neg] at h3
      exact cls_eq hD F n hws h3 ⟨0, by rw [mzero, sub_self]⟩
    · rintro ⟨u, v, rfl⟩
      obtain ⟨u0, hu0⟩ := (hD R (res R F) U n).2.1 u
      obtain ⟨v0, hv0⟩ := (hD R (res R F) V n).2.1 v
      have hu0c := ((hD R (res R F) U n).2.2.1 u u0 hu0).1
      have hv0c := ((hD R (res R F) V n).2.2.1 v v0 hv0).1
      haveI := inj F n
      obtain ⟨s', hs'⟩ := hF R ((res R F).X n) a (Sec.res b v0)
      change Sec.res a s' = Sec.res b v0 at hs'
      obtain ⟨t, htf, htg⟩ := (hG R ((res R F).X n) a b f g hmv).2 s' v0 hs'
      refine ⟨u0 - s', -Sec.map ((res R F).d n (n + 1)) t, ?_, ?_, ?_, ?_⟩
      · have h1 : IsCls (pull R (sch.map a) F n u) (Sec.res a u0) := (hD R (res R F) U n).2.2.2.2 a u u0 hu0
        have h2 : IsCls (pull R (sch.map b) F n v) (Sec.res b v0) := (hD R (res R F) V n).2.2.2.2 b v v0 hv0
        have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h1 ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h2 h2).2).1
        rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← hs', ← rsub] at h3
        exact h3
      · obtain ⟨y, hy⟩ := (hD R (res R F) X (n + 1)).1 (-Sec.map ((res R F).d n (n + 1)) t)
          (by rw [mneg, dd, neg_zero])
        have hy0 : y = 0 := ((hD R (res R F) X (n + 1)).2.2.1 _ _ hy).2.mpr
          (tr (res R F) n (n + 1 - 1) (n + 1) (by ring) _ ⟨-t, mneg _ _⟩)
        rw [hy0] at hy
        exact hy
      · rw [rneg, ← map_res, htf, msub, hu0c, zero_sub]
      · rw [rneg, ← map_res, htg, hv0c, neg_zero]

end LateralTheory.KummerTheory.ExactPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.MVnatPf

open LateralTheory.KummerTheory.ContCut

theorem res_res {R : Type} [CommRing R] {F : Shv R} {A B C : Scheme.{0}} (g₁ : A ⟶ B) (g₂ : B ⟶ C) (x : Sec F C) :
    Sec.res g₁ (Sec.res g₂ x) = Sec.res (g₁ ≫ g₂) x := by
  show _ = (F.obj.map (g₁ ≫ g₂).op).hom x
  rw [op_comp, Functor.map_comp]
  rfl

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {A B : Scheme.{0}} (g : A ⟶ B) (x : Sec F B) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show ((F.obj.map g.op) ≫ φ.hom.app (op A)).hom x = (φ.hom.app (op B) ≫ G.obj.map g.op).hom x
  rw [φ.hom.naturality]

theorem conn_pull (hD : Dict) {R : Type} [CommRing R] (F : Shv R) {W U V X W' U' V' X' : Scheme.{0}}
    (a : W ⟶ U) (f : U ⟶ X) (g : V ⟶ X) (a' : W' ⟶ U') (f' : U' ⟶ X') (g' : V' ⟶ X')
    (hw : W' ⟶ W) (hu : U' ⟶ U) (hv : V' ⟶ V) (hx : X' ⟶ X)
    (ea : a' ≫ hu = hw ≫ a) (ef : f' ≫ hx = hu ≫ f) (eg : g' ≫ hx = hv ≫ g) (n : ℤ) w x
    (h : Conn F a f g n w x) :
    Conn F a' f' g' n (pull R (sch.map hw) F n w) (pull R (sch.map hx) F (n + 1) x) := by
  obtain ⟨s, z, hs, hz, e1, e2⟩ := h
  refine ⟨Sec.res hu s, Sec.res hx z, ?_, ?_, ?_, ?_⟩
  · have := (hD R (res R F) W n).2.2.2.2 hw w _ hs
    rw [res_res, ea, ← res_res]
    exact this
  · exact (hD R (res R F) X (n + 1)).2.2.2.2 hx x _ hz
  · rw [res_res, ef, ← res_res, e1, map_res]
  · rw [res_res, eg, ← res_res, e2]
    exact map_zero _

theorem unop_nat {K : Type 1} [Category.{0} K] {A B : K ⥤ Scheme.{0}ᵒᵖ} (φ : A ⟶ B) {k k' : K} (h : k ⟶ k') :
    (φ.app k').unop ≫ (A.map h).unop = (B.map h).unop ≫ (φ.app k).unop := by
  have := congrArg Quiver.Hom.unop (φ.naturality h)
  rw [unop_comp, unop_comp] at this
  exact this

theorem MVnat_of (hD : Dict) (hΔ : Delta) (hE : Exact) : MVnat := by
  intro R _ F K _ X U V W f g a b hM
  have dk : ∀ (n : ℤ) (k : K), ∃ δ : H R (sch.obj (W.obj k).unop) F n →+ H R (sch.obj (X.obj k).unop) F (n + 1),
      ∀ w x, Conn F (a.app k).unop (f.app k).unop (g.app k).unop n w x ↔ δ w = x :=
    fun n k => hΔ R F _ _ _ _ (hM k) n
  choose δ hδ using dk
  refine ⟨{
    f := fun n => Functor.whiskerRight f (Hf F n)
    g := fun n => Functor.whiskerRight g (Hf F n)
    a := fun n => Functor.whiskerRight a (Hf F n)
    b := fun n => Functor.whiskerRight b (Hf F n)
    δ := fun n =>
      { app := fun k => AddCommGrpCat.ofHom (δ n k)
        naturality := fun k k' h => by
          apply AddCommGrpCat.hom_ext
          ext w
          show δ n k' (pull R (sch.map (W.map h).unop) F n w) = pull R (sch.map (X.map h).unop) F (n + 1) (δ n k w)
          exact (hδ n k' _ _).1 (conn_pull hD F _ _ _ _ _ _ _ _ _ _ (unop_nat a h) (unop_nat f h) (unop_nat g h) n _ _
            ((hδ n k _ _).2 rfl)) }
    comm := fun n => by
      ext k : 2
      simp only [NatTrans.comp_app, Functor.whiskerRight_app]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply Quiver.Hom.unop_inj
      rw [unop_comp, unop_comp]
      exact (hM k).2.2.1.w
    exUV := fun n k u v h => (hE R F _ _ _ _ (hM k) n).1 u v h
    exX := fun n k x h1 h2 => by
      obtain ⟨w, hw⟩ := (hE R F _ _ _ _ (hM k) n).2.1 x h1 h2
      exact ⟨w, (hδ n k w x).1 hw⟩
    exW := fun n k w => (hδ n k w 0).symm.trans ((hE R F _ _ _ _ (hM k) n).2.2 w) }⟩

end LateralTheory.KummerTheory.MVnatPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.BCPf
open LateralTheory.KummerTheory.ContCut

@[reassoc] theorem bcHom_fst {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    bcHom f p r e s ≫ pullback.fst p (Spec.map s) = pullback.fst r (Spec.map s) ≫ f := by
  unfold bcHom pullback.map; exact pullback.lift_fst _ _ _

theorem bcHom_snd {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    bcHom f p r e s ≫ pullback.snd p (Spec.map s) = pullback.snd r (Spec.map s) := by
  unfold bcHom pullback.map; rw [pullback.lift_snd, Category.comp_id]

theorem bcHom_isPullback {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) :
    IsPullback (bcHom f p r e s) (pullback.fst r (Spec.map s)) (pullback.fst p (Spec.map s)) f := by
  have big : IsPullback (bcHom f p r e s ≫ pullback.snd p (Spec.map s)) (pullback.fst r (Spec.map s))
      (Spec.map s) (f ≫ p) := by
    rw [bcHom_snd, e]; exact (IsPullback.of_hasPullback r (Spec.map s)).flip
  exact IsPullback.of_right big (bcHom_fst f p r e s) (IsPullback.of_hasPullback p (Spec.map s)).flip

theorem bcHom_open {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) [IsOpenImmersion f] : IsOpenImmersion (bcHom f p r e s) :=
  MorphismProperty.of_isPullback (bcHom_isPullback f p r e s).flip ‹_›

theorem bcHom_range {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) (x : ↥(pullback p (Spec.map s))) (hx : pullback.fst p (Spec.map s) x ∈ Set.range f) :
    x ∈ Set.range (bcHom f p r e s) := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨q, hq, -⟩ := Scheme.exists_preimage_of_isPullback (bcHom_isPullback f p r e s) x u hu.symm
  exact ⟨q, hq⟩

theorem BC_of : BC := by
  intro R A s W U V X a b f g p pU pV pW ea eb ef eg h
  obtain ⟨hf, hg, hpb, hcov⟩ := h
  refine ⟨bcHom_open f p pU ef s, bcHom_open g p pV eg s, ?_, ?_⟩
  · have sq1 : IsPullback (pullback.fst pW (Spec.map s)) (bcHom b pV pW eb s) b (pullback.fst pV (Spec.map s)) :=
      (bcHom_isPullback b pV pW eb s).flip
    have big0 := sq1.paste_horiz hpb
    have big : IsPullback (bcHom a pU pW ea s ≫ pullback.fst pU (Spec.map s)) (bcHom b pV pW eb s) f
        (bcHom g p pV eg s ≫ pullback.fst p (Spec.map s)) := by
      rw [bcHom_fst, bcHom_fst]; exact big0
    refine IsPullback.of_right big ?_ (bcHom_isPullback f p pU ef s).flip
    apply pullback.hom_ext
    · simp only [Category.assoc, bcHom_fst, bcHom_fst_assoc]; rw [hpb.w]
    · simp only [Category.assoc, bcHom_snd]
  · intro x
    rcases hcov (pullback.fst p (Spec.map s) x) with hx | hx
    · exact Or.inl (bcHom_range f p pU ef s x hx)
    · exact Or.inr (bcHom_range g p pV eg s x hx)

end LateralTheory.KummerTheory.BCPf
end
end

section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.KummerTheory.FivePf
open LateralTheory.KummerTheory.ContCut

variable {K : Type 1} [Category.{0} K]

theorem mapc (G : K ⥤ AddCommGrpCat.{1}) {a b d : K} (f : a ⟶ b) (g : b ⟶ d) (x : G.obj a) :
    (G.map g).hom ((G.map f).hom x) = (G.map (f ≫ g)).hom x := by
  rw [G.map_comp]; rfl

theorem natap {F G : K ⥤ AddCommGrpCat.{1}} (α : F ⟶ G) {k k' : K} (h : k ⟶ k') (x : F.obj k) :
    (α.app k').hom ((F.map h).hom x) = (G.map h).hom ((α.app k).hom x) := by
  have := congrArg (fun φ => φ.hom x) (α.naturality h)
  exact this

theorem commap {X U V W : ℤ → K ⥤ AddCommGrpCat.{1}} (S : MVSeq X U V W) (n : ℤ) (k : K) (x : (X n).obj k) :
    ((S.a n).app k).hom (((S.f n).app k).hom x) = ((S.b n).app k).hom (((S.g n).app k).hom x) := by
  have := congrArg (fun φ => (φ.app k).hom x) (S.comm n)
  exact this

variable {J : Type} [SmallCategory J] {D : J ⥤ K}

theorem natι {F G : K ⥤ AddCommGrpCat.{1}} (α : F ⟶ G) (c : Cocone D) (j : J) (x : F.obj (D.obj j)) :
    (α.app c.pt).hom ((F.map (c.ι.app j)).hom x) = (G.map (c.ι.app j)).hom ((α.app (D.obj j)).hom x) :=
  natap α (c.ι.app j) x

theorem push (G : K ⥤ AddCommGrpCat.{1}) (c : Cocone D) {j k : J} (f : j ⟶ k) (y : G.obj (D.obj j)) :
    (G.map (c.ι.app k)).hom ((G.map (D.map f)).hom y) = (G.map (c.ι.app j)).hom y := by
  rw [mapc, c.w]

theorem five_succ [IsFiltered J] (X U V W : ℤ → K ⥤ AddCommGrpCat.{1}) (S : MVSeq X U V W) (c : Cocone D)
    (hU : ∀ n, Lim (U n) c) (hV : ∀ n, Lim (V n) c) (hW : ∀ n, Lim (W n) c) (m : ℤ) : Lim (X (m + 1)) c := by
  constructor
  · intro x
    obtain ⟨j1, u, hu⟩ := (hU (m + 1)).1 (((S.f (m + 1)).app c.pt).hom x)
    obtain ⟨j2, v, hv⟩ := (hV (m + 1)).1 (((S.g (m + 1)).app c.pt).hom x)
    obtain ⟨k, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs j1 j2
    have e0 : ((W (m + 1)).map (c.ι.app k)).hom
        (((S.a (m + 1)).app (D.obj k)).hom (((U (m + 1)).map (D.map g1)).hom u) -
          ((S.b (m + 1)).app (D.obj k)).hom (((V (m + 1)).map (D.map g2)).hom v)) = 0 := by
      rw [map_sub, ← natι (S.a (m + 1)), ← natι (S.b (m + 1)), push, push, hu, hv, commap, sub_self]
    obtain ⟨k2, f2, h2⟩ := (hW (m + 1)).2 k _ e0
    rw [map_sub, ← natap (S.a (m + 1)), ← natap (S.b (m + 1)), sub_eq_zero] at h2
    obtain ⟨x', hx1, hx2⟩ := S.exUV (m + 1) (D.obj k2) _ _ h2
    obtain ⟨xi, hxi⟩ : ∃ xi : (X (m + 1)).obj c.pt, xi = ((X (m + 1)).map (c.ι.app k2)).hom x' := ⟨_, rfl⟩
    have hfd : ((S.f (m + 1)).app c.pt).hom (x - xi) = 0 := by
      rw [map_sub, hxi, natι (S.f (m + 1)), hx1, push, push, hu, sub_self]
    have hgd : ((S.g (m + 1)).app c.pt).hom (x - xi) = 0 := by
      rw [map_sub, hxi, natι (S.g (m + 1)), hx2, push, push, hv, sub_self]
    obtain ⟨w, hw⟩ := S.exX m c.pt _ hfd hgd
    obtain ⟨j3, w0, hw0⟩ := (hW m).1 w
    obtain ⟨k4, g3, g4, -⟩ := IsFilteredOrEmpty.cocone_objs k2 j3
    refine ⟨k4, ((X (m + 1)).map (D.map g3)).hom x' + ((X (m + 1)).map (D.map g4)).hom (((S.δ m).app (D.obj j3)).hom w0), ?_⟩
    rw [map_add (f := _), push, push, ← natι (S.δ m), hw0, hw, ← hxi]
    exact add_sub_cancel _ _
  · intro j y hy
    have hfy : ((U (m + 1)).map (c.ι.app j)).hom (((S.f (m + 1)).app (D.obj j)).hom y) = 0 := by
      rw [← natι (S.f (m + 1)), hy, map_zero]
    obtain ⟨k1, f1, h1⟩ := (hU (m + 1)).2 j _ hfy
    have hgy : ((V (m + 1)).map (c.ι.app k1)).hom
        (((V (m + 1)).map (D.map f1)).hom (((S.g (m + 1)).app (D.obj j)).hom y)) = 0 := by
      rw [push, ← natι (S.g (m + 1)), hy, map_zero]
    obtain ⟨k2, f2, h2⟩ := (hV (m + 1)).2 k1 _ hgy
    have hf1 : ((S.f (m + 1)).app (D.obj k2)).hom (((X (m + 1)).map (D.map (f1 ≫ f2))).hom y) = 0 := by
      rw [natap, D.map_comp, ← mapc, h1, map_zero]
    have hg1 : ((S.g (m + 1)).app (D.obj k2)).hom (((X (m + 1)).map (D.map (f1 ≫ f2))).hom y) = 0 := by
      rw [natap, D.map_comp, ← mapc, h2]
    obtain ⟨w, hw⟩ := S.exX m (D.obj k2) _ hf1 hg1
    have hdw : ((S.δ m).app c.pt).hom (((W m).map (c.ι.app k2)).hom w) = 0 := by
      rw [natι (S.δ m), hw, push, hy]
    obtain ⟨u, v, huv⟩ := (S.exW m c.pt _).1 hdw
    obtain ⟨j1, u0, hu0⟩ := (hU m).1 u
    obtain ⟨j2, v0, hv0⟩ := (hV m).1 v
    obtain ⟨k3, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs j1 j2
    obtain ⟨k4, g3, g4, -⟩ := IsFilteredOrEmpty.cocone_objs k2 k3
    have he : ((W m).map (c.ι.app k4)).hom (((W m).map (D.map g3)).hom w -
        (((S.a m).app (D.obj k4)).hom (((U m).map (D.map (g1 ≫ g4))).hom u0) -
          ((S.b m).app (D.obj k4)).hom (((V m).map (D.map (g2 ≫ g4))).hom v0))) = 0 := by
      rw [map_sub, map_sub, push, ← natι (S.a m), ← natι (S.b m), push, push, hu0, hv0, huv, sub_self]
    obtain ⟨k5, g5, h5⟩ := (hW m).2 k4 _ he
    rw [map_sub, sub_eq_zero, mapc, map_sub, ← natap (S.a m), ← natap (S.b m)] at h5
    refine ⟨k5, (f1 ≫ f2) ≫ g3 ≫ g5, ?_⟩
    rw [D.map_comp, ← mapc, ← hw, ← natap (S.δ m), D.map_comp, h5]
    exact (S.exW m _ _).2 ⟨_, _, rfl⟩

theorem Five_of : LateralTheory.KummerTheory.ContCut.Five := by
  intro J _ _ K _ X U V W ⟨S⟩ D c hU hV hW n
  have := five_succ X U V W S c hU hV hW (n - 1)
  rwa [sub_add_cancel] at this

end LateralTheory.KummerTheory.FivePf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.TwExtPf

theorem sep {M : Shv ℤ} {U : Scheme.{0}} (x y : Sec M U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hP⟩ := h
  exact Sheaf.isSeparated M U S hS x y (fun V g hg => hP _ g hg)

theorem TwExt_of (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hM : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) :
    LateralTheory.KummerTheory.BockCut.TwExt := by
  intro Q _ i M φ ψ h
  refine (hM ℤ φ).2.2.2 ψ fun U a => ?_
  obtain ⟨S, hS, hP⟩ := (hT Q i).1 U a
  refine sep _ _ ⟨S, hS, fun V g hg => ?_⟩
  have nφ : Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) :=
    congrArg (fun f => (ModuleCat.Hom.hom f) a) (φ.hom.naturality g.op).symm
  have nψ : Sec.res g (Sec.map ψ a) = Sec.map ψ (Sec.res g a) :=
    congrArg (fun f => (ModuleCat.Hom.hom f) a) (ψ.hom.naturality g.op).symm
  show Sec.res g (Sec.map φ a) = Sec.res g (Sec.map ψ a)
  rw [nφ, nψ]
  have ha : Sec.res g a = 0 ∨ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = c • LateralTheory.KummerTheory.BockCut.genZ i ζ := hP V g hg
  rcases ha with h0 | ⟨ζ, c, hc⟩
  · have e : (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = 0 := h0
    rw [e]; simp only [Sec.map, map_zero]
  · rw [hc]; have hh := h V ζ; simp only [Sec.map] at hh ⊢; rw [map_nsmul, map_nsmul, hh]

end LateralTheory.KummerTheory.TwExtPf
end
end
