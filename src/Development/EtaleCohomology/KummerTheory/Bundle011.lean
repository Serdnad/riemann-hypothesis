module

public import Development.EtaleCohomology.KummerTheory.Bundle003
public import Development.EtaleCohomology.KummerTheory.CupAWCutEv
public import Development.EtaleCohomology.TateTwists.Bundle013
public import Development.EtaleCohomology.TateTwists.Bundle006
public import Development.EtaleCohomology.KummerTheory.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle007
public import Development.EtaleCohomology.TateTwists.Bundle005
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.FlasquePf

variable {R : Type} [CommRing R]

def toG (G : Shv R) {W : Scheme.{0}} (t : Sec G W) : (freeP R).obj (yoneda.obj W) ⟶ G.obj where
  app V := ModuleCat.freeDesc
    (TypeCat.ofHom fun (f : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj V)) => (Sec.res f.down t : G.obj.obj V))
  naturality V V' h := by
    apply ModuleCat.free_hom_ext
    intro x
    change ModuleCat.freeDesc _ ((ModuleCat.free _).map (uliftFunctor.map ((yoneda.obj W).map h))
      (ModuleCat.freeMk x)) = (G.obj.map h).hom (ModuleCat.freeDesc _ (ModuleCat.freeMk x))
    rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    change (G.obj.map (h.unop ≫ x.down).op).hom t = (G.obj.map h).hom ((G.obj.map x.down.op).hom t)
    rw [op_comp, Functor.map_comp]
    rfl

def ofSec (G : Shv R) {W : Scheme.{0}} (t : Sec G W) : (free R).obj (yoneda.obj W) ⟶ G :=
  ((sheafificationAdjunction _ _).homEquiv _ G).symm (toG G t)

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (h : V ⟶ U) (x : P.obj (op U)) :
    Sec.res h (freeGen R P U x) = freeGen R P V (P.map h.op x) := by
  unfold freeGen Sec.res
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U) ≫
    (sheafify Scheme.etaleTopology ((freeP R).obj P)).map h.op).hom (ModuleCat.freeMk (ULift.up x)) = _
  rw [← NatTrans.naturality]
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
    ((ModuleCat.free _).map _ (ModuleCat.freeMk _)) = _
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom y)
    (ModuleCat.free_map_apply _ _)

theorem freeGen_map {P Q : PSh} (m : P ⟶ Q) {V : Scheme.{0}} (x : P.obj (op V)) :
    (((free R).map m).hom.app (op V)).hom (freeGen R P V x) = freeGen R Q V (m.app _ x) := by
  unfold freeGen
  calc _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyMap Scheme.etaleTopology ((freeP R).map m)).app
        (op V)).hom (ModuleCat.freeMk (ULift.up x)) := rfl
    _ = (((freeP R).map m ≫ toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op V)).hom
        (ModuleCat.freeMk (ULift.up x)) := by rw [toSheafify_naturality]
    _ = _ := by
      change ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op V)).hom
        ((ModuleCat.free _).map _ (ModuleCat.freeMk _)) = _
      exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op V)).hom y)
        (ModuleCat.free_map_apply _ _)

theorem ofSec_gen (G : Shv R) {W : Scheme.{0}} (t : Sec G W) :
    ((ofSec G t).hom.app (op W)).hom (freeGen R (yoneda.obj W) W (𝟙 W)) = t := by
  have h : toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj W)) ≫ (ofSec G t).hom = toG G t :=
    toSheafify_sheafifyLift _ _ _
  have h2 : ((ofSec G t).hom.app (op W)).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj (yoneda.obj W))).app
      (op W)).hom (ModuleCat.freeMk (ULift.up (𝟙 W)))) = ((toG G t).app (op W)).hom (ModuleCat.freeMk (ULift.up (𝟙 W))) := by
    rw [← h]; rfl
  unfold freeGen
  rw [h2]
  change (ModuleCat.freeDesc _ (ModuleCat.freeMk _)) = t
  refine (ModuleCat.freeDesc_apply _ _).trans ?_
  change (G.obj.map (𝟙 (op W))).hom t = t
  rw [CategoryTheory.Functor.map_id]
  rfl

instance mono_freeP {W U : Scheme.{0}} (a : W ⟶ U) [Mono a] : Mono ((freeP R).map (yoneda.map a)) := by
  have : ∀ V, Mono (((freeP R).map (yoneda.map a)).app V) := by
    intro V
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (Finsupp.mapDomain _)
    apply Finsupp.mapDomain_injective
    intro x y e
    apply ULift.ext
    exact (cancel_mono a).1 (congrArg ULift.down e)
  exact NatTrans.mono_of_mono_app _

instance mono_free {W U : Scheme.{0}} (a : W ⟶ U) [Mono a] : Mono ((free R).map (yoneda.map a)) := by
  change Mono ((presheafToSheaf _ _).map ((freeP R).map (yoneda.map a)))
  infer_instance

theorem Flasque_of : LateralTheory.KummerTheory.ContCut.Flasque := by
  intro R _ G _ W U a _ t
  let φ := ofSec G t
  let ψ := Injective.factorThru φ ((free R).map (yoneda.map a))
  have hψ : (free R).map (yoneda.map a) ≫ ψ = φ := Injective.comp_factorThru _ _
  refine ⟨(ψ.hom.app (op U)).hom (freeGen R (yoneda.obj U) U (𝟙 U)), ?_⟩
  change (G.obj.map a.op).hom ((ψ.hom.app (op U)).hom _) = t
  have nat := congrArg (fun k => k.hom (freeGen R (yoneda.obj U) U (𝟙 U))) (ψ.hom.naturality a.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at nat
  rw [← nat]
  change (ψ.hom.app (op W)).hom (Sec.res a (freeGen R (yoneda.obj U) U (𝟙 U))) = t
  rw [freeGen_res]
  have e : (yoneda.obj U).map a.op (𝟙 U) = (yoneda.map a).app (op W) (𝟙 W) := by simp
  rw [e, ← freeGen_map]
  rw [← ofSec_gen G t]
  exact congrArg (fun k => (k.hom.app (op W)).hom (freeGen R (yoneda.obj W) W (𝟙 W))) hψ

end LateralTheory.KummerTheory.FlasquePf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.GluePf

def pc (U V : Scheme.{0}) : Bool → Scheme.{0} := fun b => Bool.rec V U b

def pm {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) : ∀ b : Bool, pc U V b ⟶ X :=
  fun b => Bool.rec (motive := fun b => pc U V b ⟶ X) g f b

theorem mem_cover {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : LateralTheory.KummerTheory.ContCut.IsMV a b f g) :
    Sieve.generate (Presieve.ofArrows (pc U V) (pm f g)) ∈ Scheme.etaleTopology X := by
  obtain ⟨hf, hg, -, hcov⟩ := h
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2 ⟨fun x => ?_, fun i => ?_⟩
  · rcases hcov x with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · cases i
    · exact (inferInstance : Etale g)
    · exact (inferInstance : Etale f)

theorem sheafFor {R : Type} [CommRing R] (G : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V)
    (f : U ⟶ X) (g : V ⟶ X) (h : LateralTheory.KummerTheory.ContCut.IsMV a b f g) :
    Presieve.IsSheafFor (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))
      (Presieve.ofArrows (pc U V) (pm f g)) := by
  have hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.property
  rw [Presieve.isSheafFor_iff_generate]
  exact hG.isSheafFor _ (mem_cover a b f g h)

theorem compat {R : Type} [CommRing R] (G : Shv R) {W U V X : Scheme.{0}} {a : W ⟶ U} {b : W ⟶ V}
    {f : U ⟶ X} {g : V ⟶ X} (hpb : IsPullback a b f g) {s : Sec G U} {t : Sec G V}
    (hst : Sec.res a s = Sec.res b t) {Z : Scheme.{0}} (gi : Z ⟶ U) (gj : Z ⟶ V) (e : gi ≫ f = gj ≫ g) :
    (G.obj.map gi.op).hom s = (G.obj.map gj.op).hom t := by
  obtain ⟨l, hl1, hl2⟩ := hpb.exists_lift gi gj e
  subst hl1 hl2
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (G.obj.map l.op).hom hst

theorem Glue_of : LateralTheory.KummerTheory.ContCut.Glue := by
  intro R _ G W U V X a b f g h
  have hS := sheafFor G a b f g h
  rw [Presieve.isSheafFor_arrows_iff] at hS
  obtain ⟨hf, hg, hpb, -⟩ := h
  refine ⟨fun z hz1 hz2 => ?_, fun s t hst => ?_⟩
  · have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (pm f g)
        (fun _ => (0 : Sec G _)) := by
      intro i j Z gi gj _
      change (G.obj.map gi.op).hom 0 = (G.obj.map gj.op).hom 0
      simp
    obtain ⟨t, -, ht⟩ := hS _ hc
    have e1 := ht z (fun i => by cases i <;> assumption)
    have e2 := ht 0 (fun i => by
      change (G.obj.map _).hom 0 = 0
      simp)
    rw [e1, e2]
  · let x : ∀ i, Sec G (pc U V i) := fun i => Bool.rec (motive := fun i => Sec G (pc U V i)) t s i
    have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (pm f g) x := by
      intro i j Z gi gj e
      change (G.obj.map gi.op).hom (x i) = (G.obj.map gj.op).hom (x j)
      cases i <;> cases j
      · have : gi = gj := (cancel_mono g).1 e
        subst this; rfl
      · exact (compat G hpb hst gj gi e.symm).symm
      · exact compat G hpb hst gi gj e
      · have : gi = gj := (cancel_mono f).1 e
        subst this; rfl
    obtain ⟨z, hz, -⟩ := hS x hc
    exact ⟨z, hz true, hz false⟩

end LateralTheory.KummerTheory.GluePf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AffPf
open LateralTheory.KummerTheory.ContCut

theorem lim_of_iso {J : Type} [SmallCategory J] {K : Type 1} [Category.{0} K] {G G' : K ⥤ AddCommGrpCat.{1}}
    (e : G ≅ G') {D : J ⥤ K} (c : Cocone D) (h : Lim G c) : Lim G' c := by
  have nat : ∀ {a b : K} (f : a ⟶ b) (z : G.obj a), (G'.map f).hom ((e.hom.app a).hom z) = (e.hom.app b).hom ((G.map f).hom z) := by
    intro a b f z
    have := congrArg (fun φ => φ.hom z) (e.hom.naturality f)
    simpa using this.symm
  have inv : ∀ (a : K) (z : G'.obj a), (e.hom.app a).hom ((e.inv.app a).hom z) = z := by
    intro a z
    have := congrArg (fun φ => φ.hom z) (e.inv_hom_id_app a)
    simpa using this
  have inv' : ∀ (a : K) (z : G.obj a), (e.inv.app a).hom ((e.hom.app a).hom z) = z := by
    intro a z
    have := congrArg (fun φ => φ.hom z) (e.hom_inv_id_app a)
    simpa using this
  have natc : ∀ (j : J) (z : G.obj (D.obj j)), (G'.map (c.ι.app j)).hom ((e.hom.app (D.obj j)).hom z) =
      (e.hom.app c.pt).hom ((G.map (c.ι.app j)).hom z) := fun j z => nat (c.ι.app j) z
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := h.1 ((e.inv.app c.pt).hom x)
    refine ⟨j, (e.hom.app (D.obj j)).hom y, ?_⟩
    rw [natc, hy, inv]
  · have h0 : (G.map (c.ι.app j)).hom ((e.inv.app (D.obj j)).hom y) = 0 := by
      have h1 := natc j ((e.inv.app (D.obj j)).hom y)
      rw [inv, hy] at h1
      have h2 := congrArg (e.inv.app c.pt).hom h1
      rw [inv', map_zero] at h2
      exact h2.symm
    obtain ⟨k, f, hf⟩ := h.2 j _ h0
    refine ⟨k, f, ?_⟩
    have h1 := nat (D.map f) ((e.inv.app (D.obj j)).hom y)
    rw [inv, hf, map_zero] at h1
    exact h1

theorem Aff_of (hR : AffRing) : Aff := by
  intro hb q X _ R p hq J _ _ D c hc n i
  obtain ⟨T, ⟨e⟩, hmap, hcol⟩ := hR p
  obtain ⟨hT⟩ := hcol c hc
  have unit : ∀ A, IsUnit ((q : ℕ) : T.obj A) := by
    intro A
    obtain ⟨φ⟩ := hmap A
    simpa using hq.map φ.hom
  have key : Lim (T ⋙ Scheme.Spec.rightOp ⋙ Hf (tw q i) n) c := by
    have hB := hb q (D ⋙ T) (T.mapCocone c) hT n i
    refine ⟨fun x => ?_, fun j y hy => ?_⟩
    · obtain ⟨j, y, hy⟩ := hB.1 x (unit c.pt)
      exact ⟨j, y, hy⟩
    · obtain ⟨k, f, hf⟩ := hB.2 j y (unit (D.obj j)) hy
      exact ⟨k, f, hf⟩
  exact lim_of_iso (Functor.isoWhiskerRight e (Hf (tw q i) n)).symm c key

end LateralTheory.KummerTheory.AffPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DE
variable {R : Type} [CommRing R] {I : Cx R} {X : Scheme.{0}} {n : ℤ}

def eta (a : Sec (I.X n) X) : (freeP R).obj (yoneda.obj X) ⟶ (I.X n).obj where
  app U := ModuleCat.freeDesc (↾fun y : ULift.{1} (U.unop ⟶ X) => ((I.X n).obj.map y.down.op).hom a)
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro y
    erw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.free_map_apply]
    erw [ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    erw [← ModuleCat.comp_apply, ← Functor.map_comp]
    rfl

theorem eta_app (a : Sec (I.X n) X) (U : Scheme.{0}) (x : U ⟶ X) :
    ((eta a).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = Sec.res x a := by
  erw [eta, ModuleCat.freeDesc_apply]
  rfl

def phi (a : Sec (I.X n) X) : (free R).obj (yoneda.obj X) ⟶ I.X n :=
  ⟨sheafifyLift Scheme.etaleTopology (eta a) (I.X n).property⟩

theorem phi_gen (a : Sec (I.X n) X) (U : Scheme.{0}) (x : U ⟶ X) :
    Sec.map (phi a) (freeGen R (yoneda.obj X) U x) = Sec.res x a := by
  have key := congrArg (fun t => (t.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (eta a) (I.X n).property)
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at key
  exact key.trans (eta_app a U x)

def coch (a : Sec (I.X n) X) : Cochain ((chains R).obj (sch.obj X)) I n :=
  Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((chainsXIso R (sch.obj X) 0).hom ≫ phi a) n

theorem coch_zero (a : Sec (I.X n) X) (h : -((0 : ℕ) : ℤ) + n = n) (U : Scheme.{0}) (x : U ⟶ X) :
    ev (R := R) (coch a) 0 n h U x = Sec.res x a := by
  change Sec.map ((chainsXIso R _ 0).inv ≫ (coch a).v _ _ h) (freeGen R ((sch.obj X).obj (op (SimplexCategory.mk 0))) U x) = _
  rw [coch, Cochain.single_v]
  erw [Iso.inv_hom_id_assoc]
  exact phi_gen a U x

theorem coch_succ (a : Sec (I.X n) X) (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx (sch.obj X) (p + 1) U) : ev (R := R) (coch a) (p + 1) s h U x = 0 := by
  rw [AW.ev_eq, coch, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), comp_zero]
  rfl

theorem ev_zero_cochain {E : Spc} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  simp [ev]

theorem coch_delta (a : Sec (I.X n) X) (ha : Sec.map (I.d n (n + 1)) a = 0) : δ n (n + 1) (coch a) = 0 := by
  apply AW.ev_ext
  intro p s h U x
  rw [ev_zero_cochain]
  rcases p with _ | p
  · obtain rfl : s = n + 1 := by omega
    rw [AW.ev_delta_zero rfl (coch a) n (n + 1) (by simp) h U x, coch_zero a (by simp) U x]
    have e := AW.sec_map_res (I.d n (n + 1)) (show U ⟶ X from x) a
    rw [ha] at e
    exact e.symm.trans (LinearMap.map_zero _)
  · rw [AW.ev_delta_succ rfl (coch a) p (-((p + 1 : ℕ) : ℤ) + n) s rfl h U x, coch_succ]
    rw [show Sec.map (I.d (-((p + 1 : ℕ) : ℤ) + n) s) (0 : Sec (I.X (-((p + 1 : ℕ) : ℤ) + n)) U) = 0 from LinearMap.map_zero _, zero_add]
    rcases p with _ | p
    · have hs : n = s := by omega
      subst hs
      rw [Fin.sum_univ_two]
      have e : ∀ i : Fin 2, ev (R := R) (coch a) 0 n (by omega) U (x.face i) =
          Sec.res (show U ⟶ X from x) a := fun i => coch_zero a _ U _
      rw [e 0, e 1]
      simp
    · simp only [coch_succ, smul_zero, Finset.sum_const_zero]

theorem dictExist : DictExist := by
  intro R _ I X n a ha
  refine ⟨⟨coch a, (Cocycle.mem_iff n (n + 1) rfl _).2 (coch_delta a ha)⟩, ?_, ?_⟩
  · exact (coch_zero a (by simp) X (𝟙 X)).trans (by rw [Sec.res, op_id, CategoryTheory.Functor.map_id]; rfl)
  · intro p s h U y
    exact coch_succ a p s h U y

end LateralTheory.KummerTheory.DE

namespace LateralTheory.KummerTheory

theorem DictExist_of : DictExist := DE.dictExist
end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DZ

theorem ev_zero' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} p s h U x :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  have e := LateralTheory.KummerTheory.AW.ev_add (0 : Cochain ((chains R).obj E) I n) 0 p s h U x
  rw [add_zero] at e
  simpa using e.symm

end LateralTheory.KummerTheory.DZ

open LateralTheory.KummerTheory.DZ LateralTheory.EtaleFoundations in
theorem LateralTheory.KummerTheory.DictZero_of : LateralTheory.KummerTheory.DictZero := by
  intro R _ I X n α hα
  refine ⟨?_, ?_⟩
  · rw [← LateralTheory.KummerTheory.AW.ev_delta_zero (m := n + 1) rfl α.1 n (n + 1) (by simp) (by simp) X (𝟙 X), Cocycle.δ_eq_zero]
    exact ev_zero' R _ _ _ _ _
  · rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α (n - 1) (by omega)]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev β 0 (n - 1) (by simp) X (𝟙 X), ?_⟩
      rw [← LateralTheory.KummerTheory.AW.ev_delta_zero (m := n) (by omega) β (n - 1) n (by simp) (by simp) X (𝟙 X), hβ]
    · rintro ⟨y, hy⟩
      obtain ⟨γ, hγ⟩ := LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data R (a0 X I (n - 1) y) (etaleSimplicialCochain_scheme_section_extension_naturality X I (n - 1) y)
      refine ⟨γ, LateralTheory.KummerTheory.AW.ev_ext _ _ ?_⟩
      intro p s h U x
      cases p with
      | zero =>
        obtain rfl : s = n := by omega
        rw [LateralTheory.KummerTheory.AW.ev_delta_zero (m := s) (by omega) γ (s - 1) s (by simp) h U x, hγ, etaleSimplicialCochain_scheme_section_extension_degree_zero]
        refine (map_res _ _ _).trans ?_
        exact (congrArg (Sec.res _) hy).trans (LateralTheory.KummerTheory.AW.ev_res α.1 0 s _ x (𝟙 X))
      | succ p =>
        rw [hα p s h U x, LateralTheory.KummerTheory.AW.ev_delta_succ (m := n) (by omega) γ p (-((p + 1 : ℕ) : ℤ) + (n - 1)) s rfl h U x]
        simp only [hγ]
        cases p with
        | zero =>
          obtain rfl : s = n - 1 := by omega
          simp [a0, Fin.sum_univ_two]
          rw [show x.face 0 = x from rfl, show x.face 1 = x from rfl]
          exact add_neg_cancel _
        | succ p => simp [a0]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RestrResPf

instance restrAdditive (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) : (restr φ).Additive where
  map_add {X Y f g} := by
    ext U x
    rfl

theorem restr_exact (hex : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S)
    (C : ShortComplex (Shv S)) (h : C.Exact) : (C.map (restr φ)).Exact :=
  (hex R (C.map (restr φ))).2 (fun U b hb => (hex S C).1 h U b hb)

theorem restr_preservesHomology (hex : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (R S : Type) [CommRing R] [CommRing S]
    (φ : R →+* S) : (restr φ).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (restr_exact hex R S φ)

theorem single_key (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr φ).obj F)).inv ≫
      ((HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F).f 0 =
    (restr φ).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv := by
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp

theorem RestrRes_of (hex : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (hres : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) :
    LateralTheory.KummerTheory.BockCut.RestrRes := by
  intro R S _ _ φ F
  haveI := restr_preservesHomology hex R S φ
  let M := (restr φ).mapHomologicalComplex (ComplexShape.up ℤ)
  let T : Cx R := M.obj (res S F)
  let σ : SemiMap (res S F) T :=
    { app := fun U s => AddMonoidHom.mk' (fun a => (show Sec (T.X s) U from a)) (fun _ _ => rfl)
      nat := fun _ _ _ => rfl
      comm := fun _ _ _ _ => rfl }
  haveI : QuasiIso (resAug F) := (hres S F).2.2.2.1
  have hq2 : QuasiIso (M.map (resAug F)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology (resAug F) (restr φ)
  let e := (HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F
  have hq1 : QuasiIso e := @quasiIso_of_isIso _ _ _ _ _ _ _ e inferInstance (fun _ => inferInstance) (fun _ => inferInstance)
  let ε : sgl ((restr φ).obj F) ⟶ T := e ≫ M.map (resAug F)
  refine ⟨T, σ, ε, ?_, fun U s => Function.bijective_id, ?_⟩
  · first
      | exact quasiIso_comp (hφ := hq1) (hφ' := hq2)
      | exact @quasiIso_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq1 hq2
  · intro U a
    have h2 : Sec.map (e.f 0) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr φ).obj F)).inv
        (show Sec ((restr φ).obj F) U from a)) =
        Sec.map ((restr φ).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv)
        (show Sec ((restr φ).obj F) U from a) :=
      congrArg (fun f => Sec.map f (show Sec ((restr φ).obj F) U from a)) (single_key R S φ F)
    change Sec.map ((restr φ).map ((resAug F).f 0)) (Sec.map (e.f 0)
      (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr φ).obj F)).inv
        (show Sec ((restr φ).obj F) U from a))) = _
    rw [h2]
    rfl

end LateralTheory.KummerTheory.RestrResPf
end
