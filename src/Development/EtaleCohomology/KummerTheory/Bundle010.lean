module

public import Development.EtaleCohomology.KummerTheory.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem ev_add (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  simp [ev, Cochain.add_v, Preadditive.comp_add]

theorem ev_neg (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h U x :
    ev (-α) p s h U x = -ev α p s h U x := by
  have h0 : ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by simp [ev]
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← ev_add, neg_add_cancel, h0]

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem val_res' (R : Type) [CommRing R] {P : PSh} {F : Shv R} (φ : (free R).obj P ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U)
    (x : P.obj (op U)) :
    Sec.res g ((φ.hom.app (op U)).hom (freeGen R P U x)) = (φ.hom.app (op V)).hom (freeGen R P V (P.map g.op x)) := by
  have e1 := congrArg (fun (f : ((free R).obj P).obj.obj (op U) ⟶ F.obj.obj (op V)) => f.hom (freeGen R P U x)) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1
  refine e1.symm.trans (congrArg _ ?_)
  have e2 := congrArg (fun (f : ((freeP R).obj P).obj (op U) ⟶ ((free R).obj P).obj.obj (op V)) => f.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  erw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at e2
  unfold freeGen
  refine e2.symm.trans (congrArg _ ?_)
  first
  | rfl
  | exact Finsupp.mapDomain_single
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem ev_res (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) :=
  val_res' R _ V U g x

theorem free_gen_map (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have e := congrArg (fun (φ : ((freeP R).obj P).obj (op U) ⟶ ((free R).obj Q).obj.obj (op U)) =>
    φ.hom (ModuleCat.freeMk (ULift.up x))) (congrArg (fun η => η.app (op U)) (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f)))
  erw [NatTrans.comp_app, NatTrans.comp_app, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.comp_apply] at e
  unfold freeGen
  refine e.symm.trans (congrArg _ ?_)
  first
  | rfl
  | exact Finsupp.mapDomain_single

theorem chainsXIso_nat (R : Type) [CommRing R] {E' E : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p : ℤ)) = (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  simp only [chainsXIso, chains, chainsN, Functor.comp_map, ComplexShape.embeddingDownNat, Functor.comp_obj]
  erw [HomologicalComplex.extendMap_f _ _ (i := p) rfl]
  simp only [AlgebraicTopology.alternatingFaceMapComplex_map_f]
  erw [Iso.inv_hom_id_assoc]
  rfl
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem ev_pre (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} {E' : Spc} (f : E' ⟶ E)
    (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  unfold ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainsXIso_nat, Category.assoc]
  exact congrArg (fun y => (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom y) (free_gen_map R _ U x)

theorem evLin : EvLin := fun R _ E I n =>
  ⟨fun α β p s h U x => ⟨ev_add R α β p s h U x, ev_neg R α p s h U x⟩,
   fun α p s h V U g x => ev_res R α p s h V U g x,
   fun f α p s h U x => ev_pre R f α p s h U x⟩
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem Dict_of' (hE : DictExist) (hN : DictNormal) (hZ : DictZero) : Dict := Dict_of evLin hE hN hZ
end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem lex_red_cast (Q q : ℕ) {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht Q E n i) :
    red Q q E n' i' (Ht.cast hn hi x) = Ht.cast hn hi (red Q q E n i x) := by
  subst hn hi; rfl

theorem lex_cast_add {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    Ht.cast hn hi (x + y) = Ht.cast hn hi x + Ht.cast hn hi y := by
  subst hn hi; rfl

theorem lex_cast_nsmul {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (m : ℕ) (x : Ht q E n i) :
    Ht.cast hn hi (m • x) = m • Ht.cast hn hi x := by
  subst hn hi; rfl

theorem lex_ext_red (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (a n i : ℤ) (x : Ht Q (sch.obj X) a i) (y : Ht Q (sch.obj Y) (n - a) 0) :
    red Q q _ n i (ext Q pX pY a n i x y) = ext q pX pY a n i (red Q q _ a i x) (red Q q _ (n - a) 0 y) := by
  unfold ext
  rw [lex_red_cast, (hA Q q hq _).1, pull_red, pull_red]

theorem lex_ext_add_left (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x x' : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i (x + x') y = ext q pX pY a n i x y + ext q pX pY a n i x' y := by
  unfold ext
  rw [map_add (f := _), map_add (f := _), AddMonoidHom.add_apply, lex_cast_add]

theorem lex_ext_add_right (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Ht q (sch.obj X) a i) (y y' : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i x (y + y') = ext q pX pY a n i x y + ext q pX pY a n i x y' := by
  unfold ext
  rw [map_add (f := _), map_add (f := _), lex_cast_add]

theorem lex_ext_nsmul_left (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (m : ℕ)
    (x : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i (m • x) y = m • ext q pX pY a n i x y := by
  unfold ext
  rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, lex_cast_nsmul]

theorem lex_ext_nsmul_right (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (m : ℕ)
    (x : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i x (m • y) = m • ext q pX pY a n i x y := by
  unfold ext
  rw [map_nsmul, map_nsmul, lex_cast_nsmul]

def lexF (hA : A11) (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0) : Hl l (sch.obj (pullback pX pY)) n i :=
  ⟨fun k => ext (l ^ k) pX pY a n i (lev l x k) (lev l y k), fun k => by
    have : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    change red (l ^ (k + 1)) (l ^ k) _ n i (ext (l ^ (k + 1)) pX pY a n i (x.1 (k + 1)) (y.1 (k + 1))) =
      ext (l ^ k) pX pY a n i (x.1 k) (y.1 k)
    exact (lex_ext_red hA _ _ (pow_dvd_pow l (Nat.le_succ k)) pX pY a n i (x.1 (k + 1)) (y.1 (k + 1))).trans
      (congrArg₂ _ (x.2 k) (y.2 k))⟩

theorem LimExtHl_of : LimExtHl := by
  intro hA l _ X Y S pX pY a n i
  refine ⟨LinearMap.mk₂ ℤ_[l] (lexF hA l pX pY a n i) ?_ ?_ ?_ ?_, fun x y k => ?_⟩
  · intro x x' y
    apply Subtype.ext; funext k
    exact lex_ext_add_left (l ^ k) pX pY a n i (x.1 k) (x'.1 k) (y.1 k)
  · intro r x y
    apply Subtype.ext; funext k
    change ext (l ^ k) pX pY a n i ((r • x).1 k) (y.1 k) = (r • (lexF hA l pX pY a n i x y).1 k : HtL l k _ n i)
    rw [Submodule.coe_smul, Pi.smul_apply, HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
    exact lex_ext_nsmul_left (l ^ k) pX pY a n i _ (x.1 k) (y.1 k)
  · intro x y y'
    apply Subtype.ext; funext k
    exact lex_ext_add_right (l ^ k) pX pY a n i (x.1 k) (y.1 k) (y'.1 k)
  · intro r x y
    apply Subtype.ext; funext k
    change ext (l ^ k) pX pY a n i (x.1 k) ((r • y).1 k) = (r • (lexF hA l pX pY a n i x y).1 k : HtL l k _ n i)
    rw [Submodule.coe_smul, Pi.smul_apply, HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
    exact lex_ext_nsmul_right (l ^ k) pX pY a n i _ (x.1 k) (y.1 k)
  · rfl

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LimLHPf

theorem cast_add' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by subst hn; subst hi; rfl

theorem cast_nsmul' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (m : ℕ) (x : Ht q E n i) :
    (m • x).cast hn hi = m • x.cast hn hi := by subst hn; subst hi; rfl

theorem red_cast (Q q : ℕ) {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht Q E n i) :
    red Q q E n' i' (x.cast hn hi) = (red Q q E n i x).cast hn hi := by subst hn; subst hi; rfl

theorem ext_add (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i)
    (y y' : Ht q (sch.obj Y) (n - a) 0) : ext q pX pY a n i x (y + y') = ext q pX pY a n i x y + ext q pX pY a n i x y' := by
  unfold LateralTheory.KummerTheory.ext; rw [map_add (f := _), map_add (f := _), cast_add']

theorem ext_nsmul (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i)
    (m : ℕ) (y : Ht q (sch.obj Y) (n - a) 0) : ext q pX pY a n i x (m • y) = m • ext q pX pY a n i x y := by
  unfold LateralTheory.KummerTheory.ext; rw [map_nsmul, map_nsmul, cast_nsmul']

theorem red_ext (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Ht Q (sch.obj X) a i) (y : Ht Q (sch.obj Y) (n - a) 0) :
    red Q q _ n i (ext Q pX pY a n i x y) = ext q pX pY a n i (red Q q _ a i x) (red Q q _ (n - a) 0 y) := by
  unfold LateralTheory.KummerTheory.ext
  rw [red_cast, (hA Q q hq _).1, ← pull_red, ← pull_red]

theorem lh_add (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ)
    (y y' : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    lh q pX pY i r c M n (y + y') = lh q pX pY i r c M n y + lh q pX pY i r c M n y' := by
  unfold LateralTheory.KummerTheory.lh
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact ext_add _ _ _ _ _ _ _ _ _

theorem lh_nsmul (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ) (m : ℕ)
    (y : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    lh q pX pY i r c M n (m • y) = m • lh q pX pY i r c M n y := by
  unfold LateralTheory.KummerTheory.lh
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact ext_nsmul _ _ _ _ _ _ _ _ _

theorem red_lh (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht Q (sch.obj X) a i) (M : ℕ) (n : ℤ)
    (y : ∀ a : Fin (M + 1), Fin (r a) → Ht Q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    red Q q _ n i (lh Q pX pY i r c M n y) =
      lh q pX pY i r (fun a s => red Q q _ a i (c a s)) M n (fun a s => red Q q _ _ 0 (y a s)) := by
  unfold LateralTheory.KummerTheory.lh

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact red_ext hA Q q hq _ _ _ _ _ _ _

theorem lev_red (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} (x : Hl l E n i) (k : ℕ) :
    red (l ^ (k + 1)) (l ^ k) E n i (lev l x (k + 1)) = lev l x k := x.2 k

instance nz (l : ℕ) [Fact l.Prime] (k : ℕ) : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem dvd_succ (l k : ℕ) : l ^ k ∣ l ^ (k + 1) := pow_dvd_pow l (Nat.le_succ k)

variable {l : ℕ} [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i)

def phiFun (hA : A11) (y : ∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    Hl l (sch.obj (pullback pX pY)) n i :=
  ⟨fun k => lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k), fun k => by
    change red (l ^ (k + 1)) (l ^ k) _ n i (lh (l ^ (k + 1)) pX pY i r (fun a s => lev l (c a s) (k + 1)) M n
      (fun a s => lev l (y a s) (k + 1))) = _
    rw [red_lh hA _ _ (dvd_succ l k)]
    simp only [lev_red]⟩

def phi (hA : A11) : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
    Hl l (sch.obj (pullback pX pY)) n i where
  toFun := phiFun pX pY n i M r c hA
  map_add' y y' := Subtype.ext (funext fun k => by
    change lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k + lev l (y' a s) k) =
      lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k) +
      lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y' a s) k)
    rw [← lh_add]; rfl)
  map_smul' t y := Subtype.ext (funext fun k => by
    change lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => (t • (show HtL l k _ _ _ from lev l (y a s) k))) =
      (t • (show HtL l k _ _ _ from lev l (phiFun pX pY n i M r c hA y) k))
    have h1 : (fun (a : Fin (M + 1)) (s : Fin (r a)) =>
        (t • (show HtL l k (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0 from lev l (y a s) k) : Ht (l ^ k) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0)) =
        (PadicInt.toZModPow k t).val • (fun (a : Fin (M + 1)) (s : Fin (r a)) => lev l (y a s) k) :=
      funext fun a => funext fun s => HtL.smul_eq l k k le_rfl _ _ _ t _
    rw [h1, lh_nsmul]
    exact (HtL.smul_eq l k k le_rfl _ _ _ t _).symm)

theorem phi_ker (hA : A11) (N : ℕ)
    (hiso : ∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n))
    (y : ∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0)
    (hy : phi pX pY n i M r c hA y = 0) : N • y = 0 := by
  funext a s
  apply Subtype.ext; funext k
  have h0 : lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k) = 0 := by
    have := congrArg (fun z : Hl l (sch.obj (pullback pX pY)) n i => lev l z k) hy
    exact this
  have := congrFun (congrFun ((hiso k).1 _ h0) a) s
  exact this

theorem phi_coker (hA : A11) (N : ℕ)
    (hfin : ∀ (k : ℕ) (m : ℤ), Finite (Ht (l ^ k) (sch.obj Y) m 0))
    (hiso : ∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n))
    (b : Hl l (sch.obj (pullback pX pY)) n i) : ∃ y, phi pX pY n i M r c hA y = N • b := by
  let D : ℕ → Type 1 := fun k => ∀ a : Fin (M + 1), Fin (r a) → Ht (l ^ k) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0
  let Sl : ℕ → Type 1 := fun k => {z : D k // lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n z = N • lev l b k}
  let f : ∀ k, Sl (k + 1) ⟶ Sl k := fun k => TypeCat.ofHom fun (z : Sl (k + 1)) => (⟨fun a s => red (l ^ (k + 1)) (l ^ k) _ _ 0 (z.1 a s), by
    have h := congrArg (red (l ^ (k + 1)) (l ^ k) _ n i) z.2
    rw [red_lh hA _ _ (dvd_succ l k), map_nsmul, lev_red] at h
    simp only [lev_red] at h
    exact h⟩ : Sl k)
  let F : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence f
  have : ∀ j, Finite (F.obj j) := fun j => by
    have := hfin (unop j)
    change Finite (Sl (unop j))
    have : ∀ (a : Fin (M + 1)), Finite (Fin (r a) → Ht (l ^ unop j) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :=
      fun a => by have := hfin (unop j) (n - ((a : ℕ) : ℤ)); infer_instance
    have : Finite (D (unop j)) := Pi.finite
    exact Subtype.finite
  have : ∀ j, Nonempty (F.obj j) := fun j => by
    obtain ⟨z, hz⟩ := (hiso (unop j)).2 (lev l b (unop j))
    exact ⟨(⟨z, hz⟩ : Sl (unop j))⟩
  obtain ⟨sec, hsec⟩ := nonempty_sections_of_finite_inverse_system F
  have hstep : ∀ k a s, red (l ^ (k + 1)) (l ^ k) _ _ 0 (((sec (op (k + 1)) : Sl (k + 1)).1) a s) =
      ((sec (op k) : Sl k).1) a s := by
    intro k a s
    have h := hsec (homOfLE (Nat.le_succ k)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at h
    exact congrArg (fun z : Sl k => z.1 a s) h
  refine ⟨fun a s => ⟨fun k => ((sec (op k) : Sl k).1) a s, fun k => hstep k a s⟩, ?_⟩
  apply Subtype.ext; funext k
  exact (sec (op k) : Sl k).2

theorem LimLH_of : LimLH := by
  intro hA l _ X Y S pX pY n i M N r c hfin hiso
  exact ⟨phi pX pY n i M r c hA, fun y k => rfl,
    fun y hy => phi_ker pX pY n i M r c hA N hiso y hy, fun b => phi_coker pX pY n i M r c hA N hfin hiso b⟩

end LateralTheory.KummerTheory.LimLHPf
end
end

section

noncomputable section
open scoped TensorProduct
open GlobalTheory.EtC IsLocalRing Polynomial

namespace LateralTheory.KummerTheory

theorem hens_root_of_sub {R S : Type*} [CommRing R] [CommRing S] [HenselianLocalRing R] [IsLocalRing S]
    (φ : R →+* S) (hc : (maximalIdeal S).comap φ = maximalIdeal R) (f : S[X]) (hf : f.Monic) (a₀ : S)
    (hlift : ∀ n, f.coeff n ∈ Set.range φ) (ha : a₀ ∈ Set.range φ) (h1 : f.eval a₀ ∈ maximalIdeal S)
    (h2 : IsUnit (f.derivative.eval a₀)) : ∃ a, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal S := by
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_degree_eq_and_monic ((lifts_iff_coeff_lifts f).2 hlift) hf
  obtain ⟨b₀, rfl⟩ := ha
  have hmem : ∀ x, x ∈ maximalIdeal R ↔ φ x ∈ maximalIdeal S := fun x => by rw [← hc]; rfl
  have e1 : φ (g.eval b₀) = f.eval (φ b₀) := by rw [← hg, eval_map, eval₂_at_apply]
  have e2 : φ (g.derivative.eval b₀) = f.derivative.eval (φ b₀) := by
    rw [← hg, derivative_map, eval_map, eval₂_at_apply]
  have hu : IsUnit (g.derivative.eval b₀) := by
    by_contra hu
    have := (hmem _).1 ((mem_maximalIdeal _).2 hu)
    rw [e2] at this
    exact (mem_maximalIdeal _).1 this h2
  obtain ⟨b, hb, hbb⟩ := HenselianLocalRing.is_henselian g hgm b₀ ((hmem _).2 (e1 ▸ h1)) hu
  refine ⟨φ b, ?_, ?_⟩
  · rw [IsRoot.def] at hb ⊢
    rw [← hg, eval_map, eval₂_at_apply, hb, map_zero]
  · rw [← map_sub]; exact (hmem _).1 hbb

abbrev incMap (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [CommRing A] [Algebra κ A]
    (L : IntermediateField κ K) : A ⊗[κ] L →ₐ[A] A ⊗[κ] K :=
  Algebra.TensorProduct.map (AlgHom.id A A) L.val

theorem incMap_mono {κ K A : Type} [Field κ] [Field K] [Algebra κ K] [CommRing A] [Algebra κ A]
    {L L' : IntermediateField κ K} (h : L ≤ L') {x : A ⊗[κ] K} (hx : x ∈ (incMap κ K A L).range) :
    x ∈ (incMap κ K A L').range := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨Algebra.TensorProduct.map (AlgHom.id A A) (IntermediateField.inclusion h) y, ?_⟩
  have : (incMap κ K A L').comp (Algebra.TensorProduct.map (AlgHom.id A A) (IntermediateField.inclusion h))
      = incMap κ K A L := Algebra.TensorProduct.ext' (fun a l => by simp)
  exact congrArg (fun F : A ⊗[κ] L →ₐ[A] A ⊗[κ] K => F y) this

theorem exists_fd_range {κ K A : Type} [Field κ] [Field K] [Algebra κ K] [Algebra.IsIntegral κ K] [CommRing A]
    [Algebra κ A] (s : Finset (A ⊗[κ] K)) :
    ∃ L : IntermediateField κ K, FiniteDimensional κ L ∧ ∀ x ∈ s, x ∈ (incMap κ K A L).range := by
  have one : ∀ x : A ⊗[κ] K, ∃ L : IntermediateField κ K, FiniteDimensional κ L ∧ x ∈ (incMap κ K A L).range := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨⊥, inferInstance, zero_mem _⟩
    | tmul a k =>
      refine ⟨IntermediateField.adjoin κ {k},
        IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral k), ?_⟩
      exact ⟨a ⊗ₜ ⟨k, IntermediateField.mem_adjoin_simple_self κ k⟩, by simp⟩
    | add x y hx hy =>
      obtain ⟨L₁, h₁, hx⟩ := hx
      obtain ⟨L₂, h₂, hy⟩ := hy
      exact ⟨L₁ ⊔ L₂, inferInstance, add_mem (incMap_mono le_sup_left hx) (incMap_mono le_sup_right hy)⟩
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, inferInstance, by simp⟩
  | insert a s _ ih =>
    obtain ⟨L₁, h₁, ha⟩ := one a
    obtain ⟨L₂, h₂, hs⟩ := ih
    refine ⟨L₁ ⊔ L₂, inferInstance, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact incMap_mono le_sup_left ha
    · exact incMap_mono le_sup_right (hs x hx)

theorem SHInsepHens_of (hL : SHInsepLoc) : SHInsepHens := by
  intro κ K A _ _ _ _ _ _ hA _
  have hA' := hA
  obtain ⟨_, -⟩ := hA'
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ h1 h2
  classical
  obtain ⟨L, hFD, hs⟩ := exists_fd_range (A := A) (insert a₀ (f.support.image f.coeff))
  have : IsLocalRing (A ⊗[κ] L) := hL κ L A hA
  have : HenselianLocalRing (A ⊗[κ] L) := GlobalTheory.henselianLocalRing_of_finite A _
  have hint : (incMap κ K A L).toRingHom.IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap A (A ⊗[κ] L)) _ ?_
    have e : (incMap κ K A L).toRingHom.comp (algebraMap A (A ⊗[κ] L)) = algebraMap A (A ⊗[κ] K) :=
      (incMap κ K A L).comp_algebraMap
    rw [e]
    exact fun x => Algebra.IsIntegral.isIntegral (R := A) x
  have hc : (maximalIdeal (A ⊗[κ] K)).comap (incMap κ K A L).toRingHom = maximalIdeal (A ⊗[κ] L) :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hint _)
  refine hens_root_of_sub (incMap κ K A L).toRingHom hc f hf a₀ ?_ ?_ h1 h2
  · intro n
    by_cases hn : n ∈ f.support
    · exact (AlgHom.mem_range _).1 (hs _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn)))
    · exact ⟨0, by simp [Polynomial.notMem_support_iff.1 hn]⟩
  · exact (AlgHom.mem_range _).1 (hs _ (Finset.mem_insert_self _ _))

end LateralTheory.KummerTheory
end
end
