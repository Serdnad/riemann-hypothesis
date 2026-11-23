module

public import Development.EtaleCohomology.KummerTheory.InjSlice
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ContCut

def Lim {J : Type} [SmallCategory J] {K : Type 1} [Category.{0} K] (G : K ⥤ AddCommGrpCat.{1}) {D : J ⥤ K} (c : Cocone D) :
    Prop :=
  (∀ x : G.obj c.pt, ∃ (j : J) (y : G.obj (D.obj j)), (G.map (c.ι.app j)).hom y = x) ∧
  ∀ (j : J) (y : G.obj (D.obj j)), (G.map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (G.map (D.map f)).hom y = 0

structure MVSeq {K : Type 1} [Category.{0} K] (X U V W : ℤ → K ⥤ AddCommGrpCat.{1}) where
  f : ∀ n, X n ⟶ U n
  g : ∀ n, X n ⟶ V n
  a : ∀ n, U n ⟶ W n
  b : ∀ n, V n ⟶ W n
  δ : ∀ n, W n ⟶ X (n + 1)
  comm : ∀ n, f n ≫ a n = g n ≫ b n
  exUV : ∀ n k u v, ((a n).app k).hom u = ((b n).app k).hom v → ∃ x, ((f n).app k).hom x = u ∧ ((g n).app k).hom x = v
  exX : ∀ n k x, ((f (n + 1)).app k).hom x = 0 → ((g (n + 1)).app k).hom x = 0 → ∃ w, ((δ n).app k).hom w = x
  exW : ∀ n k w, ((δ n).app k).hom w = 0 ↔ ∃ u v, w = ((a n).app k).hom u - ((b n).app k).hom v

def IsMV {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X) : Prop :=
  IsOpenImmersion f ∧ IsOpenImmersion g ∧ IsPullback a b f g ∧ ∀ x : X, x ∈ Set.range f ∨ x ∈ Set.range g

def Hf {R : Type} [CommRing R] (F : Shv R) (n : ℤ) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} where
  obj X := AddCommGrpCat.of (H R (sch.obj X.unop) F n)
  map f := AddCommGrpCat.ofHom (pull R (sch.map f.unop) F n)
  map_id X := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => by
    change pull R (sch.map (𝟙 X.unop)) F n x = x
    rw [CategoryTheory.Functor.map_id, pull_id])
  map_comp f g := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => by
    change pull R (sch.map (g.unop ≫ f.unop)) F n x = pull R _ F n (pull R _ F n x)
    rw [Functor.map_comp, pull_comp])

theorem bcMap_comp {X : Scheme.{0}} {R A B C : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B) (k : R ⟶ C)
    (h : A ⟶ B) (h' : B ⟶ C) (e : f ≫ h = g) (e' : g ≫ h' = k) (e'' : f ≫ h ≫ h' = k) :
    bcMap p f k (h ≫ h') e'' = bcMap p g k h' e' ≫ bcMap p f g h e := by
  apply pullback.hom_ext <;> simp [bcMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

def bc {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R) : Under R ⥤ Scheme.{0}ᵒᵖ where
  obj A := op (pullback p (Spec.map A.hom))
  map {A B} h := (bcMap p A.hom B.hom h.right (Under.w h)).op
  map_id A := Quiver.Hom.unop_inj (by apply pullback.hom_ext <;> simp [bcMap])
  map_comp h h' := Quiver.Hom.unop_inj (bcMap_comp p _ _ _ h.right h'.right (Under.w h) (Under.w h') (Under.w (h ≫ h')))

def bcHom {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R) (e : f ≫ p = r)
    (s : R ⟶ A) : pullback r (Spec.map s) ⟶ pullback p (Spec.map s) :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by rw [Category.comp_id, e]) (by simp)

theorem bcHom_bcMap {U X : Scheme.{0}} {R A B : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) (t : R ⟶ B) (h : A ⟶ B) (e' : s ≫ h = t) :
    bcHom f p r e t ≫ bcMap p s t h e' = bcMap r s t h e' ≫ bcHom f p r e s := by
  apply pullback.hom_ext <;> simp [bcMap, bcHom, pullback.map, pullback.lift_fst, pullback.lift_snd,
    pullback.lift_snd_assoc, pullback.lift_fst_assoc]

def bcNat {U X : Scheme.{0}} {R : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R) (e : f ≫ p = r) :
    bc p ⟶ bc r where
  app A := (bcHom f p r e A.hom).op
  naturality _ _ h := Quiver.Hom.unop_inj (bcHom_bcMap f p r e _ _ h.right (Under.w h))

def Conn {R : Type} [CommRing R] (F : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (f : U ⟶ X) (g : V ⟶ X) (n : ℤ)
    (w : H R (sch.obj W) F n) (x : H R (sch.obj X) F (n + 1)) : Prop :=
  ∃ (s : Sec ((res R F).X n) U) (z : Sec ((res R F).X (n + 1)) X), IsCls w (Sec.res a s) ∧ IsCls x z ∧
    Sec.res f z = Sec.map ((res R F).d n (n + 1)) s ∧ Sec.res g z = 0

def Five : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] {K : Type 1} [Category.{0} K]
  (X U V W : ℤ → K ⥤ AddCommGrpCat.{1}), Nonempty (MVSeq X U V W) → ∀ {D : J ⥤ K} (c : Cocone D),
  (∀ n, Lim (U n) c) → (∀ n, Lim (V n) c) → (∀ n, Lim (W n) c) → ∀ n, Lim (X n) c

def Ind : Prop := ∀ (R : CommRingCat.{0}) (P : ∀ X : Scheme.{0}, (X ⟶ Spec R) → Prop),
  (∀ (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec R), P X p) →
  (∀ {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X) (p : X ⟶ Spec R), IsMV a b f g →
    P U (f ≫ p) → P V (g ≫ p) → P W (a ≫ f ≫ p) → P X p) →
  ∀ (X : Scheme.{0}) (p : X ⟶ Spec R) [QuasiCompact p] [IsSeparated p], P X p

def BC : Prop := ∀ {R A : CommRingCat.{0}} (s : R ⟶ A) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (p : X ⟶ Spec R) (pU : U ⟶ Spec R) (pV : V ⟶ Spec R) (pW : W ⟶ Spec R) (ea : a ≫ pU = pW) (eb : b ≫ pV = pW)
  (ef : f ≫ p = pU) (eg : g ≫ p = pV), IsMV a b f g →
  IsMV (bcHom a pU pW ea s) (bcHom b pV pW eb s) (bcHom f p pU ef s) (bcHom g p pV eg s)

def Glue : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X)
  (g : V ⟶ X), IsMV a b f g →
  (∀ z : Sec G X, Sec.res f z = 0 → Sec.res g z = 0 → z = 0) ∧
  ∀ (s : Sec G U) (t : Sec G V), Sec.res a s = Sec.res b t → ∃ z : Sec G X, Sec.res f z = s ∧ Sec.res g z = t

def Flasque : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) [Injective G] {W U : Scheme.{0}} (a : W ⟶ U) [Mono a],
  Function.Surjective fun s : Sec G U => Sec.res a s

def Delta : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X)
  (g : V ⟶ X), IsMV a b f g → ∀ n : ℤ, ∃ δ : H R (sch.obj W) F n →+ H R (sch.obj X) F (n + 1),
    ∀ w x, Conn F a f g n w x ↔ δ w = x

def Exact : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X)
  (g : V ⟶ X), IsMV a b f g → ∀ n : ℤ,
  (∀ u v, pull R (sch.map a) F n u = pull R (sch.map b) F n v →
    ∃ x, pull R (sch.map f) F n x = u ∧ pull R (sch.map g) F n x = v) ∧
  (∀ x, pull R (sch.map f) F (n + 1) x = 0 → pull R (sch.map g) F (n + 1) x = 0 → ∃ w, Conn F a f g n w x) ∧
  ∀ w, Conn F a f g n w 0 ↔ ∃ u v, w = pull R (sch.map a) F n u - pull R (sch.map b) F n v

def MVnat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K : Type 1} [Category.{0} K] (X U V W : K ⥤ Scheme.{0}ᵒᵖ)
  (f : X ⟶ U) (g : X ⟶ V) (a : U ⟶ W) (b : V ⟶ W),
  (∀ k, IsMV (a.app k).unop (b.app k).unop (f.app k).unop (g.app k).unop) →
  Nonempty (MVSeq (fun n => X ⋙ Hf F n) (fun n => U ⋙ Hf F n) (fun n => V ⋙ Hf F n) (fun n => W ⋙ Hf F n))

def AffRing : Prop := ∀ {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (p : X ⟶ Spec R),
  ∃ T : Under R ⥤ CommRingCat.{0}, Nonempty (bc p ≅ T ⋙ Scheme.Spec.rightOp) ∧ (∀ A, Nonempty (R ⟶ T.obj A)) ∧
    ∀ {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ Under R} (c : Cocone D),
      IsColimit ((Under.forget R).mapCocone c) → Nonempty (IsColimit (T.mapCocone c))

def Aff : Prop := B1 → ∀ (q : ℕ) {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (p : X ⟶ Spec R), IsUnit (q : R) →
  ∀ {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ Under R} (c : Cocone D),
    IsColimit ((Under.forget R).mapCocone c) → ∀ n i : ℤ, Lim (bc p ⋙ Hf (tw q i) n) c

theorem goal_of (h5 : Five) (hI : Ind) (hB : BC) (hM : MVnat) (hA : Aff) : Cont := by
  intro _ b1 q _ X R p _ _ hq J _ _ D c hc u hu v hv n i
  let D' : J ⥤ Under R :=
    { obj := fun j => Under.mk (u j)
      map := fun f => Under.homMk (D.map f) (hu f)
      map_id := fun j => by ext1; exact D.map_id j
      map_comp := fun f g => by ext1; exact D.map_comp f g }
  let c' : Cocone D' :=
    { pt := Under.mk v
      ι := { app := fun j => Under.homMk (c.ι.app j) (hv j)
             naturality := fun j k f => by ext1; exact c.ι.naturality f } }
  have hc' : IsColimit ((Under.forget R).mapCocone c') := hc
  have key : ∀ n, Lim (bc p ⋙ Hf (tw q i) n) c' := by
    refine hI R (fun X p => ∀ n, Lim (bc p ⋙ Hf (tw q i) n) c') (fun X _ p n => hA b1 q p hq c' hc' n i) ?_ X p
    intro W U V X a b f g p h hU hV hW
    have eb : b ≫ g ≫ p = a ≫ f ≫ p := by rw [← Category.assoc, ← h.2.2.1.w, Category.assoc]
    exact h5 _ _ _ _ (hM _ (tw q i) _ _ _ _ (bcNat f p _ rfl) (bcNat g p _ rfl) (bcNat a _ _ rfl) (bcNat b _ _ eb)
      fun k => hB k.hom a b f g p _ _ _ rfl eb rfl rfl h) c' hU hV hW
  exact key n

end LateralTheory.KummerTheory.ContCut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def EvLin : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
  (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
    ev (R := R) (α + β) p s h U x = ev (R := R) α p s h U x + ev (R := R) β p s h U x ∧ ev (R := R) (-α) p s h U x = -ev (R := R) α p s h U x) ∧
  (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
    Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x)) ∧
  ∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
    ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev (R := R) α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x)

def DictExist : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ) (a : Sec (I.X n) X),
  Sec.map (I.d n (n + 1)) a = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
    ev (R := R) α.1 0 n (by simp) X (𝟙 X) = a ∧
    ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev (R := R) α.1 (p + 1) s h U y = 0

def DictNormal : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ)
  (α : Cocycle ((chains R).obj (sch.obj X)) I n), ∃ α' : Cocycle ((chains R).obj (sch.obj X)) I n,
    CohomologyClass.mk α' = CohomologyClass.mk α ∧
    ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev (R := R) α'.1 (p + 1) s h U y = 0

def DictZero : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ)
  (α : Cocycle ((chains R).obj (sch.obj X)) I n),
  (∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev (R := R) α.1 (p + 1) s h U y = 0) →
  Sec.map (I.d n (n + 1)) (ev (R := R) α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
    (CohomologyClass.mk α = 0 ↔ ∃ b : Sec (I.X (n - 1)) X, Sec.map (I.d (n - 1) n) b = ev (R := R) α.1 0 n (by simp) X (𝟙 X))

theorem Dict_of (hL : EvLin) (hE : DictExist) (hN : DictNormal) (hZ : DictZero) : Dict := by
  intro R _ I X n
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨α, h0, h1⟩ := hE R I X n a ha
    exact ⟨_, α, rfl, h0, h1⟩
  · intro x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨α', e, h1⟩ := hN R I X n α
    exact ⟨_, α', e, rfl, h1⟩
  · rintro x a ⟨α, rfl, h0, h1⟩
    subst h0
    exact hZ R I X n α h1
  · rintro x x' a a' ⟨α, rfl, h0, h1⟩ ⟨α', rfl, h0', h1'⟩
    refine ⟨⟨α + α', CohomologyClass.mk_add _ _ |>.symm, ?_, ?_⟩, ⟨-α, ?_, ?_, ?_⟩⟩
    · rw [← h0, ← h0']; exact ((hL R).1 α.1 α'.1 0 n _ X (𝟙 X)).1
    · intro p s h U y
      rw [show ((α + α' : Cocycle _ _ n) : Cochain _ _ n) = α.1 + α'.1 from rfl, ((hL R).1 _ _ _ _ _ _ _).1, h1, h1', add_zero]
    · rw [← CohomologyClass.mk_neg]
    · rw [← h0]; exact ((hL R).1 α.1 α.1 0 n _ X (𝟙 X)).2
    · intro p s h U y
      rw [show ((-α : Cocycle _ _ n) : Cochain _ _ n) = -α.1 from rfl, ((hL R).1 α.1 α.1 _ _ _ _ _).2, h1, neg_zero]
  · rintro Y f x a ⟨α, rfl, h0, h1⟩
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_, ?_⟩
    · change ev (R := R) ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) 0 n _ Y (𝟙 Y) = _
      refine ((hL R).2.2 (sch.map f) α.1 0 n _ Y (𝟙 Y)).trans ?_
      rw [← h0]
      exact (((hL R).2.1 α.1 0 n _ Y X f (𝟙 X)).trans rfl).symm
    · intro p s h U y
      change ev (R := R) ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) (p + 1) s h U y = 0
      exact ((hL R).2.2 (sch.map f) α.1 _ _ _ _ _).trans (h1 _ _ _ _ _)

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem IsoUpTo.comb_mono {q : ℕ} {E : Spc} {n i : ℤ} {r : ℕ} {c : Fin r → Ht q E n i} {N N' : ℕ} (hd : N ∣ N')
    (h : IsoUpTo N (comb q c)) : IsoUpTo N' (comb q c) := by
  obtain ⟨m, rfl⟩ := hd
  refine ⟨fun a ha => by rw [mul_comm, mul_smul, h.1 a ha, smul_zero], fun b => ?_⟩
  obtain ⟨a, ha⟩ := h.2 (m • b)
  exact ⟨a, by rw [ha, mul_smul]⟩

theorem inv_of_field (l : ℕ) (k : Type) [Field k] (hl : IsUnit (l : k)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) : Inv l (sch.obj X) := by
  intro U ⟨x⟩
  have h := hl.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ((show U ⟶ X from x) ≫ p).appTop).hom
  rwa [map_natCast] at h

theorem goal_of (hLH : LH) (hInv : SHInv) (hSt : Stalk) (hB : Bock) (hAd : AdicDeg) (hL : Limit) : GOAL := by
  intro a2 a6n a6r a7 a8 a9 a10 a11 b1 b2 b3 e2 e3 e4 l _ k _ _ hl X Y pX pY _ _ _ n i
  have hne : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hu : ∀ j : ℕ, IsUnit ((l ^ j : ℕ) : k) := fun j => by rw [Nat.cast_pow]; exact hl.pow j
  have hA := hAd a11 l (sch.obj X) i (fun b => hB a7 a8 a10 a11 l b _ i (inv_of_field l k hl pX))
    (fun j m => e4 (l ^ j) k (hu j) pX m i)
  choose r c N hN hQ hI using hA
  obtain ⟨e, he⟩ := hLH a2 a6n b1
  let M : ℕ := n.toNat + 1
  let N' : ℕ := ∏ a ∈ Finset.range (M + 1), N (a : ℕ)
  have hN' : 0 < N' := Finset.prod_pos fun a _ => hN _
  refine hL a9 a11 l pX pY n i M (N' ^ e M) (fun a => r a) (fun a => c a) (by omega) (pow_pos hN' _) (fun a _ => hQ _)
    (fun j m => e4 (l ^ j) k (hu j) pY m 0) fun j => ?_
  refine he (l ^ j) pX (hu j) i _ _ M N' (fun A s hA m hm => ?_) pY n (by omega)
  exact hSt a6n a6r a9 b2 (l ^ j) pX A s hA (hu j) i _ _ M N' (hInv a9 b2 b3 e2 e3 (l ^ j) k (hu j) pX A s hA i)
    (fun a ha => (hI a j).comb_mono (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega)))) m hm

end LateralTheory.KummerTheory

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

def LimExtHl : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ),
  ∃ e : Hl l (sch.obj X) a i →ₗ[ℤ_[l]] Hl l (sch.obj Y) (n - a) 0 →ₗ[ℤ_[l]] Hl l (sch.obj (pullback pX pY)) n i,
    ∀ x y k, lev l (e x y) k = ext (l ^ k) pX pY a n i (lev l x k) (lev l y k)

def LimLH : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M N : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i),
  (∀ (k : ℕ) (m : ℤ), Finite (Ht (l ^ k) (sch.obj Y) m 0)) →
  (∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n)) →
  ∃ Φ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
      Hl l (sch.obj (pullback pX pY)) n i,
    (∀ y k, lev l (Φ y) k = lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k)) ∧
    IsoUpTo N Φ

def LimAssemble : Prop := A9 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M N : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i), n ≤ M → 0 < N → (∀ a ≤ M, QBasis l (c a)) →
  ∀ (e : ∀ a : ℤ, Hl l (sch.obj X) a i →ₗ[ℤ_[l]] Hl l (sch.obj Y) (n - a) 0 →ₗ[ℤ_[l]] Hl l (sch.obj (pullback pX pY)) n i)
    (Φ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
      Hl l (sch.obj (pullback pX pY)) n i),
  (∀ y, Φ y = ∑ a : Fin (M + 1), ∑ s : Fin (r a), e ((a : ℕ) : ℤ) (c a s) (y a s)) → IsoUpTo N Φ →
  ∃ κ : (⨁ a : ℤ, HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) ≃ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i,
    ∀ (a : ℤ) (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0),
      κ (DirectSum.lof ℚ_[l] ℤ (fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) a
        (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y

theorem Limit_of (h1 : LimExtHl) (h2 : LimLH) (h3 : LimAssemble) : Limit := by
  intro hA9 hA11 l _ X Y S pX pY n i M N r c hnM hN hB hfin hiso
  choose e he using fun a : ℤ => h1 hA11 l pX pY a n i
  obtain ⟨Φ, hΦ, hΦN⟩ := h2 hA11 l pX pY n i M N r c hfin hiso
  have key : ∀ y, Φ y = ∑ a : Fin (M + 1), ∑ s : Fin (r a), e ((a : ℕ) : ℤ) (c a s) (y a s) := by
    intro y
    apply Subtype.ext
    funext k
    change lev l (Φ y) k = _
    rw [hΦ y k, Submodule.coe_sum, Finset.sum_apply]
    unfold lh
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact (he _ _ _ k).symm
  obtain ⟨κ, hκ⟩ := h3 hA9 l pX pY n i M N r c hnM hN hB e Φ key hΦN
  exact ⟨κ, fun a x y => ⟨e a x y, fun k => he a x y k, hκ a x y⟩⟩

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open scoped TensorProduct
open GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def SHInsepLoc : Prop := ∀ (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A], SH A → IsLocalRing (A ⊗[κ] K)

def SHInsepHens : Prop := ∀ (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A], SH A → ∀ [IsLocalRing (A ⊗[κ] K)], HenselianLocalRing (A ⊗[κ] K)

def SHInsepRes : Prop := ∀ (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A], SH A → ∀ [IsLocalRing (A ⊗[κ] K)], IsSepClosed (IsLocalRing.ResidueField (A ⊗[κ] K))

theorem SHInsep_of (hL : SHInsepLoc) (hH : SHInsepHens) (hR : SHInsepRes) : SHInsep := by
  intro κ K A _ _ _ _ _ _ hA
  have := hL κ K A hA
  exact ⟨hH κ K A hA, hR κ K A hA⟩

end LateralTheory.KummerTheory
end
end

section

open CategoryTheory Limits

namespace LateralTheory.KummerTheory.GhostPf

variable {A : Type*} [Category A] [Abelian A]

theorem cyc (C : CochainComplex A ℤ) (N : ℕ) {j k l : ℤ} (hjk : j + 1 = k) (hkl : k + 1 = l)
    (hH : N • 𝟙 (C.homology k) = 0) {I : A} (φ : C.X k ⟶ I) (hφ : C.d j k ≫ φ = 0)
    {P : A} (f : P ⟶ C.X k) (hf : f ≫ C.d k l = 0) : f ≫ (N • φ) = 0 := by
  rw [← C.liftCycles_i f l ((ComplexShape.up ℤ).next_eq' hkl) hf,
    ← C.p_descOpcycles φ j ((ComplexShape.up ℤ).prev_eq' hjk) hφ]
  have e : C.iCycles k ≫ (N • (C.pOpcycles k ≫ C.descOpcycles φ j ((ComplexShape.up ℤ).prev_eq' hjk) hφ)) =
      C.homologyπ k ≫ (N • 𝟙 (C.homology k)) ≫ C.homologyι k ≫
        C.descOpcycles φ j ((ComplexShape.up ℤ).prev_eq' hjk) hφ := by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp]
    rw [← Category.assoc (C.iCycles k), ← C.homology_π_ι, Category.assoc]
  rw [Category.assoc, e, hH]
  simp

theorem extd (C : CochainComplex A ℤ) (N : ℕ) {j k l : ℤ} (hjk : j + 1 = k) (hkl : k + 1 = l)
    (hH : N • 𝟙 (C.homology k) = 0) {I : A} [Injective I] (φ : C.X k ⟶ I) (hφ : C.d j k ≫ φ = 0) :
    ∃ c : C.X l ⟶ I, C.d k l ≫ c = N • φ := by
  have hk : kernel.ι (factorThruImage (C.d k l)) ≫ (N • φ) = 0 := by
    apply cyc C N hjk hkl hH φ hφ
    calc kernel.ι (factorThruImage (C.d k l)) ≫ C.d k l
        = (kernel.ι (factorThruImage (C.d k l)) ≫ factorThruImage (C.d k l)) ≫ image.ι (C.d k l) := by
          rw [Category.assoc, image.fac]
      _ = 0 := by rw [kernel.condition, zero_comp]
  refine ⟨Injective.factorThru (Abelian.epiDesc _ _ hk) (image.ι (C.d k l)), ?_⟩
  calc C.d k l ≫ _ = factorThruImage (C.d k l) ≫ image.ι (C.d k l) ≫
        Injective.factorThru (Abelian.epiDesc _ _ hk) (image.ι (C.d k l)) := by
          rw [← Category.assoc, image.fac]
    _ = N • φ := by rw [Injective.comp_factorThru, Abelian.comp_epiDesc]

theorem step (C : CochainComplex A ℤ) (N M : ℕ) {i j k l : ℤ} (_hij : i + 1 = j) (hjk : j + 1 = k)
    (hkl : k + 1 = l) (hH : N • 𝟙 (C.homology k) = 0) [Injective (C.X k)]
    (a : C.X j ⟶ C.X i) (b : C.X k ⟶ C.X j) (hab : a ≫ C.d i j + C.d j k ≫ b = M • 𝟙 (C.X j)) :
    ∃ c : C.X l ⟶ C.X k, (N • b) ≫ C.d j k + C.d k l ≫ c = (N * M) • 𝟙 (C.X k) := by
  have hdb : C.d j k ≫ b = M • 𝟙 (C.X j) - a ≫ C.d i j := by rw [← hab]; abel
  have hφ : C.d j k ≫ (M • 𝟙 (C.X k) - b ≫ C.d j k) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hdb, Preadditive.sub_comp, Category.assoc,
      HomologicalComplex.d_comp_d]
    simp
  obtain ⟨c, hc⟩ := extd C N hjk hkl hH _ hφ
  refine ⟨c, ?_⟩
  rw [hc, Preadditive.nsmul_comp, smul_sub, mul_smul]
  abel

theorem homot (C : CochainComplex A ℤ) [C.IsStrictlyGE (-1)] (hI : ∀ j, Injective (C.X j)) (N m : ℕ)
    (hH : ∀ j : ℤ, j < m → N • 𝟙 (C.homology j) = 0) :
    ∀ n : ℕ, ∀ i j k : ℤ, i + 1 = j → j + 1 = k → j = (n : ℤ) - 1 → j < m →
      ∃ a : C.X j ⟶ C.X i, ∃ b : C.X k ⟶ C.X j, a ≫ C.d i j + C.d j k ≫ b = N ^ (n + 1) • 𝟙 (C.X j) := by
  intro n
  induction n with
  | zero =>
    intro i j k hij hjk hj hjm
    have hj' : j = -1 := by simpa using hj
    subst hj'
    have := hI (-1)
    have hz : C.d i (-1) ≫ 𝟙 (C.X (-1)) = 0 :=
      (C.isZero_of_isStrictlyGE (-1) i (by omega)).eq_of_src _ _
    obtain ⟨c, hc⟩ := extd C N hij hjk (hH _ hjm) (𝟙 _) hz
    exact ⟨0, c, by simp [hc]⟩
  | succ n ih =>
    intro i j k hij hjk hj hjm
    subst hij
    obtain ⟨a, b, hab⟩ := ih (i - 1) i (i + 1) (by ring) rfl (by push_cast at hj; omega) (by omega)
    have := hI (i + 1)
    obtain ⟨c, hc⟩ := step C N (N ^ (n + 1)) (by ring : i - 1 + 1 = i) rfl hjk (hH _ hjm) a b hab
    exact ⟨N • b, c, by rw [hc, ← pow_succ']⟩

theorem Ghost_of : LateralTheory.KummerTheory.Ghost := by
  intro A _ _ _ C _ hI N m hH j hj P f hf
  by_cases hlow : j < -1
  · refine ⟨0, ?_⟩
    exact (C.isZero_of_isStrictlyGE (-1) j hlow).eq_of_tgt _ _
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = (n : ℤ) - 1 := ⟨(j + 1).toNat, by omega⟩
    obtain ⟨a, b, hab⟩ := homot C hI N m hH n (j - 1) j (j + 1) (by ring) rfl hn hj
    have hnm : n + 1 ≤ m + 1 := by omega
    refine ⟨N ^ (m + 1 - (n + 1)) • (f ≫ a), ?_⟩
    have e : f ≫ a ≫ C.d (j - 1) j = N ^ (n + 1) • f := by
      have := congrArg (f ≫ ·) hab
      simp only [Preadditive.comp_add, Preadditive.comp_nsmul, Category.comp_id] at this
      rw [← Category.assoc f (C.d j (j + 1)) b, hf, zero_comp, add_zero] at this
      exact this
    rw [Preadditive.nsmul_comp, Category.assoc, e, smul_smul, ← pow_add, Nat.sub_add_cancel hnm]

end LateralTheory.KummerTheory.GhostPf
end
