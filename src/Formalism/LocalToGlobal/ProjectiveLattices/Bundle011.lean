module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace Formalism.L2.Pj.GSR

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Corr

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : IsGrpPullback G' G f F) {k : Type} [CommRing k] (tk : Spec (CommRingCat.of k) ⟶ S') (g : Spec (CommRingCat.of k) ⟶ S)
  (hg : tk ≫ f = g)

abbrev viaT (X : Over (Spec (CommRingCat.of k))) : Over S' := Over.mk (X.hom ≫ tk)

def Rel {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) : Prop :=
  w.left ≫ F = v.left ≫ pullback.fst G.hom g

def liftT {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) : viaT tk Y ⟶ viaT tk X :=
  Over.homMk φ.left (by
    show φ.left ≫ X.hom ≫ tk = Y.hom ≫ tk
    rw [← Category.assoc, Over.w φ])

variable {tk g}

include hc in
theorem rel_uniq_w {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v) : w = w' := by
  have e : w.left ≫ F = w'.left ≫ F :=
    (h : w.left ≫ F = _).trans (h' : w'.left ≫ F = _).symm
  exact Over.OverMorphism.ext (hc.1.hom_ext e (by rw [Over.w w, Over.w w']))

theorem rel_uniq_v {X : Over (Spec (CommRingCat.of k))} {w : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w v') : v = v' := by
  have e : v.left ≫ pullback.fst G.hom g = v'.left ≫ pullback.fst G.hom g :=
    (h : _ = v.left ≫ pullback.fst G.hom g).symm.trans (h' : _ = v'.left ≫ pullback.fst G.hom g)
  refine Over.OverMorphism.ext (pullback.hom_ext e ?_)
  have hv : v.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v
  have hv' : v'.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v'
  rw [hv, hv']


include hc hg in
theorem rel_exists_v {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') :
    ∃ v : X ⟶ (Over.pullback g).obj G, Rel (F := F) tk g w v := by
  have hw : w.left ≫ G'.hom = X.hom ≫ tk := Over.w w
  have cond : (w.left ≫ F) ≫ G.hom = X.hom ≫ g := by
    rw [Category.assoc, hc.1.w, reassoc_of% hw, hg]
  exact ⟨Over.homMk (pullback.lift _ _ cond) (pullback.lift_snd _ _ cond), (pullback.lift_fst _ _ cond).symm⟩

def iota2 (hg : tk ≫ f = g) (X : Over (Spec (CommRingCat.of k))) :
    Over.mk (X.hom ≫ g) ⟶ Over.mk ((viaT tk X).hom ≫ f) :=
  Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (X.hom ≫ tk) ≫ f = X.hom ≫ g
    rw [Category.id_comp, Category.assoc, hg])

theorem rel_iff {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) :
    Rel (F := F) tk g w v ↔
      pushPt (isGrpPullback_pullback G g).1.w v = iota2 hg X ≫ pushPt hc.1.w w := by
  constructor
  · intro h
    ext
    simp only [pushPt, iota2, Over.comp_left, Over.homMk_left, Category.id_comp]
    exact (h : w.left ≫ F = _).symm
  · intro h
    have e : (pushPt (isGrpPullback_pullback G g).1.w v).left = (iota2 hg X ≫ pushPt hc.1.w w).left := by
      rw [h]
    simp only [pushPt, iota2, Over.comp_left, Over.homMk_left, Category.id_comp] at e
    exact e.symm

include hc hg in
theorem rel_mul {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v') : Rel (F := F) tk g (w * w') (v * v') := by
  rw [Formalism.L2.Pj.GSR.rel_iff hc hg] at h h' ⊢
  have e1 := map_mul (pushHom (isGrpPullback_pullback G g) X) v v'
  have e2 := map_mul ((preHom (iota2 hg X)).comp (pushHom hc (viaT tk X))) w w'
  exact e1.trans ((congrArg₂ (· * ·) h h').trans e2.symm)

include hc hg in
theorem rel_one {X : Over (Spec (CommRingCat.of k))} : Rel (F := F) tk g (1 : viaT tk X ⟶ G') (1 : X ⟶ (Over.pullback g).obj G) := by
  rw [Formalism.L2.Pj.GSR.rel_iff hc hg]
  exact (map_one (pushHom (isGrpPullback_pullback G g) X)).trans
    (map_one ((preHom (iota2 hg X)).comp (pushHom hc (viaT tk X)))).symm

include hc hg in
theorem rel_prod : ∀ {N : ℕ} {X : Over (Spec (CommRingCat.of k))} (u : Fin N → (viaT tk X ⟶ G'))
    (u' : Fin N → (X ⟶ (Over.pullback g).obj G)), (∀ i, Rel (F := F) tk g (u i) (u' i)) →
    Rel (F := F) tk g (List.ofFn u).prod (List.ofFn u').prod
  | 0, X, u, u', _ => by simpa using rel_one hc hg (X := X)
  | N + 1, X, u, u', h => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    exact rel_mul hc hg (h 0) (rel_prod (fun i => u i.succ) (fun i => u' i.succ) fun i => h i.succ)

theorem rel_pre {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) {w : viaT tk X ⟶ G'}
    {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) : Rel (F := F) tk g (liftT tk φ ≫ w) (φ ≫ v) := by
  show (φ.left ≫ w.left) ≫ F = (φ.left ≫ v.left) ≫ pullback.fst G.hom g
  rw [Category.assoc, Category.assoc, (h : w.left ≫ F = _)]

end Corr

section Count

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f F) {k : Type} [CommRing k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)




end Count

end Formalism.L2.Pj.GSR
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Dual

variable {S T : Type} [CommRing S] [CommRing T]

def dualMap (φ : S →+* T) : DualNumber S →+* DualNumber T where
  toFun x := TrivSqZeroExt.inl (φ x.fst) + TrivSqZeroExt.inr (φ x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

def toΓ (S : Type) [CommRing S] : S →+* Γ(Sp S, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom

end Dual

variable (Xo : Moduli Dw l) (c : Coeff l)

def sOf (S : Type) [CommRing S] [Algebra c.F S] : Sp S ⟶ Sp (KA l) :=
  spMap ((algebraMap c.F S).comp (IntermediateField.inclusion c.le).toRingHom)

variable {Xo c}

abbrev tEps {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Over Xo.X :=
  Over.mk (spMap (algebraMap S (DualNumber S)) ≫ x)

def IsTanAt {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) : Prop :=
  v ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x ∧
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v = (1 : Over.mk x ⟶ Xo.univ.t.G).left


variable (c) in
def IsEigAt {S : Type} [CommRing S] [Algebra c.F S] (τ : E →+* ℂ)
    (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) : Prop :=
  ∀ a : 𝓞 E, v ≫ (Xo.univ.t.act.act a).left = spMap (epsMul (algebraMap c.F S (embK c τ a))) ≫ v

def IsCombAt {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) : Prop :=
  ∃ u : Fin m → (tEps x ⟶ Xo.univ.t.G), (∀ i, (u i).left = spMap (epsMul (cf i)) ≫ v i) ∧
    ((List.ofFn u).prod).left = w

abbrev Gx {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Scheme.{0} := (Over.mk x ⊗ Xo.univ.t.G).left

abbrev PPx {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : LB (Gx x) :=
  ReciprocityTheory.ChartRestriction.G.Out.LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (Over.mk x)

def scal {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (i : (PPx x).ι) :
    Γ(Gx x, (PPx x).U i) :=
  ReciprocityTheory.ChartRestriction.G.Out.liftFun Xo.univ.t.G ((PPx x).U i) (T := Over.mk x) (toΓ S a)

variable (Xo c)

structure FrPt (S : Type) [CommRing S] [Algebra c.F S] : Type where
  x : Sp S ⟶ Xo.X
  x_over : x ≫ Xo.s = sOf c S
  u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)
  tan : ∀ τ i, IsTanAt x (u τ i)
  eig : ∀ τ i, IsEigAt c τ (u τ i)
  basis : ∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w
  s : LB.Sec (PPx x)
  gen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s.f i

variable {Xo c}

def FrMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) : Prop :=
  z.x = spMap φ.toRingHom ≫ y.x ∧
    (∀ τ i, z.u τ i = spMap (dualMap φ.toRingHom) ≫ y.u τ i) ∧
    ∃ pm : Gx z.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left ≫ spMap φ.toRingHom ∧
      ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z.x).U i ≤ pm ⁻¹ᵁ (PPx y.x).U i), (pm.appLE _ _ h).hom (y.s.f i) = z.s.f i

def FrBor {S : Type} [CommRing S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) : Prop :=
  y'.x = y.x ∧
    (∀ τ i, ∃ cf : Fin (Dw.mult τ) → S, cf i = (t (some ⟨τ, i⟩) : S) ∧ (∀ j, i < j → cf j = 0) ∧
      IsCombAt y.x (y.u τ) cf (y'.u τ i)) ∧
    ∃ pm : Gx y'.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y'.x) Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y'.x) Xo.univ.t.G).left ∧
      ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.x).U i ≤ pm ⁻¹ᵁ (PPx y.x).U i),
        (pm.appLE _ _ h).hom (scal y.x (t none : S) i * y.s.f i) = y'.s.f i

variable (Xo c)

abbrev Rul : Type := Rules (K := c.F) (fun S _ _ => FrPt Xo c S)

set_option maxSynthPendingDepth 1 in
instance (priority := high) rulModule : Module c.F (Rul Xo c) :=
  inferInstance

def sec (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  secW (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (ex Dw a n)

def evR (f : Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : S :=
  evalAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f y

theorem sec_mul (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) {f g : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (hg : g ∈ sec Xo c a' n') : f * g ∈ sec Xo c (a + a') (n + n') := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_⟩
  · intro p q φ y z h
    change f q z * g q z = φ (f p y * g p y)
    rw [hf1 p q φ y z h, hg1 p q φ y z h, map_mul]
  · intro p t y y' h
    change f p y' * g p y' = _ * (f p y * g p y)
    rw [hf2 p t y y' h, hg2 p t y y' h]
    have he : ∀ i, ex Dw (a + a') (n + n') i = ex Dw a n i + ex Dw a' n' i := by
      intro i
      cases i <;> rfl
    try unfold wchar
    rw [show (∏ i, (t i : p.R) ^ ex Dw (a + a') (n + n') i) =
        (∏ i, (t i : p.R) ^ ex Dw a n i) * ∏ i, (t i : p.R) ^ ex Dw a' n' i by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [he, pow_add]]
    ring

end Formalism.L2.Pj
end
end
