module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.CohomologicalPurity.InrFold
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Countable
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Category.Grp.EpiMono

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity

namespace UpperTheory.Et.Prd

structure DC where
  A : ℕ → ℤ → Type 1
  [grp : ∀ p s, AddCommGroup (A p s)]
  d : ∀ p s t, A p s →+ A p t
  δ : ∀ p s, A p s →+ A (p + 1) s

attribute [instance] DC.grp

structure DC.Ok (C : DC) : Prop where
  dd : ∀ p s t u x, C.d p t u (C.d p s t x) = 0
  δδ : ∀ p s x, C.δ (p + 1) s (C.δ p s x) = 0
  comm : ∀ p s t x, C.d (p + 1) s t (C.δ p s x) = C.δ p t (C.d p s t x)

abbrev DC.Tot (C : DC) : Type 1 := ∀ p s, C.A p s

def DC.Deg (C : DC) (n : ℤ) (x : C.Tot) : Prop := ∀ (p : ℕ) (s : ℤ), (p : ℤ) + s ≠ n → x p s = 0

def DC.D (C : DC) (n : ℤ) (x : C.Tot) : C.Tot
  | 0, t => C.d 0 (t - 1) t (x 0 (t - 1))
  | p + 1, t => C.d (p + 1) (t - 1) t (x (p + 1) (t - 1)) + (n + 1).negOnePow • C.δ p t (x p t)

abbrev DC.Hom (C C' : DC) : Type 1 := ∀ p s, C.A p s →+ C'.A p s

def DC.Hom.Ok {C C' : DC} (Φ : C.Hom C') : Prop :=
  (∀ p s x, Φ p (s + 1) (C.d p s (s + 1) x) = C'.d p s (s + 1) (Φ p s x)) ∧ ∀ p s x, Φ (p + 1) s (C.δ p s x) = C'.δ p s (Φ p s x)

def DC.Hom.tot {C C' : DC} (Φ : C.Hom C') (x : C.Tot) : C'.Tot := fun p s => Φ p s (x p s)

def DC.Hom.ColEx {C C' : DC} (Φ : C.Hom C') (p : ℕ) : Prop :=
  ∀ (s : ℤ) (a : C.A p (s + 1)) (y : C'.A p s), C.d p (s + 1) (s + 1 + 1) a = 0 → Φ p (s + 1) a = C'.d p s (s + 1) y →
    ∃ (a' : C.A p s) (y' : C'.A p (s - 1)), C.d p s (s + 1) a' = a ∧ y = Φ p s a' + C'.d p (s - 1) s y'

def DC.Hom.TotEx {C C' : DC} (Φ : C.Hom C') : Prop :=
  ∀ (n : ℤ) (a : C.Tot) (y : C'.Tot), C.Deg (n + 1) a → C'.Deg n y → C.D (n + 1) a = 0 → Φ.tot a = C'.D n y →
    ∃ (a' : C.Tot) (y' : C'.Tot), C.Deg n a' ∧ C'.Deg (n - 1) y' ∧ C.D n a' = a ∧ y = Φ.tot a' + C'.D (n - 1) y'

structure Sub (E : Spc) where
  mem : ∀ (p : ℕ) (U : Scheme.{0}), Sx E p U → Prop
  face : ∀ (p : ℕ) (U : Scheme.{0}) (x : Sx E (p + 1) U) (i : Fin (p + 2)), mem (p + 1) U x → mem p U (x.face i)

def Sub.bot (E : Spc) : Sub E := ⟨fun _ _ _ => False, fun _ _ _ _ h => h⟩

def Sub.img {E' E : Spc} (f : E' ⟶ E) : Sub E :=
  ⟨fun p U x => ∃ y : Sx E' p U, y.map f = x, by
    rintro p U _ i ⟨y, rfl⟩
    exact ⟨y.face i, ConcreteCategory.congr_hom
      (NatTrans.congr_app (f.naturality (SimplexCategory.δ i).op) (op U)) y⟩⟩

variable {R : Type} [CommRing R]

def Fam {E : Spc} (Z : Sub E) (p : ℕ) (M : Shv R) : AddSubgroup (∀ U : Scheme.{0}, Sx E p U → Sec M U) where
  carrier := {a | (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ U x, Z.mem p U x → a U x = 0}
  zero_mem' := ⟨fun _ _ _ _ => map_zero _, fun _ _ _ => rfl⟩
  add_mem' {a b} ha hb := ⟨fun V U g x => (map_add _ _ _).trans (congrArg₂ (· + ·) (ha.1 V U g x) (hb.1 V U g x)),
    fun U x h => by rw [Pi.add_apply, Pi.add_apply, ha.2 U x h, hb.2 U x h, add_zero]⟩
  neg_mem' {a} ha := ⟨fun V U g x => (map_neg _ _).trans (congrArg Neg.neg (ha.1 V U g x)),
    fun U x h => by rw [Pi.neg_apply, Pi.neg_apply, ha.2 U x h, neg_zero]⟩

def Fam.map {E : Spc} (Z : Sub E) (p : ℕ) {M N : Shv R} (φ : M ⟶ N) : Fam Z p M →+ Fam Z p N where
  toFun a := ⟨fun U x => Sec.map φ (a.1 U x), fun V U g x => by
      change _ = Sec.map φ (a.1 V (x.res g))
      rw [← a.2.1 V U g x]
      exact (ConcreteCategory.congr_hom (φ.hom.naturality g.op) (a.1 U x)).symm,
    fun U x h => (congrArg (Sec.map φ) (a.2.2 U x h)).trans (map_zero _)⟩
  map_zero' := by ext U x; simp
  map_add' a b := by ext U x; simp

theorem face_res {E : Spc} {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E (p + 1) U) (i : Fin (p + 2)) :
    (x.face i).res g = (x.res g).face i :=
  (ConcreteCategory.congr_hom ((E.δ i).naturality g.op) x).symm

def Fam.δ {E : Spc} (Z : Sub E) (p : ℕ) (M : Shv R) (η : ℤˣ) : Fam Z p M →+ Fam Z (p + 1) M where
  toFun a := ⟨fun U x => η • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • a.1 U (x.face i), fun V U g x => by

      simp only [Sec.res, Units.smul_def, map_zsmul, map_sum]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => congrArg _ ?_)
      rw [← face_res]; exact a.2.1 V U g _,
    fun U x h => by simp [fun i => a.2.2 U _ (Z.face p U x i h)]⟩
  map_zero' := by ext U x; simp
  map_add' a b := by ext U x; simp [Finset.sum_add_distrib]

def famDC {E : Spc} (Z : Sub E) (K : Cx R) (m : ℤ) : DC where
  A p s := Fam Z p (K.X (s + m))
  d p s t := Fam.map Z p (K.d (s + m) (t + m))
  δ p s := Fam.δ Z p _ m.negOnePow

def Comp {E E' : Spc} (j : E ⟶ E') {Z : Sub E} {K : Cx R} {m N : ℤ} (γ : Cochain ((chains R).obj E') K N)
    (x : (famDC Z K m).Tot) : Prop :=
  ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s + m) (U : Scheme.{0}) (z : Sx E p U),
    (show Fam Z p (K.X (s + m)) from x p s).1 U z = ev (R := R) γ p (s + m) h U (z.map j)

def HRel {E : Spc} {K : Cx R} {n : ℤ} (x : (famDC (Sub.bot E) K 0).Tot) (c : CohomologyClass ((chains R).obj E) K n) : Prop :=
  ∃ γ : Cocycle ((chains R).obj E) K n, CohomologyClass.mk γ = c ∧ Comp (𝟙 E) γ.1 x

def SRel {P : Arrow Spc} {K : Cx R} {m N : ℤ} (x : (famDC (Sub.img P.hom) K m).Tot)
    (c : CohomologyClass ((chains R).obj (dbl P)) K N) : Prop :=
  ∃ γ : Cocycle ((chains R).obj (dbl P)) K N, CohomologyClass.mk γ = c ∧ Comp (dbl.inl P) γ.1 x ∧
    ∀ (p : ℕ) (s : ℤ) h (U : Scheme.{0}) (z : Sx P.right p U), ev (R := R) γ.1 p s h U (z.map (dbl.inr P)) = 0

structure TModel (C : DC) (n : ℤ) {H : Type 1} [AddCommGroup H] (rel : C.Tot → H → Prop) : Prop where
  ex : ∀ x, C.Deg n x → C.D n x = 0 → ∃ c, rel x c
  surj : ∀ c, ∃ x, C.Deg n x ∧ C.D n x = 0 ∧ rel x c
  sub : ∀ x c x' c', rel x c → rel x' c' → rel (x - x') (c - c')
  zero : ∀ x c, C.Deg n x → rel x c → (c = 0 ↔ ∃ y, C.Deg (n - 1) y ∧ C.D (n - 1) y = x)

def under {X : Scheme.{0}} {E : Spc} (π : E ⟶ sch.obj X) {p : ℕ} {W : Scheme.{0}} (z : Sx E p W) : W ⟶ X := z.map π

def IsProd {I J K : Cx R} (μ : Pair I J K) {X : Scheme.{0}} {E : Spc} (π : E ⟶ sch.obj X) {m : ℤ} (β : Sec (J.X m) X)
    {Z : Sub E} (Φ : (famDC (Sub.bot E) I 0).Hom (famDC Z K m)) : Prop :=
  ∀ (p : ℕ) (s : ℤ) (a : Fam (Sub.bot E) p (I.X (s + 0))) (W : Scheme.{0}) (z : Sx E p W),
    (show Fam Z p (K.X (s + m)) from Φ p s a).1 W z =
      (m * (p : ℕ)).negOnePow • μ.mul W (s + 0) m (s + m) (by omega) (a.1 W z) (Sec.res (under π z) β)

def IsRep {J : Cx R} {X : Scheme.{0}} (U : X.Opens) {m : ℤ} (β : Sec (J.X m) X)
    (c : CohomologyClass ((chains R).obj (dbl (opn U))) J m) : Prop :=
  Sec.map (J.d m (m + 1)) β = 0 ∧ Sec.res U.ι β = 0 ∧
  ∃ γ : Cocycle ((chains R).obj (dbl (opn U))) J m, CohomologyClass.mk γ = c ∧
    (∀ (W : Scheme.{0}) (x : W ⟶ X),
      ev (R := R) γ.1 0 m (by simp) W (Sx.map (E := sch.obj X) (p := 0) (dbl.inl (opn U)) x) = Sec.res x β) ∧
    (∀ (W : Scheme.{0}) (x : W ⟶ X),
      ev (R := R) γ.1 0 m (by simp) W (Sx.map (E := sch.obj X) (p := 0) (dbl.inr (opn U)) x) = 0) ∧
    ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (z : Sx (dbl (opn U)) (p + 1) W), ev (R := R) γ.1 (p + 1) s h W z = 0

end UpperTheory.Et.Prd

end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH

namespace UpperTheory.Ru.crystallineComparison.Th

variable {C : Type 1} [Category.{0} C]

def zm (F : Coef C) : C ⥤ ModuleCat.{1} ℤ where
  obj A := ModuleCat.of ℤ (F.obj A)
  map φ := ModuleCat.ofHom (F.map φ).hom.toIntLinearMap
  map_id A := by ext x; simp
  map_comp φ ψ := by ext x; simp

def zmMap {F G : Coef C} (α : F ⟶ G) : zm F ⟶ zm G where
  app A := ModuleCat.ofHom (α.app A).hom.toIntLinearMap
  naturality A B φ := by
    ext x
    exact congrArg (fun f => f.hom x) (α.naturality φ)

abbrev TH (P : C ⥤ Type) (F : Coef C) (j : ℕ) : Type 1 := CH.H (elF P (zm F)) j

def tPull {Q P : C ⥤ Type} (u : Q ⟶ P) (F : Coef C) (j : ℕ) : TH P F j →+ TH Q F j :=
  ((elMor u (zm F)).pull j).toAddMonoidHom

def tMap (P : C ⥤ Type) {F G : Coef C} (α : F ⟶ G) (j : ℕ) : TH P F j →+ TH P G j :=
  ((elCoef P (zmMap α)).pull j).toAddMonoidHom

theorem tPull_tMap {Q P : C ⥤ Type} (u : Q ⟶ P) {F G : Coef C} (α : F ⟶ G) (j : ℕ) (x : TH P F j) :
    tPull u G j (tMap P α j x) = tMap Q α j (tPull u F j x) := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (elF P (zm F))) j).1 x
  rfl

theorem ses_app (S : ShortComplex (Coef C)) (h : S.ShortExact) :
    (∀ A, Function.Injective (S.f.app A).hom) ∧ (∀ A, Function.Exact (S.f.app A).hom (S.g.app A).hom) ∧
      ∀ A, Function.Surjective (S.g.app A).hom := by
  have := h.mono_f
  have := h.epi_g
  refine ⟨fun A => ?_, fun A => ?_, fun A => ?_⟩
  · exact (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance A)
  · have := (h.map_of_exact ((evaluation C AddCommGrpCat.{1}).obj A)).exact
    exact (ShortComplex.ab_exact_iff_function_exact _).1 this
  · exact (AddCommGrpCat.epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app _).1 inferInstance A)

theorem les_ex (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) :
    ∃ δ : ∀ n, TH P S.X₃ n →ₗ[ℤ] TH P S.X₁ (n + 1),
      (∀ n (y : (cx (elF P (zm S.X₂))).X n) (x : (cx (elF P (zm S.X₁))).X (n + 1)) hz hx,
        (elCoef P (zmMap S.f)).hom.f (n + 1) x = (cx (elF P (zm S.X₂))).d n y →
          δ n ((cx (elF P (zm S.X₃))).cls ((elCoef P (zmMap S.g)).hom.f n y) hz) = (cx (elF P (zm S.X₁))).cls x hx) ∧
      Function.Injective ((elCoef P (zmMap S.f)).hom.mapH 0) ∧
      (∀ n, Function.Exact ((elCoef P (zmMap S.f)).hom.mapH n) ((elCoef P (zmMap S.g)).hom.mapH n)) ∧
      (∀ n, Function.Exact ((elCoef P (zmMap S.g)).hom.mapH n) (δ n)) ∧
      ∀ n, Function.Exact (δ n) ((elCoef P (zmMap S.f)).hom.mapH (n + 1)) := by
  obtain ⟨hi, he, hs⟩ := ses_app S h
  obtain ⟨h1, h2, h3⟩ := CrystallineSemistableComparison.P.ses_cochains (Functor.whiskerLeft (CategoryOfElements.π P) (zmMap S.f))
    (Functor.whiskerLeft (CategoryOfElements.π P) (zmMap S.g))
    (fun T => hi T.1) (fun T => he T.1) (fun T => hs T.1)
  exact CrystallineSemistableComparison.P.les _ _ h1 h2 h3

def tδ (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ) : TH P S.X₃ j →+ TH P S.X₁ (j + 1) :=
  (Classical.choose (les_ex P S h) j).toAddMonoidHom

theorem tδ_spec (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (n : ℕ)
    (y : (cx (elF P (zm S.X₂))).X n) (x : (cx (elF P (zm S.X₁))).X (n + 1)) (hz) (hx)
    (e : (elCoef P (zmMap S.f)).hom.f (n + 1) x = (cx (elF P (zm S.X₂))).d n y) :
    tδ P S h n ((cx (elF P (zm S.X₃))).cls ((elCoef P (zmMap S.g)).hom.f n y) hz) = (cx (elF P (zm S.X₁))).cls x hx :=
  (Classical.choose_spec (les_ex P S h)).1 n y x hz hx e

theorem ex₃ (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ) :
    Function.Exact (tMap P S.g j) (tδ P S h j) :=
  (Classical.choose_spec (les_ex P S h)).2.2.2.1 j

theorem ex₁ (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ) :
    Function.Exact (tδ P S h j) (tMap P S.f (j + 1)) :=
  (Classical.choose_spec (les_ex P S h)).2.2.2.2 j

theorem tPull_tδ {Q P : C ⥤ Type} (u : Q ⟶ P) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ) (x : TH P S.X₃ j) :
    tPull u S.X₁ (j + 1) (tδ P S h j x) = tδ Q S h j (tPull u S.X₃ j x) := by
  obtain ⟨hi, he, hs⟩ := ses_app S h
  obtain ⟨c, hc, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (elF P (zm S.X₃))) j).1 x
  obtain ⟨h1, h2, h3⟩ := CrystallineSemistableComparison.P.ses_cochains (Functor.whiskerLeft (CategoryOfElements.π P) (zmMap S.f))
    (Functor.whiskerLeft (CategoryOfElements.π P) (zmMap S.g))
    (fun T => hi T.1) (fun T => he T.1) (fun T => hs T.1)
  obtain ⟨y, rfl⟩ := h3 j c
  have hdy : (Mor.ofNatTrans (Functor.whiskerLeft (CategoryOfElements.π P) (zmMap S.g))).hom.f (j + 1)
      ((cx (elF P (zm S.X₂))).d j y) = 0 := by
    rw [← Cx.Hom.comm]; exact hc
  obtain ⟨x, hx⟩ := ((h2 (j + 1)) _).1 hdy
  have hxz : (cx (elF P (zm S.X₁))).d (j + 1) x = 0 := by
    apply h1 (j + 1 + 1)
    rw [map_zero, ← Cx.Hom.comm, hx]
    exact (cx (elF P (zm S.X₂))).dd j y
  have e1 : tPull u S.X₃ j ((cx (elF P (zm S.X₃))).cls ((elCoef P (zmMap S.g)).hom.f j y) hc) =
      (cx (elF Q (zm S.X₃))).cls ((elCoef Q (zmMap S.g)).hom.f j ((elMor u (zm S.X₂)).hom.f j y))
        (by
          exact ((elMor u (zm S.X₃)).hom.comm j ((elCoef P (zmMap S.g)).hom.f j y)).trans
            ((congrArg _ hc).trans (map_zero _))) := rfl
  have e2 : tPull u S.X₁ (j + 1) ((cx (elF P (zm S.X₁))).cls x hxz) =
      (cx (elF Q (zm S.X₁))).cls ((elMor u (zm S.X₁)).hom.f (j + 1) x) (by
        rw [Cx.Hom.comm, hxz, map_zero]) := rfl
  refine (congrArg (tPull u S.X₁ (j + 1)) (tδ_spec P S h j y x hc hxz hx)).trans ?_
  refine e2.trans (Eq.trans ?_ (congrArg (tδ Q S h j) e1).symm)
  refine (tδ_spec Q S h j _ _ _ _ ?_).symm
  refine Eq.trans ?_ ((elMor u (zm S.X₂)).hom.comm j y).symm
  exact congrArg ((elMor u (zm S.X₂)).hom.f (j + 1)) hx

end UpperTheory.Ru.crystallineComparison.Th
end
end
