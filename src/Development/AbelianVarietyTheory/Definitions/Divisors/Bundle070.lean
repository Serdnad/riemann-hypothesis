module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle673
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle681
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {G : GDatum} {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂]
  {S S' : Scheme.{0}}

def IsGGPull {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {N : ℕ} {s' : S' ⟶ Sp R₂} {s : S ⟶ Sp R₁}
    (o' : GObj gb₂ N s') (o : GObj gb₁ N s) (f : S' ⟶ S) : Prop :=
  ∃ (φA : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left),
    IsGrpPullback o'.A o.A f φA ∧ IsSquare φA φ₂ ∧
    (∀ c : G.O, (o'.act.act c).left ≫ φA = φA ≫ (o.act.act c).left) ∧ Nonempty (LBIso o'.P (o.P.pull φ₂)) ∧
    ∀ y : G.La, (o'.eta y).left ≫ φA = f ≫ (o.eta y).left

def GBase.IsMap (β : R₁ →+* R₂) (gb₁ : GBase G R₁) (gb₂ : GBase G R₂) : Prop :=
  gb₂.ρ = β gb₁.ρ ∧ ∀ i, gb₂.t i = β.comp (gb₁.t i)

def GBase.map (β : R₁ →+* R₂) (gb : GBase G R₁) : GBase G R₂ where
  ρ := β gb.ρ
  ρ_root := by simpa using congrArg β gb.ρ_root
  t i := β.comp (gb.t i)
  t_ω i := by rw [RingHom.comp_apply, gb.t_ω]
  comax i j hij := by
    have h := congrArg (Ideal.map β) (gb.comax i j hij)
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    simpa [Function.comp_def] using h

theorem GBase.IsMap.id (gb : GBase G R₁) : GBase.IsMap (RingHom.id R₁) gb gb :=
  ⟨rfl, fun _ => rfl⟩

def IsGGPullOver (β : R₁ →+* R₂) {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {N : ℕ} {s' : S' ⟶ Sp R₂} {s : S ⟶ Sp R₁}
    (o' : GObj gb₂ N s') (o : GObj gb₁ N s) (f : S' ⟶ S) : Prop :=
  f ≫ s = s' ≫ spMap β ∧ GBase.IsMap β gb₁ gb₂ ∧ IsGGPull o' o f

section Over

variable {β : R₁ →+* R₂} {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {N : ℕ} {s' : S' ⟶ Sp R₂} {s : S ⟶ Sp R₁}
  {o' : GObj gb₂ N s'} {o : GObj gb₁ N s} {f : S' ⟶ S}

end Over

variable {R : Type} [CommRing R] [Algebra ℚ R]

theorem isGGPull_iff {gb : GBase G R} {N : ℕ} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : GObj gb N s'}
    {o : GObj gb N s} {f : S' ⟶ S} : IsGGPull o' o f ↔ Nonempty (GObjMap o' o f) :=
  ⟨fun ⟨φ, φ₂, h₁, h₂, h₃, ⟨h₄⟩, h₅⟩ => ⟨⟨φ, φ₂, h₁, h₂, h₃, h₄, h₅⟩⟩,
    fun ⟨m⟩ => ⟨m.φ, m.φ₂, m.cart, m.sq, m.act, ⟨m.pol⟩, m.eta⟩⟩

theorem isGGPullOver_id_iff {gb : GBase G R} {N : ℕ} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : GObj gb N s'}
    {o : GObj gb N s} {f : S' ⟶ S} :
    IsGGPullOver (RingHom.id R) o' o f ↔ f ≫ s = s' ∧ Nonempty (GObjMap o' o f) := by
  have e : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id (CommRingCat.of R)
  rw [IsGGPullOver, e, Category.comp_id, isGGPull_iff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, GBase.IsMap.id gb, h.2⟩⟩

theorem IsGGPull.refl {gb : GBase G R} {N : ℕ} {s : S ⟶ Sp R} (o : GObj gb N s) : IsGGPull o o (𝟙 S) :=
  isGGPull_iff.2 (Unique.gObjMap_id o)

section Comp

variable {R₃ : Type} [CommRing R₃] [Algebra ℚ R₃] {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {gb₃ : GBase G R₃} {N : ℕ}
  {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R₁} {s₂ : S₂ ⟶ Sp R₂} {s₃ : S₃ ⟶ Sp R₃} {o₁ : GObj gb₁ N s₁}
  {o₂ : GObj gb₂ N s₂} {o₃ : GObj gb₃ N s₃} {f : S₃ ⟶ S₂} {f' : S₂ ⟶ S₁}

end Comp

theorem GObj.eta_zero {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)

theorem GObj.eta_neg {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (x : G.La) :
    o.eta (-x) = (o.eta x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← o.eta_add, add_neg_cancel, GObj.eta_zero]

theorem GObj.eta_nsmul {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (n : ℕ) (x : G.La) :
    o.eta (n • x) = o.eta x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, GObj.eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

def gHeckeSub {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (g : G.La →ₗ[G.O] G.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • g x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, GObj.eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add (f := _), smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, GObj.eta_neg]⟩

def IsGHecke {gb : GBase G R} (g : G.La →ₗ[G.O] G.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : GObj gb (N * k) s)
    (o' : GObj gb N s) (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ c' : G.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta (g x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (gHeckeSub o g N) (fun h => (Hecke.transl h.1).left) ψ.left ∧
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (Hecke.sq2 ψ))) ∧ c ∣ k ^ 2

def IsGHeckeMap {gb : GBase G R} (g : G.La →ₗ[G.O] G.La) (c k N : ℕ) (X : GenModel gb N) (X' : GenModel gb (N * k))
    (π : X'.X ⟶ X.X) : Prop :=
  π ≫ X.s = X'.s ∧ ∃ (o' : GObj gb N X'.s) (ψ : X'.univ.A ⟶ o'.A), IsGHecke g c k N X'.univ o' ψ ∧
    Nonempty (GObjMap o' X.univ π)

section API

variable {gb : GBase G R} {g : G.La →ₗ[G.O] G.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : GObj gb (N * k) s}
  {o' : GObj gb N s} {ψ : o.A ⟶ o'.A}

theorem IsGHecke.isMonHom (h : IsGHecke g c k N o o' ψ) : IsMonHom ψ := h.1

theorem IsGHecke.act (h : IsGHecke g c k N o o' ψ) (c' : G.O) : o.act.act c' ≫ ψ = ψ ≫ o'.act.act c' := h.2.1 c'

theorem IsGHecke.eta (h : IsGHecke g c k N o o' ψ) (x : G.La) : o'.eta x = o.eta (g x) ≫ ψ := h.2.2.1 x

theorem IsGHecke.cover (h : IsGHecke g c k N o o' ψ) :
    GlobalTheory.ZM.IsGaloisCover (gHeckeSub o g N) (fun h => (Hecke.transl h.1).left) ψ.left := h.2.2.2.1

theorem IsGHecke.pol (h : IsGHecke g c k N o o' ψ) :
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (Hecke.sq2 ψ))) := h.2.2.2.2.1

variable {X : GenModel gb N} {X' : GenModel gb (N * k)} {π : X'.X ⟶ X.X}

end API

def GObj.forgetMul {gb : GBase G R} {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {s : S ⟶ Sp R} (o : GObj gb (N * k) s) :
    GObj gb N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta x := o.eta (k • x)
  eta_add x y := by rw [smul_add, o.eta_add]
  eta_lin c x := by rw [smul_comm, o.eta_lin]
  eta_ker x := by rw [smul_comm, smul_smul, o.eta_ker]
  geom K _ _ x β hx := by
    obtain ⟨I, hI⟩ := o.geom K x β hx
    refine ⟨I, fun y => ?_⟩
    rw [o.eta_nsmul, MonObj.comp_pow, hI, I.tower N k hN hk]

theorem gHeckeSub_smul_id_eq_one {gb : GBase G R} {N k : ℕ} {s : S ⟶ Sp R} (o : GObj gb (N * k) s) :
    ∀ h ∈ gHeckeSub o (k • LinearMap.id) N, h = 1 := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  exact o.eta_ker x

end GlobalTheory.UPel.HT.Gen
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

def Classifies (Xo : Moduli Dw l) (c : Coeff l) {T T' : Scheme.{0}} (t : SAB H T) (g : T' ⟶ T) (y : T' ⟶ Xo.XF c) : Prop :=
  ∃ t' : SAB H T', Nonempty (SABMap t' t g) ∧ Nonempty (SABMap t' Xo.univ.t (y ≫ pullback.fst _ _))

theorem genOf_iff (Xo : Moduli Dw l) (c : Coeff l) {R : Type} [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c)
    (t : SAB H (Sp R)) : GlobalTheory.UPoinc.GenOf Xo c y t ↔ Classifies Xo c t (jK R) y := Iff.rfl

structure Fam (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] where

  b : c.F →+* R

  t : SAB H (Sp R)

  P : PELUnif (maximalIdeal R) t

  y : Sp (FractionRing R) ⟶ Xo.XF c
  y_over : y ≫ pullback.snd _ _ = jK R ≫ spMap b
  gen : GlobalTheory.UPoinc.GenOf Xo c y t

structure MonoFam (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] extends Fam Xo c R where

  m : ℕ

  s : Fin m → R
  s_mem : ∀ i, s i ∈ maximalIdeal R

  δ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X
  cone : IsCone H.bar φ δ
  rank : Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q
  mono : IsMonomial P.D.toPre s (fun i => (l.M' : ℤ) • δ i)

variable {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

abbrev Gens {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) : Type :=
  ∀ a b : Q.X, LB.Gen (LB.LinComb Q.P.L (K := Fin 4) ![(Q.c (a + b)).left, (Q.c a).left, (Q.c b).left, (Q.c 0).left]
    ![-1, 1, 1, -1])

def TauIn {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : Gens Q) {N : ℕ} (s : Fin N → V)
    (ε : Fin N → LinearMap.BilinForm ℤ Q.X) : Prop :=
  ∀ a b, (τ₀ a b).IsGen ∧ ∃ k : (FractionRing V)ˣ,
    (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ ∀ z J, Good Q.P.L z J →
      val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k) * val (τ₀ a b) (toUnit (TK V)).left z J

def lamUnit {B B₀ B' Z : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {π₁ : B' ⟶ B} {π₀ : B' ⟶ B₀}
    (w : LB.Iso (M.pull π₁) (M₀.pull π₀)) {X : Type} [AddCommGroup X] (x : X → (Z ⟶ B')) (a b : X) (z : Z)
    (J : (Z ⟶ B) → M.ι) (J₀ : (Z ⟶ B₀) → M₀.ι) : (Z.presheaf.stalk z)ˣ :=
  gw w (x (a + b)) z (J₀ (x (a + b) ≫ π₀)) (fun _ => J (x (a + b) ≫ π₁)) *
    (gw w (x a) z (J₀ (x a ≫ π₀)) (fun _ => J (x a ≫ π₁)))⁻¹ *
    (gw w (x b) z (J₀ (x b ≫ π₀)) (fun _ => J (x b ≫ π₁)))⁻¹ *
    gw w (x 0) z (J₀ (x 0 ≫ π₀)) (fun _ => J (x 0 ≫ π₁))

def SepAt {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) {m : ℕ} (s : Fin m → V)
    (gam : Fin m → LinearMap.BilinForm ℤ Q.X) {K : Type} [Field K] (ev : V →+* K) (k₀ : Subfield K) : Prop :=
  (∀ i, ev (s i) = 0) ∧
  ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
    (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
    (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)) (α : Fin m → Kˣ),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧
    w.IsGen ∧
    (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) ∧
    ∀ a b τ₀, GlobalTheory.RigChart.IsUnitTau Q s gam a b τ₀ →
      ∃ τ₁ : LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]), τ₁.IsGen ∧
        ∀ z J J₀, Good Q.P.L z J → Good M₀ z J₀ →
          val τ₀ (spMap ev) z J = lamUnit w c' a b z J J₀ *
            gm (𝟙 (Sp K)) z ⊤ (unitOn (∏ i, α i ^ gam i a b)) * val τ₁ (spMap k₀.subtype) z J₀

abbrev DefOver {K : Type} [Field K] (k₀ : Subfield K) {Y : Scheme.{0}} (P : Sp K ⟶ Y) : Prop :=
  GlobalTheory.Poinc.Sep.DefOver k₀ P

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def OpenCls (C : MonoFam Xo c φ R) : Prop :=
  ∃ (yo : Sp (Localization.Away (∏ i, C.s i)) ⟶ Xo.XF c) (tO : SAB H (Sp (Localization.Away (∏ i, C.s i)))),
    Nonempty (SABMap tO C.t (spMap (algebraMap R (Localization.Away (∏ i, C.s i))))) ∧
    Nonempty (SABMap tO Xo.univ.t (yo ≫ pullback.fst _ _)) ∧
    ∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, C.s i)),
      g ≫ spMap (algebraMap R (Localization.Away (∏ i, C.s i))) = jK R → g ≫ yo = C.y

def Inj (C : MonoFam Xo c φ R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R',
    Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ →
    ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ →
      κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → θ₁ = θ₂

def PointRigid (C : MonoFam Xo c φ R) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) → SepAt C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ev k₀ →
    (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀

def IsTaut {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)) : Prop :=
  ∃ hm : C.m = m, (∀ i, C.s i = bdParam k m e (Fin.cast hm i)) ∧ OpenCls C ∧ Inj C ∧
    (GlobalTheory.RigChart.IsRigid C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ∧ PointRigid C ∧
      ((residue (ChartRing k m e)).comp C.b).EssFiniteType) ∧
    (∃ (N : ℕ) (s : Fin C.m ⊕ Fin N → ChartRing k m e)
      (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre),
      (∀ i, s (.inl i) = C.s i) ∧ (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) ∧ (∀ k, IsUnit (s (.inr k))) ∧
      TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
        (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X))) ∧
    (letI := ((residue (ChartRing k m e)).comp C.b).toAlgebra;
      ((m + e : ℕ) : Cardinal) + Algebra.trdeg c.F (ResidueField (ChartRing k m e)) = Dw.dim)

def UPre (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) [IsOpenImmersion j]
    (BD : EffCartierData S) (d : ℕ) (x : S) : Prop :=
  ∃ (k : Type) (_ : Field k) (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S)
    (a : Fin C.m → ℕ),
    IsTaut C ∧ C.y ≫ j = jK _ ≫ ξ ∧ ξ (closedPoint _) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} ∧
    (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i}

theorem Fam.rank_le [IsNoetherianRing R] (C : Fam Xo c R) :
    Module.finrank (𝓞 E) C.P.D.toPre.X ≤ min Dw.p Dw.q := by
  haveI : CharZero R := C.b.charZero_iff C.b.injective |>.1 inferInstance
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := C.gen
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let u : Sp K ⟶ Sp (FractionRing R) := spMap (algebraMap (FractionRing R) K)
  have hu : u ≫ jK R = spMap f := (Spec.map_comp _ _).symm
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective ((u ≫ C.y ≫ pullback.fst _ _) ≫ Xo.s)
  have hdet := (Xo.univ.geom K _ β₀.hom hβ₀.symm).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act (u ≫ C.y ≫ pullback.fst _ _) τ N →
      Module.finrank (𝓞 E) C.P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act u τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act C.t.act m₁.act u τ N).1 h₅
    rw [hu] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R C.t C.P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

theorem level_pos (l : Geo.Tor.Level H) : 0 < l.M' :=
  Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

theorem MonoFam.s_ne_zero (C : MonoFam Xo c φ R) (i : Fin C.m) : C.s i ≠ 0 := by
  intro h0
  have hy : ∃ y, C.δ i y y ≠ 0 := by
    by_contra hn
    push Not at hn
    refine C.cone.linearIndependent.ne_zero i (LinearMap.ext₂ fun a b => ?_)
    have := hn (a + b)
    simp only [map_add (f := _), LinearMap.add_apply, hn, (C.cone.mem i).1 b a] at this
    simp only [LinearMap.zero_apply]
    omega
  obtain ⟨y, hy⟩ := hy
  obtain ⟨u, n, hn, e⟩ := C.mono y
  have hni : n i ≠ 0 := fun h1 => by
    have := hn i
    simp only [h1, LinearMap.smul_apply, smul_eq_mul, Nat.cast_zero, mul_zero, mul_eq_zero] at this
    exact this.elim (by exact_mod_cast (level_pos l).ne') hy
  exact GlobalTheory.PsiCoordLocal.ne_zero_of_coord e (by
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0, zero_pow hni]), mul_zero])

theorem Fam.exists_monoFam [IsNoetherianRing R] (C : Fam Xo c R) (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) {u : R}
    (hu : u ∈ maximalIdeal R) {β : LinearMap.BilinForm ℤ C.P.D.toPre.X} (hβ : β ∈ balForms H.bar C.P.D.toPre.X)
    (h : IsMonomial C.P.D.toPre ![u] ![(l.M' : ℤ) • β]) : ∃ C' : MonoFam Xo c φ R, C'.toFam = C := by
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) _
  have hM : (0 : ℤ) < l.M' := by exact_mod_cast level_pos l
  have h0 : ∀ y, 0 ≤ β y y := fun y => nonneg_of_mul_nonneg_right (h.nonneg 0 y) hM
  obtain ⟨m, δ, cf, hδ, hcf, hsum⟩ := GlobalTheory.ConeInterior.exists_pos_comb (hφ _ C.rank_le) hβ
    (toReal_mem_psdCone_of_nonneg E H _ β hβ h0)
  refine ⟨⟨C, m, fun i => u ^ cf i, fun i => Ideal.pow_mem_of_mem _ hu _ (hcf i), δ, hδ, C.rank_le, fun y => ?_⟩, rfl⟩
  obtain ⟨v, n, hn, hc⟩ := h y
  have ev : ∀ i, ∃ k : ℕ, ((l.M' : ℤ) • δ i) y y = 2 * k := fun i => by
    have h1 := apply_self_eq_two_mul ((balForms_eq_levelForms H C.P.D.toPre.X).le (hδ.mem i)) y
    have h2 := hδ.nonneg i y
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ δ i y (H.w0 • y) by omega)
    exact ⟨l.M' * k, by rw [LinearMap.smul_apply, LinearMap.smul_apply, h1, hk]; push_cast; simp; ring⟩
  choose k hk using ev
  have e : n 0 = ∑ i, cf i * k i := by
    have h1 : ((l.M' : ℤ) • β) y y = 2 * n 0 := hn 0
    have h2 : ((l.M' : ℤ) • β) y y = ∑ i, cf i * ((l.M' : ℤ) • δ i) y y := by
      simp only [hsum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, nsmul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [hk] at h2
    have : (2 : ℤ) * n 0 = 2 * ((∑ i, cf i * k i : ℕ) : ℤ) := by
      rw [← h1, h2]; push_cast; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    omega
  refine ⟨v, k, hk, ?_⟩
  simpa only [Fin.prod_univ_one, Matrix.cons_val_zero, e, ← pow_mul, Finset.prod_pow_eq_pow_sum] using hc

end GlobalTheory.UChart
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

section Ord

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {F : SFam g n ζ}

def OrdGe (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) ∧
    ∃ w : T.V, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def OrdEq (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  ∃ w : T.Vˣ, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def ThroughU {X : Scheme.{0}} (U₀ : M.Z.Opens) (u₀ : U₀.toScheme ⟶ X) (c : X ⟶ F.X) (T : Trait F) (ξ : Sp T.V ⟶ M.Z) : Prop :=
  ∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ ξ₀ ≫ u₀ ≫ c = T.y

variable {M}

variable (M)

end Ord

def TraitExtSt : Prop :=
  ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (T : Trait F) (f : V →+* T.V) (fK : FractionRing V →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧
        f.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap T.V _ (f a)) ∧ T.y = spMap fK ≫ y

def TraitUniqSt : Prop :=
  ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T T' : Trait F) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W] (f : T.V →+* W) (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W)
    (fK' : FractionRing T'.V →+* FractionRing W), GlobalTheory.Mum.Base W → IsDiscreteValuationRing W →
    Function.Injective f → Function.Injective f' → IsLocalHom f → IsLocalHom f' →
    (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) →
    spMap fK ≫ T.y = spMap fK' ≫ T'.y → ∀ (w : W) (m m' : ℕ), Irreducible w → Associated (f T.ϖ) (w ^ m) →
      Associated (f' T'.ϖ) (w ^ m') →
      ∃ e : T.D.toPre.X ≃+ T'.D.toPre.X, ∀ a b, (m : ℤ) * T.β a b = m' * T'.β (e a) (e b)

end GlobalTheory.Poinc
end
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

def Factor.Alg {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} (F : Factor D D') : Prop :=
  (∃ b : ℕ, 0 < b ∧ Star.star F.e * F.e = b • (Star.star F.e * F.f * F.e)) ∧
    Star.star F.e * F.f * F.e = Star.star F.e * Star.star F.f * F.e ∧ ∃ g : F.O, g * (Star.star F.e * F.f * F.e) = F.e

end GlobalTheory.Mum
end
end
