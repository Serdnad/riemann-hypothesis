module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle072
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

def IsBiRig {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) : Prop :=
  P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left)

def IsPPol {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) : Prop :=
  IsBiRig A P ∧ RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧
    ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1

def IsComplAt {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R] (ψ : A →+* R) : Prop :=
  IsNoetherianRing R ∧ IsAdicComplete (maximalIdeal R) R ∧ ψ.Flat ∧ ((maximalIdeal R).comap ψ).map ψ = maximalIdeal R ∧
    ∀ r : R, ∃ a b : A, IsUnit (ψ b) ∧ r * ψ b - ψ a ∈ maximalIdeal R

section From

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W) (iw : W →+* V)
  {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ)

def DataFrom (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)) : Prop :=
  ∃ (β : Q.B.left ⟶ T.B.left) (β₂ : (G2 Q.B).left ⟶ (G2 T.B).left)
    (w : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ T.B T.M.L).pull β₂)),
    IsGrpPullback Q.B T.B (spMap iw) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (Q.c a).left ≫ β = spMap iw ≫ (T.c₀ ((n : ℤ) • e a)).left) ∧
    ∀ a b, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧
      ∀ z J J', Good T.M.L z J → Good Q.M.L z J' →
        val (Q.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V).left) z ⊤ (unitOn k) *
          (lamVal w (lift (toUnit (TK V) ≫ Q.c a) (toUnit (TK V) ≫ Q.c b)).left z J J' *
            val (T.τ₀ ((n : ℤ) • e a) ((n : ℤ) • e b)) ((TK V).hom ≫ spMap iw) z J)

def DegFrom (D : DegPre V) (e : D.X ≃+ (Fin T.r → ℤ)) : Prop :=
  ∃ (Q : Data V) (e' : D.X ≃+ Q.X), Refines Q (RingHom.id V) D e' ∧ DataFrom T iw s ε n Q (e'.symm.trans e)

end From

structure LowBase {o : Type} [CommRing o] (ζ : o) (n : ℕ) where

  h : ℕ

  F : SFam h n ζ

  W : Type
  [ring : CommRing W]
  [loc : IsLocalRing W]
  noeth : IsNoetherianRing W
  complete : IsAdicComplete (maximalIdeal W) W

  T : TautBase o W

  u : Sp W ⟶ (LowChart.powA F T.r).left
  u_et : IsEtaleCompletion (Scheme.stalkClosedPointTo u).hom
  u_sep : ((residue W).comp (Scheme.stalkClosedPointTo u).hom).FormallyUnramified
  u_base : u ≫ LowChart.toO F T.r = spMap T.b
  dim : T.g = h

  β : T.B.left ⟶ F.univ.A.left

  β₂ : (G2 T.B).left ⟶ (G2 F.univ.A).left
  cart : IsGrpPullback T.B F.univ.A (u ≫ (LowChart.powA F T.r).hom) β
  sq : IsSquare β β₂
  lb : LBIso (abelian₂ T.B T.M.L) (F.univ.P.pull β₂)
  coord : ∀ i, (T.c₀ (Pi.single i 1)).left ≫ β = u ≫ (LowChart.coord F i).left

attribute [instance] LowBase.ring LowBase.loc

structure Taut {o : Type} [CommRing o] (ζ : o) (g n : ℕ) (φ : InvFun ℤ) extends LowBase ζ n where
  genus : h + T.r = g

  m : ℕ

  N : ℕ

  ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin T.r → ℤ))
  cone : IsCone id φ fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin T.r → ℤ))
  defin : ∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin T.r → ℤ)) x x

  R : Type
  [ringR : CommRing R]
  [domR : IsDomain R]
  [locR : IsLocalRing R]

  ψ : MvPolynomial (Fin m ⊕ Fin N) W →+* R
  compl : IsComplAt ψ
  ψ_loc : IsLocalHom (ψ.comp MvPolynomial.C)
  bd : ∀ k, ψ (MvPolynomial.X (.inl k)) ∈ maximalIdeal R
  tor : ∀ k, IsUnit (ψ (MvPolynomial.X (.inr k)))

  Q : Data R

  e : Q.X ≃+ (Fin T.r → ℤ)
  data : DataFrom T (ψ.comp MvPolynomial.C) (fun k => ψ (MvPolynomial.X k))
    (fun k => (ε k : LinearMap.BilinForm ℤ (Fin T.r → ℤ))) n Q e

attribute [instance] Taut.ringR Taut.domR Taut.locR

namespace Taut

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ)

def iw : C.W →+* C.R := C.ψ.comp MvPolynomial.C

def b : o →+* C.R := C.iw.comp C.T.b

def s (k : Fin C.m ⊕ Fin C.N) : C.R := C.ψ (MvPolynomial.X k)

def t (k : Fin C.m) : C.R := C.s (.inl k)

def form (k : Fin C.m ⊕ Fin C.N) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ) := C.ε k

def δ (k : Fin C.m) : LinearMap.BilinForm ℤ C.Q.X := pull C.e.toIntLinearEquiv.toLinearMap (C.form (.inl k))

def IsFam (F : SFam g n ζ) (G₁ : Over (Sp C.R)) [GrpObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X)
    (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) : Prop :=
  IsSemiAbelian G₁ ∧ (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) ∧ IsGenFibre F y α₁ ∧
    IsMumfordFam F y α₁ C.Q ∧ y ≫ F.s = jK C.R ≫ spMap C.b

end Taut

def IsMumPol {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁]
    (P : LB (G2 G₁).left) : Prop :=
  IsCN R ∧ Q.IsPos (maximalIdeal R) ∧ IsSemiAbelian G₁ ∧ IsBiRig G₁ P ∧
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left)
        (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'),
        IsGrpPullback G' G₁ (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂)

def SameFib {S S' T : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S)
    (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (P' : LB (G2 A').left) (f' : T ⟶ S') : Prop :=
  ∃ (H : Over T) (_ : GrpObj H) (_ : IsCommMonObj H) (a : H.left ⟶ A.left) (a₂ : (G2 H).left ⟶ (G2 A).left)
    (a' : H.left ⟶ A'.left) (a₂' : (G2 H).left ⟶ (G2 A').left),
    IsGrpPullback H A f a ∧ IsSquare a a₂ ∧ IsGrpPullback H A' f' a' ∧ IsSquare a' a₂' ∧ LBIso (P.pull a₂) (P'.pull a₂')

def TorsRat {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : FractionRing R →+* K) (x : Over.mk (spMap κ ≫ jK R) ⟶ G), x ^ n = 1 →
    ∃ x₀ : Over.mk (jK R) ⟶ G, x.left = spMap κ ≫ x₀.left

def GalRigid {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (θ : R →+* R') (σ : R' ≃+* R'), IsCN R' → Function.Injective θ →
    θ.Finite → IsOfFinOrder σ → (∀ a, σ (θ (f a)) = θ (f a)) → (∀ r, σ (θ r) - θ r ∈ maximalIdeal R') → ∀ r, σ (θ r) = θ r

end GlobalTheory.TChart
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
namespace GlobalTheory.UPoinc.UModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def valInt (t : UCTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* OO p :=
  (RatModel.valLoc t.y z₁ (specializes_of_eq t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem val_eq_valInt (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : t.val a = (valInt t a : PadicAlgCl p) :=
  RatModel.val_spMap_comp (OO p).subtype t.y (specializes_of_eq t.cen) (X₁.M.stalkEquiv z₁ a)

theorem norm_val_le (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖t.val a‖ ≤ 1 := by
  rw [val_eq_valInt]
  have h : Valued.v (valInt t a : PadicAlgCl p) ≤ 1 := (valInt t a).2
  exact_mod_cast h

end GlobalTheory.UPoinc.UModel
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

section Ord

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω)

def UOrdGe (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) ∧
    ∃ w : T.V, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def UOrdEq (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  ∃ w : T.Vˣ, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

section API

variable {M} {T : UTrait Xo c} {ξ : Sp T.V ⟶ M.Z} {x y : Ω} {a b : ℕ}

theorem uOrdEq_one (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) : UOrdEq M T ξ 1 0 :=
  ⟨1, by rw [RatModel.val_one, pow_zero, Units.val_one, mul_one, map_one]⟩

end API

variable {M}

end Ord

def UTraitExtSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V →
    ∀ y : Sp (FractionRing V) ⟶ Xo.XF c,
      ∃ (T : UTrait Xo c) (f : V →+* T.V) (fK : FractionRing V →+* FractionRing T.V), Function.Injective f ∧
        IsLocalHom f ∧ f.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap T.V _ (f a)) ∧ T.y = spMap fK ≫ y

def UTraitUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T T' : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (f : T.V →+* W)
    (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W) (fK' : FractionRing T'.V →+* FractionRing W),
    GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → Function.Injective f → Function.Injective f' → IsLocalHom f →
    IsLocalHom f' → (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) →
    (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) → spMap fK ≫ T.y = spMap fK' ≫ T'.y →
    ∀ (w : W) (m m' : ℕ), Irreducible w → Associated (f T.ϖ) (w ^ m) → Associated (f' T'.ϖ) (w ^ m') →
      ∃ e : T.P.D.toPre.X ≃ₗ[𝓞 E] T'.P.D.toPre.X, ∀ a b, (m : ℤ) * T.be a b = m' * T'.be (e a) (e b)

def UPoinOnX (Xo : Moduli D l) (c : Coeff l) (φ : InvFun (𝓞 E)) {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z)
    (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) (BD : EffCartierData S) :
    Prop :=
  (IsProjOver zs ∧ IsNormalScheme Z ∧ IsOpenImmersion i ∧ Dense (Set.range i) ∧ i ≫ zs = pullback.snd _ _ ∧
    OZ.IsLB ∧ IsAmpleLB OZ) ∧
  (1 ≤ N ∧ ∀ (Y : Model Xo c (RingHom.id c.F)) (f : Y.X ⟶ Z), Y.j ≫ f = i → (GlobalTheory.FlagMod.detOm Y).IsLB →
    LBIso (OZ.pull f) (lbPow (GlobalTheory.FlagMod.detOm Y) N)) ∧
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)),
    Nonempty (PELUnif (maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t →
      ∀ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _ → ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ≫ i ∧ ξ ≫ zs = σ) ∧
  (1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ UValOn Xo c i φ J d) ∧
  (GlobalTheory.Poinc.IsNormBl π J ∧ IsProjOver (π ≫ zs) ∧ IsOpenImmersion j ∧ Dense (Set.range j) ∧ j ≫ π = i ∧
    π ⁻¹' Set.range i = Set.range j ∧ BD.idealSheaf = J.comap π ∧ UValOn Xo c j φ BD.idealSheaf d) ∧
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (OZ.pull π) k) (CechPic.dual BD.lb))

end GlobalTheory.UPoinc
end
end
