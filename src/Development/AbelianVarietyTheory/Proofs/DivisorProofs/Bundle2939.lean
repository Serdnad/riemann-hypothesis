module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle673
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle080
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem USetup.range_π_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (η : Xo.XF c) (A : Set C.Z), (∀ w, X₁.uΩ w = η) → closure {C.i η} = A → Set.range X₁.π = A := by
  intro E _ _ _ H Dw _ l Xo c C X₁ η A hη hA
  haveI := X₁.fin
  have hc : IsClosedMap X₁.π.base := X₁.π.isClosedMap
  let w₀ : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : X₁.M.pt w₀ = genericPoint X₁.M.Z := X₁.M.pt_apply w₀
  have hpt : X₁.π (X₁.M.pt w₀) = C.i η := by
    have h := congrArg (fun f => f.base w₀) X₁.comp
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hη w₀]
    simpa using h
  have huniv : closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) = Set.univ := genericPoint_spec X₁.M.Z
  rw [← hA, ← hpt, hgen, ← Set.image_singleton, ← Set.image_univ, ← huniv]
  exact (hc.closure_image_eq_of_continuous X₁.π.continuous _).symm

end GlobalTheory.UPoinc
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

def USame {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') : Prop :=
  ∃ (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left),
    IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a ∧ IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a' ∧
    LBIso P₀.L (ρ.P.L.pull a) ∧ LBIso P₀.L (ρ'.P.L.pull a') ∧
    ∀ x, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ a = spMap (φ.comp S.R.val.toRingHom) ≫ (ρ.pt x).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (lab x)).left

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf}

def UIsLab (X : USetup C) {p : ℕ} [Fact p.Prime] {z : X.M.Z} (ct : UCTrait X p z)
    (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) : Prop :=
  ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R')
    (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf),
    USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ spMap (ratHull R').val.toRingHom ≫ u' = X.uΩ ∧
    R' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∧
    ∃ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
      IsGrpPullback G ρ'.P.A (spMap (toRat R')) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧
      LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ ct.y) a) ∧
        ∃ (u : ρ'.UTest p y₀) (lb : u.Lab) (j : u.D.toPre.X ≃+ ct.T.P.D.toPre.X),
          (∀ χ, lb.q χ = ct.sc * (ct.T.be (j χ) (j χ) : ℝ) / 2) ∧
          (∀ a χ, lb.yy a = QuotientAddGroup.mk χ → yy a = QuotientAddGroup.mk (j χ)) ∧
          ∀ (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
            (w w' : Sp (PadicAlgCl p) ⟶ G.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
            QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ α = x.left ≫ u.φ → w' ≫ α = x'.left ≫ u.φ →
            w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → CongMod m (j pk'.y) (a • j pk.y)

structure UDeep (X₁ : USetup C) where

  X : USetup C
  [alg : Algebra X₁.Ω₁ X.Ω₁]
  fd : FiniteDimensional X₁.Ω₁ X.Ω₁
  gal : IsGalois X₁.Ω₁ X.Ω₁

  pt : X.uΩ = spMap (algebraMap X₁.Ω₁ X.Ω₁) ≫ X₁.uΩ

  q : X.M.Z ⟶ X₁.M.Z
  fin : IsFinite q
  gen : X.M.pt ≫ q = spMap (algebraMap X₁.Ω₁ X.Ω₁) ≫ X₁.M.pt
  comp : q ≫ X₁.π = X.π

  m : ℕ
  sq : X.S.N = m ^ 2
  dvd : X₁.S.r * X₁.S.N ∣ m

  lab : X₁.S.Gam →+ X.S.Gam
  same : USame X₁.ρ X.ρ lab (algebraMap X₁.Ω₁ X.Ω₁)
  lab_range : ∀ x : X.S.Gam, ∃ a, lab a = (X.S.r * X.S.N / (X₁.S.r * X₁.S.N)) • x

attribute [instance] UDeep.alg

namespace UDeep

variable {X₁ : USetup C} (D : UDeep X₁)

@[reducible] def lift {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z)
    (h : y ≫ D.q = ct.y) : UCTrait D.X p (y (cPt p)) where
  y := y
  cen := rfl
  T := ct.T
  ι := ct.ι
  int := ct.int
  comm := by rw [← D.comp, ← Category.assoc y, h, ct.comm]

def Compat {Y : Type} [AddCommGroup Y] (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) Y)
    (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) Y) : Prop :=
  ∀ a μ, yy₁ a = QuotientAddGroup.mk μ →
    yy (D.lab a) = QuotientAddGroup.mk ((D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • μ)

end UDeep

end GlobalTheory.UPoinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.TraitPull

theorem exists_pull_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ h : T.V →+* W, Function.Injective h → IsLocalHom h → ∃ (tW : SAB H (Sp W)) (_ : SABMap tW T.t (spMap h)) (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X), ∀ y, 0 ≤ T.be (e y) (e y) ∧ ∃ r, PsiCoord PW.D.toPre y r ∧ Associated (r ^ 2) (h T.ϖ ^ (T.be (e y) (e y)).toNat) := by
  intro E _ _ _ H Dw l Xo c T W _ _ _ hW hWd h hi hl
  obtain ⟨tW, ⟨m⟩⟩ := GlobalTheory.Models.Inhab.exists_pull (spMap h) T.t
  obtain ⟨PW, e, he⟩ := GlobalTheory.UnifDvrBaseChange.exists_pelUnif E H T.V T.cdvr T.t T.P W hW hWd h hi hl tW ⟨m⟩
  refine ⟨tW, m, PW, e, fun y => ?_⟩
  obtain ⟨u, n, hn, hc⟩ := T.mono (e y)
  have hn0 : T.be (e y) (e y) = 2 * (n 0 : ℤ) := hn 0
  obtain ⟨v, hv⟩ := he y _ hc
  refine ⟨by rw [hn0]; positivity, _, hv, ?_⟩
  have ht : (T.be (e y) (e y)).toNat = 2 * n 0 := by rw [hn0]; omega
  rw [ht]
  have hu : IsUnit ((v : W) * h u) := v.isUnit.mul (u.isUnit.map h)
  have e1 : ((v : W) * h (u * ∏ i, ![T.ϖ] i ^ n i)) ^ 2 = ((v : W) * h u) ^ 2 * h T.ϖ ^ (2 * n 0) := by
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow]
    ring
  rw [e1]
  exact associated_unit_mul_left _ _ (hu.pow 2)

end GlobalTheory.UPoinc.TraitPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ProjOverBase

theorem isProjOver_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (κ : C.o →+* X.o₁), X.uΩ ≫ C.i ≫ C.z = spMap ((algebraMap X.o₁ X.Ω₁).comp κ) → IsProjOver X.M.s := by
  intro E _ _ _ H Dw l Xo cf C X κ h
  have hs : X.M.s ≫ spMap κ = X.π ≫ C.z := by
    refine ext_of_isDominant X.M.pt ?_
    rw [← Category.assoc, X.M.pt_s, ← Category.assoc, X.comp]
    simp only [USetup.uΩ, UCompact.i, Category.assoc] at h ⊢
    rw [h]
    exact (Spec.map_comp (CommRingCat.ofHom κ) (CommRingCat.ofHom (algebraMap X.o₁ X.Ω₁))).symm
  haveI := C.ded
  exact GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over C.o X.o₁ κ X.M.Z C.Z C.z X.π X.M.s C.proj X.fin inferInstance hs

end GlobalTheory.UPoinc.ProjOverBase

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UTrait

theorem finrank_le_min : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c),
    Module.finrank (𝓞 E) T.P.D.toPre.X ≤ min Dw.p Dw.q := by
  intro E _ _ _ H Dw l Xo c T
  obtain ⟨hdvr, -, hch⟩ := T.cdvr
  haveI := hdvr
  haveI := hch
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  let K := AlgebraicClosure (FractionRing T.V)
  let g : FractionRing T.V →+* K := algebraMap (FractionRing T.V) K
  let f : T.V →+* K := g.comp (algebraMap T.V (FractionRing T.V))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing T.V) K).injective.comp (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := T.V) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.X := spMap g ≫ T.y ≫ pullback.fst _ _
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective (x' ≫ Xo.s)
  have hβ : x' ≫ Xo.s = spMap β₀.hom := hβ₀.symm
  have hdet := (Xo.univ.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hjK : spMap g ≫ jK T.V = spMap f := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act x' τ N →
      Module.finrank (𝓞 E) T.P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act (spMap g) τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act T.t.act m₁.act (spMap g) τ N).1 h₅
    rw [hjK] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H T.V T.t T.P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

end GlobalTheory.UPoinc.UTrait
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.KerAb

theorem subset_abLocus {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Zh : ZHOut ρ M U₀ EE) (hO : S.Over₀ M U₀) :
    (U₀ : Set M.Z) ⊆ abLocus Zh.G := by
  intro z hz
  rw [Zh.ab]
  show S.TT M z = ⊥
  have hpp := (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1
  have h1 : S.perp ⊥ = ⊤ := by
    refine top_unique fun a _ h hh => ?_
    rw [AddSubgroup.mem_bot.mp hh]
    simp [ZH.eStd]
  rw [ZH.ThetaSys.TT, ZH.ThetaSys.HH, hO.supI_eq hz, S.supp, ← h1, hpp]

theorem ker_mem_and_subset_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∀ (R : Type) [CommRing R] (q : Sp R ⟶ M.Z) (V' : Type) [CommRing V'] [IsDomain V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → spMap g' ≫ q = spMap h ≫ ξ → (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) ∈ q ⁻¹' (U₀ : Set M.Z) ∧ (U₀ : Set M.Z) ⊆ abLocus out.G := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm T ξ hξ R _ q V' _ _ h g' hh hq
  refine ⟨?_, subset_abLocus out hAdm.1⟩
  obtain ⟨ξ₀, h₀, -⟩ := hξ
  let w : Sp V' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V')
  let v : Sp (FractionRing T.V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing T.V))
  have e₁ : spMap g' w = (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) :=
    PrimeSpectrum.ext (RingHom.ker_eq_comap_bot g').symm
  have e₂ : spMap h w = jK T.V v := by
    refine PrimeSpectrum.ext ?_
    show Ideal.comap h ⊥ = Ideal.comap (algebraMap T.V (FractionRing T.V)) ⊥
    rw [← RingHom.ker_eq_comap_bot, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hh,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective T.V (FractionRing T.V))]
  have e₃ : q (spMap g' w) = U₀.ι (ξ₀ v) := by
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply, e₂, ← Scheme.Hom.comp_apply, ← h₀, Scheme.Hom.comp_apply]
  rw [← e₁]
  show q (spMap g' w) ∈ U₀
  rw [e₃]
  exact (ξ₀ v).2

end GlobalTheory.UPoinc.KerAb
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.LamRigid GlobalTheory.LamBiext

namespace GlobalTheory.MumfordE8Bimultiplicative

theorem lamVal_law₁ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B]
    (M₀ : RigLB B₀) (M : RigLB B) (c₀ : CubicalStr B₀ M₀) (c : CubicalStr B M) (hB₀ : IsAbelianScheme B₀)
    (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b]
    (w : LB.Iso (abelian₂ B₀ M₀.L) ((abelian₂ B M.L).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left))
    (hw : w.IsGen)
    (hn : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.L.ι) (J' : (T.left ⟶ B₀.left) → M₀.L.ι),
      Good M.L z J → Good M₀.L z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1)
    (T : Over S) (x x' y : T ⟶ B₀) (z : T.left) (J : (T.left ⟶ B.left) → M.L.ι) (J' : (T.left ⟶ B₀.left) → M₀.L.ι)
    (hJ : Good M.L z J) (hJ' : Good M₀.L z J') :
    GlobalTheory.PolDeg.lamVal w (lift (x * x') y).left z J J' * cubV c₀ z J' x x' y =
      cubV c z J (x ≫ a) (x' ≫ a) (y ≫ b) * GlobalTheory.PolDeg.lamVal w (lift x y).left z J J' *
        GlobalTheory.PolDeg.lamVal w (lift x' y).left z J J' := by
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M.L).IsLB := DVR.linComb_isLB _ M.isLB _ _
  have hL' : (abelian₂ B₀ M₀.L).IsLB := DVR.linComb_isLB _ M₀.isLB _ _
  let β₂ : (G2 B₀).left ⟶ (G2 B).left := (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left
  have Hlam : ∀ {T₀ : Over S} (p q : T₀ ⟶ B₀) {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift p q).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h ((p ≫ a) * (q ≫ b)).left * (h (p ≫ a).left)⁻¹ * (h (q ≫ b).left)⁻¹ *
          h (1 : T₀ ⟶ B).left := fun p q U _ h => by
    rw [GlobalTheory.MumRigidZero.lift_comp_left]; exact prod_lam (p ≫ a) (q ≫ b) h
  obtain ⟨l₁, l₂, hl₁, hl₂, cl₁, cl₂, vl⟩ := exists_laws M₀ c₀
  let φ3 := law1φ B₀ (x3 B₀ 0) (x3 B₀ 1) (x3 B₀ 2)
  let β₃ : (G3 B₀).left ⟶ (G3 B).left := (lift (x3 B₀ 0 ≫ a) (lift (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b))).left
  have fe3 : FormEq (fun I => β₃ ≫ thφ B (x3 B) I) thε (flatφ (lamφ B) (fun k => φ3 k ≫ β₂)) (flatε lamε lawε) :=
    fun U _ h => by
      have e₁ := prod_cub (x3 B₀ 0 ≫ a) (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b) h
      have e₂ := prod_law₁ (x3 B₀ 0) (x3 B₀ 1) (x3 B₀ 2) (fun χ => ∏ i, h ((χ ≫ β₂) ≫ lamφ B i) ^ lamε i)
      rw [id₃] at e₂
      simp only [Over.id_left, Category.id_comp, Hlam, MonObj.mul_comp] at e₂
      rw [e₁, prod_flat, e₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  obtain ⟨g₃, hg₃, hv₃⟩ := exists_gen M.isLB fe3 (LB.pullGen M.L (thφ B (x3 B)) thε c.t β₃)
    (DVR.pullGen_isGen _ _ _ _ c.isGen β₃)
  have ht₃ := nest_isGen (L := M.L) (φ := lamφ B) (δ := lamε) hg₃
  have Ft3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι), Good M.L z₀ J₀ →
      val (L := abelian₂ B M.L) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) (lift p (lift p' q)).left z₀ (ind B J₀) =
        cubV c z₀ J₀ (p ≫ a) (p' ≫ a) (q ≫ b) := by
    intro T₀ p p' q z₀ J₀ hJ₀
    show val (L := LB.LinComb M.L (lamφ B) lamε) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) _ z₀ (ind B J₀) = _
    rw [val_nest hg₃ _ (good_ind hJ₀) hJ₀]
    simp only [adj_ind M.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    rw [hv₃ _ _ z₀ J₀ hJ₀]
    refine (val_pull hJ₀ _ _ _).trans ?_
    refine congrArg (fun r => val (L := M.L) (φ := thφ B (x3 B)) (ε := thε) c.t r z₀ J₀) ?_
    show (lift p (lift p' q) ≫ lift (x3 B₀ 0 ≫ a) (lift (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b))).left =
      (lift (p ≫ a) (lift (p' ≫ a) (q ≫ b))).left
    simp only [comp_lift, ← Category.assoc, cartesian_lift_three_comp_projection]
    rfl
  have Fa3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀' : (T₀.left ⟶ B₀.left) → M₀.L.ι),
      Good M₀.L z₀ J₀' → val (L := abelian₂ B₀ M₀.L) l₁ (lift p (lift p' q)).left z₀ (ind B₀ J₀') = cubV c₀ z₀ J₀' p p' q := by
    intro T₀ p p' q z₀ J₀' hJ₀'
    show val (L := lamLB M₀) l₁ _ z₀ (ind B₀ J₀') = _
    rw [(vl z₀ (ind B₀ J₀') (good_ind hJ₀') J₀' hJ₀').1 p p' q, adj_ind M₀.isLB hJ₀', adj_ind M₀.isLB hJ₀',
      adj_ind M₀.isLB hJ₀']
    simp
  have Fp3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι)
      (J₀' : (T₀.left ⟶ B₀.left) → M₀.L.ι),
      pw w φ3 lawε (lift p (lift p' q)).left z₀ (fun k => ind B J₀ ((lift p (lift p' q)).left ≫ φ3 k ≫ β₂))
        (fun k => ind B₀ J₀' ((lift p (lift p' q)).left ≫ φ3 k)) =
        lamVal w (lift (p * p') q).left z₀ J₀ J₀' * (lamVal w (lift p q).left z₀ J₀ J₀')⁻¹ *
          (lamVal w (lift p' q).left z₀ J₀ J₀')⁻¹ := by
    intro T₀ p p' q z₀ J₀ J₀'
    rw [pw_eq]; exact prod_law₁ p p' q (fun χ => lamVal w χ z₀ J₀ J₀')
  have sj3 : Function.Surjective ((snd B₀ (B₀ ⊗ B₀)).left ≫ (snd B₀ B₀).left ≫ B₀.hom).appTop.hom :=
    surj_comp (surj_snd hG hB₀ _) (surj_comp (surj_snd hG hB₀ _) (hG _ _ hB₀).2)
  have he3 : (lift (1 : 𝟙_ (Over S) ⟶ B₀) (lift 1 1)).left ≫ (snd B₀ (B₀ ⊗ B₀)).left ≫ (snd B₀ B₀).left ≫ B₀.hom =
      𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S) ⟶ B₀) (lift 1 1))
  have R3 := rigid_pw w hw hL hL' φ3 lawε hl₁ ht₃ _ _ he3 sj3 (fun y₀ => by
    obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt M.isLB y₀
    obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt M₀.isLB y₀
    refine ⟨ind B J₁, ind B₀ J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
    rw [Ft3 (T₀ := 𝟙_ (Over S)) 1 1 1 y₀ J₁ hJ₁, Fp3, Fa3 1 1 1 y₀ J₁' hJ₁', GlobalTheory.MumRigidZero.one_comp_hom a,
      _root_.mul_one, (isCub_cubV c hJ₁).face, (isCub_cubV c₀ hJ₁').face, hn (𝟙_ (Over S)) y₀ J₁ J₁' hJ₁ hJ₁']
    simp)
  have E3 := R3 T.left (lift x (lift x' y)).left z (ind B J) (ind B₀ J') (good_ind hJ) (good_ind hJ')
  rw [Ft3 x x' y z J hJ, Fp3, Fa3 x x' y z J' hJ'] at E3
  rw [E3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumfordE8Bimultiplicative

end

open GlobalTheory.Mum

namespace GlobalTheory.MumfordE8Bimultiplicative

end GlobalTheory.MumfordE8Bimultiplicative
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.mumfordBundleIso_value_one_zero_first_factor : ∀ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B] (M₀ : LB B₀.left) (M : LB B.left), M₀.IsLB → M.IsLB → IsAbelianScheme B₀ → ∀ (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b] (w : LB.Iso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left)), w.IsGen → (∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1) → ∀ (T : Over S) (y : T ⟶ B₀) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) y).left z J J' = 1 := by
  first | exact @GlobalTheory.MumRigidZero.lamVal_one_left | exact GlobalTheory.MumRigidZero.lamVal_one_left | (intros; apply GlobalTheory.MumRigidZero.lamVal_one_left <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_lambdaGenerator_zpow_with_periods : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℤ),
    ∃ g : LB.Gen (LB.LinComb D.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ n))
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A))) (Sum.elim Oε (fun l => -n * Oε l))), g.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a (n • b)) (𝟙 _) z J *
          val g (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J = val (D.tau a b) (𝟙 _) z J ^ n := by
  first | exact @GlobalTheory.Mum.exists_lamGen_zpow | exact GlobalTheory.Mum.exists_lamGen_zpow | (intros; apply GlobalTheory.Mum.exists_lamGen_zpow <;> assumption)
end
