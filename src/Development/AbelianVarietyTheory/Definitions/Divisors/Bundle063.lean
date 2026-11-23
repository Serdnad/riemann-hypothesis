module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
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
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

def UValOn (Xo : Moduli D l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) (J : S.IdealSheafData)
    (d : ℕ) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ S) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ j = jK W ≫ χ →
    ∀ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))), Nonempty (SABMap tK t (jK W)) →
      Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∀ P : PELUnif (maximalIdeal W) t,
      ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
        ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong J χ = Ideal.span {ϖ ^ n}

def GenOf (Xo : Moduli D l) (c : Coeff l) {R : Type} [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c)
    (t : SAB H (Sp R)) : Prop :=
  ∃ tK : SAB H (Sp (FractionRing R)), Nonempty (SABMap tK t (jK R)) ∧ Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _))

variable {Xo : Moduli D l} {c : Coeff l}

theorem exists_over_iff {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (y : Sp (FractionRing R) ⟶ Xo.XF c) :
    (∃ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _) ↔ ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := by
  constructor
  · rintro ⟨σ, -⟩ n hn
    have := (IsUnit.mk0 (n : c.F) (Nat.cast_ne_zero.2 hn)).map (Spec.preimage σ).hom
    rwa [map_natCast] at this
  · intro hu
    haveI := c.fin
    let g : c.F →+* FractionRing R := (Spec.preimage (y ≫ pullback.snd _ _)).hom
    have hint : ∀ a : c.F, ∃ r : R, algebraMap R (FractionRing R) r = g a := fun a => by
      obtain ⟨m, hm, ha⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2
        (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
      have hint : IsIntegral R (g (m • a)) := by
        obtain ⟨p, hp, h0⟩ := ha
        refine ⟨p.map (Int.castRingHom R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap R (FractionRing R)).comp (Int.castRingHom R))
          (g.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, h0, map_zero]
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
      have hum : IsUnit (m : R) := by
        have := hu m.natAbs (by simpa using hm)
        rcases Int.natAbs_eq m with e | e <;> rw [e] <;> simpa using this
      obtain ⟨u, hu'⟩ := hum
      refine ⟨(↑u⁻¹ : R) * r, ?_⟩
      have e : g (m • a) = algebraMap R (FractionRing R) u * g a := by simp [hu']
      rw [map_mul, hr, e, ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    choose f hf using hint
    have hi := IsFractionRing.injective R (FractionRing R)
    let b : c.F →+* R :=
      { toFun := f
        map_one' := hi (by simp [hf])
        map_mul' := fun _ _ => hi (by simp [hf])
        map_zero' := hi (by simp [hf])
        map_add' := fun _ _ => hi (by simp [hf]) }
    refine ⟨spMap b, ?_⟩
    rw [← Spec.map_preimage (y ≫ pullback.snd _ _), ← Spec.map_comp]
    congr 1
    ext a
    exact hf a

end GlobalTheory.UPoinc
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart.SepBModel

theorem gm_field {W : Type} [Field W] {Z : Scheme.{0}} (r : Z ⟶ Sp W) (z : Z) (U : (Sp W).Opens) (h : r z ∈ U)
    (a : Γ(Sp W, U)ˣ) : ∃ x : Wˣ, gm r z U a = gm r z ⊤ (unitOn x) := by
  obtain rfl : U = ⊤ := top_unique fun y _ => by rwa [Subsingleton.elim y (r z)]
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom.toMonoidHom a, congrArg _ (Units.ext ?_)⟩
  exact ((Scheme.ΓSpecIso (CommRingCat.of W)).hom_inv_id_apply a.val).symm

theorem gm_spMap {W V : Type} [CommRing W] [CommRing V] (f : W →+* V) (z : Sp V) (x : Wˣ) :
    gm (spMap f) z ⊤ (unitOn x) = gm (𝟙 (Sp V)) z ⊤ (unitOn (Units.map f.toMonoidHom x)) := by
  have e : unitOn (Units.map f.toMonoidHom x) = pullU (spMap f) ⊤ (unitOn x) := by
    apply Units.ext
    exact congrArg (fun q => q.hom (x : W)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  rw [e]
  exact (gm_pull (𝟙 _) (spMap f) z ⊤ trivial (unitOn x)).symm

theorem gm_unitOn_inj {V : Type} [CommRing V] [IsDomain V] (z : Sp V) {x y : Vˣ}
    (h : gm (𝟙 (Sp V)) z ⊤ (unitOn x) = gm (𝟙 (Sp V)) z ⊤ (unitOn y)) : x = y := by
  have h1 := congrArg Units.val h
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at h1
  have h2 := germ_injective_of_isIntegral (Sp V) (U := ⊤) z trivial h1
  exact Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).1 h2)





theorem lbIso_two {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : Y ⟶ X) (r : Z ⟶ Y) :
    LBIso (L.pull (r ≫ φ)) ((L.pull φ).pull r) := by
  have h : LBIso L L := by
    refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
    refine (gm_res (𝟙 X) y _ hy _).trans (Eq.symm ?_)
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res (𝟙 X) y _ hy _))).trans ?_
    have e := (gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2).trans (gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2).symm
    exact (mul_right_comm _ _ _).trans (mul_inv_eq_of_eq_mul e)
  exact (LBIso.chartPull (Geo.Tor.chartPullPull L φ φ rfl) (Geo.Tor.chartPullPull L φ φ rfl) h).chartPull
    (chartPullSame L (fun _ => r ≫ φ) (fun _ => φ) _ r fun _ => rfl) (Geo.Tor.chartPullPull (L.pull φ) r r rfl)



variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem stalkMap_gm {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)ˣ) :
    Units.map (r.stalkMap z).hom.toMonoidHom (gm f (r z) U a) = gm (r ≫ f) z U a := by
  apply Units.ext
  rw [gm_val (r ≫ f) z U h]
  show (r.stalkMap z).hom (gm f (r z) U a).val = _
  rw [gm_val f (r z) U h]
  exact Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _


end GlobalTheory.UChart.SepBModel
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKSChart

section Data

variable {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R)
  (gam : Fin m → LinearMap.BilinForm ℤ Q.X)

def constHom {k : Type} [Field k] (ρ : R →+* DualNumber k) : R →+* DualNumber k :=
  (algebraMap k (DualNumber k)).comp ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)

def IsUnitPart (y : Q.X) (n : Fin m → ℕ)
    (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c y).left) fun _ => -1)) : Prop :=
  ψ₀.IsGen ∧ (∀ i, gam i y y = 2 * n i) ∧ ∃ e : (FractionRing R)ˣ,
    (e : FractionRing R) = algebraMap R _ (∏ i, t i ^ n i) ∧ ∀ z J, Good Q.P.L z J →
      val (Q.psi y) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn e) * val ψ₀ (toUnit (TK R)).left z J

end Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.LogKSChart
end
end
