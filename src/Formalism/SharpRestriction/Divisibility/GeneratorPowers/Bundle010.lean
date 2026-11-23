module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)

attribute [local instance] Over.cartesianMonoidalCategory

section Rel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def FrTrunc (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, LB.Gen.Corr t.PP.L _ _ _ _
    (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)]) (cε 2) (e (m + 1))
      (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
    (e m)

def FrAxes (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ m, LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
          (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S)
            p.1 p.2)).left)
      (LB.oneGen t.PP.L) ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d =>
          (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S)
            p.1 p.2)).left)
      (LB.oneGen t.PP.L)

def Rig0G (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) :
    Prop :=
  LB.Gen.Corr t.PP.L _ _ _ _
    (LB.pullGen t.PP.L _ _ (eLG t x0 d x act e wP 0) (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left)
    (rigT t.G t.PP.L t.PP.rig (overAt x0 S) 1)

end Rel

section Ids

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O]

structure AxesOK (ph1 ph2 : PS R 3 d) (sy : PS R 2 d) (ad : O → PS R 2 d) : Prop where
  cocycleLeft_zero_fst : ev (n := 2) ![0, pt R d 0, pt R d 1] ph1 = 1
  cocycleLeft_zero_snd : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph1 = 1
  cocycleLeft_zero_thd : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph1 = 1
  cocycleRight_zero_fst : ev (n := 2) ![0, pt R d 0, pt R d 1] ph2 = 1
  cocycleRight_zero_snd : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph2 = 1
  cocycleRight_zero_thd : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph2 = 1
  symmetry_zero_fst : ev (n := 1) ![0, pt R d 0] sy = 1
  symmetry_zero_snd : ev (n := 1) ![pt R d 0, 0] sy = 1
  ad_c : ∀ a, MvPowerSeries.constantCoeff (ad a) = 1

structure FBRest [StarRing O] (G : FGLaw R d) (A : Germ.OAct O G) (ph1 ph2 : PS R 3 d) (sy : PS R 2 d)
    (ad : O → PS R 2 d) : Prop where
  adjoint_zero_fst : ∀ a, ev (n := 1) ![0, pt R d 0] (ad a) = 1
  adjoint_zero_snd : ∀ a, ev (n := 1) ![pt R d 0, 0] (ad a) = 1

  cocycleLeft_assoc :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 3] ph1 *
        ev (n := 4) ![G.add (pt R d 0) (pt R d 1), pt R d 2, pt R d 3] ph1 =
      ev (n := 4) ![pt R d 1, pt R d 2, pt R d 3] ph1 *
        ev (n := 4) ![pt R d 0, G.add (pt R d 1) (pt R d 2), pt R d 3] ph1

  cocycleLeft_comm : ev (n := 3) ![pt R d 1, pt R d 0, pt R d 2] ph1 = ph1

  cocycleRight_assoc :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 2] ph2 *
        ev (n := 4) ![pt R d 0, G.add (pt R d 1) (pt R d 2), pt R d 3] ph2 =
      ev (n := 4) ![pt R d 0, pt R d 2, pt R d 3] ph2 *
        ev (n := 4) ![pt R d 0, pt R d 1, G.add (pt R d 2) (pt R d 3)] ph2

  cocycleRight_comm : ev (n := 3) ![pt R d 0, pt R d 2, pt R d 1] ph2 = ph2

  interchange :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 2] ph1 * ev (n := 4) ![pt R d 0, pt R d 1, pt R d 3] ph1 *
        ev (n := 4) ![G.add (pt R d 0) (pt R d 1), pt R d 2, pt R d 3] ph2 =
      ev (n := 4) ![pt R d 0, pt R d 2, pt R d 3] ph2 * ev (n := 4) ![pt R d 1, pt R d 2, pt R d 3] ph2 *
        ev (n := 4) ![pt R d 0, pt R d 1, G.add (pt R d 2) (pt R d 3)] ph1

  sy_inv : sy * ev (n := 2) ![pt R d 1, pt R d 0] sy = 1

  sy_law :
    ph2 * ev (n := 3) ![pt R d 0, pt R d 1] sy * ev (n := 3) ![pt R d 0, pt R d 2] sy =
      ev (n := 3) ![pt R d 0, G.add (pt R d 1) (pt R d 2)] sy * ev (n := 3) ![pt R d 1, pt R d 2, pt R d 0] ph1

  adjoint_compat_left : ∀ a : O,
    ev (n := 3) ![comp1 (A.act a) (pt R d 0), comp1 (A.act a) (pt R d 1), pt R d 2] ph1 *
        ev (n := 3) ![G.add (pt R d 0) (pt R d 1), pt R d 2] (ad a) =
      ev (n := 3) ![pt R d 0, pt R d 2] (ad a) * ev (n := 3) ![pt R d 1, pt R d 2] (ad a) *
        ev (n := 3) ![pt R d 0, pt R d 1, comp1 (A.act (star a)) (pt R d 2)] ph1

  adjoint_compat_right : ∀ a : O,
    ev (n := 3) ![comp1 (A.act a) (pt R d 0), pt R d 1, pt R d 2] ph2 *
        ev (n := 3) ![pt R d 0, G.add (pt R d 1) (pt R d 2)] (ad a) =
      ev (n := 3) ![pt R d 0, pt R d 1] (ad a) * ev (n := 3) ![pt R d 0, pt R d 2] (ad a) *
        ev (n := 3) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1),
          comp1 (A.act (star a)) (pt R d 2)] ph2
  ad_one : ad 1 = 1

  ad_mul : ∀ a b : O, ad (a * b) =
    ev (n := 2) ![comp1 (A.act b) (pt R d 0), pt R d 1] (ad a) *
      ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1)] (ad b)

  ad_add : ∀ a b : O,
    ev (n := 2) ![comp1 (A.act a) (pt R d 0), comp1 (A.act b) (pt R d 0), pt R d 1] ph1 * ad (a + b) =
      ad a * ad b *
        ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1), comp1 (A.act (star b)) (pt R d 1)] ph2

  ad_sy : ∀ a : O,
    ad a * ev (n := 2) ![pt R d 1, pt R d 0] (ad (star a)) *
        ev (n := 2) ![comp1 (A.act a) (pt R d 0), pt R d 1] sy =
      ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1)] sy

def mkFB [StarRing O] (G : FGLaw R d) (A : Germ.OAct O G) (ph1 ph2 : PS R 3 d) (sy : PS R 2 d)
    (ad : O → PS R 2 d) (ha : AxesOK ph1 ph2 sy ad) (hr : FBRest G A ph1 ph2 sy ad) : Germ.FB R d O :=
  { G := G, A := A, ph1 := ph1, ph2 := ph2, sy := sy, ad := ad,
    cocycleLeft_zero_fst := ha.cocycleLeft_zero_fst, cocycleLeft_zero_snd := ha.cocycleLeft_zero_snd, cocycleLeft_zero_thd := ha.cocycleLeft_zero_thd,
    cocycleRight_zero_fst := ha.cocycleRight_zero_fst, cocycleRight_zero_snd := ha.cocycleRight_zero_snd, cocycleRight_zero_thd := ha.cocycleRight_zero_thd,
    symmetry_zero_fst := ha.symmetry_zero_fst, symmetry_zero_snd := ha.symmetry_zero_snd, adjoint_zero_fst := hr.adjoint_zero_fst, adjoint_zero_snd := hr.adjoint_zero_snd,
    cocycleLeft_assoc := hr.cocycleLeft_assoc, cocycleLeft_comm := hr.cocycleLeft_comm, cocycleRight_assoc := hr.cocycleRight_assoc, cocycleRight_comm := hr.cocycleRight_comm,
    interchange := hr.interchange, sy_inv := hr.sy_inv, sy_law := hr.sy_law, adjoint_compat_left := hr.adjoint_compat_left,
    adjoint_compat_right := hr.adjoint_compat_right, ad_one := hr.ad_one, ad_mul := hr.ad_mul, ad_add := hr.ad_add, ad_sy := hr.ad_sy }

end Ids

def FrameSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0)
    (S : Type) [CommRing S] [IsLocalRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G)
    (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G), IsChartG t x0 d G.F A.act tg uvec x →
    ∃ (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d),
      IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e ∧ IsPrimG t wP ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e ∧
        (∀ a, MvPowerSeries.constantCoeff (ad a) = 1) ∧ Rig0G t x0 d x A.act e wP

def FBIdSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0),
    (∀ n, Function.Bijective (ReciprocityTheory.ChartRestriction.G.Out.powObj t.G n).hom.appTop.hom) → ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G)
    (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (e : ∀ m, FrTyG t x0 d x m) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d)
    (ad : 𝓞 E → PS S 2 d), IsChartG t x0 d G.F A.act tg uvec x →
    IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e → FrAxes t x0 d x e → (∀ a, MvPowerSeries.constantCoeff (ad a) = 1) →
      AxesOK ph1 ph2 sy ad ∧ FBRest G A ph1 ph2 sy ad

def GermSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0)
    (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d)
    (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t), IsChartG t x0 d F act tg uvec x →
    IsFrameG t x0 d x F act ph1 ph2 sy ad e → IsPrimG t wP → FrTrunc t x0 d x e →
    ∀ (k : ℕ) (Fs : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))), ∃ f, IsGermG t x0 d x act e wP k Fs f

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace BidegreeTwoJet

section Jets

variable {V : Type} [CommRing V] {G' G : Over (Sp V)} [GrpObj G'] [GrpObj G] {n d : ℕ}

def zV (pG : IsPowGrp G' G n) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (m : ℕ) : jOG (𝟙 (Sp V)) d m n ⟶ G' :=
  pG.lim.lift (Fan.mk _ fun i => homAt (𝟙 (Sp V)) (jetCopy (S := V) d m i) ≫ xT m)

end Jets

section Coord

variable {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D' : DegData V I}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' G : Over (Sp V)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  {n d : ℕ}

end Coord


end BidegreeTwoJet
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

section Jet

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')

theorem orig_pow_le_comap (κ : Type) (m : ℕ) :
    orig S κ ^ (m + 1) ≤ (orig S' κ ^ (m + 1)).comap (MvPolynomial.map ψ) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, orig, Ideal.map_span, ← Set.range_comp]
  apply le_of_eq
  congr 2
  ext i
  simp

def jetBC (κ : Type) (m : ℕ) : Jet S κ m →+* Jet S' κ m :=
  Ideal.quotientMap _ (MvPolynomial.map ψ) (orig_pow_le_comap ψ κ m)

theorem jetBC_algebraMap (κ : Type) (m : ℕ) (s : S) :
    jetBC ψ κ m (algebraMap S (Jet S κ m) s) = algebraMap S' (Jet S' κ m) (ψ s) := by
  simp [jetBC, MvPolynomial.algebraMap_eq]
  rfl

end Jet

section Over

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)

def rjBC (d m n : ℕ) : rjO (spMap ψ ≫ x0) d m n ⟶ rjO x0 d m n :=
  Over.homMk (spMap (jetBC ψ (Fin n × Fin d) m)) (by
    dsimp
    simp only [spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext s
    exact jetBC_algebraMap ψ _ m s)

def ptBC : ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap ψ) rfl

end Over

def RawBCSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S S' : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] [CommRing S'] [Algebra c.F S'] [Algebra ℚ S']
    (ψ : S →ₐ[c.F] S') (x0 : Sp S ⟶ Xo.X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (C : RChartAt Xo c x0 u),
    ∃ (B' : Germ.FB S' C.d (𝓞 E)) (x' : ∀ m, rjO (spMap (ψ : S →+* S') ≫ x0) C.d m 1 ⟶ Xo.univ.t.G)
      (e' : ∀ m, RFrTy (spMap (ψ : S →+* S') ≫ x0) C.d x' m),
      (∀ m, x' m = rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m) ∧
      (∀ i, B'.G.F i = MvPowerSeries.map (ψ : S →+* S') (C.B.G.F i)) ∧
      (∀ a i, B'.A.act a i = MvPowerSeries.map (ψ : S →+* S') (C.B.A.act a i)) ∧
      B'.ph1 = MvPowerSeries.map (ψ : S →+* S') C.B.ph1 ∧ B'.ph2 = MvPowerSeries.map (ψ : S →+* S') C.B.ph2 ∧
      B'.sy = MvPowerSeries.map (ψ : S →+* S') C.B.sy ∧
      (∀ a, B'.ad a = MvPowerSeries.map (ψ : S →+* S') (C.B.ad a)) ∧
      RIsChart (spMap (ψ : S →+* S') ≫ x0) (fun τ i => spMap (dualMap (ψ : S →+* S')) ≫ u τ i) C.d B'.G.F B'.A.act
        (fun ℓ j => ψ (C.uvec ℓ j)) x' ∧
      RIsFrame (spMap (ψ : S →+* S') ≫ x0) C.d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' ∧
      B'.IsCanonGauge S' (MvPowerSeries.map (ψ : S →+* S') C.h) ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (reL (spMap (ψ : S →+* S') ≫ x0) C.d x' B'.A.act e' C.wP 0)
          (homAt (spMap (ψ : S →+* S') ≫ x0) (jetAug : Jet S' (Fin 1 × Fin C.d) 0 →ₐ[S'] S')).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt (spMap (ψ : S →+* S') ≫ x0) S') 1) ∧
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo x0)))
        (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo (spMap (ψ : S →+* S') ≫ x0))))
        (f : MvPowerSeries (Fin 1 × Fin C.d) S),
        IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (ptBC (ψ : S →+* S') x0 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' →
        RIsGerm x0 C.d C.x C.B.A.act C.e C.wP k F f →
        RIsGerm (spMap (ψ : S →+* S') ≫ x0) C.d x' B'.A.act e' C.wP k F' (MvPowerSeries.map (ψ : S →+* S') f)

def NabMapSt : Prop :=
  ∀ (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] (ψ : S →+* S') (d : ℕ)
    (O : Type) [CommRing O] [StarRing O] (B : Germ.FB S d O) (B' : Germ.FB S' d O),
    (∀ i, B'.G.F i = MvPowerSeries.map ψ (B.G.F i)) →
    (∀ a i, B'.A.act a i = MvPowerSeries.map ψ (B.A.act a i)) →
    ∀ (h : Germ.PS S 2 d), B.IsCanonGauge S h →
    ∀ (w0 : O) (m : ℕ) (f : Germ.PS S 1 d) (κ : Type) [Fintype κ] (u : κ → Fin d → S) (P : MvPolynomial κ S),
      B'.nabVal S' (MvPowerSeries.map ψ h) w0 m (MvPowerSeries.map ψ f) (fun l j => ψ (u l j)) (MvPolynomial.map ψ P) =
        ψ (B.nabVal S h w0 m f u P)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

def JetD {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (e : ∀ m, FrTy y d x m) (wP : PrimTy H Xo) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (D : ℕ) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    Prop :=
  ∃ (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y d D 1)))
    (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x D).left) fun _ => (k : ℤ))),
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y d D 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y d x act e wP D) k) ∧
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (x D) τ (toΓ _ (psJet D f))

def OrdStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (ch : ChartAt Xo c y)
      (k n D : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
      (f : Fin n → MvPowerSeries (Fin 1 × Fin ch.d) S),
      (∀ b, JetD y ch.d ch.x ch.B.A.act ch.e ch.wP k (F b) D (f b)) →
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
        (∀ m ∈ P.support, m.degree ≤ D) →
        chartVal ch k f P = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y k (F b) (colOf m b)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def ChartIndepSt2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C C' : ChartAt Xo c y) (k n : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S),
    (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) →
    (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      chartVal C k f P = chartVal C' k f' P

theorem thExprUniq_of_chartIndep2 (hC : ChartIndepSt2) : ThExprUniqSt := by
  intro E _ _ _ H Dw l Xo c _ nab₁ nab₂ h₁ h₂ S _ _ _ y k n F a P hP
  obtain ⟨C₁, hex₁, hpin₁⟩ := h₁.2 S y
  obtain ⟨C₂, hex₂, hpin₂⟩ := h₂.2 S y
  choose f₁ hf₁ using fun b => hex₁ k (F b)
  choose f₂ hf₂ using fun b => hex₂ k (F b)
  have e₁ : ∀ m, ∏ b, nab₁ y k (F b) (colOf m b) =
      ∏ b, C₁.B.nabVal S C₁.h H.w0 k (f₁ b) C₁.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₁ k (F b) (f₁ b) (hf₁ b) (colOf m b)
  have e₂ : ∀ m, ∏ b, nab₂ y k (F b) (colOf m b) =
      ∏ b, C₂.B.nabVal S C₂.h H.w0 k (f₂ b) C₂.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₂ k (F b) (f₂ b) (hf₂ b) (colOf m b)
  have h := hC E H Dw l Xo c h₁.1 S y C₁ C₂ k n F f₁ f₂ hf₁ hf₂ a P hP
  simp only [chartVal] at h
  simp only [e₁, e₂]
  exact h

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

def GramFormPhiStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) → (∃ z : E, cj z ≠ z) →
    ∀ (w₀ : 𝓞 E), (w₀ : E) + cj w₀ = 1 →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (β : SymB cj Y),
      (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
        (Matrix.of fun i j => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b i) (b j)).PosDef) →
      ∃ b : Module.Basis (Fin (Module.finrank ℤ Y)) ℤ Y,
        (∀ j, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b j) (b j) / 2 ≤
          (|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
              (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 3 * phiC cj β) ∧
        ∀ j (z : Y), |(β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b j) z| ≤
          2 * Real.sqrt (Module.finrank ℤ Y) * ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) z z / 2)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
