module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Mathlib.RingTheory.LaurentSeries
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

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

section ChartG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)

abbrev jOG (m n : ℕ) : Over X0 := overAt x0 (Jet S (Fin n × Fin d) m)

abbrev tEpsG : Over X0 := Over.mk (spMap (algebraMap S (DualNumber S)) ≫ x0)

def IsTanAtG (v : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  v ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x0 ∧
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v = (1 : Over.mk x0 ⟶ t.G).left

def IsCombAtG {m : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S)
    (w : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  ∃ u : Fin m → (tEpsG x0 ⟶ t.G), (∀ i, (u i).left = spMap (epsMul (cf i)) ≫ v i) ∧
    ((List.ofFn u).prod).left = w

def jptG (x : ∀ m, jOG x0 d m 1 ⟶ t.G) {n : ℕ} (m : ℕ) (i : Fin n) : jOG x0 d m n ⟶ t.G :=
  homAt x0 (jetCopy d m i) ≫ x m

structure IsChartG {κ : Type} [Fintype κ] (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) : Prop where
  zero : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ x (m + 1) = x m
  law : ∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m =
    jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)
  act : ∀ m (a : 𝓞 E), x m ≫ t.act.act a =
    homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act a p.2)) ≫ x m
  tan : ∀ ℓ : κ, IsCombAtG t x0
    (fun j : Fin d => (homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left) (uvec ℓ)
    (tg ℓ)

  basis : ∀ v : Fin d → S, ∃! a : κ → S, ∀ j, ∑ ℓ, a ℓ * uvec ℓ j = v j

end ChartG

section FrameG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

def cφG {T : Over X0} {n : ℕ} (xs : Fin n → (T ⟶ t.G)) :
    ULift (Finset (Fin n)) → (T.left ⟶ t.G.left) :=
  fun I => (psum t.G xs I.down).left

def scaleGenG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    LB.Gen (LB.LinComb t.PP.L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩

def genPowG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (k : ℕ) :
    LB.Gen (LB.LinComb t.PP.L φ fun i => (k : ℤ) * ε i) :=
  ⟨fun j => g.s j ^ k⟩

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
variable (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

abbrev FrTyG (m : ℕ) : Type :=
  LB.Gen (cubeLB t.G ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] t.PP.L)

def peG (e : ∀ m, FrTyG t x0 d x m) (m : ℕ) {n' : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S) :=
  LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left

structure IsFrameG (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) : Prop where
  gen : ∀ m, (e m).IsGen
  ph1 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  ph2 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  sy : ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (e m)
      (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))
  ad : ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
      LB.Gen.Corr t.PP.L _ _ _ _
        (LB.mulGen t.PP.L _ _ _ _
          (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
          (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)]))
        (scaleGenG t _ _ (unitΓ u)
          (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))

end FrameG

section GermG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
variable (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def jBaseG (m n : ℕ) : jOG x0 d m n ⟶ Over.mk x0 :=
  Over.homMk (spMap (algebraMap S (Jet S (Fin n × Fin d) m))) rfl

abbrev PrimTyG : Type :=
  LB.Gen (LB.LinComb t.PP.L
    (Sum.elim (fun _ : Fin 1 => 𝟙 t.G.left) (cφG t ![𝟙 t.G, t.act.act H.w0]))
    (Sum.elim (fun _ => 1) fun I => -cε 2 I))

def IsPrimG (wP : PrimTyG t) : Prop :=
  wP.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _
    (LB.pullGen t.PP.L _ _ wP (eSec t.G)) t.PP.rig

def eLG (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t)
    (m : ℕ) :=
  LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wP (x m).left)
    (peG t x0 d x e m ![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)])

def IsGermG (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTyG t x0 d x m)
    (wP : PrimTyG t) (k : ℕ)
    (F : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    Prop :=
  ∀ m, ∃ (F' : LB.Sec (LPow t.G t.PP.L k (jOG x0 d m 1)))
    (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
    IsPullSec t.G t.PP.L k (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr t.PP.L _ _ _ _ τ (genPowG t _ _ (eLG t x0 d x act e wP m) k) ∧
    IsValueAt t.G t.PP.L k F' (x m) τ (toΓ _ (psJet m f))

end GermG

section Link

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)

theorem isChart_iff (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) :
    IsChart y d F act uvec x ↔ IsChartG Xo.univ.t y.x d F act (fun ℓ => y.u ℓ.1 ℓ.2) uvec x :=
  ⟨fun h => ⟨h.zero, h.trunc, h.law, h.act, h.tan, h.basis⟩,
    fun h => ⟨h.zero, h.trunc, h.law, h.act, h.tan, h.basis⟩⟩



theorem isFrame_iff (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTy y d x m) :
    IsFrame y d x F act ph1 ph2 sy ad e ↔ IsFrameG Xo.univ.t y.x d x F act ph1 ph2 sy ad e :=
  ⟨fun h => ⟨h.gen, h.ph1, h.ph2, h.sy, h.ad⟩, fun h => ⟨h.gen, h.ph1, h.ph2, h.sy, h.ad⟩⟩

theorem isPrim_iff (wP : PrimTy H Xo) : IsPrim wP ↔ IsPrimG Xo.univ.t wP := Iff.rfl



theorem isGerm_iff (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTy y d x m) (wP : PrimTy H Xo)
    (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f : MvPowerSeries (Fin 1 × Fin d) S) :
    IsGerm y d x act e wP k F f ↔ IsGermG Xo.univ.t y.x d x act e wP k F f := Iff.rfl

end Link

end Formalism.L2.Pj
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

section Exp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

abbrev dL (Dw : Datum H) : ℕ := Fintype.card (Lt1 Dw)

def ltIdx (Dw : Datum H) : Lt1 Dw ≃ Fin (dL Dw) := Fintype.equivFin _

def addP {S : Type} [CommRing S] : Fin 1 × Fin (dL Dw) → MvPolynomial (Fin 2 × Fin (dL Dw)) S :=
  fun p => X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2)

def actP {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S] (a : 𝓞 E) :
    Fin 1 × Fin (dL Dw) → MvPolynomial (Fin 1 × Fin (dL Dw)) S :=
  fun p => C (algebraMap c.F S (embK c ((ltIdx Dw).symm p.2).1 a)) * X p

variable {S : Type} [CommRing S] [Algebra c.F S]

variable (y : FrPt Xo c S)

structure IsExpChart (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G) : Prop where
  zero : ∀ m, homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m) ≫
    x (m + 1) = x m
  law : ∀ m, homAt y.x (jetSubstP m (addP (Dw := Dw) (S := S))) ≫ x m =
    jpt y (dL Dw) x m (0 : Fin 2) * jpt y (dL Dw) x m (1 : Fin 2)
  act : ∀ m (a : 𝓞 E), x m ≫ Xo.univ.t.act.act a = homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a)) ≫ x m
  tan : ∀ ℓ : Lt1 Dw, IsCombAt y.x
    (fun j : Fin (dL Dw) => (homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left)
    (fun j => if j = ltIdx Dw ℓ then 1 else 0) (y.u ℓ.1 ℓ.2)

variable (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G)

abbrev ExpFr (m : ℕ) : Type :=
  LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (1 : ℤ))

def eAt (e : ∀ m, ExpFr y x m) (m : ℕ) (a : 𝓞 E) :=
  LB.pullGen Xo.univ.t.PP.L _ _ (e m) (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left

def betaφ (a : 𝓞 E) : Fin 4 → (Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) :=
  ![(Xo.univ.t.act.act (1 + a * H.bar a)).left, (Xo.univ.t.act.act a).left, 𝟙 _,
    (Xo.univ.t.act.act (a * H.bar a)).left]

def betaε : Fin 4 → ℤ := ![1, -2, -1, -1]

structure IsExpGauge (e : ∀ m, ExpFr y x m) : Prop where
  gen : ∀ m, (e m).IsGen
  trunc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (e (m + 1))
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left)
    (e m)
  rig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (e 0) (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left)
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)
  coc : ∀ a : 𝓞 E, ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) ∧
    ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eAt y x e m (1 + a * H.bar a))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left)
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eAt y x e m a) 2)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (e m) (eAt y x e m (a * H.bar a)))))

def IsExpGerm (e : ∀ m, ExpFr y x m) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) :
    Prop :=
  ∀ m, ∃ (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y (dL Dw) m 1)))
    (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y (dL Dw) m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (e m) k) ∧
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (x m) τ (toΓ _ (psJet m f))

end Exp

def expVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {S : Type} [CommRing S]
    (f : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (α : Lt1 Dw →₀ ℕ) : S :=
  (α.prod fun _ n => (n.factorial : S)) *
    MvPowerSeries.coeff (Finsupp.mapDomain (fun ℓ => ((0 : Fin 1), ltIdx Dw ℓ)) α) f

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev ArcLt (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ)

def arcDet (Dw : Datum H) (K₁ : Type) [Field K₁] : MvPolynomial (ArcLt Dw) (LaurentSeries K₁) :=
  ∏ τ : E →+* ℂ, Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)))

abbrev ArcS (Dw : Datum H) (K₁ : Type) [Field K₁] : Type := Localization.Away (arcDet Dw K₁)

def arcX (Dw : Datum H) (K₁ : Type) [Field K₁] (τ : E →+* ℂ) (i k : Fin (Dw.mult τ)) : ArcS Dw K₁ :=
  algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw))

def arcι (Dw : Datum H) (K₁ : Type) [Field K₁] : PowerSeries K₁ →+* ArcS Dw K₁ :=
  (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)).comp
    ((MvPolynomial.C).comp (HahnSeries.ofPowerSeries ℤ K₁))

variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsLieImage {Y : Model Xo c β} {K₁ : Type} [Field K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b}
    {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (ν : ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁)) (v : epsR (PowerSeries K₁) ⟶ W.t.G) : Prop :=
  ∀ (n : ℕ) (ρ : DualNumber (PowerSeries K₁) →+* DualNumber (PowerSeries K₁ ⧸ Ideal.span {PowerSeries.X} ^ (n + 1)))
    (κ : DualNumber K₁ →+* DualNumber (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1)))
    (vn : Sp (DualNumber (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1))) ⟶
      (ReciprocityTheory.ChartRestriction.G.Out.thickObj (PowerSeries K₁) (Ideal.span {PowerSeries.X}) n W.t.G).left),
    (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ r)) → ρ DualNumber.eps = DualNumber.eps →
    (∀ r, κ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (PowerSeries.C r))) →
    κ DualNumber.eps = DualNumber.eps →
    vn ≫ (ReciprocityTheory.ChartRestriction.G.Out.thickObj (PowerSeries K₁) (Ideal.span {PowerSeries.X}) n W.t.G).hom =
      spMap (algebraMap (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1))
        (DualNumber (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1)))) →
    vn ≫ (ReciprocityTheory.ChartRestriction.G.Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left = spMap ρ ≫ v.left →
    ∀ x, GenRelR W.w (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) vn) (LB.pullGen _ _ _ (ν.s x) (spMap κ))

def IsArcPointPowerSeries (Y : Model Xo c β) {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} (a : ArcIn Dw l β K₁ b)
    (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁))
    [Algebra c.F (ArcS Dw K₁)] (yF : FrPt Xo c (ArcS Dw K₁)) : Prop :=
  χ ≫ Y.s = spMap (PowerSeries.C (R := K₁)) ≫ spMap b ∧
  (∃ z : Sp (ArcS Dw K₁) ⟶ Xo.XF c, z ≫ Y.j = spMap (arcι Dw K₁) ≫ χ ∧ z ≫ pullback.fst _ _ = yF.x) ∧
  ∃ v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries K₁) ⟶ W.t.G),
    (∀ τ k, IsLieImage W (e τ k) (v τ k)) ∧
    ∀ τ i, ∃ vS : Fin (Dw.mult τ) → (Sp (DualNumber (ArcS Dw K₁)) ⟶ Xo.univ.t.G.left),
      (∀ k, ∃ v'' : Sp (DualNumber (ArcS Dw K₁)) ⟶ Y.oF.t.G.left,
        v'' ≫ Y.m.φ = spMap (dualMap (arcι Dw K₁)) ≫ (v τ k).left ≫ W.m.φ ∧ vS k = v'' ≫ Y.m0.toSABMap.φ) ∧
      IsCombAt yF.x vS (fun k => arcX Dw K₁ τ i k) (yF.u τ i)

def SectionOfLineBundleOne {X : Scheme.{0}} {L : LB X} (σ : ReciprocityTheory.ChartRestriction.G.Out.H0 L 1) (θ : LB.Sec L) : Prop :=
  ∀ (j : Fin 1 → L.ι) (h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0)),
    σ.f j = (X.presheaf.map (homOfLE h).op).hom (θ.f (j 0))

def IsArcPt3At (Y : Model Xo c β) {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} (a : ArcIn Dw l β K₁ b)
    (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    [Algebra c.F (ArcS Dw K₁)] (yF : FrPt Xo c (ArcS Dw K₁)) (th : a.D₀.P.L.Sec) : Prop :=
  ∃ (σ : ReciprocityTheory.ChartRestriction.G.Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x)
    (θ' : LB.Sec W.P.U.LG.L) (θ : LB.Sec W.t.PP.L),
    (∃ j, th.f j ≠ 0) ∧ (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 (show _ from σ) fam) ∧
    (∀ (j : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι) (V : W.P.D.toPre.P.A.left.Opens)
      (h₁ : V ≤ LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j)
      (h₂ : V ≤ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ W.φ ⁻¹ᵁ a.D₀.P.L.U j₀),
      LB.Coh W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j →
      (W.φ.appLE _ _ h₃).hom (th.f j₀) = resG _ h₂ (W.w.s (fun _ => j₀, j 1)).val * resG _ h₁ ((fam 0).f j)) ∧
    SectionOfLineBundleOne σ θ' ∧ HEq θ θ' ∧
    ∃ (t' : SAB H (Sp (ArcS Dw K₁))) (m1 : SABMap t' Xo.univ.t yF.x) (m2 : SABMap t' W.t (spMap (arcι Dw K₁)))
      (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (W.t.PP.L.pull m2.φ))
      (σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (W.t.PP.L.pull m2.φ)),
      (∃ g : t'.G.left ⟶ Y.oF.t.G.left, g ≫ Y.m0.toSABMap.φ = m1.φ ∧ g ≫ Y.m.φ = m2.φ ≫ W.m.φ) ∧
      RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ' s1 ∧ IsoMaps w2 σ' θ2 ∧ PullSec m2.φ θ θ2 ∧
      ∀ g : t'.G.left ⟶ Gx yF.x, g ≫ (snd (Over.mk yF.x) Xo.univ.t.G).left = m1.φ →
        g ≫ (fst (Over.mk yF.x) Xo.univ.t.G).left = t'.G.hom →
        ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx yF.x).U (fun _ => j PUnit.unit)),
          s1.f j = (g.appLE _ _ h).hom (yF.s.f (fun _ => j PUnit.unit))

def ArcLieBasis {Y : Model Xo c β} {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b}
    {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁)) : Prop :=
  ∃ v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries K₁) ⟶ W.t.G),
    (∀ τ k, IsLieImage W (e τ k) (v τ k)) ∧
    ∀ τ : E →+* ℂ,
      let eig : (epsR (PowerSeries K₁) ⟶ W.t.G) → Prop := fun w => ∀ x : 𝓞 E,
        (w ≫ W.t.act.act x).left =
          spMap (epsScaleR (PowerSeries.C (R := K₁) (algebraMap c.F K₁ (embK c τ x)))) ≫ w.left
      (∀ k, IsTangent (v τ k) ∧ eig (v τ k)) ∧
      ∀ w, IsTangent w → eig w → ∃! cf : Fin (Dw.mult τ) → PowerSeries K₁, IsLieComb cf (v τ) w

end Formalism.L2.Pj
end
end
