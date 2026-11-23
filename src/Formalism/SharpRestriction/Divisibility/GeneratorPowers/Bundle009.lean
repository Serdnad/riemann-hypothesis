module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S]

def compL {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (g : MvPowerSeries (Fin 1 × Fin d) S) :
    MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  MvPowerSeries.subst (fun p : Fin 1 × Fin d => φ p.2) g

def atPt {n : ℕ} (b : Fin n) (g : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) :
    MvPowerSeries (Fin n × Fin (dL Dw)) S :=
  MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) => (MvPowerSeries.X (b, q.2) : MvPowerSeries (Fin n × Fin (dL Dw)) S)) g

structure IsExpOf {d : ℕ} (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) : Prop where
  const : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0
  lin : ∀ ℓ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1) (φ j) = uvec ℓ j
  hom : ∀ j, MvPowerSeries.subst (fun p : Fin 2 × Fin d => atPt p.1 (φ p.2)) (F j) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) (φ j)

variable [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]

def jφ {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m :=
  jetSubstPS (fun p : Fin 1 × Fin d => φ p.2)

def xExp (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    jO y (dL Dw) m 1 ⟶ Xo.univ.t.G :=
  homAt y.x (jφ φ m) ≫ C.x m

def FrTruncC (y : FrPt Xo c S) (C : ChartAt Xo c y) : Prop :=
  ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
      (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
    (C.e m)

def IsExpGaugeOf (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (e : ∀ m, ExpFr y (xExp y C φ) m) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
    (u : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m)
      (scaleGen _ _ (unitΓ u) (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act C.e C.wP m)
        (homAt y.x (jφ φ m)).left))

end Defs

def ExpChartOfSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y),
    ∃ φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S, IsExpOf C.B.G.F C.uvec φ ∧ IsExpChart y (xExp y C φ)

def ExpGaugeOfSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y), FrTruncC y C →
    ∀ (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
      ∃ e : ∀ m, ExpFr y (xExp y C φ) m, IsExpGauge y (xExp y C φ) e ∧ IsExpGaugeOf y C φ e

def TieSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ →
    ∀ e : ∀ m, ExpFr y (xExp y C φ) m, IsExpGaugeOf y C φ e →
    ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
      (f : MvPowerSeries (Fin 1 × Fin C.d) S), IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
      ∃ g : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, IsExpGerm y (xExp y C φ) e k F g ∧
        ∀ α : Lt1 Dw →₀ ℕ, C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1) = expVal g α

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def GaugeUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S)
    (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G), IsExpChart y x →
    ∀ e e' : ∀ m, ExpFr y x m, IsExpGauge y x e → IsExpGauge y x e' →
    ∃ q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, MvPowerSeries.constantCoeff q = 0 ∧
      (∀ m, MvPowerSeries.coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ ℓ ℓ' : Lt1 Dw, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 +
          Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1) q ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
        (f f' : MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
        IsExpGerm y x e k F f → IsExpGerm y x e' k F f' →
          f' = f * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (FGLaw)

def ChartDataGSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0)
    (S : Type) [CommRing S] [IsLocalRing S] (x0 : Sp S ⟶ X0) {κ : Type} [Fintype κ]
    (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)),
    (∀ ℓ, IsTanAtG t x0 (tg ℓ)) →
    (∀ w, IsTanAtG t x0 w →
      ∃! a : κ → S, IsCombAtG t x0 (m := Fintype.card κ)
        (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w) →
    ∃ (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G),
      d = Fintype.card κ ∧ (∀ ℓ (j : Fin d), uvec ℓ j = if (j : ℕ) = (Fintype.equivFin κ ℓ : ℕ) then 1 else 0) ∧
      IsChartG t x0 d G.F A.act tg uvec x

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem res_top_mul {U V : Y.Opens} (hV : V ≤ U) (a : Γ(Y, ⊤)ˣ) (x : Γ(Y, U)ˣ) :
    res hV (res le_top a * x) = res le_top a * res hV x := by
  rw [map_mul, DVR.res_res']

theorem pull_top_res (h : Z ⟶ Y) {U : Y.Opens} {W : Z.Opens} (hW : W ≤ h ⁻¹ᵁ U) (a : Γ(Y, ⊤)ˣ) :
    res hW (pullU h U (res le_top a)) = res le_top (Units.map h.appTop.hom.toMonoidHom a) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  erw [Scheme.Hom.appLE_map]

theorem scaleGenG_one (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε 1 g = g := by
  cases g
  simp only [scaleGenG, map_one, one_mul]

theorem pullGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (h : Z ⟶ Y) :
    LB.pullGen t.PP.L φ ε (scaleGenG t φ ε v g) h =
      scaleGenG t (fun k => h ≫ φ k) ε (Units.map h.appTop.hom.toMonoidHom v) (LB.pullGen t.PP.L φ ε g h) := by
  unfold LB.pullGen scaleGenG
  congr 1
  funext j
  erw [map_mul, map_mul, pull_top_res]

theorem mulGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (φ' : K' → (Y ⟶ t.G.left)) (ε' : K' → ℤ)
    (v v' : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb t.PP.L φ' ε')) :
    LB.mulGen t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v' g') =
      scaleGenG t _ _ (v * v') (LB.mulGen t.PP.L φ ε φ' ε' g g') := by
  unfold LB.mulGen scaleGenG
  congr 1
  funext j
  erw [res_top_mul, res_top_mul, map_mul, mul_mul_mul_comm]
  rfl

theorem invGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    LB.invGen t.PP.L φ ε (scaleGenG t φ ε v g) = scaleGenG t φ _ v⁻¹ (LB.invGen t.PP.L φ ε g) := by
  unfold LB.invGen scaleGenG
  congr 1
  funext j
  erw [map_inv, mul_inv_rev, mul_comm]
  rfl

theorem corr_scaleGenG {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ t.G.left)} {ε' : K' → ℤ}
    {g : LB.Gen (LB.LinComb t.PP.L φ ε)} {g' : LB.Gen (LB.LinComb t.PP.L φ' ε')}
    (hc : LB.Gen.Corr t.PP.L φ ε φ' ε' g g') (v : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v g') := by
  intro j j' hj hj' hm
  have e := hc j j' hj hj' hm
  unfold scaleGenG
  dsimp only
  erw [res_top_mul, res_top_mul, e]

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem unitΓ_homAt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B)
    (u : Aˣ) :
    Units.map (Formalism.L2.Pj.homAt x0 f).left.appTop.hom.toMonoidHom (unitΓ u) =
      unitΓ (Units.map f.toMonoidHom u) := by
  ext
  simp only [unitΓ, toΓ, Formalism.L2.Pj.homAt, Over.homMk_left, spMap, Units.coe_map,
    MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem act_zero : Xo.univ.t.act.act 0 = 1 := by
  have h := Xo.univ.t.act.add 0 0
  rw [add_zero] at h
  first
    | exact mul_eq_left.mp h.symm
    | exact mul_right_eq_self.mp h.symm
    | exact self_eq_mul_right.mp h
    | simpa using h

private theorem comp_psum_lemma {T T' : Over Xo.X} (f : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ Xo.univ.t.G))
    (S : Finset (Fin n)) :
    f ≫ psum Xo.univ.t.G xs S = psum Xo.univ.t.G (fun i => f ≫ xs i) S := by
  unfold psum
  generalize (List.finRange n).filter (· ∈ S) = L
  induction L with
  | nil =>
    simp only [List.foldr_nil, pzero]
    first
      | simp
      | rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit]
  | cons k L ih =>
    simp only [List.foldr_cons]
    rw [← ih]
    simp only [padd]
    first
      | rw [CartesianMonoidalCategory.comp_lift_assoc]
      | simp

theorem comp_cφ {T T' : Over Xo.X} (f : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ Xo.univ.t.G)) (I : ULift (Finset (Fin n))) :
    f.left ≫ cφ xs I = cφ (fun i => f ≫ xs i) I := by
  simp only [cφ]
  rw [← Over.comp_left, comp_psum_lemma]

theorem comp_thφ {T T' : Over Xo.X} (f : T' ⟶ T) (xs : Fin 3 → (T ⟶ Xo.univ.t.G)) (I : thK) :
    f.left ≫ thφ Xo.univ.t.G xs I = thφ Xo.univ.t.G (fun i => f ≫ xs i) I := by
  simp only [thφ]
  rw [← Over.comp_left, comp_psum_lemma]

private theorem padd_eq_lemma_2 {T : Over Xo.X} (a b : T ⟶ Xo.univ.t.G) :
    padd Xo.univ.t.G a b = a * b := rfl

private theorem pzero_eq_lemma_3 (T : Over Xo.X) : pzero Xo.univ.t.G T = 1 := rfl



theorem prod_cφ2 {T : Over Xo.X} {U : Type} [CommGroup U] (h : (T.left ⟶ Xo.univ.t.G.left) → U)
    (xs : Fin 2 → (T ⟶ Xo.univ.t.G)) :
    ∏ I : ULift (Finset (Fin 2)), h (cφ xs I) ^ cε 2 I =
      h (1 : T ⟶ Xo.univ.t.G).left * (h (xs 0 * 1).left)⁻¹ * (h (xs 1 * 1).left)⁻¹ * h (xs 0 * (xs 1 * 1)).left := by
  have hsum : ∀ F : ULift (Finset (Fin 2)) → U,
      ∏ I : ULift (Finset (Fin 2)), F I = ∏ s : Finset (Fin 2), F (ULift.up s) :=
    fun F => Fintype.prod_equiv Equiv.ulift _ _ (fun _ => rfl)
  have hU : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have f0 : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  have f1 : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  have f2 : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  have f3 : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  have c3 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  rw [hsum, hU, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [cφ, cε, psum, f0, f1, f2, f3, c3, List.foldr_cons, List.foldr_nil, padd_eq_lemma_2,
    pzero_eq_lemma_3, Finset.card_empty, Finset.card_singleton]
  clear hsum hU f0 f1 f2 f3 c3
  try norm_num only
  try simp only [zpow_one, zpow_neg, zpow_neg_one]
  rw [mul_assoc (h (Over.Hom.left (1 : T ⟶ Xo.univ.t.G))),
    mul_assoc (h (Over.Hom.left (1 : T ⟶ Xo.univ.t.G))), mul_assoc (h (xs 0 * 1).left)⁻¹]



theorem cocycle_product_three {T : Over Xo.X} {U : Type} [CommGroup U] (h : (T.left ⟶ Xo.univ.t.G.left) → U)
    (xs : Fin 3 → (T ⟶ Xo.univ.t.G)) :
    ∏ I : thK, h (thφ Xo.univ.t.G xs I) ^ thε I =
      (h (1 : T ⟶ Xo.univ.t.G).left)⁻¹ * h (xs 0 * 1).left * h (xs 1 * 1).left * h (xs 2 * 1).left *
        (h (xs 0 * (xs 1 * 1)).left)⁻¹ * (h (xs 0 * (xs 2 * 1)).left)⁻¹ * (h (xs 1 * (xs 2 * 1)).left)⁻¹ *
          h (xs 0 * (xs 1 * (xs 2 * 1))).left := by
  have hsum : ∀ F : thK → U, ∏ I : thK, F I = ∏ s : Finset (Fin 3), F (ULift.up s) :=
    fun F => Fintype.prod_equiv (Equiv.ulift : thK ≃ Finset (Fin 3)) _ _ (fun _ => rfl)
  have hU : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have f0 : (List.finRange 3).filter (· ∈ (∅ : Finset (Fin 3))) = [] := by decide
  have f1 : (List.finRange 3).filter (· ∈ ({0} : Finset (Fin 3))) = [0] := by decide
  have f2 : (List.finRange 3).filter (· ∈ ({1} : Finset (Fin 3))) = [1] := by decide
  have f3 : (List.finRange 3).filter (· ∈ ({2} : Finset (Fin 3))) = [2] := by decide
  have f4 : (List.finRange 3).filter (· ∈ ({0, 1} : Finset (Fin 3))) = [0, 1] := by decide
  have f5 : (List.finRange 3).filter (· ∈ ({0, 2} : Finset (Fin 3))) = [0, 2] := by decide
  have f6 : (List.finRange 3).filter (· ∈ ({1, 2} : Finset (Fin 3))) = [1, 2] := by decide
  have f7 : (List.finRange 3).filter (· ∈ ({0, 1, 2} : Finset (Fin 3))) = [0, 1, 2] := by decide
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  rw [hsum, hU, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [thφ, thε, psum, f0, f1, f2, f3, f4, f5, f6, f7, c4, c5, c6, c7, List.foldr_cons,
    List.foldr_nil, padd_eq_lemma_2, pzero_eq_lemma_3, Finset.card_empty, Finset.card_singleton]
  clear hsum hU f0 f1 f2 f3 f4 f5 f6 f7 c4 c5 c6 c7
  try norm_num only
  try simp only [zpow_one, zpow_neg, zpow_neg_one]
  repeat rw [mul_assoc (h (1 : T ⟶ Xo.univ.t.G).left)⁻¹]
  repeat rw [mul_assoc (h (xs 0 * 1).left)]
  repeat rw [mul_assoc (h (xs 1 * 1).left)]
  repeat rw [mul_assoc (h (xs 2 * 1).left)]
  repeat rw [mul_assoc (h (xs 0 * (xs 1 * 1)).left)⁻¹]
  repeat rw [mul_assoc (h (xs 0 * (xs 2 * 1)).left)⁻¹]
  all_goals exact (rfl : (0 : ℕ) = 0)

abbrev AdTy (Xo : Moduli Dw l) (a : 𝓞 E) : Type :=
  LB.Gen (LB.LinComb Xo.univ.t.PP.L
    (Sum.elim (cφ ![fst Xo.univ.t.G Xo.univ.t.G, snd Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act (H.bar a)])
      (cφ ![fst Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act a, snd Xo.univ.t.G Xo.univ.t.G]))
    (Sum.elim (cε 2) fun I => -cε 2 I))

abbrev wPc (wP : PrimTy H Xo) (c : 𝓞 E) :=
  LB.pullGen Xo.univ.t.PP.L _ _ wP (Xo.univ.t.act.act c).left

abbrev cubAt (p q r : Xo.univ.t.G ⟶ Xo.univ.t.G) :=
  LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift p (lift q r)).left

def Bq (wP : PrimTy H Xo) (a : 𝓞 E) (wLa : AdTy Xo a) (wLb : AdTy Xo (H.bar a)) :=
  let A := Xo.univ.t.act.act
  let b := a * H.bar a
  LB.mulGen Xo.univ.t.PP.L _ _ _ _
    (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (wPc wP (1 + b))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP a))
          (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP a))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ wP)
        (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP b))))
    (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (cubAt (A 1) (A b) (A ((1 + b) * H.w0)))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (cubAt (A H.w0) (A (b * H.w0)) (A 1))
          (cubAt (A H.w0) (A (b * H.w0)) (A b))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wLa (lift (A 1) (A (a * H.w0))).left)
        (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wLb (lift (A a) (A H.w0)).left))))

theorem Bq_isGen (wP : PrimTy H Xo) (hwP : wP.IsGen) (a : 𝓞 E) (wLa : AdTy Xo a) (hwa : wLa.IsGen)
    (wLb : AdTy Xo (H.bar a)) (hwb : wLb.IsGen) : (Bq wP a wLa wLb).IsGen := by
  have hP := fun c => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ wP hwP (Xo.univ.t.act.act c).left
  have hC := fun (p q r : Xo.univ.t.G ⟶ Xo.univ.t.G) =>
    ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ _ Xo.univ.t.cub.isGen (lift p (lift q r)).left
  unfold Bq
  refine ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hP _)
        (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))
          (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))))
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ hwP)
        (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))))
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hC _ _ _)
        (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hC _ _ _) (hC _ _ _)))
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
        (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hwa _)
        (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hwb _))))

theorem exists_betaRaw (wP : PrimTy H Xo) (hwP : wP.IsGen) (a : 𝓞 E) (hbb : H.bar (H.bar a) = a)
    (wLa : AdTy Xo a) (hwa : wLa.IsGen) (wLb : AdTy Xo (H.bar a)) (hwb : wLb.IsGen) :
    ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (Bq wP a wLa wLb) r z J := by
  have hL := Xo.univ.t.PP.isLB
  refine exists_gen hL ?_ _ (Bq_isGen wP hwP a wLa hwa wLb hwb)
  intro U _ hU
  unfold betaφ betaε
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Fin.prod_univ_four,
    comp_cφ, comp_thφ, Category.comp_id, zpow_neg, zpow_one, neg_neg, Finset.prod_inv_distrib, prod_cφ2, cocycle_product_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, x3, lift_fst, lift_snd_assoc, lift_snd, lift_fst_assoc, Category.id_comp]
  have h1 : ∀ p q : 𝓞 E, Xo.univ.t.act.act p * Xo.univ.t.act.act q = Xo.univ.t.act.act (p + q) :=
    fun p q => (Xo.univ.t.act.add p q).symm
  have h2 : ∀ p q : 𝓞 E, Xo.univ.t.act.act p ≫ Xo.univ.t.act.act q = Xo.univ.t.act.act (p * q) :=
    fun p q => (Xo.univ.t.act.mul p q).symm
  have h3 : (1 : Xo.univ.t.G ⟶ Xo.univ.t.G) = Xo.univ.t.act.act 0 := act_zero.symm
  have h4 : 𝟙 Xo.univ.t.G = Xo.univ.t.act.act 1 := Xo.univ.t.act.one.symm
  have h5 : 𝟙 Xo.univ.t.G.left = (Xo.univ.t.act.act 1).left := by rw [Xo.univ.t.act.one]; rfl
  simp only [h3, h1, h2, hbb, h4, h5]
  ring_nf
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  abel

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
end
end
