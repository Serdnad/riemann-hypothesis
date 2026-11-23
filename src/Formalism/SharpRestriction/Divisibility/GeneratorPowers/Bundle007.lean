module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x :=
  ReciprocityTheory.ChartRestriction.G.DVR.res_res' h1 h2 x

private theorem gs_idRes_lemma {X Y : Scheme.{0}} (h : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    (hV : W ≤ h ⁻¹ᵁ U) (y : Y) (hy : y ∈ W) (x : Γ(X, U)) :
    gs (𝟙 Y) y W ((Y.presheaf.map (homOfLE hV).op).hom ((h.app U).hom x)) = gs h y U x := by
  rw [gs_res (𝟙 Y) y hV hy, gs_pull (𝟙 Y) h y U (hV hy), Category.id_comp]

section Corr

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

theorem corr_pullGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (H : LB.Gen.Corr L φ ε φ' ε' t t')
    (h : Z ⟶ Y) : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) (LB.pullGen L φ' ε' t' h) := by
  apply ReciprocityTheory.ChartRestriction.G.DVR.corr_pullGen <;> assumption

theorem corr_refl {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) : LB.Gen.Corr L φ ε φ ε t t := by
  intro j j' _ _ hjj
  obtain rfl : j = j' := funext fun k => hjj k k rfl
  rfl

end Corr

section Xo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_scale {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ Xo.univ.t.G.left)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} {t' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')}
    (Hc : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' t t') (w : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (scaleGen φ ε w t) (scaleGen φ' ε' w t') := by
  intro j j' hj hj' hjj
  have e := Hc j j' hj hj' hjj
  have key : ∀ {U V : Y.Opens} (hle : V ≤ U) (a b : Γ(Y, U)ˣ), res hle (a * b) = res hle a * res hle b :=
    fun hle a b => map_mul _ a b
  erw [key, key, res_res', res_res', e]

theorem corr_genPow {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ Xo.univ.t.G.left)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} {t' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')}
    (Hc : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' t t') (k : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (genPow φ ε t k) (genPow φ' ε' t' k) := by
  intro j j' hj hj' hjj
  have key : ∀ {U V : Y.Opens} (hle : V ≤ U) (a : Γ(Y, U)ˣ), res hle (a ^ k) = res hle a ^ k :=
    fun hle a => map_pow _ a k
  show res _ (t.s j ^ k) = res _ (t'.s j' ^ k)
  erw [key, key]
  exact congrArg (· ^ k) (Hc j j' hj hj' hjj)

theorem genPow_scale_pull {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε))
    (h : Z ⟶ Y) (w : Γ(Z, ⊤)ˣ) (k : ℕ) :
    genPow _ _ (scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L φ ε t h)) k =
      scaleGen _ _ (w ^ k) (LB.pullGen Xo.univ.t.PP.L φ _ (genPow φ ε t k) h) := by
  simp only [genPow, scaleGen, LB.pullGen, mul_pow, map_pow]
  have hp : ∀ {U : Y.Opens} {W : Z.Opens} (hle : W ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)ˣ),
      res hle (pullU h U (x ^ k)) = res hle (pullU h U x) ^ k := fun hle x => by rw [map_pow, map_pow]
  congr 1
  funext j
  congr 1
  exact (hp _ _).symm

end Xo

section Pull

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)


theorem isPullSec_comp (a : ℤ) {T1 T2 T3 : Over S0} (h1 : T2 ⟶ T1) (h2 : T3 ⟶ T2)
    {s1 : LB.Sec (LPow A L a T1)} {s2 : LB.Sec (LPow A L a T2)} {s3 : LB.Sec (LPow A L a T3)}
    (e1 : IsPullSec A L a (h1 ▷ A) (whiskerRight_snd _ _) s1 s2)
    (e2 : IsPullSec A L a (h2 ▷ A) (whiskerRight_snd _ _) s2 s3) :
    IsPullSec A L a ((h2 ≫ h1) ▷ A) (whiskerRight_snd _ _) s1 s3 := by
  intro j
  apply fn_ext
  intro y hy
  have hy2 : (h2 ▷ A).left y ∈ (LPow A L a T2).U j :=
    chart_le_res A L (h2 ▷ A) (whiskerRight_snd _ _) a j hy
  rw [GermD.pullSec_stalk (A := A) (L := L) a e2 (𝟙 _) y j hy, Category.id_comp,
    GermD.pullSec_stalk (A := A) (L := L) a e1 (h2 ▷ A).left y j hy2,
    gs_idRes_lemma _ _ y hy, comp_whiskerRight, Over.comp_left]

theorem isPullSec_congr (a : ℤ) {T T' : Over S0} {h h' : T' ⟶ T} (e : h = h')
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (hs : IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) s s') :
    IsPullSec A L a (h' ▷ A) (whiskerRight_snd _ _) s s' := by
  subst e
  exact hs

theorem ptSecT_whisker {T T' : Over S0} (h : T' ⟶ T) (z : T ⟶ A) :
    (ptSecT A (h ≫ z)).left ≫ (h ▷ A).left = h.left ≫ (ptSecT A z).left := by
  have e : ptSecT A (h ≫ z) ≫ (h ▷ A) = h ≫ ptSecT A z := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e2 := congrArg (fun f => f.left) e
  simpa using e2

end Pull

section Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem isValueAt_pullScale (hL : Xo.univ.t.PP.L.IsLB) (a : ℤ) {T T' : Over Xo.X} (h : T' ⟶ T)
    {s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L a T)} {s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L a T')}
    (hs : IsPullSec Xo.univ.t.G Xo.univ.t.PP.L a (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) s s')
    {z : T ⟶ Xo.univ.t.G}
    {τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := T.left) (K := Fin 1) (fun _ => z.left) fun _ => a)}
    {v : Γ(T.left, ⊤)} (hv : IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s z τ v) (w : Γ(T'.left, ⊤)ˣ) :
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s' (h ≫ z)
      (scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L _ _ τ h.left))
      ((h.left.appTop).hom v * ((w⁻¹ : Γ(T'.left, ⊤)ˣ) : Γ(T'.left, ⊤))) := by
  intro j
  apply fn_ext
  intro y hy
  have hy2 : h.left y ∈ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hy3 : (ptSecT Xo.univ.t.G z).left (h.left y) ∈ (LPow Xo.univ.t.G Xo.univ.t.PP.L a T).U j :=
    val_le Xo.univ.t.G Xo.univ.t.PP.L z j hy2
  have hy1 : (ptSecT Xo.univ.t.G (h ≫ z)).left y ∈ (LPow Xo.univ.t.G Xo.univ.t.PP.L a T').U j :=
    val_le Xo.univ.t.G Xo.univ.t.PP.L (h ≫ z) j hy
  have hv' : gs h.left y ⊤ v * gs h.left y _ (τ.s j).val =
      gs (h.left ≫ (ptSecT Xo.univ.t.G z).left) y _ (s.f j) := by
    have e := congrArg (gs h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j)) (hv j)
    rw [gs_mul _ _ _ hy2, gs_res h.left y le_top hy2,
      gs_res h.left y (val_le Xo.univ.t.G Xo.univ.t.PP.L z j) hy2] at e
    exact e.symm.trans (gs_pull h.left (ptSecT Xo.univ.t.G z).left y ((LPow Xo.univ.t.G Xo.univ.t.PP.L a T).U j) hy3
      (s.f j))
  have e1 : gs (𝟙 T'.left) y ⊤ ((h.left.appTop).hom v) = gs h.left y ⊤ v := by
    have := gs_pull (𝟙 T'.left) h.left y ⊤ trivial v
    rw [Category.id_comp] at this
    exact this
  have lhs : gs (𝟙 T'.left) y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j)
      ((T'.left.presheaf.map (homOfLE (val_le Xo.univ.t.G Xo.univ.t.PP.L (h ≫ z) j)).op).hom
        (((ptSecT Xo.univ.t.G (h ≫ z)).left.app _).hom (s'.f j))) =
      gs h.left y ⊤ v * gs h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j) (τ.s j).val := by
    refine (gs_idRes_lemma _ _ y hy _).trans ?_
    refine (GermD.pullSec_stalk (A := Xo.univ.t.G) (L := Xo.univ.t.PP.L) a hs _ y j hy1).trans ?_
    rw [ptSecT_whisker Xo.univ.t.G h z]
    exact hv'.symm
  have pgle : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤
      h.left ⁻¹ᵁ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j :=
    fun _ hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have ex2 : (show Γ(T'.left, LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j) from
          ((scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L _ _ τ h.left)).s j).val) =
      (T'.left.presheaf.map (homOfLE (le_top : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤ ⊤)).op).hom
        w.val *
      (T'.left.presheaf.map (homOfLE pgle).op).hom
        ((h.left.app (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j)).hom (τ.s j).val) := rfl
  have rhs : gs (𝟙 T'.left) y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j)
      ((T'.left.presheaf.map (homOfLE (le_top : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤ ⊤)).op).hom
          ((h.left.appTop).hom v * ((w⁻¹ : Γ(T'.left, ⊤)ˣ) : Γ(T'.left, ⊤))) *
        (show Γ(T'.left, LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j) from
          ((scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L _ _ τ h.left)).s j).val)) =
      gs h.left y ⊤ v * gs h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j) (τ.s j).val := by
    rw [ex2, map_mul, gs_mul (𝟙 _) y _ hy, gs_mul (𝟙 _) y _ hy, gs_mul (𝟙 _) y _ hy,
      gs_res (𝟙 _) y le_top hy, gs_res (𝟙 _) y le_top hy, gs_res (𝟙 _) y pgle hy]
    erw [gs_pull (𝟙 _) h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j) (pgle hy)]
    rw [Category.id_comp, e1]
    erw [gs_res (𝟙 _) y (le_top : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤ ⊤) hy
      (w : Γ(T'.left, ⊤))]
    rw [gs_unit (𝟙 _) y ⊤ trivial w⁻¹, gs_unit (𝟙 _) y ⊤ trivial w, map_inv,
      mul_assoc (gs h.left y ⊤ v), Units.inv_mul_cancel_left]
  exact lhs.trans rhs.symm

end Val

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
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

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (x0 : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (d : ℕ)

abbrev rjO (m n : ℕ) : Over Xo.X := overAt x0 (Jet S (Fin n × Fin d) m)

def rjpt (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) {n : ℕ} (m : ℕ) (i : Fin n) : rjO x0 d m n ⟶ Xo.univ.t.G :=
  homAt x0 (jetCopy d m i) ≫ x m

structure RIsChart (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) : Prop where
  zero : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ x (m + 1) = x m
  law : ∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m =
    rjpt x0 d x m (0 : Fin 2) * rjpt x0 d x m (1 : Fin 2)
  act : ∀ m (a : 𝓞 E), x m ≫ Xo.univ.t.act.act a =
    homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act a p.2)) ≫ x m
  tan : ∀ ℓ : Lt1 Dw, IsCombAt x0
    (fun j : Fin d => (homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left) (uvec ℓ)
    (u ℓ.1 ℓ.2)

  basis : ∀ v : Fin d → S, ∃! a : Lt1 Dw → S, ∀ j, ∑ ℓ, a ℓ * uvec ℓ j = v j

end Chart

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

variable {S : Type} [CommRing S] [Algebra c.F S] (x0 : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (d : ℕ)
variable (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G)

abbrev RFrTy (m : ℕ) : Type :=
  LB.Gen (cubeLB Xo.univ.t.G ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)] Xo.univ.t.PP.L)

def rpe (e : ∀ m, RFrTy x0 d x m) (m : ℕ) {n' : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S) :=
  LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m)
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left

structure RIsFrame (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, RFrTy x0 d x m) : Prop where
  gen : ∀ m, (e m).IsGen
  ph1 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
        (lift (rjpt x0 d x m (0 : Fin 3)) (lift (rjpt x0 d x m (1 : Fin 3)) (rjpt x0 d x m (2 : Fin 3)))).left)
      (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (rpe x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)])
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.invGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))
          (LB.invGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  ph2 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
        (lift (rjpt x0 d x m (1 : Fin 3)) (lift (rjpt x0 d x m (2 : Fin 3)) (rjpt x0 d x m (0 : Fin 3)))).left)
      (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (rpe x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.invGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)]))
          (LB.invGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  sy : ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m)
      (scaleGen _ _ (unitΓ u⁻¹) (rpe x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))
  ad : ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb Xo.univ.t.PP.L
      (Sum.elim (cφ ![fst Xo.univ.t.G Xo.univ.t.G, snd Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act (H.bar a)])
        (cφ ![fst Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act a, snd Xo.univ.t.G Xo.univ.t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (rjpt x0 d x m (0 : Fin 2)) (rjpt x0 d x m (1 : Fin 2))).left)
          (rpe x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)]))
        (scaleGen _ _ (unitΓ u)
          (rpe x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))

end Frame

section Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (x0 : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (d : ℕ)
variable (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G)

def rjBase (m n : ℕ) : rjO x0 d m n ⟶ ptO Xo x0 :=
  Over.homMk (spMap (algebraMap S (Jet S (Fin n × Fin d) m))) rfl

def reL (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, RFrTy x0 d x m) (wP : PrimTy H Xo)
    (m : ℕ) :=
  LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wP (x m).left)
    (rpe x0 d x e m ![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)])

def RIsGerm (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, RFrTy x0 d x m)
    (wP : PrimTy H Xo) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo x0))) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    Prop :=
  ∀ m, ∃ (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (rjO x0 d m 1)))
    (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (rjBase x0 d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (reL x0 d x act e wP m) k) ∧
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (x m) τ (toΓ _ (psJet m f))

end Germ

section Pin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

structure RChartAt [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (x0 : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) where
  d : ℕ
  B : Germ.FB S d (𝓞 E)
  uvec : Lt1 Dw → Fin d → S
  x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G
  e : ∀ m, RFrTy x0 d x m
  wP : PrimTy H Xo
  h : Germ.PS S 2 d
  chart : RIsChart x0 u d B.G.F B.A.act uvec x
  frame : RIsFrame x0 d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e
  prim : IsPrim wP
  gauge : B.IsCanonGauge S h

  rig0 : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (reL x0 d x B.A.act e wP 0)
      (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left)
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt x0 S) 1)

end Pin

section ToRaw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def ChartAt.toRaw [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
    (C : ChartAt Xo c y) : RChartAt Xo c y.x y.u :=
  ⟨C.d, C.B, C.uvec, C.x, C.e, C.wP, C.h,
    ⟨C.chart.zero, C.chart.trunc, C.chart.law, C.chart.act, C.chart.tan, C.chart.basis⟩,
    ⟨C.frame.gen, C.frame.ph1, C.frame.ph2, C.frame.sy, C.frame.ad⟩, C.prim, C.gauge, C.rig0⟩

theorem isGerm_iff_raw {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (e : ∀ m, FrTy y d x m) (wP : PrimTy H Xo) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    IsGerm y d x act e wP k F f ↔ RIsGerm y.x d x act e wP k F f := Iff.rfl

end ToRaw

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def chartVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    {y : FrPt Xo c S} (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S)
    (P : MvPolynomial (LtN Dw n) c.F) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
    ∏ b, C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial (colOf m b) 1)

def ThExprUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab₁ nab₂ : NabV Xo c),
    IsNab Xo c nab₁ → IsNab Xo c nab₂ →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (k n : ℕ)
      (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
      (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab₁ y k (F b) (colOf m b) =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab₂ y k (F b) (colOf m b)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPolynomial (X)

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {S : Type} [CommRing S]

def IsExpHomR (x0 : Sp S ⟶ Xo.X) (d : ℕ) (x : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G) : Prop :=
  (∀ m, homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ x (m + 1) = x m) ∧
  ∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d =>
      (X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2) : MvPolynomial (Fin 2 × Fin d) S)) ≫ x m =
    (homAt x0 (jetCopy d m (0 : Fin 2) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) ≫ x m) *
      (homAt x0 (jetCopy d m (1 : Fin 2) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) ≫ x m)

def SameTanR (x0 : Sp S ⟶ Xo.X) (d : ℕ) (x x' : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G) : Prop :=
  ∀ j : Fin d,
    homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1 =
      homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x' 1

end

def ExpUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (d : ℕ) (x x' : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G),
    IsExpHomR y.x d x → IsExpHomR y.x d x' → SameTanR y.x d x x' → x = x'

def ExpUniqRawSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (S : Type) [CommRing S] [Algebra ℚ S] (x0 : Sp S ⟶ Xo.X) (d : ℕ)
    (x x' : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G),
    IsExpHomR x0 d x → IsExpHomR x0 d x' → SameTanR x0 d x x' → x = x'

def ExpUniqLocSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (S : Type) [CommRing S] [IsLocalRing S] [Algebra ℚ S] (x0 : Sp S ⟶ Xo.X) (d : ℕ)
    (x x' : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G),
    IsExpHomR x0 d x → IsExpHomR x0 d x' → SameTanR x0 d x x' → x = x'

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
