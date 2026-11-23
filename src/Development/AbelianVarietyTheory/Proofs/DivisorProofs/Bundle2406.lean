module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
public import Formalism.SharpRestriction.Divisibility.JumpSets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowCoefMemCoefAlgebraOfDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvInterior

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

section Moves

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)

def nu (g : LevelAut Dw l) : SABMap Xo.univ.t Xo.univ.t (GlobalTheory.CompLevelStab.mv hpq hA Xo g) :=
  (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose

theorem nu_spec (g : LevelAut Dw l) :
    IsLevMove (GlobalTheory.CompLevelStab.mv hpq hA Xo g) (nu hpq hA Xo g) (liftLa g) LinearMap.id :=
  (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose_spec.2

theorem nu_mul (c : Coeff l) (g h : LevelAut Dw l) : (nu hpq hA Xo (g * h)).φ = (nu hpq hA Xo g).φ ≫ (nu hpq hA Xo h).φ := by
  obtain ⟨μ, hμ, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).2.1 _ _ (nu hpq hA Xo g) (nu hpq hA Xo h)
  have hg := nu_spec hpq hA Xo g
  have hh := nu_spec hpq hA Xo h
  have hc : IsLevMove (GlobalTheory.CompLevelStab.mv hpq hA Xo g ≫ GlobalTheory.CompLevelStab.mv hpq hA Xo h) μ (liftLa (g * h))
      LinearMap.id := by
    refine ⟨?_, fun a => ?_, fun a => ?_⟩
    · rw [Category.assoc, hh.1, hg.1]
    · rw [GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub g h a), hμ, ← Category.assoc, hg.2.1,
        Category.assoc, hh.2.1, Category.assoc]
    · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a =
          (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
      rw [e, hμ, ← Category.assoc, hg.2.2, Category.assoc, hh.2.2, Category.assoc]
  have := (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose_spec.1
  have := (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo h).choose_spec.1
  rw [← hμ]
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c (g * h) (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo (g * h)).choose_spec.1
    inferInstance (nu_spec hpq hA Xo (g * h)) hc).2

end Moves

section Lift

variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem j₀_ι' : j₀ TF.Y Z ≫ (barComp TF.Y Z).ι = i₀ TF.Y Z ≫ (TF.Y.jQ ≫ pullback.fst _ _) := j₀_ι TF.Y Z

def toF : (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ TF.Y.oF.t.G.left :=
  TF.Y.m.cart.1.lift (pullback.fst TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι))
    (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ i₀ TF.Y Z) (by
      rw [pullback.condition, Category.assoc]; exact congrArg (_ ≫ ·) (j₀_ι' TF Z))

theorem toF_m : toF TF Z ≫ TF.Y.m.φ = pullback.fst TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) :=
  TF.Y.m.cart.1.lift_fst _ _ _

theorem toF_hom : toF TF Z ≫ TF.Y.oF.t.G.hom =
    pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ i₀ TF.Y Z :=
  TF.Y.m.cart.1.lift_snd _ _ _

theorem toF_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) TF.Y.oF.t.G (i₀ TF.Y Z) (toF TF Z) :=
  IsGrpPullback.cancel TF.Y.m.cart
    ((GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z (j₀ TF.Y Z)).congr (j₀_ι' TF Z) (toF_m TF Z).symm) (toF_hom TF Z)

def toU : (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ Xo.univ.t.G.left := toF TF Z ≫ TF.Y.m0.toSABMap.φ

theorem toU_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) Xo.univ.t.G (i₀ TF.Y Z ≫ pullback.fst _ _)
    (toU TF Z) :=
  (toF_cart TF Z).comp TF.Y.m0.cart

theorem hom_ext' {T : Scheme.{0}} {u u' : T ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left}
    (h₁ : u ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) =
      u' ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι))
    (h₂ : u ≫ toU TF Z = u' ≫ toU TF Z) : u = u' :=
  (toU_cart TF Z).1.hom_ext h₂ h₁

end Lift

section Move

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem nF_w (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
    (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g) :
    (toU TF Z ≫ (nu hpq hA Xo g).φ) ≫ Xo.univ.t.G.hom =
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) ≫ pullback.fst _ _ := by
  rw [Category.assoc, (nu hpq hA Xo g).cart.1.w, ← Category.assoc, (toU_cart TF Z).1.w, hr,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, GlobalTheory.CompLevelStab.mvF_fst]
  rfl

def nF (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
    (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g) :
    (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left :=
  pullback.lift
    (TF.Y.m0.cart.1.lift (toU TF Z ≫ (nu hpq hA Xo g).φ)
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) (nF_w hpq hA TF Z g r hr) ≫ TF.Y.m.φ)
    (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r) (by
      rw [Category.assoc, TF.Y.m.cart.1.w, ← Category.assoc, TF.Y.m0.cart.1.lift_snd]
      simp only [Category.assoc]
      exact congrArg (fun x => _ ≫ r ≫ x) (j₀_ι' TF Z).symm)

variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)

theorem nF_snd : nF hpq hA TF Z g r hr ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) =
    pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r :=
  pullback.lift_snd _ _ _

theorem nF_toF : nF hpq hA TF Z g r hr ≫ toF TF Z = TF.Y.m0.cart.1.lift (toU TF Z ≫ (nu hpq hA Xo g).φ)
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) (nF_w hpq hA TF Z g r hr) := by
  apply TF.Y.m.cart.1.hom_ext
  · rw [Category.assoc, toF_m]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, toF_hom, ← Category.assoc, nF_snd, Category.assoc, TF.Y.m0.cart.1.lift_snd]

theorem nF_toU : nF hpq hA TF Z g r hr ≫ toU TF Z = toU TF Z ≫ (nu hpq hA Xo g).φ := by
  rw [toU, ← Category.assoc, nF_toF]
  exact TF.Y.m0.cart.1.lift_fst _ _ _

theorem nF_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) r
    (nF hpq hA TF Z g r hr) := by
  refine IsGrpPullback.cancel (toU_cart TF Z) (((toU_cart TF Z).comp (nu hpq hA Xo g).cart).congr ?_ ?_) ?_
  · rw [Category.assoc, ← GlobalTheory.CompLevelStab.mvF_fst, ← Category.assoc, ← hr, Category.assoc]
  · exact (nF_toU hpq hA TF Z g r hr).symm
  · exact nF_snd hpq hA TF Z g r hr

end Move

section Laws

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem act_toF (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ toF TF Z =
    toF TF Z ≫ (TF.Y.oF.t.act.act a).left := by
  apply TF.Y.m.cart.1.hom_ext
  · rw [Category.assoc, toF_m, Category.assoc, TF.Y.m.act a, ← Category.assoc, toF_m]
    exact GlobalTheory.EqvAct.pullAct_pullψ TF Z (j₀ TF.Y Z) a
  · rw [Category.assoc, toF_hom, Category.assoc, Over.w (TF.Y.oF.t.act.act a), toF_hom, ← Category.assoc]
    exact congrArg (· ≫ i₀ TF.Y Z) (Over.w ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a))

theorem act_toU (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ toU TF Z =
    toU TF Z ≫ (Xo.univ.t.act.act a).left := by
  rw [toU, ← Category.assoc, act_toF, Category.assoc, TF.Y.m0.toSABMap.act a, Category.assoc]

variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)

theorem act_nF (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ nF hpq hA TF Z g r hr =
    nF hpq hA TF Z g r hr ≫ ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left := by
  apply hom_ext' TF Z
  · rw [Category.assoc, nF_snd, Category.assoc]
    have e := Over.w ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a)
    erw [e, ← Category.assoc, e]
    exact (nF_snd hpq hA TF Z g r hr).symm
  · have e1 : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ nF hpq hA TF Z g r hr ≫ toU TF Z =
        toU TF Z ≫ (Xo.univ.t.act.act a).left ≫ (nu hpq hA Xo g).φ := by
      rw [nF_toU, ← Category.assoc, act_toU, Category.assoc]
    have e2 : (nF hpq hA TF Z g r hr ≫ ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left) ≫ toU TF Z =
        toU TF Z ≫ (nu hpq hA Xo g).φ ≫ (Xo.univ.t.act.act a).left := by
      rw [Category.assoc, act_toU, ← Category.assoc, nF_toU, Category.assoc]
    rw [Category.assoc, e1, e2, (nu hpq hA Xo g).act a]

theorem sec_toU (b : Dw.La) (w : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left)
    (hw : w ≫ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).hom = 𝟙 _)
    (hb : w ≫ GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z) = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ) :
    w ≫ toU TF Z = i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta b).left := by
  have hF : w ≫ toF TF Z = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left := by
    apply TF.Y.m.cart.1.hom_ext
    · rw [Category.assoc, toF_m, Category.assoc]
      exact hb
    · rw [Category.assoc, toF_hom, ← Category.assoc]
      erw [hw]
      rw [Category.id_comp, Category.assoc, Over.w (TF.Y.oF.eta b)]
      exact (Category.comp_id _).symm
  rw [toU, ← Category.assoc, hF, Category.assoc, TF.Y.m0.eta b]

end Laws

end GlobalTheory.EqvInterior
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.ExpTie.Lift

variable {D : D7}

abbrev lamL (j : Fin D.R.m) (τ : D.what₂.Tau) : DomWeight (Vc D j).rank :=
  Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ

def lamT (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) : ℕ :=
  if h : a < (Vc D j).rank then (lamL j τ).natW ⟨a, h⟩ else 0

def cT (j : Fin D.R.m) (τ : D.what₂.Tau) : ℝ :=
  ((Vc D j).rank : ℝ) / 2 - 1 - ((lamL j τ).detShift : ℝ)


open Classical in
def wts (L : SizeData₂ D) (j : Fin D.R.m) : Wts D.what₂.Tau where
  lam := lamT j
  T2 := Finset.univ.filter fun τ => (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
  j := fun _ => (j : ℕ) + 1
  q := fun _ => D.R.m - ((j : ℕ) + 1)
  xm := fun τ => ⌈cT j τ⌉
  xp := fun τ => ⌊cT j τ + L.Sc⌋
  c := cT j
  e := fun τ => wj D ((j : ℕ) + 1) τ
  fr := fun _ τ => τ
  cj := fun _ _ => false
  Sp := Formalism.MainNotions.JumpSetsAlt.excSet D

def ValsAt (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) : Prop :=
  (∀ (a : ℕ) (ha : a < D.R.k - 1),
      ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ = (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ)) ∧
    (∀ i : Fin D.R.m, (i : ℕ) ≤ j →
      ((wts L j).U (parOf L j) τ (D.R.k - 1 + i) : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ)) ∧
    (∀ s : ℕ, s < D.R.t →
      ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) - (wts L j).c τ =
        -wj D ((j : ℕ) + 1) τ + ((D.R.t : ℝ) - 1) / 2 - s) ∧
    (∀ i : Fin D.R.m, (j : ℕ) < i →
      ((wts L j).U (parOf L j) τ (D.R.k - 1 + i + D.R.t) : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ))

end GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

open Formalism.IndefR.Bridge

variable {D : D7}

theorem lamT_of_lt (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (h : a < (Vc D j).rank) :
    (lamT j τ a : ℤ) = (lamL j τ).w ⟨a, h⟩ - (lamL j τ).detShift := by
  have hn : 0 < (Vc D j).rank := by omega
  have hle : (lamL j τ).detShift ≤ (lamL j τ).w ⟨a, h⟩ := by
    unfold DomWeight.detShift
    rw [dite_eq_left hn]
    exact (lamL j τ).anti (Fin.mk_le_mk.2 (by omega))
  unfold lamT DomWeight.natW
  rw [dite_eq_left h]
  omega

theorem anti (L : SizeData₂ D) (j : Fin D.R.m) : ∀ τ a b, a ≤ b → b < (parOf L j).Nr → (wts L j).lam τ b ≤ (wts L j).lam τ a := by
  intro τ a b hab hb
  have ha : a < (Vc D j).rank := lt_of_le_of_lt hab hb
  have h1 := lamT_of_lt j τ a ha
  have h2 := lamT_of_lt j τ b hb
  have h3 := (lamL j τ).anti (show (⟨a, ha⟩ : Fin _) ≤ ⟨b, hb⟩ from Fin.mk_le_mk.2 hab)
  show lamT j τ b ≤ lamT j τ a
  omega

theorem rank_eq (j : Fin D.R.m) : (Vc D j).rank = D.R.k - 1 + D.R.m + D.R.t := by
  have h := D.sp.V_rank ((j : ℕ) + 1) (by omega) (by omega)
  have hk := D.R.m_add_three_le_k
  simp only [Vc, h, Ranks.nV, Ranks.r]
  omega

theorem what₂ (L : SizeData₂ D) (j : Fin D.R.m) : ∀ τ, Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t + (wts L j).q τ = (parOf L j).Nr := by
  intro τ
  have := rank_eq j
  have hj := j.2
  simp only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]
  omega

end GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

open Formalism.IndefR.Bridge

variable {D : D7}

theorem U_last (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) :
    (wts L j).U (parOf L j) τ ((Vc D j).rank - 1) = 0 := by
  have hn := rank_eq j
  have ht0 := D.R.t_odd.pos
  have hlt : (Vc D j).rank - 1 < (Vc D j).rank := by omega
  have h1 := lamT_of_lt j τ _ hlt
  have h2 : (lamL j τ).detShift = (lamL j τ).w ⟨(Vc D j).rank - 1, hlt⟩ := by
    unfold DomWeight.detShift; rw [dite_eq_left (by omega)]
  show Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) ((Vc D j).rank - 1) = 0
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem liftWeightCombinatorialData_U_le_U_zero (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    (wts L j).U (parOf L j) τ a ≤ (wts L j).U (parOf L j) τ 0 := by
  have h := anti L j τ 0 a (Nat.zero_le _) ha
  show Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) 0
  change lamT j τ a ≤ lamT j τ 0 at h
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem U_nonneg (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    0 ≤ (wts L j).U (parOf L j) τ a := by
  show 0 ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem T2_card (L : SizeData₂ D) (j : Fin D.R.m) : (wts L j).T2.card ≤ D.host.T2.card := by
  classical
  calc (wts L j).T2.card ≤ D.host.thickPlaces.card := by
        refine Finset.card_le_card_of_injOn (fun τ => (D.eTau τ : D.R.GG)) ?_ ?_
        · intro τ hτ
          simp only [wts, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ
          exact hτ
        · intro a _ b _ h
          exact D.eTau.injective (Subtype.ext h)
    _ ≤ D.host.T2.card := by
        unfold Host.thickPlaces
        exact Finset.card_image_le

theorem c_le (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (hv : ValsAt L j τ) :
    (wts L j).c τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2 := by
  have hn := rank_eq j
  have hU := U_last L j τ
  have ht : (1 : ℝ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have ht0 := D.R.t_odd.pos
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm : 0 < D.R.m := by omega
  by_cases hj : (j : ℕ) + 1 < D.R.m
  · have h := hv.2.2.2 ⟨D.R.m - 1, by omega⟩ (by simp; omega)
    have hrow : D.R.k - 1 + (D.R.m - 1) + D.R.t = (Vc D j).rank - 1 := by omega
    simp only [hrow, hU] at h
    have hg := (D.hc τ).gap_be ⟨D.R.m - 1, by omega⟩
    have hw : wj D D.R.m τ = (((D.hc τ).e ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) := by
      unfold wj; rw [dite_eq_left (by omega)]
    have hg' : (((D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) + ((D.R.t : ℝ) + 3) / 2 ≤
        (((D.hc τ).e ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) := by
      have h2 : ((((D.hc τ).e ⟨D.R.m - 1, by omega⟩ - (D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ)) : ℝ) ≥ ((((D.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) := by
        exact_mod_cast hg
      push_cast at h2
      linarith
    push_cast at h
    rw [hw]; linarith
  · have hjm : (j : ℕ) + 1 = D.R.m := by omega
    have h := hv.2.2.1 (D.R.t - 1) (by omega)
    have hrow : D.R.k + (j : ℕ) + (D.R.t - 1) = (Vc D j).rank - 1 := by omega
    simp only [hrow, hU] at h
    have hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hts, hjm] at h
    push_cast at h
    linarith

end GlobalTheory.ExpTie.Lift

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.highest_weight_base_change : GlobalTheory.HighWt.BaseChange := by
  first | exact @GlobalTheory.HighWt.baseChange_holds | exact GlobalTheory.HighWt.baseChange_holds | (intros; apply GlobalTheory.HighWt.baseChange_holds <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.genericRowCoef_mem_coefAlgebra_of_domain : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ), GlobalTheory.HighWt.CoefIn O N lam := by
  first | exact @GlobalTheory.HighWt.coefIn_of_domain | exact GlobalTheory.HighWt.coefIn_of_domain | (intros; apply GlobalTheory.HighWt.coefIn_of_domain <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.firstOrderDeformation_form_lift_values_sub : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (U : A'.left.Opens), IsAffineOpen U → ∀ (P : GPt A), P.In (i ⁻¹ᵁ U) → ∀ (y₁ y₂ : Sp (DualNumber P.B) ⟶ A'.left) (h₁ : IsLift i P y₁) (h₂ : IsLift i P y₂) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (c : Fin n → P.B), (∀ a, IsTangent (u a)) → (∀ f : Γ(A'.left, U), valR y₁ U f - valR y₂ U f = (TrivSqZeroExt.inr (∑ a, c a * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B)) → (liftVal h ω.1 h₁ - liftVal h ω.1 h₂).snd = -∑ a, c a * algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
  first | exact @GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd | exact GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd | (intros; apply GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.weilTransport_archimedeanSlice_sobolev_bounds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) p0 (i j : ℕ), ∃ B : ℝ,
      ∀ᶠ p in nhds p0, ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y)) x‖) ^ 2 ≤ B := by
  first | exact @GlobalTheory.WeilL2Words.weilTransport_archimedeanSlice_sobolev_bounds_alt | exact GlobalTheory.WeilL2Words.weilTransport_archimedeanSlice_sobolev_bounds_alt | (intros; apply GlobalTheory.WeilL2Words.weilTransport_archimedeanSlice_sobolev_bounds_alt <;> assumption)
end
