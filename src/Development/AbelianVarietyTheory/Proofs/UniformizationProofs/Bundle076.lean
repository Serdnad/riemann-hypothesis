module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivLiftOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle069
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.RedOnto

open GlobalTheory.FormalPoint

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)
  {T : Over (Spec (CommRingCat.of R))}

def Coords (e : ℕ) (g : GtPt D T) {Z : Scheme.{0}} (r : Z ⟶ T.left)
    (y : Z ⟶ (thickObj R I e G).left) : Prop :=
  y ≫ (U.gt e).pG.left = r ≫ g.b.left ∧
    ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J → val ((U.gt e).t χ) y z J = val (g.s χ) r z J

variable {U}

theorem Coords.comp {e : ℕ} {g : GtPt D T} {Z W : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) (k : W ⟶ Z) :
    Coords U e g (k ≫ r) (k ≫ y) := by
  unfold Coords at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Category.assoc, h1, Category.assoc], fun χ w J hJ => ?_⟩

  have hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ ((U.gt e).t χ) y) (LB.pullGen D.P.L _ _ (g.s χ) r) :=
    corr_of_val D.P.isLB fun z J' hJ' => by
      rw [val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp]
      exact h2 χ z J' hJ'
  have hk := val_corr hJ hc k
  rwa [val_pull hJ, val_pull hJ] at hk

theorem Coords.unique {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y y' : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) (h' : Coords U e g r y') : y = y' := by
  unfold Coords at h h'
  exact GlobalTheory.TorusCoord.ext_of_val (U.gt e) y y' (h.1.trans h'.1.symm)
    fun χ w J hJ => (h.2 χ w J hJ).trans (h'.2 χ w J hJ).symm


variable (U) in
theorem exists_coords (e : ℕ) (g : GtPt D T) {Z : Scheme.{0}} (r : Z ⟶ T.left)
    (σ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (h : σ ≫ thick R I e = r ≫ T.hom) :
    ∃ y, Coords U e g r y := by
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.FormalPoint.exists_point (U.gt e) g (Z := Over.mk σ)
    (Over.homMk r h.symm)
  refine ⟨x, ?_⟩
  unfold Coords
  refine ⟨hx1, fun χ z J hJ => ?_⟩
  have hv := hx2 χ Z (𝟙 Z) z J hJ
  rw [Category.id_comp, Category.id_comp] at hv
  exact hv

theorem Coords.succ {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    Coords U (e + 1) g r (y ≫ thickMap R I e G) := by
  unfold Coords at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Category.assoc, U.gt_q e]; exact h1, fun χ z J hJ => ?_⟩
  rw [← val_pull hJ ((U.gt (e + 1)).t χ) (thickMap R I e G) y, val_corr hJ (U.gt_t e χ) y]
  exact h2 χ z J hJ

private theorem comp_hom_eq_of_coords {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    r ≫ T.hom = y ≫ (thickObj R I e G).hom ≫ thick R I e := by
  obtain ⟨h1, -⟩ := h
  have e1 : g.b.left ≫ D.P.A.hom = T.hom := Over.w g.b
  have e2 : (U.gt e).pG.left ≫ D.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (U.gt e).pG
  calc r ≫ T.hom = (r ≫ g.b.left) ≫ D.P.A.hom := by rw [Category.assoc, e1]
    _ = (y ≫ (U.gt e).pG.left) ≫ D.P.A.hom := by rw [h1]
    _ = y ≫ (thickObj R I e G).hom ≫ thick R I e := by rw [Category.assoc, e2]

theorem comp_fstG_eq {g : GtPt D T} {x : T ⟶ G} (hx : U.Red x g) {e : ℕ} {Z : Scheme.{0}}
    {r : Z ⟶ T.left} {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    y ≫ (fstG I e G).left = r ≫ x.left := by
  have hb := comp_hom_eq_of_coords h
  have ex : x.left ≫ G.hom = T.hom := Over.w x

  obtain ⟨a, ha⟩ := GlobalTheory.FormalPoint.exists_lift_fstG (Z := Over.mk (y ≫ (thickObj R I e G).hom))
    (Over.homMk (r ≫ x.left) (by
      show (r ≫ x.left) ≫ G.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e
      rw [Category.assoc, ex, hb, Category.assoc]))
  have ha' : a.left ≫ (fstG I e G).left = r ≫ x.left := congrArg CommaMorphism.left ha
  have hc : Coords U e g r a.left := hx e Z r a.left ha'
  rw [← Coords.unique hc h]
  exact ha'

end Level

section Complete

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {S : Type} [CommRing S] {φ : R →+* S} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)

theorem red_iff_reduction (g : GtPt D (Over.mk (spMap φ))) (x : Over.mk (spMap φ) ⟶ G) :
    U.Red x g ↔ ∀ e, Coords U e g (adicLevelι (I.map φ) (e + 1)) (reduction I x e) := by
  constructor
  · intro hx e
    exact hx e _ _ _ (GlobalTheory.FormalPoint.reduction_fstG I x e)
  · intro h e Z r xe hxe
    have ex : x.left ≫ G.hom = spMap φ := Over.w x
    have ef : (fstG I e G).left ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
    have hs : r ≫ spMap φ = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← ex, ← Category.assoc, ← hxe]
      simp only [Category.assoc, ef]

    obtain ⟨l, hl⟩ := GlobalTheory.FormalPoint.exists_factor_level I φ r _ hs
    have hc := Coords.comp (h e) l
    have hred : l ≫ GlobalTheory.FormalPoint.reduction I x e = xe := by
      rw [← cancel_mono (fstG I e G).left, Category.assoc, GlobalTheory.FormalPoint.reduction_fstG, ← Category.assoc,
        hl, hxe]
    rw [hl, hred] at hc
    exact hc

variable [IsLocalRing S]


variable {U} in
theorem red_unique [IsHausdorff (I.map φ) S] {g : GtPt D (Over.mk (spMap φ))}
    {x x' : Over.mk (spMap φ) ⟶ G} (h : U.Red x g) (h' : U.Red x' g) : x = x' := by
  have hr := (red_iff_reduction U g x).1 h
  have hr' := (red_iff_reduction U g x').1 h'
  apply Over.OverMorphism.ext
  apply GlobalTheory.hom_ext_of_isHausdorff (I.map φ)
  intro n
  rw [← GlobalTheory.FormalPoint.reduction_fstG I x n, ← GlobalTheory.FormalPoint.reduction_fstG I x' n, Coords.unique (hr n) (hr' n)]

theorem existsUnique_red [IsAdicComplete (I.map φ) S] (g : GtPt D (Over.mk (spMap φ))) :
    ∃! x : Over.mk (spMap φ) ⟶ G, U.Red x g := by
  have hy : ∀ e, ∃ y, Coords U e g (adicLevelι (I.map φ) (e + 1)) y := fun e =>
    exists_coords U e g (adicLevelι (I.map φ) (e + 1)) (GlobalTheory.FormalPoint.levelMap I φ e)
      (GlobalTheory.FormalPoint.levelMap_thick I φ e)
  choose y hy using hy
  have htf : ∀ n, thickMap R I n G ≫ (fstG I (n + 1) G).left = (fstG I n G).left := by
    intro n
    unfold thickMap fstG
    simp only [pullback.map, Category.comp_id, Over.homMk_left, pullback.lift_fst]

  have hcomp : ∀ n, GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)) ≫ y (n + 1) = y n ≫ thickMap R I n G := by
    intro n
    refine Coords.unique ?_ (Coords.succ (hy n))
    have hk := Coords.comp (hy (n + 1)) (GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)))
    rwa [GlobalTheory.adicLevelMap_ι] at hk
  have hf : GlobalTheory.IsAdicFamily (I.map φ) (fun n => y n ≫ (fstG I n G).left) := by
    intro n
    show GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)) ≫ y (n + 1) ≫ (fstG I (n + 1) G).left =
      y n ≫ (fstG I n G).left
    rw [← Category.assoc, hcomp n, Category.assoc, htf n]
  have hs : ∀ n, (y n ≫ (fstG I n G).left) ≫ G.hom = adicLevelι (I.map φ) (n + 1) ≫ spMap φ := by
    intro n
    have ef : (fstG I n G).left ≫ G.hom = (thickObj R I n G).hom ≫ thick R I n := Over.w (fstG I n G)
    rw [Category.assoc, ef]
    exact (comp_hom_eq_of_coords (hy n)).symm

  obtain ⟨x₀, ⟨hx₀, hxn⟩, -⟩ := GlobalTheory.existsUnique_over_of_isAdicFamily (spMap φ) G.hom hf hs
  have hred : U.Red (Over.homMk x₀ hx₀ : Over.mk (spMap φ) ⟶ G) g := by
    refine (red_iff_reduction U g _).2 fun e => ?_
    have he : GlobalTheory.FormalPoint.reduction I (Over.homMk x₀ hx₀ : Over.mk (spMap φ) ⟶ G) e = y e := by
      rw [← cancel_mono (fstG I e G).left, GlobalTheory.FormalPoint.reduction_fstG]
      exact hxn e
    rw [he]
    exact hy e
  exact ⟨_, hred, fun x' hx' => red_unique hx' hred⟩

end Complete

theorem main : (AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ g : GtPt D (TA V W), ∃! x : TA V W ⟶ G, U.Red x g) := by
  intro V _ _ _ _ D A G _ _ U W _ _ _ hW g
  obtain ⟨-, -, -, -, hc⟩ := hW
  exact existsUnique_red (φ := algebraMap V W) U g

end GlobalTheory.UU.RedOnto

end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianPartLift

noncomputable local instance (priority := high) grpObjThickForAbelianPart {R : Type} [CommRing R]
    (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] :
    GrpObj (thickObj R I e G) :=
  letI : (Over.pullback (thick R I e)).Monoidal :=
    (Over.instBraidedPullback (f := thick R I e)).toMonoidal
  Functor.grpObjObj (F := Over.pullback (thick R I e))

section General
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_torus_lift [Module.Free ℤ X] {Z' Z : Over S} (ρ : Z' ⟶ Z)
    (h : ∀ a : Γ(Z'.left, ⊤)ˣ, ∃ r : Γ(Z.left, ⊤)ˣ, ρ.left.appTop.hom r.val = a.val)
    (t : Z' ⟶ splitTorus S X) : ∃ t' : Z ⟶ splitTorus S X, ρ ≫ t' = t := by
  let e := Module.Free.chooseBasis ℤ X
  choose r hr using h
  let l : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := e.constr ℤ fun k => Additive.ofMul (r (chV t (e k)))
  let m : X →ₗ[ℤ] Additive Γ(Z'.left, ⊤)ˣ :=
    (MonoidHom.toAdditiveRight (splitTorusPointsEquiv S X Z' t)).toIntLinearMap
  let n : Additive Γ(Z.left, ⊤)ˣ →ₗ[ℤ] Additive Γ(Z'.left, ⊤)ˣ :=
    (MonoidHom.toAdditive (Units.map ρ.left.appTop.hom.toMonoidHom)).toIntLinearMap
  have hl : n ∘ₗ l = m := e.ext fun k => by
    rw [LinearMap.comp_apply, Module.Basis.constr_basis]
    exact congrArg Additive.ofMul (Units.ext (hr _))
  let t' := (splitTorusPointsEquiv S X Z).symm (AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom)
  have ht' : ∀ χ, chV t' χ = Additive.toMul (l χ) := fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; rfl
  refine ⟨t', (splitTorusPointsEquiv S X Z').injective (MonoidHom.ext fun χ => Units.ext ?_)⟩
  have e₁ : (chV (ρ ≫ t') (Multiplicative.toAdd χ)).val = ρ.left.appTop.hom (chV t' (Multiplicative.toAdd χ)).val := by
    rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]
  refine e₁.trans ?_
  rw [ht']
  exact congrArg (fun a => (Additive.toMul a).val) (LinearMap.congr_fun hl (Multiplicative.toAdd χ))

theorem units_lift {A A' : Type} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A'] (f : A →+* A')
    (hf : Function.Surjective f) (a : Γ(Spec (CommRingCat.of A'), ⊤)ˣ) :
    ∃ r : Γ(Spec (CommRingCat.of A), ⊤)ˣ, (Spec.map (CommRingCat.ofHom f)).appTop.hom r.val = a.val := by
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨c, hc⟩ := hf ((Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom a.val)
  have hu : IsUnit c := IsUnit.of_map f c (hc ▸ a.isUnit.map _)
  refine ⟨(hu.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).unit, ?_⟩
  rw [IsUnit.unit_spec]
  have e := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [← e, hc]
  exact congrArg (fun q => q.hom a.val) (Scheme.ΓSpecIso (CommRingCat.of A')).hom_inv_id

theorem exists_lift_extending [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {A A' : Type} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A'] (f : A →+* A')
    (hf : Function.Surjective f) (b : Spec (CommRingCat.of A) ⟶ Q.B.left) (y : Spec (CommRingCat.of A') ⟶ G.left)
    (hy : y ≫ Q.q.left = Spec.map (CommRingCat.ofHom f) ≫ b) :
    ∃ g : Spec (CommRingCat.of A) ⟶ G.left, g ≫ Q.q.left = b ∧ Spec.map (CommRingCat.ofHom f) ≫ g = y := by
  have := Q.q_hom
  have := Q.i_hom
  let b' : Over.mk (b ≫ Q.B.hom) ⟶ Q.B := Over.homMk b rfl
  let y' : Over.mk (y ≫ G.hom) ⟶ G := Over.homMk y rfl
  let ρ : Over.mk (y ≫ G.hom) ⟶ Over.mk (b ≫ Q.B.hom) := Over.homMk (Spec.map (CommRingCat.ofHom f)) (by
    change Spec.map (CommRingCat.ofHom f) ≫ b ≫ Q.B.hom = y ≫ G.hom
    rw [← Category.assoc, ← hy, Category.assoc, Over.w])
  have hy' : y' ≫ Q.q = ρ ≫ b' := Over.OverMorphism.ext hy
  obtain ⟨g, hg⟩ := Q.exists_lift b'
  have h₁ : (y' * (ρ ≫ g)⁻¹) ≫ Q.q = toUnit _ ≫ η[Q.B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hg, hy', mul_inv_cancel, Hom.one_def]
  obtain ⟨t, ht⟩ := exists_torus_lift ρ (units_lift f hf) (Q.isKernel.lift _ _ h₁)
  have h₃ : (t ≫ Q.i) ≫ Q.q = 1 := by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  have a₁ : ((t ≫ Q.i) * g) ≫ Q.q = b' := by rw [MonObj.mul_comp, h₃, _root_.one_mul, hg]
  have a₂ : ρ ≫ ((t ≫ Q.i) * g) = y' := by
    rw [MonObj.comp_mul, ← Category.assoc, ht, IsPullback.lift_fst, inv_mul_cancel_right]
  exact ⟨((t ≫ Q.i) * g).left, congrArg (fun q => q.left) a₁, congrArg (fun q => q.left) a₂⟩

end General

open GlobalTheory.FormalPoint

theorem main : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B, ∃ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ b
  let I := IsLocalRing.maximalIdeal V
  let φ := algebraMap V W
  let J := I.map φ
  have hJ : J ≠ ⊤ := ne_top_of_isHausdorff J
  have hloc := isLocalRing_quotient_pow hJ
  have hbw : b.left ≫ a.B.hom = Spec.map (CommRingCat.ofHom φ) := Over.w b
  have pb : ∀ e, IsPullback (a.b e) (t.l e).Q.B.hom a.B.hom (thick V I e) := fun e => (a.b_pb e).1.1
  have w : ∀ e, (adicLevelι J (e + 1) ≫ b.left) ≫ a.B.hom = levelMap I φ e ≫ thick V I e := fun e =>
    (Category.assoc _ _ _).trans ((congrArg _ hbw).trans (levelMap_thick I φ e).symm)
  let c : ∀ e, Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (t.l e).Q.B.left := fun e => (pb e).lift _ _ (w e)
  have c₁ : ∀ e, c e ≫ a.b e = adicLevelι J (e + 1) ≫ b.left := fun e => (pb e).lift_fst _ _ _
  have c₂ : ∀ e, c e ≫ (t.l e).Q.B.hom = levelMap I φ e := fun e => (pb e).lift_snd _ _ _
  have mth : ∀ e, Mono (thick V I e) := fun e => have := isClosedImmersion_red (I ^ (e + 1)); inferInstance
  have mono : ∀ e, Mono (a.b e) := fun e =>
    (MorphismProperty.monomorphisms _).of_isPullback (pb e).flip (mth e)
  have cc : ∀ e, c e ≫ t.β e = adicLevelMap J (Nat.le_succ (e + 1)) ≫ c (e + 1) := fun e => by
    have := mono (e + 1)
    rw [← cancel_mono (a.b (e + 1)), Category.assoc, Category.assoc, a.b_β, c₁, c₁, adicLevelMap_ι_assoc]
  let P := fun e => {x : Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (thickObj V I e G).left //
    x ≫ (t.l e).Q.q.left = c e}
  have base : Nonempty (P 0) := by
    obtain ⟨g, hg⟩ := (t.l 0).Q.exists_lift (Over.homMk (c 0) rfl : Over.mk (c 0 ≫ (t.l 0).Q.B.hom) ⟶ (t.l 0).Q.B)
    exact ⟨⟨g.left, congrArg (fun q => q.left) hg⟩⟩
  have step : ∀ e (x : P e), ∃ x' : P (e + 1),
      adicLevelMap J (Nat.le_succ (e + 1)) ≫ x'.1 = x.1 ≫ thickMap V I e G := fun e x => by
    obtain ⟨g, h₁, h₂⟩ := exists_lift_extending (t.l (e + 1)).Q (Ideal.Quotient.factorPow J (Nat.le_succ (e + 1)))
      (Ideal.Quotient.factor_surjective _) (c (e + 1)) (x.1 ≫ thickMap V I e G)
      (by rw [Category.assoc, ← t.β_q, ← Category.assoc, x.2, cc])
    exact ⟨⟨g, h₁⟩, h₂⟩
  choose nx hnx using step
  let x : ∀ e, P e := fun e => Nat.rec base.some nx e
  have hx : ∀ e, adicLevelMap J (Nat.le_succ (e + 1)) ≫ (x (e + 1)).1 = (x e).1 ≫ thickMap V I e G :=
    fun e => hnx e (x e)
  have tm : ∀ e, thickMap V I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left := fun e =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have fam : IsAdicFamily J fun e => (x e).1 ≫ (fstG I e G).left := fun e => by
    rw [← Category.assoc, hx, Category.assoc, tm]
  have fw : ∀ e, (fstG I e G).left ≫ G.hom = (thickObj V I e G).hom ≫ thick V I e := fun e => pullback.condition
  obtain ⟨g, ⟨g₁, g₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (Spec.map (CommRingCat.ofHom φ)) G.hom fam fun e => by
    rw [Category.assoc, fw, ← Over.w (t.l e).Q.q, Category.assoc, ← Category.assoc, (x e).2, ← Category.assoc, c₂]
    exact levelMap_thick I φ e
  refine ⟨Over.homMk g g₁, fun e Z r xe h => ?_⟩
  replace h : xe ≫ (fstG I e G).left = r ≫ g := h
  obtain ⟨l, rfl⟩ := exists_factor_level I φ r (xe ≫ (thickObj V I e G).hom) (by
    rw [Category.assoc, ← fw, ← Category.assoc, h, Category.assoc, g₁])
  have : Mono (fstG I e G).left := have := mth e; (inferInstance : Mono (pullback.fst G.hom (thick V I e)))
  have hxe : xe = l ≫ (x e).1 := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, g₂]
  rw [hxe, Category.assoc, Category.assoc, ← c₁, ← Category.assoc (x e).1, (x e).2]

end GlobalTheory.AbelianPartLift
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AdditionTensor

section
variable {F : Type} [CommRing F] {Z Y T : Scheme.{0}} {L : LB Z} {K : Type} [Fintype K]

noncomputable def svalHom (p : Y ⟶ Spec (CommRingCat.of F)) (φ : K → (Y ⟶ Z)) (ε : K → ℤ) (r : T ⟶ Y) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) : SecMod p (LB.LinComb L φ ε) →+ T.presheaf.stalk z :=
  AddMonoidHom.mk' (fun s => sval s.sec r z J) (fun _ _ => gs_add r z _ (hJ.mem φ r) _ _)

theorem svalHom_smul (p : Y ⟶ Spec (CommRingCat.of F)) (φ : K → (Y ⟶ Z)) (ε : K → ℤ) (r : T ⟶ Y) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) (c : F) (s : SecMod p (LB.LinComb L φ ε)) :
    svalHom p φ ε r z hJ (c • s) =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * svalHom p φ ε r z hJ s :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _)
    ((gs_res r z le_top (hJ.mem φ r) (scal p c)).trans (gs_pull r p z ⊤ trivial _)))

end

theorem sum_sval_mul_eq_zero {F : Type} [CommRing F] {Z Y₁ Y₂ T : Scheme.{0}} {L : LB Z}
    (p₁ : Y₁ ⟶ Spec (CommRingCat.of F)) (p₂ : Y₂ ⟶ Spec (CommRingCat.of F)) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y₁ ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂ ⟶ Z)) (ε₂ : K₂ → ℤ) {n : ℕ}
    (a : Fin n → SecMod p₁ (LB.LinComb L φ₁ ε₁)) (b : Fin n → SecMod p₂ (LB.LinComb L φ₂ ε₂))
    (h : ∑ i, TensorProduct.tmul F (a i) (b i) = 0) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂) (e : r₁ ≫ p₁ = r₂ ≫ p₂) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) :
    ∑ i, sval (a i).sec r₁ z J * sval (b i).sec r₂ z J = 0 := by
  let f : SecMod p₁ (LB.LinComb L φ₁ ε₁) →+ SecMod p₂ (LB.LinComb L φ₂ ε₂) →+ T.presheaf.stalk z :=
    (((AddMonoidHom.mul (R := T.presheaf.stalk z)).comp (svalHom p₁ φ₁ ε₁ r₁ z hJ)).flip.comp
      (svalHom p₂ φ₂ ε₂ r₂ z hJ)).flip
  have hf : ∀ s t, f s t = svalHom p₁ φ₁ ε₁ r₁ z hJ s * svalHom p₂ φ₂ ε₂ r₂ z hJ t := fun _ _ => rfl
  have hb : ∀ (c : F) s t, f (c • s) t = f s (c • t) := fun c s t => by
    rw [hf, hf, svalHom_smul, svalHom_smul, e]; ring
  have := congrArg (TensorProduct.liftAddHom f hb) h

  rw [map_sum, map_zero] at this
  simp only [TensorProduct.liftAddHom_tmul] at this
  exact this

end GlobalTheory.AdditionTensor

namespace GlobalTheory

theorem addition_tensor_ne_zero : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∑ i, TensorProduct.tmul F (t i) (t' i) ≠ 0 := by
  intro S P F _ p th n t t' hadd hth h0
  obtain ⟨κ, -, hκ⟩ := hadd
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : IsIntegral (Over.mk p).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have hI : IsIntegral (Over.mk p ⊗ P.A).left := isIntegral_tensor_left_of_smooth_grpObj S P.A (Over.mk p)
  obtain ⟨z⟩ : Nonempty (Over.mk p ⊗ P.A).left := inferInstance
  obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB z (K := PEmpty) (fun k => k.elim) (fun k => k.elim)
    (fun k => k.elim) (fun k => k.elim)
  have hne : ∃ j, th.sec.f j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hth (DVR.SecOps.sec_ext hc)
  have hv := sval_ne_zero_of_isIso P.A.left (Over.mk p ⊗ P.A).left P.L P.isLB (Fin 1)
    (fun _ => (snd (Over.mk p) P.A).left) (fun _ => ((1 : ℕ) : ℤ)) th.sec hne _ (𝟙 _) z J hJ
  have h1 := hκ (Over.mk p ⊗ P.A) (fst _ _) (snd _ _) 1 z J hJ
  have h2 := AdditionTensor.sum_sval_mul_eq_zero (fst (Over.mk p) P.A).left (fst (Over.mk p) P.A).left
    (fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (fun _ => ((2 : ℕ) : ℤ))
    (fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (fun _ => ((2 : ℕ) : ℤ)) t t' h0
    (lift (fst (Over.mk p) P.A) (snd (Over.mk p) P.A)).left (lift (fst (Over.mk p) P.A) (1 : Over.mk p ⊗ P.A ⟶ P.A)).left
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z hJ
  have h3 := h1.symm.trans h2
  rw [inv_one, _root_.mul_one, lift_fst_snd, Units.mul_right_eq_zero, mul_self_eq_zero] at h3
  exact hv h3

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.nonempty_biTriv_of_nonempty_biTriv_reduction : (∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] [IsCommMonObj G₀] [ConnectedSpace G₀.left] (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G (red J) F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P (red J) F hw w → ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat (red J) F i₀ i → Nonempty (BiTriv P₀.c i₀) → Nonempty (BiTriv P.c i)) := by
  first | exact @GlobalTheory.UU.biTriv_lift_of_isNilpotent | exact GlobalTheory.UU.biTriv_lift_of_isNilpotent | (intros; apply GlobalTheory.UU.biTriv_lift_of_isNilpotent <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.exists_torus_quotient_scheme_over_nilpotent_thickening : (∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ (Q₀ : TQ G₀ X) (i : splitTorus _ X ⟶ G), IsMonHom i → TorusCompat (red J) F Q₀.i i → ∃ (B : Over (Spec (CommRingCat.of A))) (q : G ⟶ B) (j : Q₀.B.left ⟶ B.left), IsPullback j Q₀.B.hom B.hom (red J) ∧ Q₀.q.left ≫ j = F ≫ q.left ∧ IsAffineHom q.left ∧ ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧ (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧ (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧ ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) := by
  first | exact @GlobalTheory.TorusQuotientLift.exists_quotient_scheme | exact GlobalTheory.TorusQuotientLift.exists_quotient_scheme | (intros; apply GlobalTheory.TorusQuotientLift.exists_quotient_scheme <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_section_primitive_twist_torus_extension : GlobalFnsSt → ∀ (A : Type) [CommRing A] [IsLocalRing A] (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (Q : TQ G X) (M : LB Q.B.left), M.IsLB → (∃ s : LB.Sec (M.pull Q.q.left), (∃ j, s.f j ≠ 0)) → ∃ O : LB Q.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ Q.B O), u.IsGen) ∧ ∃ s : LB.Sec (LB.div M O), (∃ j, s.f j ≠ 0) := by
  first | exact @GlobalTheory.exists_sec_primitive_twist | exact GlobalTheory.exists_sec_primitive_twist | (intros; apply GlobalTheory.exists_sec_primitive_twist <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.isSemiAbelian_of_uniformisation_over_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], UnifPre (maximalIdeal V) D A G → IsSemiAbelian G := by
  first | exact @GlobalTheory.isSemiAbelian_of_unifPre_dvr | exact GlobalTheory.isSemiAbelian_of_unifPre_dvr | (intros; apply GlobalTheory.isSemiAbelian_of_unifPre_dvr <;> assumption)
end
