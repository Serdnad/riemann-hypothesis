module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3039
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj.GenPull

theorem pull_comp_iso {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {F : Y ⟶ X} (H : LBIso M (L.pull F)) (h : Z ⟶ Y) :
    LBIso (M.pull h) (L.pull (h ≫ F)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (chartPullSame L _ _ _ h fun _ => rfl) H

theorem pull_congr_iso {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {a b : Y ⟶ X} (e : a = b) :
    LBIso (L.pull a) (L.pull b) := e ▸ GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL a)

theorem pull_pull_iso {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso ((L.pull a).pull b) (L.pull (b ≫ a)) :=
  pull_comp_iso (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL a)) b

theorem pull_id_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)

end GlobalTheory.TInj.GenPull


open GlobalTheory.TInj.GenPull in
theorem GlobalTheory.TInj.overPt_genPull : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀) (f : R →+* V) (D : DegData V J') (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif J' D A ((Over.pullback (specOf f)).obj G₀)), IsPullUnif f hD (Iso.refl _) U₀ U → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ κ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ ≫ jK R = jK V ≫ spMap f → ∃ α : A.A.left ⟶ c.A.left, OverPt c A (κ ≫ y₀) α ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ A.A.left) (x₀ : Z ⟶ A₀.A.left), x ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = x₀ ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) → x ≫ α = x₀ ≫ α₀ := by
  intro X g n B _ ζ sX c R _ _ V _ _ J J' D₀ A₀ G₀ _ _ U₀ f D hD A U hU y₀ α₀ hO κ hκ
  let G := (Over.pullback (specOf f)).obj G₀
  let p := pullback.fst G.hom (jK V)
  let q := pullback.fst G₀.hom (specOf f)
  let p₀ := pullback.fst G₀.hom (jK R)
  have hsq : jK V ≫ specOf f = κ ≫ jK R := hκ.symm
  let κG : pullback G.hom (jK V) ⟶ pullback G₀.hom (jK R) :=
    pullback.lift (p ≫ q) (pullback.snd _ _ ≫ κ) (by
      have c1 : q ≫ G₀.hom = G.hom ≫ specOf f := pullback.condition
      have c2 : p ≫ G.hom = pullback.snd G.hom (jK V) ≫ jK V := pullback.condition
      rw [Category.assoc, c1, ← Category.assoc, c2, Category.assoc, hsq, Category.assoc])
  have hκf : κG ≫ p₀ = p ≫ q := pullback.lift_fst _ _ _
  have w : κG ≫ ((Over.pullback (jK R)).obj G₀).hom = ((Over.pullback (jK V)).obj G).hom ≫ κ :=
    pullback.lift_snd _ _ _
  have hκG : IsGrpPullback ((Over.pullback (jK V)).obj G) ((Over.pullback (jK R)).obj G₀) κ κG :=
    (isGrpPullback_pullback G₀ (jK R)).cancel
      (((isGrpPullback_pullback G (jK V)).comp (isGrpPullback_pullback G₀ (specOf f))).congr hsq hκf.symm) w
  have : IsMonHom U.gen.hom := U.gen_hom
  have : IsMonHom U₀.gen.hom := U₀.gen_hom
  have : IsMonHom U.gen.symm.hom := show IsMonHom U.gen.inv by infer_instance
  have hu : IsGrpPullback A.A ((Over.pullback (jK V)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have hg : IsGrpPullback ((Over.pullback (jK R)).obj G₀) A₀.A (𝟙 _) U₀.gen.hom.left := isGrpPullback_of_iso U₀.gen
  let π : A.A.left ⟶ A₀.A.left := U.gen.inv.left ≫ κG ≫ U₀.gen.hom.left
  have hπ : IsGrpPullback A.A A₀.A κ π := (hu.comp (hκG.comp hg)).congr (by simp) rfl
  obtain ⟨hO₁, α₀₂, sα₀, hΛ₀⟩ := hO

  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hLG₀ : U₀.LG.L.IsLB := U₀.LG.isLB
  obtain ⟨wL, hwL, -⟩ := hU.lg
  have E1 : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull p) := U.ext
  have E2 : LBIso (U.LG.L.pull p) (U₀.LG.L.pull (p ≫ (Iso.refl G).hom.left ≫ q)) := pull_comp_iso ⟨wL, hwL⟩ p
  have E4 : LBIso (U₀.LG.L.pull (p ≫ (Iso.refl G).hom.left ≫ q)) (U₀.LG.L.pull (κG ≫ p₀)) :=
    pull_congr_iso hLG₀ (by rw [hκf, Iso.refl_hom, Over.id_left, Category.id_comp])
  have E3 : LBIso ((A₀.L.pull U₀.gen.hom.left).pull κG) (U₀.LG.L.pull (κG ≫ p₀)) := pull_comp_iso U₀.ext κG
  have E5 := pull_pull_iso A₀.isLB U₀.gen.hom.left κG
  have hA₀g := pull_isLB A₀.isLB U₀.gen.hom.left
  have X1 : LBIso (A.L.pull U.gen.hom.left) (A₀.L.pull (κG ≫ U₀.gen.hom.left)) :=
    LBIso.trans (pull_isLB A.isLB _) (pull_isLB hLG _) (pull_isLB A₀.isLB _) E1
      (LBIso.trans (pull_isLB hLG _) (pull_isLB hLG₀ _) (pull_isLB A₀.isLB _) E2
        (LBIso.trans (pull_isLB hLG₀ _) (pull_isLB hLG₀ _) (pull_isLB A₀.isLB _) E4
          (LBIso.trans (pull_isLB hLG₀ _) (pull_isLB hA₀g _) (pull_isLB A₀.isLB _) E3.symm E5)))
  have X2 : LBIso ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) (A₀.L.pull π) := pull_comp_iso X1 _
  have X3 : LBIso A.L ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) :=
    LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _) (pull_id_iso A.isLB)
      (LBIso.trans (pull_isLB A.isLB _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
        (pull_congr_iso A.isLB (by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]))
        (pull_pull_iso A.isLB _ _).symm)
  have hA : LBIso A.L (A₀.L.pull π) :=
    LBIso.trans A.isLB (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB A₀.isLB _) X3 X2
  have sπ := GlobalTheory.LamPull.exists_isSquare hπ.1.w
  have hΛ := GlobalTheory.LamPull.lbIso_lam_pull hπ A₀.isLB A.isLB hA sπ
  have hΛA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hΛA₀ : (abelian₂ A₀.A A₀.L).IsLB := DVR.linComb_isLB _ A₀.isLB _ _
  refine ⟨π ≫ α₀, ⟨hπ.comp hO₁, _ ≫ α₀₂, ⟨?_, ?_⟩,
    LBIso.trans hΛA (pull_isLB hΛA₀ _) (pull_isLB c.isLB _) hΛ (pull_comp_iso hΛ₀ _)⟩, ?_⟩
  · rw [Category.assoc, sα₀.1, ← Category.assoc, sπ.1, Category.assoc]
  · rw [Category.assoc, sα₀.2, ← Category.assoc, sπ.2, Category.assoc]
  · intro Z x x₀ hx
    have : Mono (jK R) := GlobalTheory.GenericBundleDescent.mono_jK R
    have : Mono p₀ := pullback.fst_of_mono
    have h1 : x ≫ U.gen.inv.left ≫ κG = x₀ ≫ U₀.gen.inv.left := by
      apply (cancel_mono p₀).1
      simp only [Category.assoc, hκf]
      exact hx
    show x ≫ (U.gen.inv.left ≫ κG ≫ U₀.gen.hom.left) ≫ α₀ = x₀ ≫ α₀
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Category.assoc x, h1]
    simp only [Category.assoc]
    rw [← Category.assoc U₀.gen.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem degPre_c_zero {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) : D.c 0 = 1 := by
  have h : D.c 0 * D.c 0 = D.c 0 := by
    have := D.c_add 0 0
    rw [add_zero] at this
    exact this.symm
  exact mul_eq_left.1 h

theorem val_tau_zero_zero {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (hT : D.TauBimult)
    (z : (TK V).left) (J : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    val (D.tau 0 0) (𝟙 _) z J = 1 := by
  have h := (val_mul hJ _ _ (𝟙 _)).symm.trans ((val_corr hJ (hT 0 0 0) (𝟙 _)).trans (val_mul hJ _ _ (𝟙 _)))
  have e : ∀ a : D.X, a = 0 → val (D.tau a 0) (𝟙 _) z J = val (D.tau 0 0) (𝟙 _) z J := by
    rintro a rfl; rfl
  rw [e _ (add_zero 0)] at h
  have f : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 0 0 0)) (𝟙 _) z J = 1 := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
    show cubV D.cub z J (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0) = 1
    rw [degPre_c_zero, MonObj.comp_one]
    exact (isCub_cubV D.cub hJ).face _ _
  rw [f, _root_.mul_one] at h
  exact mul_eq_left.1 h.symm

theorem tautBase_c₀_zero {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) : T.c₀ 0 = 1 :=
  mul_eq_left.1 ((T.c₀_add 0 0).symm.trans (by rw [add_zero]))

theorem val_τ₀_zero_zero {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W)
    (z : (𝟙_ (Over (Sp W))).left) (J) (hJ : Good T.M.L z J) : val (T.τ₀ 0 0) (𝟙 _) z J = 1 := by
  have h := T.τ₀_add 0 0 0 z J hJ
  have f : cubV T.cub z J (T.c₀ 0) (T.c₀ 0) (T.c₀ 0) = 1 := by
    rw [tautBase_c₀_zero]; exact (isCub_cubV T.cub hJ).face _ _
  rw [f, _root_.mul_one, add_zero] at h
  exact mul_eq_left.1 h.symm

theorem val_τ₀_zero_at {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {Z : Scheme.{0}}
    (r : Z ⟶ (𝟙_ (Over (Sp W))).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (hJ : Good T.M.L z J) :
    val (T.τ₀ 0 0) r z J = 1 := by
  have c : LB.Gen.Corr T.M.L _ _ _ _ (T.τ₀ 0 0) (LB.oneGen T.M.L) :=
    corr_of_val T.M.isLB fun y J' hJ' => (val_τ₀_zero_zero T y J' hJ').trans (val_one _).symm
  exact (val_corr hJ c r).trans (val_one r)

theorem lamVal_origin_of_from : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (z : (TK V).left) (J : ((TK V).left ⟶ T.B.left) → T.M.L.ι) (J' : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι), Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : TK V ⟶ D.P.A) (1 : TK V ⟶ D.P.A)).left z J J' = 1 := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hT hF z J J' hJ hJ'
  obtain ⟨k, hk, hv⟩ := hF.2.2.2.2 0 0
  have h := hv z J J' hJ hJ'
  have k1 : k = 1 := by
    ext
    rw [hk]
    simp
  have e0 : ((n : ℤ) • e 0) = 0 := by rw [map_zero, smul_zero]
  rw [k1, val_tau_zero_zero D hT z J' hJ', e0, val_τ₀_zero_at T _ z J hJ, degPre_c_zero, MonObj.comp_one] at h
  have u1 : unitOn (1 : (FractionRing V)ˣ) = 1 := map_one _
  simp only [u1, map_one, _root_.one_mul, _root_.mul_one] at h
  exact h.symm

end GlobalTheory.TInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem gm_spMap_unitOn_top {A B : Type} [CommRing A] [CommRing B] (m : A →+* B) (z : Sp B) (k : Aˣ) :
    gm (spMap m) z ⊤ (unitOn k) = gm (𝟙 (Sp B)) z ⊤ (unitOn (Units.map m.toMonoidHom k)) := by
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
  have nat := congrArg (fun q => q.hom k.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom m))
  exact congrArg ((Sp B).presheaf.germ ⊤ z trivial).hom nat.symm

theorem from_pull : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D), Function.Injective f → From T ω s ε n D₀.toPre e β ββ w → ∃ ββ' w', From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ Jd D₀ ω s e β ββ w f D hD hf hF
  obtain ⟨pb, sq, gen, hc, hτ⟩ := hF
  have hR : ∃ (β₂₁ : (G2 D.P.A).left ⟶ (G2 D₀.toPre.P.A).left)
      (w₁ : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D₀.toPre.P.A D₀.toPre.P.L).pull β₂₁)),
      IsGrpPullback D.P.A D₀.toPre.P.A (spMap f) (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ∧
      IsSquare (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) β₂₁ ∧ w₁.IsGen ∧
      (∀ a, (D.c a).left ≫ (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) =
        spMap f ≫ (D₀.toPre.c (hD.xe a)).left) ∧
      ∀ κ : (TK V).left ⟶ (TK R).left, κ ≫ jK R = jK V ≫ spMap f → ∀ a b z J J', Good D₀.toPre.P.L z J →
        Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' =
          lamVal w₁ (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J J' *
            val (D₀.toPre.tau (hD.xe a) (hD.xe b)) κ z J := by
    obtain ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, tau₁⟩ := GlobalTheory.MumFam.refAt_pull R V f hf Jd D₀ D hD
    exact ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, fun κ hκ a b z J J' hJ hJ' => (tau₁ κ hκ a b z J J' hJ hJ').trans
      (congrArg _ ((Wit.exists_tau D₀.toPre (hD.xe a) (hD.xe b)).choose_spec.2 _ κ z J hJ))⟩
  obtain ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, tau₁⟩ := hR
  have hΛT : (abelian₂ T.B T.M.L).IsLB := DVR.linComb_isLB _ T.M.isLB _ _
  have hΛ₀ : (abelian₂ D₀.toPre.P.A D₀.toPre.P.L).IsLB := DVR.linComb_isLB _ D₀.toPre.P.isLB _ _
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  obtain ⟨w', T3⟩ := exists_comp hΛ₀ w w₁ ((isGen_iff _).1 gen) ((isGen_iff _).1 gen₁) hΛT hΛ
  refine ⟨β₂₁ ≫ ββ, w', (IsGrpPullback.comp pb₁ pb).congr (GlobalTheory.HalfBC.spMap_comp_spMap' ω f) rfl, ⟨?_, ?_⟩,
    (isGen_iff _).2 (T3.pgen_comp hΛ₀ ((isGen_iff _).1 gen) ((isGen_iff _).1 gen₁)), fun a => ?_, fun a b => ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (β₂₁ ≫ ·) sq.1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) sq₁.1).trans (Category.assoc _ _ _))))
  · exact (Category.assoc _ _ _).trans ((congrArg (β₂₁ ≫ ·) sq.2).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) sq₁.2).trans (Category.assoc _ _ _))))
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ β) (c₁ a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (spMap f ≫ ·) (hc (hD.xe a))).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (GlobalTheory.HalfBC.spMap_comp_spMap' ω f))))))
  · obtain ⟨k₀, hk₀, hv₀⟩ := hτ (hD.xe a) (hD.xe b)
    let m : FractionRing R →+* FractionRing V := IsLocalization.map (FractionRing V) f (M := nonZeroDivisors R)
      (T := nonZeroDivisors V) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)
    have hm : ∀ r, m (algebraMap R (FractionRing R) r) = algebraMap V (FractionRing V) (f r) := fun r =>
      IsLocalization.map_eq _ _
    refine ⟨Units.map m.toMonoidHom k₀, ?_, fun z Jt J' hJt hJ' => ?_⟩
    · show m k₀ = _
      rw [hk₀, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow₀, hm]
      rfl
    · let κ : (TK V).left ⟶ (TK R).left := spMap m
      have hκ : κ ≫ jK R = jK V ≫ spMap f := by
        show spMap m ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap V (FractionRing V)) ≫ spMap f
        rw [GlobalTheory.HalfBC.spMap_comp_spMap', GlobalTheory.HalfBC.spMap_comp_spMap']
        congr 1
        exact RingHom.ext hm
      choose J₁ hJ₀ using fun χ : (TK V).left ⟶ D₀.toPre.P.A.left => exists_chart D₀.toPre.P.isLB (χ z)
      have hJ₁ : Good D₀.toPre.P.L z J₁ := hJ₀
      have t₁ := tau₁ κ hκ a b z J₁ J' hJ₁ hJ'
      have n₁ : val (D₀.toPre.tau (hD.xe a) (hD.xe b)) (κ ≫ 𝟙 _) z J₁ = Units.map (κ.stalkMap z).hom.toMonoidHom
          (val (D₀.toPre.tau (hD.xe a) (hD.xe b)) (𝟙 _) (κ z) (fun ψ => J₁ (κ ≫ ψ))) :=
        Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) κ z J₁ hJ₁).2.2.1 _)
      rw [Category.comp_id] at n₁
      have h₀ := hv₀ (κ z) (fun ψ => Jt (κ ≫ ψ)) (fun ψ => J₁ (κ ≫ ψ)) (fun ψ => hJt (κ ≫ ψ)) (fun ψ => hJ₁ (κ ≫ ψ))
      have h₁ := (congrArg (Units.map (κ.stalkMap z).hom.toMonoidHom) h₀).trans
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_mul _ _ _)))
      have g₁ : Units.map (κ.stalkMap z).hom.toMonoidHom (gm (𝟙 (TK R).left) (κ z) ⊤ (unitOn k₀)) =
          gm (𝟙 (TK V).left) z ⊤ (unitOn (Units.map m.toMonoidHom k₀)) := by
        rw [← GlobalTheory.ConstFam.gm_comp_stalkMap κ (𝟙 _) z ⊤ trivial, Category.comp_id]
        exact gm_spMap_unitOn_top m z k₀
      have g₂ := (GlobalTheory.HalfBC.lamVal_comp w κ
        (lift (toUnit (TK R) ≫ D₀.toPre.c (hD.xe a)) (toUnit (TK R) ≫ D₀.toPre.c (hD.xe b))).left z Jt J₁ hJt hJ₁).symm
      have g₃ : Units.map (κ.stalkMap z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b)))
          ((TK R).hom ≫ spMap ω) (κ z) (fun ψ => Jt (κ ≫ ψ))) =
          val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b))) (κ ≫ (TK R).hom ≫ spMap ω) z Jt :=
        (Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ _ κ z Jt hJt).2.2.1 _)).symm
      have hb : κ ≫ (TK R).hom ≫ spMap ω = (TK V).hom ≫ spMap (f.comp ω) := by
        show κ ≫ jK R ≫ spMap ω = jK V ≫ spMap (f.comp ω)
        rw [← Category.assoc, hκ, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
      have hx : ∀ χ, (toUnit (TK V) ≫ D.c χ).left ≫ (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) =
          κ ≫ (toUnit (TK R) ≫ D₀.toPre.c (hD.xe χ)).left := fun χ => by
        show (jK V ≫ (D.c χ).left) ≫ _ = κ ≫ jK R ≫ (D₀.toPre.c (hD.xe χ)).left
        rw [Category.assoc, c₁ χ, ← Category.assoc, ← Category.assoc, hκ]
      have hP : κ ≫ (lift (toUnit (TK R) ≫ D₀.toPre.c (hD.xe a)) (toUnit (TK R) ≫ D₀.toPre.c (hD.xe b))).left =
          (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left ≫ β₂₁ := by
        refine Eq.symm ?_
        apply pullback.hom_ext
        · show _ ≫ (fst D₀.toPre.P.A D₀.toPre.P.A).left = _ ≫ (fst D₀.toPre.P.A D₀.toPre.P.A).left
          rw [Category.assoc, sq₁.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
            lift_fst]
          exact hx a
        · show _ ≫ (snd D₀.toPre.P.A D₀.toPre.P.A).left = _ ≫ (snd D₀.toPre.P.A D₀.toPre.P.A).left
          rw [Category.assoc, sq₁.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
            lift_snd]
          exact hx b
      have key : ∀ p : (TK V).left ⟶ (G2 D.P.A).left,
          lamVal w' p z Jt J' = lamVal w (p ≫ β₂₁) z Jt J₁ * lamVal w₁ p z J₁ J' := by
        intro p
        have t := T3 _ p z (fun I => Jt (p ≫ (β₂₁ ≫ ββ) ≫ GlobalTheory.PrimCocycle.lamφ T.B I))
          (fun I => J₁ ((p ≫ β₂₁) ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
          (fun I => J' (p ≫ GlobalTheory.PrimCocycle.lamφ D.P.A I))
          (Set.mem_iInter.2 fun I => hJt _) (Set.mem_iInter.2 fun I => hJ₁ _) (Set.mem_iInter.2 fun I => hJ' _)
        refine t.trans (congrArg₂ (· * ·) ?_ ?_)
        · show _ = gw w (p ≫ β₂₁) z (fun I => Jt ((p ≫ β₂₁) ≫ ββ ≫ GlobalTheory.PrimCocycle.lamφ T.B I))
            (fun I => J₁ ((p ≫ β₂₁) ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
          simp only [Category.assoc]
        · show _ = gw w₁ p z (fun I => J₁ (p ≫ β₂₁ ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
            (fun I => J' (p ≫ GlobalTheory.PrimCocycle.lamφ D.P.A I))
          simp only [Category.assoc]
      show _ = _ * (_ * val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b))) _ z Jt)
      rw [t₁, n₁, h₁, g₁, g₂, g₃, hP, hb, key]
      ac_rfl

end GlobalTheory.TInj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj
attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qImg_lattice : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (J : Ideal V), AdmBase V J → ∀ (D₁ D₂ : DegData V J) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], Match D₁.toPre D₂.toPre b φ F → ∀ (k : ℕ) (p : QkPt D₁.toPre F k) (p' : QkPt D₂.toPre F k), Act D₁.toPre D₂.toPre b φ.symm.toAddMonoidHom p.g p'.g → p'.y = φ p.y := by
  intro V _ _ _ J hJ D₁ D₂ b φ F _ _ _ hM k p p' hA
  obtain ⟨hmon, -, -, hnrm, hlast⟩ := hM
  obtain ⟨hex, hadd, -⟩ := GlobalTheory.Mum.Two.act_two_hom V D₁.toPre D₂.toPre b φ.symm.toAddMonoidHom hmon hnrm F
  choose α hα hαu using hex
  let f : GtPtF D₁.toPre F →+ GtPtF D₂.toPre F := AddMonoidHom.mk' α fun x y =>
    (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1
      (hadd x y (x + y) (α x) (α y) (α (x + y)) ((GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl) (hα x) (hα y) (hα _))
  obtain ⟨h₁, hn₁, hi₁⟩ := p.eq
  obtain ⟨h₂, hn₂, hi₂⟩ := p'.eq
  obtain ⟨g', hg'A, hg'I⟩ := hlast p.y h₁ hi₁
  have e₁ : h₁ = k • p.g := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn₁
  have e₂ : h₂ = k • p'.g := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn₂
  have ep : p'.g = f p.g := hαu p.g p'.g hA
  have eg : g' = f h₁ := hαu h₁ g' hg'A
  have : g' = h₂ := by rw [eg, e₁, map_nsmul, ← ep, e₂]
  rw [← this] at hi₂
  exact GlobalTheory.IotaInj.main GlobalTheory.firstFiveLaws V J hJ D₂ F p'.y (φ p.y) g' hi₂ hg'I

end GlobalTheory.TInj

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.PFactorPull


open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.FactorPull in
theorem algebraic_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X) (β : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B (spMap θ) β → (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) → ∃ (inc : Q'.B ⟶ D₁.P.A) (pr : D₁.P.A ⟶ Q'.B) (xi : Q'.X →+ D₁.X) (xp : D₁.X →+ Q'.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left ∧ (∀ y, hD.xe (xi y) = F.xi (ex y)) ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧ (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) ∧ (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁.X, ∃ y, star F.e • z = star F.e • F.f • xi y) := by
  intro R V _ _ _ _ θ Q D₀ F D₁ hD _ o₁ hx ho Q' ex β gp hcβ
  have gp' := pull_grp hD
  obtain ⟨inc, mi, hi⟩ := hom_pull gp gp' F.inc F.inc_hom
  obtain ⟨pr, mp, hp⟩ := hom_pull gp' gp F.pr F.pr_hom
  obtain ⟨xi, hxi⟩ : ∃ xi : Q'.X →+ D₁.X, ∀ y, hD.xe (xi y) = F.xi (ex y) :=
    ⟨hD.xe.symm.toAddMonoidHom.comp (F.xi.comp ex.toAddMonoidHom), fun y => hD.xe.apply_symm_apply _⟩
  obtain ⟨xp, hxp⟩ : ∃ xp : D₁.X →+ Q'.X, ∀ y, ex (xp y) = F.xp (hD.xe y) :=
    ⟨ex.symm.toAddMonoidHom.comp (F.xp.comp hD.xe.toAddMonoidHom), fun y => ex.apply_symm_apply _⟩
  have hc : ∀ y, D₁.c (xi y) = Q'.c y ≫ inc := fun y => ext_pull gp' (by
    rw [hD.c_pr, hxi, F.c_xi, Over.comp_left, Over.comp_left, Category.assoc, hi, ← Category.assoc (Q'.c y).left,
      hcβ, Category.assoc]
    try rfl)
  refine ⟨inc, pr, xi, xp, hi, hxi, mi, mp, ext_pull gp ?_, ext_pull gp' ?_, fun y => ex.injective ?_,
    fun y => hD.xe.injective ?_, hc, fun y y' h => ?_, fun z => ?_⟩
  · rw [Over.comp_left, Category.assoc, hp, ← Category.assoc, hi, Category.assoc, ← Over.comp_left, F.inc_pr,
      Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
  · rw [Over.comp_left, Category.assoc, hi, ← Category.assoc, hp, Category.assoc, ← Over.comp_left, F.pr_inc, ho]
  · rw [hxp, hxi, F.xp_xi]
  · rw [hxi, hxp, F.xi_xp, hx]
  · have h' := congrArg hD.xe h
    simp only [hx, hxi] at h'
    exact ex.injective (F.inj h')
  · obtain ⟨y, hy⟩ := F.onto (hD.xe z)
    refine ⟨ex.symm y, hD.xe.injective ?_⟩
    rw [hx, hx, hx, hxi, ex.apply_symm_apply, hy]

end GlobalTheory.PFactorPull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitaryRechartings_common_geometricFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (σ : X.Ω₁ →+* X.Ω₁) (s : X.M.Z ⟶ X.M.Z), X.M.pt ≫ s = spMap σ ≫ X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X.M.Z) (S' S'' : ThetaSys X.o₁ X.Ω₁) (ρ' : S'.Real) (ρ'' : S''.Real), S'.R ≤ X.M.O (y (closedPoint (PadicAlgCl p))) → S''.R ≤ X.M.O ((y ≫ s) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : S'.R →+* PadicAlgCl p) (y₁ : S''.R →+* PadicAlgCl p), (∀ a : S'.R, y₀ a = X.M.val y a) → (∀ a : S''.R, y₁ a = X.M.val (y ≫ s) a) → ∀ (u : ρ'.UTest p y₀) (u₁ : ρ''.UTest p y₁) (u' : Sp (ratHull S'.R) ⟶ Xo.XF cf) (u'' : Sp (ratHull S''.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S'.R))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (G'' : Over (Sp (ratHull S''.R))) (_ : GrpObj G'') (α'' : G''.left ⟶ ρ''.P.A.left) (β'' : G''.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat S'.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → IsGrpPullback G'' ρ''.P.A (spMap (toRat S''.R)) α'' → IsGrpPullback G'' Xo.univ.t.G (u'' ≫ pullback.fst _ _) β'' → LBIso (ρ''.P.L.pull α'') (Xo.univ.t.PP.L.pull β'') → ∀ (W₀ : Over (Sp X.Ω₁)) (_ : GrpObj W₀) (k₀ : W₀.left ⟶ G.left) (k₀'' : W₀.left ⟶ G''.left), IsGrpPullback W₀ G (spMap (ratHull S'.R).val.toRingHom) k₀ → IsGrpPullback W₀ G'' (spMap (σ.comp (ratHull S''.R).val.toRingHom)) k₀'' → k₀ ≫ β = k₀'' ≫ β'' → ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u₁.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u₁.A.A (spMap (algebraMap (FractionRing u₁.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u₁.A.L.pull a') ∧ (∀ (k' : S'.Gam) (k'' : S''.Gam) (w : Sp X.Ω₁ ⟶ W₀.left), w ≫ W₀.hom = 𝟙 _ → w ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt k').left → w ≫ k₀'' ≫ α'' = spMap (σ.comp S''.R.val.toRingHom) ≫ (ρ''.pt k'').left → ∃ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u₁.V) (PadicAlgCl p) ⟶ u₁.A.A), v ≫ P₀.A.hom = 𝟙 _ ∧ v ≫ a = x.left ∧ v ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt k').left ∧ x'.left ≫ u₁.φ = spMap y₁ ≫ (ρ''.pt k'').left) ∧ ∀ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (g : Sp (PadicAlgCl p) ⟶ G.left) (h : Sp (PadicAlgCl p) ⟶ G''.left), v ≫ P₀.A.hom = 𝟙 _ → g ≫ α = v ≫ a ≫ u.φ → h ≫ α'' = v ≫ a' ≫ u₁.φ → g ≫ β = h ≫ β'' := by
  first | exact @GlobalTheory.UPoinc.USpreadU.main | exact GlobalTheory.UPoinc.USpreadU.main | (intros; apply GlobalTheory.UPoinc.USpreadU.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.unitaryApproxPoincareSeriesAt_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (φ : InvFun (𝓞 E)) (d m : ℕ), 1 ≤ m → UApproxAt X₁ φ d → UApproxAt X₁ φ (d * m) := by
  first | exact @GlobalTheory.UPoinc.uApproxAt_mul | exact GlobalTheory.UPoinc.uApproxAt_mul | (intros; apply GlobalTheory.UPoinc.uApproxAt_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eighth_power_fibre_iso_eq_coordinatewise_power : ∀ (l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ j, 1 ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsUnit (l : V₁) → ∀ (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → ∃ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ ∧ ∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  first | exact @GlobalTheory.PoincDiag.fibreIso_eq_pow | exact GlobalTheory.PoincDiag.fibreIso_eq_pow | (intros; apply GlobalTheory.PoincDiag.fibreIso_eq_pow <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_period_generator_on_open : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (ψW : PsiOn D W) (a b : D.X), ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε), t.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ W.toScheme) (z : Z) J, Good D.P.L z J → val t r z J = val (ψW.tau a b) r z J) ∧ ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ z J, Good D.P.L z J → val t lam z J = val (D.tau a b) (𝟙 _) z J := by
  first | exact @GlobalTheory.exists_tau_onOpen | exact GlobalTheory.exists_tau_onOpen | (intros; apply GlobalTheory.exists_tau_onOpen <;> assumption)
end
