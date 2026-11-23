module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
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
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualApprox

variable (R : Type) [CommRing R]

abbrev spO (C : Type) [CommRing C] [Algebra R C] : Over (Sp R) := Over.mk (spMap (algebraMap R C))

variable {R}

def spOMap {C C' : Type} [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (f : C →ₐ[R] C') :
    spO R C' ⟶ spO R C :=
  Over.homMk (spMap f.toRingHom) (Spread.spMap_algHom_comp f)

@[simp]
theorem spOMap_left {C C' : Type} [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (f : C →ₐ[R] C') :
    (spOMap f).left = spMap f.toRingHom := rfl

theorem spOMap_comp {C C' C'' : Type} [CommRing C] [CommRing C'] [CommRing C''] [Algebra R C] [Algebra R C']
    [Algebra R C''] (f : C →ₐ[R] C') (g : C' →ₐ[R] C'') : spOMap g ≫ spOMap f = spOMap (g.comp f) := by
  ext1
  simp only [Over.comp_left, spOMap_left]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable (R) (C : Type) [CommRing C] [Algebra R C]

abbrev stage (s : Finset C) : Over (Sp R) := spO R (Algebra.adjoin R (s : Set C))

def toStage (s : Finset C) : spO R C ⟶ stage R C s := spOMap (Algebra.adjoin R (s : Set C)).val

variable {R C}

def stageMap {s t : Finset C} (h : s ⊆ t) : stage R C t ⟶ stage R C s :=
  spOMap (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h)))

theorem toStage_stageMap {s t : Finset C} (h : s ⊆ t) : toStage R C t ≫ stageMap h = toStage R C s := by
  rw [toStage, stageMap, spOMap_comp, toStage]
  rfl

theorem whiskerLeft_toStage_left (X : Over (Sp R)) (s : Finset C) :
    (X ◁ toStage R C s).left = Spread.bcMap X.hom (Algebra.adjoin R (s : Set C)).val :=
  Spread.eq_bcMap X.hom _ (Over.whiskerLeft_left_fst _) (Over.whiskerLeft_left_snd _)

theorem whiskerLeft_stageMap_left (X : Over (Sp R)) {s t : Finset C} (h : s ⊆ t) :
    (X ◁ stageMap h).left = Spread.bcMap X.hom (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h))) :=
  Spread.eq_bcMap X.hom _ (Over.whiskerLeft_left_fst _) (Over.whiskerLeft_left_snd _)

instance (s : Finset C) : IsAffine (stage R C s).left := by
  dsimp; infer_instance

theorem locallyOfFiniteType_stage (s : Finset C) : LocallyOfFiniteType (stage R C s).hom := by
  dsimp
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  show RingHom.FiniteType (algebraMap R (Algebra.adjoin R (s : Set C)))
  rw [RingHom.finiteType_algebraMap, ← Subalgebra.fg_iff_finiteType]
  exact Subalgebra.fg_adjoin_finset s


open GlobalTheory.CechPic in
theorem exists_lb_stage (X : Over (Sp R)) [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (N : LB (X ⊗ spO R C).left) (hN : N.IsLB) :
    ∃ (s : Finset C) (M : LB (X ⊗ stage R C s).left), M.IsLB ∧ LBIso N (M.pull (X ◁ toStage R C s).left) := by
  classical
  let ρ : ∀ s : (Finset C)ᵒᵖ, (X ⊗ spO R C).left ⟶ (Spread.bcDiagram X.hom C).obj s := fun s =>
    (Spread.bcCone X.hom C).π.app s
  have w : ∀ {s t} (g : s ⟶ t), ρ s ≫ (Spread.bcDiagram X.hom C).map g = ρ t := fun g =>
    ((Spread.bcCone X.hom C).w g)
  have hc : IsLimit (schemeConeOfFamily _ ρ w) := Spread.isLimitBcCone X.hom C
  obtain ⟨s, M, hM, hiso, -⟩ := LBLimit.exists_lb_of_isLimit _ ρ w hc N hN
  refine ⟨s.unop, M, hM, ?_⟩
  rw [whiskerLeft_toStage_left]
  exact hiso


open GlobalTheory.CechPic in
theorem exists_stage_pull_eq (X : Over (Sp R)) [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (s : Finset C) (c c' : Pic (X ⊗ stage R C s).left)
    (h : CechPic.pull (X ◁ toStage R C s).left c = CechPic.pull (X ◁ toStage R C s).left c') :
    ∃ (t : Finset C) (hst : s ⊆ t),
      CechPic.pull (X ◁ stageMap hst).left c = CechPic.pull (X ◁ stageMap hst).left c' := by
  classical
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨L', hL', rfl⟩ := cls_surj c'
  let ρ : ∀ s : (Finset C)ᵒᵖ, (X ⊗ spO R C).left ⟶ (Spread.bcDiagram X.hom C).obj s := fun s =>
    (Spread.bcCone X.hom C).π.app s
  have w : ∀ {s t} (g : s ⟶ t), ρ s ≫ (Spread.bcDiagram X.hom C).map g = ρ t := fun g =>
    ((Spread.bcCone X.hom C).w g)
  have hc : IsLimit (schemeConeOfFamily _ ρ w) := Spread.isLimitBcCone X.hom C
  have h' : LBIso (L.pull (X ◁ toStage R C s).left) (L'.pull (X ◁ toStage R C s).left) :=
    (cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).1 h
  rw [whiskerLeft_toStage_left] at h'
  have e : LBIso (L.pull (ρ (.op s))) (L'.pull (ρ (.op s))) := h'
  obtain ⟨j, f, hf⟩ := exists_lbIso_of_isLimit _ ρ w hc (i := .op s) L L' hL hL' e
  refine ⟨j.unop, f.unop.le, ?_⟩
  rw [whiskerLeft_stageMap_left]
  exact (cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).2 hf

end GlobalTheory.DualApprox

namespace GlobalTheory.DualApprox

open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon

variable {R : Type} [CommRing R] {C : Type} [CommRing C] [Algebra R C]

theorem whiskerLeft_eq_lift' {X Y Z : Over (Sp R)} (g : Y ⟶ Z) : X ◁ g = lift (fst X Y) (snd X Y ≫ g) := by
  ext1 <;> simp

theorem exists_fam_stage (A : Over (Sp R)) [GrpObj A] [QuasiCompact A.hom] [QuasiSeparated A.hom]
    (N : LB (A ⊗ spO R C).left) (hF : Fam A N) :
    ∃ (t : Finset C) (N₀ : LB (A ⊗ stage R C t).left), Fam A N₀ ∧ Same A N N₀ (𝟙 _) (toStage R C t) := by
  classical
  have hN := hF.isLB
  obtain ⟨s, M, hM, hiso⟩ := exists_lb_stage A N hN
  have H1 : ∀ (Y : Over (Sp R)) (x : Y ⟶ A) (y : Y ⟶ spO R C), evc hN x y = evc hM x (y ≫ toStage R C s) := by
    intro Y x y
    have e : cls N hN = cls _ (pull_isLB hM (A ◁ toStage R C s).left) := (cls_eq_iff hN (pull_isLB hM _)).2 hiso
    have e2 : cls _ (pull_isLB hM (A ◁ toStage R C s).left) = evc hM (fst A _) (snd A _ ≫ toStage R C s) := by
      rw [whiskerLeft_eq_lift']; rfl
    rw [evc, e, e2, pull_evc, lift_fst, lift_snd_assoc]
  have : QuasiCompact (A ⊗ A).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have : QuasiSeparated (A ⊗ A).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  let D : ∀ U : Over (Sp R), (M : LB (A ⊗ U).left) → M.IsLB → Pic ((A ⊗ A) ⊗ U).left := fun U M hM =>
    evc hM (fst (A ⊗ A) U ≫ fst A A * fst (A ⊗ A) U ≫ snd A A) (snd (A ⊗ A) U) -
      evc hM (fst (A ⊗ A) U ≫ fst A A) (snd (A ⊗ A) U) - evc hM (fst (A ⊗ A) U ≫ snd A A) (snd (A ⊗ A) U)
  have hD : CechPic.pull ((A ⊗ A) ◁ toStage R C s).left (D _ M hM) = CechPic.pull ((A ⊗ A) ◁ toStage R C s).left 0 := by
    rw [map_zero]
    simp only [D, map_sub, pull_evc, MonObj.comp_mul, ← Category.assoc, whiskerLeft_fst, whiskerLeft_snd]
    rw [← H1, ← H1, ← H1, (isAdditive_iff hN).1 hF.add]
    abel
  obtain ⟨t, hst, ht⟩ := exists_stage_pull_eq (A ⊗ A) s _ _ hD
  rw [map_zero] at ht
  let N₀ : LB (A ⊗ stage R C t).left := ev M (fst A _) (snd A _ ≫ stageMap hst)
  have hN₀ : N₀.IsLB := pull_isLB hM _
  have H2 : ∀ (Y : Over (Sp R)) (x : Y ⟶ A) (y : Y ⟶ stage R C t), evc hN₀ x y = evc hM x (y ≫ stageMap hst) := by
    intro Y x y
    rw [evc_ev hM, lift_fst, lift_snd_assoc]
  refine ⟨t, N₀, ⟨hN₀, (isAdditive_iff hN₀).2 fun Y a a' y => ?_⟩, ?_⟩
  · rw [H2, H2, H2]
    have e := congrArg (CechPic.pull (lift (lift a a') y).left) ht
    simp only [D, map_sub, map_zero, pull_evc, MonObj.comp_mul, ← Category.assoc, whiskerLeft_fst,
      whiskerLeft_snd] at e
    simp only [Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc] at e
    rw [sub_sub, sub_eq_zero] at e
    exact e
  · rw [same_iff hN hN₀, H2, Category.assoc, toStage_stageMap, ← H1, Category.comp_id]

end GlobalTheory.DualApprox

namespace GlobalTheory.DualApprox

open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon

theorem exists_fam_finiteType : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ∃ (T₀ : Over (Sp R)) (h : T ⟶ T₀) (N₀ : LB (A ⊗ T₀).left), IsAffine T₀.left ∧ LocallyOfFiniteType T₀.hom ∧ Fam A N₀ ∧ Same A N N₀ (𝟙 T) h := by
  intro R _ _ A _ hA T _ N hF
  have : IsProper A.hom := hA.proper
  letI : Algebra R Γ(T.left, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop).hom.toAlgebra
  let e : T ≅ spO R Γ(T.left, ⊤) := Over.isoMk T.left.isoSpec (by
    show T.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop).hom) = T.hom
    rw [CommRingCat.ofHom_hom, Spec.map_comp]
    simp only [Scheme.isoSpec, asIso_hom]
    rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id])
  have hN := hF.isLB
  let N' : LB (A ⊗ spO R Γ(T.left, ⊤)).left := ev N (fst A _) (snd A _ ≫ e.inv)
  have hN' : N'.IsLB := pull_isLB hN _
  have H : ∀ (Y : Over (Sp R)) (x : Y ⟶ A) (y : Y ⟶ spO R Γ(T.left, ⊤)),
      evc hN' x y = evc hN x (y ≫ e.inv) := by
    intro Y x y
    rw [evc_ev hN, lift_fst, lift_snd_assoc]
  have hF' : Fam A N' := ⟨hN', (isAdditive_iff hN').2 fun Y a a' y => by
    rw [H, H, H]
    exact (isAdditive_iff hN).1 hF.add _ _ _ _⟩
  obtain ⟨t, N₀, h₀, hs⟩ := exists_fam_stage A N' hF'
  refine ⟨stage R _ t, e.hom ≫ toStage R _ t, N₀, inferInstance, locallyOfFiniteType_stage t, h₀, ?_⟩
  rw [same_iff hN' h₀.isLB] at hs
  rw [same_iff hN h₀.isLB]
  have k := congrArg (CechPic.pull (A ◁ e.hom).left) hs
  rw [pull_evc, pull_evc, whiskerLeft_fst, ← Category.assoc, whiskerLeft_snd, Category.comp_id, H,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, ← Category.assoc, whiskerLeft_snd,
    Category.assoc] at k
  rw [Category.comp_id]
  exact k

end GlobalTheory.DualApprox
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem isPullback_prod_map {S : Scheme.{0}} (A : Over S) {V V' : Over S} (v : V ⟶ V') :
    IsPullback (lift (fst A V) (snd A V ≫ v)).left (snd A V).left (snd A V').left v.left := by
  have hT : IsPullback (fst A V).left (snd A V).left A.hom V.hom := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A V').left (snd A V').left A.hom V'.hom := IsPullback.of_hasPullback _ _
  have m₁ : (lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left = (fst A V).left := by
    rw [← Over.comp_left, lift_fst]
  have m₂ : (lift (fst A V) (snd A V ≫ v)).left ≫ (snd A V').left = (snd A V).left ≫ v.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hT' : IsPullback ((lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left) (snd A V).left A.hom
      (v.left ≫ V'.hom) := by
    rw [m₁, Over.w v]; exact hT
  exact IsPullback.of_right hT' m₂ hY

theorem isPullback_prod_kernel {S : Scheme.{0}} (A Y Y' W : Over S) (c : Y' ⟶ Y) (w₁ w₂ : W ⟶ Y')
    (hK : IsPullback w₁.left w₂.left c.left c.left) :
    IsPullback (lift (fst A W) (snd A W ≫ w₁)).left (lift (fst A W) (snd A W ≫ w₂)).left
      (lift (fst A Y') (snd A Y' ≫ c)).left (lift (fst A Y') (snd A Y' ≫ c)).left := by
  have Hc := isPullback_prod_map A c
  have H₂ := isPullback_prod_map A w₂
  have outer := H₂.flip.paste_horiz hK
  have e₁ : (lift (fst A W) (snd A W ≫ w₁)).left ≫ (snd A Y').left = (snd A W).left ≫ w₁.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have e₂ : (lift (fst A Y') (snd A Y' ≫ c)).left ≫ (snd A Y).left = (snd A Y').left ≫ c.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext hK.w
  refine IsPullback.of_right (h₁₂ := (snd A Y').left) (h₂₂ := (snd A Y).left) ?_ ?_ Hc.flip
  · rw [e₁, e₂]; exact outer
  · rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst, lift_fst, lift_snd_assoc,
      lift_snd_assoc, Category.assoc, Category.assoc, hw]

theorem same_of_fpqc : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (T U Y Y' : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left), Fam A N → Fam A M → ∀ (y : Y ⟶ T) (u : Y ⟶ U) (c : Y' ⟶ Y), Flat c.left → Surjective c.left → QuasiCompact c.left → Same A N M (c ≫ y) (c ≫ u) → Same A N M y u := by
  intro S A _ hA T U Y Y' N M hN hM y u c hfl hsu hqc hc
  rw [same_iff hN.isLB hM.isLB, ← sub_eq_zero]
  obtain ⟨L, hL, hcl⟩ := cls_surj (evc hN.isLB (fst A Y) (snd A Y ≫ y) - evc hM.isLB (fst A Y) (snd A Y ≫ u))
  rw [← hcl]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ Y).left), Triv (L.pull f) ↔
      CechPic.pull f (evc hN.isLB (fst A Y) (snd A Y ≫ y)) = CechPic.pull f (evc hM.isLB (fst A Y) (snd A Y ≫ u)) := by
    intro X f
    rw [← sub_eq_zero, ← map_sub, ← hcl, ← cls_pull hL f (pull_isLB hL f)]
    exact (cls_eq_zero_iff (pull_isLB hL f)).symm
  refine (cls_eq_zero_iff hL).2 ?_
  let F : A ⊗ Y' ⟶ A ⊗ Y := lift (fst A Y') (snd A Y' ≫ c)
  let e : Y ⟶ A ⊗ Y := lift 1 (𝟙 Y)
  let e' : Y' ⟶ A ⊗ Y' := lift 1 (𝟙 Y')
  have h0 : Triv (L.pull e.left) := by
    rw [key]
    simp only [e, pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [hN.add.evc_one hN.isLB, hM.add.evc_one hM.isLB]
  have h1 : Triv (L.pull F.left) := by
    rw [key]
    simp only [F, pull_evc, lift_fst, lift_snd_assoc]
    rw [same_iff hN.isLB hM.isLB] at hc
    simpa only [Category.assoc] using hc
  have hEF : e' ≫ F = c ≫ e := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [e, e', F]
  have hep : e' ≫ snd A Y' = 𝟙 Y' := lift_snd _ _

  have hT : IsPullback (fst A Y').left (snd A Y').left A.hom Y'.hom := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := IsPullback.of_hasPullback _ _
  have m₁ : F.left ≫ (fst A Y).left = (fst A Y').left := by rw [← Over.comp_left, lift_fst]
  have m₂ : F.left ≫ (snd A Y).left = (snd A Y').left ≫ c.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hT' : IsPullback (F.left ≫ (fst A Y).left) (snd A Y').left A.hom (c.left ≫ Y.hom) := by
    rw [m₁, Over.w c]; exact hT
  have H : IsPullback F.left (snd A Y').left (snd A Y).left c.left := IsPullback.of_right hT' m₂ hY
  have hF₁ : Flat F.left := MorphismProperty.of_isPullback H.flip hfl
  have hF₂ : Surjective F.left := MorphismProperty.of_isPullback H.flip hsu
  have hF₃ : QuasiCompact F.left := MorphismProperty.of_isPullback H.flip hqc

  let W : Over S := Over.mk (pullback.fst c.left c.left ≫ Y'.hom)
  let w₁ : W ⟶ Y' := Over.homMk (pullback.fst c.left c.left) rfl
  let w₂ : W ⟶ Y' := Over.homMk (pullback.snd c.left c.left) (by
    show pullback.snd c.left c.left ≫ Y'.hom = pullback.fst c.left c.left ≫ Y'.hom
    rw [← Over.w c, ← Category.assoc, ← pullback.condition, Category.assoc])
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext pullback.condition
  have hK : IsPullback w₁.left w₂.left c.left c.left := IsPullback.of_hasPullback c.left c.left
  let g₁ : A ⊗ W ⟶ A ⊗ Y' := lift (fst A W) (snd A W ≫ w₁)
  let g₂ : A ⊗ W ⟶ A ⊗ Y' := lift (fst A W) (snd A W ≫ w₂)
  have hKP : IsPullback g₁.left g₂.left F.left F.left := isPullback_prod_kernel A Y Y' W c w₁ w₂ hK
  have hg : g₁.left ≫ F.left = g₂.left ≫ F.left := hKP.w

  obtain ⟨g, hgg⟩ := h0
  obtain ⟨t, ht⟩ := h1
  have n₁ : (snd A Y' ≫ e').left ≫ F.left = (snd A Y' ≫ c).left ≫ e.left := by
    rw [← Over.comp_left, ← Over.comp_left, Category.assoc, hEF, Category.assoc]
  obtain ⟨t', ht', hv⟩ := exists_gen hL (K' := PUnit) (φ' := fun _ => F.left) (ε' := fun _ => 1)
    (fun U _ k => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, n₁]
      simp)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (snd A Y' ≫ e').left)))
      (LB.pullGen L _ _ g (snd A Y' ≫ c).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hgg _))
  have norm : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y'.left) (z : Z) (J), Geo.Tor.Good L z J →
      val t' (r ≫ e'.left) z J = val g (r ≫ c.left) z J := by
    intro Z r z J hJ
    have a₁ : (r ≫ e'.left) ≫ (snd A Y' ≫ e').left = r ≫ e'.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    have a₂ : (r ≫ e'.left) ≫ (snd A Y' ≫ c).left = r ≫ c.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    rw [hv Z _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, a₁, a₂, mul_inv_cancel,
      _root_.one_mul]
  refine GlobalTheory.T.lineBundle_trivial_of_generator_fpqc_descent L hL F.left hF₁ hF₂ hF₃ g₁.left g₂.left hKP t' ht' (fun z J hJ => ?_)
  let o : W ⟶ A ⊗ W := lift 1 (𝟙 W)
  have hg1 : o.left ≫ g₁.left = w₁.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₁, e']
  have hg2 : o.left ≫ g₂.left = w₂.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₂, e']
  have ho : o.left ≫ (snd A W).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have hwc : w₁.left ≫ c.left = w₂.left ≫ c.left := by rw [← Over.comp_left, ← Over.comp_left, hw]
  have key2 := gen_unique' hL (φ := fun _ : PUnit => g₁.left ≫ F.left) (ε := fun _ => (1 : ℤ))
    (φ' := fun _ : PUnit => g₂.left ≫ F.left) (ε' := fun _ => 1)
    (fun U _ k => by simp only [hg]) (snd A W).left o.left ho (surj_snd GlobalTheory.SemiRigid.globalFns hA W)
    (u := LB.pullGen L _ _ t' g₁.left) (u' := LB.pullGen L _ _ t' g₂.left)
    (DVR.pullGen_isGen _ _ _ _ ht' _) (DVR.pullGen_isGen _ _ _ _ ht' _)
    (fun y I hI => by rw [val_pull hI, val_pull hI, hg1, hg2, norm _ _ _ _ hI, norm _ _ _ _ hI, hwc])
    _ (𝟙 _) z J hJ
  rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at key2

end GlobalTheory.DualCon
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistKerFinite

theorem evc_lam {S : Scheme.{0}} {A Y : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    (x y : Y ⟶ A) : evc hP x y = lam (cls L hL) x y := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem add_inv_eq_of_same {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hL : L.IsLB) {N : LB (A ⊗ T).left} (hN : N.IsLB) (a a' : Y ⟶ A) (t : Y ⟶ T)
    (h₁ : Same A (abelian₂ A L) N a t) (h₂ : Same A (abelian₂ A L) N a' t) :
    CechPic.pull a.left (cls L hL) + CechPic.pull (a⁻¹).left (cls L hL) =
      CechPic.pull a'.left (cls L hL) + CechPic.pull (a'⁻¹).left (cls L hL) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e := ((same_iff hP hN a t).1 h₁).trans ((same_iff hP hN a' t).1 h₂).symm
  rw [evc_lam hL hP, evc_lam hL hP] at e
  have e' := congrArg (CechPic.pull (lift (a⁻¹ * a'⁻¹) (𝟙 Y)).left) e
  simp only [pull_lam, lift_fst, lift_snd_assoc, Category.id_comp] at e'
  simp only [lam] at e'
  rw [show a⁻¹ * a'⁻¹ * a = a'⁻¹ by rw [mul_right_comm, inv_mul_cancel, _root_.one_mul],
    show a⁻¹ * a'⁻¹ * a' = a⁻¹ from inv_mul_cancel_right _ _] at e'
  linear_combination (norm := abel) e'.symm

theorem isFinite_twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left := by
  intro R _ _ A _ hB L hL hA T _ _ N hN H h hh hH
  haveI := hB.comm
  have := hB.proper
  obtain ⟨d, -, n, s, hc, ha⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R A L hL).1 hA
  have hAT : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback A.hom T.hom
  have : IsProper (snd A T).left := MorphismProperty.of_isPullback hAT inferInstance
  have : IsAffineHom (fst A T).left := MorphismProperty.of_isPullback hAT.flip inferInstance
  let f : H.left ⟶ T.left := (h ≫ snd A T).left
  have hf : f ≫ T.hom = H.hom := Over.w (h ≫ snd A T)
  have : IsProper f := inferInstanceAs (IsProper (h.left ≫ (snd A T).left))
  change IsFinite f
  suffices LocallyQuasiFinite f from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (f ⁻¹' {z}) with h0 | ⟨x₀, hx₀⟩
  · rw [h0]; exact Set.finite_empty
  let K : Type := H.left.residueField x₀
  let y₀ : Spec (CommRingCat.of K) ⟶ H.left := H.left.fromSpecResidueField x₀
  let g : Spec (CommRingCat.of K) ⟶ T.left := y₀ ≫ f
  let π : pullback f g ⟶ H.left := pullback.fst f g
  let q : pullback f g ⟶ Spec (CommRingCat.of K) := pullback.snd f g
  let Z : Scheme.{0} := pullback f g
  have hpb : IsPullback π q f g := IsPullback.of_hasPullback f g
  have : IsProper q := MorphismProperty.of_isPullback hpb inferInstance
  have : IsAffineHom π := MorphismProperty.of_isPullback hpb.flip inferInstance
  let P : Over (Sp R) := Over.mk (y₀ ≫ H.hom)
  let Q : Over (Sp R) := Over.mk (π ≫ H.hom)
  let yo : P ⟶ H := Over.homMk y₀ rfl
  let qo : Q ⟶ P := Over.homMk q (by
    show q ≫ y₀ ≫ H.hom = π ≫ H.hom
    rw [← hf, ← Category.assoc π, hpb.w]
    simp only [g, Category.assoc])
  let p₁ : Q ⟶ H := Over.homMk π rfl
  have hpt : p₁ ≫ h ≫ snd A T = qo ≫ yo ≫ h ≫ snd A T := by
    ext
    exact hpb.w
  let w : H ⟶ A := h ≫ fst A T
  have hs₁ : Same A (abelian₂ A L) N (p₁ ≫ w) (p₁ ≫ h ≫ snd A T) :=
    (hH _ _ _).2 ⟨p₁, by ext <;> simp [w]⟩
  have hs₂ : Same A (abelian₂ A L) N (qo ≫ yo ≫ w) (p₁ ≫ h ≫ snd A T) := by
    rw [hpt]
    exact (hH _ _ _).2 ⟨qo ≫ yo, by ext <;> simp [w]⟩
  have key := add_inv_eq_of_same hL hN.isLB _ _ _ hs₁ hs₂
  rw [← GrpObj.comp_inv qo, Over.comp_left _ _ _ qo, Over.comp_left _ _ _ qo, pull_comp qo.left,
    pull_comp qo.left, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w).left,
    GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w)⁻¹.left, map_zero, add_zero] at key
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace q
  have : IsAffineHom (p₁ ≫ w).left := inferInstanceAs (IsAffineHom (π ≫ h.left ≫ (fst A T).left))
  have : Z.IsQuasiAffine := GlobalTheory.AmpleStabFinite.quasiAffine_of_pull_add (p₁ ≫ w).left ((p₁ ≫ w)⁻¹).left
    (isLB_pw hL d) s hc (fun i => (ha i).1) (by
      rw [GlobalTheory.AmpleStabFinite.cls_pw hL, map_zsmul, map_zsmul, ← zsmul_add]
      exact (congrArg _ key).trans (zsmul_zero _))
  have : IsAffine Z := GlobalTheory.AmpleStabFinite.isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set Z).Finite := by
    have := q.finite_preimage_singleton (IsLocalRing.closedPoint K)
    refine this.subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun v hv => ?_
  have e : f v = g (IsLocalRing.closedPoint K) := by
    have e₀ : y₀ (IsLocalRing.closedPoint K) = x₀ := Scheme.fromSpecResidueField_apply x₀ _
    exact (show f v = z from hv).trans ((show f x₀ = z from hx₀).symm.trans (congrArg f e₀).symm)
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) v _ e
  exact ⟨t, trivial, ht⟩

end GlobalTheory.TwistKerFinite
end
end
