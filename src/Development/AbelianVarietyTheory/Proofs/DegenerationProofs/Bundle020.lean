module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentation
public import Mathlib.Algebra.DualNumber
public import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SS.WeakNeronDef

theorem fromSpecStalk_comp {X : Scheme.{0}} {B : CommRingCat.{0}} (p : X ⟶ Spec B) (x : X) :
    X.fromSpecStalk x ≫ p =
      Spec.map ((Scheme.ΓSpecIso B).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  simp

theorem isDominant_fromSpecStalk (X : Scheme.{0}) [IsIntegral X] (x : X) : IsDominant (X.fromSpecStalk x) := by
  refine ⟨?_⟩
  have h : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_spec X
  exact h2.mono (Set.singleton_subset_iff.2 h)

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_j (N : Model R A) : IsPullback N.j A.hom N.Y.hom (spMap (algebraMap R K)) := by
  have h := Over.w N.e.inv
  have : IsIso N.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map N.e.inv))
  refine IsPullback.of_iso (IsPullback.of_hasPullback N.Y.hom (spMap (algebraMap R K)))
    (asIso N.e.inv.left).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [Model.j]
  · simp [← h]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem exists_dvr_point (N : Model R A) [IsIntegral N.Y.left] (hN : N.Irr) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ y ∈ N.sp, IsDiscreteValuationRing (N.Y.left.presheaf.stalk y) ∧
      Irreducible (((Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫
        N.Y.left.presheaf.germ ⊤ y trivial).hom ϖ) := by
  have := N.smooth
  have hs := IsPullback.of_hasPullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  set i := pullback.fst N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) with hi
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have : IsClosedImmersion i := by rw [hi]; infer_instance
  have := GlobalTheory.isReduced_of_smooth_of_isReduced
    (pullback.snd N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  have hr : Set.range i = N.sp := Set.ext fun x => DvrModel.mem_range_special hs x
  have : IrreducibleSpace ↥(pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
    have h1 : IrreducibleSpace (Set.range i) := by
      rw [hr]; exact Subtype.irreducibleSpace hN
    exact i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.surjective.irreducibleSpace
      i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.continuous
  have := isIntegral_of_irreducibleSpace_of_isReduced
    (pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  exact ⟨i (genericPoint _), hr.le ⟨_, rfl⟩, DvrModel.isDiscreteValuationRing_stalk_generic hϖ hs⟩

end GlobalTheory.SS.WeakNeronDef

namespace GlobalTheory.SS

open WeakNeronDef

theorem exists_defAt_of_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [IsIntegral A.left] (I : Type) (M : I → Model R A), WeakNeron M → ∀ N : Model R A, N.Irr → ∃ i, ∃ y ∈ N.sp, DefAt N (M i) (𝟙 A) y := by
  intro R K _ _ _ _ _ _ A _ I M hM N hN
  have := N.smooth
  have hK := isPullback_j N
  have : IsIntegral N.Y.left := DvrModel.isIntegral hK
  have : IsOpenImmersion N.j := DvrModel.isOpenImmersion_generic hK
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨y, hy, hd, hi⟩ := exists_dvr_point N hN hϖ
  let ψ := (Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫ N.Y.left.presheaf.germ ⊤ y trivial
  let R' : Type := N.Y.left.presheaf.stalk y
  let K' : Type := FractionRing R'
  letI : Algebra R R' := ψ.hom.toAlgebra
  let s : Sp R' ⟶ N.Y.left := N.Y.left.fromSpecStalk y
  have hs : s ≫ N.Y.hom = spMap (algebraMap R R') := fromSpecStalk_comp N.Y.hom y
  have hi' : Irreducible (algebraMap R R' ϖ) := hi
  have := DvrModel.isLocalization_away (K := K) hϖ
  have hu : IsUnit (((algebraMap R' K').comp (algebraMap R R')) ϖ) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R' K')).2 hi'.ne_zero).isUnit
  let k : K →+* K' := IsLocalization.Away.lift ϖ hu
  have hk : spMap k ≫ spMap (algebraMap R K) = spMap ((algebraMap R' K').comp (algebraMap R R')) := by
    rw [← Spec.map_comp, ← IsLocalization.Away.lift_comp ϖ (S := K) hu]; rfl
  have hw : (spMap (algebraMap R' K') ≫ s) ≫ N.Y.hom = spMap k ≫ spMap (algebraMap R K) := by
    rw [hk, Category.assoc, hs, ← Spec.map_comp]; rfl
  let a := hK.lift _ _ hw
  have ha : a ≫ N.j = spMap (algebraMap R' K') ≫ s := hK.lift_fst _ _ _
  have ha' : a ≫ A.hom = spMap k := hK.lift_snd _ _ _
  obtain ⟨i, b, hb, hb'⟩ := hM R' K' (by
    rw [hϖ.maximalIdeal_eq, hi'.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]) a
    (by rw [← Category.assoc, ha', hk])
  have := (M i).smooth
  have := (M i).sep
  obtain ⟨U, hU, g, h₁, h₂⟩ := spread_out_of_isGermInjective' N.Y.hom (M i).Y.hom (x := y) b (hb.trans hs.symm)
  refine ⟨i, y, hy, U, g, hU, h₂, ?_⟩
  let t : Sp R' ⟶ U.toScheme := U.fromSpecStalkOfMem y hU
  have ht : t ≫ U.ι = s := Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  have hP := isPullback_morphismRestrict N.j U
  have hc : a ≫ N.j = (spMap (algebraMap R' K') ≫ t) ≫ U.ι := by rw [ha, Category.assoc, ht]
  let c := hP.lift _ _ hc.symm
  have hc₁ : c ≫ (N.j ⁻¹ᵁ U).ι = a := hP.lift_snd _ _ _
  have hc₂ : c ≫ (N.j ∣_ U) = spMap (algebraMap R' K') ≫ t := hP.lift_fst _ _ _
  have : IsDominant s := isDominant_fromSpecStalk _ _
  have := GlobalTheory.isDominant_spMap_of_isFractionRing R' K'
  have : IsDominant (c ≫ (N.j ⁻¹ᵁ U).ι ≫ N.j) := by
    rw [← Category.assoc, hc₁, ha]; infer_instance
  have : IsDominant c := IsDominant.of_comp_of_isOpenImmersion c ((N.j ⁻¹ᵁ U).ι ≫ N.j)
  refine ext_of_isDominant_of_isSeparated (M i).Y.hom ?_ c ?_
  · simp only [Category.assoc, h₂, Over.id_left, Category.id_comp, Model.j_hom]
    rw [morphismRestrict_ι_assoc, Model.j_hom]
  · simp only [Over.id_left, Category.id_comp]
    rw [← Category.assoc, hc₂, ← Category.assoc, hc₁, ← hb', Category.assoc]
    exact congrArg _ h₁.symm

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.IdemSplit

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : C} [GrpObj G]
  (i : H ⟶ G) (r : G ⟶ H) (hir : i ≫ r = 𝟙 H) [he : IsMonHom (r ≫ i)]

include hir in
theorem sec_idem : i ≫ r ≫ i = i := by rw [reassoc_of% hir]

theorem one_comp : (η[G] ≫ r) ≫ i = η[G] := by
  rw [Category.assoc, IsMonHom.one_hom]

include hir in
theorem mul_comp : ((i ⊗ₘ i) ≫ μ[G] ≫ r) ≫ i = (i ⊗ₘ i) ≫ μ[G] := by
  rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
    sec_idem i r hir]

include hir in
theorem inv_comp : (i ≫ GrpObj.inv ≫ r) ≫ i = i ≫ GrpObj.inv := by
  rw [Category.assoc, Category.assoc, GrpObj.inv_hom, ← Category.assoc, sec_idem i r hir]

@[reducible] def grpObj : GrpObj H :=
  haveI : Mono i := (SplitMono.mk r hir).mono
  { one := η[G] ≫ r
    mul := (i ⊗ₘ i) ≫ μ[G] ≫ r
    one_mul := by
      rw [← cancel_mono i, Category.assoc, mul_comp i r hir, ← tensorHom_id,
        tensorHom_comp_tensorHom_assoc, one_comp, Category.id_comp, tensorHom_def'_assoc,
        MonObj.one_mul, leftUnitor_naturality]
    mul_one := by
      rw [← cancel_mono i, Category.assoc, mul_comp i r hir, ← id_tensorHom,
        tensorHom_comp_tensorHom_assoc, one_comp, Category.id_comp, tensorHom_def_assoc,
        MonObj.mul_one, rightUnitor_naturality]
    mul_assoc := by
      rw [← cancel_mono i, Category.assoc, Category.assoc (α_ H H H).hom, Category.assoc (H ◁ _),
        mul_comp i r hir, ← id_tensorHom, ← tensorHom_id,
        tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, mul_comp i r hir,
        Category.id_comp]
      have h1 : ((i ⊗ₘ i) ≫ μ[G]) ⊗ₘ i = ((i ⊗ₘ i) ⊗ₘ i) ≫ μ[G] ▷ G := by
        rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
      have h2 : i ⊗ₘ ((i ⊗ₘ i) ≫ μ[G]) = (i ⊗ₘ (i ⊗ₘ i)) ≫ G ◁ μ[G] := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
      rw [h1, h2, Category.assoc, Category.assoc, MonObj.mul_assoc, associator_naturality_assoc]
    inv := i ≫ GrpObj.inv ≫ r
    left_inv := by
      rw [← cancel_mono i, Category.assoc, Category.assoc (toUnit H), mul_comp i r hir, one_comp,
        lift_map_assoc, inv_comp i r hir, Category.id_comp]
      have := GrpObj.left_inv G
      have h2 := congrArg (i ≫ ·) this
      simpa using h2
    right_inv := by
      rw [← cancel_mono i, Category.assoc, Category.assoc (toUnit H), mul_comp i r hir, one_comp,
        lift_map_assoc, inv_comp i r hir, Category.id_comp]
      have := GrpObj.right_inv G
      have h2 := congrArg (i ≫ ·) this
      simpa using h2 }

theorem isMonHom_sec : letI := grpObj i r hir; IsMonHom i :=
  letI := grpObj i r hir
  { one_hom := one_comp i r
    mul_hom := mul_comp i r hir }

theorem isMonHom_ret : letI := grpObj i r hir; IsMonHom r :=
  letI := grpObj i r hir
  { one_hom := rfl
    mul_hom := by
      haveI : Mono i := (SplitMono.mk r hir).mono
      change μ[G] ≫ r = (r ⊗ₘ r) ≫ (i ⊗ₘ i) ≫ μ[G] ≫ r
      rw [← cancel_mono i, Category.assoc, Category.assoc (r ⊗ₘ r), mul_comp i r hir,
        tensorHom_comp_tensorHom_assoc, IsMonHom.mul_hom] }

theorem isComm [BraidedCategory C] [IsCommMonObj G] : letI := grpObj i r hir; IsCommMonObj H :=
  letI := grpObj i r hir
  { mul_comm := by
      change (β_ H H).hom ≫ (i ⊗ₘ i) ≫ μ[G] ≫ r = (i ⊗ₘ i) ≫ μ[G] ≫ r
      rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc] }

end General

end GlobalTheory.SS.IdemSplit

namespace GlobalTheory.SS

theorem smConn_idempotent_splits : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], SmConn G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (G₁ : Over S) (_ : GrpObj G₁) (i : G₁ ⟶ G) (r : G ⟶ G₁), SmConn G₁ ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 G₁ ∧ r ≫ i = e := by
  intro S G _ hG e he hee
  obtain ⟨hc, hs, hsep, hqc, hgc⟩ := hG
  let i := equalizer.ι e (𝟙 G)
  let r : G ⟶ equalizer e (𝟙 G) := equalizer.lift e (by simp [hee])
  have hri : r ≫ i = e := equalizer.lift_ι _ _
  have hir : i ≫ r = 𝟙 _ := by
    rw [← cancel_mono i, Category.assoc, hri, Category.id_comp]
    simpa using equalizer.condition e (𝟙 G)
  haveI : IsMonHom (r ≫ i) := by rw [hri]; exact he
  have hl : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir, Over.id_left]
  have hw := Over.w r
  exact ⟨_, IdemSplit.grpObj i r hir, i, r,
    ⟨IdemSplit.isComm i r hir, GlobalTheory.Retract.smooth hl hw, GlobalTheory.Retract.isSeparated hl hw,
      GlobalTheory.Retract.quasiCompact hl hw, GlobalTheory.Retract.geometricallyConnected hl hw⟩,
    IdemSplit.isMonHom_sec i r hir, IdemSplit.isMonHom_ret i r hir, hir, hri⟩

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.StalkDer
variable {K : Type} [Field K] {P : Scheme.{0}} {X : Over (Sp K)}

def gm (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) :
    Γ(X.left, V) →+* P.presheaf.stalk z :=
  (P.presheaf.germ (f ⁻¹ᵁ V) z hz).hom.comp (f.app V).hom

theorem germ_appLE (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (W : P.Opens) (h : W ≤ f ⁻¹ᵁ V)
    (hz : z ∈ W) (u : Γ(X.left, V)) :
    (P.presheaf.germ W z hz).hom ((f.appLE V W h).hom u) = gm f z V (h hz) u :=
  TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE h) z hz _

theorem gm_res (f : P ⟶ X.left) (z : P) (V V' : X.left.Opens) (h : V' ≤ V) (hz : z ∈ f ⁻¹ᵁ V')
    (u : Γ(X.left, V)) :
    gm f z V' hz ((X.left.presheaf.map (homOfLE h).op).hom u) = gm f z V (h hz) u := by
  rw [← germ_appLE f z V' _ le_rfl hz, ← germ_appLE f z V (f ⁻¹ᵁ V') (fun _ hx => h hx) hz]
  congr 1
  exact congrArg (fun φ => φ.hom u) (f.map_appLE le_rfl (homOfLE h).op)

def gmDual (D : VF X) (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) :
    Γ(X.left, V) →+* DualNumber (P.presheaf.stalk z) where
  toFun b := (gm f z V hz b, gm f z V hz (D.D V b))
  map_one' := TrivSqZeroExt.ext (map_one _) (by
    show gm f z V hz (D.D V 1) = 0
    have := D.const V 1
    rw [map_one] at this
    rw [this, map_zero])
  map_mul' a b := TrivSqZeroExt.ext (map_mul _ a b) (by
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    show gm f z V hz (D.D V (a * b)) = gm f z V hz a * gm f z V hz (D.D V b) +
      gm f z V hz (D.D V a) * gm f z V hz b
    rw [D.leibniz, map_add (f := _), map_mul, map_mul]; ring)
  map_zero' := TrivSqZeroExt.ext (map_zero _) (by
    show gm f z V hz (D.D V 0) = 0
    rw [map_zero, map_zero])
  map_add' a b := TrivSqZeroExt.ext (map_add _ a b) (by
    show gm f z V hz (D.D V (a + b)) = gm f z V hz (D.D V a) + gm f z V hz (D.D V b)
    rw [map_add (f := _), map_add (f := _)])

theorem gmDual_res (D : VF X) (f : P ⟶ X.left) (z : P) (V V' : X.left.Opens) (h : V' ≤ V)
    (hz : z ∈ f ⁻¹ᵁ V') (u : Γ(X.left, V)) :
    gmDual D f z V' hz ((X.left.presheaf.map (homOfLE h).op).hom u) = gmDual D f z V (h hz) u :=
  TrivSqZeroExt.ext (gm_res f z V V' h hz u) (by
    show gm f z V' hz (D.D V' _) = gm f z V (h hz) (D.D V u)
    rw [D.res, gm_res])

theorem extend (D : VF X) (f : P ⟶ X.left) (z : P)
    (Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z)) (V₀ : X.left.Opens)
    (hV₀ : IsAffineOpen V₀) (hz₀ : z ∈ f ⁻¹ᵁ V₀)
    (H : ∀ u, Φ (gm f z V₀ hz₀ u) = gmDual D f z V₀ hz₀ u)
    (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) (u : Γ(X.left, V)) :
    Φ (gm f z V hz u) = gmDual D f z V hz u := by
  obtain ⟨r, hr, hzr⟩ := hV₀.exists_basicOpen_le (V := V) ⟨f z, hz⟩ hz₀
  have hzr' : z ∈ f ⁻¹ᵁ X.left.basicOpen r := hzr
  have := hV₀.isLocalization_basicOpen r
  have e : Φ.comp (gm f z _ hzr') = gmDual D f z _ hzr' := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    refine RingHom.ext fun a => ?_
    have h1 := gm_res f z V₀ _ (X.left.basicOpen_le r) hzr' a
    have h2 := gmDual_res D f z V₀ _ (X.left.basicOpen_le r) hzr' a
    exact ((congrArg Φ h1).trans (H a)).trans h2.symm
  rw [← gm_res f z V _ hr hzr', ← gmDual_res D f z V _ hr hzr']
  exact RingHom.congr_fun e _

theorem gmDual_const (D : VF X) (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V)
    (c : Γ(Sp K, ⊤)) :
    gmDual D f z V hz ((X.hom.appLE ⊤ V le_top).hom c) =
      TrivSqZeroExt.inl ((P.presheaf.germ ⊤ z trivial).hom (((f ≫ X.hom).appLE ⊤ ⊤ le_top).hom c)) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show gm f z V hz _ = (P.presheaf.germ ⊤ z trivial).hom _
    rw [← germ_appLE f z V _ le_rfl hz,
      ← TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)) z hz]
    congr 1
    have e1 := Scheme.Hom.appLE_comp_appLE f X.hom ⊤ V (f ⁻¹ᵁ V) le_top le_rfl
    have e2 := (f ≫ X.hom).appLE_map (U := ⊤) (V := ⊤) le_top (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op
    exact congrArg (fun φ => φ.hom c) (e1.trans e2.symm)
  · show gm f z V hz (D.D V _) = 0
    have e : (X.hom.appLE ⊤ V le_top).hom c =
        cstK X V ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom c) := by
      show _ = (X.hom.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom _)
      congr 1
      exact (congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id).symm
    rw [e, D.const, map_zero]

theorem exists_dual {Y : Over (Sp K)} (p : P ⟶ X.left) (q : P ⟶ Y.left)
    (H : IsPullback p q X.hom Y.hom) (D : VF X) (E : VF Y) (z : P) :
    ∃ Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z), (∀ a, (Φ a).fst = a) ∧
      (∀ V hz u, Φ (gm p z V hz u) = gmDual D p z V hz u) ∧
      ∀ V hz u, Φ (gm q z V hz u) = gmDual E q z V hz u := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p z)) isOpen_univ
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ := Y.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (q z)) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hW : IsAffineOpen W := hW
  have hzU : z ∈ p ⁻¹ᵁ U := hzU
  have hzW : z ∈ q ⁻¹ᵁ W := hzW
  have hO : IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) := by
    have : IsAffine _ := isAffineOpen_top (Sp K)
    have : IsAffine _ := hU
    have : IsAffine _ := hW
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top
      rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := W) (UX := U) le_top
    le_top rfl).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hW hU)
  have hz : z ∈ p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W := ⟨hzU, hzW⟩
  have w : X.hom.appLE ⊤ U le_top ≫ CommRingCat.ofHom (gmDual D p z U hzU) =
      Y.hom.appLE ⊤ W le_top ≫ CommRingCat.ofHom (gmDual E q z W hzW) := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    refine (gmDual_const D p z U hzU c).trans (Eq.trans ?_ (gmDual_const E q z W hzW c).symm)
    simp only [H.w]
  let φ := po.desc _ _ w
  have h1 : ∀ u, φ.hom ((p.appLE U _ inf_le_left).hom u) = gmDual D p z U hzU u := fun u =>
    congrArg (fun φ => φ.hom u) (po.inl_desc _ _ w)
  have h2 : ∀ u, φ.hom ((q.appLE W _ inf_le_right).hom u) = gmDual E q z W hzW u := fun u =>
    congrArg (fun φ => φ.hom u) (po.inr_desc _ _ w)
  have hf : φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom (P.presheaf.stalk z) (P.presheaf.stalk z)
      (P.presheaf.stalk z)).toRingHom = P.presheaf.germ _ z hz := by
    refine po.hom_ext (CommRingCat.hom_ext (RingHom.ext fun u => ?_))
      (CommRingCat.hom_ext (RingHom.ext fun u => ?_))
    · exact (congrArg TrivSqZeroExt.fst (h1 u)).trans (germ_appLE p z U _ inf_le_left hz u).symm
    · exact (congrArg TrivSqZeroExt.fst (h2 u)).trans (germ_appLE q z W _ inf_le_right hz u).symm
  have hf' : ∀ b, (φ.hom b).fst = (P.presheaf.germ _ z hz).hom b := fun b =>
    congrArg (fun φ => φ.hom b) hf
  letI := P.presheaf.algebra_section_stalk (⟨z, hz⟩ : (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W : P.Opens))
  have loc := hO.isLocalization_stalk ⟨z, hz⟩
  have hu : ∀ s : (hO.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl, IsUnit (φ.hom s) := fun s => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hf']
    exact IsLocalization.map_units (P.presheaf.stalk z) s
  let Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z) := IsLocalization.lift hu
  have hΦ : ∀ b, Φ ((P.presheaf.germ _ z hz).hom b) = φ.hom b := fun b =>
    IsLocalization.lift_eq hu b
  refine ⟨Φ, fun a => ?_, extend D p z Φ U hU hzU fun u => ?_, extend E q z Φ W hW hzW fun u => ?_⟩
  · have : (TrivSqZeroExt.fstHom (P.presheaf.stalk z) (P.presheaf.stalk z)
        (P.presheaf.stalk z)).toRingHom.comp Φ = RingHom.id _ := by
      apply IsLocalization.ringHom_ext (hO.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
      refine RingHom.ext fun b => ?_
      exact (congrArg TrivSqZeroExt.fst (hΦ b)).trans (hf' b)
    exact congrArg (fun f => f a) this
  · rw [← germ_appLE p z U _ inf_le_left hz, hΦ, h1]
  · rw [← germ_appLE q z W _ inf_le_right hz, hΦ, h2]

end GlobalTheory.SS.StalkDer

namespace GlobalTheory.SS

open StalkDer in
theorem exists_stalk_derivation_of_isPullback : ∀ (K : Type) [Field K] (P X Y : Over (Sp K)) (p : P.left ⟶ X.left) (q : P.left ⟶ Y.left), IsPullback p q X.hom Y.hom → ∀ (D : VF X) (z : P.left), ∃ δ : P.left.presheaf.stalk z →+ P.left.presheaf.stalk z, (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ (∀ (V : X.left.Opens) (W : P.left.Opens) (h : W ≤ p ⁻¹ᵁ V) (hz : z ∈ W) (u : Γ(X.left, V)), δ ((P.left.presheaf.germ W z hz).hom ((p.appLE V W h).hom u)) = (P.left.presheaf.germ W z hz).hom ((p.appLE V W h).hom (D.D V u))) ∧ ∀ (V : Y.left.Opens) (W : P.left.Opens) (h : W ≤ q ⁻¹ᵁ V) (hz : z ∈ W) (u : Γ(Y.left, V)), δ ((P.left.presheaf.germ W z hz).hom ((q.appLE V W h).hom u)) = 0 := by
  intro K _ P X Y p q H D z
  obtain ⟨Φ, h0, h1, h2⟩ := exists_dual p q H D (VF.zero Y) z
  refine ⟨⟨⟨fun x => (Φ x).snd, by simp⟩, fun a b => by simp⟩, fun a b => ?_,
    fun V W h hz u => ?_, fun V W h hz u => ?_⟩
  · show (Φ (a * b)).snd = a * (Φ b).snd + b * (Φ a).snd
    rw [map_mul, DualNumber.snd_mul, h0, h0]; ring
  · rw [germ_appLE, germ_appLE]
    exact congrArg TrivSqZeroExt.snd (h1 V (h hz) u)
  · rw [germ_appLE]
    exact (congrArg TrivSqZeroExt.snd (h2 V (h hz) u)).trans (map_zero (gm q z V (h hz)))
end GlobalTheory.SS
end
end
