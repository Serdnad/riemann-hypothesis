module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle005
public import Development.EtaleCohomology.CohomologicalPurity.Bundle007
public import Development.EtaleCohomology.CohomologicalPurity.Bundle006
public import Development.EtaleCohomology.CohomologicalPurity.Bundle010
public import Development.EtaleCohomology.CohomologicalPurity.Bundle011
public import Development.EtaleCohomology.CohomologicalPurity.Bundle009
public import Development.EtaleCohomology.CohomologicalPurity.Bundle008
public import Development.EtaleCohomology.CohomologicalPurity.Bundle016
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

@[expose] public section

section

namespace LateralTheory.Fin.LeafChart
theorem etale_chart_localization_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafLoc := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafLoc_of
theorem etale_chart_shrinking_open_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafShrink := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafShrink_of
theorem etale_chart_conormal_rank_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafRank := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of
theorem etale_chart_generator_choice_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafPick := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafPick_of
theorem etale_chart_ideal_span_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafSpan := by
  apply LateralTheory.CohomologicalPurity.LeafSpanPf.LeafSpan_of
theorem etale_chart_etaleness_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafEt := by
  apply LateralTheory.CohomologicalPurity.LeafEtPf.LeafEt_of
theorem etale_chart_coordinate_functions_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafCoord := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafCoord_of <;> first | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_chart_ideal_span_property_holds | exact etale_chart_etaleness_property_holds
theorem etale_chart_section_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafSec := by
  apply LateralTheory.CohomologicalPurity.LeafSecPf.LeafSec_of
theorem etale_chart_polynomial_algebra_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := by
  apply LateralTheory.CohomologicalPurity.LeafPolyPf.LeafPoly_of
theorem etale_chart_neighborhood_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd_of <;> first | exact etale_chart_section_property_holds | exact etale_chart_polynomial_algebra_property_holds
theorem etale_coordinate_chart_existence : LateralTheory.CohomologicalPurity.LeafChart := by
  apply LateralTheory.CohomologicalPurity.ChartCut.goal_of <;> first | exact etale_chart_localization_property_holds | exact etale_chart_shrinking_open_property_holds | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_chart_ideal_span_property_holds | exact etale_chart_etaleness_property_holds | exact etale_chart_coordinate_functions_property_holds | exact etale_chart_section_property_holds | exact etale_chart_polynomial_algebra_property_holds | exact etale_chart_neighborhood_property_holds
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafChart := etale_coordinate_chart_existence
end LateralTheory.Fin.LeafChart
end

section

namespace LateralTheory.Fin.LeafBd
theorem etale_boundary_monomorphism_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafMono := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafMono_of
theorem etale_relative_boundary_pushout_property_holds : LateralTheory.CohomologicalPurity.Bd.LeafPush := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafPush_of
theorem etale_boundary_good_pair_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGood := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafGood_of
theorem etale_boundary_connecting_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafDelta := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafDelta_of
theorem etale_boundary_exact_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafExact := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafExact_of
theorem etale_boundary_generator_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGen := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafGen_of
theorem etale_boundary_image_hom_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImgHom := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafImgHom_of <;> first | exact etale_boundary_generator_of_thom_isomorphism
theorem etale_boundary_image_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImg := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafImg_of <;> first | exact etale_boundary_image_hom_of_thom_isomorphism
theorem etale_boundary_map_of_thom_isomorphism : LateralTheory.CohomologicalPurity.LeafBd := by
  apply LateralTheory.CohomologicalPurity.Bd.goal_of <;> first | exact etale_boundary_monomorphism_of_thom_isomorphism | exact etale_relative_boundary_pushout_property_holds | exact etale_boundary_good_pair_of_thom_isomorphism | exact etale_boundary_connecting_of_thom_isomorphism | exact etale_boundary_exact_of_thom_isomorphism | exact etale_boundary_generator_of_thom_isomorphism | exact etale_boundary_image_hom_of_thom_isomorphism | exact etale_boundary_image_of_thom_isomorphism
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafBd := etale_boundary_map_of_thom_isomorphism
end LateralTheory.Fin.LeafBd
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurNatPf

open PurPf

theorem fold_map {P' P : Arrow Spc} (ψ : P' ⟶ P) : dbl.map ψ ≫ dbl.fold P = dbl.fold P' ≫ ψ.right := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext <;>
      simp only [dbl.map, dbl.fold, pushout.map] <;> (first
        | (erw [pushout.inl_desc_assoc, Category.assoc]; erw [pushout.inl_desc, pushout.inl_desc_assoc]; simp)
        | (erw [pushout.inr_desc_assoc, Category.assoc]; erw [pushout.inr_desc, pushout.inr_desc_assoc]; simp)
        | (erw [pushout.inl_desc_assoc, Category.assoc, Category.assoc]; erw [pushout.inl_desc, pushout.inl_desc]; simp)
        | (erw [pushout.inr_desc_assoc, Category.assoc, Category.assoc]; erw [pushout.inr_desc, pushout.inr_desc]; simp))

theorem proj_pull (q : ℕ) {P' P : Arrow Spc} (ψ : P' ⟶ P) (n i : ℤ) (c : Ht q (dbl P) n i) :
    Hs.pull q ψ n i (Hs.proj q P n i c) = Hs.proj q P' n i (pull _ (dbl.map ψ) _ n c) := by
  apply Subtype.ext
  change pull _ (dbl.map ψ) _ n (c - _) = _ - _
  rw [map_sub, ← pull_comp, fold_map, pull_comp, ← pull_comp _ (dbl.inr P') (dbl.map ψ), dbl.inr_map, pull_comp]

theorem act_pull (hN : DivisorNaturality) (q : ℕ) [NeZero q] {P' P : Arrow Spc} (ψ : P' ⟶ P) {n m i j : ℤ} (a : Ht q P.right n i)
    (b : Hs q P m j) : Hs.pull q ψ _ _ (Hs.act q a b) = Hs.act q (pull _ ψ.right _ _ a) (Hs.pull q ψ _ _ b) := by
  unfold Hs.act
  rw [proj_pull, (hN q).1]
  congr 2
  rw [← pull_comp, ← pull_comp, fold_map]

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem dbl_map_comp {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) :
    dbl.map α ≫ dbl.map β = dbl.map (α ≫ β) := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext
    · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
      rw [← Category.assoc, inl_map, Category.assoc, inl_map, inl_map, Arrow.comp_right, Category.assoc]
    · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
      rw [← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, dbl.inr_map, Arrow.comp_right, Category.assoc]

theorem pull_pull (q : ℕ) {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q α n i (Hs.pull q β n i x) = Hs.pull q (α ≫ β) n i x := by
  apply Subtype.ext
  change pull _ (dbl.map α) _ n (pull _ (dbl.map β) _ n x.1) = pull _ (dbl.map (α ≫ β)) _ n x.1
  rw [← pull_comp, dbl_map_comp]

def purOf {d : ℕ} {P : SP d} (t : Tube P) (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(P.X, ⊤))) (n i : ℤ)
    (x : Ht q (sch.obj P.Z) n i) : Hs q (opn P.U) (n + 2 * d) (i + d) :=
  (AddEquiv.ofBijective _ ((t.ok q hq).2.2.1 (n + 2 * d) (i + d))).symm
    (Hs.act q (P := abv P.U t.π) ((AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).symm
      (pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x)) (Hs.pull q (abvMap P.U t.π) _ _ (fcl d q P)))

theorem purT_eq {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (x : Ht q (sch.obj P.Z) n i) : purT T q P n i x = purOf (T P) q hq n i x := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  unfold purT
  rw [dite_eq_left h]
  rfl

theorem purOf_char {d : ℕ} {P : SP d} (t : Tube P) (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(P.X, ⊤))) (n i : ℤ)
    (x : Ht q (sch.obj P.Z) n i) (y : Hs q (opn P.U) (n + 2 * d) (i + d)) (e : Ht q t.E n i)
    (he : pull _ (pullback.fst t.π (sch.map P.ι)) (tw q i) n e = pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x)
    (hy : Hs.pull q (abvMap P.U t.π) _ _ y = Hs.act q (P := abv P.U t.π) e (Hs.pull q (abvMap P.U t.π) _ _ (fcl d q P))) :
    purOf t q hq n i x = y := by
  have he' : (AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).symm
      (pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x) = e := by
    rw [AddEquiv.symm_apply_eq]; exact he.symm
  unfold purOf
  rw [he', AddEquiv.symm_apply_eq]
  exact hy.symm

theorem unit_of {d : ℕ} {P' P : SP d} (φ : P'.Hom P) (q : ℕ) (hq : IsUnit (q : Γ(P.X, ⊤))) :
    IsUnit (q : Γ(P'.X, ⊤)) := by
  have := hq.map φ.f.appTop.hom
  simpa using this

theorem purOf_nat (hN : DivisorNaturality) {d : ℕ} (hC : IsCl d (fcl d)) {P' P : SP d} (φ : P'.Hom P) (t : Tube P) (t' : Tube P')
    (b : t'.E ⟶ t.E) (hb : b ≫ t.π = t'.π ≫ sch.map φ.f) (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (x : Ht q (sch.obj P.Z) n i) :
    Hs.pull q (opnMap φ.f _ _ φ.le) _ _ (purOf t q hq n i x) =
      purOf t' q (unit_of φ q hq) n i (pull _ (sch.map φ.g) _ _ x) := by
  set_option synthInstance.maxHeartbeats 200000 in
    symm

    set e := (AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).symm (pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x)
      with he_def
    have he : pull _ (pullback.fst t.π (sch.map P.ι)) (tw q i) n e = pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x :=
      (AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).apply_symm_apply _
    have hy : Hs.pull q (abvMap P.U t.π) _ _ (purOf t q hq n i x) =
        Hs.act q (P := abv P.U t.π) e (Hs.pull q (abvMap P.U t.π) _ _ (fcl d q P)) :=
      (AddEquiv.ofBijective _ ((t.ok q hq).2.2.1 (n + 2 * d) (i + d))).apply_symm_apply _

    have hw : (pullback.fst t'.π (sch.map P'.ι) ≫ b) ≫ t.π = (pullback.snd t'.π (sch.map P'.ι) ≫ sch.map φ.g) ≫ sch.map P.ι := by
      rw [Category.assoc, hb, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp, φ.cart.w]
    let c : pullback t'.π (sch.map P'.ι) ⟶ pullback t.π (sch.map P.ι) := pullback.lift _ _ hw

    have hw2 : (pullback.fst t'.π (sch.map P'.U.ι) ≫ b) ≫ t.π =
        (pullback.snd t'.π (sch.map P'.U.ι) ≫ sch.map (φ.f.resLE P.U P'.U φ.le)) ≫ sch.map P.U.ι := by
      rw [Category.assoc, hb, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp, Scheme.Hom.resLE_comp_ι]
    let ψ : abv P'.U t'.π ⟶ abv P.U t.π := Arrow.homMk (pullback.lift _ _ hw2) b (by simp only [abv, Arrow.mk_hom]; exact pullback.lift_fst _ _ _)
    have hsq : abvMap P'.U t'.π ≫ opnMap φ.f _ _ φ.le = ψ ≫ abvMap P.U t.π := by
      apply Arrow.hom_ext
      · simp only [Arrow.comp_left, abvMap, opnMap, ψ, Arrow.homMk_left]; exact (pullback.lift_snd _ _ _).symm
      · simp only [Arrow.comp_right, abvMap, opnMap, ψ, Arrow.homMk_right]; exact hb.symm
    apply purOf_char t' q _ n i _ _ (pull _ b _ _ e)
    · rw [← pull_comp, ← pull_comp, show pullback.fst t'.π (sch.map P'.ι) ≫ b = c ≫ pullback.fst t.π (sch.map P.ι) from (pullback.lift_fst _ _ hw).symm,
        show pullback.snd t'.π (sch.map P'.ι) ≫ sch.map φ.g = c ≫ pullback.snd t.π (sch.map P.ι) from (pullback.lift_snd _ _ hw).symm,
        pull_comp, pull_comp, he]
    · rw [pull_pull, hsq, ← pull_pull, hy]
      refine (act_pull hN q ψ (P := abv P.U t.π) e _).trans ?_
      congr 1
      rw [pull_pull, ← hsq, ← pull_pull, (hC q).2.1 P' P φ hq]

theorem dbl_map_of_right {P : Arrow Spc} (ψ : P ⟶ P) (h : ψ.right = 𝟙 _) : dbl.map ψ = 𝟙 _ := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext
    · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
      rw [inl_map, h, Category.id_comp, Category.comp_id]
    · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
      rw [dbl.inr_map, h, Category.id_comp, Category.comp_id]

theorem pull_of_right (q : ℕ) {P : Arrow Spc} (ψ : P ⟶ P) (h : ψ.right = 𝟙 _) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q ψ n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map ψ) _ n x.1 = x.1
  rw [dbl_map_of_right ψ h, pull_id]

def idHom {d : ℕ} (P : SP d) : P.Hom P where
  f := 𝟙 _
  g := 𝟙 _
  cart := by
    first
      | exact IsPullback.of_vert_isIso ⟨by simp⟩
      | exact IsPullback.of_horiz_isIso ⟨by simp⟩
  le := fun x hx => hx

end PurNatPf

open PurNatPf PurPf

theorem LeafPurNat_of : EtalePurityNaturality := by
  intro hH hCl d T hT q _ P hq P' φ n i x
  have hN : DivisorNaturality := hH.2.2.2.2.1
  have hC : IsCl d (fcl d) := pick_spec (hCl hH d)
  obtain ⟨T', a, b, ha, hb⟩ := hT P' P φ
  have hq' := unit_of φ q hq
  rw [purT_eq T q P hq, purT_eq T q P' hq', purOf_nat hN hC φ (T P) T' b hb q hq]
  have hb' : a ≫ (T P').π = T'.π ≫ sch.map (idHom P').f := by
    rw [ha]; change _ = T'.π ≫ sch.map (𝟙 _); rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have key := purOf_nat hN hC (idHom P') (T P') T' a hb' q hq' n i (pull _ (sch.map φ.g) _ _ x)
  rw [pull_of_right] at key
  · rw [key]
    change _ = purOf T' q _ n i (pull _ (sch.map (𝟙 _)) _ _ _)
    rw [CategoryTheory.Functor.map_id, pull_id]
  · change sch.map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
    rfl

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurRedPf

open PurPf

theorem inv_red (q r : ℕ) {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (hq : Function.Bijective (pull (ZMod q) f (tw q i) n)) (hr : Function.Bijective (pull (ZMod r) f (tw r i) n))
    (y : Ht q E n i) :
    (AddEquiv.ofBijective _ hr).symm (red q r E n i y) = red q r E' n i ((AddEquiv.ofBijective _ hq).symm y) := by
  apply hr.1
  rw [AddEquiv.ofBijective_apply_symm_apply]
  rw [GlobalTheory.EtC.pull_red]
  congr 1
  exact ((AddEquiv.ofBijective _ hq).apply_symm_apply y).symm

def redS (q r : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs r P n i :=
  ⟨red q r _ n i x.1, by
    change pull _ (dbl.inr P) (tw r i) n (red q r _ n i x.1) = 0
    have hx : pull _ (dbl.inr P) (tw q i) n x.1 = 0 := x.2
    rw [GlobalTheory.EtC.pull_red, hx, map_zero]⟩

theorem redS_coe (q r : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : (redS q r P n i x).1 = red q r _ n i x.1 := rfl

theorem Hs.pullS_red (q r : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull r φ n i (redS q r P n i x) = redS q r P' n i (Hs.pull q φ n i x) := by
  apply Subtype.ext
  change pull _ (dbl.map φ) (tw r i) n (red q r _ n i x.1) = red q r _ n i (pull _ (dbl.map φ) (tw q i) n x.1)
  rw [GlobalTheory.EtC.pull_red]

theorem Hs.inv_red (q r : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ)
    (hq : Function.Bijective (Hs.pull q φ n i)) (hr : Function.Bijective (Hs.pull r φ n i)) (y : Hs q P' n i) :
    (AddEquiv.ofBijective _ hr).symm (redS q r P' n i y) = redS q r P n i ((AddEquiv.ofBijective _ hq).symm y) := by
  apply hr.1
  rw [AddEquiv.ofBijective_apply_symm_apply, Hs.pullS_red]
  congr 1
  exact ((AddEquiv.ofBijective _ hq).apply_symm_apply y).symm

theorem Hs.act_red (hA : A11) (q r : ℕ) [NeZero q] (hrq : r ∣ q) {P : Arrow Spc} {n m i j : ℤ}
    (a : Ht q P.right n i) (b : Hs q P m j) :
    Hs.act r (red q r _ n i a) (redS q r P m j b) = redS q r P _ _ (Hs.act q a b) := by
  apply Subtype.ext
  have hc : cup r (pull _ (dbl.fold P) (tw r i) n (red q r _ n i a)) (red q r _ m j b.1) =
      red q r _ _ _ (cup q (pull _ (dbl.fold P) (tw q i) n a) b.1) := by
    rw [(hA q r hrq (dbl P)).1, GlobalTheory.EtC.pull_red]
  simp only [Hs.act, Hs.proj, redS_coe]
  rw [hc, map_sub, GlobalTheory.EtC.pull_red, GlobalTheory.EtC.pull_red]

theorem fcl_isCl (hH : Hyp) (hCl : LeafCl) (d : ℕ) : IsCl d (fcl d) := by
  unfold fcl
  exact pick_spec (hCl hH d)

theorem purT_eq {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (a : Ht q (sch.obj P.Z) n i) :
    purT T q P n i a = (AddEquiv.ofBijective _ (((T P).ok q hq).2.2.1 (n + 2 * d) (i + d))).symm
      (Hs.act q (P := abv P.U (T P).π) ((AddEquiv.ofBijective _ (((T P).ok q hq).1 i n)).symm
        (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n a))
        (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P))) := by
  unfold purT
  rw [dite_eq_left ⟨NeZero.ne q, hq⟩]
  rfl

theorem act_fcl (hH : Hyp) (hCl : LeafCl) {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d)
    (hq : IsUnit (q : Γ(P.X, ⊤))) (r : ℕ) (hrq : r ∣ q) (n i : ℤ) (x : Ht q (T P).E n i) :
    Hs.act r (P := abv P.U (T P).π) (red q r (T P).E n i x) (Hs.pull r (abvMap P.U (T P).π) _ _ (fcl d r P)) =
      redS q r _ _ _ (Hs.act q (P := abv P.U (T P).π) x (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P))) := by
  have hfr : fcl d r P = redS q r _ _ _ (fcl d q P) := Subtype.ext (((fcl_isCl hH hCl d) q).2.2 r hrq P hq)
  rw [hfr, Hs.pullS_red]
  exact Hs.act_red hH.2.2.2.2.2.2.2.1 q r hrq _ _

end PurRedPf

open PurPf PurRedPf

theorem LeafPurRed_of : EtalePurityReduction := by
  intro hH hCl d T q _ P hq r hrq n i a
  have hq0 : q ≠ 0 := NeZero.ne q
  have hr0 : r ≠ 0 := by rintro rfl; exact hq0 (zero_dvd_iff.mp hrq)
  have : NeZero r := ⟨hr0⟩
  have hru : IsUnit (r : Γ(P.X, ⊤)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hrq) hq
  rw [purT_eq T r P hru, purT_eq T q P hq, GlobalTheory.EtC.pull_red, inv_red q r _ n i (((T P).ok q hq).1 i n) (((T P).ok r hru).1 i n), act_fcl hH hCl T q P hq r hrq, Hs.inv_red q r _ _ _, redS_coe]

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurProjPf

open PurPf

def HsCast {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) : Hs q P N' I' := by
  subst hN; subst hI; exact x

theorem HsCast_val {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) :
    (HsCast hN hI x).1 = Ht.cast hN hI x.1 := by
  subst hN; subst hI; rfl

theorem HsCast_pull {q : ℕ} {P' P : Arrow Spc} (φ : P' ⟶ P) {N N' I I' : ℤ} (hN : N = N') (hI : I = I')
    (x : Hs q P N I) : Hs.pull q φ N' I' (HsCast hN hI x) = HsCast hN hI (Hs.pull q φ N I x) := by
  subst hN; subst hI; rfl

theorem HsCast_fgt {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) :
    Hs.fgt q P N' I' (HsCast hN hI x) = Ht.cast hN hI (Hs.fgt q P N I x) := by
  subst hN; subst hI; rfl

theorem act_val (hA : DivisorNaturality) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m i j : ℤ} (a : Ht q P.right n i)
    (b : Hs q P m j) : (Hs.act q a b).1 = cup q (pull _ (dbl.fold P) _ n a) b.1 := by
  have hb : pull _ (dbl.inr P) (tw q j) m b.1 = 0 := b.2
  change cup q (pull _ (dbl.fold P) _ n a) b.1 -
    pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1)) = _
  rw [(hA q).1, hb]
  simp only [map_zero, sub_zero]

theorem act_cup (hA : DivisorNaturality) (hR : DivisorRingCompatibility) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m k i j l : ℤ}
    (x : Ht q P.right n i) (y : Ht q P.right m j) (c : Hs q P k l) :
    Hs.act q (cup q x y) c = HsCast (by ring) (by ring) (Hs.act q x (Hs.act q y c)) := by
  apply Subtype.ext
  rw [HsCast_val, act_val hA, act_val hA, act_val hA, (hA q).1, (hR q _).2.1]

theorem fgt_act (hA : DivisorNaturality) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m i j : ℤ} (a : Ht q P.right n i)
    (s : Hs q P m j) : Hs.fgt q P _ _ (Hs.act q a s) = cup q a (Hs.fgt q P m j s) := by
  change pull _ (dbl.inl P) _ _ (Hs.act q a s).1 = cup q a (pull _ (dbl.inl P) _ _ s.1)
  rw [act_val hA, (hA q).1, ← pull_comp, show dbl.inl P ≫ dbl.fold P = 𝟙 _ from pushout.inl_desc (f := P.hom) (g := P.hom) _ _ _, pull_id]

theorem purT_char {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (x : Ht q (sch.obj P.Z) n i) : ∃ e : Ht q (T P).E n i,
      pull _ (pullback.fst (T P).π (sch.map P.ι)) _ _ e = pull _ (pullback.snd (T P).π (sch.map P.ι)) _ _ x ∧
      Hs.pull q (abvMap P.U (T P).π) _ _ (purT T q P n i x) =
        Hs.act q (P := abv P.U (T P).π) e (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P)) := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  refine ⟨(AddEquiv.ofBijective _ (((T P).ok q hq).1 i n)).symm
    (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n x), ?_, ?_⟩
  · exact AddEquiv.ofBijective_apply_symm_apply _ (((T P).ok q hq).1 i n)
  · unfold purT
    rw [dite_eq_left h]
    exact AddEquiv.ofBijective_apply_symm_apply _ (((T P).ok q hq).2.2.1 (n + 2 * d) (i + d))

end PurProjPf

open PurPf PurProjPf

theorem LeafPurProj_of : EtalePurityProjection := by
  intro hH d T q _ P hq n m i j a b
  have hA : DivisorNaturality := hH.2.2.2.2.1
  have hR : DivisorRingCompatibility := hH.2.2.2.2.2.1
  obtain ⟨eb, heb1, heb2⟩ := purT_char T q P hq m j b
  obtain ⟨ex, hex1, hex2⟩ := purT_char T q P hq (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)
  have hex : ex = cup q (pull (ZMod q) (T P).π (tw q i) n a) eb := by
    apply (((T P).ok q hq).1 (i + j) (n + m)).1
    set_option synthInstance.maxHeartbeats 200000 in
      rw [hex1, (hA q).1, (hA q).1, heb1, ← pull_comp, ← pull_comp, pullback.condition]
  have hN : n + (m + 2 * (d : ℤ)) = n + m + 2 * d := by ring
  have hI : i + (j + (d : ℤ)) = i + j + d := by ring
  have key : purT T q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b) =
      HsCast hN hI (Hs.act q (P := opn P.U) (n := n) (i := i) a (purT T q P m j b)) := by
    apply (((T P).ok q hq).2.2.1 (n + m + 2 * d) (i + j + d)).1
    rw [hex2, hex, HsCast_pull]
    refine (act_cup hA hR q (P := abv P.U (T P).π) (pull (ZMod q) (T P).π (tw q i) n a) eb
      (Hs.pull q (abvMap P.U (T P).π) (2 * d) d (fcl d q P))).trans ?_
    rw [TubeCut.LeafActNat_of hA q _ _ (abvMap P.U (T P).π) n (m + 2 * d) i (j + d) a (purT T q P m j b), heb2]
    rfl
  rw [key, HsCast_fgt]
  exact congrArg (Ht.cast hN hI) (fgt_act hA q (P := opn P.U) a (purT T q P m j b))

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity

theorem LeafSurjGeo_of : LeafSurjGeo := by
  intro X' X Z f _ ι' ι _ hp U hU T t
  let F : Bool → Scheme.{0} := fun b => Bool.rec (pullback t f) (t ⁻¹ᵁ U).toScheme b
  let m : ∀ b, F b ⟶ T := fun b => Bool.rec (pullback.fst t f) (t ⁻¹ᵁ U).ι b
  have hR : Presieve.ofArrows F m ∈ Scheme.precoverage @Etale T := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : t.base x ∈ (U : Set X)
      · refine ⟨true, ?_⟩
        show x ∈ Set.range (t ⁻¹ᵁ U).ι.base
        rw [Scheme.Opens.range_ι]; exact hx
      · rw [hU, Set.notMem_compl_iff] at hx
        obtain ⟨z, hz⟩ := hx
        have hw : f.base (ι'.base z) = ι.base z := by
          rw [← Scheme.Hom.comp_apply, hp.w]; simp
        obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := f) x (ι'.base z)
          (by rw [hw, hz])
        exact ⟨false, p, hp1⟩
    · cases b <;> dsimp [m] <;> infer_instance
  refine ⟨Sieve.generate (Presieve.ofArrows F m),
    Precoverage.generate_mem_toGrothendieck hR, ?_⟩
  intro V g hg
  obtain ⟨W, h, k, hk, rfl⟩ := hg
  obtain ⟨b⟩ := hk
  cases b
  · right
    refine ⟨h ≫ pullback.snd t f, ?_⟩
    simp only [m, Category.assoc, ← pullback.condition]
  · left
    refine ⟨h ≫ (t ∣_ U), ?_⟩
    simp only [m, Category.assoc, morphismRestrict_ι]

end LateralTheory.CohomologicalPurity
end
end
