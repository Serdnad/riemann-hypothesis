module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031

@[expose] public section

section

open GlobalTheory GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.ChartMem

variable {K : Type} [Field K]

def wt {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) : K :=
  if i ∈ J then 1 else (x i : K)

theorem frame_eq {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) :
    frame x J i = wt x J i • dlog (x i) := by
  unfold frame wt
  split_ifs with h
  · simp
  · simp [dlog, smul_smul]

theorem prod_wt {n : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) :
    ∏ i ∈ I, wt x J i = ∏ i ∈ I \ J, (x i : K) := by
  simp only [wt]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.sdiff_eq_filter]

theorem wt_mul_prod {n : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) (i : Fin n) (hi : i ∉ I) :
    wt x J i * ∏ j ∈ I \ J, (x j : K) = ∏ j ∈ insert i I \ J, (x j : K) := by
  rw [← prod_wt, ← prod_wt, Finset.prod_insert hi]

theorem prod_sdiff_ne_zero {n : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) :
    ∏ j ∈ I \ J, (x j : K) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => Units.ne_zero _

theorem ιMulti_frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) :
    ∀ (a : ℕ) (v : Fin a → Ω[K⁄ℤ]), (∀ i, v i ∈ Set.range (frame x J)) →
      ∃ (I : Finset (Fin n)) (m : ℤ), (m ≠ 0 → I.card = a) ∧
        ExteriorAlgebra.ιMulti K a v = ((m : K) * ∏ j ∈ I \ J, (x j : K)) • logWedge x I := by
  intro a
  induction a with
  | zero =>
    intro v _
    exact ⟨∅, 1, fun _ => rfl, by simp [logWedge]⟩
  | succ a ih =>
    intro v hv
    obtain ⟨I, m, hc, he⟩ := ih (Matrix.vecTail v) (fun i => hv i.succ)
    obtain ⟨i0, hi0⟩ := hv 0
    rw [ExteriorAlgebra.ιMulti_succ_apply, he, ← hi0, frame_eq, map_smul, smul_mul_smul_comm]
    by_cases hi : i0 ∈ I
    · refine ⟨∅, 0, fun h => absurd rfl h, ?_⟩
      rw [(GlobalTheory.T.logDifferential_mul_logCoordinateWedge K n x i0 I).1 hi]
      simp
    · obtain ⟨ε, hε, hw⟩ := (GlobalTheory.T.logDifferential_mul_logCoordinateWedge K n x i0 I).2 hi
      refine ⟨insert i0 I, m * ε, fun h => ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hi, hc (left_ne_zero_of_mul h)]
      · rw [hw, ← Int.cast_smul_eq_zsmul K, smul_smul, ← wt_mul_prod x J I i0 hi]
        push_cast
        ring_nf

theorem list_frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) : ∀ l : List (Fin n),
    (l.map fun i => ExteriorAlgebra.ι K (frame x J i)).prod =
      (l.map (wt x J)).prod • (l.map fun i => ExteriorAlgebra.ι K (dlog (x i))).prod
  | [] => by simp
  | i :: l => by
    simp only [List.map_cons, List.prod_cons]
    rw [list_frame x J l, frame_eq, map_smul, smul_mul_smul_comm]

theorem ofFn_orderEmbOfFin {n a : ℕ} (I : Finset (Fin n)) (h : I.card = a) {β : Type} (f : Fin n → β) :
    List.ofFn (fun i => f (I.orderEmbOfFin h i)) = (I.sort (· ≤ ·)).map f := by
  apply List.ext_getElem
  · simp [h]
  · intro k h1 h2
    simp [Finset.orderEmbOfFin_apply]

theorem ιMulti_orderEmbOfFin {n a : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) (h : I.card = a) :
    ExteriorAlgebra.ιMulti K a (fun i => frame x J (I.orderEmbOfFin h i)) =
      (∏ j ∈ I \ J, (x j : K)) • logWedge x I := by
  rw [ExteriorAlgebra.ιMulti_apply,
    show (List.ofFn fun i => ExteriorAlgebra.ι K (frame x J (I.orderEmbOfFin h i))) = _ from
      ofFn_orderEmbOfFin I h (fun j => ExteriorAlgebra.ι K (frame x J j)),
    list_frame, logWedge, ← prod_wt]
  congr 1
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.sort_eq, Finset.prod_eq_multiset_prod]

def coeffForms (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) :
    AddSubgroup (abelian₂ K) where
  carrier := {η | ∃ c : Finset (Fin n) → K, (∀ I, I.card ≠ a → c I = 0) ∧
    (∀ I, c I * t / ∏ j ∈ I \ J, (x j : K) ∈ A) ∧ η = ∑ I, c I • logWedge x I}
  add_mem' := by
    rintro _ _ ⟨c, h1, h2, rfl⟩ ⟨d, g1, g2, rfl⟩
    refine ⟨c + d, fun I h => by simp [h1 I h, g1 I h], fun I => ?_, by
      simp [add_smul, Finset.sum_add_distrib]⟩
    simpa [add_mul, add_div] using A.add_mem (h2 I) (g2 I)
  zero_mem' := ⟨0, by simp, by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨c, h1, h2, rfl⟩
    refine ⟨-c, fun I h => by simp [h1 I h], fun I => ?_, by simp [neg_smul, Finset.sum_neg_distrib]⟩
    simpa [neg_mul, neg_div] using A.neg_mem (h2 I)

end GlobalTheory.LogDR.ChartMem

namespace GlobalTheory.LogDR


open ChartMem in
theorem mem_chartForms_iff : ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) (η : abelian₂ K), η ∈ chartForms A x J t a ↔ ∃ c : Finset (Fin n) → K, (∀ I, I.card ≠ a → c I = 0) ∧ (∀ I, c I * t / ∏ j ∈ I \ J, (x j : K) ∈ A) ∧ η = ∑ I, c I • logWedge x I := by
  intro K _ A n x J t a η
  constructor
  · intro hη
    have hle : chartForms A x J t a ≤ coeffForms A x J t a := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      obtain ⟨I, m, hm, he⟩ := ιMulti_frame x J a v hv
      refine ⟨fun I' => if I' = I then c * ((m : K) * ∏ j ∈ I \ J, (x j : K)) else 0, ?_, ?_, ?_⟩
      · intro I' h'
        dsimp only
        split_ifs with e
        · subst e
          by_cases h0 : m = 0
          · simp [h0]
          · exact absurd (hm h0) h'
        · rfl
      · intro I'
        dsimp only
        split_ifs with e
        · subst e
          have hp := prod_sdiff_ne_zero x J I'
          have hq : c * ((m : K) * ∏ j ∈ I' \ J, (x j : K)) * t / ∏ j ∈ I' \ J, (x j : K) =
              (m : K) * (c * t) := by
            field_simp
          rw [hq]
          exact A.mul_mem (intCast_mem A m) hc
        · simp
      · rw [he, smul_smul]
        simp [ite_smul]
    exact hle hη
  · rintro ⟨c, h1, h2, rfl⟩
    refine AddSubgroup.sum_mem _ fun I _ => ?_
    by_cases h : I.card = a
    · have hp := prod_sdiff_ne_zero x J I
      have e : c I • logWedge x I = (c I / ∏ j ∈ I \ J, (x j : K)) •
          ExteriorAlgebra.ιMulti K a (fun i => frame x J (I.orderEmbOfFin h i)) := by
        rw [ιMulti_orderEmbOfFin, smul_smul, div_mul_cancel₀ _ hp]
      rw [e]
      apply AddSubgroup.subset_closure
      refine ⟨_, ?_, _, fun i => ⟨_, rfl⟩, rfl⟩
      show c I / _ * (t : K) ∈ A
      rw [div_mul_eq_mul_div]
      exact h2 I
    · rw [h1 I h, zero_smul]
      exact zero_mem _

end GlobalTheory.LogDR
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem fam_ev_param {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] {N : LB (A ⊗ T).left} (hN : Fam A N)
    (y : Y ⟶ T) : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
  refine ⟨h, (isAdditive_iff h).2 fun Z a a' t ↦ ?_⟩
  simp only [evc_ev hN.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)

theorem classify_mono : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left)
    (M : LB (A ⊗ U).left), Rep A b P → Fam A M → Inj A M →
    ∃ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' ∧ Same A M P (fst U S') φ ∧ Mono φ.left := by
  intro S A B S' U _ b P M hP hM hI
  obtain ⟨φ, ⟨hb, hN⟩, -⟩ := hP.univ (U ⊗ S') (snd U S') _ (fam_ev_param hM (fst U S'))
  have hS : Same A M P (fst U S') φ := hN
  refine ⟨φ, hb, hS, ?_⟩
  have hm : Mono φ := ⟨fun {Y} a a' e ↦ by
    have e1 : Same A M P (a ≫ fst U S') (a ≫ φ) := by
      rw [same_iff hM.isLB hP.fam.isLB] at hS ⊢
      have := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ a)).left) hS
      simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using this
    have e2 : Same A M P (a' ≫ fst U S') (a' ≫ φ) := by
      rw [same_iff hM.isLB hP.fam.isLB] at hS ⊢
      have := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ a')).left) hS
      simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using this
    have e3 : Same A M M (a ≫ fst U S') (a' ≫ fst U S') := by
      rw [same_iff hM.isLB hP.fam.isLB] at e1 e2
      rw [same_iff hM.isLB hM.isLB, e1, e2, e]
    have ef := hI Y _ _ e3
    have es : a ≫ snd U S' = a' ≫ snd U S' := by rw [← hb, reassoc_of% e]
    exact CartesianMonoidalCategory.hom_ext _ _ ef es⟩
  exact Over.mono_left_of_mono φ
end DualCon
end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RepChart

theorem repChart : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (M : LB (A ⊗ U).left), Rep A b P → Fam A M → ∀ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' → Same A M P (fst U S') φ → IsOpenImmersion φ.left → ∀ (T : Over S) (_ : T ⟶ S') (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  intro S A B S' U _ b P M hP hM φ hφb hsame hopen T t N hN
  have hP' := hP.fam.isLB
  have hM' := hM.isLB
  have hN' := hN.isLB
  obtain ⟨x, ⟨hxb, hxN⟩, -⟩ := hP.univ T t N hN
  have ex : cls N hN' = evc hP' (fst A T) (snd A T ≫ x) := (cls_eq_iff hN' (pull_isLB hP' _)).2 hxN
  have eφ : evc hM' (fst A (U ⊗ S')) (snd A (U ⊗ S') ≫ fst U S') = evc hP' (fst A (U ⊗ S')) (snd A (U ⊗ S') ≫ φ) :=
    (same_iff hM' hP' _ _).1 hsame
  have eY : ∀ (Y : Over S) (y : Y ⟶ T), evc hN' (fst A Y) (snd A Y ≫ y) = evc hP' (fst A Y) (snd A Y ≫ y ≫ x) := by
    intro Y y
    have e := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ y)).left) ex
    rw [pull_evc, lift_fst, lift_snd_assoc] at e
    exact e
  have eV : ∀ (Y : Over S) (v : Y ⟶ U ⊗ S'), evc hM' (fst A Y) (snd A Y ≫ v ≫ fst U S') =
      evc hP' (fst A Y) (snd A Y ≫ v ≫ φ) := by
    intro Y v
    have e := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ v)).left) eφ
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc] at e
    exact e
  have uniq : ∀ (Y : Over S) (y : Y ⟶ T) (x₁ x₂ : Y ⟶ B), x₁ ≫ b = y ≫ t → x₂ ≫ b = y ≫ t →
      evc hP' (fst A Y) (snd A Y ≫ x₁) = evc hN' (fst A Y) (snd A Y ≫ y) →
      evc hP' (fst A Y) (snd A Y ≫ x₂) = evc hN' (fst A Y) (snd A Y ≫ y) → x₁ = x₂ := by
    intro Y y x₁ x₂ h₁ h₂ e₁ e₂
    have hL : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN' _
    have hF : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
      refine ⟨hL, (isAdditive_iff hL).2 fun Z a a' z ↦ ?_⟩
      simp only [evc_ev hN', lift_fst, lift_snd_assoc]
      exact (isAdditive_iff hN').1 hN.add Z a a' (z ≫ y)
    refine (hP.univ Y (y ≫ t) _ hF).unique ⟨h₁, (cls_eq_iff hL (pull_isLB hP' _)).1 ?_⟩
      ⟨h₂, (cls_eq_iff hL (pull_isLB hP' _)).1 ?_⟩
    · rw [cls_ev hN', cls_ev hP', e₁]
    · rw [cls_ev hN', cls_ev hP', e₂]
  refine ⟨x.left ⁻¹ᵁ φ.left.opensRange, fun Y y ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu⟩
    rw [same_iff hN' hM'] at hu
    let v : Y ⟶ U ⊗ S' := lift u (y ≫ t)
    have hvx : v ≫ φ = y ≫ x := by
      refine uniq Y y _ _ ?_ ?_ ?_ (by rw [eY])
      · rw [Category.assoc, hφb, lift_snd]
      · rw [Category.assoc, hxb]
      · rw [← eV, lift_fst, hu]
    intro z
    have e := congrArg (fun q : Y ⟶ B ↦ q.left z) hvx
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at e
    simp only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
    exact ⟨_, e⟩
  · intro h
    have hr : Set.range (y.left ≫ x.left) ⊆ Set.range φ.left := by
      rintro _ ⟨z, rfl⟩
      have := h z
      simp only [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange] at this
      simpa [Scheme.Hom.comp_apply] using this
    let l := IsOpenImmersion.lift φ.left (y.left ≫ x.left) hr
    have hl : l ≫ φ.left = y.left ≫ x.left := IsOpenImmersion.lift_fac _ _ _
    let v : Y ⟶ U ⊗ S' := Over.homMk l (by
      rw [← Over.w φ, ← Category.assoc, hl, Category.assoc, Over.w x, Over.w y])
    have hvx : v ≫ φ = y ≫ x := Over.OverMorphism.ext (by simpa [v] using hl)
    refine ⟨v ≫ fst U S', (same_iff hN' hM' _ _).2 ?_⟩
    rw [eV, hvx, eY]

end GlobalTheory.RepChart
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_iso : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {Y Y' : Over S}, (Y ≅ Y') → HasRepAF A g Y → HasRepAF A g Y' := by
  first | exact @GlobalTheory.hasRepAF_of_iso | exact GlobalTheory.hasRepAF_of_iso | (intros; apply GlobalTheory.hasRepAF_of_iso <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Pinch

variable {S : Scheme.{0}}

theorem isPullback_fst_whiskerRight {X Y : Over S} (f : X ⟶ Y) (W : Over S) :
    IsPullback (fst X W) (f ▷ W) f (fst Y W) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift s.fst (s.snd ≫ snd _ _)) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp [s.condition]
    · simp
  · ext1
    · simp [← h1]
    · simp [← h2]

theorem isPullback_snd_whiskerLeft (W : Over S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (snd W X) (W ◁ f) f (snd W Y) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst _ _) s.fst) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp
    · simp [s.condition]
  · ext1
    · simp [← h2]
    · simp [← h1]

theorem rep_cmp (S : Scheme.{0}) (A B' S' C Z : Over S) [GrpObj A] (b' : B' ⟶ S') (P' : LB (A ⊗ B').left)
    (e : C ⟶ Z) (Q : LB (A ⊗ C).left) (h₁ : Rep A b' P') (h₂ : Rep A e Q) :
    ∃ q : B' ⊗ Z ⟶ C, q ≫ e = snd B' Z ∧ IsPullback q.left (fst B' Z ≫ b').left C.hom S'.hom ∧
      Same A P' Q (fst B' Z) q := by
  have r₁ := Rep.baseChange S A B' S' (S' ⊗ Z) (B' ⊗ Z) b' P' (fst S' Z) (fst B' Z) (b' ▷ Z) h₁
    (isPullback_fst_whiskerRight b' Z)
  have r₂ := Rep.baseChange S A C Z (S' ⊗ Z) (S' ⊗ C) e Q (snd S' Z) (snd S' C) (S' ◁ e) h₂
    (isPullback_snd_whiskerLeft S' e)
  obtain ⟨ε, hε, hs⟩ := rep_unique S A (B' ⊗ Z) (S' ⊗ C) (S' ⊗ Z) (b' ▷ Z) _ (S' ◁ e) _ r₁ r₂
  have hf : ε.hom.left ≫ (fst S' C).left = (fst B' Z ≫ b').left := by
    rw [← Over.comp_left, ← whiskerLeft_fst S' e, reassoc_of% hε, whiskerRight_fst]
  refine ⟨ε.hom ≫ snd S' C, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← whiskerLeft_snd, reassoc_of% hε, whiskerRight_snd]
  · have hpb : IsPullback (snd S' C).left (fst S' C).left C.hom S'.hom :=
      (IsPullback.of_hasPullback S'.hom C.hom).flip
    have : IsIso ε.hom.left := ⟨⟨ε.inv.left, by rw [← Over.comp_left, ε.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, ε.inv_hom_id, Over.id_left]⟩⟩
    have hiso : IsPullback ε.hom.left (fst B' Z ≫ b').left (fst S' C).left (𝟙 S'.left) :=
      IsPullback.of_horiz_isIso ⟨by rw [hf, Category.comp_id]⟩
    have := hiso.paste_horiz hpb
    rwa [Category.id_comp, ← Over.comp_left] at this
  · rw [same_iff h₁.fam.isLB h₂.fam.isLB]
    rw [same_iff r₁.fam.isLB r₂.fam.isLB, evc_ev h₁.fam.isLB, evc_ev h₂.fam.isLB] at hs
    simpa [lift_fst, lift_snd_assoc] using hs

end GlobalTheory.Pinch
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_affine_open_saturated_basicOpen_preimage : ∀ (B' C Y : Scheme.{0}) (i : Y ⟶ B') (q : Y ⟶ C), IsClosedImmersion i → IsFinite q → FinAff B' → ∀ (y : Y) (O : C.Opens), IsAffineOpen O → q y ∈ O → ∃ (V' : B'.Opens) (r : Γ(C, O)), IsAffineOpen V' ∧ i y ∈ V' ∧ i ⁻¹ᵁ V' = q ⁻¹ᵁ (C.basicOpen r) := by
  first | exact @GlobalTheory.Pinch.exists_affine_basicOpen_nbhd | exact GlobalTheory.Pinch.exists_affine_basicOpen_nbhd | (intros; apply GlobalTheory.Pinch.exists_affine_basicOpen_nbhd <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.properSmoothGeomConnected_sigmaDesc_disjoint_cover : ∀ {X : Scheme.{0}} {κ : Type} [Finite κ] (V : κ → X.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme) (g : ℕ), (∀ i, Good g (f i)) → Good g (Sigma.desc fun i => f i ≫ (V i).ι) := by
  first | exact @GlobalTheory.DualCon.good_sigmaDesc_of_disjoint_cover | exact GlobalTheory.DualCon.good_sigmaDesc_of_disjoint_cover | (intros; apply GlobalTheory.DualCon.good_sigmaDesc_of_disjoint_cover <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.relDimPreserved_of_equal_local_relDims : ∀ (S : Scheme.{0}) (A B : Over S), Surjective A.hom → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd A.hom (V i).ι)) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd B.hom (V i).ι)) → DimLe A B := by
  first | exact @GlobalTheory.DualCon.dimLe_of_local | exact GlobalTheory.DualCon.dimLe_of_local | (intros; apply GlobalTheory.DualCon.dimLe_of_local <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.representing_additiveFamilies_isDual_comm : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] (P : LB (A ⊗ B).left), Rep A (toUnit B) P → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsDual A B P ∧ IsAdditive (swap P) := by
  first | exact @GlobalTheory.DualCon.rep_isDual | exact GlobalTheory.DualCon.rep_isDual | (intros; apply GlobalTheory.DualCon.rep_isDual <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.representsAdditiveLineBundleFamilies_unique_iso : ∀ (S : Scheme.{0}) (A B B' S' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (b' : B' ⟶ S') (P' : LB (A ⊗ B').left), Rep A b P → Rep A b' P' → ∃ e : B ≅ B', e.hom ≫ b' = b ∧ Same A P P' (𝟙 B) e.hom := by
  first | exact @GlobalTheory.DualCon.rep_unique | exact GlobalTheory.DualCon.rep_unique | (intros; apply GlobalTheory.DualCon.rep_unique <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.FinAffNoeth

theorem finAff_of_relAmple_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → FinAff A.left := by
  intro R _ _ A _ hA L hL hR
  exact GlobalTheory.DualCon.FinAffAmple.finAff_of_relAmple R A hA L hL hR

end GlobalTheory.DualCon.FinAffNoeth
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sameRigidifiedFamily_abelianScheme_of_local : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ Same A M N (Over.homMk W.ι rfl ≫ u : Over.mk (W.ι ≫ Y.hom) ⟶ U) (Over.homMk W.ι rfl ≫ t)) → Same A M N u t := by
  first | exact @GlobalTheory.DualCon.SameLocal.same_of_local | exact GlobalTheory.DualCon.SameLocal.same_of_local | (intros; apply GlobalTheory.DualCon.SameLocal.same_of_local <;> assumption)
end
