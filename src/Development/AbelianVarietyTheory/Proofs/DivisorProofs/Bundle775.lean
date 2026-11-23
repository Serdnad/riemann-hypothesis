module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechHOneInj

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq {a b : (NE κ)ᵒᵖ} (f f' : a ⟶ b) : f = f' :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem mp_transport0 (g : C0 F) {a a' b : (NE κ)ᵒᵖ} (e : a = a') (f : a ⟶ b) (f' : a' ⟶ b) :
    mp F f (g a) = mp F f' (g a') := by
  subst e; rw [hom_eq f f']

theorem mp_transport1 {p : ℕ} (x : CC F p) {s s' : {s : Finset κ // s.card = p + 1}} (e : s = s')
    {b : (NE κ)ᵒᵖ} (f : ne s.1 (card_nonempty s) ⟶ b) (f' : ne s'.1 (card_nonempty s') ⟶ b) :
    mp F f (x s) = mp F f' (x s') := by
  subst e; rw [hom_eq f f']

theorem ne_eq_ne {s s' : Finset κ} (hs : s.Nonempty) (hs' : s'.Nonempty) (e : s = s') :
    ne s hs = ne s' hs' := by
  subst e; rfl

theorem min'_pair {i j : κ} (h : i < j) : ({i, j} : Finset κ).min' (Finset.insert_nonempty _ _) = i :=
  le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
    (Finset.le_min' _ _ _ (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> [exact le_rfl; exact h.le]))

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (z : CC F 1) {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) :
    e1 F z a b f = if h : mn b < mn a then
      -(mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b) (pair_subset f))
        (z ⟨{mn b, mn a}, Finset.card_pair h.ne⟩)) else 0 := by
  simp only [e1, LinearMap.pi_apply]; split_ifs <;> simp

end GlobalTheory.CechHOneInj

namespace GlobalTheory.CechHOneInj

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem δ_pair (z : CC F 1) (g : C0 F) (hg : e1 F z = d0 F g) {i j : κ} (h : i < j)
    (hs : ({i, j} : Finset κ).card = 1 + 1) :
    δ F 0 (fun s => g (ne s.1 (card_nonempty s))) ⟨{i, j}, hs⟩ = z ⟨{i, j}, hs⟩ := by
  have hi : i ∈ ({i, j} : Finset κ) := Finset.mem_insert_self _ _
  have hj : j ∈ ({i, j} : Finset κ) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have sij : ({i} : Finset κ) ⊆ {i, j} := Finset.singleton_subset_iff.2 hi
  have sji : ({j} : Finset κ) ⊆ {i, j} := Finset.singleton_subset_iff.2 hj
  have ei : ({i, j} : Finset κ).erase i = {j} := Finset.erase_insert (by simp [h.ne])
  have ej : ({i, j} : Finset κ).erase j = {i} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩
      · rfl
      · exact absurd rfl hx
    · rintro rfl; exact ⟨h.ne, Or.inl rfl⟩
  have h1 := congrFun (congrFun (congrFun hg (ne {i} (Finset.singleton_nonempty _)))
    (ne {i, j} (Finset.insert_nonempty _ _))) (homOf sij)
  have h2 := congrFun (congrFun (congrFun hg (ne {j} (Finset.singleton_nonempty _)))
    (ne {i, j} (Finset.insert_nonempty _ _))) (homOf sji)
  have mi : mn (ne ({i} : Finset κ) (Finset.singleton_nonempty _)) = i := Finset.min'_singleton i
  have mj : mn (ne ({j} : Finset κ) (Finset.singleton_nonempty _)) = j := Finset.min'_singleton j
  have mij : mn (ne ({i, j} : Finset κ) (Finset.insert_nonempty _ _)) = i := min'_pair h
  rw [orderedCechToCatCochainsOne_apply_valueAtSubset, amitsur_d0_apply, dite_eq_right (by rw [mi, mij]; exact lt_irrefl i)] at h1
  rw [orderedCechToCatCochainsOne_apply_valueAtSubset, amitsur_d0_apply, dite_eq_left (by rw [mj, mij]; exact h)] at h2
  have key := mp_transport1 F z
    (s := ⟨{mn (ne {i, j} (Finset.insert_nonempty _ _)), mn (ne {j} (Finset.singleton_nonempty _))},
      Finset.card_pair (by rw [mj, mij]; exact h.ne)⟩) (s' := ⟨{i, j}, hs⟩)
    (Subtype.ext (by simp only [mj, mij])) (homOf (pair_subset (homOf sji))) (𝟙 _)
  rw [mp_id] at key
  have si : GlobalTheory.cubeSign ({i, j} : Finset κ) i = 1 :=
    GlobalTheory.cubeSign_eq_one_of_forall_le (by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact le_rfl
      · exact h.le)
  have sj : GlobalTheory.cubeSign ({i, j} : Finset κ) j = -1 := by
    have := GlobalTheory.cubeSign_erase_of_lt hi h (t := ({i, j} : Finset κ))
    rw [ei, GlobalTheory.cubeSign_singleton] at this
    linarith
  rw [δ_apply, Fintype.sum_eq_add ⟨i, hi⟩ ⟨j, hj⟩ (by simp [h.ne]) (by
    rintro ⟨x, hx⟩ ⟨ha, hb⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact absurd rfl ha
    · exact absurd rfl hb)]
  dsimp only
  have tj := mp_transport0 F g (ne_eq_ne _ (Finset.singleton_nonempty j) ei)
    (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx (⟨{i, j}, hs⟩ : {s : Finset κ // s.card = 1 + 1}) ⟨i, hi⟩)))
      (b := ne {i, j} (Finset.insert_nonempty _ _)) (Finset.erase_subset _ _))
    (homOf (a := ne {j} (Finset.singleton_nonempty j)) (b := ne {i, j} (Finset.insert_nonempty _ _)) sji)
  have ti := mp_transport0 F g (ne_eq_ne _ (Finset.singleton_nonempty i) ej)
    (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx (⟨{i, j}, hs⟩ : {s : Finset κ // s.card = 1 + 1}) ⟨j, hj⟩)))
      (b := ne {i, j} (Finset.insert_nonempty _ _)) (Finset.erase_subset _ _))
    (homOf (a := ne {i} (Finset.singleton_nonempty i)) (b := ne {i, j} (Finset.insert_nonempty _ _)) sij)
  rw [si, sj, one_smul, neg_smul, one_smul]
  linear_combination h2 - h1 + key + tj - ti

theorem exists_cech_primitive : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (z : CC F 1), δ F 1 z = 0 →
    ∀ g : C0 F, e1 F z = d0 F g → ∃ c : CC F 0, δ F 0 c = z := by
  intro κ _ R _ F z _ g hg
  refine ⟨fun s => g (ne s.1 (card_nonempty s)), ?_⟩
  funext t
  obtain ⟨s, hs⟩ := t
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hs
  rcases lt_or_gt_of_ne hij with h | h
  · exact δ_pair F z g hg h hs
  · revert hs
    rw [Finset.pair_comm i j]
    exact δ_pair F z g hg h

end GlobalTheory.CechHOneInj
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

def triVal (c : CC F 2) (X : (NE κ)ᵒᵖ) (s : Finset κ) : F.obj X :=
  if h : s.card = 2 + 1 ∧ s ⊆ sub X then
    mp F (homOf (a := ne s (card_nonempty ⟨s, h.1⟩)) (b := X) h.2) (c ⟨s, h.1⟩)
  else 0

variable {F}

theorem hom_eq {a b : (NE κ)ᵒᵖ} (f g : a ⟶ b) : f = g := Subsingleton.elim _ _

theorem triVal_eq (c : CC F 2) (X : (NE κ)ᵒᵖ) {s : Finset κ} (hs : s.card = 2 + 1) (h : s ⊆ sub X) :
    mp F (homOf (a := ne s (card_nonempty ⟨s, hs⟩)) (b := X) h) (c ⟨s, hs⟩) = triVal F c X s := by
  unfold triVal; rw [dite_eq_left ⟨hs, h⟩]

theorem triVal_map (c : CC F 2) {X Y : (NE κ)ᵒᵖ} (f : X ⟶ Y) {s : Finset κ} (h : s ⊆ sub X) :
    mp F f (triVal F c X s) = triVal F c Y s := by
  unfold triVal
  by_cases hs : s.card = 2 + 1
  · rw [dite_eq_left ⟨hs, h⟩, dite_eq_left ⟨hs, h.trans (sub_subset f)⟩, ← mp_comp]
    congr 1
  · rw [dite_eq_right (fun h' => hs h'.1), dite_eq_right (fun h' => hs h'.1), map_zero]

theorem alternatingToOrderedCechDegreeTwo_apply_triple (c : CC F 2) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    e2 F c a b d f g = if mn d < mn b ∧ mn b < mn a then -triVal F c d {mn d, mn b, mn a} else 0 := by
  unfold e2
  simp only [LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [← triVal_eq c d (card_three h.1 h.2) (triple_subset f g)]
    rfl
  · rfl

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem triVal_eq' (c : CC F 2) {X : (NE κ)ᵒᵖ} (s : {s : Finset κ // s.card = 2 + 1})
    (f : ne s.1 (card_nonempty s) ⟶ X) : mp F f (c s) = triVal F c X s.1 := by
  obtain ⟨s, hs⟩ := s
  rw [← triVal_eq c X hs (sub_subset f), hom_eq f (homOf (sub_subset f))]

theorem triVal_rel (c : CC F 2) (hc : δ F 2 c = 0) (X : (NE κ)ᵒᵖ) {w x y z : κ}
    (h1 : w < x) (h2 : x < y) (h3 : y < z) (hs : ({w, x, y, z} : Finset κ) ⊆ sub X) :
    triVal F c X {x, y, z} - triVal F c X {w, y, z} + triVal F c X {w, x, z} - triVal F c X {w, x, y} = 0 := by
  have ht : ({w, x, y, z} : Finset κ).card = 2 + 1 + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [h1.ne, (h1.trans h2).ne, (h1.trans (h2.trans h3)).ne]),
      Finset.card_insert_of_notMem (by simp [h2.ne, (h2.trans h3).ne]), Finset.card_pair h3.ne]
  have e := congrArg (mp F (homOf (a := ne _ (card_nonempty ⟨_, ht⟩)) (b := X) hs))
    (congrFun hc ⟨_, ht⟩)

  rw [δ_apply, map_sum, Pi.zero_apply, map_zero] at e
  have e' : ∑ i ∈ ({w, x, y, z} : Finset κ), GlobalTheory.cubeSign ({w, x, y, z} : Finset κ) i •
      triVal F c X (({w, x, y, z} : Finset κ).erase i) = 0 := by
    rw [← e, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← mp_comp, triVal_eq']
  rw [Finset.sum_insert (by simp [h1.ne, (h1.trans h2).ne, (h1.trans (h2.trans h3)).ne]),
    Finset.sum_insert (by simp [h2.ne, (h2.trans h3).ne]), Finset.sum_pair h3.ne] at e'
  have hwx := h1.ne; have hwy := (h1.trans h2).ne; have hwz := (h1.trans (h2.trans h3)).ne
  have hxy := h2.ne; have hxz := (h2.trans h3).ne; have hyz := h3.ne
  simp only [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h1, h2, h3, h1.trans h2,
    h1.trans (h2.trans h3), h2.trans h3, lt_irrefl, not_lt_of_gt, if_true, if_false] at e'
  simp only [Finset.insert_empty, Finset.card_empty, Finset.card_singleton,
    Finset.card_pair hwx, Finset.card_insert_of_notMem (show w ∉ ({x, y} : Finset κ) by simp [hwx, hwy]),
    Finset.card_pair hxy] at e'
  rw [Finset.erase_insert (by simp [hwx, hwy, hwz]),
    Finset.erase_insert_of_ne hwx, Finset.erase_insert (by simp [hxy, hxz]),
    Finset.erase_insert_of_ne hwy, Finset.erase_insert_of_ne hxy,
    Finset.erase_insert (by simp [hyz]),
    Finset.erase_insert_of_ne hwz, Finset.erase_insert_of_ne hxz,
    Finset.erase_insert_of_ne hyz, Finset.erase_singleton] at e'
  norm_num at e'
  linear_combination e'

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem alternatingToOrderedCechDegreeTwo_map_apply (c : CC F 2) {a b d g : (NE κ)ᵒᵖ} (f : a ⟶ b) (f' : b ⟶ d) (f'' : d ⟶ g) :
    mp F f'' (e2 F c a b d f f') =
      if mn d < mn b ∧ mn b < mn a then -triVal F c g {mn d, mn b, mn a} else 0 := by
  rw [alternatingToOrderedCechDegreeTwo_apply_triple]
  split_ifs
  · rw [map_neg, triVal_map c f'' (triple_subset f f')]
  · exact map_zero _

theorem e2_mem_Z2_of_delta_eq_zero (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2) (hc : δ F 2 c = 0) :
    e2 F c ∈ Z2 F := by
  intro a b d g φ ψ χ
  have hab := mn_le_of_hom φ; have hbd := mn_le_of_hom ψ; have hdg := mn_le_of_hom χ
  have hs : ({mn g, mn d, mn b, mn a} : Finset κ) ⊆ sub g := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mn_mem g
    · exact sub_subset χ (mn_mem d)
    · exact sub_subset (ψ ≫ χ) (mn_mem b)
    · exact sub_subset (φ ≫ ψ ≫ χ) (mn_mem a)
  have hrel : mn g < mn d → mn d < mn b → mn b < mn a →
      triVal F c g {mn d, mn b, mn a} - triVal F c g {mn g, mn b, mn a} +
        triVal F c g {mn g, mn d, mn a} - triVal F c g {mn g, mn d, mn b} = 0 :=
    fun h1 h2 h3 => triVal_rel c hc g h1 h2 h3 hs
  rw [alternatingToOrderedCechDegreeTwo_map_apply, alternatingToOrderedCechDegreeTwo_apply_triple, alternatingToOrderedCechDegreeTwo_apply_triple, alternatingToOrderedCechDegreeTwo_apply_triple]
  generalize mn a = xa at *
  generalize mn b = xb at *
  generalize mn d = xd at *
  generalize mn g = xg at *
  rcases hdg.lt_or_eq with h1 | rfl <;> rcases hbd.lt_or_eq with h2 | rfl <;>
    rcases hab.lt_or_eq with h3 | rfl <;>
    simp_all [lt_irrefl, not_lt_of_ge, le_of_lt]
  rw [if_pos (h2.trans h3), if_pos (h1.trans h2)]
  linear_combination -hrel
end GlobalTheory.CechPoset
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

noncomputable section

open Opposite

namespace GlobalTheory.CechPoset

section Bij

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem sec_res_self (s : X ⟶ Sp R) {U : X.Opens} (h : U ≤ U) (c : Sec s U) : Sec.res s h c = c :=
  congrArg (fun q ↦ q.hom c) (X.presheaf.map_id (op U))

theorem ker_res (s : X ⟶ Sp R) (g : LinearMap.ker (d0 (OAff s))) {U V : X.affineOpens}
    (h : V.1 ≤ U.1) : g.1 (op V) = Sec.res s h (g.1 (op U)) := by
  have := congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) (op U)) (op V))
    (homOfLE (show V ≤ U from h)).op
  rw [amitsur_d0_apply] at this
  exact sub_eq_zero.1 this

variable {κ : Type} [LinearOrder κ]

theorem kerF_res (s : X ⟶ Sp R) (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (g : LinearMap.ker (d0 (covF s D hD))) {I J : Finset κ} (hI : I.Nonempty) (hJ : J.Nonempty)
    (h : I ⊆ J) {U : X.Opens} (hU : U ≤ ⨅ k ∈ J, D k) (hU' : U ≤ ⨅ k ∈ I, D k) :
    Sec.res s hU' (g.1 (ne I hI)) = Sec.res s hU (g.1 (ne J hJ)) := by
  have e := congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) (ne I hI)) (ne J hJ))
    (homOf (a := ne I hI) (b := ne J hJ) h)
  rw [amitsur_d0_apply] at e
  have e' : g.1 (ne J hJ) = Sec.res s (show (⨅ k ∈ J, D k) ≤ ⨅ k ∈ I, D k from
      biInf_mono fun _ hk ↦ h hk) (g.1 (ne I hI)) := sub_eq_zero.1 e
  rw [e']
  exact Sec.res_res s _ hU _

end Bij

theorem restrictCompatibleFamilyToIntersections_bijective {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {κ : Type}
    [LinearOrder κ] [Fintype κ] (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    ⨆ i, D i = ⊤ → Function.Bijective (res0 s D hD) := by
  intro hcov
  have hle1 : ∀ i : κ, D i ≤ ⨅ k ∈ ({i} : Finset κ), D k := fun i ↦
    le_iInf₂ fun k hk ↦ by rw [Finset.mem_singleton.1 hk]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro g hg
    have h0 : ∀ i : κ, g.1 (op (cov D hD (OrderDual.toDual ⟨{i}, Finset.singleton_nonempty i⟩))) = 0 :=
      fun i ↦ congrFun (congrArg Subtype.val hg) (ne {i} (Finset.singleton_nonempty i))
    apply Subtype.ext
    funext V
    show g.1 V = 0
    let Idx := {p : X.affineOpens × κ // p.1.1 ≤ V.unop.1 ⊓ D p.2}
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun j : Idx ↦ j.1.1.1) V.unop.1
      (fun j ↦ homOfLE (j.2.trans inf_le_left)) ?_ _ _ ?_
    · intro x hx
      have hx' : x ∈ ⨆ i, D i := by rw [hcov]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
      obtain ⟨W, hWB, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ V.unop.1 ⊓ D i from ⟨hx, hi⟩)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨W, hWB⟩, i), hWle⟩, hxW⟩
    · intro j
      have hW : j.1.1.1 ≤ V.unop.1 := j.2.trans inf_le_left
      have hWi : j.1.1.1 ≤ (cov D hD (OrderDual.toDual ⟨{j.1.2}, Finset.singleton_nonempty _⟩)).1 :=
        (j.2.trans inf_le_right).trans (hle1 j.1.2)
      have e1 := ker_res s g (U := V.unop) (V := j.1.1) hW
      have e2 := ker_res s g (V := j.1.1) hWi
      rw [h0, map_zero] at e2
      show Sec.res s hW (g.1 V) = Sec.res s hW 0
      rw [map_zero, ← e1, e2]
  · intro g'
    let sf : ∀ i : κ, Sec s (D i) := fun i ↦ Sec.res s (hle1 i) (g'.1 (ne {i} (Finset.singleton_nonempty i)))
    have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 D sf := by
      intro i j
      show Sec.res s inf_le_left (sf i) = Sec.res s inf_le_right (sf j)
      have hij : D i ⊓ D j ≤ ⨅ k ∈ ({i, j} : Finset κ), D k := le_iInf₂ fun k hk ↦ by
        obtain hk | hk := Finset.mem_insert.1 hk
        · rw [hk]; exact inf_le_left
        · rw [Finset.mem_singleton.1 hk]; exact inf_le_right
      exact (Sec.res_res s (hle1 i) inf_le_left _).symm.trans
        ((kerF_res s D hD g' (Finset.singleton_nonempty i) (Finset.insert_nonempty _ _)
          (by simp) hij (inf_le_left.trans (hle1 i))).trans
        ((kerF_res s D hD g' (Finset.singleton_nonempty j) (Finset.insert_nonempty _ _)
          (by simp) hij (inf_le_right.trans (hle1 j))).symm.trans
        (Sec.res_res s (hle1 j) inf_le_right _)))
    obtain ⟨G, hG, -⟩ := X.sheaf.existsUnique_gluing' D ⊤ (fun i ↦ homOfLE le_top) hcov.symm.le sf hcomp
    let g : LinearMap.ker (d0 (OAff s)) := ⟨fun V ↦ Sec.res s le_top (G : Γ(X, ⊤)), by
      rw [LinearMap.mem_ker]
      funext U U' φ
      rw [amitsur_d0_apply]
      show Sec.res s le_top (G : Γ(X, ⊤)) - Sec.res s _ (Sec.res s le_top (G : Γ(X, ⊤))) = 0
      exact sub_eq_zero.2 (Sec.res_res s _ _ _)⟩
    refine ⟨g, Subtype.ext (funext fun I ↦ ?_)⟩
    show Sec.res s le_top (G : Γ(X, ⊤)) = g'.1 I
    have hm := mn_mem I
    have hi : (cov D hD I.unop).1 ≤ D (mn I) := iInf₂_le (mn I) hm
    have hGi : Sec.res s (le_top : D (mn I) ≤ ⊤) (G : Γ(X, ⊤)) = sf (mn I) := hG (mn I)
    refine (Sec.res_res s le_top hi _).trans ?_
    rw [hGi]
    exact (Sec.res_res s (hle1 (mn I)) hi _).symm.trans
      ((kerF_res s D hD g' (Finset.singleton_nonempty (mn I)) (sub_nonempty I)
        (Finset.singleton_subset_iff.2 hm) le_rfl _).trans (sec_res_self s _ _))

end GlobalTheory.CechPoset
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_bijective {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') (V : X'.Opens) : Function.Bijective (trivCoord φ s' V) :=
  (GlobalTheory.AbLaw.SecOn.chart (LB.isLB_pull (LB.isLB_triv X) φ) (i0 φ)
    (by rw [triv_pull_U]; exact le_top)).bijective

theorem Φ_bijective_of_affine : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (h : IsPullback φ s' s (spMap (algebraMap R R'))) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ∀ p : ℕ, Function.Bijective (Φ h.w D hD' p) := by
  intro R R' _ _ _ X X' s s' φ h κ _ _ D hD' hD p
  have hB := GlobalTheory.AbLaw.secTermBaseChange_bijective (M := LB.triv X) (D := D) (LB.isLB_triv X) h (p + 1)
    fun t ht => hD t (Finset.card_pos.1 (by omega))
  exact (Function.Bijective.piMap fun t => trivCoord_bijective φ s' _).comp hB

end GlobalTheory.CechPoset
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset

theorem Φ_one_tmul : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), Φ w D hD' 0 ((1 : R') ⊗ₜ[R] one s D) = fun _ => 1 := by
  intro R R' _ _ _ X X' s s' φ w κ _ D hD'
  funext t
  have key : GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ) = 1 := by
    erw [GlobalTheory.AbLaw.secTermBaseChange_tmul, one_smul]
    refine (GlobalTheory.AbLaw.SecOn.coord_pullLE (M := LB.triv X) φ (GlobalTheory.AbLaw.preimage_biInf D φ t.1).ge ((GlobalTheory.AbLaw.secOnTrivEquiv _).symm 1) (i0 φ)).trans ?_
    have hc : GlobalTheory.LB.coord ((GlobalTheory.AbLaw.secOnTrivEquiv (X := X) (⨅ i ∈ t.1, D i)).symm 1) PUnit.unit = 1 := by
      refine (GlobalTheory.AbLaw.SecOn.coord_chart_symm (M := Out.Inh.trivLB X) (Out.Inh.trivLB_isLB X) PUnit.unit PUnit.unit le_top (1 : Γ(X, ⨅ i ∈ t.1, D i))).trans ?_
      rw [map_one]
      exact (_root_.one_mul _).trans (map_one _)
    exact (congrArg _ hc).trans (map_one _)
  change Sec.res s' _ (GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ)) = 1
  rw [key]
  exact (Sec.res s' _).map_one

end GlobalTheory.CechPoset
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem sum_cubeSign_card_two {κ : Type} [LinearOrder κ] (t : Finset κ) (h : t.card = 2) :
    ∑ i ∈ t, GlobalTheory.cubeSign t i = 0 := by
  have key : ∀ x y : κ, x < y → ∑ i ∈ ({x, y} : Finset κ), GlobalTheory.cubeSign {x, y} i = 0 := by
    intro x y hxy
    rw [Finset.sum_pair hxy.ne]
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, hxy, hxy.not_gt]
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h
  rcases lt_or_gt_of_ne hxy with h' | h'
  · exact key x y h'
  · rw [Finset.pair_comm]; exact key y x h'

theorem δ_zero_one : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), δ F 0 (fun _ => 1) = 0 := by
  intro κ _ R _ F
  funext t
  rw [δ_apply]
  simp only [map_one, Pi.zero_apply]
  rw [← Finset.sum_smul, Finset.sum_coe_sort t.1 (fun i => GlobalTheory.cubeSign t.1 i),
    sum_cubeSign_card_two t.1 t.2, zero_smul]

end GlobalTheory.CechPoset
end
