module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx.RowLink

variable {R : Type} [CommRing R] {N : ℕ}

def Orth (y z : (Fin N → R) × (Fin N → R)) : Prop := y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0

theorem mem_splitSeq_iff (l : List ((Fin N → R) × (Fin N → R))) :
    l ∈ splitSeq R N ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise Orth := by
  simp only [splitSeq, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, List.pairwise_iff_get.mpr fun i j hij => ⟨?_, ?_⟩⟩
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hy
      simpa using h i i
    · simpa [Fin.ne_of_lt hij] using h i j
    · simpa [(Fin.ne_of_lt hij).symm] using h j i
  · rintro ⟨h1, h2⟩ i j
    have hp := List.pairwise_iff_get.mp h2
    rcases lt_trichotomy i j with hij | rfl | hij
    · simpa [Fin.ne_of_lt hij] using (hp i j hij).1
    · simpa using h1 _ (List.get_mem l i)
    · simpa [(Fin.ne_of_lt hij).symm] using (hp j i hij).2

theorem append_mem_splitSeq_iff (l₁ l₂ : List ((Fin N → R) × (Fin N → R))) :
    l₁ ++ l₂ ∈ splitSeq R N ↔
      l₁ ∈ splitSeq R N ∧ l₂ ∈ splitSeq R N ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, Orth a b := by
  rw [mem_splitSeq_iff, mem_splitSeq_iff, mem_splitSeq_iff, List.pairwise_append]
  constructor
  · rintro ⟨h1, p1, p2, p3⟩
    exact ⟨⟨fun y hy => h1 y (List.mem_append.mpr (Or.inl hy)), p1⟩,
      ⟨fun y hy => h1 y (List.mem_append.mpr (Or.inr hy)), p2⟩, p3⟩
  · rintro ⟨⟨h1, p1⟩, ⟨h2, p2⟩, p3⟩
    exact ⟨fun y hy => (List.mem_append.mp hy).elim (h1 y) (h2 y), p1, p2, p3⟩

def corr (γ : List ((Fin N → R) × (Fin N → R))) (v : Fin N → R) : Fin N → R :=
  v - ∑ i : Fin γ.length, ((γ.get i).2 ⬝ᵥ v) • (γ.get i).1

theorem dot_corr_of_orth (γ : List ((Fin N → R) × (Fin N → R))) (u v : Fin N → R)
    (hu : ∀ z ∈ γ, u ⬝ᵥ z.1 = 0) : u ⬝ᵥ corr γ v = u ⬝ᵥ v := by
  unfold corr
  rw [dotProduct_sub, dotProduct_sum, Finset.sum_eq_zero, sub_zero]
  intro i _
  rw [dotProduct_smul, hu _ (List.get_mem γ i), smul_zero]

theorem form_dot_corr (γ : List ((Fin N → R) × (Fin N → R))) (hγ : γ ∈ splitSeq R N)
    (z : (Fin N → R) × (Fin N → R)) (hz : z ∈ γ) (v : Fin N → R) : z.2 ⬝ᵥ corr γ v = 0 := by
  obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hz
  have h : ∀ i j : Fin γ.length, (γ.get i).2 ⬝ᵥ (γ.get j).1 = if i = j then 1 else 0 := hγ
  unfold corr
  rw [dotProduct_sub, dotProduct_sum]
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin γ.length)),
      (γ.get k).2 ⬝ᵥ (((γ.get i).2 ⬝ᵥ v) • (γ.get i).1) =
        if k = i then (γ.get i).2 ⬝ᵥ v else 0 := by
    intro i _
    rw [dotProduct_smul, h k i, smul_eq_mul]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hs, Finset.sum_ite_eq Finset.univ k, if_pos (Finset.mem_univ _),
    sub_self]

end GlobalTheory.SeqCx.RowLink

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exists_splitSeq_linkIn_orthogonal_eq_linkIn : ∀ (R : Type) [CommRing R] (N : ℕ) (γ σ : List ((Fin N → R) × (Fin N → R))), γ ∈ splitSeq R N → σ ∈ splitSeq R N → (∀ y ∈ σ, ∀ z ∈ γ, y.2 ⬝ᵥ z.1 = 0) → ∃ ρ ∈ splitSeq R N, ρ.length = γ.length + σ.length ∧ linkIn {x | x ∈ splitSeq R N ∧ ∀ y ∈ x, ∀ z ∈ γ, y.2 ⬝ᵥ z.1 = 0} {y | ∀ z ∈ γ, z.2 ⬝ᵥ y.1 = 0} σ = linkIn (splitSeq R N) Set.univ ρ := by
  intro R _ N γ σ hγ hσ hσγ
  obtain ⟨σ', hσ'eq⟩ : ∃ s, s = σ.map (fun y => (GlobalTheory.SeqCx.RowLink.corr γ y.1, y.2)) := ⟨_, rfl⟩
  have hc : ∀ y ∈ σ, ∀ v, y.2 ⬝ᵥ GlobalTheory.SeqCx.RowLink.corr γ v = y.2 ⬝ᵥ v :=
    fun y hy v => GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ y.2 v (hσγ y hy)
  have hσ's : σ' ∈ splitSeq R N := by
    rw [GlobalTheory.SeqCx.RowLink.mem_splitSeq_iff] at hσ ⊢
    rw [hσ'eq]
    refine ⟨?_, ?_⟩
    · intro y' hy'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hy'
      show y.2 ⬝ᵥ GlobalTheory.SeqCx.RowLink.corr γ y.1 = 1
      rw [hc y hy]
      exact hσ.1 y hy
    · rw [List.pairwise_map]
      refine hσ.2.imp_of_mem ?_
      intro a b ha hb hab
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at hab ⊢
      exact ⟨(hc a ha b.1).trans hab.1, (hc b hb a.1).trans hab.2⟩
  have horth : ∀ a ∈ γ, ∀ b ∈ σ', GlobalTheory.SeqCx.RowLink.Orth a b := by
    intro a ha b hb
    rw [hσ'eq] at hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    simp only [GlobalTheory.SeqCx.RowLink.Orth]
    exact ⟨GlobalTheory.SeqCx.RowLink.form_dot_corr γ hγ a ha y.1, hσγ y hy a ha⟩
  have hρ : γ ++ σ' ∈ splitSeq R N :=
    (GlobalTheory.SeqCx.RowLink.append_mem_splitSeq_iff γ σ').mpr ⟨hγ, hσ's, horth⟩
  refine ⟨γ ++ σ', hρ, by rw [List.length_append, hσ'eq, List.length_map], ?_⟩
  ext w
  simp only [linkIn, Set.mem_setOf_eq, Set.mem_univ, implies_true, true_and, List.append_assoc,
    GlobalTheory.SeqCx.RowLink.append_mem_splitSeq_iff, List.mem_append]
  constructor
  · rintro ⟨hS, ⟨-, hw, hσw⟩, hz⟩
    refine ⟨hγ, ⟨hσ's, hw, ?_⟩, ?_⟩
    · intro a ha b hb
      rw [hσ'eq] at ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      have h1 := hσw y hy b hb
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at h1 ⊢
      exact ⟨h1.1, (GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ b.2 y.1 (hz b (Or.inr hb))).trans h1.2⟩
    · intro a ha b hb
      rcases hb with hb | hb
      · exact horth a ha b hb
      · simp only [GlobalTheory.SeqCx.RowLink.Orth]
        exact ⟨hS b hb a ha, hz b (Or.inr hb) a ha⟩
  · rintro ⟨-, ⟨-, hw, hσ'w⟩, hγx⟩
    refine ⟨fun x hx z hz => And.left (hγx z hz x (Or.inr hx)), ⟨hσ, hw, ?_⟩, ?_⟩
    · intro a ha b hb
      have hbγ : ∀ z ∈ γ, b.2 ⬝ᵥ z.1 = 0 := fun z hz => And.right (hγx z hz b (Or.inr hb))
      have h1 := hσ'w (GlobalTheory.SeqCx.RowLink.corr γ a.1, a.2)
        (by rw [hσ'eq]; exact List.mem_map.mpr ⟨a, ha, rfl⟩) b hb
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at h1 ⊢
      exact ⟨h1.1, (GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ b.2 a.1 hbγ).symm.trans h1.2⟩
    · intro y hy z hz
      rcases hy with hy | hy
      · exact hσγ y hy z hz
      · exact And.right (hγx z hz y (Or.inr hy))

end
end

section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx.BdBd

theorem bd_single (V : Type) (l : List V) (r : ℤ) :
    bd V (Finsupp.single l r) =
      r • ∑ i ∈ Finset.range l.length, (-1 : ℤ) ^ i • Finsupp.single (l.eraseIdx i) (1 : ℤ) := by
  simp [bd, Finsupp.linearCombination_single]

noncomputable def consMap (V : Type) (x : V) : (List V →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun l : List V => x :: l)

theorem bd_single_cons (V : Type) (x : V) (l : List V) :
    bd V (Finsupp.single (x :: l) 1) =
      Finsupp.single l 1 - consMap V x (bd V (Finsupp.single l 1)) := by
  rw [bd_single, bd_single, one_smul, one_smul, List.length_cons, Finset.sum_range_succ']

  simp only [consMap, map_sum, map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
  List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, pow_zero, one_smul, pow_succ, mul_neg_one,
  neg_smul, Finset.sum_neg_distrib]
  abel

theorem bd_consMap (V : Type) (x : V) :
    bd V ∘ₗ consMap V x = LinearMap.id - consMap V x ∘ₗ bd V := by
  apply Finsupp.lhom_ext
  intro l r
  have h : Finsupp.single l r = r • Finsupp.single l (1 : ℤ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [h]
  simp only [map_zsmul]
  rw [show consMap V x (Finsupp.single l 1) = Finsupp.single (x :: l) 1 by
    simp [consMap, Finsupp.mapDomain_single], bd_single_cons, smul_sub]

theorem bd_bd_single (V : Type) (l : List V) : bd V (bd V (Finsupp.single l 1)) = 0 := by
  induction l with
  | nil => simp [bd_single]
  | cons x l ih =>
    rw [bd_single_cons, map_sub]
    have := congrArg (fun f => f (bd V (Finsupp.single l 1))) (bd_consMap V x)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at this
    rw [this, ih, map_zero]
    abel

end GlobalTheory.SeqCx.BdBd

namespace GlobalTheory.SeqCx

theorem bd_bd : ∀ (V : Type) (c : List V →₀ ℤ), bd V (bd V c) = 0 := by
  intro V c
  have h : bd V ∘ₗ bd V = 0 := by
    apply Finsupp.lhom_ext
    intro l r
    have e : Finsupp.single l r = r • Finsupp.single l (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [e, map_zsmul, map_zsmul, GlobalTheory.SeqCx.BdBd.bd_bd_single, smul_zero]
  exact congrArg (fun f => f c) h

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_boundary_comp_boundary_apply : ∀ (V : Type) (c : List V →₀ ℤ), bd V (bd V c) = 0 := by
  first
  | exact @GlobalTheory.SeqCx.bd_bd
  | exact @GlobalTheory.SeqCx.BdBd.bd_bd_single
  | exact @GlobalTheory.SeqCx.BdBd.bd_consMap
  | exact @GlobalTheory.SeqCx.BdBd.bd_single_cons
  | exact @GlobalTheory.SeqCx.BdBd.bd_single
end
end

section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

private theorem bd_single_eq_sum_neg_one_pow_eraseIdx (V : Type) (l : List V) :
    bd V (Finsupp.single l 1) =
      ∑ i ∈ Finset.range l.length, (-1 : ℤ) ^ i • Finsupp.single (l.eraseIdx i) 1 := by
  simp [bd, Finsupp.linearCombination_single]

theorem bd_single_append (V : Type) (τ w : List V) :
    bd V (Finsupp.single (τ ++ w) 1) =
      Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1)) +
      (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (bd V (Finsupp.single w 1)) := by
  simp only [bd_single_eq_sum_neg_one_pow_eraseIdx, Finsupp.mapDomain_finsetSum, Finset.smul_sum]
  rw [List.length_append, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single, List.eraseIdx_append_of_lt_length hi]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single,
      List.eraseIdx_append_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      pow_add, mul_smul]

theorem bd_mapDomain_prepend : ∀ (V : Type) (τ : List V) (c : List V →₀ ℤ), bd V (Finsupp.mapDomain (fun w => τ ++ w) c) = (c.sum fun w a => a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1))) + (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (bd V c) := by
  intro V τ c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.mapDomain_add, smul_add,
      Finsupp.sum_add_index' (by intro; simp) (by intros; simp [add_smul])]
    abel
  | single w a =>
    rw [Finsupp.mapDomain_single, Finsupp.sum_single_index (by simp)]
    have h1 : Finsupp.single (τ ++ w) a = a • Finsupp.single (τ ++ w) (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have h2 : Finsupp.single w a = a • Finsupp.single w (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1, h2, map_smul, map_smul, bd_single_append, Finsupp.mapDomain_smul, smul_add, smul_comm a]

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_boundary_prefix_chain : ∀ (V : Type) (τ : List V) (c : List V →₀ ℤ), bd V (Finsupp.mapDomain (fun w => τ ++ w) c) = (c.sum fun w a => a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1))) + (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (bd V c) := by
  first
  | exact @GlobalTheory.SeqCx.bd_mapDomain_prepend
  | exact @GlobalTheory.SeqCx.bd_single_append
end
end

section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.ShapiroZero

theorem H0π_smul {k G : Type} [CommRing k] [Group G] (B : Rep k G) (g : G) (v : B.V) :
    (groupHomology.H0π B).hom (B.ρ g v) = (groupHomology.H0π B).hom v := by
  have e : ∀ w : B.V, (groupHomology.H0Iso B).hom.hom ((groupHomology.H0π B).hom w) =
      Representation.Coinvariants.mk B.ρ w :=
    fun w => congrArg (fun f => ModuleCat.Hom.hom f w) (groupHomology.H0π_comp_H0Iso_hom B)
  have hinj : Function.Injective (groupHomology.H0Iso B).hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [e, e, Representation.Coinvariants.mk_self_apply]

theorem linkExactnessStability_hom_fact {k G : Type} [CommRing k] [Group G] (B : Rep k G) (v : B.V) :
    (groupHomology.H0Iso B).hom.hom ((groupHomology.H0π B).hom v) = Representation.Coinvariants.mk B.ρ v := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f v) (groupHomology.H0π_comp_H0Iso_hom B)
  exact h

end GlobalTheory.HomStab.ShapiroZero


open GlobalTheory.HomStab.ShapiroZero in
theorem GlobalTheory.HomStab.isIso_map_ptMap_zero : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X)
    (hx : ∀ h, φ h • x = x), φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) →
    ∀ A : Rep k G, IsIso (groupHomology.map φ (ptMap φ x hx A) 0) := by
  intro k G H X _ _ _ _ φ x hx hrange htrans A
  choose s hs using htrans
  have stab : ∀ g : G, g • x = x → ∃ h : H, φ h = g := fun g hg => by
    have hmem : g ∈ φ.range := by
      rw [hrange]
      exact hg
    exact hmem
  have key : ∀ v : A.V, (groupHomology.map φ (ptMap φ x hx A) 0).hom
      ((groupHomology.H0π (Rep.res φ A)).hom v) =
      (groupHomology.H0π (permT X A)).hom (Finsupp.single x v) :=
    fun v => congrArg (fun f => ModuleCat.Hom.hom f v) (groupHomology.H0π_comp_map φ (ptMap φ x hx A))
  have resInv : ∀ (h : H) (b : A.V), (groupHomology.H0π (Rep.res φ A)).hom (A.ρ (φ h) b) =
      (groupHomology.H0π (Rep.res φ A)).hom b :=
    fun h b => GlobalTheory.HomStab.ShapiroZero.H0π_smul (Rep.res φ A) h b
  have permInv : ∀ (g : G) (w : (permT X A).V), (groupHomology.H0π (permT X A)).hom ((permT X A).ρ g w) =
      (groupHomology.H0π (permT X A)).hom w :=
    fun g w => GlobalTheory.HomStab.ShapiroZero.H0π_smul (permT X A) g w
  have piRes : Function.Surjective (groupHomology.H0π (Rep.res φ A)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have piPerm : Function.Surjective (groupHomology.H0π (permT X A)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have act : ∀ (g : G) (y : X) (a : A.V),
      (permT X A).ρ g (Finsupp.single y a) = Finsupp.single (g • y) (A.ρ g a) := by
    intro g y a
    simp [permT, permRep]
  let L : (X →₀ A.V) →ₗ[k] groupHomology (Rep.res φ A) 0 :=
    Finsupp.lsum k (fun y => (groupHomology.H0π (Rep.res φ A)).hom ∘ₗ (A.ρ (s y)⁻¹))
  have Lsingle : ∀ y a, L (Finsupp.single y a) = (groupHomology.H0π (Rep.res φ A)).hom (A.ρ (s y)⁻¹ a) := by
    intro y a
    simp [L]
  have hL : ∀ g : G, L ∘ₗ (permT X A).ρ g = L := by
    intro g
    ext y a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [act, Lsingle, Lsingle]
    have ht : ((s (g • y))⁻¹ * g * s y) • x = x := by
      rw [mul_smul, mul_smul, hs y, inv_smul_eq_iff, hs]
    obtain ⟨h, hh⟩ := stab _ ht
    have e : A.ρ (s (g • y))⁻¹ (A.ρ g a) = A.ρ (φ h) (A.ρ (s y)⁻¹ a) := by
      rw [hh, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, resInv]
  let N : groupHomology (permT X A) 0 →ₗ[k] groupHomology (Rep.res φ A) 0 :=
    Representation.Coinvariants.lift (permT X A).ρ L hL ∘ₗ (groupHomology.H0Iso (permT X A)).hom.hom
  have NM : ∀ v : A.V, N ((groupHomology.map φ (ptMap φ x hx A) 0).hom
      ((groupHomology.H0π (Rep.res φ A)).hom v)) = (groupHomology.H0π (Rep.res φ A)).hom v := by
    intro v
    rw [key]
    simp only [N, LinearMap.comp_apply]
    rw [GlobalTheory.HomStab.ShapiroZero.linkExactnessStability_hom_fact, Representation.Coinvariants.lift_mk, Lsingle]
    obtain ⟨h, hh⟩ := stab (s x)⁻¹ (by rw [inv_smul_eq_iff, hs])
    rw [← hh, resInv]
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (groupHomology.map φ (ptMap φ x hx A) 0).hom
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨v, rfl⟩ := piRes a
    obtain ⟨w, rfl⟩ := piRes b
    have hN := congrArg N hab
    rw [NM, NM] at hN
    exact hN
  · intro z
    obtain ⟨w, rfl⟩ := piPerm z
    induction w using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add u w hu hw =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hw
      exact ⟨a + b, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩
    | single y a =>
      refine ⟨(groupHomology.H0π (Rep.res φ A)).hom (A.ρ (s y)⁻¹ a), ?_⟩
      rw [key, ← permInv (s y), act, hs, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.shapiro_isIso_groupHomology_zero : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → ∀ A : Rep k G, IsIso (groupHomology.map φ (ptMap φ x hx A) 0) := by
  first
  | exact @GlobalTheory.HomStab.isIso_map_ptMap_zero
  | exact @GlobalTheory.HomStab.ShapiroZero.linkExactnessStability_hom_fact
  | exact @GlobalTheory.HomStab.ShapiroZero.H0π_smul
end
end

section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem chainsMap_id_add {k G : Type} [CommRing k] [Group G] {A B : Rep k G} (f g : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) (f + g) =
      groupHomology.chainsMap (MonoidHom.id G) f + groupHomology.chainsMap (MonoidHom.id G) g := by
  ext n : 1
  apply groupHomology.inhomogeneousChains.ext
  intro x
  ext a : 2
  simp only [groupHomology.chainsMap_f_single, HomologicalComplex.add_f_apply]
  simp [groupHomology.chainsMap_f_single]
  rw [← Finsupp.single_add]
  rfl

theorem hMap_add {k G : Type} [CommRing k] [Group G] {A B : Rep k G} (f g : A ⟶ B) (n : ℕ) :
    hMap (f + g) n = hMap f n + hMap g n := by
  unfold hMap groupHomology.map
  rw [chainsMap_id_add, HomologicalComplex.homologyMap_add]

noncomputable def hMapHom {k G : Type} [CommRing k] [Group G] (A B : Rep k G) (n : ℕ) :
    (A ⟶ B) →+ (groupHomology A n ⟶ groupHomology B n) :=
  AddMonoidHom.mk' (fun f => hMap f n) fun f g => hMap_add f g n

theorem hMap_additive : ∀ (k G : Type) [CommRing k] [Group G] (A B : Rep k G) (n : ℕ), (∀ f g : A ⟶ B, hMap (f + g) n = hMap f n + hMap g n) ∧ hMap (0 : A ⟶ B) n = 0 ∧ (∀ (m : ℤ) (f : A ⟶ B), hMap (m • f) n = m • hMap f n) ∧ ∀ (ι : Type) (T : Finset ι) (f : ι → (A ⟶ B)), hMap (∑ i ∈ T, f i) n = ∑ i ∈ T, hMap (f i) n := by
  intro k G _ _ A B n
  refine ⟨fun f g => hMap_add f g n, ?_, ?_, ?_⟩
  · exact map_zero (hMapHom A B n)
  · intro m f
    exact map_zsmul (hMapHom A B n) m f
  · intro ι T f
    exact map_sum (hMapHom A B n) f T

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.hMap_sum_zsmul_add : ∀ (k G : Type) [CommRing k] [Group G] (A B : Rep k G) (n : ℕ), (∀ f g : A ⟶ B, hMap (f + g) n = hMap f n + hMap g n) ∧ hMap (0 : A ⟶ B) n = 0 ∧ (∀ (m : ℤ) (f : A ⟶ B), hMap (m • f) n = m • hMap f n) ∧ ∀ (ι : Type) (T : Finset ι) (f : ι → (A ⟶ B)), hMap (∑ i ∈ T, f i) n = ∑ i ∈ T, hMap (f i) n := by
  first
  | exact @GlobalTheory.HomStab.hMap_additive
  | exact @GlobalTheory.HomStab.hMap_add
  | exact @GlobalTheory.HomStab.chainsMap_id_add
end
end
