module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Finset.Prod
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

section

namespace GlobalTheory.SymmProd

open scoped Matrix

theorem zpow_finsum_eq {U : Type} [CommGroup U] {ι : Type} (s : Finset ι) (x : U) (f : ι → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

theorem prod_collect {U : Type} [CommGroup U] {r : ℕ} (W M : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (e : ℤ) :
    ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^ (M i k * M j l)) ^ (e * W i j)
      = ∏ k, ∏ l, lam k l ^ ((e • (Mᵀ * W * M)) k l) := by
  have h : ∀ k l, (e • (Mᵀ * W * M)) k l = ∑ i, ∑ j, (M i k * M j l) * (e * W i j) := by
    intro k l
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [h, zpow_finsum_eq, ← Finset.prod_zpow, ← zpow_mul]
  calc ∏ i, ∏ j, ∏ k, ∏ l, lam k l ^ (M i k * M j l * (e * W i j))
      = ∏ i, ∏ k, ∏ j, ∏ l, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun i _ => Finset.prod_comm
    _ = ∏ k, ∏ i, ∏ j, ∏ l, lam k l ^ (M i k * M j l * (e * W i j)) := Finset.prod_comm
    _ = ∏ k, ∏ i, ∏ l, ∏ j, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i _ => Finset.prod_comm
    _ = ∏ k, ∏ l, ∏ i, ∏ j, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun k _ => Finset.prod_comm

theorem prod_antisymm {U : Type} [CommGroup U] {r : ℕ} (D : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (hlam : ∀ k l, lam k l = lam l k) :
    ∏ k, ∏ l, lam k l ^ ((D - Dᵀ) k l) = 1 := by
  simp only [Matrix.sub_apply, Matrix.transpose_apply, zpow_sub, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  rw [mul_inv_eq_one, Finset.prod_comm]
  exact Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun l _ => by rw [hlam]

theorem prod_four_maps_eq_one (U : Type) [CommGroup U] {r : ℕ} (W A : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (hlam : ∀ k l, lam k l = lam l k)
    (hW : W = (W + W.transpose) * A) :
    ∏ a : Fin 4, ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^
      ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k *
        (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a j l)) ^
      ((![1, -2, -1, 2] : Fin 4 → ℤ) a * W i j) = 1 := by
  simp only [prod_collect]
  rw [← prod_antisymm (Aᵀ * W) lam hlam, Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← zpow_finsum_eq, ← Matrix.sum_apply]
  refine congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => lam k l ^ M k l) ?_
  have h2 : Wᵀ * A = W - W * A := by
    rw [eq_sub_iff_add_eq, add_comm, ← add_mul]; exact hW.symm
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_zero, h2]
  noncomm_ring

end GlobalTheory.SymmProd
end

section

open scoped BigOperators
open Classical

namespace GlobalTheory

namespace GelfandTrick

variable {G : Type} [Group G]

def InDoubleCoset (J : Subgroup G) (a y : G) : Prop := ∃ k₁ ∈ J, ∃ k₂ ∈ J, y = k₁ * a * k₂

theorem InDoubleCoset.mul {J : Subgroup G} {a y z j₁ j₂ : G} (h : InDoubleCoset J a y)
    (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J) (hz : z = j₁ * y * j₂) : InDoubleCoset J a z := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h
  exact ⟨j₁ * k₁, J.mul_mem h₁ hk₁, k₂ * j₂, J.mul_mem hk₂ h₂, by rw [hz]; group⟩


open Classical in
theorem card_pairs_le (J : Subgroup G) (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hinv : ∀ a, τ (τ a) = a) (hdc : ∀ g : G, ∃ k₁ ∈ J, ∃ k₂ ∈ J, τ g = k₁ * g * k₂)
    (hJ : ∀ k ∈ J, τ k ∈ J) (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, InDoubleCoset J α γ)
    (hR' : ∀ x : G, InDoubleCoset J α x → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J)
    (hS : ∀ γ ∈ S, InDoubleCoset J β γ)
    (hS' : ∀ x : G, InDoubleCoset J β x → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ J) (c : G ⧸ J) :
    ((R ×ˢ S).filter (fun (p : G × G) => ((p.1 * p.2 : G) : G ⧸ J) = c)).card ≤
      ((S ×ˢ R).filter (fun (p : G × G) => ((p.1 * p.2 : G) : G ⧸ J) = c)).card := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have hone : τ 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hτinv : ∀ a, τ a⁻¹ = (τ a)⁻¹ := fun a => by
    have := hmul a a⁻¹
    rw [mul_inv_cancel, hone] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have hτdc : ∀ a y, InDoubleCoset J a y → InDoubleCoset J a (τ y) := fun a y h => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hdc y
    exact h.mul hk₁ hk₂ e
  obtain ⟨k₁, hk₁, k₂, hk₂, hx⟩ := hdc x
  refine Finset.card_le_card_of_forall_subsingleton
    (fun (p q : G × G) => q.1⁻¹ * (x * k₂ * (τ p.1)⁻¹) ∈ J) ?_ ?_
  · rintro ⟨γ, δ⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp
    obtain ⟨⟨hγ, hδ⟩, hj⟩ := hp
    have h1 : τ x = τ ((γ * δ)⁻¹ * x) * τ δ * τ γ := by
      rw [← hmul, ← hmul]; congr 1; group
    have h2 : InDoubleCoset J β (x * k₂ * (τ γ)⁻¹) := by
      refine (hτdc _ _ (hS δ hδ)).mul (J.mul_mem (J.inv_mem hk₁) (hJ _ hj)) J.one_mem ?_
      have : x * k₂ = k₁⁻¹ * τ x := by rw [hx]; group
      rw [this, h1]; group
    obtain ⟨δ', ⟨hδ', hj'⟩, -⟩ := hS' _ h2
    have h3 : InDoubleCoset J α (δ'⁻¹ * x) :=
      (hτdc _ _ (hR γ hγ)).mul hj' (J.inv_mem hk₂) (by group)
    obtain ⟨γ', ⟨hγ', hj''⟩, -⟩ := hR' _ h3
    refine ⟨(δ', γ'), ?_, hj'⟩
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq]
    refine ⟨⟨hδ', hγ'⟩, ?_⟩
    rwa [mul_inv_rev, mul_assoc]
  · rintro ⟨δ', γ'⟩ - ⟨γ₁, δ₁⟩ h₁ ⟨γ₂, δ₂⟩ h₂
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_product,
      QuotientGroup.eq, Finset.mem_coe] at h₁ h₂
    obtain ⟨⟨⟨hγ₁, hδ₁⟩, hj₁⟩, hr₁⟩ := h₁
    obtain ⟨⟨⟨hγ₂, hδ₂⟩, hj₂⟩, hr₂⟩ := h₂
    have h4 : γ₂⁻¹ * γ₁ ∈ J := by
      have := hJ _ (J.mul_mem (J.inv_mem hr₁) hr₂)
      have e : (δ'⁻¹ * (x * k₂ * (τ γ₁)⁻¹))⁻¹ * (δ'⁻¹ * (x * k₂ * (τ γ₂)⁻¹))
          = τ (γ₂⁻¹ * γ₁) := by rw [hmul, hτinv]; group
      rwa [e, hinv] at this
    have hγ : γ₁ = γ₂ :=
      (hR' γ₁ (hR γ₁ hγ₁)).unique ⟨hγ₁, by simpa using J.one_mem⟩ ⟨hγ₂, h4⟩
    subst hγ
    have h5 : InDoubleCoset J β (γ₁⁻¹ * x) := (hS δ₁ hδ₁).mul J.one_mem hj₁ (by group)
    have hδ : δ₁ = δ₂ :=
      (hS' _ h5).unique ⟨hδ₁, by rwa [mul_inv_rev, mul_assoc] at hj₁⟩
        ⟨hδ₂, by rwa [mul_inv_rev, mul_assoc] at hj₂⟩
    rw [hδ]

end GelfandTrick

end GlobalTheory
end

section

namespace GlobalTheory

theorem mapDomain_apply_eq_sum_filter {α β : Type} {M : Type*} [AddCommMonoid M] (f : α → β)
    (x : α →₀ M) (b : β) [DecidableEq β] :
    (Finsupp.mapDomain f x) b = ∑ a ∈ x.support.filter (fun a => f a = b), x a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

theorem mapDomain_neg_of_group {α β : Type} {M : Type*} [AddCommGroup M] (f : α → β)
    (x : α →₀ M) : Finsupp.mapDomain f (-x) = -Finsupp.mapDomain f x :=
  map_neg (Finsupp.mapDomain.addMonoidHom f) x

theorem mapDomain_corner_lift : ∀ (M : Type 1) [AddCommGroup M] (X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : Type)
    (c : X₂ → X₄) (d : X₃ → X₄) (u : Y₁ → Y₂) (v : Y₁ → Y₃) (c' : Y₂ → Y₄) (d' : Y₃ → Y₄)
    (r₂ : X₂ → Y₂) (r₃ : X₃ → Y₃) (r₄ : X₄ → Y₄) (G : Y₄ → Prop),
    (∀ x, c' (r₂ x) = r₄ (c x)) → (∀ y, d' (r₃ y) = r₄ (d y)) → (∀ x, c' (u x) = d' (v x)) →
    Function.Injective c' → (∀ x, G (c' x)) → (∀ y, G (d' y) → ∃ x, v x = y) →
    ∀ (a₂ : X₂ →₀ M) (a₃ : X₃ →₀ M), Finsupp.mapDomain c a₂ + Finsupp.mapDomain d a₃ = 0 →
    (∀ y ∈ a₃.support, ∀ y' ∈ a₃.support, d y = d y' → r₃ y = r₃ y' ∨ G (d' (r₃ y))) →
    ∃ a : Y₁ →₀ M, Finsupp.mapDomain u a = Finsupp.mapDomain r₂ a₂ ∧
      Finsupp.mapDomain v a = -Finsupp.mapDomain r₃ a₃ := by
  intro M _ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ c d u v c' d' r₂ r₃ r₄ G h1 h2 h3 hinj hG hlift a₂ a₃ hsum hpair
  classical
  have hdownF : Finsupp.mapDomain d a₃ = -Finsupp.mapDomain c a₂ :=
    eq_neg_of_add_eq_zero_right hsum
  have hdown : ∀ z, (Finsupp.mapDomain d a₃) z = -(Finsupp.mapDomain c a₂) z := fun z => by
    rw [hdownF, Finsupp.neg_apply]

  have hsupp : ∀ y'', ¬ G (d' y'') → (Finsupp.mapDomain r₃ a₃) y'' = 0 := by
    intro y'' hy''
    rw [mapDomain_apply_eq_sum_filter]
    rw [← Finset.sum_fiberwise_of_maps_to (t := (a₃.support.filter (fun y => r₃ y = y'')).image d)
      (g := d) (fun i hi => Finset.mem_image_of_mem d hi)]
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.mp hz
    have hyF' := Finset.mem_filter.mp hyF
    have hnot : ¬ G (r₄ (d y)) := by rw [← h2, hyF'.2]; exact hy''
    have hfib : ((a₃.support.filter (fun y => r₃ y = y'')).filter fun i => d i = d y) =
        a₃.support.filter (fun i => d i = d y) := by
      ext y'
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1', _⟩, h3'⟩; exact ⟨h1', h3'⟩
      · rintro ⟨h1', h3'⟩
        refine ⟨⟨h1', ?_⟩, h3'⟩
        rcases hpair y hyF'.1 y' h1' h3'.symm with h | h
        · rw [← h, hyF'.2]
        · rw [hyF'.2] at h; exact absurd h hy''
    have hc0 : (Finsupp.mapDomain c a₂) (d y) = 0 := by
      rw [mapDomain_apply_eq_sum_filter]
      refine Finset.sum_eq_zero fun x hx => ?_
      exfalso
      have hx' := (Finset.mem_filter.mp hx).2
      apply hnot
      rw [← hx', ← h1]; exact hG _
    have e := mapDomain_apply_eq_sum_filter d a₃ (d y)
    rw [hdown, hc0, neg_zero] at e
    rw [hfib]
    convert e.symm

  let S : Set Y₃ := {y | G (d' y)}
  have hS : ↑(Finsupp.mapDomain r₃ a₃).support ⊆ Set.range (Subtype.val : S → Y₃) := by
    intro y hy
    by_contra hn
    apply Finsupp.mem_support_iff.mp hy
    apply hsupp
    intro hG'
    exact hn ⟨⟨y, hG'⟩, rfl⟩
  let lift : S → Y₁ := fun s => Classical.choose (hlift s.1 s.2)
  have hlift' : v ∘ lift = Subtype.val := funext fun s => Classical.choose_spec (hlift s.1 s.2)
  let a : Y₁ →₀ M := -Finsupp.mapDomain lift
    (Finsupp.comapDomain Subtype.val (Finsupp.mapDomain r₃ a₃) Subtype.val_injective.injOn)
  have hva : Finsupp.mapDomain v a = -Finsupp.mapDomain r₃ a₃ := by
    simp only [a, mapDomain_neg_of_group, ← Finsupp.mapDomain_comp, hlift']
    rw [Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective _ hS]

  refine ⟨a, Finsupp.mapDomain_injective hinj ?_, hva⟩
  have e1 : Finsupp.mapDomain c' (Finsupp.mapDomain u a) =
      Finsupp.mapDomain d' (Finsupp.mapDomain v a) := by
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show c' ∘ u = d' ∘ v from funext h3]
  have e2 : Finsupp.mapDomain d' (Finsupp.mapDomain r₃ a₃) =
      Finsupp.mapDomain r₄ (Finsupp.mapDomain d a₃) := by
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show d' ∘ r₃ = r₄ ∘ d from funext h2]
  have e3 : Finsupp.mapDomain c' (Finsupp.mapDomain r₂ a₂) =
      Finsupp.mapDomain r₄ (Finsupp.mapDomain c a₂) := by
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show c' ∘ r₂ = r₄ ∘ c from funext h1]
  rw [e1, hva, mapDomain_neg_of_group, e2, hdownF, mapDomain_neg_of_group, neg_neg, e3]

end GlobalTheory
end

section

namespace GlobalTheory

open Matrix

theorem exists_basis_of_blockLowerTriangular_inv (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]
    (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M)
    (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O)
    (h1 : P * P' = 1) (h2 : P' * P = 1) (hz : ∀ i j, P (Sum.inl i) (Sum.inr j) = 0) :
    ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by
  have hAA : P.toBlocks₁₁ * P'.toBlocks₁₁ = 1 := by
    ext i i'
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inl i')
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁] using this
  have hA'A : P'.toBlocks₁₁ * P.toBlocks₁₁ = 1 := mul_eq_one_comm.mp hAA
  have hAB : P.toBlocks₁₁ * P'.toBlocks₁₂ = 0 := by
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂] using this
  have hB : P'.toBlocks₁₂ = 0 := by
    calc P'.toBlocks₁₂ = (P'.toBlocks₁₁ * P.toBlocks₁₁) * P'.toBlocks₁₂ := by rw [hA'A, Matrix.one_mul]
      _ = P'.toBlocks₁₁ * (P.toBlocks₁₁ * P'.toBlocks₁₂) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hAB, Matrix.mul_zero]
  have hb : ∀ a j, P' (Sum.inl a) (Sum.inr j) = 0 := fun a j => by
    simpa [Matrix.toBlocks₁₂] using congrFun (congrFun hB a) j
  have hDD : P.toBlocks₂₂ * P'.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h1 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hb, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  have hD'D : P'.toBlocks₂₂ * P.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h2 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  set D := P.toBlocks₂₂ with hDdef
  set D' := P'.toBlocks₂₂
  let L : (Fin k → O) ≃ₗ[O] (Fin k' → O) :=
    LinearEquiv.ofLinear (Matrix.toLin' Dᵀ) (Matrix.toLin' D'ᵀ)
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hD'D, Matrix.transpose_one, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hDD, Matrix.transpose_one, Matrix.toLin'_one])
  refine ⟨Module.Basis.ofEquivFun (lbs.equivFun.trans L.symm), fun j => ?_⟩
  rw [Module.Basis.coe_ofEquivFun]
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun j' _ => ?_
  congr 1
  simp [L, Matrix.mulVec, dotProduct, Pi.single_apply, hDdef, Matrix.toBlocks₂₂]

end GlobalTheory
end

section

namespace GlobalTheory.SquareDistanceExpansion

open Matrix

theorem expand {R : Type} [CommRing R] {n : ℕ} (X Y X' Y' : Matrix (Fin n) (Fin n) R) :
    (1 + X + Y) * (1 + X' + Y') = 1 + X + Y + X' + Y' + X * X' + X * Y' + Y * X' + Y * Y' := by
  noncomm_ring

theorem sq_id {R : Type} [CommRing R] {d : ℕ} (H H' : Matrix (Fin d) (Fin d) R) :
    H * H' - 1 = (H - 1) + (H' - 1) + (H - 1) * (H' - 1) := by
  noncomm_ring

theorem prod_eq {R : Type} [CommRing R] {n d : ℕ} (a c : Matrix (Fin n) (Fin d) R)
    (α γ : Matrix (Fin d) (Fin n) R) (M N : Matrix (Fin d) (Fin d) R) :
    a * M * α * (c * N * γ) = a * M * (α * c) * N * γ := by
  simp only [Matrix.mul_assoc]

theorem dist {R : Type} [CommRing R] {n d : ℕ} (a : Matrix (Fin n) (Fin d) R)
    (α : Matrix (Fin d) (Fin n) R) (A B : Matrix (Fin d) (Fin d) R) :
    a * (A + B + A * B) * α = a * A * α + a * B * α + a * A * B * α := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem main : (let d1 : {R : Type} → [CommRing R] → {n d : ℕ} → Matrix (Fin n) (Fin d) R → Matrix (Fin n) (Fin d) R → Matrix (Fin d) (Fin n) R → Matrix (Fin d) (Fin n) R → Matrix (Fin d) (Fin d) R → Matrix (Fin d) (Fin d) R → Matrix (Fin n) (Fin n) R := @(fun {R : Type} [CommRing R] {n d : ℕ} (a b : Matrix (Fin n) (Fin d) R) (α β : Matrix (Fin d) (Fin n) R) (H K : Matrix (Fin d) (Fin d) R) ↦ (1 : Matrix (Fin n) (Fin n) R) + a * (H - (1 : Matrix (Fin d) (Fin d) R)) * α + b * (K - (1 : Matrix (Fin d) (Fin d) R)) * β); ∀ {R : Type} [inst : CommRing R] {n d : ℕ} {a b : Matrix (Fin n) (Fin d) R} {α β : Matrix (Fin d) (Fin n) R}, α * a = (1 : Matrix (Fin d) (Fin d) R) → β * b = (1 : Matrix (Fin d) (Fin d) R) → α * b = (0 : Matrix (Fin d) (Fin d) R) → β * a = (0 : Matrix (Fin d) (Fin d) R) → ∀ (H K H' K' : Matrix (Fin d) (Fin d) R), d1 a b α β H K * d1 a b α β H' K' = d1 a b α β (H * H') (K * K')) := by
  dsimp only
  intro R _ n d a b α β hαa hβb hαb hβa H K H' K'
  have e1 := prod_eq a a α α (H - 1) (H' - 1)
  have e2 := prod_eq a b α β (H - 1) (K' - 1)
  have e3 := prod_eq b a β α (K - 1) (H' - 1)
  have e4 := prod_eq b b β β (K - 1) (K' - 1)
  rw [hαa, Matrix.mul_one] at e1
  rw [hαb, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul] at e2
  rw [hβa, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul] at e3
  rw [hβb, Matrix.mul_one] at e4
  rw [expand, e1, e2, e3, e4, sq_id H H', sq_id K K', dist a α (H - 1) (H' - 1),
    dist b β (K - 1) (K' - 1)]
  abel

end GlobalTheory.SquareDistanceExpansion
end

section

open Matrix

namespace GlobalTheory

theorem eigen_decomp_base_change :
  ∀ (K C : Type) [CommRing K] [CommRing C] (n a : ℕ) (ω : K) (tr nm : ℤ), ω ^ 2 - (tr : K) * ω + (nm : K) = 0 → ∀ (f : K →+* Matrix (Fin n) (Fin n) C) (ρ : C), ρ ^ 2 - (tr : C) * ρ + (nm : C) = 0 → IsUnit (2 * ρ - (tr : C)) → ∀ (t : Fin a → (K →+* C)), (∀ i, t i ω = ρ) → (∀ v : Fin n → C, Matrix.mulVec (f ω) v = ρ • v → ∃ w : Fin a → Fin n → C, (∀ i (c : K), Matrix.mulVec (f c) (w i) = t i c • w i) ∧ v = ∑ i, w i) → ∀ (R' : Type) [CommRing R'] (g : C →+* R') (v : Fin n → R'), Matrix.mulVec ((f ω).map g) v = g ρ • v → ∃ w : Fin a → Fin n → R', (∀ i (c : K), Matrix.mulVec ((f c).map g) (w i) = g (t i c) • w i) ∧ v = ∑ i, w i := by
  intro K C _ _ n a ω tr nm hω f ρ hρ hu t ht H R' _ g v hv
  obtain ⟨uinv, huinv⟩ : ∃ uinv : C, uinv * (2 * ρ - (tr : C)) = 1 := by
    obtain ⟨u, hu'⟩ := hu
    exact ⟨↑u⁻¹, by rw [← hu']; simp⟩
  set Ω := f ω with hΩdef

  have hΩΩ : Ω * Ω = (tr : Matrix (Fin n) (Fin n) C) * Ω - (nm : Matrix (Fin n) (Fin n) C) := by
    have h1 : ω * ω = (tr : K) * ω - (nm : K) := by linear_combination hω
    have h2 := congrArg f h1
    simpa [map_mul, map_sub, map_intCast] using h2
  have key : ∀ x : Fin n → C, Ω *ᵥ (Ω *ᵥ x) = (tr : C) • (Ω *ᵥ x) - (nm : C) • x := by
    intro x
    rw [mulVec_mulVec, hΩΩ, sub_mulVec, ← mulVec_mulVec, intCast_mulVec, intCast_mulVec]
  have eig : ∀ x : Fin n → C, Ω *ᵥ (Ω *ᵥ x - ((tr : C) - ρ) • x) = ρ • (Ω *ᵥ x - ((tr : C) - ρ) • x) := by
    intro x
    rw [mulVec_sub, mulVec_smul, key]
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(x k)) * hρ
  let e : Fin n → Fin n → C := fun j => uinv • (Ω *ᵥ Pi.single j 1 - ((tr : C) - ρ) • Pi.single j 1)
  have he : ∀ j, Ω *ᵥ e j = ρ • e j := by
    intro j
    simp only [e, mulVec_smul, eig]
    rw [smul_comm]
  choose W hW hWsum using fun j => H (e j) (he j)

  have hmap : ∀ (M : Matrix (Fin n) (Fin n) C) (x : Fin n → C), M.map g *ᵥ (g ∘ x) = g ∘ (M *ᵥ x) := by
    intro M x
    funext k
    simp only [Function.comp_apply]
    rw [RingHom.map_mulVec]
  have hvsum : v = ∑ j, v j • (g ∘ e j) := by
    funext k
    have hv' := congrFun hv k
    simp only [mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hv'
    simp only [e, Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.sub_apply,
      mulVec_single_one, col_apply, Pi.single_apply, map_mul, map_sub, mul_ite, mul_one, mul_zero,
      map_zero]
    have hterm : ∀ x, v x * (g uinv * (g (Ω k x) - g (if k = x then (tr : C) - ρ else 0))) =
        g uinv * (g (Ω k x) * v x) - (if k = x then g uinv * g ((tr : C) - ρ) * v k else 0) := by
      intro x
      split_ifs with h
      · subst h; ring
      · simp only [map_zero, sub_zero]; ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_sub_distrib, ← Finset.mul_sum, hv',
      Finset.sum_ite_eq]
    have hg := congrArg g huinv
    simp only [map_mul, map_sub, map_intCast, map_one, map_ofNat] at hg ⊢
    simp only [Finset.mem_univ, if_true]
    linear_combination (-(v k)) * hg
  refine ⟨fun i => ∑ j, v j • (g ∘ W j i), ?_, ?_⟩
  · intro i c
    rw [mulVec_sum]
    simp only [mulVec_smul, hmap, hW]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
    congr 1
    funext k
    simp [Function.comp_apply]
  · conv_lhs => rw [hvsum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.smul_sum]
    congr 1
    rw [hWsum j]
    funext k

    simp [Finset.sum_apply, map_sum]

end GlobalTheory
end

section

namespace GlobalTheory.SequenceFromIteration

theorem exists_seq_of_step {A : Type} (P : ℕ → A → Prop) (Q : ℕ → A → A → Prop) (a₀ : A)
    (h₀ : P 0 a₀) (hstep : ∀ (n : ℕ) (a : A), P n a → ∃ b : A, P (n + 1) b ∧ Q n a b) :
    ∃ F : ℕ → A, F 0 = a₀ ∧ ∀ n : ℕ, P n (F n) ∧ Q n (F n) (F (n + 1)) := by
  choose g hgP hgQ using hstep
  let G : (n : ℕ) → {a : A // P n a} := fun n =>
    Nat.rec (motive := fun n => {a : A // P n a}) ⟨a₀, h₀⟩
      (fun k x => ⟨g k x.1 x.2, hgP k x.1 x.2⟩) n
  exact ⟨fun n => (G n).1, rfl, fun n => ⟨(G n).2, hgQ n (G n).1 (G n).2⟩⟩

end GlobalTheory.SequenceFromIteration
end
