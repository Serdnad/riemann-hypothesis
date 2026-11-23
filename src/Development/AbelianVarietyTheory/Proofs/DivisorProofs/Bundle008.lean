module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

open Filter
open scoped Classical

namespace GlobalTheory

theorem relIndex_inf_conj_eq_finprod_of_restricted_product
    (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (K T C : Subgroup G) (KH TH CH : ∀ i, Subgroup (H i)) (g : G)
    (hglue : ∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i)
    (hT : ∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i)
    (hC : ∀ x, x ∈ C ↔ x ∈ T ∧ ∀ i, p i x ∈ CH i)
    (hCT : ∀ i, CH i ≤ TH i)
    (_hloc : ∀ i, TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom ≤ CH i ∧
      (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) ≠ 0)
    (hCK : ∀ᶠ i in cofinite, CH i ≤ KH i) :
    (T ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex C =
      ∏ᶠ i, (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) := by
  have hfin : {i | ¬ (p i g ∈ KH i ∧ CH i ≤ KH i)}.Finite :=
    Filter.eventually_cofinite.1 ((hcof g).and hCK)
  set S : Finset ι := hfin.toFinset with hS
  have hSn : ∀ i, i ∉ S → p i g ∈ KH i ∧ CH i ≤ KH i := by
    intro i hi
    by_contra h
    exact hi (hfin.mem_toFinset.2 h)
  have hmem : ∀ i (y : H i), y ∈ (KH i).map (MulAut.conj (p i g)).toMonoidHom ↔
      (p i g)⁻¹ * y * p i g ∈ KH i := by
    intro i y
    rw [Subgroup.mem_map_equiv]
    simp
  have hmemG : ∀ x : G, x ∈ K.map (MulAut.conj g).toMonoidHom ↔
      ∀ i, (p i g)⁻¹ * p i x * p i g ∈ KH i := by
    intro x
    rw [Subgroup.mem_map_equiv, hK]
    simp
  have hle : ∀ i, i ∉ S → CH i ≤ TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom := by
    intro i hi y hy
    obtain ⟨h1, h2⟩ := hSn i hi
    exact ⟨hCT i hy, (hmem i y).2 (mul_mem (mul_mem (inv_mem h1) (h2 hy)) h1)⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  swap
  · intro i hi
    by_contra h
    exact hi (Subgroup.relIndex_eq_one.2 (hle i h))
  let φ : C →* (∀ i : S, CH i) :=
    { toFun := fun x i => ⟨p i x, ((hC x).1 x.2).2 i⟩
      map_one' := by ext i; simp
      map_mul' := by intro x y; ext i; simp }
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hglue (fun i => if h : i ∈ S then (y ⟨i, h⟩ : H i) else 1) (by
      refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
      intro i hi
      by_contra h
      apply hi
      have h' : i ∉ S := h
      simp [h'])
    have hxC : ∀ i, p i x ∈ CH i := by
      intro i
      rw [hx]
      split_ifs with h
      · exact (y ⟨i, h⟩).2
      · exact one_mem _
    refine ⟨⟨x, (hC x).2 ⟨(hT x).2 fun i => hCT i (hxC i), hxC⟩⟩, ?_⟩
    funext i
    apply Subtype.ext
    show p i x = _
    rw [hx]
    simp
  have hcomap : (T ⊓ K.map (MulAut.conj g).toMonoidHom).subgroupOf C =
      (Subgroup.pi Set.univ (fun i : S =>
        (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).subgroupOf (CH i))).comap φ := by
    ext x
    have hx := (hC x).1 x.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Subgroup.mem_inf, hmemG]
    constructor
    · rintro ⟨h1, h2⟩ i _
      exact ⟨(hT x).1 h1 i, (hmem i _).2 (h2 i)⟩
    · intro h
      refine ⟨hx.1, fun i => ?_⟩
      by_cases hi : i ∈ S
      · exact (hmem i _).1 (h ⟨i, hi⟩ trivial).2
      · exact (hmem i _).1 (hle i hi (hx.2 i)).2
  have hpi : ∀ L : ∀ i : S, Subgroup (CH i),
      (Subgroup.pi Set.univ L).index = ∏ i, (L i).index := by
    intro L
    simp_rw [Subgroup.index, ← Nat.card_pi]
    refine Nat.card_congr
      ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
    rw [QuotientGroup.leftRel_pi]
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hφ, hpi,
    ← Finset.prod_coe_sort S]
  rfl

end GlobalTheory
end

section

namespace GlobalTheory.FourTermSumSwap

theorem sum_four_swap : ∀ {R α β : Type} [inst : AddCommMonoid R] [inst_1 : Fintype α] [inst_2 : Fintype β]
    (f : α → β → α → β → R),
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by
  intro R α β _ _ _ f
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ a : α, ∑ c : α, ∑ b : β, ∑ e : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ b : β, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ e : β, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

end GlobalTheory.FourTermSumSwap
end

section

namespace GlobalTheory.FourTermSumReorder

theorem sum_four_reorder {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ b : β, ∑ a : α, ∑ c : α, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ p : β × α, ∑ q : α × β, f p.2 p.1 q.1 q.2 := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ q : α × β, ∑ p : β × α, f p.2 p.1 q.1 q.2 := Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
        simp only [Fintype.sum_prod_type]

end GlobalTheory.FourTermSumReorder
end

section

namespace GlobalTheory.MembershipOfSum

theorem mem_of_sum_mem {k : Type} [Field k] {H : Type 1} [AddCommGroup H] [Module k H]
    {O : Type} [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H)
    (hF : ∀ (c : O), ∀ x ∈ F, ρ c x ∈ F) {a : ℕ} (χ : Fin a → O → k)
    (hχ : ∀ (i j : Fin a), i ≠ j → ∃ (c : O), χ i c ≠ χ j c) (S : Finset (Fin a))
    (u : Fin a → H) (hu : ∀ i ∈ S, ∀ (c : O), ρ c (u i) - χ i c • u i ∈ F)
    (hs : ∑ i ∈ S, u i ∈ F) : ∀ i ∈ S, u i ∈ F := by
  induction S using Finset.induction_on generalizing u with
  | empty => intro i hi; simp at hi
  | insert j S hj ih =>
    have key : ∀ i ∈ S, u i ∈ F := by
      intro i hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      obtain ⟨c, hc⟩ := hχ i j hij
      have h1 : ∑ l ∈ insert j S, (χ l c - χ j c) • u l ∈ F := by
        have e : ∑ l ∈ insert j S, (χ l c - χ j c) • u l =
            ρ c (∑ l ∈ insert j S, u l) - χ j c • ∑ l ∈ insert j S, u l
              - ∑ l ∈ insert j S, (ρ c (u l) - χ l c • u l) := by

          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [sub_smul]; abel
        rw [e]
        exact F.sub_mem (F.sub_mem (hF c _ hs) (F.smul_mem _ hs))
          (F.sum_mem fun l hl => hu l hl c)
      rw [Finset.sum_insert hj, sub_self, zero_smul, zero_add] at h1
      have h2 := ih (fun l => (χ l c - χ j c) • u l) (by
        intro l hl d
        have := F.smul_mem (χ l c - χ j c) (hu l (Finset.mem_insert_of_mem hl) d)
        rw [smul_sub, smul_comm] at this
        rw [map_smul]
        exact this) h1 i hi
      exact (F.smul_mem_iff (sub_ne_zero.mpr hc)).mp h2
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [Finset.sum_insert hj] at hs
      have := F.sub_mem hs (F.sum_mem key)
      simpa using this
    · exact key i hi

end GlobalTheory.MembershipOfSum
end

section

namespace GlobalTheory.ProductZpowAdd

theorem prod_zpow_add {F : Type} [inst : Field F] {d : ℕ} (x : Fin (d + 1) → F)
    (hx : ∀ i : Fin (d + 1), x i ≠ 0) (m n : Fin (d + 1) → ℤ) :
    ∏ j : Fin (d + 1), x j ^ (m j + n j)
      = (∏ j : Fin (d + 1), x j ^ m j) * ∏ j : Fin (d + 1), x j ^ n j := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (hx j) _ _

end GlobalTheory.ProductZpowAdd
end

section

namespace GlobalTheory

theorem sum_transversal_left_translate_invariant :
    ∀ {G X : Type} [Group G] [AddCommMonoid X] (H K : Subgroup G) (R : Finset G) (f : G → X),
      (∀ r ∈ R, r ∈ H) → (∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K) →
      (∀ r ∈ H, ∀ c ∈ K, f (r * c) = f r) → ∀ k ∈ H, ∑ r ∈ R, f (k * r) = ∑ r ∈ R, f r := by
  intro G X _ _ H K R f hR hU hf k hk
  have hkH : ∀ a ∈ R, k * a ∈ H := fun a ha => H.mul_mem hk (hR a ha)
  refine Finset.sum_bij (fun a ha => Classical.choose (hU (k * a) (hkH a ha)).exists)
    (fun a ha => (Classical.choose_spec (hU (k * a) (hkH a ha)).exists).1) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ heq
    have h1 := (Classical.choose_spec (hU (k * a₁) (hkH a₁ ha₁)).exists).2
    have h2 := (Classical.choose_spec (hU (k * a₂) (hkH a₂ ha₂)).exists).2
    rw [heq] at h1
    set r' := Classical.choose (hU (k * a₂) (hkH a₂ ha₂)).exists
    have hm : a₁⁻¹ * a₂ ∈ K := by
      have := K.mul_mem (K.inv_mem h1) h2
      simpa [mul_assoc] using this
    have hu := (hU a₂ (hR a₂ ha₂)).unique (y₁ := a₁) (y₂ := a₂) ⟨ha₁, hm⟩ ⟨ha₂, by simpa using K.one_mem⟩
    exact hu
  · intro b hb
    have hb' : k⁻¹ * b ∈ H := H.mul_mem (H.inv_mem hk) (hR b hb)
    obtain ⟨a, ⟨ha, haK⟩, -⟩ := hU (k⁻¹ * b) hb'
    refine ⟨a, ha, ?_⟩
    have hs := Classical.choose_spec (hU (k * a) (hkH a ha)).exists
    have hbK : b⁻¹ * (k * a) ∈ K := by
      have := K.inv_mem haK
      simpa [mul_assoc] using this
    exact (hU (k * a) (hkH a ha)).unique hs ⟨hb, hbK⟩
  · intro a ha
    have hs := Classical.choose_spec (hU (k * a) (hkH a ha)).exists
    set r' := Classical.choose (hU (k * a) (hkH a ha)).exists
    have := hf r' (hR r' hs.1) (r'⁻¹ * (k * a)) hs.2
    rw [mul_inv_cancel_left] at this
    exact this

end GlobalTheory
end

section

namespace GlobalTheory
namespace CosetAvg

open MulAction

theorem orbit_sum {H X M : Type*} [Group H] [Fintype H] [MulAction H X] [AddCommGroup M]
    [Module ℂ M] (y : X) [Fintype (orbit H y)] (F : X → M) :
    (Fintype.card (orbit H y) : ℂ) • ∑ h : H, F (h • y) =
      (Fintype.card H : ℂ) • ∑ z : orbit H y, F z := by
  have h1 : ∀ z : orbit H y, ∑ h : H, F (h • (z : X)) = ∑ h : H, F (h • y) := by
    rintro ⟨z, g, rfl⟩
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => by simp [mul_smul])
  have h2 : ∀ h : H, ∑ z : orbit H y, F (h • (z : X)) = ∑ z : orbit H y, F z := by
    intro h
    exact Fintype.sum_equiv (MulAction.toPerm h) _ _ (fun z => rfl)
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.card_univ,
    ← Finset.sum_const, ← Finset.sum_const]
  calc ∑ _z : orbit H y, ∑ h : H, F (h • y) = ∑ z : orbit H y, ∑ h : H, F (h • (z : X)) :=
        Finset.sum_congr rfl (fun z _ => (h1 z).symm)
    _ = ∑ h : H, ∑ z : orbit H y, F (h • (z : X)) := Finset.sum_comm
    _ = ∑ _h : H, ∑ z : orbit H y, F z := Finset.sum_congr rfl (fun h _ => h2 h)

theorem avg_of_invariant {H X M ι : Type*} [Group H] [Fintype H] [MulAction H X]
    [AddCommGroup M] [Module ℂ M] (s : Finset ι) (y : ι → X) [∀ i, Fintype (orbit H (y i))]
    (F : ι → X → M) (hinv : ∀ h : H, ∑ i ∈ s, F i (h • y i) = ∑ i ∈ s, F i (y i)) :
    ∑ i ∈ s, F i (y i) =
      ∑ i ∈ s, ((Fintype.card (orbit H (y i)) : ℂ)⁻¹ • ∑ z : orbit H (y i), F i z) := by
  have hH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hO : ∀ i, (Fintype.card (orbit H (y i)) : ℂ) ≠ 0 := fun i => by
    haveI : Nonempty (orbit H (y i)) := ⟨⟨y i, mem_orbit_self _⟩⟩
    exact_mod_cast Fintype.card_ne_zero
  have key : ∀ i, ∑ h : H, F i (h • y i) = (Fintype.card H : ℂ) •
      ((Fintype.card (orbit H (y i)) : ℂ)⁻¹ • ∑ z : orbit H (y i), F i z) := by
    intro i
    rw [smul_comm (Fintype.card H : ℂ), ← orbit_sum, smul_smul, inv_mul_cancel₀ (hO i), one_smul]
  apply smul_right_injective M hH
  simp only
  calc (Fintype.card H : ℂ) • ∑ i ∈ s, F i (y i) = ∑ _h : H, ∑ i ∈ s, F i (y i) := by
        rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    _ = ∑ h : H, ∑ i ∈ s, F i (h • y i) := Finset.sum_congr rfl (fun h _ => (hinv h).symm)
    _ = ∑ i ∈ s, ∑ h : H, F i (h • y i) := Finset.sum_comm
    _ = _ := by rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _ => key i)

end CosetAvg
end GlobalTheory

namespace GlobalTheory
namespace CosetAvg

open MulAction

theorem sum_translates_eq_avg : ∀ {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : G →* Module.End ℂ M) (K : Subgroup G) {ι : Type} (s : Finset ι) (a : ι → G) (R : ι → Finset G) (w : ι → M), (∀ i ∈ s, (∀ γ ∈ R i, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * a i * k₂) ∧ ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a i * k₂) → ∃! γ, γ ∈ R i ∧ γ⁻¹ * x ∈ K) → (∀ i ∈ s, ∀ k ∈ K, ρ k (w i) = w i) → (∀ k ∈ K, ρ k (∑ i ∈ s, ρ (a i) (w i)) = ∑ i ∈ s, ρ (a i) (w i)) → ∑ i ∈ s, ρ (a i) (w i) = ∑ i ∈ s, ((R i).card : ℂ)⁻¹ • ∑ γ ∈ R i, ρ γ (w i) := by
  intro G M _ _ _ ρ K ι s a R w hR hw hm
  classical
  have hsm : ∀ (k : K) (g : G), k • ((g : G) : G ⧸ K) = ((k * g : G) : G ⧸ K) := fun k g => rfl
  let Y : SubMulAction K (G ⧸ K) :=
    { carrier := {q | ∃ i ∈ s, ∃ k : K, q = k • ((a i : G) : G ⧸ K)}
      smul_mem' := by
        rintro c q ⟨i, hi, k, rfl⟩
        exact ⟨i, hi, c * k, (mul_smul c k _).symm⟩ }
  have hYsub : (Y : Set (G ⧸ K)) ⊆
      ((s.biUnion fun i => (R i).image (QuotientGroup.mk : G → G ⧸ K) : Finset (G ⧸ K)) :
        Set (G ⧸ K)) := by
    rintro q ⟨i, hi, k, rfl⟩
    obtain ⟨γ, ⟨hγ, hγk⟩, -⟩ := (hR i hi).2 (k * a i) ⟨k, k.2, 1, K.one_mem, by simp⟩
    refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨γ, hγ, ?_⟩⟩)
    rw [hsm, QuotientGroup.eq]
    exact hγk
  haveI : Finite Y := (Set.Finite.subset (Finset.finite_toSet _) hYsub).to_subtype
  letI : Fintype Y := Fintype.ofFinite Y
  let φ := MulAction.toPermHom K Y
  let H := φ.range
  letI : Fintype H := Fintype.ofFinite H
  have hy : ∀ i ∈ s, ((a i : G) : G ⧸ K) ∈ Y := fun i hi => ⟨i, hi, 1, by simp⟩
  let y : s → Y := fun i => ⟨((a i : G) : G ⧸ K), hy i i.2⟩
  letI : ∀ i, Fintype (orbit H (y i)) := fun i => Fintype.ofFinite _
  let F : s → Y → M := fun i q => ρ (q : G ⧸ K).out (w i)
  have hF : ∀ (i : s) (q : Y) (g : G), (q : G ⧸ K) = (g : G ⧸ K) → F i q = ρ g (w i) := by
    intro i q g hq
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [F, hq, hk, map_mul, Module.End.mul_apply, hw i i.2 k k.2]
  have hval : ∀ (k : K) (i : s),
      ((((⟨φ k, k, rfl⟩ : H) • y i : Y)) : G ⧸ K) = ((k * a i : G) : G ⧸ K) := fun k i => rfl
  have hinv : ∀ h : H, ∑ i ∈ Finset.univ, F i (h • y i) = ∑ i ∈ Finset.univ, F i (y i) := by
    rintro ⟨_, k, rfl⟩
    rw [Finset.sum_congr rfl (fun i _ => hF i _ _ (hval k i)),
      Finset.sum_congr rfl (fun i _ => hF i (y i) (a i) rfl)]
    simp only [map_mul, Module.End.mul_apply]

    rw [← map_sum, Finset.sum_coe_sort s (fun i => ρ (a i) (w i)), hm k k.2]
  have hmain := avg_of_invariant (H := H) Finset.univ y F hinv

  have horb : ∀ i : s, ∃ e : (R i) ≃ orbit H (y i),
      ∀ γ : R i, ((e γ : Y) : G ⧸ K) = ((γ : G) : G ⧸ K) := by
    intro i
    have hmemY : ∀ γ ∈ R i, ((γ : G) : G ⧸ K) ∈ Y := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (hR i i.2).1 γ hγ
      exact ⟨i, i.2, ⟨k₁, hk₁⟩, by rw [hsm, QuotientGroup.mk_mul_of_mem _ hk₂]⟩
    have hmemO : ∀ (γ : G) (hγ : γ ∈ R i), (⟨(γ : G ⧸ K), hmemY γ hγ⟩ : Y) ∈ orbit H (y i) := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, hγe⟩ := (hR i i.2).1 γ hγ
      refine ⟨⟨φ ⟨k₁, hk₁⟩, ⟨k₁, hk₁⟩, rfl⟩, Subtype.ext ?_⟩
      exact (hval _ _).trans ((QuotientGroup.mk_mul_of_mem _ hk₂).symm.trans (congrArg _ hγe.symm))
    let f : R i → orbit H (y i) := fun γ => ⟨⟨(γ : G ⧸ K), hmemY γ γ.2⟩, hmemO γ γ.2⟩
    have hbij : Function.Bijective f := by
      constructor
      · rintro ⟨γ, hγ⟩ ⟨γ', hγ'⟩ he
        have he' : ((γ : G) : G ⧸ K) = ((γ' : G) : G ⧸ K) :=
          congrArg (fun z : orbit H (y i) => ((z : Y) : G ⧸ K)) he
        rw [QuotientGroup.eq] at he'
        have hu := (hR i i.2).2 γ' ((hR i i.2).1 γ' hγ')
        exact Subtype.ext (hu.unique ⟨hγ, he'⟩ ⟨hγ', by simp⟩)
      · rintro ⟨z, ⟨⟨_, k, rfl⟩, hz⟩⟩
        obtain ⟨γ, ⟨hγ, hγk⟩, -⟩ := (hR i i.2).2 (k * a i) ⟨k, k.2, 1, K.one_mem, by simp⟩
        refine ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
        exact (QuotientGroup.eq.mpr hγk).trans ((hval k i).symm.trans (congrArg Subtype.val hz))
    exact ⟨Equiv.ofBijective f hbij, fun γ => rfl⟩
  rw [← Finset.sum_coe_sort s, ← Finset.sum_coe_sort s, Finset.sum_congr rfl
    (fun i _ => (hF i (y i) (a i) rfl).symm), hmain]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  obtain ⟨e, he⟩ := horb i
  rw [← Fintype.card_congr e, Fintype.card_coe]
  congr 1
  rw [← Finset.sum_coe_sort (R i)]
  exact (Fintype.sum_equiv e _ _ (fun γ => (hF i _ _ (he γ)).symm)).symm

end CosetAvg
end GlobalTheory
end

section

namespace GlobalTheory

theorem coeff_mem_of_poly_values_mem : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (N : ℕ) (c : ℕ → V), (∀ u : ℂ, ∑ k ∈ Finset.range N, u ^ k • c k ∈ S) → ∀ k < N, c k ∈ S := by
  intro V _ _ S N c h k hk
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  set p : Polynomial ℂ := ∑ j ∈ Finset.range N,
    Polynomial.C (f (Submodule.Quotient.mk (c j))) * Polynomial.X ^ j with hpdef
  have hp : p = 0 := by
    apply Polynomial.funext
    intro u
    have h1 : S.mkQ (∑ k ∈ Finset.range N, u ^ k • c k) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr (h u)
    have h0 := congrArg f h1

    simp only [map_sum, map_smul, Submodule.mkQ_apply, smul_eq_mul, map_zero] at h0
    simp only [hpdef, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h0]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff k) hp
  simp only [hpdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero, mul_ite, mul_one, mul_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa [Finset.mem_range.mpr hk] using hc

end GlobalTheory
end
