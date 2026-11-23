module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.RingTheory.Length
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

section
end

section

open Pointwise Set

namespace ReciprocityTheory.Coh.ContinuousSections

variable {G : Type*} [Group G]

def rel (K N : Subgroup G) [hN : N.Normal] : Setoid G where
  r x y := ∃ k ∈ K, ∃ n ∈ N, y = k * n * x
  iseqv := {
    refl := fun x => ⟨1, K.one_mem, 1, N.one_mem, by simp⟩
    symm := by
      rintro x y ⟨k, hk, n, hn, rfl⟩
      refine ⟨k⁻¹, K.inv_mem hk, k * n⁻¹ * k⁻¹, hN.conj_mem _ (N.inv_mem hn) k, by group⟩
    trans := by
      rintro x y z ⟨k, hk, n, hn, rfl⟩ ⟨k', hk', n', hn', rfl⟩
      refine ⟨k' * k, K.mul_mem hk' hk, k⁻¹ * n' * k * n, N.mul_mem ?_ hn, by group⟩
      simpa using hN.conj_mem n' hn' k⁻¹ }

noncomputable def rep (K N : Subgroup G) [N.Normal] (x : G) : G :=
  (Quotient.mk (rel K N) x).out

lemma rep_eq (K N : Subgroup G) [N.Normal] {x y : G} (h : (rel K N) x y) : rep K N x = rep K N y := by
  unfold rep
  rw [Quotient.sound (s := rel K N) h]

lemma rep_spec (K N : Subgroup G) [N.Normal] (x : G) : ∃ k ∈ K, ∃ n ∈ N, x = k * n * rep K N x := by
  exact Quotient.mk_out (s := rel K N) x

def tr (K N : Subgroup G) [N.Normal] : Set G := {y | y * (rep K N y)⁻¹ ∈ N}

lemma tr_coset (K N : Subgroup G) [N.Normal] {y z : G} (h : z * y⁻¹ ∈ N) :
    z ∈ tr K N ↔ y ∈ tr K N := by
  have hr : rep K N z = rep K N y :=
    (rep_eq K N ⟨1, K.one_mem, z * y⁻¹, h, by group⟩).symm
  show z * (rep K N z)⁻¹ ∈ N ↔ y * (rep K N y)⁻¹ ∈ N
  rw [hr, show z * (rep K N y)⁻¹ = z * y⁻¹ * (y * (rep K N y)⁻¹) by group]
  exact N.mul_mem_cancel_left h

variable [TopologicalSpace G] [IsTopologicalGroup G]

lemma tr_closed (K N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G)) : IsClosed (tr K N) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  refine ⟨(fun z => z * y⁻¹) ⁻¹' (N : Set G), fun z hz hzt => hy ((tr_coset K N hz).1 hzt),
    hN.preimage (continuous_id.mul continuous_const), ?_⟩
  simp

def admitted (U : Subgroup G) (p : Subgroup G × Set G) : Prop :=
  p.1 ≤ U ∧ IsClosed p.2 ∧ (∀ k ∈ p.1, ∀ s ∈ p.2, k * s ∈ p.2) ∧
  (∀ a ∈ p.2, ∀ b ∈ p.2, a * b⁻¹ ∈ U → a * b⁻¹ ∈ p.1) ∧ ∀ g, ∃ a ∈ p.2, a * g⁻¹ ∈ U

lemma adm_of_section_mem (U K : Subgroup G) (S : Set G) (h : admitted U (K, S)) (N : Subgroup G) [N.Normal]
    (hN : IsOpen (N : Set G)) : admitted U (K ⊓ N, S ∩ tr K N) := by
  obtain ⟨hKU, hSc, hKS, hSK, hSU⟩ := h
  refine ⟨inf_le_left.trans hKU, hSc.inter (tr_closed K N hN), ?_, ?_, ?_⟩
  · rintro k ⟨hkK, hkN⟩ s ⟨hsS, hsT⟩
    refine ⟨hKS k hkK s hsS, (tr_coset K N ?_).2 hsT⟩
    simpa using hkN
  · rintro a ⟨haS, haT⟩ b ⟨hbS, hbT⟩ hab
    have habK := hSK a haS b hbS hab
    refine ⟨habK, ?_⟩
    have hr : rep K N b = rep K N a := rep_eq K N ⟨a * b⁻¹, habK, 1, N.one_mem, by group⟩
    have ha : a * (rep K N a)⁻¹ ∈ N := haT
    have hb : b * (rep K N b)⁻¹ ∈ N := hbT
    rw [hr] at hb
    have := N.mul_mem ha (N.inv_mem hb)
    simpa [mul_assoc] using this
  · intro g
    obtain ⟨a, haS, hag⟩ := hSU g
    obtain ⟨k, hk, n, hn, ha⟩ := rep_spec K N a
    set r := rep K N a with hrdef
    have hrel : rep K N (k⁻¹ * a) = r := (rep_eq K N ⟨k⁻¹, K.inv_mem hk, 1, N.one_mem, by group⟩).symm
    refine ⟨k⁻¹ * a, ⟨hKS _ (K.inv_mem hk) a haS, ?_⟩, ?_⟩
    · show k⁻¹ * a * (rep K N (k⁻¹ * a))⁻¹ ∈ N
      rw [hrel, ha]
      simpa [mul_assoc] using hn
    · rw [mul_assoc]
      exact U.mul_mem (U.inv_mem (hKU hk)) hag

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma admissible_chain_inf [CompactSpace G] (U : Subgroup G) (hU : IsClosed (U : Set G))
    (c : Set (Subgroup G × Set G)) (hc : ∀ p ∈ c, admitted U p)
    (htot : ∀ p ∈ c, ∀ q ∈ c, p ≤ q ∨ q ≤ p) (y : Subgroup G × Set G) (hy : y ∈ c) :
    admitted U (⨅ p ∈ c, p.1, ⋂ p ∈ c, p.2) := by
  refine ⟨(iInf₂_le y hy).trans (hc y hy).1, isClosed_biInter fun p hp => (hc p hp).2.1, ?_, ?_, ?_⟩
  · intro k hk s hs
    simp only [Subgroup.mem_iInf] at hk
    simp only [Set.mem_iInter] at hs ⊢
    exact fun p hp => (hc p hp).2.2.1 k (hk p hp) s (hs p hp)
  · intro a ha b hb hab
    simp only [Set.mem_iInter] at ha hb
    simp only [Subgroup.mem_iInf]
    exact fun p hp => (hc p hp).2.2.2.1 a (ha p hp) b (hb p hp) hab
  · intro g
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    have hne := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun p : c => p.1.2 ∩ {a | a * g⁻¹ ∈ U}) ?_ ?_
      (fun p => ((hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul continuous_const))).isCompact)
      (fun p => (hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul continuous_const)))
    · obtain ⟨a, ha⟩ := hne
      simp only [Set.mem_iInter] at ha
      refine ⟨a, ?_, (ha ⟨y, hy⟩).2⟩
      simp only [Set.mem_iInter]
      exact fun p hp => (ha ⟨p, hp⟩).1
    · intro p q
      rcases htot p.1 p.2 q.1 q.2 with hpq | hqp
      · exact ⟨p, le_rfl, Set.inter_subset_inter_left _ (Prod.le_def.1 hpq).2⟩
      · exact ⟨q, Set.inter_subset_inter_left _ (Prod.le_def.1 hqp).2, le_rfl⟩
    · intro p
      obtain ⟨a, haS, hag⟩ := (hc p.1 p.2).2.2.2.2 g
      exact ⟨a, haS, hag⟩

theorem core [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (U : Subgroup G)
    (hU : IsClosed (U : Set G)) : ∃ t : G → G, Continuous t ∧ (∀ g, t g * g⁻¹ ∈ U) ∧
      ∀ g h, g * h⁻¹ ∈ U → t g = t h := by
  classical
  have hchain : ∀ c ⊆ {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)},
      IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)},
        ∀ z ∈ c, z ≤ ub := by
    intro c hcs hc y hy
    refine ⟨OrderDual.toDual (⨅ p ∈ OrderDual.toDual ⁻¹' c, p.1, ⋂ p ∈ OrderDual.toDual ⁻¹' c, p.2),
      admissible_chain_inf U hU _ (fun p hp => hcs hp) ?_ (OrderDual.ofDual y) hy, ?_⟩
    · intro p hp q hq
      by_cases hpq : p = q
      · exact Or.inl (le_of_eq hpq)
      · rcases hc hp hq (fun h => hpq (OrderDual.toDual.injective h)) with h | h
        · exact Or.inr h
        · exact Or.inl h
    · intro z hz
      exact Prod.le_def.2 ⟨iInf₂_le (OrderDual.ofDual z) hz,
        Set.iInter₂_subset (OrderDual.ofDual z) hz⟩
  have hstart : OrderDual.toDual ((U, Set.univ) : Subgroup G × Set G) ∈
      {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)} :=
    ⟨le_rfl, isClosed_univ, fun _ _ _ _ => Set.mem_univ _, fun _ _ _ _ h => h,
      fun g => ⟨g, Set.mem_univ _, by simp⟩⟩
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ _ hchain _ hstart
  have hA : admitted U (OrderDual.ofDual m) := hm.1
  set K := (OrderDual.ofDual m).1 with hKdef
  set S := (OrderDual.ofDual m).2 with hSdef
  have hK1 : ∀ k ∈ K, k = 1 := by
    intro k hk
    by_contra hne
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isOpen_compl_singleton : IsOpen ({k}ᶜ : Set G)) (Set.mem_compl_singleton_iff.2 (Ne.symm hne))
    have hstep := adm_of_section_mem U K S hA N.toSubgroup N.isOpen'
    have hle := hm.2 (y := OrderDual.toDual (K ⊓ N.toSubgroup, S ∩ tr K N.toSubgroup)) hstep
      (Prod.le_def.2 ⟨inf_le_left, Set.inter_subset_left⟩)
    have hkN : k ∈ N.toSubgroup := ((Prod.le_def.1 hle).1 hk).2
    exact hN hkN rfl
  have hex : ∀ g, ∃ a ∈ S, a * g⁻¹ ∈ U := hA.2.2.2.2
  have huniq : ∀ g a a', a ∈ S → a' ∈ S → a * g⁻¹ ∈ U → a' * g⁻¹ ∈ U → a = a' := by
    intro g a a' ha ha' hag ha'g
    have hU' : a * a'⁻¹ ∈ U := by
      have := U.mul_mem hag (U.inv_mem ha'g)
      simpa [mul_assoc] using this
    exact mul_inv_eq_one.1 (hK1 _ (hA.2.2.2.1 a ha a' ha' hU'))
  choose t htS htU using hex
  refine ⟨t, ?_, htU, fun g h hgh => ?_⟩
  · rw [continuous_iff_isClosed]
    intro C hC
    have hset : t ⁻¹' C = (U : Set G) * (S ∩ C) := by
      ext g
      constructor
      · intro hg
        refine Set.mem_mul.2 ⟨g * (t g)⁻¹, ?_, t g, ⟨htS g, hg⟩, by group⟩
        simpa using U.inv_mem (htU g)
      · rintro ⟨u, hu, a, ⟨haS, haC⟩, rfl⟩
        show t (u * a) ∈ C
        rw [huniq (u * a) (t (u * a)) a (htS _) haS (htU _) (by simpa using U.inv_mem hu)]
        exact haC
    rw [hset]
    exact (hU.isCompact.mul (hA.2.1.inter hC).isCompact).isClosed
  · refine huniq g (t g) (t h) (htS g) (htS h) (htU g) ?_
    have : t h * g⁻¹ = (t h * h⁻¹) * (g * h⁻¹)⁻¹ := by group
    rw [this]
    exact U.mul_mem (htU h) (U.inv_mem hgh)

end ReciprocityTheory.Coh.ContinuousSections
end

section

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open Topology
open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem comm_of_dense [T2Space G] {s : G} (hs : Dense (Subgroup.zpowers s : Set G)) (a b : G) :
    a * b = b * a := by
  have hcl : IsClosed {p : G × G | p.1 * p.2 = p.2 * p.1} :=
    isClosed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst)
  have hd : Dense ((Subgroup.zpowers s : Set G) ×ˢ (Subgroup.zpowers s : Set G)) := hs.prod hs
  have hsub : (Subgroup.zpowers s : Set G) ×ˢ (Subgroup.zpowers s : Set G) ⊆
      {p : G × G | p.1 * p.2 = p.2 * p.1} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact zpow_mul_comm s i j
  have h := hcl.closure_subset_iff.2 hsub
  rw [hd.closure_eq] at h
  exact h (Set.mem_univ (a, b))

theorem normal_of_comm (hc : ∀ a b : G, a * b = b * a) (W : Subgroup G) : W.Normal :=
  ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩

theorem finite_quot [CompactSpace G] (hc : ∀ a b : G, a * b = b * a) {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : Finite (G ⧸ W) := by
  exact Subgroup.quotient_finite_of_isOpen W hW

theorem index_pos [CompactSpace G] (hc : ∀ a b : G, a * b = b * a) {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : 0 < W.index := by
  haveI := finite_quot hc hW
  exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

variable {s : G}

theorem mem_zpowers_quot (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} [W.Normal]
    (hW : IsOpen (W : Set G)) (x : G ⧸ W) : x ∈ Subgroup.zpowers (QuotientGroup.mk' W s) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hU : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (W : Set G)) :=
    hW.preimage (continuous_const.mul continuous_id)
  obtain ⟨y, hyU, hy⟩ := hs.inter_open_nonempty _ hU ⟨g, by simp [W.one_mem]⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow, QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq.mpr hyU).symm

theorem zpow_mem_iff [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G)) (z : ℤ) :
    s ^ z ∈ W ↔ (W.index : ℤ) ∣ z := by
  haveI := normal_of_comm hc W
  haveI := finite_quot hc hW
  have hord : orderOf (QuotientGroup.mk' W s) = W.index := by
    rw [orderOf_eq_card_of_forall_mem_zpowers (mem_zpowers_quot hs hW)]
    rfl
  rw [← QuotientGroup.eq_one_iff (N := W), ← hord, orderOf_dvd_iff_zpow_eq_one, ← map_zpow,
    QuotientGroup.mk'_apply]

theorem exists_pow [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G)) (g : G) :
    ∃ j : ℕ, g⁻¹ * s ^ j ∈ W := by
  haveI := normal_of_comm hc W
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_quot hs hW (g : G ⧸ W))
  rw [← map_zpow, QuotientGroup.mk'_apply] at hk
  have hgk : g⁻¹ * s ^ k ∈ W := QuotientGroup.eq.mp hk.symm
  have hn : (0 : ℤ) < W.index := by exact_mod_cast index_pos hc hW
  refine ⟨(k % (W.index : ℤ)).toNat, ?_⟩
  have hj : (((k % (W.index : ℤ)).toNat : ℕ) : ℤ) = k % (W.index : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hn.ne')
  have hd : s ^ (k % (W.index : ℤ) - k) ∈ W := by
    rw [zpow_mem_iff hc hs hW]
    exact ⟨-(k / (W.index : ℤ)), by rw [Int.emod_def]; ring⟩
  have heq : g⁻¹ * s ^ (k % (W.index : ℤ)).toNat =
      (g⁻¹ * s ^ k) * s ^ (k % (W.index : ℤ) - k) := by
    rw [mul_assoc, ← zpow_add, ← zpow_natCast, hj]
    congr 2
    ring
  rw [heq]
  exact W.mul_mem hgk hd

section Desc

variable {X : Type*} (n : ℕ) (T : ℕ → X)

theorem per_mul (hper : ∀ j, T (j + n) = T j) (a t : ℕ) : T (a + n * t) = T a := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]

theorem per_of_dvd (hper : ∀ j, T (j + n) = T j) (a b : ℕ) (h : (n : ℤ) ∣ (b : ℤ) - a) :
    T a = T b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · have h1 : ((b : ℕ) : ℤ) = ((a + n * m : ℕ) : ℤ) := by push_cast; linarith
    have h2 : b = a + n * m := by exact_mod_cast h1
    rw [h2, per_mul n T hper]
  · rw [mul_neg] at hc
    have h1 : ((a : ℕ) : ℤ) = ((b + n * m : ℕ) : ℤ) := by push_cast; linarith
    have h2 : a = b + n * m := by exact_mod_cast h1
    rw [h2, per_mul n T hper]

end Desc

noncomputable def desc (W : Subgroup G) (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*}
    (T : ℕ → X) (g : G) : X :=
  T (Classical.choose (h g))

theorem desc_eq [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G))
    (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*} (T : ℕ → X)
    (hper : ∀ j, T (j + W.index) = T j) {g : G} {j : ℕ} (hj : g⁻¹ * s ^ j ∈ W) :
    desc W h T g = T j := by
  have h0 := Classical.choose_spec (h g)
  show T (Classical.choose (h g)) = T j
  have hm : s ^ ((j : ℤ) - (Classical.choose (h g) : ℕ)) ∈ W := by
    have hw := W.mul_mem (W.inv_mem h0) hj
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at hw
    rw [zpow_sub, zpow_natCast, zpow_natCast, hc]
    exact hw
  exact per_of_dvd W.index T hper _ _ ((zpow_mem_iff hc hs hW _).mp hm)

theorem desc_continuous [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G))
    (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*} [TopologicalSpace X] (T : ℕ → X)
    (hper : ∀ j, T (j + W.index) = T j) : Continuous (desc W h T) := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hU : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (W : Set G)) :=
    hW.preimage (continuous_const.mul continuous_id)
  have hg : g ∈ (fun y => g⁻¹ * y) ⁻¹' (W : Set G) := by simp [W.one_mem]
  refine (continuousAt_const : ContinuousAt (fun _ : G => desc W h T g) g).congr ?_
  filter_upwards [hU.mem_nhds hg] with y hy
  have h0 := Classical.choose_spec (h g)
  have hy' : y⁻¹ * s ^ Classical.choose (h g) ∈ W := by
    have hw := W.mul_mem (W.inv_mem hy) h0
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at hw
    exact hw
  rw [desc_eq hc hs hW h T hper hy']
  rfl

end ProcyclicCohomology

end ReciprocityTheory.Coh
end

section

namespace ReciprocityTheory.Coh

noncomputable section

universe u

variable {R : Type u} [CommRing R]

structure Cx (R : Type u) [CommRing R] where
  X : ℕ → Type u
  [acg : ∀ n, AddCommGroup (X n)]
  [mod : ∀ n, Module R (X n)]
  d : ∀ n, X n →ₗ[R] X (n + 1)
  dd : ∀ n x, d (n + 1) (d n x) = 0

attribute [instance] Cx.acg Cx.mod

namespace Cx

def Z (A : Cx R) (n : ℕ) : Submodule R (A.X n) := LinearMap.ker (A.d n)

def B (A : Cx R) : (n : ℕ) → Submodule R (A.X n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (A.d n)

abbrev H (A : Cx R) (n : ℕ) := A.Z n ⧸ (A.B n).comap (A.Z n).subtype

def cls (A : Cx R) (n : ℕ) (x : A.X n) (hx : A.d n x = 0) : A.H n := Submodule.Quotient.mk ⟨x, hx⟩

structure Hom (A B : Cx R) where
  f : ∀ n, A.X n →ₗ[R] B.X n
  comm : ∀ n x, f (n + 1) (A.d n x) = B.d n (f n x)

variable {A B C : Cx R}

def Hom.id (A : Cx R) : Hom A A := ⟨fun _ => LinearMap.id, fun _ _ => rfl⟩

def Hom.comp (ψ : Hom B C) (φ : Hom A B) : Hom A C :=
  ⟨fun n => (ψ.f n).comp (φ.f n), fun n x => by simp [φ.comm, ψ.comm]⟩

def Hom.Z (φ : Hom A B) (n : ℕ) : A.Z n →ₗ[R] B.Z n :=
  (φ.f n).restrict fun x hx => by
    have hx' : A.d n x = 0 := hx
    show B.d n (φ.f n x) = 0
    rw [← φ.comm, hx', map_zero]

def Hom.H (φ : Hom A B) (n : ℕ) : A.H n →ₗ[R] B.H n :=
  Submodule.mapQ _ _ (φ.Z n) fun x hx => by
    cases n with
    | zero =>
      have hx' : x.1 = 0 := hx
      show φ.f 0 x.1 ∈ (⊥ : Submodule R _)
      rw [hx', map_zero]; exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨y, hy⟩ := hx
      refine ⟨φ.f n y, ?_⟩
      show B.d n (φ.f n y) = φ.f (n + 1) x.1
      rw [← φ.comm, hy]; rfl

def Hom.QuasiIso (φ : Hom A B) : Prop := ∀ n, Function.Bijective (φ.H n)

structure SES (i : Hom A B) (p : Hom B C) : Prop where
  inj : ∀ n, Function.Injective (i.f n)
  exact : ∀ n, Function.Exact (i.f n) (p.f n)
  surj : ∀ n, Function.Surjective (p.f n)

def IsConn (i : Hom A B) (p : Hom B C) (δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)) : Prop :=
  ∀ n (b : B.X n) (a : A.X (n + 1)) (hc : C.d n (p.f n b) = 0) (ha : A.d (n + 1) a = 0),
    B.d n b = i.f (n + 1) a → δ n (C.cls n (p.f n b) hc) = A.cls (n + 1) a ha

structure LES (i : Hom A B) (p : Hom B C) (δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)) : Prop where
  inj : Function.Injective (i.H 0)
  exB : ∀ n, Function.Exact (i.H n) (p.H n)
  exC : ∀ n, Function.Exact (p.H n) (δ n)
  exA : ∀ n, Function.Exact (δ n) (i.H (n + 1))

def FinLen (A : Cx R) (N : ℕ) : Prop :=
  (∀ n, IsFiniteLength R (A.H n)) ∧ ∀ n, N < n → Subsingleton (A.H n)

def chi (A : Cx R) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1) ^ n * ((Module.length R (A.H n)).toNat : ℤ)

structure IsTowerLim (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m)) :
    Prop where
  surj : ∀ m n, Function.Surjective ((τ m).f n)
  compat : ∀ m n x, (τ m).f n ((π (m + 1)).f n x) = (π m).f n x
  ext : ∀ n (x : L.X n), (∀ m, (π m).f n x = 0) → x = 0
  lift : ∀ n (y : ∀ m, (A m).X n), (∀ m, (τ m).f n (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).f n x = y m

end Cx

end

end ReciprocityTheory.Coh
end
