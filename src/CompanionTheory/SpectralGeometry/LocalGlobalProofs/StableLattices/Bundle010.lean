module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle002
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)

namespace GlobalTheory.CompanionTheory.PrimeRing.StdChain

variable {R : Type} [Ring R]

theorem word_left (E : R) (m : ℕ) (q x : ℕ → R) (hE : ∀ i ≤ m, E * q i = q i) (hid : q m * q m = q m)
    (hx : ∀ i < m, q i * x i = x i) (n k : ℕ) (hk : k + n = m) :
    q k * (word E ((List.range' k n).map x) * q m) = word E ((List.range' k n).map x) * q m := by
  cases n with
  | zero =>
    obtain rfl : k = m := by omega
    simp [hE k le_rfl, hid]
  | succ n =>
    have hkm : k < m := by omega
    have hEx : E * x k = x k := by
      rw [← hx k hkm, ← mul_assoc, hE k hkm.le]
    rw [List.range'_succ, List.map_cons, word_cons, hEx]
    simp only [← mul_assoc, hx k hkm]

theorem word_cases (E : R) (m : ℕ) (q x : ℕ → R) (hE : ∀ i ≤ m, E * q i = q i) (hid : q m * q m = q m)
    (hx1 : ∀ i < m, q i * x i = x i) (hx2 : ∀ i < m, x i * q (i + 1) = x i)
    (horth : ∀ i ≤ m, ∀ k ≤ m, i ≠ k → q i * q k = 0) (l : List ℕ) (hl : ∀ a ∈ l, a < m) :
    word E (l.map x) * q m = 0 ∨ ∃ k, k + l.length = m ∧ l = List.range' k l.length := by
  induction l with
  | nil => exact Or.inr ⟨m, rfl, rfl⟩
  | cons a l ih =>
    have ha : a < m := hl a (by simp)
    have hEx : E * x a = x a := by
      rw [← hx1 a ha, ← mul_assoc, hE a ha.le]
    rw [List.map_cons, word_cons, hEx]
    rcases ih (fun b hb => hl b (by simp [hb])) with h | ⟨k, hk, h⟩
    · left
      rw [mul_assoc, h, mul_zero]
    · by_cases hak : a + 1 = k
      · right
        refine ⟨a, by simp; omega, ?_⟩
        rw [List.length_cons, List.range'_succ, hak, ← h]
      · left
        have hw := word_left E m q x hE hid hx1 l.length k hk
        rw [← h] at hw
        calc x a * word E (l.map x) * q m
            = x a * q (a + 1) * (q k * (word E (l.map x) * q m)) := by
              rw [hx2 a ha, hw, mul_assoc]
          _ = x a * (q (a + 1) * q k) * (word E (l.map x) * q m) := by
              simp only [mul_assoc]
          _ = 0 := by
              rw [horth (a + 1) (by omega) k (by omega) hak]
              simp

theorem exists_chain (A S : Set R) (E : R) (m : ℕ) (q : ℕ → R)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) (hS : S ⊆ A)
    (hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0)
    (hA : ∀ i ≤ m, q i ∈ A) (hne : ∀ i ≤ m, q i ≠ 0) (hid : ∀ i ≤ m, q i * q i = q i)
    (hE : ∀ i ≤ m, E * q i = q i) (n k : ℕ) (hk : k + n = m) :
    ∃ (x : ℕ → R) (y : R), y ≠ 0 ∧ y ∈ A ∧ q k * y = y ∧
      (∀ i, k ≤ i → i < m → x i ∈ A ∧ q i * x i = x i ∧ x i * q (i + 1) = x i) ∧
      word E ((List.range' k n).map x) * q m = y := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = m := by omega
    exact ⟨0, q k, hne k le_rfl, hA k le_rfl, hid k le_rfl, fun i h1 h2 => absurd h2 (by omega),
      by simp [hE k le_rfl]⟩
  | succ n ih =>
    obtain ⟨x, y, hy0, hyA, hqy, hx, hw⟩ := ih (k + 1) (by omega)
    have hkm : k < m := by omega
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ S, q k * s * y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hne k hkm.le (hprime _ (hA k hkm.le) y hyA hy0 hcon)
    have hqs : q k * s ∈ A := hmul _ (hA k hkm.le) _ (hS hs)
    have hxk : q k * s * q (k + 1) ∈ A := hmul _ hqs _ (hA (k + 1) hkm)
    refine ⟨Function.update x k (q k * s * q (k + 1)), q k * s * y, hsy, hmul _ hqs _ hyA, ?_, ?_, ?_⟩
    · simp only [← mul_assoc, hid k hkm.le]
    · intro i h1 h2
      rcases eq_or_lt_of_le h1 with rfl | h3
      · rw [Function.update_self]
        refine ⟨hxk, ?_, ?_⟩
        · simp only [← mul_assoc, hid k hkm.le]
        · rw [mul_assoc _ (q (k + 1)), hid (k + 1) hkm]
      · rw [Function.update_of_ne (by omega)]
        exact hx i (by omega) h2
    · have hmap : (List.range' (k + 1) n).map (Function.update x k (q k * s * q (k + 1))) =
          (List.range' (k + 1) n).map x := by
        apply List.map_congr_left
        intro a ha
        have := List.mem_range'_1.mp ha
        rw [Function.update_of_ne (by omega)]
      have hEq : E * (q k * s * q (k + 1)) = q k * s * q (k + 1) := by
        simp only [← mul_assoc, hE k hkm.le]
      rw [List.range'_succ, List.map_cons, word_cons, hmap, Function.update_self, mul_assoc, hw, hEq,
        mul_assoc _ (q (k + 1)), hqy]

theorem no_chain_nat (A S : Set R) (E : R) (m : ℕ) (q : ℕ → R)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) (hS : S ⊆ A)
    (hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0)
    (hstd : ∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0)
    (hA : ∀ i ≤ m, q i ∈ A) (hne : ∀ i ≤ m, q i ≠ 0) (hid : ∀ i ≤ m, q i * q i = q i)
    (horth : ∀ i ≤ m, ∀ k ≤ m, i ≠ k → q i * q k = 0) (hE : ∀ i ≤ m, E * q i = q i) : False := by
  obtain ⟨x, y, hy0, -, -, hx, hw⟩ :=
    exists_chain A S E m q hmul hS hprime hA hne hid hE m 0 (by omega)
  have hx' : ∀ i, i < m → x i ∈ A ∧ q i * x i = x i ∧ x i * q (i + 1) = x i :=
    fun i hi => hx i (Nat.zero_le _) hi
  have h0 := hstd (fun i => x i) (fun i => (hx' i i.2).1)
  have hm : ∀ π : Equiv.Perm (Fin m), (List.ofFn fun i => x (π i)) =
      (List.ofFn fun i => (π i : ℕ)).map x := by
    intro π
    rw [List.map_ofFn]
    rfl
  have key : stdPoly E (fun i : Fin m => x i) * q m = y := by
    rw [stdPoly, Finset.sum_mul, Finset.sum_eq_single 1]
    · rw [hm]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one, id]
      rw [CompanionTheory.D.gk.admitted.FinOfPIAux.ofFn_val, hw]
    · intro π _ hπ
      rw [hm, mul_assoc]
      rcases word_cases E m q x hE (hid m le_rfl) (fun i hi => (hx' i hi).2.1)
        (fun i hi => (hx' i hi).2.2) horth (List.ofFn fun i => (π i : ℕ))
        (by simp [List.mem_ofFn]) with h | ⟨k, hk, h⟩
      · rw [h, mul_zero]
      · exfalso
        apply hπ
        rw [List.length_ofFn] at hk h
        obtain rfl : k = 0 := by omega
        rw [← CompanionTheory.D.gk.admitted.FinOfPIAux.ofFn_val] at h
        ext i
        exact congrFun (List.ofFn_injective h) i
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h0, zero_mul] at key
  exact hy0 key.symm

theorem no_orthogonal_idempotents : ∀ (R : Type) [Ring R] (A S : Set R) (E : R) (m : ℕ) (q : Fin (m + 1) → R),
    (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) → S ⊆ A →
    (∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0) →
    (∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0) →
    (∀ i, q i ∈ A) → (∀ i, q i ≠ 0) → (∀ i, q i * q i = q i) → (∀ i k, i ≠ k → q i * q k = 0) →
    (∀ i, E * q i = q i) → False := by
  intro R _ A S E m q hmul hS hprime hstd hA hne hid horth hE
  let qq : ℕ → R := fun i => if h : i < m + 1 then q ⟨i, h⟩ else 0
  have hqq : ∀ i (h : i ≤ m), qq i = q ⟨i, Nat.lt_succ_of_le h⟩ := fun i h =>
    dif_pos (Nat.lt_succ_of_le h)
  refine no_chain_nat A S E m qq hmul hS hprime hstd ?_ ?_ ?_ ?_ ?_
  · intro i h
    rw [hqq i h]
    exact hA _
  · intro i h
    rw [hqq i h]
    exact hne _
  · intro i h
    rw [hqq i h]
    exact hid _
  · intro i h k h' hik
    rw [hqq i h, hqq k h']
    exact horth _ _ fun e => hik (congrArg Fin.val e)
  · intro i h
    rw [hqq i h]
    exact hE _

end GlobalTheory.CompanionTheory.PrimeRing.StdChain
end

section

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

theorem exists_least_norm_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {C : Set E} (hne : C.Nonempty) (hcl : IsClosed C) (hconv : Convex ℝ C) :
    ∃ u ∈ C, ∀ w ∈ C, ‖u‖ ≤ ‖w‖ ∧ (‖w‖ ≤ ‖u‖ → w = u) := by
  obtain ⟨u, hu, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv (0 : E)
  have hin := (norm_eq_iInf_iff_real_inner_le_zero hconv hu).1 hmin
  refine ⟨u, hu, fun w hw => ?_⟩
  have h1 := hin w hw
  have h3 : inner ℝ (0 - u) (w - u) = ‖u‖ ^ 2 - inner ℝ w u := by
    rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm w u]
    ring
  have h2 : ‖w - u‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w u + ‖u‖ ^ 2 := norm_sub_sq_real w u
  have h4 : inner ℝ w u ≤ ‖w‖ * ‖u‖ := real_inner_le_norm w u
  constructor
  · rcases (norm_nonneg u).eq_or_lt with h0 | h0
    · rw [← h0]; exact norm_nonneg w
    · nlinarith
  · intro hle
    have h6 : ‖w‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have := norm_nonneg w
      nlinarith
    have h8 : ‖w - u‖ = 0 := by
      have := norm_nonneg (w - u)
      nlinarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h8)

theorem stFixVec : StFixVec := by
  intro G H _ _ _ _ _ _ _ σ hiso hcont
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨v, hv⟩ : ∃ v : H, ‖v‖ = 1 :=
    ⟨((‖x‖ : ℂ)⁻¹) • x, by
      have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      simp [norm_smul, this]⟩
  have hopen : IsOpen {g : G | ‖σ g v - v‖ < 1 / 2} :=
    isOpen_lt (((hcont v).sub continuous_const).norm) continuous_const
  have hone : (1 : G) ∈ {g : G | ‖σ g v - v‖ < 1 / 2} := by simp
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _ (hopen.mem_nhds hone)
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  set A : Set H := Set.range (fun k : V => σ (k : G) v) with hA
  set C : Set H := closure (convexHull ℝ A) with hC
  have hvA : v ∈ A := ⟨1, by simp⟩
  have hCne : C.Nonempty := ⟨v, subset_closure (subset_convexHull ℝ A hvA)⟩
  have hCconv : Convex ℝ C := (convex_convexHull ℝ A).closure
  have hCball : C ⊆ Metric.closedBall v (1 / 2) := by
    refine closure_minimal (convexHull_min ?_ (convex_closedBall _ _)) Metric.isClosed_closedBall
    rintro _ ⟨k, rfl⟩
    have := hV k.2
    simp only [Set.mem_setOf_eq] at this
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact this.le
  have hstable : ∀ k : V, ∀ y ∈ C, σ (k : G) y ∈ C := by
    intro k y hy
    have hmaps : Set.MapsTo (σ (k : G)) (convexHull ℝ A) (convexHull ℝ A) := by
      have hconvpre : Convex ℝ ((σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A) :=
        (convex_convexHull ℝ A).linear_preimage _
      have hsub : A ⊆ (σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A := by
        rintro _ ⟨l, rfl⟩
        refine subset_convexHull ℝ A ⟨k * l, ?_⟩
        simp
      exact fun z hz => convexHull_min hsub hconvpre hz
    exact map_mem_closure (σ (k : G)).continuous hy hmaps
  obtain ⟨u, huC, hu⟩ := exists_least_norm_unique hCne isClosed_closure hCconv
  refine ⟨V.toSubgroup, u, V.isOpen, ?_, ?_⟩
  · rintro rfl
    have := hCball huC
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg, hv] at this
    norm_num at this
  · intro k hk
    exact (hu _ (hstable ⟨k, hk⟩ u huC)).2 (hiso k u).le

end GlobalTheory.CompanionTheory.RgFl
end

section

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.CartanMove

variable {G G' : Type} [Group G] [Group G']

theorem closure_symm_eq (e : G ≃* G') {l : ℕ} (t' : Fin l → G') :
    Submonoid.closure (Set.range fun j => e.symm (t' j)) =
      (Submonoid.closure (Set.range t')).map e.symm.toMonoidHom := by
  rw [MonoidHom.map_mclosure, ← Set.range_comp]
  rfl

theorem apply_mem_closure (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G}
    (hs : s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j))) :
    e s ∈ Submonoid.closure (Set.range t') := by
  rw [closure_symm_eq] at hs
  obtain ⟨x, hx, rfl⟩ := hs
  simpa using hx

theorem symm_mem_closure (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G'}
    (hs : s ∈ Submonoid.closure (Set.range t')) :
    e.symm s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j)) := by
  rw [closure_symm_eq]
  exact ⟨s, hs, rfl⟩

theorem isCartan_comap (e : G ≃* G') {K' : Subgroup G'} {d l : ℕ} (h : IsCartan K' d l) :
    IsCartan (K'.comap e.toMonoidHom) d l := by
  obtain ⟨c', t', h1, h2, h3, h4⟩ := h
  have hmem : ∀ {x : G'}, x ∈ K' → e.symm x ∈ K'.comap e.toMonoidHom := fun {x} hx => by
    simpa [Subgroup.mem_comap] using hx
  refine ⟨fun i => e.symm (c' i), fun j => e.symm (t' j), ?_, ?_, ?_, ?_⟩
  · intro i k
    simpa [Subgroup.mem_comap] using h1 i (e k)
  · intro i j
    exact (h2 i j).map e.symm
  · intro g
    obtain ⟨i, j, s, hs, k, hk, k', hk', hg⟩ := h3 (e g)
    refine ⟨i, j, e.symm s, symm_mem_closure e t' hs, e.symm k, hmem hk, e.symm k', hmem hk', ?_⟩
    apply e.injective
    simpa [map_mul] using hg
  · intro s hs s' hs' k hk
    obtain ⟨a, ha, b, hb, hab⟩ := h4 (e s) (apply_mem_closure e t' hs) (e s')
      (apply_mem_closure e t' hs') (e k) hk
    refine ⟨e.symm a, hmem ha, e.symm b, hmem hb, ?_⟩
    apply e.injective
    simpa [map_mul] using hab

theorem stMove : StMove := by
  intro G G' _ _ _ _ e h U hU
  have hopen : IsOpen ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G') := by
    have : ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G') = e.toHomeomorph '' (U : Set G) := rfl
    rw [this]
    exact e.toHomeomorph.isOpenMap _ hU
  obtain ⟨K', hK'U, hoK', hcK', d, l, hC⟩ := h _ hopen
  refine ⟨K'.comap e.toMulEquiv.toMonoidHom, ?_, ?_, ?_, d, l, isCartan_comap _ hC⟩
  · intro x hx
    obtain ⟨u, hu, hux⟩ := hK'U hx
    have : u = x := e.toMulEquiv.injective hux
    exact this ▸ hu
  · exact hoK'.preimage e.toHomeomorph.continuous
  · exact e.toHomeomorph.isCompact_preimage.2 hcK'

end GlobalTheory.CompanionTheory.CartanMove
end

section

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.HeckePair

theorem stPair : StPair := by
  intro G _ _ _ K hKo hKc g
  have : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hcont : Continuous fun k : K => (((k : G) * g : G) : G ⧸ K) :=
    (QuotientGroup.continuous_mk (N := K)).comp (continuous_subtype_val.mul continuous_const)
  have hfin : (Set.range fun k : K => (((k : G) * g : G) : G ⧸ K)).Finite :=
    (isCompact_range hcont).finite_of_discrete
  refine hfin.subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.HeckePair
end

section

open scoped InnerProductSpace
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted

namespace GlobalTheory.CompanionTheory.FixedProj

theorem stProj : StProj := by
  unfold StProj
  intro G H _ _ _ _ σ hiso K
  let V : Submodule ℂ H :=
    { carrier := {v | ∀ k ∈ K, σ k v = v}
      add_mem' := fun {a b} ha hb k hk => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add (f := _), ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun c v hv k hk => by
        simp only [Set.mem_ofPred_eq] at hv ⊢
        rw [map_smul, hv k hk] }
  have hmem : ∀ v, v ∈ V ↔ ∀ k ∈ K, σ k v = v := fun v => Iff.rfl
  have hVc : IsClosed (V : Set H) := by
    have hV : (V : Set H) = ⋂ k ∈ K, {v | σ k v = v} := by
      ext v
      simp only [Set.mem_iInter]
      exact hmem v
    rw [hV]
    exact isClosed_biInter fun k _ => isClosed_eq (σ k).continuous continuous_id
  haveI : CompleteSpace V := hVc.completeSpace_coe
  have hin : ∀ g v w, inner ℂ (σ g v) w = inner ℂ v (σ g⁻¹ w) := CompanionTheory.D.gk.admitted.FinOfPIAux.inner_left σ hiso
  refine ⟨V.starProjection, ?_, ?_, ?_⟩
  · unfold IsAvg
    refine ⟨?_, ?_, ?_⟩
    · intro v k hk
      exact (hmem _).1 (V.starProjection_apply_mem v) k hk
    · intro v hv
      exact Submodule.starProjection_eq_self_iff.2 ((hmem v).2 hv)
    · intro v k hk
      have horth : σ k v - v ∈ Vᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 : inner ℂ u (σ k v) = inner ℂ u v := by
          have h := hin k⁻¹ u v
          rw [inv_inv, (hmem u).1 hu k⁻¹ (K.inv_mem hk)] at h
          exact h.symm
        rw [inner_sub_right, h1, sub_self]
      have h0 := (Submodule.starProjection_apply_eq_zero_iff V).2 horth
      rw [map_sub, sub_eq_zero] at h0
      exact h0
  · intro u w
    exact Submodule.inner_starProjection_left_eq_right (K := V) u w
  · intro T hT
    have hTσ : ∀ g v, T (σ g v) = σ g (T v) := fun g v =>
      congrArg (fun S : H →L[ℂ] H => S v) (hT g)
    have hTV : ∀ v ∈ V, T v ∈ V := fun v hv k hk => by
      rw [← hTσ, (hmem v).1 hv k hk]
    have hadj : ∀ w ∈ V, ContinuousLinearMap.adjoint T w ∈ V := by
      intro w hw k hk
      apply ext_inner_right ℂ
      intro z
      rw [hin, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hTσ, ← hin,
        (hmem w).1 hw k hk]
    ext v
    have h1 : V.starProjection (T (V.starProjection v)) = T (V.starProjection v) :=
      Submodule.starProjection_eq_self_iff.2 (hTV _ (V.starProjection_apply_mem v))
    have hu : v - V.starProjection v ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal (K := V) v
    have h2 : V.starProjection (T (v - V.starProjection v)) = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff V).2
      rw [Submodule.mem_orthogonal] at hu ⊢
      intro w hw
      rw [← ContinuousLinearMap.adjoint_inner_left]
      exact hu _ (hadj w hw)
    have hv : v = V.starProjection v + (v - V.starProjection v) := by abel
    show T (V.starProjection v) = V.starProjection (T v)
    conv_rhs => rw [hv]
    simp only [map_add (f := _)]
    rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.FixedProj
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.unitary_factors_of_unitary_upper_mul_lowerUni : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ (rev : ι → ι), (∀ i, rev (rev i) = i) → (∀ i j, wt i < wt j → wt (rev j) < wt (rev i)) → Function.Injective wt → ∀ (st : E → E), (∀ a b, st (a * b) = st b * st a) → st 1 = 1 → st 0 = 0 → (∀ i, st (P i) = P (rev i)) → (∀ a a' : E, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a') → (∀ b b' : E, b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b') → ∀ a a' b b' : E, a * a' = 1 → a' * a = 1 → b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b → st (a * b) * (a * b) = 1 → (a * b) * st (a * b) = 1 → st a * a = 1 ∧ st b * b = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor | exact GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor | (intros; apply GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.torus_conjugation_preserves_congruence : ∀ {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E, GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → (∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J) → ∀ (T T' : E) (τ : ι → L), (∀ i, τ i ≠ 0) → T * T' = 1 → T' * T = 1 → (∀ i, T * P i = τ i • P i) → (∀ i, P i * T = τ i • P i) → (∀ i j, wt i ≤ wt j → ‖τ i‖ ≤ ‖τ j‖) → ∀ a b : E, a - 1 ∈ J → b - 1 ∈ J → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → T * a * T' - 1 ∈ J ∧ T' * b * T - 1 ∈ J := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence | exact GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence | (intros; apply GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.congruence_endomorphism_inverse_exists : ∀ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] (Λ : AddSubgroup V), IsLat L Λ → ∀ π : L, ‖π‖ < 1 → ∀ g ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π, ∃ g' ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π, (1 + g) * (1 + g') = 1 ∧ (1 + g') * (1 + g) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.CongUnit.main | exact GlobalTheory.CompanionTheory.Iwahori.CongUnit.main | (intros; apply GlobalTheory.CompanionTheory.Iwahori.CongUnit.main <;> assumption)
end
