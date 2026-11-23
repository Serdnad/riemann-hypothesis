module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic

@[expose] public section

section

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

def dhFam (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) : Multiset ℂ :=
  Z.val.bind (fun ρ => Multiset.replicate (m ρ) (s - ρ))

theorem dhFam_mem (Z : Finset ℂ) (m : ℂ → ℕ) (s ρ : ℂ) (h : ρ ∈ Z) (hm : 1 ≤ m ρ) :
    s - ρ ∈ dhFam Z m s := by
  unfold dhFam
  rw [Multiset.mem_bind]
  exact ⟨ρ, h, Multiset.mem_replicate.2 ⟨by omega, rfl⟩⟩

theorem dhFlat (S : Multiset ℂ) : ∃ (N : ℕ) (w : Fin N → ℂ), Finset.univ.val.map w = S := by
  refine ⟨S.toList.length, S.toList.get, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]

theorem dhFlat_sum {β : Type*} [AddCommMonoid β] {N : ℕ} (w : Fin N → ℂ) (S : Multiset ℂ)
    (h : Finset.univ.val.map w = S) (g : ℂ → β) : ∑ i, g (w i) = (S.map g).sum := by
  rw [← h, Multiset.map_map]
  rfl

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem meansq_split (I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (r : ℕ → ℕ → ℕ) (A : ℕ → ℕ → ℝ)
    (P η : ℝ) (hP : 0 ≤ P) (hη : 0 ≤ η) (nstar : ℕ)
    (hA : ∀ n ∈ I, ∀ n' ∈ I, A n n' ≤ P)
    (hA' : ∀ n ∈ I, ∀ n' ∈ I, r n n' ≠ 1 → r n n' ≠ nstar → A n n' ≤ η * P) :
    ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n' ≤
      ((∑ n ∈ I, ∑ n' ∈ I, if r n n' = 1 then c n * c n' else 0) +
        (∑ n ∈ I, ∑ n' ∈ I, if r n n' = nstar then c n * c n' else 0) + η * (∑ n ∈ I, c n) ^ 2) * P := by
  have hpt : ∀ n ∈ I, ∀ n' ∈ I, c n * c n' * A n n' ≤
      ((if r n n' = 1 then c n * c n' else 0) + (if r n n' = nstar then c n * c n' else 0) +
        η * (c n * c n')) * P := by
    intro n hn n' hn'
    have hcc : 0 ≤ c n * c n' := mul_nonneg (hc n) (hc n')
    have hAP := mul_le_mul_of_nonneg_left (hA n hn n' hn') hcc
    have hηP : 0 ≤ η * (c n * c n') * P := mul_nonneg (mul_nonneg hη hcc) hP
    have hccP : 0 ≤ c n * c n' * P := mul_nonneg hcc hP
    split_ifs with h1 h2 h2
    · linarith
    · linarith
    · linarith
    · have hA2 := mul_le_mul_of_nonneg_left (hA' n hn n' hn' h1 h2) hcc
      linarith
  calc ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n'
      ≤ ∑ n ∈ I, ∑ n' ∈ I, ((if r n n' = 1 then c n * c n' else 0) +
          (if r n n' = nstar then c n * c n' else 0) + η * (c n * c n')) * P :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => hpt n hn n' hn'
    _ = _ := by
        rw [sq, Finset.sum_mul_sum]
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section

open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem pow_key (x : ℝ) (hx0 : 0 < x) (a k : ℕ) (hka : k ≤ a) :
    x ^ (a + k) ≤ (5 * x) ^ a * (x / 5) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hka
  have hx : (5 * x) ^ (k + m) * (x / 5) ^ k = 5 ^ m * x ^ (k + m + k) := by
    rw [mul_pow, div_pow]
    field_simp
    ring
  rw [hx]
  have h1 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
  exact le_mul_of_one_le_left (by positivity) h1

theorem prodDist_step {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s S : Finset ι) (hS : S ⊆ s)
    (h3 : 3 * S.card ≤ s.card) (r ρ : ℝ) (hr : 0 < r)
    (hfar : ∀ j ∈ s, j ∉ S → r / 5 ≤ |ρ - t j|)
    (hin : ((r / 5) / 25) ^ S.card ≤ ∏ j ∈ S, |ρ - t j|) :
    (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by
  have hsplit : (∏ j ∈ s \ S, |ρ - t j|) * ∏ j ∈ S, |ρ - t j| = ∏ j ∈ s, |ρ - t j| :=
    Finset.prod_sdiff hS
  have hfar' : (r / 5) ^ (s \ S).card ≤ ∏ j ∈ s \ S, |ρ - t j| := by
    calc (r / 5) ^ (s \ S).card = ∏ _j ∈ s \ S, (r / 5) := (Finset.prod_const _).symm
      _ ≤ ∏ j ∈ s \ S, |ρ - t j| := by
        apply Finset.prod_le_prod₀
        · intro i _
          positivity
        · intro i hi
          rw [Finset.mem_sdiff] at hi
          exact hfar i hi.1 hi.2
  have hcard : (s \ S).card + S.card = s.card := Finset.card_sdiff_add_card_eq_card hS
  have hka : S.card ≤ (s \ S).card := by omega
  have key := pow_key (r / 25) (by positivity) (s \ S).card S.card hka
  calc (r / 25) ^ s.card = (r / 25) ^ ((s \ S).card + S.card) := by rw [hcard]
    _ ≤ (5 * (r / 25)) ^ (s \ S).card * (r / 25 / 5) ^ S.card := key
    _ = (r / 5) ^ (s \ S).card * ((r / 5) / 25) ^ S.card := by
        rw [show 5 * (r / 25) = r / 5 by ring, show r / 25 / 5 = r / 5 / 25 by ring]
    _ ≤ (∏ j ∈ s \ S, |ρ - t j|) * ∏ j ∈ S, |ρ - t j| :=
        mul_le_mul hfar' hin (by positivity)
          (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    _ = ∏ j ∈ s, |ρ - t j| := hsplit

private theorem exists_center_near_with_few_points_close {ι : Type*} (t : ι → ℝ) (s : Finset ι) (c r : ℝ)
    (hr : 0 < r) :
    ∃ c' : ℝ, |c' - c| ≤ 4 * r / 5 ∧
      3 * (s.filter (fun j => |t j - c'| < 2 * r / 5)).card ≤ s.card := by
  classical
  set S1 := s.filter (fun j => |t j - (c - 4 * r / 5)| < 2 * r / 5) with hS1
  set S2 := s.filter (fun j => |t j - c| < 2 * r / 5) with hS2
  set S3 := s.filter (fun j => |t j - (c + 4 * r / 5)| < 2 * r / 5) with hS3
  have d12 : Disjoint S1 S2 := by
    rw [hS1, hS2, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have d13 : Disjoint S1 S3 := by
    rw [hS1, hS3, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have d23 : Disjoint S2 S3 := by
    rw [hS2, hS3, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have hsub : S1 ∪ S2 ∪ S3 ⊆ s :=
    Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) (Finset.filter_subset _ _)
  have hsum : S1.card + S2.card + S3.card ≤ s.card := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨d13, d23⟩),
      Finset.card_union_of_disjoint d12] at h
  by_cases h1 : 3 * S1.card ≤ s.card
  · refine ⟨c - 4 * r / 5, ?_, h1⟩
    rw [abs_le]
    constructor <;> linarith
  by_cases h2 : 3 * S2.card ≤ s.card
  · refine ⟨c, ?_, h2⟩
    rw [abs_le]
    constructor <;> linarith
  · refine ⟨c + 4 * r / 5, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> linarith
    · have h3' : 3 * S3.card ≤ s.card := by omega
      exact h3'

theorem exists_far_from_points {ι : Type*} [DecidableEq ι] (t : ι → ℝ) :
    ∀ (N : ℕ) (s : Finset ι), s.card = N → ∀ (c r : ℝ), 0 < r →
      ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro s hs c r hr
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      rw [Finset.card_eq_zero] at hs
      subst hs
      refine ⟨c, by simp [hr.le], by simp⟩
    · obtain ⟨c', hc', h3⟩ := exists_center_near_with_few_points_close t s c r hr
      set S := s.filter (fun j => |t j - c'| < 2 * r / 5) with hSdef
      have hlt : S.card < N := by omega
      obtain ⟨ρ, hρ, hin⟩ := ih S.card hlt S rfl c' (r / 5) (by positivity)
      refine ⟨ρ, ?_, prodDist_step t s S (Finset.filter_subset _ _) h3 r ρ hr ?_ hin⟩
      · calc |ρ - c| ≤ |ρ - c'| + |c' - c| := abs_sub_le ρ c' c
          _ ≤ r / 5 + 4 * r / 5 := add_le_add hρ hc'
          _ = r := by ring
      · intro j hj hjS
        have hn : 2 * r / 5 ≤ |t j - c'| :=
          not_lt.mp (fun h => hjS (Finset.mem_filter.2 ⟨hj, h⟩))
        have htri : |t j - c'| ≤ |t j - ρ| + |ρ - c'| := abs_sub_le (t j) ρ c'
        rw [abs_sub_comm (t j) ρ] at htri
        linarith

theorem prodDist {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s : Finset ι) (c r : ℝ) (hr : 0 < r) :
    ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| :=
  exists_far_from_points t s.card s rfl c r hr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
end
end

section

open Finset Complex Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

def tp (n : ℕ) (z : Fin n → ℂ) : ℂ[X] := ∏ i, (X - C (z i))

theorem tp_natDeg (n : ℕ) (z : Fin n → ℂ) : (tp n z).natDegree ≤ n := by
  unfold tp
  exact (natDegree_prod_le _ _).trans (by simp [natDegree_X_sub_C])

theorem tp_eval (n : ℕ) (z : Fin n → ℂ) (x : ℂ) : (tp n z).eval x = ∏ i, (x - z i) := by
  simp [tp, eval_prod]

theorem tp_eval_sum (n : ℕ) (z : Fin n → ℂ) (x : ℂ) :
    (tp n z).eval x = ∑ a ∈ range (n + 1), (tp n z).coeff a * x ^ a :=
  eval_eq_sum_range' (Nat.lt_succ_of_le (tp_natDeg n z)) x

theorem tp_coeff_norm (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (a : ℕ) (ha : a ≤ n) :
    ‖(tp n z).coeff a‖ ≤ n.choose a := by
  classical
  set s : Multiset ℂ := Finset.univ.val.map z with hs
  have hcard : Multiset.card s = n := by simp [hs]
  have htp : tp n z = (s.map fun t => X - C t).prod := by
    rw [tp, Finset.prod_eq_multiset_prod, hs, Multiset.map_map]
    rfl
  have hprod : ∀ t : Multiset ℂ, (∀ x ∈ t, ‖x‖ ≤ 1) → ‖t.prod‖ ≤ 1 := by
    intro t
    induction t using Multiset.induction_on with
    | empty => intro _; simp
    | cons x t ih =>
      intro h
      rw [Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (h x (Multiset.mem_cons_self x t)) (norm_nonneg _)
        (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))
  have hmem : ∀ t ∈ s, ‖t‖ ≤ 1 := by
    intro t ht
    rw [hs, Multiset.mem_map] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact hz i
  rw [htp, Multiset.prod_X_sub_C_coeff s (by rw [hcard]; exact ha), hcard, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul, ← Nat.choose_symm ha, Multiset.esymm]
  calc ‖((s.powersetCard (n - a)).map Multiset.prod).sum‖
      ≤ (((s.powersetCard (n - a)).map Multiset.prod).map norm).sum := norm_multiset_sum_le _
    _ = ((s.powersetCard (n - a)).map fun t => ‖t.prod‖).sum := by rw [Multiset.map_map]; rfl
    _ ≤ ((s.powersetCard (n - a)).map fun _ => (1 : ℝ)).sum := by
        refine Multiset.sum_map_le_sum_map _ _ fun t ht => hprod t fun x hx => hmem x ?_
        exact Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hx
    _ = n.choose (n - a) := by simp [Multiset.card_powersetCard, hcard]

theorem tp_sum_norm (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ ≤ 2 ^ n := by
  calc ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ ≤ ∑ a ∈ range (n + 1), (n.choose a : ℝ) :=
        Finset.sum_le_sum fun a ha => tp_coeff_norm n z hz a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
    _ = 2 ^ n := by exact_mod_cast Nat.sum_range_choose n

theorem tp_rev (n : ℕ) (z : Fin n → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0) :
    ∏ i, (1 - z i * ζ) = ∑ a ∈ range (n + 1), (tp n z).coeff a * ζ ^ (n - a) := by
  have h1 : ∏ i, (1 - z i * ζ) = ζ ^ n * (tp n z).eval ζ⁻¹ := by
    rw [tp_eval, ← Fin.prod_const n ζ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_sub, mul_inv_cancel₀ hζ]
    ring
  rw [h1, tp_eval_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [inv_pow, pow_sub₀ _ hζ ha']
  ring

theorem tp_root (n : ℕ) (z : Fin n → ℂ) (i : Fin n) :
    ∑ a ∈ range (n + 1), (tp n z).coeff a * z i ^ a = 0 := by
  rw [← tp_eval_sum, tp_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
end
end

section

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem meansq_expand (PP I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (κ : ℕ → ℂ)
    (hκ : ∀ n, ‖κ n‖ ≤ 1) (J : ℕ → ℕ → ℤ) :
    (∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2) ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ)| := by
  have key : ((∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ I, ∑ n' ∈ I, ((c n : ℝ) : ℂ) * ((c n' : ℝ) : ℂ) * (κ n * (starRingEnd ℂ) (κ n')) *
        ((∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ) : ℝ) : ℂ) := by
    have h1 : ∀ q, ((‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        ∑ n ∈ I, ∑ n' ∈ I, ((c n : ℝ) : ℂ) * ((c n' : ℝ) : ℂ) * (κ n * (starRingEnd ℂ) (κ n')) *
          (((J n q * J n' q : ℤ) : ℝ) : ℂ) := by
      intro q

      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
      simp only [map_mul, Complex.conj_ofReal, map_intCast]
      push_cast
      ring
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [Complex.ofReal_sum, Finset.mul_sum]
  calc (∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2)
      ≤ ‖((∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real]; exact le_abs_self _
    _ ≤ ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ)| := by
        rw [key]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
          RCLike.norm_conj, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hc n),
          abs_of_nonneg (hc n')]
        have h2 : ‖κ n‖ * ‖κ n'‖ ≤ 1 := by
          have := mul_le_mul (hκ n) (hκ n') (norm_nonneg _) zero_le_one
          simpa using this
        have h3 : 0 ≤ c n * c n' := mul_nonneg (hc n) (hc n')
        have h4 : c n * c n' * (‖κ n‖ * ‖κ n'‖) ≤ c n * c n' := by
          simpa using mul_le_mul_of_nonneg_left h2 h3
        exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF

theorem u_disc (η : ℝ) (hη : 0 < η) (w : ℂ) (hw : η ≤ w.re) :
    ‖(η : ℂ) / w‖ ^ 2 ≤ ((η : ℂ) / w).re := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    linarith
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
  rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.div_re, Complex.normSq_ofReal,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  have h1 : η * η ≤ η * w.re := mul_le_mul_of_nonneg_left hw hη.le
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hn.le)

theorem u_sum_re (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) :
    (∑ i, ((η : ℂ) / w i) ^ j).re = η ^ j * (∑ i, 1 / (w i) ^ j).re := by
  have h : ∑ i, ((η : ℂ) / w i) ^ j = ((η ^ j : ℝ) : ℂ) * ∑ i, 1 / (w i) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow, div_eq_mul_one_div, Complex.ofReal_pow]
  rw [h, Complex.re_ofReal_mul]


end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
end
end

section

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_num_rpow (x ε : ℝ) (hx : 0 < x) :
    (x ^ 400) ^ (1 - 1 / 400 + ε / 1600 : ℝ) = x ^ 399 * x ^ (ε / 4) := by
  rw [← Real.rpow_natCast x 400, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x 399,
    ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

theorem tail_num_alg (x Q K l a g : ℝ) (hx : 0 < x) (hQ : 0 < Q) :
    x * ((K * l * (l * (1 / x ^ 2) * (x ^ 399 * a) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * g / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2)))
      = K * l ^ 2 * a + K * (l * x ^ 403 / Q) + (x ^ 398 + 1) * g / x ^ 399 := by
  have hx0 : x ≠ 0 := hx.ne'
  have hQ0 : Q ≠ 0 := hQ.ne'
  field_simp

theorem tail_num_third (x : ℝ) (hx : 3 ≤ x) :
    (x ^ 398 + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 399 ≤ 802 := by
  suffices h : ∀ n : ℕ,
      (x ^ n + 1) * Real.log (x ^ (n + 2) + x ^ (n + 2) * (1 / x ^ 2)) / x ^ (n + 1)
        ≤ 2 * ((n : ℝ) + 3) by
    have hbound : 2 * ((398 : ℝ) + 3) = 802 := by norm_num
    simpa only [Nat.reduceAdd, Nat.cast_ofNat, hbound] using h 398
  intro n
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hp : 0 < x ^ n := by positivity
  have hp1 : 1 ≤ x ^ n := one_le_pow₀ hx1
  have hA : x ^ (n + 2) + x ^ (n + 2) * (1 / x ^ 2) = x ^ n * (x ^ 2 + 1) := by
    rw [pow_add]
    field_simp
  have hsq : x ^ 2 + 1 ≤ x ^ 3 := by nlinarith
  have hsq_pos : 0 < x ^ 2 + 1 := by positivity
  have hlog_sq : Real.log (x ^ 2 + 1) ≤ 3 * Real.log x := by
    calc Real.log (x ^ 2 + 1) ≤ Real.log (x ^ 3) := Real.log_le_log hsq_pos hsq
      _ = 3 * Real.log x := by rw [Real.log_pow]; norm_num
  have hlog_x : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
  have hL1 : Real.log (x ^ n * (x ^ 2 + 1)) ≤ ((n : ℝ) + 3) * x := by
    rw [Real.log_mul hp.ne' hsq_pos.ne', Real.log_pow]
    calc (n : ℝ) * Real.log x + Real.log (x ^ 2 + 1)
        ≤ (n : ℝ) * Real.log x + 3 * Real.log x := add_le_add le_rfl hlog_sq
      _ = ((n : ℝ) + 3) * Real.log x := by ring
      _ ≤ ((n : ℝ) + 3) * x := mul_le_mul_of_nonneg_left hlog_x (by positivity)
  have hxn : x ≤ x ^ (n + 1) := by
    simpa only [pow_succ, one_mul] using mul_le_mul_of_nonneg_right hp1 hx0.le
  rw [hA, div_le_iff₀ (by positivity : (0 : ℝ) < x ^ (n + 1))]
  calc (x ^ n + 1) * Real.log (x ^ n * (x ^ 2 + 1))
      ≤ (x ^ n + 1) * (((n : ℝ) + 3) * x) := mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = ((n : ℝ) + 3) * (x ^ (n + 1) + x) := by rw [pow_succ]; ring
    _ ≤ ((n : ℝ) + 3) * (x ^ (n + 1) + x ^ (n + 1)) := by gcongr
    _ = 2 * ((n : ℝ) + 3) * x ^ (n + 1) := by ring

end Formalism.HermitianLattices.Ext.BoxTail
end
end
