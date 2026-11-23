module

public import Formalism.SubspaceCounting.Bundle001
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Tactic.Continuity
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

section

namespace Formalism.G0

namespace QVandermondeP

theorem gb_zero_right (q n : ℕ) : gaussBinom q n 0 = 1 := by
  cases n <;> rfl

theorem gb_zero_succ (q k : ℕ) : gaussBinom q 0 (k + 1) = 0 := rfl

theorem gb_succ_succ (q n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) :=
  rfl

theorem gb_eq_zero (q : ℕ) : ∀ n k : ℕ, n < k → gaussBinom q n k = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [gb_succ_succ, gb_eq_zero q n k (by omega), gb_eq_zero q n (k + 1) (by omega)]
    simp

theorem form2 (q m : ℕ) : ∀ g n : ℕ, gaussBinom q (m + g) n =
    ∑ l ∈ Finset.range (n + 1),
      q ^ ((n - l) * (g - l)) * gaussBinom q m (n - l) * gaussBinom q g l := by
  intro g
  induction g with
  | zero =>
    intro n
    rw [Finset.sum_range_succ']
    simp [gb_zero_succ, gb_zero_right]
  | succ g ih =>
    intro n
    cases n with
    | zero => simp [gb_zero_right]
    | succ k =>
      show gaussBinom q ((m + g) + 1) (k + 1) = _
      rw [gb_succ_succ, ih k, ih (k + 1)]
      rw [Finset.sum_range_succ' _ (k + 1), Finset.sum_range_succ' _ (k + 1)]
      have h1 : ∀ l ∈ Finset.range (k + 1),
          q ^ ((k + 1 - (l + 1)) * (g + 1 - (l + 1))) * gaussBinom q m (k + 1 - (l + 1)) *
              gaussBinom q (g + 1) (l + 1) =
            q ^ ((k - l) * (g - l)) * gaussBinom q m (k - l) * gaussBinom q g l +
              q ^ (k + 1) * (q ^ ((k + 1 - (l + 1)) * (g - (l + 1))) *
                gaussBinom q m (k + 1 - (l + 1)) * gaussBinom q g (l + 1)) := by
        intro l hl
        have hl' : l ≤ k := by
          have := Finset.mem_range.mp hl
          omega
        rw [gb_succ_succ]
        simp only [Nat.add_sub_add_right]
        rcases Nat.lt_or_ge g (l + 1) with h | h
        · rw [gb_eq_zero q g (l + 1) h]
          ring
        · obtain ⟨a, rfl⟩ : ∃ a, k = l + a := ⟨k - l, by omega⟩
          obtain ⟨b, rfl⟩ : ∃ b, g = l + 1 + b := ⟨g - (l + 1), by omega⟩
          have e1 : l + a - l = a := by omega
          have e2 : l + 1 + b - l = b + 1 := by omega
          have e3 : l + 1 + b - (l + 1) = b := by omega
          rw [e1, e2, e3]
          ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
      simp only [Nat.sub_zero, gb_zero_right]
      ring

end QVandermondeP

end Formalism.G0
end

section

noncomputable section

open Finset

namespace Formalism.G0

namespace TopsConditionalProbabilityWindows


open Classical in
def P (U : Finset ℕ) (δ : ℝ) (A : Finset ℕ → Prop) : ℝ :=
  by classical exact ∑ t ∈ U.powerset, if A t then δ ^ t.card * (1 - δ) ^ (U.card - t.card) else 0

theorem key (n L K : ℕ) (t : Finset ℕ) (h0t : 0 ∉ t) (h : ¬ CondA n (insert 0 t) L K) :
    ∃ i ∈ range n, ∃ S ∈ powersetCard (if 0 ∈ window n i L then K else K + 1)
      ((window n i L).erase 0), S ⊆ t := by
  classical
  unfold CondA at h
  push Not at h
  obtain ⟨i, hi, hK⟩ := h
  refine ⟨i, mem_range.2 hi, ?_⟩
  set W := window n i L
  set s := t ∩ W.erase 0 with hs_def
  have hm : (if 0 ∈ W then K else K + 1) ≤ s.card := by
    by_cases hw : 0 ∈ W
    · rw [if_pos hw]
      have hsub : insert 0 t ∩ W ⊆ insert 0 s := by
        intro x hx
        rcases mem_inter.1 hx with ⟨hx1, hx2⟩
        rcases mem_insert.1 hx1 with rfl | hxt
        · exact mem_insert_self _ _
        · refine mem_insert_of_mem (mem_inter.2 ⟨hxt, mem_erase.2 ⟨?_, hx2⟩⟩)
          rintro rfl
          exact h0t hxt
      have := (card_le_card hsub).trans (card_insert_le 0 s)
      omega
    · rw [if_neg hw]
      have hsub : insert 0 t ∩ W ⊆ s := by
        intro x hx
        rcases mem_inter.1 hx with ⟨hx1, hx2⟩
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hw hx2
        rcases mem_insert.1 hx1 with hx | hxt
        · exact absurd hx hx0
        · exact mem_inter.2 ⟨hxt, mem_erase.2 ⟨hx0, hx2⟩⟩
      have := card_le_card hsub
      omega
  obtain ⟨S, hSs, hSc⟩ := exists_subset_card_eq hm
  refine ⟨S, mem_powersetCard.2 ⟨?_, hSc⟩, ?_⟩
  · exact fun x hx => (mem_inter.1 (hSs hx)).2
  · exact fun x hx => (mem_inter.1 (hSs hx)).1

end TopsConditionalProbabilityWindows


end Formalism.G0
end
end

section

noncomputable section

open scoped BigOperators

namespace Formalism.G0

namespace ManyOrbitsP

theorem add_pow_ge (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (k : ℕ) :
    p ^ (k + 1) + ((k : ℝ) + 1) * q * p ^ k ≤ (p + q) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpq : 0 ≤ p + q := add_nonneg hp hq
    have h1 := mul_le_mul_of_nonneg_left ih hpq
    have h2 : 0 ≤ ((k : ℝ) + 1) * q ^ 2 * p ^ k := by positivity
    have e : (p + q) * (p ^ (k + 1) + ((k : ℝ) + 1) * q * p ^ k) -
        (p ^ (k + 1 + 1) + (((k : ℝ) + 1) + 1) * q * p ^ (k + 1)) = ((k : ℝ) + 1) * q ^ 2 * p ^ k := by
      ring
    have e2 : (p + q) * (p + q) ^ (k + 1) = (p + q) ^ (k + 1 + 1) := by ring
    push_cast
    linarith

theorem fact_esymm_le (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (n : ℕ) :
    (n.factorial : ℝ) * s.esymm n ≤ s.sum ^ n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n =>
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]
      simp
  | cons a t ih =>
    have ha : 0 ≤ a := hs a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have hS : 0 ≤ t.sum := Multiset.sum_nonneg ht
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n =>
      have e : (a ::ₘ t).esymm (n + 1) = t.esymm (n + 1) + a * t.esymm n := by
        simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
      have h1 := ih ht (n + 1)
      have h2 := ih ht n
      have h3 := add_pow_ge t.sum a hS ha n
      have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) * a)
      rw [e, Multiset.sum_cons, add_comm a t.sum]
      rw [Nat.factorial_succ] at h1 ⊢
      push_cast at h1 ⊢
      have e5 : ((n : ℝ) + 1) * (n.factorial : ℝ) * (t.esymm (n + 1) + a * t.esymm n) =
          ((n : ℝ) + 1) * (n.factorial : ℝ) * t.esymm (n + 1) + ((n : ℝ) + 1) * a * ((n.factorial : ℝ) * t.esymm n) := by
        ring
      linarith [h1, h3, h4, e5]

section Mod

variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]

theorem allBut_mono {π : R} {M P : Submodule R X} {g g' E E' : ℕ} (h : AllButLE π M P g E)
    (hg : g ≤ g') (hE : E ≤ E') : AllButLE π M P g' E' := by
  obtain ⟨C, hCM, hcard, hC⟩ := h
  refine ⟨C, hCM, hcard.trans hg, fun x hx => ?_⟩
  have := Submodule.smul_mem _ (π ^ (E' - E)) (hC x hx)
  rwa [smul_smul, ← pow_add, Nat.sub_add_cancel hE] at this

end Mod

end ManyOrbitsP

end Formalism.G0
end
end

section

noncomputable section

open scoped BigOperators
open Module

namespace Formalism.G0

namespace SubspaceCountP

theorem gb_zero_right (q n : ℕ) : gaussBinom q n 0 = 1 := by
  cases n <;> rfl

theorem gb_succ_succ (q n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) :=
  rfl

theorem gb_eq_zero (q : ℕ) : ∀ n k : ℕ, n < k → gaussBinom q n k = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [gb_succ_succ, gb_eq_zero q n k (by omega), gb_eq_zero q n (k + 1) (by omega)]
    simp

def P (q : ℤ) (m k : ℕ) : ℤ := ∏ i ∈ Finset.range k, (q ^ m - q ^ i)

theorem P_succ_right (q : ℤ) (m k : ℕ) : P q m (k + 1) = P q m k * (q ^ m - q ^ k) := by
  unfold P; rw [Finset.prod_range_succ]

theorem P_succ_succ (q : ℤ) (m k : ℕ) :
    P q (m + 1) (k + 1) = (q ^ (m + 1) - 1) * (q ^ k * P q m k) := by
  unfold P
  rw [Finset.prod_range_succ', pow_zero, mul_comm]
  congr 1
  rw [← Finset.card_range k, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

theorem gb_mul_P (q : ℤ) (qn : ℕ) (hq : (qn : ℤ) = q) :
    ∀ n k : ℕ, (gaussBinom qn n k : ℤ) * P q k k = P q n k := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => simp [P, gb_zero_right]
    | succ k =>
      have : P q 0 (k + 1) = 0 := by
        unfold P
        exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos k)) (by simp)
      rw [this]; simp [gaussBinom]
  | succ n ih =>
    intro k
    cases k with
    | zero => simp [P, gb_zero_right]
    | succ k =>
      rw [gb_succ_succ]
      push_cast
      rw [hq]
      have h1 := ih k
      have h2 := ih (k + 1)
      rw [P_succ_succ q k k, P_succ_succ q n k]
      rw [P_succ_succ q k k, P_succ_right] at h2
      linear_combination (q ^ (k + 1) - 1) * q ^ k * h1 + q ^ (k + 1) * h2

end SubspaceCountP

namespace SubspaceCountP

abbrev LI (F V : Type) [Field F] [AddCommGroup V] [Module F V] (k : ℕ) :=
  {s : Fin k → V // LinearIndependent F s}

abbrev Gr (F W : Type) [Field F] [AddCommGroup W] [Module F W] (k : ℕ) :=
  {U : Submodule F W // finrank F U = k}

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W]

def spanMap (k : ℕ) (s : LI F W k) : Gr F W k :=
  ⟨Submodule.span F (Set.range s.1), (finrank_span_eq_card s.2).trans (Fintype.card_fin k)⟩

variable [Finite W]

def fiberEquiv (k : ℕ) (U : Gr F W k) : {s : LI F W k // spanMap k s = U} ≃ LI F U.1 k where
  toFun s := ⟨fun i => ⟨s.1.1 i, by
      have h := congrArg Subtype.val s.2
      simp only [spanMap] at h
      rw [← h]
      exact Submodule.subset_span ⟨i, rfl⟩⟩, by
      apply LinearIndependent.of_comp U.1.subtype
      exact s.1.2⟩
  invFun t := ⟨⟨U.1.subtype ∘ t.1, t.2.map' _ (Submodule.ker_subtype _)⟩, by
      apply Subtype.ext
      apply Submodule.eq_of_le_of_finrank_eq
      · show Submodule.span F (Set.range (U.1.subtype ∘ t.1)) ≤ U.1
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (t.1 i).2
      · rw [(spanMap k _).2, U.2]⟩
  left_inv s := rfl
  right_inv t := rfl

end SubspaceCountP

namespace SubspaceCountP

variable {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W]

theorem card_LI_eq (k : ℕ) :
    Nat.card (LI F W k) =
      Nat.card (Gr F W k) * ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by
  classical
  let _ := Fintype.ofFinite (Gr F W k)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (spanMap (F := F) (W := W) k)), Nat.card_sigma]
  have h : ∀ U : Gr F W k, Nat.card {s // spanMap k s = U} =
      ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by
    intro U
    rw [Nat.card_congr (fiberEquiv k U), card_linearIndependent (by rw [U.2]), U.2]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem cast_prod_eq_P (q m k : ℕ) (hq : 1 ≤ q) (hm : k ≤ m) :
    ((∏ i : Fin k, (q ^ m - q ^ i.val) : ℕ) : ℤ) = P (q : ℤ) m k := by
  rw [Nat.cast_prod, P, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  rfl

end SubspaceCountP

open SubspaceCountP in
theorem countSubspacesEq : SubspaceCount := by
  intro F W _ _ _ _ _ k
  classical
  have hcount : countBelow (⊤ : Submodule F W) k = Nat.card (Gr F W k) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => by simp))
  rw [hcount]
  rcases lt_or_ge (finrank F W) k with hnk | hkn
  · rw [gb_eq_zero _ _ _ hnk, Nat.card_eq_zero]
    left
    constructor
    rintro ⟨U, hU⟩
    have := Submodule.finrank_le U
    omega
  · have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have h1 := card_LI_eq (F := F) (W := W) k
    rw [card_linearIndependent hkn] at h1
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h1
    rw [Nat.cast_mul, cast_prod_eq_P _ _ _ hq.le hkn, cast_prod_eq_P _ _ _ hq.le le_rfl] at h2
    have h3 := gb_mul_P (Fintype.card F : ℤ) (Fintype.card F) rfl (finrank F W) k
    have hP : P (Fintype.card F : ℤ) k k ≠ 0 := by
      unfold P
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      have : (Fintype.card F : ℤ) ^ i < (Fintype.card F : ℤ) ^ k :=
        pow_lt_pow_right₀ (by exact_mod_cast hq) (Finset.mem_range.mp hi)
      omega
    have : (Nat.card (Gr F W k) : ℤ) = gaussBinom (Fintype.card F) (finrank F W) k :=
      mul_right_cancel₀ hP (h2.symm.trans h3.symm)
    exact_mod_cast this

end Formalism.G0
end
end
