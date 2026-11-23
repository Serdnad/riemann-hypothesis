module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

section

open Matrix Finset Real

namespace GlobalTheory

namespace ZetaProd

theorem zeta_le (l K : ℕ) (hK : 0 < K) :
    (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ (l + 2)) ≤
      (∑ m ∈ Finset.range K, 1 / ((m : ℝ) + 1) ^ (l + 2)) + 1 / ((K : ℝ) + 1) ^ l * (1 / K) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have key : ∀ n : ℕ, (∑ m ∈ Finset.range (K + n), 1 / ((m : ℝ) + 1) ^ (l + 2)) ≤
      (∑ m ∈ Finset.range K, 1 / ((m : ℝ) + 1) ^ (l + 2)) +
        1 / ((K : ℝ) + 1) ^ l * (1 / K - 1 / ((K : ℝ) + n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, Finset.sum_range_succ]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : 1 / (((K + n : ℕ) : ℝ) + 1) ^ (l + 2) ≤
          1 / ((K : ℝ) + 1) ^ l * (1 / ((K : ℝ) + n) - 1 / ((K : ℝ) + (n + 1 : ℕ))) := by
        push_cast
        have e : 1 / ((K : ℝ) + n) - 1 / ((K : ℝ) + (n + 1)) =
            1 / (((K : ℝ) + n) * ((K : ℝ) + n + 1)) := by
          field_simp
          ring
        rw [e, one_div_mul_one_div]
        apply one_div_le_one_div_of_le (by positivity)
        rw [pow_add]
        apply mul_le_mul
        · apply pow_le_pow_left₀ (by positivity)
          linarith
        · nlinarith
        · positivity
        · positivity
      nlinarith
  apply Real.tsum_le_of_sum_range_le (fun m => by positivity)
  intro n
  have h2 : (∑ m ∈ Finset.range n, 1 / ((m : ℝ) + 1) ^ (l + 2)) ≤
      ∑ m ∈ Finset.range (K + n), 1 / ((m : ℝ) + 1) ^ (l + 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro i _ _
      positivity
  have h3 : 0 ≤ 1 / ((K : ℝ) + 1) ^ l * (1 / ((K : ℝ) + n)) := by positivity
  have := key n
  nlinarith

theorem zeta_nonneg (l : ℕ) : 0 ≤ ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l :=
  tsum_nonneg (fun m => by positivity)

theorem zeta_two_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2) ≤ 1.645 := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  have h2 : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    simpa using h
  rw [h2.tsum_eq]
  have := Real.pi_lt_d4
  have := Real.pi_pos
  nlinarith

theorem zeta_three_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 3) ≤ 1.2027 :=
  (zeta_le 1 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_four_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 4) ≤ 1.0825 :=
  (zeta_le 2 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_five_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 5) ≤ 1.0370 :=
  (zeta_le 3 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_six_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 6) ≤ 1.0174 :=
  (zeta_le 4 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_seven_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 7) ≤ 1.0084 :=
  (zeta_le 5 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_eight_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 8) ≤ 1.0041 :=
  (zeta_le 6 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_tail_le (n : ℕ) :
    (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ (n + 9)) ≤ 1 + 0.00235 * (1 / 2) ^ n := by
  refine (zeta_le (n + 7) 2 (by norm_num)).trans ?_
  have h : (1 / 3 : ℝ) ^ n ≤ (1 / 2) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have e1 : 1 / ((1 : ℝ) + 1) ^ (n + 7 + 2) = (1 / 2) ^ n / 512 := by
    rw [_root_.one_div_pow, add_assoc, pow_add]; norm_num; ring
  have e2 : 1 / ((2 : ℝ) + 1) ^ (n + 7) = (1 / 3) ^ n / 2187 := by
    rw [_root_.one_div_pow, pow_add]; norm_num; ring
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, zero_add, one_pow]
  rw [e1, e2]
  have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  linarith

theorem prod_three_eight (N : ℕ) (hN : N ≤ 8) :
    ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤ 1.391 := by
  have hb : ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤
      ∏ l ∈ Finset.Icc 3 N, (if l = 3 then (1.2027 : ℝ) else if l = 4 then 1.0825 else
        if l = 5 then 1.0370 else if l = 6 then 1.0174 else if l = 7 then 1.0084
        else 1.0041) := by
    apply Finset.prod_le_prod₀ (fun l _ => zeta_nonneg l)
    intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨h1, h2⟩ := hl
    have h3 : l ≤ 8 := h2.trans hN
    interval_cases l
    · simpa using zeta_three_le
    · simpa using zeta_four_le
    · simpa using zeta_five_le
    · simpa using zeta_six_le
    · simpa using zeta_seven_le
    · simpa using zeta_eight_le
  refine hb.trans ?_
  interval_cases N <;> norm_num [Finset.prod_Icc_succ_top]

theorem prod_three_tail (n : ℕ) :
    ∏ l ∈ Finset.Icc 3 (n + 8), (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤
      1.398 * (1 - 0.0047 * (1 / 2) ^ n) := by
  induction n with
  | zero =>
    refine (prod_three_eight 8 le_rfl).trans ?_
    norm_num
  | succ n ih =>
    rw [show n + 1 + 8 = (n + 8) + 1 by ring, Finset.prod_Icc_succ_top (by omega)]
    have h1 := zeta_tail_le n
    have hx : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    have hx1 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    refine (mul_le_mul ih h1 (zeta_nonneg _) (by nlinarith)).trans ?_
    rw [pow_succ]
    nlinarith [mul_nonneg hx hx]

theorem prod_three_le (N : ℕ) :
    ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤ 1.398 := by
  rcases le_total N 8 with h | h
  · exact (prod_three_eight N h).trans (by norm_num)
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 8 := ⟨N - 8, by omega⟩
    refine (prod_three_tail n).trans ?_
    have hx : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    nlinarith

theorem prod_two_lt (N : ℕ) :
    ∏ l ∈ Finset.Icc 2 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) < 2.3 := by
  rcases lt_or_ge N 2 with h | h
  · rw [Finset.Icc_eq_empty (by omega)]
    norm_num
  · have e : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [e, Finset.prod_insert (by simp)]
    refine (mul_le_mul zeta_two_le (prod_three_le N)
      (Finset.prod_nonneg fun l _ => zeta_nonneg l) (by norm_num)).trans_lt ?_
    norm_num

theorem sphere_le (l : ℕ) (hl : 1 ≤ l) :
    2 * Real.pi ^ l / ((l - 1).factorial : ℝ) ≤ 32.5 := by
  have h1 := Real.pi_lt_d4
  have h0 := Real.pi_pos
  have hp : ∀ k : ℕ, π ^ k ≤ (3.1416 : ℝ) ^ k := fun k => pow_le_pow_left₀ h0.le h1.le k
  have tail : ∀ n : ℕ, 2 * Real.pi ^ (n + 4) / ((n + 3).factorial : ℝ) ≤ 32.5 := by
    intro n
    induction n with
    | zero =>
      have := hp 4
      norm_num [Nat.factorial] at this ⊢
      linarith
    | succ n ih =>
      refine le_trans ?_ ih
      have hf : (0 : ℝ) < ((n + 3).factorial : ℝ) := by positivity
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [show n + 1 + 3 = (n + 3) + 1 by ring, Nat.factorial_succ,
        show n + 1 + 4 = (n + 4) + 1 by ring, pow_succ]
      push_cast
      rw [div_le_div_iff₀ (by positivity) hf]
      have hq : 0 ≤ 2 * π ^ (n + 4) * ((n + 3).factorial : ℝ) := by positivity
      have : π ≤ (n : ℝ) + 3 + 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hq]
  rcases le_or_gt 4 l with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, l = n + 4 := ⟨l - 4, by omega⟩
    exact tail n
  · have := hp l
    interval_cases l <;> norm_num [Nat.factorial] at this ⊢ <;> linarith

end ZetaProd

theorem zetaProd_sphereVolume_bounds :
    (∀ N : ℕ, ∏ l ∈ Finset.Icc 2 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) < 2.3) ∧
    (∀ N : ℕ, ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) < 1.4) ∧
    ∀ l : ℕ, 1 ≤ l → 2 * Real.pi ^ l / ((l - 1).factorial : ℝ) ≤ 32.5 :=
  ⟨ZetaProd.prod_two_lt, fun N => (ZetaProd.prod_three_le N).trans_lt (by norm_num),
    ZetaProd.sphere_le⟩

end GlobalTheory
end

section

open Finset

namespace GlobalTheory

theorem card_le_prod_of_separated_levels {α β : Type} (S : Set α) (lv : β → ℕ)
    (r : β → α → α → Prop) (B : β → ℝ) (hr : ∀ b, Equivalence (r b)) (s : Finset β) :
    (∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S →
      (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) →
      (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b) →
    ∀ T : Finset α, (↑T : Set α) ⊆ S → (∀ x ∈ T, ∀ y ∈ T, (∀ b ∈ s, r b x y) → x = y) →
      (T.card : ℝ) ≤ ∏ b ∈ s, B b := by
  classical
  induction s using Finset.induction_on_max_value lv with
  | empty =>
    intro _ T _ hT
    have : T.card ≤ 1 := Finset.card_le_one.2 fun x hx y hy => hT x hx y hy (by simp)
    simpa using this
  | insert a s ha hmax ih =>
    intro hp T hTS hT
    have hps : ∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S →
        (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) →
        (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b := by
      intro b hb T' h1 h2 h3
      refine hp b (mem_insert_of_mem hb) T' h1 ?_ h3
      intro x hx y hy b' hb' hlt
      rcases mem_insert.1 hb' with rfl | hb'
      · exact absurd (hmax b hb) (by omega)
      · exact h2 x hx y hy b' hb' hlt
    have hBa : 0 ≤ B a := by
      simpa using hp a (mem_insert_self _ _) ∅ (by simp) (by simp) (by simp)
    rw [prod_insert ha]
    rcases T.eq_empty_or_nonempty with rfl | ⟨x0, -⟩
    · have := ih hps ∅ (by simp) (by simp)
      simp only [card_empty, Nat.cast_zero] at this ⊢
      positivity
    haveI : Nonempty α := ⟨x0⟩
    let q : α → Set α := fun x => {y | ∀ b ∈ s, r b x y}
    have hq : ∀ x y, q x = q y ↔ ∀ b ∈ s, r b x y := by
      intro x y
      constructor
      · intro h
        have : y ∈ q y := fun b _ => (hr b).refl y
        rw [← h] at this
        exact this
      · intro h
        ext z
        exact ⟨fun hz b hb => (hr b).trans ((hr b).symm (h b hb)) (hz b hb),
          fun hz b hb => (hr b).trans (h b hb) (hz b hb)⟩
    let ρ : α → α := fun x => Function.invFunOn q (↑T : Set α) (q x)
    have hρ : ∀ x ∈ T, ρ x ∈ T ∧ q (ρ x) = q x := fun x hx =>
      Function.invFunOn_pos (f := q) (s := (↑T : Set α)) ⟨x, hx, rfl⟩
    have him : ((T.image ρ).card : ℝ) ≤ ∏ b ∈ s, B b := by
      refine ih hps _ ?_ ?_
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_coe.1 hz)
        exact hTS (hρ x hx).1
      · intro z hz w hw h
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
        obtain ⟨y, hy, rfl⟩ := mem_image.1 hw
        have h' := (hq _ _).2 h
        rw [(hρ x hx).2, (hρ y hy).2] at h'
        simp only [ρ, h']
    have hfib : ∀ z ∈ T.image ρ, ((T.filter (fun x => ρ x = z)).card : ℝ) ≤ B a := by
      intro z _
      have key : ∀ x ∈ T.filter (fun x => ρ x = z), ∀ y ∈ T.filter (fun x => ρ x = z),
          ∀ b ∈ s, r b x y := by
        intro x hx y hy
        obtain ⟨hx, hx'⟩ := mem_filter.1 hx
        obtain ⟨hy, hy'⟩ := mem_filter.1 hy
        rw [← hq, ← (hρ x hx).2, ← (hρ y hy).2, hx', hy']
      refine hp a (mem_insert_self _ _) _ ?_ ?_ ?_
      · intro x hx
        exact hTS (mem_filter.1 (mem_coe.1 hx)).1
      · intro x hx y hy b' hb' hlt
        rcases mem_insert.1 hb' with rfl | hb'
        · exact absurd hlt (lt_irrefl _)
        · exact key x hx y hy b' hb'
      · intro x hx y hy h
        refine hT x (mem_filter.1 hx).1 y (mem_filter.1 hy).1 ?_
        intro b hb
        rcases mem_insert.1 hb with rfl | hb
        · exact h
        · exact key x hx y hy b hb
    rw [Finset.card_eq_sum_card_image ρ T]
    push_cast
    calc ∑ z ∈ T.image ρ, ((T.filter (fun x => ρ x = z)).card : ℝ)
        ≤ ∑ _z ∈ T.image ρ, B a := sum_le_sum hfib
      _ = B a * ((T.image ρ).card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ B a * ∏ b ∈ s, B b := mul_le_mul_of_nonneg_left him hBa

theorem finite_and_ncard_le_prod_of_levels :
    ∀ (α β : Type) (S : Set α) (s : Finset β) (lv : β → ℕ) (r : β → α → α → Prop) (B : β → ℝ), (∀ b, Equivalence (r b)) → (∀ x ∈ S, ∀ y ∈ S, (∀ b ∈ s, r b x y) → x = y) → (∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S → (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) → (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b) → S.Finite ∧ ((S.ncard : ℕ) : ℝ) ≤ ∏ b ∈ s, B b := by
  intro α β S s lv r B hr hinj hp
  have h : ∀ T : Finset α, (↑T : Set α) ⊆ S → (T.card : ℝ) ≤ ∏ b ∈ s, B b := fun T hT =>
    card_le_prod_of_separated_levels S lv r B hr s hp T hT
      fun x hx y hy => hinj x (hT hx) y (hT hy)
  have hS : S.Finite := by
    by_contra hinf
    obtain ⟨n, hn⟩ := exists_nat_gt (∏ b ∈ s, B b)
    obtain ⟨T, hT, hc⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have := h T hT
    rw [hc] at this
    linarith
  refine ⟨hS, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hS]
  exact h _ (by simp)

end GlobalTheory
end

section

open scoped ENNReal Classical

namespace GlobalTheory

theorem sum_fibre_two_index_bound : ∀ (α Θ : Type) (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ) (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ), (∀ a ∈ S, 0 ≤ f a) → (∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a)) → (∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) → ENNReal.ofReal (∑ a ∈ S, f a) ≤ ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
  intro α Θ S xf yf Φ Tr f B₁ B₂ R₁ R₂ hf hR hB
  rw [ENNReal.ofReal_sum_of_nonneg hf]
  have h1 : ∑ a ∈ S, ENNReal.ofReal (f a) = ∑ x ∈ R₁, ∑ y ∈ R₂,
      ∑ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y), ENNReal.ofReal (f a) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := xf) (t := R₁) (fun a ha => (hR a ha).1)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_fiberwise_of_maps_to (g := yf) (t := R₂)
      (fun a ha => (hR a (Finset.mem_filter.1 ha).1).2.1)]
  rw [h1]
  refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
  have hmem : ∀ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y),
      a ∈ S ∧ xf a = x ∧ yf a = y := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    exact ⟨ha.1.1, ha.1.2, ha.2⟩
  generalize hS' : (S.filter (fun a => xf a = x)).filter (fun a => yf a = y) = S' at hmem ⊢
  rw [← Finset.sum_fiberwise_of_maps_to (g := Φ) (t := S'.image Φ)
    (fun a ha => Finset.mem_image_of_mem Φ ha)]
  have hfib : ∀ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ENNReal.ofReal (B₁ x * B₂ y) := by
    intro t ht
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨ha₀S, hx₀, hy₀⟩ := hmem a₀ ha₀
    have hsub : S'.filter (fun a => Φ a = Φ a₀)
        = S.filter (fun b => Φ b = Φ a₀ ∧ xf b = xf a₀ ∧ yf b = yf a₀) := by
      subst hS'
      ext b
      simp only [Finset.mem_filter]
      rw [hx₀, hy₀]
      tauto
    rw [hsub, ← ENNReal.ofReal_sum_of_nonneg (fun b hb => hf b (Finset.mem_filter.1 hb).1)]
    exact (ENNReal.ofReal_le_ofReal (hB a₀ ha₀S)).trans_eq (by rw [hx₀, hy₀])
  calc ∑ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ∑ t ∈ S'.image Φ, ENNReal.ofReal (B₁ x * B₂ y) := Finset.sum_le_sum hfib
    _ = ((S'.image Φ).card : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      gcongr
      have hsubT : ((S'.image Φ : Finset Θ) : Set Θ) ⊆ Tr x y := by
        intro t ht
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
        obtain ⟨haS, hxa, hya⟩ := hmem a ha
        have h := (hR a haS).2.2
        rw [hxa, hya] at h
        exact h
      have hc := Set.encard_le_encard hsubT
      rw [Set.encard_coe_eq_coe_finsetCard] at hc
      rw [← ENat.toENNReal_coe]
      exact ENat.toENNReal_le.2 hc

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem exists_measurableSet_slice_of_transversal
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (σ : G → G)
    (hN : MeasurableSet (N : Set G)) (hM : MeasurableSet (M : Set G))
    (hK : MeasurableSet (K : Set G)) (hσ : Measurable σ)
    (h1 : ∀ x, σ x * x⁻¹ ∈ K ⊓ M) (h2 : ∀ l ∈ K ⊓ M, ∀ x, σ (l * x) = σ x)
    (h3 : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N)
    (h4 : ∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1)
    (DN DM : Set G) (hDN : MeasurableSet DN) (hDM : MeasurableSet DM) :
    ∃ D : Set G, MeasurableSet D ∧ ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K,
      (u * m * k ∈ D ↔ u ∈ DN ∧ m * (k * (σ k)⁻¹) ∈ DM) := by
  have uniq : ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, σ k = k → ∀ u' ∈ N, ∀ m' ∈ M, ∀ k' ∈ K, σ k' = k' →
      u * m * k = u' * m' * k' → u = u' ∧ m = m' ∧ k = k' := by
    intro u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h
    have e : k = m⁻¹ * u⁻¹ * (u' * m' * k') := by rw [← h]; group
    have e1 : (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * (m⁻¹ * m') = k * k'⁻¹ := by rw [e]; group
    have hkk : k * k'⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk')
    have hmm : m⁻¹ * m' ∈ M := M.mul_mem (M.inv_mem hm) hm'
    have e2 := h4 _ (h3 _ (M.inv_mem hm) _ (N.mul_mem (N.inv_mem hu) hu')) _ hmm (e1 ▸ hkk)
    have huu : u = u' := by
      have : u' = u * (m * (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * m⁻¹) := by group
      rw [this, e2]; group
    rw [e2, one_mul] at e1
    have e3 := h2 (k * k'⁻¹) ⟨hkk, e1 ▸ hmm⟩ k'
    rw [inv_mul_cancel_right, hs, hs'] at e3
    subst huu e3
    exact ⟨rfl, mul_left_cancel (mul_right_cancel h), rfl⟩
  let X : Set (G × G × G) := (DN ∩ N) ×ˢ ((DM ∩ M) ×ˢ ((K : Set G) ∩ {k | σ k = k}))
  have hX : MeasurableSet X :=
    (hDN.inter hN).prod ((hDM.inter hM).prod
      (hK.inter (measurableSet_eq_fun hσ measurable_id)))
  let f : G × G × G → G := fun p => p.1 * p.2.1 * p.2.2
  have hf : Continuous f := by fun_prop
  have hinj : Set.InjOn f X := by
    rintro ⟨u, m, k⟩ ⟨⟨_, hu⟩, ⟨_, hm⟩, hk, hs⟩ ⟨u', m', k'⟩ ⟨⟨_, hu'⟩, ⟨_, hm'⟩, hk', hs'⟩ h
    obtain ⟨a, b, c⟩ := uniq u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h
    rw [a, b, c]
  refine ⟨f '' X, hX.image_of_continuousOn_injOn hf.continuousOn hinj, ?_⟩
  intro u hu m hm k hk
  have hl := h1 k
  have hl' : k * (σ k)⁻¹ ∈ K ⊓ M := by
    have := (K ⊓ M).inv_mem hl
    simpa using this
  have hσK : σ k ∈ K := by
    have := K.mul_mem hl.1 hk
    simpa using this
  have hσσ : σ (σ k) = σ k := by
    have := h2 _ hl k
    simpa using this
  have hm2 : m * (k * (σ k)⁻¹) ∈ M := M.mul_mem hm hl'.2
  have e : u * m * k = u * (m * (k * (σ k)⁻¹)) * σ k := by group
  constructor
  · rintro ⟨⟨u', m', k'⟩, ⟨⟨hdu, hu'⟩, ⟨hdm, hm'⟩, hk', hs'⟩, h⟩
    obtain ⟨a, b, _⟩ := uniq u hu _ hm2 _ hσK hσσ u' hu' m' hm' k' hk' hs' (e.symm.trans h.symm)
    rw [b, a]
    exact ⟨hdu, hdm⟩
  · rintro ⟨hdu, hdm⟩
    exact ⟨(u, m * (k * (σ k)⁻¹), σ k), ⟨⟨hdu, hu⟩, ⟨hdm, hm2⟩, hσK, hσσ⟩, e.symm⟩

end GlobalTheory
end
