module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

@[expose] public section

section

open scoped ComplexConjugate

namespace GlobalTheory

theorem skewFamily_eq_of_strictLower_of_diagIm
    {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ) (hs : ∀ a, s a * s a = 1)
    (Y Y' : ι × Fin r × Fin r → ℂ)
    (hY : ∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b)))
    (hYt : ∀ τ, ∑ a, Y (τ, a, a) = 0)
    (hY' : ∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b)))
    (hY't : ∀ τ, ∑ a, Y' (τ, a, a) = 0)
    (hlt : ∀ τ a b, b < a → Y (τ, a, b) = Y' (τ, a, b))
    (him : ∀ τ (a : Fin r), (a : ℕ) + 1 < r → (Y (τ, a, a)).im = (Y' (τ, a, a)).im) :
    Y = Y' := by
  have hre : ∀ (Z : ι × Fin r × Fin r → ℂ),
      (∀ τ a b, Z (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Z (τ, a, b))) →
      ∀ τ a, (Z (τ, a, a)).re = 0 := by
    intro Z hZ τ a
    have h := hZ τ a a
    rw [hs a] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.ofReal_one, neg_mul, one_mul, Complex.neg_re, Complex.conj_re] at h2
    linarith
  have hoff : ∀ τ (c : Fin r), (c : ℕ) + 1 < r → Y (τ, c, c) = Y' (τ, c, c) :=
    fun τ c hc => Complex.ext (by rw [hre Y hY τ c, hre Y' hY' τ c]) (him τ c hc)
  have hdiag : ∀ τ (a : Fin r), Y (τ, a, a) = Y' (τ, a, a) := by
    intro τ a
    by_cases ha : (a : ℕ) + 1 < r
    · exact hoff τ a ha
    · have hsum : ∀ c ∈ Finset.univ.erase a, Y (τ, c, c) = Y' (τ, c, c) := by
        intro c hc
        apply hoff
        have hca : c ≠ a := Finset.ne_of_mem_erase hc
        have hcv : (c : ℕ) ≠ a := fun h => hca (Fin.ext h)
        have := c.isLt
        have := a.isLt
        omega
      have e1 : Y (τ, a, a) + ∑ c ∈ Finset.univ.erase a, Y (τ, c, c) = 0 := by
        exact (Finset.add_sum_erase Finset.univ (fun c => Y (τ, c, c)) (Finset.mem_univ a)).trans (hYt τ)
      have e2 : Y' (τ, a, a) + ∑ c ∈ Finset.univ.erase a, Y' (τ, c, c) = 0 := by
        exact (Finset.add_sum_erase Finset.univ (fun c => Y' (τ, c, c)) (Finset.mem_univ a)).trans (hY't τ)
      rw [Finset.sum_congr rfl hsum] at e1
      linear_combination e1 - e2
  funext p
  obtain ⟨τ, a, b⟩ := p
  rcases lt_trichotomy a b with h | rfl | h
  · rw [hY τ b a, hY' τ b a, hlt τ b a h]
  · exact hdiag τ a
  · exact hlt τ a b h

end GlobalTheory
end

section

open scoped Classical

namespace GlobalTheory

theorem pieri_recursion_zero (n : ℕ) (c : ℕ → ℂ) (D : (Fin n → ℕ) → ℂ)
    (hD : ∀ l, ¬ Antitone l → D l = 0)
    (hr : ∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), D (l + (fun i => if i ∈ J then 1 else 0)) = c j * D l)
    (h0 : D 0 = 0) : ∀ μ, D μ = 0 := by
  have main : ∀ s k (μ : Fin n → ℕ), ∑ i, μ i = s →
      n - (Finset.univ.filter (fun i => μ i ≠ 0)).card = k → D μ = 0 := by
    intro s
    refine Nat.strong_induction_on s ?_
    intro s ihs k
    refine Nat.strong_induction_on k ?_
    intro k ihk μ hs hk
    by_cases hμ : Antitone μ
    swap
    · exact hD μ hμ
    by_cases hz : μ = 0
    · subst hz; exact h0
    set J0 : Finset (Fin n) := Finset.univ.filter (fun i => μ i ≠ 0) with hJ0
    set l : Fin n → ℕ := fun i => μ i - 1 with hl
    have hla : Antitone l := fun a b hab => Nat.sub_le_sub_right (hμ hab) 1
    have hj : J0.card ≤ n := by simpa using Finset.card_le_univ J0
    have hlμ : l + (fun i => if i ∈ J0 then 1 else 0) = μ := by
      funext i
      simp only [Pi.add_apply, hl, hJ0, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h <;> omega
    have hsum : ∀ J : Finset (Fin n),
        ∑ i, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) i = ∑ i, l i + J.card := by
      intro J
      simp [Finset.sum_add_distrib, Finset.sum_boole]
    have hDl : D l = 0 := by
      have hlt : ∑ i, l i < s := by
        rw [← hs]
        obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
          by_contra h
          push_neg at h
          exact hz (funext h)
        exact Finset.sum_lt_sum (fun i _ => Nat.sub_le _ _)
          ⟨i, Finset.mem_univ _, by simp only [hl]; omega⟩
      exact ihs _ hlt _ l rfl rfl
    have hsingle : ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = J0.card),
        D (l + (fun i => if i ∈ J then 1 else 0)) = D (l + (fun i => if i ∈ J0 then 1 else 0)) := by
      refine Finset.sum_eq_single_of_mem J0 (by simp) ?_
      intro J hJ hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      set ν : Fin n → ℕ := l + (fun i => if i ∈ J then 1 else 0) with hν
      by_cases hνa : Antitone ν
      swap
      · exact hD ν hνa
      have hnsub : ¬ J ⊆ J0 := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))
      obtain ⟨i, hiJ, hiJ0⟩ := Finset.not_subset.mp hnsub
      have hμi : μ i = 0 := by simpa [hJ0] using hiJ0
      have hνi : 1 ≤ ν i := by simp [hν, hiJ]
      have hsub : insert i J0 ⊆ Finset.univ.filter (fun k => ν k ≠ 0) := by
        intro k hk
        rw [Finset.mem_insert] at hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hk with rfl | hk
        · omega
        · have hk' : μ k ≠ 0 := by simpa [hJ0] using hk
          have hki : k ≤ i := by
            by_contra h
            push_neg at h
            have := hμ h.le
            omega
          have := hνa hki
          omega
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hiJ0] at hcard
      have hcn : (Finset.univ.filter (fun k => ν k ≠ 0)).card ≤ n := by
        simpa using Finset.card_le_univ (Finset.univ.filter (fun k => ν k ≠ 0))
      refine ihk (n - (Finset.univ.filter (fun k => ν k ≠ 0)).card) ?_ ν ?_ rfl
      · omega
      · have h1 := hsum J
        have h2 := hsum J0
        rw [hlμ] at h2
        rw [hν, h1, hJ, ← h2, hs]
    have hrec := hr l hla J0.card hj
    rw [hsingle, hDl, mul_zero, hlμ] at hrec
    exact hrec
  intro μ
  exact main _ _ μ rfl rfl

theorem pieri_recursion_unique : ∀ (n : ℕ) (c : ℕ → ℂ) (V U : (Fin n → ℕ) → ℂ),
    (∀ l, ¬ Antitone l → V l = 0) → (∀ l, ¬ Antitone l → U l = 0) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), V (l + (fun i => if i ∈ J then 1 else 0)) = c j * V l) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), U (l + (fun i => if i ∈ J then 1 else 0)) = c j * U l) →
    V 0 = U 0 → V = U := by
  intro n c V U hV hU hrV hrU h0
  have h := pieri_recursion_zero n c (fun l => V l - U l)
    (fun l hl => by simp [hV l hl, hU l hl])
    (fun l hl j hj => by
      simp only [Finset.sum_sub_distrib, hrV l hl j hj, hrU l hl j hj, mul_sub])
    (by simp [h0])
  funext μ
  exact sub_eq_zero.mp (h μ)

end GlobalTheory
end

section

open scoped ComplexConjugate

namespace GlobalTheory

theorem skew_family_inner_re_split : ∀ {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ), (∀ a, s a * s a = 1) → ∀ (Y Y' : ι × Fin r × Fin r → ℂ), (∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b))) → (∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b))) → ∑ p, (conj (Y p) * Y' p).re = 2 * ∑ q : ι × {p : Fin r × Fin r // p.2 < p.1}, (conj (Y (q.1, q.2.1.1, q.2.1.2)) * Y' (q.1, q.2.1.1, q.2.1.2)).re + ∑ τ, ∑ a, (Y (τ, a, a)).im * (Y' (τ, a, a)).im := by
  intro ι _ r s hs Y Y' hY hY'
  set F : ι → Fin r → Fin r → ℝ := fun τ a b => (conj (Y (τ, a, b)) * Y' (τ, a, b)).re with hF
  have key : ∀ τ a b, F τ b a = F τ a b := by
    intro τ a b
    have h2 : (s a * s b) * (s a * s b) = 1 := by rw [mul_mul_mul_comm, hs, hs, one_mul]
    simp only [hF, hY τ a b, hY' τ a b, map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal,
      Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, Complex.mul_im, Complex.neg_im]
    linear_combination ((Y (τ, a, b)).re * (Y' (τ, a, b)).re + (Y (τ, a, b)).im * (Y' (τ, a, b)).im) * h2
  have diag : ∀ τ a, F τ a a = (Y (τ, a, a)).im * (Y' (τ, a, a)).im := by
    intro τ a
    have h1 := congrArg Complex.re (hY τ a a)
    have h2 := congrArg Complex.re (hY' τ a a)
    simp only [hs, Complex.ofReal_one, Complex.neg_re, Complex.mul_re, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_im] at h1 h2
    simp only [hF, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have e1 : (Y (τ, a, a)).re = 0 := by linarith
    rw [e1]; ring
  have per : ∀ τ, ∑ a, ∑ b, F τ a b
      = 2 * ∑ p : {p : Fin r × Fin r // p.2 < p.1}, F τ p.1.1 p.1.2 + ∑ a, F τ a a := by
    intro τ
    have hsplit : ∀ a b, F τ a b = ((if b < a then F τ a b else 0) + (if a < b then F τ a b else 0))
        + (if a = b then F τ a b else 0) := by
      intro a b
      rcases lt_trichotomy a b with h | rfl | h
      · simp [h, not_lt_of_gt h, h.ne]
      · simp
      · simp [h, not_lt_of_gt h, h.ne']
    have hsub : ∑ p : {p : Fin r × Fin r // p.2 < p.1}, F τ p.1.1 p.1.2
        = ∑ a, ∑ b, if b < a then F τ a b else 0 := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin r × Fin r => p.2 < p.1)) (by simp)
        (fun p : Fin r × Fin r => F τ p.1 p.2), Finset.sum_filter, Fintype.sum_prod_type]
    have hsym : (∑ a, ∑ b, if a < b then F τ a b else 0) = ∑ a, ∑ b, if b < a then F τ a b else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [key]
    have hdiag : (∑ a, ∑ b, if a = b then F τ a b else 0) = ∑ a, F τ a a := by
      simp
    calc ∑ a, ∑ b, F τ a b
        = ∑ a, ∑ b, (((if b < a then F τ a b else 0) + (if a < b then F τ a b else 0))
            + (if a = b then F τ a b else 0)) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsplit a b))
      _ = ((∑ a, ∑ b, if b < a then F τ a b else 0) + (∑ a, ∑ b, if a < b then F τ a b else 0))
            + ∑ a, ∑ b, if a = b then F τ a b else 0 := by
          simp only [Finset.sum_add_distrib]
      _ = _ := by rw [hsym, hdiag, hsub]; ring
  have lhs : ∑ p, (conj (Y p) * Y' p).re = ∑ τ, ∑ a, ∑ b, F τ a b := by
    simp only [hF, Fintype.sum_prod_type]
  rw [lhs, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [per τ]
  simp only [diag]
  rfl

end GlobalTheory
end

section

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

open scoped BigOperators Matrix in
open Polynomial in
private lemma one_sub_prod_le_sum_one_sub_of_mem_Icc {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h0' : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1' : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hP1 : ∏ i ∈ s, f i ≤ 1 := Finset.prod_le_one₀ h0' h1'
    have ha1 := h1 a (Finset.mem_insert_self a s)
    have key := ih h0' h1'
    nlinarith [mul_nonneg (sub_nonneg.2 hP1) (sub_nonneg.2 ha1)]


open scoped BigOperators Matrix in
open Polynomial in
theorem _root_.GlobalTheory.degree_ratio_shift_bound : ∀ (Pl : Type) [Fintype Pl] (N p kc : ℕ) (u1 : Pl → ℕ → ℝ) (g1 w : Pl → ℝ) (T : ℝ), kc ≤ p → p ≤ N → 0 < T → (∀ τ, 0 < w τ) → (∀ τ, 3 * (N : ℝ) < g1 τ) → (∀ τ i l, i < l → l < N → u1 τ l < u1 τ i) → (∀ τ i l, i < p → p ≤ l → l < N → g1 τ ≤ u1 τ i - u1 τ l) → (∀ τ i l, i < kc → p ≤ l → l < N → w τ / (2 * T) ≤ u1 τ i - u1 τ l) → let u' : Pl → ℕ → ℝ := fun τ i => if i < p then u1 τ i else u1 τ i + 3 * N; let deg : (Pl → ℕ → ℝ) → ℝ := fun v => ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l); 0 < deg u' ∧ 0 ≤ 1 - deg u' / deg u1 ∧ 1 - deg u' / deg u1 ≤ 3 * N * ∑ τ, (((p - kc : ℕ) : ℝ) * ((N - p : ℕ) : ℝ) / g1 τ + 2 * kc * ((N - p : ℕ) : ℝ) * T / w τ) := by
  intro Pl inst N p kc u1 g1 w T hkc hpN hT hw hg hmono hgap hwgap u' deg
  have hN : (0 : ℝ) ≤ 3 * N := by positivity
  have hd : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l → 0 < u1 τ i - u1 τ l := by
    intro τ l i hl hi
    exact sub_pos.2 (hmono τ i l (Finset.mem_range.1 hi) (Finset.mem_range.1 hl))
  obtain ⟨F, hF⟩ : ∃ F : Pl → ℕ → ℕ → ℝ,
      ∀ τ l i, F τ l i = (u' τ i - u' τ l) / (u1 τ i - u1 τ l) := ⟨_, fun _ _ _ => rfl⟩
  have hfac : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      u' τ i - u' τ l = (u1 τ i - u1 τ l) * F τ l i := by
    intro τ l i hl hi
    have hne := (hd τ l i hl hi).ne'
    rw [hF]
    field_simp
  have hFeq : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      F τ l i = if i < p ∧ p ≤ l then 1 - 3 * (N : ℝ) / (u1 τ i - u1 τ l) else 1 := by
    intro τ l i hl hi
    have hne := (hd τ l i hl hi).ne'
    rw [Finset.mem_range] at hl hi
    rw [hF]
    by_cases hip : i < p
    · by_cases hpl : p ≤ l
      · have hl' : ¬ l < p := not_lt.2 hpl
        simp only [u', hip, hl', hpl, and_self, ↓reduceIte]
        field_simp <;> ring
      · have hl' : l < p := lt_of_not_ge hpl
        simp only [u', hip, hl', hpl, and_false, ↓reduceIte]
        exact div_self hne
    · have hl' : ¬ l < p := by omega
      simp only [u', hip, hl', false_and, ↓reduceIte]
      rw [show u1 τ i + 3 * (N : ℝ) - (u1 τ l + 3 * N) = u1 τ i - u1 τ l by ring]
      exact div_self hne
  have hF01 : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      0 < F τ l i ∧ F τ l i ≤ 1 := by
    intro τ l i hl hi
    rw [hFeq τ l i hl hi]
    split_ifs with h
    · have hdp := hd τ l i hl hi
      have hlt : 3 * (N : ℝ) < u1 τ i - u1 τ l :=
        (hg τ).trans_le (hgap τ i l h.1 h.2 (Finset.mem_range.1 hl))
      have h3 : 3 * (N : ℝ) / (u1 τ i - u1 τ l) < 1 := (div_lt_one hdp).2 hlt
      have h4 : 0 ≤ 3 * (N : ℝ) / (u1 τ i - u1 τ l) := div_nonneg hN hdp.le
      constructor <;> linarith
    · exact ⟨one_pos, le_rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Pl → ℕ → ℝ, ∀ τ i, c τ i = if i < kc then 2 * T / w τ else 1 / g1 τ :=
    ⟨_, fun _ _ => rfl⟩
  have hbound : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      1 - F τ l i ≤ 3 * (N : ℝ) * (if i < p ∧ p ≤ l then c τ i else 0) := by
    intro τ l i hl hi
    have hdp := hd τ l i hl hi
    rw [hFeq τ l i hl hi]
    split_ifs with h
    · rw [sub_sub_cancel, div_eq_mul_one_div]
      refine mul_le_mul_of_nonneg_left ?_ hN
      rw [hc]
      split_ifs with hk
      · have h1 : w τ ≤ (u1 τ i - u1 τ l) * (2 * T) :=
          (div_le_iff₀ (by linarith)).1 (hwgap τ i l hk h.2 (Finset.mem_range.1 hl))
        rw [div_le_div_iff₀ hdp (hw τ)]
        nlinarith
      · have hgpos : 0 < g1 τ := lt_of_le_of_lt hN (hg τ)
        exact one_div_le_one_div_of_le hgpos (hgap τ i l h.1 h.2 (Finset.mem_range.1 hl))
    · simp
  have hsum : ∀ τ, ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range l,
      3 * (N : ℝ) * (if i < p ∧ p ≤ l then c τ i else 0) =
      3 * (N : ℝ) * (((p - kc : ℕ) : ℝ) * ((N - p : ℕ) : ℝ) / g1 τ
        + 2 * kc * ((N - p : ℕ) : ℝ) * T / w τ) := by
    intro τ
    simp_rw [← Finset.mul_sum]
    congr 1
    have hS : ∑ i ∈ Finset.range p, c τ i =
        (kc : ℝ) * (2 * T / w τ) + ((p - kc : ℕ) : ℝ) * (1 / g1 τ) := by
      rw [← Finset.sum_range_add_sum_Ico _ hkc]
      have e1 : ∑ i ∈ Finset.range kc, c τ i = ∑ i ∈ Finset.range kc, 2 * T / w τ :=
        Finset.sum_congr rfl fun i hi => by rw [hc, if_pos (Finset.mem_range.1 hi)]
      have e2 : ∑ i ∈ Finset.Ico kc p, c τ i = ∑ i ∈ Finset.Ico kc p, 1 / g1 τ :=
        Finset.sum_congr rfl fun i hi => by rw [hc, if_neg (not_lt.2 (Finset.mem_Ico.1 hi).1)]
      rw [e1, e2, Finset.sum_const, Finset.sum_const, Finset.card_range, Nat.card_Ico,
        nsmul_eq_mul, nsmul_eq_mul]
    have hinner : ∀ l, ∑ i ∈ Finset.range l, (if i < p ∧ p ≤ l then c τ i else 0) =
        if p ≤ l then ∑ i ∈ Finset.range p, c τ i else 0 := by
      intro l
      by_cases hl : p ≤ l
      · rw [if_pos hl, ← Finset.sum_range_add_sum_Ico _ hl]
        have e1 : ∑ i ∈ Finset.range p, (if i < p ∧ p ≤ l then c τ i else 0) =
            ∑ i ∈ Finset.range p, c τ i :=
          Finset.sum_congr rfl fun i hi => if_pos ⟨Finset.mem_range.1 hi, hl⟩
        have e2 : ∑ i ∈ Finset.Ico p l, (if i < p ∧ p ≤ l then c τ i else 0) = 0 :=
          Finset.sum_eq_zero fun i hi =>
            if_neg fun h => absurd h.1 (not_lt.2 (Finset.mem_Ico.1 hi).1)
        rw [e1, e2, add_zero]
      · rw [if_neg hl]
        exact Finset.sum_eq_zero fun i _ => if_neg fun h => hl h.2
    rw [Finset.sum_congr rfl fun l _ => hinner l, ← Finset.sum_range_add_sum_Ico _ hpN]
    have e3 : ∑ l ∈ Finset.range p, (if p ≤ l then ∑ i ∈ Finset.range p, c τ i else 0) = 0 :=
      Finset.sum_eq_zero fun l hl => if_neg (not_le.2 (Finset.mem_range.1 hl))
    have e4 : ∑ l ∈ Finset.Ico p N, (if p ≤ l then ∑ i ∈ Finset.range p, c τ i else 0) =
        ∑ l ∈ Finset.Ico p N, ∑ i ∈ Finset.range p, c τ i :=
      Finset.sum_congr rfl fun l hl => if_pos (Finset.mem_Ico.1 hl).1
    rw [e3, e4, zero_add, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, hS]
    ring
  have hQ : ∀ τ l, l ∈ Finset.range N →
      0 < ∏ i ∈ Finset.range l, F τ l i ∧ ∏ i ∈ Finset.range l, F τ l i ≤ 1 := fun τ l hl =>
    ⟨Finset.prod_pos fun i hi => (hF01 τ l i hl hi).1,
      Finset.prod_le_one₀ (fun i hi => (hF01 τ l i hl hi).1.le) fun i hi => (hF01 τ l i hl hi).2⟩
  have hR : ∀ τ, 0 < ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i ∧
      ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i ≤ 1 := fun τ =>
    ⟨Finset.prod_pos fun l hl => (hQ τ l hl).1,
      Finset.prod_le_one₀ (fun l hl => (hQ τ l hl).1.le) fun l hl => (hQ τ l hl).2⟩
  have hP0 : 0 < ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i :=
    Finset.prod_pos fun τ _ => (hR τ).1
  have hP1 : ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i ≤ 1 :=
    Finset.prod_le_one₀ (fun τ _ => (hR τ).1.le) fun τ _ => (hR τ).2
  have hdeg1 : 0 < deg u1 := by
    simp only [deg]
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun l hl =>
      Finset.prod_pos fun i hi => hd τ l i hl hi
  have hdeg : deg u' = deg u1 * ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i := by
    simp only [deg, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun l hl =>
      Finset.prod_congr rfl fun i hi => hfac τ l i hl hi
  have hratio : deg u' / deg u1 = ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i := by
    have hne := hdeg1.ne'
    rw [hdeg]
    field_simp
  refine ⟨by rw [hdeg]; exact mul_pos hdeg1 hP0, by rw [hratio]; linarith, ?_⟩
  rw [hratio]
  calc 1 - ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i
      ≤ ∑ τ, (1 - ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i) :=
        one_sub_prod_le_sum_one_sub_of_mem_Icc _ _ (fun τ _ => (hR τ).1.le) fun τ _ => (hR τ).2
    _ ≤ ∑ τ, ∑ l ∈ Finset.range N, (1 - ∏ i ∈ Finset.range l, F τ l i) :=
        Finset.sum_le_sum fun τ _ => one_sub_prod_le_sum_one_sub_of_mem_Icc _ _
          (fun l hl => (hQ τ l hl).1.le) fun l hl => (hQ τ l hl).2
    _ ≤ ∑ τ, ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range l, (1 - F τ l i) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun l hl =>
          one_sub_prod_le_sum_one_sub_of_mem_Icc _ _ (fun i hi => (hF01 τ l i hl hi).1.le)
            fun i hi => (hF01 τ l i hl hi).2
    _ ≤ ∑ τ, ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range l,
          3 * (N : ℝ) * (if i < p ∧ p ≤ l then c τ i else 0) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun l hl =>
          Finset.sum_le_sum fun i hi => hbound τ l i hl hi
    _ = ∑ τ, 3 * (N : ℝ) * (((p - kc : ℕ) : ℝ) * ((N - p : ℕ) : ℝ) / g1 τ
          + 2 * kc * ((N - p : ℕ) : ℝ) * T / w τ) :=
        Finset.sum_congr rfl fun τ _ => hsum τ
    _ = _ := by rw [Finset.mul_sum]

end GlobalTheory
end

section

open CategoryTheory Limits

namespace GlobalTheory

theorem natCard_homology_restrictScalars {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ) :
    Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  have e : (((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n ≅
      (ModuleCat.restrictScalars.{0} f).obj (D.homology n) :=
    (D.sc n).mapHomologyIso (ModuleCat.restrictScalars.{0} f)
  exact Nat.card_congr e.toLinearEquiv.toEquiv

end GlobalTheory
end
