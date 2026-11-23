module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle001
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle006
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

variable {K : Type} [NormedField K] in
private lemma summable_coeff_mul_pow [CompleteSpace K] (c : ℕ → K) (hc : ∀ n, ‖c n‖ ≤ 1) (y : K)
    (hy : ‖y‖ < 1) : Summable (fun n => c n * y ^ n) :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg y) hy) fun n => by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hc n)

variable {K : Type} [NormedField K] in
private lemma exists_quotient_by_linear_of_zero [IsUltrametricDist K] [CompleteSpace K] (c : ℕ → K)
    (hc : ∀ n, ‖c n‖ ≤ 1) (x : K) (hx : ‖x‖ < 1) (h0 : ∑' n, c n * x ^ n = 0) :
    ∃ d : ℕ → K, (∀ n, ‖d n‖ ≤ 1) ∧ c 0 = -(x * d 0) ∧ ∀ n, c (n + 1) = d n - x * d (n + 1) := by
  refine ⟨fun k => ∑' m, c (m + k + 1) * x ^ m, fun k => ?_, ?_, fun n => ?_⟩
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le fun m => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (hc _) (by positivity) (pow_le_one₀ (norm_nonneg x) hx.le)
  · have hs := summable_coeff_mul_pow c hc x hx
    rw [hs.tsum_eq_zero_add] at h0
    have : ∑' m, c (m + 1) * x ^ (m + 1) = x * ∑' m, c (m + 0 + 1) * x ^ m := by
      rw [← tsum_mul_left]
      exact tsum_congr fun m => by rw [add_zero, pow_succ]; ring
    rw [this, pow_zero, mul_one] at h0
    linear_combination h0
  · have hs : Summable (fun m => c (m + n + 1) * x ^ m) :=
      summable_coeff_mul_pow (fun m => c (m + n + 1)) (fun m => hc _) x hx
    show c (n + 1) = ∑' m, c (m + n + 1) * x ^ m - x * ∑' m, c (m + (n + 1) + 1) * x ^ m
    rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
    have : ∑' m, c (m + 1 + n + 1) * x ^ (m + 1) = ∑' m, x * (c (m + (n + 1) + 1) * x ^ m) :=
      tsum_congr fun m => by
        rw [show m + 1 + n + 1 = m + (n + 1) + 1 by omega, pow_succ]
        ring
    rw [this, pow_zero, mul_one, zero_add]
    ring

variable {K : Type} [NormedField K] in
private lemma tsum_eq_sub_mul_tsum [CompleteSpace K] (c d : ℕ → K) (hd : ∀ n, ‖d n‖ ≤ 1) (x : K)
    (hc : ∀ n, ‖c n‖ ≤ 1) (h0 : c 0 = -(x * d 0)) (hrel : ∀ n, c (n + 1) = d n - x * d (n + 1))
    (y : K) (hy : ‖y‖ < 1) :
    ∑' n, c n * y ^ n = (y - x) * ∑' n, d n * y ^ n := by
  have hsc := summable_coeff_mul_pow c hc y hy
  have hsd := summable_coeff_mul_pow d hd y hy
  have e1 : ∑' n, c n * y ^ n = c 0 + ∑' n, c (n + 1) * y ^ (n + 1) := by
    simpa using hsc.tsum_eq_zero_add
  have e2 : ∑' n, d n * y ^ n = d 0 + ∑' n, d (n + 1) * y ^ (n + 1) := by
    simpa using hsd.tsum_eq_zero_add
  have hA : Summable (fun n => y * (d n * y ^ n)) := hsd.mul_left y
  have hB : Summable (fun n => x * (d (n + 1) * y ^ (n + 1))) :=
    ((summable_nat_add_iff 1).mpr hsd).mul_left x
  have e3 : ∑' n, c (n + 1) * y ^ (n + 1) =
      y * ∑' n, d n * y ^ n - x * ∑' n, d (n + 1) * y ^ (n + 1) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← hA.tsum_sub hB]
    exact tsum_congr fun n => by rw [hrel n, pow_succ]; ring
  rw [e1, e3, h0]
  linear_combination x * e2

variable {K : Type} [NormedField K] in
private lemma coeff_bounds_of_zeros [IsUltrametricDist K] [CompleteSpace K] (S : Finset K) :
    ∀ c : ℕ → K, (∀ n, ‖c n‖ ≤ 1) → (∀ x ∈ S, ‖x‖ < 1 ∧ ∑' n, c n * x ^ n = 0) →
      (∀ r : ℝ, 0 < r → r ≤ 1 → (∀ x ∈ S, r ≤ ‖x‖) → ∀ k, ‖c k‖ * r ^ k ≤ ∏ x ∈ S, ‖x‖) ∧
      (‖c S.card‖ = 1 → (∀ k < S.card, ‖c k‖ < 1) → ∏ x ∈ S, ‖x‖ = ‖c 0‖) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro c hc _
    refine ⟨fun r hr0 hr1 _ k => ?_, fun h1 _ => ?_⟩
    · rw [Finset.prod_empty]
      exact mul_le_one₀ (hc k) (by positivity) (pow_le_one₀ hr0.le hr1)
    · simpa using h1.symm
  | insert x S hxS ih =>
    intro c hc hz
    obtain ⟨hx, hx0⟩ := hz x (Finset.mem_insert_self x S)
    obtain ⟨d, hd, h0, hrel⟩ := exists_quotient_by_linear_of_zero c hc x hx hx0
    have hzd : ∀ y ∈ S, ‖y‖ < 1 ∧ ∑' n, d n * y ^ n = 0 := by
      intro y hy
      obtain ⟨hy1, hy0⟩ := hz y (Finset.mem_insert_of_mem hy)
      refine ⟨hy1, ?_⟩
      rw [tsum_eq_sub_mul_tsum c d hd x hc h0 hrel y hy1] at hy0
      have hne : y - x ≠ 0 := sub_ne_zero.mpr fun h => hxS (h ▸ hy)
      exact (mul_eq_zero.mp hy0).resolve_left hne
    obtain ⟨ih1, ih2⟩ := ih d hd hzd
    have hP : 0 ≤ ∏ y ∈ S, ‖y‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    refine ⟨fun r hr0 hr1 hrS k => ?_, fun h1 hlt => ?_⟩
    · rw [Finset.prod_insert hxS]
      have hrx : r ≤ ‖x‖ := hrS x (Finset.mem_insert_self x S)
      have hrS' : ∀ y ∈ S, r ≤ ‖y‖ := fun y hy => hrS y (Finset.mem_insert_of_mem hy)
      have hb := ih1 r hr0 hr1 hrS'
      cases k with
      | zero =>
        rw [h0, norm_neg, norm_mul, pow_zero, mul_one]
        have := hb 0
        rw [pow_zero, mul_one] at this
        exact mul_le_mul_of_nonneg_left this (norm_nonneg x)
      | succ n =>
        have hm : ‖c (n + 1)‖ ≤ max ‖d n‖ (‖x‖ * ‖d (n + 1)‖) := by
          rw [hrel n, sub_eq_add_neg]
          simpa [norm_mul] using IsUltrametricDist.norm_add_le_max (d n) (-(x * d (n + 1)))
        have e1 : ‖d n‖ * r ^ (n + 1) ≤ ‖x‖ * ∏ y ∈ S, ‖y‖ := by
          rw [pow_succ, ← mul_assoc, mul_comm ‖x‖]
          exact mul_le_mul (hb n) hrx hr0.le hP
        have e2 : ‖x‖ * ‖d (n + 1)‖ * r ^ (n + 1) ≤ ‖x‖ * ∏ y ∈ S, ‖y‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hb (n + 1)) (norm_nonneg x)
        calc ‖c (n + 1)‖ * r ^ (n + 1)
            ≤ max ‖d n‖ (‖x‖ * ‖d (n + 1)‖) * r ^ (n + 1) :=
              mul_le_mul_of_nonneg_right hm (by positivity)
          _ = max (‖d n‖ * r ^ (n + 1)) (‖x‖ * ‖d (n + 1)‖ * r ^ (n + 1)) :=
              max_mul_of_nonneg _ _ (by positivity)
          _ ≤ ‖x‖ * ∏ y ∈ S, ‖y‖ := max_le e1 e2
    · rw [Finset.card_insert_of_notMem hxS] at h1 hlt
      have hsmall : ∀ k, ‖x * d k‖ < 1 := fun k => by
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg x) (hd k)).trans_lt hx
      have hdk : ∀ k, d k = c (k + 1) + x * d (k + 1) := fun k => by rw [hrel k]; ring
      have hd1 : ‖d S.card‖ = 1 := by
        rw [hdk, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, h1]
        · exact max_eq_left (hsmall _).le
        · rw [h1]
          exact (hsmall _).ne'
      have hdlt : ∀ k < S.card, ‖d k‖ < 1 := fun k hk => by
        rw [hdk]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
          (max_lt (hlt (k + 1) (by omega)) (hsmall _))
      rw [Finset.prod_insert hxS, ih2 hd1 hdlt, h0, norm_neg, norm_mul]

theorem _root_.GlobalTheory.ConvSer.norm_coeff_le_prod_zeros : ∀ (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (h : PowerSeries K) (S : Finset K),
    _root_.GlobalTheory.ConvSer.Intg h → (∀ x ∈ S, ‖x‖ < 1 ∧ _root_.GlobalTheory.ConvSer.ev1 h x = 0) →
    (∀ r : ℝ, 0 < r → r ≤ 1 → (∀ x ∈ S, r ≤ ‖x‖) → ∀ k, ‖PowerSeries.coeff k h‖ * r ^ k ≤
      ∏ x ∈ S, ‖x‖) ∧ (‖PowerSeries.coeff S.card h‖ = 1 → (∀ k < S.card,
      ‖PowerSeries.coeff k h‖ < 1) → ∏ x ∈ S, ‖x‖ = ‖PowerSeries.coeff 0 h‖) := by
  intro K _ _ _ h S hI hS
  exact coeff_bounds_of_zeros S (fun n => PowerSeries.coeff n h)
    (fun n => hI (Finsupp.single () n)) hS

end GlobalTheory.ConvSer
end

section

open GlobalTheory.ConvSer Polynomial

namespace GlobalTheory.ConvSer

theorem norm_coeff_prod_X_sub_C_le_pow {K : Type} [NormedField K] [IsUltrametricDist K]
    (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (S : Finset K) (hS : ∀ x ∈ S, ‖x‖ ≤ θ) (a : ℕ) :
    ‖(∏ x ∈ S, (X - C x) : K[X]).coeff a‖ ≤ θ ^ (S.card - a) := by
  first
  | exact @_root_.GlobalTheory.RootProductCoeffBound.main
  | exact _root_.GlobalTheory.RootProductCoeffBound.main
  | (apply _root_.GlobalTheory.RootProductCoeffBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootProductCoeffBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootProductCoeffBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootProductCoeffBound.main ..)

theorem exists_pow_eq_interpolation {K : Type} [NormedField K] [IsUltrametricDist K]
    (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (S : Finset K) (hS : ∀ x ∈ S, ‖x‖ ≤ θ)
    (hN : 0 < S.card) (k : ℕ) :
    ∃ Q : K[X], (∀ a, S.card ≤ a → Q.coeff a = 0) ∧ (∀ a, ‖Q.coeff a‖ ≤ θ ^ (k - a)) ∧
      ∀ x ∈ S, Q.eval x = x ^ k := by
  induction k with
  | zero =>
    refine ⟨1, fun a ha => ?_, fun a => ?_, by simp⟩
    · rw [coeff_one, if_neg (by omega)]
    · rw [coeff_one]; split_ifs <;> simp
  | succ k ih =>
    obtain ⟨Q, hQ0, hQ1, hQ2⟩ := ih
    obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by omega⟩
    set P : K[X] := ∏ x ∈ S, (X - C x) with hP
    have hPm : P.Monic := monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)
    have hPd : P.natDegree = n + 1 := by
      rw [hP, natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]
      simp [hn]
    refine ⟨X * Q - C (Q.coeff n) * P, fun a ha => ?_, fun a => ?_, fun x hx => ?_⟩
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [coeff_sub, coeff_X_mul, coeff_C_mul]
      rcases (show n = b ∨ n < b by omega) with rfl | h
      · have : P.coeff (n + 1) = 1 := by rw [← hPd]; exact hPm.coeff_natDegree
        rw [this]; simp
      · rw [hQ0 b (by omega), coeff_eq_zero_of_natDegree_lt (p := P) (by omega)]; simp
    · by_cases ha : n + 1 < a
      · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
        rw [coeff_sub, coeff_X_mul, coeff_C_mul, hQ0 b (by omega),
          coeff_eq_zero_of_natDegree_lt (p := P) (by omega)]
        simp; positivity
      rw [coeff_sub, coeff_C_mul, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · cases a with
        | zero => simp; positivity
        | succ a =>
          rw [coeff_X_mul]
          simpa using hQ1 a
      · rw [norm_neg, norm_mul]
        calc _ ≤ θ ^ (k - n) * θ ^ (S.card - a) :=
              mul_le_mul (hQ1 n) (norm_coeff_prod_X_sub_C_le_pow θ h0 h1 S hS a) (norm_nonneg _)
                (by positivity)
          _ = θ ^ (k - n + (S.card - a)) := by ring
          _ ≤ _ := pow_le_pow_of_le_one h0 h1 (by omega)
    · have : P.eval x = 0 := by
        rw [hP, eval_prod]
        exact Finset.prod_eq_zero hx (by simp)
      simp [this, hQ2 x hx, pow_succ']

theorem exists_integral_interpolation_two :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (S : Finset K)
      (H : MvPowerSeries (Fin 2) K), (∀ x ∈ S, ‖x‖ < 1) → Intg H →
      ∃ c : Fin S.card → Fin S.card → K, (∀ a b, ‖c a b‖ ≤ 1) ∧ ∀ x ∈ S, ∀ y ∈ S,
        ev H ![x, y] = ∑ a, ∑ b, c a b * x ^ (a : ℕ) * y ^ (b : ℕ) := by
  intro K _ _ _ S H hS hH
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => 0, by simp, by simp⟩
  obtain ⟨x0, hx0, hmax⟩ := S.exists_max_image (fun x => ‖x‖) hne
  set θ := ‖x0‖
  have h0 : 0 ≤ θ := norm_nonneg _
  have h1 : θ < 1 := hS x0 hx0
  choose Q hQ0 hQ1 hQ2 using
    exists_pow_eq_interpolation θ h0 h1.le S hmax hne.card_pos
  have hev : ∀ k, ∀ x ∈ S, x ^ k = ∑ a : Fin S.card, (Q k).coeff a * x ^ (a : ℕ) := by
    intro k x hx
    rw [← hQ2 k x hx, Fin.sum_univ_eq_sum_range (fun a => (Q k).coeff a * x ^ a)]
    apply eval_eq_sum_range'
    have := hne.card_pos
    have h : (Q k).natDegree ≤ S.card - 1 :=
      natDegree_le_iff_coeff_eq_zero.2 (fun a ha => hQ0 k a (by omega))
    omega
  have hg : ∀ a : ℕ, Summable (fun k : ℕ => θ ^ (k - a)) := by
    intro a
    rw [← summable_nat_add_iff a]
    simpa using summable_geometric_of_lt_one h0 h1
  let T : ℕ → ℕ → (Fin 2 →₀ ℕ) → K := fun a b ν =>
    MvPowerSeries.coeff ν H * (Q (ν 0)).coeff a * (Q (ν 1)).coeff b
  have hT : ∀ a b ν, ‖T a b ν‖ ≤ θ ^ (ν 0 - a) * θ ^ (ν 1 - b) := by
    intro a b ν
    simp only [T, norm_mul]
    refine mul_le_mul ?_ (hQ1 _ _) (norm_nonneg _) (by positivity)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hH ν)).trans (hQ1 _ _)
  have hsum : ∀ a b, Summable (T a b) := by
    intro a b
    refine Summable.of_norm_bounded ?_ (hT a b)
    have h : Summable (fun p : ℕ × ℕ => θ ^ (p.1 - a) * θ ^ (p.2 - b)) :=
      Summable.mul_of_nonneg (f := fun k : ℕ => θ ^ (k - a)) (g := fun k : ℕ => θ ^ (k - b))
        (hg a) (hg b) (fun _ => pow_nonneg h0 _) (fun _ => pow_nonneg h0 _)
    have hinj : Function.Injective (fun ν : Fin 2 →₀ ℕ => (ν 0, ν 1)) := by
      intro ν μ h
      simp only [Prod.mk.injEq] at h
      ext i
      fin_cases i
      · exact h.1
      · exact h.2
    have h' := h.comp_injective hinj
    simpa only [Function.comp_def] using h'
  refine ⟨fun a b => ∑' ν, T a b ν, fun a b => ?_, fun x hx y hy => ?_⟩
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one (fun ν => ?_)
    exact (hT a b ν).trans (mul_le_one₀ (pow_le_one₀ h0 h1.le) (by positivity)
      (pow_le_one₀ h0 h1.le))
  · have h : HasSum (fun ν => ∑ a : Fin S.card, ∑ b : Fin S.card,
        T a b ν * x ^ (a : ℕ) * y ^ (b : ℕ))
        (∑ a : Fin S.card, ∑ b : Fin S.card, (∑' ν, T a b ν) * x ^ (a : ℕ) * y ^ (b : ℕ)) :=
      hasSum_sum fun a _ => hasSum_sum fun b _ =>
        ((hsum a b).hasSum.mul_right _).mul_right _
    rw [← h.tsum_eq, ev]
    congr 1
    funext ν
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hev (ν 0) x hx, hev (ν 1) y hy, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [T]
    ring

end GlobalTheory.ConvSer
end

section

open Formalism.REAL

namespace GlobalTheory

theorem tensorStd_rel_adjoint_splitCasimir : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → GlRel Et ∧ (∀ a b x y, inner ℂ (Et a b x) y = inner ℂ x (Et b a y)) ∧ Om.IsSymmetric ∧ ∀ a b, Om * Et a b = Et a b * Om := by
  intro V _ _ _ n E Et Om hE hadj hEt hOm
  have hv : ∀ a b c d v, E a b (E c d v) = E c d (E a b v) +
      ((if b = c then E a d v else 0) - if d = a then E c b v else 0) := by
    intro a b c d v
    have h := LinearMap.congr_fun (hE a b c d) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← sub_eq_iff_eq_add', h]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    refine LinearMap.ext fun y => PiLp.ext fun k => ?_
    have h1 : ((if b = c then Et a d else 0) - if d = a then Et c b else 0 :
        Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) y k =
        (if b = c then Et a d y k else 0) - if d = a then Et c b y k else 0 := by
      split_ifs <;> simp
    rw [h1]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, hEt, map_add (f := _)]
    rw [hv a b c d]
    split_ifs <;> (try simp only [map_zero]) <;> abel
  · intro a b x y
    simp only [PiLp.inner_apply, hEt, inner_add_left, inner_add_right, Finset.sum_add_distrib, hadj]
    congr 1
    have h1 : ∀ c, inner ℂ (if c = a then x b else 0) (y c) =
        if c = a then inner ℂ (x b) (y c) else 0 := by
      intro c; split_ifs <;> simp
    have h2 : ∀ c, inner ℂ (x c) (if c = b then y a else 0) =
        if c = b then inner ℂ (x c) (y a) else 0 := by
      intro c; split_ifs <;> simp
    simp [h1, h2]
  · intro x y
    simp only [PiLp.inner_apply, hOm, sum_inner, inner_sum, hadj]
    exact Finset.sum_comm
  · intro a b
    refine LinearMap.ext fun y => PiLp.ext fun k => ?_

    simp only [Module.End.mul_apply, hEt, hOm, map_add (f := _), map_sum, Finset.sum_add_distrib]
    have h1 : ∀ c, E c k (E a b (y c)) = _ := fun c => hv c k a b (y c)
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, apply_ite (E _ k), map_zero]
    by_cases h : k = a
    · simp [h, add_assoc]
    · simp [h]

end GlobalTheory
end

section

open Formalism.REAL

namespace GlobalTheory

theorem _root_.GlobalTheory.tensor_dual_standard_rel : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))), _root_.Formalism.REAL.GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → _root_.Formalism.REAL.GlRel Et ∧ (∀ a b x y, inner ℂ (Et a b x) y = inner ℂ x (Et b a y)) ∧ Om.IsSymmetric ∧ ∀ a b, Om * Et a b = Et a b * Om := by
  intro V _ _ _ n E Et Om hE hsym hEt hOm
  have hE' : ∀ a b c d (v : V), E a b (E c d v) - E c d (E a b v) = (if b = c then E a d v else 0) - if d = a then E c b v else 0 := by
    intro a b c d v
    have := congrArg (fun T : Module.End ℂ V => T v) (hE a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    rw [this]; split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    ext y e
    have key : E a b (E c d (y.ofLp e)) = E c d (E a b (y.ofLp e)) + ((if b = c then E a d (y.ofLp e) else 0) - if d = a then E c b (y.ofLp e) else 0) := by
      have h := hE' a b c d (y.ofLp e); rw [sub_eq_iff_eq_add] at h; rw [h]; abel
    have hR : (((if b = c then Et a d else 0) - if d = a then Et c b else 0) y).ofLp e = (if b = c then (Et a d y).ofLp e else 0) - (if d = a then (Et c b y).ofLp e else 0) := by
      split_ifs <;> simp
    rw [hR]
    simp only [LinearMap.sub_apply, Module.End.mul_apply]
    rw [WithLp.ofLp_sub, Pi.sub_apply, hEt, hEt, hEt, hEt, hEt, hEt, map_sub, map_sub, key]
    split_ifs <;> simp only [hEt, map_zero, sub_zero, zero_sub] <;> subst_vars <;>
      first | abel1 | (exfalso; tauto) | (simp_all; done) | (split_ifs <;> subst_vars <;> first | abel1 | (exfalso; tauto) | (simp_all; done) | (simp_all; abel1))
  · intro a b x y
    simp only [PiLp.inner_apply, hEt, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib, hsym]
    have h1 : ∀ i, inner ℂ (if i = b then x.ofLp a else 0) (y.ofLp i) = if i = b then inner ℂ (x.ofLp a) (y.ofLp b) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    have h2 : ∀ i, inner ℂ (x.ofLp i) (if i = a then y.ofLp b else 0) = if i = a then inner ℂ (x.ofLp a) (y.ofLp b) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    simp only [h1, h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro x y
    simp only [PiLp.inner_apply, hOm, sum_inner, inner_sum, hsym]
    exact Finset.sum_comm
  · intro a b
    ext y e

    simp only [Module.End.mul_apply, hOm, hEt, map_sub, map_sum]
    have key : ∀ i, E e i (E a b (y.ofLp i)) = E a b (E e i (y.ofLp i)) + (if i = a then E e b (y.ofLp i) else 0) - (if b = e then E a i (y.ofLp i) else 0) := by
      intro i; have h := hE' e i a b (y.ofLp i); rw [sub_eq_iff_eq_add] at h; rw [h]; abel
    have h3 : ∀ i, E e i (if i = b then y.ofLp a else 0) = if i = b then E e b (y.ofLp a) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    simp only [key, h3, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : e = b
    · subst h; simp only [if_true]; abel
    · simp only [h, Ne.symm h, if_false, Finset.sum_const_zero]; abel

end GlobalTheory
end

section

namespace GlobalTheory.PrimaryCharacter

theorem exists_extend_of_injective {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  first
  | exact @_root_.GlobalTheory.ExtensionCharacter.exists_extension_character
  | exact _root_.GlobalTheory.ExtensionCharacter.exists_extension_character
  | (apply _root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExtensionCharacter.exists_extension_character ..)

theorem exists_factor_of_ker_le {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (χ : H →* Fˣ) (h : Φ.ker ≤ χ.ker) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  obtain ⟨κ, hκ⟩ := exists_extend_of_injective (QuotientGroup.kerLift Φ)
    (QuotientGroup.kerLift_injective Φ) (QuotientGroup.lift Φ.ker χ h)
  exact ⟨κ, fun x => hκ (QuotientGroup.mk x)⟩

end GlobalTheory.PrimaryCharacter
end
