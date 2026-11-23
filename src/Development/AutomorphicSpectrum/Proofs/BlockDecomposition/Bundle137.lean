module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle132
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

theorem e_upper_mul_pow_succ_eq {i j : Fin n} (hij : (j : ℕ) = i + 1) (m : ℕ) :
    e (i, j) * e (j, i) ^ (m + 1) =
      e (j, i) ^ (m + 1) * e (i, j) + ((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) -
        (((m : ℂ) + 1) * m) • e (j, i) ^ m := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hxy : e (i, j) * e (j, i) = e (j, i) * e (i, j) + (e (i, i) - e (j, j)) := by
    have := e_mul_sub_mul (i, j) (j, i)
    simp only [if_true] at this
    rw [← this]; abel
  have hh : ∀ p : ℕ, (e (i, i) - e (j, j)) * e (j, i) ^ p =
      e (j, i) ^ p * (e (i, i) - e (j, j)) - (2 * (p : ℂ)) • e (j, i) ^ p := by
    intro p
    rw [sub_mul, e_diag_mul_e_pow, e_diag_mul_e_pow, rootAt_lower_self hne, rootAt_lower_other hne,
      mul_sub]
    module
  induction m with
  | zero =>
    simp only [pow_zero, pow_one, one_mul, Nat.cast_zero, zero_add, one_smul, mul_zero, zero_smul,
      sub_zero]
    exact hxy
  | succ m ih =>
    have e1 : e (i, j) * e (j, i) ^ (m + 1 + 1) =
        e (j, i) * (e (i, j) * e (j, i) ^ (m + 1)) + (e (i, i) - e (j, j)) * e (j, i) ^ (m + 1) := by
      rw [pow_succ' _ (m + 1), ← mul_assoc, hxy, add_mul, mul_assoc]
    rw [e1, hh, ih]
    simp only [mul_sub, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ']
    push_cast
    module

theorem h_mul_sub_mem_Jp {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x) {i j : Fin n}
    (hij : (j : ℕ) = i + 1) :
    (e (i, i) - e (j, j)) * x - ((1 : ℂ) + (μ i : ℂ) - (μ j : ℂ)) • x ∈ Jp n := by
  have hi := hx i
  have hj := hx j
  have hd := rhoVec_sub (n := n) hij
  have key : (e (i, i) - e (j, j)) * x - ((1 : ℂ) + (μ i : ℂ) - (μ j : ℂ)) • x =
      x * (e (i, i) - algebraMap ℂ (U n) (rhoVec n i)) -
        x * (e (j, j) - algebraMap ℂ (U n) (rhoVec n j)) := by
    have h1 : e (i, i) * x = x * e (i, i) + (μ i : ℂ) • x := by rw [← hi]; abel
    have h2 : e (j, j) * x = x * e (j, j) + (μ j : ℂ) • x := by rw [← hj]; abel
    have h3 : rhoVec n i = rhoVec n j + 1 := by rw [← hd]; ring
    rw [sub_mul, h1, h2]
    simp only [mul_sub, ← Algebra.commutes, ← Algebra.smul_def, h3]
    module
  rw [key]
  exact vermaIdeal_le_Jp (Submodule.sub_mem _ (mul_e_sub_mem_vermaIdeal _ _ i)
    (mul_e_sub_mem_vermaIdeal _ _ j))

theorem natural_of_primitive {n : ℕ} (μ : Fin n → ℤ) (x : U n) (i j : Fin n) (hx : IsAdW μ x)
    (hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) (hxJ : x ∉ Jp n)
    (hij : (j : ℕ) = i + 1) (hN : ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n) :
    ∃ p : ℕ, 1 + μ i - μ j = (p : ℤ) := by
  classical
  have hp := Nat.find_spec hN
  have hmin := fun m => Nat.find_min hN (m := m)
  obtain ⟨q, hq⟩ : ∃ q, Nat.find hN = q + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => hxJ ?_
    rw [h0] at hp
    simpa using hp
  rw [hq] at hp
  have hqn : e (j, i) ^ q * x ∉ Jp n := hmin q (by omega)
  have hEx : e (i, j) * x ∈ Jp n := hup (i, j) (by
    simp only [IsUpper]; rw [Fin.lt_def, hij]; omega)
  set c : ℂ := (1 : ℂ) + (μ i : ℂ) - (μ j : ℂ) with hc
  have h1 := mul_mem_Jp (e (i, j)) hp
  have h2 := mul_mem_Jp (e (j, i) ^ (q + 1)) hEx
  have h3 := mul_mem_Jp (e (j, i) ^ q) (h_mul_sub_mem_Jp hx hij)
  have key : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) =
      e (i, j) * (e (j, i) ^ (q + 1) * x) - e (j, i) ^ (q + 1) * (e (i, j) * x) -
        ((q : ℂ) + 1) • (e (j, i) ^ q * ((e (i, i) - e (j, j)) * x - c • x)) := by
    rw [← mul_assoc (e (i, j)), e_upper_mul_pow_succ_eq hij q]
    simp only [mul_sub, sub_mul, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    module
  have hmem : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) ∈ Jp n := by
    rw [key]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) (Submodule.smul_mem _ _ h3)
  have hzero : ((q : ℂ) + 1) * (c - q) = 0 := by
    by_contra hne
    exact hqn ((Submodule.smul_mem_iff _ hne).1 hmem)
  have hq1 : (q : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  have hcq : c = q := sub_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_left hq1)
  refine ⟨q, ?_⟩
  have : ((1 + μ i - μ j : ℤ) : ℂ) = ((q : ℤ) : ℂ) := by
    push_cast
    exact hcq
  exact_mod_cast this

end GlobalTheory.CompanionTheory.PresRho
end
end

section

set_option maxSynthPendingDepth 1

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho.LowMeet

variable {n : ℕ}

theorem not_hasUpper {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : ¬ HasUpper m := by
  rintro ⟨a, ha, hne⟩
  exact not_lower_of_upper ha (hm a (Finsupp.mem_support_iff.2 hne))

theorem lowPart_eq {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : lowPart m = m := by
  ext a
  simp only [lowPart, Finsupp.filter_apply]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hm a (Finsupp.mem_support_iff.2 (Ne.symm hne)))

theorem diagExp_eq {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : diagExp m = 0 := by
  ext i
  rw [diagExp_apply]
  by_contra hne
  exact not_lower_of_diag (a := (i, i)) rfl (hm (i, i) (Finsupp.mem_support_iff.2 hne))

theorem recover (lam : Fin n → ℂ) {x : U n} (hx : x ∈ lowSpan n) :
    Finsupp.linearCombination ℂ (canon (n := n)) (vermaCoord lam x) = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [vermaCoord_canon_of_not lam (not_hasUpper hm), lowPart_eq hm, diagExp_eq hm]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | smul r x _ hx => rw [map_smul, map_smul, hx]

theorem eq_zero_of_mem (lam : Fin n → ℂ) {x : U n} (hx : x ∈ lowSpan n)
    (hJ : x ∈ vermaIdeal lam) : x = 0 := by
  rw [← recover lam hx, vermaCoord_vermaIdeal lam hJ, map_zero]

theorem canonSpan_lower_le (lo hi : ℕ) : canonSpan (IsLower (n := n)) lo hi ≤ lowSpan n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨m, hm, -, -, rfl⟩
  exact ⟨m, hm, rfl⟩

theorem word_mem_lowSpan {w : List (Fin n × Fin n)} (hw : ∀ a ∈ w, IsLower a) :
    word w ∈ lowSpan n :=
  canonSpan_lower_le _ _ (word_mem_canonSpan closed_lower w hw)

theorem isLower_simple {i j : Fin n} (hij : (j : ℕ) = i + 1) : IsLower (j, i) := by
  simp only [IsLower]; rw [Fin.lt_def, hij]; omega

theorem mul_sq_mem_lowSpan {a : Fin n × Fin n} (ha : IsLower a) {x : U n} (hx : x ∈ lowSpan n) :
    x * e a ^ 2 ∈ lowSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    have h : canon m * e a ^ 2 = word (expand m ++ [a, a]) := by
      rw [word_append, word_cons, word_singleton, pow_two]; rfl
    rw [h]
    refine word_mem_lowSpan fun b hb => ?_
    rcases List.mem_append.1 hb with hb | hb
    · exact hm b (mem_support_of_mem_expand hb)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hb
      rw [hb]; exact ha
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

def lowSq (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (v : U n) (i j : Fin n), v ∈ lowSpan n ∧ (j : ℕ) = i + 1 ∧
    v * e (j, i) ^ 2 = x}

theorem lowSq_le_lowSpan : lowSq n ≤ lowSpan n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, i, j, hv, hij, rfl⟩
  exact mul_sq_mem_lowSpan (isLower_simple hij) hv

theorem lowSq_le_sqSpan : lowSq n ≤ sqSpan n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨v, i, j, -, hij, rfl⟩
  exact ⟨v, i, j, hij, rfl⟩

theorem canon_mul_sq_mem (m : Fin n × Fin n →₀ ℕ) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    canon m * e (j, i) ^ 2 ∈ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  by_cases h : HasUpper m
  · refine Submodule.mem_sup_right ?_
    exact mul_pow_mem_vermaIdeal hij (rhoVec n) 1 (by rw [rhoVec_sub hij]; simp)
      (canon_mem_nPlusU h)
  · have hup : ∀ a ∈ upL n, m a = 0 := fun a ha => by
      by_contra hne; exact h ⟨a, mem_upL.1 ha, hne⟩
    set low := word (blockW (lowL n) m) with hlow
    have hlowS : low ∈ lowSpan n :=
      word_mem_lowSpan fun a ha => mem_lowL.1 (mem_of_mem_blockW ha).1
    set p := MvPolynomial.monomial (diagExp m) (1 : ℂ)
    set q := translate (fun k => ((2 : ℕ) : ℂ) * rootAt (j, i) k) p
    have hc : canon m * e (j, i) ^ 2 = low * e (j, i) ^ 2 * hcEmb q := by
      rw [canon_eq_triangular, blockW_eq_nil hup, word_nil, mul_one, mul_assoc,
        hcEmb_mul_e_pow, mul_assoc]
    have hs : canon m * e (j, i) ^ 2 =
        MvPolynomial.eval (rhoVec n) q • (low * e (j, i) ^ 2) +
          low * e (j, i) ^ 2 * (hcEmb q - algebraMap ℂ (U n) (MvPolynomial.eval (rhoVec n) q)) := by
      rw [hc, mul_sub, ← Algebra.commutes, ← Algebra.smul_def]
      abel
    rw [hs]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ ?_))
      (Submodule.mem_sup_right
        (mul_mem_vermaIdeal _ _ (hcEmb_sub_eval_mem_vermaIdeal (rhoVec n) q)))
    exact Submodule.subset_span ⟨low, i, j, hlowS, hij, rfl⟩

theorem mul_sq_mem (u : U n) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    u * e (j, i) ^ 2 ∈ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  have hu : u ∈ Submodule.span ℂ (Set.range (canon (n := n))) := by
    rw [span_canon_eq_top]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact canon_mul_sq_mem m hij
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem Jp_le : Jp n ≤ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  refine sup_le le_sup_right (Submodule.span_le.2 ?_)
  rintro _ ⟨u, i, j, hij, rfl⟩
  exact mul_sq_mem u hij

theorem mem_sqSpan_of_mem_lowSpan_of_mem_Jp : ∀ {n : ℕ} (x : U n), x ∈ lowSpan n → x ∈ Jp n →
    x ∈ sqSpan n := by
  intro n x hx hJ
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 (Jp_le hJ)
  have ht0 : t = 0 := by
    refine eq_zero_of_mem (rhoVec n) ?_ ht
    have := Submodule.sub_mem _ hx (lowSq_le_lowSpan hs)
    rwa [add_sub_cancel_left] at this
  rw [ht0, add_zero]
  exact lowSq_le_sqSpan hs

end GlobalTheory.CompanionTheory.PresRho.LowMeet
end

section

set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

def adL (F u : U n) : U n := F * u - u * F

theorem adL_zero (F : U n) : adL F 0 = 0 := by simp [adL]

theorem adL_sub (F u v : U n) : adL F (u - v) = adL F u - adL F v := by
  simp only [adL, mul_sub, sub_mul]; abel

theorem adL_neg (F u : U n) : adL F (-u) = - adL F u := by
  simp only [adL, mul_neg, neg_mul]; abel

theorem adL_e (i j c d : Fin n) :
    adL (e (j, i)) (e (c, d)) =
      (if i = c then e (j, d) else 0) - (if d = j then e (c, i) else 0) :=
  e_mul_sub_mul (j, i) (c, d)

theorem adL_iter_e {i j : Fin n} (hij : i ≠ j) (a : Fin n × Fin n) :
    (adL (e (j, i)))^[3] (e a) = 0 := by
  obtain ⟨c, d⟩ := a
  show adL (e (j, i)) (adL (e (j, i)) (adL (e (j, i)) (e (c, d)))) = 0
  have hji : j ≠ i := hij.symm
  by_cases h1 : i = c <;> by_cases h2 : d = j
  · subst h1; subst h2
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji]
  · subst h1
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h2]
  · subst h2
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h1]
  · simp [adL_e, adL_sub, adL_neg, adL_zero, h1, h2]

theorem pow_mul_mem_Jp_of_le {F w : U n} {N N' : ℕ} (h : N ≤ N') (hw : F ^ N * w ∈ Jp n) :
    F ^ N' * w ∈ Jp n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [pow_add, mul_assoc]
  exact mul_mem_Jp _ hw

theorem exists_pow_mul_mul_mem (F : U n) (s : ℕ) :
    ∀ (r M : ℕ) (u y : U n), r + M = s → (adL F)^[r] u = 0 → F ^ M * y ∈ Jp n →
      ∃ N : ℕ, F ^ N * (u * y) ∈ Jp n := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro r M u y hs hu hy
    rcases M with _ | M
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul] at hy ⊢
      exact mul_mem_Jp u hy
    rcases r with _ | r
    · refine ⟨0, ?_⟩
      have : u = 0 := hu
      simp [this]
    obtain ⟨N₁, h₁⟩ := ih (r + 1 + M) (by omega) (r + 1) M u (F * y) rfl hu
      (by rw [← mul_assoc, ← pow_succ]; exact hy)
    obtain ⟨N₂, h₂⟩ := ih (r + (M + 1)) (by omega) r (M + 1) (adL F u) y rfl
      (by rw [← Function.iterate_succ_apply]; exact hu) hy
    refine ⟨max N₁ N₂ + 1, ?_⟩
    have key : F ^ (max N₁ N₂ + 1) * (u * y) =
        F ^ max N₁ N₂ * (u * (F * y)) + F ^ max N₁ N₂ * (adL F u * y) := by
      rw [pow_succ, ← mul_add, mul_assoc]
      congr 1
      simp only [adL, sub_mul, mul_assoc]
      abel
    rw [key]
    exact Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
      (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)

theorem lower_locally_nilpotent {n : ℕ} (i j : Fin n) (x : U n) (hij : (j : ℕ) = i + 1) :
    ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n := by
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have step : ∀ v : U n, ∀ y : U n, (∃ N : ℕ, e (j, i) ^ N * y ∈ Jp n) →
      ∃ N : ℕ, e (j, i) ^ N * (v * y) ∈ Jp n := by
    intro v
    induction v using U.induction with
    | halg r =>
      rintro y ⟨N, hN⟩
      refine ⟨N, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]
      exact Submodule.smul_mem _ r hN
    | hι X =>
      intro y hy
      obtain ⟨M, hM⟩ := hy
      have hsum : ∀ t : Finset (Fin n × Fin n), ∃ N : ℕ, e (j, i) ^ N *
          ((∑ a ∈ t, X a.1 a.2 • e (n := n) a) * y) ∈ Jp n := by
        intro t
        induction t using Finset.induction_on with
        | empty => exact ⟨0, by simp⟩
        | insert a t ha ih =>
          obtain ⟨N₁, h₁⟩ := ih
          obtain ⟨N₂, h₂⟩ := exists_pow_mul_mul_mem (e (j, i)) (3 + M) 3 M (e a) y rfl
            (adL_iter_e hne a) hM
          refine ⟨max N₁ N₂, ?_⟩
          rw [Finset.sum_insert ha, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂))
            (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
      rw [ι_eq_sum_e]
      exact hsum Finset.univ
    | hmul a b ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb _ hy)
    | hadd a b ha hb =>
      intro y hy
      obtain ⟨N₁, h₁⟩ := ha y hy
      obtain ⟨N₂, h₂⟩ := hb y hy
      refine ⟨max N₁ N₂, ?_⟩
      rw [add_mul, mul_add]
      exact Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
        (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)
  have h1 : ∃ N : ℕ, e (j, i) ^ N * (1 : U n) ∈ Jp n :=
    ⟨2, by simpa using mul_sq_mem_Jp (1 : U n) hij⟩
  simpa using step x 1 h1

end GlobalTheory.CompanionTheory.PresRho
end
end

section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho.NormIneq

variable {n : ℕ}

theorem casC_eq_sum (σ : Fin n → ℂ) :
    casC σ = ∑ a, σ a ^ 2 + ∑ a, σ a * ((n : ℂ) - 1 - 2 * ((a : ℕ) : ℂ)) :=
  _root_.UpperTheory.Reformulated.B.CasimirElement.main σ

theorem sum_wt_mul (m : Fin n × Fin n →₀ ℕ) (f : Fin n → ℤ) :
    ∑ k, wt m k * f k = m.sum fun a c => (c : ℤ) * (f a.1 - f a.2) := by
  simp only [wt, Finsupp.sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [rootAt, mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem lt_of_step {f : Fin n → ℤ} (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j < f i) :
    ∀ (d : ℕ) (i j : Fin n), (j : ℕ) = i + d + 1 → f j < f i := by
  intro d
  induction d with
  | zero => intro i j hij; exact h i j (by simpa using hij)
  | succ d ih =>
    intro i j hij
    have hk : (i : ℕ) + d + 1 < n := by have := j.2; omega
    have h1 := ih i ⟨(i : ℕ) + d + 1, hk⟩ rfl
    have h2 := h ⟨(i : ℕ) + d + 1, hk⟩ j (by simp only; omega)
    exact h2.trans h1

theorem eq_zero_of_casC_eq {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (hm : LowExp m)
    (hp : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ p : ℕ, 1 + wt m i - wt m j = (p : ℤ))
    (hc : casC (fun k => rhoVec n k + (wt m k : ℂ)) = casC (rhoVec n)) : m = 0 := by
  by_contra hne
  obtain ⟨f, hf⟩ : ∃ f : Fin n → ℤ, ∀ k, f k = 2 * ((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ)) + wt m k :=
    ⟨_, fun _ => rfl⟩
  have hstep : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j < f i := by
    intro i j hij
    obtain ⟨p, hp⟩ := hp i j hij
    have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
    have hij' : ((j : ℕ) : ℤ) = ((i : ℕ) : ℤ) + 1 := by exact_mod_cast hij
    rw [hf, hf, hij']
    linarith
  have hneg : ∑ k, wt m k * f k < 0 := by
    rw [sum_wt_mul]
    refine Finset.sum_neg (fun a ha => ?_) (Finsupp.support_nonempty_iff.2 hne)
    have hlow : (a.2 : ℕ) < a.1 := hm a ha
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (a.1 : ℕ) = a.2 + d + 1 := ⟨(a.1 : ℕ) - a.2 - 1, by omega⟩
    have hlt := lt_of_step hstep d a.2 a.1 hd
    have hpos : (0 : ℤ) < (m a : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 ha)
    exact mul_neg_of_pos_of_neg hpos (by linarith)
  have key : ((∑ k, wt m k * f k : ℤ) : ℂ) =
      casC (fun k => rhoVec n k + (wt m k : ℂ)) - casC (rhoVec n) := by
    rw [casC_eq_sum, casC_eq_sum, add_sub_add_comm, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    push_cast
    simp only [rhoVec]
    ring
  rw [hc, sub_self] at key
  have : ∑ k, wt m k * f k = 0 := by exact_mod_cast key
  omega

end GlobalTheory.CompanionTheory.PresRho.NormIneq
end
