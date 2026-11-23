module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.FramesOf
public import Formalism.SharpRestriction.GrowthBounds.SourceCleaning
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

theorem numeric_product_inequality (A B u : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hu1 : u ≤ 1) (hu : 1 - B ≤ u) :
    1 - A - B ≤ (1 - A) * u := by
  rcases le_or_gt A 1 with h | h
  · have h1 : (1 - A) * (1 - B) ≤ (1 - A) * u := mul_le_mul_of_nonneg_left hu (by linarith)
    have h2 := mul_nonneg hA hB
    linarith
  · have h1 : (A - 1) * u ≤ (A - 1) * 1 := mul_le_mul_of_nonneg_left hu1 (by linarith)
    linarith

theorem num_size (C k r N Q cS c0 z Y a : ℝ) (hC : 2 ≤ C) (hk : 1 ≤ k) (hr : 2 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hcS : 8 ≤ cS) (hc0 : 0 ≤ c0) (hz : 0 ≤ z) (hY : 2 ≤ Y)
    (hsz : C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + (r * N * c0 + z)) * Y ≤ a) :
    1 ≤ a ∧ N * k * c0 * Y ≤ a := by
  have hk3 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have hr21 : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ (by linarith)
  have hQ5 : (1 : ℝ) ≤ Q ^ 5 := one_le_pow₀ hQ
  have hk0 : 0 ≤ k := by linarith
  have hN0 : 0 ≤ N := by linarith
  have e1 : k ≤ C * k ^ 3 := le_trans hk3 (le_mul_of_one_le_left (by positivity) (by linarith))
  have e2 : k ≤ C * k ^ 3 * r ^ 2 := le_trans e1 (le_mul_of_one_le_right (by positivity) hr21)
  have e3 : k * N ≤ C * k ^ 3 * r ^ 2 * N := mul_le_mul_of_nonneg_right e2 hN0
  have hP : k * N ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 := le_trans e3 (le_mul_of_one_le_right (by positivity) hQ5)
  have hkN : 1 ≤ k * N := one_le_mul_of_one_le_of_one_le hk hN
  have hrN : 1 ≤ r * N := one_le_mul_of_one_le_of_one_le (by linarith) hN
  have hom : c0 ≤ r * N * c0 + z := by
    have : c0 ≤ r * N * c0 := le_mul_of_one_le_left hc0 hrN
    linarith
  have hS : 0 ≤ cS + (r * N * c0 + z) := by linarith
  have ha0 : k * N * (cS + (r * N * c0 + z)) * Y ≤ a :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP hS) (by linarith)) hsz
  constructor
  · have e4 : 1 ≤ k * N * (cS + (r * N * c0 + z)) := one_le_mul_of_one_le_of_one_le hkN (by linarith)
    have e5 : 1 ≤ k * N * (cS + (r * N * c0 + z)) * Y := one_le_mul_of_one_le_of_one_le e4 (by linarith)
    linarith
  · refine le_trans ?_ ha0
    have e6 : k * N * c0 ≤ k * N * (cS + (r * N * c0 + z)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e7 := mul_le_mul_of_nonneg_right e6 (show (0 : ℝ) ≤ Y by linarith)
    calc N * k * c0 * Y = k * N * c0 * Y := by ring
      _ ≤ _ := e7

theorem level_bound_numeric (C Ct0 r N X c0 z : ℝ) (hC2 : 2 ≤ C) (hC3 : Ct0 ≤ C) (hr : 2 ≤ r) (hN : 0 ≤ N) (hX : 0 ≤ X)
    (hc0 : 0 ≤ c0) : Ct0 * N * X + N * c0 + (r * N * c0 + z) ≤ C * r * N * (X + c0) + z := by
  have hCr : Ct0 ≤ C * r := le_trans hC3 (le_mul_of_one_le_right (by linarith) (by linarith))
  have hCr2 : r + 1 ≤ C * r := by
    have : 2 * r ≤ C * r := mul_le_mul_of_nonneg_right hC2 (by linarith)
    linarith
  have e1 : Ct0 * N * X ≤ C * r * N * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCr hN) hX
  have e2 : (r + 1) * (N * c0) ≤ C * r * (N * c0) := mul_le_mul_of_nonneg_right hCr2 (mul_nonneg hN hc0)
  have e3 : C * r * N * (X + c0) = C * r * N * X + C * r * (N * c0) := by ring
  have e4 : (r + 1) * (N * c0) = r * N * c0 + N * c0 := by ring
  rw [e3]
  linarith

theorem num_count (C Cr r k Y a c0 : ℝ) (n : ℕ) (hCr : 0 < Cr) (hC5 : Cr + 1 ≤ C) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hn : 1 ≤ (n : ℝ)) (hY : 2 ≤ Y) (hc0 : 0 ≤ c0) (ha : 1 ≤ a) (ha2 : (n : ℝ) * k * c0 * Y ≤ a) :
    1 - C * n * r ^ 2 * k / Y ≤ (1 - Cr * n * r ^ 2 * k / Y) * (1 - k * c0 / a) ^ n := by
  have hYpos : 0 < Y := by linarith
  have hapos : 0 < a := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hB0 : 0 ≤ (n : ℝ) * r ^ 2 * k / Y := by positivity
  have hB1 : 1 / Y ≤ (n : ℝ) * r ^ 2 * k / Y := by
    apply div_le_div_of_nonneg_right _ hYpos.le
    have hr21 : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ (by linarith)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn hr21) hk
  have hy0 : 0 ≤ k * c0 / a := by positivity
  have hNy : (n : ℝ) * (k * c0 / a) ≤ 1 / Y := by
    rw [le_div_iff₀ hYpos]
    have : (n : ℝ) * (k * c0 / a) * Y = ((n : ℝ) * k * c0 * Y) / a := by ring
    rw [this, div_le_one hapos]
    exact ha2
  have hy1 : k * c0 / a ≤ 1 := by
    have e1 : k * c0 / a ≤ (n : ℝ) * (k * c0 / a) := le_mul_of_one_le_left hy0 hn
    have e2 : 1 / Y ≤ 1 := by
      rw [div_le_one hYpos]; linarith
    linarith
  have hu1 : (1 - k * c0 / a) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hu : 1 - (n : ℝ) * r ^ 2 * k / Y ≤ (1 - k * c0 / a) ^ n := by
    have hb := one_add_mul_le_pow (a := -(k * c0 / a)) (by linarith) n
    have e2 : (1 : ℝ) + -(k * c0 / a) = 1 - k * c0 / a := by ring
    rw [e2] at hb
    linarith
  have hAeq : Cr * n * r ^ 2 * k / Y = Cr * ((n : ℝ) * r ^ 2 * k / Y) := by ring
  have hCeq : C * n * r ^ 2 * k / Y = C * ((n : ℝ) * r ^ 2 * k / Y) := by ring
  rw [hAeq, hCeq]
  have h3 := numeric_product_inequality (Cr * ((n : ℝ) * r ^ 2 * k / Y)) ((n : ℝ) * r ^ 2 * k / Y) ((1 - k * c0 / a) ^ n)
    (mul_nonneg hCr.le hB0) hB0 hu1 hu
  have h4 : (Cr + 1) * ((n : ℝ) * r ^ 2 * k / Y) ≤ C * ((n : ℝ) * r ^ 2 * k / Y) :=
    mul_le_mul_of_nonneg_right hC5 hB0
  linarith

theorem num : Num := by
  intro C Ct0 CD1 Cr h0 h1 h2 hC2 hC3 hC4 hC5 p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hH
  obtain ⟨hp, hr, _, hN1, _, hY, _, hk, _, hD, hc, hsz⟩ := hH
  have hN1pos : 1 ≤ orbitWindowCount r de h x := by unfold orbitWindowCount; omega
  have hNnat : 1 ≤ TT.card := by
    rcases Nat.eq_zero_or_pos TT.card with h0' | h0'
    · rw [h0', Nat.mul_zero] at hN1
      have : 0 < orbitWindowCount r de h x ^ 2 := by positivity
      omega
    · exact h0'
  have hN : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hNnat
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : 1 ≤ m + 1 := by omega
    exact_mod_cast this
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hp1 : (1 : ℝ) < p := by
    have : 1 < p := by omega
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by linarith
  have hQ : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1.le
  have hY2 : (2 : ℝ) ≤ Y := le_trans hr2 hY
  have hc0 : (0 : ℝ) ≤ c0 := Nat.cast_nonneg _
  have hz : (0 : ℝ) ≤ 2 * (r : ℝ) * n' * cpp := by positivity
  have hcS : (8 : ℝ) ≤ cStar := by
    have : 8 ≤ cStar := by omega
    exact_mod_cast this
  obtain ⟨ha1, ha2⟩ := num_size C _ _ _ _ _ _ _ Y a hC2 hk1 hr2 hN hQ hcS hc0 hz hY2 hsz
  have hapos : 0 < a := by linarith
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha1
  have hlogb : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 ha1
  refine ⟨?_, mul_nonneg (by linarith) hc0, ?_, ?_⟩
  · unfold t0 om tableLineDegreeFive.tBound
    have hLa : 0 ≤ tableLineDegreeFive.La C (orbitWindowCount r de h x) a := by
      unfold tableLineDegreeFive.La
      have : 0 ≤ C := by linarith
      positivity
    have hX0 : 0 ≤ tableLineDegreeFive.La C (orbitWindowCount r de h x) a * a / ((p : ℝ) * ((m + 1 : ℕ) : ℝ)) + a * (p : ℝ) ^ (-(L₁ : ℤ)) +
        ((m + 1 : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x := by
      have e1 : 0 ≤ tableLineDegreeFive.La C (orbitWindowCount r de h x) a * a / ((p : ℝ) * ((m + 1 : ℕ) : ℝ)) := by positivity
      have e2 : 0 ≤ a * (p : ℝ) ^ (-(L₁ : ℤ)) := by positivity
      have e3 : 0 ≤ ((m + 1 : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x := by positivity
      linarith
    have key := level_bound_numeric C Ct0 r TT.card _ c0 (2 * (r : ℝ) * n' * cpp) hC2 hC3 hr2 (by linarith) hX0 hc0
    refine le_trans key (le_of_eq ?_)
    ring
  · refine le_trans ?_ hD
    have e1 : CD1 * (TT.card : ℝ) ≤ C * (TT.card : ℝ) := mul_le_mul_of_nonneg_right hC4 (by linarith)
    have e2 : CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 ≤ C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right e1 (by positivity)
    exact mul_le_mul_of_nonneg_right e2 hlogb
  · exact num_count C Cr r _ Y a c0 TT.card h2 hC5 hr2 hk1 hN hY2 hc0 ha1 ha2

end Formalism.MainNotions.Pf14
end
end

section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem getElem_ge_of_many (D : List ℤ) (hD : D.Pairwise (· > ·)) (T : Finset ℤ) (b : ℤ)
    (hT : ∀ z ∈ T, z ∈ D ∧ b ≤ z) (l : ℕ) (hl : l < T.card) (hlen : l < D.length) : b ≤ D[l] := by
  by_contra hlt
  push_neg at hlt
  have hsub : T ⊆ (D.take l).toFinset := by
    intro z hz
    obtain ⟨hzD, hbz⟩ := hT z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hzD
    have hil : i < l := by
      by_contra h
      push_neg at h
      rcases h.lt_or_eq with h | h
      · have := List.pairwise_iff_getElem.1 hD l i hlen hi h
        linarith
      · have e : D[l] = D[i] := by simp [h]
        linarith
    have hi' : i < (D.take l).length := by simp; omega
    have hm := List.getElem_mem hi'
    simp only [List.getElem_take] at hm
    exact List.mem_toFinset.2 hm
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le (D.take l)
  simp only [List.length_take] at h2
  omega

section Fr

variable {n' r : ℕ} [NeZero n']

theorem fr_mono' {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → F.fr j 0 ≤ F.fr j i := by
  intro i hi
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j i hi))

theorem fr_lt {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) :
    ∀ k i, i < k → k < r → F.fr j i < F.fr j k := by
  intro k i hik hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hik with h | h
    · exact lt_trans (ih h (by omega)) (hV.2.2.1 j k hk)
    · subst h
      exact hV.2.2.1 j i hk

theorem seg_of {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (s : ℤ) :
    ∃ j : ℤ, F.fr (j - 1) (r - 1) < s ∧ s ≤ F.fr j (r - 1) := by
  classical
  have hn : (1 : ℤ) ≤ (n' : ℤ) := by
    have : n' ≠ 0 := NeZero.ne n'
    omega
  have hstep : ∀ j : ℤ, F.fr j (r - 1) < F.fr (j + 1) (r - 1) := by
    intro j
    exact lt_of_lt_of_le (hV.2.2.2.1 j) (fr_mono' hV (j + 1) (r - 1) (by omega))
  have hmono : StrictMono (fun j : ℤ => F.fr j (r - 1)) := strictMono_int_of_lt_succ hstep
  have hup : ∀ m : ℕ, F.fr 0 (r - 1) + m ≤ F.fr ((m : ℤ) * F.J) (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hV.2.1 ((m : ℤ) * F.J) (r - 1)
      rw [show ((m + 1 : ℕ) : ℤ) * (F.J : ℤ) = (m : ℤ) * F.J + F.J by push_cast; ring, h]
      push_cast
      omega
  have hdown : ∀ m : ℕ, F.fr (-((m : ℤ) * F.J)) (r - 1) + m ≤ F.fr 0 (r - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hV.2.1 (-(((m + 1 : ℕ) : ℤ) * F.J)) (r - 1)
      rw [show -(((m + 1 : ℕ) : ℤ) * (F.J : ℤ)) + F.J = -((m : ℤ) * F.J) by push_cast; ring] at h
      push_cast at h ⊢
      omega
  have hP : ∃ j : ℤ, s ≤ F.fr j (r - 1) := by
    refine ⟨((s - F.fr 0 (r - 1)).toNat : ℤ) * F.J, ?_⟩
    have := hup (s - F.fr 0 (r - 1)).toNat
    omega
  have hB : ∃ b : ℤ, ∀ j : ℤ, s ≤ F.fr j (r - 1) → b ≤ j := by
    refine ⟨-(((F.fr 0 (r - 1) - s + 1).toNat : ℤ) * F.J), fun j hj => ?_⟩
    have h1 := hdown (F.fr 0 (r - 1) - s + 1).toNat
    by_contra hlt
    push_neg at hlt
    have h2 : F.fr j (r - 1) < F.fr (-(((F.fr 0 (r - 1) - s + 1).toNat : ℤ) * F.J)) (r - 1) := hmono hlt
    omega
  obtain ⟨j, hj, hmin⟩ := Int.exists_least_of_bdd hB hP
  refine ⟨j, ?_, hj⟩
  by_contra h
  push_neg at h
  have := hmin (j - 1) h
  omega

theorem evensBefore_pairwise (F : Frames n' r) (s : ℤ) : (evensBefore F s).Pairwise (· > ·) := by
  unfold evensBefore
  rw [List.pairwise_reverse]
  exact (Finset.sortedLT_sort _).pairwise

theorem arow_near {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hr : 1 ≤ r) (hG : G' ≤ n') (s : ℤ) (l : ℕ) (hl : l < r) : (s - Arow F s l).toNat ≤ G' := by
  obtain ⟨-, hV, hG', -, -⟩ := hF
  obtain ⟨j, hj1, hj2⟩ := seg_of hV hr s
  unfold Arow
  by_cases hlen : l < (evensBefore F s).length
  · rw [List.getD_eq_getElem _ _ hlen]
    have hrn : (G' : ℤ) ≤ (r : ℤ) * (n' : ℤ) := by
      have : G' ≤ r * n' := le_trans hG (by nlinarith)
      exact_mod_cast this
    have key : s - (G' : ℤ) ≤ (evensBefore F s)[l] := by
      refine getElem_ge_of_many (evensBefore F s) (evensBefore_pairwise F s)
        ((Finset.range r).image (fun i => F.fr (j - 1) i)) (s - G') ?_ l ?_ hlen
      · intro z hz
        simp only [Finset.mem_image, Finset.mem_range] at hz
        obtain ⟨i, hi, rfl⟩ := hz
        have h0 := fr_mono' hV (j - 1) i hi
        have h1 : F.fr (j - 1) i ≤ F.fr (j - 1) (r - 1) := by
          rcases Nat.lt_or_ge i (r - 1) with h | h
          · exact le_of_lt (fr_lt hV (j - 1) (r - 1) i h (by omega))
          · have : i = r - 1 := by omega
            rw [this]
        have h2 := hG' j
        have h3 := hV.2.2.2.2.1 (j - 1) i hi
        refine ⟨?_, by omega⟩
        simp only [evensBefore, List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨by omega, by omega⟩, h3.1, h3.2⟩
      · rw [Finset.card_image_of_injOn]
        · simpa using hl
        · intro a ha b hb hab
          simp only [Finset.coe_range, Set.mem_Iio] at ha hb
          simp only at hab
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · have := fr_lt hV (j - 1) b a h hb
            omega
          · have := fr_lt hV (j - 1) a b h ha
            omega
    omega
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

theorem twist_of {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hr : 1 ≤ r) (hG : G' ≤ n') (p : ℕ) (hp : 1 ≤ p) : TwistBound p F (p ^ G') := by
  refine ⟨fun j => ?_, fun s _ l hl => Nat.pow_le_pow_right (by omega) (arow_near hF hr hG s.val l hl)⟩
  unfold Qj zF
  apply Nat.pow_le_pow_right (by omega)
  have h1 := hF.2.2.1 (j + 1)
  have h2 := fr_mono' hF.2.1 j (r - 1) (by omega)
  simp only [add_sub_cancel_right] at h1
  omega

end Fr

end Formalism.MainNotions.Pf14
end
end
