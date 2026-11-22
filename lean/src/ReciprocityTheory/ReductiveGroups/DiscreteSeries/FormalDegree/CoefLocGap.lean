import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

open Formalism.MainNotions.CayleySignature

theorem lt_sub_of_increments {m : ℕ} (b : Fin m → ℝ) (G : ℝ) (hG : 0 < G)
    (h : ∀ (j : Fin m) (hj : j.val + 1 < m), G < b ⟨j.val + 1, hj⟩ - b j) :
    ∀ i j : Fin m, i < j → G < b j - b i := by
  cases m with
  | zero => exact fun i => Fin.elim0 i
  | succ m =>
    have increasing : StrictMono b := Fin.strictMono_iff_lt_succ.2 fun a =>
      sub_pos.mp (hG.trans (h a.castSucc (Nat.succ_lt_succ a.isLt)))
    intro i j hij
    have next_le : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hij
    exact (h i (next_le.trans_lt j.isLt)).trans_le
      (sub_le_sub_right (increasing.monotone (Fin.le_iff_val_le_val.2 next_le)) _)


theorem lt_abs_sub_of_increments {m : ℕ} (b : Fin m → ℝ) (G : ℝ) (hG : 0 < G)
    (h : ∀ (j : Fin m) (hj : j.val + 1 < m), G < b ⟨j.val + 1, hj⟩ - b j)
    (i j : Fin m) (hij : i ≠ j) : G < |b i - b j| := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · rw [abs_sub_comm]
    exact (lt_sub_of_increments b G hG h i j hij).trans_le (le_abs_self _)
  · exact (lt_sub_of_increments b G hG h j i hji).trans_le (le_abs_self _)


theorem cayley_weight_high_index (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (i : Fin (2 * r + k + 1)) (hi : ¬ i.val < k - 1) :
    lam48 k r v b i = -b ⟨i.val - (k - 1), by have := i.isLt; omega⟩ := by
  unfold lam48
  exact dif_neg hi

theorem gapAtLeast_of_increments (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (G : ℝ) (hG : 0 < G)
    (hanti : StrictAnti (lam48 k r v b))
    (hb : ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2), G < b ⟨j.val + 1, hj⟩ - b j) :
    GapAtLeast (eps48 k r) (lam48 k r v b) G := by
  have key : ∀ a c : Fin (2 * r + k + 1), a.val < k - 1 → ¬ c.val < k - 1 → (c.val - (k - 1)) % 2 = 1 →
      G ≤ |lam48 k r v b a - lam48 k r v b c| := by
    intro a c ha hc hpar
    have hk : k - 1 < 2 * r + k + 1 := by omega
    have h1 := hanti (show a < ⟨k - 1, hk⟩ by rw [Fin.lt_def]; exact ha)
    rw [cayley_weight_high_index k r v b ⟨k - 1, hk⟩ (by simp)] at h1
    simp only [Nat.sub_self] at h1
    rw [cayley_weight_high_index k r v b c hc]
    have h2 := lt_sub_of_increments b G hG hb ⟨0, by omega⟩ ⟨c.val - (k - 1), by have := c.isLt; omega⟩
      (by rw [Fin.lt_def]; simp only; omega)
    refine le_trans ?_ (le_abs_self _)
    linarith
  intro a c hac
  wlog horder : a ≤ c generalizing a c
  · simpa only [abs_sub_comm] using this c a hac.symm (le_of_not_ge horder)
  by_cases ha : a.val < k - 1
  · by_cases hc : c.val < k - 1
    · exact (hac (by simp only [eps48, if_pos ha, if_pos hc])).elim
    have hp : (c.val - (k - 1)) % 2 = 1 := by
      by_contra hne
      exact hac (by simp [eps48, ha, hc, show (c.val - (k - 1)) % 2 = 0 by omega])
    exact key a c ha hc hp
  · have hc : ¬ c.val < k - 1 := fun h => ha (lt_of_le_of_lt horder h)
    rw [cayley_weight_high_index k r v b a ha, cayley_weight_high_index k r v b c hc, neg_sub_neg]
    refine (lt_abs_sub_of_increments b G hG hb _ _ ?_).le
    intro heq
    have hv := congrArg Fin.val heq
    exact hac (congrArg (eps48 k r) (Fin.ext (by simp only at hv; omega)))


theorem q_le_of_cayley_signature (k r : ℕ) : qOf (eps48 k r) ≤ r + 1 := by
  have hodd : ∀ x : Fin (2 * r + k + 1), eps48 k r x = false →
      ¬ x.val < k - 1 ∧ (x.val - (k - 1)) % 2 = 1 := by
    intro x hx
    unfold eps48 at hx
    by_cases h1 : x.val < k - 1
    · rw [if_pos h1] at hx
      exact absurd hx (by decide)
    · rw [if_neg h1] at hx
      refine ⟨h1, ?_⟩
      have h2 : ¬ ((x.val - (k - 1)) % 2 = 0) := by simpa using hx
      omega
  unfold qOf
  calc (Finset.univ.filter fun a => eps48 k r a = false).card
      ≤ (Finset.range (r + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun a : Fin (2 * r + k + 1) => (a.val - (k - 1)) / 2)
        · intro a _
          simp only [Finset.mem_coe, Finset.mem_range]
          have := a.isLt
          omega
        · intro a ha c hc hac
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hc
          have h1 := hodd a ha
          have h2 := hodd c hc
          dsimp only at hac
          apply Fin.ext
          omega
    _ = r + 1 := Finset.card_range _

theorem cubic_bound_of_gap_nat (n r t M : ℕ) (hM : M = n + (2 * r + 2) * t) (ht : n + 5 ≤ t) :
    96 * n ^ 2 * (r + 1) ≤ 2 * M ^ 3 := by
  subst hM
  have ht2 : 2 * t ≤ (2 * r + 2) * t := Nat.mul_le_mul (by omega) le_rfl
  have hr : 10 * (r + 1) ≤ (2 * r + 2) * t := by
    calc 10 * (r + 1) ≤ (2 * r + 2) * 5 := by omega
      _ ≤ (2 * r + 2) * t := Nat.mul_le_mul le_rfl (by omega)
  set X := (2 * r + 2) * t with hX
  have h3 : 3 * n ≤ n + X := by omega
  have h10 : 10 * (r + 1) ≤ n + X := by omega
  calc 96 * n ^ 2 * (r + 1) ≤ 2 * ((3 * n) * (3 * n) * (10 * (r + 1))) := by
        nlinarith [Nat.zero_le (n ^ 2 * r), Nat.zero_le (n ^ 2)]
    _ ≤ 2 * ((n + X) * (n + X) * (n + X)) := by gcongr
    _ = 2 * (n + X) ^ 3 := by ring

/-- The operator-norm integrability threshold is largest at the upper bound
for the split rank. -/
theorem weighted_gap_threshold_le (n q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r)
    (hr : 1 ≤ r) (hn : r ≤ n) :
    8 * Real.sqrt (2 * q) * (4 * n ^ 2 * Real.sqrt (2 * r) + 2 * n * q) ≤ 96 * n ^ 2 * r := by
  let s := Real.sqrt (2 * r)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 2 * r := Real.sq_sqrt (by linarith)
  have hs_one : 1 ≤ s := by nlinarith
  have hn_nonneg : 0 ≤ n := by linarith
  have hs_le : Real.sqrt (2 * q) ≤ s := Real.sqrt_le_sqrt (by linarith)
  have hq_le : q ≤ n * s := (hqr.trans hn).trans (le_mul_of_one_le_right hn_nonneg hs_one)
  calc
    _ ≤ 8 * s * (6 * n ^ 2 * s) :=
      mul_le_mul (by gcongr) (by nlinarith [mul_le_mul_of_nonneg_left hq_le hn_nonneg])
        (by positivity) (by positivity)
    _ = _ := by linear_combination 48 * n ^ 2 * hs_sq

theorem cayley_weight_gap (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (hlam : Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b)) (hgap : Formalism.MainNotions.CayleySignature.GapBig k r b) :
    ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) h ∧
      (1 ≤ S7.q0 (Formalism.MainNotions.CayleySignature.eps48 k r) →
        ((2 * r + k + 1 : ℕ) : ℝ) * (pOf (Formalism.MainNotions.CayleySignature.eps48 k r) : ℝ) * (qOf (Formalism.MainNotions.CayleySignature.eps48 k r) : ℝ) + 1 < h ∧
        8 * Real.sqrt (2 * (S7.q0 (Formalism.MainNotions.CayleySignature.eps48 k r) : ℝ)) *
            (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) +
              2 * ((2 * r + k + 1 : ℕ) : ℝ) * S7.q0 (Formalism.MainNotions.CayleySignature.eps48 k r)) < h) := by
  obtain ⟨t, -, ht1, -, ht⟩ := hgap
  have ht1' : 2 * r + k + 1 + 5 ≤ t := ht1
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 * r + k + 1 + (2 * r + 2) * t := ⟨_, rfl⟩
  have hb : ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * (M : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j := by
    rw [hM]; exact ht
  have hMpos : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have htpos : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  refine ⟨2 * (M : ℝ) ^ 3 + (t : ℝ) + 3, ?_, ?_⟩
  · exact gapAtLeast_of_increments k r v b _ (by positivity) hlam.1 hb
  · intro _
    have hq : qOf (eps48 k r) ≤ r + 1 := q_le_of_cayley_signature k r
    have hpn : pOf (eps48 k r) ≤ 2 * r + k + 1 := by
      unfold pOf; exact (Finset.card_filter_le _ _).trans (by simp)
    have hqn : qOf (eps48 k r) ≤ 2 * r + k + 1 := by
      unfold qOf; exact (Finset.card_filter_le _ _).trans (by simp)
    have hq0 : S7.q0 (eps48 k r) ≤ r + 1 := (min_le_right _ _).trans hq
    have hnM : 2 * r + k + 1 ≤ M := by rw [hM]; omega
    have hnat1 : (2 * r + k + 1) * pOf (eps48 k r) * qOf (eps48 k r) ≤ M ^ 3 := by
      calc _ ≤ M * M * M := Nat.mul_le_mul (Nat.mul_le_mul hnM (hpn.trans hnM)) (hqn.trans hnM)
        _ = M ^ 3 := by ring
    have hnat2 := cubic_bound_of_gap_nat (2 * r + k + 1) r t M hM ht1'
    have c1 : ((2 * r + k + 1 : ℕ) : ℝ) * (pOf (eps48 k r) : ℝ) * (qOf (eps48 k r) : ℝ) ≤ (M : ℝ) ^ 3 := by
      exact_mod_cast hnat1
    have c2 : (96 : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) ^ 3 := by
      exact_mod_cast hnat2
    have hM3 : (0 : ℝ) ≤ (M : ℝ) ^ 3 := by positivity
    refine ⟨by linarith, ?_⟩
    refine (weighted_gap_threshold_le _ _ _ (by positivity) ?_ ?_ ?_).trans_lt (by linarith)
    · exact_mod_cast hq0
    · exact_mod_cast (show 1 ≤ r + 1 by omega)
    · exact_mod_cast (show r + 1 ≤ 2 * r + k + 1 by omega)


end ReciprocityTheory.ChartRestriction.DS
