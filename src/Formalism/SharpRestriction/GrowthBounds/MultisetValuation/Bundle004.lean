module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

variable {p n' k1 t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ} {lam0 : Fin n' → Fin (k1 + 1) → ℤ}
  {w : ℕ → Fin n' → ℤ}

theorem w_one_le (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') :
    ∀ j, 1 ≤ j → j ≤ m → w 1 s ≤ w j s := by
  intro j hj hm
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj0 | hj'
    · subst hj0
      exact le_rfl
    · exact (ih hj' (by omega)).trans (h.w_mono s j hj' (by omega))

theorem lamI_ge_last (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ k1 + 1) :
    lam0 s (Fin.last k1) ≤ lamI lam0 s i := by
  unfold lamI
  rw [dite_eq_left ⟨h1, h2⟩]
  exact h.dom s (Fin.le_last _)

theorem lamI_add_w_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (i j : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ k1 + 1) (hj : 1 ≤ j) (hm : j ≤ m) : 0 ≤ lamI lam0 s i + w j s := by
  have h3 := lamI_ge_last h s i h1 h2
  have h4 := w_one_le h s j hj hm
  have h5 := (h.w_low s).2
  linarith

theorem al_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') : 0 ≤ al TT lam0 s := by
  have hk : 2 ≤ k1 + 1 := by have := h.two_r; have := h.r_pos; omega
  unfold al
  split_ifs
  · unfold lamI
    rw [dite_eq_left (show 1 ≤ 1 ∧ 1 ≤ k1 + 1 by omega), dite_eq_left (show 1 ≤ 2 ∧ 2 ≤ k1 + 1 by omega)]
    exact sub_nonneg.mpr (h.dom s (Fin.mk_le_mk.mpr (by omega)))
  · exact le_rfl

theorem cap_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    0 ≤ cap t TT lam0 w j s := by
  have hk : 2 ≤ k1 + 1 := by have := h.two_r; have := h.r_pos; omega
  unfold cap nu
  split_ifs <;> first
    | omega
    | exact lamI_add_w_nonneg h s _ j (by omega) (by omega) hj hm

theorem gam_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) : 0 ≤ gam p := by
  unfold gam
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five_le
  apply div_nonneg
  · positivity
  · nlinarith

theorem Pr_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    0 ≤ Pr t r lam0 w j := by
  unfold Pr
  have hk := h.two_r
  have hr := h.r_pos
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro s _
    have hcard : (Icc (k1 + 2 - r) (k1 + 1)).card = r := by
      rw [Nat.card_Icc]
      omega
    have key : ∀ a ∈ Icc (k1 + 2 - r) (k1 + 1), (0 : ℝ) ≤ (w j s : ℝ) + (lamI lam0 s a : ℝ) := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have h0 := lamI_add_w_nonneg h s a j (by omega) ha.2 hj hm
      have h0' : (0 : ℤ) ≤ w j s + lamI lam0 s a := by linarith
      exact_mod_cast h0'
    have hsum := Finset.sum_nonneg key
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at hsum
    linarith
  · positivity

theorem gA_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) :
    -de p t TT lam0 w j ≤ gA p t TT lam0 w j := by
  unfold gA
  have key : ∀ X Y : ℝ, 0 ≤ X → -Y ≤ X - Y := fun X Y hX => by linarith
  apply key
  apply Finset.sum_nonneg
  intro s _
  apply tsum_nonneg
  intro e
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

theorem gB_le (h : Std p n' k1 t m c r TT a b lam0 w) (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    gB p t TT lam0 w j ≤ gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) - de p t TT lam0 w j := by
  unfold gB
  have key : ∀ A X Y : ℝ, 0 ≤ X → A - X - Y ≤ A - Y := fun A X Y hX => by linarith
  apply key
  apply Finset.sum_nonneg
  intro s _
  apply tsum_nonneg
  intro e
  apply le_min
  · apply div_nonneg
    · exact_mod_cast al_nonneg h s
    · positivity
  · exact_mod_cast cap_nonneg h _ j hj hm

theorem relative_presentation_of_d7 (D : Formalism.BasicNotions.D7) : RelativePresentationLiterature D := by
  intro p n' k1 t m c r TT a b lam0 w h
  unfold Sv
  have hA : 0 ≤ gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) :=
    mul_nonneg (gam_nonneg h) (Finset.sum_nonneg fun s _ => by exact_mod_cast al_nonneg h s)
  calc ∑ j ∈ Icc 1 m, max (gB p t TT lam0 w j - Pr t r lam0 w j - gA p t TT lam0 w j) 0
      ≤ ∑ j ∈ Icc 1 m, gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Icc] at hj
        have e1 := gB_le h j hj.1 hj.2
        have e2 := Pr_nonneg h j hj.1 hj.2
        have e3 := gA_ge p t TT lam0 w j
        exact max_le (by linarith) hA
    _ = (m : ℝ) * gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset

theorem nc_lgp_le (p : ℕ) (hp : 2 ≤ p) (x : ℤ) (A : ℝ) (c : ℕ) (_hA : 1 ≤ A) (hx : (x : ℝ) ≤ A ^ c)
    (hl : 1 ≤ Real.logb p A) : (lgp p x : ℝ) ≤ (c + 1) * Real.logb p A := by
  unfold lgp
  split_ifs with h
  · push_cast
    have : 0 ≤ Real.logb p A := by linarith
    nlinarith
  · push_cast
    have hx0 : 0 < x := by omega
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
    have h1 : (Nat.log p x.toNat : ℝ) ≤ Real.logb p (x.toNat : ℝ) := Real.natLog_le_logb _ _
    have h2 : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
      have : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx0.le
      exact_mod_cast this
    rw [h2] at h1
    have h3 : Real.logb p (x : ℝ) ≤ Real.logb p (A ^ c) :=
      Real.logb_le_logb_of_le hp1 (by exact_mod_cast hx0) hx
    rw [Real.logb_pow] at h3
    nlinarith

variable {n' k1 : ℕ}

theorem nc_de_le (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (A : ℝ) (NM : ℝ) (hA : 1 ≤ A) (hl : 1 ≤ Real.logb p A) (hN1 : (NN k1 t j : ℝ) ≤ NM)
    (hN0 : (NN k1 t (j - 1) : ℝ) ≤ NM) (hal : ∀ s, (al TT lam0 s : ℝ) ≤ A ^ 2)
    (hls : ∀ s, (lsz t TT lam0 w j s : ℝ) ≤ A ^ 4) :
    de p t TT lam0 w j ≤ 8 * (n' : ℝ) * NM ^ 2 * Real.logb p A + 9 * (TT.card : ℝ) * Real.logb p A ^ 2 := by
  unfold de
  set ℓ := Real.logb p A with hℓ
  have hN1' : (1 : ℝ) ≤ NN k1 t j := by unfold NN; push_cast; nlinarith
  have hNM : 1 ≤ NM := le_trans hN1' hN1
  have hN0' : (0 : ℝ) ≤ NN k1 t (j - 1) := by positivity
  have hα : ∀ s, (lgp p (al TT lam0 s) : ℝ) ≤ 3 * ℓ := fun s => by
    have := nc_lgp_le p hp _ A 2 hA (hal s) hl; push_cast at this; linarith
  have hlz : ∀ s, (lgp p (lsz t TT lam0 w j s) : ℝ) ≤ 5 * ℓ := fun s => by
    have := nc_lgp_le p hp _ A 4 hA (hls s) hl; push_cast at this; linarith
  have hα0 : ∀ s, (0 : ℝ) ≤ lgp p (al TT lam0 s) := fun s => by positivity
  have hlz0 : ∀ s, (0 : ℝ) ≤ lgp p (lsz t TT lam0 w j s) := fun s => by positivity
  have h1 : ∑ s : Fin n', ((NN k1 t j : ℝ) * lgp p (al TT lam0 s) +
      (NN k1 t (j - 1) : ℝ) * (NN k1 t j : ℝ) * lgp p (lsz t TT lam0 w j s)) ≤
      ∑ _s : Fin n', (8 * NM ^ 2 * ℓ) := by
    apply Finset.sum_le_sum
    intro s _
    have e1 : (NN k1 t j : ℝ) * lgp p (al TT lam0 s) ≤ NM * (3 * ℓ) :=
      mul_le_mul hN1 (hα s) (hα0 s) (by linarith)
    have e2 : (NN k1 t (j - 1) : ℝ) * (NN k1 t j : ℝ) * lgp p (lsz t TT lam0 w j s) ≤ NM * NM * (5 * ℓ) :=
      mul_le_mul (mul_le_mul hN0 hN1 (by positivity) (by linarith)) (hlz s) (hlz0 s) (by nlinarith)
    have e3 : NM * (3 * ℓ) ≤ NM * NM * (3 * ℓ) := by
      have : 0 ≤ NM * (3 * ℓ) := by positivity
      nlinarith
    nlinarith
  have h2 : ∑ s ∈ TT, ((lgp p (al TT lam0 s) : ℝ)) ^ 2 ≤ ∑ _s ∈ TT, (9 * ℓ ^ 2) := by
    apply Finset.sum_le_sum
    intro s _
    have := hα s
    have := hα0 s
    nlinarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  nlinarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset

theorem nc_geom (p : ℕ) (hp : 2 ≤ p) :
    HasSum (fun e : ℕ => (((p : ℝ)) ^ (2 * e + 1))⁻¹) (Formalism.MainNotions.FormalGroupSystem.gam p) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hq : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hr : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have h0 : 0 ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
  have := (hasSum_geometric_of_lt_one h0 hr).mul_left ((p : ℝ)⁻¹)
  have e1 : (fun e : ℕ => ((p : ℝ) ^ (2 * e + 1))⁻¹) = fun i : ℕ => (p : ℝ)⁻¹ * ((p : ℝ) ^ 2)⁻¹ ^ i := by
    funext e
    rw [pow_succ, pow_mul, mul_inv, inv_pow]
    ring
  have e2 : Formalism.MainNotions.FormalGroupSystem.gam p = (p : ℝ)⁻¹ * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
    rw [Formalism.MainNotions.FormalGroupSystem.gam]
    first
      | (field_simp; ring)
      | field_simp
  rw [e1, e2]
  exact this

theorem nc_geomc (p : ℕ) (hp : 2 ≤ p) (c : ℝ) :
    HasSum (fun e : ℕ => c / ((p : ℝ)) ^ (2 * e + 1)) (c * Formalism.MainNotions.FormalGroupSystem.gam p) := by
  have := (nc_geom p hp).mul_left c
  simpa [div_eq_mul_inv] using this

theorem nc_abs_min_le (a b : ℝ) (hb : 0 ≤ b) : |min a b| ≤ |a| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, abs_of_nonneg hb, abs_of_nonneg (hb.trans h)]
    exact h

theorem nc_summable_min (p : ℕ) (hp : 2 ≤ p) (y : ℝ) (z : ℕ → ℝ) (hz : ∀ e, 0 ≤ z e) :
    Summable fun e : ℕ => min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e) := by
  have hg : Summable (fun e : ℕ => |y| / ((p : ℝ)) ^ (2 * e + 1)) := (nc_geomc p hp |y|).summable
  have hb : ∀ e : ℕ, ‖min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e)‖ ≤ |y| / ((p : ℝ)) ^ (2 * e + 1) := by
    intro e
    have hq : (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
      positivity
    rw [Real.norm_eq_abs]
    calc |min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e)| ≤ |y / ((p : ℝ)) ^ (2 * e + 1)| := nc_abs_min_le _ _ (hz e)
      _ = |y| / ((p : ℝ)) ^ (2 * e + 1) := by rw [abs_div, abs_of_pos hq]
  first
    | exact Summable.of_norm_bounded hg hb
    | exact Summable.of_norm_bounded _ hg hb

theorem nc_min (p : ℕ) (hp : 2 ≤ p) (y yu : ℝ) (z zu : ℕ → ℝ) (hy : y ≤ yu) (hz : ∀ e, zu e ≤ z e)
    (hz0 : ∀ e, 0 ≤ zu e) :
    Formalism.MainNotions.FormalGroupSystem.gam p * y - ∑' e : ℕ, min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e) ≤
      Formalism.MainNotions.FormalGroupSystem.gam p * yu - ∑' e : ℕ, min (yu / ((p : ℝ)) ^ (2 * e + 1)) (zu e) := by
  have hs1 := nc_geomc p hp y
  have hs2 := nc_geomc p hp yu
  have m1 := nc_summable_min p hp y z (fun e => (hz0 e).trans (hz e))
  have m2 := nc_summable_min p hp yu zu hz0
  rw [mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p) y, mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p) yu, ← hs1.tsum_eq, ← hs2.tsum_eq]
  rw [← hs1.summable.tsum_sub m1, ← hs2.summable.tsum_sub m2]
  refine (hs1.summable.sub m1).tsum_le_tsum (fun e => ?_) (hs2.summable.sub m2)
  have hq : (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    positivity
  have ha : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy hq.le
  have hze := hz e
  simp only [Pi.sub_apply, min_def]
  split_ifs <;> linarith

theorem nc_pos (p : ℕ) (hp : 2 ≤ p) (y yu : ℝ) (z zu : ℕ → ℝ) (ex exu : ℕ → Prop) [DecidablePred ex]
    [DecidablePred exu] (hy : y ≤ yu) (hyu : 0 ≤ yu) (hz : ∀ e, zu e ≤ z e) (hz0 : ∀ e, 0 ≤ zu e)
    (hex : ∀ e, exu e → ex e) :
    ∑' e : ℕ, (if ex e then 0 else max 0 (y / ((p : ℝ)) ^ (2 * e + 1) - z e)) ≤
      ∑' e : ℕ, (if exu e then 0 else max (yu / ((p : ℝ)) ^ (2 * e + 1) - zu e) 0) := by
  have hq : ∀ e : ℕ, (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
    intro e
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    positivity
  have hS := (nc_geomc p hp yu).summable
  have hR : Summable (fun e : ℕ => if exu e then 0 else max (yu / ((p : ℝ)) ^ (2 * e + 1) - zu e) 0) := by
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hS
    · split_ifs
      · exact le_rfl
      · exact le_max_right _ _
    · have h1 : 0 ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_nonneg hyu (hq e).le
      have h2 := hz0 e
      split_ifs
      · exact h1
      · exact max_le (by linarith) h1
  have hLs : Summable (fun e : ℕ => if ex e then 0 else max 0 (y / ((p : ℝ)) ^ (2 * e + 1) - z e)) := by
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hS
    · split_ifs
      · exact le_rfl
      · exact le_max_left _ _
    · have h1 : 0 ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_nonneg hyu (hq e).le
      have h3 : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy (hq e).le
      have h2 := hz0 e
      have h4 := hz e
      split_ifs
      · exact h1
      · exact max_le h1 (by linarith)
  refine hLs.tsum_le_tsum (fun e => ?_) hR
  have h3 : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy (hq e).le
  have h4 := hz e
  by_cases he : ex e
  · rw [if_pos he]
    split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  · have heu : ¬ exu e := fun h => he (hex e h)
    rw [if_neg he, if_neg heu]
    exact max_le (le_max_right _ _) (le_trans (by linarith) (le_max_left _ _))

variable {n' k1 : ℕ}

theorem nc_gB_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (ya zc : Fin n' → ℝ) (dlv : ℝ) (h1 : ∀ s ∈ TT, ya s ≤ al TT lam0 s)
    (h2 : ∀ s, (cap t TT lam0 w j s : ℝ) ≤ zc s) (h3 : ∀ s, 0 ≤ cap t TT lam0 w j s)
    (hd : de p t TT lam0 w j ≤ dlv) :
    Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ TT, ya s -
              ∑ s ∈ TT.filter IsOddPos, ∑' e : ℕ,
                min (ya s / ((p : ℝ)) ^ (2 * e + 1)) (zc (Formalism.MainNotions.G.posAdd s (2 * e + 1))) - dlv ≤
      gB p t TT lam0 w j := by
  unfold gB
  have hg0 : 0 ≤ Formalism.MainNotions.FormalGroupSystem.gam p := (nc_geom p hp).nonneg fun e => by positivity
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not TT IsOddPos,
    ← Finset.sum_filter_add_sum_filter_not TT IsOddPos (fun s => Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ))]
  have hA : ∑ s ∈ TT.filter IsOddPos, (Formalism.MainNotions.FormalGroupSystem.gam p * ya s - ∑' e : ℕ,
        min (ya s / ((p : ℝ)) ^ (2 * e + 1)) (zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) ≤
      ∑ s ∈ TT.filter IsOddPos, (Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ) - ∑' e : ℕ,
        min ((al TT lam0 s : ℝ) / ((p : ℝ)) ^ (2 * e + 1)) (cap t TT lam0 w j (Formalism.MainNotions.G.posAdd s (2 * e + 1)) : ℝ)) := by
    apply Finset.sum_le_sum
    intro s hs
    exact nc_min p hp _ _ _ _ (h1 s (Finset.mem_filter.1 hs).1) (fun e => h2 _) (fun e => by exact_mod_cast h3 _)
  have hB : ∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), Formalism.MainNotions.FormalGroupSystem.gam p * ya s ≤
      ∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ) := by
    apply Finset.sum_le_sum
    intro s hs
    exact mul_le_mul_of_nonneg_left (h1 s (Finset.mem_filter.1 hs).1) hg0
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hA
  linarith

theorem nc_gA_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (ya zc : Fin n' → ℝ) (dlv : ℝ) (ex : Fin n' → ℕ → Prop) [∀ s, DecidablePred (ex s)]
    (h1 : ∀ s ∈ TT, ya s ≤ al TT lam0 s) (h0 : ∀ s, 0 ≤ al TT lam0 s)
    (h2 : ∀ s, (cap t TT lam0 w j s : ℝ) ≤ zc s) (h3 : ∀ s, 0 ≤ cap t TT lam0 w j s)
    (hex : ∀ s ∈ TT, ∀ e, 2 * e + 1 ∈ dSet TT s → ex s e)
    (hd : de p t TT lam0 w j ≤ dlv) :
    ∑ s ∈ TT, ∑' e : ℕ, (if ex s e then 0 else
        max 0 (ya s / ((p : ℝ)) ^ (2 * e + 1) - zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) - dlv ≤
      gA p t TT lam0 w j := by
  unfold gA
  have hA : ∑ s ∈ TT, ∑' e : ℕ, (if ex s e then 0 else
        max 0 (ya s / ((p : ℝ)) ^ (2 * e + 1) - zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) ≤
      ∑ s ∈ TT, ∑' e : ℕ, (if 2 * e + 1 ∈ dSet TT s then 0 else
        max ((al TT lam0 s : ℝ) / (p : ℝ) ^ (2 * e + 1) -
          (cap t TT lam0 w j (Formalism.MainNotions.G.posAdd s (2 * e + 1)) : ℝ)) 0) := by
    apply Finset.sum_le_sum
    intro s hs
    exact nc_pos p hp _ _ _ _ (ex s) (fun e => 2 * e + 1 ∈ dSet TT s) (h1 s hs) (by exact_mod_cast h0 s)
      (fun e => h2 _) (fun e => by exact_mod_cast h3 _) (hex s hs)
  linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem ea_applyD_map {σ τ K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ K) :
    applyD P (MvPowerSeries.map φ f) = MvPolynomial.map φ (applyD P f) := by
  unfold applyD

  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have e : φ.comp (Int.castRingHom K) = Int.castRingHom K' := RingHom.ext_int _ _
  have e2 : φ (∏ x ∈ n.support, ((n x).factorial : K)) = ∏ x ∈ n.support, ((n x).factorial : K') := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun x _ => map_natCast φ _
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map φ), MvPolynomial.map_C,
    MvPolynomial.map_map, e, MvPowerSeries.coeff_map, map_mul φ, e2]

def ea_InClassA (X : Sys p) {K' : Type} [Field K'] (R' : Subring K') (j : ℕ) (h F : MvPowerSeries (X.ZA j) K') : Prop :=
  ∃ g : ℕ → MvPowerSeries (X.ZA j) K', (∀ i, IntR R' (g i)) ∧ ∀ α : X.ZA j →₀ ℕ,
    MvPowerSeries.coeff α F = ∑ i ∈ range (α.degree + 1),
      (((p : K') ^ i)⁻¹ * MvPowerSeries.coeff α (h ^ i * g i))

def ea_RestSU (X : Sys p) (Y : Pend X) : Prop :=
  DworkLemma p → BeProp p Y.be → ∀ (v : X.Pl) (j : ℕ) (U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc),
    IntR Y.Oc (inParamK p Y.Kc U) →
    ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra Y.Kc K'] [IsScalarTower (K0 p) Y.Kc K'] (R' : Subring K')
      (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ Y.Oc, algebraMap Y.Kc K' x ∈ R') →
      ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ R') ∧
        ea_InClassA X R' j (X.hhA K' j v u) (atPi vp (MvPowerSeries.map (algebraMap Y.Kc K')
          (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U))))

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Local

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem lambda_index_one (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) : lamI (G.P.lam0 v) s 1 = G.P.lam0 v s ⟨0, by omega⟩ := by
  unfold lamI; rw [dite_eq_left ⟨le_rfl, by omega⟩]

theorem lambda_index_two (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) : lamI (G.P.lam0 v) s 2 = G.P.lam0 v s ⟨1, by omega⟩ := by
  unfold lamI; rw [dite_eq_left ⟨by omega, by omega⟩]

theorem nc_w_ge (s : Fin (G.P.n' v)) (j : ℕ) (hj : 1 ≤ j) : Fl.w v 1 s ≤ Fl.w v j s := by
  induction j, hj using Nat.le_induction with
  | base => exact le_rfl
  | succ l hl ih => exact le_trans ih (Fl.w_mono v s l hl)

end Local

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
