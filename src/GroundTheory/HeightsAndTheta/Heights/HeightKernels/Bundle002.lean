module

public import GroundTheory.HeightsAndTheta.Heights.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Finset

namespace KAlt

def frobDelta {r : ℕ} (la : Fin r → ℕ) : ℚ :=
  ∏ a : Fin r, ∏ b : Fin r,
    if a < b then ((la a + (r - 1 - a) : ℕ) : ℚ) - ((la b + (r - 1 - b) : ℕ) : ℚ) else 1

theorem frobDim_eq {r : ℕ} (la : Fin r → ℕ) :
    frobDim la = ((∑ a, la a).factorial : ℚ) * frobDelta la /
      ∏ a : Fin r, ((la a + (r - 1 - a)).factorial : ℚ) := rfl

theorem frobDelta_add_const {r : ℕ} (s : ℕ) (ν : Fin r → ℕ) :
    frobDelta (fun a => s + ν a) = frobDelta ν := by
  unfold frobDelta
  refine prod_congr rfl fun a _ => prod_congr rfl fun b _ => ?_
  split_ifs
  · push_cast; ring
  · rfl

theorem prod_sub_eq_prod_factorial : ∀ r : ℕ,
    (∏ a : Fin r, ∏ b : Fin r, if a < b then ((b : ℕ) : ℚ) - ((a : ℕ) : ℚ) else 1) =
      ∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ) := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    have h0 : (∏ b : Fin (r + 1), if (0 : Fin (r + 1)) < b
        then (((b : ℕ) : ℚ) - (((0 : Fin (r + 1)) : ℕ) : ℚ)) else 1) = (r.factorial : ℚ) := by
      rw [Fin.prod_univ_succ]
      simp only [lt_self_iff_false, ite_false, Fin.succ_pos, ite_true, one_mul, Fin.val_succ,
        Fin.val_zero, Nat.cast_zero, sub_zero]
      push_cast
      rw [Fin.prod_univ_eq_prod_range (fun i => ((i : ℚ) + 1)) r]
      exact_mod_cast Finset.prod_range_add_one_eq_factorial r
    have hs : ∀ a : Fin r, (∏ b : Fin (r + 1), if a.succ < b
        then (((b : ℕ) : ℚ) - ((a.succ : ℕ) : ℚ)) else 1) =
        ∏ b : Fin r, if a < b then (((b : ℕ) : ℚ) - ((a : ℕ) : ℚ)) else 1 := by
      intro a
      rw [Fin.prod_univ_succ]
      simp only [Fin.not_lt_zero, ite_false, one_mul, Fin.succ_lt_succ_iff, Fin.val_succ]
      refine prod_congr rfl fun b _ => ?_
      split_ifs
      · push_cast; ring
      · rfl
    have hshift (a : Fin r) : r + 1 - 1 - (a.succ : ℕ) = r - 1 - (a : ℕ) := by
      simp only [Fin.val_succ]
      omega
    conv_lhs => rw [Fin.prod_univ_succ]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [h0, hs, ih, hshift]
    simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel]

theorem frobDelta_const {r : ℕ} (s : ℕ) :
    frobDelta (fun _ : Fin r => s) = ∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ) := by
  rw [← prod_sub_eq_prod_factorial r]
  unfold frobDelta
  refine prod_congr rfl fun a _ => prod_congr rfl fun b _ => ?_
  split_ifs with h
  · have ha := a.isLt
    have hb := b.isLt
    have hab : (a : ℕ) < b := h
    have : ((s + (r - 1 - (a : ℕ)) : ℕ) : ℚ) + ((a : ℕ) : ℚ) =
        ((s + (r - 1 - (b : ℕ)) : ℕ) : ℚ) + ((b : ℕ) : ℚ) := by
      exact_mod_cast (show s + (r - 1 - (a : ℕ)) + a = s + (r - 1 - (b : ℕ)) + b by omega)
    linarith
  · rfl

theorem frobDelta_nonneg {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) : 0 ≤ frobDelta ν := by
  unfold frobDelta
  refine prod_nonneg fun a _ => prod_nonneg fun b _ => ?_
  split_ifs with h
  · have h1 : ν b ≤ ν a := hν h.le
    have hab : (a : ℕ) < b := h
    have hb := b.isLt
    have h2 : ν b + (r - 1 - (b : ℕ)) ≤ ν a + (r - 1 - (a : ℕ)) := by omega
    rw [sub_nonneg]
    exact_mod_cast h2
  · exact zero_le_one

theorem factorial_mul_le (s c d : ℕ) :
    (s + c).factorial * (c + d).factorial ≤ (s + c + d).factorial * c.factorial := by
  induction d with
  | zero => simp [mul_comm]
  | succ d ih =>
    rw [show c + (d + 1) = (c + d) + 1 by ring, Nat.factorial_succ,
      show s + c + (d + 1) = (s + c + d) + 1 by ring, Nat.factorial_succ]
    calc (s + c).factorial * ((c + d + 1) * (c + d).factorial)
        = (c + d + 1) * ((s + c).factorial * (c + d).factorial) := by ring
      _ ≤ (s + c + d + 1) * ((s + c + d).factorial * c.factorial) :=
          Nat.mul_le_mul (by omega) ih
      _ = ((s + c + d + 1) * (s + c + d).factorial) * c.factorial := by ring

theorem prod_factorial_le {r : ℕ} (s : ℕ) (ν : Fin r → ℕ) :
    (∏ a : Fin r, ((s + (r - 1 - (a : ℕ))).factorial : ℚ)) *
        ∏ a : Fin r, ((ν a + (r - 1 - (a : ℕ))).factorial : ℚ) ≤
      (∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ)) *
        ∏ a : Fin r, ((s + ν a + (r - 1 - (a : ℕ))).factorial : ℚ) := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_le_prod₀
  · intro a _; positivity
  · intro a _
    have := factorial_mul_le s (r - 1 - (a : ℕ)) (ν a)
    rw [show s + ν a + (r - 1 - (a : ℕ)) = s + (r - 1 - (a : ℕ)) + ν a by ring,
      show ν a + (r - 1 - (a : ℕ)) = (r - 1 - (a : ℕ)) + ν a by ring,
      mul_comm (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ)]
    exact_mod_cast this

end KAlt

theorem FrobeniusRectangleBound.intersectionNumber_baseChange : FrobeniusRectangleBound.Statement := by
  intro r s ν hν
  simp only [KAlt.frobDim_eq, KAlt.frobDelta_add_const, KAlt.frobDelta_const]
  have hsum : (∑ a : Fin r, (s + ν a)) = r * s + ∑ a, ν a := by
    rw [Finset.sum_add_distrib]; simp
  have hsum' : (∑ _a : Fin r, s) = r * s := by simp
  rw [hsum, hsum']
  set k := ∑ a, ν a with hk
  set A := ∏ a : Fin r, ((s + ν a + (r - 1 - (a : ℕ))).factorial : ℚ) with hA
  set B := ∏ a : Fin r, ((s + (r - 1 - (a : ℕ))).factorial : ℚ) with hB
  set E := ∏ a : Fin r, ((ν a + (r - 1 - (a : ℕ))).factorial : ℚ) with hE
  set F := ∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ) with hF
  set D := KAlt.frobDelta ν with hD
  have hA0 : 0 < A := prod_pos fun a _ => by positivity
  have hB0 : 0 < B := prod_pos fun a _ => by positivity
  have hE0 : 0 < E := prod_pos fun a _ => by positivity
  have hD0 : 0 ≤ D := KAlt.frobDelta_nonneg ν hν
  have key : B * E ≤ F * A := KAlt.prod_factorial_le s ν
  have hch : ((r * s + k).choose k : ℚ) * ((r * s).factorial : ℚ) * (k.factorial : ℚ) =
      ((r * s + k).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ r * s + k by omega)
    rw [show r * s + k - k = r * s by omega] at h
    rw [← h]; push_cast; ring
  have hrhs : ((r * s + k).choose k : ℚ) * ((r * s).factorial * F / B) * (k.factorial * D / E) =
      ((r * s + k).factorial : ℚ) * D * F / (B * E) := by
    rw [← hch]; field_simp
  rw [hrhs, div_le_div_iff₀ hA0 (mul_pos hB0 hE0)]
  calc ((r * s + k).factorial : ℚ) * D * (B * E) ≤ ((r * s + k).factorial : ℚ) * D * (F * A) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = ((r * s + k).factorial : ℚ) * D * F * A := by ring

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

namespace KCoord

section Mean

variable {S : Type*} [Fintype S]

theorem card_pos_real [Nonempty S] : (0 : ℝ) < Fintype.card S := by
  exact_mod_cast Fintype.card_pos

theorem finMean_mono [Nonempty S] {f h : S → ℝ} (hfh : ∀ s, f s ≤ h s) : finMean f ≤ finMean h :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => hfh s) card_pos_real.le

theorem finMean_add (f h : S → ℝ) : finMean (fun s => f s + h s) = finMean f + finMean h := by
  simp [finMean, Finset.sum_add_distrib, add_div]

theorem finMean_sub (f h : S → ℝ) : finMean (fun s => f s - h s) = finMean f - finMean h := by
  simp [finMean, Finset.sum_sub_distrib, sub_div]

theorem finMean_const_mul (c : ℝ) (f : S → ℝ) : finMean (fun s => c * f s) = c * finMean f := by
  simp [finMean, ← Finset.mul_sum, mul_div_assoc]

theorem finMean_const [Nonempty S] (c : ℝ) : finMean (fun _ : S => c) = c := by
  have h := (card_pos_real (S := S)).ne'
  simp only [finMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Mean

theorem mul_log_le (G a : ℝ) (hG : 0 ≤ G) (ha : 0 < a) :
    G * log (1 + a) ≤ π / 192 * a ^ 2 + 48 / π * G ^ 2 := by
  have h1 : log (1 + a) ≤ a := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + a by linarith)
    linarith
  have h2 : G * log (1 + a) ≤ G * a := mul_le_mul_of_nonneg_left h1 hG
  have hpi : 0 < π := Real.pi_pos
  have h3 : π / 192 * a ^ 2 + 48 / π * G ^ 2 - G * a = (π * a - 96 * G) ^ 2 / (192 * π) := by
    field_simp
    ring
  have h4 : 0 ≤ (π * a - 96 * G) ^ 2 / (192 * π) := by positivity
  linarith

theorem posLog_le_half_log (ρ : ℝ) (hρ : 0 < ρ) :
    posLog (1 / ρ) ≤ 1 / 2 * log (1 + (ρ ^ 2)⁻¹) := by
  have hx : 0 < 1 + (ρ ^ 2)⁻¹ := by positivity
  have h0 : 0 ≤ 1 / 2 * log (1 + (ρ ^ 2)⁻¹) := by
    have : 0 ≤ log (1 + (ρ ^ 2)⁻¹) := Real.log_nonneg (by
      have : 0 ≤ (ρ ^ 2)⁻¹ := by positivity
      linarith)
    linarith
  have h1 : log (1 / ρ) ≤ 1 / 2 * log (1 + (ρ ^ 2)⁻¹) := by
    have e : log (1 / ρ) = 1 / 2 * log ((ρ ^ 2)⁻¹) := by
      rw [one_div, Real.log_inv, Real.log_inv, Real.log_pow]
      push_cast
      ring
    rw [e]
    have : log ((ρ ^ 2)⁻¹) ≤ log (1 + (ρ ^ 2)⁻¹) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  simp only [Real.posLog]
  exact max_le h0 h1

end KCoord

theorem WeakMatrixArithmetic.intersectionNumber_baseChange : WeakMatrixArithmetic.Statement := by
  intro C₀ hC₀
  refine ⟨64 * (33 + C₀), by positivity, ?_⟩
  intro g _ S _ _ ρ Φ hρ hΦ hmean
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hG : (0 : ℝ) ≤ g := by linarith
  set L := log (2 * (g : ℝ)) with hL
  have hLge : log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : (1 / 2 : ℝ) < log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hLpos : 1 / 2 < L := by linarith
  have hpi3 : 3 < π := Real.pi_gt_three
  have hpi : 0 < π := Real.pi_pos
  set x : S → ℝ := fun s => (ρ s ^ 2)⁻¹ with hx
  set E : S → ℝ := fun s => g * log (1 + 1 / ρ s) + C₀ * g * L with hE
  set K : ℝ := 48 / π * (g : ℝ) ^ 2 + C₀ * g * L with hK

  have hEx : ∀ s, E s ≤ π / 192 * x s + K := by
    intro s
    have h := KCoord.mul_log_le (g : ℝ) (1 / ρ s) hG (by have := (hρ s).1; positivity)
    have e : (1 / ρ s) ^ 2 = x s := by simp [hx, one_div, inv_pow]
    rw [e] at h
    simp only [hE, hK]
    linarith

  have hK' : K ≤ (32 + C₀) * ((g : ℝ) ^ 2 * L) := by
    have h1 : 48 / π * (g : ℝ) ^ 2 ≤ 32 * ((g : ℝ) ^ 2 * L) := by
      have hg2 : 0 ≤ (g : ℝ) ^ 2 := by positivity
      have : 48 / π ≤ 16 := by
        rw [div_le_iff₀ hpi]; linarith
      have h16 : 16 * (g : ℝ) ^ 2 ≤ 32 * ((g : ℝ) ^ 2 * L) := by nlinarith
      nlinarith
    have h2 : C₀ * g * L ≤ C₀ * ((g : ℝ) ^ 2 * L) := by
      have : (g : ℝ) * L ≤ (g : ℝ) ^ 2 * L := by
        have : (g : ℝ) ≤ (g : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this (by linarith)
      have := mul_le_mul_of_nonneg_left this hC₀
      linarith [mul_assoc C₀ (g : ℝ) L]
    simp only [hK]
    linarith
  have hgL : 0 ≤ (g : ℝ) ^ 2 * L := by have := sq_nonneg (g : ℝ); nlinarith

  have hmx : π / 192 * finMean x ≤ Φ + K := by
    have h1 : finMean (fun s => π / 96 * x s - E s) ≥ finMean (fun s => π / 192 * x s - K) :=
      KCoord.finMean_mono fun s => by have := hEx s; linarith
    have h2 : finMean (fun s => π / 192 * x s - K) = π / 192 * finMean x - K := by
      rw [KCoord.finMean_sub, KCoord.finMean_const_mul, KCoord.finMean_const]
    have h3 : finMean (fun s => π / 96 * x s - E s) ≤ Φ := hmean
    linarith
  have hmx' : finMean x ≤ 64 * (Φ + K) := by
    have : finMean x ≤ 192 / π * (Φ + K) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
      linarith
    have hΦK : 0 ≤ Φ + K := by
      have : 0 ≤ K := by simp only [hK]; positivity
      linarith
    have : 192 / π ≤ 64 := by rw [div_le_iff₀ hpi]; linarith
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  ·
    show finMean x ≤ _
    nlinarith
  ·
    show finMean E ≤ _
    have h0 : finMean E ≤ finMean (fun s => π / 192 * x s + K) := KCoord.finMean_mono hEx
    have h0' : finMean (fun s => π / 192 * x s + K) = π / 192 * finMean x + K := by
      rw [KCoord.finMean_add, KCoord.finMean_const_mul, KCoord.finMean_const]
    have h1 : finMean E ≤ π / 192 * finMean x + K := h0.trans h0'.le
    nlinarith
  ·
    have hpt : ∀ s, posLog (1 / ρ s) ≤ 1 / 2 * log (1 + x s) := fun s =>
      KCoord.posLog_le_half_log (ρ s) (hρ s).1
    have h1 := KCoord.finMean_mono hpt
    rw [KCoord.finMean_const_mul] at h1
    have hj : finMean (fun s => log (1 + x s)) ≤ log (1 + finMean x) := by
      have hcard := (KCoord.card_pos_real (S := S))
      have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := Finset.univ)
        (w := fun _ : S => (1 : ℝ) / Fintype.card S) (p := fun s => 1 + x s)
        (fun _ _ => by positivity)
        (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
        (fun s _ => by
          show (0 : ℝ) < 1 + x s
          have : 0 ≤ x s := by simp only [hx]; positivity
          linarith)
      simp only [smul_eq_mul] at hJ
      have e1 : ∑ s, 1 / (Fintype.card S : ℝ) * log (1 + x s) = finMean fun s => log (1 + x s) := by
        simp [finMean, ← Finset.mul_sum, div_eq_inv_mul]
      have e2 : ∑ s, 1 / (Fintype.card S : ℝ) * (1 + x s) = 1 + finMean x := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, finMean]
        field_simp
      rw [e1, e2] at hJ
      exact hJ
    linarith

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KCoord

theorem sq_coord_le {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) (hY : Y.PosDef)
    (i : ι) (v : ι → ℝ) : v i ^ 2 ≤ Y⁻¹ i i * qf Y v := by
  have hU : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit
  have hsymm : Yᵀ = Y := by
    have := hY.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set w : ι → ℝ := Y⁻¹ *ᵥ Pi.single i 1 with hw
  have hYw : Y *ᵥ w = Pi.single i 1 := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  have hwY : ∀ x : ι → ℝ, w ⬝ᵥ (Y *ᵥ x) = x i := by
    intro x
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, hYw]
    simp [dotProduct, Pi.single_apply]
  have hxY : ∀ x : ι → ℝ, x ⬝ᵥ (Y *ᵥ w) = x i := by
    intro x
    rw [hYw]
    simp [dotProduct, Pi.single_apply]
  have hwi : w i = Y⁻¹ i i := by
    rw [hw]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hpos : 0 < Y⁻¹ i i := hY.inv.diag_pos
  have hnn : ∀ t : ℝ, 0 ≤ qf Y v - 2 * t * v i + t ^ 2 * Y⁻¹ i i := by
    intro t
    have h0 : 0 ≤ (v - t • w) ⬝ᵥ (Y *ᵥ (v - t • w)) := by
      have := hY.posSemidef.dotProduct_mulVec_nonneg (v - t • w)
      simpa using this
    have hexp : (v - t • w) ⬝ᵥ (Y *ᵥ (v - t • w)) =
        qf Y v - 2 * t * v i + t ^ 2 * Y⁻¹ i i := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [hwY, hwY, hxY, hwi]
      simp only [qf]
      ring
    linarith
  have h := hnn (v i / Y⁻¹ i i)
  have hne : Y⁻¹ i i ≠ 0 := ne_of_gt hpos
  have e : qf Y v - 2 * (v i / Y⁻¹ i i) * v i + (v i / Y⁻¹ i i) ^ 2 * Y⁻¹ i i =
      qf Y v - v i ^ 2 / Y⁻¹ i i := by
    field_simp
    ring
  rw [e] at h
  have h2 : v i ^ 2 / Y⁻¹ i i ≤ qf Y v := by linarith
  rwa [div_le_iff₀ hpos, mul_comm] at h2

end KCoord

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset

noncomputable section

namespace PlueckerNormSqAlt

theorem onePipe_mul_conjTranspose {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) :
    onePipe Z * (onePipe Z)ᴴ = 1 + Z * Zᴴ := by
  ext a b
  simp only [Matrix.mul_apply, conjTranspose_apply, onePipe, of_apply, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, Matrix.add_apply]
  congr 1
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

theorem rowsOf_conjTranspose {j N : ℕ} (A : Matrix (Fin j) (Fin N) ℂ)
    (I : {I : Finset (Fin N) // I.card = j}) : rowsOf Aᴴ I = (colsOf A I)ᴴ := by
  ext a b
  simp [rowsOf, colsOf, conjTranspose_apply]

end PlueckerNormSqAlt


open PlueckerNormSqAlt in
theorem PlueckerNormSq.proof (h : CauchyBinet.Statement) : PlueckerNormSq.Statement := by
  intro j m Z
  rw [← onePipe_mul_conjTranspose, h ℂ j (j + m) (onePipe Z) (onePipe Z)ᴴ]
  push_cast
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [rowsOf_conjTranspose, det_conjTranspose, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  rfl

end

end GroundTheory.Heights₂.Heights
end
