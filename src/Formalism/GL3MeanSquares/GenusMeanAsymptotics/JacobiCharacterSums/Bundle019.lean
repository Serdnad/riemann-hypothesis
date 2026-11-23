module

public import Formalism.GL3MeanSquares.Bundle001
public import Formalism.LandauZeroFreeBounds.Bundle001
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle008
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle010
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle004
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensBlock
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle018
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle013
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006

@[expose] public section

section

open Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

lemma tail_box_log {n t Q : ℝ} (hn : 1 ≤ n) (hQ : 2 ≤ Q) (hnQ : n ≤ Q) (ht : |t| ≤ Q - 1) :
    Real.log (n * (|t| + 2)) ≤ 3 * Real.log Q := by
  have hn0 : 0 < n := by linarith
  have hpos : 0 < n * (|t| + 2) := mul_pos hn0 (by positivity)
  have h1 : n * (|t| + 2) ≤ Q ^ 3 := by
    have ht2 : |t| + 2 ≤ Q + 1 := by linarith
    have hQ2 : Q + 1 ≤ Q ^ 2 := by nlinarith
    calc n * (|t| + 2) ≤ Q * (Q + 1) := mul_le_mul hnQ ht2 (by positivity) (by linarith)
      _ ≤ Q * Q ^ 2 := mul_le_mul_of_nonneg_left hQ2 (by linarith)
      _ = Q ^ 3 := by ring
  calc Real.log (n * (|t| + 2)) ≤ Real.log (Q ^ 3) := Real.log_le_log hpos h1
    _ = 3 * Real.log Q := by rw [Real.log_pow]; norm_num

lemma tail_box_sum {δ : ℝ} (hδ : 0 < δ) (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (h : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) :
    ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / δ := by
  calc ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / δ := Finset.sum_le_sum fun ρ hρ => by
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (h ρ hρ)
    _ = (∑ ρ ∈ Z, (m ρ : ℝ)) / δ := by rw [Finset.sum_div]

theorem tail_box_negLD (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (Q : ℝ), χ ≠ 1 → 2 ≤ Q → (N : ℝ) ≤ Q →
      Formalism.HermitianLattices.ZeroFreeRegionGL2.ZeroFreeBox Q χ →
      ∀ s : ℂ, 1 - 1 / 400 + δ ≤ s.re → |s.im| ≤ Q - 1 →
        ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ K * Real.log Q := by
  obtain ⟨C, hC⟩ := Formalism.ZeroFreeDirichlet.lfunction_polynomial_growth
  obtain ⟨CR, hCR0, hCR⟩ := Formalism.ZeroFreeDirichlet.l_log_deriv_right
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA0 : 0 ≤ Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1 := by
    have : 0 ≤ Real.log (2 * (21 * (|C| + 1))) :=
      Real.log_nonneg (by have := abs_nonneg C; nlinarith)
    positivity
  refine ⟨3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (1440 / 11 + 1 / (δ * Real.log 2)) +
    (10 + CR) / Real.log 2, by positivity, ?_⟩
  intro N _ χ Q hχ hQ hNQ hbox s hs ht
  have hlogQ : Real.log 2 ≤ Real.log Q := Real.log_le_log two_pos hQ
  have hlogQ0 : 0 ≤ Real.log Q := hl2.le.trans hlogQ
  have hrest : 0 ≤ (10 + CR) / Real.log 2 * Real.log Q := by positivity
  by_cases hσ : s.re < 11 / 10
  ·
    have hfs : DirichletCharacter.LFunction χ s ≠ 0 := hbox s (by linarith) (by linarith)
    obtain ⟨Z, m, hZ, -, hsum, hdiff⟩ := Formalism.ZeroFreeDirichlet.landau_lemma_lfunction_zeros Formalism.ZeroFreeDirichlet.landau_local3 hC
      Formalism.ZeroFreeDirichlet.inverseBound hχ (by linarith) hσ hfs
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
    have hlog3 := tail_box_log hN1 hQ hNQ ht

    have hfar : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖ := by
      intro ρ hρ
      obtain ⟨hball, hzero⟩ := (hZ ρ).1 hρ
      rw [Metric.mem_closedBall, dist_eq_norm] at hball
      have him : |ρ.im - s.im| ≤ 11 / 20 / 3 := by
        have := Complex.abs_im_le_norm (ρ - ((21 / 20 : ℂ) + s.im * I))
        simp at this
        linarith
      have hre : ρ.re ≤ 1 - 1 / 400 := by
        by_contra hgt
        push Not at hgt
        have hρim : |ρ.im| ≤ Q := by
          have := abs_sub_abs_le_abs_sub ρ.im s.im
          linarith
        exact hbox ρ hgt hρim hzero
      have := Complex.re_le_norm (s - ρ)
      rw [Complex.sub_re] at this
      linarith
    have hS := tail_box_sum hδ Z m s hfar
    have e1 : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q)) :=
      hdiff.trans (by gcongr)
    have e2 : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q) / Real.log 2 / δ := by
      refine hS.trans (div_le_div_of_nonneg_right ?_ hδ.le)
      exact hsum.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog3 hA0) hl2.le)
    have htri : ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤
        ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by
      rw [Formalism.ZeroFreeDirichlet.negLD, norm_neg]
      exact (norm_add_le _ _).trans_eq' (by rw [sub_add_cancel])
    have hδ0 : δ ≠ 0 := hδ.ne'
    have hl20 : Real.log 2 ≠ 0 := hl2.ne'
    have e3 : 1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q)) +
        (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (3 * Real.log Q) / Real.log 2 / δ =
        3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) * (1440 / 11 + 1 / (δ * Real.log 2)) *
          Real.log Q := by
      field_simp
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ _ := htri
      _ ≤ _ := add_le_add e1 e2
      _ = _ := e3
      _ ≤ _ := by rw [add_mul]; linarith
  ·
    push Not at hσ
    have h1 : 1 < s.re := by linarith
    have hb := hCR N χ s h1
    have hinv : 1 / (s.re - 1) ≤ 10 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have e5 : 10 + CR ≤ (10 + CR) / Real.log 2 * Real.log Q := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlogQ (by linarith)
    have hbig : 0 ≤ 3 * (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
        (1440 / 11 + 1 / (δ * Real.log 2)) * Real.log Q := by positivity
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ 1 / (s.re - 1) + CR := hb
      _ ≤ 10 + CR := by linarith
      _ ≤ (10 + CR) / Real.log 2 * Real.log Q := e5
      _ ≤ _ := by rw [add_mul]; linarith

end Formalism.HermitianLattices.Ext.BoxTail
end
end

section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem second_block_count (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)) (U : ℕ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hq : 256 ≤ qd M T)
    (hc : 971882496 * Real.log (qd M T) ^ 5 ≤ Real.sqrt (qd M T))
    (hU1 : qd M T ^ 3 ≤ U) (hU2 : 2 * U ≤ qd M T ^ 12)
    (hS : ∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T)
    (hsp : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|)
    (hbig : ∀ p ∈ S, 1 / (2 * (pJd M T : ℝ)) ≤
      ‖blkD (pYd M T) (pNd M T) U (fun n => p.1 (n : ZMod M)) p.2‖) :
    (S.card : ℝ) ≤ 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) * (4 * (48 * Real.log ((M : ℝ) * T)) ^ 2) := by
  set q := qd M T with hqdef
  set x : ℝ := (M : ℝ) * T with hx
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ x := by rw [hx]; nlinarith
  have hxq : x ≤ q := Nat.le_ceil x
  have hqx1 : (q : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hqx : (q : ℝ) ≤ 2 * x := by linarith
  have hq' : (256 : ℝ) ≤ q := by exact_mod_cast hq
  have hl1 : 1 ≤ Real.log x := one_le_log_of_three_le_second (by linarith)
  have hLq1 : 1 ≤ Real.log q := one_le_log_of_three_le_second (by linarith)
  have hLq : Real.log q ≤ 2 * Real.log x := by
    have h1 : Real.log q ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hqx
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hU : 1 ≤ U := le_trans (Nat.one_le_pow _ _ (by omega)) hU1
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hJ : ((pJd M T : ℕ) : ℝ) ≤ 24 * Real.log q := dyadic_index_le_log_second q (by omega)
  have hJ0 : (0 : ℝ) < (pJd M T : ℝ) := by
    have : 0 < pJd M T := by unfold pJd; omega
    exact_mod_cast this
  have hl0 : 0 ≤ Real.log (2 * (U : ℝ)) := Real.log_nonneg (by linarith)
  have hl : 1 + Real.log (2 * (U : ℝ)) ≤ 13 * Real.log q := by
    have h1 : (2 * (U : ℝ)) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU2
    have h2 : Real.log (2 * (U : ℝ)) ≤ Real.log ((q : ℝ) ^ 12) := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hG : 9 + 8 * Real.log (2 * T + 1) ≤ 17 * Real.log x := by
    have h1 : Real.log (2 * T + 1) ≤ Real.log x :=
      Real.log_le_log (by linarith) (by rw [hx]; nlinarith)
    linarith
  have hG0 : 0 ≤ 9 + 8 * Real.log (2 * T + 1) := by
    have : 0 ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
    linarith
  have hK0 : 0 ≤ 8 * ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hK : 8 * ((M : ℝ) + 1) * (2 + 2 * T) ≤ 48 * q := by
    have : 8 * ((M : ℝ) + 1) * (2 + 2 * T) ≤ 48 * x := by rw [hx]; nlinarith
    linarith
  have hθ : (0 : ℝ) < 1 / (2 * (pJd M T : ℝ)) := by positivity
  have hsmall := second_small_condition ((U : ℝ) ^ (1 - 2 * σ)) (1 + Real.log (2 * (U : ℝ)))
    (8 * ((M : ℝ) + 1) * (2 + 2 * T)) (pJd M T : ℝ) q (Real.sqrt q) (Real.log q) (by linarith)
    (Real.sqrt_pos.2 (by linarith)) (rpow_neg_exponent_bound_second q U σ (by omega) hσ hU1) (by linarith) hl hK0 hK
    hJ0 hJ hc
  have hmain := dyadic_block_count S (fun p n => p.1 (n : ZMod M)) (fun p => p.2) (pYd M T) (pNd M T) U σ
    (1 / (2 * (pJd M T : ℝ))) (9 + 8 * Real.log (2 * T + 1)) (8 * ((M : ℝ) + 1) * (2 + 2 * T))
    hU hθ (by linarith) hG0 hK0 (fun p _ n => DirichletCharacter.norm_le_one _ _)
    (fun p hp => (hS p hp).1)
    (off_diagonal_bound M S σ T U hU hT (by linarith) hS hsp) hbig hsmall
  refine hmain.trans ?_
  have hu2 := rpow_pos_exponent_bound_second q U x σ (by linarith) hqx hσ hσ1 (by omega)
  have hu0 : 0 ≤ (U : ℝ) ^ (2 - 2 * σ) := by positivity
  have he : 4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) / (1 / (2 * (pJd M T : ℝ))) ^ 2 =
      4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) * (4 * (pJd M T : ℝ) ^ 2) := by
    field_simp
    ring
  rw [he]
  have hl' : 1 + Real.log (2 * (U : ℝ)) ≤ 26 * Real.log x := by linarith
  have hJ' : (pJd M T : ℝ) ≤ 48 * Real.log x := by linarith
  have hl00 : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by linarith
  gcongr

theorem zero_count_second : Count1 := by
  obtain ⟨q₁, hq₁⟩ := log_pow_five_le_sqrt 971882496
  refine ⟨48 * (4 * 64 * 26 ^ 3 * 17 * (4 * 48 ^ 2)), max q₁ 256, ?_⟩
  intro M _ T σ S hM hT hσ hq hS hsp
  have hq256 : 256 ≤ qd M T := le_trans (le_max_right _ _) hq
  have hc := hq₁ (qd M T) (le_trans (le_max_left _ _) hq)
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ (M : ℝ) * T := by nlinarith
  have hl1 : 1 ≤ Real.log ((M : ℝ) * T) := one_le_log_of_three_le_second (by linarith)
  have hX0 : 0 ≤ ((M : ℝ) * T) ^ (24 * (1 - σ)) := by positivity
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp only [card_empty, Nat.cast_zero]; positivity
  have hσ1 : σ ≤ 1 := by
    obtain ⟨-, h1, h2, -⟩ := hS p₀ hp₀
    linarith
  set B : ℝ := 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) * (4 * (48 * Real.log ((M : ℝ) * T)) ^ 2) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  classical
  let Sj : ℕ → Finset (DirichletCharacter ℂ M × ℂ) := fun j =>
    S.filter (fun p => 1 / (2 * (pJd M T : ℝ)) ≤
      ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => p.1 (n : ZMod M)) p.2‖)
  have hsub : S ⊆ (range (pJd M T)).biUnion Sj := by
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hp
    obtain ⟨j, hj, hjb⟩ := zero_detection_second M p.1 h1 T hT hM p.2 (by linarith) h4 h5
    exact mem_biUnion.2 ⟨j, hj, mem_filter.2 ⟨hp, hjb⟩⟩
  have hj : ∀ j ∈ range (pJd M T), ((Sj j).card : ℝ) ≤ B := by
    intro j hj
    have hjJ : j < pJd M T := mem_range.1 hj
    have hYN : qd M T ^ 3 * 2 ^ pJd M T ≤ qd M T ^ 12 := dyadic_size_le_pow_twelve_second (qd M T) hq256
    apply second_block_count M T σ (Sj j) (pYd M T * 2 ^ j) hM hT hσ hσ1 hq256 hc
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · calc 2 * (pYd M T * 2 ^ j) = qd M T ^ 3 * 2 ^ (j + 1) := by unfold pYd; ring
        _ ≤ qd M T ^ 3 * 2 ^ pJd M T := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ _ := hYN
    · intro p hp
      obtain ⟨-, h2, h3, h4, -⟩ := hS p (mem_filter.1 hp).1
      exact ⟨h2, h3.le, h4⟩
    · intro p hp p' hp'
      exact hsp p (mem_filter.1 hp).1 p' (mem_filter.1 hp').1
    · intro p hp
      exact (mem_filter.1 hp).2
  have h1 : (S.card : ℝ) ≤ ∑ j ∈ range (pJd M T), ((Sj j).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    exact_mod_cast this
  have h2 : ∑ j ∈ range (pJd M T), ((Sj j).card : ℝ) ≤ (pJd M T : ℝ) * B := by
    have := sum_le_card_nsmul (range (pJd M T)) (fun j => ((Sj j).card : ℝ)) B hj
    simpa using this
  have hJ' : (pJd M T : ℝ) ≤ 48 * Real.log ((M : ℝ) * T) := by
    have hJ : ((pJd M T : ℕ) : ℝ) ≤ 24 * Real.log (qd M T) := dyadic_index_le_log_second (qd M T) (by omega)
    have hqx1 : ((qd M T : ℕ) : ℝ) < (M : ℝ) * T + 1 := Nat.ceil_lt_add_one (by linarith)
    have hq' : (256 : ℝ) ≤ (qd M T : ℝ) := by exact_mod_cast hq256
    have h3 : Real.log (qd M T) ≤ Real.log (2 * ((M : ℝ) * T)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3
    have h4 : Real.log 2 ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have h3 : (pJd M T : ℝ) * B ≤ 48 * Real.log ((M : ℝ) * T) * B := by gcongr
  have h4 : 48 * Real.log ((M : ℝ) * T) * B =
      48 * (4 * 64 * 26 ^ 3 * 17 * (4 * 48 ^ 2)) * ((M : ℝ) * T) ^ (24 * (1 - σ)) *
        Real.log ((M : ℝ) * T) ^ 7 := by
    rw [hB]; ring
  have h5 : Real.log ((M : ℝ) * T) ^ 7 ≤ Real.log ((M : ℝ) * T) ^ 10 :=
    pow_le_pow_right₀ hl1 (by norm_num)
  calc (S.card : ℝ) ≤ 48 * Real.log ((M : ℝ) * T) * B := h1.trans (h2.trans h3)
    _ = _ := h4
    _ ≤ _ := by gcongr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

section

open Finset Complex Classical Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhc_removable (Z : Finset ℂ) : ∀ (U : Set ℂ) (G : ℂ → ℂ) (C : ℝ), IsOpen U →
    DifferentiableOn ℂ G (U \ (Z : Set ℂ)) → (∀ z ∈ U \ (Z : Set ℂ), ‖G z‖ ≤ C) →
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧ (∀ z ∈ U \ (Z : Set ℂ), H z = G z) ∧
      ∀ z ∈ U, ‖H z‖ ≤ C := by
  induction Z using Finset.induction_on with
  | empty =>
    intro U G C _ hd hb
    exact ⟨G, by simpa using hd, fun _ _ => rfl, by simpa using hb⟩
  | insert a Z ha ih =>
    intro U G C hU hd hb
    have hset : U \ ((insert a Z : Finset ℂ) : Set ℂ) = (U \ {a}) \ (Z : Set ℂ) := by
      ext z
      simp [not_or, and_assoc]
    rw [hset] at hd hb
    obtain ⟨H₁, hH₁d, hH₁e, hH₁b⟩ := ih (U \ {a}) G C (hU.sdiff isClosed_singleton) hd hb
    rw [hset]
    by_cases haU : a ∈ U
    · have hUa : U ∈ 𝓝 a := hU.mem_nhds haU
      have hbd : BddAbove (norm ∘ H₁ '' (U \ {a})) :=
        ⟨C, by rintro _ ⟨z, hz, rfl⟩; exact hH₁b z hz⟩
      have hD := differentiableOn_update_limUnder_of_bddAbove hUa hH₁d hbd
      have hne : ∀ z, z ≠ a → Function.update H₁ a (limUnder (𝓝[≠] a) H₁) z = H₁ z :=
        fun z hz => Function.update_of_ne hz _ _
      refine ⟨_, hD, ?_, ?_⟩
      · intro z hz
        rw [hne z hz.1.2]
        exact hH₁e z hz
      · intro z hz
        by_cases hza : z = a
        · rw [hza]
          have hc := (hD.differentiableAt hUa).continuousAt
          have ht := (hc.norm).tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))
          refine le_of_tendsto ht ?_
          filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hUa] with w hw hwU
          rw [hne w hw]
          exact hH₁b w ⟨hwU, hw⟩
        · rw [hne z hza]
          exact hH₁b z ⟨hz, hza⟩
    · have hUe : U \ {a} = U := Set.sdiff_singleton_eq_self haU
      rw [hUe] at hH₁d hH₁b hH₁e ⊢
      exact ⟨H₁, hH₁d, hH₁e, hH₁b⟩

lemma dhc_iter (c ρ : ℂ) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun z => c / (z - ρ)) s =
      c * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ := by
  have h : (fun z : ℂ => c / (z - ρ)) = fun z => c * (fun z : ℂ => (1 * z - ρ)⁻¹) z := by
    ext z
    simp [div_eq_mul_inv]
  have hk : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
  simp only [one_pow, mul_one, one_mul]
  rw [hk, zpow_neg, zpow_natCast]
  ring

lemma dhc_cauchy (H : ℂ → ℂ) (z₀ s : ℂ) (ϱ C : ℝ) (hϱ : 0 < ϱ)
    (hHd : DifferentiableOn ℂ H (Metric.ball z₀ (2 * ϱ))) (hHb : ∀ z ∈ Metric.ball z₀ (2 * ϱ), ‖H z‖ ≤ C)
    (hs : s ∈ Metric.closedBall z₀ ϱ) (k : ℕ) :
    ‖iteratedDeriv k H s‖ ≤ k.factorial * C / ϱ ^ k := by
  have hcont : ContinuousAt (fun R : ℝ => (k.factorial : ℝ) * C / R ^ k) ϱ :=
    continuousAt_const.div (continuousAt_id.pow k) (pow_pos hϱ k).ne'
  have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio ϱ))
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hϱ] with R hR
  have hsub : Metric.closedBall s R ⊆ Metric.ball z₀ (2 * ϱ) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz hs
    rw [Metric.mem_ball]
    have := dist_triangle z s z₀
    linarith [hR.2]
  exact norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR.1 (hHd.diffContOnCl_ball hsub)
    (fun z hz => hHb z (hsub (Metric.sphere_subset_closedBall hz)))

theorem deuring_heilbronn_cauchy : DHCauchy := by
  intro f z₀ r B hr hB hfd hf0 hfb
  obtain ⟨Z, m, hZ, hm1, -, -, hsum, hbd⟩ := landau_local3 f z₀ r B hr hB hfd hf0 hfb
  refine ⟨Z, m, hZ, hm1, hsum, ?_⟩
  have hfan : ∀ z ∈ Metric.ball z₀ (r / 6), AnalyticAt ℂ f z := fun z hz =>
    (hfd.mono Metric.ball_subset_closedBall).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (by linarith) hz))
  have hnz : ∀ z ∈ Metric.ball z₀ (r / 6) \ (Z : Set ℂ), f z ≠ 0 := fun z hz h0 =>
    hz.2 (Finset.mem_coe.2 ((hZ z).2
      ⟨Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hz.1), h0⟩))
  have hGd : DifferentiableOn ℂ (fun z => deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ))
      (Metric.ball z₀ (r / 6) \ (Z : Set ℂ)) := by
    intro z hz
    have h1 := hfan z hz.1
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (h1.deriv.differentiableAt.div h1.differentiableAt (hnz z hz)).sub ?_
    refine DifferentiableAt.fun_sum (fun ρ hρ => ?_)
    exact (differentiableAt_const _).div (differentiableAt_id.sub_const ρ)
      (sub_ne_zero.2 (fun h => hz.2 (h ▸ Finset.mem_coe.2 hρ)))
  obtain ⟨H, hHd, hHe, hHb⟩ := dhc_removable Z _ _ (72 * Real.log B / r) Metric.isOpen_ball hGd
    (fun z hz => hbd z (Metric.ball_subset_closedBall hz.1) (hnz z hz))
  intro k s hs hfs
  have hsZ : s ∉ (Z : Set ℂ) := fun h => hfs ((hZ s).1 (Finset.mem_coe.1 h)).2
  have hsU : s ∈ Metric.ball z₀ (r / 6) := by
    rw [Metric.mem_closedBall] at hs
    rw [Metric.mem_ball]
    linarith
  have hev : (fun z => -(deriv f z / f z)) =ᶠ[𝓝 s]
      fun z => -(∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) - H z := by
    have hn : Metric.ball z₀ (r / 6) \ (Z : Set ℂ) ∈ 𝓝 s :=
      (Metric.isOpen_ball.sdiff Z.finite_toSet.isClosed).mem_nhds ⟨hsU, hsZ⟩
    filter_upwards [hn] with z hz
    rw [hHe z hz]
    ring
  have hHan : AnalyticAt ℂ H s := hHd.analyticAt (Metric.isOpen_ball.mem_nhds hsU)
  have hcd : ∀ ρ ∈ Z, ContDiffAt ℂ k (fun z => (m ρ : ℂ) / (z - ρ)) s := fun ρ hρ =>
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const)
      (sub_ne_zero.2 (fun h => hsZ (h ▸ Finset.mem_coe.2 hρ)))
  have hkey : ‖iteratedDeriv k H s‖ ≤ k.factorial * (72 * Real.log B / r) / (r / 12) ^ k := by
    have h2 : 2 * (r / 12) = r / 6 := by ring
    exact dhc_cauchy H z₀ s (r / 12) _ (by positivity) (h2 ▸ hHd) (h2 ▸ hHb) hs k
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpm : ((-1 : ℂ) ^ k * (-1) ^ k) = 1 := by rw [← mul_pow]; simp
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_fun_sub (ContDiffAt.neg (ContDiffAt.sum hcd)) hHan.contDiffAt,
    iteratedDeriv_fun_neg, iteratedDeriv_fun_sum hcd]
  simp_rw [dhc_iter]
  have he : (-1 : ℂ) ^ k / (k.factorial : ℂ) *
        (-∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ -
          iteratedDeriv k H s) + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) =
      -((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k H s) := by
    have : ∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ =
        ((-1) ^ k * (k.factorial : ℂ)) * ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [div_eq_mul_inv]
      ring
    rw [this]
    generalize (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)) = S
    field_simp
    linear_combination (-(k.factorial : ℂ) * S) * hpm
  rw [he, norm_neg, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hfr : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  calc 1 / (k.factorial : ℝ) * ‖iteratedDeriv k H s‖
      ≤ 1 / (k.factorial : ℝ) * (k.factorial * (72 * Real.log B / r) / (r / 12) ^ k) := by gcongr
    _ = 72 * Real.log B / r * (12 / r) ^ k := by
      rw [div_pow, div_pow]
      field_simp

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
