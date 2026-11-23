module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle004
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.OneSubTwoCpowLower
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensBlock
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplBox
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLF
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplMainA
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle022
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem count_block0 (M : ℕ) (T σ c : ℝ) (S : Finset (DirichletCharacter ℂ 1 × ℂ)) (N U : ℕ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hq : 512 ≤ qd M T) (hc0 : 0 < c)
    (hc : 87880000 / c ^ 2 * Real.log (qd M T) ^ 7 ≤ Real.sqrt (qd M T))
    (hU1 : qd M T ^ 3 ≤ U) (hU2 : 2 * U ≤ qd M T ^ 12)
    (hS : ∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T)
    (hsp : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → 1 ≤ |p.2.im - p'.2.im|)
    (hbig : ∀ p ∈ S, c / (((pJd M T : ℝ) + 1) * Real.log (qd M T)) ≤
      ‖blkD (pYd M T) N U (fun n => p.1 (n : ZMod 1)) p.2‖) :
    (S.card : ℝ) ≤ 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) *
      ((50 * Real.log ((M : ℝ) * T) * (2 * Real.log ((M : ℝ) * T))) ^ 2 / c ^ 2) := by
  set q := qd M T with hqdef
  set x : ℝ := (M : ℝ) * T with hx
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ x := by rw [hx]; nlinarith
  have hxq : x ≤ q := Nat.le_ceil x
  have hqx1 : (q : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hqx : (q : ℝ) ≤ 2 * x := by linarith
  have hq' : (512 : ℝ) ≤ q := by exact_mod_cast hq
  have hl1 : 1 ≤ Real.log x := one_le_log_of_three_le' (by linarith)
  have hLq1 : 1 ≤ Real.log q := one_le_log_of_three_le' (by linarith)
  have hLq : Real.log q ≤ 2 * Real.log x := by
    have h1 : Real.log q ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hqx
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hU : 1 ≤ U := le_trans (Nat.one_le_pow _ _ (by omega)) hU1
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hJ : ((pJd M T : ℕ) : ℝ) + 1 ≤ 25 * Real.log q := dyadic_index_le_log q (by omega)
  have hJ0 : (0 : ℝ) < (pJd M T : ℝ) + 1 := by positivity
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
  have hK0 : 0 ≤ 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hK : 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) ≤ 16 * q := by
    have : 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) ≤ 16 * x := by
      rw [hx]; push_cast; nlinarith
    linarith
  have hθ : (0 : ℝ) < c / (((pJd M T : ℝ) + 1) * Real.log q) := by positivity
  have hsmall := first_small_condition ((U : ℝ) ^ (1 - 2 * σ)) (1 + Real.log (2 * (U : ℝ)))
    (8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T)) ((pJd M T : ℝ) + 1) q (Real.sqrt q) (Real.log q) c
    (by linarith) (Real.sqrt_pos.2 (by linarith)) hc0 (rpow_neg_exponent_bound q U σ (by omega) hσ hU1)
    (by linarith) hl hK0 hK hJ0 hJ hc
  have hmain := dyadic_block_count S (fun p n => p.1 (n : ZMod 1)) (fun p => p.2) (pYd M T) N U σ
    (c / (((pJd M T : ℝ) + 1) * Real.log q)) (9 + 8 * Real.log (2 * T + 1))
    (8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T))
    hU hθ (by linarith) hG0 hK0 (fun p _ n => DirichletCharacter.norm_le_one _ _)
    (fun p hp => (hS p hp).1)
    (off_diagonal_bound 1 S σ T U hU hT (by linarith) hS (fun p hp p' hp' hne _ => hsp p hp p' hp' hne))
    hbig hsmall
  refine hmain.trans ?_
  have hu2 := rpow_pos_exponent_bound q U x σ (by linarith) hqx hσ hσ1 (by omega)
  have hu0 : 0 ≤ (U : ℝ) ^ (2 - 2 * σ) := by positivity
  have he : 4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) / (c / (((pJd M T : ℝ) + 1) * Real.log q)) ^ 2 =
      4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) * ((((pJd M T : ℝ) + 1) * Real.log q) ^ 2 / c ^ 2) := by
    have hLq0 : Real.log q ≠ 0 := by linarith
    field_simp
  rw [he]
  have hl' : 1 + Real.log (2 * (U : ℝ)) ≤ 26 * Real.log x := by linarith
  have hJ' : (pJd M T : ℝ) + 1 ≤ 50 * Real.log x := by linarith
  have hl00 : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by linarith
  have hLq00 : 0 ≤ Real.log q := by linarith
  gcongr

theorem zero_count_first : Count0 := by
  obtain ⟨c, hc0, q₂, hdet⟩ := zero_detection_first
  obtain ⟨q₁, hq₁⟩ := log_pow_seven_le_sqrt (87880000 / c ^ 2)
  refine ⟨100 * (4 * 64 * 26 ^ 3 * 17 * (100 ^ 2 / c ^ 2)), max (max q₁ q₂) 512, ?_⟩
  intro M _ T σ S hM hT hσ hq hS hsp
  have hq512 : 512 ≤ qd M T := le_trans (le_max_right _ _) hq
  have hc := hq₁ (qd M T) (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq)
  have hq2 : q₂ ≤ qd M T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ (M : ℝ) * T := by nlinarith
  have hl1 : 1 ≤ Real.log ((M : ℝ) * T) := one_le_log_of_three_le' (by linarith)
  have hX0 : 0 ≤ ((M : ℝ) * T) ^ (24 * (1 - σ)) := by positivity
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp only [card_empty, Nat.cast_zero]; positivity
  have hσ1 : σ ≤ 1 := by
    obtain ⟨-, h1, h2, -⟩ := hS p₀ hp₀
    linarith
  set B : ℝ := 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) *
      ((50 * Real.log ((M : ℝ) * T) * (2 * Real.log ((M : ℝ) * T))) ^ 2 / c ^ 2) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  classical
  let e : DirichletCharacter ℂ M × ℂ → DirichletCharacter ℂ 1 × ℂ := fun p => (1, p.2)
  have hinj : Set.InjOn e (S : Set (DirichletCharacter ℂ M × ℂ)) := by
    intro p hp p' hp' h
    have h2 : (e p).2 = (e p').2 := congrArg Prod.snd h
    exact Prod.ext ((hS p hp).1.trans (hS p' hp').1.symm) h2
  set S' : Finset (DirichletCharacter ℂ 1 × ℂ) := S.image e with hS'
  have hcard : S'.card = S.card := card_image_of_injOn hinj
  let Sij : ℕ × ℕ → Finset (DirichletCharacter ℂ 1 × ℂ) := fun ij =>
    S'.filter (fun p => c / (((pJd M T : ℝ) + 1) * Real.log (qd M T)) ≤
      ‖blkD (pYd M T) (2 ^ ij.1 * pNd M T) (pYd M T * 2 ^ ij.2) (fun n => p.1 (n : ZMod 1)) p.2‖)
  have hsub : S' ⊆ (range 2 ×ˢ range (pJd M T + 1)).biUnion Sij := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS a ha
    rw [h1] at h5
    obtain ⟨i, hi, j, hj, hjb⟩ := hdet M T hT hM hq2 a.2 (by linarith) h4 h5
    exact mem_biUnion.2 ⟨(i, j), mem_product.2 ⟨hi, hj⟩, mem_filter.2 ⟨hp, hjb⟩⟩
  have hj : ∀ ij ∈ range 2 ×ˢ range (pJd M T + 1), ((Sij ij).card : ℝ) ≤ B := by
    intro ij hij
    have hjJ : ij.2 < pJd M T + 1 := mem_range.1 (mem_product.1 hij).2
    have hYN : 2 * (qd M T ^ 3 * 2 ^ pJd M T) ≤ qd M T ^ 12 := dyadic_size_le_pow_twelve (qd M T) hq512
    apply count_block0 M T σ c (Sij ij) (2 ^ ij.1 * pNd M T) (pYd M T * 2 ^ ij.2) hM hT hσ hσ1 hq512
      hc0 hc
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · calc 2 * (pYd M T * 2 ^ ij.2) ≤ 2 * (qd M T ^ 3 * 2 ^ pJd M T) := by
            unfold pYd
            gcongr
            omega
        _ ≤ _ := hYN
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := mem_image.1 (mem_filter.1 hp).1
      obtain ⟨-, h2, h3, h4, -⟩ := hS a ha
      exact ⟨h2, h3.le, h4⟩
    · intro p hp p' hp' hne
      obtain ⟨a, ha, rfl⟩ := mem_image.1 (mem_filter.1 hp).1
      obtain ⟨a', ha', rfl⟩ := mem_image.1 (mem_filter.1 hp').1
      exact hsp a ha a' ha' (fun h => hne (by rw [h]))
    · intro p hp
      exact (mem_filter.1 hp).2
  have h1 : (S.card : ℝ) ≤ ∑ ij ∈ range 2 ×ˢ range (pJd M T + 1), ((Sij ij).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    rw [hcard] at this
    exact_mod_cast this
  have h2 : ∑ ij ∈ range 2 ×ˢ range (pJd M T + 1), ((Sij ij).card : ℝ) ≤
      2 * ((pJd M T : ℝ) + 1) * B := by
    have := sum_le_card_nsmul (range 2 ×ˢ range (pJd M T + 1)) (fun ij => ((Sij ij).card : ℝ)) B hj
    simpa using this
  have hJ' : (pJd M T : ℝ) + 1 ≤ 50 * Real.log ((M : ℝ) * T) := by
    have hJ : ((pJd M T : ℕ) : ℝ) + 1 ≤ 25 * Real.log (qd M T) := dyadic_index_le_log (qd M T) (by omega)
    have hqx1 : ((qd M T : ℕ) : ℝ) < (M : ℝ) * T + 1 := Nat.ceil_lt_add_one (by linarith)
    have hq' : (512 : ℝ) ≤ (qd M T : ℝ) := by exact_mod_cast hq512
    have h3 : Real.log (qd M T) ≤ Real.log (2 * ((M : ℝ) * T)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3
    have h4 : Real.log 2 ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have h3 : 2 * ((pJd M T : ℝ) + 1) * B ≤ 2 * (50 * Real.log ((M : ℝ) * T)) * B := by gcongr
  have h4 : 2 * (50 * Real.log ((M : ℝ) * T)) * B =
      100 * (4 * 64 * 26 ^ 3 * 17 * (100 ^ 2 / c ^ 2)) * ((M : ℝ) * T) ^ (24 * (1 - σ)) *
        Real.log ((M : ℝ) * T) ^ 9 := by
    rw [hB]; ring
  have h5 : Real.log ((M : ℝ) * T) ^ 9 ≤ Real.log ((M : ℝ) * T) ^ 10 :=
    pow_le_pow_right₀ hl1 (by norm_num)
  calc (S.card : ℝ) ≤ 2 * (50 * Real.log ((M : ℝ) * T)) * B := h1.trans (h2.trans h3)
    _ = _ := h4
    _ ≤ _ := by gcongr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem density_norm (h : LogDensityM) :
    ∃ a B C : ℝ, 1 ≤ a ∧ 0 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℕ) [NeZero M] (T v : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)), 3 ≤ M → 2 ≤ T →
      (∀ p ∈ S, 1 / 2 ≤ p.2.re ∧ p.2.re ≤ 1 ∧ Real.log ((M : ℝ) * T) * (1 - p.2.re) ≤ v ∧ |p.2.im| ≤ T ∧
        IsLZero p.1 p.2) →
      (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
      (S.card : ℝ) ≤ C * Real.exp (a * v) * Real.log ((M : ℝ) * T) ^ B := by
  obtain ⟨A, B, C, h⟩ := h
  refine ⟨max A 1, max B 0, max C 1, le_max_right _ _, le_max_right _ _, le_max_right _ _, ?_⟩
  intro M _ T v S hM hT hS hsp
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hMT : (6 : ℝ) ≤ (M : ℝ) * T := by nlinarith
  set ℓ : ℝ := Real.log ((M : ℝ) * T) with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hℓ0 : 0 < ℓ := by linarith
  rcases S.eq_empty_or_nonempty with rfl | ⟨p0, hp0⟩
  · simp only [card_empty, Nat.cast_zero]
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  have hv : 0 ≤ v := by
    obtain ⟨_, h2, h3, _⟩ := hS p0 hp0
    have : 0 ≤ ℓ * (1 - p0.2.re) := mul_nonneg hℓ0.le (by linarith)
    linarith
  set σ : ℝ := max (1 / 2) (1 - v / ℓ) with hσ
  have hσ1 : σ ≤ 1 := by
    apply max_le (by norm_num)
    have : 0 ≤ v / ℓ := div_nonneg hv hℓ0.le
    linarith
  have hσ2 : 1 - σ ≤ v / ℓ := by
    have := le_max_right (1 / 2 : ℝ) (1 - v / ℓ)
    linarith
  have key := h M T σ S hM hT (le_max_left _ _) (by
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hp
    refine ⟨max_le h1 ?_, h4, h5⟩
    have : 1 - p.2.re ≤ v / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
    linarith) hsp
  refine key.trans ?_
  have e1 : ((M : ℝ) * T) ^ (A * (1 - σ)) ≤ Real.exp (max A 1 * v) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have h1 : A * (1 - σ) ≤ max A 1 * (v / ℓ) := by
      have hA0 : 0 ≤ max A 1 := le_trans zero_le_one (le_max_right _ _)
      calc A * (1 - σ) ≤ max A 1 * (1 - σ) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        _ ≤ max A 1 * (v / ℓ) := mul_le_mul_of_nonneg_left hσ2 hA0
    calc ℓ * (A * (1 - σ)) ≤ ℓ * (max A 1 * (v / ℓ)) := mul_le_mul_of_nonneg_left h1 hℓ0.le
      _ = max A 1 * v := by field_simp
  have e2 : ℓ ^ B ≤ ℓ ^ (max B 0) := Real.rpow_le_rpow_of_exponent_le hℓ1 (le_max_left _ _)
  have p1 : 0 ≤ ((M : ℝ) * T) ^ (A * (1 - σ)) := Real.rpow_nonneg (by linarith) _
  have p2 : 0 ≤ ℓ ^ B := Real.rpow_nonneg hℓ0.le _
  have hC0 : 0 ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
  calc C * ((M : ℝ) * T) ^ (A * (1 - σ)) * ℓ ^ B
      ≤ max C 1 * ((M : ℝ) * T) ^ (A * (1 - σ)) * ℓ ^ B := by
        apply mul_le_mul_of_nonneg_right _ p2
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) p1
    _ ≤ max C 1 * Real.exp (max A 1 * v) * ℓ ^ (max B 0) := by
        apply mul_le_mul _ e2 p2 (by positivity)
        exact mul_le_mul_of_nonneg_left e1 hC0

theorem ell_bounds (M : ℕ) (hM : 8 ≤ M) (A₁ : ℝ) (hA : 1 ≤ A₁) :
    2 ≤ Real.log M ∧ Real.log M ≤ Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) ∧
      Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) ≤ (A₁ + 2) * Real.log M := by
  have hM' : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hp : (M : ℝ) ≤ (M : ℝ) ^ A₁ := by
    conv_lhs => rw [← Real.rpow_one (M : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hA
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Real.log 8 ≤ Real.log M := Real.log_le_log (by norm_num) hM'
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  · apply Real.log_le_log hM0
    nlinarith
  · have h1 : (M : ℝ) * ((M : ℝ) ^ A₁ + 3) ≤ (M : ℝ) ^ (A₁ + 2) := by
      rw [Real.rpow_add hM0, show ((M : ℝ) ^ (2 : ℝ)) = (M : ℝ) * M by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring]
      have h2 : (M : ℝ) ^ A₁ + 3 ≤ (M : ℝ) ^ A₁ * M := by nlinarith
      calc (M : ℝ) * ((M : ℝ) ^ A₁ + 3) ≤ (M : ℝ) * ((M : ℝ) ^ A₁ * M) :=
            mul_le_mul_of_nonneg_left h2 hM0.le
        _ = _ := by ring
    calc _ ≤ Real.log ((M : ℝ) ^ (A₁ + 2)) := Real.log_le_log (by positivity) h1
      _ = _ := Real.log_rpow hM0 _

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def DeuringHeilbronnMB : Prop :=
  ∃ (c₀ c₁ c₂ : ℝ) (B : ℕ), 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - c₁ / Real.log ((M : ℝ) * T) < β₁ → β₁ < 1 →
    IsLZero χ ρ → 1 - c₀ ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    c₂ * Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ B)) / Real.log ((M : ℝ) * T) ≤ 1 - ρ.re

def ZeroSumOfB : Prop := LogDensityM → DeuringHeilbronnMB → ZeroSum

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem smoothed_explicit_formula : ExplicitS := by
  intro κ hκ hκ'
  obtain ⟨C₁, hC₁, hch⟩ := ex_choose
  obtain ⟨C₄, hC₄, hbox⟩ := ex_box
  obtain ⟨C₂, C₃, hC₂, hC₃, hcore⟩ := exm_core
  set G := 6 * C₁ * C₂ / κ with hG
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  set AL := 3 * (G + 4 / (3 * κ)) * (2 / κ) with hAL
  set AW := (1 + 2 * C₃) + (3 * (G + 1) + 3 * (G + 1)) with hAW
  set C := max (max 4 C₄) (max AL AW) with hC
  have hC4 : 4 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCC₄ : C₄ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCL : AL ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCW : AW ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, by linarith, ?_⟩
  intro M _ χ T hM hT
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨σ₁, T', δ, hσ, hσ', hTT', hT'T, hδ0, hδ', hδlow, hgapre, hgapim⟩ := hch κ hκ hκ' M χ T hM hT
  obtain ⟨Z₀, hZ₀, hwin, _⟩ := hbox M χ (T + 1) hM (by linarith)
  have hZ : ∀ ρ : ℂ, ρ ∈ Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T') ↔
      (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T') := by
    intro ρ
    rw [Finset.mem_filter, hZ₀]
    constructor
    · rintro ⟨⟨h0, _, _⟩, h1, h2⟩
      exact ⟨h0, h1, h2⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, by linarith, by linarith⟩, h1, h2⟩
  refine ⟨Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T'), exOrd χ, explicitFormulaConstant χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨h0, h1, h2⟩ := (hZ ρ).1 hρ
    exact ⟨(isLZero_iff_exLF χ ρ).2 h0, by linarith, by linarith⟩
  · intro ρ hρ hre him
    have h0 := (isLZero_iff_exLF χ ρ).1 hρ
    refine (hZ ρ).2 ⟨h0, by linarith, ?_⟩
    have h2 := hgapim ρ h0 (by linarith)
    rcases (him.trans hTT').lt_or_eq with h | h
    · exact h
    · rw [h] at h2; simp at h2; linarith
  · intro ρ hρ
    exact exOrd_pos χ ((hZ ρ).1 hρ).1
  · intro ρ hρ hd
    have h0 := ((hZ ρ).1 hρ).1
    exact exOrd_eq_one χ h0 (exLF_deriv_ne_zero χ h0 hd)
  · intro t
    have hsub : (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1) ⊆
        Z₀.filter (fun ρ => |ρ.im - t| ≤ 1) :=
      Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    have h1 : (∑ ρ ∈ (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1),
        exOrd χ ρ) ≤ ∑ ρ ∈ Z₀.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ :=
      Finset.sum_le_sum_of_subset hsub
    have h2 : (0 : ℝ) ≤ Real.log ((M : ℝ) * (|t| + 2)) := by
      apply Real.log_nonneg
      have := abs_nonneg t
      nlinarith
    calc ((∑ ρ ∈ (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1),
        exOrd χ ρ : ℕ) : ℝ) ≤ ((∑ ρ ∈ Z₀.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ ≤ C₄ * Real.log ((M : ℝ) * (|t| + 2)) := hwin t
      _ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) := by gcongr
  · intro y hy
    have hmain := hcore κ hκ hκ' M χ T σ₁ T' δ hM hT hσ hσ' hTT' hT'T hδ0 hδ' hgapre hgapim _ hZ y hy
    refine hmain.trans ?_
    have hl1 := exm_log_ge_one (M : ℝ) T hM' hT
    have hNle := exm_N_le κ C₁ C₂ (M : ℝ) T δ hκ hC₁ hC₂ hM' hT hδ0 hδlow
    rw [← hG] at hNle
    set N := C₂ * (2 * Real.log ((M : ℝ) * T)) / δ with hN
    have hN0 : 0 ≤ N := by rw [hN]; positivity
    have ht := exm_tail_num C₃ T T' y (Real.log ((M : ℝ) * T)) hC₃ hT hTT' hy hl1
    have hh := exm_horiz_num G N T T' y (Real.log ((M : ℝ) * T)) hG0 hN0 hNle hT hTT' hy hl1
    have hl := exm_left_num κ G N (M : ℝ) T T' σ₁ y hκ hκ' hG0 hN0 hNle hM' hT hTT' hT'T hσ hσ' hy
    have hy0 : 0 < y := by linarith
    have hly := exm_log_y y hy
    have hX : 1 ≤ (M : ℝ) * T := by nlinarith
    have hfin := sum_le_mul_rpow_add AL AW C ((M : ℝ) * T) (y ^ (-(κ / 2)))
      (Real.log y * Real.log ((M : ℝ) * T) ^ 2 / T) hC4 hCL hCW hX (Real.rpow_nonneg hy0.le _)
      (by have : 0 < T := by linarith
          positivity)
    refine le_trans ?_ hfin
    have hsum := add_le_add (add_le_add ht hl) (add_le_add hh hh)
    calc _ = _ := by ring
      _ ≤ _ := hsum
      _ = _ := by rw [hAW, hAL]; ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
