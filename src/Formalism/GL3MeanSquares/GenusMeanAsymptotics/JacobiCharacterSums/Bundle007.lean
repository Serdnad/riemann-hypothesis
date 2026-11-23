module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle002
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle001
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle006
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle005
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.LFunctionEqGOfOneLt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

theorem norm_u_sum (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) (hη : 0 ≤ η) :
    ‖∑ i, ((η : ℂ) / w i) ^ j‖ = η ^ j * ‖∑ i, 1 / (w i) ^ j‖ := by
  have e : ∑ i, ((η : ℂ) / w i) ^ j = (η : ℂ) ^ j * ∑ i, 1 / (w i) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow, mul_one_div]
  rw [e, norm_mul, norm_pow]
  congr 2
  simpa using abs_of_nonneg hη

theorem core2 (CT : ℝ) (a : ℕ) (hCT : 0 < CT) (ha : 1 ≤ a)
    (hT : ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n → (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
      ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + a * n ∧ ((n : ℝ) / (CT * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i, z i ^ k‖)
    (CF CP cZ cS c₁ c₂ : ℝ) (hCF : 0 < CF) (hCP : 0 < CP) (hcZ : 0 < cZ) (hcS : 0 < cS) (hc₁ : 0 < c₁)
    (hc₁Z : c₁ ≤ cZ / 4) (hc₂ : 0 < c₂)
    (hc₂κ : c₂ ≤ kap a (Real.log (max CT 1)) / (25 * CF))
    (hc₂P : c₂ ≤ th a / (2 * Real.exp 1 * CP * rr a))
    (L ℓ lam η Mr K : ℝ) (hL : 1 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 2 * L) (hlam : 0 < lam)
    (hηZ : cZ / (2 * L) ≤ η) (hηc : η ≤ c0 a) (hηL : η * L < c₂ * K) (hMr : 0 < Mr)
    (hM : ℓ ^ 2 / Mr ≤ 32 * lam / cS) (hX : lam * L ^ 3 = c₁ * Real.exp (-K))
    (hK : K0 a (Real.log (max CT 1)) CP cZ cS c₁ < K)
    (N : ℕ) (w : Fin N → ℂ) (hw : ∀ i, η ≤ (w i).re) (hi0 : ∃ i, w i = ((η + η : ℝ) : ℂ))
    (hS : (∑ i, 1 / w i).re ≤ 2 * lam / η ^ 2 + CF * L * 25)
    (hpow : ∀ j : ℕ, 1 ≤ j → ‖∑ i, 1 / (w i) ^ j‖ ≤
        CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ)
        + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * j * lam / η ^ (j + 1) + CF * L * 25 ^ j) :
    False := by
  set D := Real.log (max CT 1) with hD_def
  have hD : 0 ≤ D := Real.log_nonneg (le_max_right _ _)
  have hL0 : 0 < L := by linarith
  have hη : 0 < η := lt_of_lt_of_le (by positivity) hηZ
  have hr := rr_gt a
  have hr0 : 0 < rr a := by linarith
  have hε0 := eps_pos a
  have hε1 := eps_le a
  have hth := th_pos a
  have hκ := kap_pos a ha D hD
  have hκth := kap_le a ha D hD
  have hE0 : 0 < E0 a D := Real.exp_pos _
  have hG : 0 < GG a CP cZ cS c₁ := by unfold GG; positivity
  have hK0 : 0 < K0 a D CP cZ cS c₁ := by unfold K0; positivity
  have hKpos : 0 < K := lt_trans hK0 hK
  have hthK : E0 a D * GG a CP cZ cS c₁ < th a * K := by
    have h1 : K0 a D CP cZ cS c₁ * th a = E0 a D * GG a CP cZ cS c₁ := by unfold K0; field_simp
    have h2 : K0 a D CP cZ cS c₁ * th a < K * th a := mul_lt_mul_of_pos_right hK hth
    linarith only [h1, h2]
  have hexpK : Real.exp (-K) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hXc : lam * L ^ 3 ≤ c₁ := by
    rw [hX]; have := mul_le_mul_of_nonneg_left hexpK hc₁.le; linarith only [this]
  have hlη1 : lam / η ≤ 2 * (lam * L) / cZ := by
    rw [div_le_div_iff₀ hη hcZ]
    have h1 : cZ ≤ 2 * L * η := by rw [div_le_iff₀ (by positivity)] at hηZ; linarith only [hηZ]
    have := mul_le_mul_of_nonneg_left h1 hlam.le
    linarith only [this]
  have hlamL : lam * L ≤ lam * L ^ 3 := by
    have h2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
    have h3 : L ≤ L ^ 3 := by
      have : L ^ 3 = L * L ^ 2 := by ring
      rw [this]; have := mul_le_mul_of_nonneg_left h2 hL0.le; linarith only [this]
    exact mul_le_mul_of_nonneg_left h3 hlam.le
  have hlη2 : lam / η ≤ 1 / 2 := by
    have h1 : 2 * (lam * L) / cZ ≤ 1 / 2 := by
      rw [div_le_iff₀ hcZ]; linarith only [hlamL, hXc, hc₁Z]
    linarith only [h1, hlη1]

  set u : Fin N → ℂ := fun i => (η : ℂ) / w i with hu_def
  have hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re := fun i => Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_disc η hη (w i) (hw i)
  have hi : ∃ i, 1 / 2 ≤ ‖u i‖ := by
    obtain ⟨i, hi⟩ := hi0
    refine ⟨i, ?_⟩
    simp only [hu_def, hi, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη,
      abs_of_pos (by linarith : (0 : ℝ) < η + η)]
    rw [le_div_iff₀ (by linarith)]; linarith
  set S : ℝ := ∑ i, (u i).re with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => le_trans (by positivity) (hu i))
  have hS_eq : S = η * (∑ i, 1 / w i).re := by
    have := Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_sum_re η w 1
    simp only [pow_one] at this
    rw [hS_def, ← this, Complex.re_sum]
  have hSle : S ≤ 2 * (lam / η) + 25 * CF * (η * L) := by
    rw [hS_eq]
    have h2 := mul_le_mul_of_nonneg_left hS hη.le
    have h3 : η * (2 * lam / η ^ 2 + CF * L * 25) = 2 * (lam / η) + 25 * CF * (η * L) := by
      field_simp
    linarith only [h2, h3]
  have h25c : 25 * CF * c₂ ≤ kap a D := by
    rw [le_div_iff₀ (by positivity)] at hc₂κ; linarith only [hc₂κ]
  have hCFηL : 25 * CF * (η * L) ≤ kap a D * K := by
    have h1 : 25 * CF * (η * L) ≤ 25 * CF * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le (by positivity)
    have h2 := mul_le_mul_of_nonneg_right h25c hKpos.le
    linarith only [h1, h2]
  have hSK : S ≤ 1 + kap a D * K := by linarith only [hSle, hCFηL, hlη2]

  set m := ⌈th a * K⌉₊ with hm_def
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
    rw [hm_def]; exact (Nat.ceil_pos.mpr (by positivity)).ne')
  have hmle : (m : ℝ) < th a * K + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmge : th a * K ≤ m := Nat.le_ceil _
  obtain ⟨j, n, hmj, hjan, hn1, hnS, hLB⟩ :=
    exists_power_sum_lower_bound CT a hCT hT (eps a) hε0 (by linarith) N u hu hi m hm1
  have hjr1 : (m : ℝ) + 1 ≤ j := by exact_mod_cast hmj
  have hjr : th a * K < j := by linarith only [hjr1, hmge]
  have hj1 : 1 ≤ j := by omega
  have hj2 : 2 ≤ j := by omega
  have hnε : (n : ℝ) * eps a ^ 2 ≤ 1 + kap a D * K := le_trans hnS hSK
  have hjan' : (j : ℝ) ≤ m + a * n := by exact_mod_cast hjan
  have hjup : (j : ℝ) ≤ 2 * th a * K + j0 a := by
    have h1 : (a : ℝ) * n ≤ a / eps a ^ 2 + a * kap a D / eps a ^ 2 * K := by
      have : (n : ℝ) ≤ (1 + kap a D * K) / eps a ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hnε
      calc (a : ℝ) * n ≤ a * ((1 + kap a D * K) / eps a ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have h2 : a * kap a D / eps a ^ 2 * K ≤ th a * K :=
      mul_le_mul_of_nonneg_right (akap_le' a ha D hD) hKpos.le
    unfold j0; linarith only [h1, h2, hjan', hmle]
  have hanD : (a : ℝ) * n * D ≤ a * D / eps a ^ 2 + j := by
    have h1 : (a : ℝ) * n * D = (a * D / eps a ^ 2) * (n * eps a ^ 2) := by field_simp
    have h2 := akapD_le a ha D hD
    have h3 : (a * D / eps a ^ 2) * (n * eps a ^ 2) ≤ (a * D / eps a ^ 2) * (1 + kap a D * K) :=
      mul_le_mul_of_nonneg_left hnε (by positivity)
    have h4 : (a * D / eps a ^ 2) * (1 + kap a D * K) = a * D / eps a ^ 2 + (a * D * kap a D / eps a ^ 2) * K := by ring
    have h5 := mul_le_mul_of_nonneg_right h2 hKpos.le
    linarith only [h1, h3, h4, h5, hjr]
  have hLB2 : 1 / (E0 a D * (rr a / 8) ^ j) ≤ ‖∑ i, u i ^ j‖ + eps a ^ (j - 2) * S :=
    le_trans (lb_part a D m n j _ (by omega) hanD (turan_lb CT hCT a n m hn1)) hLB

  have hU : ‖∑ i, u i ^ j‖ ≤ (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    have h1 : ‖∑ i, u i ^ j‖ = η ^ j * ‖∑ i, 1 / (w i) ^ j‖ := norm_u_sum η w j hη.le
    have h2 := mul_le_mul_of_nonneg_left (hpow j hj1) (pow_pos hη j).le
    have hc₂P' : 2 * Real.exp 1 * CP * c₂ * rr a ≤ th a := by
      rw [le_div_iff₀ (by positivity)] at hc₂P; linarith only [hc₂P]
    have h3 := ub_terms a CP CF cZ cS c₂ (kap a D) L ℓ lam η Mr K j hj1 hCP hCF hcZ hcS hc₂ hL hℓ0 hℓ hlam hη
      hMr hKpos hlη1 hM hηc hηL h25c hκth hc₂P' hjr
    rw [h1]; exact le_trans h2 h3
  have hF : eps a ^ (j - 2) * S ≤ rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j :=
    far_part a S j hj2 (by linarith only [hSK, hjr, mul_le_mul_of_nonneg_right hκth hKpos.le])
  have hXj := x_part a c₁ K hc₁ j hjup
  rw [← hX] at hXj
  set cA := 8 * CP / cZ + 4 / cZ + 32 * CP / cS with hcA
  have hcA0 : 0 ≤ cA := by positivity
  have hJ0 : 0 ≤ ((j : ℝ) + 1) ^ 2 := by positivity
  have hU2 : cA * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3) ≤
      cA * ((j : ℝ) + 1) ^ 2 * (c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j) :=
    mul_le_mul_of_nonneg_left hXj (by positivity)
  have htot : 1 / (E0 a D * (rr a / 8) ^ j) ≤ GG a CP cZ cS c₁ * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    have : GG a CP cZ cS c₁ * ((j : ℝ) + 1) ^ 2 / rr a ^ j =
        cA * ((j : ℝ) + 1) ^ 2 * (c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j + rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
      unfold GG; rw [hcA]; ring
    rw [this]; linarith only [hLB2, hU, hF, hU2]
  exact final_step a (E0 a D) (GG a CP cZ cS c₁) hE0 hG j (by linarith only [hthK, hjr]) htot

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

section

open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma mco_one {Y N : ℕ} (hY : 1 ≤ Y) (hN : 1 ≤ N) : mco Y N 1 = 1 := by
  unfold mco
  have h : (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = 1) = {(1, 1)} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_Icc, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha1, -⟩, hb1, -⟩, h⟩
      constructor <;> nlinarith
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨⟨le_rfl, hY⟩, le_rfl, hN⟩, rfl⟩
  rw [h, sum_singleton]
  simp

lemma mco_filter_eq_antidiag {Y N n : ℕ} (hn : 1 ≤ n) (hnY : n ≤ Y) (hYN : Y ≤ N) :
    (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨h, by omega⟩
  · rintro ⟨h, -⟩
    have ha : a ≠ 0 := by
      rintro rfl
      omega
    have hb : b ≠ 0 := by
      rintro rfl
      omega
    have ha' : a ≤ n := Nat.le_of_dvd (by omega) (Dvd.intro b h)
    have hb' : b ≤ n := Nat.le_of_dvd (by omega) (Dvd.intro_left a h)
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, h⟩

lemma mco_filter_subset_antidiag {Y N n : ℕ} (hn : 1 ≤ n) :
    (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) ⊆ n.divisorsAntidiagonal := by
  intro x hx
  rw [mem_filter] at hx
  rw [Nat.mem_divisorsAntidiagonal]
  exact ⟨hx.2, by omega⟩

lemma mco_sum_moebius_divisors {n : ℕ} (hn : 2 ≤ n) : ∑ i ∈ n.divisors, (μ i : ℤ) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply] at h
  rw [h, one_apply_ne (by omega)]

lemma mco_eq_zero {Y N n : ℕ} (h2 : 2 ≤ n) (hnY : n ≤ Y) (hYN : Y ≤ N) : mco Y N n = 0 := by
  unfold mco
  rw [mco_filter_eq_antidiag (by omega) hnY hYN]
  have h := Nat.sum_divisorsAntidiagonal (fun a _ => ((μ a : ℤ) : ℂ)) (n := n)
  rw [h]
  exact_mod_cast mco_sum_moebius_divisors h2

lemma mco_norm_le (Y N : ℕ) {n : ℕ} (hn : 1 ≤ n) : ‖mco Y N n‖ ≤ (n.divisors.card : ℝ) := by
  unfold mco
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (sum_le_sum (g := fun _ => (1 : ℝ)) ?_) ?_
  · intro p _
    have h1 := abs_moebius_le_one (n := p.1)
    first
      | (rw [Complex.norm_intCast]; exact_mod_cast h1)
      | (rw [Complex.norm_int]; exact_mod_cast h1)
      | (rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]; exact_mod_cast h1)
  · rw [sum_const, nsmul_eq_mul, mul_one]
    have hc := card_le_card (mco_filter_subset_antidiag (Y := Y) (N := N) hn)
    have he : n.divisorsAntidiagonal.card = n.divisors.card := by
      first
        | exact Nat.card_divisorsAntidiagonal_eq_card_divisors n
        | (rw [← Nat.map_div_right_divisors, card_map])
    rw [he] at hc
    exact_mod_cast hc

theorem mollifier_identity : MollId := by
  unfold MollId
  intro q _ χ s Y N K hY hYN hK
  have hN : 1 ≤ N := le_trans hY hYN
  have hYK : Y ≤ K := by
    calc Y = Y * 1 := (mul_one Y).symm
      _ ≤ Y * N := Nat.mul_le_mul le_rfl hN
      _ ≤ K := hK
  have hmaps : ∀ p ∈ Icc 1 Y ×ˢ Icc 1 N, p.1 * p.2 ∈ Icc 1 K := by
    intro p hp
    simp only [mem_product, mem_Icc] at hp ⊢
    constructor
    · have := Nat.mul_le_mul hp.1.1 hp.2.1
      simpa using this
    · exact le_trans (Nat.mul_le_mul hp.1.2 hp.2.2) hK
  rw [sum_mul]
  simp_rw [mul_sum]
  rw [sum_comm, ← sum_product',
    ← sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2) (t := Icc 1 K) hmaps]
  calc _ = ∑ k ∈ Icc 1 K, mco Y N k * χ k * (k : ℂ) ^ (-s) := by
        apply sum_congr rfl
        intro k _
        unfold mco
        rw [sum_mul, sum_mul]
        apply sum_congr rfl
        intro p hp
        rw [mem_filter] at hp
        obtain ⟨-, hpk⟩ := hp
        subst hpk
        simp only [Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
        ring
    _ = 1 + ∑ n ∈ Ioc Y K, mco Y N n * χ n * (n : ℂ) ^ (-s) := by
        have hsplit : Icc 1 K = Icc 1 Y ∪ Ioc Y K := by
          ext k
          simp only [mem_union, mem_Icc, mem_Ioc]
          omega
        have hdisj : Disjoint (Icc 1 Y) (Ioc Y K) := by
          rw [disjoint_left]
          intro k hk hk'
          rw [mem_Icc] at hk
          rw [mem_Ioc] at hk'
          omega
        rw [hsplit, sum_union hdisj]
        congr 1
        rw [sum_eq_single 1]
        · rw [mco_one hY hN]
          simp
        · intro k hk hk1
          rw [mem_Icc] at hk
          rw [mco_eq_zero (by omega) hk.2 hYN]
          simp
        · intro h
          exact absurd (mem_Icc.mpr ⟨le_rfl, hY⟩) h

theorem coefficient_square_bound : CoeffSqOf := by
  unfold CoeffSqOf
  intro hD
  unfold CoeffSq
  unfold FX.DivisorBound at hD
  have hs0 : s0 = 399 / 400 := by
    unfold s0
    norm_num
  obtain ⟨C, hC⟩ := hD (1 / 400) (by norm_num)
  have hC1 : 1 ≤ C := by
    have h := hC 1 le_rfl
    simpa using h
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro Y N U hU
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hterm : ∀ n ∈ Ioc U (2 * U),
      (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hUn : (U : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have h1 : ‖mco Y N n‖ ≤ C * (n : ℝ) ^ (1 / 400 : ℝ) := le_trans (mco_norm_le Y N hn1) (hC n hn1)
    have h2 : (n : ℝ) ^ (1 / 400 : ℝ) * (n : ℝ) ^ (-s0) = (n : ℝ) ^ (-(199 / 200 : ℝ)) := by
      rw [← Real.rpow_add hnpos, hs0]
      norm_num
    have h3 : (n : ℝ) ^ (-(199 / 200 : ℝ)) ≤ (U : ℝ) ^ (-(199 / 200 : ℝ)) := by
      first
        | exact Real.rpow_le_rpow_of_nonpos hUpos hUn (by norm_num)
        | exact Real.rpow_le_rpow_of_exponent_nonpos hUpos hUn (by norm_num)
        | (rw [Real.rpow_neg hnpos.le, Real.rpow_neg hUpos.le]
           exact inv_anti₀ (Real.rpow_pos_of_pos hUpos _) (Real.rpow_le_rpow hUpos.le hUn (by norm_num)))
        | (rw [Real.rpow_neg hnpos.le, Real.rpow_neg hUpos.le]
           exact inv_le_inv_of_le (Real.rpow_pos_of_pos hUpos _) (Real.rpow_le_rpow hUpos.le hUn (by norm_num)))
    have h4 : 0 ≤ ‖mco Y N n‖ * (n : ℝ) ^ (-s0) := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hnpos.le _)
    have h5 : ‖mco Y N n‖ * (n : ℝ) ^ (-s0) ≤ C * (U : ℝ) ^ (-(199 / 200 : ℝ)) := by
      calc ‖mco Y N n‖ * (n : ℝ) ^ (-s0) ≤ C * (n : ℝ) ^ (1 / 400 : ℝ) * (n : ℝ) ^ (-s0) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hnpos.le _)
        _ = C * (n : ℝ) ^ (-(199 / 200 : ℝ)) := by rw [mul_assoc, h2]
        _ ≤ C * (U : ℝ) ^ (-(199 / 200 : ℝ)) := mul_le_mul_of_nonneg_left h3 (by linarith)
    first
      | exact pow_le_pow_left h4 h5 2
      | exact pow_le_pow_left₀ h4 h5 2
      | nlinarith
  have e1 : ((U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 = (U : ℝ) ^ (-(199 / 100 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hUpos.le]
    norm_num
  have e2 : (U : ℝ) * (U : ℝ) ^ (-(199 / 100 : ℝ)) = (U : ℝ) ^ (-(99 / 100 : ℝ)) := by
    rw [show (U : ℝ) ^ (-(99 / 100 : ℝ)) = (U : ℝ) ^ ((1 : ℝ) + -(199 / 100 : ℝ)) by norm_num,
      Real.rpow_add hUpos, Real.rpow_one]
  calc ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2
      ≤ ∑ n ∈ Ioc U (2 * U), (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := sum_le_sum hterm
    _ = (U : ℝ) * (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := by
        rw [sum_const, Nat.card_Ioc, show 2 * U - U = U by omega, nsmul_eq_mul]
    _ = C ^ 2 * ((U : ℝ) * ((U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2) := by ring
    _ = C ^ 2 * (U : ℝ) ^ (-(99 / 100 : ℝ)) := by rw [e1, e2]
    _ ≤ C ^ 2 * (U : ℝ) ^ (-(197 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)) (by positivity)

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma norm_cpow_neg_le_one {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : 0 ≤ w.re) : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := by
  rw [norm_natCast_cpow_of_pos (by omega), neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

lemma norm_cpow_step_le {i U : ℕ} (hU : 1 ≤ U) (hi : U ≤ i) {w : ℂ} (hw : 0 < w.re) :
    ‖(((i + 1 : ℕ) : ℂ) ^ (-w) - (i : ℂ) ^ (-w))‖ ≤ ‖w‖ / U := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have h := Formalism.FX.LFunctionPartialSum.norm_cpow_sub_le' hi0 hw
  have e1 : (((i : ℝ) : ℂ)) = (i : ℂ) := by push_cast; rfl
  have e2 : ((((i : ℝ) + 1 : ℝ)) : ℂ) = ((i + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [e1, e2, norm_sub_rev] at h
  refine h.trans ?_
  have hUi : (U : ℝ) ≤ i := by exact_mod_cast hi
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have h1 : (i : ℝ) ^ (-w.re - 1) ≤ (i : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ i)) (by linarith)
  have h2 : (i : ℝ) ^ (-1 : ℝ) ≤ 1 / U := by
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ hU0 hUi
  calc ‖w‖ * (i : ℝ) ^ (-w.re - 1) ≤ ‖w‖ * (1 / U) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
    _ = ‖w‖ / U := by ring

theorem pair_twist_bound : PairTwistOf := by
  intro hPS p p' hp hp' hne w hw U hU
  set m : ℝ := (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ) with hm
  set g : ℕ → ℂ := fun n => cv p n * (starRingEnd ℂ) (cv p' n) with hg
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-w) with hf
  have hGs : ∀ k, ‖∑ i ∈ range k, g i‖ ≤ m := fun k => hPS p p' hp hp' hne k
  have hm0 : 0 ≤ m := by positivity
  have hrw : ∑ n ∈ Ioc U (2 * U), cv p n * (starRingEnd ℂ) (cv p' n) * (n : ℂ) ^ (-w) =
      ∑ n ∈ Ioc U (2 * U), f n • g n := by
    refine sum_congr rfl (fun n _ => ?_); simp only [hf, hg, smul_eq_mul]; ring
  rw [hrw, Finset.sum_Ioc_by_parts f g (by omega : U < 2 * U)]
  have hb1 : ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (2 * U)‖ * ‖∑ i ∈ range (2 * U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (norm_cpow_neg_le_one (by omega) hw.le) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb2 : ‖f (U + 1) • ∑ i ∈ range (U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (U + 1)‖ * ‖∑ i ∈ range (U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (norm_cpow_neg_le_one (by omega) hw.le) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb3 : ‖∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ m * ‖w‖ := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Ioc U (2 * U - 1),
        ‖(f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ ‖w‖ / U * m := by
      intro i hi
      rw [smul_eq_mul, norm_mul]
      have hi' : U ≤ i := by have := (mem_Ioc.1 hi).1; omega
      exact mul_le_mul (norm_cpow_step_le hU hi' hw) (hGs _) (norm_nonneg _) (by positivity)
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
    have hcnt : ((2 * U - 1 - U : ℕ) : ℝ) ≤ U := by exact_mod_cast (by omega : 2 * U - 1 - U ≤ U)
    calc ((2 * U - 1 - U : ℕ) : ℝ) * (‖w‖ / U * m) ≤ U * (‖w‖ / U * m) :=
          mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = m * ‖w‖ := by field_simp
  calc ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i - f (U + 1) • ∑ i ∈ range (U + 1), g i -
        ∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖
      ≤ m + m + m * ‖w‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add hb1 hb2)) hb3
    _ ≤ 2 * m * (1 + ‖w‖) := by nlinarith [norm_nonneg w]

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end
