module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle023
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle004
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle025
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle024
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTZSum
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
import Mathlib.NumberTheory.LSeries.Nonvanishing
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

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def DHTuran2 : Prop :=
  ∃ (C : ℝ) (A : ℕ), 0 < C ∧ 1 ≤ A ∧ ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n →
    (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
    ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + A * n ∧ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (A * n) ≤ ‖∑ i, z i ^ k‖

def DHDom : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (γ σ : ℝ) (k : ℕ), χ₁ ^ 2 = 1 → 1 < σ →
    ‖iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I) + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ ≤
      ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re

def DHIneqF : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T η : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    19 / 20 ≤ β₁ → β₁ < 1 → IsLZero χ ρ → 22 / 25 ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    0 < η → η ≤ 2 / 25 →
    ∃ (N : ℕ) (w : Fin N → ℂ),
      (∀ i, η ≤ (w i).re) ∧
      (∃ i, w i = ((η + (1 - ρ.re) : ℝ) : ℂ)) ∧
      (∑ i, 1 / w i).re ≤ 2 * (1 - β₁) / η ^ 2 + C * Real.log ((M : ℝ) * T) * 25 ∧
      ∀ j : ℕ, 1 ≤ j →
        ‖∑ i, 1 / (w i) ^ j‖ ≤
          ((-1 : ℂ) ^ (j - 1) * (iteratedDeriv (j - 1) (negLD (1 : DirichletCharacter ℂ M)) ((1 + η : ℝ) : ℂ)
              + iteratedDeriv (j - 1) (negLD χ₁) ((1 + η : ℝ) : ℂ))).re / ((j - 1).factorial : ℝ)
          + 2 * j * (1 - β₁) / η ^ (j + 1) + C * Real.log ((M : ℝ) * T) * 25 ^ j

def DHHyper : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (y x : ℝ), 3 ≤ M → χ₁ ^ 2 = 1 → χ₁ ≠ 1 →
    1 ≤ y → y ≤ x →
    ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
      ‖DirichletCharacter.LFunction χ₁ 1‖ * Real.log (x / y) + C * M * (Real.log y + 1) / Real.sqrt y

def DHPrime : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ σ : ℝ) (k : ℕ),
    3 ≤ M → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - 1 / Real.log (3 * M) ≤ β₁ → β₁ < 1 → 1 < σ → σ ≤ 2 →
    ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re / (k.factorial : ℝ) ≤
      C * (1 - β₁) * Real.log (3 * M) ^ 2 * (k + 2) ^ 2 / (σ - 1) ^ (k + 2)
        + (C * Real.log (3 * M)) ^ (k + 1) / (k.factorial : ℝ)
        + C * (k + 2) * Real.log (3 * M) ^ 2 / (M * (σ - 1) ^ (k + 1))

def DHIneqFOf : Prop := DHPos → DHLocal → DHDom → DHIneqF

def DHPrimeOf : Prop := DHHyper → DHPrime

def DHFinish2Of : Prop := DHTuran2 → DHIneqF → DHPrime → DeuringHeilbronnMB

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem pow_absorb (N : ℕ) (c l large₂ : ℝ) (hc : 0 < c) (hl : 2 ≤ l)
    (hL : 2 * N / c * l * Real.log (l + 2) ≤ large₂) :
    l ^ N * Real.exp (-(c / 2 * large₂ / l)) ≤ 1 := by
  have hl0 : 0 < l := by linarith
  have hpow : Real.exp (N * Real.log l) = l ^ N := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hl0 N)]
  have key : (N : ℝ) * Real.log l ≤ c / 2 * large₂ / l := by
    rw [le_div_iff₀ hl0]
    have hlog : Real.log l ≤ Real.log (l + 2) := Real.log_le_log hl0 (by linarith)
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc (N : ℝ) * Real.log l * l ≤ N * Real.log (l + 2) * l := by gcongr
      _ = c / 2 * (2 * N / c * l * Real.log (l + 2)) := by field_simp
      _ ≤ c / 2 * large₂ := by gcongr
  calc l ^ N * Real.exp (-(c / 2 * large₂ / l))
      = Real.exp (N * Real.log l + -(c / 2 * large₂ / l)) := by rw [Real.exp_add, hpow]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem zero_sum_bound_lossy : ZeroSumOfB := by
  intro hLD hDH
  obtain ⟨a, B, C, ha, hB, hC, hdens⟩ := density_norm hLD
  obtain ⟨c₀, c₁, c₂, N, hc₀, hc₁, hc₂, hdh⟩ := hDH
  refine ⟨min c₀ (1 / 20), lt_min hc₀ (by norm_num), min_le_right _ _, ?_⟩
  intro C₁ A₁ hA₁
  have hk : 0 < A₁ + 2 := by linarith
  have hcZ := cZ_pos
  have hcZ' := cZ_le
  set η0 : ℝ := min (cZ / 2) (c₁ / (A₁ + 2)) with hη0
  have hη0pos : 0 < η0 := lt_min (by linarith) (by positivity)
  have hη0a : η0 ≤ cZ / 2 := min_le_left _ _
  have hη0b : η0 ≤ c₁ / (A₁ + 2) := min_le_right _ _
  have hη0c : η0 ≤ c₁ := hη0b.trans (div_le_self hc₁.le (by linarith))
  have hη01 : η0 ≤ 1 := by linarith
  set A' : ℝ := 4 * |C₁| * C * Real.exp (a + a * cZ / 2) * (A₁ + 2) ^ (B + 1) with hA'
  have hA'0 : 0 ≤ A' := by
    have h1 : 0 ≤ (A₁ + 2) ^ (B + 1) := Real.rpow_nonneg hk.le _
    have h2 : 0 ≤ C := by linarith
    positivity
  set c : ℝ := cZ / (4 * (A₁ + 2)) with hc
  have hc0 : 0 < c := by positivity
  set K0 : ℝ := (A₁ + 2) * (a + 1 + 2 / c₂) + (B + 1) / c with hK0
  have hK00 : 0 ≤ K0 := by
    have h1 : 0 ≤ a + 1 + 2 / c₂ := by positivity
    have h2 : 0 ≤ (B + 1) / c := by positivity
    positivity
  refine ⟨c / 2, A' * (A₁ + 2) ^ N / η0, K0 + 2 * N / c, by positivity, ?_⟩
  intro M _ Z m h8 hZ _ hms hwin y hy hL
  have hM8 : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM8' : (8 : ℝ) ≤ M := by exact_mod_cast hM8
  have hM0 : (0 : ℝ) < M := by linarith
  have hpw : 0 < (M : ℝ) ^ A₁ := Real.rpow_pos_of_pos hM0 _
  obtain ⟨hl2, hlℓ, hℓk⟩ := ell_bounds M hM8 A₁ hA₁
  set ℓ : ℝ := Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) with hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓN : 1 ≤ ℓ ^ N := one_le_pow₀ hℓ1
  have hll : 0 ≤ Real.log M * Real.log (Real.log M + 2) :=
    mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  have hL1 : K0 * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    have : 0 ≤ 2 * N / c * (Real.log M * Real.log (Real.log M + 2)) :=
      mul_nonneg (by positivity) hll
    nlinarith
  have hL2 : 2 * N / c * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    have : 0 ≤ K0 * (Real.log M * Real.log (Real.log M + 2)) := mul_nonneg hK00 hll
    nlinarith
  have habs := pow_absorb N c (Real.log M) (Real.log y) hc0 hl2 hL2
  suffices h : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) by
    obtain ⟨θ, h0, h1, hη, hθ⟩ := h
    have key := zeroSum_core a B C ha hB hC hdens (min c₀ (1 / 20)) c₂ C₁ A₁ (min_le_right _ _) hc₂ hA₁
      M Z m h8 hZ hms hwin y hy hL1 θ h0 h1 hθ
    refine key.trans ?_
    have hηpos : 0 < etaOf M := etaOf_pos M (by omega)
    set E : ℝ := Real.exp (-(c / 2 * Real.log y / Real.log M)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hEE : Real.exp (-(c * Real.log y / Real.log M)) = E * E := by
      rw [hE, ← Real.exp_add]
      congr 1
      ring
    rw [hEE]
    have hpow : ℓ ^ N ≤ (A₁ + 2) ^ N * Real.log M ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hℓ0.le hℓk N
    have hθle : θ ≤ etaOf M * ((A₁ + 2) ^ N * Real.log M ^ N) / η0 := by
      rw [le_div_iff₀ hη0pos]
      calc θ * η0 = η0 * θ := by ring
        _ ≤ etaOf M * ℓ ^ N := hη
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hηpos.le
    have hkN : 0 ≤ (A₁ + 2) ^ N := by positivity
    calc A' * θ * (E * E)
        ≤ A' * (etaOf M * ((A₁ + 2) ^ N * Real.log M ^ N) / η0) * (E * E) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hθle hA'0
      _ = (A' * (A₁ + 2) ^ N / η0 * etaOf M * E) * (Real.log M ^ N * E) := by ring
      _ ≤ (A' * (A₁ + 2) ^ N / η0 * etaOf M * E) * 1 := by
          apply mul_le_mul_of_nonneg_left habs
          positivity
      _ = _ := by ring
  have hone' : η0 ≤ etaOf M * ℓ ^ N → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) := by
    intro hη
    refine ⟨1, one_pos, le_refl _, by linarith, ?_⟩
    intro χ ρ _ hr
    unfold InRegion at hr
    replace hr := not_le.mp hr
    have habs := abs_nonneg ρ.im
    have h1 : (1 : ℝ) ≤ (M : ℝ) * (|ρ.im| + 2) := by nlinarith
    have h2 : 0 ≤ cZ / Real.log ((M : ℝ) * (|ρ.im| + 2)) := div_nonneg hcZ.le (Real.log_nonneg h1)
    have h3 : 0 ≤ ℓ * (1 - ρ.re) := mul_nonneg hℓ0.le (by linarith)
    simpa using h3
  have hone : η0 ≤ etaOf M → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) := by
    intro hη
    apply hone'
    calc η0 ≤ etaOf M := hη
      _ = etaOf M * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hℓN (hη0pos.le.trans hη)
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · apply hone
    rw [etaOf_none M he]
    exact hη01
  · obtain ⟨hsq, hne, hL0, _, hβ1⟩ := eOf_exc M (χ₁, β₁) he
    simp only at hsq hne hL0 hβ1
    have hβ : 0 < 1 - β₁ := by linarith
    have hlow : (1 - β₁) * ℓ / (A₁ + 2) ≤ (1 - β₁) * Real.log M := by
      rw [div_le_iff₀ hk]
      calc (1 - β₁) * ℓ ≤ (1 - β₁) * ((A₁ + 2) * Real.log M) := mul_le_mul_of_nonneg_left hℓk hβ.le
        _ = _ := by ring
    have hup : (1 - β₁) * ℓ ^ N ≤ (1 - β₁) * Real.log M * ℓ ^ N := by
      have h0 : 0 ≤ (1 - β₁) * ℓ ^ N := by positivity
      calc (1 - β₁) * ℓ ^ N = (1 - β₁) * ℓ ^ N * 1 := (mul_one _).symm
        _ ≤ (1 - β₁) * ℓ ^ N * Real.log M := mul_le_mul_of_nonneg_left (by linarith) h0
        _ = _ := by ring
    by_cases hr : InRegion cZ M (β₁ : ℂ)
    · by_cases hcc : c₁ ≤ (1 - β₁) * ℓ
      · apply hone
        rw [etaOf_some M χ₁ β₁ he]
        apply le_min hη01
        have : c₁ / (A₁ + 2) ≤ (1 - β₁) * ℓ / (A₁ + 2) := div_le_div_of_nonneg_right hcc hk.le
        linarith
      · replace hcc := not_le.mp hcc
        by_cases hu : c₁ ≤ (1 - β₁) * ℓ ^ N
        · apply hone'
          rw [etaOf_some M χ₁ β₁ he, min_mul_of_nonneg (1 : ℝ) ((1 - β₁) * Real.log M) (by positivity : (0 : ℝ) ≤ ℓ ^ N)]
          apply le_min
          · linarith
          · linarith
        · replace hu := not_le.mp hu
          have hθ0 : 0 < (1 - β₁) * ℓ ^ N / c₁ := by positivity
          have hθ1 : (1 - β₁) * ℓ ^ N / c₁ ≤ 1 := by
            rw [div_le_one hc₁]; exact hu.le
          refine ⟨(1 - β₁) * ℓ ^ N / c₁, hθ0, hθ1, ?_, ?_⟩
          · rw [etaOf_some M χ₁ β₁ he, min_mul_of_nonneg (1 : ℝ) ((1 - β₁) * Real.log M) (by positivity : (0 : ℝ) ≤ ℓ ^ N)]
            apply le_min
            · calc η0 * ((1 - β₁) * ℓ ^ N / c₁) ≤ 1 * 1 := mul_le_mul hη01 hθ1 hθ0.le zero_le_one
                _ ≤ 1 * ℓ ^ N := by linarith
            · calc η0 * ((1 - β₁) * ℓ ^ N / c₁) ≤ c₁ * ((1 - β₁) * ℓ ^ N / c₁) :=
                    mul_le_mul_of_nonneg_right hη0c hθ0.le
                _ = (1 - β₁) * ℓ ^ N := by field_simp
                _ ≤ _ := hup
          · intro χ ρ hρ hnr
            obtain ⟨hz, hre, him⟩ := hZ χ ρ hρ
            have hd := hdh M χ₁ χ β₁ ((M : ℝ) ^ A₁ + 3) ρ (by omega) (by linarith) hsq hne hL0
              (by
                have : 1 - β₁ < c₁ / ℓ := by rw [lt_div_iff₀ hℓ0]; exact hcc
                linarith)
              hβ1 hz
              (by
                have := min_le_left c₀ (1 / 20 : ℝ)
                linarith)
              (by linarith)
              (by
                intro heq
                have h2 : ρ = (β₁ : ℂ) := (Prod.mk.inj heq).2
                rw [h2] at hnr
                exact hnr hr)
            rw [one_div_div]
            rw [div_le_iff₀ hℓ0] at hd
            linarith
    · apply hone
      have := etaOf_far M (by omega) χ₁ β₁ he hr
      linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet



theorem psi_relative_far_range : PsiRelBOf := by
  intro hE hS hZS cA hcA
  obtain ⟨κ, hκ, hκ', hZ⟩ := hZS
  obtain ⟨C, hC, hEx⟩ := hE κ hκ hκ'
  obtain ⟨cz, Az, Cz, hcz, hZ⟩ := hZ C 12 (by norm_num)
  obtain ⟨C₀, B, hC₀, hB, hnum⟩ := num_main cA κ C hcA hκ hC
  obtain ⟨c₁, hc₁, heta⟩ := etaOf_lower 1 one_pos
  refine ⟨min cz (cA ^ 2), 22 * |Az| + B / c₁, max Cz C₀, lt_min hcz (by positivity), ?_⟩
  intro M _ h8 y hy hr1 hr2
  have hM8 : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM8r : (8 : ℝ) ≤ M := by exact_mod_cast hM8
  have hM3 : 3 ≤ M := by omega
  have hM0 : (0 : ℝ) < M := by linarith
  have hy0 : 0 < y := by linarith
  have hT8 : (8 : ℝ) ≤ (M : ℝ) ^ (12 : ℝ) := by
    calc (8 : ℝ) ≤ (M : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hM8r
      _ ≤ (M : ℝ) ^ (12 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hδ0 : 0 < ((M : ℝ) ^ 5)⁻¹ := by positivity
  have hδ : ((M : ℝ) ^ 5)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    apply inv_anti₀ (by norm_num)
    calc (2 : ℝ) ≤ (M : ℝ) ^ 1 := by rw [pow_one]; linarith
      _ ≤ (M : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  choose Z m K h1 h2 h3 h4 h5 h6 using fun χ => hEx M χ ((M : ℝ) ^ (12 : ℝ)) hM3 (by linarith)
  have hl : 1 ≤ Real.log M := one_le_log_of_three_le (by linarith)
  have hll : 1 ≤ Real.log (Real.log M + 2) := one_le_log_of_three_le (by linarith)
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hrz : Cz * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    refine le_trans ?_ hr1
    have : Cz ≤ max Cz C₀ := le_max_left _ _
    gcongr
  have hrn : C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    refine le_trans ?_ hr1
    have : C₀ ≤ max Cz C₀ := le_max_right _ _
    gcongr
  have hZS := hZ M Z m h8 h1 h3 h4 h5 y hy hrz
  have hN := hnum M y hM8r hy hrn hr2
  generalize hTdef : (M : ℝ) ^ (12 : ℝ) = T at *
  generalize hδdef : ((M : ℝ) ^ 5)⁻¹ = δ at *
  generalize htdef : y ^ (-(κ / 2)) = t at *
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = C * (((M : ℝ) * T) ^ C * t
      + Real.log (2 * y) * Real.log ((M : ℝ) * T) ^ 2 / T) := ⟨_, rfl⟩
  rw [← hEdef] at hN
  have hT0 : 0 < T := by linarith
  have ht0 : 0 ≤ t := by rw [← htdef]; positivity
  have hlg : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hre : ∀ χ, ∀ ρ ∈ Z χ, 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
    intro χ ρ hρ
    obtain ⟨hz, hlo, -⟩ := h1 χ ρ hρ
    refine ⟨by linarith, ?_⟩
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hz.1 (not_lt.1 hcon) hz.2
  have hEu : ∀ u : ℝ, y ≤ u → u ≤ 2 * y →
      C * (((M : ℝ) * T) ^ C * u ^ (-(κ / 2)) + Real.log u * Real.log ((M : ℝ) * T) ^ 2 / T) ≤ E := by
    intro u hu1 hu2
    rw [hEdef]
    have a1 : u ^ (-(κ / 2)) ≤ t := by
      rw [← htdef]; exact Real.rpow_le_rpow_of_nonpos hy0 hu1 (by linarith)
    have a2 : Real.log u ≤ Real.log (2 * y) := Real.log_le_log (by linarith) hu2
    gcongr
  have hsharp : ∀ χ : DirichletCharacter ℂ M,
      ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z χ, (m χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤
      4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) := by
    intro χ
    refine hS M χ (Z χ) (m χ) (K χ) E y δ (hre χ) hy hδ0 hδ ?_
    intro u hu
    have hu1 : y ≤ u := by
      rcases hu with rfl | rfl
      · exact le_rfl
      · nlinarith
    have hu2 : u ≤ 2 * y := by
      rcases hu with rfl | rfl
      · linarith
      · nlinarith
    exact (h6 χ u (by linarith)).trans (hEu u hu1 hu2)
  obtain ⟨W, hW⟩ : ∃ W : DirichletCharacter ℂ M → ℝ, W = fun χ =>
      ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) := ⟨_, rfl⟩
  have hW0 : ∀ χ, 0 ≤ W χ := by
    intro χ
    rw [hW]
    apply Finset.sum_nonneg
    intro ρ hρ
    have : ((excW (eOf M) χ ρ : ℕ) : ℝ) ≤ (m χ ρ : ℝ) := by
      exact_mod_cast (excW_le_one (eOf M) χ ρ).trans (h3 χ ρ hρ)
    have h0 : (0 : ℝ) ≤ (m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ) := by linarith
    positivity
  have hmW : ∀ χ, ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ W χ + excI (eOf M) χ := by
    intro χ
    have := sum_excW_le (eOf M) χ (Z χ) y (by linarith) (fun ρ hρ => (hre χ ρ hρ).2)
    have e : ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        = W χ + ∑ ρ ∈ Z χ, (excW (eOf M) χ ρ : ℝ) * y ^ (ρ.re - 1) := by
      rw [hW, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    linarith
  have hper : ∀ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * W χ
        + excI (eOf M) χ * (20 * δ * y + 2 * y * t) := by
    intro χ
    have a := one_char hM3 (eOf M) (fun p hp => eOf_exc M p hp) χ (Z χ) (m χ) y κ T _ (by linarith)
      hT0.le (h2 χ) (fun ρ hρ => (hre χ ρ hρ).1) (h3 χ) (hsharp χ)
    rw [htdef] at a
    have a' : ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
        4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) + 2 * y * W χ + excI (eOf M) χ * (2 * y * t) := by
      rw [hW]; exact a
    have b : 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        ≤ 20 * δ * y * (W χ + excI (eOf M) χ) := mul_le_mul_of_nonneg_left (hmW χ) (by positivity)
    have c : 20 * δ * y * W χ ≤ 20 * y * W χ := by
      have : 0 ≤ y * W χ := mul_nonneg hy0.le (hW0 χ)
      nlinarith
    linarith
  have hsum : ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (M : ℝ) * (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * ∑ χ, W χ
        + (20 * δ * y + 2 * y * t) := by
    refine (Finset.sum_le_sum (fun χ _ => hper χ)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    have q0 : 0 ≤ 4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y) := by positivity
    have q1 : 0 ≤ 20 * δ * y + 2 * y * t := by positivity
    have r1 := mul_le_mul_of_nonneg_right (card_char_le M) q0
    have r2 := mul_le_mul_of_nonneg_right (sum_excI_le (eOf M)) q1
    linarith
  have hη0 : 0 < etaOf M := etaOf_pos M (by omega)
  have hex := inv_le_exp hcA (lt_min hcz (by positivity : 0 < cA ^ 2)) (min_le_right _ _) hM8r hy hr2
  have hηM : (M : ℝ)⁻¹ ≤ etaOf M / c₁ := by
    have := heta M hM3
    rw [Real.rpow_neg_one] at this
    rw [le_div_iff₀ hc₁]; linarith
  have hMi : 0 < (M : ℝ)⁻¹ := by positivity
  have hWs : ∑ χ, W χ ≤ |Az| * etaOf M * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
    rw [hW]
    refine hZS.trans ?_
    have e1 : Real.exp (-(cz * Real.log y / Real.log M))
        ≤ Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      have : min cz (cA ^ 2) ≤ cz := min_le_left _ _
      gcongr
    have e2 : Az ≤ |Az| := le_abs_self _
    gcongr
  have hfin : B * y * ((M : ℝ)⁻¹ * (M : ℝ)⁻¹)
      ≤ B * y * (etaOf M / c₁ * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M))) := by
    gcongr
  generalize Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) = ex at *
  have f1 : 22 * y * ∑ χ, W χ ≤ 22 * y * (|Az| * etaOf M * ex) :=
    mul_le_mul_of_nonneg_left hWs (by positivity)
  have f2 : (22 * |Az| + B / c₁) * y * etaOf M * ex
      = 22 * y * (|Az| * etaOf M * ex) + B * y * (etaOf M / c₁ * ex) := by ring
  rw [f2]
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
