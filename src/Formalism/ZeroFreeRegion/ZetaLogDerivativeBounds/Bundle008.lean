module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.AbsZetaPrimeSumErrorLeOfLarge
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle002
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle007
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Complex

noncomputable section

namespace Formalism.ZF

private theorem abs_zetaPrimeSumError_le_of_sqrt_log_lt (c : ℝ) (hc : 0 < c) (y : ℝ) (hy : 2 ≤ y)
    (hs : Real.sqrt (Real.log y) < 8 / c) :
    |Formalism.Gz y| ≤
      ((Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2) * Real.exp 1) * y *
        Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hsq : 0 ≤ Real.sqrt (Real.log y) := Real.sqrt_nonneg _
  have hlogL : Real.log y ≤ (8 / c) ^ 2 := by
    calc Real.log y = Real.sqrt (Real.log y) ^ 2 := (Real.sq_sqrt hlog).symm
      _ ≤ (8 / c) ^ 2 := pow_le_pow_left₀ hsq hs.le 2
  have hyL : y ≤ Real.exp ((8 / c) ^ 2) := by
    calc y = Real.exp (Real.log y) := (Real.exp_log hy0).symm
      _ ≤ Real.exp ((8 / c) ^ 2) := Real.exp_le_exp.mpr hlogL
  have hinner : y * Real.log y + Real.log y + 2 ≤
      Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2 := by
    have := mul_le_mul hyL hlogL hlog (Real.exp_pos _).le
    linarith
  have hcs : (c / 8) * Real.sqrt (Real.log y) ≤ 1 := by
    calc (c / 8) * Real.sqrt (Real.log y) ≤ (c / 8) * (8 / c) :=
          mul_le_mul_of_nonneg_left hs.le (by positivity)
      _ = 1 := by field_simp
  have hexp : Real.exp (-1) ≤ Real.exp (-(c / 8) * Real.sqrt (Real.log y)) :=
    Real.exp_le_exp.mpr (by linarith)
  set M : ℝ := Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hMe : M = M * Real.exp 1 * Real.exp (-1) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  calc |Formalism.Gz y| ≤ y * (y * Real.log y + Real.log y + 2) :=
        abs_zetaPrimeSumError_le_of_one_le y (by linarith)
    _ ≤ y * M := mul_le_mul_of_nonneg_left hinner hy0.le
    _ = y * (M * Real.exp 1 * Real.exp (-1)) := by rw [← hMe]
    _ ≤ y * (M * Real.exp 1 * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by
        apply mul_le_mul_of_nonneg_left _ hy0.le
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = M * Real.exp 1 * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring

theorem zetaPrimeSumErrorBoundOfBounds : GzPNTOf := by
  intro hZF hLD hRH hP hRS
  obtain ⟨c₀, hc₀, hZ⟩ := hZF
  obtain ⟨c₁, C₁, hc₁, hD⟩ := hLD
  obtain ⟨C₂, hC₂, hR⟩ := hRH
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = max C₁ 0 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hDdef ▸ le_max_right _ _
  have hD' : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ D * Real.log (|s.im| + 2) ^ 2 := by
    intro s hs hre
    exact (hD s hs hre).trans
      (mul_le_mul_of_nonneg_right (hDdef ▸ le_max_left _ _) (sq_nonneg _))
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (min c₀ c₁) (1 / 2) := ⟨_, rfl⟩
  have hc : 0 < c := hcdef ▸ lt_min (lt_min hc₀ hc₁) (by norm_num)
  have hc2 : c ≤ 1 / 2 := hcdef ▸ min_le_right _ _
  have hcc₀ : c ≤ c₀ := hcdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hcc₁ : c ≤ c₁ := hcdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (D + 1) +
      4 * (D + 1)) * (6 * (8 / c) ^ 3) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B =
      (Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2) * Real.exp 1 := ⟨_, rfl⟩
  refine ⟨c / 8, max A B, div_pos hc (by norm_num), ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  have hyE : 0 ≤ y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) :=
    mul_nonneg hy0 (Real.exp_pos _).le
  have h8c : 16 ≤ 8 / c := by
    rw [le_div_iff₀ hc]; linarith
  by_cases hs : 8 / c ≤ Real.sqrt (Real.log y)
  · have hs1 : 1 ≤ Real.sqrt (Real.log y) := by linarith
    have h := abs_zetaPrimeSumError_le_of_large c₀ c₁ D C₂ hD0 hC₂ hZ hD' hR hP hRS
      c hc hc2 hcc₀ hcc₁ y hy hs hs1
    rw [← hA] at h
    calc |Formalism.Gz y| ≤ A * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := h
      _ = A * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by ring
      _ ≤ max A B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hyE
      _ = max A B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring
  · rw [not_le] at hs
    have h := abs_zetaPrimeSumError_le_of_sqrt_log_lt c hc y hy hs
    rw [← hB] at h
    calc |Formalism.Gz y| ≤ B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := h
      _ = B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by ring
      _ ≤ max A B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hyE
      _ = max A B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring

end Formalism.ZF
end
end

section

open Complex

noncomputable section

namespace Formalism.ZF

theorem logDerivBoundInRegionOfBounds : LogDerivRegionOf := by
  intro hZF hLR hG hI hSH hLL
  obtain ⟨c₀, hc₀, hZ0⟩ := hZF
  obtain ⟨CR, hCR0, hCR⟩ := hLR
  obtain ⟨cS, CS, hcS, hCS⟩ := hSH (Real.exp 24)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set c := min (min (c₀ / 4) 1) (cS * Real.log 2) with hc
  have hcpos : 0 < c := lt_min (lt_min (by linarith) one_pos) (mul_pos hcS (by linarith))
  have hc1 : c ≤ c₀ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ cS * Real.log 2 := min_le_right _ _
  have hK1 : 0 ≤ 1441 + 60 / c₀ := by positivity
  have hK3 : 0 ≤ 4 * |CS| := by positivity
  refine ⟨c, (1441 + 60 / c₀) + (4 + 4 * CR) + 4 * |CS|, hcpos, ?_⟩
  intro s hs1 hreg
  have hs : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
  set σ := s.re with hσ
  set t := s.im with ht
  set L := Real.log (|t| + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hLpos : 1 / 2 < L := by linarith
  have hL0 : 0 < L := by linarith
  have hLsq : 1 / 4 ≤ L ^ 2 := by nlinarith
  by_cases hright : 1 + 1 / L < σ
  · have hinvpos : 0 < 1 / L := by positivity
    have hσ1 : 1 < σ := by linarith
    have h1 := hCR s hσ1
    have hnorm : σ - 1 ≤ ‖s - 1‖ := by
      have : (s - 1).re = σ - 1 := by simp [hσ]
      calc σ - 1 = (s - 1).re := this.symm
        _ ≤ |(s - 1).re| := le_abs_self _
        _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
    have hσL : 1 / (σ - 1) ≤ L := by
      rw [div_le_iff₀ (by linarith)]
      have h := hright
      have : 1 / L < σ - 1 := by linarith
      rw [div_lt_iff₀ hL0] at this
      linarith
    have h2 : ‖1 / (s - 1)‖ ≤ L := by
      rw [norm_div, norm_one]
      calc 1 / ‖s - 1‖ ≤ 1 / (σ - 1) := one_div_le_one_div_of_le (by linarith) hnorm
        _ ≤ L := hσL
    calc ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖
        ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
      _ ≤ (1 / (σ - 1) + CR) + L := add_le_add h1 h2
      _ ≤ (4 + 4 * CR) * L ^ 2 := by nlinarith [mul_nonneg hCR0 (sq_nonneg L)]
      _ ≤ _ := by nlinarith [mul_nonneg hK1 (sq_nonneg L), mul_nonneg hK3 (sq_nonneg L)]
  · push_neg at hright
    by_cases hbig : 24 ≤ L
    · have hlo : 1 - (c₀ / 4) / L ≤ σ := by
        have : c / L ≤ (c₀ / 4) / L := by gcongr
        linarith
      have hlo' : 1 - 1 / L ≤ σ := by
        have : c / L ≤ 1 / L := by gcongr
        linarith
      have hm := Formalism.ZF.ldr_mid hZ0 hc₀ hG hI hLL (σ := σ) (t := t) hbig hlo hlo' hright
      rw [hs]
      calc _ ≤ (1441 + 60 / c₀) * L ^ 2 := hm
        _ ≤ _ := by nlinarith [mul_nonneg hK3 (sq_nonneg L), mul_nonneg hCR0 (sq_nonneg L)]
    · push_neg at hbig
      have htT : |t| ≤ Real.exp 24 := by
        have : |t| + 2 < Real.exp 24 := by
          rw [← Real.log_lt_iff_lt_exp (by positivity)]
          exact hbig
        linarith
      have hcL : c / L ≤ cS := by
        rw [div_le_iff₀ hL0]
        nlinarith
      have hinv : 1 / L ≤ 2 := by
        rw [div_le_iff₀ hL0]; linarith
      have hσ3 : σ ≤ 3 := by linarith
      have hb := hCS s hs1 htT (by linarith) hσ3
      calc _ ≤ CS := hb
        _ ≤ |CS| := le_abs_self _
        _ ≤ 4 * |CS| * L ^ 2 := by nlinarith [abs_nonneg CS]
        _ ≤ _ := by nlinarith [mul_nonneg hK1 (sq_nonneg L), mul_nonneg hCR0 (sq_nonneg L)]

end Formalism.ZF
end
end

section

open Complex

noncomputable section

namespace Formalism.ZF

theorem classicalZeroFreeRegionOfBounds : ZeroFreeOf := by
  intro h341 hLDR hG hI hSH hLL
  obtain ⟨t₀, -, ht₀⟩ := zfo_large h341 hLDR hG hI hLL
  obtain ⟨c₂, hc₂, hsmall⟩ := hSH t₀
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (1 / 200000) (c₂ * Real.log 2), lt_min (by norm_num) (mul_pos hc₂ hlog2), ?_⟩
  intro s hs1 hre
  have hL : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hLpos : 0 < Real.log (|s.im| + 2) := lt_of_lt_of_le hlog2 hL
  rcases le_or_gt |s.im| t₀ with hT | hT
  · apply hsmall s hT _ hs1
    have hc : min (1 / 200000) (c₂ * Real.log 2) / Real.log (|s.im| + 2) ≤ c₂ := by
      rw [div_le_iff₀ hLpos]
      calc min (1 / 200000) (c₂ * Real.log 2) ≤ c₂ * Real.log 2 := min_le_right _ _
        _ ≤ c₂ * Real.log (|s.im| + 2) := mul_le_mul_of_nonneg_left hL hc₂.le
    linarith
  · intro hz
    have hs : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
    have hβ := ht₀ s.re s.im hT.le (by rw [← hs]; exact hz)
    have h2 : min (1 / 200000) (c₂ * Real.log 2) / Real.log (|s.im| + 2) ≤ (1 / 200000) / Real.log (|s.im| + 2) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
    linarith

end Formalism.ZF
end
end
