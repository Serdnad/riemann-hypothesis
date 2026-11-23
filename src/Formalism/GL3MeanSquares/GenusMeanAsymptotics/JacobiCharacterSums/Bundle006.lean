module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle002
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle003
public import Formalism.LandauZeroFreeBounds.Statement
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle002
import Formalism.GL3MeanSquares.Bundle001

@[expose] public section

section

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

theorem lb_part (a : ℕ) (D : ℝ) (m n j : ℕ) (T : ℝ) (hmj : m ≤ j)
    (hanD : (a : ℝ) * n * D ≤ a * D / eps a ^ 2 + j)
    (hT : Real.exp (-((a : ℝ) * m) - a * n * D) ≤ T) :
    1 / (E0 a D * (rr a / 8) ^ j) ≤ (1 / 2) ^ j * T := by
  have hR : rr a / 8 = 2 * Real.exp ((a : ℝ) + 1) := by unfold rr; ring
  have hm' : (m : ℝ) ≤ j := by exact_mod_cast hmj
  have ham : (a : ℝ) * m ≤ a * j := mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg a)
  have key : Real.exp (-((a : ℝ) * D / eps a ^ 2) - ((a : ℝ) + 1) * j)
      ≤ Real.exp (-((a : ℝ) * m) - a * n * D) := by
    apply Real.exp_le_exp.mpr
    linarith
  have heq : 1 / (E0 a D * (rr a / 8) ^ j)
      = (1 / 2) ^ j * Real.exp (-((a : ℝ) * D / eps a ^ 2) - ((a : ℝ) + 1) * j) := by
    rw [hR, E0, mul_pow, Real.exp_sub, Real.exp_neg, mul_comm ((a : ℝ) + 1) (j : ℝ),
      Real.exp_nat_mul]
    rw [one_div (2 : ℝ)]
    first
    | ring1
    | (field_simp; done)
    | (field_simp; ring1)
    | (field_simp; rw [← mul_pow]; norm_num)
  rw [heq]
  exact (mul_le_mul_of_nonneg_left key (by positivity)).trans
    (mul_le_mul_of_nonneg_left hT (by positivity))

theorem x_part (a : ℕ) (c₁ K : ℝ) (hc₁ : 0 < c₁) (j : ℕ) (hj : (j : ℝ) ≤ 2 * th a * K + j0 a) :
    c₁ * Real.exp (-K) ≤ c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j := by
  have hlog := log_rr_pos a
  have hid := th_log a
  have hRpos : 0 < rr a := by linarith [rr_gt a]
  have hRj : rr a ^ j = Real.exp (j * Real.log (rr a)) := by
    rw [Real.exp_nat_mul, Real.exp_log hRpos]
  rw [hRj, mul_div_assoc, ← Real.exp_sub]
  refine mul_le_mul_of_nonneg_left ?_ hc₁.le
  rw [Real.exp_le_exp]
  have h1 : (j : ℝ) * Real.log (rr a)
      ≤ (2 * th a * K + j0 a) * Real.log (rr a) :=
    mul_le_mul_of_nonneg_right hj hlog.le
  have h2 : (2 * th a * K + j0 a) * Real.log (rr a)
      = K + j0 a * Real.log (rr a) := by
    linear_combination K * hid
  linarith

theorem far_part (a : ℕ) (S : ℝ) (j : ℕ) (hj2 : 2 ≤ j) (hS : S ≤ 1 + j) :
    eps a ^ (j - 2) * S ≤ rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
  have hRpos : 0 < rr a := by linarith [rr_gt a]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  have hinv : eps a ^ k = 1 / rr a ^ k := by
    unfold eps; rw [one_div_pow]
  have hJ0 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hSX : S ≤ (((k + 2 : ℕ) : ℝ) + 1) ^ 2 := by linarith [sq_nonneg ((k + 2 : ℕ) : ℝ)]
  have e : rr a ^ 2 * (((k + 2 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ (k + 2)
      = (((k + 2 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ k := by
    rw [pow_add (rr a) k 2, mul_comm (rr a ^ k) (rr a ^ 2),
      mul_div_mul_left _ _ (pow_ne_zero 2 hRpos.ne')]
  rw [hinv, e, one_div_mul_eq_div]
  gcongr

private theorem pow_mul_div_pow_succ_eq_div (η X : ℝ) (hη : η ≠ 0) (j : ℕ) :
    η ^ j * (X / η ^ (j + 1)) = X / η := by
  first
  | rw [mul_div_assoc', pow_succ η j, mul_div_mul_left _ _ (pow_ne_zero j hη)]
  | (field_simp; done)
  | (field_simp; ring)

private theorem pow_mul_div_mul_pow_eq_div (η M X : ℝ) (hη : η ≠ 0) (j : ℕ) :
    η ^ j * (X / (M * η ^ j)) = X / M := by
  first
  | rw [mul_div_assoc', mul_comm M (η ^ j), mul_div_mul_left _ _ (pow_ne_zero j hη)]
  | (field_simp; done)
  | (field_simp; ring)



theorem ub_terms (a : ℕ) (CP CF cZ cS c₂ κ L ℓ lam η Mr K : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hCP : 0 < CP) (hCF : 0 < CF) (hcZ : 0 < cZ) (hcS : 0 < cS) (hc₂ : 0 < c₂)
    (hL : 1 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 2 * L) (hlam : 0 < lam) (hη : 0 < η) (hMr : 0 < Mr) (hK : 0 < K)
    (hlη1 : lam / η ≤ 2 * (lam * L) / cZ) (hM : ℓ ^ 2 / Mr ≤ 32 * lam / cS) (hηc : η ≤ c0 a)
    (hηL : η * L < c₂ * K) (h25c : 25 * CF * c₂ ≤ κ) (hκth : κ ≤ th a)
    (hc₂P : 2 * Real.exp 1 * CP * c₂ * rr a ≤ th a) (hjr : th a * K < j) :
    η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ)
        + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * j * lam / η ^ (j + 1) + CF * L * 25 ^ j) ≤
      (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
  have hR16 := rr_gt a
  have hRpos : 0 < rr a := by linarith
  have hRne : rr a ≠ 0 := hRpos.ne'
  have hηne : η ≠ 0 := hη.ne'
  have hL0 : 0 < L := by linarith
  have hJ1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hJpos : (0 : ℝ) < j := by linarith
  have hJsq : (j : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by linarith [sq_nonneg (j : ℝ)]
  have hL2 : 1 ≤ L ^ 2 := by linarith [mul_le_mul hL hL zero_le_one hL0.le]
  have hLL3 : L ≤ L ^ 3 := by linarith [mul_le_mul_of_nonneg_left hL2 hL0.le]
  have hL3 : 1 ≤ L ^ 3 := by linarith
  have hJ1sq : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 2 * L ^ 3 := by
    linarith [mul_le_mul_of_nonneg_left hL3 (sq_nonneg ((j : ℝ) + 1)), sq_nonneg (j : ℝ)]
  have hJL : (j : ℝ) * L ≤ ((j : ℝ) + 1) ^ 2 * L ^ 3 := mul_le_mul hJsq hLL3 hL0.le (by positivity)
  have hℓ2 : ℓ ^ 2 ≤ 4 * L ^ 2 := by
    linarith [mul_le_mul hℓ hℓ hℓ0 (by linarith : (0 : ℝ) ≤ 2 * L)]
  have b1 : η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1)) ≤ 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_pow_succ_eq_div η _ hηne j]
    calc CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η = CP * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 * (lam / η) := by ring
      _ ≤ CP * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 * (2 * (lam * L) / cZ) :=
          mul_le_mul_of_nonneg_left hlη1 (by positivity)
      _ = 2 * CP * lam * L / cZ * ((j : ℝ) + 1) ^ 2 * ℓ ^ 2 := by ring
      _ ≤ 2 * CP * lam * L / cZ * ((j : ℝ) + 1) ^ 2 * (4 * L ^ 2) :=
          mul_le_mul_of_nonneg_left hℓ2 (by positivity)
      _ = 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have b3 : η ^ j * (CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j)) ≤ 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_mul_pow_eq_div η Mr _ hηne j]
    calc CP * ((j : ℝ) + 1) * ℓ ^ 2 / Mr = CP * ((j : ℝ) + 1) * (ℓ ^ 2 / Mr) := by ring
      _ ≤ CP * ((j : ℝ) + 1) * (32 * lam / cS) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 32 * CP / cS * lam * ((j : ℝ) + 1) := by ring
      _ ≤ 32 * CP / cS * lam * (((j : ℝ) + 1) ^ 2 * L ^ 3) := mul_le_mul_of_nonneg_left hJ1sq (by positivity)
      _ = 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have b4 : η ^ j * (2 * (j : ℝ) * lam / η ^ (j + 1)) ≤ 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_pow_succ_eq_div η _ hηne j]
    calc 2 * (j : ℝ) * lam / η = 2 * (j : ℝ) * (lam / η) := by ring
      _ ≤ 2 * (j : ℝ) * (2 * (lam * L) / cZ) := mul_le_mul_of_nonneg_left hlη1 (by positivity)
      _ = 4 / cZ * lam * ((j : ℝ) * L) := by ring
      _ ≤ 4 / cZ * lam * (((j : ℝ) + 1) ^ 2 * L ^ 3) := mul_le_mul_of_nonneg_left hJL (by positivity)
      _ = 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have hx0 : 0 ≤ CP * ℓ * η := by positivity
  have hxK : CP * ℓ * η ≤ 2 * CP * c₂ * K := by
    have e1 : CP * η * ℓ ≤ CP * η * (2 * L) := mul_le_mul_of_nonneg_left hℓ (by positivity)
    have e2 : CP * (η * L) ≤ CP * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le hCP.le
    linarith
  have hexR : Real.exp 1 * (CP * ℓ * η) * rr a ≤ th a * K := by
    calc Real.exp 1 * (CP * ℓ * η) * rr a
        ≤ Real.exp 1 * (2 * CP * c₂ * K) * rr a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxK (Real.exp_pos 1).le) hRpos.le
      _ = (2 * Real.exp 1 * CP * c₂ * rr a) * K := by ring
      _ ≤ th a * K := mul_le_mul_of_nonneg_right hc₂P hK.le
  have hy : Real.exp 1 * (CP * ℓ * η) / (j : ℝ) ≤ 1 / rr a := by
    first
    | (rw [div_le_div_iff₀ hJpos hRpos]; linarith)
    | (rw [div_le_div_iff hJpos hRpos]; linarith)
    | (rw [div_le_div_iff_of_pos hJpos hRpos]; linarith)
  have b2 : η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) ≤ ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    calc η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) = (CP * ℓ * η) ^ j / ((j - 1).factorial : ℝ) := by ring
      _ ≤ (j : ℝ) * (Real.exp 1 * (CP * ℓ * η) / j) ^ j := fact_bound _ hx0 j hj
      _ ≤ (j : ℝ) * (1 / rr a) ^ j := by
          first
          | exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hy j) hJpos.le
          | exact mul_le_mul_of_nonneg_left (pow_le_pow_left (by positivity) hy j) hJpos.le
          | gcongr (j : ℝ) * ?_ ^ j
      _ = (j : ℝ) / rr a ^ j := by rw [one_div_pow, mul_one_div]
      _ ≤ ((j : ℝ) + 1) ^ 2 / rr a ^ j := by gcongr
  have b5 : η ^ j * (CF * L * 25 ^ j) ≤ rr a * (((j : ℝ) + 1) ^ 2 / rr a ^ j) := by
    have h25 : 25 * η ≤ 1 / rr a := by
      have := twentyFive_mul_smallConstant a
      linarith
    have hcl : 25 * (CF * η * L) ≤ (j : ℝ) := by
      have e1 : CF * (η * L) ≤ CF * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le hCF.le
      have e2 : 25 * CF * c₂ * K ≤ th a * K :=
        mul_le_mul_of_nonneg_right (h25c.trans hκth) hK.le
      linarith
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    calc η ^ (k + 1) * (CF * L * 25 ^ (k + 1)) = 25 * (CF * η * L) * (25 * η) ^ k := by ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * (1 / rr a) ^ k := by
          first
          | exact mul_le_mul hcl (pow_le_pow_left₀ (by positivity) h25 k) (by positivity) (by positivity)
          | exact mul_le_mul hcl (pow_le_pow_left (by positivity) h25 k) (by positivity) (by positivity)
      _ = ((k + 1 : ℕ) : ℝ) / rr a ^ k := by rw [one_div_pow, mul_one_div]
      _ ≤ (((k + 1 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ k := by gcongr
      _ = rr a * ((((k + 1 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ (k + 1)) := by
          rw [pow_succ (rr a) k, mul_div_assoc', mul_comm (rr a ^ k) (rr a),
            mul_div_mul_left _ _ hRne]
  have hsplit : η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ) + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * (j : ℝ) * lam / η ^ (j + 1) + CF * L * 25 ^ j)
      = η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1)) + η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) + η ^ j * (CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j)) + η ^ j * (2 * (j : ℝ) * lam / η ^ (j + 1)) + η ^ j * (CF * L * 25 ^ j) := by
    ring
  have hfin : 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + ((j : ℝ) + 1) ^ 2 / rr a ^ j + 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + rr a * (((j : ℝ) + 1) ^ 2 / rr a ^ j) = (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3) + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by ring
  rw [hsplit]
  exact (add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5).trans_eq hfin

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

section

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem inRegion_of_lt {c Z β : ℝ} {q : ℕ} (hc : 0 < c) (hZ : 3 ≤ Z) (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Z ^ 2)
    (hβ : 1 - c / 3 / Real.log Z < β) : Formalism.ZeroFreeDirichlet.InRegion c q (β : ℂ) := by
  unfold Formalism.ZeroFreeDirichlet.InRegion
  rw [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add]
  have hZpos : 0 < Z := by linarith
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have h2q : 0 < Real.log ((q : ℝ) * 2) := Real.log_pos (by linarith)
  have hZ3 : Real.log (Z ^ 3) = 3 * Real.log Z := by rw [Real.log_pow]; norm_num
  have hle : Real.log ((q : ℝ) * 2) ≤ 3 * Real.log Z := by
    rw [← hZ3]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hdiv : c / 3 / Real.log Z ≤ c / Real.log ((q : ℝ) * 2) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hc.le h2q hle
  linarith

theorem isLZero_changeLevel {M q : ℕ} [NeZero M] [NeZero q] (h : M ∣ q) (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1)
    {s : ℂ} (hs : DirichletCharacter.LFunction χ s = 0) :
    Formalism.ZeroFreeDirichlet.IsLZero (DirichletCharacter.changeLevel h χ) s := by
  refine ⟨Or.inl ?_, ?_⟩
  · intro h1
    apply hχ
    apply DirichletCharacter.changeLevel_injective h
    rw [h1, map_one]
  · rw [DirichletCharacter.LFunction_changeLevel h χ (Or.inl hχ), hs, zero_mul]

theorem page_across (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (Z : ℝ) (M₁ M₂ : ℕ) [NeZero M₁] [NeZero M₂] (χ₁ : DirichletCharacter ℂ M₁)
      (χ₂ : DirichletCharacter ℂ M₂) (β₁ β₂ : ℝ), 3 ≤ Z → (M₁ : ℝ) ≤ Z → (M₂ : ℝ) ≤ Z →
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 →
      DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 → DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0 →
      1 - c₀ / Real.log Z < β₁ → 1 - c₀ / Real.log Z < β₂ → β₁ < 1 → β₂ < 1 →
      ∀ n : ℕ, n.Coprime (M₁ * M₂) → χ₁ (n : ZMod M₁) = χ₂ (n : ZMod M₂) := by
  obtain ⟨c, hc, hzfr⟩ := hZ
  refine ⟨c / 3, by positivity, ?_⟩
  intro Z M₁ M₂ _ _ χ₁ χ₂ β₁ β₂ hZ3 hM₁ hM₂ _ _ hne₁ hne₂ hz₁ hz₂ hb₁ hb₂ _ _ n hn
  haveI : NeZero (M₁ * M₂) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hq1 : 1 ≤ M₁ * M₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hqZ : ((M₁ * M₂ : ℕ) : ℝ) ≤ Z ^ 2 := by
    push_cast
    rw [pow_two]
    exact mul_le_mul hM₁ hM₂ (Nat.cast_nonneg _) (by linarith)

  have hr₁ := inRegion_of_lt hc hZ3 hq1 hqZ hb₁
  have hr₂ := inRegion_of_lt hc hZ3 hq1 hqZ hb₂
  have hL₁ := isLZero_changeLevel (dvd_mul_right M₁ M₂) χ₁ hne₁ hz₁
  have hL₂ := isLZero_changeLevel (dvd_mul_left M₂ M₁) χ₂ hne₂ hz₂
  obtain ⟨-, -, -, -, huniq⟩ := hzfr (M₁ * M₂) _ _ hr₁ hL₁
  have heq := (huniq _ _ hr₂ hL₂).1
  have hv := congrArg (fun ψ : DirichletCharacter ℂ (M₁ * M₂) =>
    ψ ((ZMod.unitOfCoprime n hn : (ZMod (M₁ * M₂))ˣ) : ZMod (M₁ * M₂))) heq
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_mul_left M₂ M₁),
    ZMod.cast_natCast (dvd_mul_right M₁ M₂)] at hv
  exact hv.symm

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

def exLF {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ M else DirichletCharacter.LFunction χ

def exOrd {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (exLF χ) ρ

def exKer (y : ℝ) (w : ℂ) : ℂ := (y : ℂ) ^ w / (w * (w - 1))

def explicitFormulaConstant {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : ℂ := -(deriv (exLF χ) 1 / exLF χ 1)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

def liX (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t

def piAP (X : ℝ) (M b : ℕ) : ℕ :=
  ((Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)).card

def IsExcPair {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) : Prop :=
  χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 ∧
    1 - 1 / (8 * Real.log M) < β₁ ∧ β₁ < 1

def mainAP {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (b : ℕ) (X : ℝ) : ℝ :=
  match e with
  | none => liX X / (M.totient : ℝ)
  | some (χ₁, β₁) => (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ)

def PNTAPRelW : Prop :=
  ∃ c₃ A₀ C₀ : ℝ, 0 < c₃ ∧ ∀ (M : ℕ) [NeZero M], 8 ∣ M →
    ∃ e : Option (DirichletCharacter ℂ M × ℝ),
      (∀ p : DirichletCharacter ℂ M × ℝ, e = some p → IsExcPair p.1 p.2) ∧
      (e = none → ∀ (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ), ¬ IsExcPair χ₁ β₁) ∧
      ∀ (X : ℝ) (b : ℕ), 2 ≤ X → C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X → b.Coprime M →
        |(piAP X M b : ℝ) - mainAP e b X| ≤
          A₀ * (Real.exp (-(c₃ * Real.log X / Real.log M)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            mainAP e b X

def soutPart (m₀ N : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors.filter (fun p => Odd (N.factorization p) ∧ ¬ p ∣ m₀), p

def sP (c : ℕ → ℝ) (N p : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), c n

def RR (c : ℕ → ℝ) (m₀ N : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)), c n

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end
