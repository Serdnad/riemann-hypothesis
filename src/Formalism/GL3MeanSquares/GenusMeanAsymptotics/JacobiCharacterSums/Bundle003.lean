module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

section

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

theorem exists_power_sum_lower_bound (C : ℝ) (a : ℕ) (hC : 0 < C)
    (hT : ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n → (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
      ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + a * n ∧ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i, z i ^ k‖)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (N : ℕ) (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re) (hi : ∃ i, 1 / 2 ≤ ‖u i‖)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ j n : ℕ, m + 1 ≤ j ∧ j ≤ m + a * n ∧ 1 ≤ n ∧ (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re ∧
      (1 / 2) ^ j * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤
        ‖∑ i, u i ^ j‖ + ε ^ (j - 2) * ∑ i, (u i).re := by
  classical
  have hre0 : ∀ i, 0 ≤ (u i).re := fun i => le_trans (sq_nonneg _) (hu i)
  have hle1 : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h1 := hu i
    have h2 : (u i).re ≤ ‖u i‖ := by
      first
        | exact Complex.re_le_norm (u i)
        | exact Complex.re_le_abs (u i)
    nlinarith [norm_nonneg (u i)]
  obtain ⟨i0, hi0⟩ := hi

  set I := Finset.univ.filter (fun i => ε ≤ ‖u i‖) with hIdef
  have hi0I : i0 ∈ I := Finset.mem_filter.2 ⟨Finset.mem_univ _, by linarith⟩
  have hIne : I.Nonempty := ⟨i0, hi0I⟩
  obtain ⟨i1, hi1I, hi1⟩ := Finset.exists_mem_eq_sup' hIne (fun i => ‖u i‖)
  set r := I.sup' hIne (fun i => ‖u i‖) with hr
  have hr0 : 1 / 2 ≤ r := le_trans hi0 (Finset.le_sup' (fun i => ‖u i‖) hi0I)
  have hrpos : 0 < r := by linarith
  have hnr : ‖(r : ℂ)‖ = r := by
    first
      | rw [Complex.norm_real, Real.norm_of_nonneg hrpos.le]
      | simp [abs_of_pos hrpos]
  set n := I.card with hn
  have hn1 : 1 ≤ n := Finset.card_pos.2 hIne
  let e : Fin n ≃ I := I.equivFin.symm
  let z : Fin n → ℂ := fun k => u (e k) / r
  have hz1 : ∀ k, ‖z k‖ ≤ 1 := by
    intro k
    simp only [z]
    rw [norm_div, hnr, div_le_one hrpos]
    exact Finset.le_sup' (fun i => ‖u i‖) (e k).2
  have hz2 : ∃ k, ‖z k‖ = 1 := by
    refine ⟨e.symm ⟨i1, hi1I⟩, ?_⟩
    simp only [z, Equiv.apply_symm_apply]
    rw [norm_div, hnr, ← hi1]
    exact div_self hrpos.ne'
  obtain ⟨k, hk1, hk2, hkB⟩ := hT n m z hn1 hz1 hz2

  have hsumz : ∑ k', z k' ^ k = (∑ i ∈ I, u i ^ k) / (r : ℂ) ^ k := by
    simp only [z, div_pow]
    rw [← Finset.sum_div]
    congr 1
    rw [← Finset.sum_coe_sort I]
    exact e.sum_comp (fun i : I => u i ^ k)
  have hB0 : 0 ≤ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hC.le (by positivity))) _
  have hmain : (1 / 2) ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i ∈ I, u i ^ k‖ := by
    rw [hsumz, norm_div, norm_pow, hnr, le_div_iff₀ (pow_pos hrpos k)] at hkB
    calc (1 / 2) ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n)
        ≤ r ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hr0 k) hB0
      _ ≤ ‖∑ i ∈ I, u i ^ k‖ := by linarith

  have hcompl : ∑ i ∈ Iᶜ, ‖u i‖ ^ k ≤ ε ^ (k - 2) * ∑ i, (u i).re := by
    calc ∑ i ∈ Iᶜ, ‖u i‖ ^ k ≤ ∑ i ∈ Iᶜ, ε ^ (k - 2) * (u i).re := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hlt : ‖u i‖ < ε := by
            rw [Finset.mem_compl, Finset.mem_filter] at hi
            push_neg at hi
            exact hi (Finset.mem_univ _)
          calc ‖u i‖ ^ k = ‖u i‖ ^ 2 * ‖u i‖ ^ (k - 2) := by
                rw [← pow_add]
                congr 1
                omega
            _ ≤ (u i).re * ε ^ (k - 2) :=
                mul_le_mul (hu i) (pow_le_pow_left₀ (norm_nonneg _) hlt.le _) (by positivity) (hre0 i)
            _ = ε ^ (k - 2) * (u i).re := by ring
      _ = ε ^ (k - 2) * ∑ i ∈ Iᶜ, (u i).re := by rw [Finset.mul_sum]
      _ ≤ ε ^ (k - 2) * ∑ i, (u i).re :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hre0 i)
            (by positivity)
  have hsplit : ‖∑ i ∈ I, u i ^ k‖ ≤ ‖∑ i, u i ^ k‖ + ∑ i ∈ Iᶜ, ‖u i‖ ^ k := by
    have h := Finset.sum_add_sum_compl I (fun i => u i ^ k)
    have h' : ∑ i ∈ I, u i ^ k = ∑ i, u i ^ k - ∑ i ∈ Iᶜ, u i ^ k := by
      rw [← h]
      ring
    rw [h']
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_pow _ _))
  have hnε : (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re := by
    calc (n : ℝ) * ε ^ 2 = ∑ i ∈ I, ε ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ I, (u i).re := Finset.sum_le_sum fun i hi =>
          le_trans (pow_le_pow_left₀ hε0.le (Finset.mem_filter.1 hi).2 2) (hu i)
      _ ≤ ∑ i, (u i).re :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hre0 i
  refine ⟨k, n, hk1, hk2, hn1, hnε, ?_⟩
  linarith [hmain, hsplit, hcompl]

theorem turan_lb (C : ℝ) (hC : 0 < C) (a n m : ℕ) (hn : 1 ≤ n) :
    Real.exp (-((a : ℝ) * m) - a * n * Real.log (max C 1)) ≤ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hCm : 0 < max C 1 := lt_max_of_lt_right one_pos
  have h1 : Real.exp (-(m : ℝ) / n) * (m + n) ≤ n :=
    calc Real.exp (-(m : ℝ) / n) * (m + n) = n * (Real.exp (-(m : ℝ) / n) * ((m : ℝ) / n + 1)) := by
          field_simp
      _ ≤ n * (Real.exp (-(m : ℝ) / n) * Real.exp ((m : ℝ) / n)) := by
          gcongr
          exact Real.add_one_le_exp _
      _ = n := by
          rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, mul_one]
  have hb : Real.exp (-(m : ℝ) / n - Real.log (max C 1)) ≤ (n : ℝ) / (C * (m + n)) := by
    rw [Real.exp_sub, Real.exp_log hCm]
    have h2 : Real.exp (-(m : ℝ) / n) ≤ n / (m + n) := by
      rw [le_div_iff₀ (by positivity)]
      exact h1
    calc Real.exp (-(m : ℝ) / n) / max C 1 ≤ ((n : ℝ) / (m + n)) / max C 1 := by gcongr
      _ ≤ ((n : ℝ) / (m + n)) / C := by
          gcongr
          exact le_max_left _ _
      _ = n / (C * (m + n)) := by rw [div_div, mul_comm]
  calc Real.exp (-((a : ℝ) * m) - a * n * Real.log (max C 1))
      = Real.exp (-(m : ℝ) / n - Real.log (max C 1)) ^ (a * n) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp
    _ ≤ ((n : ℝ) / (C * (m + n))) ^ (a * n) := pow_le_pow_left₀ (Real.exp_pos _).le hb _

theorem fact_bound (x : ℝ) (hx : 0 ≤ x) (j : ℕ) (hj : 1 ≤ j) :
    x ^ j / ((j - 1).factorial : ℝ) ≤ j * (Real.exp 1 * x / j) ^ j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hF : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hF1 : ((j - 1).factorial : ℝ) ≠ 0 := by positivity
  have hP : (0 : ℝ) < (j : ℝ) ^ j := pow_pos hjpos j
  have hfact : ((j - 1).factorial : ℝ) * j = j.factorial := by
    have : j * (j - 1).factorial = j.factorial := by
      first
        | exact Nat.mul_factorial_pred (show j ≠ 0 by omega)
        | exact Nat.mul_factorial_pred (show 0 < j by omega)
    rw [← this]
    push_cast
    ring
  have hkey : (j : ℝ) ^ j / j.factorial ≤ Real.exp 1 ^ j :=
    calc (j : ℝ) ^ j / j.factorial ≤ Real.exp j := by
          first
            | exact Real.pow_div_factorial_le_exp _ hjpos.le j
            | exact Real.pow_div_factorial_le_exp hjpos.le j
      _ = Real.exp 1 ^ j := by rw [← Real.exp_nat_mul, mul_one]
  have h1 : 1 / (j.factorial : ℝ) ≤ Real.exp 1 ^ j / (j : ℝ) ^ j := by
    rw [div_le_div_iff₀ hF hP]
    rw [div_le_iff₀ hF] at hkey
    linarith
  have hx' : 0 ≤ (j : ℝ) * x ^ j := by positivity
  calc x ^ j / ((j - 1).factorial : ℝ) = ((j : ℝ) * x ^ j) * (1 / j.factorial) := by
        rw [← hfact]
        field_simp
    _ ≤ ((j : ℝ) * x ^ j) * (Real.exp 1 ^ j / (j : ℝ) ^ j) := mul_le_mul_of_nonneg_left h1 hx'
    _ = j * (Real.exp 1 * x / j) ^ j := by
        rw [div_pow, mul_pow]
        ring

theorem log_sq_bound (M : ℝ) (hM : 1 ≤ M) : Real.log (3 * M) ^ 2 ≤ 32 * Real.sqrt M := by
  have h3M : (1 : ℝ) ≤ 3 * M := by linarith
  have hL0 : 0 ≤ Real.log (3 * M) := Real.log_nonneg h3M
  have hL : Real.log (3 * M) ≤ (3 * M) ^ ((1 : ℝ) / 4) / (1 / 4) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have hq : ((3 * M) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt (3 * M) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : Real.sqrt (3 * M) ≤ 2 * Real.sqrt M := by
    rw [← h4, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log (3 * M) ^ 2 ≤ ((3 * M) ^ ((1 : ℝ) / 4) / (1 / 4)) ^ 2 :=
        pow_le_pow_left₀ hL0 hL 2
    _ = 16 * ((3 * M) ^ ((1 : ℝ) / 4)) ^ 2 := by ring
    _ = 16 * Real.sqrt (3 * M) := by rw [hq]
    _ ≤ 32 * Real.sqrt M := by linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

def cS (U : ℕ) : ℂ := ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ)

def cT (U : ℕ) : ℂ := ∑ b ∈ Ioc 0 U, χ (b : ZMod q) * (Real.log b : ℂ) / (b : ℂ)

def cF (N : ℕ) : ℂ := ∑ n ∈ Ioc 0 N, (∑ d ∈ n.divisors, χ (d : ZMod q)) / (n : ℂ)

def hH (k : ℕ) : ℝ := ∑ a ∈ Ioc 0 k, ((a : ℝ))⁻¹

theorem cF_eq (N : ℕ) :
    cF χ N = ∑ b ∈ Ioc 0 N, χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) := by
  have hcond : ∀ (n d : ℕ), n ∈ Finset.Ioc 0 N ∧ d ∈ n.divisors ↔
      n ∈ (Finset.Ioc 0 N).filter (d ∣ ·) ∧ d ∈ Finset.Ioc 0 N := by
    intro n d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, hdn, -⟩
      have h1 := Nat.le_of_dvd hn0 hdn
      have h2 := Nat.pos_of_dvd_of_pos hdn hn0
      exact ⟨⟨⟨hn0, hnN⟩, hdn⟩, h2, by omega⟩
    · rintro ⟨⟨⟨hn0, hnN⟩, hdn⟩, -, -⟩
      exact ⟨⟨hn0, hnN⟩, hdn, by omega⟩
  unfold cF hH
  simp only [Finset.sum_div]
  rw [Finset.sum_comm' hcond]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
  have himg : (Finset.Ioc 0 N).filter (d ∣ ·) = (Finset.Ioc 0 (N / d)).image (fun a => d * a) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨a, rfl⟩⟩
      refine ⟨a, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos a with h | h
        · subst h
          simp at h1
        · exact h
      · exact (Nat.le_div_iff_mul_le hd0).mpr (by rw [mul_comm]; exact h2)
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hd0 h1, ?_⟩, dvd_mul_right d a⟩
      have h3 := (Nat.le_div_iff_mul_le hd0).mp h2
      rw [mul_comm]
      exact h3
  rw [himg, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd0 h)]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha0 : (a : ℂ) ≠ 0 := by
    have h1 := (Finset.mem_Ioc.mp ha).1
    exact_mod_cast h1.ne'
  have hd0' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  field_simp

theorem cF_split (N U : ℕ) (hUN : U ≤ N) :
    cF χ N = ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) +
      ∑ a ∈ Ioc 0 N, ((a : ℂ))⁻¹ * ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ) := by
  rw [cF_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUN]
  congr 1
  have hcond : ∀ (b a : ℕ), b ∈ Finset.Ioc U N ∧ a ∈ Finset.Ioc 0 (N / b) ↔
      b ∈ Finset.Ioc U (N / a) ∧ a ∈ Finset.Ioc 0 N := by
    intro b a
    simp only [Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hUb, hbN⟩, ha0, haN⟩
      have hb0 : 0 < b := by omega
      have h1 : a * b ≤ N := (Nat.le_div_iff_mul_le hb0).mp haN
      refine ⟨⟨hUb, (Nat.le_div_iff_mul_le ha0).mpr (by linarith)⟩, ha0, ?_⟩
      exact le_trans (Nat.le_mul_of_pos_right a hb0) h1
    · rintro ⟨⟨hUb, hbNa⟩, ha0, haN⟩
      have h1 : b * a ≤ N := (Nat.le_div_iff_mul_le ha0).mp hbNa
      have hb0 : 0 < b := by omega
      exact ⟨⟨hUb, le_trans (Nat.le_mul_of_pos_right b ha0) h1⟩, ha0,
        (Nat.le_div_iff_mul_le hb0).mpr (by linarith)⟩
  unfold hH
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm' hcond]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
end
end

section

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

lemma sharp_cpow_sub_one {ρ : ℂ} (hρ0 : ρ ≠ 0) (hre : ρ.re ≤ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖(t : ℂ) ^ ρ - 1‖ ≤ ‖ρ‖ * (t - 1) := by
  have hd : ∀ x ∈ Set.Icc (1 : ℝ) t,
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ ρ) (ρ * (x : ℂ) ^ (ρ - 1)) (Set.Icc 1 t) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    exact ((Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico (1 : ℝ) t, ‖ρ * (x : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ‖ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have h1 : x ^ (ρ - 1).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.1 (by simp; linarith)
    calc ‖ρ‖ * x ^ (ρ - 1).re ≤ ‖ρ‖ * 1 := by gcongr
      _ = ‖ρ‖ := mul_one _
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simpa using h

lemma differenced_kernel_bound {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ‖(((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ)‖ ≤ ‖ρ‖ * δ * δ := by
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  let f : ℝ → ℂ := fun u => (((u : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) + (((u⁻¹ - 1 : ℝ)) : ℂ)
  let f' : ℝ → ℂ := fun u => ((u : ℂ) ^ ρ - 1) / (u : ℂ) ^ 2
  have hd : ∀ x ∈ Set.Icc (1 : ℝ) (1 + δ), HasDerivWithinAt f (f' x) (Set.Icc 1 (1 + δ)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0.ne'
    have h1 := (((Complex.hasStrictDerivAt_cpow_const (c := ρ - 1)
      (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).sub_const 1).div_const (ρ - 1)
    have h2 := ((hasDerivAt_inv hx0.ne').sub_const 1).ofReal_comp
    refine (h1.add h2).hasDerivWithinAt.congr_deriv ?_
    simp only [f']
    have e1 : (x : ℂ) ^ (ρ - 1 - 1) = (x : ℂ) ^ ρ / (x : ℂ) ^ 2 := by
      rw [show ρ - 1 - 1 = ρ - 2 by ring, Complex.cpow_sub _ _ hxc,
        show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    rw [e1]
    push_cast
    field_simp
    ring
  have hb : ∀ x ∈ Set.Ico (1 : ℝ) (1 + δ), ‖f' x‖ ≤ ‖ρ‖ * δ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hk := sharp_cpow_sub_one hρ0 hre hx.1
    simp only [f']
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    have hx1 : 1 ≤ x ^ 2 := one_le_pow₀ hx.1
    calc ‖(x : ℂ) ^ ρ - 1‖ / x ^ 2 ≤ ‖(x : ℂ) ^ ρ - 1‖ := div_le_self (norm_nonneg _) hx1
      _ ≤ ‖ρ‖ * (x - 1) := hk
      _ ≤ ‖ρ‖ * δ := by gcongr; linarith [hx.2]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (1 + δ) ⟨by linarith, le_rfl⟩
  have hf1 : f 1 = 0 := by simp [f]
  rw [hf1, sub_zero, show 1 + δ - 1 = δ by ring] at h
  exact h

lemma sharp_kernel {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖(((1 + δ) / δ : ℝ) : ℂ) * ((((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) - 1‖ ≤ 2 * δ * ‖ρ‖ := by
  set g : ℂ := (((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) with hg
  set e : ℂ := g + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ) with he
  have hae := differenced_kernel_bound hρ0 hρ1 hre hδ
  rw [← hg, ← he] at hae
  have hr : (1 + δ) / δ * ((1 + δ)⁻¹ - 1) = -1 := by
    field_simp
    ring
  have hid : (((1 + δ) / δ : ℝ) : ℂ) * g - 1 = (((1 + δ) / δ : ℝ) : ℂ) * e := by
    rw [he, mul_add, ← Complex.ofReal_mul, hr]
    push_cast
    ring
  have hq : 0 < (1 + δ) / δ := by positivity
  rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq.le]
  calc (1 + δ) / δ * ‖e‖ ≤ (1 + δ) / δ * (‖ρ‖ * δ * δ) := by gcongr
    _ = (1 + δ) * (δ * ‖ρ‖) := by field_simp
    _ ≤ 2 * (δ * ‖ρ‖) := by gcongr; linarith
    _ = 2 * δ * ‖ρ‖ := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
