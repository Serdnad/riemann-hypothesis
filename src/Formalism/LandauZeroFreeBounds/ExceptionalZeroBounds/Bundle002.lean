module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def weightedPartialSumUpTo (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n * ((x / n - 1 : ℝ) : ℂ)

def partialSumUpTo (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n

lemma sum_Icc_eq_add_sum_Ioc (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have h1 : ∀ m : ℕ, Icc 1 m = Ioc 0 m := fun m => by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1, h1, Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]

lemma weightedSum_identity (f : ℕ → ℂ) {y Y : ℝ} (hyY : y ≤ Y) :
    (y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y
      = ((Y - y : ℝ) : ℂ) * partialSumUpTo f y
        + ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ) := by
  unfold weightedPartialSumUpTo partialSumUpTo
  rw [sum_Icc_eq_add_sum_Ioc _ (Nat.floor_mono hyY)]
  simp only [mul_add, Finset.mul_sum]
  rw [show ∀ a b c : ℂ, a + b - c = (a - c) + b from fun a b c => by ring, ← Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro n _; push_cast; ring
  · apply Finset.sum_congr rfl; intro n _; push_cast; ring

lemma norm_sum_Ioc_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
  have hY1 : 1 ≤ Y := le_trans hy hyY
  have hterm : ∀ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊,
      ‖f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖ ≤ (Y - y) * Real.log Y := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : y < (n : ℝ) := by
      have := Nat.lt_floor_add_one y
      have h2 : ((⌊y⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
      linarith
    have hn2 : (n : ℝ) ≤ Y := by
      have := Nat.floor_le (show 0 ≤ Y by linarith)
      have h2 : (n : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn.2
      linarith
    have hnpos : (0:ℝ) < n := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hA : 0 ≤ y * (Y / n - 1) := by
      apply mul_nonneg (by linarith)
      rw [sub_nonneg, le_div_iff₀ hnpos]; linarith
    have hB : y * (Y / n - 1) ≤ Y - y := by
      have e : y * (Y / n - 1) = (Y - n) * (y / n) := by field_simp
      rw [e]
      have h3 : y / n ≤ 1 := by rw [div_le_one hnpos]; linarith
      have h4 : 0 ≤ Y - n := by linarith
      nlinarith
    rw [abs_of_nonneg hA]
    have hf' : ‖f n‖ ≤ Real.log Y :=
      calc ‖f n‖ ≤ Λ n := hf n
        _ ≤ Real.log n := vonMangoldt_le_log
        _ ≤ Real.log Y := Real.log_le_log hnpos hn2
    calc ‖f n‖ * (y * (Y / n - 1)) ≤ Real.log Y * (Y - y) :=
          mul_le_mul hf' hB hA (Real.log_nonneg hY1)
      _ = (Y - y) * Real.log Y := by ring
  calc _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, ‖f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, (Y - y) * Real.log Y := Finset.sum_le_sum hterm
    _ = ((Ioc ⌊y⌋₊ ⌊Y⌋₊).card : ℝ) * ((Y - y) * Real.log Y) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by linarith) (Real.log_nonneg hY1))
      rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono hyY)]
      have h1 := Nat.floor_le (show 0 ≤ Y by linarith)
      have h2 := Nat.lt_floor_add_one y
      linarith

lemma norm_weightedSum_sub_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖((y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y) - ((Y - y : ℝ) : ℂ) * partialSumUpTo f y‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
  rw [weightedSum_identity f hyY, add_sub_cancel_left]
  exact norm_sum_Ioc_le f hf hy hyY

lemma sum_vonMangoldt_not_coprime_le (q : ℕ) (hq : q ≠ 0) (N : ℕ) :
    ∑ n ∈ Icc 1 N, Λ n * (if n.Coprime q then 0 else 1) ≤ (Nat.log 2 N : ℝ) * Real.log q := by
  set K := Nat.log 2 N
  set g : ℕ → ℝ := fun n => Λ n * (if n.Coprime q then 0 else 1) with hg
  have hgle : ∀ n, g n ≤ Λ n := fun n => by
    simp only [hg]; split_ifs <;> simp [vonMangoldt_nonneg]
  have hsub : (Icc 1 N).filter (fun n => g n ≠ 0) ⊆ (q ^ K).divisors := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨_, hN⟩, hgn⟩ := hn
    have hΛ : Λ n ≠ 0 := by intro h; apply hgn; simp [hg, h]
    have hnc : ¬ n.Coprime q := by intro h; apply hgn; simp [hg, h]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (vonMangoldt_ne_zero_iff.1 hΛ)
    have hpq : p ∣ q := by
      by_contra hc
      exact hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hc))
    have hkK : k ≤ K := by
      apply Nat.le_log_of_pow_le one_lt_two
      exact le_trans (Nat.pow_le_pow_left hp.two_le k) hN
    rw [Nat.mem_divisors]
    exact ⟨(pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkK), pow_ne_zero _ hq⟩
  calc ∑ n ∈ Icc 1 N, g n = ∑ n ∈ (Icc 1 N).filter (fun n => g n ≠ 0), g n :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => g n ≠ 0), Λ n := Finset.sum_le_sum fun n _ => hgle n
    _ ≤ ∑ n ∈ (q ^ K).divisors, Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ = (K : ℝ) * Real.log q := by rw [vonMangoldt_sum, Nat.cast_pow, Real.log_pow]

lemma one_apply_natCast {q : ℕ} (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if n.Coprime q then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).2 h)
  · exact MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n q).1 hu))

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma convolution_nonneg_of_divisors (f g : ArithmeticFunction ℂ) (n : ℕ)
    (hf : ∀ d, d ∣ n → 0 ≤ f d) (hg : ∀ d, d ∣ n → 0 ≤ g d) : 0 ≤ (f * g) n := by
  change 0 ≤ ∑ x ∈ Nat.divisorsAntidiagonal n, f x.1 * g x.2
  refine Finset.sum_nonneg fun x hx => ?_
  have h := (Nat.mem_divisorsAntidiagonal.1 hx).1
  exact mul_nonneg (hf _ (Dvd.intro _ h)) (hg _ (Dvd.intro_left _ h))

lemma character_convolution_eq {N N' M : ℕ} (χ : DirichletCharacter ℂ N) (χ' : DirichletCharacter ℂ N')
    (ψ : DirichletCharacter ℂ M) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    (n : ℕ) :
    (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) * toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M))) n
      = χ' (n : ZMod N') * DirichletCharacter.zetaMul χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) a *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M)) b), DirichletCharacter.zetaMul,
    coe_zeta_mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hdvd : i ∣ n := Nat.dvd_of_mem_divisors hi
  have hi0 : i ≠ 0 := (Nat.pos_of_mem_divisors hi).ne'
  have hni : n / i ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero hi0)).ne'
  simp only [toArithmeticFunction, coe_mk, hi0, hni, if_false]
  rw [hψ i]
  calc χ' ((n / i : ℕ) : ZMod N') * (χ (i : ZMod N) * χ' (i : ZMod N'))
      = (χ' ((n / i : ℕ) : ZMod N') * χ' (i : ZMod N')) * χ (i : ZMod N) := by ring
    _ = χ' (n : ZMod N') * χ (i : ZMod N) := by
      rw [← map_mul, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]


set_option backward.isDefEq.respectTransparency.types false in
lemma prime_power_coefficient_nonneg {N N' M : ℕ} {χ : DirichletCharacter ℂ N} {χ' : DirichletCharacter ℂ N'}
    {ψ : DirichletCharacter ℂ M} (hχ : χ ^ 2 = 1) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    {p : ℕ} (hp : p.Prime)
    (hc : χ' (p : ZMod N') = 0 ∨ χ' (p : ZMod N') = 1 ∨ (χ' (p : ZMod N') = -1 ∧ χ (p : ZMod N) = -1))
    (k : ℕ) :
    0 ≤ (DirichletCharacter.zetaMul χ * (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M)))) (p ^ k) := by
  have hζ : ∀ j, DirichletCharacter.zetaMul χ (p ^ j) = ∑ i ∈ Finset.range (j + 1), χ (p : ZMod N) ^ i := by
    intro j
    rw [DirichletCharacter.zetaMul, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [toArithmeticFunction, hp.ne_zero]
  apply convolution_nonneg_of_divisors
  · intro d _
    exact DirichletCharacter.zetaMul_nonneg hχ d
  · intro d hd
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rw [character_convolution_eq χ χ' ψ hψ, Nat.cast_pow, map_pow]
    rcases hc with h | h | ⟨h, h'⟩
    · exact mul_nonneg (by rw [h]; exact pow_nonneg le_rfl j) (DirichletCharacter.zetaMul_nonneg hχ _)
    · exact mul_nonneg (by rw [h]; exact pow_nonneg zero_le_one j) (DirichletCharacter.zetaMul_nonneg hχ _)
    · rw [h, hζ, h', neg_one_geom_sum]
      split_ifs with he
      · simp
      · have hj : Even j := by
          rcases Nat.even_or_odd j with hj | hj
          · exact hj
          · exact absurd hj.add_one he
        rw [hj.neg_one_pow]
        norm_num

end Formalism.ZeroFreeDirichlet
end
end
