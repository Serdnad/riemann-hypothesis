module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Prime.Factorial
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
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.Primorial
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory.PrimeLogSum
open Finset

open Finset in
private lemma log_three_lt_one_point_one_one : Real.log 3 < 1.11 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp 0.11
  have h3 : Real.exp 1.11 = Real.exp 1 * Real.exp 0.11 := by
    rw [← Real.exp_add]; norm_num
  rw [h3]
  nlinarith

open Finset in
private lemma log_succ_div_le_telescoping_sub (n : ℕ) (hn : 3 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1))
      ≤ (Real.log n + 4 / 3) / n - (Real.log ((n + 1 : ℕ) : ℝ) + 4 / 3) / ((n + 1 : ℕ) : ℝ) := by
  push_cast
  set x : ℝ := (n : ℝ) with hx
  have hx3 : (3 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hd : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div (by positivity) hx0.ne'] at h
    have : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have h1 : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ (x + 1) * (1 / x) :=
    mul_le_mul_of_nonneg_left hd (by linarith)
  have h2 : (x + 1) * (1 / x) ≤ 4 / 3 := by
    rw [mul_one_div, div_le_iff₀ hx0]; linarith
  have key : Real.log (x + 1)
      ≤ (x + 1) * (Real.log x + 4 / 3) - x * (Real.log (x + 1) + 4 / 3) := by
    nlinarith
  have hpos : 0 < (x + 1) * x := by positivity
  calc Real.log (x + 1) / ((x + 1) * (x + 1 - 1))
      = Real.log (x + 1) / ((x + 1) * x) := by ring_nf
    _ ≤ ((x + 1) * (Real.log x + 4 / 3) - x * (Real.log (x + 1) + 4 / 3)) / ((x + 1) * x) :=
        div_le_div_of_nonneg_right key hpos.le
    _ = (Real.log x + 4 / 3) / x - (Real.log (x + 1) + 4 / 3) / (x + 1) := by
        field_simp

open Finset in
private lemma sum_log_div_mul_pred_add_le_const (N : ℕ) (hN : 3 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) + (Real.log N + 4 / 3) / N
      ≤ Real.log 2 / 2 + Real.log 3 / 6 + (Real.log 3 + 4 / 3) / 3 := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp [Finset.sum_range_succ]
    norm_num
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have := log_succ_div_le_telescoping_sub n hn
    linarith

open Finset in
private lemma div_le_factorization_factorial' (N p : ℕ) (hp : p.Prime) :
    N / p ≤ (N.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (lt_add_one (Nat.log p N))]
  rcases Nat.lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  · have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
      simp [Nat.log_pos hp.one_lt h]
    simpa using single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1

open Finset in
private lemma mul_sum_prime_log_div_le_log_factorial_add (N : ℕ) :
    (N : ℝ) * ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log (N.factorial : ℝ) + N * Real.log 4 := by
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hfac : Real.log (N.factorial : ℝ)
      = ∑ p ∈ P, ((N.factorial).factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization]
    apply Finsupp.sum_of_support_subset
    · intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      simp only [hP, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le ((hp.1.dvd_factorial).1 hp.2.1), hp.1⟩
    · intro i _
      simp
  have htheta : ∑ p ∈ P, Real.log p ≤ N * Real.log 4 := by
    rw [← Real.log_prod (fun p hp => by
      have := (Finset.mem_filter.1 hp).2.pos
      positivity), ← Real.log_pow]
    apply Real.log_le_log
    · exact Finset.prod_pos fun p hp => by
        have := (Finset.mem_filter.1 hp).2.pos
        positivity
    · have h := primorial_le_four_pow N
      have h' : ((primorial N : ℕ) : ℝ) ≤ ((4 ^ N : ℕ) : ℝ) := by exact_mod_cast h
      simpa [primorial, hP, Nat.cast_prod] using h'
  rw [Finset.mul_sum, hfac]
  calc ∑ p ∈ P, (N : ℝ) * (Real.log p / p)
      ≤ ∑ p ∈ P, (((N.factorial).factorization p : ℝ) * Real.log p + Real.log p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := (Finset.mem_filter.1 hp).2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        have hv : ((N / p : ℕ) : ℝ) ≤ ((N.factorial).factorization p : ℝ) := by
          exact_mod_cast div_le_factorization_factorial' N p hp'
        have hlt : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by
          exact_mod_cast Nat.lt_div_mul_add hp'.pos
        have hq : (N : ℝ) / p ≤ ((N.factorial).factorization p : ℝ) + 1 := by
          rw [div_le_iff₀ hp0]
          nlinarith
        calc (N : ℝ) * (Real.log p / p) = (N : ℝ) / p * Real.log p := by ring
          _ ≤ (((N.factorial).factorization p : ℝ) + 1) * Real.log p :=
            mul_le_mul_of_nonneg_right hq hlog
          _ = _ := by ring
    _ = ∑ p ∈ P, ((N.factorial).factorization p : ℝ) * Real.log p + ∑ p ∈ P, Real.log p :=
        Finset.sum_add_distrib
    _ ≤ _ := by linarith

open Finset in
private lemma log_factorial_le_stirling_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + 1 + Real.log n / 2 := by
  have h1 : Real.log (Stirling.stirlingSeq n) ≤ Real.log (Stirling.stirlingSeq 1) := by
    have := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (n - 1))
    simpa [Function.comp, Nat.sub_add_cancel hn] using this
  rw [Stirling.log_stirlingSeq_formula, Stirling.log_stirlingSeq_formula] at h1
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul (by norm_num) hn0, Real.log_div hn0 (Real.exp_pos 1).ne', Real.log_exp] at h1
  simp only [Nat.factorial_one, Nat.cast_one, mul_one, Real.log_one, one_div, Real.log_inv,
    Real.log_exp] at h1
  linarith [h1]


open Finset in
theorem _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le : ∀ N : ℕ,
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
      ≤ Real.log N + 2.2 := by
  intro N
  have hl2 := Real.log_two_lt_d9
  have hl3 := log_three_lt_one_point_one_one
  have hl3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rcases Nat.lt_or_ge N 4 with hN | hN
  · interval_cases N <;>
      simp [Finset.sum_filter, Finset.sum_range_succ, Nat.prime_two, Nat.prime_three] <;>
      norm_num <;> linarith
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hsplit : ∑ p ∈ P, Real.log p / ((p : ℝ) - 1)
      = ∑ p ∈ P, Real.log p / p + ∑ p ∈ P, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
    have h3 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h4 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hB : ∑ p ∈ P, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ n ∈ Finset.range (N + 1), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n _ _
    apply div_nonneg (Real.log_natCast_nonneg n)
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  have hC := sum_log_div_mul_pred_add_le_const N (by omega)
  have hg : 0 ≤ (Real.log N + 4 / 3) / N :=
    div_nonneg (by linarith [Real.log_natCast_nonneg N]) (Nat.cast_nonneg N)
  have hA := mul_sum_prime_log_div_le_log_factorial_add N
  have hF := log_factorial_le_stirling_bound N (by omega)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : Real.log N ≤ 0.4 * N := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / Real.exp 1 by positivity)
    rw [Real.log_div hNpos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    have he := Real.exp_one_gt_d9
    have h5 : (N : ℝ) / Real.exp 1 ≤ 0.4 * N := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      nlinarith
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hA' : ∑ p ∈ P, Real.log p / p ≤ Real.log N - 1 + 0.25 + 0.2 + Real.log 4 := by
    have h : (N : ℝ) * ∑ p ∈ P, Real.log p / p
        ≤ N * (Real.log N - 1 + 0.25 + 0.2 + Real.log 4) := by
      linarith
    exact le_of_mul_le_mul_left h hNpos
  rw [hsplit]
  linarith

end GlobalTheory.PrimeLogSum
end

section

namespace GlobalTheory.LocalHomExtension

theorem exists_isLocalHom_extension {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C]
    [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal) (hv : Valuation.Integers v O)
    (φ : A →+* B) (hφ : Function.Injective φ) (hint : φ.IsIntegral)
    (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  let : Algebra A B := φ.toAlgebra
  let : Algebra A O := ι.toAlgebra
  let : Algebra A C := ((algebraMap O C).comp ι).toAlgebra
  have : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  have : Module.IsTorsionFree A C := Module.isTorsionFree_iff_algebraMap_injective.mpr hι
  have : Algebra.IsIntegral A B := ⟨hint⟩

  let f : B →ₐ[A] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])

  have hO : ∀ b : B, ∃ o : O, algebraMap O C o = f b := fun b => by
    have h1 : IsIntegral A (f b) := (Algebra.IsIntegral.isIntegral b).map f
    exact hv.exists_of_le_one (hv.mem_of_integral h1.tower_top)
  choose g hg using hO
  have inj := hv.hom_inj
  let ι' : B →+* O :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => inj (by rw [hg, map_add (f := _), map_add (f := _), hg, hg]) }
  have hcomp : ι'.comp φ = ι := by
    ext a
    apply inj
    show algebraMap O C (g (φ a)) = algebraMap O C (ι a)
    rw [hg]
    exact f.commutes a
  refine ⟨ι', ?_, hcomp⟩

  have hA : (IsLocalRing.maximalIdeal O).comap ι = IsLocalRing.maximalIdeal A :=
    ((IsLocalRing.local_hom_TFAE ι).out 1 5).mp (inferInstance : IsLocalHom ι)
  have hp : (((IsLocalRing.maximalIdeal O).comap ι').comap (algebraMap A B)).IsMaximal := by
    rw [Ideal.comap_comap, show ι'.comp (algebraMap A B) = ι from hcomp, hA]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have hpm := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap A B)
    (show (algebraMap A B).IsIntegral from hint) ((IsLocalRing.maximalIdeal O).comap ι') hp
  exact ((IsLocalRing.local_hom_tfae ι').out 1 5).mpr (IsLocalRing.eq_maximalIdeal hpm)

end GlobalTheory.LocalHomExtension
end

section

namespace GlobalTheory

theorem exists_mem_valuation_le_of_mem_span {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {M : Type} [AddCommGroup M]
    [Module O M] (A : Set M) (φ : M →ₗ[O] O) {x : M} (hx : x ∈ Submodule.span O A)
    (h0 : v (algebraMap O C (φ x)) ≠ 0) :
    ∃ a ∈ A, v (algebraMap O C (φ x)) ≤ v (algebraMap O C (φ a)) := by
  by_contra hne
  push Not at hne
  have key : ∀ y ∈ Submodule.span O A,
      v (algebraMap O C (φ y)) < v (algebraMap O C (φ x)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem a ha => exact hne a ha
    | zero => simpa using pos_iff_ne_zero.mpr h0
    | add a b _ _ ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact v.map_add_lt ha hb
    | smul o a _ ha =>
      rw [map_smul, smul_eq_mul, map_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one o)) ha
  exact lt_irrefl _ (key x hx)

theorem exists_leading_minors_ge_of_le_rank {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {r : ℕ} (A : Set (Fin r → O))
    {c : O} (hc : c ≠ 0) (hA : ∀ x : Fin r → O, c • x ∈ Submodule.span O A) :
    ∀ n : ℕ, n ≤ r → ∃ t : ℕ → Fin r → O, (∀ i, i < n → t i ∈ A) ∧
      ∀ (m : ℕ) (hm : m ≤ r), m ≤ n → v (algebraMap O C c) ^ m ≤
        v (algebraMap O C (Matrix.of fun a i : Fin m => t i (Fin.castLE hm a)).det) := by
  have hvc : v (algebraMap O C c) ≠ 0 := by
    rw [Ne, v.zero_iff]
    intro h
    exact hc (hv.hom_inj (by rw [h, map_zero]))
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    intro m hm h0
    obtain rfl : m = 0 := Nat.le_zero.mp h0
    simp
  | succ n ih =>
    intro hn
    obtain ⟨t, htA, ht⟩ := ih (Nat.le_of_succ_le hn)
    let coef : Fin (n + 1) → O := fun a => (-1) ^ ((a : ℕ) + n) *
      (Matrix.of fun b i : Fin n => t i (Fin.castLE hn (a.succAbove b))).det
    let φ : (Fin r → O) →ₗ[O] O :=
      ∑ a : Fin (n + 1), coef a • LinearMap.proj (Fin.castLE hn a)
    have hφ : ∀ x, φ x = ∑ a : Fin (n + 1), coef a * x (Fin.castLE hn a) := by
      intro x
      simp [φ, LinearMap.sum_apply]
    have hdet : ∀ x, (Matrix.of fun a i : Fin (n + 1) =>
        Function.update t n x i (Fin.castLE hn a)).det = φ x := by
      intro x
      rw [hφ, Matrix.det_succ_column _ (Fin.last n)]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : (Matrix.of fun a i : Fin (n + 1) =>
          Function.update t n x i (Fin.castLE hn a)).submatrix a.succAbove
          (Fin.last n).succAbove =
          Matrix.of fun b i : Fin n => t i (Fin.castLE hn (a.succAbove b)) := by
        ext b i
        simp [Function.update_of_ne (Nat.ne_of_lt i.isLt)]
      rw [this]
      simp only [coef, Matrix.of_apply, Fin.val_last, Function.update_self]
      ring
    have hval : φ (c • Pi.single (Fin.castLE hn (Fin.last n)) 1) =
        c * (Matrix.of fun a i : Fin n => t i (Fin.castLE (Nat.le_of_succ_le hn) a)).det := by
      rw [map_smul, smul_eq_mul, hφ, Finset.sum_eq_single (Fin.last n)]
      · congr 1
        simp only [coef, Pi.single_eq_same, mul_one, Fin.val_last, Fin.succAbove_last]
        rw [← two_mul, pow_mul]
        simp only [even_two, Even.neg_pow, one_pow, one_mul]
        rfl
      · intro b _ hb
        rw [Pi.single_eq_of_ne (fun h => hb (Fin.castLE_injective hn h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hlow : v (algebraMap O C c) ^ (n + 1) ≤
        v (algebraMap O C (φ (c • Pi.single (Fin.castLE hn (Fin.last n)) 1))) := by
      rw [hval, map_mul, map_mul, pow_succ']
      exact mul_le_mul_right (ht n _ le_rfl) _
    obtain ⟨a, haA, ha⟩ := exists_mem_valuation_le_of_mem_span v hv A φ (hA _)
      (ne_of_gt (lt_of_lt_of_le (pow_pos (pos_iff_ne_zero.mpr hvc) _) hlow))
    refine ⟨Function.update t n a, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · rw [Function.update_of_ne (Nat.ne_of_lt h)]
        exact htA i h
      · rw [Function.update_self]
        exact haA
    · intro m hm hmn
      rcases Nat.lt_or_eq_of_le hmn with h | rfl
      · have h' : m ≤ n := Nat.lt_succ_iff.mp h
        have : (Matrix.of fun b i : Fin m => Function.update t n a i (Fin.castLE hm b)) =
            Matrix.of fun b i : Fin m => t i (Fin.castLE hm b) := by
          ext b i
          simp [Function.update_of_ne (Nat.ne_of_lt (lt_of_lt_of_le i.isLt h'))]
        rw [this]
        exact ht m hm h'
      · rw [hdet]
        exact hlow.trans ha

theorem exists_leading_minors_ge :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
      v.Integers O → ∀ (r : ℕ) (A : Set (Fin r → O)) (c : O), c ≠ 0 →
      (∀ x : Fin r → O, c • x ∈ Submodule.span O A) →
      ∃ t : Fin r → Fin r → O, (∀ i, t i ∈ A) ∧ ∀ s : Fin r,
        v (algebraMap O C c) ^ (s.val + 1) ≤
          v (algebraMap O C (Matrix.of fun a i : Fin (s.val + 1) =>
            t (Fin.castLE s.isLt i) (Fin.castLE s.isLt a)).det) := by
  intro C _ v O _ _ hv r A c hc hA
  obtain ⟨t, htA, ht⟩ := exists_leading_minors_ge_of_le_rank v hv A hc hA r le_rfl
  exact ⟨fun i => t i, fun i => htA i i.isLt, fun s => ht (s.val + 1) s.isLt s.isLt⟩

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_matrix_fix_type_kill {O A : Type} [CommRing O] {d : ℕ}
    (ρ : A → Matrix (Fin d) (Fin d) O) {T : Type} [DecidableEq T] {r : T → ℕ} (σ : T → A → O)
    (u : (Σ t : T, Fin (r t)) → Fin d → O)
    (hsep : ∀ t t', t ≠ t' → ∃ a, IsUnit (σ t a - σ t' a))
    (heig : ∀ a l, (ρ a).mulVec (u l) = σ l.1 a • u l) (t₀ : T) (S : Finset T) (hS : t₀ ∉ S) :
    ∃ P : Matrix (Fin d) (Fin d) O, (∀ l, l.1 = t₀ → P.mulVec (u l) = u l) ∧
      (∀ l, l.1 ∈ S → P.mulVec (u l) = 0) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun l _ => Matrix.one_mulVec _, fun l hl => absurd hl (by simp)⟩
  | insert t S htS ih =>
    obtain ⟨P, hP1, hP2⟩ := ih (fun h => hS (Finset.mem_insert_of_mem h))
    have hne : t₀ ≠ t := fun h => hS (h ▸ Finset.mem_insert_self t S)
    obtain ⟨a, c, hc⟩ := hsep t₀ t hne
    have key : ∀ l, (P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O)))).mulVec (u l)
        = ((↑c⁻¹ : O) * (σ l.1 a - σ t a)) • P.mulVec (u l) := by
      intro l
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, heig, ← sub_smul, smul_smul, Matrix.mulVec_smul]
    refine ⟨P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O))),
      fun l hl => ?_, fun l hl => ?_⟩
    · rw [key, hP1 l hl, hl, ← hc, Units.inv_mul, one_smul]
    · rw [key]
      rcases Finset.mem_insert.mp hl with h | h
      · rw [h, sub_self, mul_zero, zero_smul]
      · rw [hP2 l h, smul_zero]

theorem exists_dual_forms_of_separated_types :
    ∀ (O A : Type) [CommRing O] (d : ℕ) (ρ : A → Matrix (Fin d) (Fin d) O) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (σ : T → A → O) (u : (Σ t : T, Fin (r t)) → Fin d → O), (∀ t t', t ≠ t' → ∃ a, IsUnit (σ t a - σ t' a)) → (∀ a l, (ρ a).mulVec (u l) = σ l.1 a • u l) → (∀ t, ∃ lam : Fin (r t) → Fin d → O, ∀ i i', ∑ s, lam i s * u ⟨t, i'⟩ s = if i = i' then 1 else 0) → ∃ lam : (Σ t : T, Fin (r t)) → Fin d → O, ∀ l l', ∑ s, lam l s * u l' s = if l = l' then 1 else 0 := by
  intro O A _ d ρ T _ _ r σ u hsep heig hdual
  choose lam hlam using hdual
  choose P hP1 hP2 using fun t₀ : T =>
    exists_matrix_fix_type_kill ρ σ u hsep heig t₀ (Finset.univ.erase t₀) (by simp)
  refine ⟨fun l => Matrix.vecMul (lam l.1 l.2) (P l.1), ?_⟩
  rintro ⟨t, i⟩ ⟨t', i'⟩
  change Matrix.vecMul (lam t i) (P t) ⬝ᵥ u ⟨t', i'⟩ = _
  rw [← Matrix.dotProduct_mulVec]
  by_cases h : t' = t
  · subst h
    rw [hP1 t' ⟨t', i'⟩ rfl]
    have := hlam t' i i'
    simpa [dotProduct] using this
  · rw [hP2 t ⟨t', i'⟩ (by simpa using h), dotProduct_zero, if_neg]
    intro h'
    exact h (congrArg Sigma.fst h').symm

end GlobalTheory
end
