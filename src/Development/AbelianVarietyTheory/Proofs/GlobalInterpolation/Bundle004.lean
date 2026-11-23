module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.TwoRealCharacters

theorem hasSum_re_neg_logDeriv (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hσ : 1 < σ) :
    HasSum (fun n : ℕ => (χ n).re * (vonMangoldt n / (n : ℝ) ^ σ))
      (-(deriv (LFunction χ) σ / LFunction χ σ).re) := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have h := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs] at h
  have h' := Complex.hasSum_re h
  convert (preTransparency := .reducible) h' using 1
  · funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast n,
        ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp [Pi.mul_apply, Complex.div_ofReal_re, mul_div_assoc]
  · rw [neg_div, Complex.neg_re]

theorem re_sum_nonneg (q : ℕ) (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (a : ZMod q) :
    0 ≤ ((1 : DirichletCharacter ℂ q) a).re + (χ a).re + (ψ a).re + ((χ * ψ) a).re := by
  by_cases ha : IsUnit a
  · have hsq : ∀ φ : DirichletCharacter ℂ q, φ ^ 2 = 1 → φ a = 1 ∨ φ a = -1 := by
      intro φ hφ
      apply mul_self_eq_one_iff.mp
      have hval := congrArg (fun ξ : DirichletCharacter ℂ q => ξ a) hφ
      simp only [MulChar.pow_apply' φ two_ne_zero, MulChar.one_apply ha] at hval
      rw [← pow_two]
      exact hval
    rw [MulChar.one_apply ha, MulChar.coeToFun_mul, Pi.mul_apply]
    rcases hsq χ hχ with h1 | h1 <;> rcases hsq ψ hψ with h2 | h2 <;> norm_num [h1, h2]
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha,
      MulChar.map_nonunit _ ha]
    simp

theorem neg_sum_logDeriv_nonneg : ∀ (q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q) (σ : ℝ), χ ^ 2 = 1 → ψ ^ 2 = 1 → 1 < σ → 0 ≤ -((deriv (LFunction (1 : DirichletCharacter ℂ q)) σ / LFunction (1 : DirichletCharacter ℂ q) σ).re + (deriv (LFunction χ) σ / LFunction χ σ).re + (deriv (LFunction ψ) σ / LFunction ψ σ).re + (deriv (LFunction (χ * ψ)) σ / LFunction (χ * ψ) σ).re) := by
  intro q _ χ ψ σ hχ hψ hσ
  have h := (((hasSum_re_neg_logDeriv q 1 σ hσ).add (hasSum_re_neg_logDeriv q χ σ hσ)).add
    (hasSum_re_neg_logDeriv q ψ σ hσ)).add (hasSum_re_neg_logDeriv q (χ * ψ) σ hσ)
  have hnn := h.nonneg fun n => by
    have h1 := re_sum_nonneg q χ ψ hχ hψ (n : ZMod q)
    have h2 : 0 ≤ vonMangoldt n / (n : ℝ) ^ σ :=
      div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
    have h3 := mul_nonneg h1 h2
    linarith
  linarith

end GlobalTheory.TwoRealCharacters
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LGrowth

open Filter Topology Asymptotics

theorem norm_partialSum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤ q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hper : ∀ m : ℕ, ∑ k ∈ Finset.range q, χ ((m + k : ℕ) : ZMod q) = 0 := by
    intro m
    have h0 : ∑ a : ZMod q, χ a = 0 := χ.sum_eq_zero_of_ne_one hχ
    rw [← h0, ← Equiv.sum_comp (Equiv.addLeft (m : ZMod q))]
    refine Finset.sum_bij (fun k _ => (k : ZMod q)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb hab
      have := (ZMod.natCast_eq_natCast_iff' a b q).1 hab
      rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
        at this
    · intro b _
      exact ⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
    · intro a _
      simp
  have hI : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)
      = ∑ k ∈ Finset.range n, χ ((1 + k : ℕ) : ZMod q) := by
    intro n
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp
  rw [hI]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n q with h | h
    · refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => χ.norm_le_one _).trans ?_
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast h.le
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
      rw [Finset.sum_range_add]
      have := hper (1 + m)
      simp only [← add_assoc]
      rw [this, add_zero]
      exact ih m (by omega)

section General

variable {f : ℕ → ℂ} {C : ℝ}

noncomputable def summatory (f : ℕ → ℂ) (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k

theorem measurable_summatory (f : ℕ → ℂ) : Measurable (summatory f) :=
  (measurable_from_top (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor

theorem summatory_eq_zero {t : ℝ} (ht : t < 1) : summatory f t = 0 := by
  simp [summatory, Nat.floor_eq_zero.2 ht]

theorem mellin_summatory (s : ℂ) :
    mellin (summatory f) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin, setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (s := Set.Ici (1 : ℝ)) (fun t ht => Set.mem_Ioi.2 (zero_lt_one.trans_le (Set.mem_Ici.1 ht))), integral_Ici_eq_integral_Ioi]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [summatory, smul_eq_mul]
    rw [mul_comm]
    congr 2
    ring
  · intro t ht
    rw [summatory_eq_zero (not_le.1 ht.2), smul_zero]

theorem differentiableAt_mellin_summatory (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => mellin (summatory f) (-z)) s := by
  have h : DifferentiableAt ℂ (mellin (summatory f)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      refine (locallyIntegrable_const C).mono (measurable_summatory f).aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => (hC _).trans (Real.le_norm_self C)
    · refine IsBigO.of_bound C (Eventually.of_forall fun t => ?_)
      simpa [summatory] using hC ⌊t⌋₊
    · simpa using hs
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht
      simp [summatory_eq_zero ht]
    · simp
  exact h.comp s differentiableAt_id.neg

theorem norm_mellin_summatory_le (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    ‖mellin (summatory f) (-s)‖ ≤ C / s.re := by
  rw [mellin_summatory]
  have hlt : -(s.re + 1) < -1 := by linarith
  refine (norm_integral_le_of_norm_le (g := fun t : ℝ => C * t ^ (-(s.re + 1)))
    ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul C) ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.rpow_nonneg ht0.le _)
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt zero_lt_one, Real.one_rpow]
    refine le_of_eq ?_
    have : -(s.re + 1) + 1 = -s.re := by ring
    rw [this]
    field_simp

end General

theorem LFunction_eq_mul_mellin (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = s * mellin (summatory fun n => χ (n : ZMod q)) (-s) := by
  have hC := norm_partialSum_le q χ hχ
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have h1 : AnalyticOnNhd ℂ (LFunction χ) {z : ℂ | 0 < z.re} :=
    (differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
  have h2 : AnalyticOnNhd ℂ (fun z => z * mellin (summatory fun n => χ (n : ZMod q)) (-z))
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    exact (differentiableAt_id.mul
      (differentiableAt_mellin_summatory hC hz)).differentiableWithinAt
  refine h1.eqOn_of_preconnected_of_eventuallyEq h2 (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 2) (by simp) ?_ hs
  have hV : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hV.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by simp)] with z hz
  rw [LFunction_eq_LSeries χ hz, mellin_summatory]
  refine LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hz)
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz) ?_
  refine IsBigO.of_bound q (Eventually.of_forall fun n => ?_)
  simpa using hC n

theorem norm_LFunction_le : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ s : ℂ, 0 < s.re → ‖LFunction χ s‖ ≤ q * ‖s‖ / s.re := by
  intro q _ χ hχ s hs
  rw [LFunction_eq_mul_mellin q χ hχ hs, norm_mul]
  refine (mul_le_mul_of_nonneg_left
    (norm_mellin_summatory_le (norm_partialSum_le q χ hχ) hs) (norm_nonneg s)).trans ?_
  exact le_of_eq (by ring)

end GlobalTheory.LGrowth
end

section

namespace GlobalTheory.ZetaFractionalIntegral

open MeasureTheory Set Filter Asymptotics

lemma zeta_eq_mul_integral_floor {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Set.Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (fun _ : ℕ ↦ (1 : ℝ)) k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.isBigO_of_le _ fun n ↦ ?_
    simp
  have key := LSeries_eq_mul_integral_of_nonneg (fun _ ↦ (1 : ℝ)) zero_le_one hs hO (fun _ ↦ zero_le_one)
  have e1 : LSeries (fun n : ℕ ↦ (((fun _ : ℕ ↦ (1 : ℝ)) n : ℝ) : ℂ)) s = riemannZeta s := by
    rw [← LSeries_one_eq_riemannZeta hs]
    congr 1
  rw [← e1, key]
  congr 2
  funext t
  simp

lemma integrableOn_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi 1) := integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) one_pos

lemma integrableOn_fract_mul {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hg : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re, Complex.add_re, Complex.one_re]; linarith) one_pos
  refine MeasureTheory.Integrable.mono hg (((Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable).mul
    hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  have : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1.le
  calc ‖((Int.fract t : ℝ) : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖ ≤ 1 * ‖(t : ℂ) ^ (-(s + 1))‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = ‖(t : ℂ) ^ (-(s + 1))‖ := one_mul _

theorem zeta_eq_sub_integral_fract :
    (let d1 : ℂ → ℂ := @(fun (s : ℂ) ↦ ∫ (t : ℝ) in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (↑t : ℂ) ^ (-(s + (1 : ℂ)))); ∀ {s : ℂ}, (1 : ℝ) < Complex.re s → riemannZeta s = s / (s - (1 : ℂ)) - s * d1 s) := by
  intro d1 s hs
  simp only [d1]
  have hA := integrableOn_cpow_neg hs
  have hB := integrableOn_fract_mul hs
  have hsplit : ∫ t in Set.Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s)) -
        ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← integral_sub hA hB]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
      rw [Int.self_sub_fract, natCast_floor_eq_intCast_floor ht0.le]
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [show -s = -(s + 1) + 1 by ring, Complex.cpow_add _ _ (by exact_mod_cast ht0.ne'), Complex.cpow_one,
        mul_comm]
    have hfl' : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, hfl, Complex.ofReal_sub]
    rw [hpow, hfl']
    ring
  have hI : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) one_pos, Complex.ofReal_one,
      Complex.one_cpow, show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]
  rw [zeta_eq_mul_integral_floor hs, hsplit, hI]
  ring

end GlobalTheory.ZetaFractionalIntegral
end

section

namespace GlobalTheory.ConductorAdicCompletion

theorem eq_one_of_pow_near_one (z : ℂ) (h : ∀ k : ℕ, ‖z ^ k - 1‖ ≤ 1 / 2) : z = 1 := by
  by_contra hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1

  have hre : ∀ k : ℕ, 1 / 2 ≤ (z ^ k).re := by
    intro k
    have h2 := (Complex.abs_re_le_norm (z ^ k - 1)).trans (h k)
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_le.mp h2).1
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hsum : ∑ k ∈ Finset.range N, z ^ k = (z ^ N - 1) / (z - 1) := geom_sum_eq hz N
  have hlow : (N : ℝ) / 2 ≤ (∑ k ∈ Finset.range N, z ^ k).re := by
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ k ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun k _ => hre k
  have hup : (∑ k ∈ Finset.range N, z ^ k).re ≤ 1 / 2 / ‖z - 1‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [hsum, norm_div]
    exact div_le_div_of_nonneg_right (h N) (norm_nonneg _)
  have he : 1 / 2 / ‖z - 1‖ = (1 / ‖z - 1‖) / 2 := by ring
  linarith

theorem exists_ball_trivial {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous ψ) :
    ∃ m : ℤ, ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1 := by
  have hmem : {x : K | ‖ψ x - 1‖ < 1 / 2} ∈ nhds (0 : K) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (by fun_prop) continuous_const
    · simp
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hmem
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]
    exact (map_ne_zero _).mpr γ.ne_zero
  refine ⟨WithZero.log g - 1, fun x hx => ?_⟩
  have hlt : WithZero.exp (WithZero.log g - 1) < g :=
    (WithZero.lt_log_iff_exp_lt hg0).mp (by omega)
  apply eq_one_of_pow_near_one
  intro k
  rw [← AddChar.map_nsmul_eq_pow]
  have hk : Valued.v (k • x) ≤ WithZero.exp (WithZero.log g - 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul]
      exact Valuation.map_add_le _ ih hx
  have : k • x ∈ {x : K | ‖ψ x - 1‖ < 1 / 2} := by
    apply hγ
    exact (Valuation.restrict_lt_iff_lt_embedding _).mpr (hk.trans_lt hlt)
  exact le_of_lt this

theorem exists_conductor {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m : ℤ => ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1)
    ⟨WithZero.log (Valued.v t₀ : WithZero (Multiplicative ℤ)), fun m hm => by
      have h1 : WithZero.exp m < Valued.v t₀ := lt_of_not_ge fun h => ht₀ (hm _ h)
      exact ((WithZero.lt_log_iff_exp_lt (ne_zero_of_lt h1)).mpr h1).le⟩
    (exists_ball_trivial ψ hc)
  refine ⟨n, fun t => ⟨fun h => ?_, fun h s hs => ?_⟩⟩
  · by_contra hlt
    have h1 : WithZero.exp n < Valued.v t := lt_of_not_ge hlt
    have hv0 : (Valued.v t : WithZero (Multiplicative ℤ)) ≠ 0 := ne_zero_of_lt h1
    have ht : t ≠ 0 := fun h0 => hv0 (by simp [h0])
    have h2 := (WithZero.lt_log_iff_exp_lt hv0).mpr h1
    have h3 := hmax (WithZero.log (Valued.v t : WithZero (Multiplicative ℤ))) (fun x hx => by
      rw [WithZero.exp_log hv0] at hx
      have h4 := h (x / t) (by
        rw [map_div₀]
        exact div_le_one_of_le₀ hx zero_le)
      rwa [mul_div_cancel₀ _ ht] at h4)
    omega
  · apply hn
    rw [map_mul]
    exact (mul_le_of_le_one_right' hs).trans h

theorem exists_conductor_adicCompletion :
    ∀ (F : Type) [Field F] [NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (ψ : AddChar (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) ℂ),
      Continuous (⇑ψ : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v → ℂ) →
      (∀ t, ‖ψ t‖ = (1 : ℝ)) → (∃ t, ψ t ≠ (1 : ℂ)) →
      ∃ n : ℤ, ∀ t : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v,
        (∀ s ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v,
          ψ (t * s) = (1 : ℂ)) ↔
        (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v →
          WithZero (Multiplicative ℤ)) t ≤ WithZero.exp n := by
  intro F _ _ v ψ hc _ hne
  exact exists_conductor ψ hc hne

end GlobalTheory.ConductorAdicCompletion
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Polynomial

namespace GlobalTheory


open Polynomial in
theorem exists_prod_abs_sub_ge_on_segment : ∀ (N : ℕ) (x : Fin N → ℝ) (a δ : ℝ), 0 < δ →
    ∃ r : ℝ, a ≤ r ∧ r ≤ a + δ ∧ (δ / (2 * Real.exp 1)) ^ N ≤ ∏ i, |r - x i| := by
  intro N x a δ hδ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨a, le_rfl, by linarith, by simp⟩
  by_contra hcon
  push Not at hcon
  have he : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he0 : (0 : ℝ) < Real.exp 1 := by linarith
  set m : ℝ := δ / (2 * Real.exp 1) with hm
  have hm0 : 0 < m := by positivity
  let P : ℝ[X] := ∏ i : Fin N, (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))
  have hlc : P.leadingCoeff = Real.exp 1 ^ N := by
    simp only [P, leadingCoeff_prod, leadingCoeff_linear he0.ne']
    simp
  have hdeg : P.degree ≤ N := by
    have : P.degree = ∑ _i : Fin N, (1 : WithBot ℕ) := by
      simp only [P, degree_prod, degree_linear he0.ne']
    rw [this]; simp
  have hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1 := by
    intro t ht
    have h1 := hcon (a + δ / 2 + δ / 2 * t) (by nlinarith [ht.1]) (by nlinarith [ht.2])
    have h2 : |P.eval t| = (∏ i, |a + δ / 2 + δ / 2 * t - x i|) / m ^ N := by
      simp only [P, eval_prod, Finset.abs_prod]
      have : ∀ i : Fin N, |eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))|
          = |a + δ / 2 + δ / 2 * t - x i| / m := by
        intro i
        have : eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))
            = (a + δ / 2 + δ / 2 * t - x i) / m := by
          simp only [eval_add, eval_mul, eval_C, eval_X, hm]
          field_simp
          ring
        rw [this, abs_div, abs_of_pos hm0]
      simp only [this, Finset.prod_div_distrib]
      simp
    rw [h2, div_le_one (by positivity)]
    exact h1.le
  have h3 := Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one hdeg hb
  rw [hlc] at h3
  have h4 : (2 : ℝ) ^ (N - 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h5 : (2 : ℝ) ^ N < Real.exp 1 ^ N := pow_lt_pow_left₀ he (by norm_num) hN.ne'
  linarith

end GlobalTheory
end
