module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.NumberTheory.ZetaValues
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped ComplexConjugate

private lemma arSum_term (r : ℕ) (t : ℝ) (ht : (r : ℝ) + 1 ≤ t) (x y : ℝ) (n₁ m : ℕ) (hx : 0 ≤ x)
    (hn : 1 ≤ n₁ * m ^ 2) (h : x ≤ y * (m : ℝ) ^ r) :
    x ^ 2 / ((n₁ * m ^ 2 : ℕ) : ℝ) ^ t ≤ y ^ 2 / (n₁ : ℝ) ^ t * (1 / (m : ℝ) ^ 2) := by
  have hn1 : 1 ≤ n₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hn1r : (1:ℝ) ≤ n₁ := by exact_mod_cast hn1
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx2 : x ^ 2 ≤ y ^ 2 * ((m:ℝ) ^ r) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx h 2
  have hM : (m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2 ≤ ((m:ℝ) ^ 2) ^ t := by
    have h1 : ((m:ℝ) ^ 2) ^ (r + 1) = (m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2 := by ring
    rw [← h1, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by push_cast; linarith)
  have hcast : ((n₁ * m ^ 2 : ℕ) : ℝ) ^ t = (n₁ : ℝ) ^ t * ((m:ℝ) ^ 2) ^ t := by
    push_cast
    exact Real.mul_rpow (by positivity) (by positivity)
  have hN : (0:ℝ) < (n₁ : ℝ) ^ t := Real.rpow_pos_of_pos (by linarith) t
  have hm0 : (0:ℝ) < (m:ℝ) := by linarith
  rw [hcast]
  calc x ^ 2 / ((n₁ : ℝ) ^ t * ((m:ℝ) ^ 2) ^ t)
      ≤ (y ^ 2 * ((m:ℝ) ^ r) ^ 2) / ((n₁ : ℝ) ^ t * ((m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2)) :=
        div_le_div₀ (by positivity) hx2 (by positivity) (mul_le_mul_of_nonneg_left hM hN.le)
    _ = y ^ 2 / (n₁ : ℝ) ^ t * (1 / (m:ℝ) ^ 2) := by
        field_simp

theorem UpperTheory.V.Af.Rs.arSum :
    UpperTheory.V.Af.Rs.ArSum := by
  intro r t a b P ht hP h3 hsu
  have ht0 : 0 < t := by have : (0:ℝ) ≤ r := Nat.cast_nonneg r; linarith
  set u : ℕ → ℝ := fun n => ‖a n‖ ^ 2 / (n:ℝ) ^ t with hu
  set w : ℕ → ℂ := fun n => starRingEnd ℂ (b n) * a n / (((n:ℝ) ^ t : ℝ) : ℂ) with hw
  have h3' : ∀ n : ℕ, ∃ q : ℕ × ℕ, 1 ≤ n → a n ≠ 0 →
      q.1 ∈ P ∧ n = q.1 * q.2 ^ 2 ∧ ‖a n‖ ≤ ‖a q.1‖ * (q.2:ℝ) ^ r ∧ ‖b n‖ ≤ ‖a q.1‖ * (q.2:ℝ) ^ r := by
    intro n
    by_cases hc : 1 ≤ n ∧ a n ≠ 0
    · obtain ⟨n₁, hn₁, m, h1, h2, h4⟩ := h3 n hc.1 hc.2
      exact ⟨(n₁, m), fun _ _ => ⟨hn₁, h1, h2, h4⟩⟩
    · exact ⟨(0, 0), fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose φ hφ using h3'
  set Q : Set ℕ := {n | n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0} with hQ
  set c : ℕ → ℝ := ({m | 2 ≤ m} : Set ℕ).indicator (fun m => 1 / (m:ℝ) ^ 2) with hc
  set g : ℕ × ℕ → ℝ := fun q => P.indicator u q.1 * c q.2 with hg
  set G : ℕ → ℝ := Q.indicator (fun n => g (φ n)) with hG
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [hu]; positivity
  have hc0 : ∀ m, 0 ≤ c m := fun m => by
    simp only [hc]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _
  have hPu : Summable (P.indicator u) := hsu.indicator P
  have hzeta : Summable (fun m : ℕ => 1 / (m:ℝ) ^ 2) := hasSum_zeta_two.summable
  have hcs : Summable c := hzeta.indicator _
  have hgs : Summable g :=
    summable_mul_of_summable_norm (f := P.indicator u) (g := c)
      (summable_norm_iff.mpr hPu) (summable_norm_iff.mpr hcs)
  have hg0 : ∀ q, 0 ≤ g q := fun q =>
    mul_nonneg (Set.indicator_nonneg (fun n _ => hu0 n) _) (hc0 _)
  have hinj : Function.Injective (fun x : Q => φ x.1) := by
    intro x y hxy
    have hxQ : x.1 ∉ P ∧ 1 ≤ x.1 ∧ a x.1 ≠ 0 := x.2
    have hyQ : y.1 ∉ P ∧ 1 ≤ y.1 ∧ a y.1 ≠ 0 := y.2
    have hx := hφ x.1 hxQ.2.1 hxQ.2.2
    have hy := hφ y.1 hyQ.2.1 hyQ.2.2
    apply Subtype.ext
    simp only at hxy
    rw [hx.2.1, hy.2.1, hxy]
  have hGs : Summable G := by
    rw [hG, ← summable_subtype_iff_indicator]
    exact hgs.comp_injective hinj
  have hc34 : ∑' m, c m ≤ 3 / 4 := by
    have e1 := hzeta.sum_add_tsum_nat_add 2
    have e2 := hcs.sum_add_tsum_nat_add 2
    have s2 : ∑ i ∈ Finset.range 2, c i = 0 := by simp [Finset.sum_range_succ, hc]
    have s1 : ∑ i ∈ Finset.range 2, (1 / ((i:ℕ):ℝ) ^ 2) = 1 := by simp [Finset.sum_range_succ]
    have e3 : (fun i => c (i + 2)) = (fun i => 1 / (((i + 2 : ℕ)) : ℝ) ^ 2) := by
      funext i
      simp only [hc]
      rw [Set.indicator_of_mem (show i + 2 ∈ {m : ℕ | 2 ≤ m} by simp)]
    rw [s2, zero_add, e3] at e2
    rw [s1, hasSum_zeta_two.tsum_eq] at e1
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have hpi2 : Real.pi ^ 2 < 9.93 := by nlinarith
    rw [← e2]
    linarith
  have hGle : ∑' n, G n ≤ (∑' n, P.indicator u n) * (3 / 4) := by
    rw [hG, ← tsum_subtype]
    calc ∑' x : Q, g (φ x) ≤ ∑' q, g q := tsum_comp_le_tsum_of_inj hgs hg0 hinj
      _ = (∑' n, P.indicator u n) * ∑' m, c m := by
          exact (tsum_mul_tsum_of_summable_norm (f := P.indicator u) (g := c)
            (summable_norm_iff.mpr hPu) (summable_norm_iff.mpr hcs)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hc34
          (tsum_nonneg (fun n => Set.indicator_nonneg (fun n _ => hu0 n) _))
  have hpt : ∀ n, ‖w n‖ ≤ P.indicator u n + G n ∧
      6 * P.indicator u n - 8 * G n ≤ 7 * (w n).re - u n := by
    intro n
    by_cases hn : n ∈ P
    · have hGn : G n = 0 := by
        simp only [hG]
        have hnQ : n ∉ Q := fun h => by
          have h' : n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0 := h
          exact h'.1 hn
        exact Set.indicator_of_notMem hnQ _
      have hPn : P.indicator u n = u n := Set.indicator_of_mem hn u
      have hwn : w n = ((u n : ℝ) : ℂ) := by
        simp only [hw, hu]
        rw [hP n hn, Complex.conj_mul']
        push_cast
        ring
      rw [hGn, hPn, hwn, Complex.norm_real, Real.norm_of_nonneg (hu0 n), Complex.ofReal_re]
      constructor <;> linarith [hu0 n]
    · have hPn : P.indicator u n = 0 := Set.indicator_of_notMem hn u
      by_cases hq : 1 ≤ n ∧ a n ≠ 0
      · have hφn := hφ n hq.1 hq.2
        have hGn : G n = P.indicator u (φ n).1 * c (φ n).2 := by
          simp only [hG, hg]
          exact Set.indicator_of_mem (show n ∈ Q from ⟨hn, hq.1, hq.2⟩) _
        rcases hφq : φ n with ⟨n₁, m⟩
        rw [hφq] at hφn hGn
        obtain ⟨hn₁P, hnm, hA, hB⟩ := hφn
        simp only at hn₁P hnm hA hB hGn
        rcases Nat.lt_or_ge m 2 with hlt | hm2
        · exfalso
          interval_cases m
          · simp at hnm
            omega
          · simp at hnm
            exact hn (hnm ▸ hn₁P)
        have hc2 : c m = 1 / (m:ℝ) ^ 2 := by
          simp only [hc]
          exact Set.indicator_of_mem (show m ∈ {m : ℕ | 2 ≤ m} from hm2) _
        have hPn1 : P.indicator u n₁ = u n₁ := Set.indicator_of_mem hn₁P u
        rw [hc2, hPn1] at hGn
        have h1n : 1 ≤ n₁ * m ^ 2 := hnm ▸ hq.1
        have k1 := arSum_term r t ht ‖a n‖ ‖a n₁‖ n₁ m (norm_nonneg _) h1n hA
        have k2 := arSum_term r t ht ‖b n‖ ‖a n₁‖ n₁ m (norm_nonneg _) h1n hB
        rw [← hnm] at k1 k2
        have hnt : 0 < (n:ℝ) ^ t := Real.rpow_pos_of_pos (by exact_mod_cast hq.1) t
        have hwn : ‖w n‖ = ‖b n‖ * ‖a n‖ / (n:ℝ) ^ t := by
          simp only [hw]
          rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hnt.le]
        have hw2 : ‖w n‖ ≤ G n := by
          rw [hwn, hGn]
          have hab : ‖b n‖ * ‖a n‖ ≤ (‖a n‖ ^ 2 + ‖b n‖ ^ 2) / 2 := by
            nlinarith [sq_nonneg (‖a n‖ - ‖b n‖)]
          calc ‖b n‖ * ‖a n‖ / (n:ℝ) ^ t ≤ ((‖a n‖ ^ 2 + ‖b n‖ ^ 2) / 2) / (n:ℝ) ^ t := by gcongr
            _ = (‖a n‖ ^ 2 / (n:ℝ) ^ t + ‖b n‖ ^ 2 / (n:ℝ) ^ t) / 2 := by ring
            _ ≤ _ := by simp only [hu]; linarith
        have hun : u n ≤ G n := by
          rw [hGn]
          simp only [hu]
          exact k1
        have hre : -‖w n‖ ≤ (w n).re := by
          have := Complex.abs_re_le_norm (w n)
          linarith [neg_abs_le (w n).re]
        rw [hPn]
        constructor <;> linarith
      · have hGn : G n = 0 := by
          simp only [hG]
          have hnQ : n ∉ Q := fun h => by
            have h' : n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0 := h
            exact hq ⟨h'.2.1, h'.2.2⟩
          exact Set.indicator_of_notMem hnQ _
        have hz : w n = 0 ∧ u n = 0 := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            simp [hw, hu, Real.zero_rpow (ne_of_gt ht0)]
          · have han : a n = 0 := by
              by_contra h
              exact hq ⟨h0, h⟩
            simp [hw, hu, han]
        rw [hPn, hGn, hz.1, hz.2]
        simp
  have hws : Summable w := Summable.of_norm_bounded (hPu.add hGs) (fun n => (hpt n).1)
  have hres : Summable (fun n => (w n).re) :=
    Summable.of_norm_bounded (hPu.add hGs)
      (fun n => by rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hpt n).1)
  rw [Complex.re_tsum hws]
  have hD := Summable.tsum_le_tsum (fun n => (hpt n).2)
    ((hPu.mul_left 6).sub (hGs.mul_left 8)) ((hres.mul_left 7).sub hsu)
  rw [Summable.tsum_sub (hPu.mul_left 6) (hGs.mul_left 8),
    Summable.tsum_sub (hres.mul_left 7) hsu, Summable.tsum_mul_left 6 hPu,
    Summable.tsum_mul_left 8 hGs, Summable.tsum_mul_left 7 hres] at hD
  linarith [hGle]
end

section

theorem UpperTheory.V.Af.Rs.charEq2 :
    UpperTheory.V.Af.Rs.Core → UpperTheory.V.Af.Rs.Deplete → UpperTheory.V.Af.Rs.CharEq2 := by
  intro hCore hDep k N M _ _ hk χ ψ g h hev
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨B, hB⟩ := hev.bddAbove
  obtain ⟨L, hL⟩ : ∃ L, L = N * M * B.factorial := ⟨_, rfl⟩
  haveI : NeZero L := ⟨by
    rw [hL]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne M)) (Nat.factorial_ne_zero B)⟩
  haveI : NeZero (L * L) := ⟨Nat.mul_ne_zero (NeZero.ne L) (NeZero.ne L)⟩
  have hNL : N ∣ L := ⟨M * B.factorial, by rw [hL]; ring⟩
  have hML : M ∣ L := ⟨N * B.factorial, by rw [hL]; ring⟩
  obtain ⟨χ1, g1, hg1⟩ := hDep k N L hk hNL χ g
  obtain ⟨χ2, h1, hh1⟩ := hDep k M L hk hML ψ h
  have good : ∀ p, Nat.Prime p → ¬ p ∣ L → (h.a p = g.a p ∧ (starRingEnd ℂ) (g.a p) * χ p = g.a p ∧
      (starRingEnd ℂ) (h.a p) * ψ p = h.a p) := by
    intro p hp hpL
    by_contra hbad
    have hle : p ≤ B := hB (by simp only [Set.mem_setOf_eq]; exact fun H => hbad (H hp))
    exact hpL (hL ▸ Dvd.dvd.mul_left (Nat.dvd_factorial hp.pos hle) _)
  have hcore := hCore k (L * L) hk χ1 χ2 g1 h1 ?_ ?_
  · rw [Filter.eventually_cofinite]
    apply ((Finset.range (L + 1)).finite_toSet).subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    by_cases hpL : p ∣ L
    · simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne L)) hpL)
    · exfalso
      apply hp
      intro hpp
      rw [← ((hg1 p hpp).1 hpL).1, ← ((hh1 p hpp).1 hpL).1, hcore]
  · intro p hp
    by_cases hpL : p ∣ L
    · rw [(hg1 p hp).2 hpL, (hh1 p hp).2 hpL]
    · rw [((hh1 p hp).1 hpL).2, ((hg1 p hp).1 hpL).2]
      exact (good p hp hpL).1
  · intro p hp hne
    by_cases hpL : p ∣ L
    · exact (hg1 p hp).2 hpL
    · obtain ⟨e1, e2, e3⟩ := good p hp hpL
      rw [((hg1 p hp).1 hpL).2]
      by_contra ha
      apply hne
      rw [((hg1 p hp).1 hpL).1, ((hh1 p hp).1 hpL).1]
      rw [e1] at e3
      have hc : (starRingEnd ℂ) (g.a p) ≠ 0 := by simpa using ha
      exact mul_left_cancel₀ hc (e2.trans e3.symm)
end

section

open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

namespace UpperTheory.V.Af.Rs

private noncomputable def ex (n : ℕ) (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * n * x)

private theorem ex_norm (n : ℕ) (x : ℝ) : ‖ex n x‖ = 1 := by
  unfold ex
  have h : (2 * Real.pi * Complex.I * n * x : ℂ) = ((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem ex_cont (n : ℕ) : Continuous (ex n) := by unfold ex; fun_prop

private theorem ex_orth (m n : ℕ) : ∫ x in (0 : ℝ)..1, conj (ex m x) * ex n x = if m = n then 1 else 0 := by
  unfold ex
  have key : ∀ x : ℝ, conj (Complex.exp (2 * Real.pi * Complex.I * m * x)) *
      Complex.exp (2 * Real.pi * Complex.I * n * x) =
      Complex.exp ((2 * Real.pi * Complex.I * ((n : ℂ) - m)) * x) := by
    intro x
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
    ring
  simp_rw [key]
  split_ifs with hmn
  · subst hmn
    simp
  · have hc : (2 * Real.pi * Complex.I * ((n : ℂ) - m)) ≠ 0 := by
      have h1 : ((n : ℂ) - m) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast (Ne.symm hmn)
      have h2 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [h1, h2, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have e1 : Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) - m) * ((1 : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
      rw [← this]
      congr 1
      push_cast
      ring
    rw [e1]
    simp

private theorem pars_abs (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b) (F G : ℝ → ℂ)
    (hF : ∀ x, HasSum (fun n => a n * ex n x) (F x)) (hG : ∀ x, HasSum (fun n => b n * ex n x) (G x)) :
    HasSum (fun n => conj (b n) * a n) (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
  have han : Summable (fun n => ‖a n‖) := summable_norm_iff.mpr ha
  have hbn : Summable (fun n => ‖b n‖) := summable_norm_iff.mpr hb
  have hGc : Continuous G := by
    have e : G = fun x => ∑' n, b n * ex n x := funext fun x => (hG x).tsum_eq.symm
    rw [e]
    refine continuous_tsum (fun n => continuous_const.mul (ex_cont n)) hbn ?_
    intro n x
    rw [norm_mul, ex_norm, mul_one]
  have hGb : ∀ t, ‖G t‖ ≤ ∑' n, ‖b n‖ := by
    intro t
    rw [← (hG t).tsum_eq]
    have e : (fun n => ‖b n * ex n t‖) = fun n => ‖b n‖ := by
      funext n
      rw [norm_mul, ex_norm, mul_one]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · rw [e]; exact hbn
    · rw [e]
  have hC : ∀ n, ∫ x in (0 : ℝ)..1, conj (G x) * ex n x = conj (b n) := by
    intro n
    have hs : HasSum (fun m => ∫ x in (0 : ℝ)..1, conj (b m) * (conj (ex m x) * ex n x))
        (∫ x in (0 : ℝ)..1, conj (G x) * ex n x) := by
      refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun m _ => ‖b m‖)
        ?_ ?_ ?_ ?_ ?_
      · intro m
        exact (continuous_const.mul
          ((Complex.continuous_conj.comp (ex_cont m)).mul (ex_cont n))).aestronglyMeasurable
      · intro m
        refine Filter.Eventually.of_forall (fun t _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, ex_norm, ex_norm]
        simp
      · exact Filter.Eventually.of_forall (fun t _ => hbn)
      · exact intervalIntegrable_const
      · refine Filter.Eventually.of_forall (fun t _ => ?_)
        have e : (fun m => conj (b m) * (conj (ex m t) * ex n t)) =
            fun m => conj (b m * ex m t) * ex n t := by
          funext m
          rw [map_mul, mul_assoc]
        rw [e]
        exact (Complex.hasSum_conj'.mpr (hG t)).mul_right (ex n t)
    simp_rw [intervalIntegral.integral_const_mul, ex_orth] at hs
    have h2 : HasSum (fun m => conj (b m) * if m = n then (1 : ℂ) else 0) (conj (b n)) := by
      have e : (fun m => conj (b m) * if m = n then (1 : ℂ) else 0) =
          fun m => if m = n then conj (b n) else 0 := by
        funext m
        split_ifs with h
        · rw [h, mul_one]
        · rw [mul_zero]
      rw [e]
      exact hasSum_ite_eq n (conj (b n))
    exact hs.unique h2
  have hB : HasSum (fun n => ∫ x in (0 : ℝ)..1, a n * (conj (G x) * ex n x))
      (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => ‖a n‖ * ∑' m, ‖b m‖) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (continuous_const.mul
        ((Complex.continuous_conj.comp hGc).mul (ex_cont n))).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall (fun t _ => ?_)
      rw [norm_mul, norm_mul, ex_norm, mul_one, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hGb t) (norm_nonneg _)
    · exact Filter.Eventually.of_forall (fun t _ => han.mul_right _)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun t _ => ?_)
      have e : (fun n => a n * (conj (G t) * ex n t)) = fun n => conj (G t) * (a n * ex n t) := by
        funext n
        ring
      rw [e]
      exact (hF t).mul_left (conj (G t))
  simp_rw [intervalIntegral.integral_const_mul, hC] at hB
  have e : (fun n => conj (b n) * a n) = fun n => a n * conj (b n) := by
    funext n
    ring
  rw [e]
  exact hB

private theorem line_exp (k L : ℕ) [NeZero L] (f : CuspForm (Gamma1 L) (k : ℤ)) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ) * ex n x) (f (pt x y)) := by
  have hp : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 L)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1
  have hs := ModularForm.hasSum_qExpansion f one_pos hp (pt x y)
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
  have hc : ((pt x y : ℍ) : ℂ) = x + y * Complex.I := by
    unfold pt
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have e : (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ) * ex n x) =
      fun m => (qExpansion 1 f).coeff m * Function.Periodic.qParam 1 ↑(pt x y) ^ m := by
    funext n
    rw [hc, mul_assoc]
    unfold coef ex Function.Periodic.qParam
    congr 1
    rw [← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ) * n * y)) * Complex.I_sq
  rw [e]
  exact hs

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.pars :
    UpperTheory.V.Af.Rs.Pars := by
  intro k L _ f g y hy
  have hF := line_exp k L f y hy
  have hG := line_exp k L g y hy
  have ex0 : ∀ n, ex n 0 = 1 := by
    intro n
    simp [ex]
  have ha : Summable (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) :=
    (hF 0).summable.congr (fun n => by rw [ex0, mul_one])
  have hb : Summable (fun n : ℕ => coef g n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) :=
    (hG 0).summable.congr (fun n => by rw [ex0, mul_one])
  have h := pars_abs _ _ ha hb (fun x => f (pt x y)) (fun x => g (pt x y)) hF hG
  have e : (fun n : ℕ => conj (coef g n) * coef f n * ((Real.exp (-(4 * Real.pi * n) * y) : ℝ) : ℂ)) =
      fun n => conj (coef g n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) *
        (coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) := by
    funext n
    rw [map_mul, Complex.conj_ofReal,
      show -(4 * Real.pi * n) * y = (-(2 * Real.pi * n) * y) + (-(2 * Real.pi * n) * y) by ring,
      Real.exp_add]
    push_cast
    ring
  rw [e]
  exact h
end

section

open scoped MatrixGroups

theorem UpperTheory.V.Af.Rs.rowRep :
    UpperTheory.V.Af.Rs.RowRep := by
  intro x
  set g := (x 0).gcd (x 1) with hg
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · obtain ⟨h0', h1'⟩ := Int.gcd_eq_zero_iff.mp h0
    refine ⟨0, 1, ?_⟩
    funext i
    fin_cases i <;> simp [h0', h1']
  · have hc : IsCoprime (x 0 / (g : ℤ)) (x 1 / (g : ℤ)) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)
    obtain ⟨γ, -, hγ⟩ := ModularGroup.bottom_row_surj (R := ℤ)
      (show ![x 0 / (g : ℤ), x 1 / (g : ℤ)] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} by simpa using hc)
    refine ⟨g, γ, ?_⟩
    funext i
    have hi := congrFun hγ i
    simp only [UpperTheory.V.Af.Rs.row, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [hi]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left (x 0) (x 1))).symm
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right (x 0) (x 1))).symm
end
