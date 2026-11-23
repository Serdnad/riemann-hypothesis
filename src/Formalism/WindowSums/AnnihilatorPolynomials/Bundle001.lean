module

public import Formalism.WindowSums.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

noncomputable section

namespace Formalism.WindowSums

open Finset

lemma windowSum_count (a : ℤ) (L : ℕ) (r : ℤ) (hr : 0 < r) :
    ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℝ) ≤ (L : ℝ) / (r : ℝ) + 1 := by
  have hmaps : ∀ x ∈ (Finset.Ico a (a + L)).filter (fun x => r ∣ x),
      (x - a) / r ∈ Finset.Icc (0 : ℤ) ((L : ℤ) / r) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx
    simp only [Finset.mem_Icc]
    exact ⟨Int.ediv_nonneg (by linarith) hr.le, Int.ediv_le_ediv hr (by linarith)⟩
  have hinj : Set.InjOn (fun x => (x - a) / r)
      ((Finset.Ico a (a + L)).filter (fun x => r ∣ x) : Set ℤ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    obtain ⟨k, rfl⟩ := hx.2
    obtain ⟨m, rfl⟩ := hy.2
    simp only at hxy
    rw [show r * k - a = -a + r * k by ring, show r * m - a = -a + r * m by ring,
      Int.add_mul_ediv_left _ _ hr.ne', Int.add_mul_ediv_left _ _ hr.ne'] at hxy
    have : k = m := by linarith
    rw [this]
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  have hq0 : 0 ≤ (L : ℤ) / r := Int.ediv_nonneg (by positivity) hr.le
  rw [Int.card_Icc, sub_zero] at hcard
  have hc : ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℝ) ≤
      (((L : ℤ) / r : ℤ) : ℝ) + 1 := by
    have h1 : ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℤ) ≤ (L : ℤ) / r + 1 := by
      have := Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ (L : ℤ) / r + 1)
      omega
    exact_mod_cast h1
  have hdiv : (((L : ℤ) / r : ℤ) : ℝ) ≤ (L : ℝ) / (r : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hr)]
    exact_mod_cast Int.ediv_mul_le (L : ℤ) hr.ne'
  linarith

private theorem sum_range_one_div_pow_succ_eq (x : ℝ) (hx : 1 < x) (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / x ^ (k + 1) = (1 - 1 / x ^ K) / (x - 1) := by
  have hx0 : x - 1 ≠ 0 := by linarith
  have hxp : x ≠ 0 := by linarith
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring

theorem sum_padicValInt_le : WindowSum := by
  intro ℓ _ a L D S hS h0 hD
  have hℓ : ℓ.Prime := Fact.out
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hL0 : (0 : ℝ) ≤ (L : ℝ) / ((ℓ : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) (by linarith)
  rcases Nat.eq_zero_or_pos D with rfl | hDpos
  · have hzero : ∑ i ∈ S, padicValInt ℓ i = 0 := Finset.sum_eq_zero fun i hi =>
      (h0 ((abs_nonpos_iff.1 (by exact_mod_cast hD i hi)) ▸ hi)).elim
    rw [hzero]
    simpa [Real.logb_zero] using hL0
  have hv : ∀ i ∈ S, padicValInt ℓ i =
      ((Finset.range (Nat.log ℓ D)).filter (fun k => (ℓ : ℤ) ^ (k + 1) ∣ i)).card := by
    intro i hi
    have hi0 : i ≠ 0 := fun h => h0 (h ▸ hi)

    have hvK : padicValInt ℓ i ≤ Nat.log ℓ D := by
      have hdvd : (ℓ : ℤ) ^ padicValInt ℓ i ∣ i := (padicValInt_dvd_iff _ _).2 (Or.inr le_rfl)
      have h1 : ℓ ^ padicValInt ℓ i ∣ i.natAbs := by
        rw [← Int.natCast_dvd]
        exact_mod_cast hdvd
      have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hi0) h1
      have h3 : i.natAbs ≤ D := by
        have h4 := hD i hi
        rw [← Int.natCast_natAbs] at h4
        exact_mod_cast h4
      exact Nat.le_log_of_pow_le hℓ.one_lt (h2.trans h3)
    have hf : (Finset.range (Nat.log ℓ D)).filter (fun k => (ℓ : ℤ) ^ (k + 1) ∣ i) =
        Finset.range (padicValInt ℓ i) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, padicValInt_dvd_iff, hi0, false_or]
      omega
    rw [hf, Finset.card_range]
  have hcount : ∀ k, ((S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card : ℝ) ≤
      (L : ℝ) / (ℓ : ℝ) ^ (k + 1) + 1 := by
    intro k
    have h1 := windowSum_count a L ((ℓ : ℤ) ^ (k + 1)) (pow_pos (by exact_mod_cast hℓ.pos) _)
    push_cast at h1
    refine le_trans ?_ h1
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hS)
  have hsum : ∑ i ∈ S, padicValInt ℓ i = ∑ k ∈ Finset.range (Nat.log ℓ D),
      (S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card := by
    rw [Finset.sum_congr rfl hv]
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlog : ((Nat.log ℓ D : ℕ) : ℝ) ≤ Real.logb ℓ D := by
    rw [Real.le_logb_iff_rpow_le hℓ1 (by exact_mod_cast hDpos), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self ℓ hDpos.ne'
  have h1 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hy : 0 ≤ 1 / (ℓ : ℝ) ^ Nat.log ℓ D := by positivity
  have hgeo : (L : ℝ) * ((1 - 1 / (ℓ : ℝ) ^ Nat.log ℓ D) / ((ℓ : ℝ) - 1)) ≤
      (L : ℝ) / ((ℓ : ℝ) - 1) := by
    rw [← mul_div_assoc, div_le_div_iff₀ h1 h1]
    nlinarith [Nat.cast_nonneg (α := ℝ) L, mul_nonneg (Nat.cast_nonneg (α := ℝ) L) hy]
  rw [hsum]
  push_cast
  calc ∑ k ∈ Finset.range (Nat.log ℓ D), ((S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card : ℝ)
      ≤ ∑ k ∈ Finset.range (Nat.log ℓ D), ((L : ℝ) / (ℓ : ℝ) ^ (k + 1) + 1) :=
        Finset.sum_le_sum fun k _ => hcount k
    _ = (L : ℝ) * ∑ k ∈ Finset.range (Nat.log ℓ D), 1 / (ℓ : ℝ) ^ (k + 1) + (Nat.log ℓ D : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (L : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
        rw [sum_range_one_div_pow_succ_eq _ hℓ1]
        linarith

end Formalism.WindowSums
end
end

section

noncomputable section

namespace Formalism.WindowSums

open PowerSeries

theorem mem_span_iff_of_distinct_exponents : DistinctTerms := by
  intro O _ _ ϖ hϖ hnu ι I w e m B s hw he
  classical
  constructor
  · intro hmem
    by_contra hbad
    push_neg at hbad
    obtain ⟨i₁, hi₁, hb₁, hs₁⟩ := hbad
    have hJne : (I.filter fun i => e i < B ∧ m i < s).Nonempty :=
      ⟨i₁, Finset.mem_filter.mpr ⟨hi₁, hb₁, hs₁⟩⟩
    obtain ⟨i₀, hi₀J, hmin⟩ := (I.filter fun i => e i < B ∧ m i < s).exists_min_image e hJne
    obtain ⟨hi₀, hB, hs⟩ := Finset.mem_filter.mp hi₀J
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
    have hcoef := congrArg (PowerSeries.coeff (e i₀)) hab

    rw [map_add (f := _), mul_comm a, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_add,
    PowerSeries.coeff_mul_C, map_sum] at hcoef
    have hterm : ∀ i ∈ I, PowerSeries.coeff (e i₀) (w i * X ^ e i * C (ϖ ^ m i)) =
        (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
      intro i _
      rw [PowerSeries.coeff_mul_C, mul_comm (w i), PowerSeries.coeff_X_pow_mul']
    rw [Finset.sum_congr rfl hterm, ← Finset.add_sum_erase _ _ hi₀, if_pos le_rfl,
      Nat.sub_self] at hcoef
    have hrest : ϖ ^ s ∣ ∑ i ∈ I.erase i₀,
        (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
      refine Finset.dvd_sum fun i hi => ?_
      obtain ⟨hne, hiI⟩ := Finset.mem_erase.mp hi
      by_cases hle : e i ≤ e i₀
      · rw [if_pos hle]
        have hlt : e i < e i₀ := lt_of_le_of_ne hle fun h => hne (he hiI hi₀ h)
        have hms : s ≤ m i := by
          by_contra hms
          push_neg at hms
          have := hmin i (Finset.mem_filter.mpr ⟨hiI, by omega, hms⟩)
          omega
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hms) _
      · rw [if_neg hle, zero_mul]
        exact dvd_zero _
    have hdvd : ϖ ^ s ∣ PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀ := by
      have h2 : PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀ =
          PowerSeries.coeff (e i₀) b * ϖ ^ s - ∑ i ∈ I.erase i₀,
            (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
        rw [hcoef]; ring
      rw [h2]
      exact dvd_sub (dvd_mul_left _ _) hrest
    have hu : IsUnit (PowerSeries.coeff 0 (w i₀)) := by
      have := (hw i₀ hi₀).map (PowerSeries.constantCoeff (R := O))
      simpa using this
    have hsplit : ϖ ^ s = ϖ ^ m i₀ * ϖ ^ (s - m i₀) := by
      rw [← pow_add, Nat.add_sub_cancel' hs.le]
    rw [hsplit, mul_comm (PowerSeries.coeff 0 (w i₀))] at hdvd
    have hd2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ)).mp hdvd
    have hd3 : ϖ ∣ PowerSeries.coeff 0 (w i₀) :=
      (dvd_pow_self ϖ (by omega)).trans hd2
    exact hnu (isUnit_of_dvd_unit hd3 hu)
  · intro h
    refine Ideal.sum_mem _ fun i hi => ?_
    rcases h i hi with hb | hs
    · have hx : (X : PowerSeries O) ^ B ∈
          Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)} :=
        Ideal.subset_span (Set.mem_insert _ _)
      have heq : w i * X ^ e i * C (ϖ ^ m i) = X ^ B * (w i * X ^ (e i - B) * C (ϖ ^ m i)) := by
        rw [show e i = B + (e i - B) by omega, pow_add]
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [heq]
      exact Ideal.mul_mem_right _ _ hx
    · have hc : C (ϖ ^ s) ∈ Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have heq : w i * X ^ e i * C (ϖ ^ m i) = C (ϖ ^ s) * (w i * X ^ e i * C (ϖ ^ (m i - s))) := by
        rw [show m i = s + (m i - s) by omega, pow_add, map_mul]
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [heq]
      exact Ideal.mul_mem_right _ _ hc

end Formalism.WindowSums
end
end

section

namespace Formalism.WindowSums

open Finset

section ZpowValAux

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma zv_prime : Prime (ℓ : ℤ_[ℓ]) := PadicInt.prime_p

lemma zv_emult_eq_val {x : ℤ_[ℓ]} (hx : x ≠ 0) :
    emultiplicity (ℓ : ℤ_[ℓ]) x = (x.valuation : ℕ∞) := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [emultiplicity_mul zv_prime, emultiplicity_of_isUnit_right zv_prime.not_unit (Units.isUnit _),
    zero_add, emultiplicity_pow_self_of_prime zv_prime]

lemma zv_emult_unit_mul {c : ℤ_[ℓ]} (hc : IsUnit c) (y : ℤ_[ℓ]) :
    emultiplicity (ℓ : ℤ_[ℓ]) (c * y) = emultiplicity (ℓ : ℤ_[ℓ]) y := by
  rw [emultiplicity_mul zv_prime, emultiplicity_of_isUnit_right zv_prime.not_unit hc, zero_add]

lemma zv_not_dvd_of_dvd_sub_one {x : ℤ_[ℓ]} (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1) : ¬ (ℓ : ℤ_[ℓ]) ∣ x := by
  intro h
  have h1 : (ℓ : ℤ_[ℓ]) ∣ 1 := by
    have h2 := dvd_sub h hx
    rwa [sub_sub_cancel] at h2
  exact zv_prime.not_unit (isUnit_of_dvd_one h1)

lemma zv_two_sq_step (h2 : ℓ = 2) {x : ℤ_[ℓ]} (h4 : (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ 2 - 1) = emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + 1 := by
  have hx1 : (ℓ : ℤ_[ℓ]) ∣ x - 1 := (dvd_pow_self _ two_ne_zero).trans h4
  have e : x + 1 = (x - 1) + (ℓ : ℤ_[ℓ]) := by
    have hc : (ℓ : ℤ_[ℓ]) = 2 := by
      have h7 := congrArg (fun n : ℕ => (n : ℤ_[ℓ])) h2
      simpa using h7
    rw [hc]
    ring

  have hp1 : emultiplicity (ℓ : ℤ_[ℓ]) (x + 1) = 1 := by
    rw [← Nat.cast_one (R := ℕ∞), emultiplicity_eq_coe]
    refine ⟨by rw [pow_one, e]; exact dvd_add hx1 dvd_rfl, fun hd => ?_⟩
    have h3 : (ℓ : ℤ_[ℓ]) ^ 2 ∣ (ℓ : ℤ_[ℓ]) ^ 1 := by
      have h5 := dvd_sub hd h4
      rw [e, add_sub_cancel_left] at h5
      rw [pow_one]
      exact h5
    have h6 := (pow_dvd_pow_iff zv_prime.ne_zero zv_prime.not_unit).1 h3
    omega
  rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring, emultiplicity_mul zv_prime, hp1]

lemma zv_pow_prime_pow (x : ℤ_[ℓ]) (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1)
    (h2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) (k : ℕ) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ ℓ ^ k - 1) = emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + k := by
  by_cases hl : ℓ = 2
  · have h4 := h2 hl
    induction k with
    | zero => simp
    | succ k ih =>
      have hy : (ℓ : ℤ_[ℓ]) ^ 2 ∣ x ^ ℓ ^ k - 1 := h4.trans (sub_one_dvd_pow_sub_one x _)
      have e : x ^ ℓ ^ (k + 1) = (x ^ ℓ ^ k) ^ 2 := by
        rw [pow_succ, pow_mul]
        exact congrArg (fun n => (x ^ ℓ ^ k) ^ n) hl
      rw [e, zv_two_sq_step hl hy, ih]
      push_cast
      ring
  · have hodd : Odd ℓ := hℓ.out.odd_of_ne_two hl
    have h1 := emultiplicity_pow_prime_pow_sub_pow_prime_pow (x := x) (y := 1) zv_prime hodd
      (by simpa using hx) (zv_not_dvd_of_dvd_sub_one hx) k
    rwa [one_pow] at h1

lemma zv_not_dvd_cast {m : ℕ} (hm : ¬ ℓ ∣ m) : ¬ (ℓ : ℤ_[ℓ]) ∣ (m : ℤ_[ℓ]) := by
  intro h
  rw [← PadicInt.norm_lt_one_iff_dvd] at h
  have h' : ‖((m : ℤ) : ℤ_[ℓ])‖ < 1 := by
    rw [Int.cast_natCast]
    exact h
  exact hm (Int.natCast_dvd_natCast.1 ((PadicInt.norm_int_lt_one_iff_dvd (m : ℤ)).1 h'))

lemma zv_pow_nat (x : ℤ_[ℓ]) (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1)
    (h2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) {n : ℕ} (hn : n ≠ 0) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ n - 1) =
      emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + padicValNat ℓ n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn ℓ hℓ.out.ne_one
  have hm0 : m ≠ 0 := right_ne_zero_of_mul hn
  have hy1 : (ℓ : ℤ_[ℓ]) ∣ x ^ ℓ ^ e - 1 := hx.trans (sub_one_dvd_pow_sub_one x _)
  have h1 := emultiplicity_pow_sub_pow_of_prime zv_prime hy1
    (zv_not_dvd_of_dvd_sub_one (by simpa using hy1)) (zv_not_dvd_cast hm)
  rw [one_pow] at h1
  have hv : padicValNat ℓ (ℓ ^ e * m) = e := by
    rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hℓ.out.ne_zero) hm0,
      Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]
  rw [pow_mul, h1, zv_pow_prime_pow x hx h2 e, hv]

end ZpowValAux

theorem valuation_zpow_sub_one : ZpowVal := by
  intro ℓ _ u s hs1 hs2 hval j hj

  have key : ∀ y : ℤ_[ℓ]ˣ, emultiplicity (ℓ : ℤ_[ℓ]) ((y : ℤ_[ℓ]) - 1) = s → ∀ n : ℕ, n ≠ 0 →
      ((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 ≠ 0 ∧
        PadicInt.valuation (((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = s + padicValNat ℓ n := by
    intro y hy n hn
    have hy1 : (ℓ : ℤ_[ℓ]) ∣ (y : ℤ_[ℓ]) - 1 := by
      have h1 := pow_dvd_of_le_emultiplicity (k := 1) (by rw [hy]; exact_mod_cast hs1)
      rwa [pow_one] at h1
    have hy2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ (y : ℤ_[ℓ]) - 1 := fun h =>
      pow_dvd_of_le_emultiplicity (by rw [hy]; exact_mod_cast hs2 h)
    have he := zv_pow_nat (y : ℤ_[ℓ]) hy1 hy2 hn
    rw [← Units.val_pow_eq_pow_val, hy] at he
    have hne : ((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 ≠ 0 := by
      intro h0
      rw [h0, emultiplicity_zero] at he
      exact absurd he (by norm_cast)
    refine ⟨hne, ?_⟩
    rw [zv_emult_eq_val hne] at he
    exact_mod_cast he
  have hx0 : (u : ℤ_[ℓ]) - 1 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at hval
    omega
  have hem : emultiplicity (ℓ : ℤ_[ℓ]) ((u : ℤ_[ℓ]) - 1) = s := by
    rw [zv_emult_eq_val hx0, hval]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hj rfl
    rw [zpow_natCast, padicValInt.of_nat]
    simpa only [Nat.padicValNat_def] using key u hem n hn
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hj (by simp)
    have hinv : emultiplicity (ℓ : ℤ_[ℓ]) (((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = s := by
      have e : ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 = (-((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) * ((u : ℤ_[ℓ]) - 1) := by
        rw [mul_sub, neg_mul, Units.inv_mul]
        ring
      rw [e, zv_emult_unit_mul (Units.isUnit _).neg, hem]
    have hv : padicValInt ℓ (-(n : ℤ)) = padicValNat ℓ n := by
      simp [padicValInt, Nat.padicValNat_def]
    rw [zpow_neg, zpow_natCast, ← inv_pow, hv]
    exact key u⁻¹ hinv n hn

end Formalism.WindowSums
end
