module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.PowerSeries.Order

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.Val

variable {LL : Type} [Field LL] (v : AddValuation LL (WithTop ℚ))

theorem v_natCast_nonneg (m : ℕ) : 0 ≤ v (m : LL) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ n ih =>
    rw [Nat.cast_succ]
    exact v.map_le_add ih v.map_one.symm.le

private theorem withTop_zero_lt_one : (0 : WithTop ℚ) < 1 := by
  first
  | exact WithTop.coe_lt_coe.2 zero_lt_one

private theorem withTop_rat_not_one_add_one_le_one : ¬ ((1 : WithTop ℚ) + 1 ≤ 1) := by
  first
  | (rw [← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe]; norm_num)

private theorem le_v_sum_range_of_forall (f : ℕ → LL) (g : WithTop ℚ) (hf : ∀ i, g ≤ v (f i)) (m : ℕ) :
    g ≤ v (∑ i ∈ Finset.range m, f i) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact v.map_le_add ih (hf n)

theorem v_intCast_nonneg (z : ℤ) : 0 ≤ v (z : LL) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · first
    | (rw [Int.cast_natCast]; exact v_natCast_nonneg v n)
  · first
    | (rw [Int.cast_neg, Int.cast_natCast, v.map_neg]; exact v_natCast_nonneg v n)

variable {p : ℕ} (hp : p.Prime) (hv : v (p : LL) = 1)
include hp hv

theorem v_natCast_eq_zero (m : ℕ) (hm : ¬ p ∣ m) : v (m : LL) = 0 := by
  have h0 := v_natCast_nonneg v m
  refine le_antisymm (not_lt.mp fun hlt => ?_) h0
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
  have hb := Nat.gcd_eq_gcd_ab p m
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at hb
  have hL : (p : LL) * (Nat.gcdA p m : LL) + (m : LL) * (Nat.gcdB p m : LL) = 1 := by
    first
    | (have h := congrArg (fun z : ℤ => (z : LL)) hb; push_cast at h; exact h.symm)
  have h1 : 0 < v ((p : LL) * (Nat.gcdA p m : LL)) := by
    rw [v.map_mul, hv]
    exact lt_of_lt_of_le withTop_zero_lt_one (le_add_of_nonneg_right (v_intCast_nonneg v _))
  have h2 : 0 < v ((m : LL) * (Nat.gcdB p m : LL)) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_right (v_intCast_nonneg v _))
  have h3 : min (v ((p : LL) * (Nat.gcdA p m : LL))) (v ((m : LL) * (Nat.gcdB p m : LL))) ≤
      v ((p : LL) * (Nat.gcdA p m : LL) + (m : LL) * (Nat.gcdB p m : LL)) :=
    v.map_le_add (min_le_left _ _) (min_le_right _ _)
  rw [hL, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min h1 h2))

omit hp hv in
theorem v_eq_zero_of_close {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) : v ξ = 0 := by
  have hpos : 0 < v (ξ - 1) := lt_of_lt_of_le withTop_zero_lt_one h1
  have h0 : (0 : WithTop ℚ) ≤ v ((ξ - 1) + 1) := v.map_le_add hpos.le v.map_one.symm.le
  rw [sub_add_cancel] at h0
  refine le_antisymm (not_lt.mp fun hlt => ?_) h0
  have h3 : min (v ξ) (v (ξ - 1)) ≤ v (ξ + -(ξ - 1)) :=
    v.map_le_add (min_le_left _ _) (by rw [v.map_neg]; exact min_le_right _ _)
  have e : ξ + -(ξ - 1) = 1 := by ring
  rw [e, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min hlt hpos))

omit hp hv in
theorem v_geom_nonneg {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (m : ℕ) :
    0 ≤ v (∑ i ∈ Finset.range m, ξ ^ i) := by
  have hξ := v_eq_zero_of_close v h1
  exact le_v_sum_range_of_forall v (fun i => ξ ^ i) 0
    (fun i => by
      show (0 : WithTop ℚ) ≤ v (ξ ^ i)
      exact le_of_eq (by rw [v.map_pow, hξ, smul_zero])) m

omit hp hv in
theorem v_pow_sub_one {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (m : ℕ) :
    v (ξ - 1) ≤ v (ξ ^ m - 1) := by
  rw [← geom_sum_mul ξ m, v.map_mul]
  exact le_add_of_nonneg_left (v_geom_nonneg v h1 m)


omit hp hv in
theorem v_geom_sub {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (m : ℕ) :
    v (ξ - 1) ≤ v ((∑ i ∈ Finset.range m, ξ ^ i) - (m : LL)) := by
  have e : (∑ i ∈ Finset.range m, ξ ^ i) - (m : LL) = ∑ i ∈ Finset.range m, (ξ ^ i - 1) := by
    first
    | (rw [Finset.sum_sub_distrib]; simp)
  rw [e]
  exact le_v_sum_range_of_forall v (fun i => ξ ^ i - 1) _ (fun i => v_pow_sub_one v h1 i) m

theorem pow_p_ne_one {ξ : LL} (hp3 : 3 ≤ p) (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (hne : ξ ≠ 1) :
    ξ ^ p ≠ 1 := by
  intro hpow
  have hS : (∑ i ∈ Finset.range p, ξ ^ i) = 0 := by
    have h := geom_sum_mul ξ p
    rw [hpow, sub_self] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h') hne
  have eSp : (∑ i ∈ Finset.range p, ξ ^ i) - (p : LL) =
      (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ξ ^ j) * (ξ - 1) := by
    rw [Finset.sum_mul]
    simp only [geom_sum_mul]
    first
    | (rw [Finset.sum_sub_distrib]; simp)
  have hT : 1 ≤ v (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ξ ^ j) := by
    have e2 : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ξ ^ j) =
        (∑ i ∈ Finset.range p, ((∑ j ∈ Finset.range i, ξ ^ j) - (i : LL))) +
          (((∑ i ∈ Finset.range p, i : ℕ)) : LL) := by
      first
      | (rw [Finset.sum_sub_distrib, Nat.cast_sum]; ring)
    rw [e2]
    apply v.map_le_add
    · exact le_v_sum_range_of_forall v _ _ (fun i => le_trans h1 (v_geom_sub v h1 i)) p
    · obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := hp.eq_two_or_odd'.resolve_left (by omega)
      have hs : (∑ i ∈ Finset.range p, i) = p * k := by
        apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
        rw [Finset.sum_range_id_mul_two, hk, Nat.add_sub_cancel]
        ring
      rw [hs, Nat.cast_mul, v.map_mul, hv]
      exact le_add_of_nonneg_right (v_natCast_nonneg v k)
  have hvS : 1 + 1 ≤ v ((∑ i ∈ Finset.range p, ξ ^ i) - (p : LL)) := by
    rw [eSp, v.map_mul]
    exact add_le_add hT h1
  rw [hS, zero_sub, v.map_neg, hv] at hvS
  exact withTop_rat_not_one_add_one_le_one hvS

theorem pow_ne_one_of_close (hp3 : 3 ≤ p) :
    ∀ (m : ℕ) (ξ : LL), 0 < m → (1 : WithTop ℚ) ≤ v (ξ - 1) → ξ ≠ 1 → ξ ^ m ≠ 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro ξ hm h1 hne
    by_cases hpm : p ∣ m
    · obtain ⟨k, rfl⟩ := hpm
      have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
      have hlt : k < p * k := by
        have : 1 < p := hp.one_lt
        nlinarith
      rw [pow_mul]
      exact ih k hlt (ξ ^ p) hk (le_trans h1 (v_pow_sub_one v h1 p))
        (pow_p_ne_one v hp hv hp3 h1 hne)
    · intro hpow
      have hS : (∑ i ∈ Finset.range m, ξ ^ i) = 0 := by
        have h := geom_sum_mul ξ m
        rw [hpow, sub_self] at h
        rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd (sub_eq_zero.mp h') hne
      have h2 := v_geom_sub v h1 m
      rw [hS, zero_sub, v.map_neg, v_natCast_eq_zero v hp hv m hpm] at h2
      exact absurd (le_trans h1 h2) (not_le.mpr withTop_zero_lt_one)

theorem zpow_ne_one_of_close (hp3 : 3 ≤ p) (ξ : LL) (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1))
    (hne : ξ ≠ 1) (k : ℤ) (hk : k ≠ 0) : ξ ^ k ≠ 1 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · have hn : 0 < n := by omega
    rw [zpow_natCast]
    exact pow_ne_one_of_close v hp hv hp3 n ξ hn h1 hne
  · have hn : 0 < n := by omega
    rw [zpow_neg, zpow_natCast, Ne, inv_eq_one]
    exact pow_ne_one_of_close v hp hv hp3 n ξ hn h1 hne

end Formalism.MainNotions.N.Pv.LocalLengthBound.Val
end
end

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.Wd

open PowerSeries

variable {O LL : Type} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
  (hinj : Function.Injective (algebraMap O LL)) (l : O)
  (ψ : PowerSeries O →+* PowerSeries LL) (hψC : ∀ o : O, ψ (PowerSeries.C o) = PowerSeries.C (algebraMap O LL o))
  (u : PowerSeries LL) (hu : IsUnit u) (hψ : ψ (PowerSeries.X + PowerSeries.C l) = PowerSeries.X * u)
include hinj hψC hu hψ


theorem poly_eq_zero : ∀ (k : ℕ) (r : Polynomial O), r.degree < k →
    PowerSeries.X ^ k ∣ ψ (r : PowerSeries O) → r = 0 := by
  have dvd_of_dvd_isUnit_mul_lemma {R : Type _} [CommRing R] {u f g : R} (hu : IsUnit u)
      (h : g ∣ u * f) : g ∣ f := by
    obtain ⟨v, rfl⟩ := hu
    have e : f = ↑v⁻¹ * (↑v * f) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [e]
    exact dvd_mul_of_dvd_right h _
  have hψX : ψ PowerSeries.X = PowerSeries.X * u - PowerSeries.C (algebraMap O LL l) := by
    have h := hψ
    rw [map_add (f := _), hψC] at h
    exact eq_sub_of_add_eq h
  intro k
  induction k with
  | zero =>
    intro r hr _
    by_contra hr0
    rw [Polynomial.degree_eq_natDegree hr0] at hr
    have h0 : r.natDegree < 0 := by exact_mod_cast hr
    omega
  | succ k ih =>
    intro r hr hdvd
    have hmon : (Polynomial.X + Polynomial.C l : Polynomial O).Monic := Polynomial.monic_X_add_C l
    have hrem : Polynomial.modByMonic r (Polynomial.X + Polynomial.C l) = Polynomial.C (r.eval (-l)) := by
      have hg : (Polynomial.X + Polynomial.C l : Polynomial O) = Polynomial.X - Polynomial.C (-l) := by
        rw [map_neg, sub_neg_eq_add]
      rw [hg]
      exact Polynomial.modByMonic_X_sub_C_eq_C_eval r (-l)
    have hsplit : r = Polynomial.C (r.eval (-l)) +
        (Polynomial.X + Polynomial.C l) * Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) := by
      have h1 : Polynomial.modByMonic r (Polynomial.X + Polynomial.C l) +
          (Polynomial.X + Polynomial.C l) * Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) = r := by
        first
          | exact Polynomial.modByMonic_add_div r (Polynomial.X + Polynomial.C l)
      rw [hrem] at h1
      exact h1.symm
    have hqdeg : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).degree < k := by
      by_cases hq0 : Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) = 0
      · rw [hq0, Polynomial.degree_zero]
        first
          | exact WithBot.bot_lt_coe _
      · have hr0 : r ≠ 0 := by
          rintro rfl
          exact hq0 (Polynomial.zero_divByMonic _)
        have hpos : 0 < (Polynomial.X + Polynomial.C l : Polynomial O).degree := by
          first
            | (rw [Polynomial.degree_X_add_C]; exact zero_lt_one)
        have h1 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).degree < r.degree := by
          first
            | exact Polynomial.degree_divByMonic_lt r (Polynomial.X + Polynomial.C l) hr0 hpos
        rw [Polynomial.degree_eq_natDegree hq0, Polynomial.degree_eq_natDegree hr0] at h1
        rw [Polynomial.degree_eq_natDegree hr0] at hr
        rw [Polynomial.degree_eq_natDegree hq0]
        have a1 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).natDegree < r.natDegree := by
          exact_mod_cast h1
        have a2 : r.natDegree < k + 1 := by exact_mod_cast hr
        have a3 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).natDegree < k := by omega
        exact_mod_cast a3
    obtain ⟨c, q, hrq, hq⟩ : ∃ (c : O) (q : Polynomial O),
        r = Polynomial.C c + (Polynomial.X + Polynomial.C l) * q ∧ q.degree < k :=
      ⟨_, _, hsplit, hqdeg⟩
    have hψr : ψ (r : PowerSeries O) =
        PowerSeries.C (algebraMap O LL c) + PowerSeries.X * (u * ψ (q : PowerSeries O)) := by
      rw [hrq]
      first
        | (simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
            map_add, map_mul, hψC, hψX]; ring)
        | (simp [hψC, hψX]; ring)
    have hX : PowerSeries.X ∣ ψ (r : PowerSeries O) :=
      (dvd_pow_self _ (Nat.succ_ne_zero k)).trans hdvd
    rw [hψr, PowerSeries.X_dvd_iff] at hX
    first
      | simp only [map_add (f := _), map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
          zero_mul, add_zero] at hX
    have hc0 : c = 0 := hinj (hX.trans (map_zero _).symm)
    simp only [hc0, map_zero, zero_add] at hψr
    rw [hψr, pow_succ'] at hdvd
    have h2 : PowerSeries.X ^ k ∣ u * ψ (q : PowerSeries O) :=
      (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp hdvd
    have hq0 : q = 0 := ih q hq (dvd_of_dvd_isUnit_mul_lemma hu h2)
    rw [hrq, hc0, hq0]
    simp

theorem dvd_of_dvd_image [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : l ∈ IsLocalRing.maximalIdeal O) (k : ℕ) (a : PowerSeries O)
    (ha : PowerSeries.X ^ k ∣ ψ a) : (PowerSeries.X + PowerSeries.C l) ^ k ∣ a := by
  have hres : PowerSeries.map (IsLocalRing.residue O) ((PowerSeries.X + PowerSeries.C l) ^ k) =
      PowerSeries.X ^ k := by
    rw [map_pow, map_add (f := _), PowerSeries.map_X, PowerSeries.map_C,
      (IsLocalRing.residue_eq_zero_iff l).mpr hlm, map_zero, add_zero]
  have hg : PowerSeries.map (IsLocalRing.residue O) ((PowerSeries.X + PowerSeries.C l) ^ k) ≠ 0 := by
    rw [hres]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hdiv⟩ := PowerSeries.exists_isWeierstrassDivision (f := a) hg
  have hdeg : r.degree < k := by
    have h := hdiv.degree_lt
    have hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) l = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hlm
    first
      | simpa [hz, PowerSeries.order_X_pow] using h
      | (rw [hres, PowerSeries.order_X_pow, ENat.toNat_coe] at h; exact h)
      | (simp only [hres, PowerSeries.order_X_pow, ENat.toNat_coe] at h; exact h)
  have hψa : ψ a = (PowerSeries.X * u) ^ k * ψ q + ψ (r : PowerSeries O) := by
    rw [hdiv.eq_mul_add, map_add (f := _), map_mul, map_pow, hψ]
  have h1 : PowerSeries.X ^ k ∣ (PowerSeries.X * u) ^ k * ψ q :=
    dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_mul_right _ _) k) _
  have h2 : PowerSeries.X ^ k ∣ ψ (r : PowerSeries O) := by
    rw [hψa] at ha
    first
      | exact (dvd_add_right h1).mp ha
  have hr0 : r = 0 := poly_eq_zero hinj l ψ hψC u hu hψ k r hdeg h2
  rw [hdiv.eq_mul_add, hr0, Polynomial.coe_zero, add_zero]
  exact dvd_mul_right _ _

end Formalism.MainNotions.N.Pv.LocalLengthBound.Wd
end
end
