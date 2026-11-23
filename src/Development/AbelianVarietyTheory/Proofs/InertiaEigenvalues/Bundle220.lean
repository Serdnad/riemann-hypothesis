module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.LocalFields.Interface
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem character_kernel_generator (G : Type) [Group G] (p r : ℕ) (a : G → ℤ) (hp : p.Prime)
    (hadd : ∀ σ τ, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ) (hne : ∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) :
    ∃ (J : Subgroup G) (_ : J.Normal) (σ₁ : G) (c : ℤ), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧
      c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ ∧ ¬ (p : ℤ) ∣ c := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcast : ∀ x : ℤ, ((x : ZMod (p ^ r)) = 0 ↔ (p : ℤ) ^ r ∣ x) := by
    intro x
    exact_mod_cast ZMod.intCast_zmod_eq_zero_iff_dvd x (p ^ r)
  have hmul : ∀ σ τ, ((a (σ * τ) : ZMod (p ^ r))) = (a σ : ZMod (p ^ r)) + (a τ : ZMod (p ^ r)) := by
    intro σ τ
    have := (hcast _).2 (hadd σ τ)
    push_cast at this
    linear_combination this
  have hone : ((a 1 : ℤ) : ZMod (p ^ r)) = 0 := by
    have := hmul 1 1
    simp only [mul_one] at this
    linear_combination -this
  let f : G →* Multiplicative (ZMod (p ^ r)) :=
    { toFun := fun σ => Multiplicative.ofAdd (a σ : ZMod (p ^ r))
      map_one' := by simp only [hone, ofAdd_zero]
      map_mul' := fun σ τ => by simp only [hmul, ofAdd_add] }
  have hfx : ∀ σ, f σ = Multiplicative.ofAdd (a σ : ZMod (p ^ r)) := fun _ => rfl
  have hker : ∀ σ, σ ∈ f.ker ↔ (p : ℤ) ^ r ∣ a σ := by
    intro σ
    rw [MonoidHom.mem_ker, hfx, ofAdd_eq_one, hcast]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := f.range)
  obtain ⟨σ₁, hσ₁⟩ := g.2
  set x : ZMod (p ^ r) := (a σ₁ : ZMod (p ^ r)) with hxdef
  have hidx : f.ker.index = addOrderOf x := by
    have h1 : f.ker.index = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [h1, ← hg, ← Subgroup.orderOf_coe, ← hσ₁, hfx, orderOf_ofAdd_eq_addOrderOf]
  have hsm : ∀ k : ℕ, k • x = 0 ↔ (p : ℤ) ^ r ∣ (k : ℤ) * a σ₁ := by
    intro k
    rw [← hcast]
    push_cast
    rw [nsmul_eq_mul]
  have hdvd : addOrderOf x ∣ p ^ r :=
    (addOrderOf_dvd_natCard x).trans (by rw [Nat.card_zmod])
  obtain ⟨s, hsr, hs⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hs0 : s ≠ 0 := by
    rintro rfl
    obtain ⟨τ, hτ⟩ := hne
    have : f.ker = ⊤ := Subgroup.index_eq_one.1 (by rw [hidx, hs, pow_zero])
    exact hτ ((hker τ).1 (this ▸ Subgroup.mem_top τ))
  obtain ⟨c, hc⟩ := (hsm (addOrderOf x)).1 (addOrderOf_nsmul_eq_zero x)
  refine ⟨f.ker, inferInstance, σ₁, c, hker, ?_, ?_⟩
  · rw [hidx, hc]; ring
  · rintro ⟨d, rfl⟩
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have key : (p : ℤ) ^ r ∣ ((p ^ (s - 1) : ℕ) : ℤ) * a σ₁ := by
      refine ⟨d, ?_⟩
      apply mul_left_cancel₀ hp0
      have hs' : (p : ℤ) ^ s = p * p ^ (s - 1) := by
        rw [← pow_succ']; congr 1; omega
      have := hc
      rw [hs] at this
      push_cast at this ⊢
      rw [hs'] at this
      linear_combination this
    have h2 : addOrderOf x ∣ p ^ (s - 1) :=
      addOrderOf_dvd_of_nsmul_eq_zero ((hsm _).2 key)
    rw [hs, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h2
    omega

end GlobalTheory.PMon.Ram
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem psers_norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  simpa using h

theorem psers_terms_tendsto_zero : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → Filter.Tendsto (fun n : ℤ => ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) Filter.cofinite (nhds 0) := by
  intro l _ h j r h1 hr0 hr1
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hlR : (1 : ℝ) < l := by exact_mod_cast hl
  have ha := psers_norm_natCast_self l
  set a := ‖(l : ℂ_[l])‖ with ha_def
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a < 1 := by rw [ha]; exact inv_lt_one_of_one_lt₀ hlR
  rw [Int.cofinite_eq, Filter.tendsto_sup]
  constructor
  · rw [← Filter.map_neg_atTop, Filter.tendsto_map'_iff, ← Nat.map_cast_int_atTop,
      Filter.tendsto_map'_iff]
    refine squeeze_zero (fun k => ?_) (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1)
    · simp only [Function.comp_apply, neg_neg, zpow_natCast]
      exact mul_nonneg (pow_nonneg ha0 _) (Real.rpow_nonneg hr0 _)
    · simp only [Function.comp_apply, neg_neg, zpow_natCast]
      have : r ^ ((l : ℝ) ^ (-(k : ℤ) * h + j : ℤ)) ≤ 1 :=
        Real.rpow_le_one hr0 hr1.le (zpow_nonneg (by positivity) _)
      calc a ^ k * r ^ ((l : ℝ) ^ (-(k : ℤ) * h + j : ℤ)) ≤ a ^ k * 1 :=
            mul_le_mul_of_nonneg_left this (pow_nonneg ha0 _)
        _ = a ^ k := mul_one _
  · rw [← Nat.map_cast_int_atTop, Filter.tendsto_map'_iff]
    have hN : Filter.Tendsto (fun k : ℕ => l ^ (k * h + j)) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (fun k => ?_) Filter.tendsto_id
      calc k ≤ l ^ k := (Nat.lt_pow_self hl).le
        _ ≤ l ^ (k * h + j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    refine squeeze_zero (fun k => ?_) (fun k => ?_)
      ((tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp hN)
    · exact mul_nonneg (zpow_nonneg ha0 _) (Real.rpow_nonneg hr0 _)
    · have e1 : a ^ (-((k : ℕ) : ℤ)) = (l : ℝ) ^ k := by
        rw [zpow_neg, zpow_natCast, ha, inv_pow, inv_inv]
      have e2 : (l : ℝ) ^ (((k : ℕ) : ℤ) * h + j : ℤ) = ((l ^ (k * h + j) : ℕ) : ℝ) := by
        rw [show (((k : ℕ) : ℤ) * h + j : ℤ) = ((k * h + j : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast]
        push_cast; ring
      simp only [Function.comp_apply]
      rw [e1, e2, Real.rpow_natCast]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
      have : l ^ k ≤ l ^ (k * h + j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      exact_mod_cast this

end GlobalTheory
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.Uniq

theorem exists_strict_max (f d : ℤ → ℝ) (hd : ∀ n, f (n + 1) = f n + d n) (hanti : StrictAnti d)
    (hne : ∀ n, d n ≠ 0) (hpos : ∃ m, 0 < d m) (hneg : ∃ m, d m < 0) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ → f n < f n₀ := by
  obtain ⟨m, hm⟩ := hpos
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, d z < 0 → b ≤ z := ⟨m, fun z hz => by
    by_contra hc
    push_neg at hc
    have := hanti hc
    linarith⟩
  obtain ⟨n₀, hn₀, hmin⟩ := Int.exists_least_of_bdd hbdd hneg
  have hafter : ∀ k, n₀ ≤ k → d k < 0 := fun k hk => by
    rcases hk.lt_or_eq with h | h
    · exact (hanti h).trans hn₀
    · rw [← h]; exact hn₀
  have hbefore : ∀ k, k < n₀ → 0 < d k := fun k hk => by
    rcases lt_or_gt_of_ne (hne k) with h | h
    · exact absurd (hmin k h) (not_le.2 hk)
    · exact h
  have hfwd : ∀ k : ℕ, f (n₀ + k + 1) < f n₀ := by
    intro k
    induction k with
    | zero =>
      have := hd n₀
      have := hafter n₀ le_rfl
      simp only [Nat.cast_zero, add_zero]
      linarith
    | succ k ih =>
      rw [show n₀ + ((k + 1 : ℕ) : ℤ) + 1 = n₀ + k + 1 + 1 by push_cast; ring]
      have := hd (n₀ + k + 1)
      have := hafter (n₀ + k + 1) (by omega)
      linarith
  have hbwd : ∀ k : ℕ, f (n₀ - k - 1) < f n₀ := by
    intro k
    induction k with
    | zero =>
      have := hd (n₀ - 1)
      have := hbefore (n₀ - 1) (by omega)
      simp only [Nat.cast_zero, sub_zero]
      rw [sub_add_cancel] at *
      linarith
    | succ k ih =>
      have := hd (n₀ - ((k + 1 : ℕ) : ℤ) - 1)
      have := hbefore (n₀ - ((k + 1 : ℕ) : ℤ) - 1) (by omega)
      rw [show n₀ - ((k + 1 : ℕ) : ℤ) - 1 + 1 = n₀ - k - 1 by push_cast; ring] at *
      linarith
  refine ⟨n₀, fun n hn => ?_⟩
  rcases lt_or_gt_of_ne hn with h | h
  · have := hbwd (n₀ - n - 1).toNat
    rwa [show n₀ - ((n₀ - n - 1).toNat : ℤ) - 1 = n by omega] at this
  · have := hfwd (n - n₀ - 1).toNat
    rwa [show n₀ + ((n - n₀ - 1).toNat : ℤ) + 1 = n by omega] at this

end GlobalTheory.PSer.Uniq

namespace GlobalTheory.PSer.Uniq

theorem exists_unique_max_term : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (s : ℝ), 2 ≤ h → 0 < s → s < 1 →
    ∃ j : ℕ, j < 2 ∧ ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ →
      ‖(l : ℂ_[l])‖ ^ (-n) * s ^ ((l : ℝ) ^ (n * h + j : ℤ)) <
        ‖(l : ℂ_[l])‖ ^ (-n₀) * s ^ ((l : ℝ) ^ (n₀ * h + j : ℤ)) := by
  intro l _ h s hh hs0 hs1
  have hlp : l.Prime := Fact.out
  have hν1 : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hν0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hlp.ne_zero)
  set ν := ‖(l : ℂ_[l])‖ with hν
  have hL : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hL0 : (0 : ℝ) < l := by linarith
  have hls : Real.log s < 0 := Real.log_neg hs0 hs1
  have hlν : Real.log ν < 0 := Real.log_neg hν0 hν1
  have hq : (1 : ℝ) < (l : ℝ) ^ h := one_lt_pow₀ hL (by omega)
  set c : ℝ := ((l : ℝ) ^ h - 1) * Real.log s with hc_def
  have hc : c < 0 := mul_neg_of_pos_of_neg (by linarith) hls
  let u : ℕ → ℤ → ℝ := fun j n => (l : ℝ) ^ (n * h + j : ℤ)
  let f : ℕ → ℤ → ℝ := fun j n => -(n : ℝ) * Real.log ν + u j n * Real.log s
  let d : ℕ → ℤ → ℝ := fun j n => -Real.log ν + u j n * c
  have hu_succ : ∀ j n, u j (n + 1) = u j n * (l : ℝ) ^ h := fun j n => by
    simp only [u]
    rw [show ((n + 1) * (h : ℤ) + (j : ℤ)) = (n * h + j) + ((h : ℕ) : ℤ) by ring,
      zpow_add₀ hL0.ne', zpow_natCast]
  have hd : ∀ j n, f j (n + 1) = f j n + d j n := by
    intro j n
    simp only [f, d, hc_def]
    rw [hu_succ]
    push_cast
    ring
  have hmono : ∀ j, StrictMono (u j) := fun j a b hab => by
    simp only [u]
    apply zpow_lt_zpow_right₀ hL
    have : (0 : ℤ) < (b - a) * h := mul_pos (by omega) (by omega)
    linarith
  have hanti : ∀ j, StrictAnti (d j) := fun j a b hab => by
    simp only [d]
    have := mul_lt_mul_of_neg_right (hmono j hab) hc
    linarith
  set B : ℝ := Real.log ν / c with hB_def
  have hB : 0 < B := div_pos_of_neg_of_neg hlν hc
  have hBc : B * c = Real.log ν := div_mul_cancel₀ _ hc.ne
  have hpos : ∀ j, ∃ m, 0 < d j m := fun j => by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hB (inv_lt_one_of_one_lt₀ hL)
    refine ⟨-((k : ℤ) + j), ?_⟩
    have h1 : u j (-((k : ℤ) + j)) ≤ (l : ℝ) ^ (-(k : ℤ)) := by
      simp only [u]
      apply zpow_le_zpow_right₀ hL.le
      have : (0 : ℤ) ≤ ((k : ℤ) + j) * ((h : ℤ) - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
    have h2 : (l : ℝ) ^ (-(k : ℤ)) = ((l : ℝ)⁻¹) ^ k := by rw [zpow_neg, zpow_natCast, inv_pow]
    have h3 : u j (-((k : ℤ) + j)) < B := by rw [h2] at h1; exact h1.trans_lt hk
    have := mul_lt_mul_of_neg_right h3 hc
    simp only [d]
    linarith
  have hneg : ∀ j, ∃ m, d j m < 0 := fun j => by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B hL
    refine ⟨k, ?_⟩
    have h1 : (l : ℝ) ^ ((k : ℤ)) ≤ u j k := by
      simp only [u]
      apply zpow_le_zpow_right₀ hL.le
      have : (0 : ℤ) ≤ (k : ℤ) * ((h : ℤ) - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
    rw [zpow_natCast] at h1
    have := mul_lt_mul_of_neg_right (hk.trans_le h1) hc
    simp only [d]
    linarith
  have htie : ∀ n n', d 0 n = 0 → d 1 n' = 0 → False := by
    intro n n' h0 h1
    have e1 : u 0 n * c = u 1 n' * c := by simp only [d] at h0 h1; linarith
    have e2 := (zpow_right_strictMono₀ hL).injective (mul_right_cancel₀ hc.ne e1)
    push_cast at e2
    have hdvd : (h : ℤ) ∣ 1 := ⟨n - n', by linear_combination -e2⟩
    have := Int.eq_one_of_dvd_one (by positivity) hdvd
    omega
  have hfin : ∀ j, (∀ n, d j n ≠ 0) → ∃ n₀ : ℤ, ∀ n, n ≠ n₀ →
      ν ^ (-n) * s ^ (u j n) < ν ^ (-n₀) * s ^ (u j n₀) := by
    intro j hne
    obtain ⟨n₀, hn₀⟩ := exists_strict_max (f j) (d j) (hd j) (hanti j) hne (hpos j) (hneg j)
    refine ⟨n₀, fun n hn => ?_⟩
    have hT : ∀ m, Real.log (ν ^ (-m) * s ^ (u j m)) = f j m := fun m => by
      rw [Real.log_mul (zpow_pos hν0 _).ne' (Real.rpow_pos_of_pos hs0 _).ne', Real.log_zpow,
        Real.log_rpow hs0]
      simp only [f]
      push_cast
      ring
    rw [← Real.log_lt_log_iff (mul_pos (zpow_pos hν0 _) (Real.rpow_pos_of_pos hs0 _))
      (mul_pos (zpow_pos hν0 _) (Real.rpow_pos_of_pos hs0 _)), hT, hT]
    exact hn₀ n hn
  by_cases H : ∀ n, d 0 n ≠ 0
  · exact ⟨0, by norm_num, hfin 0 H⟩
  · push_neg at H
    obtain ⟨n, hn⟩ := H
    exact ⟨1, by norm_num, hfin 1 fun n' hn' => htie n n' hn hn'⟩

end GlobalTheory.PSer.Uniq
end
