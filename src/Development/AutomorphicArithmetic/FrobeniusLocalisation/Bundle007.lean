module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle005
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle004
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdArith
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem arith {l : ℕ} (hl : l.Prime) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (1 - ((l ^ j).totient : ℝ) / ((l ^ (k + 1)).totient : ℝ)) =
      ((k + 1 : ℕ) : ℝ) - 1 / ((l : ℝ) - 1) := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hs : (∑ j ∈ Finset.range (k + 1), ((l ^ j).totient : ℝ)) = (l : ℝ) ^ k := by
    exact_mod_cast Formalism.HC.Der.Rd.sum_totient_pow hl k
  rw [hs, Nat.totient_prime_pow_succ hl]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (l : ℝ) - 1 ≠ 0 := by linarith
  have hp : (l : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by linarith)
  push_cast [Nat.cast_sub hl.one_le]
  congr 1
  rw [div_mul_eq_div_div, div_self hp]

private theorem intCast_mul_mul_mul_eq_of_mul_eq {l : ℕ} (hl : l.Prime) {j e c : ℕ} (hje : j ≤ e)
    (hd : c ∣ (l ^ e).totient / (l ^ j).totient) :
    1 - 1 / (c : ℝ) ≤ 1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ) := by
  have hjd : (l ^ j).totient ∣ (l ^ e).totient := Nat.totient_dvd_of_dvd (pow_dvd_pow l hje)
  have hj0 : 0 < (l ^ j).totient := Nat.totient_pos.2 (pow_pos hl.pos j)
  have he0 : 0 < (l ^ e).totient := Nat.totient_pos.2 (pow_pos hl.pos e)
  have hq0 : 0 < (l ^ e).totient / (l ^ j).totient := Nat.div_pos (Nat.le_of_dvd he0 hjd) hj0
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos hd hq0
  have hcle : c ≤ (l ^ e).totient / (l ^ j).totient := Nat.le_of_dvd hq0 hd
  have hq : (((l ^ e).totient / (l ^ j).totient : ℕ) : ℝ) =
      ((l ^ e).totient : ℝ) / ((l ^ j).totient : ℝ) :=
    Nat.cast_div hjd (by exact_mod_cast hj0.ne')
  have h1 : (1 : ℝ) / (((l ^ e).totient / (l ^ j).totient : ℕ) : ℝ) ≤ 1 / (c : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast hc0) (by exact_mod_cast hcle)
  rw [hq, one_div_div] at h1
  linarith

theorem UpperTheory.HF.vd_le :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → H.vdH l ≤ (H.sl l : ℝ) - 1 / ((l : ℝ) - 1) ∧ H.vdH l ≤ (H.condE.factorization l : ℝ) := by
  intro φ H l hl
  have heN := (layer_bot H.toHostRaw hl (Nat.zero_le (H.condN.factorization l))).2.2
  simp only [UpperTheory.HF.Formalism.HC.HostRaw.sl]
  generalize hE : (UpperTheory.HF.Formalism.HC.HostRaw.condE H.toHostRaw).factorization l = e at heN ⊢
  have hcard : ∀ j ∈ Finset.range (H.condN.factorization l),
      (1 - 1 / (Nat.card (UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw
        (H.condN / l ^ H.condN.factorization l * l ^ j)) : ℝ)) ≤
      if j < e then 1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ) else 0 := by
    intro j hj
    have hjN : j ≤ H.condN.factorization l := (Finset.mem_range.1 hj).le
    obtain ⟨hbot, hdvd, -⟩ := layer_bot H.toHostRaw hl hjN
    rw [hE] at hbot hdvd
    split_ifs with hje
    · exact intCast_mul_mul_mul_eq_of_mul_eq hl hje.le (hdvd hje.le)
    · push_neg at hje
      rw [hbot.2 hje, Subgroup.card_bot]
      simp
  have hsum := Finset.sum_le_sum hcard
  rw [← vd_formula H hl] at hsum
  have hS : ∑ j ∈ Finset.range (H.condN.factorization l),
      (if j < e then 1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ) else 0) =
      ∑ j ∈ Finset.range e, (1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ)) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le heN
    rw [hm, Finset.sum_range_add]
    have h2 : ∑ x ∈ Finset.range m,
        (if e + x < e then 1 - ((l ^ (e + x)).totient : ℝ) / ((l ^ e).totient : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero (fun x _ => if_neg (by omega))
    rw [h2, add_zero]
    exact Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.1 hj))
  rw [hS] at hsum
  have hle : ∑ j ∈ Finset.range e, (1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ)) ≤ (e : ℝ) := by
    calc _ ≤ ∑ j ∈ Finset.range e, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => sub_le_self 1 (by positivity))
      _ = e := by simp
  refine ⟨?_, hsum.trans hle⟩
  rcases e with _ | k
  · have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
    have h1 : 1 / ((l : ℝ) - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    simp only [Finset.range_zero, Finset.sum_empty] at hsum
    simp only [Nat.zero_eq, zero_le, max_eq_left, Nat.cast_one]
    linarith
  · rw [arith hl k] at hsum
    rw [max_eq_right (by omega)]
    exact hsum
end

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem half_le {c : ℕ} (h : 2 ≤ c) : (1 : ℝ) / 2 ≤ 1 - 1 / (c : ℝ) := by
  have h2 : (2 : ℝ) ≤ c := by exact_mod_cast h
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2
  linarith

private theorem term_nonneg {c : ℕ} (h : 0 < c) : (0 : ℝ) ≤ 1 - 1 / (c : ℝ) := by
  have hc : (1 : ℝ) ≤ c := by exact_mod_cast h
  have h1 : 1 / (c : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hc
  linarith

theorem UpperTheory.HF.vd_tame_wild :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → (¬ l ∣ H.el l → H.vdH l = 1 - 1 / (H.el l : ℝ)) ∧ (l ∣ H.el l → 1 ≤ H.vdH l) ∧ (¬ l ∣ H.el l → H.sl l = 1) := by
  intro φ H l hl
  set v := H.condN.factorization l with hv
  set e := (HostRaw.condE H.toHostRaw).factorization l with he
  let G : ℕ → Subgroup φ.GG := fun j => HostRaw.imgOne H.toHostRaw (H.condN / l ^ v * l ^ j)
  have hev : e ≤ v := (layer_bot H.toHostRaw (j := 0) hl (Nat.zero_le _)).2.2
  have hbot : ∀ j, j ≤ v → (G j = ⊥ ↔ e ≤ j) := fun j hj => (layer_bot H.toHostRaw hl hj).1
  have hdvd : ∀ j, j ≤ e → Nat.card (G j) ∣ (l ^ e).totient / (l ^ j).totient :=
    fun j hj => (layer_bot H.toHostRaw hl (hj.trans hev)).2.1 hj
  have hcard_one : ∀ j, j ≤ v → (Nat.card (G j) = 1 ↔ e ≤ j) :=
    fun j hj => Subgroup.card_eq_one.trans (hbot j hj)
  have hpos : ∀ j, j ≤ v → 0 < Nat.card (G j) := by
    intro j hjv
    by_cases hje : j ≤ e
    · have h1 : (l ^ j).totient ∣ (l ^ e).totient := Nat.totient_dvd_of_dvd (pow_dvd_pow l hje)
      have h2 : 0 < (l ^ j).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
      have h3 : 0 < (l ^ e).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
      exact Nat.pos_of_dvd_of_pos (hdvd j hje) (Nat.div_pos (Nat.le_of_dvd h3 h1) h2)
    · push_neg at hje
      rw [(hcard_one j hjv).2 hje.le]
      exact Nat.one_pos
  have hge : ∀ j, j < e → 2 ≤ Nat.card (G j) := by
    intro j hj
    have hjv : j ≤ v := by omega
    have h1 := hpos j hjv
    have h2 : Nat.card (G j) ≠ 1 := fun h => by
      have := (hcard_one j hjv).1 h
      omega
    omega
  have hanti : 1 ≤ v → Nat.card (G 1) ∣ Nat.card (G 0) := by
    intro h1v
    apply Subgroup.card_dvd_of_le
    apply HostRaw.imgOne_anti _ (mul_dvd_mul_left _ (pow_dvd_pow l (by norm_num)))
    calc H.condN / l ^ v * l ^ 1 ∣ H.condN / l ^ v * l ^ v := mul_dvd_mul_left _ (pow_dvd_pow l h1v)
      _ = H.condN := Nat.div_mul_cancel (Nat.ordProj_dvd _ _)
  have hel : H.el l = Nat.card (G 0) := by
    show Nat.card (HostRaw.imgOne H.toHostRaw (H.condN / l ^ v)) =
      Nat.card (HostRaw.imgOne H.toHostRaw (H.condN / l ^ v * l ^ 0))
    rw [pow_zero, mul_one]
  have hsum : H.vdH l = ∑ j ∈ Finset.range v, (1 - 1 / (Nat.card (G j) : ℝ)) := vd_formula H hl
  have hsl : H.sl l = max 1 e := rfl
  have key1 : ¬ l ∣ H.el l → e ≤ 1 := by
    intro hnd
    by_contra hlt
    push_neg at hlt
    have h1v : 1 ≤ v := by omega
    have hd := hdvd 1 hlt.le
    rw [Nat.totient_prime_pow hl (by omega), pow_one, Nat.totient_prime hl,
      Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hl.one_lt)] at hd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hl).1 hd
    have hne : Nat.card (G 1) ≠ 1 := fun h => by
      have := (hcard_one 1 h1v).1 h
      omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hk')
    have hl1 : l ∣ Nat.card (G 1) := hk' ▸ dvd_pow_self l hk0
    exact hnd (hel ▸ hl1.trans (hanti h1v))
  have key2 : l ∣ H.el l → 2 ≤ e := by
    intro hd
    rw [hel] at hd
    by_contra hlt
    have hcases : e = 0 ∨ e = 1 := by omega
    rcases hcases with h0 | h1
    · rw [(hcard_one 0 (Nat.zero_le _)).2 (by omega)] at hd
      exact hl.not_dvd_one hd
    · have hd0 := hdvd 0 (by omega)
      rw [h1] at hd0
      simp [Nat.totient_prime hl] at hd0
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hl.one_lt) (hd.trans hd0)
      have := hl.two_le
      omega
  refine ⟨fun hnd => ?_, fun hd => ?_, fun hnd => ?_⟩
  · have he1 := key1 hnd
    rw [hsum, hel]
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro j hj hj0
      have hjv : j ≤ v := (Finset.mem_range.1 hj).le
      rw [(hcard_one j hjv).2 (by omega)]
      norm_num
    · intro h0
      have hv0 : v = 0 := by simpa using h0
      rw [(hcard_one 0 (Nat.zero_le _)).2 (by omega)]
      norm_num
  · rw [hsum]
    have h2e := key2 hd
    have h2v : 2 ≤ v := h2e.trans hev
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range v := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega
    have h01 : (0 : ℕ) ≠ 1 := by norm_num
    calc (1 : ℝ) = 1 / 2 + 1 / 2 := by norm_num
      _ ≤ (1 - 1 / (Nat.card (G 0) : ℝ)) + (1 - 1 / (Nat.card (G 1) : ℝ)) :=
          add_le_add (half_le (hge 0 (by omega))) (half_le (hge 1 (by omega)))
      _ = ∑ j ∈ ({0, 1} : Finset ℕ), (1 - 1 / (Nat.card (G j) : ℝ)) :=
          (Finset.sum_pair (f := fun j => (1 - 1 / (Nat.card (G j) : ℝ))) h01).symm
      _ ≤ ∑ j ∈ Finset.range v, (1 - 1 / (Nat.card (G j) : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j hj _ => term_nonneg (hpos j (Finset.mem_range.1 hj).le))
  · rw [hsl]
    exact max_eq_left (key1 hnd)
end
