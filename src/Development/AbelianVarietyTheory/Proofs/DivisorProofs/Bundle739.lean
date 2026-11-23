module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut

namespace RankOnePf

variable {W : Type} [AddCommGroup W] [Module ℚ W]

theorem rankOne_H_X_pow (X H : Module.End ℚ W) (hHX : ∀ w, H (X w) = X (H w) + (2 : ℚ) • X w)
    (k : ℕ) (w : W) : H ((X ^ k) w) = (X ^ k) (H w) + ((2 * k : ℕ) : ℚ) • (X ^ k) w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [ih, hHX, map_add (f := _), map_smul]
    push_cast
    module

theorem rankOne_H_Y_pow (Y H : Module.End ℚ W) (hHY : ∀ w, H (Y w) = Y (H w) - (2 : ℚ) • Y w)
    (k : ℕ) (w : W) : H ((Y ^ k) w) = (Y ^ k) (H w) - ((2 * k : ℕ) : ℚ) • (Y ^ k) w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [ih, hHY, map_sub, map_smul]
    push_cast
    module

theorem rankOne_X_Y_pow (X Y H : Module.End ℚ W) (hXY : ∀ w, X (Y w) = Y (X w) + H w)
    (hHY : ∀ w, H (Y w) = Y (H w) - (2 : ℚ) • Y w) (k : ℕ) (w : W) :
    X ((Y ^ (k + 1)) w) = (Y ^ (k + 1)) (X w) + ((k + 1 : ℕ) : ℚ) • (Y ^ k) (H w)
      - (((k + 1) * k : ℕ) : ℚ) • (Y ^ k) w := by
  induction k generalizing w with
  | zero => simp [hXY]
  | succ k ih =>
    have h1 : (Y ^ (k + 1 + 1)) w = (Y ^ (k + 1)) (Y w) := by
      rw [pow_succ Y (k + 1), Module.End.mul_apply]
    rw [h1, ih, hXY, hHY]
    simp only [map_add (f := _), map_sub, map_smul, pow_succ, Module.End.mul_apply]
    push_cast
    module

theorem rankOne_coef_succ (n : ℕ) :
    coef 0 (n + 1) * (((n + 1) * (n + 1 + 1) : ℕ) : ℚ) = - coef 0 n := by
  have h1 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [coef, Nat.factorial_succ, add_zero, Nat.factorial_zero]
  push_cast
  field_simp
  ring

end RankOnePf

end GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut


open RankOnePf in
theorem rankOne : RankOne := by
  intro W _ _ N K D hG hB o q ho hq hoq T hoT hqT
  have hqo : q ≠ o := Ne.symm hoq
  have hH : ∀ x, (D o o - D q q) x = D o o x - D q q x := fun x => rfl
  have hHT : (D o o - D q q) T = 0 := by rw [hH, hoT, hqT, sub_zero]
  have hXY : ∀ w, D o q (D q o w) = D q o (D o q w) + (D o o - D q q) w := by
    intro w
    have e := LinearMap.congr_fun (hG o q q o ho hq hq ho) w
    rw [if_pos (rfl : q = q), if_pos (rfl : o = o)] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    rw [hH]
    exact sub_eq_iff_eq_add'.mp e
  have hHX : ∀ w, (D o o - D q q) (D o q w) = D o q ((D o o - D q q) w) + (2 : ℚ) • D o q w := by
    intro w
    have e1 := LinearMap.congr_fun (hG o o o q ho ho ho hq) w
    rw [if_pos (rfl : o = o), if_neg hqo] at e1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, sub_zero] at e1
    have e2 := LinearMap.congr_fun (hG q q o q hq hq ho hq) w
    rw [if_neg hqo, if_pos (rfl : q = q)] at e2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, zero_sub, LinearMap.neg_apply] at e2
    rw [hH, hH, map_sub, sub_eq_iff_eq_add'.mp e1, sub_eq_iff_eq_add'.mp e2]
    module
  have hHY : ∀ w, (D o o - D q q) (D q o w) = D q o ((D o o - D q q) w) - (2 : ℚ) • D q o w := by
    intro w
    have e1 := LinearMap.congr_fun (hG o o q o ho ho hq ho) w
    rw [if_neg hoq, if_pos (rfl : o = o)] at e1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, zero_sub, LinearMap.neg_apply] at e1
    have e2 := LinearMap.congr_fun (hG q q q o hq hq hq ho) w
    rw [if_pos (rfl : q = q), if_neg hoq] at e2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, sub_zero] at e2
    rw [hH, hH, map_sub, sub_eq_iff_eq_add'.mp e1, sub_eq_iff_eq_add'.mp e2]
    module
  constructor
  ·
    have hterm : ∀ m : ℕ, D o q ((D q o ^ (m + 1)) ((D o q ^ (m + 1)) T)) =
        (D q o ^ (m + 1)) ((D o q ^ (m + 1 + 1)) T) +
          (((m + 1) * (m + 1 + 1) : ℕ) : ℚ) • (D q o ^ m) ((D o q ^ (m + 1)) T) := by
      intro m
      have hx : D o q ((D o q ^ (m + 1)) T) = (D o q ^ (m + 1 + 1)) T := by
        rw [pow_succ' (D o q) (m + 1), Module.End.mul_apply]
      rw [rankOne_X_Y_pow _ _ _ hXY hHY, rankOne_H_X_pow _ _ hHX, hHT, map_zero, zero_add, hx,
        map_smul]
      push_cast
      module
    have hsum : ∀ n : ℕ, D o q (∑ k ∈ Finset.range (n + 1), coef 0 k • (D q o ^ k) ((D o q ^ k) T)) =
        coef 0 n • (D q o ^ n) ((D o q ^ (n + 1)) T) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, map_add (f := _), ih, map_smul, hterm n]
        have hc := rankOne_coef_succ n
        rw [show coef 0 n = -(coef 0 (n + 1) * (((n + 1) * (n + 1 + 1) : ℕ) : ℚ)) by rw [hc, neg_neg]]
        module
    have hXK : (D o q ^ (K + 1)) T = 0 := by
      refine hB o ho q hq ((2 * (K + 1) : ℕ) : ℤ) _ ?_ (by push_cast; omega)
      have h := rankOne_H_X_pow _ _ hHX (K + 1) T
      rw [hHT, map_zero, zero_add, hH] at h
      rw [Int.cast_natCast]
      exact h
    have hp : proj K 0 (D o q) (D q o) T =
        ∑ k ∈ Finset.range (K + 1), coef 0 k • (D q o ^ k) ((D o q ^ k) T) := by
      simp only [proj, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    rw [hp, hsum K, hXK, map_zero, smul_zero]
  ·
    intro hXT
    have hYterm : ∀ k : ℕ, D o q ((D q o ^ (k + 1)) T) = -((((k + 1) * k : ℕ) : ℚ)) • (D q o ^ k) T := by
      intro k
      rw [rankOne_X_Y_pow _ _ _ hXY hHY, hXT, hHT, map_zero, map_zero, smul_zero, add_zero, zero_sub,
        neg_smul]
    have hYK : (D q o ^ (K + 1)) T = 0 := by
      refine hB q hq o ho ((2 * (K + 1) : ℕ) : ℤ) _ ?_ (by push_cast; omega)
      have h := rankOne_H_Y_pow _ _ hHY (K + 1) T
      rw [hHT, map_zero, zero_sub, hH] at h
      rw [Int.cast_natCast, ← neg_sub, h, neg_neg]
    have hdesc : ∀ d i : ℕ, i + d = K → (D q o ^ (i + 1)) T = 0 := by
      intro d
      induction d with
      | zero =>
        intro i hi
        rw [add_zero] at hi
        subst hi
        exact hYK
      | succ d ih =>
        intro i hi
        have h2 := ih (i + 1) (by omega)
        have h3 := hYterm (i + 1)
        rw [h2, map_zero] at h3
        rcases smul_eq_zero.mp h3.symm with h | h
        · exfalso
          have : ((((i + 1 + 1) * (i + 1) : ℕ) : ℚ)) ≠ 0 := by positivity
          exact this (neg_eq_zero.mp h)
        · exact h
    have := hdesc K 0 (by omega)
    simpa using this

end GlobalTheory.LeviCut
end

section

open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut.StepScalarProof

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem adj_apply' (x S : Module.End ℚ V) : adj x S = x * S - S * x := by
  simp [adj]

theorem H_pow (F H : Module.End ℚ V) (v : V) (n : ℕ)
    (hHF : H * F - F * H = -(F + F)) (hv : H v = (n : ℚ) • v) :
    ∀ i : ℕ, H ((F ^ i) v) = ((n : ℚ) - 2 * i) • (F ^ i) v := by
  have h1 : H * F = F * H - (F + F) := by
    calc H * F = (H * F - F * H) + F * H := by abel
      _ = F * H - (F + F) := by rw [hHF]; abel
  intro i
  induction i with
  | zero => simp [hv]
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply (f := H), h1]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, ih, map_smul]
    push_cast
    module

theorem E_pow (E F H : Module.End ℚ V) (v : V) (n : ℕ)
    (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F)) (hE : E v = 0) (hv : H v = (n : ℚ) • v) :
    ∀ i : ℕ, E ((F ^ (i + 1)) v) = (((i : ℚ) + 1) * ((n : ℚ) - i)) • (F ^ i) v := by
  have h1 : E * F = F * E + H := by
    calc E * F = (E * F - F * E) + F * E := by abel
      _ = F * E + H := by rw [hEF]; abel
  have hH := H_pow F H v n hHF hv
  intro i
  induction i with
  | zero =>
    rw [pow_one, ← Module.End.mul_apply (f := E), h1]
    simp [hE, hv]
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply (f := E), h1]
    simp only [LinearMap.add_apply, Module.End.mul_apply, ih, map_smul, hH]
    rw [← Module.End.mul_apply (f := F), ← pow_succ']
    push_cast
    module

theorem adjE_pow (E F H T : Module.End ℚ V) (v : V) (n : ℕ)
    (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F)) (hE : E v = 0) (hv : H v = (n : ℚ) • v)
    (hT : ∀ k : ℕ, 0 < k → T ((F ^ k) v) = 0) :
    ∀ k : ℕ, (∀ i, k < i → (((adj E) ^ k) T) ((F ^ i) v) = 0) ∧
      (((adj E) ^ k) T) ((F ^ k) v) =
        ((-1 : ℚ) ^ k * (k.factorial : ℚ) * ∏ t ∈ Finset.range k, ((n : ℚ) - t)) • T v := by
  have hEp := E_pow E F H v n hEF hHF hE hv
  intro k
  induction k with
  | zero =>
    refine ⟨fun i hi => ?_, by simp⟩
    simpa using hT i hi
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hstep : ∀ y, (((adj E) ^ (k + 1)) T) y = E ((((adj E) ^ k) T) y) - (((adj E) ^ k) T) (E y) := by
      intro y
      rw [pow_succ', Module.End.mul_apply, adj_apply']
      simp [Module.End.mul_apply]
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [hstep, hEp, map_smul, ih1 i' (by omega), ih1 (i' + 1) (by omega)]
      simp
    · rw [hstep, hEp, map_smul, ih1 (k + 1) (by omega), ih2, smul_smul, Finset.prod_range_succ,
        Nat.factorial_succ]
      simp only [map_zero, zero_sub]
      rw [← neg_smul]
      congr 1
      push_cast
      ring

theorem phi_adjF_pow (F : Module.End ℚ V) (φ : V →ₗ[ℚ] ℚ) (hφ : ∀ x, φ (F x) = 0) :
    ∀ (k : ℕ) (S : Module.End ℚ V) (y : V), φ ((((adj F) ^ k) S) y) = (-1 : ℚ) ^ k * φ (S ((F ^ k) y)) := by
  intro k
  induction k with
  | zero => intro S y; simp
  | succ k ih =>
    intro S y
    rw [pow_succ, Module.End.mul_apply, ih, adj_apply']
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hφ, zero_sub]
    rw [← Module.End.mul_apply (f := F), ← pow_succ', pow_succ]
    ring

theorem partial_sum (n j : ℕ) :
    ∀ K : ℕ, ((n : ℚ) + j + 1) * ∑ k ∈ Finset.range (K + 1),
        (-1 : ℚ) ^ k * (j.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) / ((k + j + 1).factorial : ℚ) =
      1 + (-1 : ℚ) ^ K * (j.factorial : ℚ) * (∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t)) /
        ((K + j + 1).factorial : ℚ) := by
  intro K
  induction K with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, Finset.prod_range_zero, one_mul, Finset.prod_range_one,
      Nat.cast_zero, sub_zero]
    rw [Nat.factorial_succ j]
    have h : (j.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have e1 : K + 1 + j + 1 = (K + j + 1) + 1 := by ring
    rw [e1, Nat.factorial_succ (K + j + 1), Finset.prod_range_succ _ (K + 1)]
    have h : ((K + j + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    generalize ((K + j + 1).factorial : ℚ) = f at h ⊢
    generalize (∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t)) = P
    field_simp
    ring

theorem stepScalar : StepScalar := by
  intro V _ _ E F H T v φ n K j hEF hHF hE hv hnK hφ hT
  have hA := adjE_pow E F H T v n hEF hHF hE hv hT
  have hB := phi_adjF_pow F φ hφ
  have hterm : ∀ k : ℕ, φ ((((adj F) ^ k * (adj E) ^ k) T) v) =
      (k.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) * φ (T v) := by
    intro k
    rw [Module.End.mul_apply, hB, (hA k).2, map_smul, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  have hP : ∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t) = 0 :=
    Finset.prod_eq_zero (i := n) (Finset.mem_range.2 (by omega)) (sub_self _)
  have hS := partial_sum n j K
  simp only [hP, mul_zero, zero_div, add_zero] at hS

  simp only [proj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul,
  hterm]
  have hc : ∀ k : ℕ, coef j k * ((k.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) * φ (T v)) =
      (-1 : ℚ) ^ k * (j.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) / ((k + j + 1).factorial : ℚ) *
        φ (T v) := by
    intro k
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((k + j + 1).factorial : ℚ) ≠ 0 := by positivity
    simp only [coef]
    field_simp
  simp only [hc, ← Finset.sum_mul]
  rw [mul_comm, ← mul_assoc, hS, one_mul]

end GlobalTheory.LeviCut.StepScalarProof
end

section

open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut.GridIntProof

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem adj_pow_apply (x U : Module.End ℚ V) (k : ℕ) :
    (adj x ^ k) U = ∑ t ∈ Finset.range (k + 1),
      (((-1 : ℚ) ^ (k - t) * (k.choose t : ℚ)) • (x ^ t * U * x ^ (k - t))) := by
  have hc : Commute (LinearMap.mulLeft ℚ x) ((-1 : ℚ) • LinearMap.mulRight ℚ x) :=
    (LinearMap.commute_mulLeft_right x x).smul_right _
  have h1 : adj x = LinearMap.mulLeft ℚ x + (-1 : ℚ) • LinearMap.mulRight ℚ x := by
    simp [adj, sub_eq_add_neg]
  rw [h1, hc.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul ℚ, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]

def IntOn (L M : Submodule ℤ V) (c : ℕ) (U : Module.End ℚ V) : Prop := ∀ x ∈ L, ((c : ℕ) : ℤ) • U x ∈ M

theorem intOn_divAdj (L M : Submodule ℤ V) (e : Module.End ℚ V)
    (hL : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (e ^ k) x ∈ L)
    (hM : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (e ^ k) x ∈ M)
    (c : ℕ) (U : Module.End ℚ V) (hU : IntOn L M c U) (k : ℕ) :
    IntOn L M c (((k.factorial : ℚ)⁻¹) • (adj e ^ k) U) := by
  intro y hy
  have hE : ((c : ℕ) : ℤ) • (((k.factorial : ℚ)⁻¹ • (adj e ^ k) U) y) =
      ∑ t ∈ Finset.range (k + 1), ((-1 : ℤ) ^ (k - t)) • ((t.factorial : ℚ)⁻¹ •
        (e ^ t) (((c : ℕ) : ℤ) • U (((k - t).factorial : ℚ)⁻¹ • (e ^ (k - t)) y))) := by
    rw [LinearMap.smul_apply, adj_pow_apply, LinearMap.sum_apply, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have hch := Nat.choose_mul_factorial_mul_factorial ht'
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      LinearMap.sum_apply, Finset.smul_sum]
    congr 1
    have h1 : ((k.choose t : ℕ) : ℚ) * (t.factorial : ℚ) * ((k - t).factorial : ℚ) = (k.factorial : ℚ) := by
      exact_mod_cast hch
    have h2 : (t.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((k - t).factorial : ℚ) ≠ 0 := by positivity
    have h4 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h5 : ((k.choose t : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos ht').ne'
    rw [← h1]
    push_cast
    field_simp
  rw [hE]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
  exact hM t _ (hU _ (hL (k - t) y hy))

theorem intOn_proj (L M : Submodule ℤ V) (X Y : Module.End ℚ V)
    (hLX : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (X ^ k) x ∈ L)
    (hMX : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (X ^ k) x ∈ M)
    (hLY : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (Y ^ k) x ∈ L)
    (hMY : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (Y ^ k) x ∈ M)
    (K j₀ Λ : ℕ) (hΛ : ∀ k ≤ K, (j₀ + k + 1).factorial ∣ Λ * (j₀.factorial * k.factorial))
    (c : ℕ) (U : Module.End ℚ V) (hU : IntOn L M c U) :
    IntOn L M (c * Λ) (proj K j₀ (adj X) (adj Y) U) := by
  intro y hy
  simp only [proj, LinearMap.sum_apply, Finset.smul_sum]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨m, hm⟩ := hΛ k hkK
  have hE : ((c * Λ : ℕ) : ℤ) • ((coef j₀ k • (adj Y ^ k * adj X ^ k)) U) y =
      ((-1 : ℤ) ^ k * (m : ℤ)) • (((c : ℕ) : ℤ) • (((k.factorial : ℚ)⁻¹ • (adj Y ^ k)
        ((k.factorial : ℚ)⁻¹ • (adj X ^ k) U)) y)) := by
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    have h2 : (j₀.factorial : ℚ) ≠ 0 := by positivity
    have h3 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h4 : ((j₀ + k + 1).factorial : ℚ) ≠ 0 := by positivity
    have hΛq : (Λ : ℚ) = ((j₀ + k + 1).factorial : ℚ) * (m : ℚ) / ((j₀.factorial : ℚ) * (k.factorial : ℚ)) := by
      rw [eq_div_iff (by positivity)]
      exact_mod_cast hm
    have hkj : k + j₀ + 1 = j₀ + k + 1 := by omega
    simp only [coef, hkj]
    push_cast
    rw [hΛq]
    field_simp
  rw [hE]
  refine Submodule.smul_mem _ _ ?_
  exact intOn_divAdj L M Y hLY hMY c _ (intOn_divAdj L M X hLX hMX c U hU k) k y hy

theorem intOn_listProd (L M : Submodule ℤ V) (n : ℕ) :
    ∀ (l : List (Module.End ℚ (Module.End ℚ V))), (∀ f ∈ l, ∀ c U, IntOn L M c U → IntOn L M (c * n) (f U)) →
      ∀ c U, IntOn L M c U → IntOn L M (c * n ^ l.length) (l.prod U)
  | [], _, c, U, hU => by simpa using hU
  | f :: l, hf, c, U, hU => by
      rw [List.prod_cons, Module.End.mul_apply, List.length_cons, pow_succ, ← mul_assoc]
      exact hf f (List.mem_cons_self ..) _ _
        (intOn_listProd L M n l (fun g hg => hf g (List.mem_cons_of_mem _ hg)) c U hU)

end GlobalTheory.LeviCut.GridIntProof

namespace GlobalTheory.LeviCut


open GridIntProof in
theorem gridInt_holds : GridInt := by
  intro V _ _ a b K w Λ e L M hL hM hw hΛ c T hT
  have hstep : ∀ i < a, ∀ j, a ≤ j → j < a + b → ∀ (c : ℕ) (U : Module.End ℚ V), IntOn L M c U →
      IntOn L M (c * Λ) (rootP (fun c d => adj (e c d)) K i j U) := by
    intro i hi j hj1 hj2 c U hU
    have hij : i ≠ j := by omega
    have hji : j ≠ i := by omega
    exact intOn_proj L M (e i j) (e j i) (fun k x hx => hL i (by omega) j hj2 hij k x hx)
      (fun k x hx => hM i (by omega) j hj2 hij k x hx) (fun k x hx => hL j hj2 i (by omega) hji k x hx)
      (fun k x hx => hM j hj2 i (by omega) hji k x hx) K (j - i - 1) Λ (fun k hk => hΛ _ _ (by omega)) c U hU
  have hrow : ∀ i < a, ∀ (c : ℕ) (U : Module.End ℚ V), IntOn L M c U →
      IntOn L M (c * Λ ^ b) (rowP (fun c d => adj (e c d)) K i a b U) := by
    intro i hi c U hU
    have h := intOn_listProd L M Λ ((List.range' a b).map (rootP (fun c d => adj (e c d)) K i)) (by
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      rw [List.mem_range'_1] at hj
      exact hstep i hi j hj.1 hj.2) c U hU
    simpa [rowP] using h
  have h := intOn_listProd L M (Λ ^ b) ((List.range a).reverse.map fun i => rowP (fun c d => adj (e c d)) K i a b)
    (by
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨i, hi, rfl⟩ := hf
      rw [List.mem_reverse, List.mem_range] at hi
      exact hrow i hi) c T hT
  have e1 : (Λ ^ b) ^ ((List.range a).reverse.map fun i => rowP (fun c d => adj (e c d)) K i a b).length =
      Λ ^ (a * b) := by
    simp [← pow_mul, mul_comm]
  rw [e1] at h
  exact h

end GlobalTheory.LeviCut
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.thickSet_density_le_inv_four_Lw : ∀ (D : D7) (L : SizeData₂ D), 8 * D.host.Lw < D.R.n → L.de2 ≤ 1 / (4 * (D.host.Lw : ℝ)) := by
  first | exact @GlobalTheory.thick_density_le | exact GlobalTheory.thick_density_le | (intros; apply GlobalTheory.thick_density_le <;> assumption)
end
