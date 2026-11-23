module

public import Formalism.PolynomialDimension.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Algebra.BigOperators.Fin
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

theorem weylDim_cons_snoc (m : ℕ) (a b : ℤ) (μ : Fin m → ℤ) :
    weylDim (m + 2) (Fin.cons a (Fin.snoc μ b) : Fin (m + 2) → ℤ) =
      weylDim m μ * (∏ j : Fin m, ((((a - μ j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) *
      (∏ j : Fin m, ((((μ j - b : ℤ)) : ℚ) + (m : ℚ) - ((j : ℕ) : ℚ)) / ((m : ℚ) - ((j : ℕ) : ℚ))) *
      (((((a - b : ℤ)) : ℚ) + (m : ℚ) + 1) / ((m : ℚ) + 1)) := by
  unfold weylDim
  simp only [Fin.prod_univ_succ (n := m + 1)]
  simp only [Fin.prod_univ_castSucc (n := m)]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last, lt_self_iff_false,
    Fin.not_lt_zero, if_false, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff,
    Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    Fin.val_zero, one_mul, mul_one]
  have hl : ∀ x : Fin m, ¬ (Fin.last m < x.castSucc) := fun x => (Fin.castSucc_lt_last x).asymm
  simp only [hl, if_false, Finset.prod_const_one, mul_one]
  push_cast
  simp only [sub_zero, ← add_assoc, add_sub_add_right_eq_sub, Finset.prod_mul_distrib]
  ring

theorem weylDim_zero (m : ℕ) : weylDim m (fun _ => (0 : ℤ)) = 1 := by
  unfold weylDim
  apply Finset.prod_eq_one; intro i _
  apply Finset.prod_eq_one; intro j _
  split_ifs with h
  · have : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≠ 0 := by
      have : (i : ℕ) < (j : ℕ) := h
      have : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast this
      linarith
    simp [this]
  · rfl

theorem weylDim_pos_of_antitone (m : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) : 0 < weylDim m μ := by
  unfold weylDim
  apply Finset.prod_pos; intro i _
  apply Finset.prod_pos; intro j _
  split_ifs with h
  · have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast (show (i : ℕ) < (j : ℕ) from h)
    have h2 : μ j ≤ μ i := hμ h.le
    have h3 : ((μ j : ℤ) : ℚ) ≤ ((μ i : ℤ) : ℚ) := by exact_mod_cast h2
    push_cast
    apply div_pos <;> linarith
  · exact one_pos

theorem weylDim_hwt (m A B : ℕ) : (weylDim (m + 2) (hwt m A B) : ℝ) =
    (∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
    (∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
    (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)) := by
  unfold hwt
  rw [weylDim_cons_snoc, weylDim_zero]
  push_cast
  simp only [sub_zero, sub_neg_eq_add, one_mul, zero_add]

theorem weylDim_cwt (m A c B : ℕ) (μ : Fin m → ℤ) : (weylDim (m + 2) (cwt m A c B μ) : ℝ) =
    (weylDim m μ : ℝ) *
    (∏ j : Fin m, ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
    (∏ j : Fin m, ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
    (((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1)) := by
  unfold cwt
  rw [weylDim_cons_snoc]
  push_cast
  simp only [sub_neg_eq_add]

theorem prod_le_pow_mul_prod (m : ℕ) (f g : Fin m → ℝ) (t : ℝ) (hf : ∀ j, 0 ≤ f j)
    (hfg : ∀ j, f j ≤ (1 + t) * g j) :
    ∏ j, f j ≤ (1 + t) ^ m * ∏ j, g j := by
  calc ∏ j, f j ≤ ∏ j, ((1 + t) * g j) := Finset.prod_le_prod₀ (fun j _ => hf j) (fun j _ => hfg j)
    _ = (1 + t) ^ m * ∏ j, g j := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem fin_sub_pos (m : ℕ) (j : Fin m) : 0 < (m : ℝ) - ((j : ℕ) : ℝ) := by
  have : ((j : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast j.isLt
  linarith

theorem cwt_bound (m A c B : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) (h0 : ∀ i, 0 ≤ μ i ∧ μ i ≤ c)
    (t : ℝ) (ht : 0 ≤ t) (hA : (c : ℝ) ≤ t * A) (hB : (c : ℝ) ≤ t * B) :
    0 ≤ (weylDim (m + 2) (cwt m A c B μ) : ℝ) ∧
    (weylDim (m + 2) (cwt m A c B μ) : ℝ) ≤
      (1 + t) ^ (2 * m + 1) * ((weylDim m μ : ℝ) * (weylDim (m + 2) (hwt m A B) : ℝ)) := by
  have hW : 0 < (weylDim m μ : ℝ) := by exact_mod_cast weylDim_pos_of_antitone m μ hμ
  have hμ0 : ∀ j, (0 : ℝ) ≤ (μ j : ℝ) := fun j => by exact_mod_cast (h0 j).1
  have hμc : ∀ j, (μ j : ℝ) ≤ (c : ℝ) := fun j => by exact_mod_cast (h0 j).2
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [weylDim_cwt, weylDim_hwt]
  have f1 : ∀ j : Fin m, 0 ≤ ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := by
    intro j
    have := hμc j
    have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    apply div_nonneg
    · linarith
    · positivity
  have f2 : ∀ j : Fin m, 0 ≤ ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) := by
    intro j; have := fin_sub_pos m j; have := hμ0 j; apply div_nonneg <;> linarith
  have f3 : 0 ≤ ((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1) := by positivity
  have P1 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) t f1
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := hμ0 j
      have : 0 ≤ t * (((j : ℕ) : ℝ) + 1) := by positivity
      nlinarith)
  have P2 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) t f2
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (fin_sub_pos m j).le
      have := hμc j
      have := fin_sub_pos m j
      have : 0 ≤ t * ((m : ℝ) - ((j : ℕ) : ℝ)) := by positivity
      nlinarith)
  have P3 : ((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1) ≤ (1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ t * ((B : ℝ) + m + 1) := by positivity
    nlinarith
  have g1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => f1 j
  have g2 : 0 ≤ ∏ j : Fin m, ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => f2 j
  have k1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => by positivity
  have k2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => by have := fin_sub_pos m j; apply div_nonneg <;> linarith
  have k3 : 0 ≤ (1 + t) ^ m := by positivity
  refine ⟨by positivity, ?_⟩
  calc _ ≤ (weylDim m μ : ℝ) *
        ((1 + t) ^ m * ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
        ((1 + t) ^ m * ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
        ((1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1))) := by gcongr
    _ = _ := by ring

theorem hwt_bound (m A c B : ℕ) (t : ℝ) (ht : 0 ≤ t) (hA : (c : ℝ) ≤ t * A) (hB : (c : ℝ) ≤ t * B) :
    (weylDim (m + 2) (hwt m (A + c) (B + c)) : ℝ) ≤ (1 + t) ^ (2 * m + 1) * (weylDim (m + 2) (hwt m A B) : ℝ) := by
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [weylDim_hwt, weylDim_hwt]
  push_cast
  have f1 : ∀ j : Fin m, 0 ≤ ((A : ℝ) + c + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := fun j => by positivity
  have f2 : ∀ j : Fin m, 0 ≤ ((B : ℝ) + c + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) := by
    intro j; have := fin_sub_pos m j; apply div_nonneg <;> linarith
  have P1 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) t f1
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ t * (((j : ℕ) : ℝ) + 1) := by positivity
      nlinarith)
  have P2 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) t f2
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (fin_sub_pos m j).le
      have := fin_sub_pos m j
      have : 0 ≤ t * ((m : ℝ) - ((j : ℕ) : ℝ)) := by positivity
      nlinarith)
  have P3 : ((A : ℝ) + c + (B + c) + m + 1) / ((m : ℝ) + 1) ≤ (1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ t * ((m : ℝ) + 1) := by positivity
    nlinarith
  have g1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + c + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => f1 j
  have g2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + c + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => f2 j
  have f3 : 0 ≤ ((A : ℝ) + c + (B + c) + m + 1) / ((m : ℝ) + 1) := by positivity
  have k1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => by positivity
  have k2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => by have := fin_sub_pos m j; apply div_nonneg <;> linarith
  have k3 : 0 ≤ (1 + t) ^ m := by positivity
  calc _ ≤ ((1 + t) ^ m * ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
        ((1 + t) ^ m * ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
        ((1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1))) := by gcongr
    _ = _ := by ring

end Formalism.CountingSumsFrames
end

section

set_option linter.unusedSimpArgs false

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.CountingSumsFrames

section Gen

variable (K : Type) [Field K] (k : ℕ)

def eulX_har (f : PolXY K k) : PolXY K k := ∑ i : Fin k, X (Sum.inl i) * pderiv (Sum.inl i) f

def eulY (f : PolXY K k) : PolXY K k := ∑ i : Fin k, X (Sum.inr i) * pderiv (Sum.inr i) f

variable {K k}

theorem ctrF_apply (f : PolXY K k) :
    ctrF K k f = ∑ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := by
  simp [ctrF, LinearMap.sum_apply]

theorem pderiv_inl_h (i : Fin k) : pderiv (Sum.inl i) (hXY K k) = X (Sum.inr i) := by
  classical
  simp [hXY, pderiv_X, Pi.single_apply, Finset.sum_ite_eq']

theorem pderiv_inr_h (i : Fin k) : pderiv (Sum.inr i) (hXY K k) = X (Sum.inl i) := by
  classical
  simp [hXY, pderiv_X, Pi.single_apply, Finset.sum_ite_eq']

theorem ctrF_h_mul (f : PolXY K k) :
    ctrF K k (hXY K k * f) = hXY K k * ctrF K k f + (k : K) • f + eulX_har K k f + eulY K k f := by
  classical
  have key : ∀ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) (hXY K k * f)) =
      hXY K k * pderiv (Sum.inl i) (pderiv (Sum.inr i) f) + f +
        X (Sum.inl i) * pderiv (Sum.inl i) f + X (Sum.inr i) * pderiv (Sum.inr i) f := by
    intro i
    rw [pderiv_mul, pderiv_inr_h, map_add (f := _), pderiv_mul, pderiv_mul, pderiv_inl_h, pderiv_X_self]
    ring
  rw [ctrF_apply, ctrF_apply, eulX_har, eulY, Finset.sum_congr rfl (fun i _ => key i)]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul K]

theorem coeff_X_mul_pderiv (v : XY k) (f : PolXY K k) (m : XY k →₀ ℕ) :
    AddMonoidAlgebra.coeff (X v * pderiv v f) m = (m v : K) * AddMonoidAlgebra.coeff f m := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq]
  | monomial n a =>
    rw [X_mul_pderiv_monomial, MvPolynomial.coeff_smul, coeff_monomial]
    by_cases h : n = m
    · subst h; simp
    · simp [h]

theorem coeff_eulX (f : PolXY K k) (m : XY k →₀ ℕ) :
    AddMonoidAlgebra.coeff (eulX_har K k f) m = (xDeg m : K) * AddMonoidAlgebra.coeff f m := by
  simp [eulX_har, coeff_sum, coeff_X_mul_pderiv, xDeg, Finset.sum_mul]

theorem coeff_eulY (f : PolXY K k) (m : XY k →₀ ℕ) :
    AddMonoidAlgebra.coeff (eulY K k f) m = (yDeg m : K) * AddMonoidAlgebra.coeff f m := by
  simp [eulY, coeff_sum, coeff_X_mul_pderiv, yDeg, Finset.sum_mul]

theorem eulX_of_mem {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    eulX_har K k f = (A : K) • f := by
  ext m
  rw [coeff_eulX, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ f.support
  · rw [(hf m hm).1]
  · rw [notMem_support_iff.1 hm]; simp

theorem eulY_of_mem {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    eulY K k f = (B : K) • f := by
  ext m
  rw [coeff_eulY, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ f.support
  · rw [(hf m hm).2]
  · rw [notMem_support_iff.1 hm]; simp

end Gen

theorem slTwoCommutator_holds : SlTwo := by
  intro K _ _ k A B f hf
  rw [ctrF_h_mul, eulX_of_mem hf, eulY_of_mem hf]
  simp only [Algebra.smul_def, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_zero, map_add (f := _), map_mul,
      map_one, map_zero, map_natCast]
  ring

section Gen2

variable {K : Type} [Field K] {k : ℕ}

end Gen2

section Fis

variable {K : Type} [Field K] {k : ℕ}

end Fis

section Can

variable {K : Type} [Field K] {k : ℕ}

end Can

end Formalism.CountingSumsFrames
end
end

section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

lemma dimPol_mono (k' : ℕ) {a b : ℕ} (h : a ≤ b) : dimPol k' a ≤ dimPol k' b :=
  Nat.choose_le_choose k' (by omega)

theorem harmonic_level_count_rec (k' : ℕ) : ∀ A B : ℕ,
    ∑ j ∈ range (min A B + 1), dimHar k' (A - j) (B - j) = dimPol k' A * dimPol k' B
  | 0, B => by simp [dimHar]
  | A + 1, 0 => by simp [dimHar]
  | A + 1, B + 1 => by
    rw [show min (A + 1) (B + 1) + 1 = (min A B + 1) + 1 by omega, Finset.sum_range_succ']
    have e : ∀ j ∈ range (min A B + 1),
        dimHar k' (A + 1 - (j + 1)) (B + 1 - (j + 1)) = dimHar k' (A - j) (B - j) := by
      intro j _
      rw [show A + 1 - (j + 1) = A - j by omega, show B + 1 - (j + 1) = B - j by omega]
    rw [Finset.sum_congr rfl e, harmonic_level_count_rec k' A B]
    have hle : dimPol k' A * dimPol k' B ≤ dimPol k' (A + 1) * dimPol k' (B + 1) :=
      Nat.mul_le_mul (dimPol_mono k' (by omega)) (dimPol_mono k' (by omega))
    simp only [dimHar, Nat.sub_zero, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, or_self, if_false]
    exact Nat.add_sub_cancel' hle

theorem harmonic_level_count : LevelCount :=
  fun k' A B => harmonic_level_count_rec k' A B

end Formalism.CountingSumsFrames
end
end

section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

theorem det_leading_diagonal : DetLeadDiag := by
  intro K _ n J A d hdeg hcoeff
  have hprod : ∀ σ : Equiv.Perm (Fin n), (∏ i, A (σ i) i).coeff (n * J) = ∏ i, (A (σ i) i).coeff J := by
    intro σ
    have h1 := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ) (fun i => A (σ i) i) J
      (fun i _ => hdeg (σ i) i)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  rw [Matrix.det_apply']
  constructor
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro σ _
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_intCast, zero_add]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ i, (A (σ i) i).natDegree ≤ ∑ _i : Fin n, J := Finset.sum_le_sum fun i _ => hdeg (σ i) i
      _ = n * J := by simp
  · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 1]
    · rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hprod]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply]
      exact Finset.prod_congr rfl fun i _ => by rw [hcoeff]; simp
    · intro σ _ hσ
      rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hprod]
      obtain ⟨i, hi⟩ := not_forall.mp (mt Equiv.ext hσ)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hcoeff, if_neg (by simpa using hi)]), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

end Formalism.CountingSumsFrames
end
end

section

noncomputable section

open scoped BigOperators TensorProduct
open Finset

namespace Formalism.CountingSumsFrames

theorem one_sub_sum_mul_prod_le_prod {ι : Type} (s : Finset ι) (κ n d : ι → ℝ) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1)
    (hd : ∀ j, 0 ≤ d j) (h : ∀ j, (1 - κ j) * d j ≤ n j) :
    (1 - ∑ j ∈ s, κ j) * ∏ j ∈ s, d j ≤ ∏ j ∈ s, n j := by
  classical
  have hP : ∀ t : Finset ι, 1 - ∑ j ∈ t, κ j ≤ ∏ j ∈ t, (1 - κ j) := by
    intro t
    refine Finset.induction_on t (by simp) ?_
    intro i t hi ih
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ 1 - κ i := by linarith [(hκ i).2]
    have h2 : 0 ≤ ∑ j ∈ t, κ j := Finset.sum_nonneg fun j _ => (hκ j).1
    have h3 := mul_le_mul_of_nonneg_left ih h1
    nlinarith [mul_nonneg (hκ i).1 h2]
  have hd0 : 0 ≤ ∏ j ∈ s, d j := Finset.prod_nonneg fun j _ => hd j
  calc (1 - ∑ j ∈ s, κ j) * ∏ j ∈ s, d j ≤ (∏ j ∈ s, (1 - κ j)) * ∏ j ∈ s, d j :=
        mul_le_mul_of_nonneg_right (hP s) hd0
    _ = ∏ j ∈ s, ((1 - κ j) * d j) := Finset.prod_mul_distrib.symm
    _ ≤ ∏ j ∈ s, n j := Finset.prod_le_prod₀
        (fun j _ => mul_nonneg (by linarith [(hκ j).2]) (hd j)) (fun j _ => h j)

theorem share_product_bound : ShareProd := by
  intro J κ n d hκ h
  push_cast
  exact one_sub_sum_mul_prod_le_prod Finset.univ κ (fun j => (n j : ℝ)) (fun j => (d j : ℝ)) hκ (fun j => Nat.cast_nonneg _) h

section Partner

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end Partner

end Formalism.CountingSumsFrames
end
end
