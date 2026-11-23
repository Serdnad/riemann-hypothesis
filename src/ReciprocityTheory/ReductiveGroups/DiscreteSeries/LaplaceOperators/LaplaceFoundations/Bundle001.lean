module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

open scoped Nat

section Abstract

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

theorem norm_exp_sub_one_sub_le (x : 𝔸) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  have h2 := (hasSum_nat_add_iff' 2).mpr h
  have e : ∑ i ∈ Finset.range 2, ((i !⁻¹ : ℂ) • x ^ i) = 1 + x := by
    simp [Finset.sum_range_succ]
  rw [e, ← sub_sub] at h2
  have hr := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  rw [← Real.exp_eq_exp_ℝ] at hr
  have hg := hr.mul_left (‖x‖ ^ 2)
  refine h2.norm_le_of_bounded hg ?_
  intro m
  rw [norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
  have hf : ((m + 2)! : ℝ)⁻¹ ≤ ((m ! : ℕ) : ℝ)⁻¹ := by
    apply inv_anti₀ (by exact_mod_cast Nat.factorial_pos m)
    exact_mod_cast Nat.factorial_le (by omega)
  have hp : ‖x ^ (m + 2)‖ ≤ ‖x‖ ^ (m + 2) := norm_pow_le' x (by omega)
  calc ((((m + 2)! : ℕ) : ℝ))⁻¹ * ‖x ^ (m + 2)‖ ≤ ((m ! : ℕ) : ℝ)⁻¹ * ‖x‖ ^ (m + 2) :=
        mul_le_mul hf hp (norm_nonneg _) (by positivity)
    _ = ‖x‖ ^ 2 * (((m ! : ℕ) : ℝ)⁻¹ * ‖x‖ ^ m) := by ring

theorem conj_identity (a b u M : 𝔸) :
    a * M * b - M - (u * M - M * u) =
      M * (b - 1 + u) - u * M * u + u * M * (b - 1 + u) + (a - 1 - u) * M -
        (a - 1 - u) * M * u + (a - 1 - u) * M * (b - 1 + u) := by
  noncomm_ring

theorem norm_six (a b c d e f : 𝔸) :
    ‖a - b + c + d - e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_add_le (a - b + c + d - e) f
  have h2 := norm_sub_le (a - b + c + d) e
  have h3 := norm_add_le (a - b + c) d
  have h4 := norm_add_le (a - b) c
  have h5 := norm_sub_le a b
  linarith

theorem norm_matrix_triple_product_le (x y z : 𝔸) : ‖x * y * z‖ ≤ ‖x‖ * ‖y‖ * ‖z‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

theorem le3 {a b c A B C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h1 : a ≤ A) (h2 : b ≤ B)
    (h3 : c ≤ C) : a * b * c ≤ A * B * C :=
  mul_le_mul (mul_le_mul h1 h2 hb (ha.trans h1)) h3 hc (mul_nonneg (ha.trans h1) (hb.trans h2))

theorem conj_taylor (Y M : 𝔸) (τ r m : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hY : ‖Y‖ ≤ r)
    (hM : ‖M‖ ≤ m) :
    ‖NormedSpace.exp ((τ : ℂ) • Y) * M * NormedSpace.exp (-((τ : ℂ) • Y)) - M -
        (τ : ℂ) • (Y * M - M * Y)‖ ≤
      m * (2 * r ^ 2 * Real.exp r + r ^ 2 + 2 * r ^ 3 * Real.exp r + r ^ 4 * Real.exp r ^ 2) *
        τ ^ 2 := by
  set u : 𝔸 := (τ : ℂ) • Y with hu
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hY
  have hm0 : 0 ≤ m := (norm_nonneg _).trans hM
  have hsm : (τ : ℂ) • (Y * M - M * Y) = u * M - M * u := by
    rw [hu, smul_sub, smul_mul_assoc, mul_smul_comm]
  rw [hsm, conj_identity]
  set p : ℝ := τ * r with hp
  set E : ℝ := Real.exp r with hE
  set q : ℝ := p ^ 2 * E with hq
  have hp0 : 0 ≤ p := mul_nonneg hτ0 hr0
  have hE0 : 0 ≤ E := (Real.exp_pos r).le
  have hq0 : 0 ≤ q := mul_nonneg (pow_nonneg hp0 2) hE0
  have hu' : ‖u‖ ≤ p := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
    exact mul_le_mul_of_nonneg_left hY hτ0
  have hexp : Real.exp ‖u‖ ≤ E := by
    apply Real.exp_le_exp.mpr
    calc ‖u‖ ≤ p := hu'
      _ ≤ r := by rw [hp]; nlinarith
  have hA : ‖NormedSpace.exp u - 1 - u‖ ≤ q := by
    refine (norm_exp_sub_one_sub_le u).trans ?_
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu' 2) hexp (Real.exp_pos _).le
      (pow_nonneg hp0 2)
  have hB : ‖NormedSpace.exp (-u) - 1 + u‖ ≤ q := by
    have := norm_exp_sub_one_sub_le (-u)
    rw [sub_neg_eq_add, norm_neg] at this
    refine this.trans ?_
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu' 2) hexp (Real.exp_pos _).le
      (pow_nonneg hp0 2)
  set A := NormedSpace.exp u - 1 - u
  set B := NormedSpace.exp (-u) - 1 + u
  have t1 : ‖M * B‖ ≤ m * q :=
    (norm_mul_le _ _).trans (mul_le_mul hM hB (norm_nonneg _) hm0)
  have t2 : ‖u * M * u‖ ≤ p * m * p :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hu' hM hu')
  have t3 : ‖u * M * B‖ ≤ p * m * q :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hu' hM hB)
  have t4 : ‖A * M‖ ≤ q * m :=
    (norm_mul_le _ _).trans (mul_le_mul hA hM (norm_nonneg _) hq0)
  have t5 : ‖A * M * u‖ ≤ q * m * p :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hA hM hu')
  have t6 : ‖A * M * B‖ ≤ q * m * q :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hA hM hB)
  refine (norm_six _ _ _ _ _ _).trans ?_
  have hτ3 : τ ^ 3 ≤ τ ^ 2 := pow_le_pow_of_le_one hτ0 hτ1 (by norm_num)
  have hτ4 : τ ^ 4 ≤ τ ^ 2 := pow_le_pow_of_le_one hτ0 hτ1 (by norm_num)
  have key : m * q + p * m * p + p * m * q + q * m + q * m * p + q * m * q =
      m * (2 * r ^ 2 * E * τ ^ 2 + r ^ 2 * τ ^ 2 + 2 * r ^ 3 * E * τ ^ 3 + r ^ 4 * E ^ 2 * τ ^ 4) := by
    rw [hq, hp]; ring
  have c3 : 2 * r ^ 3 * E * τ ^ 3 ≤ 2 * r ^ 3 * E * τ ^ 2 :=
    mul_le_mul_of_nonneg_left hτ3 (by positivity)
  have c4 : r ^ 4 * E ^ 2 * τ ^ 4 ≤ r ^ 4 * E ^ 2 * τ ^ 2 :=
    mul_le_mul_of_nonneg_left hτ4 (by positivity)
  have fin : m * q + p * m * p + p * m * q + q * m + q * m * p + q * m * q ≤
      m * (2 * r ^ 2 * E + r ^ 2 + 2 * r ^ 3 * E + r ^ 4 * E ^ 2) * τ ^ 2 := by
    rw [key]
    have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (le_refl
      (2 * r ^ 2 * E * τ ^ 2 + r ^ 2 * τ ^ 2)) c3) c4) hm0
    linarith
  linarith

end Abstract

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

section Op

open scoped NNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

theorem entry_le_op (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine le_trans ?_ (Finset.le_sup (f := fun i : Fin n => ∑ j : Fin n, ‖A i j‖₊)
      (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖A i j‖₊) (fun _ _ => bot_le) (Finset.mem_univ j)
  exact_mod_cast h

theorem op_le_of_entry (A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, ‖A i j‖ ≤ c) : ‖A‖ ≤ n * c := by
  have h' : ‖A‖₊ ≤ (n : ℝ≥0) * c.toNNReal := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    calc ∑ j, ‖A i j‖₊ ≤ ∑ _j : Fin n, c.toNNReal :=
          Finset.sum_le_sum fun j _ => (by
            have := Real.toNNReal_le_toNNReal (h i j)
            rwa [norm_toNNReal] at this)
      _ = (n : ℝ≥0) * c.toNNReal := by simp
  have := NNReal.coe_le_coe.mpr h'
  push_cast [Real.coe_toNNReal _ hc] at this
  exact this

theorem conj_taylor_entry (R : ℝ) (hR : 0 ≤ R) (Y M : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ i j, ‖Y i j‖ ≤ R) (hM : ∀ i j, ‖M i j‖ ≤ R) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (i j : Fin n) :
    ‖(NormedSpace.exp ((τ : ℂ) • Y) * M * NormedSpace.exp (-((τ : ℂ) • Y)) - M -
        (τ : ℂ) • (Y * M - M * Y)) i j‖ ≤
      (n * R) * (2 * (n * R) ^ 2 * Real.exp (n * R) + (n * R) ^ 2 +
        2 * (n * R) ^ 3 * Real.exp (n * R) + (n * R) ^ 4 * Real.exp (n * R) ^ 2) * τ ^ 2 :=
  (entry_le_op _ i j).trans
    (conj_taylor Y M τ (n * R) (n * R) hτ0 hτ1 (op_le_of_entry Y R hR hY)
      (op_le_of_entry M R hR hM))

end Op

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ConjugationTaylorBound in
theorem b3c : ConjugationSecondOrderBound := by
  intro n R
  have hR : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  refine ⟨(n * max R 0) * (2 * (n * max R 0) ^ 2 * Real.exp (n * max R 0) + (n * max R 0) ^ 2 +
        2 * (n * max R 0) ^ 3 * Real.exp (n * max R 0) +
        (n * max R 0) ^ 4 * Real.exp (n * max R 0) ^ 2), by positivity, ?_⟩
  intro Y M hY hM τ h0 h1
  have hY' : ∀ i j, ‖Y i j‖ ≤ max R 0 := fun i j =>
    (Matrix.norm_entry_le_entrywise_sup_norm Y).trans (hY.trans (le_max_left _ _))
  have hM' : ∀ i j, ‖M i j‖ ≤ max R 0 := fun i j =>
    (Matrix.norm_entry_le_entrywise_sup_norm M).trans (hM.trans (le_max_left _ _))
  exact (Matrix.norm_le_iff (by positivity)).2
    (fun i j => conj_taylor_entry (max R 0) hR Y M hY' hM' τ h0 h1 i j)

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section

noncomputable section

open Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

theorem double_sum_diag_split {n : ℕ} (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ a, ∑ b, (if a < b then f a b + f b a else 0) := by
  have h1 : ∀ a b, f a b = (if a < b then f a b else 0) + (if a = b then f a b else 0)
      + (if b < a then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have h2 : ∑ a, ∑ b, (if b < a then f a b else 0) = ∑ a, ∑ b, (if a < b then f b a else 0) :=
    Finset.sum_comm
  calc ∑ a, ∑ b, f a b
      = ∑ a, ∑ b, ((if a < b then f a b else 0) + (if a = b then f a b else 0)
          + (if b < a then f a b else 0)) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))
    _ = ∑ a, ∑ b, (if a < b then f a b else 0) + ∑ a, f a a
          + ∑ a, ∑ b, (if b < a then f a b else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        rw [h2, add_comm (∑ a, ∑ b, (if a < b then f a b else 0)) (∑ a, f a a), add_assoc,
          ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        split_ifs <;> simp

theorem b2Id : RaisingLoweringNormIdentities := by
  intro n ε M _ _ E lam w hD
  obtain ⟨hGl, hU, hw1, ⟨hdiag, hup⟩, hcas⟩ := hD
  set Λ := lowK ε lam with hΛ
  let sR : Fin n → Fin n → ℝ := fun a b => if ε a = ε b then 1 else -1
  have hsC : ∀ a b, adjSign ε a b = ((sR a b : ℝ) : ℂ) := by
    intro a b; simp only [adjSign, sR]; split_ifs <;> simp
  have hsymm : ∀ a b, sR a b = sR b a := by
    intro a b; simp only [sR]
    by_cases h : ε a = ε b
    · simp [h]
    · simp [h, Ne.symm h]
  have hsq : ∀ a b, sR a b * sR a b = 1 := by
    intro a b; simp only [sR]; split_ifs <;> norm_num
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw1]; simp
  have hQ : ∀ a b, ⟪w, E a b (E b a w)⟫_ℂ = ((sR a b * ‖E b a w‖ ^ 2 : ℝ) : ℂ) := by
    intro a b
    have h := hU b a w (E b a w)
    rw [inner_self_eq_norm_sq_to_K, hsC] at h
    have h1 : ((sR b a : ℝ) : ℂ) * ((sR b a : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hsq]; simp
    calc ⟪w, E a b (E b a w)⟫_ℂ
        = ((sR b a : ℝ) : ℂ) * (((sR b a : ℝ) : ℂ) * ⟪w, E a b (E b a w)⟫_ℂ) := by
          rw [← mul_assoc, h1, one_mul]
      _ = _ := by
          rw [← h, hsymm b a]; try simp only [RCLike.ofReal_eq_complex_ofReal]
          push_cast; ring
  have hC : ∀ a b, ⟪w, E a b (E b a w)⟫_ℂ - ⟪w, E b a (E a b w)⟫_ℂ = (((Λ a - Λ b : ℝ)) : ℂ) := by
    intro a b
    have h := hGl a b b a
    rw [if_pos rfl, if_pos rfl] at h
    have h2 := congrArg (fun T : Module.End ℂ M => T w) h
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
    rw [← inner_sub_right, h2, hdiag a, hdiag b, ← sub_smul, inner_smul_right, hww, mul_one]
    push_cast; ring
  have hR1 : ∀ a b, sR a b * ‖E b a w‖ ^ 2 - sR b a * ‖E a b w‖ ^ 2 = Λ a - Λ b := by
    intro a b
    have h := hC a b
    rw [hQ a b, hQ b a, ← Complex.ofReal_sub] at h
    exact_mod_cast h
  have hR2 : ∀ a, ‖E a a w‖ ^ 2 = Λ a ^ 2 := by
    intro a
    rw [hdiag a, norm_smul, hw1, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hR3 : ∀ a b, a < b → ε a = ε b → ‖E a b w‖ ^ 2 = 0 := by
    intro a b hab he; rw [hup a b hab he]; simp
  have hcasR : casVal lam = ∑ a, ∑ b, sR a b * ‖E b a w‖ ^ 2 := by
    have h1 : ⟪w, casimir E w⟫_ℂ = ∑ a, ∑ b, ⟪w, E a b (E b a w)⟫_ℂ := by
      simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, inner_sum]
    rw [hcas, inner_smul_right, hww, mul_one] at h1
    simp only [hQ] at h1
    exact_mod_cast h1
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab he
    have h := hR1 a b
    have hs1 : sR a b = 1 := if_pos he
    have hs2 : sR b a = 1 := if_pos he.symm
    rw [hs1, hs2, hR3 a b hab he] at h
    linarith
  · intro a b hab he
    have h := hR1 a b
    have hs1 : sR a b = -1 := if_neg he
    have hs2 : sR b a = -1 := if_neg (Ne.symm he)
    rw [hs1, hs2] at h
    linarith
  · have hpt : ∀ a b, (if a < b then sR a b * ‖E b a w‖ ^ 2 + sR b a * ‖E a b w‖ ^ 2 else 0) =
        (if a < b ∧ ε b = ε a then Λ a else 0) - (if a < b ∧ ε a = ε b then Λ b else 0)
        - ((if a < b ∧ ε b ≠ ε a then Λ a else 0) - (if a < b ∧ ε a ≠ ε b then Λ b else 0))
        - 2 * (if a < b ∧ ε a ≠ ε b then ‖E b a w‖ ^ 2 else 0) := by
      intro a b
      by_cases hab : a < b
      · have h := hR1 a b
        by_cases he : ε a = ε b
        · have hs1 : sR a b = 1 := if_pos he
          have hs2 : sR b a = 1 := if_pos he.symm
          have h0 := hR3 a b hab he
          rw [hs1, hs2, h0] at h
          simp [hab, he, hs1, hs2, h0]
          linarith
        · have hs1 : sR a b = -1 := if_neg he
          have hs2 : sR b a = -1 := if_neg (Ne.symm he)
          rw [hs1, hs2] at h
          simp [hab, he, Ne.symm he, hs1, hs2]
          linarith
      · simp [hab]
    have hsw1 : ∑ a, ∑ b, (if b < a ∧ ε b = ε a then Λ a else 0) =
        ∑ a, ∑ b, (if a < b ∧ ε a = ε b then Λ b else 0) := Finset.sum_comm
    have hsw2 : ∑ a, ∑ b, (if b < a ∧ ε b ≠ ε a then Λ a else 0) =
        ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then Λ b else 0) := Finset.sum_comm
    have hA : 2 * ∑ a, Λ a * rhoC ε a = ∑ a, ∑ b, (if a < b ∧ ε b = ε a then Λ a else 0)
        - ∑ a, ∑ b, (if a < b ∧ ε a = ε b then Λ b else 0) := by
      rw [← hsw1, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have e1 : ∑ b, (if a < b ∧ ε b = ε a then Λ a else 0) =
          Λ a * ∑ b, (if a < b ∧ ε b = ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      have e2 : ∑ b, (if b < a ∧ ε b = ε a then Λ a else 0) =
          Λ a * ∑ b, (if b < a ∧ ε b = ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      rw [e1, e2]
      simp only [rhoC, Finset.natCast_card_filter]
      ring
    have hB : 2 * ∑ a, Λ a * rhoN ε a = ∑ a, ∑ b, (if a < b ∧ ε b ≠ ε a then Λ a else 0)
        - ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then Λ b else 0) := by
      rw [← hsw2, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have e1 : ∑ b, (if a < b ∧ ε b ≠ ε a then Λ a else 0) =
          Λ a * ∑ b, (if a < b ∧ ε b ≠ ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      have e2 : ∑ b, (if b < a ∧ ε b ≠ ε a then Λ a else 0) =
          Λ a * ∑ b, (if b < a ∧ ε b ≠ ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      rw [e1, e2]
      simp only [rhoN, Finset.natCast_card_filter]
      ring
    have hdiagsum : ∑ a, sR a a * ‖E a a w‖ ^ 2 = ∑ a, Λ a ^ 2 :=
      Finset.sum_congr rfl (fun a _ => by rw [hR2 a, show sR a a = 1 from if_pos rfl, one_mul])
    have hspl := double_sum_diag_split (fun a b => sR a b * ‖E b a w‖ ^ 2)
    have hcasv : casVal lam = ∑ a, Λ a ^ 2 + (∑ a, ∑ b, (if a < b ∧ ε b = ε a then Λ a else 0)
        - ∑ a, ∑ b, (if a < b ∧ ε a = ε b then Λ b else 0)
        - (∑ a, ∑ b, (if a < b ∧ ε b ≠ ε a then Λ a else 0)
          - ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then Λ b else 0))
        - 2 * ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then ‖E b a w‖ ^ 2 else 0)) := by
      rw [hcasR, hspl, hdiagsum]
      congr 1
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hpt a b))]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hz : ∑ a, (Λ a ^ 2 + 2 * (Λ a * rhoC ε a) - 2 * (Λ a * rhoN ε a) - lam a * lam a
        + (rhoN ε - rhoC ε) a * (rhoN ε - rhoC ε) a) = 0 :=
      Finset.sum_eq_zero (fun a _ => by simp only [hΛ, lowK, Pi.add_apply, Pi.sub_apply]; ring)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hz
    simp only [Finset.sum_filter]
    simp only [casVal, nsq, dot] at hcasv ⊢
    linarith [hcasv, hz, hA, hB]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

theorem b3b : DerivMatrixCoeffExp := by
  intro n ε H _ _ σ w hσ hw Z hZ s
  have h0 := (isDerivedOn_smE hσ).deriv Z hZ ⟨w, hw⟩
  have hphi : phiW ε σ w Z = ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H) := by
    simp only [phiW, dif_pos hw]
  set g := σ (NormedSpace.exp ((s : ℂ) • Z)) with hg
  set T : H →L[ℂ] ℂ := (innerSL ℂ w).comp g with hT
  have h1 := ((T.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) h0
  have h2 : HasDerivAt (fun x : ℝ => T (σ (NormedSpace.exp (((x - s : ℝ) : ℂ) • Z)) w))
      (T ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H)) s := by
    have h1' : HasDerivAt (⇑(ContinuousLinearMap.restrictScalars ℝ T) ∘
        fun t : ℝ => (σ (NormedSpace.exp ((t : ℂ) • Z))) w)
        ((ContinuousLinearMap.restrictScalars ℝ T) ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H)) (s - s) := by
      rw [sub_self]; exact h1
    exact h1'.comp_sub_const s s
  rw [hphi]
  convert (preTransparency := .reducible) h2 using 1
  · funext x
    have he : NormedSpace.exp ((x : ℂ) • Z) =
        NormedSpace.exp ((s : ℂ) • Z) * NormedSpace.exp (((x - s : ℝ) : ℂ) • Z) := by
      rw [← exp_add_smul]
      congr 2
      push_cast
      ring
    rw [he, hσ.1.2 _ (exp_smul_mem_UJset hZ s) _ (exp_smul_mem_UJset hZ (x - s))]
    simp [hT, hg]
  · simp [hT, hg]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

theorem smInfUnitary : SmInfUnitaryStatement :=
  fun _ _ _ _ _ _ hσ => isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end
