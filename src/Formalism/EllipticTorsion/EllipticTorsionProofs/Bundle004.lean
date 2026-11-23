module

public import Formalism.EllipticTorsion.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

universe u

namespace Formalism.ELL.FormalGroupPointsSubgroup

open WeierstrassCurve Polynomial

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma add_le {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a + b‖ ≤ c := by
  exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

lemma sub_le {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  exact add_le ha (by rwa [norm_neg])

lemma le_sub_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a‖ ≤ ‖a - b‖ := by
  have h1 : ‖a‖ ≤ max ‖a - b‖ ‖b‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (a - b) b
  rcases le_max_iff.mp h1 with h2 | h2
  · exact h2
  · exact absurd h2 (not_le.mpr h)

lemma mul_le {a b : K} {c d : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ d) : ‖a * b‖ ≤ c * d := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)

lemma y_int (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) : ‖y‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have h' : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp h
  by_contra hy
  push_neg at hy
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 := by
    have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have hx3 : ‖x ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    refine add_le (add_le (add_le hx3 ?_) ?_) h6
    · simpa using mul_le h2 hx2
    · simpa using mul_le h4 hx
  have hT : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖y‖ := by
    refine add_le ?_ ?_
    · simpa using mul_le (mul_le h1 hx) (le_refl ‖y‖)
    · simpa using mul_le h3 (le_refl ‖y‖)
  have hlt : ‖-(W.a₁ * x * y + W.a₃ * y)‖ < ‖y ^ 2‖ := by
    rw [norm_neg, norm_pow]; nlinarith
  have key := le_sub_of_lt hlt
  rw [sub_neg_eq_add, ← add_assoc, h', norm_pow] at key
  nlinarith

lemma y_sq_le (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) : ‖y‖ ^ 2 ≤ ‖x‖ ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have h' : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp h
  by_contra hy
  push_neg at hy
  have hx0 : (0 : ℝ) < ‖x‖ := by linarith
  have hx2 : ‖x‖ ^ 2 < ‖x‖ ^ 3 := by
    nlinarith [mul_pos (mul_pos hx0 hx0) (by linarith : (0 : ℝ) < ‖x‖ - 1)]
  have hx1 : ‖x‖ ≤ ‖x‖ ^ 3 := by
    nlinarith [mul_pos hx0 (by linarith : (0 : ℝ) < ‖x‖ - 1)]
  have hxy : ‖x‖ < ‖y‖ := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul hc hc (norm_nonneg y) hx0.le
    nlinarith
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ ‖x‖ ^ 3 := by
    refine add_le (add_le (add_le (le_of_eq (norm_pow _ _)) ?_) ?_) ?_
    · exact (mul_le h2 (le_of_eq (norm_pow x 2))).trans (by linarith)
    · exact (mul_le h4 (le_refl ‖x‖)).trans (by linarith)
    · exact h6.trans (one_le_pow₀ hx.le)
  have hT : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖x‖ * ‖y‖ := by
    refine add_le ?_ ?_
    · simpa using mul_le (mul_le h1 (le_refl ‖x‖)) (le_refl ‖y‖)
    · exact (mul_le h3 (le_refl ‖y‖)).trans (by nlinarith [norm_nonneg y])
  have hlt : ‖-(W.a₁ * x * y + W.a₃ * y)‖ < ‖y ^ 2‖ := by
    rw [norm_neg, norm_pow]; nlinarith [norm_nonneg y]
  have key := le_sub_of_lt hlt
  rw [sub_neg_eq_add, ← add_assoc, h', norm_pow] at key
  linarith

lemma addX_norm [DecidableEq K] (W : WeierstrassCurve K) (hW : IntegralModel W)
    {x₁ x₂ y₁ y₂ : K} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) (hx₁ : 1 < ‖x₁‖) (hx₂ : 1 < ‖x₂‖) :
    1 < ‖W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)‖ := by
  set ℓ := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  set x₃ := W.toAffine.addX x₁ x₂ ℓ with hx₃
  set y₃ := W.toAffine.negAddY x₁ x₂ y₁ ℓ with hy₃
  by_contra hC
  push Not at hC
  have h₃ : W.toAffine.Equation x₃ y₃ := Affine.equation_negAdd h₁ h₂ hxy
  have hy3 : ‖y₃‖ ≤ 1 := y_int W hW h₃ hC
  have hpoly := Affine.addPolynomial_slope h₁ h₂ hxy
  rw [← hℓ] at hpoly
  have hev := congrArg (Polynomial.eval (x₃ + 1)) hpoly
  simp only [Affine.addPolynomial, Affine.linePolynomial, Affine.polynomial] at hev
  simp at hev
  have hx3def : x₃ = ℓ ^ 2 + W.toAffine.a₁ * ℓ - W.toAffine.a₂ - x₁ - x₂ := by simp [hx₃]
  rw [← hx3def] at hev
  obtain ⟨a1, a2, a3, a4, a6⟩ := hW

  have hy3def : y₃ = ℓ * (x₃ - x₁) + y₁ := by simp [hy₃, hx₃]
  have hx0 : 0 ≤ ‖x₁‖ := norm_nonneg _
  have hℓ0 : 0 ≤ ‖ℓ‖ := norm_nonneg _
  have hsq := y_sq_le W ⟨a1, a2, a3, a4, a6⟩ h₁ hx₁
  have hd : ‖x₁‖ ≤ ‖x₁ - x₃‖ := le_sub_of_lt (by linarith)
  have hlin : ‖ℓ‖ * ‖x₁‖ ≤ max ‖y₁‖ 1 := by
    have e : ℓ * (x₁ - x₃) = y₁ - y₃ := by rw [hy3def]; ring
    have : ‖ℓ * (x₁ - x₃)‖ ≤ max ‖y₁‖ 1 := by
      rw [e]; exact sub_le (le_max_left _ _) (hy3.trans (le_max_right _ _))
    rw [norm_mul] at this
    nlinarith
  have hℓsq : ‖ℓ‖ ^ 2 ≤ ‖x₁‖ := by
    have hm : (max ‖y₁‖ 1) ^ 2 ≤ ‖x₁‖ ^ 3 := by
      rcases le_total ‖y₁‖ 1 with h | h
      · rw [max_eq_right h, one_pow]; exact one_le_pow₀ hx₁.le
      · rw [max_eq_left h]; exact hsq
    have : (‖ℓ‖ * ‖x₁‖) ^ 2 ≤ ‖x₁‖ ^ 3 :=
      (pow_le_pow_left₀ (by positivity) hlin 2).trans hm
    have hx1p : 0 < ‖x₁‖ ^ 2 := by positivity
    nlinarith

  set M := max 1 ‖ℓ‖ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMℓ : ‖ℓ‖ ≤ M := le_max_right _ _
  have hMsq : M ^ 2 ≤ ‖x₁‖ := by
    rcases le_total 1 ‖ℓ‖ with h | h
    · rw [hM, max_eq_right h]; exact hℓsq
    · rw [hM, max_eq_left h]; nlinarith
  have ht : ‖x₃ + 1‖ ≤ 1 := add_le hC (by simp)
  have hu : ‖ℓ * (x₃ + 1 - x₁) + y₁‖ ≤ M := by
    have e : ℓ * (x₃ + 1 - x₁) + y₁ = y₃ + ℓ := by rw [hy3def]; ring
    rw [e]; exact add_le (hy3.trans hM1) hMℓ
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hLHS : ‖(ℓ * (x₃ + 1 - x₁) + y₁) ^ 2 + W.a₁ * (x₃ + 1) * (ℓ * (x₃ + 1 - x₁) + y₁)
      + W.a₃ * (ℓ * (x₃ + 1 - x₁) + y₁)
      - ((x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆)‖ ≤ ‖x₁‖ := by
    have ht2 : ‖(x₃ + 1) ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht
    have ht3 : ‖(x₃ + 1) ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht
    have hc : ‖(x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆‖ ≤ 1 := by
      refine add_le (add_le (add_le ht3 ?_) ?_) a6
      · simpa using mul_le a2 ht2
      · simpa using mul_le a4 ht
    refine sub_le (add_le (add_le ?_ ?_) ?_) (hc.trans (by nlinarith))
    · rw [norm_pow]; exact (pow_le_pow_left₀ (norm_nonneg _) hu 2).trans hMsq
    · have := mul_le (mul_le a1 ht) hu
      linarith
    · have := mul_le a3 hu
      linarith

  have hRHS : ‖x₁‖ * ‖x₂‖ ≤ ‖(x₃ + 1 - x₁) * (x₃ + 1 - x₂) * (x₃ + 1 - x₃)‖ := by
    have e1 : ‖x₁‖ ≤ ‖x₃ + 1 - x₁‖ := by
      rw [norm_sub_rev]; exact le_sub_of_lt (by linarith)
    have e2 : ‖x₂‖ ≤ ‖x₃ + 1 - x₂‖ := by
      rw [norm_sub_rev]; exact le_sub_of_lt (by linarith)
    have e3 : x₃ + 1 - x₃ = 1 := by ring
    rw [e3, mul_one, norm_mul]
    exact mul_le_mul e1 e2 (norm_nonneg _) (norm_nonneg _)
  have heq : (ℓ * (x₃ + 1 - x₁) + y₁) ^ 2 + W.a₁ * (x₃ + 1) * (ℓ * (x₃ + 1 - x₁) + y₁)
      + W.a₃ * (ℓ * (x₃ + 1 - x₁) + y₁)
      - ((x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆) =
      -((x₃ + 1 - x₁) * (x₃ + 1 - x₂) * (x₃ + 1 - x₃)) := by
    linear_combination hev
  rw [heq, norm_neg] at hLHS
  have := hRHS.trans hLHS
  nlinarith

end Formalism.ELL.FormalGroupPointsSubgroup

namespace Formalism.ELL

open WeierstrassCurve

open Classical in
theorem formal_group_points_subgroup_holds : Formalism.ELL.FormalGroupPointsSubgroup' := by
  intro K _ _ W hW _ P Q hP hQ
  refine ⟨?_, ?_⟩
  · rcases P with _ | @⟨x₁, y₁, h₁⟩
    · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, zero_add]; exact hQ
    rcases Q with _ | @⟨x₂, y₂, h₂⟩
    · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, add_zero]; exact hP
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
      trivial
    · rw [Affine.Point.add_some hxy]
      exact FormalGroupPointsSubgroup.addX_norm W hW h₁.1 h₂.1 hxy hP hQ
  · rcases P with _ | @⟨x, y, h⟩
    · trivial
    · simpa [InFormalGroupPoints] using hP

end Formalism.ELL
end
end

section

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

namespace FrobeniusExpansion

theorem exists_sum_pow_prime_pow {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → A) (n : ℕ) :
    ∃ r : A, (∑ i ∈ s, f i) ^ (p ^ n) = ∑ i ∈ s, f i ^ (p ^ n) + (p : A) * r := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp [zero_pow (pow_ne_zero n hp.ne_zero)]
  | insert a s ha ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hp (f a) (∑ i ∈ s, f i) n
    refine ⟨f a * (∑ i ∈ s, f i) * r' + r, ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]
    ring

end FrobeniusExpansion

open MvPolynomial in
theorem frobenius_expansion : FrobExpand := by
  intro K _ _ p hp _hp1 m j a b ha hab α
  classical
  set R := unitBall K
  let a' : Fin m → R := fun e => ⟨a e, ha e⟩
  obtain ⟨r, hr⟩ := FrobeniusExpansion.exists_sum_pow_prime_pow (A := MvPolynomial (Fin m) R) hp
    Finset.univ (fun e => C (a' e) * X e) j
  have hmap : (∑ e, C (a e) * X e : MvPolynomial (Fin m) K)
      = map R.subtype (∑ e, C (a' e) * X e) := by
    simp [a']
  have key : (∑ e, C (a e) * X e : MvPolynomial (Fin m) K) ^ (p ^ j)
        - ∑ e, C (b e) * X e ^ (p ^ j)
      = ∑ e, C (a e ^ (p ^ j) - b e) * X e ^ (p ^ j)
        + C (p : K) * map R.subtype r := by

    rw [hmap, ← map_pow, hr, map_add (f := _), map_sum, map_mul, map_natCast]
    simp only [map_pow, map_mul, map_C, map_X, mul_pow, map_sub, sub_mul,
      Finset.sum_sub_distrib, map_natCast]
    simp [a']
    ring
  rw [key, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_sum, coeff_C_mul, coeff_map]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun e _ => ?_
    rw [coeff_C_mul, coeff_X_pow, norm_mul]
    split_ifs
    · simpa using hab e
    · simp
  · rw [norm_mul]
    have h1 : ‖(r.coeff α : K)‖ ≤ 1 := (r.coeff α).2
    calc ‖(p : K)‖ * ‖(r.coeff α : K)‖ ≤ ‖(p : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖(p : K)‖ := mul_one _

end Formalism.ELL
end
end

section

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace VeluIntegrality

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

def ball : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rwa [norm_neg]

theorem veluGx_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluGx W x y ∈ (ball : Subring K) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  unfold veluGx
  refine sub_mem (add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem hx 2))
    (mul_mem (mul_mem (ofNat_mem _ 2) h2) hx)) h4) (mul_mem h1 hy)

theorem veluGy_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluGy W x y ∈ (ball : Subring K) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  unfold veluGy
  exact sub_mem (sub_mem (mul_mem (neg_mem (ofNat_mem _ 2)) hy) (mul_mem h1 hx)) h3

theorem veluV_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluV W x y ∈ (ball : Subring K) := by
  have gx := veluGx_mem W hW hx hy
  have gy := veluGy_mem W hW hx hy
  unfold veluV
  split_ifs
  · exact gx
  · exact sub_mem (mul_mem (ofNat_mem _ 2) gx) (mul_mem hW.1 gy)

theorem veluU_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluU W x y ∈ (ball : Subring K) := by
  unfold veluU
  exact pow_mem (veluGy_mem W hW hx hy) 2

end VeluIntegrality

open VeluIntegrality in
theorem velu_integral_model : VeluIntegralModel := by
  intro K _ _ W k S hW hS
  have hx : ∀ i, (S i).1 ∈ (ball : Subring K) := fun i => (hS i).1
  have hy : ∀ i, (S i).2 ∈ (ball : Subring K) := fun i => (hS i).2
  have hv : (∑ i, veluV W (S i).1 (S i).2) ∈ (ball : Subring K) :=
    sum_mem fun i _ => veluV_mem W hW (hx i) (hy i)
  have hw : (∑ i, (veluU W (S i).1 (S i).2 + (S i).1 * veluV W (S i).1 (S i).2))
      ∈ (ball : Subring K) :=
    sum_mem fun i _ => add_mem (veluU_mem W hW (hx i) (hy i))
      (mul_mem (hx i) (veluV_mem W hW (hx i) (hy i)))
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · show W.a₄ - 5 * (∑ i, veluV W (S i).1 (S i).2) ∈ (ball : Subring K)
    exact sub_mem h4 (mul_mem (ofNat_mem _ 5) hv)
  · show W.a₆ - (W.a₁ ^ 2 + 4 * W.a₂) * (∑ i, veluV W (S i).1 (S i).2)
      - 7 * (∑ i, (veluU W (S i).1 (S i).2 + (S i).1 * veluV W (S i).1 (S i).2)) ∈ (ball : Subring K)
    exact sub_mem (sub_mem h6 (mul_mem (add_mem (pow_mem h1 2) (mul_mem (ofNat_mem _ 4) h2)) hv))
      (mul_mem (ofNat_mem _ 7) hw)

end Formalism.ELL
end
end
