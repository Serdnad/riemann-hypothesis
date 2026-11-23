module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.BigOperators
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Complex.IntegerCompl

@[expose] public section

section

open Polynomial

namespace GlobalTheory.MonicFactorDegree

variable {κ : Type} [Field κ]

noncomputable def subst (D : ℕ) : Polynomial (Polynomial κ) →+* Polynomial (Polynomial κ) :=
  eval₂RingHom (mapRingHom (C : κ →+* Polynomial κ)) (C X * X ^ D)

lemma term_coeff (D j m i : ℕ) (p : Polynomial κ) :
    (((mapRingHom (C : κ →+* Polynomial κ)) p * (C X * X ^ D) ^ j).coeff m).coeff i =
      if D * j ≤ m then (if i = j then p.coeff (m - D * j) else 0) else 0 := by
  have hC : (C (X : Polynomial κ) : Polynomial (Polynomial κ)) ^ j = C (X ^ j) := (C_pow ..).symm
  rw [mul_pow, hC, ← pow_mul, ← mul_assoc, coeff_mul_X_pow']
  split_ifs with h1 h2
  · subst h2; rw [coeff_mul_C, coe_mapRingHom, coeff_map, coeff_C_mul_X_pow]; simp
  · rw [coeff_mul_C, coe_mapRingHom, coeff_map, coeff_C_mul_X_pow]; simp [h2]
  · simp

lemma subst_coeff_coeff (D : ℕ) (P : Polynomial (Polynomial κ)) (i k : ℕ) :
    ((subst D P).coeff (k + D * i)).coeff i = (P.coeff i).coeff k := by
  simp only [subst, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum, finsetSum_coeff, term_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro hi; simp [notMem_support_iff.mp hi]

theorem monic_factor_coeff_natDegree_le : ∀ {κ : Type} [Field κ] (Φ A B : Polynomial (Polynomial κ))
    (D : ℕ), Φ.Monic → A.Monic → B.Monic → Φ = A * B → (∀ i, (Φ.coeff i).natDegree ≤ D) →
    ∀ i, (A.coeff i).natDegree ≤ Φ.natDegree * D := by
  intro κ _ Φ A B D hΦ _ hB hAB hD i
  by_cases hi : A.coeff i = 0
  · simp [hi]
  have key : ∀ P : Polynomial (Polynomial κ), ∀ j, P.coeff j ≠ 0 →
      (P.coeff j).natDegree + D * j ≤ (subst D P).natDegree ∧ subst D P ≠ 0 := by
    intro P j hj
    have h := subst_coeff_coeff D P j (P.coeff j).natDegree
    have hne : (subst D P).coeff ((P.coeff j).natDegree + D * j) ≠ 0 := by
      intro h0
      rw [h0, coeff_zero] at h
      exact hj (leadingCoeff_eq_zero.mp h.symm)
    exact ⟨le_natDegree_of_ne_zero hne, fun h0 => hne (by simp [h0])⟩
  have hAi := key A i hi
  have hB0 := (key B B.natDegree (by rw [hB.coeff_natDegree]; exact one_ne_zero)).2
  have hmul : (subst D Φ).natDegree = (subst D A).natDegree + (subst D B).natDegree := by
    rw [hAB, map_mul, natDegree_mul hAi.2 hB0]
  have hup : (subst D Φ).natDegree ≤ Φ.natDegree * D := by
    simp only [subst, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum]
    apply natDegree_sum_le_of_forall_le
    intro j hj
    have hjd : j ≤ Φ.natDegree := le_natDegree_of_mem_supp j hj
    have h1 : (mapRingHom (C : κ →+* Polynomial κ) (Φ.coeff j)).natDegree ≤ (Φ.coeff j).natDegree := by
      rw [coe_mapRingHom]; exact natDegree_map_le
    have h2 : ((C X * X ^ D : Polynomial (Polynomial κ)) ^ j).natDegree ≤ j * D := by
      calc _ ≤ j * (C X * X ^ D : Polynomial (Polynomial κ)).natDegree := natDegree_pow_le
        _ ≤ j * D := by
          apply Nat.mul_le_mul_left
          calc _ ≤ (C X : Polynomial (Polynomial κ)).natDegree + (X ^ D : Polynomial (Polynomial κ)).natDegree :=
                natDegree_mul_le
            _ = D := by simp
    have h3 : (Φ.coeff j).natDegree + j * D ≤ Φ.natDegree * D := by
      rcases hjd.lt_or_eq with h | h
      · have h4 := hD j
        have h5 : (j + 1) * D ≤ Φ.natDegree * D := Nat.mul_le_mul_right _ h
        rw [add_mul, one_mul] at h5
        omega
      · rw [h, hΦ.coeff_natDegree, natDegree_one, zero_add]
    exact (natDegree_mul_le).trans (by omega)
  have := hAi.1
  have h6 : (A.coeff i).natDegree ≤ (subst D A).natDegree := by omega
  omega

end GlobalTheory.MonicFactorDegree
end

section

open scoped Matrix
open Polynomial

namespace GlobalTheory

theorem det_affine_eval {K : Type} [Field K] {m : ℕ} (U V : Matrix (Fin m) (Fin m) K) (t : K) :
    ((X : K[X]) • V.map C + U.map C).det.eval t = (U + t • V).det := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [add_comm]
  ring

theorem exists_nat_det_ne_zero_affine {K : Type} [Field K] [CharZero K] {m : ℕ}
    (U V : Matrix (Fin m) (Fin m) K) (t : K) (h : (U + t • V).det ≠ 0) :
    ∃ k : ℕ, (U + (k : K) • V).det ≠ 0 := by
  classical
  set p : K[X] := ((X : K[X]) • V.map C + U.map C).det
  have hp : p ≠ 0 := by
    intro h0
    apply h
    rw [← det_affine_eval]
    simp [p, h0]
  by_contra hall
  push_neg at hall
  have hsub : Set.range (fun k : ℕ => (k : K)) ⊆ (p.roots.toFinset : Set K) := by
    rintro _ ⟨k, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot, det_affine_eval]
    exact hall k
  have hinf : (Set.range (fun k : ℕ => (k : K))).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  exact hinf ((p.roots.toFinset.finite_toSet).subset hsub)

theorem exists_nat_coeffs_on_finset_det_sum_ne_zero {K : Type} [Field K] [CharZero K] {m n : ℕ}
    (T : Fin n → Matrix (Fin m) (Fin m) K) (s : Finset (Fin n)) :
    ∀ b : Fin n → K, (∑ i, b i • T i).det ≠ 0 →
      ∃ b' : Fin n → K, (∑ i, b' i • T i).det ≠ 0 ∧ ∀ i ∈ s, ∃ k : ℕ, b' i = k := by
  classical
  induction s using Finset.induction_on with
  | empty => intro b hb; exact ⟨b, hb, by simp⟩
  | insert j s hj ih =>
    intro b hb
    obtain ⟨b₁, hb₁, hs⟩ := ih b hb
    have key : ∀ t : K, ∑ i, Function.update b₁ j t i • T i
        = (∑ i, Function.update b₁ j 0 i • T i) + t • T j := by
      intro t
      have h1 := Finset.sum_erase_add (s := Finset.univ) (a := j)
        (f := fun i => Function.update b₁ j t i • T i) (Finset.mem_univ j)
      have h2 := Finset.sum_erase_add (s := Finset.univ) (a := j)
        (f := fun i => Function.update b₁ j 0 i • T i) (Finset.mem_univ j)
      have h3 : ∑ i ∈ Finset.univ.erase j, Function.update b₁ j t i • T i
          = ∑ i ∈ Finset.univ.erase j, Function.update b₁ j 0 i • T i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
          Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [← h1, ← h2, h3]
      simp
    have hb₁' : ((∑ i, Function.update b₁ j 0 i • T i) + b₁ j • T j).det ≠ 0 := by
      rw [← key, Function.update_eq_self]; exact hb₁
    obtain ⟨k, hk⟩ := exists_nat_det_ne_zero_affine _ _ _ hb₁'
    refine ⟨Function.update b₁ j (k : K), by rw [key]; exact hk, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact ⟨k, by simp⟩
    · obtain ⟨k', hk'⟩ := hs i hi'
      refine ⟨k', ?_⟩
      rw [Function.update_of_ne (by rintro rfl; exact hj hi')]
      exact hk'

theorem exists_nat_coeffs_det_ne_zero : ∀ {K : Type} [Field K] [CharZero K] {m n : ℕ}
    (T : Fin n → Matrix (Fin m) (Fin m) K) (b : Fin n → K),
    (∑ i, b i • T i).det ≠ 0 → ∃ a : Fin n → ℕ, (∑ i, (a i : K) • T i).det ≠ 0 := by
  intro K _ _ m n T b hb
  obtain ⟨b', hb', hs⟩ := exists_nat_coeffs_on_finset_det_sum_ne_zero T Finset.univ b hb
  choose a ha using fun i => hs i (Finset.mem_univ i)
  refine ⟨a, ?_⟩
  simp_rw [← ha]; exact hb'

end GlobalTheory
end

section

namespace GlobalTheory

open WeierstrassCurve WeierstrassCurve.Affine

namespace TorsionUnit

variable {K : Type} [NormedField K] [IsUltrametricDist K]

end TorsionUnit

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma short_negY_eq (A B x y : K) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).negY x y = -y := by
  simp [Affine.negY]

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma short_addX_eq (A B x₁ x₂ l : K) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).addX x₁ x₂ l = l ^ 2 - x₁ - x₂ := by
  simp [Affine.addX]

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_add_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_le_one_of_norm_sq_sub_le_one {l s : K} (h : ‖l ^ 2 - s‖ ≤ 1) (hs : ‖s‖ ≤ 1) :
    ‖l‖ ≤ 1 := by
  have hsq : ‖l ^ 2‖ ≤ 1 := by
    have := norm_add_le_one_of_le_one h hs
    rwa [sub_add_cancel] at this
  rw [norm_pow] at hsq
  exact (pow_le_one_iff_of_nonneg (norm_nonneg l) two_ne_zero).mp hsq

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_mul_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma short_equation_of_nonsingular {A B x y : K}
    (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + A * x + B := by
  have := h.1
  simp [Affine.equation_iff] at this
  linear_combination this

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_sub_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact norm_add_le_one_of_le_one ha (by rwa [norm_neg])

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  exact_mod_cast IsUltrametricDist.norm_natCast_le_one K n

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_y_eq_one_of_nsmul_eq_zero [DecidableEq K] {A B : K} {N : ℕ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (h2 : ‖(2 : K)‖ = 1) (hD : ‖4 * A ^ 3 + 27 * B ^ 2‖ = 1) (hN : Odd N)
    (hT : ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1)
    {x y : K} (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y)
    (hP : N • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖y‖ = 1 := by
  have hx := hT _ _ h hP
  have h2ne : (2 : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h2
    exact zero_ne_one h2
  have hy : y ≠ ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).negY x y := by
    intro hyy
    have hneg : -Point.some x y h = Point.some x y h := by
      rw [Point.neg_some]
      congr 1
      exact hyy.symm
    obtain ⟨k, rfl⟩ := hN
    have hPP : Point.some x y h + Point.some x y h = 0 := by
      nth_rewrite 1 [← hneg]
      exact neg_add_cancel _
    rw [add_smul, one_smul, mul_comm, mul_smul, two_smul, hPP, smul_zero, zero_add] at hP
    simp at hP
  have hy0 : y ≠ 0 := by
    intro h0
    apply hy
    rw [short_negY_eq, h0, neg_zero]
  have hdbl := Point.add_of_Y_ne (h₁ := h) (h₂ := h) hy
  have h3 := hT _ _ _ (by rw [← hdbl, smul_add, hP, add_zero])
  rw [short_addX_eq] at h3
  set l := ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).slope x x y y with hl
  have hlrel : l * (2 * y) = 3 * x ^ 2 + A := by
    rw [hl, slope_of_Y_ne rfl hy, short_negY_eq, sub_neg_eq_add, ← two_mul,
      div_mul_cancel₀ _ (mul_ne_zero h2ne hy0)]
    simp
  have hlle : ‖l‖ ≤ 1 :=
    norm_le_one_of_norm_sq_sub_le_one (s := x + x) (by rw [← sub_sub]; exact h3)
      (norm_add_le_one_of_le_one hx hx)
  have hder : ‖3 * x ^ 2 + A‖ ≤ ‖y‖ := by
    rw [← hlrel, norm_mul, norm_mul, h2, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hlle
  have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hx3 : ‖x ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hf : ‖x ^ 3 + A * x + B‖ ≤ 1 :=
    norm_add_le_one_of_le_one (norm_add_le_one_of_le_one hx3 (norm_mul_le_one_of_le_one hA hx)) hB
  have hyeq := short_equation_of_nonsingular h
  have hyle : ‖y‖ ≤ 1 := by
    have : ‖y‖ ^ 2 ≤ 1 := by rw [← norm_pow, hyeq]; exact hf
    exact (pow_le_one_iff_of_nonneg (norm_nonneg y) two_ne_zero).mp this
  refine le_antisymm hyle (not_lt.mp fun hlt => ?_)
  have hflt : ‖x ^ 3 + A * x + B‖ < 1 := by
    rw [← hyeq, norm_pow]
    nlinarith [norm_nonneg y]
  have hderlt : ‖3 * x ^ 2 + A‖ < 1 := hder.trans_lt hlt
  have ha : ‖27 * B - 18 * A * x‖ ≤ 1 :=
    norm_sub_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 27) hB)
      (norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 18) hA) hx)
  have hb : ‖6 * A * x ^ 2 - 9 * B * x + 4 * A ^ 2‖ ≤ 1 := by
    refine norm_add_le_one_of_le_one (norm_sub_le_one_of_le_one ?_ ?_) ?_
    · exact norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 6) hA) hx2
    · exact norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 9) hB) hx
    · refine norm_mul_le_one_of_le_one (norm_ofNat_le_one 4) ?_
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hA
  have hid : 4 * A ^ 3 + 27 * B ^ 2 = (27 * B - 18 * A * x) * (x ^ 3 + A * x + B) +
      (6 * A * x ^ 2 - 9 * B * x + 4 * A ^ 2) * (3 * x ^ 2 + A) := by ring
  have hlt1 : ‖4 * A ^ 3 + 27 * B ^ 2‖ < 1 := by
    rw [hid]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans_lt hflt
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans_lt hderlt
  rw [hD] at hlt1
  exact lt_irrefl _ hlt1

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_sub_y_le_norm_sub_x_of_torsion [DecidableEq K] {A B : K} {N : ℕ}
    (hT : ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1)
    {x₁ y₁ x₂ y₂ : K} (h₁ : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x₁ y₁)
    (h₂ : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x₂ y₂)
    (hP : N • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0)
    (hQ : N • (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0) (hx : x₁ ≠ x₂) :
    ‖y₁ - y₂‖ ≤ ‖x₁ - x₂‖ := by
  have hsum := Point.add_of_X_ne (h₁ := h₁) (h₂ := h₂) hx
  have h3 := hT _ _ _ (by rw [← hsum, smul_add, hP, hQ, add_zero])
  rw [short_addX_eq, slope_of_X_ne hx] at h3
  have hl : ‖(y₁ - y₂) / (x₁ - x₂)‖ ≤ 1 :=
    norm_le_one_of_norm_sq_sub_le_one (s := x₁ + x₂) (by rw [← sub_sub]; exact h3)
      (norm_add_le_one_of_le_one (hT _ _ h₁ hP) (hT _ _ h₂ hQ))
  have hne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have : y₁ - y₂ = (y₁ - y₂) / (x₁ - x₂) * (x₁ - x₂) := by field_simp
  rw [this, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hl


open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
theorem _root_.GlobalTheory.torsion_points_distinct_mod_maximal_ideal : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (A B : K) (N : ℕ), ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖(2 : K)‖ = 1 → ‖4 * A ^ 3 + 27 * B ^ 2‖ = 1 → Odd N → (∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y), N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1) → ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y), N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x ^ 3 + A * x + B‖ = 1 ∧ ∀ (x' y' : K) (h' : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x' y'), N • (WeierstrassCurve.Affine.Point.some x' y' h') = 0 → x ≠ x' → ‖x - x'‖ = 1 := by
  intro K _ _ _ A B N hA hB h2 hD hN hT x y h hP
  have hy1 := norm_y_eq_one_of_nsmul_eq_zero hA hB h2 hD hN hT h hP
  refine ⟨?_, ?_⟩
  · rw [← short_equation_of_nonsingular h, norm_pow, hy1, one_pow]
  · intro x' y' h' hP' hx
    have hxx : ‖x - x'‖ ≤ 1 := norm_sub_le_one_of_le_one (hT _ _ h hP) (hT _ _ h' hP')
    refine le_antisymm hxx (not_lt.mp fun hlt => ?_)
    have hsub := norm_sub_y_le_norm_sub_x_of_torsion hT h h' hP hP' hx
    have hnegP : N • Point.some x' _
        (((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.nonsingular_neg x' y').mpr h') = 0 := by
      rw [← Point.neg_some h', smul_neg, hP', neg_zero]
    have hadd := norm_sub_y_le_norm_sub_x_of_torsion hT h _ hP hnegP hx
    rw [short_negY_eq, sub_neg_eq_add] at hadd
    have h2y : ‖2 * y‖ < 1 := by
      have : 2 * y = (y - y') + (y + y') := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hsub.trans_lt hlt) (hadd.trans_lt hlt))
    rw [norm_mul, h2, hy1, one_mul] at h2y
    exact lt_irrefl _ h2y

end GlobalTheory
end

section

open Complex Filter Topology
open scoped Real

namespace GlobalTheory

lemma sum_Icc_inv_add_eq_cotTerm (w : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (w + n)⁻¹ =
      1 / w + ∑ j ∈ Finset.range N, (1 / (w - (j + 1)) + 1 / (w + (j + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N:ℤ) + 1)) (insert ((N:ℤ) + 1) (Finset.Icc (-(N:ℤ)) N)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [h, Finset.sum_insert, Finset.sum_insert, ih, Finset.sum_range_succ]
    · push_cast
      simp only [one_div, sub_eq_add_neg]
      ring
    · simp only [Finset.mem_Icc]; omega
    · simp only [Finset.mem_Icc, Finset.mem_insert]; omega

theorem tendsto_sum_Icc_inv_residue_cot :
    ∀ (L : ℕ) (z : ℂ) (r : ℕ), 0 < L → 0 < z.im →
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹) atTop
        (𝓝 (π / L * Complex.cot (π * ((z + r) / L)))) := by
  intro L z r hL hz
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  set w : ℂ := (z + r) / L with hw
  have hwL : z + r = w * L := by rw [hw]; field_simp
  have hmem : w ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.im hwL
    rw [← hk] at this
    simp at this
    linarith
  have h1 := ((tendsto_logDeriv_euler_cot_sub hmem).const_add (1 / w)).const_mul (L : ℂ)⁻¹
  have hlim : (L : ℂ)⁻¹ * (1 / w + (π * Complex.cot (π * w) - 1 / w)) =
      π / L * Complex.cot (π * w) := by ring
  rw [hlim] at h1
  refine h1.congr fun N => ?_
  have := sum_Icc_inv_add_eq_cotTerm w N
  simp only [cotTerm]
  rw [← this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hwL, ← add_mul, mul_inv, mul_comm]

end GlobalTheory
end
