module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

section

open Finset

namespace GlobalTheory.CompanionTheory.EntrywiseCount

theorem card_lt (n r : ℕ) (hr : r ≤ n) :
    (univ.filter (fun i : Fin n => (i : ℕ) < r)).card = r := by
  have h : (univ.filter (fun i : Fin n => (i : ℕ) < r)).card
      = ((range n).filter (fun i => i < r)).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Fin.sum_univ_eq_sum_range (fun i => if i < r then 1 else 0) n
  rw [h]
  have : (range n).filter (fun i => i < r) = range r := by
    ext x
    simp only [mem_filter, mem_range]
    omega
  rw [this, card_range]

theorem card_ge (n r : ℕ) (hr : r ≤ n) :
    (univ.filter (fun j : Fin n => r ≤ (j : ℕ))).card = n - r := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i : Fin n => (i : ℕ) < r)
  rw [card_lt n r hr, Finset.card_univ, Fintype.card_fin] at h
  simp only [not_lt] at h
  omega

theorem prod_indicator (n r : ℕ) (hr : r ≤ n) (E : ℝ) :
    ∏ i : Fin n, ∏ j : Fin n, (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then E else 1)
      = E ^ (r * (n - r)) := by
  have inner : ∀ i : Fin n, ∏ j : Fin n, (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then E else 1)
      = if (i : ℕ) < r then E ^ (n - r) else 1 := by
    intro i
    by_cases hi : (i : ℕ) < r
    · simp only [hi, true_and, if_true]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_ge n r hr]
    · simp [hi]
  simp only [inner]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_lt n r hr,
    ← pow_mul, mul_comm]

theorem factor_le (d : ℕ) (C β t : ℝ) (p : Prop) [Decidable p]
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    C * (1 + β * (if p then Real.exp t else 1)) ^ d
      ≤ (C * (1 + β) ^ d) * (if p then Real.exp ((d : ℝ) * t) else 1) := by
  have hE : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hbase : 1 + β * (if p then Real.exp t else 1)
      ≤ (1 + β) * (if p then Real.exp t else 1) := by
    split_ifs
    · nlinarith
    · linarith
  have hnn : 0 ≤ 1 + β * (if p then Real.exp t else 1) := by
    split_ifs <;> positivity
  have hpow := pow_le_pow_left₀ hnn hbase d
  rw [mul_pow] at hpow
  have hE' : (if p then Real.exp t else 1) ^ d = (if p then Real.exp ((d : ℝ) * t) else 1) := by
    split_ifs
    · rw [← Real.exp_nat_mul]
    · simp
  rw [hE'] at hpow
  calc C * (1 + β * (if p then Real.exp t else 1)) ^ d
      ≤ C * ((1 + β) ^ d * (if p then Real.exp ((d : ℝ) * t) else 1)) :=
        mul_le_mul_of_nonneg_left hpow hC
    _ = _ := by ring

theorem prod_entrywise_le : ∀ (n r d : ℕ), r ≤ n → ∀ (C β t : ℝ), 0 ≤ C → 0 ≤ β → 0 ≤ t →
    ∏ i : Fin n, ∏ j : Fin n,
        C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d
      ≤ C ^ (n * n) * (1 + β) ^ (d * (n * n))
        * Real.exp ((d : ℝ) * ((r : ℝ) * ((n : ℝ) - r)) * t) := by
  intro n r d hr C β t hC hβ ht
  have hnn : ∀ (i j : Fin n), 0 ≤
      C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d := by
    intro i j
    have : 0 ≤ (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1) := by
      split_ifs <;> positivity
    positivity
  have step : ∏ i : Fin n, ∏ j : Fin n,
        C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d
      ≤ ∏ i : Fin n, ∏ j : Fin n, ((C * (1 + β) ^ d) *
          (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp ((d : ℝ) * t) else 1)) := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Finset.prod_nonneg (fun j _ => hnn i j)
    · intro i _
      apply Finset.prod_le_prod₀
      · intro j _
        exact hnn i j
      · intro j _
        exact factor_le d C β t _ hC hβ ht
  refine step.trans (le_of_eq ?_)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [prod_indicator n r hr, ← Real.exp_nat_mul, ← pow_mul]
  have hp : (((1 + β) ^ d) ^ n) ^ n = (1 + β) ^ (d * (n * n)) := by
    rw [← pow_mul, ← pow_mul]
  have : (((r * (n - r) : ℕ) : ℝ)) * ((d : ℝ) * t) = (d : ℝ) * ((r : ℝ) * ((n : ℝ) - r)) * t := by
    rw [Nat.cast_mul, Nat.cast_sub hr]
    ring
  rw [this]
  rw [hp]

end GlobalTheory.CompanionTheory.EntrywiseCount
end

section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.RealPlace

theorem eq_diagonal_of_upperTriangular_of_unitary {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : B.BlockTriangular id) (hBB : Bᴴ * B = 1) : B = diagonal (fun i => B i i) := by
  have hinv : B⁻¹ = Bᴴ := Matrix.inv_eq_left_inv hBB
  haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (Matrix.isUnit_det_of_left_inverse hBB)
  have hT : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  rw [hinv] at hT
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : Bᴴ j i = 0 := hT h
    rw [Matrix.conjTranspose_apply, star_eq_zero] at h1
    rw [h1, Matrix.diagonal_apply_ne _ (ne_of_lt h)]
  · simp
  · rw [hB h, Matrix.diagonal_apply_ne _ (ne_of_gt h)]

theorem flag_isometry_diagonal_on_frame (n r : ℕ) (J P p : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (hJ : IsUnit J.det) (hXY : Xᴴ * J * Y = 1)
    (_hP : P.PosDef) (_hPJ : P * J⁻¹ * P = J) (hPX : P * X = J * Y)
    (hpJ : pᴴ * J * p = J) (hpP : pᴴ * P * p = P)
    (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.BlockTriangular id) (hpX : p * X = X * B) :
    ∃ d : Fin r → ℂ, p * X = X * diagonal d ∧ p * Y = Y * diagonal d := by
  have hXPX : Xᴴ * P * X = 1 := by
    rw [Matrix.mul_assoc, hPX, ← Matrix.mul_assoc]
    exact hXY
  have hBB : Bᴴ * B = 1 := by
    calc Bᴴ * B = Bᴴ * (Xᴴ * P * X) * B := by rw [hXPX, Matrix.mul_one]
      _ = (X * B)ᴴ * P * (X * B) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (p * X)ᴴ * P * (p * X) := by rw [hpX]
      _ = Xᴴ * (pᴴ * P * p) * X := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hpP]
          exact hXPX
  have hBd := eq_diagonal_of_upperTriangular_of_unitary B hB hBB
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ, D = diagonal (fun i => B i i) := ⟨_, rfl⟩
  have hBD : B = D := hBd.trans hD.symm
  have hpXD : p * X = X * D := by
    rw [hpX, hBD]
  have hr : pᴴ * (J * p * J⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hpJ, Matrix.mul_nonsing_inv J hJ]
  have hr' : (J * p * J⁻¹) * pᴴ = 1 := mul_eq_one_comm.mp hr
  have key : J * (p * Y) = J * (Y * D) := by
    calc J * (p * Y) = (J * p * J⁻¹) * pᴴ * (J * (p * Y)) := by rw [hr', Matrix.one_mul]
      _ = (J * p * J⁻¹) * (pᴴ * J * p) * Y := by simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * (J * Y) := by
          rw [hpJ]
          simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * (pᴴ * P * p * X) := by rw [hpP, hPX]
      _ = (J * p * J⁻¹) * pᴴ * (P * (p * X)) := by simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * pᴴ * (P * X * D) := by
          rw [hpXD]
          simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * pᴴ * (J * (Y * D)) := by
          rw [hPX]
          simp only [Matrix.mul_assoc]
      _ = J * (Y * D) := by rw [hr', Matrix.one_mul]
  have hpYD : p * Y = Y * D := by
    calc p * Y = J⁻¹ * (J * (p * Y)) := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hJ, Matrix.one_mul]
      _ = J⁻¹ * (J * (Y * D)) := by rw [key]
      _ = Y * D := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hJ, Matrix.one_mul]
  exact ⟨fun i => B i i, hD ▸ hpXD, hD ▸ hpYD⟩

end GlobalTheory.CompanionTheory.RealPlace
end

section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.WittMajorant

variable {n : ℕ}

private theorem conj_mul (U V D E : Matrix (Fin n) (Fin n) ℂ) (h : V * U = 1) :
    (U * D * V) * (U * E * V) = U * (D * E) * V := by
  calc (U * D * V) * (U * E * V) = U * D * (V * U) * E * V := by
        simp only [Matrix.mul_assoc]
    _ = U * (D * E) * V := by
        rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem exists_abs_sign {R : Matrix (Fin n) (Fin n) ℂ} (hR : R.IsHermitian) :
    ∃ A S : Matrix (Fin n) (Fin n) ℂ,
      A.PosSemidef ∧ A = S * R ∧ A = R * S ∧ S * S * R = R := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    have := Unitary.star_mul_self_of_mem hR.eigenvectorUnitary.2
    simpa [star_eq_conjTranspose] using this
  have hspec : R = U * diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hR.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def] using this
  set d : Fin n → ℂ := fun i => ((hR.eigenvalues i : ℝ) : ℂ) with hd
  set a : Fin n → ℂ := fun i => ((|hR.eigenvalues i| : ℝ) : ℂ) with ha
  set s : Fin n → ℂ := fun i => (((SignType.sign (hR.eigenvalues i) : SignType) : ℝ) : ℂ) with hs
  have hsd : ∀ i, s i * d i = a i := by
    intro i
    simp only [hs, hd, ha]
    rw [← Complex.ofReal_mul, sign_mul_self]
  have hds : ∀ i, d i * s i = a i := fun i => by rw [mul_comm, hsd]
  have hssd : ∀ i, s i * s i * d i = d i := by
    intro i
    simp only [hs, hd]
    rcases lt_trichotomy (hR.eigenvalues i) 0 with h | h | h
    · simp [sign_neg h]
    · simp [h]
    · simp [sign_pos h]
  refine ⟨U * diagonal a * Uᴴ, U * diagonal s * Uᴴ, ?_, ?_, ?_, ?_⟩
  · have h0 : (diagonal a).PosSemidef := by
      rw [posSemidef_diagonal_iff]
      intro i
      simp only [ha]
      exact_mod_cast abs_nonneg _
    have := h0.conjTranspose_mul_mul_same Uᴴ
    simpa using this
  · conv_rhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]
    simp only [hsd]
  · conv_rhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]
    simp only [hds]
  · conv_lhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, conj_mul _ _ _ _ hUU, diagonal_mul_diagonal, diagonal_mul_diagonal]
    simp only [hssd]
    exact hspec.symm

theorem exists_adapted_majorant (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (hJ : J.IsHermitian) (hdet : IsUnit J.det)
    (hXX : Xᴴ * J * X = 0) (hYY : Yᴴ * J * Y = 0) (hXY : Xᴴ * J * Y = 1) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.PosDef ∧ P * J⁻¹ * P = J ∧ P * X = J * Y := by
  have hJi : J⁻¹ * J = 1 := nonsing_inv_mul J hdet
  have hJi' : J * J⁻¹ = 1 := mul_nonsing_inv J hdet
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ.eq, Matrix.mul_assoc] using this
  have xx : Xᴴ * (J * X) = 0 := by rw [← Matrix.mul_assoc]; exact hXX
  have yy : Yᴴ * (J * Y) = 0 := by rw [← Matrix.mul_assoc]; exact hYY
  have xy : Xᴴ * (J * Y) = 1 := by rw [← Matrix.mul_assoc]; exact hXY
  have yx : Yᴴ * (J * X) = 1 := by rw [← Matrix.mul_assoc]; exact hYX
  set R : Matrix (Fin n) (Fin n) ℂ := J⁻¹ - X * Yᴴ - Y * Xᴴ with hRdef
  have hRh : R.IsHermitian := by
    have hi : (J⁻¹)ᴴ = J⁻¹ := (IsHermitian.inv hJ).eq
    unfold IsHermitian
    rw [hRdef, conjTranspose_sub, conjTranspose_sub, hi, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, conjTranspose_conjTranspose]
    abel
  have hRX : R * (J * X) = 0 := by
    rw [hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yx, xx,
      ← Matrix.mul_assoc J⁻¹, hJi]
    simp
  have hRY : R * (J * Y) = 0 := by
    rw [hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yy, xy,
      ← Matrix.mul_assoc J⁻¹, hJi]
    simp
  have hRJR : R * (J * R) = R := by
    have e : J * R = 1 - (J * X) * Yᴴ - (J * Y) * Xᴴ := by
      rw [hRdef, Matrix.mul_sub, Matrix.mul_sub, hJi', Matrix.mul_assoc, Matrix.mul_assoc]
    have e1 : R * (J * X * Yᴴ) = (R * (J * X)) * Yᴴ := (Matrix.mul_assoc _ _ _).symm
    have e2 : R * (J * Y * Xᴴ) = (R * (J * Y)) * Xᴴ := (Matrix.mul_assoc _ _ _).symm
    rw [e, Matrix.mul_sub, Matrix.mul_sub, e1, e2, hRX, hRY]
    simp
  obtain ⟨A, S, hA, hAS, hAR, hSSR⟩ := exists_abs_sign hRh
  have hAh : Aᴴ = A := hA.isHermitian.eq
  have hAX : A * (J * X) = 0 := by
    rw [hAS, Matrix.mul_assoc, hRX, Matrix.mul_zero]
  have hAY : A * (J * Y) = 0 := by
    rw [hAS, Matrix.mul_assoc, hRY, Matrix.mul_zero]
  have hXA : Xᴴ * (J * A) = 0 := by
    have := congrArg conjTranspose hAX
    simpa [conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc] using this
  have hYA : Yᴴ * (J * A) = 0 := by
    have := congrArg conjTranspose hAY
    simpa [conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc] using this
  have hAJA : A * (J * A) = R := by
    calc A * (J * A) = (S * R) * (J * (R * S)) := by rw [← hAS, ← hAR]
      _ = S * (R * (J * R)) * S := by simp only [Matrix.mul_assoc]
      _ = S * (R * S) := by rw [hRJR, Matrix.mul_assoc]
      _ = S * (S * R) := by rw [← hAR, hAS]
      _ = R := by rw [← Matrix.mul_assoc, hSSR]
  set T : Matrix (Fin n) (Fin n) ℂ := X * Xᴴ + Y * Yᴴ + A with hTdef
  have hTX : T * (J * X) = Y := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xx, yx, hAX]
    simp
  have hTY : T * (J * Y) = X := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xy, yy, hAY]
    simp
  have hTA : T * (J * A) = R := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hXA, hYA,
      hAJA]
    simp
  have hTJT : T * (J * T) = J⁻¹ := by
    have e : J * T = (J * X) * Xᴴ + (J * Y) * Yᴴ + J * A := by
      rw [hTdef, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
    have e1 : T * (J * X * Xᴴ) = (T * (J * X)) * Xᴴ := (Matrix.mul_assoc _ _ _).symm
    have e2 : T * (J * Y * Yᴴ) = (T * (J * Y)) * Yᴴ := (Matrix.mul_assoc _ _ _).symm
    rw [e, Matrix.mul_add, Matrix.mul_add, e1, e2, hTX, hTY, hTA, hRdef]
    abel
  have hTpsd : T.PosSemidef :=
    ((posSemidef_self_mul_conjTranspose X).add (posSemidef_self_mul_conjTranspose Y)).add hA
  have hTunit : IsUnit T := by
    have h1 : T * (J * T * J) = 1 := by
      calc T * (J * T * J) = (T * (J * T)) * J := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hTJT, hJi]
    exact (Matrix.isUnit_iff_isUnit_det T).2 (Matrix.isUnit_det_of_right_inverse h1)
  have hTpd : T.PosDef := hTpsd.posDef_iff_isUnit.2 hTunit
  have hJinj : Function.Injective J.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det J).2 hdet)
  refine ⟨J * T * J, ?_, ?_, ?_⟩
  · have := hTpd.conjTranspose_mul_mul_same hJinj
    rwa [hJ.eq] at this
  · calc J * T * J * J⁻¹ * (J * T * J) = J * (T * (J * T)) * J := by
          have h2 : J * T * J * J⁻¹ = J * T := by
            rw [Matrix.mul_assoc (J * T), hJi', Matrix.mul_one]
          rw [h2]
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hTJT, hJi', Matrix.one_mul]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hTX]

end GlobalTheory.CompanionTheory.WittMajorant
end

section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.RingSqrt

theorem exists_local_sqrt : ∀ (B V : Type) [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : B ≃+ V),
    Continuous ψ → Continuous ψ.symm →
    ∃ (r : B → B) (U : Set B), U ∈ nhds (1 : B) ∧ Filter.Tendsto r (nhds 1) (nhds 1) ∧
      (∀ᶠ h in nhds (1 : B), r h * r h = h) ∧ ∀ x ∈ U, ∀ y ∈ U, x * x = y * y → x = y := by
  intro B V _ _ _ _ _ _ ψ hψ hψs
  let L : V → (V →L[ℝ] V) := fun x =>
    AddMonoidHom.toRealLinearMap
      { toFun := fun y => ψ (ψ.symm x * ψ.symm y)
        map_zero' := by simp
        map_add' := by intro a b; simp [mul_add] }
      (hψ.comp (continuous_const.mul hψs))
  have hL : ∀ x y, L x y = ψ (ψ.symm x * ψ.symm y) := fun _ _ => rfl
  let A : V →L[ℝ] (V →L[ℝ] V) := AddMonoidHom.toRealLinearMap
      { toFun := L
        map_zero' := by ext y; simp [hL]
        map_add' := by intro a b; ext y; simp [hL, add_mul] }
      (continuous_clm_apply.2 fun y => hψ.comp (hψs.mul continuous_const))
  have hA : ∀ x y, A x y = ψ (ψ.symm x * ψ.symm y) := fun _ _ => rfl
  obtain ⟨Q, hQdef⟩ : ∃ Q : V → V, Q = fun y => y + y + A y y := ⟨_, rfl⟩
  have hQ : ∀ y, (1 + ψ.symm y) * (1 + ψ.symm y) = 1 + ψ.symm (Q y) := by
    intro y
    simp only [hQdef, hA, map_add (f := _), AddEquiv.symm_apply_apply, mul_add, add_mul, one_mul, mul_one]
    abel
  have hQ0 : Q 0 = 0 := by simp [hQdef]
  let e : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero)
  have hder : HasStrictFDerivAt Q (e : V →L[ℝ] V) 0 := by
    have h1 : HasStrictFDerivAt (fun y : V => y) (ContinuousLinearMap.id ℝ V) 0 :=
      hasStrictFDerivAt_id 0
    have h2 := A.hasStrictFDerivAt.clm_apply h1
    have h3 := (h1.add h1).add h2
    rw [hQdef]
    refine h3.congr_fderiv ?_
    ext v
    simp [e, two_smul, Units.smul_def]
  have hsub : Filter.Tendsto (fun h : B => ψ (h - 1)) (𝓝 1) (𝓝 0) := by
    have hc : Continuous fun h : B => ψ (h - 1) := hψ.comp (continuous_id.sub continuous_const)
    simpa using hc.tendsto 1
  have hg : Filter.Tendsto (hder.localInverse Q e 0) (𝓝 0) (𝓝 0) := by
    have := hder.localInverse_tendsto
    rwa [hQ0] at this
  have hr : ∀ᶠ y in 𝓝 (0 : V), Q (hder.localInverse Q e 0 y) = y := by
    have := hder.eventually_right_inverse
    rwa [hQ0] at this
  refine ⟨fun h => 1 + ψ.symm (hder.localInverse Q e 0 (ψ (h - 1))),
    (fun x => ψ (x - 1)) ⁻¹' (hder.toOpenPartialHomeomorph Q).source, ?_, ?_, ?_, ?_⟩
  · exact hsub ((hder.toOpenPartialHomeomorph Q).open_source.mem_nhds
      hder.mem_toOpenPartialHomeomorph_source)
  · have h0 : Filter.Tendsto (fun h : B => ψ.symm (hder.localInverse Q e 0 (ψ (h - 1))))
        (𝓝 1) (𝓝 0) := by
      have := (hψs.tendsto 0).comp (hg.comp hsub)
      simpa [Function.comp_def] using this
    simpa using (tendsto_const_nhds (x := (1 : B))).add h0
  · filter_upwards [hsub hr] with h hh
    rw [hQ, hh]
    simp
  · intro x hx y hy hxy
    have key : Q (ψ (x - 1)) = Q (ψ (y - 1)) := by
      have e1 := hQ (ψ (x - 1))
      have e2 := hQ (ψ (y - 1))
      simp only [AddEquiv.symm_apply_apply, add_sub_cancel] at e1 e2
      exact ψ.symm.injective (add_left_cancel (e1.symm.trans (hxy.trans e2)))
    have h1 : ψ (x - 1) = ψ (y - 1) := (hder.toOpenPartialHomeomorph Q).injOn hx hy key
    exact sub_left_inj.1 (ψ.injective h1)

end GlobalTheory.CompanionTheory.RingSqrt
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.RelIndex

theorem relIndex_ne_zero_of_isCompact_of_isOpen :
    ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → H.relIndex A ≠ 0 := by
  intro X _ _ _ A H hA hH _
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hopen : IsOpen ((H.addSubgroupOf A : AddSubgroup A) : Set A) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (A ⧸ H.addSubgroupOf A) :=
    AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact AddSubgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.RelIndex
end
