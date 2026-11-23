module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Algebra.Star.Unitary

@[expose] public section

section

open Metric

namespace GlobalTheory

theorem norm_fderiv_le_of_closedBall_subset {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {U : Set H} {f : H → ℂ} {C r : ℝ} {y : H} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < r) (hy : closedBall y r ⊆ U) (hC : ∀ x ∈ U, ‖f x‖ ≤ C) :
    ‖fderiv ℂ f y‖ ≤ C / r := by
  have hyU : y ∈ U := hy (mem_closedBall_self hr.le)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC y hyU)
  refine ContinuousLinearMap.opNorm_le_bound' _ (div_nonneg hC0 hr.le) fun v hv => ?_
  have hv0 : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have hR : 0 < r / ‖v‖ := div_pos hr hv0
  have hmem : ∀ t ∈ closedBall (0 : ℂ) (r / ‖v‖), y + t • v ∈ U := by
    intro t ht
    apply hy
    rw [mem_closedBall_zero_iff] at ht
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact (le_div_iff₀ hv0).1 ht
  have hlin : ∀ t : ℂ, HasDerivAt (fun s : ℂ => y + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hd : DifferentiableOn ℂ (fun s : ℂ => f (y + s • v)) (closedBall 0 (r / ‖v‖)) := by
    intro t ht
    exact ((hf.differentiableAt (hU.mem_nhds (hmem t ht))).comp t
      (hlin t).differentiableAt).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun s : ℂ => f (y + s • v)) (ball 0 (r / ‖v‖)) :=
    DifferentiableOn.diffContOnCl (by rwa [closure_ball _ hR.ne'])
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc
    (fun z hz => hC _ (hmem z (sphere_subset_closedBall hz)))
  have hder : HasDerivAt (fun s : ℂ => f (y + s • v)) (fderiv ℂ f y v) 0 := by
    have h1 : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
      simpa using (hf.differentiableAt (hU.mem_nhds hyU)).hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hlin 0)
  rw [hder.deriv] at hb
  refine hb.trans (le_of_eq ?_)
  field_simp

theorem differentiableOn_tsum_of_norm_le :
    ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (ι : Type) (U : Set H)
      (f : ι → H → ℂ) (u : ι → ℝ), IsOpen U → (∀ i, DifferentiableOn ℂ (f i) U) → Summable u →
      (∀ i, ∀ x ∈ U, ‖f i x‖ ≤ u i) → DifferentiableOn ℂ (fun x => ∑' i, f i x) U := by
  intro H _ _ ι U f u hU hf hu hb x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : ∀ y ∈ ball x (ε / 2), closedBall y (ε / 2) ⊆ U := by
    intro y hy z hz
    apply hball
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hz
    linarith [dist_triangle z y x]
  have h := hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℂ) (f := f)
    (f' := fun i y => fderiv ℂ (f i) y) (u := fun i => u i / (ε / 2)) (s := ball x (ε / 2))
    (x₀ := x) (x := x) (hu.div_const _) isOpen_ball (convex_ball x _).isPreconnected
    (fun i y hy => ((hf i).differentiableAt
      (hU.mem_nhds (hsub y hy (mem_closedBall_self hr.le)))).hasFDerivAt)
    (fun i y hy => norm_fderiv_le_of_closedBall_subset hU (hf i) hr (hsub y hy) (hb i))
    (mem_ball_self hr) (Summable.of_norm_bounded hu (fun i => hb i x hx)) (mem_ball_self hr)
  exact h.differentiableAt.differentiableWithinAt

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal MatrixOrder Pointwise

namespace GlobalTheory


open scoped MatrixOrder in
theorem exists_det_add_eq_det_mul_det_one_add {n : Type} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hd : P.det ≠ 0) :
    ∃ R : Matrix n n ℂ, R.PosSemidef ∧ (R = 0 → Q = 0) ∧ (P + Q).det = P.det * (1 + R).det := by
  have hP0 : (0 : Matrix n n ℂ) ≤ P := nonneg_iff_posSemidef.mpr hP
  set S := CFC.sqrt P with hSdef
  have hS0 : (0 : Matrix n n ℂ) ≤ S := CFC.sqrt_nonneg P
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP0
  have hSh : Sᴴ = S := (nonneg_iff_posSemidef.mp hS0).1
  have hdS : S.det ≠ 0 := by
    intro h
    apply hd
    rw [← hSS, det_mul, h, zero_mul]
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hdS
  have hl : S * S⁻¹ = 1 := mul_nonsing_inv S hSu
  have hr : S⁻¹ * S = 1 := nonsing_inv_mul S hSu
  have hback : S * (S⁻¹ * Q * S⁻¹) * S = Q := by
    calc S * (S⁻¹ * Q * S⁻¹) * S = (S * S⁻¹) * Q * (S⁻¹ * S) := by
          simp only [Matrix.mul_assoc]
      _ = Q := by rw [hl, hr, Matrix.one_mul, Matrix.mul_one]
  refine ⟨S⁻¹ * Q * S⁻¹, ?_, ?_, ?_⟩
  · have h := hQ.conjTranspose_mul_mul_same S⁻¹
    rwa [conjTranspose_nonsing_inv, hSh] at h
  · intro h
    rw [← hback, h, Matrix.mul_zero, Matrix.zero_mul]
  · have hPQ : P + Q = S * (1 + S⁻¹ * Q * S⁻¹) * S := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, hback]
    rw [hPQ, det_mul, det_mul, ← hSS, det_mul]
    ring

private lemma det_one_add_eq_prod_eigenvalues {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℂ}
    (hR : R.PosSemidef) :
    (1 + R).det = ((∏ i, (1 + hR.1.eigenvalues i) : ℝ) : ℂ) := by
  set U : Matrix n n ℂ := (hR.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hspec : R = U * diagonal (RCLike.ofReal ∘ hR.1.eigenvalues) * star U := by
    conv_lhs => rw [hR.1.spectral_theorem]
    rfl
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hR.1.eigenvectorUnitary.2
  have hdU : U.det * (star U).det = 1 := by rw [← det_mul, hUU, det_one]
  have h1 : 1 + R = U * diagonal (fun i => 1 + (hR.1.eigenvalues i : ℂ)) * star U := by
    have hd1 : diagonal (fun i => 1 + (hR.1.eigenvalues i : ℂ)) =
        1 + diagonal (RCLike.ofReal ∘ hR.1.eigenvalues) := by
      rw [← diagonal_one, diagonal_add]
      rfl
    rw [hd1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, ← hspec]
  rw [h1, det_mul, det_mul, det_diagonal, mul_right_comm, hdU, one_mul]
  push_cast
  rfl

private lemma exists_one_le_det_one_add_of_posSemidef {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℂ}
    (hR : R.PosSemidef) :
    ∃ c : ℝ, (1 + R).det = c ∧ 1 ≤ c ∧ (c ≤ 1 → R = 0) := by
  refine ⟨∏ i, (1 + hR.1.eigenvalues i), det_one_add_eq_prod_eigenvalues hR, ?_, ?_⟩
  · exact Finset.one_le_prod₀ fun i _ => le_add_of_nonneg_right (hR.eigenvalues_nonneg i)
  · intro hc
    apply hR.1.eigenvalues_eq_zero_iff.mp
    funext j
    have hj : 1 + hR.1.eigenvalues j ≤ ∏ i, (1 + hR.1.eigenvalues i) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      exact le_mul_of_one_le_right (by linarith [hR.eigenvalues_nonneg j])
        (Finset.one_le_prod₀ fun i _ => le_add_of_nonneg_right (hR.eigenvalues_nonneg i))
    have := hR.eigenvalues_nonneg j
    simp only [Pi.zero_apply]
    linarith

theorem det_re_mono_of_posSemidef :
    ∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef →
      0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧
        (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0) := by
  intro n _ _ P Q hP hQ
  obtain ⟨hPre, hPim⟩ := Complex.nonneg_iff.mp hP.det_nonneg
  obtain ⟨hSre, -⟩ := Complex.nonneg_iff.mp (hP.add hQ).det_nonneg
  by_cases hd : P.det = 0
  · refine ⟨hPre, ?_, fun h => absurd hd h⟩
    rw [hd, Complex.zero_re]
    exact hSre
  · obtain ⟨R, hR, hR0, hdet⟩ := exists_det_add_eq_det_mul_det_one_add hP hQ hd
    obtain ⟨c, hc, hc1, hcR⟩ := exists_one_le_det_one_add_of_posSemidef hR
    have hre : (P + Q).det.re = P.det.re * c := by
      rw [hdet, hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hpos : 0 < P.det.re := by
      rcases hPre.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext (by rw [← h, Complex.zero_re]) (by rw [← hPim, Complex.zero_im])) hd
    refine ⟨hPre, ?_, fun _ hle => hR0 (hcR ?_)⟩
    · rw [hre]
      exact le_mul_of_one_le_right hPre hc1
    · rw [hre] at hle
      by_contra hlt
      have : P.det.re * 1 < P.det.re * c := mul_lt_mul_of_pos_left (not_le.mp hlt) hpos
      linarith

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory


open scoped Matrix.Norms.L2Operator MatrixOrder in
open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem exists_scalar_sub_posSemidef {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.IsHermitian) :
    ∃ c : ℝ, 1 ≤ c ∧ ((c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - A).PosSemidef := by
  have h1 : (‖A‖ • (1 : Matrix (Fin r) (Fin r) ℂ) - A).PosSemidef := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self (a := A) hA
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact Matrix.le_iff.1 h
  refine ⟨1 + ‖A‖, by linarith [norm_nonneg A], ?_⟩
  have e : ((1 + ‖A‖ : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - A =
      1 + (‖A‖ • (1 : Matrix (Fin r) (Fin r) ℂ) - A) := by
    rw [Complex.coe_smul, add_smul, one_smul, add_sub_assoc]
  rw [e]
  exact Matrix.PosSemidef.one.add h1

theorem gram_det_eq_zero_of_lt_card {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Matrix (Fin r) ι ℂ) (h : r < Fintype.card ι) : (Nᴴ * N).det = 0 := by
  by_contra hd
  have hu : IsUnit (Nᴴ * N) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := (Matrix.rank_mul_le_right Nᴴ N).trans (Matrix.rank_le_card_height N)
  rw [h1, Fintype.card_fin] at h2
  omega

theorem gram_det_mul_le :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0)) → (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) := by
  intro H r a
  obtain ⟨c, hc1, hc⟩ := exists_scalar_sub_posSemidef (aᴴ * a) (Matrix.isHermitian_conjTranspose_mul_self a)
  refine ⟨c ^ r, one_le_pow₀ hc1, ?_⟩
  intro ι _ _ M
  by_cases hι : r < Fintype.card ι
  · rw [gram_det_eq_zero_of_lt_card (a * M) hι, gram_det_eq_zero_of_lt_card M hι]
    simp
  · push Not at hι
    have hP : (Mᴴ * (aᴴ * a) * M).PosSemidef :=
      (Matrix.posSemidef_conjTranspose_mul_self a).conjTranspose_mul_mul_same M
    have hQ : (Mᴴ * ((c : ℂ) • 1 - aᴴ * a) * M).PosSemidef := hc.conjTranspose_mul_mul_same M
    obtain ⟨-, hle, -⟩ := H ι _ _ hP hQ
    have hM0 : 0 ≤ (Mᴴ * M).det.re :=
      (H ι _ _ (Matrix.posSemidef_conjTranspose_mul_self M) (Matrix.posSemidef_conjTranspose_mul_self M)).1
    have e1 : (a * M)ᴴ * (a * M) = Mᴴ * (aᴴ * a) * M := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have e2 : Mᴴ * (aᴴ * a) * M + Mᴴ * ((c : ℂ) • 1 - aᴴ * a) * M = (c : ℂ) • (Mᴴ * M) := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [e1]
    refine hle.trans ?_
    rw [e2, Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 hι) hM0

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem driftWeight_sq_le (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (r i j : ℕ) (hj : 0 < j) (hji : j ≤ i)
    (hr : i + j ≤ r) :
    (ε ^ (i * (r - i))) ^ 2 ≤
      ε ^ 2 * (ε ^ ((i - j) * (r - (i - j))) * ε ^ ((i + j) * (r - (i + j)))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hji
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  have e1 : j + m + j + k - (j + m) = j + k := by omega
  have e2 : j + m - j = m := by omega
  have e3 : j + m + j + k - m = j + j + k := by omega
  have e4 : j + m + j + k - (j + m + j) = k := by omega
  rw [e1, e2, e3, e4, ← pow_add, ← pow_add, ← pow_mul]
  apply pow_le_pow_of_le_one h0 h1
  nlinarith [Nat.mul_le_mul hj hj]

theorem mul_sqrt_le_of_weights (x e₁ e₂ ε u v M : ℝ) (hx : 0 ≤ x) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (hε : 0 ≤ ε) (hu : 0 ≤ u) (hv : 0 ≤ v) (h : x ^ 2 ≤ ε ^ 2 * (e₁ * e₂))
    (h₁ : e₁ * u ≤ M) (h₂ : e₂ * v ≤ M) : x * Real.sqrt (u * v) ≤ ε * M := by
  have hM : 0 ≤ M := le_trans (mul_nonneg he₁ hu) h₁
  have hs0 := Real.sqrt_nonneg (u * v)
  have k3 : (x * Real.sqrt (u * v)) ^ 2 ≤ (ε * M) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hu hv)]
    calc x ^ 2 * (u * v) ≤ ε ^ 2 * (e₁ * e₂) * (u * v) :=
          mul_le_mul_of_nonneg_right h (mul_nonneg hu hv)
      _ = ε ^ 2 * ((e₁ * u) * (e₂ * v)) := by ring
      _ ≤ ε ^ 2 * (M * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ (mul_nonneg he₂ hv) hM) (sq_nonneg ε)
      _ = (ε * M) ^ 2 := by ring
  nlinarith [mul_nonneg hx hs0, mul_nonneg hε hM]

theorem weighted_sum_drift_inequality : (∀ (Y σ : Type) [Fintype σ] (r : ℕ) (t : σ → Y → Y) (α : ℕ → Y → ℝ) (c C B : ℝ), 0 ≤ c → c < 1 → 0 ≤ C → (∀ i ≤ r, ∀ y, 0 ≤ α i y) → (∀ y, α 0 y ≤ B ∧ α r y ≤ B) → (∀ (y : Y) (i : ℕ), 0 < i → i < r → (∑ s, α i (t s y) ≤ Fintype.card σ * (c * α i y)) ∨ ∃ j : ℕ, 0 < j ∧ j ≤ i ∧ i + j ≤ r ∧ ∀ s, α i (t s y) ≤ C * Real.sqrt (α (i - j) y * α (i + j) y)) → ∃ (e : ℕ → ℝ) (c' b : ℝ), (∀ i, 0 < e i) ∧ 0 ≤ c' ∧ c' < 1 ∧ 0 ≤ b ∧ ∀ y, ∑ s, (∑ i ∈ Finset.Ioo 0 r, e i * α i (t s y)) ≤ Fintype.card σ * (c' * (∑ i ∈ Finset.Ioo 0 r, e i * α i y) + b)) := by
  intro Y σ _ r t α c C B hc0 hc1 hC hα hB halt
  have hrC : 0 ≤ (r : ℝ) * C := mul_nonneg (Nat.cast_nonneg r) hC
  obtain ⟨ε, hε0, hε1, hkey⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ (r : ℝ) * C * ε < 1 - c := by
    have hden : 0 < 2 * ((r : ℝ) * C + 1) := by linarith
    refine ⟨(1 - c) / (2 * ((r : ℝ) * C + 1)), div_pos (by linarith) hden, ?_, ?_⟩
    · rw [div_le_one hden]
      linarith
    · have hεe : (1 - c) / (2 * ((r : ℝ) * C + 1)) * (2 * ((r : ℝ) * C + 1)) = 1 - c :=
        div_mul_cancel₀ _ hden.ne'
      have hpos : 0 < (1 - c) / (2 * ((r : ℝ) * C + 1)) := div_pos (by linarith) hden
      nlinarith [mul_nonneg hrC hpos.le]
  refine ⟨fun i => ε ^ (i * (r - i)), c + (r : ℝ) * C * ε, 2 * (r : ℝ) * C * ε * max B 0,
    fun i => pow_pos hε0 _, add_nonneg hc0 (mul_nonneg hrC hε0.le), by linarith,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg r)) hC) hε0.le)
      (le_max_right _ _), ?_⟩
  intro y
  dsimp only
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = ∑ i ∈ Finset.Ioo 0 r, ε ^ (i * (r - i)) * α i y := ⟨_, rfl⟩
  have hΦ0 : 0 ≤ Φ := by
    rw [hΦ]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (pow_nonneg hε0.le _) (hα i (Finset.mem_Ioo.1 hi).2.le y)
  have hB0 : 0 ≤ B := le_trans (hα 0 (Nat.zero_le _) y) (hB y).1
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Φ + 2 * B := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; linarith
  have hbd : ∀ k ≤ r, ε ^ (k * (r - k)) * α k y ≤ M := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, zero_mul, pow_zero, one_mul]
      linarith [(hB y).1]
    rcases eq_or_lt_of_le hk with hkr | hkr
    · rw [hkr, Nat.sub_self, mul_zero, pow_zero, one_mul]
      linarith [(hB y).2]
    · have h1 : ε ^ (k * (r - k)) * α k y ≤ Φ := by
        rw [hΦ]
        exact Finset.single_le_sum (f := fun i => ε ^ (i * (r - i)) * α i y)
          (fun i hi => mul_nonneg (pow_nonneg hε0.le _) (hα i (Finset.mem_Ioo.1 hi).2.le y))
          (Finset.mem_Ioo.2 ⟨hk0, hkr⟩)
      linarith
  have hterm : ∀ i ∈ Finset.Ioo 0 r, ∑ s, ε ^ (i * (r - i)) * α i (t s y) ≤
      (Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) + (Fintype.card σ : ℝ) * (C * ε * M) := by
    intro i hi
    obtain ⟨hi0, hir⟩ := Finset.mem_Ioo.1 hi
    have hA : 0 ≤ (Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc0 (mul_nonneg (pow_nonneg hε0.le _) (hα i hir.le y)))
    have hB' : 0 ≤ (Fintype.card σ : ℝ) * (C * ε * M) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hC hε0.le) hM0)
    rcases halt y i hi0 hir with hcon | ⟨j, hj0, hji, hjr, hint⟩
    · rw [← Finset.mul_sum]
      calc ε ^ (i * (r - i)) * ∑ s, α i (t s y)
          ≤ ε ^ (i * (r - i)) * ((Fintype.card σ : ℝ) * (c * α i y)) :=
            mul_le_mul_of_nonneg_left hcon (pow_nonneg hε0.le _)
        _ = (Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) := by ring
        _ ≤ _ := le_add_of_nonneg_right hB'
    · have hs : ∀ s, ε ^ (i * (r - i)) * α i (t s y) ≤ C * ε * M := by
        intro s
        have h1 := driftWeight_sq_le ε hε0.le hε1 r i j hj0 hji hjr
        have h2 := mul_sqrt_le_of_weights (ε ^ (i * (r - i))) (ε ^ ((i - j) * (r - (i - j))))
          (ε ^ ((i + j) * (r - (i + j)))) ε (α (i - j) y) (α (i + j) y) M (pow_nonneg hε0.le _)
          (pow_nonneg hε0.le _) (pow_nonneg hε0.le _) hε0.le (hα _ (by omega) y) (hα _ hjr y) h1
          (hbd _ (by omega)) (hbd _ hjr)
        calc ε ^ (i * (r - i)) * α i (t s y)
            ≤ ε ^ (i * (r - i)) * (C * Real.sqrt (α (i - j) y * α (i + j) y)) :=
              mul_le_mul_of_nonneg_left (hint s) (pow_nonneg hε0.le _)
          _ = C * (ε ^ (i * (r - i)) * Real.sqrt (α (i - j) y * α (i + j) y)) := by ring
          _ ≤ C * (ε * M) := mul_le_mul_of_nonneg_left h2 hC
          _ = C * ε * M := by ring
      calc ∑ s, ε ^ (i * (r - i)) * α i (t s y) ≤ ∑ _s : σ, C * ε * M :=
            Finset.sum_le_sum fun s _ => hs s
        _ = (Fintype.card σ : ℝ) * (C * ε * M) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ _ := le_add_of_nonneg_left hA
  have hcard : ((Finset.Ioo 0 r).card : ℝ) ≤ r := by
    exact_mod_cast (by rw [Nat.card_Ioo]; omega)
  rw [Finset.sum_comm]
  calc ∑ i ∈ Finset.Ioo 0 r, ∑ s, ε ^ (i * (r - i)) * α i (t s y)
      ≤ ∑ i ∈ Finset.Ioo 0 r, ((Fintype.card σ : ℝ) * (c * (ε ^ (i * (r - i)) * α i y)) +
          (Fintype.card σ : ℝ) * (C * ε * M)) := Finset.sum_le_sum hterm
    _ = (Fintype.card σ : ℝ) * (c * Φ) + ((Finset.Ioo 0 r).card : ℝ) * ((Fintype.card σ : ℝ) * (C * ε * M)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, hΦ]
    _ ≤ (Fintype.card σ : ℝ) * (c * Φ) + (r : ℝ) * ((Fintype.card σ : ℝ) * (C * ε * M)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hC hε0.le) hM0)))
    _ = (Fintype.card σ : ℝ) * ((c + (r : ℝ) * C * ε) * Φ + 2 * (r : ℝ) * C * ε * max B 0) := by
        rw [max_eq_left hB0, hM]
        ring
    _ = _ := by rw [hΦ]

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem rpow_neg_le_one_sub_log_add_sq {ω δ t : ℝ} (hω : 1 ≤ ω) (hδ : 0 < δ)
    (hδL : δ * Real.log ω ≤ 1) (h1 : ω⁻¹ ≤ t) (h2 : t ≤ ω) :
    t ^ (-δ) ≤ 1 - δ * Real.log t + (δ * Real.log ω) ^ 2 := by
  have hω0 : 0 < ω := by linarith
  have ht : 0 < t := lt_of_lt_of_le (inv_pos.mpr hω0) h1
  have hu : Real.log t ≤ Real.log ω := Real.log_le_log ht h2
  have hl : -Real.log ω ≤ Real.log t := by
    rw [← Real.log_inv]; exact Real.log_le_log (inv_pos.mpr hω0) h1
  have habs : |Real.log t * (-δ)| ≤ δ * Real.log ω := by
    rw [abs_le]; constructor <;> nlinarith
  have h := Real.abs_exp_sub_one_sub_id_le (habs.trans hδL)
  have h' := (abs_le.mp h).2
  have hsq : (Real.log t * (-δ)) ^ 2 ≤ (δ * Real.log ω) ^ 2 := by
    rw [← sq_abs (Real.log t * (-δ))]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [Real.rpow_def_of_pos ht]
  linarith

theorem exists_rpow_neg_sum_le_of_sum_log :
    (∀ (N : ℕ) (ω η : ℝ), 1 ≤ ω → 0 < η → ∃ δ c : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ ∀ (σ : Type) (S : Finset σ) (t : σ → ℝ), S.card = N → (∀ s ∈ S, ω⁻¹ ≤ t s ∧ t s ≤ ω) → η ≤ ∑ s ∈ S, Real.log (t s) → ∑ s ∈ S, t s ^ (-δ) ≤ N * c) := by
  intro N ω η hω hη
  have hL : 0 ≤ Real.log ω := Real.log_nonneg hω
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  obtain ⟨δ, hδ, hδL, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * Real.log ω ≤ 1 ∧
      δ * (N * Real.log ω ^ 2) ≤ η / 2 := by
    refine ⟨min (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1)),
      lt_min (by positivity) (by positivity), ?_, ?_⟩
    · have h := min_le_left (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1))
      have hp : 0 < min (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1)) :=
        lt_min (by positivity) (by positivity)
      rw [le_div_iff₀ (by positivity)] at h
      nlinarith
    · have h := min_le_right (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1))
      have hp : 0 < min (1 / (Real.log ω + 1)) (η / 2 / (N * Real.log ω ^ 2 + 1)) :=
        lt_min (by positivity) (by positivity)
      rw [le_div_iff₀ (by positivity)] at h
      nlinarith
  have he : 0 < δ * η / (2 * (N + 1)) := by positivity
  refine ⟨δ, max 0 (1 - δ * η / (2 * (N + 1))), hδ, le_max_left _ _,
    max_lt one_pos (by linarith), ?_⟩
  intro σ S t hS ht hsum
  have h1 : ∑ s ∈ S, t s ^ (-δ) ≤
      ∑ s ∈ S, (1 - δ * Real.log (t s) + (δ * Real.log ω) ^ 2) :=
    Finset.sum_le_sum fun s hs =>
      rpow_neg_le_one_sub_log_add_sq hω hδ hδL (ht s hs).1 (ht s hs).2
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
  simp only [Finset.sum_const, hS, nsmul_eq_mul, mul_one] at h1
  have h2 : δ * η ≤ δ * ∑ s ∈ S, Real.log (t s) := mul_le_mul_of_nonneg_left hsum hδ.le
  have h3 : δ * (δ * (N * Real.log ω ^ 2)) ≤ δ * (η / 2) := mul_le_mul_of_nonneg_left hδη hδ.le
  have h4 : (N : ℝ) * (1 - δ * η / (2 * (N + 1))) ≤ N * max 0 (1 - δ * η / (2 * (N + 1))) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hN
  have h5 : (N + 1 : ℝ) * (δ * η / (2 * (N + 1))) = δ * η / 2 := by field_simp
  nlinarith

end GlobalTheory
end
