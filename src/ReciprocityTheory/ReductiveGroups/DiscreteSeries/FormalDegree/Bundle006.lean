module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

theorem sum_castLE_eq_sum_ite_lt_formal_degree {M : Type*} [AddCommMonoid M] {n i : ℕ} (hi : i ≤ n) (g : Fin n → M) :
    ∑ a : Fin i, g (Fin.castLE hi a) = ∑ a : Fin n, if (a : ℕ) < i then g a else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => Fin.castLE hi a) ?_ ?_ ?_ ?_
  · intro a _
    simp [Finset.mem_filter]
  · intro a _ b _ h
    exact Fin.castLE_injective hi h
  · intro b hb
    exact ⟨⟨b, (Finset.mem_filter.1 hb).2⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro a _
    rfl

theorem prod_orderEmbOfFin {R : Type*} [CommMonoid R] {n i : ℕ} (S : Finset (Fin n)) (h : S.card = i)
    (d : Fin n → R) : ∏ k : Fin i, d (S.orderEmbOfFin h k) = ∏ s ∈ S, d s := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S h, Finset.prod_map]
  rfl

theorem leading_minor_conj_diagonal {R : Type*} [CommRing R] (f : ℂ →+* R) {n i : ℕ} (hi : i ≤ n)
    (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → R) :
    ((U.map f * diagonal d * (Uᴴ).map f).submatrix (Fin.castLE hi) (Fin.castLE hi)).det =
      ∑ S : {S : Finset (Fin n) // S.card = i},
        f ((U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2)).det *
          star (U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2)).det) * ∏ s ∈ S.1, d s := by
  have hsplit : (U.map f * diagonal d * (Uᴴ).map f).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      ((U.map f).submatrix (Fin.castLE hi) id * diagonal d) * ((Uᴴ).map f).submatrix id (Fin.castLE hi) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
  have hdet : ∀ M : Matrix (Fin i) (Fin i) ℂ, (M.map f).det = f M.det :=
    fun M => (RingHom.map_det f M).symm
  rw [hsplit, cauchyBinet]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hA : ((U.map f).submatrix (Fin.castLE hi) id * diagonal d).submatrix id (S.1.orderEmbOfFin S.2) =
      (U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2)).map f *
        diagonal (fun k => d (S.1.orderEmbOfFin S.2 k)) := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.map_apply]
  have hB : (((Uᴴ).map f).submatrix id (Fin.castLE hi)).submatrix (S.1.orderEmbOfFin S.2) id =
      ((U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2))ᴴ).map f := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [hA, hB, Matrix.det_mul, Matrix.det_diagonal, hdet, hdet, Matrix.det_conjTranspose,
    prod_orderEmbOfFin S.1 S.2 d, map_mul]
  ring

open Polynomial in
theorem coeff_prod_one_add_low {ι : Type*} [DecidableEq ι] (S : Finset ι) (v : ι → ℂ) :
    (∏ s ∈ S, (1 + X * C (v s))).coeff 0 = 1 ∧ (∏ s ∈ S, (1 + X * C (v s))).coeff 1 = ∑ s ∈ S, v s ∧
    2 * (∏ s ∈ S, (1 + X * C (v s))).coeff 2 = (∑ s ∈ S, v s) ^ 2 - ∑ s ∈ S, v s ^ 2 := by
  refine Finset.induction_on S ?_ ?_
  · simp [Polynomial.coeff_one]
  · intro a S ha ih
    obtain ⟨h0, h1, h2⟩ := ih
    have e : ∀ P : ℂ[X], (1 + X * C (v a)) * P = P + X * (C (v a) * P) := fun P => by ring
    rw [Finset.prod_insert ha, e, Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, ?_, ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, h0, add_zero]
    · rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, h1, h0]
      ring
    · rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, mul_add, h2, h1]
      ring

open Polynomial in
theorem conj_polynomial_diagonal {m : ℕ} (V : Matrix (Fin m) (Fin m) ℂ) (hV : V * Vᴴ = 1) (ν : Fin m → ℂ) :
    V.map C * diagonal (fun s => 1 + X * C (ν s)) * (Vᴴ).map C =
      1 + (X : ℂ[X]) • (V * diagonal ν * Vᴴ).map C := by
  have hD : diagonal (fun s => 1 + X * C (ν s)) = 1 + (X : ℂ[X]) • (diagonal ν).map C := by
    ext a b
    by_cases h : a = b
    · subst h
      simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  rw [hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hV,
    Matrix.map_one _ (map_zero C) (map_one C)]

theorem trace_conj_eq_trace_of_conjTranspose_mul_self {m : ℕ} (V D : Matrix (Fin m) (Fin m) ℂ) (hV : Vᴴ * V = 1) :
    trace (V * D * Vᴴ) = trace D := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

theorem sq_conj_diagonal {m : ℕ} (V : Matrix (Fin m) (Fin m) ℂ) (ν : Fin m → ℂ) (hV : Vᴴ * V = 1) :
    V * diagonal ν * Vᴴ * (V * diagonal ν * Vᴴ) = V * diagonal (fun s => ν s ^ 2) * Vᴴ := by
  calc V * diagonal ν * Vᴴ * (V * diagonal ν * Vᴴ) = V * diagonal ν * (Vᴴ * V) * diagonal ν * Vᴴ := by
        simp only [Matrix.mul_assoc]
    _ = V * diagonal (fun s => ν s ^ 2) * Vᴴ := by
        rw [hV, Matrix.mul_one, Matrix.mul_assoc V, Matrix.diagonal_mul_diagonal]
        simp [sq]

open Polynomial in
theorem coeff_two_det_hermitian {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.IsHermitian) :
    2 * (det (1 + (X : ℂ[X]) • A.map C)).coeff 2 = (trace A) ^ 2 - trace (A * A) := by
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
  set ν : Fin m → ℂ := fun s => ((hA.eigenvalues s : ℝ) : ℂ) with hν
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.prop
  have hUU' : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.prop
  have hAeq : A = U * diagonal ν * Uᴴ := hA.spectral_theorem
  have hconj := conj_polynomial_diagonal U hUU ν
  have hdU : (U.map C).det * ((Uᴴ).map C).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero C) (map_one C), Matrix.det_one]
  have hdet : (1 + (X : ℂ[X]) • (U * diagonal ν * Uᴴ).map C).det = ∏ s, (1 + X * C (ν s)) := by
    rw [← hconj, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm ((U.map C).det), mul_assoc,
      hdU, mul_one]
  rw [hAeq, hdet, (coeff_prod_one_add_low Finset.univ ν).2.2, sq_conj_diagonal U ν hUU', trace_conj_eq_trace_of_conjTranspose_mul_self U _ hUU',
    trace_conj_eq_trace_of_conjTranspose_mul_self U _ hUU', Matrix.trace_diagonal, Matrix.trace_diagonal]

theorem trace_leading_submatrix {n i : ℕ} (hi : i ≤ n) (M : Matrix (Fin n) (Fin n) ℂ) :
    trace (M.submatrix (Fin.castLE hi) (Fin.castLE hi)) = ∑ a : Fin n, if (a : ℕ) < i then M a a else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact sum_castLE_eq_sum_ite_lt_formal_degree hi (fun a => M a a)

theorem variance_eq_trace_diff {n i : ℕ} (hi : i ≤ n) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
    ((Vi M i : ℝ) : ℂ) = trace ((M * M).submatrix (Fin.castLE hi) (Fin.castLE hi)) -
      trace (M.submatrix (Fin.castLE hi) (Fin.castLE hi) * M.submatrix (Fin.castLE hi) (Fin.castLE hi)) := by
  have hMab : ∀ a b, M a b * M b a = (‖M b a‖ : ℂ) ^ 2 := by
    intro a b
    rw [← hM.apply a b]
    exact Complex.conj_mul' (M b a)
  have h1 : trace ((M * M).submatrix (Fin.castLE hi) (Fin.castLE hi)) =
      ∑ a : Fin n, if (a : ℕ) < i then ∑ b : Fin n, M a b * M b a else 0 := by
    rw [trace_leading_submatrix hi]
    simp only [Matrix.mul_apply]
  have inner : ∀ a : Fin n, ∑ b : Fin i, M a (Fin.castLE hi b) * M (Fin.castLE hi b) a =
      ∑ b : Fin n, if (b : ℕ) < i then M a b * M b a else 0 :=
    fun a => sum_castLE_eq_sum_ite_lt_formal_degree hi (fun b => M a b * M b a)
  have h2 : trace (M.submatrix (Fin.castLE hi) (Fin.castLE hi) * M.submatrix (Fin.castLE hi) (Fin.castLE hi)) =
      ∑ a : Fin n, if (a : ℕ) < i then
        ∑ b : Fin n, (if (b : ℕ) < i then M a b * M b a else 0) else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.submatrix_apply]
    calc ∑ a : Fin i, ∑ b : Fin i, M (Fin.castLE hi a) (Fin.castLE hi b) * M (Fin.castLE hi b) (Fin.castLE hi a)
        = ∑ a : Fin i, (fun a' : Fin n => ∑ b : Fin n, if (b : ℕ) < i then M a' b * M b a' else 0)
            (Fin.castLE hi a) := Finset.sum_congr rfl fun a _ => inner _
      _ = _ := sum_castLE_eq_sum_ite_lt_formal_degree hi (fun a' : Fin n => ∑ b : Fin n, if (b : ℕ) < i then M a' b * M b a' else 0)
  rw [h1, h2, ← Finset.sum_sub_distrib]
  simp only [Vi, Complex.ofReal_sum, apply_ite Complex.ofReal, Complex.ofReal_zero, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : (a : ℕ) < i
  · rw [if_pos ha, if_pos ha, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : (b : ℕ) < i
    · rw [if_pos hb, sub_self, if_neg (by omega)]
    · rw [if_neg hb, sub_zero, if_pos (by omega), hMab]
  · rw [if_neg ha, if_neg ha, sub_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg (by omega)]

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def volU (M : ℕ) : ℝ := ∏ i ∈ range M, 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)

theorem volU_eq_pow_div (M : ℕ) : volU M = 2 ^ M * Real.pi ^ (∑ i ∈ range M, (i + 1)) /
    ∏ i ∈ range M, (i.factorial : ℝ) := by
  rw [volU, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Finset.prod_pow_eq_pow_sum]

theorem volU_sum_succ_add (p q : ℕ) : ∑ i ∈ range (p + q), (i + 1) =
    ∑ i ∈ range p, (i + 1) + ∑ i ∈ range q, (i + 1) + p * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← Nat.add_assoc, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

theorem volU_factProd_pos (M : ℕ) : (0 : ℝ) < ∏ i ∈ range M, (i.factorial : ℝ) := Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos i)

theorem volU_ratio (p q m : ℕ) (h : p + q = m) :
    volU p * volU q / volU m = (∏ i ∈ range m, (i.factorial : ℝ)) /
      (Real.pi ^ (p * q) * (∏ i ∈ range p, (i.factorial : ℝ)) *
        ∏ i ∈ range q, (i.factorial : ℝ)) := by
  subst h
  have hp := volU_factProd_pos p
  have hq := volU_factProd_pos q
  have hn := volU_factProd_pos (p + q)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [volU_eq_pow_div, volU_eq_pow_div, volU_eq_pow_div, volU_sum_succ_add]
  simp only [pow_add]
  field_simp

theorem volU_factProd_mul_le (p q : ℕ) :
    (∏ i ∈ range p, i.factorial) * (∏ i ∈ range q, i.factorial) ≤
      ∏ i ∈ range (p + q), i.factorial := by
  rw [Finset.prod_range_add]
  exact Nat.mul_le_mul le_rfl
    (Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i _ => Nat.factorial_le (by omega)))

theorem volU_pOf_add_qOf (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  unfold pOf qOf
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have hone : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem cPQ_eq_volU (ε : Fin n → Bool) : cPQ ε = volU (pOf ε) * volU (qOf ε) / volU n := by
  rw [volU_ratio _ _ _ (volU_pOf_add_qOf ε)]
  rfl

theorem inv_pi_pow_le_cPQ (ε : Fin n → Bool) : (Real.pi ^ (pOf ε * qOf ε))⁻¹ ≤ cPQ ε := by
  have hle := volU_factProd_mul_le (pOf ε) (qOf ε)
  rw [volU_pOf_add_qOf ε] at hle
  have hle' : (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) ≤
      ∏ i ∈ range n, (i.factorial : ℝ) := by
    exact_mod_cast hle
  have hp := volU_factProd_pos (pOf ε)
  have hq := volU_factProd_pos (qOf ε)
  have hpi : 0 < Real.pi ^ (pOf ε * qOf ε) := pow_pos Real.pi_pos _
  have hD : 0 < Real.pi ^ (pOf ε * qOf ε) * (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) *
      ∏ i ∈ range (qOf ε), (i.factorial : ℝ) := mul_pos (mul_pos hpi hp) hq
  unfold cPQ
  rw [le_div_iff₀ hD]
  have he : (Real.pi ^ (pOf ε * qOf ε))⁻¹ * (Real.pi ^ (pOf ε * qOf ε) *
      (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ)) =
      (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) := by
    rw [mul_assoc, inv_mul_cancel_left₀ hpi.ne']
  linarith

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdU_integral_exp_norm {c : ℝ} (hc : 0 < c) :
    ∫ x : ℂ, Real.exp (-c * ‖x‖) = Real.pi * c ^ (-2 : ℝ) * Real.Gamma 3 := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 1) le_rfl hc
  have e1 : (-2 / (1 : ℝ)) = -2 := by norm_num
  have e2 : (2 / (1 : ℝ) + 1) = 3 := by norm_num
  simp only [Real.rpow_one, e1, e2] at h
  exact h

theorem fdU_integrable_exp_norm {c : ℝ} (hc : 0 < c) : Integrable (fun x : ℂ => Real.exp (-c * ‖x‖)) := by
  apply Integrable.of_integral_ne_zero
  rw [fdU_integral_exp_norm hc]
  exact (mul_pos (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hc _))
    (Real.Gamma_pos_of_pos (by norm_num))).ne'

theorem fdU_integral_gauss {b : ℝ} (hb : 0 < b) : ∫ x : ℂ, Real.exp (-b * ‖x‖ ^ 2) = Real.pi / b := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 2) (by norm_num) hb
  have e1 : (-2 / (2 : ℝ)) = -1 := by norm_num
  have e2 : (2 / (2 : ℝ) + 1) = 2 := by norm_num
  simp only [Real.rpow_two, e1, e2, Real.rpow_neg_one, Real.Gamma_two, mul_one] at h
  rw [h, div_eq_mul_inv]

theorem fdU_integrable_gauss {b : ℝ} (hb : 0 < b) : Integrable (fun x : ℂ => Real.exp (-b * ‖x‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [fdU_integral_gauss hb]
  exact (div_pos Real.pi_pos hb).ne'

theorem fdU_wab_zero_pos {ε : Fin n → Bool} (ab : PCoord ε) : 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by
  have h : ((ab.1.2 : ℕ) : ℝ) < ((ab.1.1 : ℕ) : ℝ) := by exact_mod_cast ab.2.1
  simp only [wab, Pi.zero_apply]
  linarith

theorem exp_neg_quadratic_eq_prod {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Real.exp (-Qf (0 : Fin n → ℝ) y) =
      ∏ ab : PCoord ε, Real.exp (-wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖y ab‖ ^ 2) := by
  simp only [Qf, ← Finset.sum_neg_distrib, Real.exp_sum, neg_mul]

theorem fdU_integrable_prod_gauss {ε : Fin n → Bool} (b : PCoord ε → ℝ) (hb : ∀ ab, 0 < b ab) :
    Integrable (fun y : PCoord ε → ℂ => ∏ ab : PCoord ε, Real.exp (-b ab * ‖y ab‖ ^ 2)) := by
  exact Integrable.fintype_prod
    (f := fun ab (x : ℂ) => Real.exp (-b ab * ‖x‖ ^ 2)) (fun ab => fdU_integrable_gauss (hb ab))

theorem fdU_integral_prod_gauss {ε : Fin n → Bool} (b : PCoord ε → ℝ) (hb : ∀ ab, 0 < b ab) :
    ∫ y : PCoord ε → ℂ, ∏ ab : PCoord ε, Real.exp (-b ab * ‖y ab‖ ^ 2) = ∏ ab : PCoord ε, Real.pi / b ab := by
  exact (integral_fintype_prod_eq_prod
    (fun (ab : PCoord ε) (x : ℂ) => Real.exp (-b ab * ‖x‖ ^ 2))).trans
    (Finset.prod_congr rfl fun ab _ => fdU_integral_gauss (hb ab))

theorem fdU_lintegral_gauss (ε : Fin n → Bool) :
    ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) = ENNReal.ofReal (PiW ε 0) := by
  have hb : ∀ ab : PCoord ε, 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 :=
    fun ab => fdU_wab_zero_pos ab
  have hint : Integrable (fun y : PCoord ε → ℂ => Real.exp (-Qf (0 : Fin n → ℝ) y)) := by
    simp_rw [exp_neg_quadratic_eq_prod]
    exact fdU_integrable_prod_gauss _ hb
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le)]
  congr 1
  simp_rw [exp_neg_quadratic_eq_prod]
  rw [fdU_integral_prod_gauss _ hb]
  rfl

theorem fdU_integrable_prod_exp {ε : Fin n → Bool} {c : ℝ} (hc : ∀ _ : PCoord ε, 0 < c) :
    Integrable (fun y : PCoord ε → ℂ => ∏ ab : PCoord ε, Real.exp (-c * ‖y ab‖)) := by
  exact Integrable.fintype_prod
    (f := fun _ (x : ℂ) => Real.exp (-c * ‖x‖)) (fun ab => fdU_integrable_exp_norm (hc ab))

end ReciprocityTheory.ChartRestriction.DS
end
end
