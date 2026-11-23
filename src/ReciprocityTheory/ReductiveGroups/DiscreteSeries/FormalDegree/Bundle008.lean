module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PSpecB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle005

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def wS {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n)
    (S : {S : Finset (Fin n) // S.card = i}) : ℝ :=
  ‖(((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi)
    (S.1.orderEmbOfFin S.2)).det‖ ^ 2

def yS {ε : Fin n → Bool} (z : PCoord ε → ℂ) (S : Finset (Fin n)) : ℝ := ∑ s ∈ S, pev z s

theorem minor_weight_cast {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n)
    (S : {S : Finset (Fin n) // S.card = i}) :
    ((wS z hi S : ℝ) : ℂ) =
      (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi)
        (S.1.orderEmbOfFin S.2)).det *
      star (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi)
        (S.1.orderEmbOfFin S.2)).det := by
  rw [wS, Complex.ofReal_pow, Complex.star_def, Complex.mul_conj']

theorem pmat_eq_eigenvectorUnitary_conj_diagonal_pev {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    pmat z = ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagonal (fun s => ((pev z s : ℝ) : ℂ)) *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  have hu : ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem (pmat_isHermitian z).eigenvectorUnitary.2
  calc pmat z = pmat z * (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ) := by rw [hu, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, pmat_mul_evU]

theorem pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 ∧
    ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have hU := (pmat_isHermitian z).eigenvectorUnitary.2
  exact ⟨Unitary.mul_star_self_of_mem hU, Unitary.star_mul_self_of_mem hU⟩

theorem matrix_map_id (M : Matrix (Fin n) (Fin n) ℂ) : M.map (RingHom.id ℂ) = M := by
  ext a b
  rfl

theorem leading_minor_sum_weights {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (d : Fin n → ℂ) :
    Del (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal d *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ) i =
      ∑ S, ((wS z hi S : ℝ) : ℂ) * ∏ s ∈ S.1, d s := by
  unfold Del
  rw [dite_eq_left hi]
  have h := leading_minor_conj_diagonal (RingHom.id ℂ) hi ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) d
  rw [matrix_map_id, matrix_map_id] at h
  rw [h]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [minor_weight_cast z hi S]
  rfl

theorem lemma3a {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (t : ℝ) :
    Del (NormedSpace.exp ((t : ℂ) • pmat z)) i =
      ∑ S, ((wS z hi S : ℝ) : ℂ) * Complex.exp ((t * yS z S.1 : ℝ) : ℂ) := by
  have hu := (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).1
  have hUu : IsUnit ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := isUnit_iff_exists.mpr ⟨_, hu, (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).2⟩
  have hsm : (t : ℂ) • pmat z = ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun s => ((t * pev z s : ℝ) : ℂ)) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)⁻¹ := by
    rw [Matrix.inv_eq_right_inv hu]
    conv_lhs => rw [pmat_eq_eigenvectorUnitary_conj_diagonal_pev z]
    have hd : diagonal (fun s => ((t * pev z s : ℝ) : ℂ)) =
        (t : ℂ) • diagonal (fun s => ((pev z s : ℝ) : ℂ)) := by
      ext a b
      by_cases h : a = b <;> simp [h]
    rw [hd, mul_smul_comm, smul_mul_assoc]
  have hexp : NormedSpace.exp ((t : ℂ) • pmat z) =
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun s => Complex.exp ((t * pev z s : ℝ) : ℂ)) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
    rw [hsm, Matrix.exp_conj _ _ hUu, Matrix.exp_diagonal, Matrix.inv_eq_right_inv hu]
    congr 1
    congr 1
    congr 1
    rw [Pi.exp_def]
    funext s
    simp only [Complex.exp_eq_exp_ℂ]
  rw [hexp, leading_minor_sum_weights z hi]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← Complex.exp_sum]
  congr 2
  simp [yS, Finset.mul_sum]

theorem lemma3b {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) : ∑ S, wS z hi S = 1 := by
  have h := leading_minor_sum_weights z hi (fun _ => (1 : ℂ))
  simp only [Matrix.diagonal_one, (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).1, Finset.prod_const_one, mul_one] at h
  have h1 : Del (1 : Matrix (Fin n) (Fin n) ℂ) i = 1 := by
    unfold Del
    rw [dite_eq_left hi, Matrix.submatrix_one _ (Fin.castLE_injective hi), Matrix.det_one]
  exact_mod_cast h.symm.trans h1

open Polynomial in
theorem sum_weights_coeff_eq_det {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (μ : Fin n → ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal μ *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = M) (k : ℕ) :
    ∑ S, ((wS z hi S : ℝ) : ℂ) * (∏ s ∈ S.1, (1 + X * C (μ s))).coeff k =
      (det (1 + (X : ℂ[X]) • (M.submatrix (Fin.castLE hi) (Fin.castLE hi)).map C)).coeff k := by
  have hL := leading_minor_conj_diagonal (Polynomial.C : ℂ →+* ℂ[X]) hi ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) (fun s => 1 + X * C (μ s))
  rw [conj_polynomial_diagonal _ (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).1 μ, hM] at hL
  have hsub : (1 + (X : ℂ[X]) • M.map C).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      1 + (X : ℂ[X]) • (M.submatrix (Fin.castLE hi) (Fin.castLE hi)).map C := by
    ext a b
    simp [Matrix.one_apply, (Fin.castLE_injective hi).eq_iff]
  rw [hsub] at hL
  rw [hL, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← minor_weight_cast z hi S, Polynomial.coeff_C_mul]

theorem trace_leading_submatrix_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    trace ((pmat z).submatrix (Fin.castLE hi) (Fin.castLE hi)) = 0 := by
  rw [trace_leading_submatrix]
  simp [pmat_diag_zero]


open Polynomial in
theorem lemma3c {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    ∑ S, wS z hi S * yS z S.1 = 0 := by
  have hP := sum_weights_coeff_eq_det z hi (fun s => ((pev z s : ℝ) : ℂ)) (pmat z) (pmat_eq_eigenvectorUnitary_conj_diagonal_pev z).symm 1
  beta_reduce at hP
  rw [Matrix.coeff_det_one_add_X_smul_one, trace_leading_submatrix_pmat z hi] at hP
  have hc : ∀ S : {S : Finset (Fin n) // S.card = i},
      (∏ s ∈ S.1, (1 + Polynomial.X * Polynomial.C ((pev z s : ℝ) : ℂ))).coeff 1 =
        ((yS z S.1 : ℝ) : ℂ) := by
    intro S
    rw [(coeff_prod_one_add_low S.1 _).2.1, yS]
    push_cast
    rfl
  simp only [hc] at hP
  exact_mod_cast hP


open Polynomial in
theorem lemma3d {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    ∑ S, wS z hi S * yS z S.1 ^ 2 = Vi (pmat z) i := by
  have hP2 := sum_weights_coeff_eq_det z hi (fun s => ((pev z s : ℝ) : ℂ)) (pmat z) (pmat_eq_eigenvectorUnitary_conj_diagonal_pev z).symm 2
  have hsq : ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun s => ((pev z s : ℝ) : ℂ) ^ 2) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = pmat z * pmat z := by
    rw [← sq_conj_diagonal _ _ (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).2, ← pmat_eq_eigenvectorUnitary_conj_diagonal_pev z]
  have hP1 := sum_weights_coeff_eq_det z hi (fun s => ((pev z s : ℝ) : ℂ) ^ 2) (pmat z * pmat z) hsq 1
  beta_reduce at hP1 hP2
  rw [Matrix.coeff_det_one_add_X_smul_one] at hP1
  have h2 := coeff_two_det_hermitian _ ((pmat_isHermitian z).submatrix (Fin.castLE hi))
  rw [trace_leading_submatrix_pmat z hi] at h2
  have hS : ∀ S : {S : Finset (Fin n) // S.card = i}, ((yS z S.1 : ℝ) : ℂ) ^ 2 =
      2 * (∏ s ∈ S.1, (1 + Polynomial.X * Polynomial.C ((pev z s : ℝ) : ℂ))).coeff 2 +
        (∏ s ∈ S.1, (1 + Polynomial.X * Polynomial.C (((pev z s : ℝ) : ℂ) ^ 2))).coeff 1 := by
    intro S
    obtain ⟨-, -, h2'⟩ := coeff_prod_one_add_low S.1 (fun s => ((pev z s : ℝ) : ℂ))
    obtain ⟨-, h1'', -⟩ := coeff_prod_one_add_low S.1 (fun s => ((pev z s : ℝ) : ℂ) ^ 2)
    rw [h2', h1'', yS]
    push_cast
    ring
  apply Complex.ofReal_injective
  push_cast
  rw [variance_eq_trace_diff hi (pmat z) (pmat_isHermitian z)]
  simp only [hS, mul_add, Finset.sum_add_distrib, mul_left_comm _ (2 : ℂ), ← Finset.mul_sum]
  rw [hP2, hP1, h2]
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fbr_det_exp_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    (NormedSpace.exp (pmat z)).det = 1 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hsp : pmat z = U * diagonal (fun i => (pev z i : ℂ)) * Uᴴ := by
    have := (pmat_isHermitian z).spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have h2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv h2
  have hu : IsUnit U := ⟨⟨U, Uᴴ, h2, h1⟩, rfl⟩
  rw [hsp, ← hinv, Matrix.exp_conj _ _ hu, Matrix.det_conj hu, Matrix.exp_diagonal, det_diagonal]
  have he : ∀ i, (NormedSpace.exp (fun i => (pev z i : ℂ))) i = Complex.exp (pev z i : ℂ) := by
    intro i
    rw [Pi.exp_def, Complex.exp_eq_exp_ℂ]
  simp only [he]
  rw [← Complex.exp_sum, ← Complex.ofReal_sum, sum_pev, Complex.ofReal_zero, Complex.exp_zero]

theorem fbr_det_conj {ε : Fin n → Bool} (k : KG ε) (A : Matrix (Fin n) (Fin n) ℂ) :
    (toMK k⁻¹ * A * toMK k).det = A.det := by
  rw [toMK_inv, Matrix.det_mul, Matrix.det_mul, mul_comm ((toMK k)ᴴ.det) A.det, mul_assoc, ← Matrix.det_mul,
    (toMK_facts k).1, Matrix.det_one, mul_one]

theorem fbr_phi {ε : Fin n → Bool} {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) (k : KG ε)
    (z : PCoord ε → ℂ) :
    PhiM μ (toMK k⁻¹ * NormedSpace.exp (pmat z) * toMK k) =
      ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) := by
  obtain ⟨hP, hE⟩ := inP_conj k⁻¹ (pmat_inP z)
  rw [inv_inv] at hP hE
  rw [← hE]
  set Y := toMK k⁻¹ * pmat z * toMK k with hY
  set E := NormedSpace.exp Y with hEdef
  have hpd : E.PosDef := exp_noncompactPart_posDef hP
  have hdet : lead n E = 1 := by
    have h1 : E.det = 1 := by rw [hE, fbr_det_conj, fbr_det_exp_pmat]
    unfold lead
    rw [dite_eq_left le_rfl]
    convert h1 using 2
    ext a b
    rfl
  have hpos : ∀ i : Fin n, 0 < (lead ((i : ℕ) + 1) E).re := fun i => (lead_posDef hpd _ i.isLt).1
  have h : ∀ i : Fin n, lead ((i : ℕ) + 1) E = ((lead ((i : ℕ) + 1) E).re : ℂ) := fun i =>
    Complex.ext (by simp) (by simp [(lead_posDef hpd _ i.isLt).2])
  have hphi : PhiM μ E = ((∏ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) : ℝ) : ℂ) := by
    unfold PhiM
    rw [Complex.ofReal_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [Complex.ofReal_zpow, ← h i]
  rw [hphi]
  congr 1
  have hz : ∀ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) =
      Real.exp (Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ)) := by
    intro i
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (hpos i)]
  rw [prod_congr rfl fun i _ => hz i, ← Real.exp_sum]
  congr 1
  set g : ℕ → ℝ := fun i => -(sCoef lam i * Real.log (lead (i + 1) E).re) with hg
  have hterm : ∀ i : Fin n, Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ) = g i := by
    intro i
    by_cases hi : (i : ℕ) + 1 < n
    · have hm : muNext μ i = μ ⟨(i : ℕ) + 1, hi⟩ := by simp [muNext, hi]
      have hs : sCoef lam i = lam i - lam ⟨(i : ℕ) + 1, hi⟩ + 1 := by simp [sCoef, hi]
      rw [hm, hg]
      simp only
      rw [hs]
      push_cast
      rw [hμ i, hμ ⟨(i : ℕ) + 1, hi⟩]
      simp only [rho]
      push_cast
      ring
    · have hs : sCoef lam i = 0 := by simp [sCoef, hi]
      have hn : (i : ℕ) + 1 = n := by omega
      rw [hg]
      simp only
      rw [hs, hn, hdet]
      simp
  rw [sum_congr rfl fun i _ => hterm i, Fin.sum_univ_eq_sum_range g n]
  have hsub : ∑ i ∈ range n, g i = ∑ i ∈ range (n - 1), g i := by
    symm
    refine sum_subset (range_subset_range.mpr (Nat.sub_le n 1)) ?_
    intro i hi hi'
    simp only [mem_range] at hi hi'
    have hs : sCoef lam i = 0 := by simp only [sCoef]; rw [dite_eq_right (by omega)]
    simp [hg, hs]
  rw [hsub, Ph, ← sum_neg_distrib]
  rfl

theorem psM_exp_pmat {ε : Fin n → Bool} {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) {Λ : Fin n → ℝ}
    (T : KType ε Λ) (z : PCoord ε → ℂ) : psM T μ (NormedSpace.exp (pmat z)) = fF ε lam T (pmat z) := by
  simp only [psM, fF]
  congr 1
  refine congrArg (fun f : KG ε → T.V →L[ℂ] T.V => ∫ k, f k ∂(muK ε)) (funext fun k => ?_)
  rw [fbr_phi hμ k z]

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

theorem finrank_pcoord (ε : Fin n → Bool) :
    Module.finrank ℝ (PCoord ε → ℂ) = 2 * (pOf ε * qOf ε) := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    card_PCoord, smul_eq_mul, mul_comm]

theorem lintegral_pcoord_smul {ε : Fin n → Bool} (f : (PCoord ε → ℂ) → ENNReal) {s : ℝ} (hs : 0 < s) :
    ∫⁻ z, f z = ENNReal.ofReal (s ^ (2 * (pOf ε * qOf ε))) * ∫⁻ y, f ((s : ℂ) • y) := by
  have hsm : (fun y : PCoord ε → ℂ => f ((s : ℂ) • y)) = fun y => f (s • y) := by
    funext y
    rw [Complex.coe_smul]
  have key : ∫⁻ y, f (s • y) =
      ENNReal.ofReal |(s ^ Module.finrank ℝ (PCoord ε → ℂ))⁻¹| * ∫⁻ z, f z := by
    have h1 := lintegral_map_equiv f (MeasurableEquiv.smul₀ (α := PCoord ε → ℂ) s hs.ne')
      (μ := volume)
    have h2 : (⇑(MeasurableEquiv.smul₀ (α := PCoord ε → ℂ) s hs.ne')) = (s • ·) := rfl
    rw [h2, Measure.map_addHaar_smul volume hs.ne', lintegral_smul_measure, smul_eq_mul] at h1
    exact h1.symm
  rw [hsm, key, finrank_pcoord, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

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

theorem psiM_polar {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε)
    (z : PCoord ε → ℂ) :
    PsiM T μ (toMK k * NormedSpace.exp (pmat z)) = T.op k * psM T μ (NormedSpace.exp (pmat z)) := by
  have hX := pmat_inP z
  have hex : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧
      toMK k * NormedSpace.exp (pmat z) = toMK k' * NormedSpace.exp X' := ⟨k, pmat z, hX, rfl⟩
  unfold PsiM
  rw [dite_eq_left hex]
  obtain ⟨hP, hEq⟩ := hex.choose_spec.choose_spec
  obtain ⟨h1, h2⟩ := polar_unique hX hP hEq
  rw [← h2, ← h1]

theorem psiM_exp_pmat {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    (z : PCoord ε → ℂ) : PsiM T μ (NormedSpace.exp (pmat z)) = psM T μ (NormedSpace.exp (pmat z)) := by
  have h := psiM_polar T μ (1 : KG ε) z
  have e : toMK (1 : KG ε) = 1 := rfl
  have o : T.op (1 : KG ε) = 1 := by simp [KType.op, map_one]
  rwa [e, Matrix.one_mul, o, one_mul] at h

end ReciprocityTheory.ChartRestriction.DS
end
end
