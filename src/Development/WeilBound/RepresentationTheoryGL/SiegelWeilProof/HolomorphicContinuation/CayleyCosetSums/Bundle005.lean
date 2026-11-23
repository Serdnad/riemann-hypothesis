module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussM
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle003
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

private theorem exists_unitary_mul_blockTriangular_of_inFlagDomain (b : M2 n) (hb : InG b) : IsUnit (u1 b).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hr := congrArg (fun M => star x ⬝ᵥ (M *ᵥ x)) (v_rel b hb)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, dotProduct_sub,
    dotProduct_zero, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, star_zero, zero_dotProduct,
    sub_zero, Matrix.zero_vecMul] at hr
  simp [Matrix.vecMul_smul] at hr
  have h2 : ∑ j, Complex.normSq (x j) = 0 := by
    have h3 := congrArg Complex.re hr
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.zero_re] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_apply]
    ring
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _] at h2
  apply hx0
  funext j
  exact Complex.normSq_eq_zero.mp (h2 j (Finset.mem_univ j))

theorem factor (y b : M2 n) (hy : InG y) (hb : InG b) (hc : IsUnit y.toBlocks₂₁.det) :
    ∃ (R H0 : Matrix (Fin n) (Fin n) ℂ) (κ : ℂ), IsUnit R.det ∧ H0.IsHermitian ∧ κ ≠ 0 ∧
      ∀ S, (u1 (y * nU S * b)).det = κ * (R * Rᴴ - Complex.I • (H0 + S)).det := by
  have hU := exists_unitary_mul_blockTriangular_of_inFlagDomain b hb
  have hH := hermit_cd y hy hc
  obtain ⟨U, hUdef⟩ : ∃ U, U = u1 b := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, V = v1 b := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = y.toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = y.toBlocks₂₂ := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = V * U⁻¹ := ⟨_, rfl⟩
  have hrel : Uᴴ * V - Vᴴ * U = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hUdef, hVdef]
    exact v_rel b hb
  rw [← hUdef] at hU
  rw [← hCdef] at hc
  rw [← hCdef, ← hDdef] at hH
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hUU' : (U⁻¹)ᴴ * Uᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hUU, Matrix.conjTranspose_one]
  have hP : P - Pᴴ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹) := by
    calc P - Pᴴ = ((U⁻¹)ᴴ * Uᴴ) * V * U⁻¹ - (U⁻¹)ᴴ * Vᴴ * (U * U⁻¹) := by
          rw [hUU', hUU, Matrix.one_mul, Matrix.mul_one, hPdef, Matrix.conjTranspose_mul]
      _ = (U⁻¹)ᴴ * (Uᴴ * V - Vᴴ * U) * U⁻¹ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹) := by
          rw [hrel, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hRR : (U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ = (U⁻¹)ᴴ * U⁻¹ := by
    rw [Matrix.conjTranspose_conjTranspose]
  have hI : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ) = (1 / 2 : ℂ) • (P - Pᴴ) := by
    rw [hRR, hP, smul_smul]
    congr 1
    ring
  refine ⟨(U⁻¹)ᴴ, (1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D, C.det * Complex.I ^ n * U.det, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr (Matrix.isUnit_nonsing_inv_det _ hU)
  · refine Matrix.IsHermitian.add ?_ hH
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  · exact mul_ne_zero (mul_ne_zero hc.ne_zero (pow_ne_zero _ Complex.I_ne_zero)) hU.ne_zero
  · intro S
    have hin : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S))
        = P + C⁻¹ * D + S := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, hI]
      module
    have e1 : C * P * U = C * V := by
      rw [hPdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]
    have e2 : C * (C⁻¹ * D) * U = D * U := by
      rw [← Matrix.mul_assoc C, Matrix.mul_nonsing_inv _ hc, Matrix.one_mul]
    have hmain : u1 (y * nU S * b) = C * (Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ
        - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S))) * U := by
      rw [hin, second_coord_mul_inner, (nU_blocks y S).1, (nU_blocks y S).2, ← hCdef, ← hDdef, ← hUdef, ← hVdef]
      simp only [Matrix.mul_add, Matrix.add_mul]
      rw [e1, e2]
      abel
    rw [hmain, Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin]
    ring

end PositivityTheory.Rg.Sw.HSt.L3
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR.G

variable {m n : ℕ}

theorem inner_gen (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.IsHermitian) (hd : Q.det = 0) :
    ∫ s, ψ s * Complex.exp (Complex.I * ((herm s)ᵀ * Q).trace) = 0 := by
  obtain ⟨_, _, h⟩ := hψ
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have h0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast h0
  have hβH : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hQ.transpose.eq]
    congr 1
    simp [Complex.conj_ofReal]
  have hβd : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).det = 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose, hd, mul_zero]
  have key := h _ hβH hβd
  rw [← key]
  congr 1
  ext s
  simp only [eTr]
  congr 2
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_transpose_mul' (herm s) Q]
  field_simp

open PositivityTheory.Rg.Sw.WR.G.GM in
theorem core2 (hmn : m < n) (R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUnit R.det) (H0 : Matrix (Fin n) (Fin n) ℂ)
    (hH : H0.IsHermitian) (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, ψ s * ((R * Rᴴ - Complex.I • (H0 + herm s)).det)⁻¹ ^ m = 0 := by
  have hψ0 := hψ
  obtain ⟨hψc, hψs, -⟩ := hψ0
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hRRh : (R⁻¹)ᴴ * Rᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hRR, Matrix.conjTranspose_one]
  have hBH : ∀ s : Fin n → Fin n → ℝ, (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ).IsHermitian := by
    intro s
    have h := Matrix.isHermitian_conjTranspose_mul_mul (R⁻¹)ᴴ (hH.add (GM.herm_isHermitian s))
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hD : ∀ s : Fin n → Fin n → ℝ, (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det ≠ 0 := by
    intro s
    have h := GM.det_ne_zero (hBH s) 1
    simpa using h
  have hfac : ∀ s : Fin n → Fin n → ℝ, R * Rᴴ - Complex.I • (H0 + herm s) =
      R * (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)) * Rᴴ := by
    intro s
    have hM : R * (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) * Rᴴ = H0 + herm s := by
      simp only [← Matrix.mul_assoc, hRR, Matrix.one_mul]
      rw [Matrix.mul_assoc, hRRh, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hM]
  have hbase : ∀ s : Fin n → Fin n → ℝ, secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) =
      ((Real.pi : ℂ) ^ n / (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det) ^ m := by
    intro s
    have hA : ∀ a : Fin m, Amat (fun _ : Fin m => true) 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) a =
        (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ))ᵀ := by
      intro a
      simp [Amat, sgn, Matrix.transpose_sub, Matrix.transpose_smul]
    rw [base m n _ 1 1 one_pos _ (hBH s)]
    simp only [hA, Matrix.det_transpose, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdR : R.det ≠ 0 := hR.ne_zero
  have hdRh : Rᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 hdR
  have hπ : (Real.pi : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have halg : ∀ (P D A B Y : ℂ), P ≠ 0 → D ≠ 0 → A ≠ 0 → B ≠ 0 →
      Y * (A * D * B)⁻¹ ^ m = (A * B * P)⁻¹ ^ m * (Y * (P / D) ^ m) := by
    intro P D A B Y hP hD' hA' hB'
    have k : (A * D * B)⁻¹ = (A * B * P)⁻¹ * (P / D) := by
      field_simp
    rw [k, mul_pow]
    ring
  have hpt : ∀ s : Fin n → Fin n → ℝ, ψ s * ((R * Rᴴ - Complex.I • (H0 + herm s)).det)⁻¹ ^ m =
      ((R.det * Rᴴ.det) * (Real.pi : ℂ) ^ n)⁻¹ ^ m *
        (ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)) := by
    intro s
    rw [hfac s, Matrix.det_mul, Matrix.det_mul, hbase s]
    exact halg _ _ _ _ _ hπ (hD s) hdR hdRh
  have hgi : Integrable (fun x : Fin m → Fin n → ℂ => evX (1 : PX m n) x * gs 1 x) volume :=
    integP m n 1 one_pos 1
  have hψi : Integrable ψ volume := hψc.integrable_of_hasCompactSupport hψs
  have hherm : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  have hint : Integrable (Function.uncurry fun (s : Fin n → Fin n → ℝ) (x : Fin m → Fin n → ℂ) =>
      ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)))
      (volume.prod volume) := by
    refine Integrable.mono' (hψi.norm.mul_prod hgi.norm) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have h1 : Continuous fun p : (Fin n → Fin n → ℝ) × (Fin m → Fin n → ℂ) =>
          R⁻¹ * (H0 + herm p.1) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) p.2 :=
        ((continuous_const.matrix_mul (continuous_const.add (hherm.comp continuous_fst))).matrix_mul
          continuous_const).matrix_mul ((continuous_gramX _).comp continuous_snd)
      exact (hψc.comp continuous_fst).mul ((((GM.continuous_evX 1).comp continuous_snd).mul
        ((GI.continuous_gs 1).comp continuous_snd)).mul
        (Complex.continuous_exp.comp (continuous_const.mul h1.matrix_trace)))
    · refine Filter.Eventually.of_forall fun p => le_of_eq ?_
      obtain ⟨s, x⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [GM.norm_phase (hBH s) x, mul_one]
  have hin : ∀ x : Fin m → Fin n → ℂ, ∫ s, ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) = 0 := by
    intro x
    have hGH : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.IsHermitian :=
      (Matrix.isHermitian_conjTranspose_mul_mul R⁻¹ (GM.gramX_isHermitian _ x)).transpose
    have hGd : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.det = 0 := by
      rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, det_gram_eq_zero hmn x, mul_zero, zero_mul]
    have htr : ∀ s : Fin n → Fin n → ℝ,
        (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace =
          (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace +
          ((herm s)ᵀ * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ).trace := by
      intro s
      have h1 : (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace =
          ((H0 + herm s) * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm R⁻¹]
        simp only [Matrix.mul_assoc]
      rw [h1, Matrix.add_mul, Matrix.trace_add]
      congr 1
      rw [← Matrix.trace_transpose (herm s * _), Matrix.transpose_mul, Matrix.trace_mul_comm]
    have hrw : ∀ s : Fin n → Fin n → ℝ, ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) =
        (evX (1 : PX m n) x * gs 1 x *
          Complex.exp (Complex.I * (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace)) *
        (ψ s * Complex.exp (Complex.I *
          ((herm s)ᵀ * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ).trace)) := by
      intro s
      rw [htr s, Complex.ofReal_one, mul_one, mul_add, Complex.exp_add]
      ring
    simp only [hrw]
    rw [integral_const_mul, inner_gen ψ hψ _ hGH hGd, mul_zero]
  have hmain : ∫ s, ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) = 0 := by
    simp only [secN]
    simp only [← integral_const_mul]
    rw [integral_integral_swap hint]
    simp only [hin, integral_zero]
  simp only [hpt]
  rw [integral_const_mul, hmain, mul_zero]

end PositivityTheory.Rg.Sw.HSt.L3
end
end
