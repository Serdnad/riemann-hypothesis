module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterReductionEqExp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Formalism.LocalToGlobal.Columns.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle360
public import Formalism.LocalToGlobal.Columns.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle363
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle362
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw

@[expose] public section

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.TrueCx.FrameOnto

theorem exists_congr_one {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (hM : M.PosDef) :
    ∃ S : Matrix n n ℂ, IsUnit S.det ∧ Sᴴ * M * S = 1 := by
  classical
  set U : Matrix n n ℂ := (hM.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hD : star U * M * U = diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) := by
    have h := hM.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    exact h
  set c : n → ℂ := fun i => (RCLike.ofReal ((Real.sqrt (hM.1.eigenvalues i))⁻¹) : ℂ) with hc
  refine ⟨U * diagonal c, ?_, ?_⟩
  · rw [det_mul, det_diagonal]
    refine IsUnit.mul (isUnit_det_of_left_inverse (Unitary.coe_star_mul_self _)) ?_
    refine Ne.isUnit (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    exact RCLike.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr (hM.eigenvalues_pos i)))
  · have hs : (U * diagonal c)ᴴ * M * (U * diagonal c) = diagonal (star c) * (star U * M * U) * diagonal c := by
      rw [conjTranspose_mul, diagonal_conjTranspose, ← star_eq_conjTranspose]
      simp only [Matrix.mul_assoc]
    rw [hs, hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hl := hM.eigenvalues_pos i
    have hr : (Real.sqrt (hM.1.eigenvalues i))⁻¹ * hM.1.eigenvalues i * (Real.sqrt (hM.1.eigenvalues i))⁻¹ = 1 := by
      have h0 : Real.sqrt (hM.1.eigenvalues i) ≠ 0 := Real.sqrt_ne_zero'.mpr hl
      have h2 := Real.mul_self_sqrt hl.le
      field_simp
      linarith
    simp only [hc, Pi.star_apply, Function.comp_apply, RCLike.star_def, RCLike.conj_ofReal]
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, hr, RCLike.ofReal_one]

private lemma posDef_one_sub_mul_conjTranspose_of_posDef {p q : ℕ} {z : Matrix (Fin p) (Fin q) ℂ} (hz : (1 - zᴴ * z).PosDef) :
    (1 - z * zᴴ).PosDef := by
  have hsd : (1 - z * zᴴ).PosSemidef := by
    haveI : Invertible (1 : Matrix (Fin p) (Fin p) ℂ) := invertibleOne
    haveI : Invertible (1 : Matrix (Fin q) (Fin q) ℂ) := invertibleOne
    have h1 : (fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) z zᴴ 1).PosSemidef := by
      rw [PosDef.fromBlocks₁₁ (A := (1 : Matrix (Fin p) (Fin p) ℂ)) z 1 PosDef.one]
      simpa using hz.posSemidef
    rw [PosDef.fromBlocks₂₂ 1 z (D := (1 : Matrix (Fin q) (Fin q) ℂ)) PosDef.one] at h1
    simpa using h1
  rw [hsd.posDef_iff_det_ne_zero]
  have hu : IsUnit (1 - zᴴ * z).det := (isUnit_iff_isUnit_det _).mp hz.isUnit
  refine (isUnit_det_of_right_inverse (B := 1 + z * (1 - zᴴ * z)⁻¹ * zᴴ) ?_).ne_zero
  have h := mul_nonsing_inv _ hu
  calc (1 - z * zᴴ) * (1 + z * (1 - zᴴ * z)⁻¹ * zᴴ)
      = 1 - z * zᴴ + z * ((1 - zᴴ * z) * (1 - zᴴ * z)⁻¹) * zᴴ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
          Matrix.one_mul, Matrix.mul_assoc]
    _ = 1 := by
        rw [h, Matrix.mul_one]
        abel

theorem exists_moeb_zero {p q : ℕ} {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    ∃ g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, gᴴ * Jpq p q * g = Jpq p q ∧ moeb g 0 = z := by
  classical
  have hQ : (1 - zᴴ * z).PosDef := hz
  obtain ⟨S, hSu, hS⟩ := exists_congr_one hQ
  obtain ⟨T, hTu, hT⟩ := exists_congr_one (posDef_one_sub_mul_conjTranspose_of_posDef hQ)
  have hJ : Jpq p q = fromBlocks 1 0 0 (-1) := rfl
  refine ⟨fromBlocks T (z * S) (zᴴ * T) S, ?_, ?_⟩
  · rw [hJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · refine Eq.trans ?_ hT
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · refine Eq.trans ?_ (congrArg Neg.neg hS)
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
  · unfold moeb
    rw [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
      Matrix.mul_zero, Matrix.mul_zero, zero_add, zero_add, Matrix.mul_assoc, mul_nonsing_inv _ hSu,
      Matrix.mul_one]

private lemma gram_eq_upper_bounds {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma coe_idx_symm_inl {r j : ℕ} (hj : j ≤ r) (a : Fin j) :
    (((idx hj).symm (Sum.inl a) : Fin r) : ℕ) = r - j + a := by
  unfold idx
  simp

private lemma coe_idx_symm_inr {r j : ℕ} (hj : j ≤ r) (b : Fin (r - j)) :
    (((idx hj).symm (Sum.inr b) : Fin r) : ℕ) = b := by
  unfold idx
  simp

private lemma reindex_diagonal_sgn_eq_neg_Jpq {r j : ℕ} (hj : j ≤ r) :
    reindex (idx hj) (idx hj) (diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (r - j) a : ℝ) : ℂ)) =
      -Jpq j (r - j) := by
  have hJ : Jpq j (r - j) = fromBlocks 1 0 0 (-1) := rfl
  rw [hJ]
  ext (a | a) (b | b) <;>
    simp [reindex_apply, diagonal_apply, coe_idx_symm_inl, coe_idx_symm_inr, ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.one_apply] <;>
    split_ifs <;> simp

theorem frame_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z ∈ DomI Tau j (r - j), ∃ x ∈ X.dom, domPt X hj κ x = z := by
  intro E _ _ _ r j X hj Tau _ κ hp z hz
  classical
  have hz' : ∀ t, z t ∈ hcDom j (r - j) := hz
  choose g hg hgz using fun t => exists_moeb_zero (hz' t)
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) with hD
  have hDJ : reindex (idx hj) (idx hj) D = -Jpq j (r - j) := by
    rw [hD, hp]
    exact reindex_diagonal_sgn_eq_neg_Jpq hj
  have hD' : D = reindex (idx hj).symm (idx hj).symm (-Jpq j (r - j)) := by
    rw [← hDJ]
    simp [reindex_apply, Matrix.submatrix_submatrix]
  have hDT : Dᵀ = D := by
    rw [hD]
    exact diagonal_transpose _
  have hx0 : ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ).det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ) = D := fun τ => (X.signature τ).choose_spec
  have hgy : ∀ t, (reindex (idx hj).symm (idx hj).symm (g t))ᴴ * D * reindex (idx hj).symm (idx hj).symm (g t) = D := by
    intro t
    rw [hD']
    simp only [reindex_apply, Equiv.symm_symm, conjTranspose_submatrix, submatrix_mul_equiv]
    rw [Matrix.mul_neg, Matrix.neg_mul, hg t]
  have hT : ∀ y : Matrix (Fin r) (Fin r) ℂ,
      yᵀ * D * y.map (starRingEnd ℂ) = (yᴴ * Dᵀ * y)ᵀ := by
    intro y
    have h1 : (yᴴ)ᵀ = y.map (starRingEnd ℂ) := by
      ext a b
      simp
    rw [transpose_mul, transpose_mul, transpose_transpose, h1, Matrix.mul_assoc]
  let x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r := fun τ =>
    (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)) : Matrix (Fin r) (Fin r) ℂ)
  have hm : ∀ τ, ReciprocityTheory.ChartRestriction.G.FD.mat x τ = ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)) :=
    fun τ => rfl
  have hgram : ∀ τ : X.Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = D := by
    intro τ
    have h0 := (hx0 τ).2
    rw [hm, gram_eq_upper_bounds]
    rw [gram_eq_upper_bounds] at h0
    have hre : (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)))ᵀ * X.Gm.map τ.1 *
        (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ))).map (starRingEnd ℂ) =
        (reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)))ᵀ * ((ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ)ᵀ * X.Gm.map τ.1 *
          (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ).map (starRingEnd ℂ)) *
          (reindex (idx hj).symm (idx hj).symm (g (κ.symm τ))).map (starRingEnd ℂ) := by
      rw [transpose_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    rw [hre, h0, hT, hDT, hgy, hDT]
  refine ⟨x, ?_, ?_⟩
  · show ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re
    intro τ
    have hsg : ∀ a : ℕ, ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a ≠ 0 := by
      intro a
      unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
      split_ifs <;> norm_num
    refine ⟨?_, ?_⟩
    · intro hdet
      have h := congrArg Matrix.det (hgram τ)
      rw [gram_eq_upper_bounds, det_mul, det_mul, det_transpose, hdet, zero_mul, zero_mul, hD,
        det_diagonal] at h
      exact (Finset.prod_ne_zero_iff.mpr fun (a : Fin r) _ => Complex.ofReal_ne_zero.mpr (hsg a)) h.symm
    · intro i
      have hl : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i = ((ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ) := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.dmin ReciprocityTheory.ChartRestriction.G.FD.lminor ReciprocityTheory.ChartRestriction.G.FD.psgn
        rw [hgram τ, hD, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal]
        simp only [Function.comp_apply, Fin.coe_castLE]
        rw [Fin.prod_univ_eq_prod_range (fun a => ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) (i : ℕ),
          Complex.ofReal_prod]
      have hps : ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i ≠ 0 := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.psgn
        exact Finset.prod_ne_zero_iff.mpr fun a _ => hsg a
      rw [hl, Complex.ofReal_re]
      exact mul_self_pos.mpr hps
  · funext t
    have hf : frameCo X hj x (κ t) = g t := by
      unfold frameCo
      rw [hm, ← Matrix.mul_assoc, nonsing_inv_mul _ (hx0 (κ t)).1.isUnit, Matrix.one_mul,
        Equiv.symm_apply_apply]
      simp [reindex_apply, Matrix.submatrix_submatrix]
    show moeb (frameCo X hj x (κ t)) 0 = z t
    rw [hf, hgz t]

end GlobalTheory.TrueCx.FrameOnto
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal Nat

namespace GlobalTheory.HuaIntegral

open GlobalTheory.FlagVolume

theorem exists_factor {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) :
    ∃ R : Matrix (Fin q) (Fin q) ℂ, R.det ≠ 0 ∧ A = Rᴴ * R := by
  open scoped MatrixOrder in
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg
  refine ⟨R, fun h0 => ?_, hR⟩
  have := hA.det_pos.ne'
  rw [hR, det_mul, h0, mul_zero] at this
  exact this rfl

theorem det_conjTranspose_mul_re {q : ℕ} (R : Matrix (Fin q) (Fin q) ℂ) : (Rᴴ * R).det.re = ‖R.det‖ ^ 2 := by
  rw [det_mul, det_conjTranspose, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem det_add_row {q : ℕ} (R : Matrix (Fin q) (Fin q) ℂ) (y : Fin q → ℂ) :
    (Rᴴ * R + vecMulVec (star (vecMul y R)) (vecMul y R)).det.re = ‖R.det‖ ^ 2 * (1 + ∑ k, ‖y k‖ ^ 2) := by
  have h : Rᴴ * R + vecMulVec (star (vecMul y R)) (vecMul y R) =
      Rᴴ * (1 + replicateCol Unit (star y) * replicateRow Unit y) * R := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ R, ← replicateCol_mulVec, ← replicateRow_vecMul, ← star_vecMul, vecMulVec_eq Unit]
  have h2 : (1 + y ⬝ᵥ star y : ℂ) = ((1 + ∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) := by
    simp [dotProduct, Complex.mul_conj']
  rw [h, det_mul, det_mul, det_one_add_replicateCol_mul_replicateRow, mul_right_comm, ← det_mul, h2,
    Complex.re_mul_ofReal, det_conjTranspose_mul_re]

theorem lintegral_add_row {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) (m : ℕ) :
    ∫⁻ u : Fin q → ℂ, ENNReal.ofReal (((A + vecMulVec (star u) u).det.re ^ (m + q + 1))⁻¹) =
      ENNReal.ofReal ((A.det.re ^ (m + q))⁻¹) * ENNReal.ofReal (Real.pi ^ q * m ! / (m + q)!) := by
  obtain ⟨R, hR, rfl⟩ := exists_factor hA
  have hc : Continuous fun u : Fin q → ℂ => (Rᴴ * R + vecMulVec (star u) u).det.re := by
    refine Complex.continuous_re.comp (Continuous.matrix_det (continuous_const.add ?_))
    refine continuous_matrix fun i j => ?_
    simp only [vecMulVec_apply, Pi.star_apply]
    fun_prop
  have hp : 0 < ‖R.det‖ ^ 2 := by positivity
  rw [lintegral_comp_vecMul R hR (by exact (hc.measurable.pow_const _).inv.ennreal_ofReal), det_conjTranspose_mul_re]
  simp only [det_add_row, mul_pow, mul_inv,
    ENNReal.ofReal_mul (show 0 ≤ ((‖R.det‖ ^ 2) ^ (m + q + 1))⁻¹ by positivity)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_pi_inv_pow q m one_pos, ← mul_assoc,
    ← ENNReal.ofReal_mul hp.le]
  congr 2
  · field_simp
    ring
  · simp

def rowSucc (p q : ℕ) : (Fin p × Fin q) ⊕ Fin q → Fin (p + 1) × Fin q
  | .inl a => (a.1.castSucc, a.2)
  | .inr j => (Fin.last p, j)

theorem rowSucc_bijective (p q : ℕ) : Function.Bijective (rowSucc p q) := by
  constructor
  · rintro (⟨a, b⟩ | j) (⟨a', b'⟩ | j') hh <;>
      simp_all [rowSucc, (Fin.castSucc_ne_last _).symm]
  · rintro ⟨a, b⟩
    induction a using Fin.lastCases with
    | last => exact ⟨.inr b, rfl⟩
    | cast a => exact ⟨.inl (a, b), rfl⟩

theorem exists_measurePreserving_rowSucc (p q : ℕ) :
    ∃ Φ : (Fin p × Fin q → ℂ) × (Fin q → ℂ) → (Fin (p + 1) × Fin q → ℂ),
      MeasurePreserving Φ ∧ ∀ v u, (∀ a b, Φ (v, u) (a.castSucc, b) = v (a, b)) ∧
        ∀ j, Φ (v, u) (Fin.last p, j) = u j := by
  let e := Equiv.ofBijective _ (rowSucc_bijective p q)
  refine ⟨_, (volume_measurePreserving_piCongrLeft (fun _ ↦ ℂ) e).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ ↦ ℂ)), fun u b ↦
    ⟨fun a c ↦ ?_, fun j ↦ ?_⟩⟩
  · exact MeasurableEquiv.piCongrLeft_apply_apply e _ (.inl (a, c))
  · exact MeasurableEquiv.piCongrLeft_apply_apply e _ (.inr j)

theorem lintegral_det_inv_pow (m q p : ℕ) :
    ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal
        (((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ (m + p + q))⁻¹) =
      ENNReal.ofReal (∏ i ∈ Finset.range p, (Real.pi ^ q * (m + i)! / (m + i + q)!)) := by
  have hm : ∀ p s : ℕ, Measurable fun v : Fin p × Fin q → ℂ => ENNReal.ofReal
      (((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ s)⁻¹) := by
    intro p s
    have hc : Continuous fun v : Fin p × Fin q → ℂ => (Matrix.of fun a b => v (a, b)) :=
      continuous_matrix fun i j => by simp only [of_apply]; fun_prop
    exact ((Complex.continuous_re.comp
      (continuous_const.add (hc.matrix_conjTranspose.matrix_mul hc)).matrix_det).measurable.pow_const
        s).inv.ennreal_ofReal
  induction p with
  | zero => simp [volume_pi]
  | succ p ih =>
    obtain ⟨Φ, hΦ, hΦ'⟩ := exists_measurePreserving_rowSucc p q
    rw [← hΦ.lintegral_comp (hm _ _), Measure.volume_eq_prod,
      lintegral_prod _ (by exact ((hm _ _).comp hΦ.measurable).aemeasurable)]
    have h : ∀ (v : Fin p × Fin q → ℂ) (u : Fin q → ℂ),
        1 + (Matrix.of fun a b => Φ (v, u) (a, b))ᴴ * (Matrix.of fun a b => Φ (v, u) (a, b)) =
        (1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))) + vecMulVec (star u) u := by
      intro v u
      rw [add_assoc]
      congr 1
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_castSucc, (hΦ' v u).1, (hΦ' v u).2, vecMulVec_apply]
    have hpos : ∀ v : Fin p × Fin q → ℂ,
        (1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).PosDef := fun v =>
      PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self _)
    simp only [h, show m + (p + 1) + q = (m + p) + q + 1 by ring, lintegral_add_row (hpos _)]
    rw [lintegral_mul_const _ (hm _ _), ih, Finset.prod_range_succ, ENNReal.ofReal_mul (by positivity)]

theorem dual_mass : ∀ p q : ℕ, ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal ((1 + (Matrix.of fun a b => v (a, b))ᴴ * (Matrix.of fun a b => v (a, b))).det.re ^ (-((p + q : ℕ) : ℤ))) = ENNReal.ofReal (grassConst p q)⁻¹ := by
  intro p q
  have h := lintegral_det_inv_pow 0 q p
  simp only [zero_add] at h
  simp only [_root_.zpow_neg, _root_.zpow_natCast]
  rw [h, grassConst, inv_div, div_eq_mul_inv, ← Finset.prod_inv_distrib, mul_comm p q, pow_mul,
    ← Finset.card_range p, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [inv_div, add_comm q i, mul_div_assoc]

end GlobalTheory.HuaIntegral
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.TypePrimes.psiG_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → TC.Pins B X → ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (G : GLoc (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g), TC.IdG I l Z G → ∀ ψ, Formalism.L2.Theta.IsStdChar (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ψ (-1) → ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (h : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g k : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F), Formalism.L2.Theta.IsPlaceIdem (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) v ε → ∀ c y : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F, Valued.v (algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) - G.phi k v h (inclE (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.xi0)) < 1 → ∀ z : v.adicCompletionIntegers (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F, (z : v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) = algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (y : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) → G.psi0 k v h (IsLocalRing.residue _ z) = ψ (ε * algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ((c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) * (y : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) / ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g k : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))) :=
  by
    intro B X I hI _ l Z G hG ψ hψ k v h ε hε c y hc z hz
    have hs := (TC.rec7 I l Z).nd.g_split k
    have hgp := l.pr.g_prime k
    obtain ⟨hN, hsq⟩ := GlobalTheory.Mem.TypePrimes.Red.absNorm_and_unram hgp hs v h
    obtain ⟨t, ht⟩ := GlobalTheory.Mem.TypePrimes.Red.exists_hostXi0_inverse_integer B.host
    obtain ⟨b, hb, e⟩ := GlobalTheory.Mem.TypePrimes.Red.columnCharacter_reduction_eq_exp
      (X := B.fields) (Pr := B.primes X) I.Ch l.pr B.sp.cm B.embLL B.host.xi0 hI.weil t ht G hG.piG
      (fun _ => rfl) hG.psi k v h hN c y hc z hz
    refine e.trans ?_
    exact (GlobalTheory.T.standardAddChar_placeIdempotent_div_prime (TC.rec7 I l Z) ψ hψ _
      hgp v hN hsq ε hε (c * y) (b : ℤ) (by rw [Int.cast_natCast]; exact hb)).symm
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_ptOf_mul_K1_standard : ∀ {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) (k t : GA B n), t ∈ K1 B.sp.cm n ST SG → (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) → ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (k * t) p ∧ p.deco.1.N = stdLat B.fields.E n := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.KStd.exists_ptOf_mul_K1 | exact GlobalTheory.Mem.Col2.TopCh.KStd.exists_ptOf_mul_K1 | (intros; apply GlobalTheory.Mem.Col2.TopCh.KStd.exists_ptOf_mul_K1 <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastStep_twist_level_contains_principal_congruence : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι), ∃ N : I.Q a → ℕ, (∀ P : I.Q a, P.1.valuation B.host.E (((qOf P.1 : ℕ) : B.host.E) ^ (topDep B.R (I.cst a).M + 1)) ≤ WithZero.exp (-(N P : ℤ))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.host.E (B.R.N B.R.m) P.1)), lqPrinc P.1 (N P) (g : Sp B.host.E (B.R.N B.R.m) ≃ₗ[B.host.E] Sp B.host.E (B.R.N B.R.m)) → ∃ h : g ∈ ((I.Tp a).levQ B.R.m P).H, ((I.Tp a).levQ B.R.m P).lam ⟨g, h⟩ = 1 := by
  exact @GlobalTheory.Mem.Col2.TC.levQ_top_princ
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem T_notMem_qv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (B.primes X).Ok → ∀ (u : B.Word) (a : I.ι) (P : I.Q a), (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal := by
  classical
  intro B X I hI _ u a P
  have hP : P.1 ∈ uSG (B.primes X).vGs I.SQ := Finset.mem_union.2 (Or.inr (I.mem_SQ.2 ⟨a, P.2⟩))
  exact GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P.1 hP

end GlobalTheory.Mem.Col2.ChEx
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_K1_point_congruent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → ∀ c : ℕ, ∃ z ∈ K1 hc n ST SG, (∀ P : Q, Sm Valued.v (dep P.1 c) (locM P.1 z - 1)) ∧ ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * z) p := by
  first | exact @GlobalTheory.Mem.ColAd.exists_K1_isPtOf | exact GlobalTheory.Mem.ColAd.exists_K1_isPtOf | (intros; apply GlobalTheory.Mem.ColAd.exists_K1_isPtOf <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (a : GlobalTheory.Mem.Chr.Ideles H.E), IsDetLift (host_cmData R H) x.1 a → ((x.1 ∈ Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H)) ↔ ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (compAt w a) = Valued.v (compAt (conjPrime₂ w) a)) := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val | exact GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val | (intros; apply GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val <;> assumption)
end

section

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix

namespace GlobalTheory.SeeSaw.TwLev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def RatAt (Q : Finset (HeightOneSpectrum (𝓞 E))) : Set (GL (Fin n) (AfE F E)) :=
  {z | ∀ P : Q, ∀ i j, ∃ e : E, adAt F P.1 ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ e}

variable [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))}


variable (hc : CMData F E) in
def RdLevOn {K : Type} [Field K] (A : Set (GL (Fin n) (AfE F E))) (U : Subgroup (GL (Fin n) (AfE F E))) (chi : U →* ℂˣ)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (Q : Finset (HeightOneSpectrum (𝓞 E)))
    (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ) : Prop :=
  ∀ z ∈ A, ∀ hz : z ∈ St (1 : GL (Fin n) (AfE F E)), z ∈ UAd hc n →
    (z ∈ U ↔ (∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) ∧ ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P) ∧
      ∀ (hU : z ∈ U) (h : ∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) (h' : ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P),
        ((chi ⟨z, hU⟩ : ℂˣ) : ℂ) =
          (∏ w : SG, (emb (((Λ w).lam ⟨_, h w⟩ : Kˣ) : K))⁻¹) * ∏ P : Q, ((lamQ P ⟨_, h' P⟩ : ℂˣ) : ℂ)

end GlobalTheory.SeeSaw.TwLev
end
end
