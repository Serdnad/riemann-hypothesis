module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle052
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

@[expose] public section

section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

noncomputable def qC {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (y i) * G i j * y j).re

noncomputable def qR {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) : ℝ :=
  ∑ i, ∑ j, y i * G i j * y j

private lemma exists_factor_C {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, G = Bᴴ * B := by
  first
  | exact Matrix.posSemidef_iff_eq_transpose_mul_self.1 hG.posSemidef
  | exact (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).1 hG.posSemidef
  | exact hG.posSemidef.exists_eq_conjTranspose_mul_self
  | (refine ⟨hG.posSemidef.sqrt, ?_⟩
     rw [hG.posSemidef.posSemidef_sqrt.isHermitian.eq, hG.posSemidef.sqrt_mul_self])
  | (refine ⟨CFC.sqrt G, ?_⟩
     have h0 : 0 ≤ G := hG.posSemidef.nonneg
     have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
     rw [hs, CFC.sqrt_mul_sqrt_self G h0])

private lemma exists_factor_R {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᵀ * B := by
  have hC : ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᴴ * B := by
    first
    | exact Matrix.posSemidef_iff_eq_transpose_mul_self.1 hG.posSemidef
    | exact (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).1 hG.posSemidef
    | exact hG.posSemidef.exists_eq_conjTranspose_mul_self
    | (refine ⟨hG.posSemidef.sqrt, ?_⟩
       rw [hG.posSemidef.posSemidef_sqrt.isHermitian.eq, hG.posSemidef.sqrt_mul_self])
    | (refine ⟨CFC.sqrt G, ?_⟩
       have h0 : 0 ≤ G := hG.posSemidef.nonneg
       have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
       rw [hs, CFC.sqrt_mul_sqrt_self G h0])
  obtain ⟨B, hB⟩ := hC
  exact ⟨B, by rw [hB, Matrix.conjTranspose_eq_transpose_of_trivial]⟩

private lemma qC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) :
    qC (Bᴴ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : (∑ i, ∑ j, starRingEnd ℂ (y i) * (Bᴴ * B) i j * y j) =
      dotProduct (star y) ((Bᴴ * B) *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, RCLike.star_def]
  unfold qC
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.re_sum, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  refine Finset.sum_congr rfl (fun k _ => by ring)

private lemma qR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) :
    qR (Bᵀ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : qR (Bᵀ * B) y = dotProduct y ((Bᵀ * B) *ᵥ y) := by
    simp only [qR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, Real.norm_eq_abs, sq_abs, sq, abs_mul_abs_self]

private lemma setC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    {y | qC (Bᴴ * B) y ≤ R ^ 2} = ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qC_eq, LinearMap.restrictScalars_apply,
    Matrix.toLin'_apply, sqBall]

private lemma setR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    {y | qR (Bᵀ * B) y ≤ R ^ 2} = (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qR_eq, Matrix.toLin'_apply, sqBall]
  skip

private lemma detC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) :
    (Bᴴ * B).det = (Complex.normSq B.det : ℂ) := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.normSq_eq_conj_mul_self]
  rfl

private theorem isBounded_preimage_sqBall_complex_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hS : IsCompact (sqBall r ℂ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous ((Matrix.toLin' B⁻¹).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨(Matrix.toLin' B).restrictScalars ℝ y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

private theorem convex_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    Convex ℝ (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℂ) r R) ((Matrix.toLin' B).restrictScalars ℝ)

private theorem neg_mem_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    ∀ y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R,
      -y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℂ) r R _ hy

private theorem measurableSet_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    MeasurableSet (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hc : Continuous ((Matrix.toLin' B).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet

private lemma hermitianEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : G = Bᴴ * B) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [detC_eq, h0] at h1
    simp at h1
  rw [setC_eq]
  exact ⟨convex_preimage_sqBall_complex B R, neg_mem_preimage_sqBall_complex B R, isBounded_preimage_sqBall_complex_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_complex B R⟩

theorem ellipsoidC_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_C hG
  exact hermitianEllipsoid_props_of_eq hG B hB R

private theorem isBounded_preimage_sqBall_real_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hS : IsCompact (sqBall r ℝ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous (Matrix.toLin' B⁻¹) := LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨Matrix.toLin' B y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

private theorem convex_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    Convex ℝ ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℝ) r R) (Matrix.toLin' B)

private theorem neg_mem_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    ∀ y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R, -y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℝ) r R _ hy

private theorem measurableSet_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    MeasurableSet ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hc : Continuous (Matrix.toLin' B) := LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet

private lemma realEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℝ)
    (hB : G = Bᵀ * B) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [setR_eq]
  exact ⟨convex_preimage_sqBall_real B R, neg_mem_preimage_sqBall_real B R, isBounded_preimage_sqBall_real_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_real B R⟩

theorem ellipsoidR_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_R hG
  exact realEllipsoid_props_of_eq hG B hB R

end ReciprocityTheory.GeometryOfNumbersTheory
end

section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix
open scoped ComplexOrder

theorem neg_log_det_le {r' r : ℕ} (hr : r' ≤ r) {G' : Matrix (Fin r') (Fin r') ℂ}
    {G : Matrix (Fin r) (Fin r) ℂ} (hG' : G'.PosDef) (hG : G.PosDef)
    (M : Matrix (Fin r) (Fin r') ℤ) (hM : Function.Injective (M.map (Int.cast : ℤ → ℚ)).mulVec)
    (N : Matrix (Fin r) (Fin r) ℤ) (hN : N.det ≠ 0) {A lam : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hnorm : (((A : ℂ) ^ 2) • G' -
      (M.map (Int.cast : ℤ → ℂ))ᴴ * G * M.map (Int.cast : ℤ → ℂ)).PosSemidef)
    (hsmall : ∀ i, (((N.map (Int.cast : ℤ → ℂ))ᴴ * G * N.map (Int.cast : ℤ → ℂ)) i i).re ≤ lam ^ 2) :
    -(1 / 2) * Real.log G'.det.re ≤
      -(1 / 2) * Real.log G.det.re + r' * Real.log A + ((r : ℝ) - r') * Real.log lam := by
  classical
  have hu0 : LinearIndependent ℚ (M.map (Int.cast : ℤ → ℚ)).col := Matrix.mulVec_injective_iff.mp hM
  have hNq : (N.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det]; exact_mod_cast hN
  have hw : LinearIndependent ℚ (N.map (Int.cast : ℤ → ℚ)).col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hNq.isUnit)
  obtain ⟨m, f, hmr, hLI⟩ := LinearIndependentExtension.exists_append_li _ hu0 _ hw
  subst hmr
  set U : Matrix (Fin (r' + m)) (Fin (r' + m)) ℤ :=
    Matrix.of fun i j => Fin.append (fun k => M i k) (fun k => N i (f k)) j with hUdef
  have hUq : (U.map (Int.cast : ℤ → ℚ)).col =
      Fin.append (M.map (Int.cast : ℤ → ℚ)).col ((N.map (Int.cast : ℤ → ℚ)).col ∘ f) := by
    funext j i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · rw [Fin.append_left]; simp [U, Matrix.col]
    · rw [Fin.append_right]; simp [U, Matrix.col]; rfl
  have hUdet : U.det ≠ 0 := by
    rw [← hUq, Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, ← Int.cast_det] at hLI
    exact_mod_cast hLI
  set UC := U.map (Int.cast : ℤ → ℂ) with hUC
  set MC := M.map (Int.cast : ℤ → ℂ) with hMC
  set NC := N.map (Int.cast : ℤ → ℂ) with hNC
  have hUCdet : UC.det = ((U.det : ℤ) : ℂ) := by rw [hUC, Int.cast_det]
  have hUCinj : Function.Injective UC.mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hUCdet, isUnit_iff_ne_zero]
    exact_mod_cast hUdet
  set H := UCᴴ * G * UC with hH
  have hHpd : H.PosDef := hG.conjTranspose_mul_mul_same hUCinj
  have hUl : ∀ l i, UC l (Fin.castAdd m i) = MC l i := by intro l i; simp [UC, U, MC]
  have hUr : ∀ l j, UC l (Fin.natAdd r' j) = NC l (f j) := by intro l j; simp [UC, U, NC]
  have hsub : H.submatrix (Fin.castAdd m) (Fin.castAdd m) = MCᴴ * G * MC := by
    ext i j; simp only [H, submatrix_apply, Matrix.mul_apply, conjTranspose_apply, hUl]
  have hdiag : ∀ j, H (Fin.natAdd r' j) (Fin.natAdd r' j) = (NCᴴ * G * NC) (f j) (f j) := by
    intro j; simp only [H, Matrix.mul_apply, conjTranspose_apply, hUr]
  have hMMpd : (MCᴴ * G * MC).PosDef := by
    rw [← hsub]; exact hHpd.submatrix (Fin.castAdd_injective r' m)

  have hdetH : H.det.re = ((U.det : ℝ) ^ 2) * G.det.re := by
    rw [hH, det_mul, det_mul, det_conjTranspose, hUCdet]
    simp [Complex.mul_re, Complex.mul_im, sq]
    ring
  have hd1 : (1 : ℝ) ≤ (U.det : ℝ) ^ 2 := by
    have h1 := Int.one_le_abs hUdet
    have : (1 : ℤ) ≤ U.det ^ 2 := by nlinarith [sq_abs U.det]
    exact_mod_cast this
  have hGpos := (posDef_det_re_pos hG).1
  have hG'pos := (posDef_det_re_pos hG').1
  have hstep1 : G.det.re ≤ H.det.re := by rw [hdetH]; nlinarith
  have hstep2 := det_re_le_mul_prod_diag hHpd
  rw [hsub] at hstep2
  have hprod : ∏ j : Fin m, (H (Fin.natAdd r' j) (Fin.natAdd r' j)).re ≤ (lam ^ 2) ^ m := by
    rw [← Fin.prod_const]
    refine Finset.prod_le_prod₀ (fun j _ => (Complex.pos_iff.mp (hHpd.diag_pos)).1.le) (fun j _ => ?_)
    rw [hdiag]; exact hsmall _
  have hMM : (MCᴴ * G * MC).det.re ≤ (A ^ 2) ^ r' * G'.det.re := by
    have := det_re_le_of_sub_posSemidef hMMpd hnorm
    rw [det_smul, Fintype.card_fin] at this
    have e : ((A : ℂ) ^ 2) ^ r' = (((A ^ 2) ^ r' : ℝ) : ℂ) := by push_cast; ring
    rwa [e, Complex.re_ofReal_mul] at this
  have hMMpos := (posDef_det_re_pos hMMpd).1
  have hfin : G.det.re ≤ (A ^ 2) ^ r' * G'.det.re * (lam ^ 2) ^ m := by
    have hP0 : 0 ≤ ∏ j : Fin m, (H (Fin.natAdd r' j) (Fin.natAdd r' j)).re :=
      Finset.prod_nonneg fun j _ => (Complex.pos_iff.mp (hHpd.diag_pos)).1.le
    calc G.det.re ≤ H.det.re := hstep1
      _ ≤ _ := hstep2
      _ ≤ (A ^ 2) ^ r' * G'.det.re * (lam ^ 2) ^ m :=
        mul_le_mul hMM hprod hP0 (by positivity)
  have hlog := Real.log_le_log hGpos hfin
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog ⊢
  linarith

end ReciprocityTheory.GeometryOfNumbersTheory
end

section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Module NumberField Set

set_option backward.isDefEq.respectTransparency.types false in
theorem covol_div_covol_eq_relIndex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ / ZLattice.covolume L₂ μ =
      L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  classical
  let b₂ := Module.Free.chooseBasis ℤ L₂
  let e : Module.Free.ChooseBasisIndex ℤ L₁ ≃ Module.Free.ChooseBasisIndex ℤ L₂ :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex,
        ZLattice.rank ℝ L₁, ZLattice.rank ℝ L₂])
  let b₁ := (Module.Free.chooseBasis ℤ L₁).reindex e
  let b₀ := b₂.ofZLatticeBasis ℝ L₂
  have h1 := ZLattice.covolume_eq_det_mul_measureReal L₁ μ b₁ b₀
  have h2 := ZLattice.covolume_eq_det_mul_measureReal L₂ μ b₂ b₀
  have hb : ((↑) ∘ b₂ : _ → E) = ⇑b₀ := by ext i; simp [b₀, Basis.ofZLatticeBasis_apply]
  rw [hb, Basis.det_self, abs_one, one_mul] at h2
  have hpos := ZLattice.covolume_pos L₂ μ
  rw [h2] at hpos
  rw [h1, h2, mul_div_assoc, div_self hpos.ne', mul_one,
    AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂,
    Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ j, h (Submodule.coe_mem _)⟩ i)

theorem measurePreserving_swapPi {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] :
    MeasurePreserving (fun (f : ι → κ → X) (k : κ) (i : ι) => f i k)
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => ν)
      (Measure.pi fun _ : κ => Measure.pi fun _ : ι => ν) := by
  first | exact UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi .. | (apply UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi <;> first | assumption | infer_instance)

end ReciprocityTheory.GeometryOfNumbersTheory

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder
open Matrix

section Form

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem HermFam.form_smul_left (h : HermFam K V) (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm, h.smul_right, map_mul, h.conj_symm]

theorem HermFam.form_sum_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, h.form σ x (f i) :=
  map_sum (AddMonoidHom.mk' (h.form σ x) (h.add_right σ x)) f s

theorem HermFam.form_sum_left (h : HermFam K V) (σ : K →+* ℂ) (y : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, h.form σ (f i) y := by

  rw [← h.conj_symm, h.form_sum_right, map_sum]
  simp only [h.conj_symm]

theorem HermFam.form_expand (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (c : Fin n → K)
    (v : Fin n → V) :
    h.form σ (∑ i, c i • v i) (∑ j, c j • v j) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (c i)) * h.gram σ v i j * σ (c j) := by
  rw [h.form_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h.form_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h.form_smul_left, h.smul_right, HermFam.gram, Matrix.of_apply]
  ring

end Form

section Places

variable {K : Type*} [Field K] [NumberField K]

end Places

end ReciprocityTheory.GeometryOfNumbersTheory
end
