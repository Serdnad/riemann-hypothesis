module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle041
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
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
import Mathlib.Data.Pi.Interval
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.FieldTheory.Perfect

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.PsiBound

theorem form_conj {n : ℕ} (Z M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    star x ⬝ᵥ ((Zᴴ * M * Z) *ᵥ y) = star (Z *ᵥ x) ⬝ᵥ (M *ᵥ (Z *ᵥ y)) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem form_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (x y : Fin n → ℂ) :
    star (t • x) ⬝ᵥ (M *ᵥ (t • y)) = ((t ^ 2 : ℝ) : ℂ) * (star x ⬝ᵥ (M *ᵥ y)) := by
  rw [← algebraMap_smul ℂ t x, ← algebraMap_smul ℂ t y, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.coe_algebraMap, Complex.star_def, Complex.conj_ofReal]
  push_cast; ring

theorem bound_of_form {n : ℕ} (f : (Fin n → ℂ) → ℝ) (hc : Continuous f)
    (hh : ∀ (t : ℝ) (x : Fin n → ℂ), f (t • x) = t ^ 2 * f x) (hp : ∀ x, x ≠ 0 → 0 < f x) :
    ∃ K : ℝ, ∀ (A : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 ≤ s → (∀ x, f (A *ᵥ x) = s * f x) →
      ∀ a b, ‖A a b‖ ≤ K * Real.sqrt s := by
  first
  | exact @_root_.GlobalTheory.LowerTriangularEntryBound.entry_bound
  | exact _root_.GlobalTheory.LowerTriangularEntryBound.entry_bound
  | (apply _root_.GlobalTheory.LowerTriangularEntryBound.entry_bound <;> assumption)
  | (intros; apply _root_.GlobalTheory.LowerTriangularEntryBound.entry_bound <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LowerTriangularEntryBound.entry_bound <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LowerTriangularEntryBound.entry_bound ..)

end GlobalTheory.LKCx.PsiBound

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integrableOn_poincareAreaDensity_punctured_disc : IntegrableOn (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2) (Metric.closedBall 0 (1 / 2)) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_poincare_disc | exact GlobalTheory.GoodTop.integrableOn_poincare_disc | (intros; apply GlobalTheory.GoodTop.integrableOn_poincare_disc <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_diagonal_congr_of_similitude_distinct_eigenvalues : ∀ {n : ℕ} (h g : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ), h.IsHermitian → h.det ≠ 0 → c ≠ 0 → gᴴ * h * g = (c : ℂ) • h → Function.Injective lam → (∀ i, ‖lam i‖ ^ 2 = c) → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∃ d : Fin n → ℝ, (∀ i, d i ≠ 0) ∧ (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  first | (exact @GlobalTheory.similitude_eigvec_orthogonal) | (exact GlobalTheory.similitude_eigvec_orthogonal) | (intros; apply GlobalTheory.similitude_eigvec_orthogonal  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory


open Matrix NumberField in
open scoped TensorProduct Classical in
theorem _root_.GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral (K : Type) [Field K] [NumberField K]
    (d D : ℕ) (B : ℝ) (hD : 0 < D) :
    {P : Polynomial K | P.Monic ∧ P.natDegree ≤ d ∧ ∀ k, IsIntegral ℤ ((D : K) * P.coeff k) ∧
      ∀ φ : K →+* ℂ, ‖φ (P.coeff k)‖ ≤ B}.Finite := by
  have hT : {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}.Finite := by
    have h := NumberField.Embeddings.finite_of_norm_le K ℂ ((D : ℝ) * B)
    refine (h.image fun x => x / (D : K)).subset ?_
    intro c hc
    refine ⟨(D : K) * c, ⟨hc.1, fun φ => ?_⟩, ?_⟩
    · have := mul_le_mul_of_nonneg_left (hc.2 φ) (Nat.cast_nonneg (α := ℝ) D)
      simpa [norm_mul] using this
    · have hD' : (D : K) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
      field_simp
  have hF : (Set.pi Set.univ fun _ : Fin (d + 1) =>
      {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}).Finite :=
    Set.Finite.pi fun _ => hT
  refine Set.Finite.of_finite_image
    (f := fun P : Polynomial K => fun i : Fin (d + 1) => P.coeff i) (hF.subset ?_) ?_
  · rintro _ ⟨P, hP, rfl⟩ i -
    exact ⟨(hP.2.2 i).1, (hP.2.2 i).2⟩
  · intro P hP Q hQ hPQ
    ext n
    by_cases hn : n ≤ d
    · exact congrFun hPQ ⟨n, Nat.lt_succ_of_le hn⟩
    · push_neg at hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.2.1.trans_lt hn),
        Polynomial.coeff_eq_zero_of_natDegree_lt (hQ.2.1.trans_lt hn)]

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.SimNormSq

open Polynomial

theorem commute_aeval_of_commute {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {x y : A} (h : Commute y x) (p : R[X]) : Commute y (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]; exact (Algebra.commute_algebraMap_right a y).mul_right (h.pow_right n)

theorem eq_zero_of_conjTranspose_mul_mul_eq_zero {n : ℕ} {H A : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (h : Aᴴ * H * A = 0) : A = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Matrix.zero_mulVec]
  by_contra hne
  have hpos := hH.dotProduct_mulVec_pos hne
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h,
    Matrix.zero_mulVec, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.SimNormSq

namespace GlobalTheory

open Polynomial

theorem aeval_eq_zero_of_mul_self_eq_zero_of_similitude :
    ∀ (n : ℕ) (H M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), H.PosDef → 0 < s →
      Mᴴ * H * M = (s : ℂ) • H → ∀ P : Polynomial ℂ,
        Polynomial.aeval M P * Polynomial.aeval M P = 0 → Polynomial.aeval M P = 0 := by
  intro n H M s hH hs hM P hP
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hHinv : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hHinv' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hHh : Hᴴ = H := hH.1
  have hHih : (H⁻¹)ᴴ = H⁻¹ := by rw [conjTranspose_nonsing_inv, hHh]
  have hc : ∀ A : Matrix (Fin n) (Fin n) ℂ, H⁻¹ * (H * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv, Matrix.one_mul]
  have hc' : ∀ A : Matrix (Fin n) (Fin n) ℂ, H * (H⁻¹ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv', Matrix.one_mul]
  have hM' : Mᴴ * (H * M) = (s : ℂ) • H := by rw [← Matrix.mul_assoc]; exact hM
  set D := H⁻¹ * Mᴴ * H with hD
  have hDM : D * M = (s : ℂ) • 1 := by
    rw [hD]; simp only [Matrix.mul_assoc]; rw [hM', Matrix.mul_smul, hHinv]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hMD : M * D = (s : ℂ) • 1 := by
    have h1 : ((s : ℂ)⁻¹ • D) * M = 1 := by
      rw [Matrix.smul_mul, hDM, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.mul_smul] at h2
    calc M * D = (s : ℂ) • ((s : ℂ)⁻¹ • (M * D)) := by
          rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
      _ = (s : ℂ) • 1 := by rw [h2]
  have hcomm : Commute D M := by
    show D * M = M * D
    rw [hDM, hMD]
  have hall : ∀ Y, Commute Y M → Commute Y (aeval M P) := fun Y hY =>
    SimNormSq.commute_aeval_of_commute hY P
  have hDW := hall D hcomm
  generalize hW : aeval M P = W at hP hDW ⊢
  have key : Commute (H⁻¹ * Wᴴ * H) M := by
    have h1 : Wᴴ * (H * (M * H⁻¹)) = H * (M * (H⁻¹ * Wᴴ)) := by
      have h0 := congrArg conjTranspose hDW.eq
      simp only [hD, conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
        Matrix.mul_assoc] at h0
      exact h0
    show H⁻¹ * Wᴴ * H * M = M * (H⁻¹ * Wᴴ * H)
    calc H⁻¹ * Wᴴ * H * M = H⁻¹ * (Wᴴ * (H * (M * H⁻¹))) * H := by
          simp only [Matrix.mul_assoc, hHinv, Matrix.mul_one]
      _ = H⁻¹ * (H * (M * (H⁻¹ * Wᴴ))) * H := by rw [h1]
      _ = M * (H⁻¹ * Wᴴ * H) := by
          simp only [Matrix.mul_assoc, hc]
  have hXW : Commute (H⁻¹ * Wᴴ * H) W := by
    have h4 := hall _ key
    rwa [hW] at h4
  have hX : (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W) = 0 := by
    calc (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W)
        = Wᴴ * H * (W * (H⁻¹ * Wᴴ * H)) * W := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
            Matrix.mul_assoc, hc]
      _ = Wᴴ * H * ((H⁻¹ * Wᴴ * H) * W) * W := by rw [← hXW.eq]
      _ = 0 := by simp only [Matrix.mul_assoc, hP, Matrix.mul_zero]
  have hX0 := SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hX
  have hW2 : Wᴴ * H * W = 0 := by
    have h3 : H * (H⁻¹ * Wᴴ * H * W) = Wᴴ * H * W := by simp only [Matrix.mul_assoc, hc']
    rw [← h3, hX0, Matrix.mul_zero]
  exact SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hW2

end GlobalTheory
end

section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
namespace GlobalTheory.HSAmp

theorem star_mulVec_single_dot (ι : Type) [Fintype ι] [DecidableEq ι]
    (T M : Matrix ι ι ℂ) (i : ι) :
    star (T *ᵥ Pi.single i 1) ⬝ᵥ M *ᵥ (T *ᵥ Pi.single i 1) = (Tᴴ * M * T) i i := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp [Matrix.mulVec_single, dotProduct_single]

theorem det_re_le_pow_mul_det_re (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (κ : ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hle : ∀ c : ι → ℂ, (star c ⬝ᵥ A *ᵥ c).re ≤ κ * (star c ⬝ᵥ B *ᵥ c).re) :
    A.det.re ≤ κ ^ Fintype.card ι * B.det.re := by
  obtain ⟨T, d, hT, hTB, hTA⟩ := GlobalTheory.T.exists_simultaneous_diagonalisation_posDef_hermitian ι B A hB hA.isHermitian
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).2 hT
  have hinj : Function.Injective T.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hTu

  have hcol : ∀ i, T *ᵥ Pi.single i 1 ≠ 0 := by
    intro i h
    have : Pi.single i (1 : ℂ) = 0 := hinj (by rw [h, Matrix.mulVec_zero])
    simpa using congrFun this i
  have hBi : ∀ i, star (T *ᵥ Pi.single i 1) ⬝ᵥ B *ᵥ (T *ᵥ Pi.single i 1) = 1 := by
    intro i; rw [star_mulVec_single_dot, hTB]; simp
  have hAi : ∀ i, star (T *ᵥ Pi.single i 1) ⬝ᵥ A *ᵥ (T *ᵥ Pi.single i 1) = (d i : ℂ) := by
    intro i; rw [star_mulVec_single_dot, hTA]; simp
  have hdpos : ∀ i, 0 < d i := by
    intro i
    have h := hA.dotProduct_mulVec_pos (hcol i)
    rw [hAi] at h
    exact_mod_cast h
  have hdle : ∀ i, d i ≤ κ := by
    intro i
    have h := hle (T *ᵥ Pi.single i 1)
    rw [hAi, hBi] at h
    simpa using h

  set t := T.det
  have hn : (Complex.normSq t : ℂ) = star t * t := Complex.normSq_eq_conj_mul_self
  have hdetB : (Complex.normSq t : ℂ) * B.det = 1 := by
    have := congrArg Matrix.det hTB
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
    rw [hn, ← this]; ring
  have hdetA : (Complex.normSq t : ℂ) * A.det = ((∏ i, d i : ℝ) : ℂ) := by
    have := congrArg Matrix.det hTA
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal] at this
    rw [hn, Complex.ofReal_prod, ← this]; ring
  have hpos : 0 < Complex.normSq t := Complex.normSq_pos.2 hT.ne_zero
  have hBre : Complex.normSq t * B.det.re = 1 := by
    have := congrArg Complex.re hdetB
    simpa [Complex.re_ofReal_mul] using this
  have hAre : Complex.normSq t * A.det.re = ∏ i, d i := by
    have := congrArg Complex.re hdetA
    rwa [Complex.re_ofReal_mul, Complex.ofReal_re] at this
  have hprod : ∏ i, d i ≤ κ ^ Fintype.card ι := by
    calc ∏ i, d i ≤ ∏ _i : ι, κ :=
          Finset.prod_le_prod₀ (fun i _ => (hdpos i).le) (fun i _ => hdle i)
      _ = κ ^ Fintype.card ι := by simp
  refine le_of_mul_le_mul_left ?_ hpos
  calc Complex.normSq t * A.det.re = ∏ i, d i := hAre
    _ ≤ κ ^ Fintype.card ι := hprod
    _ = Complex.normSq t * (κ ^ Fintype.card ι * B.det.re) := by
        rw [mul_left_comm, hBre, mul_one]

end GlobalTheory.HSAmp
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem finite_of_bounded_image_closure_finset :
    ∀ {V E : Type} [AddCommGroup V] [Module ℚ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] (Φ : V →+ E),
      (∀ (k : ℕ) (e : Fin k → V), LinearIndependent ℚ e → LinearIndependent ℝ (fun j => Φ (e j))) →
      ∀ (S : Finset V) (Y : Set V), Y ⊆ (AddSubgroup.closure (S : Set V) : Set V) →
        ∀ R : ℝ, (∀ y ∈ Y, ‖Φ y‖ ≤ R) → Y.Finite := by
  intro V E _ _ _ _ _ Φ hΦ S Y hY R hR
  set M : Submodule ℤ V := Submodule.span ℤ (S : Set V) with hMdef
  have hMY : Y ⊆ (M : Set V) := by
    intro y hy
    have := hY hy
    rw [← Submodule.span_int_eq_addSubgroupClosure] at this
    exact this
  haveI : Module.Finite ℤ M := Module.Finite.span_of_finite ℤ S.finite_toSet
  haveI : Module.IsTorsionFree ℤ V := .trans_faithfulSMul ℤ ℚ V
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ M
  set n := Module.finrank ℤ M
  let e : Fin n → V := fun j => (b j : V)
  have heZ : LinearIndependent ℤ e := b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have heQ : LinearIndependent ℚ e := (LinearIndependent.iff_fractionRing ℤ ℚ).1 heZ
  have heR := hΦ n e heQ
  let T : (Fin n → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ (fun j => Φ (e j))
  have hT : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 heR)
  obtain ⟨K, -, hK⟩ := T.exists_antilipschitzWith hT

  let f : V → (Fin n → ℤ) := fun y => if h : y ∈ M then fun j => b.repr ⟨y, h⟩ j else 0
  have hfy : ∀ y (h : y ∈ M), f y = fun j => b.repr ⟨y, h⟩ j := fun y h => by simp [f, h]
  have hinj : Set.InjOn f Y := by
    intro y hy z hz hyz
    have h1 := hMY hy
    have h2 := hMY hz
    rw [hfy y h1, hfy z h2] at hyz
    have : b.repr ⟨y, h1⟩ = b.repr ⟨z, h2⟩ := by
      ext j; exact congrFun hyz j
    have := b.repr.injective this
    simpa using congrArg Subtype.val this
  have hΦy : ∀ y (h : y ∈ M), Φ y = T (fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)) := by
    intro y h
    have hs' : y = ∑ j, b.repr ⟨y, h⟩ j • e j := by
      have := congrArg (Subtype.val : M → V) (b.sum_repr ⟨y, h⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    conv_lhs => rw [hs']

    simp [T, Fintype.linearCombination_apply, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
  set N : ℤ := ⌈(K : ℝ) * R⌉
  have hsub : f '' Y ⊆ Set.Icc (fun _ => -N) (fun _ => N) := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hMY hy
    rw [hfy y h]
    set c : Fin n → ℝ := fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)
    have hc : ‖c‖ ≤ (K : ℝ) * R := by
      have h1 := ZeroHomClass.bound_of_antilipschitz T hK c
      rw [← hΦy y h] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hR y hy) K.2)
    have hcj : ∀ j, |c j| ≤ (K : ℝ) * R := fun j => by
      have h0 : ‖c j‖ ≤ ‖c‖ := norm_le_pi_norm c j
      rw [Real.norm_eq_abs] at h0
      exact h0.trans hc
    constructor <;> intro j
    · have h3 : -((K : ℝ) * R) ≤ c j := (abs_le.1 (hcj j)).1
      have h4 : (-(N : ℝ)) ≤ c j := le_trans (neg_le_neg (Int.le_ceil _)) h3
      have h5 : ((-N : ℤ) : ℝ) ≤ ((b.repr ⟨y, h⟩ j : ℤ) : ℝ) := by push_cast; exact h4
      exact Int.cast_le.1 h5
    · have h4 : c j ≤ (N : ℝ) := ((abs_le.1 (hcj j)).2).trans (Int.le_ceil _)
      exact Int.cast_le.1 h4
  exact Set.Finite.of_finite_image ((Set.finite_Icc _ _).subset hsub) hinj

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.LKCx

theorem minpoly_separable_of_sq_zero_free
    (F C : Type) [Field F] [Ring C] [IsSimpleRing C] [Algebra F C] [FiniteDimensional F C]
    (n : ℕ) (σ : F →+* ℂ) (ψ : C →+* Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hψ : ∀ x : F, ψ (algebraMap F C x) = Matrix.scalar (Fin n) (σ x)) (c : C)
    (hc : ∀ P : Polynomial ℂ, Polynomial.aeval (ψ c) P * Polynomial.aeval (ψ c) P = 0 →
      Polynomial.aeval (ψ c) P = 0) :
    (minpoly F c).Separable := by
  haveI : CharZero F := (RingHom.charZero_iff σ.injective).2 inferInstance
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective ψ := ψ.injective
  have hcomp : ψ.comp (algebraMap F C) = (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).comp σ := by
    ext x
    simp only [RingHom.comp_apply, hψ, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    rfl
  have hev : ∀ Q : Polynomial F, ψ (Polynomial.aeval c Q) = Polynomial.aeval (ψ c) (Q.map σ) := by
    intro Q
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def,
      Polynomial.eval₂_map]
  have hint : IsIntegral F c := IsIntegral.of_finite F c
  have hm0 : minpoly F c ≠ 0 := minpoly.ne_zero hint
  rw [PerfectField.separable_iff_squarefree]
  intro g hg
  obtain ⟨h, hh⟩ := hg
  have hQ : Polynomial.aeval c (g * h) = 0 := by
    apply hinj
    rw [map_zero, hev]
    apply hc
    rw [← hev, ← map_mul, ← map_mul]
    have : g * h * (g * h) = minpoly F c * h := by rw [hh]; ring
    rw [this, map_mul, minpoly.aeval, zero_mul, map_zero]
  have hdvd : minpoly F c ∣ g * h := minpoly.dvd F c hQ
  have hgh0 : g * h ≠ 0 := by
    intro h0
    apply hm0
    rw [hh, mul_assoc, h0, mul_zero]
  rw [hh, mul_assoc] at hdvd
  have : g * (g * h) ∣ 1 * (g * h) := by rwa [one_mul]
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hgh0).1 this)

end GlobalTheory.LKCx
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.den_bound_combine_padic_primeToP : ∀ (p D K k : ℕ), p.Prime → ∀ q : ℚ, (∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ K * m : ℕ) : ℚ) * q = a) → (∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = a) → ∃ a : ℤ, ((D * p ^ K : ℕ) : ℚ) * q = a := by
  first | (exact @GlobalTheory.den_comb) | (exact GlobalTheory.den_comb) | (intros; apply GlobalTheory.den_comb  <;> assumption)
end
