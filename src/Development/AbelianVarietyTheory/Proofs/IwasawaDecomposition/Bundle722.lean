module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle708
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle714
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle717
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle718
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle686
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle712
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle715
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle697
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical


theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_isHomogeneous_cmType : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), (rootDiscr Dw.mult).IsHomogeneous (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2)) := by
  first | exact @GlobalTheory.GrassTop.rootDiscr_isHomogeneous | exact GlobalTheory.GrassTop.rootDiscr_isHomogeneous | (intros; apply GlobalTheory.GrassTop.rootDiscr_isHomogeneous <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

noncomputable section
namespace GlobalTheory.PointChernScale

open Matrix
open scoped ComplexOrder

theorem curv_tau {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η =
      -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := GlobalTheory.T.chernCurvature_modelGram_conjMulTranspose_inv Z w ξ η hw

theorem curv_tauBar {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := GlobalTheory.T.chernCurvature_modelGram_conjugateEmbedding Z w ξ η hw

theorem exists_factor {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ) (hP : P.PosDef) :
    ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := GlobalTheory.T.exists_isUnit_det_conjTranspose_mul_eq_of_posDef P hP

theorem posDef_swap {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    (1 - z * zᴴ).PosDef := GlobalTheory.T.posDef_one_sub_mul_conjTranspose_of_posDef_swap z h

theorem chernPoly_conj {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n)
    (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (hS : IsUnit S.det)
    (h : ∀ a b, curv F v (coordVec a) (coordVec b) =
      S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) (k : ℕ) :
    chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
      (chernPoly F v' k) := GlobalTheory.T.chernPoly_conj_linearSubst_curvature F v v' J S hS h k

theorem chernPoly_reindex {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) : chernPoly (fun u => reindex e e (F u)) v k = chernPoly F v k := GlobalTheory.T.chernFormPolyCoeff_reindex_frame e F v k

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def zLin {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (σ : GlobalTheory.AllWt.Psi H) : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin Dw.p) (Fin Dw.q) ℂ where
  toFun u := coordOf ix u σ
  map_add' u v := by ext i j; simp [coordOf]
  map_smul' c u := by ext i j; simp [coordOf]

theorem zLin_apply {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (σ : GlobalTheory.AllWt.Psi H) (u : ReciprocityTheory.L2DbarEstimates.V n) : zLin ix σ u = coordOf ix u σ := rfl

def jMat {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (A : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.p) ℂ) (B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun c a =>
  (A (ix c).1 * coordOf ix (coordVec a) (ix c).1 * B (ix c).1) (ix c).2.1 (ix c).2.2

theorem zLin_jMat {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (A : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.p) ℂ) (B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ)
    (σ : GlobalTheory.AllWt.Psi H) (a : Fin n) :
    zLin ix σ (∑ c, jMat ix A B c a • coordVec c) = A σ * zLin ix σ (coordVec a) * B σ := by
  ext i j
  change (∑ c, jMat ix A B c a • coordVec c) (ix.symm (σ, i, j)) = _
  simp [WithLp.ofLp_sum, Finset.sum_apply, jMat, zLin_apply, Pi.single_apply]

theorem conj_tau {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w : ReciprocityTheory.L2DbarEstimates.V n)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (J : Matrix (Fin n) (Fin n) ℂ)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) (hA : IsUnit A.det) (hAA : Aᴴ * A = (1 - Z w * (Z w)ᴴ)⁻¹)
    (hB : B * Bᴴ = (1 - (Z w)ᴴ * Z w)⁻¹) (hJ : ∀ a, Z (∑ c, J c a • coordVec c) = A * Z (coordVec a) * B)
    (a b : Fin n) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w (coordVec a) (coordVec b) =
      A⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
        curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 (coordVec c) (coordVec d)) * A := by
  have h0 : (1 - (Z 0)ᴴ * Z 0).PosDef := by simpa using (PosDef.one : (1 : Matrix (Fin q) (Fin q) ℂ).PosDef)
  have hsum : (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
      curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 (coordVec c) (coordVec d)) =
      -(Z (∑ c, J c a • coordVec c) * (Z (∑ d, J d b • coordVec d))ᴴ) := by
    have hc : ∀ ξ η, curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 ξ η = -(Z ξ * (Z η)ᴴ) := by
      intro ξ η
      rw [curv_tau Z 0 ξ η h0]
      simp

    simp only [hc, map_sum, map_smul, conjTranspose_sum, conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_neg, Finset.sum_neg_distrib, neg_inj]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]; rfl
  rw [hsum, hJ, hJ, curv_tau Z w _ _ hw, ← hAA, ← hB]
  simp only [conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
    nonsing_inv_mul_cancel_left _ _ hA]

theorem conj_tauBar {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w : ReciprocityTheory.L2DbarEstimates.V n)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (J : Matrix (Fin n) (Fin n) ℂ)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) (hB0 : IsUnit B.det) (hAA : Aᴴ * A = (1 - Z w * (Z w)ᴴ)⁻¹)
    (hB : B * Bᴴ = (1 - (Z w)ᴴ * Z w)⁻¹) (hJ : ∀ a, Z (∑ c, J c a • coordVec c) = A * Z (coordVec a) * B)
    (a b : Fin n) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w (coordVec a) (coordVec b) =
      (Bᵀ)⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
        curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 (coordVec c) (coordVec d)) * Bᵀ := by
  have h0 : (1 - (Z 0)ᴴ * Z 0).PosDef := by simpa using (PosDef.one : (1 : Matrix (Fin q) (Fin q) ℂ).PosDef)
  have hsum : (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
      curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 (coordVec c) (coordVec d)) =
      -((Z (∑ d, J d b • coordVec d))ᴴ * Z (∑ c, J c a • coordVec c))ᵀ := by
    have hc : ∀ ξ η, curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 ξ η = -((Z η)ᴴ * Z ξ)ᵀ := by
      intro ξ η
      rw [curv_tauBar Z 0 ξ η h0]
      simp

    simp only [hc, map_sum, map_smul, conjTranspose_sum, conjTranspose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_neg,
    Finset.sum_neg_distrib, neg_inj, transpose_sum, transpose_smul]
    simp only [Finset.smul_sum, smul_smul]
    rfl
  rw [hsum, hJ, hJ, curv_tauBar Z w _ _ hw, ← hAA, ← hB, ← transpose_nonsing_inv, Matrix.mul_neg,
    Matrix.neg_mul, neg_inj, ← transpose_mul, ← transpose_mul]
  congr 1
  simp only [conjTranspose_mul, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hB0]

theorem chernPoly_model_eq_subst {H : Host E} (Dw : Datum H) {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n) (hw : InDom (coordOf ix w)) :
    ∃ J : Matrix (Fin n) (Fin n) ℂ, ∀ (τ : E →+* ℂ) (k : ℕ),
      chernPoly (fun u => modelGram H Dw (coordOf ix u) τ) w k =
        aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
          (chernPoly (fun u => modelGram H Dw (coordOf ix u) τ) 0 k) := by
  have hP : ∀ σ, (1 - coordOf ix w σ * (coordOf ix w σ)ᴴ)⁻¹.PosDef := fun σ => (posDef_swap _ (hw σ)).inv
  have hQ : ∀ σ, (1 - (coordOf ix w σ)ᴴ * coordOf ix w σ)⁻¹.PosDef := fun σ => (hw σ).inv
  choose A hA hAA using fun σ => exists_factor _ (hP σ)
  choose A' hA' hAA' using fun σ => exists_factor _ (hQ σ)
  let B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ := fun σ => (A' σ)ᴴ
  have hB : ∀ σ, B σ * (B σ)ᴴ = (1 - (coordOf ix w σ)ᴴ * coordOf ix w σ)⁻¹ := fun σ => by
    simp only [B, conjTranspose_conjTranspose]; exact hAA' σ
  have hB0 : ∀ σ, IsUnit (B σ).det := fun σ => by
    simp only [B, det_conjTranspose]; exact (hA' σ).star
  refine ⟨jMat ix A B, fun τ k => ?_⟩
  by_cases h : τ (H.rt : E) = H.rt0
  · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun u =>
        reindex (finCongr (mult_of_mem Dw h).symm) (finCongr (mult_of_mem Dw h).symm)
          ((1 - (zLin ix ⟨τ, h⟩ u).map (starRingEnd ℂ) * (zLin ix ⟨τ, h⟩ u)ᵀ)⁻¹) := by
      funext u; simp only [modelGram, dif_pos h]; rfl
    rw [e, chernPoly_reindex, chernPoly_reindex]
    exact chernPoly_conj _ w 0 _ (A ⟨τ, h⟩) (hA _)
      (conj_tau (zLin ix ⟨τ, h⟩) w (A _) (B _) _ (hw _) (hA _) (hAA _) (hB _) (zLin_jMat ix A B _)) k
  · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
    · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun u =>
          reindex (finCongr (mult_of_not_mem Dw h).symm) (finCongr (mult_of_not_mem Dw h).symm)
            ((1 - (zLin ix ⟨conjEmb τ, h'⟩ u)ᴴ * zLin ix ⟨conjEmb τ, h'⟩ u)⁻¹) := by
        funext u; simp only [modelGram, dif_neg h, dif_pos h']; rfl
      rw [e, chernPoly_reindex, chernPoly_reindex]
      exact chernPoly_conj _ w 0 _ (B _)ᵀ (by rw [det_transpose]; exact hB0 _)
        (conj_tauBar (zLin ix ⟨conjEmb τ, h'⟩) w (A _) (B _) _ (hw _) (hB0 _) (hAA _) (hB _)
          (zLin_jMat ix A B _)) k
    · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun _ => 1 := by
        funext u; simp only [modelGram, dif_neg h, dif_neg h']
      have hc : ∀ v, chernPoly (fun _ : ReciprocityTheory.L2DbarEstimates.V n => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) v k =
          (1 : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)).coeff k := by
        intro v
        have h0 : curvPoly (fun _ : ReciprocityTheory.L2DbarEstimates.V n => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) v = 0 := by
          ext i j; simp [curvPoly]
        simp [chernPoly, h0, Matrix.charpolyRev]
      rw [e, hc, hc, Polynomial.coeff_one]
      split_ifs <;> simp

end GlobalTheory.PointChernScale


open GlobalTheory.PointChernScale in
theorem GlobalTheory.PointChern.chernTop_model_eq_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) →
    ∃ κ : ℝ, ∀ R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ,
      chernTop R (fun u => modelGram H Dw (coordOf ix u)) w = κ * chernTop R (fun u => modelGram H Dw (coordOf ix u)) 0 := by
  intro E _ _ _ H Dw n ix w hw
  obtain ⟨J, hJ⟩ := chernPoly_model_eq_subst Dw ix w hw
  refine ⟨Complex.normSq J.det, fun R => ?_⟩
  let φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    aeval fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)
  have hR : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) w x.2) R =
      φ (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) R) := by
    have := congrArg (fun f => f R) (MvPolynomial.comp_aeval (R := ℝ)
      (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) (φ.restrictScalars ℝ))
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
    rw [this]
    exact congrArg (fun f => (aeval f R : MvPolynomial (Fin n × Fin n) ℂ)) (funext fun x => hJ x.1 x.2)
  simp only [chernTop]
  rw [hR, GlobalTheory.GoodMetric.topCoeff_subst_conj, Complex.mul_conj, Complex.re_ofReal_mul]
  ring
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.isSmoothAdmissibleFan_of_cellMult_one_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → maxMult H.bar q φ ≤ 1 → IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ := by
  first | exact @GlobalTheory.PolFan.smoothEnd | exact GlobalTheory.PolFan.smoothEnd | (intros; apply GlobalTheory.PolFan.smoothEnd <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.maxSimplicialCellMultiplicity_lt_top_of_isPolyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)), IsPolyFan H.bar q φ → maxMult H.bar q φ < ⊤ := by
  first | exact @GlobalTheory.PolFan.maxMult_lt_top | exact GlobalTheory.PolFan.maxMult_lt_top | (intros; apply GlobalTheory.PolFan.maxMult_lt_top <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.SmoothEnd

theorem eq_of_isPrim_of_toReal_eq_smul : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (x y : LinearMap.BilinForm ℤ X)
    (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), IsPrim bar (⟨x, hx⟩ : balForms bar X) →
    IsPrim bar (⟨y, hy⟩ : balForms bar X) → ∀ b : ℝ, 0 < b → toReal x = b • toReal y → x = y := by
  intro O _ bar X _ _ x y hx hy px py b hb h
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact not_isPrim_zero (bar := bar) py
  obtain ⟨a, c, hac⟩ : ∃ a c, y a c ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy0 (LinearMap.ext₂ hc)
  have hR : ∀ u v, (x u v : ℝ) = b * (y u v : ℝ) := fun u v => by
    have := LinearMap.congr_fun₂ h u v
    simpa [toReal_apply] using this
  have hacR : (y a c : ℝ) ≠ 0 := by exact_mod_cast hac
  have hxac : x a c ≠ 0 := by
    have : (x a c : ℝ) ≠ 0 := by rw [hR]; exact mul_ne_zero hb.ne' hacR
    exact_mod_cast this
  have habs : |(x a c : ℝ)| = b * |(y a c : ℝ)| := by
    rw [hR, abs_mul, abs_of_pos hb]
  apply eq_of_isPrim hx hy px py (k := (y a c).natAbs) (n := (x a c).natAbs)
    (Int.natAbs_pos.2 hac) (Int.natAbs_pos.2 hxac)
  apply LinearMap.ext₂
  intro u v
  simp only [LinearMap.smul_apply, smul_eq_mul, Int.natCast_natAbs]
  have e : |(y a c : ℝ)| * (x u v : ℝ) = |(x a c : ℝ)| * (y u v : ℝ) := by
    rw [hR u v, habs]; ring
  exact_mod_cast e

end GlobalTheory.PolFan.SmoothEnd
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.StarLab

variable {O : Type} [CommRing O]

def IsCentreRay (w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∃ β : LinearMap.BilinForm ℤ X, w.evalZ β = 1 ∧ ∀ a b, t * B a b = β a b

theorem isCentreRay_comp (w : InvFun O) {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] [Module.Projective O X₁] {r : X →ₗ[O] X₁}
    (hr : Function.Surjective r) (B : X₁ → X₁ → ℝ) :
    IsCentreRay w X (fun a b => B (r a) (r b)) ↔ IsCentreRay w X₁ B := by
  constructor
  · rintro ⟨t, ht, β, hw, hβ⟩
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hs' : ∀ x, r (s x) = x := fun x => LinearMap.congr_fun hs x
    refine ⟨t, ht, pull s β, ?_, fun x y => ?_⟩
    · have e : pull r (pull s β) = β := LinearMap.ext₂ fun a b => by
        have h1 := hβ (s (r a)) (s (r b))
        have h2 := hβ a b
        simp only [hs'] at h1
        simp only [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [← evalZ_pull w hr, e, hw]
    · have := hβ (s x) (s y)
      simp only [hs'] at this
      simpa only [pull_apply] using this
  · rintro ⟨t, ht, β, hw, hβ⟩
    exact ⟨t, ht, pull r β, by rw [evalZ_pull w hr, hw], fun a b => by simp only [pull_apply, hβ]⟩


open Classical in
def starLab (lab w : InvFun O) : InvFun O where
  toFun n B := if IsCentreRay w (Fin n → O) B then -1 else Real.exp (lab.toFun n B) - 1
  inv n m r hr B := by
    simp only [isCentreRay_comp w hr B, lab.inv n m r hr B]
  zero B := by
    have : ¬ IsCentreRay w (Fin 0 → O) B := by
      rintro ⟨t, -, β, hw, -⟩
      rw [InvFun.evalZ, w.eval_of_subsingleton] at hw
      norm_num at hw
    rw [if_neg this, lab.zero, Real.exp_zero, sub_self]


open Classical in
theorem starLab_eval (lab w : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (B : X → X → ℝ) :
    (starLab lab w).eval X B = if IsCentreRay w X B then -1 else Real.exp (lab.eval X B) - 1 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [(starLab lab w).eval_eq hr, lab.eval_eq hr]
  simp only [starLab, isCentreRay_comp w hr B]

variable {X : Type} [AddCommGroup X]


open Classical in
theorem starLab_evalZ_of_eq_one (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    {β : LinearMap.BilinForm ℤ X} (h : w.evalZ β = 1) : (starLab lab w).evalZ β = -1 := by
  rw [InvFun.evalZ, starLab_eval, if_pos ⟨1, one_pos, β, h, fun a b => one_mul _⟩]

theorem starLab_evalZ_of_not (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    {β : LinearMap.BilinForm ℤ X} (h : ¬ IsCentreRay w X (fun a b => (β a b : ℝ))) :
    (starLab lab w).evalZ β = Real.exp (lab.evalZ β) - 1 := by
  rw [InvFun.evalZ, starLab_eval, if_neg h]; rfl

theorem isCentreRay_smul_iff (w : InvFun O) [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) {k : ℕ}
    (hk : 0 < k) :
    IsCentreRay w X (fun a b => ((((k : ℤ) • β) a b : ℤ) : ℝ)) ↔ IsCentreRay w X (fun a b => (β a b : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨t, ht, β', hw, h⟩
    refine ⟨t * k, mul_pos ht hk', β', hw, fun a b => ?_⟩
    rw [← h a b]; simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]; ring
  · rintro ⟨t, ht, β', hw, h⟩
    refine ⟨t / k, div_pos ht hk', β', hw, fun a b => ?_⟩
    rw [← h a b]; simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]; field_simp

theorem starLab_evalZ_smul (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    (β : LinearMap.BilinForm ℤ X) {k : ℕ} (hk : 0 < k) (hlab : lab.evalZ ((k : ℤ) • β) = lab.evalZ β) :
    (starLab lab w).evalZ ((k : ℤ) • β) = (starLab lab w).evalZ β := by
  unfold InvFun.evalZ at hlab ⊢
  rw [starLab_eval, starLab_eval, hlab]
  by_cases hc : IsCentreRay w X (fun a b => (β a b : ℝ))
  · rw [if_pos ((isCentreRay_smul_iff w β hk).2 hc), if_pos hc]
  · rw [if_neg (mt (isCentreRay_smul_iff w β hk).1 hc), if_neg hc]

theorem exists_of_isCentreRay {bar : O → O} (w : InvFun O) [Module O X] [Module.Finite O X]
    {β : LinearMap.BilinForm ℤ X} (hb : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y)
    (h : IsCentreRay w X (fun a b => (β a b : ℝ))) :
    ∃ t : ℝ, 0 < t ∧ ∃ β' : LinearMap.BilinForm ℤ X, β' ∈ balForms bar X ∧ (∀ y, 0 ≤ β' y y) ∧ w.evalZ β' = 1 ∧
      toReal β' = t • toReal β := by
  obtain ⟨t, ht, β', hw, h⟩ := h
  simp only at h
  refine ⟨t, ht, β', ⟨fun y z => ?_, fun a y z => ?_⟩, fun y => ?_, hw, LinearMap.ext₂ fun a b => ?_⟩
  · have : (β' y z : ℝ) = β' z y := by rw [← h, ← h, hb.1 y z]
    exact_mod_cast this
  · have : (β' (a • y) z : ℝ) = β' y (bar a • z) := by rw [← h, ← h, hb.2 a y z]
    exact_mod_cast this
  · have : (0 : ℝ) ≤ β' y y := by rw [← h]; exact mul_nonneg ht.le (by exact_mod_cast hp y)
    exact_mod_cast this
  · simp [← h]

theorem InRCone.of_toReal_eq_smul {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β β' : LinearMap.BilinForm ℤ X}
    (hβ : InRCone γ β) {t : ℝ} (ht : 0 ≤ t) (e : toReal β' = t • toReal β) : InRCone γ β' := by
  obtain ⟨c, hc, e'⟩ := hβ
  refine ⟨fun i => t * c i, fun i => mul_nonneg ht (hc i), ?_⟩
  rw [e, e', Finset.smul_sum]
  simp only [smul_smul]

theorem exists_isFaceCut {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hh : ∀ j, 0 ≤ h (γ j)) : ∃ (m' : ℕ) (s : Fin m' ↪ Fin m), IsFaceCut γ s h := by
  classical
  let e := Fintype.equivFin {j : Fin m // h (γ j) = 0}
  refine ⟨_, e.symm.toEmbedding.trans (Function.Embedding.subtype _), hh, fun j => ⟨fun hj => ⟨e ⟨j, hj⟩, by simp⟩, ?_⟩⟩
  rintro ⟨i, rfl⟩
  exact (e.symm i).2

theorem inRCone_face {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hf : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β)
    (h0 : h β = 0) : InRCone (fun j => γ (s j)) β := by
  classical
  obtain ⟨c, hc, e⟩ := hβ
  have h1 := apply_eq_of_toReal_eq e h
  rw [h0, Int.cast_zero] at h1
  have hz : ∀ i, c i * (h (γ i) : ℝ) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hc i) (by exact_mod_cast hf.1 i))).1 h1.symm i
      (Finset.mem_univ _)
  have hc0 : ∀ i, i ∉ Set.range s → c i = 0 := fun i hi => by
    have hpos : (h (γ i) : ℝ) ≠ 0 := by exact_mod_cast fun h' => hi ((hf.2 i).1 h')
    exact (mul_eq_zero.1 (hz i)).resolve_right hpos
  refine ⟨fun j => c (s j), fun j => hc _, ?_⟩
  rw [e]
  have hm := Finset.sum_map Finset.univ s (fun i => c i • toReal (γ i))
  rw [← hm]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [hc0 i (fun ⟨j, hj⟩ => hi (Finset.mem_map.2 ⟨j, Finset.mem_univ _, hj⟩)), zero_smul]

theorem IsFaceCut.apply_eq_zero {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hf : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X}
    (hβ : InRCone (fun j => γ (s j)) β) : h β = 0 := by
  obtain ⟨c, hc, e⟩ := hβ
  have h1 := apply_eq_of_toReal_eq e h
  simp only [(hf.2 _).2 ⟨_, rfl⟩, Int.cast_zero, mul_zero, Finset.sum_const_zero] at h1
  exact_mod_cast h1

theorem inRCone_of_sub {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (s : Fin m' → Fin m)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone (fun j => γ (s j)) β) : InRCone γ β :=
  inRCone_trans (fun j => inRCone_self γ (s j)) hβ

theorem isTwInv_starLab {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {lab w : InvFun (𝓞 E)}
    (hl : IsTwInv H lab) (hw : IsTwInv H w) : IsTwInv H (starLab lab w) := by
  intro σ hσ n B
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] (Fin n → 𝓞 E) :=
    AddEquiv.toIntLinearEquiv (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)
  have he : ∀ a, e a = fun i => σ (a i) := fun a => rfl
  have hwt : ∀ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E),
      w.evalZ (β.compl₁₂ e.toLinearMap e.toLinearMap) = w.evalZ β := fun β => by
    simp only [InvFun.evalZ, InvFun.eval_pi, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, he]
    exact hw σ hσ n (fun a b => (β a b : ℝ))
  have key : IsCentreRay w (Fin n → 𝓞 E) (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ↔
      IsCentreRay w (Fin n → 𝓞 E) B := by
    constructor
    · rintro ⟨t, ht, β, h1, h2⟩
      refine ⟨t, ht, β.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, ?_, fun a b => ?_⟩
      · rw [← hwt, ← h1]
        congr 1
        ext a b
        simp
      · have := h2 (e.symm a) (e.symm b)
        simp only [← he, LinearEquiv.apply_symm_apply] at this
        simpa using this
    · rintro ⟨t, ht, β, h1, h2⟩
      exact ⟨t, ht, β.compl₁₂ e.toLinearMap e.toLinearMap, by rw [hwt, h1], fun a b => by
        simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, he, h2]⟩
  have hlab := hl σ hσ n B
  simp only [starLab]
  by_cases hc : IsCentreRay w (Fin n → 𝓞 E) B
  · rw [if_pos (key.2 hc), if_pos hc]
  · rw [if_neg (mt key.1 hc), if_neg hc, hlab]

end GlobalTheory.PolFan.StarLab
end
end
