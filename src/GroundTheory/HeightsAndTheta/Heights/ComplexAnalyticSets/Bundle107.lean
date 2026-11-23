module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StokesOffDiscriminantWindow
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartDehomog
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMassFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle105
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import Mathlib.Topology.Separation.CompletelyRegular
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle106
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
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiffMap

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ImageDimLe.proof : ImageDimLe.Statement := by
  intro n m P Q hP
  set φ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mkₐ ℂ P).comp (aeval Q) with hφ
  have : P.IsPrime := hP
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨s, hs1, hs2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ)
  obtain ⟨t, ht1, ht2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin n) ℂ ⧸ P)
  have hle : Algebra.trdeg ℂ (MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ) ≤
      Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) :=
    trdeg_le_of_injective (Ideal.kerLiftAlg φ) (Ideal.kerLiftAlg_injective φ)
  rw [hs2, ht2] at hle
  have hst : s ≤ t := by exact_mod_cast hle
  rw [hs1, ht1]
  exact_mod_cast hst

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets

noncomputable section

theorem le_of_ringKrullDim_quotient {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) : e + 1 ≤ n := by
  have h := ringKrullDim_quotient_le J
  rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  exact_mod_cast h

theorem coneBall_hausdorff_lt_top (hMF : MassFinite.Statement) {n e : ℕ} (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} < ⊤ := by
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  let P : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 h.matᵀ)
  let Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 (h.matᵀ)⁻¹)
  have hsub : {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} ⊆
      Q '' (zeroSetEuc J ∩ ball 0 (‖P‖ + 1)) := by
    rintro z ⟨hz, hzJ⟩
    refine ⟨P z, ⟨fun q hq => hzJ q hq, ?_⟩, ?_⟩
    · rw [mem_ball_zero_iff]
      calc ‖P z‖ ≤ ‖P‖ * ‖z‖ := P.le_opNorm z
        _ ≤ ‖P‖ * 1 := by gcongr
        _ < ‖P‖ + 1 := by linarith
    · ext i
      simp [P, Q, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
  have hd : (0 : ℝ) ≤ ((2 * (e + 1) : ℕ) : ℝ) := by positivity
  calc _ ≤ Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (Q '' (zeroSetEuc J ∩ ball 0 (‖P‖ + 1))) :=
        measure_mono hsub
    _ ≤ (‖Q‖₊ : ENNReal) ^ ((2 * (e + 1) : ℕ) : ℝ) *
          Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (zeroSetEuc J ∩ ball 0 (‖P‖ + 1)) :=
        Q.lipschitz.hausdorffMeasure_image_le hd _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hd ENNReal.coe_ne_top)
        (hMF n (e + 1) J hJ (by exact_mod_cast hdim) _)

theorem integral_line_gram {n : ℕ} (e : ℕ) (h : HermNorm n) (g : (Fin n → ℂ) → ℝ)
    (hg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) (x : Fin n → ℂ) (hx : x ≠ 0) (G : ℝ) :
    ∫ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => g (h.pointOf z))
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        (g x * ((e.factorial : ℝ) / Real.pi ^ e * G / h.dualNorm x ^ (2 * (e + 1)))) := by
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  have hinv : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hMx : (h.matᵀ)⁻¹ *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    rw [← hinv, h0, Matrix.mulVec_zero]
  set ρ := ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ with hρ_def
  have hρx : h.dualNorm x = ρ := by
    rw [hρ_def, EuclideanSpace.norm_eq]
    rfl
  have hρ : 0 < ρ := by
    rw [hρ_def, norm_pos_iff]
    intro h0
    exact hMx (by simpa using congrArg WithLp.ofLp h0)
  have hpt : ∀ t : ℂ, h.pointOf (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = t • x := by
    intro t
    have : (fun i => (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) i) = t • ((h.matᵀ)⁻¹ *ᵥ x) := by
      ext i
      simp
    simp only [HermNorm.pointOf, this, Matrix.mulVec_smul, hinv]
  have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => g (h.pointOf z)) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
      fun t => (g x * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht
    have hiff : ‖t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
      rw [norm_smul, lt_div_iff₀ hρ]
    by_cases hb : ‖t‖ < 1 / ρ
    · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
        indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hg t x ht]
      ring
    · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
        indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
      ring
  rw [integral_congr_ae hae, integral_const_mul,
    integral_indicator_ball_norm_pow e (by positivity), hρx]
  rw [one_div, inv_pow, Nat.factorial_succ]
  have hρ' : ρ ^ (2 * (e + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets StokesOffDiscriminant
open scoped ContDiff Manifold

noncomputable section

theorem StokesOffDiscriminant.proof : StokesOffDiscriminant.Statement := by
  intro n d J A P _ _ _ _ hsheet F G φ hF hG hφ hFc ⟨U, hUo, hPU, hFU⟩
  set K := closure {x | x ∈ zeroSet J ∧ F x ≠ 0} with hKdef
  have hKZ : K ⊆ zeroSet J :=
    closure_minimal (by exact fun x hx => hx.1) (SheetSumMeasurable.isClosed_zeroSet J)
  have hKU : K ⊆ Uᶜ :=
    closure_minimal (fun x hx hxU => hx.2 (hFU x ⟨hxU, hx.1⟩)) hUo.isClosed_compl
  have hKc : IsCompact K := hFc.of_isClosed_subset isClosed_closure (closure_mono fun x hx => hx.2)
  have hwin : ∀ x : K, ∃ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (V : Set (Fin (d + 1) → ℂ))
      (W : Set (Fin n → ℂ)), IsOpen V ∧ IsOpen W ∧ (x : Fin n → ℂ) ∈ W ∧ DifferentiableOn ℂ s V ∧
        (∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
        ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ V ∧ IsSheetAt J A x' s := by
    rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := hsheet x (hKZ hx) fun h => hKU hx (hPU h)
    exact ⟨s, window_of_sheet hs⟩
  choose s V W hVo hWo hxW hsd hsec hWs using hwin
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover W hWo fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin n → ℂ) isClosed_closure
    (fun i : t => W i.1) (fun i => hWo i.1) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  have hρs : ∀ i, ContDiff ℝ ∞ (ρ i) := fun i => contMDiff_iff_contDiff.1 (ρ i).contMDiff
  set f : t → (Fin n → ℂ) → ℝ := fun i x => ρ i x * F x with hfdef
  have hsum : ∀ x ∈ zeroSet J, F x = ∑ i, f i x := by
    intro x hxZ
    by_cases hK : x ∈ K
    · have h1 := ρ.sum_eq_one hK
      rw [finsum_eq_sum_of_fintype] at h1
      simp only [hfdef, ← Finset.sum_mul, h1, one_mul]
    · have hF0 : F x = 0 := by_contra fun h => hK (subset_closure ⟨hxZ, h⟩)
      simp [hfdef, hF0]
  have hfs : ∀ i, SmoothNear (zeroSet J) (f i) := by
    obtain ⟨O, hO, hZO, hFO⟩ := hF
    exact fun i => ⟨O, hO, hZO, (hρs i).contDiffOn.mul hFO⟩
  have hfW : ∀ i, tsupport (f i) ⊆ W i.1 := fun i => tsupport_mul_subset_left.trans (hρ i)
  have hpiece := fun i : t => window_stokes (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G φ
    (hfs i) hG hφ hFc.mul_left (hfW i)
  have hL : ∀ y, chartDens J A F (vecCons G φ) y = ∑ i, chartDens J A (f i) (vecCons G φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => f i x * ReciprocityTheory.AnForm.maDens (fun k => vecCons G φ k ∘ s') y) (by
        intro x hx s' _
        rw [hsum x hx.1, Finset.sum_mul])
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_weight_window (hsec i.1) (hWs i.1) (f i) (hfW i) _ y)
  have hR : ∀ y, chartDens J A G (vecCons F φ) y = ∑ i, chartDens J A G (vecCons (f i) φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => G x * ReciprocityTheory.AnForm.maDens (fun k => vecCons (f i) φ k ∘ s') y) (by
        rintro x ⟨-, rfl⟩ s' hs'
        rw [maDens_sheet_finset_sum Finset.univ F f φ hs' hsum fun i _ => hfs i, Finset.mul_sum])
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_cons_window (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G (hfW i) φ y)
  unfold chartInt
  simp only [hL, hR]
  rw [integral_finsetSum _ fun i _ => (hpiece i).2.1, integral_finsetSum _ fun i _ => (hpiece i).2.2]
  exact Finset.sum_congr rfl fun i _ => (hpiece i).1

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Set ComplexSets

noncomputable section

namespace ConeSliceSheetParam

theorem eval_sup_span {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {f : MvPolynomial (Fin n) ℂ}
    {x : Fin n → ℂ} (hJ : ∀ q ∈ J, eval x q = 0) (hf : eval x f = 0) :
    ∀ q ∈ J ⊔ Ideal.span {f}, eval x q = 0 := by
  intro q hq
  have hle : J ⊔ Ideal.span {f} ≤ RingHom.ker (eval x) :=
    sup_le (fun q hq => RingHom.mem_ker.2 (hJ q hq))
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 (RingHom.mem_ker.2 hf)))
  exact RingHom.mem_ker.1 (hle hq)

theorem eval_smul_of_isHomogIdeal {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsHomogIdeal J)
    {x : Fin n → ℂ} (hx : ∀ q ∈ J, eval x q = 0) (t : ℂ) : ∀ q ∈ J, eval (t • x) q = 0 := by
  intro q hq

  rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i q), hx _ (hJ q hq i), mul_zero]

theorem eval_linForm_smul {n : ℕ} (ℓ : Fin n → ℂ) (t : ℂ) (x : Fin n → ℂ) :
    eval (t • x) (linForm ℓ) = t * eval x (linForm ℓ) := by
  rw [eval_smul_of_isHomogeneous (SliceIdeal.isHomogeneous_linForm ℓ), pow_one]

theorem slice_isPrime {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ} (hJ : IsProjPrime J)
    (hℓ : linForm ℓ ∉ J) : (J ⊔ Ideal.span {linForm ℓ - 1}).IsPrime := by
  have hP := hJ.isPrime
  have hdeh : ∀ (G : MvPolynomial (Fin n) ℂ) (d : ℕ), G.IsHomogeneous d →
      G ∈ J ⊔ Ideal.span {linForm ℓ - 1} → G ∈ J :=
    fun G d hG hm => ChartDehomog.proof ℂ n J ℓ G d hP hJ.isHomog hℓ hG hm
  have hspan : Ideal.span {linForm ℓ - 1} ≤ J ⊔ Ideal.span {linForm ℓ - 1} := le_sup_right
  refine Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {a b} hab => ?_⟩
  · exact hP.ne_top ((Ideal.eq_top_iff_one J).mpr
      (hdeh 1 0 (isHomogeneous_one _ _) (htop ▸ Submodule.mem_top)))
  obtain ⟨da, A, hA', hAa⟩ := SliceIdeal.exists_homogeneous_sub_mem ℓ a
  obtain ⟨db, B, hB', hBb⟩ := SliceIdeal.exists_homogeneous_sub_mem ℓ b
  have hAB : A * B ∈ J ⊔ Ideal.span {linForm ℓ - 1} := by
    have h : A * B = (A - a) * B + a * (B - b) + a * b := by ring
    rw [h]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hspan (Ideal.mul_mem_right _ _ hAa))
      (hspan (Ideal.mul_mem_left _ _ hBb))) hab
  rcases hP.mem_or_mem (hdeh _ _ (hA'.mul hB') hAB) with h | h
  · left
    have e : a = A - (A - a) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left h) (hspan hAa)
  · right
    have e : b = B - (B - b) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left h) (hspan hBb)

end ConeSliceSheetParam


open ConeSliceSheetParam in
theorem ConeSliceSheetParam.proof (hCov : DiscriminantSheetCover.Statement) :
    ConeSliceSheetParam.Statement := by
  classical
  intro n e h J ℓ A hJ hdim hℓ hA
  have hP := hJ.isPrime
  obtain ⟨P, U, D, N, s, hP0, hUD, hdisj, hbad, hnull, hfib⟩ :=
    hCov n e _ A (slice_isPrime hJ hℓ) (SliceDim.proof n e J ℓ hJ hdim hℓ) hA
  set J' := J ⊔ Ideal.span {linForm ℓ - 1} with hJ'
  set M := (h.matᵀ)⁻¹ with hM
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det

  have hslice : ∀ x ∈ zeroSet J', (∀ q ∈ J, eval x q = 0) ∧ eval x (linForm ℓ) = 1 := by
    intro x hx
    refine ⟨fun q hq => hx q (Ideal.mem_sup_left hq), ?_⟩
    have h1 := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rwa [map_sub, map_one, sub_eq_zero] at h1
  have hval : ∀ k j y, y ∈ U k → s k j y ∈ zeroSet J' ∧ A *ᵥ s k j y = y := by
    intro k j y hy
    have hm : s k j y ∈ ComplexSets.fibre J' A y := by rw [(hfib k y hy).1]; exact ⟨j, rfl⟩
    exact hm

  have hpt : ∀ (t : ℂ) (v : Fin n → ℂ), h.pointOf (t • WithLp.toLp 2 (M *ᵥ v)) = t • v := by
    intro t v
    simp only [HermNorm.pointOf]
    change h.matᵀ *ᵥ (t • (M *ᵥ v)) = t • v
    rw [mulVec_smul, mulVec_mulVec, hM, mul_nonsing_inv _ hdet, one_mulVec]
  refine ⟨U, D, N, s, hUD, hdisj, hnull, hfib, ?_, ?_, ?_⟩
  ·
    rintro ⟨⟨k, j⟩, y, t⟩ ⟨hy, ht⟩ ⟨⟨k', j'⟩, y', t'⟩ ⟨hy', ht'⟩ heq
    simp only at hy ht hy' ht' heq
    have hv := congrArg h.pointOf heq
    rw [hpt, hpt] at hv
    obtain ⟨hZ, hA1⟩ := hval k j y ((hUD k).2.2.1 hy)
    obtain ⟨hZ', hA1'⟩ := hval k' j' y' ((hUD k').2.2.1 hy')
    have hl := congrArg (fun x => eval x (linForm ℓ)) hv
    simp only [eval_linForm_smul, (hslice _ hZ).2, (hslice _ hZ').2, mul_one] at hl
    subst hl
    have hss : s k j y = s k' j' y' := smul_right_injective _ ht hv
    have hyy : y = y' := by rw [← hA1, ← hA1', hss]
    subst hyy
    have hkk : k = k' := by
      by_contra hk
      exact Set.disjoint_left.1 (hdisj hk) hy hy'
    subst hkk
    have hjj : j = j' := (hfib k y ((hUD k).2.2.1 hy)).2.1 hss
    subst hjj
    rfl
  ·
    rintro z ⟨⟨⟨k, j⟩, y, t⟩, ⟨hy, ht⟩, rfl⟩
    simp only at hy ht
    intro q hq
    rw [hpt]
    exact eval_smul_of_isHomogIdeal hJ.isHomog (hslice _ (hval k j y ((hUD k).2.2.1 hy)).1).1 t q hq
  ·
    obtain ⟨δ, G, hG, hGf⟩ := SliceIdeal.exists_homogeneous_sub_mem ℓ (pullback A P)
    have hGJ : G ∉ J := by
      intro hGm
      apply hP0
      have hm : pullback A P ∈ J' := by
        have e1 : pullback A P = G - (G - pullback A P) := by ring
        rw [e1]
        exact Ideal.sub_mem _ (Ideal.mem_sup_left hGm) (Ideal.mem_sup_right hGf)
      apply hA.injective
      rw [map_zero]
      change (Ideal.Quotient.mkₐ ℂ J') (pullback A P) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hm
    have hZ1 := NullSmaller.proof n (e + 1) (J ⊔ Ideal.span {linForm ℓ})
      (MassFinite.dim_sup_lt J hP hdim _ hℓ)
    have hZ2 := NullSmaller.proof n (e + 1) (J ⊔ Ideal.span {G})
      (MassFinite.dim_sup_lt J hP hdim _ hGJ)
    set F := fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
      q.2.2 • WithLp.toLp 2 (M *ᵥ s q.1.1 q.1.2 q.2.1) with hF
    let L := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)
    have hsub : {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} \
        F '' {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆
        L '' (zeroSetEuc (J ⊔ Ideal.span {linForm ℓ}) ∪ zeroSetEuc (J ⊔ Ideal.span {G})) := by
      rintro z ⟨hzC, hzF⟩
      set p := h.pointOf z with hp
      have hzp : L (WithLp.toLp 2 p) = z := by
        change WithLp.toLp 2 (M *ᵥ (h.matᵀ *ᵥ WithLp.ofLp z)) = z
        rw [mulVec_mulVec, hM, nonsing_inv_mul _ hdet, one_mulVec]
      have hpJ : ∀ q ∈ J, eval p q = 0 := hzC
      refine ⟨WithLp.toLp 2 p, ?_, hzp⟩
      by_cases h0 : eval p (linForm ℓ) = 0
      · exact Or.inl (eval_sup_span hpJ h0)
      set c := eval p (linForm ℓ) with hc
      have hpx : p = c • (c⁻¹ • p) := by rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
      have hx : c⁻¹ • p ∈ zeroSet J' :=
        eval_sup_span (eval_smul_of_isHomogIdeal hJ.isHomog hpJ c⁻¹)
          (by rw [map_sub, map_one, eval_linForm_smul, ← hc, inv_mul_cancel₀ h0, sub_self])
      by_cases hyD : A *ᵥ (c⁻¹ • p) ∈ ⋃ k, D k
      · exfalso
        obtain ⟨k, hk⟩ := mem_iUnion.1 hyD
        have hxf : c⁻¹ • p ∈ ComplexSets.fibre J' A (A *ᵥ (c⁻¹ • p)) := ⟨hx, rfl⟩
        rw [(hfib k _ ((hUD k).2.2.1 hk)).1] at hxf
        obtain ⟨j, hj⟩ := hxf
        apply hzF
        refine ⟨⟨⟨k, j⟩, A *ᵥ (c⁻¹ • p), c⟩, ⟨hk, h0⟩, ?_⟩
        rw [← hzp]
        simp only [hF, hj]
        change c • WithLp.toLp 2 (M *ᵥ (c⁻¹ • p)) = WithLp.toLp 2 (M *ᵥ p)
        rw [mulVec_smul, WithLp.toLp_smul, smul_smul, mul_inv_cancel₀ h0, one_smul]
      · have hPy : eval (A *ᵥ (c⁻¹ • p)) P = 0 := hbad hyD
        refine Or.inr (eval_sup_span hpJ ?_)
        have hGx : eval (c⁻¹ • p) G = eval (c⁻¹ • p) (pullback A P) := by
          have h2 := hx _ (Ideal.mem_sup_right hGf)
          rwa [map_sub, sub_eq_zero] at h2
        rw [hpx, eval_smul_of_isHomogeneous hG, hGx, MassFinite.eval_pullback, hPy, mul_zero]
    refine measure_mono_null hsub ?_
    refine le_antisymm ?_ zero_le
    calc Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          (L '' (zeroSetEuc (J ⊔ Ideal.span {linForm ℓ}) ∪ zeroSetEuc (J ⊔ Ideal.span {G})))
        ≤ (‖L‖₊ : ENNReal) ^ (((2 * (e + 1) : ℕ) : ℝ)) *
            Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
              (zeroSetEuc (J ⊔ Ideal.span {linForm ℓ}) ∪ zeroSetEuc (J ⊔ Ideal.span {G})) :=
          L.lipschitz.hausdorffMeasure_image_le (Nat.cast_nonneg _) _
      _ = 0 := by rw [measure_union_null hZ1 hZ2, mul_zero]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem CurveNormalisationFinite.proof (hN : FieldNumbers.NoetherIntegralClosureFinite.Statement.{0}) :
    CurveNormalisationFinite.Statement := by
  intro n I q hI
  have := isReduced_curveLocalRing I q hI
  exact finite_integralClosure_of_isReduced hN (algebraMap _ (curveLocalRing I q)) (curveLocalRing_eq_div I q)

end GroundTheory.Heights₂.Heights
end
