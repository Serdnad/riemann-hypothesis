module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle922
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableInfMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle902
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle709
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle908
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle654
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle746
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle923
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle185
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle321
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle395
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

noncomputable section

open NumberField Matrix MeasureTheory Filter GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot Topology GroundTheory.Automorphic.GJMatrix GlobalTheory.RSThetaLow

namespace GlobalTheory.RSThetaLowM

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mspanR_invT (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.mspanR π) :
    (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra :=
  GlobalTheory.T.inverseTranspose_mem_cuspFormRapidKernelSpan_contragredient E a π F hF

def rsm (π : CuspSub E a) : Submodule ℂ (Sm E a) := (GlobalTheory.JSW.mspanR π).comap (Sm E a).subtype

theorem lie_mem_rsm {π : CuspSub E a} (hπ : π.IsUnitary) (X : Lie E a) {F : Sm E a} (hF : F ∈ rsm π) :
    lie E a X F ∈ rsm π := by
  obtain ⟨ψ, hψ, hw, -⟩ := GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded E a GlobalTheory.CuspOrth.cuspFormsBounded π hπ F.1 hF
  obtain rfl : ψ = F := Subtype.ext hψ
  simpa [GlobalTheory.GLFin.word, rsm] using hw [X]

theorem bounded_of_mem_rsm {π : CuspSub E a} (hπ : π.IsUnitary) {F : Sm E a} (hF : F ∈ rsm π) :
    ∃ C : ℝ, ∀ g, ‖F.1 g‖ ≤ C :=
  (GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded E a GlobalTheory.CuspOrth.cuspFormsBounded π hπ F.1 hF).choose_spec.2.2.2

theorem decays_invT_of_mem_rsm {π : CuspSub E a} (hπ : π.IsUnitary) {F : Sm E a} (hF : F ∈ rsm π) :
    Decays fun g => F.1 (invT a (Ad E) g) := by
  obtain ⟨ψ, hψ, -, -⟩ := GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded E a GlobalTheory.CuspOrth.cuspFormsBounded π.contra hπ.contra _ (mspanR_invT π hF)
  intro L hL C₀ hC₀ N
  obtain ⟨C, h⟩ := GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector E a π.contra hπ.contra ψ (Or.inr (hψ ▸ mspanR_invT π hF)) [] L hL C₀ hC₀ N
  refine ⟨C, fun g c hc ξ hξ hm => ?_⟩
  have := h g c hc ξ hξ hm
  simpa [GlobalTheory.GLFin.word, hψ] using this

variable {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
variable {π π' : CuspSub E a} {φ φ' : Sm E a}

theorem exists_norm_rsHat_le_const (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hΦ : IsTest (rowSet E ℓ) Φ) :
    ∃ C : ℝ, ∀ g y, ‖rsHat ℓ φ.1 φ'.1 Φ J η g y‖ ≤ C := by
  obtain ⟨C, h⟩ := exists_norm_rsHat_le J η (g := id) (w := fun _ => 1) (fun X _ => lie_mem_rsm hπ X)
    (fun X _ => lie_mem_rsm hπ' X)
    (fun F hF _ _ => (bounded_of_mem_rsm hπ hF).imp fun C h _ _ _ => (h _).trans_eq (mul_one _).symm)
    (fun F hF => bounded_of_mem_rsm hπ' hF) hφ hφ' hΦ 0
  exact ⟨C, fun g y => by simpa using h g y⟩

theorem exists_tsum_norm_rsHat_le (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hΦ : IsTest (rowSet E ℓ) Φ) (K : ℕ) : ∃ C : ℝ, ∀ g ∈ lowSet E a,
      ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖rsHat ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖ ≤
        C * (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ K := by
  set N := K + Module.finrank ℝ (Fin a → Cinf E) with hN
  have had : 1 ≤ a * Module.finrank ℚ E := Nat.mul_pos ℓ.pos Module.finrank_pos
  obtain ⟨M, C₁, h₁⟩ := GlobalTheory.T.summable_nonzeroRationalVector_le_shortestVector E a (traceDualIdeal E J) (a * Module.finrank ℚ E * N)
    ((Nat.le_add_left _ K).trans (Nat.le_mul_of_pos_left _ had))
  obtain ⟨C₂, h₂⟩ := exists_norm_rsHat_le J η
    (ι := {p : GA E a × (Fin a → E) // p.2 ≠ 0 ∧
      (fun i => pFin E (((fun j => algebraMap E (Ad E) (p.2 j)) ᵥ* p.1.val) i)) ∈ latt a (traceDualIdeal E J)})
    (g := fun p => invT a (Ad E) p.1.1)
    (w := fun p => (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (p.1.2 j)) ᵥ* p.1.1.val) i)‖ ^
      (a * Module.finrank ℚ E) / (ideleModule E (GeneralLinearGroup.det p.1.1) : ℝ)) ^ N)
    (fun X _ => lie_mem_rsm hπ X) (fun X _ => lie_mem_rsm hπ' X)
    (fun F hF C₀ hC₀ => (decays_invT_of_mem_rsm hπ hF _ (isCompact_latt _) _ (hC₀.image continuous_invT) N).imp
      fun C h p c hc => by simpa only [map_mul, invT_invT] using h p.1.1 _ ⟨c, hc, rfl⟩ p.1.2 p.2.1 p.2.2)
    (fun F hF => bounded_of_mem_rsm hπ' hF) hφ hφ' hΦ M
  refine ⟨|C₁| * |C₂|, fun g hg => ?_⟩
  set δ : ℝ := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδ0 : 0 < δ := (ideleModule E _).2
  have h := (h₁ (invT a (Ad E) g) (|C₂| * δ ^ N)
    (fun ξ => rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)) (by positivity)
    (fun ξ hξ => by
      rw [rsHat_eq J η φ φ' hΦ]
      exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (Set.indicator_of_notMem hξ _)) _)
    (fun ξ ξ' h0 hξ' => by
      have h3 := h₂ ⟨(invT a (Ad E) g, ξ'), h0, hξ'⟩ ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)
      simp only [invT_invT, absDet_invT, ← hδ, div_inv_eq_mul, mul_pow, ← pow_mul] at h3
      refine h3.trans ?_
      rw [mul_assoc |C₂|, mul_comm (δ ^ N)]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))).2
  refine h.trans ?_
  rw [mul_assoc]
  refine mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hδ0.le hg (Nat.le_add_right _ _)) (abs_nonneg _)) (by positivity) (abs_nonneg _)

variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}

theorem integrableOn_partA (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hc : Continuous φ.1) (hc' : Continuous φ'.1) (hΦ : IsTest (rowSet E ℓ) Φ)
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
    {s : ℂ} (hs : 1 < s.re) : IntegrableOn (fun g => rsHat ℓ φ.1 φ'.1 Φ J η g 0 *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1)) (𝓕 ∩ lowSet E a) μ := by
  obtain ⟨C, hC⟩ := exists_norm_rsHat_le_const J η hπ hπ' hφ hφ' hΦ
  refine ((GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain E a ℓ.pos μ 𝓕 h𝓕 (s.re - 1) (by linarith)).const_mul C).mono'
    ((stronglyMeasurable_rsHat J η hc hc' hΦ continuous_const).aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp GlobalTheory.RSThetaLow.continuous_absDet.measurable).pow_const _).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.sub_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (hC g 0) (Real.rpow_nonneg (ideleModule E _).2.le _)

theorem partB_entire (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hc : Continuous φ.1) (hc' : Continuous φ'.1) (hΦ : IsTest (rowSet E ℓ) Φ)
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) :
    (∀ x : ℝ, IntegrableOn (fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1)) (𝓕 ∩ lowSet E a) μ) ∧
    (∀ s : ℂ, IntegrableOn (fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1)) (𝓕 ∩ lowSet E a) μ) ∧
    Differentiable ℂ (partB ℓ φ.1 φ'.1 Φ J η μ 𝓕) := by
  haveI : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hm : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, AEStronglyMeasurable (fun g : GA E a =>
      rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) (μ.restrict (𝓕 ∩ lowSet E a)) :=
    fun ξ => (stronglyMeasurable_rsHat J η hc hc' hΦ
      (continuous_const.matrix_vecMul Units.continuous_coe_inv.matrix_transpose)).aestronglyMeasurable
  have hlow : ∀ᵐ g ∂μ.restrict (𝓕 ∩ lowSet E a), g ∈ lowSet E a :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right
      (ae_restrict_mem (isClosed_le GlobalTheory.RSThetaLow.continuous_absDet continuous_const).measurableSet)
  have hδ := hlow.mono (q := fun g => 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧
    (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) fun g hg => ⟨(ideleModule E _).2, hg⟩
  have hi := GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain E a ℓ.pos μ 𝓕 h𝓕 1 one_pos
  simp only [Real.rpow_one] at hi
  have hb := exists_tsum_norm_rsHat_le J η hπ hπ' hφ hφ' hΦ
  have h1 := GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one _ _ _ _ GlobalTheory.RSThetaLow.continuous_absDet.measurable hδ hi (AEStronglyMeasurable.tsum hm) fun K =>
    (hb K).imp fun C h => hlow.mono fun g hg =>
      (norm_tsum_le_tsum_norm (poisson_rsPsi J η φ φ' hΦ g).2.1).trans (h g hg)
  have h2 := GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one _ _ _ _ GlobalTheory.RSThetaLow.continuous_absDet.measurable hδ hi
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (AEStronglyMeasurable.tsum fun ξ => (hm ξ).norm)) fun K =>
    (hb K).imp fun C h => hlow.mono fun g hg => by
      rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
      exact h g hg
  refine ⟨fun x => ((h2.1 ((x - 1 : ℝ) : ℂ)).norm).congr (.of_forall fun g => ?_), fun s => h1.1 _,
    h1.2.comp (differentiable_id.sub_const 1)⟩
  simp only [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.ofReal_re]
  rw [Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]

theorem integral_low_eq (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hc : Continuous φ.1) (hc' : Continuous φ'.1) (hΦ : IsTest (rowSet E ℓ) Φ)
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun g => (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s) (𝓕 ∩ lowSet E a) μ ∧
    ∫ g in 𝓕 ∩ lowSet E a, (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ =
      partA ℓ φ.1 φ'.1 Φ J η μ 𝓕 s + partB ℓ φ.1 φ'.1 Φ J η μ 𝓕 s := by
  have hA := integrableOn_partA J η hπ hπ' hφ hφ' hc hc' hΦ h𝓕 hs
  have hB := (partB_entire J η hπ hπ' hφ hφ' hc hc' hΦ h𝓕).2.1 s
  have e : ∀ g : GA E a, (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s =
      rsHat ℓ φ.1 φ'.1 Φ J η g 0 * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) +
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
        rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) := fun g => by
    rw [(poisson_rsPsi J η φ φ' hΦ g).2.2, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.2 (ideleModule E _).2.ne'),
      Complex.cpow_one]
    ring
  simp only [e]
  exact ⟨hA.add hB, integral_add hA hB⟩

end GlobalTheory.RSThetaLowM
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult

namespace GlobalTheory.ConjInt
open GlobalTheory.StdFrames GlobalTheory.AdIsom GlobalTheory.IdemSupport

theorem frame_mat_le_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b)) ≤ 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b)) ≤ 1 := by
  intro D V β Λ N hSD g Q h a b
  obtain ⟨hGi, U', hU'i, hU'⟩ := unimod_of_isSD hSD
  have hX : Formalism.UG.cT (sg D) (finE V g).val * GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram * (finE V g).val =
      GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram := GlobalTheory.LevSplit.finE_mem_UA V g
  have hYsub := GlobalTheory.ConjLt.conj_sub_one (sg D) β (finE V g) _ U' hX hU'
  have hY : (β⁻¹ * finE V g * β).val = U' * Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val *
      (Formalism.UG.cT (sg D) β.val * GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram * β.val) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hU'] at hYsub
    exact sub_left_inj.1 hYsub
  have hM : ∀ i j, Valued.v (cpt (GlobalTheory.IdemSupport.cP Q)
      ((Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val) i j)) ≤ 1 := by
    intro i j
    exact (cpt_cjA_le_iff Q _).2 (h j i)
  have hint : ∀ x ∈ GlobalTheory.StdFrames.OA D, Valued.v (cpt (GlobalTheory.IdemSupport.cP Q) x) ≤ 1 :=
    fun x hx => (mem_OA x).1 hx (GlobalTheory.IdemSupport.cP Q)

  rw [hY, Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_

  rw [map_mul, Valuation.map_mul, Matrix.mul_apply, map_sum]
  refine mul_le_one' ?_ (hint _ (hGi j b))
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul, Valuation.map_mul]
  exact mul_le_one' (hint _ (hU'i a i)) (hM i j)

end GlobalTheory.ConjInt
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremTClosing

section Mono

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem liftF_of_le {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (hF c hc)

end Mono

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ C : ℕ, 40 ≤ C →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.ElementDenominator.HodgeTateFromSandwich D HW F C := by
  intro hBS hFB C hC D HW F _ l _ K' h hN hF hS LL
  have hlp : l.Prime := Fact.out
  have hl2 : 2 ≤ l := hlp.two_le
  obtain ⟨a, ha⟩ : ∃ a, a = (l - 1).factorial := ⟨_, rfl⟩
  haveI : NeZero a := ⟨by rw [ha]; exact Nat.factorial_ne_zero _⟩
  have hla : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) (by omega)
  obtain ⟨e, he⟩ : ∃ e, e + 1 = l ^ a := ⟨l ^ a - 1, by omega⟩
  haveI : NeZero e := ⟨by
    intro h0
    rw [h0, zero_add] at he
    omega⟩
  have hnd : ¬ l ∣ a := by
    rw [ha, hlp.dvd_factorial]
    omega
  obtain ⟨⟨LL', hle, hUnr⟩, -⟩ := GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent l a e he hnd LL
  haveI := hUnr
  haveI : TameDescentExponentData ↥LL'.1 l e a := (GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent l a e he hnd LL').2 hUnr
  refine GlobalTheory.T.theoremT_descend_smaller_coefficients l (D.loc l) K' h hN hF hS LL LL' hle C ?_
  have ϖ : PiSys l e := Classical.arbitrary _
  have hStd : IsStd (D.loc l) (D.locA l) := IsStd.of_tied (D.locT l)
  intro T₁ T₂ g N η H U Sig Fr hP1 hP2 hOnto hFr hFS h1 hcard h2N hIT1 hIT2 hUr hU0 hUc hη hηH hJ1 hJ2 hl
  have hp : (pc (D.loc l) h hN hF hS).PD.p = l := (D.loc l).PD_p _
  have hlarge : 40 * (H * N ^ 2 + N ^ 3) < l := lt_of_le_of_lt (Nat.mul_le_mul_right _ hC) hl
  have hNl : N < l := by
    have : N ≤ N ^ 3 := Nat.le_self_pow (by norm_num) N
    omega
  have hcop : ∀ χ ∈ Sig, Nat.Coprime (orderOf χ) l := fun χ hχ => by
    have := hIT1.2.1 χ hχ
    rwa [hp] at this
  obtain ⟨Sig', hS1, hS2, hS3, hS4, hS5⟩ := GlobalTheory.T.exists_tameField_goodLattice_potentiallyCrystalline hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd ha
    K' h hN hF hS Sig Fr N hFr hFS h1 hcard hNl hIT1.1 hcop
  obtain ⟨c1, t1⟩ := hS5 T₁ hP1 hIT1
  obtain ⟨c2, t2⟩ := hS5 T₂ hP2 hIT2
  have hnum : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig' U :=
    ⟨hS1, hS2, hS3, h2N, hUr, hU0, hUc, hη, hηH, hlarge⟩
  have hcore := GlobalTheory.T.lift_surjection_good_crystalline_lattices hBS hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd N η H Sig' U hnum T₁ T₂ g hOnto
    ⟨c1, t1, hJ1⟩ ⟨c2, t2, hJ2⟩
  have horb := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hlp (Nat.one_le_iff_ne_zero.2 (NeZero.ne a)) he Sig' N hS1 hS2 hS3 h2N
  rw [hS4] at hcore horb
  refine ⟨horb.2.1, ?_⟩
  exact liftF_of_le _ g hcore (Nat.mul_le_mul_right _ (by omega))

end GlobalTheory.TheoremTClosing
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowCuspFromLift

theorem isoInf_append (D : D7) (L L' : List (Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut (L ++ L') τ = isoInf D.nd D.naut L τ + isoInf D.nd D.naut L' τ := by
  unfold isoInf
  rw [List.map_append, List.sum_append]

theorem isoInf_perm (D : D7) {L L' : List (Part D.naut.CG)} (h : L.Perm L') (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut L τ = isoInf D.nd D.naut L' τ := by
  unfold isoInf
  exact (h.map _).sum_eq

theorem eta_emb (s : Multiset ℂ) (h : s = {1 / 2} ∨ s = {-(1 / 2)}) :
    (s.map (fun z => -z) = {-(1 / 2)} → s = {1 / 2}) ∧ (s.map (fun z => -z) = {1 / 2} → s = {-(1 / 2)}) := by
  rcases h with rfl | rfl
  · refine ⟨fun _ => rfl, fun h' => ?_⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'
  · refine ⟨fun h' => ?_, fun _ => rfl⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'

theorem isoInf_one (D : D7) {a : ℕ} (ρ : D.naut.CG a) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut [⟨a, ρ, 1⟩] τ = D.naut.infG ρ τ := by
  simp [isoInf]

end GlobalTheory.RowCuspFromLift

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section

namespace GlobalTheory.LiftRefIrr

theorem exists_ne_of_mem_iSup' {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Sort*} (p : ι → Submodule ℂ M)
    (ℓ : M →+ ℂ) {x : M} (hx : x ∈ ⨆ i, p i) (h : ℓ x ≠ 0) : ∃ i, ∃ y ∈ p i, ℓ y ≠ 0 := by
  by_contra H
  push_neg at H
  exact h (Submodule.iSup_induction p (motive := fun z => ℓ z = 0) hx (fun i y hy => H i y hy) (map_zero ℓ)
    (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero]))

theorem exists_irr_pair {D : D7} {μ : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μ j) (x : D.what₂.Mt μ j) (hx : x ≠ 0) :
    ∃ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)) (_ : NG.IsIrrRep Mr.wt.ρ S),
      ∃ F ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, inner ℂ F x ≠ 0 := by
  obtain ⟨-, ι, -, S, hirr, -, -, -, -, hsum⟩ := GlobalTheory.T.typeSpaces_orthogonal_of_classSum_inner D.host.E D.R.nV Mr.wt Mr.J Mr.χ Mr.J_open
  let p : ι → Submodule ℂ (D.what₂.Mt μ j) :=
    fun i => (NG.isoTyp Mr.wt.ρ (S i) ⊓ NG.TypeSp Mr.wt.ρ Mr.J Mr.χ).comap Mr.real
  have htop : (⨆ i, p i) = ⊤ := by
    apply Submodule.map_injective_of_injective Mr.real_inj
    rw [Submodule.map_iSup, Submodule.map_top, Mr.real_range]
    conv_rhs => rw [← hsum]
    refine iSup_congr fun i => ?_
    show Submodule.map Mr.real (Submodule.comap Mr.real _) = _
    rw [Submodule.map_comap_eq, Mr.real_range]
    exact inf_eq_right.2 inf_le_right
  have hxm : x ∈ ⨆ i, p i := htop ▸ Submodule.mem_top
  let ℓ : D.what₂.Mt μ j →+ ℂ := AddMonoidHom.mk' (fun F => inner ℂ F x) (fun a b => inner_add_left a b x)
  obtain ⟨i, F, hF, hne⟩ := exists_ne_of_mem_iSup' p ℓ hxm (by
    show inner ℂ x x ≠ 0
    exact inner_self_ne_zero.2 hx)
  exact ⟨S i, hirr i, F, (Submodule.mem_inf.1 hF).1, hne⟩

end GlobalTheory.LiftRefIrr


end
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult

theorem _root_.GlobalTheory.T.selfDualFrame_conjugate_place_integral : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b)) ≤ 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b)) ≤ 1 := by
  first | exact @GlobalTheory.ConjInt.frame_mat_le_one | exact GlobalTheory.ConjInt.frame_mat_le_one | (intros; apply GlobalTheory.ConjInt.frame_mat_le_one <;> assumption)

end
end
