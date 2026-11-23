module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle671
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle675
public import GroundTheory.AutomorphicForms.Bundle014
public import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge
public import GroundTheory.AutomorphicForms.AnisotropicHeight
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle378
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle380
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle294
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle394
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle674
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle676
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle056
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle290
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120

@[expose] public section

section

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.Bridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hermValue_inclR (v : Fin n → E) :
    hermValue F J F (fun i => inclR (F := F) F (v i)) =
      inclR (F := F) F (hE (conj F E).toAlgHom J v v) := by
  have hc : ∀ e : E, conjBase F E F (inclR (F := F) F e) = inclR (F := F) F (conj F E e) := fun e => rfl
  have hb : baseMatrix F J F = J.map (inclR (F := F) F) := rfl

  simp only [hermValue, hc, hb, hE, Formalism.UG.hform, dotProduct, mulVec, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.map_apply, mul_assoc]

theorem ofResVec_cvec (v : Fin n → E) :
    ofResVec (ι := Fin n) (Module.finBasis F E) F (cvec F v) = fun i => inclR (F := F) F (v i) := by
  apply resVec_injective (ι := Fin n) (Module.finBasis F E) F
  rw [resVec_ofResVec]
  funext p
  simp only [cvec, resVec, Function.comp_apply, coordsVec, coords, inclR]
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem hermCoords_cvec_ne_zero {v : Fin n → E} (h : hE (conj F E).toAlgHom J v v ≠ 0) :
    hermCoords J (Module.finBasis F E) F (cvec F v) ≠ 0 := by
  intro h0
  apply h
  have h1 : hermValue F J F (ofResVec (ι := Fin n) (Module.finBasis F E) F (cvec F v)) = 0 := by
    apply (coords (Module.finBasis F E) F).injective
    rw [map_zero]
    exact h0
  rw [ofResVec_cvec, hermValue_inclR] at h1
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F F).injective (h1.trans (map_zero _).symm)

theorem matHom_mem_unitaryPoints (g : GAd (conj F E).toAlgHom J) :
    matHom (AF F) (conj F E).toAlgHom J g ∈ unitaryPoints F E J (AF F) := by
  rw [← CompanionTheory.SWFin.HR_eq]
  exact g.2

theorem exists_pos_isotropic_of_hgt_lt :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd (conj F E).toAlgHom J) (v : Fin n → E), v ≠ 0 →
      hgt (conj F E).toAlgHom J g v < ε → hE (conj F E).toAlgHom J v v = 0 := by
  obtain ⟨C, hC, hCb⟩ := exists_adelicNorm_aeval_le (K := F) (d := 2) two_pos
    (hermPoly J (Module.finBasis F E))
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
  refine ⟨min 1 C⁻¹, lt_min one_pos (inv_pos.2 hC), fun g v hv hlt => ?_⟩
  by_contra hne
  rw [hgt_eq] at hlt
  have hx : cvec F v ≠ 0 := cvec_ne_zero hv
  have hz := hermCoords_cvec_ne_zero J hne
  have hy := Reduction.hasFiniteContent_height (trG (conj F E).toAlgHom J g) hx
  have he : (fun k => MvPolynomial.aeval
      (Reduction.ratVec (cvec F v) ᵥ* ((trG (conj F E).toAlgHom J g : GL _ (AF F)) : Matrix _ _ (AF F)))
      (hermPoly J (Module.finBasis F E) k)) =
      Reduction.ratVec (hermCoords J (Module.finBasis F E) F (cvec F v)) := by
    funext k
    rw [aeval_hermPoly]
    exact congrFun (hermCoords_vecMul_trHom J (Module.finBasis F E) (cvec F v)
      ⟨_, matHom_mem_unitaryPoints J g⟩) k
  have hfz := Reduction.hasFiniteContent_ratVec hz
  rw [← he] at hfz
  have h1 := Reduction.one_le_adelicNorm_ratVec hz
  rw [← he] at h1
  have h2 : 1 ≤ C * Reduction.height (trG (conj F E).toAlgHom J g) (cvec F v) ^ 2 :=
    h1.trans (hCb _ hy hfz)
  have h0 := Reduction.height_nonneg (trG (conj F E).toAlgHom J g) (cvec F v)
  set t := Reduction.height (trG (conj F E).toAlgHom J g) (cvec F v)
  have ht1 : t < 1 := hlt.trans_le (min_le_left _ _)
  have htC : t < C⁻¹ := hlt.trans_le (min_le_right _ _)
  have h3 : C * t < 1 := by
    have := mul_lt_mul_of_pos_left htC hC
    rwa [mul_inv_cancel₀ hC.ne'] at this
  have h4 : C * t ^ 2 ≤ C * t := by
    nlinarith [mul_nonneg (mul_nonneg hC.le h0) (sub_nonneg.2 ht1.le)]
  linarith

end GlobalTheory.CompanionTheory.RedCov.Bridge

namespace GlobalTheory.CompanionTheory.RedCov

theorem isotropic_of_hgt_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0 := by
  intro F E _ _ _ _ _ σ h n J _
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((h.2.2.2 τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  exact Bridge.exists_pos_isotropic_of_hgt_lt J

end GlobalTheory.CompanionTheory.RedCov

end
end

section

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.FormHeight

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

section Forms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {n : ℕ}

theorem sigR_conj (R : Type) [CommRing R] [Algebra F R] :
    sigR R (conj F E).toAlgHom = conjBase F E R := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem hermValue_eq_hR (R : Type) [CommRing R] [Algebra F R] (H : Matrix (Fin n) (Fin n) E)
    (x : Fin n → R ⊗[F] E) : hermValue F H R x = hR R (conj F E).toAlgHom H x x := by
  rw [hR, sigR_conj]
  simp only [hermValue, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc]
  rfl

theorem coords_algebraMap_mul_inclR (s : AF F) (z : E) :
    coords (Module.finBasis F E) (AF F)
        (algebraMap (AF F) (AF F ⊗[F] E) s * inclR (F := F) (AF F) z) =
      s • Reduction.ratVec (fun k => (Module.finBasis F E).repr z k) := by
  have e : algebraMap (AF F) (AF F ⊗[F] E) s * inclR (F := F) (AF F) z = s • ((1 : AF F) ⊗ₜ[F] z) := by
    simp [inclR, Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']
  rw [e, map_smul]
  congr 1
  funext k
  simp [coords, Reduction.ratVec, Algebra.TensorProduct.basis_repr_tmul]

theorem exists_adelicNorm_hermPoly_le (H : Matrix (Fin n) (Fin n) E) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Fin (Bridge.dimN F E n) → AF F, Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent
        (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) ≤
        C * Reduction.adelicNorm y ^ 2 :=
  exists_adelicNorm_aeval_le (K := F) (d := 2) two_pos (hermPoly H (Module.finBasis F E))
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)

theorem one_le_mul_hgt_sq (J H : Matrix (Fin n) (Fin n) E) {C : ℝ}
    (hCb : ∀ y : Fin (Bridge.dimN F E n) → AF F, Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent
        (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) ≤
        C * Reduction.adelicNorm y ^ 2)
    (g : GAd (conj F E).toAlgHom J) {ξ : Fin n → E} (hξ : ξ ≠ 0)
    (s : GroundTheory.Global.IdeleGroup F) (hs : 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ))
    {z : E} (hz : z ≠ 0)
    (he : hR (AF F) (conj F E).toAlgHom H
        ((matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ)
        ((matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ) =
      algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) z) :
    1 ≤ C * hgt (conj F E).toAlgHom J g ξ ^ 2 := by
  set b := Module.finBasis F E with hb
  set v := (matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ with hv
  set y : Fin (Bridge.dimN F E n) → AF F := resVec (ι := Fin n) b (AF F) v with hy
  have ey : Reduction.ratVec (Bridge.cvec F ξ) ᵥ*
      (Bridge.trG (conj F E).toAlgHom J g : Matrix _ _ (AF F)) = y := by
    rw [Bridge.ratVec_cvec, Bridge.trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hy, hv, map_inv]
  have hfy : Reduction.HasFiniteContent y := by
    rw [← ey]
    exact Reduction.hasFiniteContent_height _ (Bridge.cvec_ne_zero hξ)
  have hz' : (fun k => b.repr z k) ≠ 0 := by
    intro h0
    apply hz
    apply b.repr.injective
    ext k
    simpa using congrFun h0 k
  have e : (fun k => MvPolynomial.aeval y (hermPoly H b k)) =
      (s : AF F) • Reduction.ratVec (fun k => b.repr z k) := by
    funext k
    rw [aeval_hermPoly, hermCoords, hy, ofResVec_resVec, hermValue_eq_hR, he,
      coords_algebraMap_mul_inclR]
  have hfz : Reduction.HasFiniteContent (fun k => MvPolynomial.aeval y (hermPoly H b k)) := by
    rw [e]
    exact (Reduction.hasFiniteContent_ratVec hz').smul s
  have h1 : 1 ≤ Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H b k)) := by
    rw [e, Reduction.adelicNorm_smul (Reduction.hasFiniteContent_ratVec hz')]
    exact one_le_mul_of_one_le_of_one_le hs (Reduction.one_le_adelicNorm_ratVec hz')
  exact h1.trans (hCb y hfy hfz)

end Forms

theorem min_le_of_one_le_mul_sq {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) (h : 1 ≤ D * t ^ 2) :
    min 1 D⁻¹ ≤ t := by
  by_cases h1 : 1 ≤ t
  · exact (min_le_left _ _).trans h1
  · replace h1 := not_le.1 h1
    have h3 : 1 ≤ D * t := by
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hD.le)
      nlinarith
    refine (min_le_right _ _).trans ?_
    rw [inv_le_iff_one_le_mul₀ hD, mul_comm]
    exact h3

theorem exists_pos_le_hgt_of_forms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (H : M → Matrix (Fin n) (Fin n) E) (L : Set (GAd σ J)), (∀ ξ : Fin n → E, (∀ j, hE σ (H j) ξ ξ = 0) → ξ = 0) → (∀ g ∈ L, ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (H j) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (H j) ξ ξ)) → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ := by
  intro F E _ _ _ _ _ σ hCM n J _ M _ H L hzero hL
  obtain ⟨hF, hEc, h2, hc⟩ := hCM
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  cases nonempty_fintype M
  choose C hC hCb using fun j => exists_adelicNorm_hermPoly_le (F := F) (H j)
  have hsum : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ => (hC j).le
  have hD : 0 < 1 + ∑ j, C j := by linarith
  refine ⟨min 1 (1 + ∑ j, C j)⁻¹, lt_min one_pos (inv_pos.2 hD), fun g hg ξ hξ => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, hE (conj F E).toAlgHom (H j) ξ ξ ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hξ (hzero ξ hno)
  obtain ⟨s, hs, he⟩ := hL g hg j
  have h1 := one_le_mul_hgt_sq J (H j) (hCb j) g hξ s hs hj (he ξ)
  have ht : 0 ≤ hgt (conj F E).toAlgHom J g ξ := Reduction.adelicNorm_nonneg _
  have hle : C j ≤ 1 + ∑ j, C j := by
    have := Finset.single_le_sum (f := C) (fun i _ => (hC i).le) (Finset.mem_univ j)
    linarith
  exact min_le_of_one_le_mul_sq hD ht
    (h1.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)))

end GlobalTheory.CompanionTheory.ParCocompact.FormHeight

end
end

section


theorem _root_.GlobalTheory.T.tuple_space_covolume_formula : PositivityTheory.SiegelWeilFormula.KWhit.MeasP.TupCovol := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol | exact GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol | (intros; apply GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_map_continuous_additive : ∀ (D : D7) (n : ℕ) (nb : PositivityTheory.GramSchwartzFunctions.BC.hermA D n → GlobalTheory.StdUnn.G D n), PositivityTheory.PfSWUS.IsNMap nb → Continuous nb ∧ (∀ b c, nb (b + c) = nb b * nb c) ∧ ∀ γ ∈ PositivityTheory.GramSchwartzFunctions.BC.ratHerm D n, nb γ ∈ GlobalTheory.StdUnn.GF D n := by
  first | exact @GlobalTheory.CompanionTheory.SiegelUnip.nb_facts | exact GlobalTheory.CompanionTheory.SiegelUnip.nb_facts | (intros; apply GlobalTheory.CompanionTheory.SiegelUnip.nb_facts <;> assumption)
end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.SubEmb

theorem subEmbedding : Ysupp.SubEmbedding :=
  subEmbedding_of_stage GlobalTheory.T.product_irreducible_append_equiv

end GlobalTheory.CompanionTheory.SubEmb
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.TemperedCore

theorem exists_lFactors_unitary : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecTemp k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsTemperedCoeff π → IsL 𝔪 π → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x ∧ ∀ (a : Fin h) (t : kˣ) (c : ℂ), Zl.ScalarBy (x a) t c → ‖c‖ = 1 := by
  intro k _ _ _ _ hSoc hCas hSeg 𝔪 N V _ _ π hN hsm hirr htemp hL
  have hy : ∀ Δ : Segment k, ∃ y : IrrGL (k := k), IsLSeg Δ y.rep := fun Δ => by
    obtain ⟨ρ, hρ⟩ := hSeg Δ
    exact ⟨IrrGL.of ρ.ρ ρ.smooth ρ.irr, hρ.of_equiv (IrrGL.equivOf _ _ _)⟩
  choose y hyL using hy
  have hypos : ∀ Δ : Segment k, 0 < (y Δ).1 := fun Δ => by
    rw [← (hyL Δ).deg_eq]
    exact Nat.mul_pos Δ.len_pos Δ.d_pos
  have hs : ∀ Δ : Segment k, ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y Δ) t c →
      ‖c‖ = nabs k t ^ (((y Δ).1 : ℝ) * s) := fun Δ => GlobalTheory.T.central_character_norm_eq_pow k (y Δ) (hypos Δ)
  choose f hf using hs
  obtain ⟨h, Δ, hΔ, hanti, hnp⟩ := GlobalTheory.T.multiset_antitone_enumeration 𝔪 f Segment.Precedes (fun a b hab =>
    GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg k a b (y a) (y b) (f a) (f b) (hyL a) (hyL b) (hf a) (hf b) hab)
  let x : Fin h → IrrGL (k := k) := fun a => y (Δ a)
  have hLF : LFactors 𝔪 x := ⟨Δ, ⟨hΔ, hnp⟩, fun i => hyL _⟩
  have hsumdeg : ∀ {h' : ℕ} (Δ' : Fin h' → Segment k) (x' : Fin h' → IrrGL (k := k)),
      Finset.univ.val.map Δ' = 𝔪 → (∀ i, IsLSeg (Δ' i) (x' i).rep) →
      ∑ a, (x' a).1 = (𝔪.map Segment.deg).sum := by
    intro h' Δ' x' hm hx'
    rw [← hm, Multiset.map_map]
    exact Finset.sum_congr rfl fun a _ => ((hx' a).deg_eq).symm
  have hdeg : ∑ a, (x a).1 = N := by
    obtain ⟨h', x', hd', ⟨Δ', ⟨hΔ', -⟩, hx'⟩, -⟩ := hL
    rw [hsumdeg Δ x hΔ (fun i => hyL _), ← hsumdeg Δ' x' hΔ' hx', hd']
  have hdrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hdeg]
    exact Equiv.sum_comp Fin.revPerm (fun a => (x a).1)
  have hsoc := hSoc 𝔪 h N x hdrev hLF π hL
  have hjm := GlobalTheory.T.jacquet_multiplicity_pos_of_socle k h N (x ∘ Fin.rev) hdrev π hsm (fun a => hypos _) hsoc
  have hW := hCas N π hN hsm hirr htemp h (x ∘ Fin.rev) hdrev (fun a => hypos _) hjm
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have ht1 : nabs k t < 1 := GlobalTheory.T.norm_lt_one_of_pow_tendsto_zero k t ht
  have ht0 : 0 < nabs k t := by
    have h0 : (MeasureTheory.distribHaarChar k t : NNReal) ≠ 0 := fun h0 => by
      have := map_mul (MeasureTheory.distribHaarChar k) t t⁻¹
      simp [h0] at this
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)
  have hge : ∀ r : ℝ, nabs k t ^ r ≤ 1 → 0 ≤ r := fun r hr => by
    by_contra hneg
    exact absurd hr (not_le.2 (Real.one_lt_rpow_of_pos_of_lt_one_of_neg ht0 ht1 (not_le.1 hneg)))
  choose c hc using fun a => GlobalTheory.T.central_character_exists k (x a) t
  obtain ⟨hpart, htot⟩ := hW t ht (c ∘ Fin.rev) (fun i => hc _)
  let e : Fin h → ℝ := fun i => f (Δ i)
  let d : Fin h → ℝ := fun i => ((x i).1 : ℝ)
  have hnorm : ∀ i, ‖c i‖ = nabs k t ^ (d i * e i) := fun i => hf (Δ i) t (c i) (hc i)
  have hprod : ∀ S : Finset (Fin h), ∏ i ∈ S, ‖c i‖ = nabs k t ^ (∑ i ∈ S, d i * e i) := fun S => by
    rw [Real.rpow_sum_of_pos ht0]
    exact Finset.prod_congr rfl fun i _ => hnorm i
  have hsum : ∑ i, d i * e i = 0 := by
    have h1 : ∏ i, ‖c i‖ = 1 := by
      rw [← htot]
      exact (Equiv.prod_comp Fin.revPerm (fun i => ‖c i‖)).symm
    rw [hprod] at h1
    refine le_antisymm ?_ (hge _ h1.le)
    have := hge (-∑ i, d i * e i) (by rw [Real.rpow_neg ht0.le, h1, inv_one])
    linarith
  have htail : ∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i := by
    intro j
    by_cases hj : (Fin.rev j).val + 1 < h
    · have h1 := hpart (Fin.rev j) hj
      have h2 := GlobalTheory.T.prod_le_rev_eq_prod_ge h (fun i => ‖c i‖) (Fin.rev j)
      rw [Fin.rev_rev] at h2
      have h3 : ∏ i ∈ Finset.univ.filter (fun i => i ≤ Fin.rev j), ‖(c ∘ Fin.rev) i‖ =
          ∏ i ∈ Finset.univ.filter (fun i => j ≤ i), ‖c i‖ := h2
      rw [h3, hprod] at h1
      exact hge _ h1
    · have hj0 : j.val = 0 := by
        have := j.isLt
        rw [Fin.val_rev] at hj
        omega
      have hf' : Finset.univ.filter (fun i => j ≤ i) = Finset.univ := by
        ext i
        simp [Fin.le_def, hj0]
      rw [hf', hsum]
  have he := GlobalTheory.T.antitone_weighted_sum_zero h d e (fun i => Nat.cast_pos.2 (hypos (Δ i))) hanti hsum htail
  refine ⟨h, x, hdeg, hLF, fun a t' c' hsc => ?_⟩
  have h1 := hf (Δ a) t' c' hsc
  have h2 : f (Δ a) = 0 := he a
  rw [h1, h2, mul_zero, Real.rpow_zero]

end GlobalTheory.CompanionTheory.TemperedCore
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.hecke_spectral_of_strict_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → Zls.MaxExpStrict π → Zls.HeckeSpectral π := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict | exact GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict | (intros; apply GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.poisson_summation_hermitian_lattice : ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∀ f : hermA D r → ℂ, Continuous f → (∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ K, ‖f (b + c.1)‖ ≤ u c) → Integrable f lam ∧ (Summable (fun t : ratHerm D r => ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) → ∑' c : ratHerm D r, f c.1 = ∑' t : ratHerm D r, ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
  first | exact @GlobalTheory.CompanionTheory.HermPoisson.poisson_herm | exact GlobalTheory.CompanionTheory.HermPoisson.poisson_herm | (intros; apply GlobalTheory.CompanionTheory.HermPoisson.poisson_herm <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.concatenated_jacquet_multiplicity_factorization : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hpos : ∀ a, 0 < ∑ i, (x a i).1) (hcat : ∑ i, (concat c x i).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), 1 ≤ jm (concat c x) hcat π → ∃ (σ : Fin s → IrrGL (k := k)) (hσ : ∑ a, (σ a).1 = N), (∀ a, (σ a).1 = ∑ i, (x a i).1) ∧ 1 ≤ jm σ hσ π := by
  first | exact @GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse | exact GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse | (intros; apply GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse <;> assumption)
end

section


theorem _root_.GlobalTheory.T.matching_unit_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMUnitOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | exact GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | (intros; apply GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf <;> assumption)
end
