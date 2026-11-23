module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle078
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle084
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle145
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle901
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.SiegelCov

section Gen

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR

theorem chi_adele (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (modu (Ainf F) (fstA F M.det) : ℝ) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := by
  apply GlobalTheory.JacSubst.chi_AF_split <;> assumption

theorem addEquivAddHaarChar_mulVecCE_adele (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    addEquivAddHaarChar (mulVecCE M hM) = distribHaarChar (AF F) hM.unit := by
  let N : Matrix Unit Unit (AF F) := fun _ _ => M.det
  have hdet : N.det = M.det := Matrix.det_unique N
  have hN : IsUnit N.det := hdet ▸ hM
  have htr := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (GlobalTheory.ModuNorm.evalUnitCE (AF F)) (mulVecCE N hN)
  have hext : ((GlobalTheory.ModuNorm.evalUnitCE (AF F)).symm.trans (mulVecCE N hN)).trans (GlobalTheory.ModuNorm.evalUnitCE (AF F)) =
      GlobalTheory.ModuNorm.mulUnitCE hM.unit := by
    ext x
    show (N *ᵥ fun _ => x) () = M.det * x
    simp [Matrix.mulVec, dotProduct, N]
  rw [hext] at htr
  rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar, htr]
  apply NNReal.coe_injective
  rw [chi_adele, chi_adele, hdet]

end Gen

end GlobalTheory.SiegelCov

namespace GlobalTheory.SiegelCov

section Coord

open Matrix GlobalTheory.ModuLR

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)

def vecCoord : (Fin n → AE F E) ≃ₗ[AF F] (Fin n × Fin (Module.finrank F E) → AF F) where
  toFun u p := (tensBasis F E).equivFun (u p.1) p.2
  invFun x i := (tensBasis F E).equivFun.symm fun k => x (i, k)
  left_inv u := by
    funext i
    exact (tensBasis F E).equivFun.symm_apply_apply (u i)
  right_inv x := by
    funext p
    obtain ⟨i, k⟩ := p
    show (tensBasis F E).equivFun ((tensBasis F E).equivFun.symm fun k => x (i, k)) k = x (i, k)
    rw [LinearEquiv.apply_symm_apply]
  map_add' u v := by funext p; simp
  map_smul' c u := by funext p; simp

theorem continuous_vecCoord : Continuous (vecCoord F E n) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hb : Continuous (tensBasis F E).equivFun :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.toLinearMap
  exact continuous_pi fun p => (continuous_apply p.2).comp (hb.comp (continuous_apply p.1))

theorem continuous_vecCoord_symm : Continuous (vecCoord F E n).symm := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hb : Continuous (tensBasis F E).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.symm.toLinearMap
  exact continuous_pi fun i => hb.comp (continuous_pi fun k => continuous_apply (i, k))

def vecCoordCE : (Fin n → AE F E) ≃ₜ+ (Fin n × Fin (Module.finrank F E) → AF F) :=
  { (vecCoord F E n).toAddEquiv with
    continuous_toFun := continuous_vecCoord F E n
    continuous_invFun := continuous_vecCoord_symm F E n }

end Coord

end GlobalTheory.SiegelCov


open GlobalTheory.GaugeEx in
theorem GlobalTheory.SiegelCov.integral_mulVec_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (μ : @Measure (Fin n → AE F E) (borel _)), GlobalTheory.SiegelAvg.IsHaarB μ →
    ∀ (t : GL (Fin n) (AE F E)) (f : (Fin n → AE F E) → ℂ),
      (letI : MeasurableSpace (Fin n → AE F E) := borel _; Integrable f μ) →
      (letI : MeasurableSpace (Fin n → AE F E) := borel _;
        ∫ y, f (((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ y) ∂μ) =
        (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) : ℂ) *
          (letI : MeasurableSpace (Fin n → AE F E) := borel _; ∫ y, f y ∂μ) := by
  intro F E _ _ _ _ _ n μ hμ t f _
  letI : MeasurableSpace (Fin n → AE F E) := borel _
  haveI : BorelSpace (Fin n → AE F E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalAddGroup (AE F E) := IsModuleTopology.isTopologicalAddGroup (AF F) _
  haveI : Module.Free (AF F) (AF F ⊗[F] E) := Module.Free.of_basis (GlobalTheory.ModuLR.tensBasis F E)
  haveI : Module.Finite (AF F) (AF F ⊗[F] E) := Module.Finite.of_basis (GlobalTheory.ModuLR.tensBasis F E)
  let Φ := GlobalTheory.SiegelCov.vecCoordCE F E n
  haveI : LocallyCompactSpace (Fin n → AE F E) := Φ.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fin n → AE F E) := Φ.toHomeomorph.isInducing.secondCountableTopology
  haveI : T2Space (Fin n → AE F E) := Φ.toHomeomorph.isEmbedding.t2Space
  haveI : μ.IsAddHaarMeasure := hμ
  haveI : TopologicalSpace.PseudoMetrizableSpace (Fin n → AE F E) := inferInstance
  haveI : SigmaCompactSpace (Fin n → AE F E) := inferInstance
  haveI : μ.Regular := inferInstance
  set T : Matrix (Fin n) (Fin n) (AE F E) := ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) with hTdef
  have hT : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 (t⁻¹).isUnit
  set L := GlobalTheory.ModuLR.mulVecCE T hT with hL
  set Λ := LinearMap.toMatrix' ((GlobalTheory.SiegelCov.vecCoord F E n).toLinearMap ∘ₗ
    (Matrix.toLin' T).restrictScalars (AF F) ∘ₗ (GlobalTheory.SiegelCov.vecCoord F E n).symm.toLinearMap) with hΛdef
  haveI : Module.Free (AE F E) (Fin n → AE F E) := Module.Free.of_basis (Pi.basisFun (AE F E) (Fin n))
  have hdet : Λ.det = Algebra.norm (AF F) T.det := by
    rw [LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  have hΛ : IsUnit Λ.det := hdet ▸ hT.map (Algebra.norm (AF F))
  have hc : GlobalTheory.ModuLR.mulVecCE Λ hΛ = (Φ.symm.trans L).trans Φ := by
    ext x
    rw [GlobalTheory.ModuLR.mulVecCE_apply, LinearMap.toMatrix'_mulVec]
    rfl
  have hχ : addEquivAddHaarChar L = distribHaarChar (AF F) hΛ.unit := by
    rw [← GlobalTheory.SiegelCov.addEquivAddHaarChar_mulVecCE_adele, hc, GlobalTheory.ModuLR.addEquivAddHaarChar_transport]
  have hu : hΛ.unit = (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))⁻¹ := by
    ext
    rw [IsUnit.unit_spec, hdet, hTdef]
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have key := addEquivAddHaarChar_smul_map μ L
  set c := addEquivAddHaarChar L with hcdef
  have hc0 : c ≠ 0 := (addEquivAddHaarChar_pos L).ne'
  have hmap : μ.map L = c⁻¹ • μ := by
    calc μ.map L = (c⁻¹ * c) • μ.map L := by rw [inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ y, f (T *ᵥ y) ∂μ = ∫ y, f y ∂(μ.map L) :=
    (integral_map_equiv L.toHomeomorph.toMeasurableEquiv f).symm
  have hmodu : ((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
      (Matrix.GeneralLinearGroup.det t)) : ℝ≥0) = c⁻¹ := by
    rw [hχ, hu, map_inv, inv_inv]
    rfl
  show ∫ y, f (T *ᵥ y) ∂μ = _
  rw [hint, hmap, integral_smul_nnreal_measure, hmodu, NNReal.smul_def, Complex.real_smul]
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertSphStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma incM_vecMulVec {n d : ℕ} (x : Fin n → E) (y : Fin d → E) :
    incM F (Matrix.vecMulVec x y) =
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (fun j => inclR (F := F) (AF F) (y j)) := by
  ext i j
  simp [incM, Matrix.vecMulVec_apply, map_mul]

lemma smul_vecMulVec {n d : ℕ} (a : AF F) (p : Fin n → AE F E) (q : Fin d → AE F E) :
    a • Matrix.vecMulVec p q = Matrix.vecMulVec p (a • q) := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_smul_comm]

lemma vecMulVec_mul_transpose {n d : ℕ} (p : Fin n → AE F E) (q : Fin d → AE F E)
    (M : Matrix (Fin d) (Fin d) (AE F E)) :
    Matrix.vecMulVec p q * Mᵀ = Matrix.vecMulVec p (M *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma vecMulVec_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {x : Fin n → E} (hx : x ∈ X.L)
    {q : Fin d → AE F E} (hq : q ∈ GlobalTheory.InertSph.latAt W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latAtV X W v := by
  apply GlobalTheory.VacTransport.vecMulVec_mem <;> assumption

end GlobalTheory.InertSphStab
end
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem fockM_comm_sum {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (j k : W × (Ix P Q × Ix R S)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAt j z w a b * star (unitAt k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  apply GlobalTheory.CCRFock.CommDM.sum_unitAt <;> assumption

theorem fockM_comm : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ j k : W × (Ix P Q × Ix R S), GlobalTheory.CCRFock.fockM H j * GlobalTheory.CCRFock.fockM H k = GlobalTheory.CCRFock.fockM H k * GlobalTheory.CCRFock.fockM H j := by
  intro V _ _ W _ _ P Q R S H _ _ hc j k
  have h11 := hc (unitAt j 1) (unitAt k 1)
  have h1i := hc (unitAt j 1) (unitAt k Complex.I)
  have hi1 := hc (unitAt j Complex.I) (unitAt k 1)
  have hii := hc (unitAt j Complex.I) (unitAt k Complex.I)
  rw [fockM_comm_sum] at h11 h1i hi1 hii
  by_cases hjk : j = k
  · rw [hjk]
  · simp only [if_neg hjk, Complex.zero_im, Complex.ofReal_zero, mul_zero, zero_smul, sub_eq_zero] at h11 h1i hi1 hii
    unfold fockM
    have c : Commute (H (unitAt j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I))
        (H (unitAt k 1) - (lineSign k.2.1 k.2.2 * Complex.I) • H (unitAt k Complex.I)) :=
      Commute.sub_left (Commute.sub_right h11 (Commute.smul_right h1i _))
        (Commute.smul_left (Commute.sub_right hi1 (Commute.smul_right hii _)) _)
    exact ((c.smul_left _).smul_right _).eq

end GlobalTheory.CCRFock
end

section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.LowStable

theorem X_mul_pderiv_totalDegree_le {σ : Type} (u v : σ) (g : MvPolynomial σ ℂ) :
    (X u * pderiv v g).totalDegree ≤ g.totalDegree := by
  apply GlobalTheory.KFixIrr.LowStable.deg_X_pderiv <;> assumption

theorem omE_mem_restrictTotalDegree {P Q R S : ℕ} (D : ℕ) (u v : Ln P Q R S) (h : linePos u = linePos v)
    (g : Pol P Q R S) (hg : g ∈ restrictTotalDegree (Ln P Q R S) ℂ D) :
    omE u v g ∈ restrictTotalDegree (Ln P Q R S) ℂ D := by
  have hN := (mem_restrictTotalDegree _ _ _).1 hg
  have hXd : ∀ a b : Ln P Q R S, X a * pderiv b g ∈ restrictTotalDegree (Ln P Q R S) ℂ D :=
    fun a b => (mem_restrictTotalDegree _ _ _).2 ((X_mul_pderiv_totalDegree_le a b g).trans hN)
  cases hu : linePos u
  · rw [GlobalTheory.CompactHarm.omE_nn u v hu (h ▸ hu) g]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (hXd v u)) (Submodule.smul_mem _ _ hg)
  · rw [GlobalTheory.CompactHarm.omE_pp u v hu (h ▸ hu) g]
    exact Submodule.add_mem _ (hXd u v) (Submodule.smul_mem _ _ hg)

theorem fockAct2_apply_eq {P Q R S : ℕ} (Z : Mat R S) (g : Pol P Q R S) :
    fockAct2 P Q R S Z g = ∑ c, ∑ d, Z c d • ∑ a, omE (a, c) (a, d) g := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]

  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have : Matrix.single c d (Z c d) = Z c d • (Eab c d : Mat R S) := by
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply, fockAct2_Eab, LinearMap.sum_apply]

theorem fockAct2_mem_restrictTotalDegree {P Q R S : ℕ} (D : ℕ) (Z : Mat R S) (hZ : IsKC Z)
    (g : Pol P Q R S) (hg : g ∈ restrictTotalDegree (Ln P Q R S) ℂ D) :
    fockAct2 P Q R S Z g ∈ restrictTotalDegree (Ln P Q R S) ℂ D := by
  rw [fockAct2_apply_eq]
  refine Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ => ?_
  by_cases hcd : sameBlock c d
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
    refine omE_mem_restrictTotalDegree D _ _ ?_ g hg
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      first | rfl | exact absurd hcd (by simp [sameBlock])
  · rw [hZ c d hcd, zero_smul]
    exact Submodule.zero_mem _

theorem lowOne_stable : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k →
    x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ Z : Formalism.BasicNotions.TH.Mat R S, Formalism.BasicNotions.TH.IsKC Z →
    ∀ f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k'),
    Formalism.BasicNotions.TH.fockAct2 P Q R S Z f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') := by
  intro P Q R S x k k' _ _ Z hZ f hf
  rw [GlobalTheory.KFixIrr.lowOne, Submodule.mem_inf] at hf ⊢
  refine ⟨?_, fockAct2_mem_restrictTotalDegree _ Z hZ f hf.2⟩
  rw [GlobalTheory.KFixIrr.mem_chiOne] at hf ⊢
  intro X hX
  have hc := LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.2 X Z) f
  rw [Module.End.mul_apply, Module.End.mul_apply] at hc
  rw [hc, hf.1 X hX, map_smul]

end GlobalTheory.LowStable
end

section

noncomputable section

namespace GlobalTheory.FieldBaseChange

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem exists_functional_det_map_ne_zero [Infinite K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (hM : M.det ≠ 0) : ∃ ℓ : F →ₗ[K] K, (M.map ℓ).det ≠ 0 := by
  classical
  let e := Module.Basis.ofVectorSpace K F
  let φ : F →ₗ[K] MvPolynomial (Module.Basis.ofVectorSpaceIndex K F) K := e.constr K MvPolynomial.X
  by_contra h
  push Not at h
  have hP : (M.map φ).det = 0 := by
    refine MvPolynomial.funext fun c => ?_
    have hc : ∀ x, MvPolynomial.aeval c (φ x) = e.constr K c x := fun x =>
      LinearMap.congr_fun (e.ext (f₁ := (MvPolynomial.aeval c).toLinearMap ∘ₗ φ) (f₂ := e.constr K c)
        (fun i => by simp [φ])) x
    rw [map_zero, ← h (e.constr K c), RingHom.map_det]
    congr 1
    ext i j
    exact hc _
  have hc : ∀ x, MvPolynomial.aeval e (φ x) = x := fun x =>
    LinearMap.congr_fun (e.ext (f₁ := (MvPolynomial.aeval e).toLinearMap ∘ₗ φ) (f₂ := LinearMap.id)
      (fun i => by simp [φ])) x
  apply hM
  have := congrArg (MvPolynomial.aeval (R := K) e) hP
  rw [map_zero, AlgHom.map_det] at this
  rw [← this]
  congr 1
  ext i j
  exact (hc _).symm

variable {V W V' W' : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W']

theorem IsExtension.exists_basis {a : V →ₛₗ[algebraMap K F] V'} (h : IsExtension a) {ι : Type}
    (v : Module.Basis ι K V) : ∃ v' : Module.Basis ι F V', ∀ i, v' i = a (v i) := by
  apply GlobalTheory.ConstFam.exists_basis_of_isExtension <;> assumption

theorem IsCoord.map_algebraMap_smul {a : V →ₛₗ[algebraMap K F] V'}
    (h : Submodule.span F (Set.range a) = ⊤) {ℓ : F →ₗ[K] K} {Λ : V' →+ V} (hΛ : IsCoord a ℓ Λ)
    (k : K) (x : V') : Λ (algebraMap K F k • x) = k • Λ x :=
  IsCoord.natural h hΛ hΛ (k • LinearMap.id) (algebraMap K F k • LinearMap.id)
    (fun v => by simp [map_smulₛₗ]) x

theorem exists_intertwining_bijective_of_extension (K F : Type) [Field K] [Field F] [Algebra K F]
    [Infinite K] (V W V' W' : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W'] [FiniteDimensional F V']
    (iV : V →ₛₗ[algebraMap K F] V') (iW : W →ₛₗ[algebraMap K F] W')
    (hV : IsExtension iV) (hW : IsExtension iW)
    (J : Type) (a : J → V →ₗ[K] V) (b : J → W →ₗ[K] W) (a' : J → V' →ₗ[F] V') (b' : J → W' →ₗ[F] W')
    (ha : ∀ i v, a' i (iV v) = iV (a i v)) (hb : ∀ i w, b' i (iW w) = iW (b i w))
    (E' : V' →ₗ[F] W') (hE' : Function.Bijective E') (hc : ∀ i v, E' (a' i v) = b' i (E' v)) :
    ∃ E : V →ₗ[K] W, Function.Bijective E ∧ ∀ i v, E (a i v) = b i (E v) := by
  classical
  let v := Module.Basis.ofVectorSpace K V
  let w₀ := Module.Basis.ofVectorSpace K W
  obtain ⟨v', hv'⟩ := hV.exists_basis v
  obtain ⟨w₀', -⟩ := hW.exists_basis w₀
  let e := LinearEquiv.ofBijective E' hE'
  let w := w₀.reindex (w₀'.indexEquiv (v'.map e))
  obtain ⟨w', hw'⟩ := hW.exists_basis w
  haveI := Module.Finite.finite_basis v'
  letI := Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex K V)
  have hdet : (LinearMap.toMatrix v' w' E').det ≠ 0 := (LinearEquiv.isUnit_det e v' w').ne_zero
  obtain ⟨ℓ, hℓ⟩ := exists_functional_det_map_ne_zero (K := K) _ hdet
  obtain ⟨Λ, hΛ⟩ := hW.coord ℓ
  let E : V →ₗ[K] W :=
    { toFun := fun x => Λ (E' (iV x))
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun k x => by
        rw [map_smulₛₗ, map_smul, hΛ.map_algebraMap_smul hW.span]; rfl }
  have hM : LinearMap.toMatrix v w E = (LinearMap.toMatrix v' w' E').map ℓ := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have : E (v j) = ∑ k, ℓ (w'.repr (E' (v' j)) k) • w k := by
      show Λ (E' (iV (v j))) = _
      rw [← hv']

      conv_lhs => rw [← w'.sum_repr (E' (v' j)), map_sum]
      simp only [hw', hΛ _ _]
    rw [this, w.repr_sum_self]
  refine ⟨E, ?_, fun i x => ?_⟩
  · have hu : IsUnit (LinearMap.toMatrix v w E).det := by rw [hM]; exact hℓ.isUnit
    exact (LinearEquiv.ofIsUnitDet hu).bijective
  · show Λ (E' (iV (a i x))) = b i (Λ (E' (iV x)))
    rw [← ha, hc]
    exact IsCoord.natural hW.span hΛ hΛ (b i) (b' i) (hb i) _

end GlobalTheory.FieldBaseChange
end
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.word_reaching_irreducible_k_module_reaches_highest_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → KUnit ε E → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → ∀ Λ : Fin n → ℝ, (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = Λ) → ∀ (μ : Fin n → ℝ) (w : V), KHighest ε E μ w → ∀ (s t : Bool) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t) → ∀ x ∈ L, ⟪x, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 → ∃ l' : List (Fin n × Fin n), l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ μ + (l'.map fun p : Fin n × Fin n => root p.1 p.2).sum = Λ := by
  first | exact @GlobalTheory.HdStep.main | exact GlobalTheory.HdStep.main | (intros; apply GlobalTheory.HdStep.main <;> assumption)
end
