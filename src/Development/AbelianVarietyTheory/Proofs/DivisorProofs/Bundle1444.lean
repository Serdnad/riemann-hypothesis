module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralBoundSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

theorem _root_.GlobalTheory.T.unitaryLattice_eq_iff_inv_mul_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ q q' : UL n w, unitLat e B ψ q = unitLat e B ψ q' ↔ q⁻¹ * q' ∈ KL n w := by
  first | exact @GlobalTheory.InertUnitLat.unitLat_eq_iff | exact GlobalTheory.InertUnitLat.unitLat_eq_iff | (intros; apply GlobalTheory.InertUnitLat.unitLat_eq_iff <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (A : GL (Fin n) (Cinf E)) (F : (Fin n → Fin n → Cinf E) → ℂ), ∫ a, F a = ∫ h : (Fin n → Fin n → Cinf E), ((jacInf (A : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) * F (fun i j => ((A : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) := by
  first | (exact @GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf) | (exact GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf) | (intros; apply GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf  <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ), IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η → ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ), (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) → (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) → IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (exact GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (intros; apply GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf  <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.schwartz_integral_bound_smooth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → ∀ (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)), IsRapidFamInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) (secKInf R σ₀ κ τ) (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ) := by
  first | (exact @GlobalTheory.JSW.MirCinf.SecFamInf.isRapidFamInf_secKInf) | (exact GlobalTheory.JSW.MirCinf.SecFamInf.isRapidFamInf_secKInf) | (intros; apply GlobalTheory.JSW.MirCinf.SecFamInf.isRapidFamInf_secKInf  <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

theorem _root_.GlobalTheory.T.exists_integer_of_algebraMap_mem_adelesFiniteMultiple : ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ), 0 < m →
    algebraMap F (AF F) y ∈ intF F m → ∃ r : 𝓞 F, y = m * r := by
  first | exact @GlobalTheory.HeckeExtend.exists_int_of_mem_intF | exact GlobalTheory.HeckeExtend.exists_int_of_mem_intF | (intros; apply GlobalTheory.HeckeExtend.exists_int_of_mem_intF <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

theorem _root_.GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (x : AF F),
    algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E N → Module.finrank F E • x ∈ intF F N := by
  first | exact @GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF | exact GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF | (intros; apply GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

theorem _root_.GlobalTheory.T.isOpen_integralTensorAdeleMultiples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    IsOpen (CE F E N : Set (AF F ⊗[F] E)) := by
  first | exact @GlobalTheory.HeckeExtend.CE_isOpen | exact GlobalTheory.HeckeExtend.CE_isOpen | (intros; apply GlobalTheory.HeckeExtend.CE_isOpen <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

theorem _root_.GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    ∀ w : AF F ⊗[F] E, At (evI F) w → w ∈ CE F E N := by
  first | exact @GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf | exact GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf | (intros; apply GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf <;> assumption)
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

theorem _root_.GlobalTheory.T.exists_splitPlace_localLatticeBasis_hyperbolicPlane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v) (n₁ : ℕ) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E) (β₁ : GL (Fin n₁) (Fv F v)) (i₀ i₁ : ℕ),
    i₀ < i₁ → i₁ < n₁ + 2 →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    (∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0) →
    PrimAt (GlobalTheory.AdelicU.splitPrime τ) L x → PrimAt (GlobalTheory.AdelicU.splitPrime τ) L y → GlobalTheory.AdelicU.IsSplitBasis τ (lowLat ι L) β₁ →
    ∃ β : GL (Fin (n₁ + 2)) (Fv F v), GlobalTheory.AdelicU.IsSplitBasis τ L β ∧ ∀ i : Fin (n₁ + 2),
      (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧ (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧
      ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j := by
  first | exact @GlobalTheory.PlaneSkewBasis.exists_isSplitBasis_plane_of_indep | exact GlobalTheory.PlaneSkewBasis.exists_isSplitBasis_plane_of_indep | (intros; apply GlobalTheory.PlaneSkewBasis.exists_isSplitBasis_plane_of_indep <;> assumption)
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

theorem _root_.GlobalTheory.T.orthogonalComplement_hyperbolicPlane_lattice_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n₁ : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E),
    (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) →
    (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    ∀ u, u ∈ lowLat ι L ↔ ∀ u' ∈ lowLat ι L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E (o * form σ (ιᵀ * J * ι.map σ) u u')) := by
  first | exact @GlobalTheory.PlaneSkewDual.lowLat_selfDual | exact GlobalTheory.PlaneSkewDual.lowLat_selfDual | (intros; apply GlobalTheory.PlaneSkewDual.lowLat_selfDual <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.TorusTheta

variable (F : Type) [Field F] [NumberField F]

theorem infScale_mul' (a b : ℝ) : infScale F a * infScale F b = infScale F (a * b) := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ = _
    rw [← map_mul, ← map_mul]
    rfl
  · show (1 : FiniteAdeleRing (𝓞 F) F) * 1 = 1
    exact mul_one 1

theorem infScale_one' : infScale F 1 = 1 := by
  simp only [infScale, map_one]
  rfl

theorem norm_infScale_fst (t : ℝ) (w : InfinitePlace F) : ‖(infScale F t).1 w‖ = |t| := by
  rw [← GroundTheory.Global.normAtPlace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply]
  simp only [infScale, RingEquiv.apply_symm_apply]
  exact mixedEmbedding.normAtPlace_real w t

theorem distribHaarChar_infScale (t : ℝ) (ht : 0 < t) (a : (AF F)ˣ) (ha : (a : AF F) = infScale F t) :
    (distribHaarChar (AF F) a : ℝ) = t ^ Module.finrank ℚ F := by
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖((a : AdeleRing (𝓞 F) F)).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [show (a : AdeleRing (𝓞 F) F) = infScale F t from ha]
    simp [infScale]
  rw [h2, mul_one]
  simp_rw [show (a : AdeleRing (𝓞 F) F) = infScale F t from ha, norm_infScale_fst, abs_of_pos ht]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

theorem lintegral_infScale_pi : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (u : κ → ℝ), (∀ j, 0 < u j) →
    ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (f : (κ → AF F) → ℝ≥0∞), ∫⁻ x, f (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) ∂μ =
      (ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F))⁻¹ * ∫⁻ x, f x ∂μ := by
  intro F _ _ κ _ u hu μ hμ f
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  let s : (κ → AF F)ˣ :=
    { val := fun j => infScale F (u j)
      inv := fun j => infScale F (u j)⁻¹
      val_inv := funext fun j => by
        show infScale F (u j) * infScale F (u j)⁻¹ = 1
        rw [infScale_mul', mul_inv_cancel₀ (hu j).ne', infScale_one']
      inv_val := funext fun j => by
        show infScale F (u j)⁻¹ * infScale F (u j) = 1
        rw [infScale_mul', inv_mul_cancel₀ (hu j).ne', infScale_one'] }
  have hχ : ((distribHaarChar (κ → AF F) s : ℝ≥0) : ℝ) = ∏ j, u j ^ Module.finrank ℚ F := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : κ => AF F), NNReal.coe_prod]
    exact Finset.prod_congr rfl fun j _ => distribHaarChar_infScale F (u j) (hu j) _ rfl
  have h1 : μ.map (fun x => s • x) = DomMulAct.mk s⁻¹ • μ := by
    ext A hA
    rw [Measure.map_apply (measurable_const_smul s) hA, Measure.domSMul_apply, Equiv.symm_apply_apply,
      Set.preimage_smul]
  have h2 : μ.map (fun x => s • x) = ((distribHaarChar (κ → AF F) s)⁻¹ : ℝ≥0) • μ := by
    rw [h1, Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk s⁻¹ • μ) μ,
      addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]
  have h3 : ∫⁻ x, f (fun j => infScale F (u j) * x j) ∂μ = ∫⁻ y, f y ∂(μ.map (fun x => s • x)) :=
    (lintegral_map_equiv f (Homeomorph.smul s).toMeasurableEquiv).symm
  rw [h3, h2, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul, ← hχ, ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_inv (distribHaarChar_pos).ne']

end GlobalTheory.TorusTheta
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

namespace GlobalTheory.DblInt

theorem elim_dot' {R : Type} [CommRing R] {κ κ' : Type} [Fintype κ] [Fintype κ'] (u v : κ → R) (x y : κ' → R) :
    Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

section Coord

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (w w' : Matrix α (β ⊕ β) E) :
    hTens c JA (dbl JB) w w' = hTens c JA JB w.toCols₁ w'.toCols₁ - hTens c JA JB w.toCols₂ w'.toCols₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Matrix.toCols₁_apply, Matrix.toCols₂_apply, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [← sub_eq_add_neg]

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (w w' : Matrix α (β ⊕ β) E) :
    symp c ξ JA (dbl JB) w w' = symp c ξ JA JB w.toCols₁ w'.toCols₁ - symp c ξ JA JB w.toCols₂ w'.toCols₂ := by
  unfold symp
  rw [hTens_dbl, mul_sub, map_sub]

variable [Invertible (2 : R)] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}

def dblCo (d : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ) where
  e :=
    { toFun := fun w => (Sum.elim (d.e w.toCols₁).1 (d.e w.toCols₂).1, Sum.elim (d.e w.toCols₁).2 (-(d.e w.toCols₂).2))
      map_add' := fun w w' => by
        have h1 : (w + w').toCols₁ = w.toCols₁ + w'.toCols₁ := by ext; simp
        have h2 : (w + w').toCols₂ = w.toCols₂ + w'.toCols₂ := by ext; simp
        rw [h1, h2, map_add (f := _), map_add (f := _)]
        ext k <;> cases k <;> simp [add_comm]
      map_smul' := fun a w => by
        have h1 : (a • w).toCols₁ = a • w.toCols₁ := by ext; simp
        have h2 : (a • w).toCols₂ = a • w.toCols₂ := by ext; simp
        rw [h1, h2, map_smul, map_smul]
        ext k <;> cases k <;> simp
      invFun := fun p => Matrix.fromCols (d.e.symm (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl))
        (d.e.symm (p.1 ∘ Sum.inr, -(p.2 ∘ Sum.inr)))
      left_inv := fun w => by
        simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, neg_neg, Prod.mk.eta, LinearEquiv.symm_apply_apply]
        exact Matrix.fromCols_toCols w
      right_inv := fun p => by
        simp only [Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, LinearEquiv.apply_symm_apply, neg_neg,
          Sum.elim_comp_inl_inr] }
  form w w' := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [symp_dbl, d.form, d.form, elim_dot', elim_dot', dotProduct_neg, dotProduct_neg]
    ring

theorem dblCo_isDblCoord (d : Darboux (symp c ξ JA JB) κ) : IsDblCoord c ξ JA JB d (dblCo c d) := fun w₁ w₂ => by
  simp [dblCo]

end Coord

section Equivs

variable {R : Type}

def conjE {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (X → ℂ) :=
  LinearEquiv.ofLinear (conjMap T.toLinearMap) (conjMap T.symm.toLinearMap)
    (LinearMap.ext fun φ => by simp [conjMap_apply]) (LinearMap.ext fun φ => by simp [conjMap_apply])

theorem conjE_apply {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) (φ : X → ℂ) : conjE T φ = star (T (star φ)) := rfl

def partLE {κ κ' : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partL T.toLinearMap) (partL T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])

def partRE {κ κ' : Type} (T : ((κ' → R) → ℂ) ≃ₗ[ℂ] ((κ' → R) → ℂ)) : ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partR T.toLinearMap) (partR T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])

def dblE {κ : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : ((κ ⊕ κ → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → R) → ℂ) :=
  (partRE (conjE T)).trans (partLE T)

end Equivs

end GlobalTheory.DblInt
end
end
