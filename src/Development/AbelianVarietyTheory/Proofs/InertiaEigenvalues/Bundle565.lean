module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle536
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle541
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.GlobalFields.Adele.Topology
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle542
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSourceHighestWeightFockStableSubspace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockInnerProductPosDefCompactMatrixUnitAdjoint
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryRepresentativesExistVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle533
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle532
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_galois_eq_embeddings_OC_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (D : Type) [CommRing D] [IsDomain D] (θ₁ θ₂ : OC l →+* D), Function.Injective θ₁ → Function.Injective θ₂ → (∀ r : ↥(OL K), θ₁ (intToOC K r) = θ₂ (intToOC K r)) → ∃ g : ↥(GK K), (∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO (g : GQ l) y)) ∧ ∀ y : OC l, ((l : ℕ) : D) ∣ θ₂ y - θ₁ (Per.σO (g : GQ l) y) := by
  first | exact @GlobalTheory.EmbTwo.exists_gal_eq | exact GlobalTheory.EmbTwo.exists_gal_eq | (intros; apply GlobalTheory.EmbTwo.exists_gal_eq <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ringOfIntegers_finiteExt_isDVR_finite_unit_iff : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), IsDiscreteValuationRing ↥(OL K) ∧ Module.Finite ℤ_[l] ↥(OL K) ∧ ∀ x : ↥(OL K), IsUnit x ↔ IsUnit (intToOC K x) := by
  first | exact @GlobalTheory.IntDvr.main | exact GlobalTheory.IntDvr.main | (intros; apply GlobalTheory.IntDvr.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.span_eq_ker_theta_of_distinguished_ainf : ∀ (l : ℕ) [Fact l.Prime] (x : Ainf l), Per.θ l x = 0 → IsUnit ((ainfDelta l).δ x) → Ideal.span {x} = RingHom.ker (Per.θ l) := by
  first | exact @GlobalTheory.BSP.span_eq_ker_theta_of_distinguished | exact GlobalTheory.BSP.span_eq_ker_theta_of_distinguished | (intros; apply GlobalTheory.BSP.span_eq_ker_theta_of_distinguished <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.etaleRealisation_indep_ainfModel : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e₀ : P₀.A ≃+* Ainf l), IsAinf K P₀ e₀ → ∃ a : Hom P₀ (ainfObj K), ∀ (M : FCrys l ↥(OL K)), Function.Bijective (M.tr a) ∧ ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)), (∀ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ → ∃ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j) ∧ (∀ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j → ∃ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ ∧ ∀ x, j₀ (M.tr a x) = j x) := by
  first | exact @GlobalTheory.Prism.realisation_indep_model | exact GlobalTheory.Prism.realisation_indep_model | (intros; apply GlobalTheory.Prism.realisation_indep_model <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
open scoped Pointwise

namespace GlobalTheory.AdeleScale

variable {E : Type} [Field E] [NumberField E]

theorem qV_ne_zero (v : HeightOneSpectrum (𝓞 E)) : (qV E v : ℝ) ≠ 0 := by
  rw [qV, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

theorem finId_adl_snd (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (v : HeightOneSpectrum (𝓞 E)) :
    ((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).2 v = ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
  change ((1 : Af E) - 1 + ((GlobalTheory.CellDec.adl ϖ m : (Af E)ˣ) : Af E)) v = _
  rw [sub_self, zero_add]
  rfl

theorem finId_fst (a : (Af E)ˣ) : ((finId E a : AdeleRing (𝓞 E) E)).1 = 1 := by
  change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
  rw [sub_zero, add_zero]

theorem ideleModule_finId_adl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))) (hs : ∀ v, v ∉ s → m v = 0) :
    (GroundTheory.Global.IdeleGroup.ideleModule E (finId E (GlobalTheory.CellDec.adl ϖ m)) : ℝ) =
      ∏ v ∈ s, ((qV E v : ℝ) ^ m v)⁻¹ := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h1 : ∀ w : InfinitePlace E,
      ‖((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).1 w‖ ^ w.mult = 1 := fun w => by
    rw [finId_fst]
    change ‖(1 : w.Completion)‖ ^ w.mult = 1
    rw [norm_one, one_pow]
  have h2 : ∀ v : HeightOneSpectrum (𝓞 E),
      ‖((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).2 v‖ = ((qV E v : ℝ) ^ m v)⁻¹ := fun v => by
    have hu : Valued.v ((ϖ v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := hϖ v
    rw [finId_adl_snd, Units.val_zpow_eq_zpow_val, norm_zpow, GroundTheory.Global.norm_uniformizer hu, _root_.inv_zpow]
    rfl
  rw [Finset.prod_eq_one fun w _ => h1 w, one_mul]
  simp_rw [h2]
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hvs
  exact hv (by show ((qV E v : ℝ) ^ m v)⁻¹ = 1; rw [hs v hvs, zpow_zero, inv_one])

end GlobalTheory.AdeleScale


open GlobalTheory.AdeleScale in
theorem GlobalTheory.AdeleScale.map_mul_finId_adl : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))), (∀ v, v ∉ s → m v = 0) →
    ∀ [MeasurableSpace (AdeleRing (𝓞 E) E)] [BorelSpace (AdeleRing (𝓞 E) E)] (μR : Measure (AdeleRing (𝓞 E) E)) [μR.IsAddHaarMeasure],
    Measure.map (fun x : AdeleRing (𝓞 E) E => ((finId E (GlobalTheory.CellDec.adl ϖ m) : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) * x) μR =
      ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) • μR := by
  intro E _ _ ϖ hϖ m s hs _ _ μR _
  set a : (AdeleRing (𝓞 E) E)ˣ := finId E (GlobalTheory.CellDec.adl ϖ m) with ha
  have hm : Measurable fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x :=
    (continuous_const.mul continuous_id).measurable
  have hchar : distribHaarChar (AdeleRing (𝓞 E) E) a • μR.map (fun x => (a : AdeleRing (𝓞 E) E) * x) = μR := by
    ext S hS
    rw [Measure.smul_apply, Measure.map_apply hm hS]
    have h1 := distribHaarChar_mul μR a ((fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x) ⁻¹' S)
    have e : a • ((fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x) ⁻¹' S) = S := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp [Units.smul_def]
    rw [e] at h1
    rw [ENNReal.smul_def, smul_eq_mul]
    exact h1
  have hmod : (distribHaarChar (AdeleRing (𝓞 E) E) a : ℝ) = ∏ v ∈ s, ((qV E v : ℝ) ^ m v)⁻¹ := by
    rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing]
    exact ideleModule_finId_adl ϖ hϖ m s hs
  have hone : ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) * (distribHaarChar (AdeleRing (𝓞 E) E) a : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ =>
      zpow_nonneg (Nat.cast_nonneg _) _), hmod, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun v _ => mul_inv_cancel₀ (zpow_ne_zero _ (qV_ne_zero v)), ENNReal.ofReal_one]
  conv_rhs => rw [← hchar]
  rw [ENNReal.smul_def (distribHaarChar (AdeleRing (𝓞 E) E) a), smul_smul, hone, one_smul]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.fockTargetMatrixUnit_compact_totalDegree_le : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m), GlobalTheory.LowestKType.Cpt w τ a b → ∀ (d : ℕ) (P : PolF D m n), P.totalDegree ≤ d → (GlobalTheory.LowestKType.kop w τ a b P).totalDegree ≤ d := by
  first | exact @GlobalTheory.LowestKType.kop_totalDegree_le | exact GlobalTheory.LowestKType.kop_totalDegree_le | (intros; apply GlobalTheory.LowestKType.kop_totalDegree_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.exists_sourceHighestWeight_fock_stable_subspace : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (V : Submodule ℂ (PolF D m n)), FiniteDimensional ℂ V → V ≠ ⊥ → (∀ P ∈ V, ∀ (τ : D.what₂.Tau) (a b : Fin n), GlobalTheory.LowestKType.sop w τ a b P ∈ V) → ∃ P ∈ V, P ≠ 0 ∧ ∃ lam : D.what₂.Tau → Fin n → ℂ, GlobalTheory.LowestKType.IsNHw w lam P := by
  first | exact @GlobalTheory.exists_nHw_of_fockS_stable | exact GlobalTheory.exists_nHw_of_fockS_stable | (intros; apply GlobalTheory.exists_nHw_of_fockS_stable <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.fockInnerProduct_posDef_compact_matrixUnit_adjoint : ∀ (D : D7) (n m : ℕ), ∃ B : PolF D m n →ₗ⋆[ℂ] PolF D m n →ₗ[ℂ] ℂ, (∀ P, (B P P).im = 0 ∧ 0 ≤ (B P P).re) ∧ (∀ P, B P P = 0 → P = 0) ∧ ∀ (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m), GlobalTheory.LowestKType.Cpt w τ a b → ∀ P Q, B (GlobalTheory.LowestKType.kop w τ a b P) Q = B P (GlobalTheory.LowestKType.kop w τ b a Q) := by
  first | exact @GlobalTheory.LowestKType.fockForm_kop_adjoint | exact GlobalTheory.LowestKType.fockForm_kop_adjoint | (intros; apply GlobalTheory.LowestKType.fockForm_kop_adjoint <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.unitary_representatives_exist_vector : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W) (ψ : W →ₗ[ℂ] PolF D m n), Function.Injective ψ → (∀ (k : K) (x : W), ψ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ x)) → ∀ (τ : D.what₂.Tau) (a b : Fin n), ∃ A : Module.End ℂ W, ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (x : W), φ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ x)) → φ ∘ₗ A = GlobalTheory.LowestKType.sop w τ a b ∘ₗ φ := by
  first | exact @GlobalTheory.UnitaryToGl.exists_transport_sop | exact GlobalTheory.UnitaryToGl.exists_transport_sop | (intros; apply GlobalTheory.UnitaryToGl.exists_transport_sop <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem lx_eq_of_rep_rel {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} {x y : LX R i v}
    (h : (rep x)⁻¹ * rep y ∈ levW R i) : x = y := by
  have : (Quotient.mk _ (Quotient.out x) : LX R i v) = Quotient.mk _ (Quotient.out y) := by
    apply Quotient.sound
    change ((QuotientGroup.leftRel (levW R i)).comap (Subtype.val : locSet R i v → GA D (Wc D i))) _ _
    rw [Setoid.comap_rel, QuotientGroup.leftRel_apply]
    exact h
  exact (Quotient.out_eq x).symm.trans (this.trans (Quotient.out_eq y))

theorem rep_notMem_levW {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} {x : LX R i v}
    (hx : x ≠ lx0 R i v) : rep x ∉ levW R i := fun h =>
  hx (lx_eq_of_rep_rel ((levW R i).mul_mem ((levW R i).inv_mem h) (trivial_level_coset_representative_mem_level R i v)))

theorem rep_suppF {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    SuppF (Wc D i) (fid D v) (rep x) := (Quotient.out x).2.2

theorem eq_one_of_suppF_zero {V : HSp D} {g : GA D V} (h : SuppF V 0 g) : g = 1 := by
  have e : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V 1 := by
    have h1 : Formalism.L2.Theta.mt V 1 = 1 := rfl
    rw [h1, ← sub_eq_zero]
    ext a b
    have := h a b
    simpa [eq_comm] using this
  exact Subtype.ext (Units.ext e)

end

theorem acoef_small : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (Eu.LX R i v)), Eu.lx0 R i v ∉ C → ∑ x ∈ C, ‖Eu.acoef R i t μ 𝓕 v x‖ ≤ s v := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hLS μ 𝓕 hμ
  obtain ⟨s, hs, hs1, hb⟩ := hLS μ 𝓕 hμ
  refine ⟨fun v => max (s v) 0, ?_, fun v => max_lt (hs1 v) one_pos, ?_⟩
  · refine Summable.of_nonneg_of_le (fun v => le_max_right _ _) (fun v => ?_) hs.abs
    exact max_le (le_abs_self _) (abs_nonneg _)
  · intro v C hC
    by_cases hex : ∃ f, IsFinIdem D v f
    · have hf : IsFinIdem D v (fid D v) := by
        unfold fid
        rw [dite_eq_left hex]
        exact hex.choose_spec
      have hinj : Function.Injective (rep : LX R i v → GA D (Wc D i)) := fun x y h =>
        lx_eq_of_rep_rel (by rw [h, inv_mul_cancel]; exact (levW R i).one_mem)
      have := hb v _ hf (C.image rep) ?_ ?_
      · rw [Finset.sum_image (fun x _ y _ h => hinj h)] at this
        exact this.trans (le_max_left _ _)
      · intro g hg
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
        exact ⟨rep_suppF x, rep_notMem_levW fun e => hC (e ▸ hx)⟩
      · intro g hg g' hg' h
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hg'
        rw [lx_eq_of_rep_rel h]
    · have hf : fid D v = 0 := by
        unfold fid
        rw [dite_eq_right hex]
      have hC0 : C = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
        have h1 : rep x = 1 := eq_one_of_suppF_zero (hf ▸ rep_suppF x)
        exact rep_notMem_levW (fun e => hC (e ▸ hx)) (h1 ▸ (levW R i).one_mem)
      rw [hC0, Finset.sum_empty]
      exact le_max_right _ _

end GlobalTheory.RawLift.Eu

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

theorem prod_toList_insert_comm {ι M : Type} [Monoid M] [DecidableEq ι] (s : Finset ι) (v : ι) (hv : v ∉ s) (f : ι → M)
    (hc : ∀ a b, a ≠ b → Commute (f a) (f b)) :
    ((insert v s).toList.map f).prod = (s.toList.map f).prod * f v := by
  have hp : ((insert v s).toList.map f).Perm ((v :: s.toList).map f) := (Finset.toList_insert hv).map f
  have hpw : ((insert v s).toList.map f).Pairwise Commute := by
    rw [List.pairwise_map]
    exact (Finset.nodup_toList _).imp fun h => hc _ _ h
  rw [hp.prod_eq' hpw, List.map_cons, List.prod_cons]
  refine (Commute.list_prod_right _ _ fun y hy => ?_).eq
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
  refine hc _ _ ?_
  rintro rfl
  exact hv (Finset.mem_toList.1 hw)

theorem fid_orth (D : D7) {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w) : fid D v * fid D w = 0 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  unfold fid
  split_ifs with h1 h2
  · obtain ⟨ε, hε, e⟩ := h1.choose_spec
    obtain ⟨ε', hε', e'⟩ := h2.choose_spec
    rw [e, e']
    exact GlobalTheory.IdemSupport.place_orth hΦ hε hε' h
  · exact mul_zero _
  · exact zero_mul _
  · exact zero_mul _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rep_mem_locSet {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    rep x ∈ locSet R i v := (Quotient.out x).2

theorem rep_commute {R : RealDat D A Ks} {i : Fin D.R.m} {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w)
    (x : LX R i v) (y : LX R i w) : Commute (rep x) (rep y) :=
  GlobalTheory.IdemSupport.commute_of_suppF _ (fid_orth D h) (rep_mem_locSet x).2 (rep_mem_locSet y).2

theorem famProd_mem_GfC (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) :
    famProd R i F ∈ GfC (Wc D i) := by
  unfold famProd
  split_ifs with h
  · refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
    exact (rep_mem_locSet _).1
  · exact Subgroup.one_mem _

theorem bop_congr (R : RealDat D A Ks) (i : Fin D.R.m) {γ γ' : GA D (Wc D i)}
    (h : trPair R i γ = trPair R i γ') : Bop R i γ = Bop R i γ' := by
  unfold Bop
  rw [h]

theorem famProd_update_of_ne (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v)
    (hF : {w | F w ≠ lx0 R i w}.Finite) (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : F v = lx0 R i v) (x : LX R i v)
    (hx : x ≠ lx0 R i v) : famProd R i (Function.update F v x) = famProd R i F * rep x := by
  have hs : {w | Function.update F v x w ≠ lx0 R i w} = insert v {w | F w ≠ lx0 R i w} := by
    ext w
    by_cases hw : w = v
    · subst hw
      simp [hx]
    · simp [hw]
  have hF' : {w | Function.update F v x w ≠ lx0 R i w}.Finite := by
    rw [hs]; exact hF.insert v
  have ht : hF'.toFinset = insert v hF.toFinset := by
    ext w
    rw [Set.Finite.mem_toFinset, hs, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_insert_iff]
  have hnv : v ∉ hF.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact fun h => h hv
  unfold famProd
  rw [dite_eq_left hF, dite_eq_left hF', ht,
    prod_toList_insert_comm hF.toFinset v hnv (fun w => rep (Function.update F v x w))
      (fun a b h => rep_commute h _ _)]
  congr 1
  · congr 1
    refine List.map_congr_left fun w hw => ?_
    have : w ≠ v := by
      rintro rfl
      exact hnv (Finset.mem_toList.1 hw)
    rw [Function.update_of_ne this]
  · simp only [Function.update_self]

theorem bop_famProd_update : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i, TransLaws R i → ∀ (F : ∀ v, Eu.LX R i v), {w | F w ≠ Eu.lx0 R i w}.Finite → ∀ v, F v = Eu.lx0 R i v → Eu.famProd R i F ∈ GfC (Wc D i) ∧ ∀ x : Eu.LX R i v, Eu.Bop R i (Eu.famProd R i (Function.update F v x)) = Eu.Bop R i (Eu.famProd R i F * Eu.rep x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hTL F hF v hv
  refine ⟨famProd_mem_GfC R i F, fun x => ?_⟩
  by_cases hx : x = lx0 R i v
  · have hu : Function.update F v x = F := by
      rw [hx, ← hv]; exact Function.update_eq_self v F
    rw [hu]
    refine bop_congr R i (funext fun a => funext fun b => ?_)
    have := hTL.2.2.2.1 _ (famProd_mem_GfC R i F) 1 (Subgroup.one_mem _) (rep x) (hx ▸ trivial_level_coset_representative_mem_level R i v) a b
    rw [one_mul] at this
    exact this.symm
  · rw [famProd_update_of_ne R i F hF v hv x hx]

end GlobalTheory.RawLift.Eu

end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.XNTransfer

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem exists_aN_iff (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : LetA O n)
    (r : RA) (hr : E.io a = r) (w : TW RW T) :
    (∃ z ∈ aN W T a, E.jD T z = w) ↔ ∃ y ∈ E.jD T '' (W.N T : Set (W.DD T)), w = inclR r • y := by
  have hs : ∀ x : W.DD T, E.jD T (a • x) = inclR r • E.jD T x := fun x => by
    rw [← algebraMap_smul W.EE a x, E.jD_smul, E.ioE_ext, hr]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, hs x⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, ⟨x, hx, rfl⟩, hs x⟩

end Generic

theorem image_map_refl {O R M : Type} [CommRing O] [AddCommGroup R] [Module O R] [AddCommGroup M]
    [Module O M] (S : Set (R ⊗[O] M)) :
    (TensorProduct.map (LinearMap.id : R →ₗ[O] R) (LinearEquiv.refl O M).toLinearMap) '' S = S := by
  have : TensorProduct.map (LinearMap.id : R →ₗ[O] R) (LinearEquiv.refl O M).toLinearMap = LinearMap.id :=
    TensorProduct.map_id
  rw [this]
  exact Set.image_id S


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X → ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, ((F l).E K s LL h).tie.jD T z = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) z') := by
  intro D HW F l _ K s LL h K' h' hle hK0 T hT z' hz'
  have hN := ((GlobalTheory.NL.BaseField.base_indep D HW F l K s LL h K' h' hle hK0).2.2 T
    (resLt (K := K) (K' := K') (LL := LL) hle T) (LinearEquiv.refl ↥(OL LL) ↥T.L.T) (fun _ _ => rfl)).2 hT
    (restrict_crys D hle T hT)
  have hN2 := (image_map_refl (O := ↥(OL LL)) (R := RW LL) (M := ↥T.L.T) _).symm.trans hN
  have h1 := (exists_aN_iff ((F l).E K' s LL h').tie (resLt (K := K) (K' := K') (LL := LL) hle T) _ _
    (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').1 _).1 ⟨z', hz', rfl⟩
  refine (exists_aN_iff ((F l).E K s LL h).tie T _ _ (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).1 _).2 ?_
  refine h1.elim fun y hy => ⟨toTW hle T y, ?_, hy.2⟩
  exact hN2.subset hy.1

end GlobalTheory.NL.XNTransfer
end
end
