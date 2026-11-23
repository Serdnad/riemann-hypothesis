module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle010
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle404
public import GroundTheory.AutomorphicForms.ReductionMahler
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle406
import GroundTheory.AutomorphicForms.Reduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle405
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle392
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle407
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001

@[expose] public section

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem convR_lift_splitCentre_mul (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ)
    (F : L2 (latticeGL E a) μ) (hF : F ∈ L2cusp μ) (t : ℝ) (x : GA E a) :
    convR μ f (lift (latticeGL E a) F) (splitCentre E a t * x) =
      convR μ f (lift (latticeGL E a) F) x := by
  have hR := R_splitCentre (μ := μ) t hF
  have h1 := GlobalTheory.AutomorphicL2Unitary.lift_R (Γ := latticeGL E a) (μ := μ) (splitCentre E a t) F
  rw [hR] at h1
  have h2 := (measurePreserving_mul_left μ x).quasiMeasurePreserving.ae_eq h1
  unfold convR
  refine integral_congr_ae ?_
  filter_upwards [h2] with y hy
  have e : splitCentre E a t * x * y = x * y * splitCentre E a t := by
    rw [splitCentre_comm t x, mul_assoc, splitCentre_comm t y, ← mul_assoc]
  rw [e]
  exact congrArg (f y * ·) hy.symm

end GlobalTheory.CompanionTheory.SmoothRep
end
end

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspRank

theorem isCompactOperator_repOp_Rcusp_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (μ : Measure (GA E 0)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E 0 → ℂ) :
    IsCompactOperator (repOp (Rcusp μ) μ f) := by
  have := SpecModel.finiteDimensional_zero μ
  have : FiniteDimensional ℂ (L2cusp μ) := inferInstance
  have : ProperSpace (L2cusp μ) := FiniteDimensional.proper ℂ _
  exact isCompactOperator_of_locallyCompactSpace_rng _

end GlobalTheory.CompanionTheory.CuspRank
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.cuspidal_of_L2_cuspidal_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : GA E a → ℂ), Continuous φ → (∀ γ g, φ (ratGL E a γ * g) = φ g) → (∀ t g, φ (splitCentre E a t * g) = φ g) → ∀ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ L2cusp μ → IsCuspidal φ := by
  first | exact @GlobalTheory.CompanionTheory.CuspL2.isCuspidal_of_toL2_mem | exact GlobalTheory.CompanionTheory.CuspL2.isCuspidal_of_toL2_mem | (intros; apply GlobalTheory.CompanionTheory.CuspL2.isCuspidal_of_toL2_mem <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

theorem _root_.GlobalTheory.T.finite_adelic_restriction_measure : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [MeasurableSpace (AutomorphicForm.archGroup E a)]
    [BorelSpace (AutomorphicForm.archGroup E a)] (U : Set (AdelicGLn.FiniteAdelicGL E a)),
    IsCompact U → U ∈ 𝓝 (1 : AdelicGLn.FiniteAdelicGL E a) →
    ((μ.restrict ((fun h : GA E a => (AdelicGLn.prodEquiv E a h).2) ⁻¹' U)).map
      (fun h : GA E a => AutomorphicForm.archEquiv E a (AdelicGLn.prodEquiv E a h).1)).IsHaarMeasure := by
  first | exact @GlobalTheory.CompanionTheory.GrowthHaar.isHaarMeasure_map_restrict | exact GlobalTheory.CompanionTheory.GrowthHaar.isHaarMeasure_map_restrict | (intros; apply GlobalTheory.CompanionTheory.GrowthHaar.isHaarMeasure_map_restrict <;> assumption)
end

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.HaarSplit


open GroundTheory.Automorphic.Reduction in
theorem map_prod_eq_smul (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ha : 0 < a)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ := by
  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph E a ha
  have hfun : (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = e := by
    funext p
    exact (he p.1 p.2).symm
  rw [hfun]
  set m : Measure (GA E a) := Measure.map e (ν.prod volume) with hm
  have hemeas : Measurable e := e.continuous.measurable
  have hinv : m.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨⟨y, s⟩, rfl⟩ := e.surjective g
    have hcomp : (fun x => e (y, s) * x) ∘ e = e ∘ Prod.map (fun x => y * x) (fun t => s + t) := by
      funext p
      obtain ⟨x, t⟩ := p
      simp only [Function.comp, Prod.map, he]
      rw [splitCentre_add, Subgroup.coe_mul]
      rw [mul_assoc, mul_assoc, ← mul_assoc (y : GA E a), ← splitCentre_comm, mul_assoc]
    have hpres : MeasurePreserving (Prod.map (fun x : normOneGL (K := E) (n := a) => y * x) (fun t : ℝ => s + t))
        (ν.prod volume) (ν.prod volume) :=
      (measurePreserving_mul_left ν y).prod (measurePreserving_add_left volume s)
    rw [hm, Measure.map_map (by fun_prop) hemeas, hcomp, ← Measure.map_map hemeas hpres.measurable, hpres.map_eq]
  have hfin : IsFiniteMeasureOnCompacts m := by
    refine ⟨fun K hK => ?_⟩
    change Measure.map e.toMeasurableEquiv (ν.prod volume) K < ⊤
    rw [e.toMeasurableEquiv.map_apply]
    exact (e.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
  have hopen : m.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  have hhaar : m.IsHaarMeasure := { }
  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure m μ
  refine ⟨(Measure.haarScalarFactor m μ : NNReal), ENNReal.coe_ne_zero.2 hc.ne', ENNReal.coe_ne_top, ?_⟩
  exact Measure.isMulLeftInvariant_eq_smul m μ

end GlobalTheory.CompanionTheory.HaarSplit
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

theorem _root_.GlobalTheory.T.compact_conjugate_centre_power_bounded : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ Q : Set (GA E a), IsCompact Q → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (x : GA E a),
      x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x ∈ Q → |n| ≤ n₀ := by
  first | exact @GlobalTheory.CompanionTheory.CuspGrowth.abs_le_of_conj_mem_compact | exact GlobalTheory.CompanionTheory.CuspGrowth.abs_le_of_conj_mem_compact | (intros; apply GlobalTheory.CompanionTheory.CuspGrowth.abs_le_of_conj_mem_compact <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

theorem _root_.GlobalTheory.T.central_eigen_exponential : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (c : ℂ), lie E a (oneL E a) φ = c • φ → ∀ (t : ℝ) (g : GA E a), φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre | exact GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre | (intros; apply GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre <;> assumption)
end

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.adelic_GL_norm_one_split : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∃ e : GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a) × ℝ ≃ₜ GA E a, ∀ x t, e (x, t) = splitCentre E a t * (x : GA E a) := by
  first | exact @GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph | exact GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph | (intros; apply GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

theorem _root_.GlobalTheory.T.plucker_minors_determine_column_space : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι),
    mnr M f₀ ≠ 0 → mnr M' f₀' ≠ 0 → (∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') → ∃ c : GL (Fin n) K, M' = M * c.1 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.Cramer.main | exact GlobalTheory.CompanionTheory.GodementH.Cramer.main | (intros; apply GlobalTheory.CompanionTheory.GodementH.Cramer.main <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

theorem _root_.GlobalTheory.T.left_invertible_exists_nonzero_minor : ∀ (R : Type) [CommRing R] [Nontrivial R] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R),
    L * M = 1 → ∃ f, mnr M f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.exists_mnr_ne_zero_of_left_inverse | exact GlobalTheory.CompanionTheory.GodementH.exists_mnr_ne_zero_of_left_inverse | (intros; apply GlobalTheory.CompanionTheory.GodementH.exists_mnr_ne_zero_of_left_inverse <;> assumption)
end

section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

theorem _root_.GlobalTheory.T.matrix_coefficient_intertwiner_adjoint : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ) (hρ : IsU ρ) (w₀ : A) (v : B)
    (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) (x y : Γ),
    ⟪σ x w₀, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm (σ y w₀)⟫_ℂ =
      star ⟪ρ x⁻¹ v, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc (ρ y⁻¹ v)⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.TwPf.coefOp_translate | exact GlobalTheory.CompanionTheory.RgHeA.TwPf.coefOp_translate | (intros; apply GlobalTheory.CompanionTheory.RgHeA.TwPf.coefOp_translate <;> assumption)
end

section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

theorem _root_.GlobalTheory.T.matrix_coefficient_orthogonality_relation : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ), IsU ρ → ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    IsSelfAdjoint (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.isSelfAdjoint_coefOp | exact GlobalTheory.CompanionTheory.RgHeA.isSelfAdjoint_coefOp | (intros; apply GlobalTheory.CompanionTheory.RgHeA.isSelfAdjoint_coefOp <;> assumption)
end
