module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle392
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle312
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle393
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom

@[expose] public section

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspL2

theorem exists_lintegral_enorm_lift_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {C : Set G} (hC : IsCompact C) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ F : L2 Γ μ, ∫⁻ g in C, ‖lift Γ F g‖ₑ ∂μ ≤ M * ‖F‖ₑ := by
  have hS : {γ : Γ | (γ : G) ∈ C * C⁻¹}.Finite := finite_mem_compact (hC.mul hC.inv)
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ≥0∞, N = ({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℝ≥0∞) := ⟨_, rfl⟩
  have hN : N ≠ ∞ := by simpa [hNdef] using hS
  have hfin : μ C ≠ ∞ := hC.measure_lt_top.ne
  refine ⟨N ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ), ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hN)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin), fun F => ?_⟩
  have hm : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have h2 : ∫⁻ g in C, ‖lift Γ F g‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ ≤
      N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ≥0∞).toReal ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
    rw [← lintegral_indicator hC.measurableSet,
      lintegral_eq_lintegral_tsum (Γ := Γ) ((hm.enorm.pow_const _).indicator hC.measurableSet),
      ← lintegral_const_mul' _ _ hN]
    refine lintegral_mono fun q => ?_
    rw [hNdef]
    refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (GlobalTheory.AutomorphicL2Local.tsum_indicator_le Γ C q.out _)
    by_cases hγ : (γ : G) * q.out ∈ C
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ]
      simp only [GlobalTheory.AutomorphicL2Unitary.lift, mk_mul, Quotient.out_eq]
    · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem hγ]
  have h3 : eLpNorm (lift Γ F) 2 (μ.restrict C) ≤ N ^ (1 / 2 : ℝ) * ‖F‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (f := F) (by simp) (by simp)]
    refine (ENNReal.rpow_le_rpow h2 (by simp)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp)]
    simp
    exact Lp.aestronglyMeasurable F
    exact hm.restrict
  have h4 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict C) (p := 1) (q := 2) (by norm_num) hm.restrict
  have e : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [eLpNorm_one_eq_lintegral_enorm, e, Measure.restrict_apply_univ] at h4
  calc _ ≤ N ^ (1 / 2 : ℝ) * ‖F‖ₑ * μ C ^ (1 / 2 : ℝ) := h4.trans (by gcongr)
    _ = _ := by ring
  exact hm.restrict

section Adelic

variable {E : Type} [Field E] [NumberField E] {a r : ℕ}

theorem exists_mem_apply_unip_eq {X : Type*} {u : GA E a → X} (hl : ∀ γ g, u (ratGL E a γ * g) = u g)
    {K : Set (BlockIx a r → Ad E)} (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K) (x : BlockIx a r → Ad E) :
    ∃ k ∈ K, ∀ g, u (unip x * g) = u (unip k * g) := by
  obtain ⟨_, ⟨y, rfl⟩, hk⟩ := hcov x
  refine ⟨_, hk, fun g => ?_⟩
  rw [unip_add, mul_assoc]
  exact ((congrArg (fun v => u (v * _)) (unip_algebraMap y)).trans (hl _ _)).symm

variable [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]

theorem lintegral_constTerm_le [_root_.NumberField.IsTotallyComplex E] (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (ν : Measure (BlockIx a r → Ad E)) {𝓕 : Set (BlockIx a r → Ad E)} (hν𝓕 : ν 𝓕 ≠ ∞)
    {K : Set (BlockIx a r → Ad E)} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K) {C : Set (GA E a)}
    (hC : IsCompact C) {u : GA E a → ℂ} (hc : Continuous u) (hl : ∀ γ g, u (ratGL E a γ * g) = u g) :
    ∫⁻ g in C, ‖∫ x in 𝓕, u (unip x * g) ∂ν‖ₑ ∂μ ≤ ν 𝓕 * ∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 hν𝓕
  haveI : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  haveI : SFinite (μ.restrict C) :=
    @MeasureTheory.instSFiniteOfSigmaFinite _ _ (μ.restrict C) (IsFiniteMeasure.toSigmaFinite _)
  haveI : SFinite (ν.restrict 𝓕) :=
    @MeasureTheory.instSFiniteOfSigmaFinite _ _ (ν.restrict 𝓕) (IsFiniteMeasure.toSigmaFinite _)
  have hC' : IsCompact ((unip '' K) * C) := (hK.image continuous_unip).mul hC
  have hb : ∀ x, ∫⁻ g in C, ‖u (unip x * g)‖ₑ ∂μ ≤ ∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ := fun x => by
    obtain ⟨k, hk, e⟩ := exists_mem_apply_unip_eq hl hcov x
    simp only [e]
    rw [← (measurePreserving_mul_left μ (unip k)).setLIntegral_comp_preimage hC'.measurableSet
      hc.enorm.measurable]
    exact lintegral_mono_set fun g hg => Set.mul_mem_mul ⟨k, hk, rfl⟩ hg
  have hj : Continuous fun p : GA E a × (BlockIx a r → Ad E) => ‖u (unip p.2 * p.1)‖ₑ :=
    (hc.comp ((continuous_unip.comp continuous_snd).mul continuous_fst)).enorm
  calc ∫⁻ g in C, ‖∫ x in 𝓕, u (unip x * g) ∂ν‖ₑ ∂μ
      ≤ ∫⁻ g in C, ∫⁻ x in 𝓕, ‖u (unip x * g)‖ₑ ∂ν ∂μ :=
        lintegral_mono fun g => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x in 𝓕, ∫⁻ g in C, ‖u (unip x * g)‖ₑ ∂μ ∂ν := lintegral_lintegral_swap hj.aemeasurable
    _ ≤ ∫⁻ x in 𝓕, (∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ) ∂ν := lintegral_mono hb
    _ = _ := by rw [setLIntegral_const, mul_comm]

theorem continuous_constTerm [_root_.NumberField.IsTotallyComplex E] (ν : Measure (BlockIx a r → Ad E)) {𝓕 : Set (BlockIx a r → Ad E)}
    (hν𝓕 : ν 𝓕 ≠ ∞) {K : Set (BlockIx a r → Ad E)} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K)
    {u : GA E a → ℂ} (hc : Continuous u) (hl : ∀ γ g, u (ratGL E a γ * g) = u g) :
    Continuous fun g => ∫ x in 𝓕, u (unip x * g) ∂ν := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 hν𝓕
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g₀
  obtain ⟨B, hB⟩ := ((hK.image continuous_unip).mul hC).exists_bound_of_continuousOn hc.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => B)
    (.of_forall fun g => (hc.comp (continuous_unip.mul continuous_const)).aestronglyMeasurable) ?_
    (integrable_const _) (.of_forall fun x => (hc.comp (continuous_const.mul continuous_id)).continuousAt)
  filter_upwards [hg] with g hg'
  refine .of_forall fun x => ?_
  obtain ⟨k, hk, e⟩ := exists_mem_apply_unip_eq hl hcov x
  rw [e]
  exact hB _ (Set.mul_mem_mul ⟨k, hk, rfl⟩ hg')

end Adelic

theorem isCuspidal_of_toL2_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : GA E a → ℂ), Continuous φ →
    (∀ γ g, φ (ratGL E a γ * g) = φ g) → (∀ t g, φ (splitCentre E a t * g) = φ g) →
    ∀ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ L2cusp μ → IsCuspidal φ := by
  intro E _ _ _ a μ _ _ φ hc hl hs h hF r h0 h1 _ _ ν 𝓕 hν h𝓕 g
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.ConstNotCusp.discreteTopology_ratN E a r
  haveI : Countable (ratN E a r) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  have hν𝓕 : ν 𝓕 ≠ ∞ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK hcov ν h𝓕).ne
  have hcont := continuous_constTerm ν hν𝓕 hK hcov hc hl
  have key : ∀ C : Set (GA E a), IsCompact C → ∫⁻ g in C, ‖∫ x in 𝓕, φ (unip x * g) ∂ν‖ₑ ∂μ = 0 := fun C hC => by
    obtain ⟨M, hM, hb⟩ := exists_lintegral_enorm_lift_le (latticeGL E a) μ ((hK.image continuous_unip).mul hC)
    have step : ∀ F' ∈ cuspContinuousL2 μ, ∫⁻ g in C, ‖∫ x in 𝓕, φ (unip x * g) ∂ν‖ₑ ∂μ ≤ ν 𝓕 * (M * ‖h.toL2 - F'‖ₑ) := by
      rintro F' ⟨ψ, hψ, e⟩
      have hcomp : ∀ g, ∫ x in 𝓕, (φ (unip x * g) - ψ (unip x * g)) ∂ν = ∫ x in 𝓕, φ (unip x * g) ∂ν := fun g => by
        rw [integral_sub (integrableOn_unip hc hl ν h𝓕 g) (integrableOn_unip hψ.1 hψ.2.1 ν h𝓕 g),
          hψ.2.2.2 r h0 h1 ν 𝓕 hν h𝓕 g, sub_zero]
      have h2 := lintegral_constTerm_le μ ν hν𝓕 hK hcov hC (u := fun g => φ g - ψ g) (hc.sub hψ.1)
        (fun γ g => by rw [hl, hψ.2.1])
      simp only [hcomp] at h2
      have e' : lift (latticeGL E a) (h.toL2 - F') =ᵐ[μ] fun g => φ g - ψ g :=
        Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_sub h.toL2 F')) (h.lift_toL2_ae_eq.sub e)
      refine h2.trans ?_
      gcongr
      refine le_trans (le_of_eq (lintegral_congr_ae (ae_restrict_of_ae ?_))) (hb (h.toL2 - F'))
      exact e'.mono fun g eg => by rw [eg]
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (show h.toL2 ∈ closure (cuspContinuousL2 μ : Set _) from hF)
    have ht : Filter.Tendsto (fun n => ν 𝓕 * (M * ‖h.toL2 - u n‖ₑ)) Filter.atTop (𝓝 0) := by
      have h3 : Filter.Tendsto (fun n => h.toL2 - u n) Filter.atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := h.toL2)).sub hlim
      have h4 : Filter.Tendsto (fun n => ‖h.toL2 - u n‖ₑ) Filter.atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto _).comp h3
      simpa using ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul h4 (Or.inr hM)) (Or.inr hν𝓕)
    exact le_antisymm (ge_of_tendsto' ht fun n => step _ (hu n)) zero_le
  have hae : (fun g => ∫ x in 𝓕, φ (unip x * g) ∂ν) =ᵐ[μ] 0 := by
    have h5 : ∀ n, ∀ᵐ g ∂μ.restrict (compactCovering (GA E a) n), ∫ x in 𝓕, φ (unip x * g) ∂ν = 0 := fun n => by
      have := (lintegral_eq_zero_iff' hcont.enorm.aemeasurable).1 (key _ (isCompact_compactCovering _ n))
      exact this.mono fun g eg => by simpa using eg
    have h6 := ae_restrict_iUnion_iff _ _ |>.2 h5
    rwa [iUnion_compactCovering, Measure.restrict_univ] at h6
  exact congrFun ((Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hae) g

end GlobalTheory.CompanionTheory.CuspL2

end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.GrowthHaar

theorem isHaarMeasure_map_restrict (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [MeasurableSpace (AutomorphicForm.archGroup E a)]
    [BorelSpace (AutomorphicForm.archGroup E a)] (U : Set (AdelicGLn.FiniteAdelicGL E a))
    (hUc : IsCompact U) (hU1 : U ∈ 𝓝 (1 : AdelicGLn.FiniteAdelicGL E a)) :
    ((μ.restrict ((fun h : GA E a => (AdelicGLn.prodEquiv E a h).2) ⁻¹' U)).map
      (fun h : GA E a => AutomorphicForm.archEquiv E a (AdelicGLn.prodEquiv E a h).1)).IsHaarMeasure := by
  haveI : T2Space (AdelicGLn.FiniteAdelicGL E a) := inferInstance
  haveI : T2Space (AutomorphicForm.archGroup E a) := inferInstance
  haveI : BorelSpace (GA E a) := inferInstance
  set q : GA E a → AdelicGLn.FiniteAdelicGL E a := fun h => (AdelicGLn.prodEquiv E a h).2 with hq_def
  set p : GA E a → AutomorphicForm.archGroup E a :=
    fun h => AutomorphicForm.archEquiv E a (AdelicGLn.prodEquiv E a h).1 with hp_def
  have hΦ : Continuous (AdelicGLn.prodEquiv E a) := (AdelicGLn.prodEquiv E a).continuous
  have hq : Continuous q := continuous_snd.comp hΦ
  have hp : Continuous p := (AutomorphicForm.archEquiv E a).continuous.comp (continuous_fst.comp hΦ)
  have hpm : Measurable p := hp.measurable
  have hS : MeasurableSet (q ⁻¹' U) := (hUc.isClosed.preimage hq).measurableSet
  have happly : ∀ B : Set (AutomorphicForm.archGroup E a), MeasurableSet B →
      ((μ.restrict (q ⁻¹' U)).map p) B = μ (p ⁻¹' B ∩ q ⁻¹' U) := fun B hB => by
    rw [Measure.map_apply hpm hB, Measure.restrict_apply (hpm hB)]
  have h1 : IsFiniteMeasureOnCompacts ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun K hK => ?_⟩
    rw [happly K hK.isClosed.measurableSet]
    have hK' : IsCompact ((AutomorphicForm.archEquiv E a).symm '' K) :=
      hK.image (AutomorphicForm.archEquiv E a).symm.continuous
    have hc : IsCompact (p ⁻¹' K ∩ q ⁻¹' U) := by
      have : p ⁻¹' K ∩ q ⁻¹' U = (AdelicGLn.prodEquiv E a).symm ''
          (((AutomorphicForm.archEquiv E a).symm '' K) ×ˢ U) := by
        ext h
        constructor
        · rintro ⟨hk, hu⟩
          exact ⟨AdelicGLn.prodEquiv E a h,
            ⟨⟨_, hk, (AutomorphicForm.archEquiv E a).symm_apply_apply _⟩, hu⟩,
            (AdelicGLn.prodEquiv E a).symm_apply_apply h⟩
        · rintro ⟨⟨x, y⟩, ⟨⟨k, hk, rfl⟩, hy⟩, rfl⟩
          refine ⟨?_, ?_⟩
          · simpa [hp_def] using hk
          · simpa [hq_def] using hy
      rw [this]
      exact (hK'.prod hUc).image (AdelicGLn.prodEquiv E a).symm.continuous
    exact hc.measure_lt_top
  have hpL : ∀ (s : AutomorphicForm.archGroup E a) (h : GA E a),
      p (AutomorphicForm.infEmb E a s * h) = s * p h := fun s h => by
    simp [hp_def, AutomorphicForm.prodEquiv_infEmb]
  have hqL : ∀ (s : AutomorphicForm.archGroup E a) (h : GA E a),
      q (AutomorphicForm.infEmb E a s * h) = q h := fun s h => by
    simp [hq_def, AutomorphicForm.prodEquiv_infEmb]
  have h2 : Measure.IsMulLeftInvariant ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun s => ?_⟩
    have hms : Measurable fun x : AutomorphicForm.archGroup E a => s * x :=
      (continuous_const.mul continuous_id).measurable
    ext B hB
    rw [Measure.map_apply hms hB, happly _ (hms hB), happly B hB,
      ← measure_preimage_mul μ (AutomorphicForm.infEmb E a s) (p ⁻¹' B ∩ q ⁻¹' U)]
    congr 1
    ext h
    simp only [Set.mem_inter_iff, Set.mem_preimage, hpL, hqL]
  have h3 : Measure.IsOpenPosMeasure ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun O hO ⟨s, hs⟩ => ?_⟩
    rw [happly O hO.measurableSet]
    have hV : IsOpen (p ⁻¹' O ∩ q ⁻¹' interior U) :=
      (hO.preimage hp).inter (isOpen_interior.preimage hq)
    have hne : (p ⁻¹' O ∩ q ⁻¹' interior U).Nonempty := by
      refine ⟨AutomorphicForm.infEmb E a s, ?_, ?_⟩
      · simpa [hp_def, AutomorphicForm.prodEquiv_infEmb] using hs
      · simpa [hq_def, AutomorphicForm.prodEquiv_infEmb] using mem_interior_iff_mem_nhds.2 hU1
    refine fun h0 => hV.measure_ne_zero μ hne (measure_mono_null ?_ h0)
    exact Set.inter_subset_inter_right _ (Set.preimage_mono interior_subset)
  exact { toIsFiniteMeasureOnCompacts := h1, toIsMulLeftInvariant := h2, toIsOpenPosMeasure := h3 }

end GlobalTheory.CompanionTheory.GrowthHaar
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.induced_fixed_nonzero : ∀ (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (P : Subgroup G) (σ : Representation ℂ P W) (K : Subgroup G), IsOpen (K : Set G) → ∀ x : W, x ≠ 0 → (∀ p : P, (p : G) ∈ K → σ p x = x) → fixed (smInd P σ) K ≠ ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.SmInd.fixed_smInd_ne_bot_of_fixed | exact GlobalTheory.CompanionTheory.SmInd.fixed_smInd_ne_bot_of_fixed | (intros; apply GlobalTheory.CompanionTheory.SmInd.fixed_smInd_ne_bot_of_fixed <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.CuspGrowth


open GlobalTheory.IdeleCovolume GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele in
theorem abs_le_of_conj_mem_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ Q : Set (GA E a), IsCompact Q → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (x : GA E a),
      x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x ∈ Q → |n| ≤ n₀ := by
  intro E _ _ _ a ha Q hQ
  have hf : Continuous fun g : GA E a => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det g)) :=
    (continuous_ideleNorm.comp GeneralLinearGroup.continuous_det).log fun _ => ideleNorm_ne_zero _
  obtain ⟨B, hB⟩ := (hQ.image hf).isBounded.exists_norm_le
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  set L := Real.log (ideleNorm (E := E) (eIdele E)) with hLdef
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  refine ⟨⌈B / (a * L)⌉₊, fun γ n x hx => ?_⟩
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  have hv : Real.log (ideleNorm (E := E) (GeneralLinearGroup.det
      (x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x))) = (n : ℝ) * (a * L) := by
    have h1 : GeneralLinearGroup.det (x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x) =
        diag E (GeneralLinearGroup.det γ) * (eIdele E ^ a) ^ n := by
      rw [map_mul, map_mul, map_mul, map_inv, map_zpow, hd, det_splitCentre_one, mul_comm, ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [h1, map_mul, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul,
      map_zpow, map_pow, Real.log_zpow, Real.log_pow]
  have hb := hB _ ⟨_, hx, rfl⟩
  beta_reduce at hb
  rw [hv, Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos ha' hL)] at hb
  have h2 : ((|n| : ℤ) : ℝ) ≤ B / (a * L) := by
    rw [le_div_iff₀ (mul_pos ha' hL)]
    simpa using hb
  have h3 : ((|n| : ℤ) : ℝ) ≤ ((⌈B / (a * L)⌉₊ : ℤ) : ℝ) := by
    rw [Int.cast_natCast]
    exact h2.trans (Nat.le_ceil _)
  exact Int.cast_le.1 h3

end GlobalTheory.CompanionTheory.CuspGrowth
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.Clozel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def scalarCurve (s : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (s : ℂ))

theorem scalarCurve_zero : scalarCurve E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 :=
    Units.ext (funext fun _ => by simp [expU])
  rw [scalarCurve, h, map_one]

theorem hasDerivAt_scalarCurve :
    HasDerivAt (fun s => toL (scalarCurve E a s).val) (oneL E a) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  rw [hasDerivAt_pi]
  intro w
  by_cases h : i = j
  · subst h
    have e : (fun s : ℝ => toL (scalarCurve E a s).val i i w) = fun s : ℝ => Complex.exp (s : ℂ) := by
      funext s
      simp [scalarCurve, toL, expU, Matrix.scalar_apply]
    have d : HasDerivAt (fun s : ℝ => Complex.exp (s : ℂ)) 1 0 := by
      simpa using (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
    have o : oneL E a i i w = 1 := by simp [oneL, toL]
    rw [e, o]
    exact d
  · have e : (fun s : ℝ => toL (scalarCurve E a s).val i j w) = fun _ : ℝ => 0 := by
      funext s
      simp [scalarCurve, toL, Matrix.scalar_apply, h]
    have o : oneL E a i j w = 0 := by simp [oneL, toL, h]
    rw [e, o]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem eigen_along_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (c : ℂ),
    lie E a (oneL E a) φ = c • φ → ∀ (t : ℝ) (g : GA E a),
      φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  intro E _ _ _ a φ c hφ t g
  set f : ℝ → ℂ := fun u => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) with hf
  have hd : ∀ u, HasDerivAt f (c * f u) u := by
    intro u
    have h1 := hasDerivAt_curve φ (g * GlobalTheory.UnitaryBC.splitCentre E a u) (scalarCurve E a) (oneL E a)
      scalarCurve_zero hasDerivAt_scalarCurve
    have h2 : lieD (oneL E a) φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) = c * f u := by
      have := congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) hφ
      simpa [hf] using this
    rw [h2] at h1
    have h3 : HasDerivAt (fun x : ℝ => φ.1 ((g * GlobalTheory.UnitaryBC.splitCentre E a u) * infGL E a (scalarCurve E a (x - u))))
        (c * f u) u := by
      have h0 : u - u = (0 : ℝ) := sub_self u
      exact HasDerivAt.comp_sub_const u u (by rw [h0]; exact h1)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    have e : GlobalTheory.UnitaryBC.splitCentre E a x =
        GlobalTheory.UnitaryBC.splitCentre E a u * infGL E a (scalarCurve E a (x - u)) := by
      have := GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add (E := E) (a := a) u (x - u)
      rw [add_sub_cancel] at this
      exact this
    simp only [hf, e, mul_assoc]
  have hP : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-c * v) * f v)
      (Complex.exp (-c * u) * (-c) * f u + Complex.exp (-c * u) * (c * f u)) u := by
    intro u
    have h0 : HasDerivAt (fun v : ℝ => -c * (v : ℂ)) (-c) u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-c)
    exact h0.cexp.mul (hd u)
  have hconst : ∀ u : ℝ, Complex.exp (-c * u) * f u = Complex.exp (-c * (0 : ℝ)) * f 0 := by
    refine fun u => is_const_of_deriv_eq_zero (f := fun v : ℝ => Complex.exp (-c * v) * f v)
      (fun x => (hP x).differentiableAt) (fun x => ?_) u 0
    rw [(hP x).deriv]
    ring
  have h0 : f 0 = φ.1 g := by
    simp [hf, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero]
  have ht := hconst t
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0] at ht
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm]
  change f t = _
  rw [← ht, ← mul_assoc, ← Complex.exp_add]
  simp

end GlobalTheory.CompanionTheory.Clozel

end
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_pairing_exists_eventual_value : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (v : V) (v' : V'), ∃ A, EvVal ν ψ T B v v' A := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.exists_evVal | exact GlobalTheory.CompanionTheory.MirPair.exists_evVal | (intros; apply GlobalTheory.CompanionTheory.MirPair.exists_evVal <;> assumption)
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

theorem _root_.GlobalTheory.T.exists_admissible_linear_functional : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ w : ℂ, w ≠ 0 → ‖w‖ * (q : ℝ) ^ 2 < 1 →
    ∃ I : (L → ℂ) → ℂ,
      (∀ F G : L → ℂ, IsAdm w F → IsAdm w G → I (F + G) = I F + I G) ∧
      (∀ (c : ℂ) (F : L → ℂ), IsAdm w F → I (c • F) = c * I F) ∧
      (∀ (F : L → ℂ) (y : L), IsAdm w F → IsAdm w (fun x => F (x + y)) ∧ I (fun x => F (x + y)) = I F) ∧
      (∀ (F : L → ℂ) (c : L), IsAdm w F → c ≠ 0 →
        IsAdm w (fun x => F (c * x)) ∧ I (fun x => F (c * x)) = (q : ℂ) ^ (2 * ordL c) * I F) ∧
      IsAdm w (sphFn (L := L) w) ∧ I (sphFn w) = (1 - w) / (1 - w * (q : ℂ) ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral | exact GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral | (intros; apply GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral <;> assumption)
end
