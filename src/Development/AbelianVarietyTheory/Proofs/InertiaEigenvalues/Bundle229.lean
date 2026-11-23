module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle216
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle217
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import Mathlib.Data.List.GetD
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
import GroundTheory.LocalFields.Interface

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.JR.UnitsHaar

theorem secondCountable_base (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] : SecondCountableTopology F := by
  haveI : LocallyCompactSpace F := @Unram.lcF F E _ _ _ _ ‹_›
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F (E := F)
  infer_instance

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E)

theorem top_K : T2Space A.K ∧ SecondCountableTopology A.K := by
  haveI := secondCountable_base F E
  let e := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : A.K ≃ₜ (Fin _ → F) := ⟨e.toEquiv, h1, h2⟩
  exact ⟨h.isEmbedding.t2Space, h.isEmbedding.isInducing.secondCountableTopology⟩

omit [Unram F E] in
theorem openUnits : IsOpenUnits A.K :=
  GlobalTheory.GaugeEx.isOpenUnits_of_basis (Module.finBasis F A.K)

omit [Unram F E] in
theorem absK_eq (t : A.K) : A.absK t = (GlobalTheory.GaugeEx.modu A.K t : ℝ) := by
  unfold Et.absK GlobalTheory.GaugeEx.modu; split_ifs <;> simp

omit [Unram F E] in
theorem borel_units : BorelSpace A.Kˣ := by
  have hemb := (openUnits A).isOpenEmbedding_unitsVal
  refine ⟨?_⟩
  rw [hemb.isEmbedding.isInducing.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
  rfl

omit [Unram F E] in
theorem modu_mul_left (c : A.Kˣ) (t : A.K) :
    GlobalTheory.GaugeEx.modu A.K ((c : A.K) * t) = GlobalTheory.GaugeEx.modu A.K c * GlobalTheory.GaugeEx.modu A.K t := by
  classical
  by_cases ht : IsUnit t
  · obtain ⟨u, rfl⟩ := ht
    rw [← Units.val_mul, GlobalTheory.GaugeEx.modu_units, GlobalTheory.GaugeEx.modu_units, GlobalTheory.GaugeEx.modu_units, map_mul]
  · have hct : ¬ IsUnit ((c : A.K) * t) := fun h => ht (IsUnit.mul_iff.1 h).2
    simp [GlobalTheory.GaugeEx.modu, ht, hct]

omit [Unram F E] in
theorem modu_units_inv (u : A.Kˣ) :
    (GlobalTheory.GaugeEx.modu A.K u)⁻¹ = distribHaarChar A.K u⁻¹ := by
  rw [GlobalTheory.GaugeEx.modu_units, map_inv]

def dens (t : A.K) : ℝ≥0 := (GlobalTheory.GaugeEx.modu A.K t)⁻¹

omit [Unram F E] in
theorem unitsMeas_eq (μK : Measure A.K) :
    LinDesc.unitsMeas A μK = (μK.withDensity fun t => (dens A t : ℝ≥0∞)).comap Units.val := by
  have : ∀ t, ENNReal.ofReal (A.absK t)⁻¹ = (dens A t : ℝ≥0∞) := fun t => by
    rw [absK_eq, dens, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  unfold LinDesc.unitsMeas
  simp only [this]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (μK : Measure A.K) (hμ : μK.IsAddHaarMeasure) :
    BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ,
      ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK := by
  classical
  obtain ⟨hT2, hSC⟩ := top_K A
  have hOU := openUnits A
  haveI hB := borel_units A
  have hemb := hOU.isOpenEmbedding_unitsVal
  have hme : MeasurableEmbedding (Units.val : A.Kˣ → A.K) := hemb.measurableEmbedding
  have hU : IsOpen {t : A.K | IsUnit t} := hemb.isOpen_range
  have hmod : Measurable (GlobalTheory.GaugeEx.modu A.K) := by
    have hc := (GlobalTheory.GaugeEx.modu_basic A.K).2.2.2 hOU
    have := hc.measurable_piecewise (g := fun _ => 0) continuousOn_const hU.measurableSet
    convert this using 1
    funext u
    by_cases hu : IsUnit u
    · simp [Set.piecewise, hu]
    · simp [Set.piecewise, GlobalTheory.GaugeEx.modu, hu]
  have hdm : Measurable (dens A) := hmod.inv
  set ν := μK.withDensity fun t => (dens A t : ℝ≥0∞) with hν
  rw [unitsMeas_eq]
  refine ⟨hB, ?_, ?_⟩
  swap
  · intro h
    have hr : Set.range (Units.val : A.Kˣ → A.K) = {t : A.K | IsUnit t} := Set.ext fun _ => Iff.rfl
    rw [← hme.integral_map, hme.map_comap, hr, restrict_withDensity hU.measurableSet,
      integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [NNReal.smul_def, Complex.real_smul, absK_eq, dens, NNReal.coe_inv, Complex.ofReal_inv, mul_comm]
  haveI := hμ
  have hc0 : ∀ c : A.Kˣ, 0 < GlobalTheory.GaugeEx.modu A.K c := fun c => ((GlobalTheory.GaugeEx.modu_basic A.K).1 c c.isUnit).1
  have hscale : ∀ (c : A.Kˣ) (G : A.K → ℝ≥0∞),
      ∫⁻ t, G t ∂μK = (GlobalTheory.GaugeEx.modu A.K c : ℝ≥0∞) * ∫⁻ t, G ((c : A.K) * t) ∂μK := by
    intro c G
    have e := ((GlobalTheory.GaugeEx.modu_basic A.K).1 c c.isUnit).2 μK hμ
    have hm : MeasurableEmbedding (fun z : A.K => (c : A.K) * z) := (Homeomorph.smul c).measurableEmbedding
    conv_lhs => rw [e]
    rw [lintegral_smul_measure, hm.lintegral_map]
    rfl
  have hinv : ∀ (c : A.Kˣ) (T : Set A.K), MeasurableSet T → ν ((fun t => (c : A.K) * t) ⁻¹' T) = ν T := by
    intro c T hT
    have hT' : MeasurableSet ((fun t => (c : A.K) * t) ⁻¹' T) := (measurable_const_mul _) hT
    rw [hν, withDensity_apply _ hT, withDensity_apply _ hT', ← lintegral_indicator hT, ← lintegral_indicator hT']
    conv_rhs => rw [hscale c]
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine lintegral_congr fun t => ?_
    by_cases ht : (c : A.K) * t ∈ T
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ (fun t => (c : A.K) * t) ⁻¹' T from ht)]
      rw [← ENNReal.coe_mul, ENNReal.coe_inj, dens, dens, modu_mul_left, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (hc0 c).ne', one_mul]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show t ∉ (fun t => (c : A.K) * t) ⁻¹' T from ht),
        mul_zero]
  have hL : (ν.comap Units.val).IsMulLeftInvariant := by
    refine ⟨fun c => ?_⟩
    ext S hS
    rw [Measure.map_apply (measurable_const_mul c) hS, hme.comap_apply, hme.comap_apply]
    have hset : Units.val '' ((fun x => c * x) ⁻¹' S) = (fun t : A.K => (c : A.K) * t) ⁻¹' (Units.val '' S) := by
      ext t; constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨c * u, hu, Units.val_mul c u⟩
      · rintro ⟨s, hs, hst⟩
        refine ⟨c⁻¹ * s, by simpa [Set.mem_preimage] using hs, ?_⟩
        rw [Units.val_mul, hst, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [hset, hinv c _ (hme.measurableSet_image.2 hS)]
  have hF : IsFiniteMeasureOnCompacts (ν.comap Units.val) := by
    refine ⟨fun C hC => ?_⟩
    rw [hme.comap_apply]
    have hcont : Continuous fun u : A.Kˣ => distribHaarChar A.K u⁻¹ :=
      (GlobalTheory.GaugeEx.continuous_distribHaarChar_units A.K).comp continuous_inv
    obtain ⟨M, hM⟩ := (hC.image hcont).bddAbove
    have hC' : IsCompact (Units.val '' C) := hC.image Units.continuous_val
    calc ν (Units.val '' C) = ∫⁻ t in Units.val '' C, (dens A t : ℝ≥0∞) ∂μK :=
          withDensity_apply _ hC'.measurableSet
      _ ≤ ∫⁻ t in Units.val '' C, (M : ℝ≥0∞) ∂μK := by
          refine setLIntegral_mono measurable_const fun t ht => ?_
          obtain ⟨u, hu, rfl⟩ := ht
          rw [ENNReal.coe_le_coe, dens, modu_units_inv]
          exact hM ⟨u, hu, rfl⟩
      _ = M * μK (Units.val '' C) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hC'.measure_lt_top
  have hP : (ν.comap Units.val).IsOpenPosMeasure := by
    refine ⟨fun U hUo hne => ?_⟩
    rw [hme.comap_apply]
    have hVo : IsOpen (Units.val '' U) := hemb.isOpenMap U hUo
    intro h0
    rw [hν, withDensity_apply _ hVo.measurableSet, lintegral_eq_zero_iff hdm.coe_nnreal_ennreal] at h0
    have h1 : ∀ᵐ t ∂(μK.restrict (Units.val '' U)), False := by
      filter_upwards [h0, ae_restrict_mem hVo.measurableSet] with t ht hV
      obtain ⟨u, -, rfl⟩ := hV
      have : (dens A u : ℝ≥0∞) ≠ 0 := by
        rw [ENNReal.coe_ne_zero, dens, modu_units_inv]; exact distribHaarChar_pos.ne'
      exact this (by simpa using ht)
    have h2 : μK.restrict (Units.val '' U) = 0 := ae_eq_bot.1 (eventually_false_iff_eq_bot.1 h1)
    rw [Measure.restrict_eq_zero] at h2
    exact (hVo.measure_pos μK (hne.image _)).ne' h2
  exact { toIsFiniteMeasureOnCompacts := hF, toIsMulLeftInvariant := hL, toIsOpenPosMeasure := hP }

end GlobalTheory.JR.UnitsHaar

namespace GlobalTheory.JR.LinDesc

theorem unitsMeas_isHaar : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ, ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK :=
  fun _ _ _ _ _ _ _ A μK hμ => GlobalTheory.JR.UnitsHaar.finiteRing_sq_sub_mul_sq_eq_of_card A μK hμ

end GlobalTheory.JR.LinDesc
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem exists_fundamentalDomain_mass_one : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G], ∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro G _ _ _ _ _ _ Γ hΓ _ _
  obtain ⟨hdisc, K, hK, hKc⟩ := hΓ
  have : DiscreteTopology Γ := hdisc
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.1 (isOpen_discrete ({0} : Set Γ))
  have hU0 : ∀ γ ∈ Γ, γ ∈ U → γ = 0 := by
    intro γ hγ hγU
    have h : (⟨γ, hγ⟩ : Γ) ∈ (Subtype.val ⁻¹' U : Set Γ) := hγU
    rw [hU] at h
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 h)
  have hUn : U ∈ nhds (0 : G) := by
    have h : (0 : Γ) ∈ (Subtype.val ⁻¹' U : Set Γ) := by rw [hU]; rfl
    exact hUo.mem_nhds h

  obtain ⟨V, hV, hVU⟩ := exists_nhds_zero_half hUn
  set V₀ := interior (V ∩ (fun x => -x) ⁻¹' V) with hV₀
  have hV₀o : IsOpen V₀ := isOpen_interior
  have hV₀0 : (0 : G) ∈ V₀ := by
    rw [hV₀, mem_interior_iff_mem_nhds]
    refine Filter.inter_mem hV ?_
    exact continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV)
  have hsub : ∀ a ∈ V₀, ∀ b ∈ V₀, a - b ∈ U := by
    intro a ha b hb
    have ha' := (interior_subset ha).1
    have hb' : -b ∈ V := (interior_subset hb).2
    rw [sub_eq_add_neg]
    exact hVU a ha' (-b) hb'

  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun k : G => (fun x => x - k) ⁻¹' V₀)
    (fun k => hV₀o.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using hV₀0⟩)
  set l := t.toList with hl
  let c : ℕ → G := fun n => l.getD n 0
  let W : ℕ → Set G := fun n => (fun x => x - c n) ⁻¹' V₀ ∩ K ∩ {_x | n < l.length}
  let S : ℕ → Set G := fun n => ⋃ γ : Γ, (fun x => (γ : G) + x) ⁻¹' W n
  let F : Set G := ⋃ n, (W n ∩ ⋂ m, ⋂ (_ : m < n), (S m)ᶜ)
  have hWm : ∀ n, MeasurableSet (W n) := fun n =>
    ((hV₀o.preimage (continuous_id.sub continuous_const)).measurableSet.inter
      hK.isClosed.measurableSet).inter (MeasurableSet.const _)
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    MeasurableSet.iUnion fun γ => (hWm n).preimage (measurable_const_add _)
  have hFm : MeasurableSet F :=
    MeasurableSet.iUnion fun n => (hWm n).inter
      (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hSm m).compl)
  have hFK : F ⊆ K := by
    intro x hx
    obtain ⟨n, hn, -⟩ := Set.mem_iUnion.1 hx
    exact hn.1.2

  have hSinv : ∀ n, ∀ γ ∈ Γ, ∀ x, γ + x ∈ S n ↔ x ∈ S n := by
    intro n γ hγ x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨δ, hδ⟩
      exact ⟨⟨(δ : G) + γ, Γ.add_mem δ.2 hγ⟩, by simpa [add_assoc] using hδ⟩
    · rintro ⟨δ, hδ⟩
      refine ⟨⟨(δ : G) - γ, Γ.sub_mem δ.2 hγ⟩, ?_⟩
      rw [show (δ : G) - γ + (γ + x) = δ + x by abel]
      exact hδ

  have hcov : ∀ y ∈ K, ∃ n, y ∈ W n := by
    intro y hy
    obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hkl : k ∈ l := by rw [hl]; exact Finset.mem_toList.2 hk
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hkl
    refine ⟨n, ⟨?_, hy⟩, hn⟩
    have hc : c n = l[n] := List.getD_eq_getElem _ _ hn
    simpa [hc] using hyk
  have hex : ∀ x : G, ∃! γ : Γ, γ +ᵥ x ∈ F := by
    intro x
    have hne : ∃ n, x ∈ S n := by
      obtain ⟨γ, hγ, hγK⟩ := hKc x
      obtain ⟨n, hn⟩ := hcov _ hγK
      exact ⟨n, Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, hn⟩⟩
    classical
    obtain ⟨δ, hδ⟩ := Set.mem_iUnion.1 (Nat.find_spec hne)
    have hδF : δ +ᵥ x ∈ F := by
      refine Set.mem_iUnion.2 ⟨Nat.find hne, hδ, ?_⟩
      simp only [Set.mem_iInter, Set.mem_compl_iff]
      intro m hm
      change ¬ ((δ : G) + x ∈ S m)
      rw [hSinv m δ δ.2 x]
      exact Nat.find_min hne hm
    refine ⟨δ, hδF, ?_⟩
    intro γ hγ
    change (γ : G) + x ∈ F at hγ
    have hγ' : (δ : G) + x ∈ F := hδF
    obtain ⟨n, hn, hnS⟩ := Set.mem_iUnion.1 hγ
    obtain ⟨n', hn', hnS'⟩ := Set.mem_iUnion.1 hγ'
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hnS hnS'
    have hxn : x ∈ S n := Set.mem_iUnion.2 ⟨γ, hn⟩
    have hxn' : x ∈ S n' := Set.mem_iUnion.2 ⟨δ, hn'⟩
    rcases lt_trichotomy n n' with h | rfl | h
    · exact absurd ((hSinv n δ δ.2 x).2 hxn) (hnS' n h)
    · have hd := hsub _ hn.1.1 _ hn'.1.1
      have hmem : (γ : G) - δ ∈ Γ := Γ.sub_mem γ.2 δ.2
      have h0 := hU0 _ hmem (by simpa [sub_sub_sub_cancel_right, add_sub_add_right_eq_sub] using hd)
      exact Subtype.ext (sub_eq_zero.1 h0)
    · exact absurd ((hSinv n' γ γ.2 x).2 hxn') (hnS n' h)

  let μ₀ : Measure G := Measure.addHaar
  have hF₀ : IsAddFundamentalDomain Γ F μ₀ := IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hex
  have h0 : μ₀ F ≠ 0 := hF₀.measure_ne_zero (NeZero.ne μ₀)
  have htop : μ₀ F ≠ ⊤ := ((measure_mono hFK).trans_lt hK.measure_lt_top).ne
  refine ⟨(μ₀ F)⁻¹ • μ₀, F, Measure.IsAddHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0),
    IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hex, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

end GlobalTheory.CuspGeneric
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem mir_exists_row : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ), m + 1 < a →
    ∀ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, ξ ≠ 0 → ∃ γ : GL (Fin a) E, IsMir (m + 1) γ ∧
      ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1 = ξ t := by
  intro E _ _ a m hma ξ hξ
  classical
  set mm : Fin a := ⟨m, by omega⟩ with hmm
  set c : Fin a := ⟨m + 1, hma⟩ with hc
  let v : Fin a → E := fun k => if h : (k : ℕ) ≤ m then ξ ⟨(k, c), by simp [hc]; omega⟩ else 0
  have hv : ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), v t.1.1 = ξ t := by
    intro t
    have h1 := t.2
    have hle : (t.1.1 : ℕ) ≤ m := by omega
    simp only [v, dif_pos hle]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext; simp [hc]; omega
  obtain ⟨t₀, ht₀⟩ := Function.ne_iff.1 hξ
  set i₀ : Fin a := t₀.1.1 with hi₀
  have hi₀m : (i₀ : ℕ) ≤ m := by have := t₀.2; omega
  have hvi₀ : v i₀ ≠ 0 := by rw [hi₀, hv]; exact ht₀
  let M : Matrix (Fin a) (Fin a) E := Matrix.of fun i k =>
    if i = mm then v k else if i = i₀ then (if k = mm then 1 else 0) else (1 : Matrix (Fin a) (Fin a) E) i k
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hrow : ∀ j, (M *ᵥ x) j = 0 := fun j => by rw [hx]; rfl
    have hoff : ∀ j, j ≠ i₀ → x j = 0 := by
      intro j hj
      by_cases hjm : j = mm
      · have hi₀ne : i₀ ≠ mm := hjm ▸ Ne.symm hj
        have := hrow i₀
        simpa [M, Matrix.mulVec, dotProduct, hi₀ne, hjm] using this
      · have := hrow j
        simpa [M, Matrix.mulVec, dotProduct, hjm, hj, Matrix.one_apply] using this
    apply hx0
    funext j
    by_cases hj : j = i₀
    · subst hj
      have := hrow mm
      simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, if_true] at this
      rw [Finset.sum_eq_single i₀ (fun k _ hk => by rw [hoff k hk, mul_zero]) (by simp)] at this
      exact (mul_eq_zero.1 this).resolve_left hvi₀
    · exact hoff j hj
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  refine ⟨hu.unit, ?_, ?_⟩
  · intro i k hik
    rw [IsUnit.unit_spec]
    simp only [M, Matrix.of_apply]
    rcases hik with hi | hk
    · have h1 : i ≠ mm := fun e => by rw [e] at hi; simp [hmm] at hi
      have h2 : i ≠ i₀ := fun e => by rw [e] at hi; omega
      simp [h1, h2]
    · have h1 : k ≠ mm := fun e => by rw [e] at hk; simp [hmm] at hk
      have h2 : k ≠ i₀ := fun e => by rw [e] at hk; omega
      split_ifs with e1 e2
      · subst e1
        simp only [v, Matrix.one_apply, h1.symm, if_false]
        rw [dite_eq_right (by omega)]
      · simp [e2, Matrix.one_apply, Ne.symm h2]
      · rfl
  · intro t
    rw [IsUnit.unit_spec]
    have hs : ∃ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), s.1.1 = mm := ⟨⟨(mm, c), by simp [hmm, hc]⟩, rfl⟩
    obtain ⟨s₀, hs₀⟩ := hs
    rw [Finset.sum_eq_single s₀]
    · simp only [eLast, hs₀, hmm, M, Matrix.of_apply, if_true, one_mul]
      exact hv t
    · intro s _ hs
      have : ¬ ((s.1.1 : ℕ) + 1 = m + 1) := by
        intro e
        apply hs
        apply Subtype.ext
        have h1 := s.2; have h2 := s₀.2
        apply Prod.ext
        · apply Fin.ext; rw [hs₀]; simp [hmm]; omega
        · apply Fin.ext; omega
      simp only [eLast, if_neg this, zero_mul]
    · simp

end GlobalTheory.CuspGeneric
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LocDict

namespace GlobalTheory.LTRecip

instance charZero_adicCompletion (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective

instance isSepClosure_kbar (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsSepClosure (w.adicCompletion E) (Kbar w) := inferInstance

end GlobalTheory.LTRecip

end
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.finite_cocycles_quotient_pow_smul_of_isOpen : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [CompactSpace M], FiniteDimensional ℚ_[p] K → (p : O) ∈ IsLocalRing.maximalIdeal O → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (ρ : Representation O G M), ContAction ρ → ∀ ϖ : O, Irreducible ϖ → (∀ n : ℕ, IsOpen ((powSub (M := M) ϖ n : Submodule O M) : Set M)) → ∀ n : ℕ, (Z1 (quotRep ρ ϖ n) : Set (G → M ⧸ powSub (M := M) ϖ n)).Finite := by
  first | exact @GlobalTheory.LocDualInt.finite_cocycles_quotient_pow_smul_module | exact GlobalTheory.LocDualInt.finite_cocycles_quotient_pow_smul_module | (intros; apply GlobalTheory.LocDualInt.finite_cocycles_quotient_pow_smul_module <;> assumption)
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.modUniformiser_cocycles_finite_classes_local : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [CompactSpace M] {G : Type} [Group G] [TopologicalSpace G] (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (ρ : Representation O G M), ContAction ρ → ∀ (ϖ : O), (p : O) ∈ Ideal.span {ϖ} → IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) → ∃ s : Finset (Z1 ρ), ∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈ LinearMap.range (LinearMap.lsmul O M ϖ) := by
  first | exact @GlobalTheory.modpi_cocycles_finite_classes | exact GlobalTheory.modpi_cocycles_finite_classes | (intros; apply GlobalTheory.modpi_cocycles_finite_classes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.approx_complexPadic_coboundary_algebraic_integer : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Set (GQ l)) (x : ℂ_[l]) (a : GQ l → ℤ_[l]), (∀ σ ∈ S, ‖Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) → ∃ (y : Om l) (b : GQ l → ℤ), (∀ σ ∈ S, ‖σ y - y - (b σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ, (l : ℤ) ^ r ∣ b σ → (l : ℤ_[l]) ^ r ∣ a σ := by
  first | exact @GlobalTheory.PMon.Ram.approx_algebraic_integer | exact GlobalTheory.PMon.Ram.approx_algebraic_integer | (intros; apply GlobalTheory.PMon.Ram.approx_algebraic_integer <;> assumption)
end
