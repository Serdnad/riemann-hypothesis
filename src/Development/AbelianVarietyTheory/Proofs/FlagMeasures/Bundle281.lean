module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle247
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle232
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle233
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle078
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle195
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle269
import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle051
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle201
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle056
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
import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem lintegral_triple_eq {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ₁ : Measure α) (μ₂ : Measure β) (μ₃ : Measure γ) [SFinite μ₂] [SFinite μ₃]
    (δ : β → ENNReal) (hδ : Measurable δ) (P : α × β × γ → ENNReal) (hP : Measurable P) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, P (u, m, k) ∂μ₃ ∂μ₂ ∂μ₁ = ∫⁻ x, δ x.2.1 * P x ∂(μ₁.prod (μ₂.prod μ₃)) := by
  symm
  rw [lintegral_prod (fun x => δ x.2.1 * P x)
    (show Measurable fun x : α × β × γ => δ x.2.1 * P x from (hδ.comp measurable_snd.fst).mul hP).aemeasurable]
  refine lintegral_congr fun u => ?_
  rw [lintegral_prod (fun y => δ y.1 * P (u, y))
    (show Measurable fun y : β × γ => δ y.1 * P (u, y) from
      (hδ.comp measurable_fst).mul (hP.comp measurable_prodMk_left)).aemeasurable]
  refine lintegral_congr fun m => ?_
  exact lintegral_const_mul (δ m)
    (show Measurable fun k : γ => P (u, m, k) from hP.comp (measurable_prodMk_left.comp measurable_prodMk_left))

theorem IsCut.sigmaFinite {n d : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)}
    {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsCut ε S E) {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : IsGaugeSub S d μ) : SigmaFinite μ := by
  obtain ⟨A, hA, hON, hspan, rfl⟩ := h
  exact (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hON hspan μ hμ).1

theorem localised_iwasawa_asymptotics : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsON EL → (∀ v, gau EN EM EK EL v = 0 → v = 0) → volume {v | gau EN EM EK EL v ≤ 1} ≠ ⊤ → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub (flagN ε W) dN μN → IsGaugeSub (flagM ε W) dM μM → IsGaugeSub (maxK ε) dK μK → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → Filter.Tendsto (fun r : ℝ => (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) * (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  intro n ε a j W hW dN dM dK dL EN EM EK EL hN hM hK hL hgau hvol μN μM μK hμN hμM hμK
  have := hN.sigmaFinite hμN
  have := hM.sigmaFinite hμM
  have := hK.sigmaFinite hμK
  obtain ⟨C, hC, hCη⟩ := GlobalTheory.T.iwasawa_product_gauge_sandwich_near_one n ε _ _ _ dN dM dK dL EN EM EK EL hN hM hK hL hgau
  obtain ⟨t₀, ht₀, hasym⟩ :=
    GlobalTheory.T.tendsto_prod_gaugeMeasures_gaugeBody n ε _ _ _ dN dM dK dL EN EM EK EL hN hM hK hgau μN μM μK hμN hμM hμK
  obtain ⟨t₁, ht₁, h₁⟩ := hCη 1 one_pos
  obtain ⟨ts, hts, hts0, hts1⟩ : ∃ ts : ℝ, 0 < ts ∧ ts ≤ t₀ ∧ ts ≤ t₁ :=
    ⟨min t₀ t₁, lt_min ht₀ ht₁, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨ρ₀, hρ₀, hball⟩ := GlobalTheory.T.iwasawa_factors_near_one_of_product_near_one n ε a j W hW ts hts
  obtain ⟨hdltm, -, hdlt⟩ := GlobalTheory.T.leviFactorInverseModulus_properties n ε a j W

  have hae : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.1 ∈ flagN ε W ∧ x.2.1 ∈ flagM ε W ∧ x.2.2 ∈ maxK ε := by
    have h1 : (μN.prod (μM.prod μK)) ((flagN ε W)ᶜ ×ˢ Set.univ) = 0 := by
      rw [Measure.prod_prod, hμN.1, zero_mul]
    have h2 : (μN.prod (μM.prod μK)) (Set.univ ×ˢ ((flagM ε W)ᶜ ×ˢ Set.univ)) = 0 := by
      rw [Measure.prod_prod, Measure.prod_prod, hμM.1, zero_mul, mul_zero]
    have h3 : (μN.prod (μM.prod μK)) (Set.univ ×ˢ (Set.univ ×ˢ (maxK ε)ᶜ)) = 0 := by
      rw [Measure.prod_prod, Measure.prod_prod, hμK.1, mul_zero, mul_zero]
    have e1 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.1 ∈ flagN ε W := by
      rw [ae_iff]
      exact measure_mono_null (fun x hx => Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩) h1
    have e2 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.2.1 ∈ flagM ε W := by
      rw [ae_iff]
      exact measure_mono_null
        (fun x hx => Set.mem_prod.2 ⟨Set.mem_univ _, Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩⟩) h2
    have e3 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.2.2 ∈ maxK ε := by
      rw [ae_iff]
      exact measure_mono_null
        (fun x hx => Set.mem_prod.2 ⟨Set.mem_univ _, Set.mem_prod.2 ⟨Set.mem_univ _, hx⟩⟩) h3
    filter_upwards [e1, e2, e3] with x hx1 hx2 hx3
    exact ⟨hx1, hx2, hx3⟩
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρρ₀ => ?_⟩
  have hPmeas : ∀ r : ℝ, Measurable fun x : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε × Formalism.REAL.UJ ε =>
      (hsBall ε r).indicator (1 : Formalism.REAL.UJ ε → ENNReal) (x.1 * x.2.1 * x.2.2) *
        (slab ε EL ρ r).indicator 1 x.2.2 := by
    intro r
    exact ((measurable_one.indicator (measurableSet_hsBall ε r)).comp
      ((measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd)).mul
      ((measurable_one.indicator (measurableSet_slab ε EL ρ r)).comp measurable_snd.snd)

  have hF : ∀ r : ℝ, (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) *
      (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) =
      ∫⁻ x, dlt j W x.2.1 * ((hsBall ε r).indicator 1 (x.1 * x.2.1 * x.2.2) *
        (slab ε EL ρ r).indicator 1 x.2.2) ∂(μN.prod (μM.prod μK)) := fun r =>
    GlobalTheory.IwConst.lintegral_triple_eq μN μM μK (dlt j W) hdltm _ (hPmeas r)
  have hc := continuous_nrm_uMat ε
  apply GlobalTheory.T.tendsto_small_ball_density_of_squeeze _ (dN + (dM + dK)) _ hvol
  intro η hη
  obtain ⟨t₂, ht₂, h₂⟩ := hCη η hη
  obtain ⟨t₃, ht₃, h₃⟩ := hdlt η hη
  obtain ⟨t, ht, htts, htρ, htt₂, htt₃⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ts ∧ t ≤ ρ ∧ t ≤ t₂ ∧ t ≤ t₃ :=
    ⟨min (min ts ρ) (min t₂ t₃), lt_min (lt_min hts hρ) (lt_min ht₂ ht₃),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hBmeas : ∀ s : ℝ, MeasurableSet {x : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε × Formalism.REAL.UJ ε |
      (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧
        gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ s} := by
    intro s
    refine measurableSet_setOfPred.2
      (((measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_fst) measurable_const)).and
      ((measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_snd.fst) measurable_const)).and
        (measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_snd.snd) measurable_const)))).and
      (measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const)))
    exact (continuous_gau EN EM EK EL).measurable.comp
      (((continuous_crd_uMat ε EN).measurable.comp measurable_fst).prodMk
        (((continuous_crd_uMat ε EM).measurable.comp measurable_snd.fst).prodMk
          ((continuous_crd_uMat ε EK).measurable.comp measurable_snd.snd)))
  refine ⟨fun s => (μN.prod (μM.prod μK)) {x |
      (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧
        gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ s},
    hasym t ht (htts.trans hts0), ?_⟩
  have hr₁ : 0 < min ρ₀ (t / (2 * C)) := lt_min hρ₀ (div_pos ht (by positivity))
  filter_upwards [Ioo_mem_nhdsGT hr₁] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hrρ₀ : r ≤ ρ₀ := (lt_of_lt_of_le hr1 (min_le_left _ _)).le
  have hrC : 2 * C * r < t := by
    have h := lt_of_lt_of_le hr1 (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    linarith
  have hη1 : (0 : ℝ) < 1 + η := by linarith
  rw [hF r]
  constructor
  ·
    rw [← lintegral_indicator_one (hBmeas _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with x hx
    obtain ⟨hxN, hxM, hxK⟩ := hx
    rw [Set.indicator_apply]
    split_ifs with hB
    · obtain ⟨⟨hu, hm, hk⟩, hγ⟩ := hB
      obtain ⟨-, hσγ, -, -, -⟩ := h₂ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu htt₂)
        (lt_of_lt_of_le hm htt₂) (lt_of_lt_of_le hk htt₂) _ _ rfl rfl
      have hσ : max (nrm (uMat (x.1 * x.2.1 * x.2.2) - 1)) (len (crd EL (uMat x.2.2 - 1))) ≤ r := by
        refine hσγ.trans ?_
        calc (1 + η) * gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
              crd EK (uMat x.2.2 - 1)) ≤ (1 + η) * (r / (1 + η)) :=
              mul_le_mul_of_nonneg_left hγ hη1.le
          _ = r := by field_simp
      have hmem1 : x.1 * x.2.1 * x.2.2 ∈ hsBall ε r :=
        ((le_max_left _ _).trans hσ : nrm (uMat (x.1 * x.2.1 * x.2.2) - 1) ≤ r)
      have hmem2 : x.2.2 ∈ slab ε EL ρ r :=
        (⟨lt_of_lt_of_le hk htρ, (le_max_right _ _).trans hσ⟩ :
          nrm (uMat x.2.2 - 1) < ρ ∧ len (crd EL (uMat x.2.2 - 1)) ≤ r)
      rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2]
      simp only [Pi.one_apply, mul_one]
      exact (h₃ x.2.1 hxM (lt_of_lt_of_le hm htt₃)).2
    · exact bot_le
  ·
    rw [← lintegral_indicator_one (hBmeas _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with x hx
    obtain ⟨hxN, hxM, hxK⟩ := hx
    by_cases hA : x.1 * x.2.1 * x.2.2 ∈ hsBall ε r
    swap
    · simp [Set.indicator_apply, hA]
    by_cases hS : x.2.2 ∈ slab ε EL ρ r
    swap
    · simp [Set.indicator_apply, hS]
    rw [Set.indicator_of_mem hA, Set.indicator_of_mem hS]
    simp only [Pi.one_apply, mul_one]
    have hA' : nrm (uMat (x.1 * x.2.1 * x.2.2) - 1) ≤ r := hA
    obtain ⟨hkρ, hL⟩ := (hS : nrm (uMat x.2.2 - 1) < ρ ∧ len (crd EL (uMat x.2.2 - 1)) ≤ r)
    obtain ⟨hu1, hm1, hk1⟩ :=
      hball x.1 hxN x.2.1 hxM x.2.2 (hA'.trans hrρ₀) (lt_of_lt_of_le hkρ hρρ₀)
    have hσ : max (nrm (uMat (x.1 * x.2.1 * x.2.2) - 1)) (len (crd EL (uMat x.2.2 - 1))) ≤ r :=
      max_le hA' hL
    obtain ⟨hγ1, -, hCu, hCm, hCk⟩ := h₁ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu1 hts1)
      (lt_of_lt_of_le hm1 hts1) (lt_of_lt_of_le hk1 hts1) _ _ rfl rfl
    have hγ2 : gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
        crd EK (uMat x.2.2 - 1)) ≤ 2 * r := by
      have := mul_le_mul_of_nonneg_left hσ (by norm_num : (0 : ℝ) ≤ 1 + 1)
      linarith
    have hCγ := mul_le_mul_of_nonneg_left hγ2 hC.le
    have hu : nrm (uMat x.1 - 1) < t := by linarith
    have hm : nrm (uMat x.2.1 - 1) < t := by linarith
    have hk : nrm (uMat x.2.2 - 1) < t := by linarith
    obtain ⟨hγη, -, -, -, -⟩ := h₂ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu htt₂)
      (lt_of_lt_of_le hm htt₂) (lt_of_lt_of_le hk htt₂) _ _ rfl rfl
    have hγ : gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
        crd EK (uMat x.2.2 - 1)) ≤ (1 + η) * r :=
      hγη.trans (mul_le_mul_of_nonneg_left hσ hη1.le)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [if_pos ⟨⟨hu, hm, hk⟩, hγ⟩, Pi.one_apply, mul_one]
    exact (h₃ x.2.1 hxM (lt_of_lt_of_le hm htt₃)).1

end GlobalTheory.IwConst
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepAverage

theorem isClosedEmbedding_entries {n : ℕ} (ε : Fin n → Bool) :
    Topology.IsClosedEmbedding (fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) := by
  have key := (uJEmb n ε).1
  exact key

theorem isClosedEmbedding_entries_inf (I : AutInst) :
    Topology.IsClosedEmbedding (fun g : I.Ginf =>
      (fun v i j => uMat (g v) i j : InfinitePlace I.F → Fin I.n → Fin I.n → ℂ)) := by
  have h : ∀ v : InfinitePlace I.F, Topology.IsClosedEmbedding
      (fun g : Formalism.REAL.UJ (I.ε v) => (fun i j => uMat g i j : Fin I.n → Fin I.n → ℂ)) :=
    fun v => isClosedEmbedding_entries (I.ε v)
  exact Topology.IsClosedEmbedding.piMap h

theorem integrable_loc {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {F : (Fin n → Fin n → ℂ) → ℂ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun g : UJ ε => F (fun i j => umat g i j) • σ (umat g) w) (muG ε) := by
  have hemb := isClosedEmbedding_entries ε
  have hrep : Continuous (fun g : UJ ε => σ (umat g) w) :=
    (hσ.2.2 w).comp_continuous hemb.continuous (fun g => g.2)
  have hcs : HasCompactSupport (fun g : UJ ε => F (fun i j => umat g i j) • σ (umat g) w) :=
    (hc.comp_isClosedEmbedding hemb).smul_right
  exact ((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs

theorem integrable_inf (B : RowsAut) (hσ : IsURep B.σs) (w : B.Hs)
    {F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g w) (muInf B.I) := by
  have hemb := isClosedEmbedding_entries_inf B.I
  have hrep : Continuous (fun g : B.I.Ginf => B.σs g w) := hσ.2.2.2 w
  have hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v) := rfl
  haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by
    rw [hμ]
    infer_instance
  have hcs : HasCompactSupport (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g w) :=
    (hc.comp_isClosedEmbedding hemb).smul_right
  exact ((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs

theorem tens_average (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) (hσ : IsURep B.σs)
    (w : ∀ v, B.H v) (F : InfinitePlace B.I.F → (Fin B.I.n → Fin B.I.n → ℂ) → ℂ)
    (hF : ∀ v, ContDiff ℝ ∞ (F v)) (hc : ∀ v, HasCompactSupport (F v)) :
    ∃ G : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      B.tens (fun v => ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) • B.σ v (umat g) (w v) ∂(muG (B.I.ε v))) =
        ∫ g, G (fun v i j => uMat (g v) i j) • B.σs g (B.tens w) ∂(muInf B.I) := by
  classical
  obtain ⟨hin, hact, hden⟩ := B.tens_spec
  set G : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun x => ∏ v, F v (x v) with hGdef
  have hGs : ContDiff ℝ ∞ G :=
    contDiff_prod (fun v _ => (hF v).comp (contDiff_apply ℝ (fun _ => (Fin B.I.n → Fin B.I.n → ℂ)) v))
  have hGc : HasCompactSupport G := by
    refine HasCompactSupport.intro' (isCompact_univ_pi fun v => hc v)
      (isClosed_set_pi fun v _ => isClosed_tsupport (F v)) ?_
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨v, hv⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)
  refine ⟨G, hGs, hGc, ?_⟩
  refine eq_of_inner_eq_on_dense_span hden ?_
  rintro y ⟨x, rfl⟩
  have hloc : ∀ v, ⟪x v, ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) • B.σ v (umat g) (w v)
        ∂(muG (B.I.ε v))⟫_ℂ =
      ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) * ⟪x v, B.σ v (umat g) (w v)⟫_ℂ ∂(muG (B.I.ε v)) := by
    intro v
    rw [← integral_inner (integrable_loc (hU v) (w v) (hF v).continuous (hc v))]
    simp only [inner_smul_right]
  have hglob : ⟪B.tens x, ∫ g, G (fun v i j => uMat (g v) i j) • B.σs g (B.tens w) ∂(muInf B.I)⟫_ℂ =
      ∫ g : B.I.Ginf, ∏ v, (F v (fun i j => uMat (g v) i j) * ⟪x v, B.σ v (uMat (g v)) (w v)⟫_ℂ)
        ∂(muInf B.I) := by
    rw [← integral_inner (integrable_inf B hσ (B.tens w) hGs.continuous hGc)]
    congr 1
    funext g
    rw [inner_smul_right, hact, hin, Finset.prod_mul_distrib]
  have hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v) := rfl
  have hprod := integral_fintype_prod_eq_prod (μ := fun v => muG (B.I.ε v))
    (fun v (h : UJ (B.I.ε v)) => F v (fun i j => uMat h i j) * ⟪x v, B.σ v (uMat h) (w v)⟫_ℂ)
  rw [hglob, hin, hμ]
  refine Eq.trans ?_ hprod.symm
  exact Finset.prod_congr rfl (fun v _ => hloc v)

theorem exists_smooth_average : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  intro hSL B d hd P u hu
  have hσ : IsURep B.σs := (tensorRep B d hd).1
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => (hd v).2.1.2.2.1

  let Av : B.Hs → Prop := fun y => ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ,
    ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      y = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I)
  have hzero : Av 0 := by
    refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_⟩
    simp only [zero_smul, integral_zero]
  have hadd : ∀ a b, Av a → Av b → Av (a + b) := by
    rintro a b ⟨F₁, hF₁, hc₁, rfl⟩ ⟨F₂, hF₂, hc₂, rfl⟩
    refine ⟨F₁ + F₂, hF₁.add hF₂, hc₁.add hc₂, ?_⟩
    rw [← integral_add (integrable_inf B hσ _ hF₁.continuous hc₁)
      (integrable_inf B hσ _ hF₂.continuous hc₂)]
    congr 1
    funext g
    rw [Pi.add_apply, add_smul]
  have hsmul : ∀ (c : ℂ) a, Av a → Av (c • a) := by
    rintro c a ⟨F₁, hF₁, hc₁, rfl⟩
    refine ⟨fun x => c * F₁ x, contDiff_const.mul hF₁, hc₁.mul_left, ?_⟩
    rw [← integral_smul]
    congr 1
    funext g
    rw [mul_smul]

  have hbase : ∀ x : ∀ v, B.H v, (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (B.tens x) := by
    intro x hx
    have hloc : ∀ v, ∃ F : (Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        x v = ∫ g : UJ (B.I.ε v), F (fun i j => umat g i j) • B.σ v (umat g) (B.w v) ∂(muG (B.I.ε v)) := by
      intro v
      have hlow := (hd v).2.2.1
      have hw0 : B.w v ≠ 0 := by
        intro h0
        have h1 := hlow.1
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      have hK := (hSL B.I.n (B.I.ε v) (B.lam v) (hd v).1 (B.H v) (B.σ v) (hd v).2.1).1
      exact GlobalTheory.T.exists_smooth_average_eq_of_mem_lowKSub' B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (B.w v) (hU v) hK hlow.2 hw0 (x v) (hx v)
    choose Fl hFl hcl hxl using hloc
    obtain ⟨G, hG, hcG, hEq⟩ := tens_average B hU hσ B.w Fl hFl hcl
    refine ⟨G, hG, hcG, ?_⟩
    rw [← hEq]
    congr 1
    funext v
    exact hxl v

  have hstep : ∀ (E : gInf B) y, Av y → Av (dAct B E y) := by
    rintro E y ⟨F₁, hF₁, hc₁, rfl⟩
    obtain ⟨F', hF', hc', hder⟩ := GlobalTheory.T.hasDerivAt_completedTensorOrbit_smoothAverage B F₁ E (B.tens B.w) hσ hF₁ hc₁
    exact ⟨F', hF', hc', hder.deriv⟩
  have hword : ∀ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (x : ∀ v, B.H v),
      (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (wordAct B l (B.tens x)) := by
    intro l x hx
    induction l with
    | nil => exact hbase x hx
    | cons X l ih => exact hstep (atPlace B X.1 X.2) _ ih
  have hu' : u ∈ Submodule.span ℂ {y | ∃ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v)))
      (x : ∀ v, B.H v), l.length ≤ P ∧ (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) ∧
        y = wordAct B l (B.tens x)} := hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, x, -, hx, rfl⟩ := hy
    exact hword l x hx
  | zero => exact hzero
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c a ha

end GlobalTheory.StepAverage
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.WeylUnitary

theorem delSq_irreducible_unitary :
    ∀ (n : ℕ) (lam : DomWeight n), FiniteDimensional ℂ (delSq ℂ n lam) ∧ delSq ℂ n lam = nablaSq ℂ n lam ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ delSq ℂ n lam, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam) ∧ ∀ U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ), U ≤ delSq ℂ n lam → (∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ p ∈ U, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ U) → U = ⊥ ∨ U = delSq ℂ n lam := by
  intro n lam
  rw [← Formalism.L2.Col.nablaSq_eq_delSq ℂ lam]
  have ha : Antitone lam.natW := fun i j hij => by
    have := lam.anti hij
    simp only [DomWeight.natW]
    omega
  refine ⟨GlobalTheory.Branching.finite_nablaSq ℂ n lam, rfl,
    fun g p hp => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ g p hp, fun U hle hU => ?_⟩
  rw [or_iff_not_imp_left]
  intro hne
  exact le_antisymm hle (GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl _ ha U hle
    (GlobalTheory.Branching.rowDivClosed_of_rowAct_stable U (GlobalTheory.Branching.rowAct_mem_of_unitary_stable U hU)) hne)

end GlobalTheory.WeylUnitary
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalWittFree

theorem exists_smul_ratTup_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y := by
  intro F E _ _ _ _ _ σ hcm n J hJ v r P T hP y hy hgram

  obtain ⟨f, hf⟩ := GlobalTheory.T.extend_free_tuple_gram_hermitian_frame F E σ hcm n J hJ v r P T hP y hy hgram

  have hdet := (GlobalTheory.FrameGram.std_frame_gram F E σ hcm n J hJ r P T hP).1

  obtain ⟨g, hg⟩ := GlobalTheory.LocalWittND.exists_smul_ratTup_eq F E σ hcm n J hJ v (r + 1 + r)
    (tupH P) hdet (Fin.append y f) hf
  refine ⟨g, funext fun i => ?_⟩

  have hF : (fun j => tupH P (Fin.castAdd r j)) = F0 P :=
    funext fun j => by simp [tupH, Fin.append_left]
  have h1 : (g • ratTup (F := F) (Fv F v) (tupH P)) (Fin.castAdd r i) =
      (g • ratTup (F := F) (Fv F v) (F0 P)) i := by
    rw [← hF]; rfl
  rw [← h1, hg, Fin.append_left]

end GlobalTheory.LocalWittFree
end
