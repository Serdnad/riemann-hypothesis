module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle009
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle013
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationInjectiveOpenMap
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.UnitsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle083
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteProjectionPushforward
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Formalism.ConjugateSelfDual.Bundle001

@[expose] public section

section

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreShift

theorem comp_shift_props {V : Type} [TopologicalSpace V] [T2Space V] {W : Set V} (hW : IsOpen W)
    {T T' : V → V} (hT : ContinuousOn T W) (hT' : ContinuousOn T' W)
    (hmem : ∀ v, T v ∈ W ↔ v ∈ W) (hmem' : ∀ v, T' v ∈ W ↔ v ∈ W)
    (hinv : ∀ v ∈ W, T' (T v) = v) {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ W) :
    Continuous (fun v => φ (T v)) ∧ HasCompactSupport (fun v => φ (T v)) ∧
      tsupport (fun v => φ (T v)) ⊆ W := by
  have hC : IsCompact (T' '' tsupport φ) := hc.isCompact.image_of_continuousOn (hT'.mono hs)
  have hCW : T' '' tsupport φ ⊆ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hmem' w).2 (hs hw)
  have hsup : ∀ v, v ∉ T' '' tsupport φ → φ (T v) = 0 := by
    intro v hv
    by_contra h
    have h1 : T v ∈ tsupport φ := subset_tsupport _ h
    exact hv ⟨T v, h1, hinv v ((hmem v).1 (hs h1))⟩
  have hts : tsupport (fun v => φ (T v)) ⊆ T' '' tsupport φ := by
    refine closure_minimal ?_ hC.isClosed
    intro v hv
    by_contra h
    exact hv (hsup v h)
  refine ⟨continuous_of_tsupport fun v hv => ?_, HasCompactSupport.intro hC hsup, hts.trans hCW⟩
  exact ContinuousAt.comp (g := φ) hφ.continuousAt (hT.continuousAt (hW.mem_nhds (hCW (hts hv))))

theorem continuous_lintegral {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y}
    {ι : X → Y} {U : Set V} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) {φ : V → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (h0 : ∀ v, 0 ≤ φ v) :
    Continuous fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by
  obtain ⟨hi, hc1⟩ := h.2.2 φ hφ hc hs
  have hcont : Continuous fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
    ENNReal.continuous_ofReal.comp (continuousOn_univ.1 hc1)
  exact hcont.congr fun b =>
    ofReal_integral_eq_lintegral_ofReal (hi b (Set.mem_univ b)) (Filter.Eventually.of_forall h0)

theorem setLIntegral_eq_lintegral {V : Type} [MeasurableSpace V] {μ : Measure V} {W : Set V}
    (hW : MeasurableSet W) {a : V → ℝ≥0∞} (ha : ∀ v, v ∉ W → a v = 0) :
    ∫⁻ v in W, a v ∂μ = ∫⁻ v, a v ∂μ := by
  rw [← lintegral_indicator hW]
  congr 1
  funext v
  by_cases hv : v ∈ W
  · rw [Set.indicator_of_mem hv]
  · rw [Set.indicator_of_notMem hv, ha v hv]

theorem lintegral_shift {V X Y : Type} [TopologicalSpace V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure V} {ν : Measure X} [ν.IsAddHaarMeasure] {f : V → Y} {g : V → X}
    {ι : X → Y} (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {U W : Set V} (hW : IsOpen W) (hWU : W ⊆ U) {fib : X → Measure V}
    (hF : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) {T : X → V → V}
    (hTm : ∀ s, Measurable (T s)) (hTμ : ∀ s, μ.map (T s) = μ)
    (hTc : ∀ s, ContinuousOn (T s) W) (hTW : ∀ s v, T s v ∈ W ↔ v ∈ W)
    (hinv : ∀ s, ∀ v ∈ W, T (-s) (T s v) = v) (hgT : ∀ s, ∀ v ∈ W, g (T s v) = g v + s)
    {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ W)
    (h0 : ∀ v, 0 ≤ φ v) (s c : X) :
    ∫⁻ v, ENNReal.ofReal (φ (T s v)) ∂(fib c) = ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib (c + s)) := by
  obtain ⟨hφs, hcs, hss⟩ :=
    comp_shift_props hW (hTc s) (hTc (-s)) (hTW s) (hTW (-s)) (hinv s) hφ hc hs
  have hψm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hψ0 : ∀ v, v ∉ W → ENNReal.ofReal (φ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]
  have hψs0 : ∀ v, v ∉ W → ENNReal.ofReal (φ (T s v)) = 0 :=
    fun v hv => hψ0 _ fun h => hv ((hTW s v).1 h)
  have hD := continuous_lintegral hF hφ hc (hs.trans hWU) h0
  have hD' := continuous_lintegral hF hφs hcs (hss.trans hWU) (fun v => h0 _)
  have hDs : Continuous fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib (b + s)) :=
    hD.comp (continuous_add_const s)
  refine GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts X ν Set.univ isOpen_univ _ _ hD'.continuousOn hDs.continuousOn
    (fun S hS _ => ?_) c (Set.mem_univ c)
  have hSm := hS.measurableSet
  have hS'm : MeasurableSet ((fun x : X => x - s) ⁻¹' S) :=
    (continuous_sub_right s).measurable hSm
  have e1 := GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage hι hg hf hW hWU hF
    (fun v => ENNReal.ofReal (φ (T s v))) (hψm.comp (hTm s)) hψs0 S hSm
  have e2 := GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage hι hg hf hW hWU hF
    (fun v => ENNReal.ofReal (φ v)) hψm hψ0 _ hS'm
  have hAm : Measurable ((g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
      fun v => ENNReal.ofReal (φ v)) := hψm.indicator (hg.measurable hS'm)
  have hA0 : ∀ v, v ∉ W → (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
      (fun v => ENNReal.ofReal (φ v)) v = 0 :=
    fun v hv => Set.indicator_apply_eq_zero.2 fun _ => hψ0 v hv
  have hB0 : ∀ v, v ∉ W → (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v = 0 :=
    fun v hv => Set.indicator_apply_eq_zero.2 fun _ => hψs0 v hv
  have hcomp : ∀ v, (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v =
      (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator (fun v => ENNReal.ofReal (φ v)) (T s v) := by
    intro v
    by_cases hv : v ∈ W
    · have hiff : T s v ∈ g ⁻¹' ((fun x : X => x - s) ⁻¹' S) ↔ v ∈ g ⁻¹' S := by
        simp only [Set.mem_preimage, hgT s v hv, add_sub_cancel_right]
      by_cases hvS : v ∈ g ⁻¹' S
      · rw [Set.indicator_of_mem hvS, Set.indicator_of_mem (hiff.2 hvS)]
      · rw [Set.indicator_of_notMem hvS, Set.indicator_of_notMem (fun h => hvS (hiff.1 h))]
    · rw [hB0 v hv, hA0 _ fun h => hv ((hTW s v).1 h)]
  have hmid : ∫⁻ v in W, (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v ∂μ =
      ∫⁻ v in W, (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
        (fun v => ENNReal.ofReal (φ v)) v ∂μ := by
    rw [setLIntegral_eq_lintegral hW.measurableSet hB0,
      setLIntegral_eq_lintegral hW.measurableSet hA0]
    simp only [hcomp]
    rw [← lintegral_map hAm (hTm s), hTμ s]
  have hpre : (fun x : X => x + s) ⁻¹' ((fun x : X => x - s) ⁻¹' S) = S := by
    ext x
    simp
  have htr := (measurePreserving_add_right ν s).setLIntegral_comp_preimage hS'm hD.measurable
  rw [hpre] at htr
  rw [← e1, hmid, e2, ← htr]

theorem fib_ne_zero : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [ν.IsAddHaarMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U W : Set V), IsOpen W → W ⊆ U → W.Nonempty → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ T : X → V → V, (∀ s, Measurable (T s)) → (∀ s, μ.map (T s) = μ) → (∀ s, ContinuousOn (T s) W) → (∀ s v, T s v ∈ W ↔ v ∈ W) → (∀ s, ∀ v ∈ W, T (-s) (T s v) = v) → (∀ s, ∀ v ∈ W, g (T s v) = g v + s) → ∀ b : X, fib b ≠ 0 := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf U W hW hWU hne fib hF T hTm hTμ
    hTc hTW hinv hgT b hb
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨φ, hφ, hc, hs, h0, -, h1⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump
    (isCompact_singleton (x := v₀)) hW (Set.singleton_subset_iff.2 hv₀)
  have hzero : ∀ c, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) = 0 := by
    intro c
    have key := lintegral_shift hι hg hf hW hWU hF hTm hTμ hTc hTW hinv hgT hφ hc hs h0 (c - b) b
    rw [add_sub_cancel] at key
    rw [← key, hb]
    simp
  have hm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have h2 := hF.2.1 _ hm
  simp only [hzero, lintegral_zero] at h2
  have h3 : ∫⁻ v in W, ENNReal.ofReal (φ v) ∂μ = 0 :=
    le_antisymm (h2 ▸ lintegral_mono_set hWU) bot_le
  have hae := (ae_restrict_iff' hW.measurableSet).1 ((lintegral_eq_zero_iff hm).1 h3)
  have hOpen : IsOpen ({v | 0 < φ v} ∩ W) := (isOpen_lt continuous_const hφ).inter hW
  have hpos : 0 < μ ({v | 0 < φ v} ∩ W) :=
    hOpen.measure_pos μ ⟨v₀, by simp [h1 v₀ rfl], hv₀⟩
  have hnull := ae_iff.1 hae
  refine hpos.ne' (measure_mono_null ?_ hnull)
  intro v hv
  rw [Set.mem_setOf_eq]
  intro hcon
  have h4 := hcon hv.2
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h4
  exact absurd hv.1 (not_lt.2 h4)

end GlobalTheory.CompanionTheory.SW.FibreShift
end

section

open MeasureTheory Topology Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreUniq

theorem fibreFamily_eq_inter (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (W : Set V) (hW : IsOpen W)
    (B B' : Set X) (hB : IsOpen B) (hB' : IsOpen B') (hBB : B' ⊆ B)
    (fib fib' : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B ∩ W) ν B fib)
    (h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B' ∩ W) ν B' fib')
    (b : X) (hb : b ∈ B') : fib' b = fib b := by
  have hO : IsOpen (g ⁻¹' B' ∩ W) := (hB'.preimage hg).inter hW
  have hOU : g ⁻¹' B' ∩ W ⊆ g ⁻¹' B ∩ W := Set.inter_subset_inter_left _ (Set.preimage_mono hBB)
  have hbB : b ∈ B := hBB hb
  refine measure_eq_of_lintegral_eq (fib' b) (fib b) (g ⁻¹' B' ∩ W) hO ?_ ?_ ?_
  · refine measure_mono_null ?_ (h'.1 b)
    intro v hv hv'
    exact hv hv'.2
  · refine measure_mono_null ?_ (h.1 b)
    intro v hv hv'
    have hgv : g v = b := hι (by rw [← hf v]; exact hv'.1)
    exact hv ⟨show g v ∈ B' from hgv ▸ hb, hv'.2.2⟩
  · intro φ hφc hφs hφO hφnn
    have hφU : tsupport φ ⊆ g ⁻¹' B ∩ W := hφO.trans hOU
    obtain ⟨hint', hcont'⟩ := h'.2.2 φ hφc hφs hφO
    obtain ⟨hint, hcont⟩ := h.2.2 φ hφc hφs hφU
    refine ⟨hint' b hb, ?_⟩
    have hψm : Measurable (fun v => ENNReal.ofReal (φ v)) := hφc.measurable.ennreal_ofReal
    have hψ0 : ∀ v, v ∉ g ⁻¹' B' ∩ W → ENNReal.ofReal (φ v) = 0 := by
      intro v hv
      have hz : φ v = 0 := by
        by_contra hne
        exact hv (hφO (subset_tsupport φ (Function.mem_support.mpr hne)))
      simp [hz]
    have hF : ∀ c ∈ B, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) = ENNReal.ofReal (∫ v, φ v ∂(fib c)) :=
      fun c hc => (ofReal_integral_eq_lintegral_ofReal (hint c hc) (ae_of_all _ hφnn)).symm
    have hF' : ∀ c ∈ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) =
        ENNReal.ofReal (∫ v, φ v ∂(fib' c)) :=
      fun c hc => (ofReal_integral_eq_lintegral_ofReal (hint' c hc) (ae_of_all _ hφnn)).symm
    have hset : ∀ S, MeasurableSet S →
        ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) ∂ν =
          ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) ∂ν := by
      intro S hS
      have hS' : MeasurableSet (S ∩ B') := hS.inter hB'.measurableSet
      have e1 := lintegral_preimage hι hg hf hO hOU h (fun v => ENNReal.ofReal (φ v)) hψm hψ0 _ hS'
      have e2 := lintegral_preimage hι hg hf hO Set.Subset.rfl h' (fun v => ENNReal.ofReal (φ v))
        hψm hψ0 _ hS'
      exact e1.symm.trans e2
    have key : ∀ (k k' : X → ℝ≥0∞) (T : Set X), MeasurableSet T → (∀ c ∈ T, k c = k' c) →
        ∫⁻ c in T, k c ∂ν = ∫⁻ c in T, k' c ∂ν := fun k k' T hT hkk =>
      lintegral_congr_ae ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall hkk))
    have hae : (fun c => ENNReal.ofReal (∫ v, φ v ∂(fib c))) =ᵐ[ν.restrict B']
        (fun c => ENNReal.ofReal (∫ v, φ v ∂(fib' c))) := by
      refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ ?_ ?_ ?_
      · exact ((hcont.mono hBB).aemeasurable hB'.measurableSet).ennreal_ofReal
      · exact (hcont'.aemeasurable hB'.measurableSet).ennreal_ofReal
      · intro S hS _
        rw [Measure.restrict_restrict hS]
        have hT : MeasurableSet (S ∩ B') := hS.inter hB'.measurableSet
        calc ∫⁻ c in S ∩ B', ENNReal.ofReal (∫ v, φ v ∂(fib c)) ∂ν
            = ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) ∂ν :=
              key _ _ _ hT (fun c hc => (hF c (hBB hc.2)).symm)
          _ = ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) ∂ν := hset S hS
          _ = ∫⁻ c in S ∩ B', ENNReal.ofReal (∫ v, φ v ∂(fib' c)) ∂ν :=
              key _ _ _ hT (fun c hc => hF' c hc.2)
    have heq := Measure.eqOn_open_of_ae_eq hae hB'
      (ENNReal.continuous_ofReal.comp_continuousOn (hcont.mono hBB))
      (ENNReal.continuous_ofReal.comp_continuousOn hcont') hb
    rw [hF' b hb, hF b hbB]
    exact heq.symm

end GlobalTheory.CompanionTheory.SW.FibreUniq
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.disintegration_injective_open_map : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U : Set V) (fib : X → Measure V), IsOpen U → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ φ : V → ℝ, Continuous φ → (∀ v, 0 ≤ φ v) → ∀ D : X → ℝ, Continuous D → (∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (φ v) ∂μ = ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν) → (∀ ε : ℝ, 0 < ε → ∃ K : Set V, IsCompact K ∧ K ⊆ U ∧ ∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A) ∩ Kᶜ, ENNReal.ofReal (φ v) ∂μ ≤ ENNReal.ofReal ε * ν A) → ∀ s₀ : X, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s₀) = ENNReal.ofReal (D s₀) := by
  first | exact @GlobalTheory.CompanionTheory.FibreDensityLimit.fibre_lintegral_eq_density | exact GlobalTheory.CompanionTheory.FibreDensityLimit.fibre_lintegral_eq_density | (intros; apply GlobalTheory.CompanionTheory.FibreDensityLimit.fibre_lintegral_eq_density <;> assumption)
end

section

open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace GlobalTheory.CompanionTheory.MatrixLie

theorem hasDerivAt_exp_mul_exp_of_finiteDimensional {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (X Y : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y)) (X + Y) 0 := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  have hX := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have hY := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  have hXY := hX.mul hY
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at hXY
  exact hXY

private theorem hasDerivAt_zero_linear_exp_smul_mul_exp_smul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (X Y : A) (ℓ : A →ₗ[ℝ] ℂ) :
    HasDerivAt (fun t : ℝ => ℓ (NormedSpace.exp (t • X) * NormedSpace.exp (t • Y))) (ℓ (X + Y)) 0 :=
  (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_mul_exp_of_finiteDimensional X Y)

theorem entry_hasDerivAt_exp_mul_exp {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ =>
      (NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • Y)) i j) ((X + Y) i j) 0 := by
  have hs : ∀ (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ), ((t : ℂ) • Z) = t • Z := by
    intro t Z
    ext a b
    simp [Complex.real_smul]
  simp only [hs]
  exact @hasDerivAt_zero_linear_exp_smul_mul_exp_smul (Matrix (Fin n) (Fin n) ℂ) Matrix.linftyOpNormedRing
    Matrix.linftyOpNormedAlgebra inferInstance X Y
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem hasDerivAt_exp_mul_exp {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • Y))
      (X + Y) 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => entry_hasDerivAt_exp_mul_exp X Y i j

theorem exists_submodule_eq_lieAlg :
    ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G →
      ∃ S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
        (S : Set (Matrix (Fin n) (Fin n) ℂ)) = lieAlg G := by
  intro n G hG
  refine ⟨{ carrier := lieAlg G, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, rfl⟩
  · intro a b ha hb
    have ha' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • a) ∈ G := ha
    have hb' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • b) ∈ G := hb
    refine GlobalTheory.T.lie_algebra_of_tangent_curve n G hG
      (fun t : ℝ => NormedSpace.exp ((t : ℂ) • a) * NormedSpace.exp ((t : ℂ) • b)) (a + b) ?_ ?_
      (hasDerivAt_exp_mul_exp a b)
    · simp
    · exact Filter.Eventually.of_forall (fun t => hG.2.2.1 _ (ha' t) _ (hb' t))
  · show ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (0 : Matrix (Fin n) (Fin n) ℂ)) ∈ G
    intro t
    simpa using hG.2.1
  · intro c X hX
    have hX' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ G := hX
    show ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (c • X)) ∈ G
    intro t
    have he : ((t : ℂ) • (c • X)) = ((t * c : ℝ) : ℂ) • X := by
      ext a b
      simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [he]
    exact hX' (t * c)

end GlobalTheory.CompanionTheory.MatrixLie
end
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

variable {F : Type} [Field F] [NumberField F]

def LocMem (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (z : F) : Prop :=
  ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ y ∈ I, (s : F) * z = (y : F)

def cosetOff {ι : Type} (S : Finset (HeightOneSpectrum (𝓞 F))) (I : Ideal (𝓞 F)) (x0 : ι → F) : Set (ι → F) :=
  {x | ∀ v, v ∉ S → ∀ i, LocMem I v (x i - x0 i)}

def latCoset {ι : Type} (I : Ideal (𝓞 F)) (x0 : ι → F) : Set (ι → F) :=
  {x | ∀ i, ∃ y ∈ I, (y : F) = x i - x0 i}

def ballV (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : Set (Fv F v) :=
  {z | Valued.v z ≤ WithZero.exp (-(k : ℤ))}

def boxInd {ι : Type} (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (c y : ι → Fv F v) : ℝ :=
  if ∀ i, y i - c i ∈ ballV v k then 1 else 0

def term {ι : Type} (θ : ℝ →+* Ainf F) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (ι → Ainf F) → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ) (ε : ℝ) (x : ι → F) : ℝ :=
  φ (fun i => θ ε * algebraMap F (Ainf F) (x i)) * ∏ v ∈ S, ψ v fun i => algebraMap F (Fv F v) (x i)

end GlobalTheory.CompanionTheory.Equi

end
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Mass.MeanV

variable {F : Type} [Field F] [NumberField F]

def IntOut (T : Finset (HeightOneSpectrum (𝓞 F))) : Set F :=
  {x | ∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F}

def GoodFac (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ) : Prop :=
  ContinuousOn g {0}ᶜ ∧ (∀ s, s ∉ v.adicCompletionIntegers F → g s = 0) ∧
    (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧
    (∀ s : Fv F v, Valued.v s = 1 → |g s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ∧ ∫ s, g s ∂lam = 1

def truncSum (θ : ℝ →+* Ainf F) (G : Ainf F → ℝ) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (δ : ℝ) : ℝ :=
  δ ^ Module.finrank ℚ F * ∑' β : {β : F // β ≠ 0}, (IntOut T).indicator
    (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) β.1

def fullSum (θ : ℝ →+* Ainf F) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (δ : ℝ) : ℝ :=
  δ ^ Module.finrank ℚ F * ∑' β : {β : F // β ≠ 0},
    G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix

theorem _root_.GlobalTheory.T.hyperbolic_pair_unitary_transitive : ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) → (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) → ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) → ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 → hform τ H y y = 0 → ∑ k, a k * y k = 1 → ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive | exact GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

theorem _root_.GlobalTheory.T.uniformizer_ratio_valuation_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ ϖ' : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → ∀ U : (v.adicCompletion F)ˣ, (U : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ϖ : F) = algebraMap F (v.adicCompletion F) (ϖ' : F) → GroundTheory.LocalField.ord (U : v.adicCompletion F) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero | exact GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero <;> assumption)
end

section

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

theorem _root_.GlobalTheory.T.analytic_germ_finite_projection : FiniteGermProjectionOpenAt.Statement → GermFiniteProjection.Statement → AnalyticGermComponents.Statement → ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w → AccPt w (𝓟 X) → ∃ (Y W : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), W ∈ 𝓝 w ∧ Y ∩ W ⊆ X ∧ IsAnalyticNear Y w ∧ GermIrreducibleAt Y w ∧ (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) ∧ ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.AnalyticGermSlice.exists_irreducible_slice | exact GlobalTheory.CompanionTheory.AnalyticGermSlice.exists_irreducible_slice | (intros; apply GlobalTheory.CompanionTheory.AnalyticGermSlice.exists_irreducible_slice <;> assumption)
end

section

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

theorem _root_.GlobalTheory.T.finite_projection_pushforward : FiniteGermProjectionOpenAt.Statement → IrreducibleGermPrimitiveForm.Statement → PrimitiveFormSheetedOffDiscriminant.Statement → UnbranchedProperCountConstant.Statement → ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), IsAnalyticNear Y w → GermIrreducibleAt Y w → (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) → (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0) → ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N := by
  first | exact @GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover | exact GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover | (intros; apply GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover <;> assumption)
end
