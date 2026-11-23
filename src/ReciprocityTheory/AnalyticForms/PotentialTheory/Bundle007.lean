module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Norm.Transitivity
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isClosed_of_isAnalyticSubset (A : FinHolAtlas e X) {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x (hx : x ∉ S)
  obtain ⟨W, hWo, hxW, r, f, hf, hSW⟩ := hS x
  obtain ⟨j, hj⟩ := A.cover x
  have hxz : ¬ ∀ i, f i x = 0 := by
    intro hz
    have hmem : x ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hxW, hz⟩
    exact hx hmem.1
  push_neg at hxz
  obtain ⟨i, hi⟩ := hxz
  have hcont : ContinuousAt (f i) x := by
    have hxt : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
      refine ⟨(A.chart j).map_source hj, ?_⟩
      show (A.chart j).symm (A.chart j x) ∈ W
      rw [(A.chart j).left_inv hj]
      exact hxW
    have h1 : ContinuousAt (f i ∘ (A.chart j).symm) (A.chart j x) := (hf i j _ hxt).continuousAt
    have h3 := h1.comp ((A.chart j).continuousAt hj)
    refine h3.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy]
  filter_upwards [hcont.eventually_ne hi, hWo.mem_nhds hxW] with y hy hyW
  intro hyS
  have hmem : y ∈ S ∩ W := ⟨hyS, hyW⟩
  rw [hSW] at hmem
  exact hy (hmem.2 i)

theorem degree_det_restrictScalars (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    (L.restrictScalars ℝ).det =
      ‖LinearMap.det (L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  have h1 : (L.restrictScalars ℝ).det =
      LinearMap.det ((L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).restrictScalars ℝ) := rfl
  rw [h1, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

theorem degree_sheet_chart_data {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V) :
    MeasurableSet ((B.chart j) '' W) ∧
    (A.chart k ∘ h ∘ (B.chart j).symm) '' ((B.chart j) '' W) = (A.chart k) '' V ∧
    Set.InjOn (A.chart k ∘ h ∘ (B.chart j).symm) ((B.chart j) '' W) ∧
    (∀ y ∈ (B.chart j) '' W, HasFDerivWithinAt (A.chart k ∘ h ∘ (B.chart j).symm)
      ((fderiv ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y).restrictScalars ℝ) ((B.chart j) '' W) y) ∧
    (∀ y ∈ (B.chart j) '' W, h ((B.chart j).symm y) ∈ (A.chart k).source) := by
  have hWsrc : ∀ y ∈ (B.chart j) '' W, (B.chart j).symm y ∈ W ∧ y ∈ (B.chart j).target := by
    rintro y ⟨w, hw, rfl⟩
    refine ⟨?_, (B.chart j).map_source (hWj hw)⟩
    rw [(B.chart j).left_inv (hWj hw)]
    exact hw
  have hsrc : ∀ y ∈ (B.chart j) '' W, h ((B.chart j).symm y) ∈ (A.chart k).source :=
    fun y hy => hVk (hbij.mapsTo (hWsrc y hy).1)
  refine ⟨?_, ?_, ?_, ?_, hsrc⟩
  · exact ((B.chart j).isOpen_image_of_subset_source hW hWj).measurableSet
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h ((B.chart j).symm y), hbij.mapsTo (hWsrc y hy).1, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hbij.surjOn hv
      refine ⟨B.chart j w, ⟨w, hw, rfl⟩, ?_⟩
      simp only [Function.comp_apply, (B.chart j).left_inv (hWj hw)]
  · rintro y₁ ⟨w₁, hw₁, rfl⟩ y₂ ⟨w₂, hw₂, rfl⟩ heq
    simp only [Function.comp_apply, (B.chart j).left_inv (hWj hw₁),
      (B.chart j).left_inv (hWj hw₂)] at heq
    have hww := hbij.injOn hw₁ hw₂
      ((A.chart k).injOn (hVk (hbij.mapsTo hw₁)) (hVk (hbij.mapsTo hw₂)) heq)
    rw [hww]
  · intro y hy
    have ha : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y :=
      hh.2 j k y ⟨(hWsrc y hy).2, hsrc y hy⟩
    exact (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

theorem sheet_integral {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V)
    (f : X → ℝ) :
    (IntegrableOn (fun y => f (h ((B.chart j).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) j y) ((B.chart j) '' W) ↔
      IntegrableOn (fun z => f ((A.chart k).symm z) * locDens A Φ k z) ((A.chart k) '' V)) ∧
    ∫ y in (B.chart j) '' W, f (h ((B.chart j).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) j y =
      ∫ z in (A.chart k) '' V, f ((A.chart k).symm z) * locDens A Φ k z := by
  obtain ⟨hU, himg, hinj, hder, hsrc⟩ := degree_sheet_chart_data hh j k hW hWj hVk hbij
  set φ := A.chart k ∘ h ∘ (B.chart j).symm with hφ
  set G : (Fin e → ℂ) → ℝ := fun z => f ((A.chart k).symm z) * locDens A Φ k z with hG
  have heq : Set.EqOn (fun y => f (h ((B.chart j).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) j y)
      (fun y => |((fderiv ℂ φ y).restrictScalars ℝ).det| • G (φ y)) ((B.chart j) '' W) := by
    intro y hy
    have hyT : y ∈ (B.chart j).target := by
      obtain ⟨w, hw, rfl⟩ := hy
      exact (B.chart j).map_source (hWj hw)
    simp only [hG, hφ, smul_eq_mul, degree_det_restrictScalars, Function.comp_apply,
      (A.chart k).left_inv (hsrc y hy)]
    rw [locDensPullback A B h hh Φ hΦ j k y hyT (hsrc y hy)]
    simp only [abs_pow, abs_norm]
    ring
  refine ⟨?_, ?_⟩
  · rw [integrableOn_congr_fun heq hU, ← himg,
      integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU hder hinj G]
  · rw [setIntegral_congr_fun hU heq, ← himg,
      integral_image_eq_integral_abs_det_fderiv_smul volume hU hder hinj G]

theorem sheet_lintegral {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V)
    (f : X → ENNReal) :
    ∫⁻ y in (B.chart j) '' W, f (h ((B.chart j).symm y)) *
        ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j y| =
      ∫⁻ z in (A.chart k) '' V, f ((A.chart k).symm z) * ENNReal.ofReal |locDens A Φ k z| := by
  obtain ⟨hU, himg, hinj, hder, hsrc⟩ := degree_sheet_chart_data hh j k hW hWj hVk hbij
  set φ := A.chart k ∘ h ∘ (B.chart j).symm with hφ
  rw [← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU hder hinj]
  refine setLIntegral_congr_fun hU fun y hy => ?_
  have hyT : y ∈ (B.chart j).target := by
    obtain ⟨w, hw, rfl⟩ := hy
    exact (B.chart j).map_source (hWj hw)
  simp only [hφ, degree_det_restrictScalars, Function.comp_apply,
    (A.chart k).left_inv (hsrc y hy)]
  rw [locDensPullback A B h hh Φ hΦ j k y hyT (hsrc y hy)]
  simp only [abs_mul, abs_pow, abs_norm]
  rw [ENNReal.ofReal_mul (abs_nonneg _)]
  ring

end

end ReciprocityTheory.AnForm.M
end

section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]

def chartPartMeasure (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (s : ℝ) (j : Fin A.n) : Measure X :=
  ((volume.restrict (A.chart j).target).withDensity fun y =>
    ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))).map (A.chart j).symm

theorem chart_weight_compact [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (j : Fin A.n) :
    IsCompact ((A.chart j) '' tsupport (P.χ j)) ∧
      (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target ∧
      ∀ y ∈ (A.chart j).target, y ∉ (A.chart j) '' tsupport (P.χ j) →
        P.χ j ((A.chart j).symm y) = 0 := by
  have hK : IsCompact (tsupport (P.χ j)) := (isClosed_tsupport _).isCompact
  have hsrc := P.tsupport_subset j
  refine ⟨hK.image_of_continuousOn ((A.chart j).continuousOn.mono hsrc), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (hsrc hx)
  · intro y hy hy'
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hy' ⟨_, h, (A.chart j).right_inv hy⟩

private theorem chiCont (A : FinHolAtlas e X) (P : ChartPartition A) (j : Fin A.n) :
    ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
  have h := ((P.smooth j) j).continuousOn
  rw [Set.preimage_univ, Set.inter_univ] at h
  exact h

theorem isFiniteMeasure_chartPartMeasure [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) :
    IsFiniteMeasure (chartPartMeasure A P Φ s j) := by
  obtain ⟨hC, hCT, hz⟩ := chart_weight_compact A P Φ j
  have hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target :=
    continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))
  have hi : IntegrableOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target := by
    refine IntegrableOn.of_forall_diff_eq_zero ((hw.mono hCT).integrableOn_compact hC)
      (A.chart j).open_target.measurableSet ?_
    intro y hy
    simp [hz y hy.1 hy.2]
  unfold chartPartMeasure
  haveI : IsFiniteMeasure ((volume.restrict (A.chart j).target).withDensity fun y =>
      ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    isFiniteMeasure_withDensity_ofReal hi.2
  infer_instance

private theorem integrableOn_part [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ) (hg : Measurable g)
    (hgi : MIntegrable A Φ g) :
    IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) (A.chart j).target := by
  obtain ⟨hC, hCT, hz⟩ := chart_weight_compact A P Φ j
  have hL := hgi j _ hCT hC
  have hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target :=
    continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))
  have hcont : ContinuousOn (fun y => max (s * (P.χ j ((A.chart j).symm y) *
      locDens A Φ j y)) 0) (A.chart j).target :=
    fun y hy => (hw y hy).max continuousWithinAt_const
  have hsymm : AEMeasurable (fun y => g ((A.chart j).symm y)) (volume.restrict
      ((A.chart j) '' tsupport (P.χ j))) :=
    hg.comp_aemeasurable (((A.chart j).continuousOn_symm.mono hCT).aemeasurable hC.measurableSet)
  have hχ1 : ∀ x, P.χ j x ≤ 1 := fun x => by
    rw [← P.sum_eq_one x]
    exact Finset.single_le_sum (fun k _ => P.nonneg k x) (Finset.mem_univ j)
  have hCi : IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0)
      ((A.chart j) '' tsupport (P.χ j)) := by
    refine (hL.norm.const_mul |s|).mono'
      (hsymm.mul ((hcont.mono hCT).aemeasurable hC.measurableSet)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 := P.nonneg j ((A.chart j).symm y)
    have h1 := hχ1 ((A.chart j).symm y)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    have hm : |max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0| ≤
        |s| * |locDens A Φ j y| := by
      rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      calc s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)
          ≤ |s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)| := le_abs_self _
        _ = |s| * (P.χ j ((A.chart j).symm y) * |locDens A Φ j y|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0]
        _ ≤ |s| * (1 * |locDens A Φ j y|) := by gcongr
        _ = |s| * |locDens A Φ j y| := by ring
    calc |g ((A.chart j).symm y)| * |max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0|
        ≤ |g ((A.chart j).symm y)| * (|s| * |locDens A Φ j y|) := by gcongr
      _ = |s| * (|g ((A.chart j).symm y)| * |locDens A Φ j y|) := by ring
  refine IntegrableOn.of_forall_diff_eq_zero hCi (A.chart j).open_target.measurableSet ?_
  intro y hy
  simp [hz y hy.1 hy.2]

theorem integral_chartPartMeasure [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ) (hg : Measurable g)
    (hgi : MIntegrable A Φ g) :
    Integrable g (chartPartMeasure A P Φ s j) ∧
      ∫ x, g x ∂chartPartMeasure A P Φ s j =
        ∫ y in (A.chart j).target, g ((A.chart j).symm y) *
          max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0 := by
  have hT := (A.chart j).open_target.measurableSet
  have hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target :=
    continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))
  have hf : AEMeasurable (fun y => (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)).toNNReal)
      (volume.restrict (A.chart j).target) := (hw.aemeasurable hT).real_toNNReal
  have hsy : AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    ((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac (withDensity_absolutelyContinuous _ _)
  have hgm : AEStronglyMeasurable g (chartPartMeasure A P Φ s j) := hg.aestronglyMeasurable
  have hpart := integrableOn_part A P Φ hΦ s j g hg hgi
  unfold chartPartMeasure at hgm ⊢
  constructor
  · rw [integrable_map_measure hgm hsy]
    refine (integrable_withDensity_iff_integrable_smul₀ hf).2 ?_
    refine hpart.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']
    ring
  · rw [integral_map hsy hgm]
    refine (integral_withDensity_eq_integral_smul₀ hf (fun y => g ((A.chart j).symm y))).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']
    ring

end

end ReciprocityTheory.AnForm.M
end
