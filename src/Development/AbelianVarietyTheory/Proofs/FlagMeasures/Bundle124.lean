module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

private theorem lintegral_eq_lintegral_weight_mul_lintegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hone : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (φ : G → ENNReal) (hφ : Measurable φ) :
    ∫⁻ y, φ y ∂μ = ∫⁻ y, β y * ∫⁻ m, φ (m * y) ∂ν ∂μ := by
  calc ∫⁻ y, φ y ∂μ = ∫⁻ y, (∫⁻ m, β (m⁻¹ * y) ∂ν) * φ y ∂μ := by
          simp only [hone, one_mul]
    _ = ∫⁻ y, ∫⁻ m, β (m⁻¹ * y) * φ y ∂ν ∂μ := by
          refine lintegral_congr (fun y => ?_)
          have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
          exact (lintegral_mul_const _ hb).symm
    _ = ∫⁻ m, ∫⁻ y, β (m⁻¹ * y) * φ y ∂μ ∂ν := by
          have hm : Measurable (fun p : G × G => β (p.2⁻¹ * p.1) * φ p.1) :=
            (hβ.comp (measurable_snd.inv.mul measurable_fst)).mul (hφ.comp measurable_fst)
          exact lintegral_lintegral_swap (f := fun y m => β (m⁻¹ * y) * φ y) hm.aemeasurable
    _ = ∫⁻ m, ∫⁻ y, β y * φ (m * y) ∂μ ∂ν := by
          refine lintegral_congr (fun m => ?_)
          have h := lintegral_mul_left_eq_self (μ := μ) (fun y => β (m⁻¹ * y) * φ y) m
          simp only [inv_mul_cancel_left] at h
          exact h.symm
    _ = ∫⁻ y, ∫⁻ m, β y * φ (m * y) ∂ν ∂μ := by
          have hm : Measurable (fun p : G × G => β p.2 * φ (p.1 * p.2)) :=
            (hβ.comp measurable_snd).mul (hφ.comp (measurable_fst.mul measurable_snd))
          exact lintegral_lintegral_swap (f := fun m y => β y * φ (m * y)) hm.aemeasurable
    _ = ∫⁻ y, β y * ∫⁻ m, φ (m * y) ∂ν ∂μ := by
          refine lintegral_congr (fun y => ?_)
          have hb : Measurable (fun m => φ (m * y)) := hφ.comp (measurable_mul_const y)
          exact lintegral_const_mul _ hb

private theorem integrable_and_integral_eq_of_lintegral_weight_one {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hfin : ∀ y, β y ≠ ⊤) (hone : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (g : G → ℂ) (hg : Measurable g) (hgi : Integrable g μ) :
    Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν) μ ∧
      ∫ y, g y ∂μ = ∫ y, ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν ∂μ := by
  have hkey := lintegral_eq_lintegral_weight_mul_lintegral μ ν β hβ hone
  have hgl : ∫⁻ y, ‖g y‖ₑ ∂μ < ⊤ := hgi.hasFiniteIntegral
  have hnorm : ∀ y (z : ℂ), ‖((β y).toReal : ℂ) * z‖ₑ = β y * ‖z‖ₑ := by
    intro y z
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin y)]
  have hHm : Measurable (fun p : G × G => ((β p.2).toReal : ℂ) * g (p.1 * p.2)) :=
    (Complex.measurable_ofReal.comp (hβ.comp measurable_snd).ennreal_toReal).mul
      (hg.comp (measurable_fst.mul measurable_snd))
  have hHi : Integrable (fun p : G × G => ((β p.2).toReal : ℂ) * g (p.1 * p.2)) (ν.prod μ) := by
    refine ⟨hHm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖((β p.2).toReal : ℂ) * g (p.1 * p.2)‖ₑ ∂(ν.prod μ) < ⊤
    rw [lintegral_prod_symm _ hHm.enorm.aemeasurable]
    simp only [hnorm]
    have h2 : ∀ y, ∫⁻ m, β y * ‖g (m * y)‖ₑ ∂ν = β y * ∫⁻ m, ‖g (m * y)‖ₑ ∂ν := fun y =>
      lintegral_const_mul _ (hg.enorm.comp (measurable_mul_const y))
    simp only [h2]
    rw [← hkey _ hg.enorm]
    exact hgl
  have heq : ∀ y, ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν = ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν :=
    fun y => integral_const_mul _ _
  have hint0 : Integrable (fun y => ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν) μ :=
    hHi.integral_prod_right
  have hint : Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν) μ :=
    hint0.congr (ae_of_all _ heq)
  refine ⟨hint, ?_⟩
  have hKm : Measurable (fun p : G × G => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2) :=
    (Complex.measurable_ofReal.comp
      (hβ.comp (measurable_fst.inv.mul measurable_snd)).ennreal_toReal).mul (hg.comp measurable_snd)
  have hKi : Integrable (fun p : G × G => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2) (ν.prod μ) := by
    refine ⟨hKm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2‖ₑ ∂(ν.prod μ) < ⊤
    rw [lintegral_prod_symm _ hKm.enorm.aemeasurable]
    simp only [hnorm]
    have h3 : ∀ y, ∫⁻ m, β (m⁻¹ * y) * ‖g y‖ₑ ∂ν = ‖g y‖ₑ := by
      intro y
      have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
      rw [lintegral_mul_const _ hb, hone, one_mul]
    simp only [h3]
    exact hgl
  have hβone : ∀ y, ∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν = 1 := by
    intro y
    have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
    rw [integral_complex_ofReal, integral_toReal hb.aemeasurable (ae_of_all _ fun m => (hfin _).lt_top),
      hone, ENNReal.toReal_one, Complex.ofReal_one]
  calc ∫ y, g y ∂μ = ∫ y, (∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν) * g y ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show g y = (∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν) * g y
        rw [hβone y, one_mul]
    _ = ∫ y, ∫ m, ((β (m⁻¹ * y)).toReal : ℂ) * g y ∂ν ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ m, ∫ y, ((β (m⁻¹ * y)).toReal : ℂ) * g y ∂μ ∂ν :=
        (integral_prod_symm _ hKi).symm.trans (integral_prod _ hKi)
    _ = ∫ m, ∫ y, ((β y).toReal : ℂ) * g (m * y) ∂μ ∂ν := by
        refine integral_congr_ae (ae_of_all _ fun m => ?_)
        have h := integral_mul_left_eq_self (μ := μ) (fun y => ((β (m⁻¹ * y)).toReal : ℂ) * g y) m
        simp only [inv_mul_cancel_left] at h
        exact h.symm
    _ = ∫ y, ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν ∂μ :=
        (integral_prod _ hHi).symm.trans (integral_prod_symm _ hHi)
    _ = ∫ y, ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν ∂μ :=
        integral_congr_ae (ae_of_all _ heq)

theorem weil_formula_cutoff : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (ν : Measure G), IsClosed (N : Set G) → IsHaarSub (N : Set G) ν → ∀ β : G → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → (∀ f : G → ENNReal, Measurable f → ∫⁻ y, f y ∂μ = ∫⁻ y, β y * ∫⁻ m, f (m * y) ∂ν ∂μ) ∧ ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν) μ ∧ ∫ y, f y ∂μ = ∫ y, ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν ∂μ := by
  intro G _ _ _ _ _ _ _ _ μ _ N ν _hN hH β hβ hfin hone
  have hH' := hH
  unfold IsHaarSub at hH'
  haveI : IsFiniteMeasureOnCompacts ν := hH'.2.1
  haveI : SigmaFinite ν := inferInstance
  have hkey := lintegral_eq_lintegral_weight_mul_lintegral μ ν β hβ hone
  refine ⟨hkey, fun f hf => ?_⟩
  have hgm : Measurable (hf.aestronglyMeasurable.mk f) :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[μ] hf.aestronglyMeasurable.mk f := hf.aestronglyMeasurable.ae_eq_mk
  obtain ⟨hgi, hgeq⟩ := integrable_and_integral_eq_of_lintegral_weight_one μ ν β hβ hfin hone _ hgm (hf.congr hfg)
  have hEm : MeasurableSet (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}) :=
    measurableSet_toMeasurable _ _
  have hE0 : μ (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}) = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp hfg
  have hsub : {y | f y ≠ hf.aestronglyMeasurable.mk f y} ⊆
      toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y} := subset_toMeasurable _ _
  have hind : Measurable ((toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
      (1 : G → ENNReal)) := measurable_one.indicator hEm
  have h0 := hkey _ hind
  rw [lintegral_indicator_one hEm, hE0] at h0
  have hIm : Measurable (fun y => β y * ∫⁻ m, (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
      (1 : G → ENNReal) (m * y) ∂ν) :=
    hβ.mul (hind.comp measurable_mul).lintegral_prod_left'
  have hae := (lintegral_eq_zero_iff' hIm.aemeasurable).mp h0.symm
  have hcong : (fun y => ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν) =ᵐ[μ]
      (fun y => ((β y).toReal : ℂ) * ∫ m, hf.aestronglyMeasurable.mk f (m * y) ∂ν) := by
    filter_upwards [hae] with y hy
    have hy' : β y * ∫⁻ m, (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
        (1 : G → ENNReal) (m * y) ∂ν = 0 := hy
    rcases mul_eq_zero.mp hy' with hb | hI
    · simp [hb]
    · congr 1
      have hmy : Measurable (fun m => (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
          (1 : G → ENNReal) (m * y)) := hind.comp (measurable_mul_const y)
      have hae2 := (lintegral_eq_zero_iff hmy).mp hI
      refine integral_congr_ae ?_
      filter_upwards [hae2] with m hm
      by_contra hne
      have hmE := hsub hne
      simp [Set.indicator_of_mem hmE] at hm
  refine ⟨hgi.congr hcong.symm, ?_⟩
  rw [integral_congr_ae hfg, hgeq, integral_congr_ae hcong]

end GlobalTheory
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem exists_measurable_cutoff_fibre_integral_one (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure G)
    (_hN : IsClosed (N : Set G)) (hν : IsHaarSub (N : Set G) ν) :
    ∃ β : G → ENNReal, Measurable β ∧ (∀ y, β y ≠ ⊤) ∧ ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1 := by
  classical
  obtain ⟨hne, hfin, hcompl, hinv⟩ := hν

  have hae : ∀ᵐ m ∂ν, m ∈ (N : Set G) := by
    rw [ae_iff]; exact hcompl

  have horb : ∀ (h : G → ENNReal) (a : G), a ∈ N → ∀ y,
      ∫⁻ z, h (z⁻¹ * (a⁻¹ * y)) ∂ν = ∫⁻ z, h (z⁻¹ * y) ∂ν := by
    intro h a ha y
    have hmap : ν.map (MeasurableEquiv.mulLeft a) = ν := hinv a ha
    calc ∫⁻ z, h (z⁻¹ * (a⁻¹ * y)) ∂ν
        = ∫⁻ z, h ((MeasurableEquiv.mulLeft a z)⁻¹ * y) ∂ν := by
          congr 1; ext z; simp [_root_.mul_inv_rev, mul_assoc]
      _ = ∫⁻ z, h (z⁻¹ * y) ∂(ν.map (MeasurableEquiv.mulLeft a)) :=
          (lintegral_map_equiv (fun z => h (z⁻¹ * y)) _).symm
      _ = ∫⁻ z, h (z⁻¹ * y) ∂ν := by rw [hmap]

  have hpos : ∀ O : Set G, IsOpen O → ∀ x ∈ O, x ∈ N → 0 < ν O := by
    intro O hO x hxO hxN
    rw [pos_iff_ne_zero]
    intro h0
    apply hne
    set U : G → Set G := fun n => (fun z => (x * n⁻¹) * z) ⁻¹' O with hU
    have hUo : ∀ n ∈ (N : Set G), IsOpen (U n) := fun n _ =>
      hO.preimage (continuous_const.mul continuous_id)
    have hU0 : ∀ n ∈ (N : Set G), ν (U n) = 0 := by
      intro n hn
      have hxn : x * n⁻¹ ∈ N := N.mul_mem hxN (N.inv_mem hn)
      have := hinv _ hxn
      rw [← this] at h0
      rwa [Measure.map_apply (measurable_const_mul _) hO.measurableSet] at h0
    obtain ⟨T, hTN, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable (N : Set G) U hUo
    have hNsub : (N : Set G) ⊆ ⋃ n ∈ T, U n := by
      rw [hTU]
      intro n hn
      exact Set.mem_biUnion hn (by simpa [hU, mul_assoc] using hxO)
    have hN0 : ν (N : Set G) = 0 :=
      measure_mono_null hNsub ((measure_biUnion_null_iff hTc).2 fun n hn => hU0 n (hTN hn))
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self (N : Set G)]
    exact measure_union_null hN0 hcompl

  let E := CompactExhaustion.choice G
  let F : ℕ → G → ENNReal := fun k y => ∫⁻ m, (E k).indicator 1 (m⁻¹ * y) ∂ν
  have hFm : ∀ k, Measurable (F k) := by
    intro k
    refine Measurable.lintegral_prod_right' (f := fun p : G × G => (E k).indicator 1 (p.2⁻¹ * p.1)) ?_
    exact (measurable_one.indicator (E.isCompact k).isClosed.measurableSet).comp
      (measurable_snd.inv.mul measurable_fst)
  have hFeq : ∀ k y, F k y = ν ((fun m => m⁻¹ * y) ⁻¹' E k) := by
    intro k y
    rw [← lintegral_indicator_one
      ((E.isCompact k).isClosed.measurableSet.preimage (measurable_inv.mul_const y))]
    rfl
  have hFtop : ∀ k y, F k y ≠ ⊤ := by
    intro k y
    rw [hFeq]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
      (((E.isCompact k).image (f := fun u : G => y * u⁻¹)
        (continuous_const.mul continuous_inv)).measure_lt_top (μ := ν)))
    intro m hm
    exact ⟨m⁻¹ * y, hm, by simp⟩
  have hFpos : ∀ y, ∃ k, 0 < F k y := by
    intro y
    obtain ⟨k, hk⟩ := E.exists_mem_nhds y
    refine ⟨k, ?_⟩
    rw [hFeq]
    refine lt_of_lt_of_le (hpos ((fun m => m⁻¹ * y) ⁻¹' interior (E k))
      (isOpen_interior.preimage (continuous_inv.mul continuous_const)) 1 ?_ N.one_mem)
      (measure_mono (Set.preimage_mono interior_subset))
    simpa [mem_interior_iff_mem_nhds] using hk
  have hFinv : ∀ k y, ∀ᵐ m ∂ν, F k (m⁻¹ * y) = F k y := by
    intro k y
    filter_upwards [hae] with m hm
    exact horb ((E k).indicator 1) m hm y

  let w : ℕ → G → ENNReal := fun k y => (2⁻¹ : ENNReal) ^ k * (E k).indicator 1 y * (1 + F k y)⁻¹
  have hwm : ∀ k, Measurable (w k) := fun k =>
    (measurable_const.mul (measurable_one.indicator (E.isCompact k).isClosed.measurableSet)).mul
      (measurable_const.add (hFm k)).inv
  let f : G → ENNReal := fun y => ∑' k, w k y
  have hfm : Measurable f := Measurable.tsum hwm
  let T : G → ENNReal := fun y => ∫⁻ m, f (m⁻¹ * y) ∂ν
  have hTm : Measurable T :=
    Measurable.lintegral_prod_right' (f := fun p : G × G => f (p.2⁻¹ * p.1))
      (hfm.comp (measurable_snd.inv.mul measurable_fst))
  have hTinv : ∀ y, ∀ᵐ m ∂ν, T (m⁻¹ * y) = T y := by
    intro y
    filter_upwards [hae] with m hm
    exact horb f m hm y
  have hTsum : ∀ y, T y = ∑' k, (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * F k y := by
    intro y
    show ∫⁻ m, ∑' k, w k (m⁻¹ * y) ∂ν = _
    rw [lintegral_tsum (f := fun k m => w k (m⁻¹ * y)) fun k => ((hwm k).comp (measurable_inv.mul_const y)).aemeasurable]
    congr 1; ext k
    calc ∫⁻ m, w k (m⁻¹ * y) ∂ν
        = ∫⁻ m, (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * (E k).indicator 1 (m⁻¹ * y) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hFinv k y] with m hm
          simp only [w, hm]
          ring
      _ = (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * F k y := by
          rw [lintegral_const_mul]
          exact (measurable_one.indicator (E.isCompact k).isClosed.measurableSet).comp
            (measurable_inv.mul_const y)
  have hgeom : ∑' k : ℕ, (2⁻¹ : ENNReal) ^ k ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    rw [ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hTtop : ∀ y, T y ≠ ⊤ := by
    intro y
    rw [hTsum]
    refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
    rw [mul_assoc]
    refine mul_le_of_le_one_right' ?_
    rw [mul_comm, ← div_eq_mul_inv]
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)
  have hT0 : ∀ y, T y ≠ 0 := by
    intro y
    obtain ⟨k, hk⟩ := hFpos y
    rw [hTsum]
    refine (lt_of_lt_of_le ?_ (ENNReal.le_tsum k)).ne'
    rw [mul_assoc, mul_comm ((1 + F k y)⁻¹), ← div_eq_mul_inv]
    refine ENNReal.mul_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)) ?_
    exact (ENNReal.div_pos_iff.2 ⟨hk.ne', ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hFtop k y⟩⟩).ne'
  have hfle : ∀ y, f y ≠ ⊤ := by
    intro y
    refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
    show (2⁻¹ : ENNReal) ^ k * (E k).indicator 1 y * (1 + F k y)⁻¹ ≤ _
    rw [mul_assoc]
    refine mul_le_of_le_one_right' ?_
    refine mul_le_one' ?_ (ENNReal.inv_le_one.2 le_self_add)
    by_cases hy : y ∈ E k <;> simp [hy]
  refine ⟨fun y => f y * (T y)⁻¹, hfm.mul hTm.inv, fun y => ?_, fun y => ?_⟩
  · exact ENNReal.mul_ne_top (hfle y) (ENNReal.inv_ne_top.2 (hT0 y))
  · calc ∫⁻ m, f (m⁻¹ * y) * (T (m⁻¹ * y))⁻¹ ∂ν
        = ∫⁻ m, f (m⁻¹ * y) * (T y)⁻¹ ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hTinv y] with m hm
          rw [hm]
      _ = T y * (T y)⁻¹ := lintegral_mul_const _ (hfm.comp (measurable_inv.mul_const y))
      _ = 1 := ENNReal.mul_inv_cancel (hT0 y) (hTtop y)

end GlobalTheory.Dec
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RadEmb

theorem hform_eq_dot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) A x y = star x ⬝ᵥ (A *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_frame {n : ℕ} {ε : Fin n → Bool} {A P : Matrix (Fin n) (Fin n) ℂ} (h : Pᴴ * A * P = Jm ε)
    (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) A (P *ᵥ x) (P *ᵥ y) = star (Formalism.QuantumDeterminants.herm (Jm ε) x y) := by
  have e : star x ⬝ᵥ (Jm ε *ᵥ y) = star (Formalism.QuantumDeterminants.herm (Jm ε) x y) := by
    simp only [Formalism.QuantumDeterminants.herm, Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [mul_comm]
  rw [← e, ← h, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

theorem inUnipRad_one (I : AutInst) {A : Type} [CommRing A] (s : A →+* A) (JA : Matrix (Fin I.n) (Fin I.n) A)
    (WA : Submodule A (Fin I.n → A)) : I.InUnipRad s JA WA 1 := by
  refine ⟨fun x _ => by simp, fun y _ => by simp, fun y x _ => by simp [Formalism.UG.hform]⟩

theorem span_isot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F) (hW : I.IsIsot W) :
    ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
    ∀ y ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x y = 0 := by
  have hφ : ∀ a, I.φ v (starRingEnd I.E a) = starRingEnd ℂ (I.φ v a) := fun a => I.cm.cmUnram.2.1 _ a
  intro x hx y hy
  rw [hform_eq_dot]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have := congrArg (I.φ v) (hW.2 a ha b hb)
      rw [← hform_eq_dot]

      simpa only [Formalism.UG.hform, map_sum, map_mul, hφ, map_zero, Matrix.map_apply] using this
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add, dotProduct_add, ha, hb, add_zero]
    | smul c a _ ha => rw [Matrix.mulVec_smul, dotProduct_smul, ha, smul_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
  | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]

theorem radical_embeds : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F), I.IsIsot W →
    ∃ Wv : Submodule ℂ (Fin I.n → ℂ), IsIsoC (I.ε v) Wv ∧
      ∀ m ∈ NW (I.ε v) Wv, (open Classical in ((Pi.mulSingle v m, 1) : I.GA)) ∈ I.NA W := by
  classical
  intro I W v hW
  have hP : ∀ u, I.P u * (I.P u)⁻¹ = 1 := fun u =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit u))
  have hQ : ∀ y, I.P v *ᵥ ((I.P v)⁻¹ *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  set WA := Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)) with hWA
  have hf := hform_frame (I.P_spec v)
  refine ⟨WA.comap (I.P v).mulVecLin, ⟨?_, fun x hx y hy => ?_⟩, fun m hm => ⟨fun u => ?_, ?_⟩⟩
  · intro h
    apply hW.1
    rw [eq_bot_iff]
    intro w hw
    have h1 : (I.P v)⁻¹ *ᵥ (fun i => I.φ v (w i)) ∈ WA.comap (I.P v).mulVecLin := by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hQ]
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    have h2 := hQ (fun i => I.φ v (w i))
    rw [h1, Matrix.mulVec_zero] at h2
    rw [Submodule.mem_bot]
    funext i
    exact (map_eq_zero (I.φ v)).1 (congrFun h2 i).symm
  · have := span_isot I W v hW _ hx _ hy
    simp only [Matrix.mulVecLin_apply] at this
    rw [hf] at this
    exact star_eq_zero.1 this
  · by_cases hu : u = v
    · subst hu
      simp only [Pi.mulSingle_eq_same]
      have e : ∀ y, (I.P u * uMat m * (I.P u)⁻¹ - 1) *ᵥ y = I.P u *ᵥ ((umat m - 1) *ᵥ ((I.P u)⁻¹ *ᵥ y)) := by
        intro y
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP]
      have mem : ∀ x ∈ WA, (I.P u)⁻¹ *ᵥ x ∈ WA.comap (I.P u).mulVecLin := fun x hx => by
        rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hQ]; exact hx
      refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩
      · rw [e, hm.1 _ (mem x hx), Matrix.mulVec_zero]
      · rw [e]
        refine hm.2.1 _ fun x hx => ?_
        have := hy _ hx
        rw [← hQ y, Matrix.mulVecLin_apply, hf] at this
        exact star_eq_zero.1 this
      · rw [e, ← hQ x, hf, hm.2.2 _ _ (mem x hx), star_zero]
    · have e : uMat ((Pi.mulSingle v m : I.Ginf) u) = 1 := by
        rw [Pi.mulSingle_eq_of_ne hu]; rfl
      simp only [e, Matrix.mul_one, hP]
      exact inUnipRad_one I _ _ _
  · exact inUnipRad_one I _ _ _

end GlobalTheory.RadEmb
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeConst

theorem gauge_exists_pos_unique :
    ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ IsGauge ε c ∧ ∀ c', IsGauge ε c' → c' = c :=
  GlobalTheory.GaugeConst.exists_unique_isGauge

end GlobalTheory.GaugeConst
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.lValEta_mem_Icc_two_pow_fDeg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ i : ℕ, 2 ≤ i → ((2 : ℝ) ^ (Formalism.HermitianLatticesTheory.fDeg K))⁻¹ ≤ Formalism.HermitianLatticesTheory.lValEta K i ∧ Formalism.HermitianLatticesTheory.lValEta K i ≤ 2 ^ (Formalism.HermitianLatticesTheory.fDeg K) := by
  first | exact @GlobalTheory.EtaValueBound.lValEta_bounds | exact GlobalTheory.EtaValueBound.lValEta_bounds | (intros; apply GlobalTheory.EtaValueBound.lValEta_bounds <;> assumption)
end
