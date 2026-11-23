module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

noncomputable section

open MeasureTheory intervalIntegral

namespace PositivityTheory.Rg.Sw.Glob.DerOneAbsH

theorem integral_deriv_zero {X Ξ : Type*} [MeasurableSpace X] [Countable Ξ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (m : Measure X) [SFinite m] (F F' : X → ℝ → Ξ → ℂ)
    (hd : ∀ x ξ, ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s => F x s ξ) (F' x t ξ) t)
    (hcont : ∀ x ξ, Continuous fun t => F' x t ξ)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun p : X × ℝ => F' p.1 p.2 ξ) (m.prod (volume.restrict (Set.Ioc 0 1))))
    (hfin : ∫⁻ p : X × ℝ, ∑' ξ, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod (volume.restrict (Set.Ioc 0 1))) ≠ ⊤)
    (hsum0 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 0 ξ‖) (hsum1 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 1 ξ‖)
    (hint0 : Integrable (fun x => ∑' ξ, F x 0 ξ) m) (hint1 : Integrable (fun x => ∑' ξ, F x 1 ξ) m)
    (hends : ∫ x, ∑' ξ, F x 1 ξ ∂m = ∫ x, ∑' ξ, F x 0 ξ ∂m)
    (hconst : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∫ x, ∑' ξ, F' x t ξ ∂m = ∫ x, ∑' ξ, F' x 0 ξ ∂m) :
    ∫ x, ∑' ξ, F' x 0 ξ ∂m = 0 := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  have hae : ∀ ξ, AEMeasurable (fun p : X × ℝ => ‖F' p.1 p.2 ξ‖ₑ) (m.prod μ) := fun ξ => (hmeas ξ).enorm
  have hle : ∀ ξ, ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) ≤ ∫⁻ p, ∑' ξ, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) :=
    fun ξ => lintegral_mono fun p => ENNReal.le_tsum (f := fun ξ => ‖F' p.1 p.2 ξ‖ₑ) ξ
  have hI : ∀ ξ, Integrable (fun p : X × ℝ => F' p.1 p.2 ξ) (m.prod μ) := fun ξ =>
    ⟨hmeas ξ, lt_of_le_of_lt (hle ξ) hfin.lt_top⟩
  have htsum : ∑' ξ, ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) ≠ ⊤ := by
    rw [← lintegral_tsum hae]; exact hfin

  have hftc : ∀ x ξ, ∫ t, F' x t ξ ∂μ = F x 1 ξ - F x 0 ξ := by
    intro x ξ
    rw [hμ, ← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (hd x ξ) ((hcont x ξ).intervalIntegrable 0 1)

  have hswap : ∀ ξ, ∫ x, (∫ t, F' x t ξ ∂μ) ∂m = ∫ t, (∫ x, F' x t ξ ∂m) ∂μ := fun ξ =>
    integral_integral_swap (f := fun x t => F' x t ξ) (hI ξ)

  have hbx : ∑' ξ, ∫⁻ x, ‖∫ t, F' x t ξ ∂μ‖ₑ ∂m ≠ ⊤ := by
    refine ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum fun ξ => ?_)
    calc ∫⁻ x, ‖∫ t, F' x t ξ ∂μ‖ₑ ∂m ≤ ∫⁻ x, ∫⁻ t, ‖F' x t ξ‖ₑ ∂μ ∂m :=
          lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) := (lintegral_prod _ (hae ξ)).symm
  have hbt : ∑' ξ, ∫⁻ t, ‖∫ x, F' x t ξ ∂m‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum fun ξ => ?_)
    calc ∫⁻ t, ‖∫ x, F' x t ξ ∂m‖ₑ ∂μ ≤ ∫⁻ t, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ∂μ :=
          lintegral_mono fun t => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) := (lintegral_prod_symm _ (hae ξ)).symm
  have S1 : ∫ x, ∑' ξ, ∫ t, F' x t ξ ∂μ ∂m = ∑' ξ, ∫ x, ∫ t, F' x t ξ ∂μ ∂m :=
    integral_tsum (fun ξ => (hI ξ).integral_prod_left.aestronglyMeasurable) hbx
  have S2 : ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ = ∑' ξ, ∫ t, ∫ x, F' x t ξ ∂m ∂μ :=
    integral_tsum (fun ξ => (hI ξ).integral_prod_right.aestronglyMeasurable) hbt

  have hslice : ∀ᵐ t ∂μ, ∀ ξ, AEStronglyMeasurable (fun x => F' x t ξ) m := by
    rw [ae_all_iff]
    intro ξ
    exact ((hmeas ξ).prod_swap).prodMk_left
  have hfinT : ∀ᵐ t ∂μ, ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ≠ ⊤ := by
    have hmξ : ∀ ξ, AEMeasurable (fun t => ∫⁻ x, ‖F' x t ξ‖ₑ ∂m) μ := fun ξ => by
      simpa using ((hae ξ).prod_swap).lintegral_prod_right'
    have hm' : AEMeasurable (fun t => ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m) μ := AEMeasurable.tsum hmξ
    have : ∫⁻ t, ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ∂μ ≠ ⊤ := by
      rw [lintegral_tsum hmξ]
      refine ne_top_of_le_ne_top htsum (le_of_eq (tsum_congr fun ξ => ?_))
      exact (lintegral_prod_symm _ (hae ξ)).symm
    filter_upwards [ae_lt_top' hm' this] with t ht using ht.ne
  have S3 : ∀ᵐ t ∂μ, ∫ x, ∑' ξ, F' x t ξ ∂m = ∑' ξ, ∫ x, F' x t ξ ∂m := by
    filter_upwards [hslice, hfinT] with t h1 h2 using integral_tsum h1 h2
  have hIoc : ∀ᵐ t ∂μ, t ∈ Set.Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc

  set c := ∫ x, ∑' ξ, F' x 0 ξ ∂m with hc
  have hμ1 : μ Set.univ = 1 := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Ioc]; simp
  have key : c = ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ := by
    have : ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ = ∫ _t, c ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [S3, hIoc] with t h1 h2
      rw [← h1, hconst t h2]
    rw [this, MeasureTheory.integral_const, Measure.real, hμ1, ENNReal.toReal_one, one_smul]
  have hsub : ∀ᵐ x ∂m, ∑' ξ, ∫ t, F' x t ξ ∂μ = ∑' ξ, F x 1 ξ - ∑' ξ, F x 0 ξ := by
    filter_upwards [hsum0, hsum1] with x h0 h1
    simp only [hftc]
    exact (h1.of_norm).tsum_sub h0.of_norm
  calc c = ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ := key
    _ = ∑' ξ, ∫ t, ∫ x, F' x t ξ ∂m ∂μ := S2
    _ = ∑' ξ, ∫ x, ∫ t, F' x t ξ ∂μ ∂m := tsum_congr fun ξ => (hswap ξ).symm
    _ = ∫ x, ∑' ξ, ∫ t, F' x t ξ ∂μ ∂m := S1.symm
    _ = ∫ x, (∑' ξ, F x 1 ξ - ∑' ξ, F x 0 ξ) ∂m := integral_congr_ae hsub
    _ = ∫ x, ∑' ξ, F x 1 ξ ∂m - ∫ x, ∑' ξ, F x 0 ξ ∂m := integral_sub hint1 hint0
    _ = 0 := by rw [hends, sub_self]

end PositivityTheory.Rg.Sw.Glob.DerOneAbsH
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositivityTheory.Rg.Sw.Glob.Fib

variable {m n : ℕ} {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X]
  [BorelSpace X]

theorem fib_meas (μ : Measure X) [μ.IsAddRightInvariant] (π : X →+ (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) →+ X) (hπs : ∀ u, π (s u) = u) (g : X → ℝ≥0∞) (hg : Measurable g)
    (hgs : ∀ z u, g (z + s u) = g z)
    (hloc : ∀ K : Set (Fin m → Fin n → ℂ), IsCompact K → ∫⁻ z, K.indicator 1 (π z) * g z ∂μ ≠ ∞) :
    ∃ c : ℝ≥0, (μ.withDensity g).map π = c • (volume : Measure (Fin m → Fin n → ℂ)) := by
  set ν : Measure (Fin m → Fin n → ℂ) := (μ.withDensity g).map π with hν
  have hπm : Measurable π := hπ.measurable
  have hint : ∀ a : (Fin m → Fin n → ℂ) → ℝ≥0∞, Measurable a → ∫⁻ u, a u ∂ν = ∫⁻ z, a (π z) * g z ∂μ := by
    intro a ha
    rw [hν, lintegral_map ha hπm]
    have e := lintegral_withDensity_eq_lintegral_mul μ hg (ha.comp hπm)
    simp only [Function.comp_def] at e
    rw [e]
    congr 1; ext z; simp [mul_comm]
  have hinv : ν.IsAddLeftInvariant := by
    refine ⟨fun u => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add u) hA, ← lintegral_indicator_one (measurable_const_add u hA),
      ← lintegral_indicator_one hA, hint _ (measurable_one.indicator (measurable_const_add u hA)),
      hint _ (measurable_one.indicator hA)]
    have key : ∀ z, ((fun x => u + x) ⁻¹' A).indicator 1 (π z) * g z =
        (fun z => A.indicator 1 (π z) * g z) (z + s u) := by
      intro z
      simp only [map_add (f := _), hπs, hgs]
      congr 1
      by_cases h : u + π z ∈ A
      · simp [Set.indicator, h, add_comm]
      · simp [Set.indicator, h, add_comm]
    simp_rw [key]
    exact lintegral_add_right_eq_self (fun z => A.indicator 1 (π z) * g z) (s u)
  have hfc : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [← lintegral_indicator_one hK.measurableSet, hint _ (measurable_one.indicator hK.measurableSet)]
    exact (hloc K hK).lt_top
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact ⟨Measure.addHaarScalarFactor ν volume, Measure.isAddLeftInvariant_eq_smul ν volume⟩

end PositivityTheory.Rg.Sw.Glob.Fib
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositivityTheory.Rg.Sw.Glob.LocCellT

variable {m n : ℕ} {X : Type*} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [IsTopologicalAddGroup X]

theorem tauFact_nonneg (μ : Measure X) [μ.IsAddRightInvariant] (π : X → (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) → X) (hπs : ∀ x u, π (x + s u) = π x + u) (g : X → ℝ≥0) (hgm : Measurable g)
    (hg : ∀ x u, g (x + s u) = g x) (ρ : (Fin m → Fin n → ℂ) → ℝ) (hρ : Continuous ρ) (hρpos : ∀ u, 0 < ρ u)
    (hint : ∫⁻ z, ENNReal.ofReal (ρ (π z)) * g z ∂μ < ∞) :
    ∃ c : ℝ≥0, ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a →
      ∫ z, a (π z) * (g z : ℂ) ∂μ = (c : ℂ) * ∫ u, a u := by
  have hπm : Measurable π := hπ.measurable
  set ν : Measure (Fin m → Fin n → ℂ) := (μ.withDensity fun z => (g z : ℝ≥0∞)).map π with hν
  have hlin : ∀ F : (Fin m → Fin n → ℂ) → ℝ≥0∞, Measurable F → ∫⁻ u, F u ∂ν = ∫⁻ z, (g z : ℝ≥0∞) * F (π z) ∂μ := by
    intro F hF
    rw [hν, lintegral_map hF hπm]
    change ∫⁻ a, (F ∘ π) a ∂(μ.withDensity fun z => (g z : ℝ≥0∞)) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ hgm.coe_nnreal_ennreal (hF.comp hπm)]
    rfl
  have hshift : ∀ (F : (Fin m → Fin n → ℂ) → ℝ≥0∞), Measurable F → ∀ u,
      ∫⁻ z, (g z : ℝ≥0∞) * F (π z + u) ∂μ = ∫⁻ z, (g z : ℝ≥0∞) * F (π z) ∂μ := by
    intro F hF u
    have h := lintegral_add_right_eq_self (μ := μ) (fun z => (g z : ℝ≥0∞) * F (π z)) (s u)
    simpa only [hπs, hg] using h
  have : ν.IsAddLeftInvariant := by
    refine ⟨fun u => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add u) hA, ← lintegral_indicator_one (measurable_const_add u hA),
      ← lintegral_indicator_one hA, hlin _ (measurable_one.indicator (measurable_const_add u hA)),
      hlin _ (measurable_one.indicator hA)]
    have e : ∀ z, ((fun v => u + v) ⁻¹' A).indicator (1 : (Fin m → Fin n → ℂ) → ℝ≥0∞) (π z) =
        A.indicator 1 (π z + u) := by
      intro z
      by_cases h : π z + u ∈ A
      · have h' : u + π z ∈ A := by rwa [add_comm]
        simp [Set.indicator, h, h']
      · have h' : u + π z ∉ A := by rwa [add_comm]
        simp [Set.indicator, h, h']
    simp_rw [e]
    exact hshift _ (measurable_one.indicator hA) u
  have : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rcases K.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨u0, hu0, hmin⟩ := hK.exists_isMinOn hne hρ.continuousOn
    have hr : 0 < ρ u0 := hρpos u0
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [← lintegral_indicator_one hKm, hlin _ (measurable_one.indicator hKm)]
    calc ∫⁻ z, (g z : ℝ≥0∞) * K.indicator 1 (π z) ∂μ
        ≤ ∫⁻ z, (ENNReal.ofReal (ρ u0))⁻¹ * (ENNReal.ofReal (ρ (π z)) * g z) ∂μ := by
          refine lintegral_mono fun z => ?_
          by_cases hz : π z ∈ K
          · have h0 : ENNReal.ofReal (ρ u0) ≠ 0 := by simp [hr]
            have h1 : (1 : ℝ≥0∞) ≤ (ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ (π z)) :=
              calc (1 : ℝ≥0∞) = (ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ u0) :=
                    (ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top).symm
                _ ≤ (ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ (π z)) :=
                    by gcongr; exact hmin hz
            calc (g z : ℝ≥0∞) * K.indicator 1 (π z) = (g z : ℝ≥0∞) * 1 := by
                  rw [Set.indicator_of_mem hz, Pi.one_apply]
              _ ≤ (g z : ℝ≥0∞) * ((ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ (π z))) := by gcongr
              _ = (ENNReal.ofReal (ρ u0))⁻¹ * (ENNReal.ofReal (ρ (π z)) * g z) := by ring
          · simp [Set.indicator_of_notMem hz]
      _ = (ENNReal.ofReal (ρ u0))⁻¹ * ∫⁻ z, ENNReal.ofReal (ρ (π z)) * g z ∂μ := by
          rw [lintegral_const_mul']
          simp [hr]
      _ < ∞ := ENNReal.mul_lt_top (by simp [hr]) hint
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν = c • (volume : Measure (Fin m → Fin n → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  refine ⟨c, fun a ha => ?_⟩
  have h1 : ∫ u, a u ∂ν = ∫ z, a (π z) * (g z : ℂ) ∂μ := by
    rw [hν, integral_map hπm.aemeasurable ha.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hgm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [NNReal.smul_def, Complex.real_smul, mul_comm]
  rw [← h1, hc, integral_smul_nnreal_measure]
  simp [NNReal.smul_def, Complex.real_smul]

theorem tauFact (μ : Measure X) [μ.IsAddRightInvariant] (π : X → (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) → X) (hπs : ∀ x u, π (x + s u) = π x + u) (B : X → ℂ) (hBm : Measurable B)
    (hB : ∀ x u, B (x + s u) = B x) (ρ : (Fin m → Fin n → ℂ) → ℝ) (hρ : Continuous ρ) (hρpos : ∀ u, 0 < ρ u)
    (hint : Integrable (fun z => ρ (π z) * ‖B z‖) μ) :
    ∃ κ : ℂ, ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a → (∃ C, ∀ u, ‖a u‖ ≤ C * ρ u) →
      ∫ z, a (π z) * B z ∂μ = κ * ∫ u, a u := by
  have hπm : Measurable π := hπ.measurable
  let gs : Fin 4 → X → ℝ≥0 := ![fun z => Real.toNNReal (B z).re, fun z => Real.toNNReal (-(B z).re),
    fun z => Real.toNNReal (B z).im, fun z => Real.toNNReal (-(B z).im)]
  have hgm : ∀ j, Measurable (gs j) := by
    intro j
    fin_cases j
    exacts [(Complex.measurable_re.comp hBm).real_toNNReal, (Complex.measurable_re.comp hBm).neg.real_toNNReal,
      (Complex.measurable_im.comp hBm).real_toNNReal, (Complex.measurable_im.comp hBm).neg.real_toNNReal]
  have hgi : ∀ j x u, gs j (x + s u) = gs j x := by
    intro j x u
    fin_cases j <;> simp [gs, hB]
  have hgle : ∀ j z, ((gs j z : ℝ≥0) : ℝ) ≤ ‖B z‖ := by
    intro j z
    have h1 := Complex.abs_re_le_norm (B z)
    have h2 := Complex.abs_im_le_norm (B z)
    fin_cases j <;> simp only [gs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Real.coe_toNNReal', Fin.mk_one, Fin.reduceFinMk] <;>
      first
      | exact max_le (le_trans (le_abs_self _) h1) (norm_nonneg _)
      | exact max_le (le_trans (neg_le_abs _) h1) (norm_nonneg _)
      | exact max_le (le_trans (le_abs_self _) h2) (norm_nonneg _)
      | exact max_le (le_trans (neg_le_abs _) h2) (norm_nonneg _)
  have hfin : ∀ j, ∫⁻ z, ENNReal.ofReal (ρ (π z)) * gs j z ∂μ < ∞ := by
    intro j
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hint.lintegral_lt_top
    rw [show ((gs j z : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (gs j z) from (ENNReal.ofReal_coe_nnreal).symm,
      ← ENNReal.ofReal_mul (hρpos _).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hgle j z) (hρpos _).le)
  choose c hc using fun j => tauFact_nonneg μ π hπ s hπs (gs j) (hgm j) (hgi j) ρ hρ hρpos (hfin j)
  have hdec : ∀ z, B z = ((gs 0 z : ℝ) : ℂ) - ((gs 1 z : ℝ) : ℂ) + Complex.I * (((gs 2 z : ℝ) : ℂ) - ((gs 3 z : ℝ) : ℂ)) := by
    intro z
    apply Complex.ext <;> simp [gs, Real.coe_toNNReal', max_def] <;> split_ifs <;> linarith
  refine ⟨(c 0 : ℂ) - c 1 + Complex.I * ((c 2 : ℂ) - c 3), fun a ha ⟨C, hC⟩ => ?_⟩
  have hint' : ∀ j, Integrable (fun z => a (π z) * ((gs j z : ℝ≥0) : ℂ)) μ := by
    intro j
    refine Integrable.mono' (hint.const_mul C) ((ha.comp hπm).mul (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have hC0 : 0 ≤ C := by
      by_contra h
      have := hC (π z)
      nlinarith [norm_nonneg (a (π z)), hρpos (π z)]
    rw [norm_mul]
    calc ‖a (π z)‖ * ‖((gs j z : ℝ≥0) : ℂ)‖ ≤ (C * ρ (π z)) * ‖B z‖ := by
          refine mul_le_mul (hC _) ?_ (norm_nonneg _) (mul_nonneg hC0 (hρpos _).le)
          rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
          exact hgle j z
      _ = C * (ρ (π z) * ‖B z‖) := by ring
  have e : (fun z => a (π z) * B z) = fun z => (a (π z) * ((gs 0 z : ℝ≥0) : ℂ) - a (π z) * ((gs 1 z : ℝ≥0) : ℂ)) +
      Complex.I * (a (π z) * ((gs 2 z : ℝ≥0) : ℂ) - a (π z) * ((gs 3 z : ℝ≥0) : ℂ)) := by
    funext z
    rw [hdec z]
    ring
  have i01 : Integrable (fun z => a (π z) * ((gs 0 z : ℝ≥0) : ℂ) - a (π z) * ((gs 1 z : ℝ≥0) : ℂ)) μ :=
    (hint' 0).sub (hint' 1)
  have i23 : Integrable (fun z => Complex.I * (a (π z) * ((gs 2 z : ℝ≥0) : ℂ) - a (π z) * ((gs 3 z : ℝ≥0) : ℂ))) μ :=
    ((hint' 2).sub (hint' 3)).const_mul Complex.I
  rw [e, integral_add i01 i23, integral_const_mul, integral_sub (hint' 0) (hint' 1), integral_sub (hint' 2) (hint' 3)]
  have k : ∀ j, ∫ z, a (π z) * ((gs j z : ℝ≥0) : ℂ) ∂μ = (c j : ℂ) * ∫ u, a u := by
    intro j
    have := hc j a ha
    simpa using this
  rw [k 0, k 1, k 2, k 3]
  ring

end PositivityTheory.Rg.Sw.Glob.LocCellT
end
end

section

noncomputable section

open Complex

namespace PositivityTheory.Rg.Sw.Glob.VacE

theorem coord_gamma (c t σ co si : ℝ) (hc : 0 < c) (ht : t ^ 2 = c ^ 2) (hσ : σ ^ 2 = 1) (hco : 0 < co)
    (hs : si ^ 2 + co ^ 2 = 1) :
    (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 /
        (((-t : ℝ) : ℂ) ^ 2 * (σ : ℂ) ^ 2 / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2) - I * t * σ * ((si * co : ℝ) : ℂ)) -
      I * t * σ * ((si / co : ℝ) : ℂ) = c := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hco' : (co : ℂ) ≠ 0 := by exact_mod_cast hco.ne'
  have htC : (t : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast ht
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hs2 : (si : ℂ) ^ 2 + (co : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have hden : (c : ℂ) * co - I * t * σ * si ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    rcases this with h | h
    · exact hc.ne' h
    · exact hco.ne' h
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div]
  rw [neg_sq, htC, hσC]
  have e1 : (c : ℂ) ^ 2 * 1 / ((c : ℂ) * ((co : ℂ))⁻¹ ^ 2) - I * t * σ * (si * co) = co * ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [e1]
  field_simp
  have htσ : (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 = (c : ℂ) ^ 2 := by rw [htC, hσC, mul_one]
  linear_combination (-(c : ℂ) ^ 2) * hs2 + (si : ℂ) ^ 2 * I ^ 2 * htσ + (si : ℂ) ^ 2 * (c : ℂ) ^ 2 * Complex.I_sq

theorem coord_const (c t σ co si : ℝ) (hc : 0 < c) (ht : t ^ 2 = c ^ 2) (hσ : σ ^ 2 = 1) (hco : 0 < co)
    (hs : si ^ 2 + co ^ 2 = 1) :
    ((co⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2)) *
        ((Real.pi : ℂ) / (((-t : ℝ) : ℂ) ^ 2 * (σ : ℂ) ^ 2 / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2) -
          I * t * σ * ((si * co : ℝ) : ℂ))) * (((|t| / Real.pi : ℝ) : ℂ)) ^ 2 =
      co + I * (σ * t / c) * si := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hco' : (co : ℂ) ≠ 0 := by exact_mod_cast hco.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htC : (t : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast ht
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hs2 : (si : ℂ) ^ 2 + (co : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have habs : ((|t| : ℝ) : ℂ) ^ 2 = (c : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs]; exact_mod_cast ht
  have hden : (c : ℂ) * co - I * t * σ * si ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    rcases this with h | h
    · exact hc.ne' h
    · exact hco.ne' h
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div]
  rw [neg_sq, htC, hσC, div_pow, habs]
  have e1 : (c : ℂ) ^ 2 * 1 / ((c : ℂ) * ((co : ℂ))⁻¹ ^ 2) - I * t * σ * (si * co) = co * ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [e1]
  have key : (co : ℂ)⁻¹ * ((Real.pi : ℂ) / ((c : ℂ) * (co : ℂ)⁻¹ ^ 2)) *
      ((Real.pi : ℂ) / (co * ((c : ℂ) * co - I * t * σ * si))) * ((c : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2) =
      (c : ℂ) / ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [key, div_eq_iff hden]
  have htσ : (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 = (c : ℂ) ^ 2 := by rw [htC, hσC, mul_one]
  field_simp
  linear_combination (-(c : ℂ) ^ 2) * hs2 + (si : ℂ) ^ 2 * I ^ 2 * htσ + (si : ℂ) ^ 2 * (c : ℂ) ^ 2 * Complex.I_sq

end PositivityTheory.Rg.Sw.Glob.VacE
end
end
