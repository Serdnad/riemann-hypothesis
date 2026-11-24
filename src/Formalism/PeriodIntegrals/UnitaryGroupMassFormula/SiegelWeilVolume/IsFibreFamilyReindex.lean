module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibUniq
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibDis
import Aesop.Main
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ENatToNat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensGen, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.FibMeas0Holds, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.IsFibreFamilyReindex

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensGen =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensGen", "h": "module\n\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\nimport Aesop.Main\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.CompletePartialOrder\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PI.VolStabSW.DensGen

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}

theorem ae_fib (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X}
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (b : X) :
    ∀ᵐ v ∂(fib b), f' v = b := by
  have h := hfib.1 b
  rw [ae_iff]
  refine measure_mono_null ?_ h
  intro v hv hmem
  exact hv (hι (by rw [← hff' v]; exact hmem.1))

theorem fib_set_nonneg [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hρ0 : ∀ v, 0 ≤ ρ v) (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  classical
  obtain ⟨hint, hGc⟩ := hfib.2.2 ρ hρc hρs hρU
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hS'm : MeasurableSet (f' ⁻¹' S) := (hS.isClosed.preimage hf').measurableSet
  have hρm : Measurable fun v => ENNReal.ofReal (ρ v) := hρc.measurable.ennreal_ofReal
  have hmain : ∫⁻ v in f' ⁻¹' S, ENNReal.ofReal (ρ v) ∂μ =
      ∫⁻ b in S, ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b) ∂ν := by
    have key := hfib.2.1 ((f' ⁻¹' S).indicator fun v => ENNReal.ofReal (ρ v)) (hρm.indicator hS'm)
    have hsupp : Function.support ((f' ⁻¹' S).indicator fun v => ENNReal.ofReal (ρ v)) ⊆ U := by
      intro v hv
      apply hρU
      apply subset_tsupport
      intro h0
      apply hv
      simp [Set.indicator, h0]
    rw [setLIntegral_eq_of_support_subset hsupp, lintegral_indicator hS'm] at key
    rw [key, ← lintegral_indicator hSm]
    apply lintegral_congr
    intro b
    have hae := ae_fib hfib hff' hι b
    by_cases hb : b ∈ S
    · rw [Set.indicator_apply, if_pos hb]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with v hv
      have hv' : v ∈ f' ⁻¹' S := by
        show f' v ∈ S
        rw [hv]
        exact hb
      rw [Set.indicator_apply, if_pos hv']
    · rw [Set.indicator_apply, if_neg hb]
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [hae] with v hv
      have hv' : v ∉ f' ⁻¹' S := by
        show f' v ∉ S
        rw [hv]
        exact hb
      rw [Set.indicator_apply, if_neg hv']
  have hG0 : ∀ b, 0 ≤ ∫ v, ρ v ∂(fib b) := fun b => integral_nonneg hρ0
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hρ0) hρc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0)
      ((hGc.mono hSB).aestronglyMeasurable hSm), hmain]
  congr 1
  refine lintegral_congr_ae ((ae_restrict_iff' hSm).mpr (Filter.Eventually.of_forall fun b hb => ?_))
  exact (ofReal_integral_eq_lintegral_ofReal (hint b (hSB hb)) (Filter.Eventually.of_forall hρ0)).symm

theorem fib_set [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  set ρp : V → ℝ := fun v => max (ρ v) 0 with hρpdef
  set ρn : V → ℝ := fun v => max (-ρ v) 0 with hρndef
  have hρeq : ρ = fun v => ρp v - ρn v :=
    funext fun v => (max_zero_sub_max_neg_zero_eq_self (ρ v)).symm
  have hcp : Continuous ρp := hρc.max continuous_const
  have hcn : Continuous ρn := hρc.neg.max continuous_const
  have hsp : HasCompactSupport ρp := hρs.comp_left (g := fun x : ℝ => max x 0) (by simp)
  have hsn : HasCompactSupport ρn := hρs.neg.comp_left (g := fun x : ℝ => max x 0) (by simp)
  have hup : tsupport ρp ⊆ U := (tsupport_comp_subset (g := fun x : ℝ => max x 0) (by simp) ρ).trans hρU
  have hun : tsupport ρn ⊆ U := by
    refine (tsupport_comp_subset (g := fun x : ℝ => max x 0) (by simp) (-ρ)).trans ?_
    rw [tsupport_neg]
    exact hρU
  have hp := fib_set_nonneg hfib hf' hff' hι ρp hcp hsp hup (fun v => le_max_right _ _) S hS hSB
  have hn := fib_set_nonneg hfib hf' hff' hι ρn hcn hsn hun (fun v => le_max_right _ _) S hS hSB
  have hip : Integrable ρp μ := hcp.integrable_of_hasCompactSupport hsp
  have hin : Integrable ρn μ := hcn.integrable_of_hasCompactSupport hsn
  obtain ⟨hintp, hGp⟩ := hfib.2.2 ρp hcp hsp hup
  obtain ⟨hintn, hGn⟩ := hfib.2.2 ρn hcn hsn hun
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  calc ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ v in f' ⁻¹' S, ρp v ∂μ - ∫ v in f' ⁻¹' S, ρn v ∂μ := by
        rw [hρeq]
        exact integral_sub hip.integrableOn hin.integrableOn
    _ = ∫ b in S, (∫ v, ρp v ∂(fib b)) ∂ν - ∫ b in S, (∫ v, ρn v ∂(fib b)) ∂ν := by rw [hp, hn]
    _ = ∫ b in S, ((∫ v, ρp v ∂(fib b)) - ∫ v, ρn v ∂(fib b)) ∂ν :=
        (integral_sub ((hGp.mono hSB).integrableOn_compact hS)
          ((hGn.mono hSB).integrableOn_compact hS)).symm
    _ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
        refine setIntegral_congr_fun hSm (fun b hb => ?_)
        rw [hρeq]
        exact (integral_sub (hintp b (hSB hb)) (hintn b (hSB hb))).symm

theorem eq_zero_of_setIntegral [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℝ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  by_contra hne
  have hpos : 0 < D b0 * D b0 := mul_self_pos.mpr hne
  have hcont : ContinuousAt (fun b => D b0 * D b) b0 :=
    continuousAt_const.mul (hD.continuousAt hW)
  have hev : ∀ᶠ b in 𝓝 b0, D b0 * D b0 / 2 < D b0 * D b :=
    hcont.eventually (lt_mem_nhds (by linarith))
  obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (Filter.inter_mem hW hev)
  have hKW : K ⊆ W := fun x hx => (hKsub hx).1
  have h0K := h0 K hKc hKW
  have hKpos : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
  have hKfin : ν K < ⊤ := hKc.measure_lt_top
  have hint : IntegrableOn D K ν := (hD.mono hKW).integrableOn_compact hKc
  have hle : ∫ b in K, D b0 * D b0 / 2 ∂ν ≤ ∫ b in K, D b0 * D b ∂ν :=
    setIntegral_mono_on (integrableOn_const hKfin.ne) (hint.const_mul (D b0))
      hKc.isClosed.measurableSet (fun b hb => le_of_lt (hKsub hb).2)
  rw [integral_const_mul, h0K, mul_zero, setIntegral_const, smul_eq_mul] at hle
  have hr : 0 < ν.real K := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  have : 0 < ν.real K * (D b0 * D b0 / 2) := mul_pos hr (by linarith)
  linarith

end PI.VolStabSW.DensGen
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensGen =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.FibMeas0Holds =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.FibMeas0Holds", "h": "module\n\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensGen\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibDis\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PI.DegenerateSiegelWeil.FibUniq

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib1 fib2 : X → Measure V}

theorem integral_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (φ : V → ℝ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (b : X) :
    ∫ v, φ v ∂(fib1 b) = ∫ v, φ v ∂(fib2 b) := by
  apply +allowSynthFailures _root_.PI.VolStabS.FibUniq.integral_eq <;> assumption

theorem fin_cpt {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) (K : Set V) (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  apply +allowSynthFailures _root_.PI.VolStabS.FibUniq.fin_cpt <;> assumption

theorem open_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (O : Set V) (hO : IsOpen O)
    (hOU : O ⊆ U) (b : X) : fib1 b O = fib2 b O := by
  apply +allowSynthFailures _root_.PI.VolStabS.FibUniq.open_eq <;> assumption

theorem fib_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hU : IsOpen U) : fib1 = fib2 := by
  apply +allowSynthFailures _root_.PI.VolStabS.FibUniq.fib_eq <;> assumption

end Gen

section Tens

open scoped TensorProduct
open PI.VolStabSW PI.VolStabSW.TensAllW

end Tens

end PI.DegenerateSiegelWeil.FibUniq

namespace PI.DegenerateSiegelWeil

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.TensAllW

end PI.DegenerateSiegelWeil
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.FibMeas0Holds =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.IsFibreFamilyReindex =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.IsFibreFamilyReindex", "h": "module\n\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.FibMeas0Holds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace PI.DegenerateSiegelWeil.Scale

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal NNReal

section Reindex

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem isFibreFamily_reindex (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X}
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞}
    (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) :
    IsFibreFamily ((cμ * cν) • μ) f ι U ν univ
      (fun b => (fib (h.symm b)).map e.toMeasurableEquiv) := by
  obtain ⟨h1, h2, h3⟩ := hfib
  have hme : ⇑e.toMeasurableEquiv = ⇑e := rfl
  have hμ' : μ.map e.toMeasurableEquiv = cμ • μ := hμ
  have hν' : ν.map h.symm.toMeasurableEquiv = cν • ν := hν
  have hpre : ∀ b, e ⁻¹' (f ⁻¹' {ι b} ∩ U) = f ⁻¹' {ι (h.symm b)} ∩ U := by
    intro b
    ext v
    have hUv : e v ∈ U ↔ v ∈ U := by
      conv_rhs => rw [← hU]
      exact Iff.rfl
    simp only [mem_preimage, mem_inter_iff, mem_singleton_iff, hff', heh, hι.eq_iff, hUv]
    rw [h.eq_symm_apply]
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · rw [MeasurableEquiv.map_apply, preimage_compl, hme, hpre]
    exact h1 (h.symm b)
  · rw [Measure.restrict_smul, lintegral_smul_measure]
    have hφe : Measurable (φ ∘ e) := hφ.comp e.continuous.measurable
    have key1 : ∫⁻ v in U, (φ ∘ e) v ∂μ = cμ * ∫⁻ v in U, φ v ∂μ := by
      have h0 : ∫⁻ v in U, φ v ∂(μ.map e.toMeasurableEquiv) = ∫⁻ v in U, (φ ∘ e) v ∂μ := by
        rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, hme, hU]
        rfl
      rw [← h0, hμ', Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    have key2 : ∫⁻ b, ∫⁻ v, φ v ∂(fib (h.symm b)).map e.toMeasurableEquiv ∂ν =
        cν * ∫⁻ b, ∫⁻ v, (φ ∘ e) v ∂fib b ∂ν := by
      simp only [lintegral_map_equiv]
      rw [← smul_eq_mul, ← lintegral_smul_measure, ← hν', lintegral_map_equiv]
      rfl
    rw [key2, ← h2 _ hφe, key1, smul_eq_mul]
    ring
  · have hφe_c : Continuous (φ ∘ e) := hφc.comp e.continuous
    have hφe_s : HasCompactSupport (φ ∘ e) := hφs.comp_homeomorph e
    have hsub : tsupport (φ ∘ e) ⊆ e ⁻¹' tsupport φ :=
      closure_minimal (fun v hv => subset_tsupport φ hv) ((isClosed_tsupport φ).preimage e.continuous)
    have hφe_U : tsupport (φ ∘ e) ⊆ U := by
      intro v hv
      rw [← hU]
      exact hφU (hsub hv)
    obtain ⟨hi, hcont⟩ := h3 _ hφe_c hφe_s hφe_U
    refine ⟨fun b _ => ?_, ?_⟩
    · rw [integrable_map_equiv]
      exact hi _ (mem_univ _)
    · have hfun : (fun b => ∫ v, φ v ∂(fib (h.symm b)).map e.toMeasurableEquiv) =
          (fun b' => ∫ v, (φ ∘ e) v ∂fib b') ∘ h.symm := by
        funext b
        simp only [Function.comp_apply, integral_map_equiv]
        rfl
      rw [hfun]
      exact ((continuousOn_univ.1 hcont).comp h.symm.continuous).continuousOn

theorem isFibreFamily_smul {B : Set X} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hfib : IsFibreFamily μ f ι U ν B fib) :
    IsFibreFamily (c • μ) f ι U ν B (fun b => c • fib b) := by
  obtain ⟨h1, h2, h3⟩ := hfib
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · simp only [Measure.smul_apply, h1 b, smul_zero]
  · rw [Measure.restrict_smul, lintegral_smul_measure, h2 φ hφ, smul_eq_mul, ← lintegral_const_mul' _ _ hc]
    simp only [lintegral_smul_measure, smul_eq_mul]
  · obtain ⟨hi, hcont⟩ := h3 φ hφc hφs hφU
    refine ⟨fun b hb => (hi b hb).smul_measure hc, ?_⟩
    simp only [integral_smul_measure, smul_eq_mul]
    exact continuousOn_const.mul hcont

end Reindex

section Uniq

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem fib_reindex_eq (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hUo : IsOpen U)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞} (hcμ : cμ ≠ ⊤)
    (hcν : cν ≠ ⊤) (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) (b : X) :
    (fib (h.symm b)).map e.toMeasurableEquiv = (cμ * cν) • fib b := by
  have hc : cμ * cν ≠ ⊤ := ENNReal.mul_ne_top hcμ hcν
  haveI : IsFiniteMeasureOnCompacts ((cμ * cν) • μ) := IsFiniteMeasureOnCompacts.smul μ hc
  have := PI.DegenerateSiegelWeil.FibUniq.fib_eq (isFibreFamily_reindex e h hff' hι heh hU hμ hν hfib)
    (isFibreFamily_smul hc hfib) hf' hff' hι hUo
  exact congrFun this b

theorem fib_map_fixed (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hUo : IsOpen U)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞} (hcμ : cμ ≠ ⊤)
    (hcν : cν ≠ ⊤) (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) (b : X) (hb : h b = b) :
    (fib b).map e.toMeasurableEquiv = (cμ * cν) • fib b := by
  have hb' : h.symm b = b := h.symm_apply_eq.2 hb.symm
  have := fib_reindex_eq e h hf' hff' hι hUo heh hU hcμ hcν hμ hν hfib b
  rwa [hb'] at this

end Uniq

end PI.DegenerateSiegelWeil.Scale
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.IsFibreFamilyReindex =====
