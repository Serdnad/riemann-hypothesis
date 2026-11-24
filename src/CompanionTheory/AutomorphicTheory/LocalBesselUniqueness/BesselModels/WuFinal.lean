module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.CoefWeightedLocHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOne
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.QuotRaw
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Closed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.BruhatDecomposition
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ConjugationInvariantMeasure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarMeasureUniqueness
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LocalWeilRepresentation
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ProdSetIsClosed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.SiegelMeasureDefinition
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocScalarPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.HaarWN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ProductDecompositionHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ExistsTowerOfLocalSetting

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocScalar, CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGap, CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocalUniquenessReduction, CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WuFinal

-- ===== clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocScalar =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocScalar", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.CoefWeightedLocHolds\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.QuotRaw\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Closed\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.BruhatDecomposition\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ConjugationInvariantMeasure\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarMeasureUniqueness\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LocalWeilRepresentation\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ProdSetIsClosed\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.SiegelMeasureDefinition\nimport Formalism.RealPlaceAnalysis.FinalF\nimport Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocScalarPf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.WuDecay
open scoped InnerProductSpace ENNReal NNReal
open Matrix

namespace Formalism.L2.SG.Pf.WuDec.LS

open Formalism.L2.SG.Pf.WuDec

section Facts

open Classical Formalism.L2.SG.Pf.WFL

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

end Facts

section K1

open Classical Formalism.L2.SG.Pf.WFL

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

end K1

section Schur

open Classical

variable {D : D7} (X : HidaSetting D)

end Schur

section Main

open Classical Formalism.L2.SG.SplitPrimeNormLemmas

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem pv_integrable (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (v : InfinitePlace X.B.I.F) :
    Integrable (Pv X v) (Formalism.REAL.muG (X.B.I.ε v)) := by
  have h := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X (coefWeighted_of_gap X Formalism.L2.SG.Closed.BM.CoefWeightedLoc_holds hG) v
  have e : Pv X v = fun g => ((X.dv v : ℝ) : ℂ) * star (Formalism.L2.SG.WuDecayPf.coefV X v g) := by
    funext g; rfl
  refine Integrable.mono' (h.norm.const_mul |X.dv v|) (continuous_Pv X v).aestronglyMeasurable
    (ae_of_all _ fun g => le_of_eq ?_)
  rw [e]
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]

theorem local_scalar_reduction : LocScalarStep := by
  intro D hG X u μS νl C hQ v c hc0 hc
  set μ := Formalism.REAL.muG (X.B.I.ε v) with hμ
  set f := X.Wloc u v with hfdef
  set ph := Pv X v with hph
  have hfc : Continuous f := X.Wloc_cont u v
  have hpc : Continuous ph := continuous_Pv X v
  have hpI : Integrable ph μ := pv_integrable X hG v
  obtain ⟨hL0, hLt⟩ := localRepresentationL2 X u hQ v
  obtain ⟨β, hβm, hβ⟩ := Formalism.L2.SG.Pf.WuDec.quot_bruhat X u hQ v
  set ν' := μ.withDensity β with hν'
  have htr : ∀ F : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable F → (∀ s ∈ NHloc X u v, ∀ x, F (s * x) = F x) →
      ∫⁻ x, F x ∂(νl v) = ∫⁻ x, F x ∂ν' := by
    intro F hF hi
    rw [hβ F hF hi, hν', lintegral_withDensity_eq_lintegral_mul _ hβm hF]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]; ring
  set L := ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(νl v) with hL
  have hinvN : ∀ s ∈ NHloc X u v, ∀ x, ‖f (s * x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := by
    intro s hs x
    obtain ⟨m, hm, h, hh, rfl⟩ := hs
    have hs' : m * h ∈ Sloc X u v := mul_mem_Sloc X u v (Nloc_sub X u v hm) (Hloc_sub X u v hh)
    rw [← eNorm_norm (f (m * h * x)), norm_Wloc_inv X u v hs', eNorm_norm]
  have hK1 : ∀ y, ∫⁻ x, ‖f (x * y)‖ₑ ^ 2 ∂ν' = L := fun y => by
    rw [← htr (fun x => ‖f (x * y)‖ₑ ^ 2) ((hfc.comp (continuous_id.mul continuous_const)).eNorm.measurable.pow_const 2)
      (fun s hs x => by simp only [mul_assoc]; exact hinvN s hs (x * y))]
    exact Formalism.L2.SG.Pf.WuDec.quot_rightInv X u hQ v (fun x => ‖f x‖ₑ ^ 2) (hfc.eNorm.measurable.pow_const 2) hinvN y
  have hL' : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν' = L := (htr _ (hfc.eNorm.measurable.pow_const 2) hinvN).symm
  have hin : ∀ y, ∫⁻ x, ‖f x‖ₑ * ‖f (x * y)‖ₑ ∂ν' ≤ 2 * L := by
    intro y
    calc ∫⁻ x, ‖f x‖ₑ * ‖f (x * y)‖ₑ ∂ν' ≤ ∫⁻ x, (‖f x‖ₑ ^ 2 + ‖f (x * y)‖ₑ ^ 2) ∂ν' :=
          lintegral_mono fun x => Formalism.L2.SG.Pf.WuDec.ennreal_mul_le_sq _ _
      _ = L + L := by
          rw [lintegral_add_left (hfc.eNorm.measurable.pow_const 2), hK1 y, hL']
      _ = 2 * L := (two_mul L).symm
  have mf : Measurable fun y => ‖f y‖ₑ := hfc.eNorm.measurable
  have mp : Measurable fun y => ‖ph y‖ₑ := hpc.eNorm.measurable
  set A : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun x =>
    ∫⁻ g, ‖ph g‖ₑ * ∫⁻ h, ‖ph h‖ₑ * ‖f (x * g * h)‖ₑ ∂μ ∂μ with hA

  set T : Formalism.REAL.UJ (X.B.I.ε v) → Formalism.REAL.UJ (X.B.I.ε v) → Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ :=
    fun x g h => ‖f x‖ₑ * (‖ph g‖ₑ * (‖ph h‖ₑ * ‖f (x * g * h)‖ₑ)) with hTdef
  have hTm : Measurable fun p : (Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) × Formalism.REAL.UJ (X.B.I.ε v) =>
      T p.1.1 p.1.2 p.2 := by
    have h3 : Continuous fun p : (Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) × Formalism.REAL.UJ (X.B.I.ε v) =>
        f (p.1.1 * p.1.2 * p.2) :=
      hfc.comp (((continuous_fst.comp continuous_fst).mul (continuous_snd.comp continuous_fst)).mul continuous_snd)
    exact (mf.comp (measurable_fst.comp measurable_fst)).mul ((mp.comp (measurable_snd.comp measurable_fst)).mul
      ((mp.comp measurable_snd).mul h3.eNorm.measurable))
  have hTm' : ∀ g, Measurable fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => T p.1 g p.2 := by
    intro g
    exact hTm.comp (measurable_fst.prodMk measurable_const |>.prodMk measurable_snd)
  have e1 : ∫⁻ x, ‖f x‖ₑ * A x ∂ν' = ∫⁻ g, ∫⁻ h, ∫⁻ x, T x g h ∂ν' ∂μ ∂μ := by
    have step1 : ∀ x, ‖f x‖ₑ * A x = ∫⁻ g, ∫⁻ h, T x g h ∂μ ∂μ := by
      intro x
      rw [hA]
      simp only []
      rw [← lintegral_const_mul' _ _ eNorm_ne_top]
      refine lintegral_congr fun g => ?_
      rw [← lintegral_const_mul' _ _ eNorm_ne_top, ← lintegral_const_mul' _ _ eNorm_ne_top]
    simp only [step1]
    rw [lintegral_lintegral_swap (hTm.lintegral_prod_right').aemeasurable]
    refine lintegral_congr fun g => ?_
    exact lintegral_lintegral_swap (hTm' g).aemeasurable
  have hT : ∫⁻ x, ‖f x‖ₑ * A x ∂ν' < ⊤ := by
    rw [e1]
    have hb : ∀ g h, ∫⁻ x, T x g h ∂ν' ≤ ‖ph g‖ₑ * (‖ph h‖ₑ * (2 * L)) := by
      intro g h
      have : ∀ x, T x g h = ‖ph g‖ₑ * (‖ph h‖ₑ * (‖f x‖ₑ * ‖f (x * (g * h))‖ₑ)) := by
        intro x; simp only [hTdef, mul_assoc]; ring
      simp only [this]
      rw [lintegral_const_mul' _ _ eNorm_ne_top, lintegral_const_mul' _ _ eNorm_ne_top]
      gcongr
      exact hin _
    calc ∫⁻ g, ∫⁻ h, ∫⁻ x, T x g h ∂ν' ∂μ ∂μ ≤ ∫⁻ g, ∫⁻ h, ‖ph g‖ₑ * (‖ph h‖ₑ * (2 * L)) ∂μ ∂μ :=
          lintegral_mono fun g => lintegral_mono fun h => hb g h
      _ = (∫⁻ g, ‖ph g‖ₑ ∂μ) * ((∫⁻ h, ‖ph h‖ₑ ∂μ) * (2 * L)) := by
          rw [← lintegral_mul_const _ mp]
          refine lintegral_congr fun g => ?_
          rw [lintegral_const_mul' _ _ eNorm_ne_top, lintegral_mul_const _ mp]
      _ < ⊤ := ENNReal.mul_lt_top hpI.2 (ENNReal.mul_lt_top hpI.2
          (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.2 hLt)))

  obtain ⟨x, hfx, hAx⟩ : ∃ x, f x ≠ 0 ∧ A x < ⊤ := by
    by_contra hcon
    push Not at hcon
    set E := {x | f x ≠ 0} with hE
    have hEm : MeasurableSet E := (isClosed_eq hfc continuous_const).isOpen_compl.measurableSet
    have hE0 : ν' E ≠ 0 := by
      intro h0
      apply hL0
      rw [← hL']
      apply (lintegral_eq_zero_iff (mf.pow_const 2)).2
      have : ∀ᵐ y ∂ν', y ∉ E := measure_eq_zero_iff_ae_notMem.1 h0
      filter_upwards [this] with y hy
      simp only [hE, Set.mem_setOf_eq, not_not] at hy
      simp [hy]
    have hle : ∀ y, E.indicator (fun _ => (⊤ : ℝ≥0∞)) y ≤ ‖f y‖ₑ * A y := by
      intro y
      by_cases hy : y ∈ E
      · rw [Set.indicator_of_mem hy, top_le_iff, top_le_iff.1 (hcon y hy), ENNReal.mul_top]
        exact eNorm_ne_zero.2 hy
      · rw [Set.indicator_of_notMem hy]; exact zero_le
    have := lt_of_le_of_lt (lintegral_mono hle) hT
    rw [lintegral_indicator_const hEm, ENNReal.top_mul hE0] at this
    exact lt_irrefl _ this

  set Φ : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v :=
    fun p => ph p.1 • (ph p.2 • f (x * p.1 * p.2)) with hΦ
  have hΦc : Continuous Φ :=
    (hpc.comp continuous_fst).smul ((hpc.comp continuous_snd).smul
      (hfc.comp ((continuous_const.mul continuous_fst).mul continuous_snd)))
  have hΦi : Integrable Φ (μ.prod μ) := by
    refine ⟨hΦc.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖Φ p‖ₑ ∂(μ.prod μ) < ⊤
    rw [lintegral_prod _ hΦc.eNorm.aemeasurable]
    have e2 : ∀ g, ∫⁻ h, ‖Φ (g, h)‖ₑ ∂μ = ‖ph g‖ₑ * ∫⁻ h, ‖ph h‖ₑ * ‖f (x * g * h)‖ₑ ∂μ := fun g => by
      simp only [hΦ, eNorm_smul]
      rw [lintegral_const_mul' _ _ eNorm_ne_top]
    simp only [e2]
    exact hAx
  have hΦv : ∫ p, Φ p ∂(μ.prod μ) = c • c • f x := by
    rw [integral_prod _ hΦi]
    have e3 : ∀ g, ∫ h, Φ (g, h) ∂μ = c • (ph g • f (x * g)) := fun g => by
      simp only [hΦ]
      rw [integral_smul, (hc (x * g)).2, smul_comm]
    simp only [e3]
    rw [integral_smul, (hc x).2]
  have hS := measurePreserving_prod_mul μ μ
  have he : MeasurableEmbedding (fun z : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => (z.1, z.1 * z.2)) :=
    (MeasurableEquiv.shearMulRight (Formalism.REAL.UJ (X.B.I.ε v))).measurableEmbedding
  set Ψ : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v :=
    fun p => ph p.1 • (ph (p.1⁻¹ * p.2) • f (x * p.2)) with hΨ
  have hcomp : Ψ ∘ (fun z : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => (z.1, z.1 * z.2)) = Φ := by
    funext z
    simp only [Function.comp_apply, hΨ, hΦ, inv_mul_cancel_left, mul_assoc]
  have hΨi : Integrable Ψ (μ.prod μ) := (hS.integrable_comp_emb he).1 (by rw [hcomp]; exact hΦi)
  have hΨv : ∫ p, Ψ p ∂(μ.prod μ) = c • f x := by
    rw [integral_prod_symm _ hΨi]
    have e4 : ∀ y, ∫ g, Ψ (g, y) ∂μ = ph y • f (x * y) := fun y => by
      simp only [hΨ, smul_smul]
      rw [integral_smul_const, (Formalism.L2.SG.Pf.WuDec.pv_conv X v y).2]
    simp only [e4]
    exact (hc x).2
  have hΦΨ : ∫ p, Φ p ∂(μ.prod μ) = ∫ p, Ψ p ∂(μ.prod μ) := by
    rw [← hcomp]
    exact hS.integral_comp he Ψ
  rw [hΦv, hΨv, smul_smul] at hΦΨ
  have h5 : (c * c - c) • f x = 0 := by rw [sub_smul, hΦΨ, sub_self]
  have h6 : c * c - c = 0 := (smul_eq_zero.1 h5).resolve_right hfx
  have h7 : c * (c - 1) = 0 := by rw [mul_sub, mul_one]; exact h6
  exact sub_eq_zero.1 ((mul_eq_zero.1 h7).resolve_left hc0)

end Main

end Formalism.L2.SG.Pf.WuDec.LS
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocScalar =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGap =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGap", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOne\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf\nimport Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeCS3d

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

namespace BM

end BM

end Formalism.MainNotions.BridgeCS3d

namespace Formalism.MainNotions.BridgeCS3dBOW

open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

theorem besselOfW_gap (hJ : CompanionTheory.Lime.BM.UniqGap) :
    Formalism.L2.SG.LocWSOf.BesselOfW := by
  intro k r z c u lam ε h H _ _ _ σ hlam hσ hgap hok hz hT hc Vp _ _ _ π hπ w hw μG μW μN ν hG hW hN hq W hWc hWeq
    hRe hne hfin
  have : CompleteSpace Vp := FiniteDimensional.complete ℂ Vp
  have hS : Side k r ε lam h σ w z c u π μW μN μG ν := ⟨hlam, hσ, hgap, hok, hw, hz, hT, hc, hπ, hW, hN, hG, hq⟩
  obtain ⟨l, hlB, hla, -⟩ := CompanionTheory.Lime.BM.dDFormOne hJ CompanionTheory.Lime.BM.inputs
    k r ε lam h H σ w Vp z c u π μW μN μG ν hS
  obtain ⟨κ, hκ⟩ := bow_core hS l hla hWc hWeq hRe
  exact ⟨fun v => κ • l v, (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).mpr (DDSmoothness.bessel_smul hlB κ), hκ⟩

end Formalism.MainNotions.BridgeCS3dBOW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGap =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocalUniquenessReduction =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocalUniquenessReduction", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGap\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniq\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.HaarWN\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ProductDecompositionHolds\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.QuotRaw\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps\nimport Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap\nimport Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable\nimport Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ExistsTowerOfLocalSetting\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.QuantumDeterminants
open scoped InnerProductSpace ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.WuDec

namespace BM

section Core

variable {k r : ℕ}

private theorem besselMultOneOnGap_of_uniqGap (hM : CompanionTheory.Lime.BM.UniqGap) :
    BesselMultOneOnGap := by
  intro k r ε lam h H _ _ σ z c u Wp _ _ π hg hok hl hds hz hT hc hπ B B' hB hB'
  obtain ⟨a, b, hab, hrel⟩ := hM k r ε lam h H σ z c u Wp π
    hok.1 hg hok.2.1 hl hds hz hT hc hπ B B'
    ((Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B).1 hB)
    ((Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B').1 hB')
  exact ⟨a, b, hab, fun x hx => hrel x hx⟩

theorem besselUniq_core (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {lam : Fin (2 * r + k + 1) → ℝ}
    {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat k r → (H →L[ℂ] H)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hds : IsDSHpk k r ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0)
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    (hπ : IsHCTypeW k r z u π) {w : H} (hw : IsLowUnitH k r ε lam σ w) (hws : w ∈ smoothVecs (k := k) (r := r) σ)
    {μG μW μN ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hG : IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) (hW : IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hQ : IsQuotMeas μG (Formalism.MainNotions.S.muS μW μN) ν)
    {W W0 : Mat k r → Vp}
    (hc1 : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he1 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W)
    (hr1 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x)
    (hl1 : l2SG ν W ≠ 0) (hl1' : l2SG ν W < ⊤)
    (hc2 : ContinuousOn W0 (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he2 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W0)
    (hr2 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W0 (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W0 x = W0 x)
    (hl2 : l2SG ν W0 ≠ 0) (hl2' : l2SG ν W0 < ⊤)
    (hx0 : ∃ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W0 x0 ≠ 0) :
    ∃ a : ℂ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x = a • W0 x :=
  Formalism.L2.SG.Pf.WuDec.besselUniq_core_of_gap hBW (besselMultOneOnGap_of_uniqGap hM1)
    hl hds hg hok hz hT hc hπ hw hws hG hW hN hQ hc1 he1 hr1 hl1 hl1' hc2 he2 hr2 hl2 hl2' hx0

end Core

open Classical Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay

section Main

variable {k r : ℕ}

theorem locUniq_gen (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    (hB : BesselNVGap) (hCW : CoefWeightedLoc) (hWl : WlocExists)
    (hk : 1 ≤ k) (hke : Even k) {T : ℝ} (hT : 0 < T) {gg : ℕ} (hgg : 0 < gg)
    {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z : Fin (2 * r + k + 1) → ℂ}
    (hF : IsFrameJ (eps48 k r) e f wf (z0v T z))
    {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (hu : Formalism.QuantumDeterminants.IsHCParam u)
    (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) (hI : InterlacingCondition k r u v b) (hH : HalfIntegralDifference k r u v b)
    (hGap : GapBig k r b) {h : ℝ} (hga : Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) (lam48 k r v b) h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hDS : IsDS (eps48 k r) (lam48 k r v b) σ)
    {w : H} (hw : IsLowUnit (eps48 k r) (lam48 k r v b) σ w)
    {Vl : Type} [NormedAddCommGroup Vl] [InnerProductSpace ℂ Vl] [FiniteDimensional ℂ Vl]
    {πl : Matrix (Fin k) (Fin k) ℂ → (Vl →L[ℂ] Vl)} (hπ : IsHCTypeU k u πl)
    {μS ν : Measure (Formalism.REAL.UJ (eps48 k r))} (hS : IsLocHaar (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T)) μS)
    (hQ : IsLocQuot μS ν)
    {W : Formalism.REAL.UJ (eps48 k r) → Vl} (hWc : Continuous W)
    (hWe : ∀ s x : Formalism.REAL.UJ (eps48 k r), ∀ h ∈ UWset k r (zBv k r T), ∀ m ∈ Nset k r,
      Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z) = h * m →
      W (s * x) = psiR (eps48 k r) gg e f z (uMat s) • piB (eps48 k r) e f wf (z0v T z) πl h (W x))
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG (eps48 k r)) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG (eps48 k r)) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG (eps48 k r)) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG (eps48 k r)) = W x)
    (hL0 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ 0) (hLt : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ ⊤) :
    (∫⁻ x, ‖W x‖ₑ * ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ∂ν
      < ⊤) ∧
    ∃ (α : Formalism.REAL.UJ (eps48 k r) → ℂ) (Ω : Set (Formalism.REAL.UJ (eps48 k r))) (a : ℝ), IsCompact Ω ∧ 1 ∈ Ω ∧
      Measurable α ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x, Integrable (fun g => α g • W (x * g)) (Formalism.REAL.muG (eps48 k r)) ∧
        ∫ g, α g • W (x * g) ∂(Formalism.REAL.muG (eps48 k r)) = W x :=
  Formalism.L2.SG.Pf.WuDec.locUniq_gen_of_gap hBW (besselMultOneOnGap_of_uniqGap hM1)
    hB hCW hWl hk hke hT hgg hF hu hl hI hH hGap hga hok hDS hw hπ hS hQ hWc hWe hWr hL0 hLt

end Main

theorem locUniq_n (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    (hB : BesselNVGap) (hCW : CoefWeightedLoc) (hWl : WlocExists) (hHN : LocHNProps)
    {k r n : ℕ} (hn : n = 2 * r + k + 1) (hk : 1 ≤ k) (hke : Even k) {T : ℝ} (hT : 0 < T) {gg : ℕ} (hgg : 0 < gg)
    (ε : Fin n → Bool) (hε : ∀ i, ε i = eps48 k r (Fin.cast hn i))
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (wf : Fin k → Fin n → ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0) (hzw : ∀ a, hJ ε z (wf a) = 0)
    {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (hu : Formalism.QuantumDeterminants.IsHCParam u)
    (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) (hI : InterlacingCondition k r u v b) (hH : HalfIntegralDifference k r u v b)
    (hGap : GapBig k r b) {h : ℝ} (hga : Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) (lam48 k r v b) h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (lam : Fin n → ℝ) (hlam : ∀ i, lam i = lam48 k r v b (Fin.cast hn i))
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hDS : IsDS ε lam σ) (w : H) (hw : IsLowUnit ε lam σ w)
    {Vl : Type} [NormedAddCommGroup Vl] [InnerProductSpace ℂ Vl] [FiniteDimensional ℂ Vl]
    (πl : Matrix (Fin k) (Fin k) ℂ → (Vl →L[ℂ] Vl)) (hπ : IsHCTypeU k u πl)
    (μS ν : Measure (Formalism.REAL.UJ ε))
    (hS : SigmaFinite μS ∧ μS ≠ 0 ∧
      μS {s | ∃ m ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z},
          s = m * h}ᶜ = 0 ∧
      ∀ s ∈ {s | ∃ m ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z},
          s = m * h}, μS.map (fun x => s * x) = μS)
    (hQ : ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
      ∫⁻ x, F x ∂(Formalism.REAL.muG ε) = ∫⁻ x, (∫⁻ s, F (s * x) ∂μS) ∂ν)
    (W : Formalism.REAL.UJ ε → Vl) (hWc : Continuous W)
    (hWe : ∀ m : Formalism.REAL.UJ ε, InN ε e z (uMat m) → ∀ h : Formalism.REAL.UJ ε,
      ((∀ a, uMat h *ᵥ e a = e a) ∧ (∀ a, uMat h *ᵥ f a = f a) ∧ uMat h *ᵥ z = z) → ∀ x,
      W (m * h * x) = psiR ε gg e f z (uMat (m * h)) • πl (fun a b => hJ ε (wf a) (uMat h *ᵥ wf b)) (W x))
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG ε) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG ε) = W x)
    (hL0 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ 0) (hLt : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ ⊤) (N : ℝ) (hN : N ≤ N1H k r) :
    (∫⁻ x, ‖W x‖ₑ * ENNReal.ofReal
        ((⨅ t : {s : Formalism.REAL.UJ ε | InS e z (uMat s)}, opn (uMat ((t : Formalism.REAL.UJ ε) * x))) ^ N) ∂ν < ⊤) ∧
    ∃ (α : Formalism.REAL.UJ ε → ℂ) (Ω : Set (Formalism.REAL.UJ ε)) (a : ℝ), IsCompact Ω ∧ 1 ∈ Ω ∧
      Measurable α ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x, Integrable (fun g => α g • W (x * g)) (Formalism.REAL.muG ε) ∧
        ∫ g, α g • W (x * g) ∂(Formalism.REAL.muG ε) = W x :=
  Formalism.L2.SG.Pf.WuDec.locUniq_n_of_gap hBW (besselMultOneOnGap_of_uniqGap hM1)
    hB hCW hWl hHN hn hk hke hT hgg ε hε e f z wf hee hff hef hez hfz hzz hww hew hfw hzw
    hu hl hI hH hGap hga hok lam hlam σ hDS w hw πl hπ μS ν hS hQ W hWc hWe hWr hL0 hLt N hN

def LocUniqStep : Prop :=
  BesselNVGap → CoefWeightedLoc → WlocExists → Formalism.L2.SG.LocWSOf.BesselOfW → CompanionTheory.Lime.BM.UniqGap →
    ∀ (D : Formalism.BasicNotions.D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u : D.what₂.Word)
      (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞), QuotWit X u μS νl C →
      ∀ v (W : Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v), Continuous W → LocEquivW X u v W → LocReprodW X u v W →
        ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(νl v) ≠ 0 → ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(νl v) ≠ ⊤ → LocConcl X u v (νl v) W

theorem local_uniqueness_reduction : LocUniqStep :=
  fun hB hCW hWl hBW hM1 =>
    Formalism.L2.SG.Pf.WuDec.local_uniqueness_reduction_of_gap
      hB hCW hWl hBW (besselMultOneOnGap_of_uniqGap hM1)

theorem locDecayStep_of (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    (hR : LocReprodStep) (hU : LocUniqStep) : LocDecayStep := by
  intro D hG X u μS νl C hQ v
  exact hU hB hC hW hBW hM1 D hG X u μS νl C hQ v (X.Wloc u v) (X.Wloc_cont u v)
    (fun m hm h hh x => locEquiv X u v m hm h hh x) (hR D hG X u μS νl C hQ v)
    (localRepresentationL2 X u hQ v).1 (localRepresentationL2 X u hQ v).2

theorem wuDecay_gap (hM1 : CompanionTheory.Lime.BM.UniqGap) (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hQK : QuotProdK) (hNU : NUnimodLoc) (hS : LocScalarStep) : Formalism.L2.SG.Pf.WuDecayOfGap :=
  wuDecayOfGap_of_steps hC (quotAll_of hQK locHNProps_holds hNU)
    (locDecayStep_of hB hC hW (Formalism.MainNotions.BridgeCS3dBOW.besselOfW_gap hM1) hM1 (locReprodStep_of hS) local_uniqueness_reduction)

end BM

end Formalism.L2.SG.Pf.WuDec
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocalUniquenessReduction =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WuFinal =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WuFinal", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.CoefWeightedLocHolds\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocScalar\npublic import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocalUniquenessReduction\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Closed.BM

theorem wuDecayOfGap_of_uniqGap (h : CompanionTheory.Lime.BM.UniqGap) : WuDecayOfGap :=
  WuDec.BM.wuDecay_gap h BesselNVGap_holds CoefWeightedLoc_holds WlocExists_holds
    QuotProdK_holds NUnimodLoc_holds WuDec.LS.local_scalar_reduction

end Formalism.L2.SG.Pf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WuFinal =====
