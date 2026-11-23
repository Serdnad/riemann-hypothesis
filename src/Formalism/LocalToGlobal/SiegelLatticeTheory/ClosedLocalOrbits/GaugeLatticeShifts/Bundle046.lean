module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHGlue
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle039
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle041
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IsClosedSLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalJacobianOfDoubleCoset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MulVecMapMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle044
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SecMeasLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle013
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle005

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB Formalism.L2.SG.Pf.GE

theorem bruhatHaar_of_sandwich_volLim (hS : Sandwich) (hV : VolLim) : BruhatHaar :=
  bruhatHaar_of_rhsHaar rhsHaar gaugeShift hS hV

theorem wbHaar_of_rhsWLim (hL : RhsWLim) : WbHaar :=
  wbHaar_of_rhsWHaar rhsWHaar gaugeShiftW hL

theorem gaugeExists_of_sandwich_rhsWLim (hS : Sandwich) (hV : VolLim) (hU : ExistsGaugeMeasureForEachRank) (hL : RhsWLim) : GaugeExists :=
  gaugeExists_of rhsHaar rhsWHaar wbDataEx hU gaugeShift gaugeShiftW (rhsLim_of hS hV) hL

theorem jacGauge_of_sandwich_gaugeMeasure (hS : Sandwich) (hV : VolLim) (hU : ExistsGaugeMeasureForEachRank) (hL : RhsWLim) : JacGauge :=
  jacGauge_of (bruhatHaar_of_sandwich_volLim hS hV) (wbHaar_of_rhsWLim hL) (gaugeExists_of_sandwich_rhsWLim hS hV hU hL)

end Formalism.L2.SG.Pf
end
end

section

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem haar_disintegration_real_holds : HaarDisintegrationReal := by
  have hR : JacobianCoordinates.JL.RightInvS :=
    JacobianCoordinates.JL.rightInvS_of JacobianCoordinates.JL.setCorr_holds (JacobianCoordinates.JL.haarCorr_of JacobianCoordinates.JL.setCorr_holds)
  have hU : JacobianCoordinates.UnimodLoc := hR
  exact UnitaryIsometries.haar_disintegration_of_local ProductExactness.product_formula_holds JacobianCoordinates.JL.jacLoc_holds ProductExactness.SecMeasLoc_holds hU
    NilradicalHermitianFrames.NH.NHLoc_holds ProductExactness.StepReal_holds

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.S.Pv.ConvG
open scoped InnerProductSpace ENNReal Pointwise

namespace Formalism.L2.SG.RealObj.EnergyConvJ

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem fin_of_weil (μ μS ν : Measure G) [IsFiniteMeasureOnCompacts μ] (hμ : μ ≠ 0)
    (hW : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν) :
    IsFiniteMeasureOnCompacts μS := by
  refine ⟨fun K hK => ?_⟩
  have hν : ν ≠ 0 := by
    rintro rfl
    apply hμ
    have := hW (fun _ => 1) measurable_const
    simpa using this
  obtain ⟨C, hC, hνC⟩ : ∃ C : Set G, IsCompact C ∧ ν C ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hν
    have : ν Set.univ = 0 := by
      rw [← iUnion_compactCovering G]
      exact measure_iUnion_null fun n => hcon _ (isCompact_compactCovering G n)
    exact Measure.measure_univ_eq_zero.mp this
  have hWc : IsCompact (K * C) := hK.mul hC
  have hWm : MeasurableSet (K * C) := hWc.isClosed.measurableSet
  have hf := hW ((K * C).indicator 1) (measurable_one.indicator hWm)
  rw [lintegral_indicator_one hWm] at hf
  have hinner : ∀ x, ∫⁻ s, (K * C).indicator 1 (s * x) ∂μS = μS ((· * x) ⁻¹' (K * C)) := fun x => by
    rw [← lintegral_indicator_one ((measurable_mul_const x) hWm)]
    rfl
  simp_rw [hinner] at hf
  have hbound : μS K * ν C ≤ μ (K * C) := by
    rw [hf, ← lintegral_indicator_const hC.isClosed.measurableSet]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]
      exact measure_mono fun k hk => Set.mul_mem_mul hk hx
    · simp [hx]
  have hμW : μ (K * C) < ⊤ := hWc.measure_lt_top
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  rw [htop, ENNReal.top_mul hνC] at hbound
  exact absurd (lt_of_le_of_lt hbound hμW) (lt_irrefl _)

end Gen

variable {D : D7}

theorem sloc_sub_NH (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) {x : Formalism.REAL.UJ (X.B.I.ε v)}
    (hx : x ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u v) : x ∈ Formalism.L2.SG.Pf.WuDec.NHloc X u v := by
  classical
  set s : X.B.I.Ginf := Function.update 1 v x with hsdef
  have hs : s ∈ X.SinfU u := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hsdef, Function.update_self]
      exact hx
    · rw [hsdef, Function.update_of_ne hw]
      exact Formalism.L2.SG.Pf.WuDec.one_mem_Sloc X u w
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hdec⟩ := Formalism.L2.S.Pv.HaarSubS.sDecomp_holds D X u
  obtain ⟨n, hn, h, hh, he⟩ := hdec s hs
  have hxv : x = n v * h v := by
    have := congrFun he v
    rw [hsdef, Function.update_self] at this
    exact this
  exact ⟨n v, hn v, h v, hh v, hxv⟩

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end
