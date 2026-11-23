module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.DShort
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FrameTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.TermsAtFiniteOfFrameOpShortFin
public import Formalism.PeriodIntegrals.Bundle023
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle034
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle033
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.GTLowerOf
public import Formalism.PeriodIntegrals.LengthPoleInLift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PoleLengthBound
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.LenBaseHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem terms_at_point_finite (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermsAtFinite D u u' :=
  PI.TermsAtPtFiniteW.termsAtFinite_of_frameOp_shortFin PI.TermsAtPtFiniteW.frameOp_holds PI.TermsAtPtFiniteW.shortFin_holds D u u'
end

section

theorem gTLower_of (h2 : Formalism.BasicNotions.FactDelDualNabla) : PI.GTLower :=
  PI.WGL.gTLower_of h2 highest_weight_irreducible gelfand_tsetlin_branching schur_fock
end

section

theorem length_pole_t0 : PI.LengthPoleInLift := PI.PoleLengthCount.pole_length_bound
end

section

theorem length_base_t0 : ∀ {D : Formalism.BasicNotions.D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} {j : ℕ}
    {X : Formalism.MainNotions.WeightAlgebra.PJ D B P j} {ka wL wF : Formalism.MainNotions.WeightFamilies.Wt D j},
    Formalism.MainNotions.Gaps.EtaleWeightGaps.LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) :=
  PoleLengthBounds.lenBase_holds
end
