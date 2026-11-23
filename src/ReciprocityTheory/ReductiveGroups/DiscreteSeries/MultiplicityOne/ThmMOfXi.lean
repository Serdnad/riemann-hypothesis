module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle004
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.InHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle012
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeHerm
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle011
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JMixed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRankOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle013
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle010
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSmooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSymBeta
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle014
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UuInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem thmM_of_xi (h : UnitaryGroupStructuralFacts) (hXi : Formalism.FourierDecayAlt.B.XiExists) : ThmM :=
  theoremM_of h hXi (stBeHerm h) (stBePos h) (stSchurW h) (stSInt h) stSchurG (stPairs h) (stBeConv h) (stBeEquiv h)
    (stRepro h) (stSmooth h) stFrame (stInvGroup h) stInvChar stInvCC (stReps h) (stTransM h) (stSym h) (stSymBeta h)
    (stBetaInf h) (stDichoG h) (stDichoW h) (stMixed h) rankOneMinors

theorem thmM : ThmM := thmM_of_xi multiplicity_one_hypotheses_hold ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end ReciprocityTheory.ChartRestriction.DS.Mult1
