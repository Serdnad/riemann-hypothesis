module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.LinearFormDegree.InvFun
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActPf
public import Mathlib.Data.Finsupp.Notation
public import Mathlib.RingTheory.MvPowerSeries.Substitution
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace DegreeOneCoeffSubstitution
open MvPowerSeries Finsupp

private lemma deg_one {σ : Type} [DecidableEq σ] (d : σ →₀ ℕ) (h : d.degree = 1) :
    ∃ s, d = Finsupp.single s 1 := by
  apply _root_.ReciprocityTheory.ChartRestriction.G.LF.InvFun.eq_single_of_degree_eq_one <;> assumption

end DegreeOneCoeffSubstitution

open MvPowerSeries Finsupp in
theorem UpperTheory.Reformulated.B.LinearTermOfSubstitution.main :
    ∀ {S : Type}
    [inst : CommRing S] {σ τ : Type} [inst_1 : Fintype σ] [DecidableEq σ] [DecidableEq τ] (a : σ → MvPowerSeries τ S),
    (∀ (s : σ), (MvPowerSeries.constantCoeff : MvPowerSeries τ S → S) (a s) = (0 : S)) →
      ∀ (f : MvPowerSeries σ S) (t : τ),
        (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (MvPowerSeries.subst a f) =
          ∑ s : σ,
            (MvPowerSeries.coeff fun₀ | s => (1 : ℕ) : MvPowerSeries σ S → S) f *
              (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (a s) := @_root_.Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf.coeff_single_subst
