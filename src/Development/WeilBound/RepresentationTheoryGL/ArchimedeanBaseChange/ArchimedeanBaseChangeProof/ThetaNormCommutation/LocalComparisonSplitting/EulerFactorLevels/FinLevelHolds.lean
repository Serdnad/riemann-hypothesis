module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle583
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle584
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle574
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle565
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle573
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle602
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle595
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle655
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle638
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle666
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle617
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.PUnitAE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

namespace PositivityTheory.Rg.BcB.G8.Fin

theorem kfOC_holds : PositivityTheory.Rg.BcB.G8.KfOC := GlobalTheory.T.finite_kernel_compact_open

theorem finLevel_holds : PositivityTheory.Rg.BcB.G8.FinLevel := GlobalTheory.T.finite_level_facts

theorem suppFin_holds : SuppFin := GlobalTheory.T.finite_support_of_twist GlobalTheory.T.local_support_facts unitAE_holds GlobalTheory.T.rational_finite_places GlobalTheory.T.local_good_reduction

theorem eulerFin_holds : EulerFin :=
  GlobalTheory.T.finite_euler_product_of GlobalTheory.T.finite_conjugacy_exists GlobalTheory.T.finite_restriction_vanishing GlobalTheory.T.aux_statement_21 (GlobalTheory.T.local_comparison_of GlobalTheory.T.local_comparison_inert GlobalTheory.T.local_comparison_split) GlobalTheory.T.local_hypotheses_hold GlobalTheory.T.finite_reindexing

theorem finHalf_holds : PositivityTheory.Rg.BcB.G8.FinHalf :=
  GlobalTheory.T.finite_half_of_twist DcCount_pf GlobalTheory.T.finite_mass_product_formula GlobalTheory.T.rational_finite_places suppFin_holds eulerFin_holds kfOC_holds finLevel_holds

end PositivityTheory.Rg.BcB.G8.Fin
