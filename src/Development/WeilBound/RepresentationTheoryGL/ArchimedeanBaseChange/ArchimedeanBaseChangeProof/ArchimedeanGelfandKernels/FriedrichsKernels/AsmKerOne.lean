module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle269
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle438
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle274
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle268
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle275
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle525
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle250
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle232
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.AsmKerOneOfSteps
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

@[expose] public section

namespace PositivityTheory.RgBcC.Fc

open PositivityTheory.RgBcC

theorem calcSteps : CalcSteps :=
  ⟨GlobalTheory.T.absolute_fourier_coefficients, GlobalTheory.T.absolute_cutoff_bound, GlobalTheory.T.functional_calculus_curve, GlobalTheory.CompanionTheory.WaveFc.wvAlg, GlobalTheory.T.closure_operator_facts, GlobalTheory.T.sobolev_operator_facts, GlobalTheory.T.compact_sobolev_embedding,
    GlobalTheory.T.section_norm_bound, GlobalTheory.T.sobolev_space_preserved, GlobalTheory.T.concentration_time_bound, GlobalTheory.T.functional_calculus_joint_curve, GlobalTheory.T.friedrichs_extension_facts, GlobalTheory.T.casimir_operator_formula, GlobalTheory.T.sobolev_integration_by_parts,
    GlobalTheory.T.dense_domain_facts⟩

theorem asmCpt : AsmCpt :=
  GlobalTheory.T.functional_calculus_first_assumption GlobalTheory.T.absolute_fourier_coefficients GlobalTheory.T.absolute_cutoff_bound GlobalTheory.T.functional_calculus_curve GlobalTheory.CompanionTheory.WaveFc.wvAlg GlobalTheory.T.closure_operator_facts GlobalTheory.T.sobolev_operator_facts GlobalTheory.T.compact_sobolev_embedding
    GlobalTheory.T.section_norm_bound GlobalTheory.T.sobolev_space_preserved GlobalTheory.T.concentration_time_bound GlobalTheory.T.functional_calculus_joint_curve GlobalTheory.T.friedrichs_extension_facts GlobalTheory.T.casimir_operator_formula GlobalTheory.T.sobolev_integration_by_parts GlobalTheory.T.dense_domain_facts

theorem asmKerOne : AsmKerOne :=
  asmKerOne_of_steps asmCpt calcSteps GlobalTheory.T.smooth_operator_facts GlobalTheory.T.paley_wiener_decay GlobalTheory.T.kernel_regularity GlobalTheory.T.kernel_localization GlobalTheory.T.kernel_weight_facts

end PositivityTheory.RgBcC.Fc
