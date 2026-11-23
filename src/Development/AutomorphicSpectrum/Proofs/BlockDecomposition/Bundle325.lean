module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentatives
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvalues
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalType
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftRapidDecay
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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


theorem _root_.GlobalTheory.T.hecke_coset_representatives : Ad3.R.C0 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant | exact GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant | (intros; apply GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant <;> assumption)
end

section


theorem _root_.GlobalTheory.T.newform_lift_conductor : Ad3.R.B0 → Ad3.R.F0b := by
  first | exact @GlobalTheory.CompanionTheory.NewformLiftConductor.f0b | exact GlobalTheory.CompanionTheory.NewformLiftConductor.f0b | (intros; apply GlobalTheory.CompanionTheory.NewformLiftConductor.f0b <;> assumption)
end

section


theorem _root_.GlobalTheory.T.newform_lift_fourier_coefficients : Ad3.R.B0 → Ad3.R.C1 → Ad3.R.U2 → Ad3.R.G0 → Ad3.R.G1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F2 → Ad3.R.F3 → Ad3.R.F5 → Ad3.R.F4 := by
  first | exact @GlobalTheory.CompanionTheory.RSEigen.abs_eigenvalue_sq | exact GlobalTheory.CompanionTheory.RSEigen.abs_eigenvalue_sq | (intros; apply GlobalTheory.CompanionTheory.RSEigen.abs_eigenvalue_sq <;> assumption)
end

section


theorem _root_.GlobalTheory.T.newform_lift_hecke_eigenvalues : Ad3.R.B0 → Ad3.R.C0 → Ad3.R.C1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.AutomorphicLevelEquivariance → Ad3.R.HeckeSumLocalTranslates → Ad3.R.F3 := by
  first | exact @GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift | exact GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift | (intros; apply GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift <;> assumption)
end

section


theorem _root_.GlobalTheory.T.newform_lift_level : Ad3.R.B0 → Ad3.R.F1 := by
  first | exact @GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists | exact GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists | (intros; apply GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists <;> assumption)
end

section


theorem _root_.GlobalTheory.T.newform_lift_level_character : Ad3.R.B0 → Ad3.R.AutomorphicLevelEquivariance := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance | exact GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance <;> assumption)
end

section


theorem _root_.GlobalTheory.T.newform_lift_local_type : Ad3.R.B0 → Ad3.R.HeckeSumLocalTranslates := by
  first | exact @GlobalTheory.CompanionTheory.RSq.f3a | exact GlobalTheory.CompanionTheory.RSq.f3a | (intros; apply GlobalTheory.CompanionTheory.RSq.f3a <;> assumption)
end

section


theorem _root_.GlobalTheory.T.newform_lift_rapid_decay : Ad3.R.B0 → Ad3.R.F5 := by
  first | exact @GlobalTheory.CompanionTheory.NewformLiftDecay.main | exact GlobalTheory.CompanionTheory.NewformLiftDecay.main | (intros; apply GlobalTheory.CompanionTheory.NewformLiftDecay.main <;> assumption)
end

section


theorem _root_.GlobalTheory.T.newform_lift_whittaker_expansion : Ad3.R.F2 := by
  first | exact @GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift | exact GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift | (intros; apply GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift <;> assumption)
end
