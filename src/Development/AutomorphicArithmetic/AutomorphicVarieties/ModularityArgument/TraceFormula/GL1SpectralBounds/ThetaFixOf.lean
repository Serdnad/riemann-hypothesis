module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.ThetaFixTop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PMultC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MultiplicityOneRigidity.GelfandKazhdanDualOfRigidity
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem phi_rat : PhiU n (Ad E) = ratGL E n (PhiU n E) :=
  (GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU (algebraMap E (Ad E)) n).symm

private theorem phi_split : PhiU n (Ad E) = GlobalTheory.CsdFromConj.phiG E n := by
  refine ga_ext ?_ ?_
  · simp [GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CsdFromConj.toUnits_PhiK, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]
  · simp [GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]

private theorem rt_phi_mem (π : CuspSub E n) {φ : Sm E n} (hφ : φ ∈ π.V) : rt E n (PhiU n (Ad E)) φ ∈ π.V := by
  have h := (GlobalTheory.CsdFromConj.phiEquiv π ⟨φ, hφ⟩).2
  rw [phi_split, GlobalTheory.CsdFromConj.rt_phiG]
  exact h

private theorem iso_theta {P : CuspSub E n} (h : P.IsCsd) : (GlobalTheory.ThetaPull.thetaSub P).Iso P := by
  apply _root_.theta_iso <;> assumption

theorem UpperTheory.V.Z.Tf.GOne.thetaFixOf :
    PositivityTheory.Rg.BcB.Desc.ThetaFixOf :=
  _root_.DiscreteGroups.T1.G.thetaFixOf

end
