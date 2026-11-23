module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.AdmissibleOf
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.ArchimedeanDenseStabilizers.StabOfMemLevelOpen
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle071
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DefinitenessStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StTensor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CompanionTheory.Rg.Fl.B

theorem stFrame : CompanionTheory.Rg.FlB.StFrame :=
  GlobalTheory.T.frame_of_anisotropic_plane_splitting (GlobalTheory.T.anisotropic_of_hensel_and_sandwich GlobalTheory.T.HenselStatement GlobalTheory.T.SandwichStatement) (GlobalTheory.T.plane_of_hensel_and_pairing GlobalTheory.T.HenselStatement (GlobalTheory.T.pairing_of_sandwich_statement GlobalTheory.T.SandwichStatement))
    (GlobalTheory.T.splitting_of_sandwich_and_pairing GlobalTheory.T.SandwichStatement (GlobalTheory.T.pairing_of_sandwich_statement GlobalTheory.T.SandwichStatement))

theorem stCartanU : StCartanU :=
  GlobalTheory.T.isometric_lattice_congruence_subgroups GlobalTheory.T.DeltaStatement (GlobalTheory.T.existence_of_sandwich_statement GlobalTheory.T.SandwichStatement) stFrame GlobalTheory.T.TorusStatement (GlobalTheory.T.decomposition_of_frame_witt_torus stFrame GlobalTheory.T.WittStatement GlobalTheory.T.TorusStatement)
    GlobalTheory.T.IwahoriStatement GlobalTheory.T.lattice_congruence_subgroups_open_compact

theorem locPI : LocPI :=
  locPI_of (GlobalTheory.T.simple_of_commutative_statement GlobalTheory.T.StatementCommutative) GlobalTheory.T.StatementStar GlobalTheory.T.HeckeAlgebraTheorem GlobalTheory.T.ModularityStatement GlobalTheory.T.TransferStatementBis GlobalTheory.T.PairingStatement stCartanU GlobalTheory.T.CartanDecompositionGL
    GlobalTheory.T.MovingStatement GlobalTheory.T.DictionaryStatement GlobalTheory.T.DefinitenessStatement CompanionTheory.Rg.FlSep.stSepDefB GlobalTheory.T.SeparatedMovingStatement

theorem unitaryIrreducibleAdmissible : GlobalTheory.Published.UnitaryIrreducibleAdmissible := admissible_of locPI GlobalTheory.T.ProjectionStatement

theorem flathTensorProduct : GlobalTheory.Published.FlathTensorProduct :=
  flath_of locPI GlobalTheory.T.ProjectionStatement GlobalTheory.T.FixedVectorStatement GlobalTheory.T.FactorizationStatement GlobalTheory.T.ArchimedeanPrincipalSeries GlobalTheory.T.IsomorphismStatement GlobalTheory.T.OperatorStatement GlobalTheory.T.stTensor'

end CompanionTheory.Rg.Fl.B
