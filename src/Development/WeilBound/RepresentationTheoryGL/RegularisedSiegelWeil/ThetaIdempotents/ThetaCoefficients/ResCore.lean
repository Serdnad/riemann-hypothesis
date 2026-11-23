module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterQuadraticFormIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongrOverOfFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEqSmulOfInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendByZeroHermitianVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle725
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle751
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EisMeasTop
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.MuCellTop
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle021
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle019
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle009
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle017
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle027
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle025
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle022
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle023
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle016
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBound
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBdd
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThProd
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WMaj
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ProjKComm
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.SphBound
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.JPosOfIdemEx
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFT
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

theorem PositivityTheory.Rg.Rsw.resCore : PositivityTheory.Rg.Rsw.ResCore :=
  open PositivityTheory.Rg.Rsw in
  have i := PositivityTheory.Rg.Rsw.L.idemEx
  have ge := PositivityTheory.Rg.Rsw.L.goodEv i
  have be := PositivityTheory.Rg.Rsw.L.bumpEx i
  have wm := PositivityTheory.Rg.Rsw.L.wMaj
  have tp := PositivityTheory.Rg.Rsw.L.thProd wm
  have rt := PositivityTheory.Rg.Rsw.L.rowTotal i be
  have fw := PositivityTheory.Rg.Rsw.L.fixW i PositivityTheory.Rg.Rsw.L.genK wm
  have ns := PositivityTheory.Rg.Rsw.L.nullSing i
  have t2 := GlobalTheory.CompanionTheory.ColumnSplitting.main i PositivityTheory.Rg.Rsw.L.latBound GlobalTheory.CompanionTheory.QKAvg.qk PositivityTheory.Rg.Rsw.L.ikSch
  have em := PositivityTheory.Rg.Rsw.Em.eisMeas i be (PositivityTheory.Rg.Rsw.L.major i ge be) fw (PositivityTheory.Rg.Rsw.L.fixTh i PositivityTheory.Rg.Rsw.L.geng PositivityTheory.Rg.Rsw.L.genK) tp (PositivityTheory.Rg.Rsw.Cell.muCell htExist i)
    PositivityTheory.Rg.Rsw.L.fibEx (GlobalTheory.CompanionTheory.RCellP.rcell wm PositivityTheory.Rg.Rsw.L.partFT) PositivityTheory.Rg.Rsw.L.posExt (PositivityTheory.Rg.Rsw.L.approxId i)
  have mi := PositivityTheory.Rg.Rsw.L.muId i ge be tp em ns (GlobalTheory.CompanionTheory.OrbUniq.uniq_of_trans i ns (GlobalTheory.CompanionTheory.RgTrans.idemEx_trans i)) (GlobalTheory.CompanionTheory.RswNoFrame.noFrame i) t2 (PositivityTheory.Rg.Rsw.L.toS i)
  have ci := GlobalTheory.CompanionTheory.RkCoef.target polar resMu mapsExist cfFJ pcBound pcFc rSec htExist tp rt wm PositivityTheory.Rg.Rsw.L.ikSch t2 mi
  have tb := PositivityTheory.Rg.Rsw.L.thBdd wm PositivityTheory.Rg.Rsw.L.latBound PositivityTheory.Rg.Rsw.L.wa1
  have cl := PositivityTheory.Rg.Rsw.L.cutLow PositivityTheory.Rg.Rsw.L.fourierPt PositivityTheory.Rg.Rsw.L.wa1
  have ie := (fun _ _ _ => PositivityTheory.Rg.Rsw.L.ikEq2 : PositivityTheory.Rg.Rsw.L.GenG → PositivityTheory.Rg.Rsw.L.WMaj → PositivityTheory.Rg.Rsw.L.IkSch → PositivityTheory.Rg.Rsw.L.IkEq) PositivityTheory.Rg.Rsw.L.geng wm PositivityTheory.Rg.Rsw.L.ikSch
  have tc := PositivityTheory.Rg.Rsw.L.thCoef PositivityTheory.Rg.Rsw.L.latBound
  PositivityTheory.Rg.Rsw.L.resCore polar cfFJ i ge fw wm (GlobalTheory.CompanionTheory.Jp.jPos_of_idemEx i) (PositivityTheory.Rg.Rsw.L.cfRel htExist) PositivityTheory.Rg.Rsw.L.cfInv cl
    (PositivityTheory.Rg.Rsw.L.cutId polar cfFJ ci tc PositivityTheory.Rg.Rsw.L.fourierPt PositivityTheory.Rg.Rsw.L.wa1 PositivityTheory.Rg.Rsw.L.cfInv tb cl PositivityTheory.Rg.Rsw.L.ikSch ie wm) tb tc PositivityTheory.Rg.Rsw.L.ikSch ie
