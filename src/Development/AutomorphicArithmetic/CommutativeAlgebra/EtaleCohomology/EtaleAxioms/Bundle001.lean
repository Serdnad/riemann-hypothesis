module

public import Development.EtaleCohomology.EtaleSheaves.Bundle018
public import Development.EtaleCohomology.EtaleSheaves.Bundle010
public import Development.EtaleCohomology.EtaleSheaves.Bundle030
public import Development.EtaleCohomology.EtaleSheaves.Bundle017
public import Development.EtaleCohomology.EtaleSheaves.Bundle012
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle026
import Development.EtaleCohomology.EtaleSheaves.Bundle046
import Development.EtaleCohomology.EtaleSheaves.Bundle019
import Development.EtaleCohomology.EtaleSheaves.Bundle034
import Development.EtaleCohomology.EtaleSheaves.Bundle011
import Development.EtaleCohomology.EtaleSheaves.Bundle015
import Development.EtaleCohomology.EtaleSheaves.Bundle016
import Development.EtaleCohomology.EtaleSheaves.Bundle022
import Development.EtaleCohomology.EtaleSheaves.Bundle023
public import Development.EtaleCohomology.EtaleSheaves.Bundle031
import Development.EtaleCohomology.EtaleSheaves.Bundle032
import Development.EtaleCohomology.EtaleSheaves.TorSecPf
public import Development.EtaleCohomology.EtaleSheaves.Bundle044
import Development.EtaleCohomology.EtaleSheaves.CechLevels.Cech0Iso
public import Development.EtaleCohomology.EtaleSheaves.Bundle055
import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.LevelsGenOfSpecLim
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

section

namespace UpperTheory.Et.QuasiAffineEquivalence

theorem a0 : LateralTheory.E.t_E1Cut.QAClosed := LateralTheory.E.QAClosedPf.QAClosed_of
theorem a1 : LateralTheory.E.ZarLocalPf.LocSH := LateralTheory.E.LocSHPf.LocSH_of
theorem a2 : LateralTheory.E.ZarLocalPf.LocDiag := LateralTheory.E.LocDiagPf.LocDiag_of
theorem a3 : LateralTheory.E.t_E1Cut.ZarLocal := LateralTheory.E.ZarLocalPf.ZarLocal_of a1 a2
theorem a4 : LateralTheory.E.MVPf.MVSpc := LateralTheory.E.LeafMVVanishPf.mvSpc
theorem a5 : LateralTheory.E.MVPf.StdCover := LateralTheory.E.MVPf.StdCover_of
theorem a6 : LateralTheory.E.MVPf.StdPB := LateralTheory.E.MVPf.StdPB_of
theorem a7 : LateralTheory.E.t_E1Cut.MV := LateralTheory.E.t_E1Cut.MV_of a4 a5 a6
theorem a8 : LateralTheory.E.LocallyConstantH0.LCMap := LateralTheory.E.LCMapPf.LCMap_of
theorem a9 : LateralTheory.E.LCBijPf.TwGenNZAC := LateralTheory.E.TwGenNZACPf.TwGenNZAC_of
theorem a10 : LateralTheory.E.LCSurjPf.LocForm := LateralTheory.E.LocFormPf.LocForm_of
theorem a11 : LateralTheory.E.LCSurjPf.Descent := LateralTheory.E.DescentPf.Descent_of a9
theorem a12 : LateralTheory.E.LCBijPf.LCSurj := LateralTheory.E.LCSurjPf.LCSurj_of a10 a11
theorem a13 : LateralTheory.E.LocallyConstantH0.LCBij := LateralTheory.E.LCBijPf.LCBij_of a9 a12
theorem a14 : LateralTheory.E.t_E1Cut.EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions := LateralTheory.E.LocallyConstantH0.localConstant_H0 a8 a13
theorem a15 : LateralTheory.E.t_E1Cut.EtLift := LateralTheory.E.EtLiftPf.EtLift_of
theorem a16 : LateralTheory.E.EtAICPf.Split := fun T C _ _ _ _ _ h => UpperTheory.exists_orthogonalIdempotents_isDomain_of_etale T C h
theorem a17 : LateralTheory.E.EtAICPf.DomOpen := LateralTheory.E.DomOpenPf.DomOpen_of
theorem a18 : LateralTheory.E.t_E1Cut.EtAIC := LateralTheory.E.EtAICPf.EtAIC_of a16 a17
theorem a19 : LateralTheory.E.FinEtSectionPf.Pieces := LateralTheory.E.PiecesPf.Pieces_of a15 a18
theorem a20 : LateralTheory.E.FinEtSectionPf.FinOpen := LateralTheory.E.FinOpenPf.FinOpen_of
theorem a21 : LateralTheory.E.FinEtSectionPf.Glue := LateralTheory.E.Gluing₂.Glue_of a15 a18
theorem a22 : LateralTheory.E.t_E1Cut.FinEtSection := LateralTheory.E.FinEtSectionPf.FinEtSection_of a15 a18 a19 a20 a21
theorem a23 : LateralTheory.E.TorEtPf.ProjF := LateralTheory.E.ProjFPf.projF
theorem a24 : LateralTheory.E.TorEtPf.ProjG := LateralTheory.E.ProjGPf.ProjG_of
theorem a25 : LateralTheory.E.LCSplitPf.TorEt := LateralTheory.E.TorEtPf.TorEt_of_proj a23 a24
theorem a26 : LateralTheory.E.LCSplitPf.TorSec := LateralTheory.E.TorSecPf.TorSec_of
theorem a27 : LateralTheory.E.t_E1Cut.LCSplit := LateralTheory.E.LCSplitPf.LCSplit_of_tor a22 a25 a26
theorem a28 : LateralTheory.E.AcycQAPf.Deg0 := LateralTheory.E.Deg0Pf.Deg0_of
theorem a29 : LateralTheory.E.CoverPf.EmptyVan := LateralTheory.E.EmptyVan₂.EmptyVan_of
theorem a30 : LateralTheory.E.AcycQAPf.Cover := LateralTheory.E.CoverPf.Cover_of a29
theorem a31 : LateralTheory.E.t_E1Cut.AcycQA := LateralTheory.E.AcycQAPf.AcycQA_of a0 a3 a7 a14 a27 a28 a30
theorem a32 : LateralTheory.E.t_E1Cut.LCGood := LateralTheory.E.LCGoodPf.LCGood_of
theorem a33 : LateralTheory.E.t_E1Cut.EqvQA := LateralTheory.E.t_E1Cut.EqvQA_of a31 a0 a14 a32

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.EqvQA := a33

end UpperTheory.Et.QuasiAffineEquivalence
end

section

namespace UpperTheory.Et.CechLevelsEtaleAxioms

theorem a0 : LateralTheory.E.LevelsGenPf.SpecLim := LateralTheory.E.SpecLimPf.SpecLim_of
theorem a1 : LateralTheory.E.LevelsPf.LevelsGen := LateralTheory.E.LevelsGenPf.LevelsGen_of_specLim a0
theorem a2 : LateralTheory.E.CechLevelsPf.Levels := LateralTheory.E.LevelsPf.Levels_of_gen a1
theorem a3 : LateralTheory.E.t_E1Cut.CechLevels := LateralTheory.E.CechLevelsPf.CechLevels_of' a2

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.CechLevels := a3

end UpperTheory.Et.CechLevelsEtaleAxioms
end
