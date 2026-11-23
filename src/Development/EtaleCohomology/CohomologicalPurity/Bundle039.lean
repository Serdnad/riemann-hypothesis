module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle004
public import Development.EtaleCohomology.CohomologicalPurity.Bundle037
public import Development.EtaleCohomology.CohomologicalPurity.Bundle032
public import Development.EtaleCohomology.CohomologicalPurity.Bundle008
public import Development.EtaleCohomology.CohomologicalPurity.Bundle034
public import Development.EtaleCohomology.CohomologicalPurity.Bundle010
public import Development.EtaleCohomology.CohomologicalPurity.Bundle011
public import Development.EtaleCohomology.CohomologicalPurity.Bundle021
public import Development.EtaleCohomology.CohomologicalPurity.Bundle020
import Development.EtaleCohomology.CohomologicalPurity.Bundle031
public import Development.EtaleCohomology.CohomologicalPurity.Bundle028
public import Development.EtaleCohomology.CohomologicalPurity.Bundle009
public import Development.EtaleCohomology.CohomologicalPurity.Bundle018
public import Development.EtaleCohomology.CohomologicalPurity.OffContBasicPfR
public import Development.EtaleCohomology.CohomologicalPurity.Bundle033
public import Development.EtaleCohomology.CohomologicalPurity.Bundle038
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

theorem LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of : LateralTheory.CohomologicalPurity.LeafAW :=
  LateralTheory.CohomologicalPurity.LeafAWCut.goal_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec
end

section

namespace LateralTheory.Fix.LeafIndExc
open LateralTheory.CohomologicalPurity

theorem bd : LeafBd :=
  Bd.goal_of Bd.LeafMono_of Bd.LeafPush_of Bd.LeafGood_of Bd.LeafDelta_of Bd.LeafExact_of
    (Bd.LeafImg_of (Bd.LeafImgHom_of Bd.LeafGen_of))

theorem exc : LeafExc :=
  LeafExc_of (LeafExcFormal_of EtaleExcIdent LeafExcDeg_of)
    (LeafExcSheaf_of (LeafFreeCok_of_inj LeafFreeCokInj_of) LeafSurjGeo_of LeafInjGeo_of)

theorem offCont : LeafOffCont :=
  leafOffCont_of offContBasic_of (etale_purity_continuity_off_closed_of_local_and_chase OffContLoc_of OffChaseGeo_full)

theorem intersectionNumber_baseChange : LeafIndExc :=
  leafIndExc_of (leafNbhdExc_of exc) (leafHsCont_of' bd exc offCont)

end LateralTheory.Fix.LeafIndExc
end
