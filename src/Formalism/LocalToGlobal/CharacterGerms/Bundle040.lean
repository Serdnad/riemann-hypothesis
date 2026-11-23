module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Formalism.LocalToGlobal.CharacterGerms.Bundle029
public import Formalism.LocalToGlobal.CharacterGerms.RankMaximalSelfCore
public import Formalism.LocalToGlobal.CharacterGerms.Bundle019
public import Formalism.LocalToGlobal.CharacterGerms.Bundle038
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf
public import Formalism.LocalToGlobal.CharacterGerms.MmOfUnitMul
public import Formalism.LocalToGlobal.CharacterGerms.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Formalism.LocalToGlobal.CharacterGerms.Bundle005
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle068

@[expose] public section

section

set_option autoImplicit false

namespace Formalism.L2.FormalSeriesBounds

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem descent_holds : DescentSt Xo c :=
  GlobalTheory.nuLocC_le_nuPlE_baseChange E H Dw l Xo c

end Formalism.L2.FormalSeriesBounds
end

section

namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_of_eig (hE : RowTiePKey.KeyEigSt) : PTSelfSt :=
  ptSelf_of_start2 (allStartSelf_of_eig hE)

end Formalism.L2.FormalSeriesBounds
end

section

set_option autoImplicit false

namespace Formalism.L2.FormalSeriesBounds

theorem noLinSelf_of (hAdj : ALinAdjSt) (hPL : ProjLieSelfSt) : NoLinSelfSt :=
  fun _ _ _ _ _ _ _ _ Y _ _ _ _ p g a0 u0 hu0 heig hV1 hc0 => noLin_self hAdj hPL Y p g a0 u0 hu0 heig hV1 hc0

theorem rank_maximal_self_of_projection (hV1 : FirstVanishingCore) (hFE : FunEqCoreSt) (hC0 : CurveLinearTermCondition) (hAdj : ALinAdjSt) (hPL : ProjLieSelfSt) :
    RankMaximalSelfOfNondegenerate :=
  rank_maximal_self_core hV1 hFE hC0 (noLinSelf_of hAdj hPL)

theorem rank_maximal_self_of_eigen (hV1 : FirstVanishingCore) (hFE : FunEqCoreSt) (hC0 : CurveLinearTermCondition) (hAdj : ALinAdjSt)
    (hE : RowTiePKey.KeyEigSt) : RankMaximalSelfOfNondegenerate :=
  rank_maximal_self_of_projection hV1 hFE hC0 hAdj (projLieSelf_of hE)

end Formalism.L2.FormalSeriesBounds
end
