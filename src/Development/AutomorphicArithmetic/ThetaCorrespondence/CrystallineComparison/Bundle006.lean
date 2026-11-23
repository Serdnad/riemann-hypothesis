module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Bundle004
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.Bundle001
public import Development.WeilBound.CoreStatements.PeriodRingComparison.PadicPeriodAlgebraMaps.CPAlgebraMapPadic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Bundle001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Bundle005
public import Development.WeilBound.CoreStatements.PeriodRingComparison.ThetaKernelDeRham.KerThetaEqSpanSymmTBdR
import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Bundle003
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
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
import Mathlib.Tactic.Linter.Style
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

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem comparison_toBdRPlus (x : Reformulated.AutPerF.Acris l (Cmp6.OC l)) :
    Cmp6.cP l (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l) x) = ACris.iota ℂ_[l] l (Cmp6.cA l x) := by
  have h := eq_toBdRPlus_of_bounded (jOC l) (jOC_zero l) (jOC_bounded l)
  rw [← h]
  show Cmp6.cP l ((Cmp6.cP l).symm (iotaP l (Cmp6.cA l x))) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

end Formalism.BasicNotions.CmpTie.Incl
end
end

section

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem incl_native
    (hι : ∀ x : Reformulated.AutPerF.Acris l (Cmp6.OC l),
      Cmp6.cP l (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l) x) = ACris.iota ℂ_[l] l (Cmp6.cA l x))
    (f : Reformulated.AutPerF.Bcris l (Cmp6.OC l) →+* Reformulated.AutPerF.BdR l (Cmp6.OC l)) :
    IsCrisDRF f ↔ Formalism.Per6.IsCrisDR l (((Cmp6.cD l).toRingHom.comp f).comp (Cmp6.cBc l).symm.toRingHom) := by
  rw [isCrisDRF_iff, ← isCrisDRA_toBdRPlus_iff]
  exact isCrisDRA_iff (Cmp6.cA l) (Cmp6.cBc l) (Cmp6.cP l) (Cmp6.cD l) (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l))
    (fun x => Cmp6.cBc_algebraMap l x) (fun y => Cmp6.cD_algebraMap l y) hι f

end Formalism.BasicNotions.CmpTie.Incl
end
end

section

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

def castCrystalline (l : ℕ) [Fact l.Prime] : Per.Bcris l ≃+* Reformulated.AutPerF.Bcris l (Cmp6.OC l) := RingEquiv.refl _
def castDeRham (l : ℕ) [Fact l.Prime] : Per.BdR l ≃+* Reformulated.AutPerF.BdR l (Cmp6.OC l) := RingEquiv.refl _
def castDeRhamPlus (l : ℕ) [Fact l.Prime] : Per.BdRp l ≃+* Reformulated.AutPerF.BdRPlus l (Cmp6.OC l) := RingEquiv.refl _

abbrev equivCrystalline (l : ℕ) [Fact l.Prime] : Per.Bcris l ≃+* Per6.Bcris l := (castCrystalline l).trans (Cmp6.cBc l)
abbrev equivDeRham (l : ℕ) [Fact l.Prime] : Per.BdR l ≃+* Per6.BdR l := (castDeRham l).trans (Cmp6.cD l)
abbrev equivDeRhamPlus (l : ℕ) [Fact l.Prime] : Per.BdRp l ≃+* Per6.BdRp l := (castDeRhamPlus l).trans (Cmp6.cP l)

end Formalism.BasicNotions.CmpTie
end
end
