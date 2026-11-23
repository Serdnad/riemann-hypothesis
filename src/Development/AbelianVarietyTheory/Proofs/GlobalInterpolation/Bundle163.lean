module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle012
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle140
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle152
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle162
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle147
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.kernelJets_levelPlace_integralMoments : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments := by
  first | exact @GlobalTheory.MomTop.jetMoments | exact GlobalTheory.MomTop.jetMoments | (intros; apply GlobalTheory.MomTop.jetMoments <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView : ∀ (R : ∀ D : D7, Obj D → Prop), (∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)) (nch : NChoice (w.D Z)), ColView w Z O.ex.tw nch → GlobalTheory.LvT.WtSign.BaseSigns B → Formalism.L2.Theta.RealTied (w.D Z) → R (w.D Z) O) → ∀ (K : Ctx) (β : BPt K), β.Is HasCols → R β.D β.O := by
  first | exact @GlobalTheory.Fc.Cv.view_at_built | exact GlobalTheory.Fc.Cv.view_at_built | (intros; apply GlobalTheory.Fc.Cv.view_at_built <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem volSigIndep_and_classItemsAt_of_massRatioUnderVolume (hU : ∀ D : D7, Formalism.MainNotions.RT.MassRatioUnderVolume D) :
    ∀ D : D7, VolSigIndep D ∧ ClassItemsAt D (D.sp.Y 0).rank := by
  intro D
  refine ⟨?_, GlobalTheory.T.hermitianClassNumberItems_all_ranks D _⟩
  have key := GlobalTheory.T.adelicQuotientVolume_eq_of_signature_rank_indep (fun D hT W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr => by
    have h2 : Conclusion2 D := volumeMass_of_unfolding D (hU D hT)
    rw [GlobalTheory.T.unitary_volume_eq_rank_mass_all_signatures D hT h2 W P Q hW hs, GlobalTheory.T.unitary_volume_eq_rank_mass_all_signatures D hT h2 W₀ P₀ Q₀ hW₀ hs₀]
    have e1 := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    have e2 := Formalism.BasicNotions.sig_sum W₀ hW₀ D.host.φ₀
    rw [hs] at e1
    rw [hs₀] at e2
    simp only at e1 e2
    rw [e1, e2, hr])
  exact key D

end GlobalTheory.Glob
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ

theorem twistedPointIntegral_of_TC_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), Formalism.L2.G.Adm2InU.TwistedPointIntegral (I.rec7 l Z) (I.tw l l0 Z) := by
  intro B X I hI l Z l0 u μ _ _
  exact Formalism.MainNotions.DIV.HookProducts.AdmPtTw.lowerTieTwAt_integral
    (GlobalTheory.T.lowerTwistedCompatible_of_evaluationBranching _ _ u μ (GlobalTheory.T.twistedEvaluation_branching_all_tuples_trueColumns I hI l Z l0 u μ))

end GlobalTheory.PerQ
end

end

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.volume_signature_indep_and_classNumberItems : (∀ D : D7, Formalism.MainNotions.RT.MassRatioUnderVolume D) → ∀ D : D7, VolSigIndep D ∧ ClassItemsAt D (D.sp.Y 0).rank := by
  first | exact @GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume | exact GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume | (intros; apply GlobalTheory.Glob.volSigIndep_and_classItemsAt_of_massRatioUnderVolume <;> assumption)

end
end
