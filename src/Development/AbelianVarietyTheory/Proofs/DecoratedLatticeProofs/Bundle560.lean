module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowOfSiegelWeilUnitary
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle521
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle551
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle559
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle532
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle520
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixEntryNormSumUpperRightBlockElementPLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle612
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle642
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle680
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeCoefficientsSqIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimeToHostCore
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle651
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.diagonalRow_of_siegelWeil_unitary :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
      GlobalTheory.Core.Rk.RowDiag (fun D L C' =>
        GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) :=
  GlobalTheory.Core.Rk.rowDiag_of_siegelWeilUnitary
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem placeLaws_finiteIntegrals : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c)
    (w : ∀ s, VTup (t s)), c.Is → c.VolLast → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) →
    (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  intro D c v 𝒯 t w hc hvl hv ht hp
  refine ⟨fun s => ?_, ?_, ?_⟩
  · exact GlobalTheory.T.locally_finite_of_tuple_conditions D c v (t s) (w s) hc hv (ht s) (hp s).form (hp s).off (hp s).gs (hp s).qfin
  · exact GlobalTheory.T.seeSaw_finiteIntegrals_doubleStep_value D c v 𝒯 t w hc hv ht hp (GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D) (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.seeSawWeilBiAction_commutes D)
  · exact GlobalTheory.T.seeSawLastTwoSteps_doubleLiftPeriod_value D c v 𝒯 t w hc hvl hv ht hp (GlobalTheory.Unf.LastSteps.lastLaw D) (GlobalTheory.T.lastSeeSaw_thetaIdentity D)
      (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.seeSawWeilBiAction_commutes D)

end GlobalTheory.SeeSaw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSawIteratedIntegralLawLastSteps_of_localFactorisation : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → QLast v w := by
  first | exact @GlobalTheory.QLastPf.qLast_of_pin | exact GlobalTheory.QLastPf.qLast_of_pin | (intros; apply GlobalTheory.QLastPf.qLast_of_pin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.fourierJacobi_period_unfolding_of_witt_descent : ∀ D : D7, Descent D → UnfFB D := by
  first | exact @GlobalTheory.Unf.unfFB_of_descent | exact GlobalTheory.Unf.unfFB_of_descent | (intros; apply GlobalTheory.Unf.unfFB_of_descent <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalDatum_foldr_local_combinations : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P₀ Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ) (PPn : Fin n → Formalism.L2.DIV.Pl D.host.E), Function.Injective PPn → (∀ PP, PP ∈ Q ↔ ∃ i, PPn i = PP) → Disjoint P₀ Q → ∀ (c : Fin n → WO S T →₀ ℂ) (Ξl : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ), (∀ i, GlobalTheory.LocMod.IsLocFac D ψ S T (PPn i) (c i) (Ξl i)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → (∀ e₀, IsIdemSum e₀ P₀ → IsRatDatum ψ S T e₀ Ξ f₀ f) → ∀ e, IsIdemSum e (P₀ ∪ Q) → IsRatDatum ψ S T e (fun γ => Ξ γ * ∏ i, Ξl i γ) f₀ ((List.finRange n).foldr (fun i g => comb ψ S T (c i) g) f) := by
  first | exact @GlobalTheory.LocComb.ratDatum_foldr_comb | exact GlobalTheory.LocComb.ratDatum_foldr_comb | (intros; apply GlobalTheory.LocComb.ratDatum_foldr_comb <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AFormL

theorem aFormL : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → ∀ SF, GlobalTheory.Hk3.IsSF R SF → AForm R SF := by
  intro hDS hHC hCusp hWS hSE hUD hBZ D G _ _ Pl0 T A Ks _ _ _ R F hG hc SF hSF
  have hHM := GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral
  have hPM := GlobalTheory.PlaceTensor.placeModels D
  exact GlobalTheory.LiftScalarL.aForm R F
    (GlobalTheory.T.finiteDatum_sourceLevelCharacter_law GlobalTheory.SingleBlock.localIntegralSingleBlock R F hPM)
    (GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses hCusp hWS hSE R F hG.params)
    (GlobalTheory.T.fockVector_matrixCoefficient_formula hHM R F hPM)
    (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue hCusp hBZ hUD R F)
    (GlobalTheory.T.thetaLevelIndex_mul_schwartzNorm_formula GlobalTheory.SingleBlock.localIntegralSingleBlock R F hPM)
    (GlobalTheory.RealCoefSq.lowestKType_coefficients_sq_integrable R F hG.core)
    hG hc SF hSF

end GlobalTheory.AFormL

end
end
