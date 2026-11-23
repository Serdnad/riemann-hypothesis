module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearCombinationLogBoundRealInequality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle102
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle080
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle078
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle065
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle087
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.NormBigOfNonvanishing
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TowerOfThetaMatching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle100
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

section
namespace GlobalTheory.RowClaim.JoinF
theorem joined_local_sum_estimates :
    _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK :=
  fun hP hK hM =>
    _root_.GlobalTheory.T.thetaLift_row_properties hP hK hM (_root_.GlobalTheory.T.twisted_theta_integral_converges hP.siegelSetUnitary hP)
      (_root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM) (_root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hM)
end GlobalTheory.RowClaim.JoinF
end

section

theorem _root_.GlobalTheory.T.local_sum_estimates_joined : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  first | exact @_root_.GlobalTheory.RowClaim.JoinF.joined_local_sum_estimates | exact _root_.GlobalTheory.RowClaim.JoinF.joined_local_sum_estimates | (intros; apply _root_.GlobalTheory.RowClaim.JoinF.joined_local_sum_estimates <;> assumption)
end
end

section

section
namespace GlobalTheory.SqTop
theorem square_top_term_joined_estimates : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.SqTop.Refl → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SqTop.DenSum ∧ GlobalTheory.SqTop.ThbSt ∧ GlobalTheory.SqTop.OneSqSt ∧ GlobalTheory.SqTop.BotSmall ∧ GlobalTheory.SqTop.BotNe ∧ GlobalTheory.SqTop.FieldDat ∧ GlobalTheory.SqTop.TorEx ∧ GlobalTheory.SqTop.DenEx ∧ GlobalTheory.SqTop.BotEx ∧ GlobalTheory.SqTop.LNe ∧ GlobalTheory.SqTop.TriEx ∧ GlobalTheory.SqTop.Tower := by
  intro hHD hPr hFE hTD hTr hZD hRefl hTI hLM
  have hS := GlobalTheory.T.completedHeckeL_bounded_in_vertical_strips
  have hInp := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied
  have hF : FieldDat := GlobalTheory.SqTop.fieldDat
  have hL : LNe := GlobalTheory.SqTop.lNe_of_functionalEquation hFE hS hF
  have hLB : LBound := GlobalTheory.T.heckeLValue_upperBound_permutedWeights_of_FE hFE hS hF
  have hTor : TorEx := GlobalTheory.ToricExist.torEx hTr hF hL
  have hBA : BetaArch := GlobalTheory.T.betaConjugate_mean_logAbs_bound_of_transport hTr hF hLB hTor
  have hDE : DenEx := GlobalTheory.DenExist.denEx hZD hF
  have hDS : DenSum := GlobalTheory.DenSumPf.denSum hZD hF
  have hThb : ThbSt := GlobalTheory.T.toricValueHeightBound_of_denominatorsMeans hTD hF hTor hDE hDS hBA
  have hBS : BotSmall := GlobalTheory.SqTop.BotSmallProof.botSmall_holds
  have hBC : BotConst := _root_.GlobalTheory.T.botConst_of_theta_matching hPr hTI hLM hInp hBS hL
  have hBE : BotEx := GlobalTheory.T.bottomPairs_exist_baseTuple hInp
  have hBET : BotExT := GlobalTheory.T.bottomPairsExistEveryTuple_of_cmThetaHypotheses hInp
  have hNB : NormBig := _root_.GlobalTheory.T.normBig_of_lNe hPr hInp hL
  have hRL : RhoLow := GlobalTheory.T.lValueRatio_lower_bound_gauge hTD hF hTor
  have hTri : TriEx := _root_.GlobalTheory.T.triEx_of_howe_duality_real hHD hPr hTI hLM hL
  have hBN : BotNe := _root_.GlobalTheory.T.bottomTheta_nonvanishing hPr hTI hLM hInp hL hBS hNB hTri
  have hTw : Tower := _root_.GlobalTheory.T.tower_of_theta_matching_lNe hPr hTI hLM hL
  have hOne : OneSqSt := GlobalTheory.T.square_ratio_valuation_without_norm_formula hInp hL hTor hBS hBET hNB hBN hTri hTw hBC hRefl hRL
  exact ⟨hDS, hThb, hOne, hBS, hBN, hF, hTor, hDE, hBE, hL, hTri, hTw⟩
end GlobalTheory.SqTop
end

section
theorem _root_.GlobalTheory.T.square_leading_term_bound : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.SqTop.Refl → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SqTop.DenSum ∧ GlobalTheory.SqTop.ThbSt ∧ GlobalTheory.SqTop.OneSqSt ∧ GlobalTheory.SqTop.BotSmall ∧ GlobalTheory.SqTop.BotNe ∧ GlobalTheory.SqTop.FieldDat ∧ GlobalTheory.SqTop.TorEx ∧ GlobalTheory.SqTop.DenEx ∧ GlobalTheory.SqTop.BotEx ∧ GlobalTheory.SqTop.LNe ∧ GlobalTheory.SqTop.TriEx ∧ GlobalTheory.SqTop.Tower := by
  first | exact @_root_.GlobalTheory.SqTop.square_top_term_joined_estimates | exact _root_.GlobalTheory.SqTop.square_top_term_joined_estimates | (intros; apply _root_.GlobalTheory.SqTop.square_top_term_joined_estimates <;> assumption)
end
end
