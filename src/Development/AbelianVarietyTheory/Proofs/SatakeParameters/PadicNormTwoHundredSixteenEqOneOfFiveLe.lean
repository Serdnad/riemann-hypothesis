module

import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
public import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementL
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMRead
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.FinalOfNRDense
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExistsUnitFactorizationBounded
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.HomotheticLatticeIntegralOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ExistsWittSeriesInverseFormalGroupIso
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepDict
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormHalfB2SubTwoTorsionLeOne

@[expose] public section

noncomputable section

namespace GlobalTheory.CurveDictionary

open NumberField Formalism.BasicNotions

theorem sgStar_lattice (L : PeriodPair) :
    Formalism.MainNotions.TaylorLogMetric.sgStar L.lattice.toAddSubgroup = Formalism.L2.Th1.F.sgStar L := by
  rw [GlobalTheory.OddTheta.sgStar_eq L L.lattice.toAddSubgroup (fun _ => Iff.rfl), GlobalTheory.Mem.Col2.ThetaVec.sgStar_eq]

theorem s2_in_unramified_closure (hTor : Formalism.L2.Th1.CM.CM4) (dK : ℕ) (L : PeriodPair) (hsq : Squarefree dK) (h4 : dK % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (l : ℕ) [Fact l.Prime] (hl5 : 5 ≤ l) (hld : ¬ l ∣ dK)
    (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]) (hlam : lam ≠ 0)
    (k2 : lam ^ 4 * ι L.g₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l) (k3 : lam ^ 6 * ι L.g₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l)
    (n2 : ‖lam ^ 4 * ι L.g₂‖ ≤ 1) (n3 : ‖lam ^ 6 * ι L.g₃‖ ≤ 1)
    (nd : ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1) :
    lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  have hlp : l.Prime := Fact.out
  have hd0 : 0 < dK := by omega
  obtain ⟨S, hS, -, -, hsum⟩ := Formalism.L2.Th1.F.hasCMByIsogeny dK L hcm (-1) 2 (by simp) hd0
  obtain ⟨hst, hns⟩ := Formalism.L2.Th1.F.hasCMByStable dK L hcm (-1) 2
  rw [Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq, hns] at hsum
  have hsum' : -(2 * (dK : ℂ)) * Formalism.L2.Th1.F.s2 L = ∑ P ∈ S, L.weierstrassP P := by
    rw [← hsum]; push_cast; ring
  have hP : ∀ P ∈ S, lam ^ 2 * ι (L.weierstrassP P) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
    intro P hPS
    obtain ⟨h1, h2⟩ := hS.1 P hPS
    have h3 : (dK : ℂ) * P ∈ L.lattice := by
      have h4' := hst _ h1
      have h5 : (dK : ℂ) * P
          = -((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK)
              * ((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) * P)) := by
        rw [← mul_assoc, ← sq, Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq]; ring
      rw [h5]; exact neg_mem h4'
    exact (hTor dK L hsq h4 hcm l hl5 hld ι lam hlam k2 k3 n2 n3 nd P dK hd0 hld h3 h2).1
  have hn : ¬ l ∣ 2 * dK := by
    intro h
    rcases (Nat.Prime.dvd_mul hlp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact hld h
  have hN : ‖((2 * dK : ℕ) : ℂ_[l])‖ = 1 :=
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hlp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one l) hn
  have hN0 : ((2 * dK : ℕ) : ℂ_[l]) ≠ 0 := by
    intro h; rw [h, norm_zero] at hN; exact zero_ne_one hN
  have key : lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L)
      = -(((2 * dK : ℕ) : ℂ_[l])⁻¹ * ∑ P ∈ S, lam ^ 2 * ι (L.weierstrassP P)) := by
    have h := congrArg ι hsum'

    rw [map_mul, map_neg, map_mul, map_sum, map_ofNat, map_natCast] at h
    rw [← Finset.mul_sum, ← h]
    push_cast
    push_cast at hN0
    have hd : (dK : ℂ_[l]) ≠ 0 := right_ne_zero_of_mul hN0
    field_simp
  rw [key]
  exact neg_mem (mul_mem (inv_mem (natCast_mem _ _)) (sum_mem fun P hPS => hP P hPS))

theorem cmLatticeInvariants_algebraic_of_goodReduction (hGood : Formalism.L2.Th1.CM.CM2) : Formalism.L2.KerInert.Sigma.InvAlg := by
  apply _root_.Formalism.L2.KerInert.Sigma.ChartWirtingerDerivatives.weierstrass_invariants_algebraic <;> assumption

theorem wModel_Δ_lamOf (hInv : Formalism.L2.KerInert.Sigma.InvAlg) (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) :
    (Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)).Δ = 1 := by
  have hδ0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  obtain ⟨⟨L, hL⟩, -⟩ := GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc.1 hδ0
  have hL' : (L.lattice : Set ℂ) = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
  obtain ⟨h2, h3⟩ := hInv D cc δ hcc hδ L hL
  have hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
    rw [← e2, ← e3]
    exact h
  refine GlobalTheory.EvenTheta.DatumBasic.wModel_Δ lam (by rw [e2]; exact h2) (by rw [e3]; exact h3) ?_
  unfold Formalism.MainNotions.TaylorLogMetric.discr
  rw [e2, e3]
  exact hdisc

theorem frobExists : Formalism.L2.Th1.Top.FrobExistsH := by
  intro l _ hl
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.kurFrob l (by omega)
  exact ⟨σ, hσ⟩

section Cob

open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC LTIso beLT BeRat)
open Formalism.InvariantFactorPaths.G7 (cob at1)
open Formalism.L2.KerInert.BeCob (eLT)

theorem ips {K : Type} [NormedField K] [IsUltrametricDist K] {f : PowerSeries K}
    (hf : Formalism.DworkPowerSeriesWeights.Integral (f : MvPowerSeries Unit K)) (k : ℕ) : ‖PowerSeries.coeff k f‖ ≤ 1 := hf _

end Cob

end GlobalTheory.CurveDictionary

namespace GlobalTheory.CurveDictionary

open NumberField Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1 At InertK ModelOverW)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF UnrOK IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.L2.KerInert.BeCob (eLT vLT psiLT)
open Formalism.L2.KerInert.BeCob (cc_beLT cc_lgF' lgF_eq_logF map_cob)
open Formalism.L2.KerInert.WeierstrassScaling (dict_core ePhi1_scale flog_scale isModel_scale isWq_scale scC scC_mul_uinv subst_Cmul_rescale)
open Formalism.L2.KerInert.Sigma (g_change inv_good sgSer_eq wModel_g wpReg_eq wp_sub_kur)

theorem curveDict_of_inputs (hGood : Formalism.L2.Th1.CM.CM2) (hTor : Formalism.L2.Th1.CM.CM4)
    (hS2of : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic)
    (hCW : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ MaximalUnramifiedExtension p → W.a₂ ∈ MaximalUnramifiedExtension p →
      W.a₃ ∈ MaximalUnramifiedExtension p → W.a₄ ∈ MaximalUnramifiedExtension p → W.a₆ ∈ MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ MaximalUnramifiedExtension p →
      Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]))
    (hBC : Formalism.L2.KerInert.BeCob.BeCoef) (hCE : Formalism.L2.KerInert.BeCob.CobExact)
    (hCS : Formalism.L2.KerInert.BeCob.CobSimeq) (hPT : Formalism.L2.KerInert.BeCob.PhTie)
    (hTT : Formalism.L2.KerInert.BeCob.ThetaTie)
    (hVI : ∀ (l : ℕ) [Fact l.Prime] (g : G1 l), g.Ok → ∀ (hLT : LTIso g) (n : ℕ),
      ‖PowerSeries.coeff n (Formalism.L2.KerInert.BeCob.vLT hLT)‖ ≤ 1) :
    Formalism.L2.KerInert.Rep.CurveDict := by
  exact _root_.Formalism.L2.KerInert.BeCob.rdictMain

end GlobalTheory.CurveDictionary
