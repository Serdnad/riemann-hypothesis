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

open Formalism.L2.G.Pend (k0ToC)
open Formalism.InvariantFactorPaths.G7 (lgF)

theorem lgF_eq_logF (l : ℕ) [Fact l.Prime] :
    PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) = lgF ℂ_[l] l := by
  rw [Formalism.L2.G.Pend.logF_map (p := l)]
  ext n
  unfold Formalism.MainNotions.GL3Theta.logF lgF
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul]

theorem cc_lgF' (K : Type) [Field K] (l : ℕ) : PowerSeries.constantCoeff (lgF K l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [lgF]

end GlobalTheory.CurveDictionary

noncomputable section

namespace GlobalTheory.CurveDictionary

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.KerInert.ParameterChangeLemmas Formalism.L2.KerInert.IntegralOrthonormalChange

variable {p : ℕ} [Fact p.Prime]

def scC (ν : ℂ_[p]) (hν : ν ≠ 0) : WeierstrassCurve.VariableChange ℂ_[p] := ⟨Units.mk0 ν hν, 0, 0, 0⟩

section Scale

variable (ν : ℂ_[p]) (hν : ν ≠ 0)

theorem scC_uinv : (((scC ν hν).u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ν⁻¹ := by simp [scC]

theorem scale_weierstrass_a1 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₁ = ν⁻¹ * W.a₁ := by
  rw [WeierstrassCurve.variableChange_a₁, scC_uinv]; simp [scC]

theorem scale_weierstrass_a2 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₂ = ν⁻¹ ^ 2 * W.a₂ := by
  rw [WeierstrassCurve.variableChange_a₂, scC_uinv]; simp [scC]

theorem scale_weierstrass_a3 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₃ = ν⁻¹ ^ 3 * W.a₃ := by
  rw [WeierstrassCurve.variableChange_a₃, scC_uinv]; simp [scC]

theorem scale_weierstrass_a4 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₄ = ν⁻¹ ^ 4 * W.a₄ := by
  rw [WeierstrassCurve.variableChange_a₄, scC_uinv]; simp [scC]

theorem scale_weierstrass_a6 (W : WeierstrassCurve ℂ_[p]) : (scC ν hν • W).a₆ = ν⁻¹ ^ 6 * W.a₆ := by
  rw [WeierstrassCurve.variableChange_a₆, scC_uinv]; simp [scC]

theorem rescale_C' (c a : ℂ_[p]) : PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with hn
  · rw [hn, pow_zero, one_mul]
  · rw [mul_zero]

theorem rescale_alg (c a : ℂ_[p]) :
    PowerSeries.rescale c (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a) = algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a := by
  rw [PowerSeries.algebraMap_eq]; exact rescale_C' c a

theorem cc_rescale (c : ℂ_[p]) (f : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (PowerSeries.rescale c f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem rescale_inv (c : ℂ_[p]) (f : PowerSeries ℂ_[p]) :
    PowerSeries.rescale c f⁻¹ = (PowerSeries.rescale c f)⁻¹ := by
  by_cases hf : PowerSeries.constantCoeff f = 0
  · rw [PowerSeries.inv_eq_zero.mpr hf, map_zero, PowerSeries.inv_eq_zero.mpr ((cc_rescale c f).trans hf)]
  · rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [cc_rescale]; exact hf), ← map_mul,
      PowerSeries.inv_mul_cancel _ hf, map_one]

theorem X_dX_rescale (c : ℂ_[p]) (f : PowerSeries ℂ_[p]) :
    PowerSeries.X * dX (PowerSeries.rescale c f) = PowerSeries.rescale c (PowerSeries.X * dX f) := by
  exact _root_.Formalism.L2.KerInert.WeierstrassScaling.X_dX_rescale (p := p) c f

theorem isWq_scale (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (h : IsWq W wq) :
    IsWq (scC ν hν • W) (PowerSeries.rescale ν⁻¹ wq) := by
  unfold IsWq at h ⊢
  dsimp only at h ⊢
  conv_lhs => rw [h]
  rw [scale_weierstrass_a1, scale_weierstrass_a2, scale_weierstrass_a3, scale_weierstrass_a4, scale_weierstrass_a6]
  simp only [map_add (f := _), map_mul, map_pow, map_one, PowerSeries.rescale_X, PowerSeries.algebraMap_eq, rescale_C']
  ring

theorem omegaW_scale (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    omegaW (scC ν hν • W) (PowerSeries.rescale ν⁻¹ wq) = PowerSeries.rescale ν⁻¹ (omegaW W wq) := by
  apply _root_.Formalism.L2.KerInert.WeierstrassScaling.omegaW_scale

theorem flog_scale (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    flog (scC ν hν • W) (PowerSeries.rescale ν⁻¹ wq) = PowerSeries.C ν * PowerSeries.rescale ν⁻¹ (flog W wq) := by
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
  unfold flog
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, omegaW_scale]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, PowerSeries.coeff_rescale]
    have h1 : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν
    rw [pow_succ]
    linear_combination (-(ν⁻¹ ^ n * PowerSeries.coeff n (omegaW W wq) / ((n + 1 : ℕ) : ℂ_[p]))) * h1

end Scale

section Subst

theorem hasSubst_cX (c : ℂ_[p]) : PowerSeries.HasSubst (c • (PowerSeries.X : PowerSeries ℂ_[p])) :=
  (PowerSeries.HasSubst.X' (R := ℂ_[p])).smul' c

theorem subst_rescale_arg (c : ℂ_[p]) (A f : PowerSeries ℂ_[p]) (hA : PowerSeries.constantCoeff A = 0) :
    PowerSeries.subst (PowerSeries.rescale c A) f = PowerSeries.rescale c (PowerSeries.subst A f) := by
  rw [PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hA) (hasSubst_cX c)]

theorem subst_Cmul_rescale (a : ℂ_[p]) (ha : a ≠ 0) (h f : PowerSeries ℂ_[p])
    (h0 : PowerSeries.constantCoeff h = 0) :
    PowerSeries.subst (PowerSeries.C a * h) (PowerSeries.rescale a⁻¹ f) = PowerSeries.subst h f := by
  have h1 : PowerSeries.constantCoeff (PowerSeries.C a * h) = 0 := by rw [map_mul, h0, mul_zero]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' h1
  rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply (hasSubst_cX a⁻¹) hs]
  congr 1
  rw [PowerSeries.subst_smul hs, PowerSeries.subst_X hs, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ ha, map_one, one_mul]

end Subst

theorem scC_mul_uinv (ν : ℂ_[p]) (hν : ν ≠ 0) (C : WeierstrassCurve.VariableChange ℂ_[p]) :
    (((scC ν hν * C).u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ν⁻¹ * ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) := by
  rw [WeierstrassCurve.VariableChange.mul_def]
  simp [scC, mul_comm]

theorem ePhi1_scale (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (C : WeierstrassCurve.VariableChange ℂ_[p])
    (wq : PowerSeries ℂ_[p]) (ν : ℂ_[p]) (hν : ν ≠ 0) :
    ePhi1 lam Λ (scC ν hν * C) (PowerSeries.rescale ν⁻¹ wq) = PowerSeries.rescale ν⁻¹ (ePhi1 lam Λ C wq) := by
  apply _root_.Formalism.L2.KerInert.WeierstrassScaling.ePhi1_scale

theorem isModel_scale (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (C : WeierstrassCurve.VariableChange ℂ_[p])
    (hU : Formalism.MainNotions.GL3Theta.IsModelU lam Λ C) (ν : ℂ_[p]) (hν : ν ≠ 0) (hν1 : ‖ν‖ = 1)
    (hν12 : ν ^ 12 = (C • wModel lam Λ).Δ) : IsModel lam Λ (scC ν hν * C) := by
  apply _root_.Formalism.L2.KerInert.WeierstrassScaling.isModel_scale <;> assumption

theorem dict_core (hp2 : p ≠ 2) (D : D7) {N N' r : ℕ} (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (h : PowerSeries ℂ_[p]) (h0 : PowerSeries.constantCoeff h = 0) (hI : ∀ n, IsIntP (PowerSeries.coeff n h))
    (κ : ℂ_[p])
    (hlog : PowerSeries.subst h (flog (C • wModel lam Λ) wq) =
      PowerSeries.C κ * PowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (Formalism.MainNotions.FormalGroupSystem.logF p))
    (ph V : PowerSeries ℂ_[p]) (hph0 : PowerSeries.constantCoeff ph = 0) (hV : ∀ n, IsIntP (PowerSeries.coeff n V))
    (hexp : (Formalism.L2.Th1.C.mvExp ph : PowerSeries ℂ_[p]) = V * (PowerSeries.subst h (ePhi1 lam Λ C wq))⁻¹)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])
    (hInt : IntegralMv (atLog D lam Λ C wq b G * ePh lam Λ C wq r)) :
    Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries (Fin r) ℂ_[p]) *
      @Formalism.MainNotions.FormalGroupSystem.inParamK p _ (Fin r) ℂ_[p] _ (Formalism.L2.G.Pend.wittFractionAlgebraCp p)
        (Formalism.L2.KerInert.Rep.thOrth D lam (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * κ) b G)) := by
  exact _root_.Formalism.L2.KerInert.WeierstrassScaling.dict_core (p := p) hp2 D (N := N) (N' := N') (r := r) lam Λ C wq h h0 hI κ hlog ph V hph0 hV hexp b G hInt

end GlobalTheory.CurveDictionary

namespace GlobalTheory.CurveDictionary

open NumberField Formalism.BasicNotions

theorem sgStar_lattice (L : PeriodPair) :
    Formalism.MainNotions.TaylorLogMetric.sgStar L.lattice.toAddSubgroup = Formalism.L2.Th1.F.sgStar L := by
  rw [GlobalTheory.OddTheta.sgStar_eq L L.lattice.toAddSubgroup (fun _ => Iff.rfl), GlobalTheory.Mem.Col2.ThetaVec.sgStar_eq]

theorem taylor_sgStar_map (L : PeriodPair) (a2 a3 s0 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : L.g₂ = a2) (h3 : L.g₃ = a3)
    (hs : Formalism.L2.Th1.F.s2 L = s0) :
    Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.sgStar L) =
      PowerSeries.map (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) (Formalism.L2.Th1.B.sgStar s0 (Formalism.L2.Th1.F.pOf a2 a3)) :=
  Formalism.L2.KerInert.Sigma.taylor_sgStar_map L a2 a3 s0 h2 h3 hs

theorem sgSer_eq {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (L : PeriodPair)
    (a2 a3 s0 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : L.g₂ = a2) (h3 : L.g₃ = a3) (hs : Formalism.L2.Th1.F.s2 L = s0) :
    Formalism.MainNotions.TaylorLogMetric.sgSer lam L.lattice.toAddSubgroup =
      Formalism.L2.Th1.B.sgStar (lam s0) (Formalism.L2.Th1.F.pOf (lam a2) (lam a3)) :=
  Formalism.L2.KerInert.Sigma.sgSer_eq lam L a2 a3 s0 h2 h3 hs

theorem wModel_g {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (a2 a3 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : Formalism.MainNotions.TaylorLogMetric.g2 Λ = a2) (h3 : Formalism.MainNotions.TaylorLogMetric.g3 Λ = a3) :
    Formalism.L2.Th1.A.g₂ (Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) = lam a2 ∧ Formalism.L2.Th1.A.g₃ (Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) = lam a3 := by
  apply _root_.Formalism.L2.KerInert.Sigma.wModel_g <;> assumption

theorem g_change {p : ℕ} [Fact p.Prime] (C : WeierstrassCurve.VariableChange ℂ_[p]) (W : WeierstrassCurve ℂ_[p]) :
    Formalism.L2.Th1.A.g₂ (C • W) = ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 4 * Formalism.L2.Th1.A.g₂ W ∧
      Formalism.L2.Th1.A.g₃ (C • W) = ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 * Formalism.L2.Th1.A.g₃ W := by
  simp only [Formalism.L2.Th1.A.g₂, Formalism.L2.Th1.A.g₃, WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_c₆]
  constructor <;> ring

theorem wpReg_eq {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) :
    Formalism.L2.Th1.A.wpReg W = Formalism.L2.Th1.F.pOf (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W) :=
  _root_.Formalism.L2.Th1.F.weierstrass_series_unique K _ _ _ _ (Formalism.L2.Th1.A.bridgeWp K W) (_root_.Formalism.L2.Th1.F.weierstrass_p_of_series K _ _)

section Int

variable {p : ℕ} [Fact p.Prime]

theorem wp_sub_kur (x : ℂ_[p]) (hx : x ∈ Formalism.MainNotions.GL3Theta.Wp p) : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p := by
  apply _root_.Formalism.L2.KerInert.Sigma.wp_sub_kur <;> assumption

theorem nadd {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem nmul {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem nsub {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]; exact nadd hx (by rwa [norm_neg])

theorem nnat (n : ℕ) : ‖(n : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℂ_[p] n

theorem nofNat (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : ℂ_[p])‖ ≤ 1 := by
  have := nnat (p := p) (OfNat.ofNat n); rwa [Nat.cast_ofNat] at this

theorem not_dvd_23 (hp : p.Prime) (h5 : 5 ≤ p) (a b : ℕ) : ¬ p ∣ 2 ^ a * 3 ^ b := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega

theorem padic_norm_twelve_eq_one_of_five_le (h5 : 5 ≤ p) : ‖(12 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p)
    (not_dvd_23 hp h5 2 1)
  norm_num at this
  exact this

theorem padicNorm_twoHundredSixteen_eq_one_of_five_le (h5 : 5 ≤ p) : ‖(216 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p)
    (not_dvd_23 hp h5 3 3)
  norm_num at this
  exact this

theorem inv_good (W : WeierstrassCurve ℂ_[p]) (h5 : 5 ≤ p) (i1 : ‖W.a₁‖ ≤ 1) (i2 : ‖W.a₂‖ ≤ 1)
    (i3 : ‖W.a₃‖ ≤ 1) (i4 : ‖W.a₄‖ ≤ 1) (i6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1)
    (w1 : W.a₁ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w2 : W.a₂ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w3 : W.a₃ ∈ Formalism.MainNotions.GL3Theta.Wp p)
    (w4 : W.a₄ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w6 : W.a₆ ∈ Formalism.MainNotions.GL3Theta.Wp p) :
    Formalism.L2.Th1.A.g₂ W ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ Formalism.L2.Th1.A.g₃ W ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧
      ‖Formalism.L2.Th1.A.g₂ W‖ ≤ 1 ∧ ‖Formalism.L2.Th1.A.g₃ W‖ ≤ 1 ∧
      ‖Formalism.L2.Th1.A.g₂ W ^ 3 - 27 * Formalism.L2.Th1.A.g₃ W ^ 2‖ = 1 := by
  apply _root_.Formalism.L2.KerInert.Sigma.inv_good <;> assumption

end Int

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

theorem map_cob {K K' : Type} [Field K] [Field K'] (φ : K →+* K') (F : MvPowerSeries (Fin 2) K)
    (hF : MvPowerSeries.constantCoeff F = 0) (f : PowerSeries K) :
    MvPowerSeries.map φ (cob F f) = cob (MvPowerSeries.map φ F) (PowerSeries.map φ f) := by
  unfold cob at1
  rw [map_sub, map_sub, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)),
    MvPowerSeries.map_X, MvPowerSeries.map_X]

theorem cc_beLT {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (hb : BeRat g (eLT hLT))
    (hph : PowerSeries.constantCoeff g.ph = 0) : MvPowerSeries.constantCoeff (beLT hLT) = 0 := by
  apply _root_.Formalism.L2.KerInert.BeCob.cc_beLT <;> assumption

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
