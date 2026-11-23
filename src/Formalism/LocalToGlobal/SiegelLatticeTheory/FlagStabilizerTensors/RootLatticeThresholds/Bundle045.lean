module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsAdd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTRph
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVGeo
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVFix
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle042
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle034
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle014
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsAddFin

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem eHom_fin (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
    FiniteDimensional ℂ (X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re) := by
  have hint := Formalism.L2.SG.Pf.RowDictPf.hint_of_gap X hG
  have hB := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re
    X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (Formalism.L2.SG.EvalTRph.isFdeg_dv X) (fun v => (X.low v).1) hint X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens
    X.B.tens_spec
  have : FiniteDimensional ℂ (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) :=
    Formalism.L2.SG.Pf.RowDictPf.finiteDimensional_HHX_of_gap X hHC hG
  exact Formalism.L2.SG.RowsDef.finiteDimensional_eHom hB.1 hB.2

theorem rowsAdd_holds (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) : RowsAdd X :=
  Formalism.L2.SG.Pf.AllRowsAdd.rowsAdd_of X (eHom_fin X hHC hG)

end Formalism.L2.SG.Pf.AllRowsAddFin
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf

theorem wuBesselOfLoc_all {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) : WuBesselOfLoc C :=
  Formalism.L2.SG.Pf.WuBL.wuBesselOfLoc Formalism.L2.SG.Pf.WuBL.reproduction_translation Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm
    Formalism.L2.SG.Pf.WuBL.parameter_gap_of_hypothesis C

theorem goodSRest_of_loc {D : D7} {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hLF : LocFactor C) (hB : WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hsm : v0Of C τ ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ))
    (hT : Formalism.BasicNotions.dsigTie D) : GoodSRest hB u u' τ :=
  Formalism.L2.SG.Pf.GoodS.goodSRest_of hB u u' τ hsm (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ)
    (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u' τ) hT

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.LocWSOf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

def coef0 (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) :
    MatKR D.R.k D.R.rS → (X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)) :=
  c • Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ'

variable {X C}

def CoefPin (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ))
    (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) : Prop :=
  PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) a ∧
  PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) b ∧
  ⟪bOf hB u τ a, ξ⟫_ℂ * ⟪ξ', bOf hB u' τ b⟫_ℂ = 1 ∧ c ≠ 0

variable (X C)

def fcT (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (u u' : D.what₂.Word)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (c : Fin (nfE D) → ℂ) (j : Fin (nfE D)) :
    Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)) :=
  fun g => coef0 X C u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) (c j)
    (torS (muT D) D.R.k D.R.rS * g * torS (muT D)⁻¹ D.R.k D.R.rS)

theorem fcT_eq (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (u u' : D.what₂.Word)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (c : Fin (nfE D) → ℂ) (j : Fin (nfE D))
    (g : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS) :
    fcT X C e u u' a b ξ ξ' c j g = c j • Formalism.MainNotions.S.Pv.BetaCut.coefM
      (sigB X (Qcs C (e (plE D j))) (Qics C (e (plE D j))) (e (plE D j))) (a j) (b j) (ξ j) (ξ' j) g := by
  simp only [fcT, coef0, Pi.smul_apply, Formalism.MainNotions.S.Pv.BetaCut.coefM, sigB, Qcs, Qics, Matrix.mul_assoc]
  rfl

abbrev carrierInTc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (Formalism.L2.SG.Pf.BaseOf.towersOf X C u u' e j).base.π
      (Formalism.L2.SG.Pf.BaseOf.towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ) : CarrierIn X u u' :=
  carrierInT X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c ν' m₀ Θ TP A₀

end Formalism.L2.SG.Pf.CarrierT
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (v : InfinitePlace X.B.I.F)

theorem hfF (w' : D.what₂.Word) (a : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (frm X w' D.host.rdE v b) =
      if b = a.castSucc then ((D.host.rdE : ℂ) ^ (D.R.rS - a.1))⁻¹ else 0 := by
  induction b using Fin.lastCases with
  | last =>
    rw [frm_last, hfz_v, if_neg (Fin.castSucc_ne_last a).symm]
  | cast b =>
    rw [frm_castSucc, hJs_r, hfe_v]
    by_cases h : b = a
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e)), mul_zero]

theorem coord_eq (hw : OkPt X u u' w) (c : FreeE w → ℂ) (p : FreeE w) :
    stCoordV X u' w (gamW X u u' w) v (yU X u u' w v c hw) p = c p := by
  unfold stCoordV
  set a' : Fin D.R.rS := ⟨p.1.1.1, by have := p.2.1; omega⟩ with ha'
  have hcs : a'.castSucc = p.1.1 := Fin.ext rfl
  have hT : uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) *ᵥ frm X u' D.host.rdE v p.1.2 =
      frm X u' D.host.rdE v p.1.2 + ∑ b', (Cw w c - 1) b' p.1.2 • frm X u' D.host.rdE v b' := by
    have h1 := T_sub X u u' w v hw c (frm X u' D.host.rdE v p.1.2)
    rw [sub_one_mulVec, ← G_eq, TG_comb X u u' w v hw c] at h1
    rw [← h1]; abel
  rw [hT, hJ_add_r', hJ_sum_r', hfF, if_neg (fun e => (ne_of_lt p.2.1) (by rw [← hcs, e]))]
  rw [Finset.sum_eq_single a'.castSucc]
  · rw [hfF, if_pos rfl, zero_add, hcs, Matrix.sub_apply, Matrix.one_apply, if_neg (ne_of_lt p.2.1), sub_zero,
      Cw_apply_free]
    have hrd : (D.host.rdE : ℂ) ^ (D.R.rS - a'.1) ≠ 0 :=
      pow_ne_zero _ (Complex.ofReal_ne_zero.2 (rdE_pos_c (D := D)).ne')
    rw [show p.1.1.1 = a'.1 from rfl]
    field_simp
  · intro b _ hb
    rw [hfF, if_neg hb, mul_zero]
  · simp

theorem continuous_yM (hw : OkPt X u u' w) :
    Continuous fun c : FreeE w → ℂ => Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) := by

  have hC : Continuous fun c : FreeE w → ℂ => Cw w c := by
    refine continuous_matrix fun i j => ?_
    simp only [Cw, Matrix.of_apply]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
    · exact continuous_const

  have hdet : ∀ c : FreeE w → ℂ, (Cw w c).det = 1 := by
    intro c
    rw [Matrix.det_of_upperTriangular]
    · simp [Cw]
    · intro i j hij
      simp only [Cw, Matrix.of_apply]
      have hji : j < i := hij
      rw [if_neg (ne_of_gt hji), dite_eq_right (fun h => absurd h.1 (lt_asymm hji))]

  have hinv : Continuous fun c : FreeE w → ℂ => (Cw w c)⁻¹ := by
    have h : (fun c : FreeE w → ℂ => (Cw w c)⁻¹) = fun c => (Cw w c).adjugate := by
      funext c
      rw [Matrix.inv_def, hdet c, Ring.inverse_one, one_smul]
    rw [h]
    exact hC.matrix_adjugate
  unfold Yc Ymat Mm Am
  exact continuous_const.add ((((continuous_const.matrix_mul (Continuous.matrix_fromBlocks
    (((continuous_const.matrix_mul hinv).matrix_mul continuous_const).matrix_conjTranspose.sub continuous_const)
    continuous_const continuous_const (hC.sub continuous_const))).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_mul continuous_const)

theorem stVSec_holds : StVSec X u u' := by
  intro w hw v
  refine ⟨fun c => yU X u u' w v c hw, ?_, fun c => ⟨inN_u X u u' w v hw c, inN_u' X u u' w v hw c⟩,
    fun c => funext fun p => coord_eq X u u' w v hw c p⟩
  have hY := continuous_yM X u u' w v hw
  unfold yU mkUJ
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hY, ?_⟩) _
  exact (continuous_const.matrix_mul hY.matrix_conjTranspose).matrix_mul continuous_const

theorem ooQuot_of_nuQPin (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) :
    ∃ νl, (∀ w, OkPt X u u' w → LocPin X u u' w νl) ∧ Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' νq νl :=
  ooQuot_geo X u u' νq hN (stRel_holds X u u') (stVGeo_of_sec X u u' (stVSec_holds X u u'))

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

abbrev gB (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : MatKR D.R.k D.R.rS := trG (C.Q τ) (C.Qi τ) γ

abbrev muRB (τ : D.what₂.Tau) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) : Measure (Mt D.R.k D.R.rS) :=
  μRv.map (fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x))

theorem pl_vOf (τ : D.what₂.Tau) : X.pl (vOf X τ) = τ := X.pl.apply_symm_apply τ

theorem torS_inv_mulVec_Wb {z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} (hz : inWb D.R.k D.R.rS z) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ D.R.k D.R.rS *ᵥ z = z := by
  rw [torS_muT_inv, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, tTi_mulVec_Wb hz, Matrix.mulVec_smul,
    dMi_mulVec_wb hz, smul_smul, Complex.star_def, map_pow, Complex.conj_I, ← mul_pow, mul_neg, Complex.I_mul_I,
    neg_neg, one_pow, one_smul]

theorem zc_vOf_eq_zB_of_inWb (u u' : D.what₂.Word) (τ : D.what₂.Tau) (hz : inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    zc X C u (vOf X τ) = ((1 : ℝ) : ℂ) • zB X (C.Qi τ) u τ := by
  unfold zB at hz
  unfold zc Qic Qics zB
  rw [pl_vOf, ← Matrix.mulVec_mulVec]
  rw [torS_inv_mulVec_Wb hz]
  simp

theorem baseOf_pi (u : D.what₂.Word) (τ : D.what₂.Tau) (m : MatKR D.R.k D.R.rS) :
    πc X C u (vOf X τ) m = piB X (C.Q τ) (C.Qi τ) u τ (tT D.R.k D.R.rS * cjI D.R.k D.R.rS (kaB D)⁻¹ 1 m *
      tTi D.R.k D.R.rS) := by
  unfold πc piB Qc Qic Qcs Qics
  rw [pl_vOf, ← torS_conjI]
  simp only [Matrix.mul_assoc]

def tN (D : D7) (θ : ℝ) (κ₀ : ENNReal) : ENNReal := κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1))

def lamPl (cO : ℝ) (scl κ : ℂ) (D : D7) (θ : ℝ) (κ₀ : ENNReal) : ℂ :=
  ((cO : ℂ)⁻¹ * scl * κ * ((tN D θ κ₀ * tN D θ κ₀).toReal : ℂ))⁻¹

theorem tN_toReal_ne (D : D7) (θ : ℝ) (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hk0 : kapN D θ ≠ 0) :
    (tN D θ κ₀ * tN D θ κ₀).toReal ≠ 0 := by
  have hd : ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (deltaN_pos (inv_pos.mpr (kaB_pos D)) one_pos)).ne'
  have hs0 : kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1) ≠ 0 := mul_ne_zero hk0 hd
  have hs1 : kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have ht0 : tN D θ κ₀ ≠ 0 := by unfold tN; exact ENNReal.div_ne_zero.mpr ⟨h0, hs1⟩
  have ht1 : tN D θ κ₀ ≠ ⊤ := by unfold tN; exact ENNReal.div_ne_top h1 hs0
  exact ENNReal.toReal_ne_zero.mpr ⟨mul_ne_zero ht0 ht0, ENNReal.mul_ne_top ht1 ht1⟩

theorem pinPlace (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (F : MatKR D.R.k D.R.rS → (X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)))
    (κ : ℂ)
    (hAmp : ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
        (locW C u u' τ).μG γ μR νR ν →
      OrbInt (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') F γ ν =
        κ • (locS hB u u' τ).J νR γ)
    (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hN : Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS = haarLie (Nset D.R.k D.R.rS) κ₀)
    (hWc : μWc X C u (vOf X τ) = (C.muW u τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (hWc' : μWc X C u' (vOf X τ) = (C.muW u' τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (νB : Measure (PairSp D.R.k D.R.rS))
    (hcell : Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (locW C u u' τ).μG (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB)
    (hG : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)))
    (hcut : ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (muStd (kaB D) (muRB C τ μRv)) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) F) p)
        (baseOf X C u u' (vOf X τ)).μSS) :
    Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ)) (muStd (kaB D) (muRB C τ μRv))
                (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) F) =
      (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀)⁻¹ •
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
          Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) := by
  have e2 := hAmp (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB hcell
  obtain ⟨hgU, -, -, hrel, hH, hq, -⟩ := hcell
  have hk0 : kapN D θ ≠ 0 := Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW
  have hc : (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').c =
      ((2 * kaB D : ℝ) : ℂ) := by
    show ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) = _
    unfold kaB; congr 1; ring
  have hBz : (baseOf X C u u' (vOf X τ)).z =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).z :=
    zc_vOf_eq_zB_of_inWb C u u' τ (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz.1
  have hBz' : (baseOf X C u u' (vOf X τ)).z' =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).z' :=
    zc_vOf_eq_zB_of_inWb C u' u τ (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz'.1
  have hBπ : (baseOf X C u u' (vOf X τ)).π =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).π := by
    funext m; exact baseOf_pi C u τ m
  have hBπ' : (baseOf X C u u' (vOf X τ)).π' =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).π' := by
    funext m; exact baseOf_pi C u' τ m
  have hBW : (baseOf X C u u' (vOf X τ)).μW =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).μW := hWc
  have hBW' : (baseOf X C u u' (vOf X τ)).μW' =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).μW' :=
    hWc'
  have hBN : (baseOf X C u u' (vOf X τ)).μN = haarLie (Nset D.R.k D.R.rS) κ₀ := hN
  have : SFinite (muRB C τ μRv) := by have := hH.1; infer_instance
  have e3 := orbJ_std (k_pos D) (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
    (kaB D) (kaB_pos D) hc hk0 ENNReal.ofReal_ne_top κ₀ h0 h1 (baseOf X C u u' (vOf X τ)) hBz hBz' hBπ hBπ' hBW hBW' hBN
    (gB C τ γ) hgU hrel (muRB C τ μRv) hH.2.2.1 hH.2.1 νB hq F hcut
  have e1 := Formalism.L2.SG.Pf.LocJEq.locJ_map_eq C hB u u' τ γ ν hG
  have hs : (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').κN = kapN D θ := rfl
  rw [hs] at e3
  refine e3.trans ?_
  refine (congrArg (fun Y => ((κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)) *
            (κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)))).toReal : ℂ) • Y) e2).trans ?_
  refine (congrArg (fun Y => ((κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)) *
            (κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)))).toReal : ℂ) • κ • Y) e1).trans ?_
  have key : ∀ (a b c : ℂ) (Y : X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)), a • b • c • Y = (a * b * c) • Y :=
    fun a b c Y => by rw [smul_smul, smul_smul]
  refine (key _ _ _ _).trans ?_
  congr 1
  rw [lamPl, inv_inv]
  unfold tN
  ring

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.LocNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (large₂ : SizeData₂ D) (C1 : ℝ)
  (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))

def aT (τ : D.what₂.Tau) : ℂ := (((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ

def K0 : ℝ := (∏ τ, Complex.normSq (aT u u' C hB τ)) / Formalism.L2.SG.Pf.OOCore3.sclV Y u u'

def LocUniqP : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) → ∀ τ,
      Formalism.MainNotions.S.hsNormSq ((locS hB u u' τ).J (Formalism.L2.SG.Pf.JointAmplitudePoints.nu1P C u u' w τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ)) =
        Formalism.MainNotions.S.hsNormSq ((locS hB u u' τ).J ((νl w (vOf X τ)).map
          (Formalism.L2.SG.Pf.LocJEq.Smap C τ ((gamW X u u' w) (vOf X τ)))) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ))

def MeasP : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau),
    AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) ((gamW X u u' w) (vOf X τ)) * Matrix.of x)))
      ((νl w (vOf X τ)).map (Formalism.L2.SG.Pf.LocJEq.Smap C τ ((gamW X u u' w) (vOf X τ))))

private theorem hsNormSq_real_smul' {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    Formalism.MainNotions.S.hsNormSq (c • A) = Complex.normSq c * Formalism.MainNotions.S.hsNormSq A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, ← Finset.mul_sum]
  rw [← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul]

theorem locNormPK_of (hU : LocUniqP u u' C hB νl) (hM : MeasP u u' C hB νl) (hK : 0 < K0 Y u u' C hB)
    (hW : Formalism.L2.SG.Pf.OOCore3.WinK large₂ C1 (K0 Y u u' C hB)) : Formalism.L2.SG.Pf.OOCore3.LocNormPK Y u u' C hB large₂ C1 νl := by
  intro w hrow hrep
  refine ⟨K0 Y u u' C hB, hK, hW, ?_⟩
  have hs : Formalism.L2.SG.Pf.OOCore3.sclV Y u u' ≠ 0 := by
    intro h0
    unfold K0 at hK
    rw [h0, div_zero] at hK
    exact lt_irrefl _ hK
  have hfac : ∀ τ, Formalism.MainNotions.S.hsNormSq ((locS hB u u' τ).J (Formalism.L2.SG.Pf.JointAmplitudePoints.nu1P C u u' w τ)
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ)) = Complex.normSq (aT u u' C hB τ) *
      Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ))
        Jv (νl w (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) ((gamW X u u' w) (vOf X τ))) := by
    intro τ
    rw [hU w hrow hrep τ]
    exact (congrArg Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.LocJEq.locJ_map_eq (C := C) (hB := hB) u u' τ _ _
      (hM w τ))).trans (hsNormSq_real_smul' _ _)
  unfold Formalism.L2.SG.Pf.JointAmplitudePoints.localAmplitudeProduct
  simp only [hfac, Finset.prod_mul_distrib]
  rw [← Equiv.prod_comp X.pl.symm]
  unfold vOf K0
  field_simp

end Formalism.L2.SG.Pf.LocNorm
end
end
