module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle016
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle017
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle025
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle009
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle018
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle026
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle022
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle023
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle024
public import Formalism.HermitianCurvature.StatementQr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts

@[expose] public section

section

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Hinv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (Hsq k r)

theorem lie_inv {X : Mat k r} (hX : inLie k r X) : (Hpk k r)⁻¹ * Xᴴ * Hpk k r = -X := by
  have hX0 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX0
  rw [Hinv, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, Hsq, Matrix.one_mul]

theorem hermPart_eq_self_of_mem_lie {X : Mat k r} (hX : inLie k r X) : hpart1 (Hpk k r) X = X := by
  simp only [hpart1]
  rw [lie_inv hX, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

theorem hpart2_eq_zero_of_inLie {X : Mat k r} (hX : inLie k r X) : hpart2 (Hpk k r) X = 0 := by
  simp only [hpart2]
  rw [lie_inv hX]
  simp

theorem two_I_inv : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
  rw [div_eq_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
  linear_combination Complex.I_sq

theorem hp_decomp (Z : Mat k r) : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
  simp only [hpart1, hpart2]
  have e : Complex.I * -(Complex.I / 2) = (1 / 2 : ℂ) := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  rw [two_I_inv, smul_smul, e, ← smul_add, sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem hpart1_add' (Z W : Mat k r) : hpart1 (Hpk k r) (Z + W) = hpart1 (Hpk k r) Z + hpart1 (Hpk k r) W := by
  simp only [hpart1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  rw [← smul_add]
  congr 1
  abel

theorem hpart2_add' (Z W : Mat k r) : hpart2 (Hpk k r) (Z + W) = hpart2 (Hpk k r) Z + hpart2 (Hpk k r) W := by
  simp only [hpart2, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  rw [← smul_add]
  congr 1
  abel

theorem hp1_real (x : ℝ) (Z : Mat k r) : hpart1 (Hpk k r) ((x : ℂ) • Z) = (x : ℂ) • hpart1 (Hpk k r) Z := by
  have hs : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simp only [hpart1, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_sub, smul_comm]

theorem hpart2_ofReal_smul (x : ℝ) (Z : Mat k r) : hpart2 (Hpk k r) ((x : ℂ) • Z) = (x : ℂ) • hpart2 (Hpk k r) Z := by
  have hs : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simp only [hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_add, smul_comm]

theorem hpart1_I_smul (Z : Mat k r) : hpart1 (Hpk k r) (Complex.I • Z) = -hpart2 (Hpk k r) Z := by
  have hs : star Complex.I = -Complex.I := Complex.conj_I
  simp only [hpart1, hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul, two_I_inv]
  simp only [neg_smul, neg_neg, sub_neg_eq_add]
  rw [← smul_add, smul_smul, show (1 / 2 : ℂ) * Complex.I = Complex.I / 2 by ring]

theorem hpart2_I_smul (Z : Mat k r) : hpart2 (Hpk k r) (Complex.I • Z) = hpart1 (Hpk k r) Z := by
  have hs : star Complex.I = -Complex.I := Complex.conj_I
  simp only [hpart1, hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul, two_I_inv]
  have e1 : -(Complex.I / 2) * Complex.I = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  have e2 : -(Complex.I / 2) * -Complex.I = -(1 / 2) := by
    linear_combination (1 / 2 : ℂ) * Complex.I_sq
  rw [smul_add, smul_smul, smul_smul, smul_sub, e1, e2, neg_smul, sub_eq_add_neg]

theorem lie_bracket {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X * Y - Y * X) := by
  have hX0 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hY0 : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  have hX' : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX0
  have hY' : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY0
  have hX'' : ∀ M : Mat k r, Xᴴ * (Hpk k r * M) = -(Hpk k r * (X * M)) := by
    intro M
    rw [← Matrix.mul_assoc, hX', Matrix.neg_mul, Matrix.mul_assoc]
  have hY'' : ∀ M : Mat k r, Yᴴ * (Hpk k r * M) = -(Hpk k r * (Y * M)) := by
    intro M
    rw [← Matrix.mul_assoc, hY', Matrix.neg_mul, Matrix.mul_assoc]
  show (X * Y - Y * X)ᴴ * Hpk k r + Hpk k r * (X * Y - Y * X) = 0
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, hX', hY', Matrix.mul_neg, hX'', hY'', neg_neg]
  abel

theorem hp_of_parts {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) :
    hpart1 (Hpk k r) (X + Complex.I • Y) = X ∧ hpart2 (Hpk k r) (X + Complex.I • Y) = Y := by
  refine ⟨?_, ?_⟩
  · rw [hpart1_add', hpart1_I_smul, hermPart_eq_self_of_mem_lie hX, hpart2_eq_zero_of_inLie hY, neg_zero, add_zero]
  · rw [hpart2_add', hpart2_I_smul, hpart2_eq_zero_of_inLie hX, hermPart_eq_self_of_mem_lie hY, zero_add]

def Psi (D : Mat k r →L[ℝ] E) (g Z : Mat k r) : E :=
  D (g * hpart1 (Hpk k r) Z) + Complex.I • D (g * hpart2 (Hpk k r) Z)

theorem Psi_add (D : Mat k r →L[ℝ] E) (g Z W : Mat k r) : Psi D g (Z + W) = Psi D g Z + Psi D g W := by
  simp only [Psi, hpart1_add', hpart2_add', Matrix.mul_add, map_add (f := _), smul_add]
  abel

theorem D_real (D : Mat k r →L[ℝ] E) (g M : Mat k r) (x : ℝ) : D (g * ((x : ℂ) • M)) = (x : ℂ) • D (g * M) := by
  rw [Matrix.mul_smul]
  exact (map_smul D x (g * M)).trans (Complex.coe_smul x _).symm

theorem Psi_real (D : Mat k r →L[ℝ] E) (g Z : Mat k r) (x : ℝ) : Psi D g ((x : ℂ) • Z) = (x : ℂ) • Psi D g Z := by
  simp only [Psi, hp1_real, hpart2_ofReal_smul, D_real, smul_add]
  rw [smul_comm (x : ℂ) Complex.I]

theorem Psi_I (D : Mat k r →L[ℝ] E) (g Z : Mat k r) : Psi D g (Complex.I • Z) = Complex.I • Psi D g Z := by
  simp only [Psi, hpart1_I_smul, hpart2_I_smul, Matrix.mul_neg, map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

theorem Psi_smul (D : Mat k r →L[ℝ] E) (g Z : Mat k r) (c : ℂ) : Psi D g (c • Z) = c • Psi D g Z := by
  have hc := Complex.re_add_im c
  calc Psi D g (c • Z) = Psi D g ((c.re : ℂ) • Z + (c.im : ℂ) • (Complex.I • Z)) := by
        rw [smul_smul, ← add_smul, hc]
    _ = (c.re : ℂ) • Psi D g Z + (c.im : ℂ) • (Complex.I • Psi D g Z) := by
        rw [Psi_add, Psi_real, Psi_real, Psi_I]
    _ = c • Psi D g Z := by
        rw [smul_smul, ← add_smul, hc]

theorem Psi_zero (D : Mat k r →L[ℝ] E) (g : Mat k r) : Psi D g 0 = 0 := by
  simpa using Psi_smul D g 0 0

theorem Psi_sub (D : Mat k r →L[ℝ] E) (g Z W : Mat k r) : Psi D g (Z - W) = Psi D g Z - Psi D g W := by
  rw [sub_eq_add_neg, Psi_add, ← neg_one_smul ℂ W, Psi_smul, neg_one_smul, ← sub_eq_add_neg]

end Formalism.FourierDecayAlt.P.JFxE
end
end

section

theorem Formalism.FourierDecayAlt.P.border_first_expansion : Formalism.FourierDecayAlt.Q.BorderE := by
  exact quantum_minor_border_es.1

theorem Formalism.FourierDecayAlt.P.border_last_expansion : Formalism.FourierDecayAlt.Q.BorderS := by
  exact quantum_minor_border_es.2

theorem Formalism.FourierDecayAlt.P.border_full_expansion : Formalism.FourierDecayAlt.Q.BorderFull := by
  exact quantum_minor_border_full

theorem Formalism.FourierDecayAlt.P.rtt_sandwich : Formalism.FourierDecayAlt.Q.RTTSandwich := by
  exact rtt_sandwich'

theorem Formalism.FourierDecayAlt.P.level_group_image : Formalism.FourierDecayAlt.Q.GlevImage := by
  obtain ⟨hH, hU, -⟩ := level_basics
  exact gl_level_image hH hU

theorem Formalism.FourierDecayAlt.P.level_transfer : Formalism.FourierDecayAlt.Q.LevelTransfer := by
  exact level_transfer_of_levHom level_basics.1

theorem Formalism.FourierDecayAlt.P.left_action_rule : Formalism.FourierDecayAlt.Q.RuleLeft := by
  exact qnRuleLeft

theorem Formalism.FourierDecayAlt.P.torus_action_rule : Formalism.FourierDecayAlt.Q.RuleTorus := by
  exact qnRuleTorus

theorem Formalism.FourierDecayAlt.P.operator_invariance : Formalism.FourierDecayAlt.Q.TInvariant := by
  exact qnTInv

theorem Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms : Formalism.FourierDecayAlt.Q.TPreservesFF := by
  exact qnTPres

theorem Formalism.FourierDecayAlt.P.capelli_commutation : Formalism.FourierDecayAlt.Q.CapCommute := by
  exact capelli_det_commute

theorem Formalism.FourierDecayAlt.P.hermitian_haar_invariance : Formalism.FourierDecayAlt.Q.HermHaar := by
  exact qnHermHaar
end

section

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem one_parameter_differentiable : Formalism.FourierDecayAlt.Qr.OneParamDiff := by
  intro W _ _ _ φ h0 hadd hc
  have hmul : ∀ s t, φ (s + t) = φ s * φ t := fun s t => hadd s t
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ s : ℝ, |s| < δ → ‖φ s - 1‖ < 1 / 2 := by
    obtain ⟨δ, hδ, H⟩ := Metric.continuous_iff.1 hc 0 (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have := H s (by rwa [Real.dist_eq, sub_zero])
    rwa [dist_eq_norm, h0] at this
  set h : ℝ := δ / 2 with hh
  have hpos : 0 < h := by positivity
  have hint : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b := fun a b => hc.intervalIntegrable a b
  set M : W →L[ℂ] W := ∫ s in (0 : ℝ)..h, φ s with hM
  have hbound : ‖M - h • (1 : W →L[ℂ] W)‖ ≤ 1 / 2 * |h - 0| := by
    have e : M - h • (1 : W →L[ℂ] W) = ∫ s in (0 : ℝ)..h, (φ s - 1) := by
      rw [intervalIntegral.integral_sub (hint 0 h) intervalIntegrable_const, intervalIntegral.integral_const,
        sub_zero]
    rw [e]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le hpos.le] at hs
    refine (hball s ?_).le
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  set tt : W →L[ℂ] W := 1 - h⁻¹ • M with htt
  have hnorm : ‖tt‖ < 1 := by
    have e : tt = h⁻¹ • (h • (1 : W →L[ℂ] W) - M) := by
      rw [htt, smul_sub, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    rw [e, norm_smul, norm_sub_rev, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    calc h⁻¹ * ‖M - h • (1 : W →L[ℂ] W)‖ ≤ h⁻¹ * (1 / 2 * |h - 0|) := by gcongr
      _ = 1 / 2 := by
        rw [sub_zero, abs_of_pos hpos, ← mul_assoc, mul_comm h⁻¹, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
      _ < 1 := by norm_num
  let u0 := Units.oneSub tt hnorm
  have hu0 : (u0 : W →L[ℂ] W) = h⁻¹ • M := by
    show 1 - tt = h⁻¹ • M
    rw [htt, sub_sub_cancel]
  set G : ℝ → W →L[ℂ] W := fun t => (∫ s in (0 : ℝ)..t + h, φ s) - ∫ s in (0 : ℝ)..t, φ s with hG
  have hφM : ∀ t, φ t * M = G t := by
    intro t
    have e1 := (ContinuousLinearMap.mul ℂ (W →L[ℂ] W) (φ t)).intervalIntegral_comp_comm (hint 0 h)
    simp only [ContinuousLinearMap.mul_apply'] at e1
    rw [hM, ← e1]
    simp only [hG]
    rw [intervalIntegral.integral_interval_sub_left (hint 0 (t + h)) (hint 0 t)]
    rw [show (fun s => φ t * φ s) = fun s => φ (t + s) from funext fun s => (hmul t s).symm,
      intervalIntegral.integral_comp_add_left φ t, add_zero]
  have hφ : φ = fun t => (h⁻¹ • G t) * (↑u0⁻¹ : W →L[ℂ] W) := by
    funext t
    rw [← hφM t, ← mul_smul_comm, ← hu0, Units.mul_inv_cancel_right]
  have hF : ∀ x, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, φ s) (φ x) x :=
    fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  refine ⟨(h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W), fun t => ?_⟩
  have hGd : HasDerivAt G (φ (t + h) - φ t) t := ((hF (t + h)).comp_add_const t h).sub (hF t)
  let R : (W →L[ℂ] W) →L[ℝ] (W →L[ℂ] W) :=
    (((ContinuousLinearMap.mul ℂ (W →L[ℂ] W)).flip (↑u0⁻¹ : W →L[ℂ] W)).restrictScalars ℝ)
  have hd := R.hasFDerivAt.comp_hasDerivAt t (hGd.const_smul h⁻¹)
  have e : ∀ x, φ x = (⇑R ∘ (h⁻¹ • G)) x := by
    intro x
    rw [hφ]
    rfl
  have e2 : φ t ∘SL ((h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W)) = R (h⁻¹ • (φ (t + h) - φ t)) := by
    show φ t * ((h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W)) = (h⁻¹ • (φ (t + h) - φ t)) * (↑u0⁻¹ : W →L[ℂ] W)
    rw [hmul t h, show φ t * φ h - φ t = φ t * (φ h - 1) by rw [mul_sub, mul_one], ← mul_smul_comm, mul_assoc]
  rw [e2]
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall e)

end Formalism.FourierDecayAlt.P
end
end
