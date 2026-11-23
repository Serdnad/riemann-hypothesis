module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle042
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AAvCongr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle023
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle071
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma one_le_gN {g : Mat k r} (hg : g ∈ GV k r) : 1 ≤ gN g := (Formalism.FourierDecayAlt.P.norm_of_inverse k r g hg).2

lemma gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := lt_of_lt_of_le one_pos (one_le_gN hg)

lemma top_ge_nat (m : ℕ) : (((m : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 le_top

lemma ckOn_top_nat {f : Mat k r → E} (hf : CkOn (⊤ : ℕ∞) (GV k r) f) (m : ℕ) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hc.of_le (top_ge_nat m), hff⟩

lemma top_ne_zero' : (((⊤ : ℕ∞)) : WithTop ℕ∞) ≠ 0 := by simp

lemma top_succ_le : (((⊤ : ℕ∞)) : WithTop ℕ∞) + 1 ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ⊤)

lemma ckOn_op_top {f : Mat k r → E} {X : Mat k r} (b : Bool) (hf : CkOn (⊤ : ℕ∞) (GV k r) f)
    (hX : inLie k r X) : CkOn (⊤ : ℕ∞) (GV k r) (op b X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  refine ⟨U, op' b X f', hU, hgU, ?_, ?_⟩
  · exact (hc.fderiv_of_isOpen hU top_succ_le).clm_apply (vf b X).contDiff.contDiffOn
  · intro g hg hgG
    have hd : DifferentiableAt ℝ f' g :=
      (hc.differentiableOn top_ne_zero').differentiableAt (hU.mem_nhds hg)
    exact (hasDerivAt_ext b hU hg hgG hd hff hX).deriv

lemma chart_rho {g0 x : Mat k r} (hg0 : g0 ∈ GV k r) (hx : x ∈ Sr g0) (hxG : x ∈ GV k r) :
    chart g0 (rho g0 x) = x := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
  obtain ⟨hl, -, hk⟩ := iot_facts hh hx
  show kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0 = x
  rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]

lemma rho_self {g0 : Mat k r} (hg0 : g0 ∈ GV k r) : rho g0 g0 = 0 := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  funext i
  simp only [Ux10.rho, hg1, iot, sub_self, Matrix.zero_mul]
  exact co_zero i

lemma self_mem_Sr {g0 : Mat k r} (hg0 : g0 ∈ GV k r) : g0 ∈ Sr g0 := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
  show IsUnit (g0 * g0⁻¹ + 1).det
  rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
  exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _

lemma chart_comp_cd {F : Mat k r → E} {g0 : Mat k r} (hg0 : g0 ∈ GV k r) (m : ℕ)
    (hF : CkOn ((m : ℕ) : ℕ∞) (GV k r) F) :
    ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Dom k r) := by
  intro Y hY
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨U, f', hU, hcU, hcd, hff⟩ := hF _ (chart_mem hg0 hY)
  have hchc : ContinuousAt (chart g0) Y := (chart_diff g0 hY).continuousAt
  have h1 : ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y' => f' (chart g0 Y')) Y :=
    (hcd.contDiffAt (hU.mem_nhds hcU)).comp Y
      (((chart_cd g0).contDiffAt (dom_open.mem_nhds hY)).of_le (top_ge_nat m))
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hchc.preimage_mem_nhds (hU.mem_nhds hcU), dom_open.mem_nhds hY] with Y' h1 h2
  exact hff _ h1 (chart_mem hg0 h2)

theorem ckOn_top_of_all {F : Mat k r → E} (hF : ∀ m : ℕ, CkOn ((m : ℕ) : ℕ∞) (GV k r) F) :
    CkOn (⊤ : ℕ∞) (GV k r) F := by
  intro g0 hg0
  have hAL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Dom k r) :=
    contDiffOn_infty.2 fun m => chart_comp_cd hg0 m (hF m)
  set U := Sr g0 ∩ rho g0 ⁻¹' Dom k r with hUdef
  have hUo : IsOpen U := (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) dom_open
  have hg0U : g0 ∈ U := ⟨self_mem_Sr hg0, by show rho g0 g0 ∈ Dom k r; rw [rho_self hg0]; exact zero_mem_dom⟩
  refine ⟨U, fun x => F (chart g0 (rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · exact hAL.comp ((rho_cd g0).mono Set.inter_subset_left) (fun x hx => hx.2)
  · intro x hx hxG
    show F x = F (chart g0 (rho g0 x))
    rw [chart_rho hg0 hx.1 hxG]

end Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.Rad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def retV (g₀ : B.Mat k r) : Set (B.Mat k r) := {Y | IsUnit (g₀⁻¹ * Y + 1).det}

def retDom (g₀ : B.Mat k r) : Set (B.Mat k r) :=
  retV g₀ ∩ (fun Y => prj (iot (g₀⁻¹ * Y))) ⁻¹' {X | IsUnit (1 - X).det}

def ret (g₀ : B.Mat k r) (Y : B.Mat k r) : B.Mat k r := g₀ * kap (prj (iot (g₀⁻¹ * Y)))

lemma isOpen_unitDet {X : Type*} [TopologicalSpace X] {f : X → B.Mat k r} (hf : Continuous f) :
    IsOpen {x | IsUnit (f x).det} := by
  simp_rw [isUnit_iff_ne_zero]
  exact isOpen_ne_fun hf.matrix_det continuous_const

lemma isOpen_retV (g₀ : B.Mat k r) : IsOpen (retV g₀) := isOpen_unitDet ((continuous_const.mul continuous_id).add continuous_const)

lemma cd_iotL (g₀ : B.Mat k r) : ContDiffOn ℝ ∞ (fun Y => iot (g₀⁻¹ * Y)) (retV g₀) := by
  have h1 : ContDiffOn ℝ ∞ (fun Y : B.Mat k r => g₀⁻¹ * Y) (retV g₀) := cdm_mul contDiffOn_const contDiffOn_id
  show ContDiffOn ℝ ∞ (fun Y => (g₀⁻¹ * Y - 1) * (g₀⁻¹ * Y + 1)⁻¹) (retV g₀)
  exact cdm_mul (h1.sub contDiffOn_const) (cdm_inv (h1.add contDiffOn_const) fun Y hY => hY)

lemma isOpen_retDom (g₀ : B.Mat k r) : IsOpen (retDom g₀) := by
  exact (cdm_prj (cd_iotL g₀)).continuousOn.isOpen_inter_preimage (isOpen_retV g₀)
    (isOpen_unitDet (f := fun X : B.Mat k r => 1 - X) (continuous_const.sub continuous_id))

lemma cd_ret (g₀ : B.Mat k r) : ContDiffOn ℝ ∞ (ret g₀) (retDom g₀) := by
  have hA : ContDiffOn ℝ ∞ (fun Y => prj (iot (g₀⁻¹ * Y))) (retDom g₀) :=
    cdm_prj ((cd_iotL g₀).mono Set.inter_subset_left)
  show ContDiffOn ℝ ∞ (fun Y => g₀ * ((1 + prj (iot (g₀⁻¹ * Y))) * (1 - prj (iot (g₀⁻¹ * Y)))⁻¹)) (retDom g₀)
  exact cdm_mul contDiffOn_const
    (cdm_mul (contDiffOn_const.add hA) (cdm_inv (contDiffOn_const.sub hA) fun Y hY => hY.2))

lemma ret_mem {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) {Y : B.Mat k r} (hY : Y ∈ retDom g₀) :
    ret g₀ Y ∈ B.GV k r :=
  Formalism.FourierDecayAlt.P.B2x8.al_mul_mem hg₀ (kap_mem (prj_lie (iot (g₀⁻¹ * Y))) hY.2)

private lemma prj_eq_self_of_inLie {X : B.Mat k r} (hX : B.inLie k r X) : prj X = X := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX'
  have h2 : Hpk k r * Xᴴ * Hpk k r = -X := by
    rw [Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.Ux10.hpk_sq', Matrix.one_mul]
  unfold prj
  rw [h2, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

lemma ret_self {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) {Y : B.Mat k r} (hY : Y ∈ B.GV k r)
    (hu : IsUnit (g₀⁻¹ * Y + 1).det) : ret g₀ Y = Y := by
  have hh : g₀⁻¹ * Y ∈ B.GV k r := Formalism.FourierDecayAlt.P.B2x8.al_mul_mem (Formalism.FourierDecayAlt.P.B2x8.al_inv_mem hg₀) hY
  obtain ⟨hl, -, hk⟩ := iot_facts hh hu
  show g₀ * kap (prj (iot (g₀⁻¹ * Y))) = Y
  rw [prj_eq_self_of_inLie hl, hk, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_GV hg₀), Matrix.one_mul]

lemma self_mem_retDom {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) : g₀ ∈ retDom g₀ := by
  have e : g₀⁻¹ * g₀ = 1 := Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_GV hg₀)
  refine ⟨?_, ?_⟩
  · show IsUnit (g₀⁻¹ * g₀ + 1).det
    rw [e, ← two_smul ℂ (1 : B.Mat k r), Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
  · show IsUnit (1 - prj (iot (g₀⁻¹ * g₀))).det
    rw [e, show iot (1 : B.Mat k r) = 0 by simp [iot], prj_zero, sub_zero, Matrix.det_one]
    exact isUnit_one

lemma ret_at {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) : ret g₀ g₀ = g₀ := ret_self hg₀ hg₀ (And.left (self_mem_retDom hg₀))

lemma glev0 {g : Mx k r} (hg : g ∈ B.GV k r) : g ∈ Glev k r 0 := by
  refine ⟨hg, ?_⟩
  intro a ha
  simp at ha

theorem smoothLev_of_ck {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
    {f : Mx k r → E} (hf : ∀ m : ℕ, CkLev k r 0 m D f) : SmoothLev k r 0 D f := by
  intro g₀ hg₀
  have hG₀ : g₀ ∈ B.GV k r := hg₀.1.1
  have hU : IsOpen (retDom g₀ ∩ ret g₀ ⁻¹' D) :=
    (cd_ret g₀).continuousOn.isOpen_inter_preimage (isOpen_retDom g₀) hD
  refine ⟨retDom g₀ ∩ ret g₀ ⁻¹' D, fun Y => f (ret g₀ Y), hU, ⟨self_mem_retDom hG₀, ?_⟩, ?_, ?_⟩
  · show ret g₀ g₀ ∈ D
    rw [ret_at hG₀]
    exact hg₀.2
  · intro Y hY
    refine ContDiffAt.contDiffWithinAt ?_
    have hr : ContDiffAt ℝ ∞ (ret g₀) Y := (cd_ret g₀).contDiffAt ((isOpen_retDom g₀).mem_nhds hY.1)
    refine contDiffAt_infty.2 fun m => ?_
    have hZ : ret g₀ Y ∈ Glev k r 0 ∩ D := ⟨glev0 (ret_mem hG₀ hY.1), hY.2⟩
    obtain ⟨U, F, hUo, hZU, hF, hfF⟩ := hf m (ret g₀ Y) hZ
    have hc : ContDiffAt ℝ m (fun Y' => F (ret g₀ Y')) Y :=
      (hF.contDiffAt (hUo.mem_nhds hZU)).comp Y (contDiffAt_infty.1 hr m)
    refine hc.congr_of_eventuallyEq ?_
    have h1 : ∀ᶠ Y' in 𝓝 Y, Y' ∈ retDom g₀ := (isOpen_retDom g₀).mem_nhds hY.1
    have h2 : ∀ᶠ Y' in 𝓝 Y, ret g₀ Y' ∈ U := hr.continuousAt.preimage_mem_nhds (hUo.mem_nhds hZU)
    filter_upwards [h1, h2] with Y' h1' h2'
    exact hfF _ h2' (glev0 (ret_mem hG₀ h1'))
  · intro g hg hgl
    show f g = f (ret g₀ g)
    rw [ret_self hG₀ hgl.1 hg.1.1]

end Formalism.FourierDecayAlt.P5.Rad
end
end

section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem sign_alternates_add_two (s : ℕ) : sgnW (s + 2) = - sgnW s := by
  unfold sgnW
  have e : (s + 2) * (s + 2 - 1) / 2 = s * (s - 1) / 2 + (2 * s + 1) := by
    have e2 : (s + 2) * (s + 2 - 1) = s * (s - 1) + 2 * (2 * s + 1) := by
      rw [show s + 2 - 1 = s + 1 by omega]
      cases s with
      | zero => rfl
      | succ k =>
        rw [show k + 1 - 1 = k by omega]
        ring
    rw [e2, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
  rw [e, pow_add, pow_succ, pow_mul]
  norm_num

theorem column_indicator_expansion : ExpansionCovector := by
  intro A _ _ M _ _ k r z' yb E La xi i0 s h t u hs hj hR hh ht hz' hyb hzy hxa hxi0
  obtain ⟨s'', rfl⟩ : ∃ s'', s = s'' + 2 := ⟨s - 2, by omega⟩
  obtain rfl : r = i0 + s'' + 1 := by omega
  set i : Fin (i0 + s'' + 1) := ⟨i0, by omega⟩ with hidef
  set f : Fin (i0 + s'') → Fin (2 * (i0 + s'' + 1) + k + 1) :=
    fun l => xR k (i0 + s'' + 1) (i0 + s'' + 1) le_rfl (i.succAbove l) with hfdef
  have hfv : ∀ l, (f l).val = (i.succAbove l).val := by intro l; simp [f, xR, eI]
  have hf : StrictMono f := by
    intro a b hab; show (f a).val < (f b).val; rw [hfv, hfv]; exact Fin.strictMono_succAbove _ hab
  set ew : Fin (k + 1) → Fin (i0 + s'' + 1) → Fin (2 * (i0 + s'' + 1) + k + 1) :=
    fun w => Fin.snoc (α := fun _ => Fin (2 * (i0 + s'' + 1) + k + 1)) f (wI k (i0 + s'' + 1) w) with hewdef
  have hew : ∀ w, StrictMono (ew w) := by
    intro w
    apply strictMono_snoc f hf
    intro l; show (f l).val < (wI k _ w).val; rw [hfv]; simp [wI]; have := (i.succAbove l).isLt; omega
  have hew_last : ∀ w (j : Fin (i0 + s'' + 1)), ew w j = wI k _ w ↔ j = Fin.last _ := by
    intro w j
    constructor
    · intro hj
      by_contra hne
      obtain ⟨l, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
      have := congrArg Fin.val hj
      simp only [ew, Fin.snoc_castSucc] at this
      rw [hfv] at this; simp [wI] at this; have := (i.succAbove l).isLt; omega
    · rintro rfl; simp [ew]

  have hdet : ∀ w, (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0)
      else xi (Fin.castLE le_rfl a) (ew w l)).det = (-1) ^ s'' * (h.det * t ^ s'' * sgnW s'') := by
    intro w
    rw [Matrix.det_succ_row _ i, Finset.sum_eq_single (Fin.last _)]
    · simp only [Matrix.of_apply, if_pos rfl, (hew_last w (Fin.last _)).mpr rfl, if_true, mul_one,
        Fin.succAbove_last]
      have hsub : (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0)
          else xi (Fin.castLE le_rfl a) (ew w l)).submatrix i.succAbove Fin.castSucc =
          Matrix.of fun a b : Fin (i0 + s'') => Zb i0 (s'' + 2) h t ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val
            ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply]
        rw [if_neg (Fin.succAbove_ne i a)]
        simp only [ew, Fin.snoc_castSucc]
        have hb := (i.succAbove b).isLt
        have hbne : (i.succAbove b).val ≠ i0 := fun h' => Fin.succAbove_ne i b (Fin.ext h')
        have hane : (i.succAbove a).val ≠ i0 := fun h' => Fin.succAbove_ne i a (Fin.ext h')
        rw [hxa _ _ (by simpa using hane), if_pos ⟨by rw [hfv]; omega, by rw [hfv]; exact hbne⟩, hfv]
        simp [i]
      rw [hsub, third_polynomial_expansion]
      simp only [Fin.val_last]
      rw [show i.val + (i0 + s'') = (i0 + i0) + s'' by simp [i]; ring, pow_add, ← two_mul, pow_mul]
      norm_num
    · intro j _ hj
      simp only [Matrix.of_apply, if_pos rfl]
      rw [if_neg (fun h' => hj ((hew_last w j).mp h'))]; simp
    · simp
  have hAA : AAx k (i0 + s'' + 1) E xi (i0 + s'' + 1) le_rfl u =
      ((-1) ^ s'' * (h.det * t ^ s'' * sgnW s'')) • ∑ w, herm (Hpk k _) (bvec (wI k _ w)) yb •
        qminor E (xR k _ (i0 + s'' + 1) le_rfl) (ew w) u := by
    unfold AAx
    rw [sum_lin (fun c => StrictMono c) (fun a p => xi (Fin.castLE le_rfl a) p) i
      (fun w => herm (Hpk k _) (bvec (wI k _ w)) yb) (fun w p => if p = wI k _ w then 1 else 0)
      (fun p => by rw [hxi0 _ _ (by simp [i])]; exact herm_bvec_sum k _ yb hyb p)]
    rw [Finset.smul_sum]
    congr 1; ext w
    rw [sum_single (fun c => StrictMono c) (fun a p => if a = i then (if p = wI k _ w then (1 : ℂ) else 0)
      else xi (Fin.castLE le_rfl a) p) (Set.range (ew w)) ?_ (ew w) (hew w) ?_, hdet w, smul_comm]
    · intro a p hp
      by_cases ha : a = i
      · rw [if_pos ha, if_neg]; intro hpw; apply hp; exact ⟨Fin.last _, by rw [hpw]; simp [ew]⟩
      · rw [if_neg ha]
        have hane : a.val ≠ i0 := fun h' => ha (Fin.ext h')
        rw [hxa _ _ (by simpa using hane)]
        rw [if_neg]
        rintro ⟨hp1, hp2⟩
        apply hp
        refine ⟨Fin.castSucc ⟨if p.val < i0 then p.val else p.val - 1, by split_ifs <;> omega⟩, ?_⟩
        ext; simp only [ew, Fin.snoc_castSucc]; rw [hfv, succAbove_val]; simp only [i]; split_ifs <;> omega
    · intro c hc hS; exact uniq_mono _ _ (hew w) hc hS
  have hhead : AAx k (i0 + s'' + 1) E xi i0 (by omega) u =
      h.det • qminor E (xR k _ i0 (by omega)) (xR k _ i0 (by omega)) u := by
    apply AAx_head
    · intro a p ha hp
      rw [hxa _ _ (by omega)]
      split_ifs
      · unfold Zb; rw [dite_eq_left ha, dite_eq_right (by omega)]
      · rfl
    · intro a b
      have hb := b.isLt
      rw [hxa _ _ (by simp; omega), if_pos (by simp [xR, eI]; omega)]
      unfold Zb
      simp [xR, eI]
  have hP := second_peeling_identity A k (i0 + s'') z' yb E i u hz'
  have hLa : (∑ w, herm (Hpk k _) (bvec (wI k _ w)) yb • La (qminor E (xR k _ (i0 + s'' + 1) le_rfl) (ew w) u)) =
      t • La (qminor E (xR k _ i0 (by omega)) (xR k _ i0 (by omega)) u) := by
    have := la_congr hR hP

    rw [map_sum] at this
    simp only [map_smul] at this
    rw [hzy] at this
    exact this
  have hD : Dlead i0 (s'' + 2) h t (i0 + s'' + 1 + 1) = h.det * t ^ (s'' + 2) * -sgnW s'' := by
    rw [show i0 + s'' + 1 + 1 = i0 + (s'' + 2) by omega, (derivative_leading_zb i0 (s'' + 2) h t).2, sign_alternates_add_two]

  rw [hAA, hhead, map_smul, map_smul, map_sum]
  simp only [map_smul]
  rw [hLa, hD, (derivative_leading_zb i0 (s'' + 2) h t).1, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [show s'' + 2 - 1 = s'' + 1 by omega]
  rcases mul_self_eq_one_iff.mp (sgnW_sq s'') with h1 | h1 <;> rw [h1] <;> field_simp <;> ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end
