module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.CategoryTheory.Category.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil

theorem hasFDerivAt_of_norming {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {X : Type} (l : X → B →L[ℂ] ℂ) (h1 : ∀ x b, ‖l x b‖ ≤ ‖b‖)
    (h2 : ∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) (F : V → B) (A : V → V →L[ℝ] B) (hA : Continuous A)
    (hF : ∀ x v, HasFDerivAt (fun w => l x (F w)) (((l x).restrictScalars ℝ).comp (A v)) v) (v : V) :
    HasFDerivAt F (A v) v := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.1 (hA.continuousAt (x := v)) c hc
  filter_upwards [Metric.ball_mem_nhds v hδ] with w hw
  refine h2 _ _ (by positivity) fun x => ?_
  have := (convex_ball v δ).norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ) (C := c)
    (φ := ((l x).restrictScalars ℝ).comp (A v))
    (fun u _ => (hF x u).hasFDerivWithinAt) (fun u hu => ?_) (Metric.mem_ball_self hδ) hw
  · simpa only [map_sub, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] using this
  · refine ContinuousLinearMap.opNorm_le_bound _ hc.le fun z => ?_
    have e : (((l x).restrictScalars ℝ).comp (A u) - ((l x).restrictScalars ℝ).comp (A v)) z = l x ((A u - A v) z) := by
      simp
    rw [e]
    refine (h1 _ _).trans (((A u - A v).le_opNorm z).trans ?_)
    have := hb hu
    rw [dist_eq_norm] at this
    gcongr

theorem sm_of_weak_deriv_closed : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ)
    (ρ : V → B →L[ℂ] B), IsHeis (fun x y => om x y) ρ → ∀ (X : Type) (l : X → B →L[ℂ] ℂ), (∀ x b, ‖l x b‖ ≤ ‖b‖) →
    (∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) →
    (∀ x v, ∃ (a : ℂ) (x' : X), ∀ b, l x (ρ v b) = a * l x' b) → ∀ Θ : Set B,
    (∀ f ∈ Θ, ∀ x, Differentiable ℝ fun v => l x (ρ v f)) →
    (∀ f ∈ Θ, ∀ z : V, ∃ f' ∈ Θ, ∀ x, HasDerivAt (fun t : ℝ => l x (ρ (t • z) f)) (l x f') 0) →
    ∀ f ∈ Θ, Sm ρ f := by
  intro V _ _ _ B _ _ _ om ρ h X l h1 h2 h3 Θ hd hc
  have sep : ∀ b b' : B, (∀ x, l x b = l x b') → b = b' := fun b b' hb => by
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    exact h2 _ 0 le_rfl fun x => by rw [map_sub, hb, sub_self, norm_zero]
  have lsm : ∀ x (r : ℝ) (b : B), l x (r • b) = r • l x b := fun x r b => ((l x).restrictScalars ℝ).map_smul r b
  have key : ∀ f ∈ Θ, ∃ D : V →L[ℝ] B, (∀ z, D z ∈ Θ) ∧
      ∀ v, HasFDerivAt (fun w => ρ w f) (((ρ v).restrictScalars ℝ).comp D -
        (om v).smulRight (((π : ℂ) * I) • ρ v f)) v := by
    intro f hf
    choose g hg hg' using hc f hf
    have hgd : ∀ x z, l x (g z) = fderiv ℝ (fun v => l x (ρ v f)) 0 z := by
      intro x z
      refine (hg' z x).unique ?_
      have a1 : HasDerivAt (fun t : ℝ => t • z) z 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const z
      have a2 : HasFDerivAt (fun v => l x (ρ v f)) (fderiv ℝ (fun v => l x (ρ v f)) 0) ((0 : ℝ) • z) := by
        rw [zero_smul]; exact (hd f hf x 0).hasFDerivAt
      exact a2.comp_hasDerivAt (0 : ℝ) a1
    let D0 : V →ₗ[ℝ] B :=
      { toFun := g
        map_add' := fun z z' => sep _ _ fun x => by rw [map_add (f := _), hgd, hgd, hgd, map_add (f := _)]
        map_smul' := fun r z => sep _ _ fun x => by rw [RingHom.id_apply, lsm, hgd, hgd, map_smul] }
    let D : V →L[ℝ] B := LinearMap.toContinuousLinearMap D0
    have hD : ∀ z, D z = g z := fun z => rfl
    refine ⟨D, fun z => hg z, hasFDerivAt_of_norming l h1 h2 _ _ ?_ ?_⟩
    · refine continuous_clm_apply.2 fun z => ?_
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply]
      have a1 := h.2.2.2 (D z)
      have a2 := h.2.2.2 f
      exact a1.sub ((om.continuous.clm_apply continuous_const).smul (a2.const_smul _))
    · intro x v
      obtain ⟨a, x', hx⟩ := h3 x v
      have e : (fun w => l x (ρ w f)) =
          fun w => cexp (-(π * I) * (om v (w - v) : ℝ)) * (a * l x' (ρ (w - v) f)) := by
        funext w
        rw [← hx, h.2.1, add_sub_cancel, map_smul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
        simp
      have b0 : HasFDerivAt (fun w : V => w - v) (ContinuousLinearMap.id ℝ V) v := (hasFDerivAt_id v).sub_const v
      have b1 : HasFDerivAt (fun w => l x' (ρ (w - v) f)) (fderiv ℝ (fun v => l x' (ρ v f)) 0) v := by
        have a2 : HasFDerivAt (fun v => l x' (ρ v f)) (fderiv ℝ (fun v => l x' (ρ v f)) 0) (v - v) := by
          rw [sub_self]; exact (hd f hf x' 0).hasFDerivAt
        simpa [Function.comp_def] using HasFDerivAt.comp (f := fun w : V => w - v) v a2 b0
      have b2 : HasFDerivAt (fun w : V => ((om v (w - v) : ℝ) : ℂ)) (Complex.ofRealCLM.comp (om v)) v := by
        simpa [Function.comp_def] using (Complex.ofRealCLM.comp (om v)).hasFDerivAt.comp v b0
      have b3 := ((b2.const_mul (-(π * I) : ℂ)).cexp).mul (b1.const_mul a)
      rw [e]
      refine b3.congr_fderiv ?_
      ext z
      simp [← hgd, h.1, hD, lsm, hx]
      ring
  have ind : ∀ n : ℕ, ∀ f ∈ Θ, ContDiff ℝ n fun v => ρ v f := by
    intro n
    induction n with
    | zero => intro f _; exact contDiff_zero.2 (h.2.2.2 f)
    | succ n ih =>
      intro f hf
      obtain ⟨D, hD, hF⟩ := key f hf
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun v => (hF v).differentiableAt, by simp, fun z => ?_⟩
      simp only [(hF _).fderiv, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply]
      exact (ih _ (hD z)).sub ((om.contDiff.clm_apply contDiff_const).smul ((ih f hf).const_smul _))
  intro f hf
  exact contDiff_infty.2 fun n => ind n f hf

end GlobalTheory.RealWeil
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil.PosDet

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem det_left {p : Matrix ι ι ℂ} (pp : p * p = p) (g : Matrix ι ι ℂ) :
    (p * g + (1 - p)).det = (p * g * p + (1 - p)).det := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have e : p * g + (1 - p) = (1 + p * (g * (1 - p))) * (p * g * p + (1 - p)) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel
  have e2 : g * (1 - p) * p = 0 := by
    simp only [mul_sub, sub_mul, mul_assoc, pp, one_mul, mul_one, sub_self]
  rw [e, det_mul, det_one_add_mul_comm, e2, add_zero, det_one, one_mul]

theorem det_right {p : Matrix ι ι ℂ} (pp : p * p = p) (g : Matrix ι ι ℂ) :
    (g * p + (1 - p)).det = (p * g * p + (1 - p)).det := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have e : g * p + (1 - p) = (p * g * p + (1 - p)) * (1 + ((1 - p) * g) * p) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel
  have e2 : p * ((1 - p) * g) = 0 := by
    simp only [mul_sub, sub_mul, pp', one_mul, sub_self]
  rw [e, det_mul, det_one_add_mul_comm, e2, add_zero, det_one, mul_one]

theorem det_compl {p : Matrix ι ι ℂ} (pp : p * p = p) {g h : Matrix ι ι ℂ} (hg : h * g = 1) :
    (p + (1 - p) * g * (1 - p)).det = (p * h + (1 - p)).det * g.det := by
  have qq : (1 - p) * (1 - p) = 1 - p := by
    simp only [mul_sub, sub_mul, pp, one_mul, mul_one]; abel
  have := det_left qq g
  rw [sub_sub_cancel] at this
  rw [add_comm p, ← this, ← det_mul, add_mul, mul_assoc p, hg, mul_one, add_comm]

theorem det_sign {p : Matrix ι ι ℂ} (pp : p * p = p) : (p - (1 - p)).det * (p - (1 - p)).det = 1 := by
  have : (p - (1 - p)) * (p - (1 - p)) = 1 := by
    simp only [mul_sub, sub_mul, pp, one_mul, mul_one]; abel
  rw [← det_mul, this, det_one]

theorem half_add_self (X : Matrix ι ι ℂ) : (1 / 2 : ℂ) • (X + X) = X := by module

theorem half_eq {p : Matrix ι ι ℂ} (pp : p * p = p) {g h : Matrix ι ι ℂ} (hg : h * g = 1) :
    (1 / 2 : ℂ) • (1 + (p - (1 - p)) * h * (p - (1 - p)) * g) =
      (p - (1 - p)) * h * (p * g * p - (1 - p) * g * (1 - p)) := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have hg' : ∀ x, h * (g * x) = x := fun x => by rw [← mul_assoc, hg, one_mul]
  rw [← half_add_self ((p - (1 - p)) * h * (p * g * p - (1 - p) * g * (1 - p)))]
  congr 1
  simp only [mul_sub, sub_mul, mul_assoc, pp, hg, hg', one_mul, mul_one]; abel

theorem det_diag {p : Matrix ι ι ℂ} (pp : p * p = p) (a : Matrix ι ι ℂ) {g h : Matrix ι ι ℂ} (hg : h * g = 1) :
    (p * a * p - (1 - p) * g * (1 - p)).det =
      (p - (1 - p)).det * (p * a + (1 - p)).det * ((p * h + (1 - p)).det * g.det) := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  rw [← det_compl pp hg, det_left pp a, ← det_mul, ← det_mul]
  congr 1
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel

theorem det_block {p : Matrix ι ι ℂ} (pp : p * p = p) {g₁ h₁ g₂ h₂ : Matrix ι ι ℂ} (hg₁ : h₁ * g₁ = 1)
    (hg₂ : h₂ * g₂ = 1) :
    (fromBlocks (p * g₁ * p - (1 - p) * g₁ * (1 - p)) (p * g₂) (-((1 - p) * g₁))
      (p * g₂ * p - (1 - p) * g₂ * (1 - p))).det =
      g₁.det * g₂.det * ((p * h₁ + (1 - p)).det * (p * g₂ + (1 - p)).det * (p * (h₂ * g₁) + (1 - p)).det) := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have gh : g₂ * h₂ = 1 := mul_eq_one_comm.1 hg₂
  have gh' : ∀ x, g₂ * (h₂ * x) = x := fun x => by rw [← mul_assoc, gh, one_mul]
  have hσ : fromBlocks p (1 - p) (1 - p) p * fromBlocks p (1 - p) (1 - p) p = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> (simp only [mul_sub, sub_mul, pp, one_mul, mul_one]; abel)
  have e : fromBlocks p (1 - p) (1 - p) p *
      fromBlocks (p * g₁ * p - (1 - p) * g₁ * (1 - p)) (p * g₂) (-((1 - p) * g₁))
      (p * g₂ * p - (1 - p) * g₂ * (1 - p)) * fromBlocks p (1 - p) (1 - p) p =
      fromBlocks ((p - (1 - p)) * g₂ * (h₂ * g₁ * p + (1 - p))) (p * g₂ * p - (1 - p) * g₁ * (1 - p)) 0
        (p * g₂ * p - (1 - p) * g₁ * (1 - p)) := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    congr 1 <;> (simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc, pp, pp', gh', one_mul, mul_one]; abel)
  have d := congrArg det e
  have dσ := congrArg det hσ
  rw [det_mul, det_one] at dσ
  rw [det_mul, det_mul, det_fromBlocks_zero₂₁, det_diag pp g₂ hg₁, det_mul, det_mul, det_right pp,
    ← det_left pp, mul_right_comm, dσ, one_mul] at d
  rw [d]
  linear_combination (g₁.det * g₂.det * ((p * h₁ + (1 - p)).det * (p * g₂ + (1 - p)).det *
    (p * (h₂ * g₁) + (1 - p)).det)) * det_sign pp

theorem detPlus_identities : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : Matrix ι ι ℂ), sᴴ = s → s * s = 1 →
    (∀ g : Matrix ι ι ℂ, gᴴ * s * g = s → dP s g⁻¹ = star (dP s g) ∧
      ((1 / 2 : ℂ) • (1 + gᴴ * g)).det = dP s g * dP s g⁻¹) ∧
    ∀ g₁ g₂ : Matrix ι ι ℂ, g₁ᴴ * s * g₁ = s → g₂ᴴ * s * g₂ = s →
      (Matrix.fromBlocks ((1 / 2 : ℂ) • (1 + g₁ᴴ * g₁)) ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂))
        ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) ((1 / 2 : ℂ) • (1 + g₂ᴴ * g₂))).det =
        dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁) := by
  intro ι _ _ s hs ss
  obtain ⟨p, hp⟩ : ∃ p : Matrix ι ι ℂ, p = (1 / 2 : ℂ) • (1 + s) := ⟨_, rfl⟩
  have pp : p * p = p := by
    rw [hp]
    simp only [smul_mul_smul_comm, mul_add, add_mul, ss, one_mul, mul_one]
    module
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have hpH : pᴴ = p := by
    rw [hp, conjTranspose_smul, conjTranspose_add, conjTranspose_one, hs]; simp
  have hsp : s = p - (1 - p) := by rw [hp]; module
  have hd : ∀ g, dP s g = (p * g + (1 - p)).det := fun g => by
    unfold dP
    rw [hp, smul_mul_assoc]
    congr 1
    module
  have key : ∀ g : Matrix ι ι ℂ, gᴴ * s * g = s → g⁻¹ * g = 1 ∧ gᴴ = s * g⁻¹ * s := fun g hg => by
    have h1 : s * gᴴ * s * g = 1 := by rw [mul_assoc s, mul_assoc s, hg, ss]
    rw [inv_eq_left_inv h1]
    refine ⟨h1, ?_⟩
    simp only [← mul_assoc, ss, one_mul]
    rw [mul_assoc, ss, mul_one]
  have ds := det_sign pp
  simp only [hd]
  refine ⟨fun g hg => ?_, fun g₁ g₂ hg₁ hg₂ => ?_⟩
  · obtain ⟨h1, h2⟩ := key g hg
    generalize g⁻¹ = h at h1 h2
    have dh := congrArg det h1
    rw [det_mul, det_one] at dh
    constructor
    · rw [← det_conjTranspose, conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hpH, h2]
      have : s * h * s * p + (1 - p) = s * (h * p + (1 - p)) * s := by
        rw [hsp]
        simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel
      rw [this, det_mul, det_mul, det_right pp, ← det_left pp, hsp, mul_right_comm, ds, one_mul]
    · rw [h2, hsp, half_eq pp h1, det_mul, det_mul, det_diag pp g h1]
      linear_combination ((p * g + (1 - p)).det * (p * h + (1 - p)).det) * (h.det * g.det) * ds +
        ((p * g + (1 - p)).det * (p * h + (1 - p)).det) * dh
  · obtain ⟨a1, a2⟩ := key g₁ hg₁
    obtain ⟨b1, b2⟩ := key g₂ hg₂
    generalize g₁⁻¹ = h₁ at a1 a2
    generalize g₂⁻¹ = h₂ at b1 b2
    have da := congrArg det a1
    have db := congrArg det b1
    rw [det_mul, det_one] at da db
    have e : Matrix.fromBlocks ((1 / 2 : ℂ) • (1 + g₁ᴴ * g₁)) ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂))
        ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) ((1 / 2 : ℂ) • (1 + g₂ᴴ * g₂)) =
        fromBlocks (s * h₁) 0 0 (s * h₂) *
          fromBlocks (p * g₁ * p - (1 - p) * g₁ * (1 - p)) (p * g₂) (-((1 - p) * g₁))
            (p * g₂ * p - (1 - p) * g₂ * (1 - p)) := by
      rw [fromBlocks_multiply, a2, b2, hsp, half_eq pp a1, half_eq pp b1]
      simp only [Matrix.zero_mul, add_zero, zero_add]
      congr 1
      · rw [← half_add_self ((p - (1 - p)) * h₁ * (p * g₂))]
        congr 1
        simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp', one_mul, mul_one]; abel
      · rw [← half_add_self ((p - (1 - p)) * h₂ * (-((1 - p) * g₁)))]
        congr 1
        simp only [mul_sub, sub_mul, mul_neg, mul_assoc, pp', one_mul, mul_one]; abel
    rw [e, det_mul, det_fromBlocks_zero₂₁, det_block pp a1 b1, det_mul, det_mul, hsp]
    generalize (p * h₁ + (1 - p)).det * (p * g₂ + (1 - p)).det * (p * (h₂ * g₁) + (1 - p)).det = T
    linear_combination T * (h₁.det * g₁.det) * (h₂.det * g₂.det) * ds + T * (h₂.det * g₂.det) * da + T * db

end GlobalTheory.RealWeil.PosDet
end

section

open MeasureTheory Filter Topology

namespace GlobalTheory.TermEst

lemma pointwise (b c θ α s t H : ℝ) (hc : 0 < c) (hθ : 1 ≤ θ) (hα : 0 < α)
    (hk : c * θ ^ 2 ≤ α * (b + c)) (hs : 0 ≤ s) (ht : 0 ≤ t) (hH : 0 ≤ H) (i m : ℕ) :
    (2 * c) ^ (i + m) / (m.factorial : ℝ) * t ^ m * (Real.exp (-((b + c) * s ^ 2)) * H * s ^ (i + m)) ≤
      θ⁻¹ ^ m * Real.exp (c * α * t ^ 2) * ((2 * c * s) ^ i * H) := by
  have hθ0 : 0 < θ := by linarith
  have e1 : (2 * c * θ * s * t) ^ m / (m.factorial : ℝ) ≤ Real.exp (2 * c * θ * s * t) :=
    Real.pow_div_factorial_le_exp _ (by positivity) m
  have e2 : 2 * c * θ * s * t ≤ c * α * t ^ 2 + (b + c) * s ^ 2 := by
    have q1 : 0 ≤ c * (α * t - θ * s) ^ 2 := by positivity
    have q2 : c * θ ^ 2 * s ^ 2 ≤ α * (b + c) * s ^ 2 := by
      exact mul_le_mul_of_nonneg_right hk (by positivity)
    have q3 : α * (2 * c * θ * s * t) ≤ α * (c * α * t ^ 2 + (b + c) * s ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left q3 hα
  have e3 : Real.exp (-((b + c) * s ^ 2)) * Real.exp (2 * c * θ * s * t) ≤ Real.exp (c * α * t ^ 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hm : (0 : ℝ) < m.factorial := by positivity
  calc (2 * c) ^ (i + m) / (m.factorial : ℝ) * t ^ m * (Real.exp (-((b + c) * s ^ 2)) * H * s ^ (i + m))
      = ((2 * c * s) ^ i * H * θ⁻¹ ^ m) *
          (Real.exp (-((b + c) * s ^ 2)) * ((2 * c * θ * s * t) ^ m / (m.factorial : ℝ))) := by
        rw [inv_pow]; field_simp; ring
    _ ≤ ((2 * c * s) ^ i * H * θ⁻¹ ^ m) *
          (Real.exp (-((b + c) * s ^ 2)) * Real.exp (2 * c * θ * s * t)) := by gcongr
    _ ≤ ((2 * c * s) ^ i * H * θ⁻¹ ^ m) * Real.exp (c * α * t ^ 2) := by gcongr
    _ = θ⁻¹ ^ m * Real.exp (c * α * t ^ 2) * ((2 * c * s) ^ i * H) := by ring

lemma norm_wt {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (h : E → ℂ) (a : E) :
    ‖GlobalTheory.ConvSeries.wt b c h a‖ = Real.exp (-((b + c) * ‖a‖ ^ 2)) * ‖h a‖ := by
  simp only [GlobalTheory.ConvSeries.wt, norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [mul_comm (Real.exp _) ‖h a‖, mul_assoc, ← Real.exp_add]
  ring_nf

theorem main : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c θ α : ℝ), 0 < c → 1 ≤ θ → 0 < α → c * θ ^ 2 ≤ α * (b + c) →
    ∀ (h : SchwartzMap E ℂ) (j i : ℕ) (y : E),
    (2 * c) ^ j / (j.factorial : ℝ) * (j.descFactorial i : ℝ) * (∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j) *
      ‖y‖ ^ (j - i) ≤ θ⁻¹ ^ (j - i) * Real.exp (c * α * ‖y‖ ^ 2) * ∫ a, (2 * c * ‖a‖) ^ i * ‖h a‖ := by
  intro E _ _ _ _ _ b c θ α hc hθ hα hk h j i y
  rcases lt_or_ge j i with hji | hij
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hji, Nat.cast_zero, mul_zero, zero_mul, zero_mul]
    exact mul_nonneg (by positivity) (integral_nonneg fun a => by positivity)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [Nat.add_sub_cancel_left]
    have hK : (2 * c) ^ (i + m) / ((i + m).factorial : ℝ) * ((i + m).descFactorial i : ℝ) =
        (2 * c) ^ (i + m) / (m.factorial : ℝ) := by
      have := Nat.factorial_mul_descFactorial (Nat.le_add_right i m)
      rw [Nat.add_sub_cancel_left] at this
      have h1 : ((i + m).factorial : ℝ) = (m.factorial : ℝ) * ((i + m).descFactorial i : ℝ) := by
        exact_mod_cast this.symm
      have h2 : (0 : ℝ) < m.factorial := by positivity
      have h3 : (0 : ℝ) < ((i + m).descFactorial i : ℝ) := by
        have : (0:ℝ) < ((i + m).factorial : ℝ) := by positivity
        rw [h1] at this
        exact pos_of_mul_pos_right this h2.le
      rw [h1]; field_simp
    rw [hK]
    have hint : Integrable (fun a : E => (2 * c * ‖a‖) ^ i * ‖h a‖) := by
      have := (h.integrable_pow_mul volume i).const_mul ((2 * c) ^ i)
      refine this.congr (Eventually.of_forall fun a => ?_)
      simp only [mul_pow]; ring
    calc (2 * c) ^ (i + m) / (m.factorial : ℝ) * (∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ (i + m)) * ‖y‖ ^ m
        = ∫ a, (2 * c) ^ (i + m) / (m.factorial : ℝ) * ‖y‖ ^ m *
            (Real.exp (-((b + c) * ‖a‖ ^ 2)) * ‖h a‖ * ‖a‖ ^ (i + m)) := by
          rw [integral_const_mul]; simp only [norm_wt]; ring
      _ ≤ ∫ a, θ⁻¹ ^ m * Real.exp (c * α * ‖y‖ ^ 2) * ((2 * c * ‖a‖) ^ i * ‖h a‖) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun a => by positivity)
            (hint.const_mul _) (Eventually.of_forall fun a => ?_)
          exact pointwise b c θ α ‖a‖ ‖y‖ ‖h a‖ hc hθ hα hk (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) i m
      _ = _ := integral_const_mul _ _

end GlobalTheory.TermEst
end

section

open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

namespace CoefNorm

theorem norm_innerC_apply_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a y : E) :
    ‖innerC a y‖ ≤ ‖a‖ * ‖y‖ := by
  simp only [innerC, ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.ofRealCLM_apply,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_real_inner_le_norm a y

theorem norm_powForm_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ) (a : E) :
    ‖powForm k a‖ ≤ ‖a‖ ^ k := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  simp only [powForm, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  rw [norm_prod]
  calc ∏ i, ‖innerC a (m i)‖ ≤ ∏ i, (‖a‖ * ‖m i‖) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => norm_innerC_apply_le a (m i)
    _ = ‖a‖ ^ k * ∏ i, ‖m i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem norm_wt_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : E → ℂ) (a : E) : ‖wt b c h a‖ ≤ ‖h a‖ := by
  unfold wt
  rw [norm_mul, norm_mul, ← Complex.ofReal_neg, ← Complex.ofReal_neg, Complex.norm_exp_ofReal,
    Complex.norm_exp_ofReal]
  have e1 : Real.exp (-(b * ‖a‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖a‖])
  have e2 : Real.exp (-(c * ‖a‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖a‖])
  calc _ ≤ 1 * ‖h a‖ * 1 := by gcongr
    _ = _ := by ring

theorem continuous_wt {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (h : E → ℂ)
    (hh : Continuous h) : Continuous (wt b c h) := by
  unfold wt
  fun_prop

end CoefNorm


open CoefNorm in
theorem norm_coef_le_integral (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : SchwartzMap E ℂ) (j : ℕ) :
    ‖coef b c (⇑h) j‖ ≤ ∫ a, ‖wt b c (⇑h) a‖ * ‖a‖ ^ j := by
  unfold coef
  refine (norm_integral_le_integral_norm _).trans ?_
  have hw : Continuous (wt b c (⇑h)) := continuous_wt b c _ h.continuous
  have hint : Integrable (fun a : E => ‖a‖ ^ j * ‖h a‖) := h.integrable_pow_mul volume j
  have hint2 : Integrable (fun a : E => ‖wt b c (⇑h) a‖ * ‖a‖ ^ j) := by
    refine hint.mono' ((hw.norm.mul (continuous_norm.pow j)).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_wt_le b c hb hc _ a) (by positivity)
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => norm_nonneg _) hint2
    (Filter.Eventually.of_forall fun a => ?_)
  simp only [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_powForm_le j a) (norm_nonneg _)

end GlobalTheory.ConvSeries
end
