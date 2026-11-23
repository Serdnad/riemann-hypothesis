module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.UHMulInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateNormInequalities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

theorem gN_eq_frob {k r : ℕ} (g : Mat k r) : gN g = ‖g‖ := by
  rw [frobenius_norm_def, gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

theorem gN_mul_le {k r : ℕ} (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact frobenius_norm_mul A B

theorem gN_conjTranspose {k r : ℕ} (A : Mat k r) : gN Aᴴ = gN A := by
  rw [gN_eq_frob, gN_eq_frob, frobenius_norm_conjTranspose]

end frob

theorem gN_nonneg {k r : ℕ} (A : Mat k r) : 0 ≤ gN A := Real.sqrt_nonneg _

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_out k r h j

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mid k r h j

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mulVec k r v i

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mulVec_mulVec k r v

theorem mat_eq_of_mulVec' {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_sq k r

theorem UH_left_inv {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_left_inv k r hg

theorem GV_mul {g x : Mat k r} (hg : g ∈ GV k r) (hx : x ∈ GV k r) : g * x ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

end hpk

theorem gN_le_mul {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) (x : Mat k r) :
    gN x ≤ gN (Hpk k r) ^ 2 * (gN g * gN (g * x)) := by
  have hx : x = Hpk k r * gᴴ * Hpk k r * (g * x) := by
    rw [← Matrix.mul_assoc, UH_left_inv k r hg, Matrix.one_mul]
  have h0 := gN_nonneg (Hpk k r)
  calc gN x = gN (Hpk k r * gᴴ * Hpk k r * (g * x)) := by rw [← hx]
    _ ≤ gN (Hpk k r * gᴴ * Hpk k r) * gN (g * x) := gN_mul_le _ _
    _ ≤ gN (Hpk k r) * gN g * gN (Hpk k r) * gN (g * x) := by
        gcongr
        · exact gN_nonneg _
        · calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le _ _
            _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) := by gcongr; exact gN_mul_le _ _
            _ = gN (Hpk k r) * gN g * gN (Hpk k r) := by rw [gN_conjTranspose]
    _ = gN (Hpk k r) ^ 2 * (gN g * gN (g * x)) := by ring

theorem real_key {A B X c a b : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hX : 0 < X) (hc : 0 < c) (hb : 0 ≤ b)
    (hab : b ≤ a) (hXle : X ≤ c * (B * A)) :
    A ^ (-a) * B ^ (-a) ≤ (X * c⁻¹) ^ (-(a - b)) * B ^ (-b) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hP : 0 < B * A := mul_pos hB0 hA0
  have e1 : A ^ (-a) * B ^ (-a) = (B * A) ^ (-(a - b)) * (B * A) ^ (-b) := by
    rw [← Real.rpow_add hP, Real.mul_rpow hB0.le hA0.le, mul_comm]; ring_nf
  rw [e1]
  have hXc : 0 < X * c⁻¹ := mul_pos hX (inv_pos.2 hc)
  have h1 : (B * A) ^ (-(a - b)) ≤ (X * c⁻¹) ^ (-(a - b)) := by
    refine Real.rpow_le_rpow_of_nonpos hXc ?_ (by linarith)
    rw [mul_inv_le_iff₀ hc]; linarith [hXle]
  have h2 : (B * A) ^ (-b) ≤ B ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos hB0 (by nlinarith) (by linarith)
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hP.le _) (Real.rpow_nonneg hXc.le _)

theorem AB_le_AG (k r : ℕ) : AB k r ≤ AG k r + 1 := by
  simp only [AB, AG, nR]
  push_cast
  nlinarith [sq_nonneg ((k : ℝ) + r - (r + 1)), (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
    (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

end ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateNormInequalities
end
end

section

noncomputable section

open MeasureTheory ComplexConjugate
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open ConjugateHilbertSpace

theorem schurDichotomy : SchurDichotomy := by
  intro G _ _ _ _ _ μ _ _ _ H _ _ _ _ θ ρ hθc hθm hθθ hmap hρ1 hρm hiso hcont hsq hirr
  classical
  have hθ1 : θ 1 = 1 := by
    have h := hθm 1 1
    rw [one_mul] at h
    exact mul_left_cancel (a := θ 1) (by rw [mul_one]; exact h.symm)
  have hθinv : ∀ a, θ a⁻¹ = (θ a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_left
    rw [← hθm, mul_inv_cancel, hθ1]
  have hθmp : MeasurePreserving θ μ μ := ⟨hθc.measurable, hmap⟩
  have hR : Formalism.MainNotions.BridgeCSchur.SqRep μ ρ := ⟨hρ1, hρm, hiso, hcont, hsq⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : G → (Cj H →L[ℂ] Cj H),
      ∀ g v, τ g v = toCj (ρ (θ g)⁻¹ (ofCj v)) :=
    ⟨fun g => opCj (ρ (θ g)⁻¹), fun g v => opCj_apply _ _⟩
  have hcoef : ∀ g (v w : Cj H), ⟪w, τ g v⟫_ℂ = ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ := by
    intro g v w
    rw [inner_def, hτ]
    have h := hR.inner_left (θ g)⁻¹ (ofCj v) (ofCj w)
    rw [inv_inv] at h
    exact h
  have hT : Formalism.MainNotions.BridgeCSchur.SqRep μ τ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext v
      simp only [hτ, hθ1, inv_one, hρ1]
      rfl
    · intro a b
      ext v
      simp only [ContinuousLinearMap.comp_apply, hτ]
      rw [hθm, mul_inv_rev, hρm]
      rfl
    · intro g v
      rw [hτ]
      exact hiso _ _
    · intro v
      have e : (fun g => τ g v) = fun g => toCj (ρ (θ g)⁻¹ (ofCj v)) := funext fun g => hτ g v
      rw [e]
      exact (hcont (ofCj v)).comp hθc.inv
    · intro v w
      have e : (fun g => ⟪w, τ g v⟫_ℂ) = fun g => ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ :=
        funext fun g => hcoef g v w
      rw [e]
      exact (hsq (ofCj w) (ofCj v)).comp_measurePreserving hθmp
  have hirrT : ∀ S : Submodule ℂ (Cj H), IsClosed (S : Set (Cj H)) →
      (∀ g, ∀ v ∈ S, τ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS hSi
    let S' : Submodule ℂ H :=
      { carrier := {x | toCj x ∈ S}
        add_mem' := fun ha hb => S.add_mem ha hb
        zero_mem' := S.zero_mem
        smul_mem' := fun c x hx => by
          have h2 := S.smul_mem (conj c) (show toCj x ∈ S from hx)
          rw [smul_def, Complex.conj_conj] at h2
          show toCj (c • x) ∈ S
          exact h2 }
    have hS'c : IsClosed (S' : Set H) := hS.preimage (eCj (H := H)).symm.continuous
    have hS'i : ∀ h, ∀ x ∈ S', ρ h x ∈ S' := by
      intro h x hx
      have h2 := hSi (θ h⁻¹) (toCj x) hx
      rw [hτ, hθθ, inv_inv] at h2
      exact h2
    rcases hirr S' hS'c hS'i with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have h3 : ofCj v ∈ S' := hv
      rw [h, Submodule.mem_bot] at h3
      exact h3
    · right
      rw [eq_top_iff]
      intro v _
      have h3 : ofCj v ∈ S' := by rw [h]; trivial
      exact h3
  by_cases hne : ∃ U : Cj H ≃ₗᵢ[ℂ] H, ∀ g v, U (τ g v) = ρ g (U v)
  · right
    obtain ⟨U, hU⟩ := hne
    refine ⟨((eCj (H := H)).symm.trans U : H ≃ₗᵢ⋆[ℂ] H), ?_, ?_⟩
    · intro g x y
      calc ⟪y, ρ (θ g) x⟫_ℂ = ⟪toCj x, τ g (toCj y)⟫_ℂ := (hcoef g (toCj y) (toCj x)).symm
        _ = ⟪U (toCj x), U (τ g (toCj y))⟫_ℂ := (U.inner_map_map _ _).symm
        _ = ⟪U (toCj x), ρ g (U (toCj y))⟫_ℂ := by rw [hU]
    · intro h v
      have h2 := hU (θ h)⁻¹ (toCj v)
      rw [hτ, hθinv, hθθ, inv_inv] at h2
      exact h2
  · left
    intro x y x' y'
    have h0 := Formalism.MainNotions.BridgeCSchur.schur_orth_ineq hT hR hirrT hirr hne (toCj y) (toCj x) x' y'
    have e : (fun g => ⟪y, ρ (θ g) x⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ) =
        fun g => ⟪toCj x, τ g (toCj y)⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ :=
      funext fun g => congrArg (· * star ⟪y', ρ g x'⟫_ℂ) (hcoef g (toCj y) (toCj x)).symm
    exact (congrArg (fun f => ∫ g, f g ∂μ) e).trans h0

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.HilbertSchmidtFunctionals

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem hilbertSchmidt_vec_add (A B : Wp →L[ℂ] Wp) : hsVec (A + B) = hsVec A + hsVec B := by
  ext i
  simp [hsVec]

theorem hilbertSchmidt_vec_smul (c : ℂ) (A : Wp →L[ℂ] Wp) : hsVec (c • A) = c • hsVec A := by
  ext i
  simp [hsVec]

def hilbertSchmidtFunctional (X₀ : Wp →L[ℂ] Wp) : (Wp →L[ℂ] Wp) →ₗ[ℂ] ℂ where
  toFun T := hsInner T X₀
  map_add' A B := by simp only [hsInner, hilbertSchmidt_vec_add, inner_add_right]
  map_smul' c A := by simp only [hsInner, hilbertSchmidt_vec_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul]

def hilbertSchmidtContinuousFunctional (X₀ : Wp →L[ℂ] Wp) : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (hilbertSchmidtFunctional X₀)

theorem hilbertSchmidt_functional_apply (X₀ T : Wp →L[ℂ] Wp) : hilbertSchmidtContinuousFunctional X₀ T = hsInner T X₀ := by
  rfl

theorem hilbertSchmidt_inner_smul_left (c : ℂ) (A B : Wp →L[ℂ] Wp) : hsInner (c • A) B = c * hsInner A B := by
  simp only [hsInner, hilbertSchmidt_vec_smul, inner_smul_right]

section adj

variable [CompleteSpace Wp] {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

theorem integrable_adjoint {U : α → Wp →L[ℂ] Wp} (hU : Integrable U μ) :
    Integrable (fun a => ContinuousLinearMap.adjoint (U a)) μ := by
  refine hU.congr' (ContinuousLinearMap.adjoint.continuous.comp_aestronglyMeasurable hU.1) ?_
  exact Filter.Eventually.of_forall fun a => (ContinuousLinearMap.adjoint.norm_map (U a)).symm

theorem integral_adjoint_comm {U : α → Wp →L[ℂ] Wp} (hU : Integrable U μ) :
    ∫ a, ContinuousLinearMap.adjoint (U a) ∂μ = ContinuousLinearMap.adjoint (∫ a, U a ∂μ) := by
  exact ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul
    (ContinuousLinearMap.adjoint : (Wp →L[ℂ] Wp) ≃ₗᵢ⋆[ℂ] (Wp →L[ℂ] Wp)).toContinuousLinearEquiv.toContinuousLinearMap hU

variable [SFinite μ] [SFinite ν]

theorem integrable_hilbertSchmidt_pairing (X₀ : Wp →L[ℂ] Wp) {U : α → Wp →L[ℂ] Wp} {V : β → Wp →L[ℂ] Wp}
    (hU : Integrable U μ) (hV : Integrable V ν) :
    Integrable (fun q : α × β => hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2))) (μ.prod ν) := by
  have hG : Continuous fun x : (Wp →L[ℂ] Wp) × (Wp →L[ℂ] Wp) =>
      hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint x.1).comp x.2) :=
    (hilbertSchmidtContinuousFunctional X₀).continuous.comp
      ((ContinuousLinearMap.adjoint.continuous.comp continuous_fst).clm_comp continuous_snd)
  have hm : AEStronglyMeasurable
      (fun q : α × β => hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2))) (μ.prod ν) :=
    Continuous.comp_aestronglyMeasurable₂
      (g := fun A B : Wp →L[ℂ] Wp => hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint A).comp B)) hG
      (hU.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
      (hV.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hb : Integrable (fun q : α × β => ‖hilbertSchmidtContinuousFunctional X₀‖ * (‖U q.1‖ * ‖V q.2‖)) (μ.prod ν) :=
    (hU.norm.mul_prod hV.norm).const_mul _
  refine hb.mono' hm (Filter.Eventually.of_forall fun q => ?_)
  calc ‖hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2))‖
      ≤ ‖hilbertSchmidtContinuousFunctional X₀‖ * ‖(ContinuousLinearMap.adjoint (U q.1)).comp (V q.2)‖ :=
        (hilbertSchmidtContinuousFunctional X₀).le_opNorm _
    _ ≤ ‖hilbertSchmidtContinuousFunctional X₀‖ * (‖U q.1‖ * ‖V q.2‖) := by
        gcongr
        calc ‖(ContinuousLinearMap.adjoint (U q.1)).comp (V q.2)‖
            ≤ ‖ContinuousLinearMap.adjoint (U q.1)‖ * ‖V q.2‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ = ‖U q.1‖ * ‖V q.2‖ := by rw [ContinuousLinearMap.adjoint.norm_map]

theorem integral_hilbertSchmidt_pairing (X₀ : Wp →L[ℂ] Wp) {U : α → Wp →L[ℂ] Wp} {V : β → Wp →L[ℂ] Wp}
    (hU : Integrable U μ) (hV : Integrable V ν) :
    ∫ q, hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2)) ∂(μ.prod ν) =
      hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (∫ a, U a ∂μ)).comp (∫ b, V b ∂ν)) := by
  rw [integral_prod _ (integrable_hilbertSchmidt_pairing X₀ hU hV)]
  have hin : ∀ a, ∫ b, hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U a)).comp (V b)) ∂ν =
      hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U a)).comp (∫ b, V b ∂ν)) := fun a =>
    ((hilbertSchmidtContinuousFunctional X₀).comp (ContinuousLinearMap.compL ℂ Wp Wp Wp (ContinuousLinearMap.adjoint (U a)))).integral_comp_comm hV
  simp_rw [hin]
  have hout := ((hilbertSchmidtContinuousFunctional X₀).comp
    ((ContinuousLinearMap.compL ℂ Wp Wp Wp).flip (∫ b, V b ∂ν))).integral_comp_comm (integrable_adjoint hU)
  rw [integral_adjoint_comm hU] at hout
  exact hout

end adj

theorem sigmaFinite_of_haar_on {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem ae_mem_big_cell (D : RealPlaceData k r Wp Wp) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have := sigmaFinite_of_haar_on D.haarW
  have := sigmaFinite_of_haar_on D.haarN
  have := sigmaFinite_of_haar_on D.haarW'
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := ae_iff.2 D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := ae_iff.2 D.haarN.conc
  have hW' : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' := ae_iff.2 D.haarW'.conc
  have h1 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hW)
  have h2 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  have h3 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.1 ∈ UWset k r D.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hW')
  have h4 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [h1, h2, h3, h4] with p a b c d
  exact ⟨a, b, c, d⟩

theorem linear_form_continuous (z : Fin (2 * r + k + 1) → ℂ) : Continuous (ell k r z) := by
  unfold ell
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [h, dite_true]
    exact continuous_id.matrix_elem _ _
  · simp only [h, dite_false]
    exact (continuous_apply (eI k r a)).comp (continuous_id.matrix_mulVec continuous_const)

theorem character_continuous (D : RealPlaceData k r Wp Wp) (τ : ℝ × ℝ) : Continuous (xiTau D τ) := by
  have hl : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun n : Mt k r => lam k r z (Matrix.of n) :=
    fun z => Complex.continuous_re.comp (continuous_const.mul ((linear_form_continuous z).comp continuous_id))
  unfold xiTau
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact (continuous_const.mul ((hl D.z).comp (continuous_snd.comp continuous_fst))).sub
    (continuous_const.mul ((hl D.z').comp (continuous_snd.comp continuous_snd)))

theorem norm_character_eq_one (D : RealPlaceData k r Wp Wp) (τ : ℝ × ℝ) (p : SS k r) : ‖xiTau D τ p‖ = 1 := by
  unfold xiTau
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem star_character_mul_self (D : RealPlaceData k r Wp Wp) (τ : ℝ × ℝ) (p : SS k r) :
    star (xiTau D τ p) * xiTau D τ p = 1 := by
  rw [Complex.star_def, Complex.conj_mul', norm_character_eq_one]
  simp

theorem character_at_one_eq_product (D : RealPlaceData k r Wp Wp) (hz : D.z' = D.z) (p : SS k r) :
    xiTau D (1, 1) p = psiD D (Matrix.of p.1.2) * star (psiD D (Matrix.of p.2.2)) := by
  unfold xiTau psiD psi lam
  rw [hz, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem adjoint_representation_inv [CompleteSpace Wp] (D : RealPlaceData k r Wp Wp) (hCW : IsClosedSubgroup (UWset k r D.z))
    {h : Mat k r} (hh : h ∈ UWset k r D.z) : ContinuousLinearMap.adjoint (D.π h⁻¹) = D.π h := by
  have hi : h⁻¹ ∈ UWset k r D.z := hCW.inv_mem h hh
  have h1 : (D.π h).comp (D.π h⁻¹) = 1 := by
    rw [← D.π_rep.2 h hh h⁻¹ hi, Matrix.mul_nonsing_inv _ (hCW.unit h hh), D.π_rep.1]
  have hA : (ContinuousLinearMap.adjoint (D.π h)).comp (D.π h) = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (D.π h)).1 (D.π_unitary h hh)
  have hadj : ContinuousLinearMap.adjoint (D.π h) = D.π h⁻¹ := by
    calc ContinuousLinearMap.adjoint (D.π h)
        = (ContinuousLinearMap.adjoint (D.π h)).comp ((D.π h).comp (D.π h⁻¹)) := by
          rw [h1]; rfl
      _ = ((ContinuousLinearMap.adjoint (D.π h)).comp (D.π h)).comp (D.π h⁻¹) := by
          rw [ContinuousLinearMap.comp_assoc]
      _ = D.π h⁻¹ := by rw [hA]; rfl
  rw [← hadj, ContinuousLinearMap.adjoint_adjoint]

end ReciprocityTheory.ChartRestriction.DS.Mult1.HilbertSchmidtFunctionals
end
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def StBeHerm : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ

def StBePos : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ u ∈ Vfl X, ∀ ξ : Wp, 0 ≤ (⟪ξ, beOp D X u u ξ⟫_ℂ).re

def StSchurW : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp), IsDiag D → ∀ v w v' w' : Wp,
    ∫ h : Mt k r, ⟪w, D.π (Matrix.of h) v⟫_ℂ * star ⟪w', D.π (Matrix.of h) v'⟫_ℂ ∂D.μW =
      ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (Module.finrank ℂ Wp : ℂ)

def StSInt : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp), IsDiag D → ∀ b : ℝ, AB k r ≤ b →
    Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) (D.μW.prod D.μN)

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
