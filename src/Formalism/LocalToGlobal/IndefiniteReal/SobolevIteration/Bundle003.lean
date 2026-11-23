module

import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfSt
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.L2.Theta Formalism.IndefR.Datum Matrix Filter Topology
open scoped ComplexOrder

namespace Formalism.IndefR.Tow.SobPf

section Gen

variable {n : ℕ}

theorem det_G_unit {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsUnit G.det := by
  rw [isUnit_iff_ne_zero]
  have h1 := hs.2.2.det_pos.ne'
  rw [Matrix.det_mul] at h1
  exact left_ne_zero_of_mul h1

theorem det_UH_unit {G g : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    IsUnit g.det := by
  have h : gᴴ * G * g = G := hg
  have h' := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h'
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h'
  exact hG.ne_zero h'.symm

theorem inv_mem_UH {G g : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have hd := det_UH_unit hG hg
  have h : gᴴ * G * g = G := hg
  show (g⁻¹)ᴴ * G * g⁻¹ = G
  calc (g⁻¹)ᴴ * G * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * G * g) * g⁻¹ := by rw [h]
    _ = (g * g⁻¹)ᴴ * G * (g * g⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [mul_assoc]
    _ = G := by rw [Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one, one_mul, mul_one]

theorem conj_mem_lieG {G g X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (hX : X ∈ lieG G) : g⁻¹ * X * g ∈ lieG G := by
  apply Formalism.IndefR.Tow.SobPf.Avg.conj_mem_lieG <;> assumption

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem deriv_clm_inv (A B : H →L[ℂ] H) (hBA : ∀ v, B (A v) = v) (f : ℝ → H) :
    deriv (fun t => A (f t)) 0 = A (deriv f 0) := by
  by_cases hf : DifferentiableAt ℝ f 0
  · exact ((A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hf.hasDerivAt).deriv
  · have hAf : ¬ DifferentiableAt ℝ (fun t => A (f t)) 0 := by
      intro h
      apply hf
      have e : (fun t => B (A (f t))) = f := funext fun t => hBA (f t)
      rw [← e]
      exact (B.restrictScalars ℝ).differentiableAt.comp 0 h
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hAf, map_zero]

theorem dRep_rep {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) (hG : IsUnit G.det) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (u : H) :
    dRep π X (π g u) = π g (dRep π (g⁻¹ * X * g) u) := by
  have hd := det_UH_unit hG hg
  have hY := conj_mem_lieG hG hg hX
  have hfun : (fun t : ℝ => π (NormedSpace.exp (t • X)) (π g u)) =
      fun t : ℝ => π g (π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) := by
    funext t
    have he : NormedSpace.exp (t • X) * g = g * NormedSpace.exp (t • (g⁻¹ * X * g)) := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul,
        Matrix.exp_conj' g (t • X) ((Matrix.isUnit_iff_isUnit_det _).2 hd)]
      simp only [← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul]
    calc π (NormedSpace.exp (t • X)) (π g u) = π (NormedSpace.exp (t • X) * g) u := by
          rw [hπ.2.1 _ (expS_mem_UH hX t) _ hg]; rfl
      _ = π (g * NormedSpace.exp (t • (g⁻¹ * X * g))) u := by rw [he]
      _ = π g (π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) := by
          rw [hπ.2.1 _ hg _ (expS_mem_UH hY t)]; rfl
  have hBA : ∀ v, π g⁻¹ (π g v) = v := by
    intro v
    rw [← ContinuousLinearMap.comp_apply, ← hπ.2.1 _ (inv_mem_UH hG hg) _ hg, Matrix.nonsing_inv_mul _ hd, hπ.1]
    rfl
  show deriv (fun t : ℝ => π (NormedSpace.exp (t • X)) (π g u)) 0 =
    π g (deriv (fun t : ℝ => π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) 0)
  rw [hfun]
  exact deriv_clm_inv (π g) (π g⁻¹) hBA _

theorem dL_rep {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) (hG : IsUnit G.det) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ lieG G) (u : H) :
    dL π l (π g u) = π g (dL π (l.map fun X => g⁻¹ * X * g) u) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    show dRep π X (dL π l (π g u)) = π g (dRep π (g⁻¹ * X * g) (dL π (l.map fun X => g⁻¹ * X * g) u))
    rw [ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)), dRep_rep hπ hG hg (hl X (by simp)) _]

end Gen

theorem foldBddK_of (h4 : SobChart) : FoldBddK := by
  intro n H _ _ G s π hs hπ w hw l hl
  have hG := det_G_unit hs
  have hc1 : Cont1 := continuity_of_sobolev_chart h4 foldCont_holds
  have hcont : ContinuousOn (fun k : Fin n → Fin n → ℂ => dL π l (π (Matrix.of k) w))
      {k | Matrix.of k ∈ KAt G s} := by
    intro k0 hk0
    have hk0K : Matrix.of k0 ∈ KAt G s := hk0
    have hk0U : Matrix.of k0 ∈ Formalism.QuantumDeterminants.UH G := hk0K.1
    have hd := det_UH_unit hG hk0U
    have hl' : ∀ X ∈ l.map (fun X => (Matrix.of k0)⁻¹ * X * Matrix.of k0), X ∈ lieG G := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact conj_mem_lieG hG hk0U (hl Y hY)
    refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hδ'⟩ := hc1 G s π hs hπ w hw _ hl' ε hε
    have hO : IsOpen {k : Fin n → Fin n → ℂ |
        ∀ i j, ‖((Matrix.of k0)⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ} := by
      have hc : ∀ i j, Continuous fun k : Fin n → Fin n → ℂ =>
          ‖((Matrix.of k0)⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ := fun i j =>
        (((continuous_const.matrix_mul
          (continuous_id' : Continuous fun k : Fin n → Fin n → ℂ => Matrix.of k)).matrix_elem i j).sub
            continuous_const).norm
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt (hc i j) continuous_const
    have hk0O : ∀ i j, ‖((Matrix.of k0)⁻¹ * Matrix.of k0) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ := by
      intro i j
      rw [Matrix.nonsing_inv_mul _ hd, sub_self, norm_zero]
      exact hδ
    obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO k0 hk0O
    refine ⟨ρ, hρ, fun {k} hk hdk => ?_⟩
    have hkK : Matrix.of k ∈ KAt G s := hk
    have hkU : Matrix.of k ∈ Formalism.QuantumDeterminants.UH G := hkK.1
    have hg : (Matrix.of k0)⁻¹ * Matrix.of k ∈ Formalism.QuantumDeterminants.UH G := mul_mem_UH₂ G _ (inv_mem_UH hG hk0U) _ hkU
    have hnear := hρO (Metric.mem_ball.2 hdk)
    have hkk : π (Matrix.of k) w = π (Matrix.of k0) (π ((Matrix.of k0)⁻¹ * Matrix.of k) w) := by
      rw [← ContinuousLinearMap.comp_apply, ← hπ.2.1 _ hk0U _ hg, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
    rw [dist_eq_norm]
    rw [hkk, dL_rep hπ hG hk0U l hl, dL_rep hπ hG hk0U l hl, ← map_sub, hπ.2.2.1 _ hk0U]
    exact hδ' _ hg hnear
  have hK : IsCompact {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isCompact_KAt hs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  exact ⟨C, fun k hk => hC (Matrix.of.symm k) hk⟩

end Formalism.IndefR.Tow.SobPf

end
end

section

noncomputable section

open Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace Chart

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

theorem oneProd_succ {d : ℕ} (Y : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (t : Fin (d + 1) → ℝ) :
    oneProd Y t = NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) := by
  unfold oneProd
  rw [List.ofFn_succ, List.prod_cons]

theorem oneProd_zero : ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), oneProd Y 0 = 1 := by
  intro d Y
  simp [oneProd, NormedSpace.exp_zero]

theorem oneProd_mem (G : Matrix (Fin n) (Fin n) ℂ) :
    ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Y i ∈ lieG G) → ∀ t : Fin d → ℝ,
      oneProd Y t ∈ Formalism.QuantumDeterminants.UH G := by
  intro d
  induction d with
  | zero =>
    intro Y _ t
    have h1 : oneProd Y t = 1 := by simp [oneProd]
    rw [h1]
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G
    simp
  | succ d ih =>
    intro Y hY t
    rw [oneProd_succ]
    exact mul_mem_UH₂ G _ (expS_mem_UH (hY 0) (t 0)) _ (ih _ (fun i => hY i.succ) _)

def lin {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) : (Fin d → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (Y i)

theorem lin_apply {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ) :
    lin Y t = ∑ i, t i • Y i := by
  unfold lin
  simp

theorem hasStrictFDerivAt_oneProd : ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ),
    HasStrictFDerivAt (oneProd Y) (lin Y) 0 := by
  intro d
  induction d with
  | zero =>
    intro Y
    have h1 : oneProd Y = fun _ => 1 := funext fun t => by simp [oneProd]
    have h2 : lin Y = 0 := ContinuousLinearMap.ext fun t => by simp [lin_apply]
    rw [h1, h2]
    exact hasStrictFDerivAt_const _ _
  | succ d ih =>
    intro Y
    have hsplit : oneProd Y = fun t : Fin (d + 1) → ℝ =>
        NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) :=
      funext fun t => oneProd_succ Y t
    let L0 : (Fin (d + 1) → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      (ContinuousLinearMap.proj (0 : Fin (d + 1))).smulRight (Y 0)
    let T : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
    have ha : HasStrictFDerivAt (fun t : Fin (d + 1) → ℝ => NormedSpace.exp (t 0 • Y 0)) L0 0 := by
      have hz : L0 0 = 0 := map_zero L0
      have he : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
          (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (L0 0) := by
        rw [hz]
        exact hasStrictFDerivAt_exp_zero
      exact (he.comp (0 : Fin (d + 1) → ℝ) L0.hasStrictFDerivAt).congr_fderiv
        (ContinuousLinearMap.ext fun t => rfl)
    have hb : HasStrictFDerivAt (fun t : Fin (d + 1) → ℝ => oneProd (fun i => Y i.succ) (fun i => t i.succ))
        ((lin fun i => Y i.succ).comp T) 0 := by
      have hz : T 0 = 0 := map_zero T
      have hi : HasStrictFDerivAt (oneProd fun i => Y i.succ) (lin fun i => Y i.succ) (T 0) := by
        rw [hz]
        exact ih _
      exact hi.comp (0 : Fin (d + 1) → ℝ) T.hasStrictFDerivAt
    have hb0 : oneProd (fun i => Y i.succ) (fun _ => (0 : ℝ)) = 1 := oneProd_zero _
    have hm := ha.mul' hb
    rw [hsplit]
    refine hm.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun t => ?_
    have e1 : NormedSpace.exp ((0 : Fin (d + 1) → ℝ) 0 • Y 0) = 1 := by simp
    have e2 : oneProd (fun i => Y i.succ) (fun i => (0 : Fin (d + 1) → ℝ) i.succ) = 1 := hb0
    show NormedSpace.exp ((0 : Fin (d + 1) → ℝ) 0 • Y 0) * (lin (fun i => Y i.succ) (T t)) +
      L0 t * oneProd (fun i => Y i.succ) (fun i => (0 : Fin (d + 1) → ℝ) i.succ) = lin Y t
    rw [e1, e2, one_mul, mul_one, lin_apply, lin_apply, Fin.sum_univ_succ]
    exact add_comm _ _

end Chart

end Formalism.IndefR.Tow.SobPf

end
end
