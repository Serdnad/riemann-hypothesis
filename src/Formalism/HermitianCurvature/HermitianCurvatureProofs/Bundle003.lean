module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Finset
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section hilbert

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_sum_smul (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (J : Finset κ)
    (a : κ → ℂ) (P : κ → ι) :
    ⟪∑ j ∈ J, a j • v (P j), ∑ l ∈ J, a l • v (P l)⟫_ℂ =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * k (P j) (P l) := by
  rw [sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_sum, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [inner_smul_right, hv]
  ring

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem form_sum_conj (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (y : κ → V) :
    B (∑ j ∈ J, conj (a j) • y j) (∑ l ∈ J, conj (a l) • y l) =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * B (y j) (y l) := by
  rw [LinearMap.map_sum₂]
  refine sum_congr rfl fun j _ => ?_

  rw [map_smul, LinearMap.smul_apply, map_sum, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [map_smulₛₗ, smul_eq_mul, Complex.conj_conj]
  ring

theorem norm_sq_sum_eq_form (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → V)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 = (B (∑ j ∈ J, conj (a j) • y j) (∑ j ∈ J, conj (a j) • y j)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sum_smul k v hv, form_sum_conj, RCLike.re_to_complex]
  congr 1
  refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => ?_
  rw [hy j hj l hl]

theorem norm_sum_le_of_form {W : Type*} [SeminormedAddCommGroup W] [Module ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (Cp : ℝ) (hCp : 0 ≤ Cp)
    (hB : ∀ x, (B x x).re ≤ (Cp * ‖x‖) ^ 2) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → W)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ Cp * ‖∑ j ∈ J, conj (a j) • y j‖ := by
  have h := norm_sq_sum_eq_form k v hv B J a P y hy
  have h2 := hB (∑ j ∈ J, conj (a j) • y j)
  rw [← h] at h2
  exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2 |> fun h3 => by
    simpa [abs_of_nonneg (norm_nonneg _)] using (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

end hilbert

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

section

open MeasureTheory Module Set
open scoped Nat

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem norm_iteratedFDeriv_id_le (j : ℕ) (x : V) : ‖iteratedFDeriv ℝ j (id : V → V) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | _ | m
  · rw [norm_iteratedFDeriv_zero]
    simp
  · rw [norm_iteratedFDeriv_one, fderiv_id]
    exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
  · rw [iteratedFDeriv_succ_eq_comp_right]
    have e : (fun y : V => fderiv ℝ (id : V → V) y) = fun _ => ContinuousLinearMap.id ℝ V := by
      funext y
      exact fderiv_id
    rw [e, iteratedFDeriv_const_of_ne (by omega : m + 1 ≠ 0)]
    simp
    positivity

theorem norm_iteratedFDeriv_inner_self_le (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => inner ℝ y y) x‖ ≤ 2 ^ n * (1 + ‖x‖) ^ 2 := by
  have hB := (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear
    (f := (id : V → V)) (g := (id : V → V)) (N := ⊤) contDiff_id contDiff_id x (n := n) le_top
  have e : (fun y : V => (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) (id y) (id y)) = fun y : V => inner ℝ y y := by
    funext y
    simp
  rw [e] at hB
  have hnB : ‖(innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ)‖ ≤ 1 := norm_innerSL_le ℝ
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖ ≤ 2 ^ n * (1 + ‖x‖) ^ 2 := by
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) * (1 + ‖x‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := norm_iteratedFDeriv_id_le i x
          have h2 := norm_iteratedFDeriv_id_le (n - i) x
          gcongr
      _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [this]
          ring
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖ := Finset.sum_nonneg fun i _ => by positivity
  calc ‖iteratedFDeriv ℝ n (fun y : V => inner ℝ y y) x‖ ≤ _ := hB
    _ ≤ 1 * (2 ^ n * (1 + ‖x‖) ^ 2) := mul_le_mul hnB hsum hS0 zero_le_one
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := one_mul _

theorem norm_iteratedFDerivWithin_inv_one_le (i : ℕ) :
    ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t⁻¹) (Ioi 0) 1‖ ≤ i ! := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    (iteratedDerivWithin_of_isOpen isOpen_Ioi) (show (1 : ℝ) ∈ Ioi 0 by norm_num), iteratedDeriv_eq_iterate]
  have e : (fun t : ℝ => t⁻¹) = Inv.inv := rfl
  rw [e, iter_deriv_inv]
  simp

theorem norm_iteratedFDeriv_u_le (k : ℕ) (x₀ : V) :
    ‖iteratedFDeriv ℝ k (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x₀‖ ≤ (k ! * k ! * 4 ^ k) * (1 + ‖x₀‖ ^ 2)⁻¹ := by
  set q₀ : ℝ := 1 + ‖x₀‖ ^ 2 with hq₀
  have hq₀pos : 0 < q₀ := by positivity
  set f : V → ℝ := fun y => q₀⁻¹ * (1 + inner ℝ y y) with hf
  have hfpos : ∀ y, 0 < f y := fun y => by
    simp only [hf, real_inner_self_eq_norm_sq]; positivity
  have hfc : ContDiff ℝ k f :=
    contDiff_const.mul (contDiff_const.add (contDiff_id.inner ℝ contDiff_id))
  have hfx : f x₀ = 1 := by
    simp only [hf, real_inner_self_eq_norm_sq]
    rw [← hq₀]
    exact inv_mul_cancel₀ hq₀pos.ne'
  have hu : (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) = q₀⁻¹ • ((fun t : ℝ => t⁻¹) ∘ f) := by
    funext y
    simp only [hf, Pi.smul_apply, Function.comp, real_inner_self_eq_norm_sq, smul_eq_mul]
    field_simp
  have hgc : ContDiff ℝ k ((fun t : ℝ => t⁻¹) ∘ f) :=
    hfc.inv fun y => (hfpos y).ne'
  rw [hu, iteratedFDeriv_const_smul_apply (hgc.contDiffAt), norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hq₀pos), mul_comm]
  gcongr
  have hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x₀‖ ≤ 4 ^ i := by
    intro i hi _
    have e : f = (fun _ : V => q₀⁻¹) + q₀⁻¹ • (fun y : V => inner ℝ y y) := by
      funext y; simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hin : ContDiff ℝ i (fun y : V => inner ℝ y y) := contDiff_id.inner ℝ contDiff_id
    have hc2 : ContDiffAt ℝ i (q₀⁻¹ • (fun y : V => inner ℝ y y)) x₀ :=
      ((hin.const_smul q₀⁻¹ : ContDiff ℝ i (q₀⁻¹ • (fun y : V => inner ℝ y y)))).contDiffAt
    have hc1 : ContDiffAt ℝ i (fun _ : V => q₀⁻¹) x₀ := contDiffAt_const
    rw [e, iteratedFDeriv_add_apply hc1 hc2,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add,
      iteratedFDeriv_const_smul_apply hin.contDiffAt, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 hq₀pos)]
    have h1 := norm_iteratedFDeriv_inner_self_le i x₀
    have h2 : (1 + ‖x₀‖) ^ 2 ≤ 2 * q₀ := by
      rw [hq₀]; nlinarith [sq_nonneg (‖x₀‖ - 1)]
    have h3 : (2 : ℝ) ^ i * 2 ≤ 4 ^ i := by
      have : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
      rw [this]
      gcongr
      exact le_self_pow₀ (by norm_num) (by omega)
    calc q₀⁻¹ * ‖iteratedFDeriv ℝ i (fun y : V => inner ℝ y y) x₀‖ ≤ q₀⁻¹ * (2 ^ i * (2 * q₀)) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = 2 ^ i * 2 := by field_simp
      _ ≤ 4 ^ i := h3
  have hC : ∀ i, i ≤ k → ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t⁻¹) (Ioi 0) (f x₀)‖ ≤ k ! := by
    intro i hi
    rw [hfx]
    exact (norm_iteratedFDerivWithin_inv_one_le i).trans (by exact_mod_cast Nat.factorial_le hi)
  have hmain := norm_iteratedFDeriv_comp_le' (N := (k : ℕ∞)) (t := Ioi (0 : ℝ))
    (by rintro _ ⟨y, rfl⟩; exact hfpos y) (uniqueDiffOn_Ioi 0)
    (ContDiffOn.mono (contDiffOn_inv (𝕜 := ℝ)) (fun t (ht : t ∈ Ioi (0 : ℝ)) => (ne_of_gt ht : t ≠ 0))) hfc le_rfl x₀ hC hD
  calc ‖iteratedFDeriv ℝ k ((fun t : ℝ => t⁻¹) ∘ f) x₀‖ ≤ k ! * k ! * 4 ^ k := hmain
    _ = k ! * k ! * 4 ^ k := rfl

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

section

namespace Formalism.FourierDecayAlt.P.Herglotz

open Real Filter Topology Finset

variable {d : ℕ}

noncomputable def ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))

lemma ee_eq (x : Fin d → ℝ) (σ : Fin d → ℤ) :
    ee x σ = Complex.exp (((2 * π * ∑ j, (σ j : ℝ) * x j : ℝ) : ℂ) * Complex.I) := by
  unfold ee
  congr 1
  push_cast
  ring

lemma norm_ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ‖ee x σ‖ = 1 := by
  rw [ee_eq]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ee_mul_conj (x : Fin d → ℝ) (σ σ' : Fin d → ℤ) :
    ee x σ * starRingEnd ℂ (ee x σ') = ee x (σ - σ') := by
  rw [ee_eq, ee_eq, ee_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring

end Formalism.FourierDecayAlt.P.Herglotz

namespace Formalism.FourierDecayAlt.P

open Real Filter Topology Finset Formalism.FourierDecayAlt.P.Herglotz

end Formalism.FourierDecayAlt.P
end

section

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

section vand

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def vN (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.vandermonde fun m : Fin (d + 1) => ((m : ℕ) : ℂ)

theorem vN_det (d : ℕ) : IsUnit (vN d).det := by
  rw [isUnit_iff_ne_zero, vN, Matrix.det_vandermonde_ne_zero_iff]
  intro a b h
  have h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := h
  exact Fin.ext (by exact_mod_cast h')

theorem coeff_of_values (d : ℕ) (c : Fin (d + 1) → E) (n : Fin (d + 1)) :
    ∑ m, (vN d)⁻¹ n m • ∑ n' : Fin (d + 1), ((((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' = c n := by
  have hinv : (vN d)⁻¹ * vN d = 1 := Matrix.nonsing_inv_mul _ (vN_det d)
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ n' : Fin (d + 1), ∑ m, ((vN d)⁻¹ n m * (((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' =
      ((vN d)⁻¹ * vN d) n n' • c n' := by
    intro n'
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
  simp_rw [e, hinv, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

end vand

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem poly_integral (μ : Measure X) (d : ℕ) (I : ℝ → X → E) (T : X → E) (hI : ∀ y, Integrable (I y) μ)
    (hP : ∀ᵐ x ∂μ, ∃ c : Fin (d + 1) → E, c (Fin.last d) = T x ∧ ∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n) :
    ∃ c : Fin (d + 1) → E, c (Fin.last d) = ∫ x, T x ∂μ ∧
      ∀ y : ℝ, ∫ x, I y x ∂μ = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  set W := (vN d)⁻¹ with hW

  set C : Fin (d + 1) → X → E := fun n x => ∑ m, W n m • I ((m : ℕ) : ℝ) x with hC
  have hCint : ∀ n, Integrable (C n) μ := fun n =>
    integrable_finsetSum _ fun m _ => (hI _).smul (W n m)

  have hae : ∀ᵐ x ∂μ, (∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • C n x) ∧ C (Fin.last d) x = T x := by
    filter_upwards [hP] with x ⟨c, hc, hcx⟩
    have hCc : ∀ n, C n x = c n := by
      intro n
      rw [hC]
      simp only
      simp_rw [hcx]
      have := coeff_of_values d c n
      simpa [hW] using this
    refine ⟨fun y => ?_, by rw [hCc, hc]⟩
    rw [hcx y]
    simp_rw [hCc]
  refine ⟨fun n => ∫ x, C n x ∂μ, ?_, fun y => ?_⟩
  · exact integral_congr_ae (hae.mono fun x hx => hx.2)
  · rw [integral_congr_ae (hae.mono fun x hx => hx.1 y)]
    have := integral_finsetSum (μ := μ) Finset.univ (f := fun (n : Fin (d + 1)) x => ((y : ℂ) ^ (n : ℕ)) • C n x)
      (fun n _ => (hCint n).smul _)
    rw [this]
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_smul]

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end
