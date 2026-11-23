module

public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
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

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology

variable {J : Type} [Fintype J] {D : ℕ}

theorem adens_maDensity_eq_maDens (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    maDensity φ z = ReciprocityTheory.AnForm.maDens φ z := rfl

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder

section Poly

variable {J : Type} [Fintype J]

theorem adens_hasFDerivAt_eval (F : MvPolynomial J ℂ) (z : J → ℂ) :
    HasFDerivAt (fun w => eval w F)
      (∑ i, eval z (pderiv i F) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) i) z := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]
    exact hasFDerivAt_const a z
  | add p q hp hq =>
    simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p n hp =>
    classical
    have h := hp.mul (hasFDerivAt_apply n z)
    have hf : (fun w : J → ℂ => eval w (p * X n)) = fun w => eval w p * w n := by
      funext w
      simp
    rw [hf]
    refine h.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    have h1 : ∀ x, eval z (pderiv x (X n : MvPolynomial J ℂ)) = if x = n then 1 else 0 := by
      intro x
      rw [pderiv_X]
      by_cases hx : x = n
      · subst hx
        simp
      · simp [hx]
    have h2 : ∀ x, eval z (pderiv x (p * X n)) =
        eval z p * (if x = n then 1 else 0) + z n * eval z (pderiv x p) := by
      intro x
      rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul, h1, eval_X]
    have h3 : ∑ x, eval z (pderiv x (p * X n)) * v x =
        eval z p * v n + z n * ∑ x, eval z (pderiv x p) * v x := by
      simp only [h2, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum, mul_assoc]
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h3.symm

end Poly

variable {J : Type} [Fintype J] {D : ℕ}

theorem adens_contDiffAt_logρ_id {m : ConeMetric (C := ℂ) (ι := J)}
    (hsm : IsSmoothMetric m) {z : J → ℂ}
    (hne : z ≠ 0) : ContDiffAt ℝ 2 (fun w => Real.log (m.ρ w)) z := by
  have hρ : ContDiffAt ℝ 2 m.ρ z :=
    (hsm.contDiffAt (isOpen_ne.mem_nhds hne)).of_le (WithTop.coe_le_coe.2 le_top)
  exact hρ.log (m.pos _ hne).ne'

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Complex Filter Topology Finset Matrix

open MvPolynomial Complex Filter Topology

section

variable {D : ℕ}

theorem bilinear_real_imag_expand {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (a b : Fin D → ℝ) (e f : Fin D → V) :
    B (∑ i, (a i • e i + b i • f i)) (∑ j, (a j • e j + b j • f j)) =
      ∑ i, ∑ j, (a i * a j * B (e i) (e j) + a i * b j * B (e i) (f j) +
        b i * a j * B (f i) (e j) + b i * b j * B (f i) (f j)) := by
  have key : ∀ (u w : Fin D → V), B (∑ i, u i) (∑ j, w j) = ∑ i, ∑ j, B (u i) (w j) := by
    intro u w

    simp only [map_sum, ContinuousLinearMap.sum_apply]
    first
      | rfl
      | exact Finset.sum_comm
  rw [key]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add (f := _), map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem decompose_real_imag_basis (v : Fin D → ℂ) :
    v = ∑ i, ((v i).re • (Pi.single i (1 : ℂ) : Fin D → ℂ) +
      (v i).im • (I • (Pi.single i (1 : ℂ) : Fin D → ℂ))) := by
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Finset.sum_add_distrib]
  apply Complex.ext <;> simp

theorem leviForm_eq_complexHessian (φ : (Fin D → ℂ) → ℝ) (y w : Fin D → ℂ) :
    (fderiv ℝ (fderiv ℝ φ) y w w + fderiv ℝ (fderiv ℝ φ) y (I • w) (I • w)) / 4 =
      (∑ i, ∑ j, starRingEnd ℂ (w i) * cxHessian φ y j i * w j).re := by
  have hw := decompose_real_imag_basis w
  have hIw : I • w = ∑ i, ((-(w i).im) • (Pi.single i (1 : ℂ) : Fin D → ℂ) +
      (w i).re • (I • (Pi.single i (1 : ℂ) : Fin D → ℂ))) := by
    rw [decompose_real_imag_basis (I • w)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]
  have e1 := bilinear_real_imag_expand (fderiv ℝ (fderiv ℝ φ) y) (fun i => (w i).re) (fun i => (w i).im)
      (fun i => (Pi.single i (1 : ℂ) : Fin D → ℂ)) (fun i => I • (Pi.single i (1 : ℂ) : Fin D → ℂ))
  have e2 := bilinear_real_imag_expand (fderiv ℝ (fderiv ℝ φ) y) (fun i => -(w i).im) (fun i => (w i).re)
      (fun i => (Pi.single i (1 : ℂ) : Fin D → ℂ)) (fun i => I • (Pi.single i (1 : ℂ) : Fin D → ℂ))
  simp only [← hw] at e1
  simp only [← hIw] at e2
  rw [e1, e2, ← Finset.sum_add_distrib]
  simp only [Complex.re_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin D))) (t := Finset.univ)
    (f := fun i j => ((starRingEnd ℂ) (w i) * cxHessian φ y j i * w j).re)]
  rw [div_eq_iff (by norm_num : (4 : ℝ) ≠ 0), Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [cxHessian]
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_re, Complex.div_im, Complex.conj_re,
    Complex.conj_im, Complex.normSq]
  ring

end

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory

variable {J : Type} [Fintype J]

def secFun (b : MvPolynomial J ℚ) (z : J → ℂ) : ℂ :=
  eval z (map (algebraMap ℚ ℂ) b)

def wgt (m : ConeMetric (C := ℂ) (ι := J)) (n : ℕ) (z : J → ℂ) : ℝ :=
  (m.ρ z ^ (2 * n))⁻¹

def logRatio (m₀ m₁ : ConeMetric (C := ℂ) (ι := J)) (z : J → ℂ) : ℝ :=
  Real.log (m₁.ρ z / m₀.ρ z)

theorem _root_.ReciprocityTheory.ChartRestriction.G.Geo.ConeMetric.nonneg
    (m : ConeMetric (C := ℂ) (ι := J)) (z : J → ℂ) :
    0 ≤ m.ρ z := by
  by_cases hz : z = 0
  · subst hz
    have h := m.smul 0 0
    rw [zero_smul, norm_zero, zero_mul] at h
    exact le_of_eq h.symm
  · exact (m.pos z hz).le

def interp (m₀ m₁ : ConeMetric (C := ℂ) (ι := J)) (t : ℝ) :
    ConeMetric (C := ℂ) (ι := J) where
  ρ z := m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t
  pos z hz := mul_pos (Real.rpow_pos_of_pos (m₀.pos z hz) _) (Real.rpow_pos_of_pos (m₁.pos z hz) _)
  smul c z := by
    rw [m₀.smul, m₁.smul, Real.mul_rpow (norm_nonneg c) (m₀.nonneg z),
      Real.mul_rpow (norm_nonneg c) (m₁.nonneg z)]
    have key : ‖c‖ ^ (1 - t) * ‖c‖ ^ t = ‖c‖ := by
      rcases eq_or_lt_of_le (norm_nonneg c) with h | h
      · rw [← h]
        by_cases ht : t = 0
        · simp [ht]
        · simp [Real.zero_rpow ht]
      · rw [← Real.rpow_add h]
        simp
    calc ‖c‖ ^ (1 - t) * m₀.ρ z ^ (1 - t) * (‖c‖ ^ t * m₁.ρ z ^ t)
        = (‖c‖ ^ (1 - t) * ‖c‖ ^ t) * (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) := by ring
      _ = ‖c‖ * (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) := by rw [key]

def mixPot (m₀ m₁ : ConeMetric (C := ℂ) (ι := J)) (D i : ℕ) : Fin D → (J → ℂ) → ℝ :=
  fun j z => if j.val < i then Real.log (m₁.ρ z) else Real.log (m₀.ρ z)

def purePot (m : ConeMetric (C := ℂ) (ι := J)) (D : ℕ) : Fin D → (J → ℂ) → ℝ :=
  fun _ z => Real.log (m.ρ z)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end
