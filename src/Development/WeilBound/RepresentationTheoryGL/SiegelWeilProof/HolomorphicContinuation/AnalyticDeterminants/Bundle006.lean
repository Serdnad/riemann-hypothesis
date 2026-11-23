module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle003
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem isymm (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin n → F) (π : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℂ n G x (u ∘ π) = iteratedFDeriv ℂ n G x u :=
  hG.contDiffAt.iteratedFDeriv_comp_perm u π

theorem ipeel0 (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin (n + 1) → F) :
    iteratedFDeriv ℂ (n + 1) G x u = iteratedFDeriv ℂ n (fun y => fderiv ℂ G y (u 0)) x (fun k => u k.succ) := by
  have hfd : ContDiffAt ℂ n (fderiv ℂ G) x := (hG.contDiffAt (n := ω)).fderiv_right le_top
  have happ := (ContinuousLinearMap.apply ℂ ℂ (u 0)).iteratedFDeriv_comp_left hfd (i := n) le_rfl
  have hfun : (fun y => fderiv ℂ G y (u 0)) = (ContinuousLinearMap.apply ℂ ℂ (u 0)) ∘ fderiv ℂ G := rfl
  rw [← isymm G x hG (n + 1) u (finRotate (n + 1)), iteratedFDeriv_succ_apply_right, hfun, happ]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply, finRotate_last]
  congr 2
  funext k
  simp [Fin.init, finRotate_apply, Fin.coeSucc_eq_succ]

theorem ipeel (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin (n + 1) → F) (i0 : Fin (n + 1)) :
    iteratedFDeriv ℂ (n + 1) G x u = iteratedFDeriv ℂ n (fun y => fderiv ℂ G y (u i0)) x (fun k => u (i0.succAbove k)) := by
  rw [← isymm G x hG (n + 1) u i0.cycleRange.symm, ipeel0 G x hG n]
  simp [Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ]

theorem detD_fin (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ → ℂ) (hG : AnalyticAt ℂ G 0) :
    detD G = ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ N G 0 (fun k => Matrix.single k (σ k) 1) := by
  have hgen : ∀ (m : ℕ) (h : m = N) (e : Fin m ≃ Fin N) (σ : Equiv.Perm (Fin N)),
      iteratedFDeriv ℂ m G 0 (fun i => Matrix.single (e i) (σ (e i)) (1 : ℂ)) =
      iteratedFDeriv ℂ N G 0 (fun k => Matrix.single k (σ k) 1) := by
    intro m h e σ
    subst h
    exact isymm G 0 hG m (fun k => Matrix.single k (σ k) 1) e
  unfold detD
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hgen _ (Fintype.card_fin N) _ σ]

end PositivityTheory.Rg.Sw.LVs.CK
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_entry (i j : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun x : M2 n => x i j) :=
  contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) i j

theorem xZx_apply (x Z : M2 n) (i j : Fin n ⊕ Fin n) :
    (x * Z * xᴴ) i j = ∑ l, (∑ m, x i m * Z m l) * starRingEnd ℂ (x j l) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem contDiff_xZx (Z : M2 n) (i j : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun x : M2 n => (x * Z * xᴴ) i j) := by
  simp_rw [xZx_apply]
  refine ContDiff.sum fun l _ => ContDiff.mul (ContDiff.sum fun m _ => (contDiff_entry i m).mul contDiff_const) ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_entry j l)

theorem cDiff : CDiff := by
  intro n Z a b
  exact ⟨contDiff_xZx Z (Sum.inr a) (Sum.inr b), (contDiff_xZx Z (Sum.inr a) (Sum.inl b)).neg⟩

theorem fderiv_xZx (Z x v : M2 n) (i j : Fin n ⊕ Fin n) :
    fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x v = (v * Z * xᴴ + x * Z * vᴴ) i j := by
  have hd : DifferentiableAt ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x :=
    ((contDiff_xZx Z i j).differentiable (by simp)).differentiableAt
  refine (hd.lineDeriv_eq_fderiv (v := v)).symm.trans ?_
  have e : (fun t : ℝ => ((x + t • v) * Z * (x + t • v)ᴴ) i j) = fun t : ℝ =>
      (x * Z * xᴴ) i j + (t : ℂ) * (v * Z * xᴴ + x * Z * vᴴ) i j + (t : ℂ) ^ 2 * (v * Z * vᴴ) i j := by
    funext t
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_smul]
    ring
  have hr : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have h : HasDerivAt (fun t : ℝ => ((x + t • v) * Z * (x + t • v)ᴴ) i j) ((v * Z * xᴴ + x * Z * vᴴ) i j) 0 := by
    rw [e]
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (v * Z * xᴴ + x * Z * vᴴ) i j) ((v * Z * xᴴ + x * Z * vᴴ) i j) 0 := by
      simpa using hr.mul_const ((v * Z * xᴴ + x * Z * vᴴ) i j)
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * (v * Z * vᴴ) i j) 0 0 := by
      simpa using (hr.pow 2).mul_const ((v * Z * vᴴ) i j)
    have h3 := ((hasDerivAt_const (0 : ℝ) ((x * Z * xᴴ) i j)).add h1).add h2
    refine (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv (by simp)
    simp
  simpa [lineDeriv] using h.deriv

theorem reK_add_imK (e : M2 n) : reK e + Complex.I • imK e = e := by
  simp only [reK, imK, smul_smul, smul_sub, smul_add]
  have h : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; ring
  rw [h]
  module

theorem reK_conj (e : M2 n) : (reK e)ᴴ = -reK e := by
  simp only [reK, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this]; module

theorem imK_conj (e : M2 n) : (imK e)ᴴ = -imK e := by
  simp only [imK, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  have : star (-Complex.I / 2) = -(-Complex.I / 2) := by simp [Complex.conj_I]; ring
  rw [this]; module

theorem fderiv_xZx_skew (Z x E : M2 n) (hE : Eᴴ = -E) (i j : Fin n ⊕ Fin n) :
    fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x (E * x) = (E * (x * Z * xᴴ) - (x * Z * xᴴ) * E) i j := by
  rw [fderiv_xZx, Matrix.conjTranspose_mul, hE]
  congr 1
  simp only [Matrix.mul_assoc, Matrix.mul_neg, sub_eq_add_neg]

theorem dK_xZx (Z x e : M2 n) (i j : Fin n ⊕ Fin n) :
    dK (fun y : M2 n => (y * Z * yᴴ) i j) x e = (e * (x * Z * xᴴ) - (x * Z * xᴴ) * e) i j := by
  rw [dK, fderiv_xZx_skew Z x _ (reK_conj e), fderiv_xZx_skew Z x _ (imK_conj e)]
  conv_rhs => rw [← reK_add_imK e]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem toBlocks₂₂_apply' (M : M2 n) (a b : Fin n) : M.toBlocks₂₂ a b = M (Sum.inr a) (Sum.inr b) := rfl
theorem toBlocks₁₁_apply' (M : M2 n) (a b : Fin n) : M.toBlocks₁₁ a b = M (Sum.inl a) (Sum.inl b) := rfl

theorem decomp (M : M2 n) : M = fromBlocks (M.toBlocks₁₁ - M.toBlocks₂₂) (M.toBlocks₁₂ + M.toBlocks₂₁) 0 0 +
    ∑ a, ∑ b, (M.toBlocks₂₂ a b • eA a b + (-M.toBlocks₂₁ a b) • eB a b) := by
  ext i j
  rcases i with a' | a' <;> rcases j with b' | b' <;>
    simp [eA, eB, Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

theorem eA_mul_apply (M : M2 n) (a b : Fin n) : (eA a b * M) (Sum.inr a) (Sum.inr b) = M (Sum.inr b) (Sum.inr b) := by
  simp [eA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem mul_eA_apply (M : M2 n) (a b : Fin n) : (M * eA a b) (Sum.inr a) (Sum.inr b) = M (Sum.inr a) (Sum.inr a) := by
  simp [eA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem eB_mul_apply (M : M2 n) (a b : Fin n) : (eB a b * M) (Sum.inr a) (Sum.inl b) = -M (Sum.inl b) (Sum.inl b) := by
  simp [eB, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem mul_eB_apply (M : M2 n) (a b : Fin n) : (M * eB a b) (Sum.inr a) (Sum.inl b) = -M (Sum.inr a) (Sum.inr a) := by
  simp [eB, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem sumA (M : M2 n) : ∑ a, ∑ b, ((eA a b * M - M * eA a b : M2 n) (Sum.inr a) (Sum.inr b)) = 0 := by
  simp only [Matrix.sub_apply, eA_mul_apply, mul_eA_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => M (Sum.inr b) (Sum.inr b))]
  simp

theorem sumB (M : M2 n) : ∑ a, ∑ b, -((eB a b * M - M * eB a b : M2 n) (Sum.inr a) (Sum.inl b)) =
    (n : ℂ) * (M.toBlocks₁₁.trace - M.toBlocks₂₂.trace) := by
  simp only [Matrix.sub_apply, eB_mul_apply, mul_eB_apply, neg_sub, neg_neg, sub_neg_eq_add, Finset.sum_sub_distrib]
  simp only [Matrix.trace, Matrix.diag, toBlocks₁₁_apply', toBlocks₂₂_apply', Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_sub]
  have h : ∀ a b : Fin n, -(-M (Sum.inl b) (Sum.inl b) + M (Sum.inr a) (Sum.inr a)) =
      M (Sum.inl b) (Sum.inl b) - M (Sum.inr a) (Sum.inr a) := fun _ _ => by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.mul_sum]

theorem ptId : PtId := by
  intro n Θ x Z hx hΘ hlaw
  set M := x * Z * xᴴ with hM
  have hxZ : x * Z = M * x := by rw [hM, Matrix.mul_assoc (x * Z), hx.2, Matrix.mul_one]
  have hΘd : DifferentiableAt ℂ Θ x := hΘ.differentiableAt (by simp)
  have hR : ∀ v, fderiv ℝ Θ x v = fderiv ℂ Θ x v := fun v => by
    have h := (hΘd.hasFDerivAt.restrictScalars ℝ).fderiv
    exact (congrArg (fun L => L v) h).trans rfl
  have hdK : ∀ e, dK Θ x e = fderiv ℂ Θ x (e * x) := fun e => by
    rw [dK, hR, hR]
    conv_rhs => rw [← reK_add_imK e]
    rw [Matrix.add_mul, Matrix.smul_mul, map_add (f := _), map_smul, smul_eq_mul]
  have hLeib : ∀ c : M2 n → ℂ, DifferentiableAt ℝ c x → ∀ e,
      dK (fun y => c y * Θ y) x e = dK c x e * Θ x + c x * dK Θ x e := fun c hc e => by
    have hΘr : DifferentiableAt ℝ Θ x := hΘd.restrictScalars ℝ
    have h := (hc.hasFDerivAt.mul hΘr.hasFDerivAt).fderiv
    have hv : ∀ v, fderiv ℝ (fun y => c y * Θ y) x v = c x * fderiv ℝ Θ x v + Θ x * fderiv ℝ c x v := fun v => by
      exact (congrArg (fun L : M2 n →L[ℝ] ℂ => L v) h).trans rfl
    simp only [dK, hv]
    ring
  have hcA : ∀ a b, DifferentiableAt ℝ (cA Z a b) x := fun a b =>
    ((cDiff n Z a b).1.differentiable (by simp)).differentiableAt
  have hcB : ∀ a b, DifferentiableAt ℝ (cB Z a b) x := fun a b =>
    ((cDiff n Z a b).2.differentiable (by simp)).differentiableAt
  have hdA : ∀ a b e, dK (cA Z a b) x e = (e * M - M * e) (Sum.inr a) (Sum.inr b) := fun a b e =>
    dK_xZx Z x e (Sum.inr a) (Sum.inr b)
  have hdB : ∀ a b e, dK (cB Z a b) x e = -((e * M - M * e) (Sum.inr a) (Sum.inl b)) := fun a b e => by
    have : cB Z a b = fun y => -((y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) := rfl
    have hd : DifferentiableAt ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x :=
      ((contDiff_xZx Z _ _).differentiable (by simp)).differentiableAt
    have hn := hd.hasFDerivAt.neg.fderiv
    have hv : ∀ v, fderiv ℝ (fun y : M2 n => -(y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v =
        -fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v := fun v => by
      exact (congrArg (fun L : M2 n →L[ℝ] ℂ => L v) hn).trans rfl
    have h := dK_xZx Z x e (Sum.inr a) (Sum.inl b)
    rw [dK] at h
    rw [this, dK, hv, hv, ← h]; ring

  have hL : fderiv ℂ Θ x (x * Z) = (n : ℂ) * (M.toBlocks₁₁.trace - M.toBlocks₂₂.trace) * Θ x +
      ∑ a, ∑ b, (cA Z a b x * dK Θ x (eA a b) + cB Z a b x * dK Θ x (eB a b)) := by
    rw [hxZ]
    conv_lhs => rw [decomp M]
    rw [Matrix.add_mul, map_add (f := _), hlaw _ (by simp)]

    simp only [Matrix.sum_mul, map_sum, Matrix.add_mul, Matrix.smul_mul, map_add (f := _), map_smul, smul_eq_mul, hdK]
    congr 1
    · simp [Matrix.trace_sub]
  rw [hL]
  simp only [hLeib _ (hcA _ _), hLeib _ (hcB _ _), hdA, hdB]
  have e1 : ∀ a b, (eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) * Θ x + cA Z a b x * dK Θ x (eA a b) +
      (-((eB a b * M - M * eB a b) (Sum.inr a) (Sum.inl b)) * Θ x + cB Z a b x * dK Θ x (eB a b)) =
      ((eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) + -((eB a b * M - M * eB a b) (Sum.inr a) (Sum.inl b))) * Θ x +
      (cA Z a b x * dK Θ x (eA a b) + cB Z a b x * dK Θ x (eB a b)) := fun a b => by ring
  simp only [e1, Finset.sum_add_distrib, ← Finset.sum_mul, sumA, sumB]
  ring

end PositivityTheory.Rg.Sw.LVs.II
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Cmi (n : ℕ) : M2 n :=
  fromBlocks ((-Complex.I / 2) • 1) ((1 / 2 : ℂ) • 1) ((Complex.I / 2) • 1) ((1 / 2 : ℂ) • 1)

theorem cm_mul_cmi : Cm n * Cmi n = 1 := by
  rw [Cm, Cmi, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases h : i = j <;>
    simp [Matrix.one_apply, h, Matrix.add_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring_nf

theorem cm_inv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv cm_mul_cmi

theorem toBlocks₂₁_mul (A B : M2 n) :
    (A * B).toBlocks₂₁ = A.toBlocks₂₁ * B.toBlocks₁₁ + A.toBlocks₂₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem toBlocks₂₂_mul (A B : M2 n) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem mul_cm₂₁ (x : M2 n) : (x * Cm n).toBlocks₂₁ = u1 x := by
  rw [toBlocks₂₁_mul, u1, Cm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one]

theorem mul_cm₂₂ (x : M2 n) : (x * Cm n).toBlocks₂₂ = u2 x := by
  rw [toBlocks₂₂_mul, u2, Cm, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, Matrix.mul_neg,
    Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one]

theorem first_cayley_block_mul_inverse_cayley (y : M2 n) : u1 (y * Cmi n) = y.toBlocks₂₁ := by
  rw [u1, toBlocks₂₁_mul, toBlocks₂₂_mul, Cmi]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

theorem second_cayley_block_mul_inverse_cayley (y : M2 n) : u2 (y * Cmi n) = y.toBlocks₂₂ := by
  rw [u2, toBlocks₂₁_mul, toBlocks₂₂_mul, Cmi]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

theorem uAct : UAct := by
  intro n x P Q R S
  simp only [mX, cm_inv, ← Matrix.mul_assoc]
  rw [first_cayley_block_mul_inverse_cayley, second_cayley_block_mul_inverse_cayley, toBlocks₂₁_mul (x * Cm n) (fromBlocks P Q R S),
    toBlocks₂₂_mul (x * Cm n) (fromBlocks P Q R S), mul_cm₂₁, mul_cm₂₂]
  simp

def incl (s : Finset (Fin n)) : Matrix (Fin n) s ℂ := Matrix.of fun c i => if c = (i : Fin n) then 1 else 0

def subOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix s s ℂ :=
  M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n))

theorem minorOn_eq (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : minorOn s M = (subOn s M).det := rfl

theorem sum_incl (s : Finset (Fin n)) (a : Fin n) (f : s → ℂ) :
    ∑ i : s, (if a = (i : Fin n) then (1 : ℂ) else 0) * f i = if h : a ∈ s then f ⟨a, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro i _ hi
      have : a ≠ (i : Fin n) := fun e => hi (Subtype.ext e.symm)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : a ≠ (i : Fin n) := fun e => h (e ▸ i.2)
    simp [this]

theorem embOn_eq (s : Finset (Fin n)) (T : Matrix s s ℂ) : embOn s T = incl s * T * (incl s)ᵀ := by
  ext a b
  simp only [Matrix.mul_apply, incl, Matrix.of_apply, Matrix.transpose_apply]
  simp only [sum_incl]
  simp only [mul_comm _ (ite (b = _) _ _)]
  rw [sum_incl]
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> simp [embOn, ha, hb]

theorem incl_mul (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : (incl s)ᵀ * M * incl s = subOn s M := by
  ext i j
  simp [Matrix.mul_apply, incl, subOn, Matrix.transpose_apply]

theorem det_one_add_mul_embOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) (T : Matrix s s ℂ) :
    (1 + M * embOn s T).det = (1 + subOn s M * T).det := by
  rw [embOn_eq]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.det_one_add_mul_comm]
  simp only [← Matrix.mul_assoc]
  rw [incl_mul]

theorem detD_const_mul {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℂ) (F : Matrix ι ι ℂ → ℂ) :
    detD (fun S => c * F S) = c * detD F := by
  by_cases hc : c = 0
  · subst hc
    simp [detD]
  · let g : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hc)
    have hfun : (fun S => c * F S) = g ∘ F := by
      funext S
      simp [g, mul_comm]
    unfold detD
    rw [hfun, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ContinuousLinearEquiv.iteratedFDeriv_comp_left]
    (simp [g]) <;> ring

theorem card_blkA {j : ℕ} (hj : j ≤ n) : Fintype.card (blkA (n := n) j) = j := by
  rw [Fintype.card_coe, blkA, Fin.card_filter_val_lt, min_eq_right hj]

theorem card_blkB {j : ℕ} (hj : j ≤ n) : Fintype.card (blkB (n := n) j) = n - j := by
  rw [Fintype.card_coe, blkB, Finset.card_compl, Fintype.card_fin, ← Fintype.card_coe, card_blkA hj]

theorem scalar_section_mul_block_unipotent {p q : ℤ} {j : ℕ} {x : M2 n} (h1 : (u1 x).det ≠ 0) (h2 : (u2 x).det ≠ 0)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      (f0 p q x * (1 + subOn (blkA j) (wM x) * T).det ^ (-q)) *
        (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ (-p) := by
  have hd1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h1
  have hd2 : IsUnit (u2 x).det := isUnit_iff_ne_zero.2 h2
  have k1 : u1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      u1 x * (1 + (wM x)⁻¹ * embOn (blkB j) S) := by
    rw [(uAct n x _ _ _ _).1, wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd2]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd1, Matrix.one_mul,
      Matrix.mul_one]
  have k2 : u2 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      u2 x * (1 + wM x * embOn (blkA j) T) := by
    rw [(uAct n x _ _ _ _).2, wM]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd2, Matrix.one_mul,
      Matrix.mul_one]
    abel
  rw [f0, f0, k1, k2, Matrix.det_mul, Matrix.det_mul, det_one_add_mul_embOn, det_one_add_mul_embOn,
    mul_zpow, mul_zpow]
  ring

theorem djSec_of (hC : Cayley) : DjSec := by
  intro n j p q x hj h1 h2
  have hin : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      (detD fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) =
      (f0 p q x * (∏ i ∈ Finset.range (n - j), (-(p : ℂ) + i)) * minorOn (blkB j) (wM x)⁻¹) *
        (1 + subOn (blkA j) (wM x) * T).det ^ (-q) := by
    intro T
    simp_rw [scalar_section_mul_block_unipotent h1 h2 T]
    rw [detD_const_mul, hC, card_blkB hj, minorOn_eq]
    push_cast
    ring
  simp_rw [hin]
  rw [detD_const_mul, hC, card_blkA hj]
  simp only [minorOn_eq]
  push_cast
  ring

end PositivityTheory.Rg.Sw.LVs
end
end
