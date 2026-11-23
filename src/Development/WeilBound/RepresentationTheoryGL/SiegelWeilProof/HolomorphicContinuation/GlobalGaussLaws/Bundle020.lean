module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Matrix ContDiff
open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.OpGenAH

section Local

variable {m n : ℕ}

local notation "EE" => (Fin m → Fin n → ℂ)

theorem isSch_add' {f g : EE → ℂ} (hf : IsSch f) (hg : IsSch g) : IsSch (fun u => f u + g u) := by
  obtain ⟨S, rfl⟩ := hf
  obtain ⟨T, rfl⟩ := hg
  exact ⟨S + T, by ext u; simp⟩

theorem isSch_cmul (c : ℂ) {f : EE → ℂ} (hf : IsSch f) : IsSch (fun u => c * f u) := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨c • S, by ext u; simp⟩

def rmulEquiv (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : EE ≃L[ℝ] EE :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => (Matrix.of u * a : Matrix (Fin m) (Fin n) ℂ)
      invFun := fun u => (Matrix.of u * a⁻¹ : Matrix (Fin m) (Fin n) ℂ)
      map_add' := fun u v => by
        show Matrix.of (u + v) * a = Matrix.of u * a + Matrix.of v * a
        rw [← Matrix.add_mul]; rfl
      map_smul' := fun c u => by
        show Matrix.of (c • u) * a = c • (Matrix.of u * a)
        ext i j
        simp [Matrix.mul_apply, Finset.smul_sum, mul_assoc]
      left_inv := fun u => by
        show Matrix.of u * a * a⁻¹ = u
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]; rfl
      right_inv := fun u => by
        show Matrix.of u * a⁻¹ * a = u
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.mul_one]; rfl }

theorem isSch_rmul (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) {f : EE → ℂ} (hf : IsSch f) :
    IsSch (fun u => f (Matrix.of u * a)) := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rmulEquiv a ha) S, by ext u; rfl⟩

theorem hasTemperateGrowth_expI : (fun t : ℝ => Complex.exp (Complex.I * t)).HasTemperateGrowth := by
  have key : ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) =
      fun t : ℝ => Complex.I ^ k * Complex.exp (Complex.I * (t : ℂ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      have h1 : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) (Complex.I * 1) t :=
        ((hasDerivAt_id t).ofReal_comp).const_mul Complex.I
      have h2 := (h1.cexp).const_mul (Complex.I ^ k)
      rw [h2.deriv]
      ring
  refine ⟨ContDiff.cexp (contDiff_const.mul Complex.ofRealCLM.contDiff), fun k => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, key]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, pow_zero]
  rw [mul_comm Complex.I (x : ℂ), Complex.norm_exp_ofReal_mul_I]

def coordL (a : Fin m) (i : Fin n) : EE →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

theorem hasTemperateGrowth_evX (P : PX m n) : (fun u : EE => evX P u).HasTemperateGrowth := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have e : (fun u : EE => evX (C c) u) = fun _ => c := by ext u; simp [evX]
    rw [e]
    exact Function.HasTemperateGrowth.const c
  | add p q hp hq =>
    have e : (fun u : EE => evX (p + q) u) = (fun u : EE => evX p u) + (fun u : EE => evX q u) := by
      ext u; simp [evX]
    rw [e]
    exact hp.add hq
  | mul_X p k hp =>
    have hk : (fun u : EE => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1).HasTemperateGrowth := by
      by_cases h : k.2.2
      · simp only [h, ite_true]
        exact ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).comp (coordL k.1 k.2.1)).hasTemperateGrowth
      · simp only [h]
        exact (coordL k.1 k.2.1).hasTemperateGrowth
    have e : (fun u : EE => evX (p * X k) u) =
        (fun u : EE => evX p u) * (fun u : EE => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1) := by
      ext u; simp [evX]
    rw [e]
    exact hp.mul hk

theorem gramX_herm (ε : Fin m → Bool) (u : EE) : (gramX ε u)ᴴ = gramX ε u := by
  ext i j

  simp [Matrix.conjTranspose_apply, gramX, Qp, Qb, evX, map_sum, mul_comm]

theorem trace_real (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) (u : EE) :
    (((b * gramX ε u).trace.re : ℝ) : ℂ) = (b * gramX ε u).trace := by
  have h : star (b * gramX ε u).trace = (b * gramX ε u).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, gramX_herm, hb, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.1 h

theorem hasTemperateGrowth_phase (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    (fun u : EE => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace)).HasTemperateGrowth := by
  have hP : (fun u : EE => (b * gramX ε u).trace) =
      fun u => evX (∑ i, ∑ j, MvPolynomial.C (b i j) * Qp ε j i) u := by
    funext u

    simp [evX, gramX, Matrix.trace, Matrix.mul_apply, map_sum]
  have hT : (fun u : EE => (b * gramX ε u).trace).HasTemperateGrowth := by
    rw [hP]
    exact hasTemperateGrowth_evX _
  have hR : (fun u : EE => t * (b * gramX ε u).trace.re).HasTemperateGrowth := by
    have h1 := ((t • Complex.reCLM : ℂ →L[ℝ] ℝ).hasTemperateGrowth).comp hT
    convert h1 using 1
    funext u
    simp
  have h3 := hasTemperateGrowth_expI.comp hR
  convert h3 using 1
  funext u
  simp only [Function.comp_apply, Complex.ofReal_mul, trace_real ε b hb u, mul_assoc]

theorem isSch_phase (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) {f : EE → ℂ}
    (hf : IsSch f) : IsSch (fun u => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace) * f u) := by
  obtain ⟨S, rfl⟩ := hf
  refine ⟨SchwartzMap.smulLeftCLM ℂ
    (fun u : EE => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace)) S, ?_⟩
  ext u
  simp [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase ε t b hb)]

theorem exists_isSch_one : ∃ f : EE → ℂ, IsSch f ∧ f 0 = 1 := by
  let β : ContDiffBump (0 : EE) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun u : EE => ((β u : ℝ) : ℂ)) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  have h2 : ContDiff ℝ ∞ (fun u : EE => ((β u : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp β.contDiff
  refine ⟨_, ⟨h1.toSchwartzMap h2, rfl⟩, ?_⟩
  simp [β.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]

end Local

theorem _root_.PositivityTheory.Rg.Sw.Glob.schOps : SchOps := fun _ _ =>
  ⟨fun _ _ hf hg => isSch_add' hf hg, fun c _ hf => isSch_cmul c hf, fun a _ ha hf => isSch_rmul a ha hf,
    fun ε t b _ hb hf => isSch_phase ε t b hb hf, exists_isSch_one⟩

end PositivityTheory.Rg.Sw.Glob.OpGenAH
end
end

section

noncomputable section

open Matrix Topology Filter
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DBoundAH

variable {n : ℕ}

def rowC {m : ℕ} (u : Fin m → Fin n → ℂ) (a : Fin m) : Fin n → ℂ := fun j => star (u a j)

theorem trace_gramB {m : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (Z * gramB ε b u).trace = ∑ a ∈ Finset.univ.filter (fun a => ε a = b),
      star (rowC u a) ⬝ᵥ (Z *ᵥ rowC u a) := by

  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramB, evX, Qb, map_sum, map_mul, MvPolynomial.eval_X,
  dotProduct, Matrix.mulVec, rowC, Pi.star_apply, star_star, Finset.mul_sum, Finset.sum_mul]
  simp only [Bool.true_eq_false, if_true, if_false]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun a _ => ?_))
  simp only [Bool.false_eq_true, if_false]
  ring

theorem star_dot_conjTranspose (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    star w ⬝ᵥ (Zᴴ *ᵥ w) = star (star w ⬝ᵥ (Z *ᵥ w)) := by
  simp only [dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem im_eq_re (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    (star w ⬝ᵥ (Z *ᵥ w)).im = (star w ⬝ᵥ (((-(Complex.I / 2)) • (Z - Zᴴ)) *ᵥ w)).re := by
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub, star_dot_conjTranspose]
  simp only [smul_eq_mul, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem norm_star_dotProduct_mulVec_le_sum_norm_mul (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    ‖star w ⬝ᵥ (M *ᵥ w)‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ∑ j, ‖w j‖ ^ 2 := by
  have hS : ∀ i j, ‖w i‖ * ‖w j‖ ≤ ∑ k, ‖w k‖ ^ 2 := by
    intro i j
    have hi : ‖w i‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
    have hj : ‖w j‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
    nlinarith [sq_nonneg (‖w i‖ - ‖w j‖), norm_nonneg (w i), norm_nonneg (w j)]
  calc ‖star w ⬝ᵥ (M *ᵥ w)‖ = ‖∑ i, ∑ j, star (w i) * (M i j * w j)‖ := by
        simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ‖star (w i) * (M i j * w j)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ = ∑ i, ∑ j, ‖M i j‖ * (‖w i‖ * ‖w j‖) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [norm_mul, norm_mul, norm_star]
          ring
    _ ≤ ∑ i, ∑ j, ‖M i j‖ * ∑ k, ‖w k‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hS i j) (norm_nonneg _)
    _ = (∑ i, ∑ j, ‖M i j‖) * ∑ k, ‖w k‖ ^ 2 := by simp [Finset.sum_mul]

private theorem exists_pos_mul_sum_sq_le_re_of_posDef (H0 : Matrix (Fin n) (Fin n) ℂ) (h0 : H0.PosDef) :
    ∃ c > 0, ∀ w : Fin n → ℂ, c * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (H0 *ᵥ w)).re := by
  classical
  have hA := h0.1
  have hspec : H0 = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ i, c ≤ hA.eigenvalues i := by
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, _, hi0⟩ := Finset.exists_min_image Finset.univ hA.eigenvalues Finset.univ_nonempty
      exact ⟨hA.eigenvalues i0, h0.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ i)⟩
  refine ⟨c, hc, fun w => ?_⟩
  have hsv : star w ᵥ* (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
      star (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) := by
    rw [Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have h1 : star w ⬝ᵥ (H0 *ᵥ w) = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) *
      (star ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i) *
        ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i)) := by
    conv_lhs => rw [hspec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hsv]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 : star (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) ⬝ᵥ
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) = star w ⬝ᵥ w := by
    rw [← hsv, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).2, Matrix.one_mulVec]
  have hre : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  have h2' : ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i‖ ^ 2 = ∑ j, ‖w j‖ ^ 2 := by
    have := congrArg Complex.re h2
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, hre] at this
    exact this
  rw [h1, Complex.re_sum, ← h2', Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Complex.re_ofReal_mul, hre]
  exact mul_le_mul_of_nonneg_right (hcle i) (by positivity)

theorem posDef_unif {P : Type} [TopologicalSpace P] {p₀ : P} (H : P → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ i j, ContinuousAt (fun p => H p i j) p₀) (h0 : (H p₀).PosDef) :
    ∃ δ > 0, ∀ᶠ p in 𝓝 p₀, ∀ w : Fin n → ℂ, δ * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (H p *ᵥ w)).re := by
  obtain ⟨c, hc, hcoer⟩ := exists_pos_mul_sum_sq_le_re_of_posDef (H p₀) h0
  have hf : Tendsto (fun p => ∑ i, ∑ j, ‖H p i j - H p₀ i j‖) (𝓝 p₀) (𝓝 0) := by
    have h00 : (0 : ℝ) = ∑ i : Fin n, ∑ j : Fin n, ‖H p₀ i j - H p₀ i j‖ := by simp
    rw [h00]
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      ((hH i j).tendsto.sub tendsto_const_nhds).norm
  have hev := (tendsto_order.1 hf).2 (c / 2) (by positivity)
  refine ⟨c / 2, by positivity, hev.mono fun p hp w => ?_⟩
  have hb := norm_star_dotProduct_mulVec_le_sum_norm_mul (H p - H p₀) w
  have hsplit : (star w ⬝ᵥ (H p *ᵥ w)).re =
      (star w ⬝ᵥ (H p₀ *ᵥ w)).re + (star w ⬝ᵥ ((H p - H p₀) *ᵥ w)).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    simp
  have hlow : -‖star w ⬝ᵥ ((H p - H p₀) *ᵥ w)‖ ≤ (star w ⬝ᵥ ((H p - H p₀) *ᵥ w)).re :=
    (abs_le.mp (Complex.abs_re_le_norm _)).1
  have hS : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have hcw := hcoer w
  have hp' : ∑ i, ∑ j, ‖(H p - H p₀) i j‖ < c / 2 := by simpa [Matrix.sub_apply] using hp
  have hK := mul_le_mul_of_nonneg_right hp'.le hS
  linarith

end DBoundAH

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

private theorem isUnit_det_and_eq_inv_of_conjTranspose_mul_eq_one {n : ℕ} (A B D : Matrix (Fin n) (Fin n) ℂ) (h1 : Aᴴ * D = 1)
    (h3 : Bᴴ * D = Dᴴ * B) : IsUnit A.det ∧ D = (Aᴴ)⁻¹ ∧ (B * Aᴴ)ᴴ = B * Aᴴ := by
  have hDA : D * Aᴴ = 1 := mul_eq_one_comm.mp h1
  have hAD : A * Dᴴ = 1 := by simpa using congrArg conjTranspose hDA
  refine ⟨?_, (inv_eq_right_inv h1).symm, ?_⟩
  · have h := congrArg det h1
    rw [det_mul, det_one, det_conjTranspose] at h
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, star_zero, zero_mul] at h
    exact zero_ne_one h
  · rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc A * Bᴴ = A * (Bᴴ * D) * Aᴴ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hDA, Matrix.mul_one]
      _ = A * (Dᴴ * B) * Aᴴ := by rw [h3]
      _ = B * Aᴴ := by rw [← Matrix.mul_assoc A Dᴴ B, hAD, Matrix.one_mul]

theorem siegelP_data (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) :
    IsUnit (mR q).toBlocks₁₁.det ∧ (mR q).toBlocks₂₂ = ((mR q).toBlocks₁₁ᴴ)⁻¹ ∧
      ((mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ)ᴴ = (mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ := by
  have hG : InG (mR q) := q.2
  rw [InG, ← fromBlocks_toBlocks (mR q), hq, JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_inj] at hG
  simp at hG
  exact isUnit_det_and_eq_inv_of_conjTranspose_mul_eq_one _ _ _ hG.1 (neg_add_eq_zero.mp hG.2.2).symm

theorem siegelP_actZ (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (Z : Matrix (Fin n) (Fin n) ℂ) :
    actZ q Z = (mR q).toBlocks₁₁ * Z * (mR q).toBlocks₁₁ᴴ + (mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ := by
  obtain ⟨hu, hD, -⟩ := siegelP_data q hq
  have hu' : IsUnit ((mR q).toBlocks₁₁ᴴ).det := by
    rw [det_conjTranspose]
    exact hu.star
  rw [actZ, hq, Matrix.zero_mul, zero_add, hD, Matrix.nonsing_inv_nonsing_inv _ hu', Matrix.add_mul]

theorem siegelP_jF (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (e : ℤ) (p p' : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    jF e p p' q Z = (mR q).toBlocks₁₁.det ^ e * (star (mR q).toBlocks₁₁.det) ^ (((p + p' : ℕ) : ℤ) - e) := by
  obtain ⟨hu, hD, -⟩ := siegelP_data q hq
  have hdet : det (mR q) = (mR q).toBlocks₁₁.det * (mR q).toBlocks₂₂.det := by
    conv_lhs => rw [← fromBlocks_toBlocks (mR q), hq]
    exact det_fromBlocks_zero₂₁ _ _ _
  have hs : star (mR q).toBlocks₁₁.det ≠ 0 := hu.star.ne_zero
  rw [jF, hq, Matrix.zero_mul, Matrix.zero_mul, zero_add, hdet, hD, det_nonsing_inv,
    det_conjTranspose, Ring.inverse_eq_inv']
  generalize (mR q).toBlocks₁₁.det = a at hs ⊢
  generalize star a = s at hs ⊢
  rw [mul_zpow, _root_.inv_zpow', _root_.inv_zpow', _root_.inv_zpow', neg_neg, neg_neg, mul_assoc,
    mul_assoc, ← zpow_add₀ hs, ← zpow_add₀ hs]
  congr 2
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def ftLoc {m : ℕ} (ε : Fin m → Bool) (t : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  ∫ y : Fin m → Fin n → ℂ, f y *
    Complex.exp (Complex.I * ((2 * t : ℝ) : ℂ) * (((Matrix.of u)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of y).trace.re : ℂ))

def FTfact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 →
    ∃ (κ : ℂ) (A A' : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ)), κ ≠ 0 ∧ ∀ Ψ (hΨ : AwayCls θ τ fr Ψ),
      AwayCls θ τ fr (A Ψ) ∧ AwayCls θ τ fr (A' Ψ) ∧ ∀ f (hf : IsSch f),
        IsSch (fun u => κ * ftLoc ε (tLoc l τ) f u) ∧ IsSch (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) ∧
        (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ) f u) (A Ψ) ∧
        (ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ)

def GenA : Prop :=
  ∀ (D : D7) (n : ℕ), Subgroup.closure {g : G D n | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨
    (∃ c, mat g = blk4 1 0 c 1)} = ⊤

def LocalL2Isometry : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ y : GR n, ∃ κ : ℝ, 0 < κ ∧ ∀ f, IsSch f → ∫ u, ‖L y f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem identG {g : M2 n} (hg : InG g) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (g.toBlocks₁₁ * X + g.toBlocks₁₂)ᴴ * (g.toBlocks₂₁ * Y + g.toBlocks₂₂) -
      (g.toBlocks₂₁ * X + g.toBlocks₂₂)ᴴ * (g.toBlocks₁₁ * Y + g.toBlocks₁₂) = Xᴴ - Y := by
  obtain ⟨h1, h2, h3⟩ := inG_rel hg
  have h3' : g.toBlocks₂₂ᴴ * g.toBlocks₁₁ - g.toBlocks₁₂ᴴ * g.toBlocks₂₁ = 1 := by
    have := congrArg conjTranspose h3
    simpa [conjTranspose_sub, conjTranspose_mul] using this
  have key : (g.toBlocks₁₁ * X + g.toBlocks₁₂)ᴴ * (g.toBlocks₂₁ * Y + g.toBlocks₂₂) -
      (g.toBlocks₂₁ * X + g.toBlocks₂₂)ᴴ * (g.toBlocks₁₁ * Y + g.toBlocks₁₂) =
      Xᴴ * (g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂) -
        (g.toBlocks₂₂ᴴ * g.toBlocks₁₁ - g.toBlocks₁₂ᴴ * g.toBlocks₂₁) * Y +
        Xᴴ * (g.toBlocks₁₁ᴴ * g.toBlocks₂₁ - g.toBlocks₂₁ᴴ * g.toBlocks₁₁) * Y +
        (g.toBlocks₁₂ᴴ * g.toBlocks₂₂ - g.toBlocks₂₂ᴴ * g.toBlocks₁₂) := by
    simp only [conjTranspose_add, conjTranspose_mul]
    noncomm_ring
  rw [key, h3, h3', h1, h2]
  simp

theorem det_CZD {g : M2 n} (hg : InG g) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) :
    IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hid := identG hg Z Z
  have h0 : star v ⬝ᵥ ((Zᴴ - Z) *ᵥ v) = 0 := by
    rw [← hid, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hMv, mulVec_zero, dotProduct_sub,
      dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hMv]
    simp
  have h0' : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) = 0 := by
    rw [← neg_sub, neg_mulVec, dotProduct_neg, h0, neg_zero]
  have hpos := Matrix.PosDef.dotProduct_mulVec_pos hZ hv
  rw [smul_mulVec, dotProduct_smul, h0', smul_zero] at hpos
  exact lt_irrefl _ hpos

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end
