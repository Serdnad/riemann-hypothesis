module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyEq
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CapelliDeterminantRisingFactorial
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockMulUnipotentDomain
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle013
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle011
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem abs_arg_lt_pi {P : ℂ} (hP : P ∈ Complex.slitPlane) : |P.arg| < Real.pi := by
  rw [abs_lt]
  exact ⟨Complex.neg_pi_lt_arg P, lt_of_le_of_ne (Complex.arg_le_pi P) (Complex.slitPlane_arg_ne_pi hP)⟩

theorem cpow_split {P a b : ℂ} (hP : P ∈ Complex.slitPlane) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha' : |a.arg| < (Real.pi - |P.arg|) / 2) (hb' : |b.arg| < (Real.pi - |P.arg|) / 2) (w : ℂ) :
    (P * a * b) ^ w = P ^ w * a ^ w * b ^ w := by
  have hP0 : P ≠ 0 := Complex.slitPlane_ne_zero hP
  have hPpi := abs_arg_lt_pi hP
  have hpos : 0 ≤ Real.pi - |P.arg| := by linarith
  have h1 : P.arg + a.arg ∈ Ioc (-Real.pi) Real.pi := by
    have := abs_add_le P.arg a.arg
    constructor
    · linarith [neg_abs_le (P.arg + a.arg)]
    · linarith [le_abs_self (P.arg + a.arg)]
  have hPa : P * a ≠ 0 := mul_ne_zero hP0 ha
  have harg : (P * a).arg = P.arg + a.arg := by
    have := congrArg Complex.im (Complex.log_mul hP0 ha h1)
    simpa [Complex.log_im] using this
  have h2 : (P * a).arg + b.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [harg]
    have := abs_add_le (P.arg + a.arg) b.arg
    have := abs_add_le P.arg a.arg
    constructor
    · linarith [neg_abs_le (P.arg + a.arg + b.arg)]
    · linarith [le_abs_self (P.arg + a.arg + b.arg)]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hPa hb), Complex.log_mul hPa hb h2, Complex.log_mul hP0 ha h1,
    Complex.cpow_def_of_ne_zero hP0, Complex.cpow_def_of_ne_zero ha, Complex.cpow_def_of_ne_zero hb,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem detD_congr {ι : Type} [Fintype ι] [DecidableEq ι] {F G : Matrix ι ι ℂ → ℂ} (h : F =ᶠ[𝓝 0] G) :
    detD F = detD G := by
  unfold detD
  rw [(h.iteratedFDeriv ℂ (Fintype.card ι)).eq_of_nhds]

theorem ev_small {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : E → ℂ} (hc : ContinuousAt c 0) (h0 : c 0 = 1)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ T in 𝓝 (0 : E), c T ≠ 0 ∧ |(c T).arg| < δ := by
  have hne : ∀ᶠ T in 𝓝 (0 : E), c T ≠ 0 := hc.eventually_ne (by rw [h0]; exact one_ne_zero)
  have hcont : ContinuousAt (fun T => (c T).arg) 0 :=
    ContinuousAt.comp (f := c) (g := Complex.arg) (Complex.continuousAt_arg (by rw [h0]; exact Complex.one_mem_slitPlane)) hc
  have ht : Tendsto (fun T => (c T).arg) (𝓝 0) (𝓝 0) := by
    have := hcont.tendsto
    simpa [h0, Complex.arg_one] using this
  filter_upwards [hne, ht (Metric.ball_mem_nhds 0 hδ)] with T h1 h2
  refine ⟨h1, ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using h2

private theorem mul_toBlocks₂₁' (A B : M2 n) :
    (A * B).toBlocks₂₁ = A.toBlocks₂₁ * B.toBlocks₁₁ + A.toBlocks₂₂ * B.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem mul_toBlocks₂₂ (A B : M2 n) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem u1_mul_mX_one_eq_add (x : M2 n) (Q R : Matrix (Fin n) (Fin n) ℂ) :
    u1 (x * mX 1 Q R 1) = u1 x + u2 x * R := by
  have hinv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_left_inv cmi_mul_cm
  have hxc21 : (x * Cm n).toBlocks₂₁ = u1 x := by
    rw [mul_toBlocks₂₁', Cm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, u1]
    simp [Matrix.mul_smul]
  have hxc22 : (x * Cm n).toBlocks₂₂ = u2 x := by
    rw [mul_toBlocks₂₂, Cm, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, u2]
    simp [Matrix.mul_smul]
  rw [mX, hinv, show x * (Cm n * fromBlocks 1 Q R 1 * Cmi n) = (x * Cm n * fromBlocks 1 Q R 1) * Cmi n by
    simp only [Matrix.mul_assoc], first_cayley_block_mul_inverse_cayley, mul_toBlocks₂₁', toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁,
    Matrix.mul_one, hxc21, hxc22]

theorem fz_mX {m : ℕ} {e : ℤ} {z : ℂ} {j : ℕ} {x : M2 n} (hx : x ∈ DomZ n)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
    (h1 : (1 + subOn (blkB j) (wM x)⁻¹ * S).det ≠ 0) (h2 : (1 + subOn (blkA j) (wM x) * T).det ≠ 0)
    (h1' : |((1 + subOn (blkB j) (wM x)⁻¹ * S).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2)
    (h2' : |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2) :
    fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
        (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ ((-(m : ℂ)) - z) := by
  obtain ⟨hD, hP⟩ := hx
  have hD' := hD
  obtain ⟨hdet, hu1, hu2, -⟩ := hD'
  obtain ⟨hQR, hRQ⟩ := embOn_mul_embOn_compl j T S
  have hdetM : (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1).det = x.det := by
    rw [Matrix.det_mul, det_mX_one _ _ hRQ, mul_one]
  have hub : (ub1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det =
      (1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det := by
    rw [inverse_first_block_mul_unipotent_domain x hD _ _ hQR hRQ, Matrix.det_mul, det_one_add_mul_comm, det_one_add_mul_embOn]
  have hw : (wM x)⁻¹ = (u1 x)⁻¹ * u2 x := by
    rw [wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu2)]
  have hu : (u1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det =
      (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det := by
    rw [u1_mul_mX_one_eq_add, ← det_one_add_mul_embOn, ← Matrix.det_mul]
    congr 1
    rw [hw, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu1), Matrix.one_mul]
  unfold fz
  rw [hdetM, hu, hub,
    show (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det * ((1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det) =
      (u1 x).det * (ub1 x).det * (1 + subOn (blkA j) (wM x) * T).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det by ring,
    cpow_split hP h2 h1 h2' h1' (-z), mul_zpow, sub_eq_add_neg, Complex.cpow_add _ _ h1,
    show (-(m : ℂ)) = ((-(m : ℤ) : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  ring

private theorem detD_det_one_add_mul_rpow_eq {ι : Type} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℂ) (t : ℂ) :
    (detD fun S : Matrix ι ι ℂ => (1 + W * S).det ^ t) =
      W.det * ∏ i ∈ Finset.range (Fintype.card ι), (t + (i : ℂ)) := by
  have hF : AnalyticAt ℂ (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) 0 := analyticAt_det_one_add_cpow t
  have h := CEq.equivar_thm ι (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) W hF
  beta_reduce at h
  rw [h]
  congr 1
  have hG : AnalyticAt ℂ (fun S : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ => (1 + S).det ^ t) 0 :=
    analyticAt_det_one_add_cpow t
  have hr := CEq.reindex_thm ι (Fin (Fintype.card ι)) (Fintype.equivFin ι) _ hG
  beta_reduce at hr
  rw [← kappaC (Fintype.card ι) t, ← hr]
  congr 1
  funext S
  have hS : (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) S =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) (1 + S) := by
    ext a b
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hS, Matrix.det_reindex_self]

theorem djZ : DjZ := by
  intro n m e j z x hj hx
  have hx' := hx
  obtain ⟨hD, hP⟩ := hx'
  have hδ : 0 < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 := by
    have := abs_arg_lt_pi hP
    linarith
  have hcA : ∀ᶠ T in 𝓝 (0 : Matrix (blkA (n := n) j) (blkA j) ℂ),
      (1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧
        |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 :=
    ev_small (c := fun T => (1 + subOn (blkA j) (wM x) * T).det)
      ((continuous_const.add (continuous_const.matrix_mul continuous_id)).matrix_det.continuousAt)
      (by simp) hδ
  have hcB : ∀ᶠ S in 𝓝 (0 : Matrix (blkB (n := n) j) (blkB j) ℂ),
      (1 + subOn (blkB j) (wM x)⁻¹ * S).det ≠ 0 ∧
        |((1 + subOn (blkB j) (wM x)⁻¹ * S).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 :=
    ev_small (c := fun S => (1 + subOn (blkB j) (wM x)⁻¹ * S).det)
      ((continuous_const.add (continuous_const.matrix_mul continuous_id)).matrix_det.continuousAt)
      (by simp) hδ
  have hinner : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      ((1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧
        |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2) →
      (detD fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) =
        (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
          ((subOn (blkB j) (wM x)⁻¹).det *
            ∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), ((-(m : ℂ)) - z + (i : ℂ))) := by
    intro T hT
    rw [PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
          (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ ((-(m : ℂ)) - z)) ?_,
      detD_const_mul, detD_det_one_add_mul_rpow_eq]
    filter_upwards [hcB] with S hS
    exact fz_mX hx T S hS.1 hT.1 hS.2 hT.2
  rw [PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun T : Matrix (blkA (n := n) j) (blkA j) ℂ =>
      (fz m e z x * ((subOn (blkB j) (wM x)⁻¹).det *
        ∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), ((-(m : ℂ)) - z + (i : ℂ)))) *
        (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) ?_]
  · rw [detD_const_mul, detD_det_one_add_mul_rpow_eq, card_blkA hj, card_blkB hj, minorOn_eq, minorOn_eq]
    have e1 : ∏ i ∈ Finset.range j, (-z + (i : ℂ)) = ∏ i ∈ Finset.range j, ((i : ℂ) - z) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    have e2 : ∏ i ∈ Finset.range (n - j), ((-(m : ℂ)) - z + (i : ℂ)) =
        ∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    rw [e1, e2]
    ring
  · filter_upwards [hcA] with T hT
    rw [hinner T hT]
    ring

end PositivityTheory.Rg.Sw.HSt
end
end

section

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fderiv_line_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : M2 n → E} {x : M2 n}
    (hf : DifferentiableAt ℂ f x) (v : M2 n) (hc : ∀ τ : ℂ, f (x + τ • v) = f x) : fderiv ℂ f x v = 0 := by
  have hl : HasDerivAt (fun τ : ℂ => x + τ • v) v 0 :=
    (((hasDerivAt_id' (0:ℂ)).smul_const v).const_add x).congr_deriv (one_smul ℂ v)
  have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℂ) hl (by simp)
  have h2 : HasDerivAt (f ∘ fun τ : ℂ => x + τ • v) 0 0 := by
    have e : (f ∘ fun τ : ℂ => x + τ • v) = fun _ => f x := funext fun τ => hc τ
    rw [e]
    exact hasDerivAt_const _ _
  exact h1.unique h2

theorem line_low (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) :
    x + τ • (x * lowQ Q) = x * mX 1 (τ • Q) 0 1 := by
  rw [mX_low, lowQ_smul, mul_add, mul_one, Matrix.mul_smul]

theorem zOfE_low (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) : zOfE (x * mX 1 Q 0 1) = zOfE x := by
  rw [zOfE_eq, zOfE_eq, first_cayley_block_mul_block, Nm_mX]; simp

theorem holomorphic_section_lowering_invariant (m : ℕ) (e : ℤ) (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) : holomorphicScalarSection m e (x * mX 1 Q 0 1) = holomorphicScalarSection m e x := by
  unfold holomorphicScalarSection
  simp only [Matrix.det_mul, det_mX_low, first_cayley_block_mul_block, mul_one, mul_zero, add_zero]

theorem fderiv_zOfE_low (x : M2 n) (h : (u1 x).det ≠ 0) (Q : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℂ zOfE x (x * lowQ Q) = 0 :=
  fderiv_line_zero (da_zOfE x h) _ fun τ => by rw [line_low, zOfE_low]

theorem fderiv_F0E_low (m : ℕ) (e : ℤ) (x : M2 n) (h0 : x.det ≠ 0) (h : (u1 x).det ≠ 0)
    (Q : Matrix (Fin n) (Fin n) ℂ) : fderiv ℂ (holomorphicScalarSection m e) x (x * lowQ Q) = 0 :=
  fderiv_line_zero (da_F0E m e x h0 h) _ fun τ => by rw [line_low, holomorphic_section_lowering_invariant]

theorem low_blocks (R : Matrix (Fin n) (Fin n) ℂ) :
    lowQ R = fromBlocks ((-1 / 2 : ℂ) • R) ((Complex.I / 2) • R) ((Complex.I / 2) • R) ((1 / 2 : ℂ) • R) := by
  rw [lowQ_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

def raiseR (S : Matrix (Fin n) (Fin n) ℂ) : M2 n := mX 1 0 S 1 - 1

private theorem Cm_mul_Cmi : Cm n * Cmi n = 1 := by
  unfold Cm Cmi
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem raise_eq (S : Matrix (Fin n) (Fin n) ℂ) : raiseR S = Cm n * fromBlocks 0 0 S 0 * Cmi n := by
  have hinv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv Cm_mul_Cmi
  have hb : (fromBlocks 1 0 S 1 : M2 n) = fromBlocks 0 0 S 0 + 1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp
  unfold raiseR mX
  rw [hinv, hb, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Cm_mul_Cmi, add_sub_cancel_right]

theorem raise_blocks (S : Matrix (Fin n) (Fin n) ℂ) :
    raiseR S = fromBlocks ((-1 / 2 : ℂ) • S) ((-Complex.I / 2) • S) ((-Complex.I / 2) • S) ((1 / 2 : ℂ) • S) := by
  rw [raise_eq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem sig_fromBlocks (A B C D : Matrix (Fin n) (Fin n) ℂ) :
    sig (fromBlocks A B C D) = fromBlocks (-Dᴴ) Bᴴ Cᴴ (-Aᴴ) := by
  rw [sig_eq]
  unfold JJ
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem sig_low (R : Matrix (Fin n) (Fin n) ℂ) : sig (lowQ R) = raiseR Rᴴ := by
  rw [low_blocks, raise_blocks, sig_fromBlocks]
  simp only [Matrix.conjTranspose_smul]
  congr 1 <;> ext i j <;> simp [Matrix.smul_apply] <;> ring_nf <;> simp [Complex.conj_I] <;> ring_nf

theorem raiseR_smul (c : ℂ) (S : Matrix (Fin n) (Fin n) ℂ) : raiseR (c • S) = c • raiseR S := by
  rw [raise_blocks, raise_blocks, Matrix.fromBlocks_smul]
  congr 1 <;> exact smul_comm _ _ _

theorem line_raise (x : M2 n) (S : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) :
    x + τ • (x * raiseR S) = x * mX 1 0 (τ • S) 1 := by
  have : mX 1 0 (τ • S) 1 = 1 + raiseR (τ • S) := by rw [raiseR]; abel
  rw [this, raiseR_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]

end PositivityTheory.Rg.Sw.HSt.CR
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem ks_inv_eq {U : Matrix (Fin n) (Fin n) ℂ} (h : U * Uᴴ = 1) : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv h

theorem ks_trace_single (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : (X * Matrix.single a b 1).trace = X b a := by
  rw [Matrix.trace_mul_single]
  simp

theorem ks_rhoP {Kg : Type} [Group Kg] (ι : Kg →* M2 n) (m : ℕ) (k k1 : Kg) (hk : InK (ι k))
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : N ∈ unitaryGroup (Fin n) ℂ) (h1 : ι k1 = Proj.kM 1 N) :
    rhoP ι m 0 1 (k * k1) = fV (m : ℤ) 0 (ι k) * ((u1 (ι k))⁻¹ * u2 (ι k) * N).trace := by
  obtain ⟨kk, hkk, hmk⟩ := Proj.kM_of_unitary (1 : Matrix (Fin n) (Fin n) ℂ) N (one_mem _) hN
  have hu1 : u1 (ι (k * k1)) = u1 (ι k) := by
    rw [map_mul, h1, ← hmk, first_block_mul_compact (ι k) hkk, hmk, Proj.first_unitary_block_of_pair, Matrix.mul_one]
  have hu2 : u2 (ι (k * k1)) = u2 (ι k) * N := by
    rw [map_mul, h1, ← hmk, second_block_mul_compact (ι k) hkk, hmk, Proj.second_unitary_block_of_pair]
  have U1 : u1 (ι k) * (u1 (ι k))ᴴ = 1 := first_cayley_block_unitary hk
  have U2 : u2 (ι k) * (u2 (ι k))ᴴ = 1 := second_cayley_block_unitary hk
  have UN : N * Nᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hN
    rwa [Matrix.star_eq_conjTranspose] at this
  have hfz : fz m 0 0 (ι (k * k1)) = (u1 (ι k)).det ^ (-(m : ℤ)) := by
    simp only [fz, zpow_zero, one_mul, neg_zero, Complex.cpow_zero, mul_one, hu1]
  have hne : (u1 (ι k)).det ≠ 0 := det_first_cayley_block_ne_zero hk.1
  have hd : star (u1 (ι k)).det = ((u1 (ι k)).det)⁻¹ := by
    have := congrArg Matrix.det U1
    rw [det_mul, det_one, det_conjTranspose] at this
    exact eq_inv_of_mul_eq_one_right this
  have hfV : fV (m : ℤ) 0 (ι k) = star ((u1 (ι k)).det ^ (-(m : ℤ))) := by
    have h := scalar_section_mul_conjugate_section hk (m : ℤ) 0
    have hf0 : f0 (m : ℤ) 0 (ι k) = (u1 (ι k)).det ^ (-(m : ℤ)) := by simp [f0]
    rw [hf0] at h
    rw [star_zpow₀, hd, eq_inv_of_mul_eq_one_right h]
    rw [_root_.zpow_neg, _root_.zpow_neg, _root_.inv_zpow, inv_inv]
  have htr : star ((u2 (ι (k * k1)))⁻¹ * 1 * u1 (ι (k * k1))).trace = ((u1 (ι k))⁻¹ * u2 (ι k) * N).trace := by
    rw [hu1, hu2, Matrix.mul_one, Matrix.mul_inv_rev, ← Matrix.trace_conjTranspose, ks_inv_eq UN, ks_inv_eq U2,
      ks_inv_eq U1]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  unfold rhoP
  rw [star_mul', hfz, htr, hfV]

theorem ks_perm_unitary (a b : Fin n) : (Equiv.swap a b).permMatrix ℂ ∈ unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_permMatrix,
    PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp [PEquiv.toMatrix_apply, Matrix.one_apply]

theorem ks_diag_unitary (b : Fin n) :
    Matrix.diagonal (fun i => if i = b then (1 : ℂ) else -1) ∈ unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = b <;> simp [h]

theorem ks_single_eq (a b : Fin n) :
    Matrix.single a b (1 : ℂ) = (1 / 2 : ℂ) • (Equiv.swap a b).permMatrix ℂ +
      (1 / 2 : ℂ) • ((Equiv.swap a b).permMatrix ℂ * Matrix.diagonal (fun i => if i = b then (1 : ℂ) else -1)) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.single_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    smul_eq_mul]
  by_cases hj : j = b
  · subst hj
    by_cases hi : i = a
    · subst hi
      simp <;> norm_num
    · have : ¬ (Equiv.swap a j i = j) := by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
        exact hi
      simp [this, Ne.symm hi]
  · simp only [hj, if_false]
    by_cases h : Equiv.swap a b i = j
    · simp only [h, if_true]
      have : ¬ (a = i ∧ b = j) := fun h' => hj h'.2.symm
      rw [if_neg this]
      ring
    · simp only [h, if_false]
      have : ¬ (a = i ∧ b = j) := fun h' => hj h'.2.symm
      rw [if_neg this]
      ring

theorem kSplit : KSplit := by
  intro n m a0 b0 Kg _ ι hK
  classical
  set Pm : Matrix (Fin n) (Fin n) ℂ := (Equiv.swap a0 b0).permMatrix ℂ with hPmdef
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => if i = b0 then (1 : ℂ) else -1) with hDdef
  have hPm : Pm ∈ unitaryGroup (Fin n) ℂ := ks_perm_unitary a0 b0
  have hD : D ∈ unitaryGroup (Fin n) ℂ := ks_diag_unitary b0
  set Nl : Fin 2 → Matrix (Fin n) (Fin n) ℂ := ![Pm, Pm * D] with hNldef
  have hNl : ∀ l, Nl l ∈ unitaryGroup (Fin n) ℂ := by
    intro l
    fin_cases l
    · exact hPm
    · exact mul_mem hPm hD
  have hex : ∀ l, ∃ k1 : Kg, ι k1 = Proj.kM 1 (Nl l) := fun l => by
    obtain ⟨kk, hkk, hmk⟩ := Proj.kM_of_unitary (1 : Matrix (Fin n) (Fin n) ℂ) (Nl l) (one_mem _) (hNl l)
    have : InK (Proj.kM 1 (Nl l)) := by rw [← hmk]; exact hkk
    exact (hK _).1 this
  choose kl hkl using hex
  refine ⟨2, fun _ => 1 / 2, kl, fun k => ?_⟩
  have hk : InK (ι k) := (hK _).2 ⟨k, rfl⟩
  rw [Fin.sum_univ_two, ks_rhoP ι m k (kl 0) hk _ (hNl 0) (hkl 0), ks_rhoP ι m k (kl 1) hk _ (hNl 1) (hkl 1)]
  rw [← ks_trace_single ((u1 (ι k))⁻¹ * u2 (ι k)) a0 b0, ks_single_eq a0 b0]
  simp only [hNldef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  ring

end PositivityTheory.Rg.Sw.HSt
end
end
