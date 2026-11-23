module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DerivEqFderivPair
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle013
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle015
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContinuousOnIteratedFDerivTranslate
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fz_contDiffOn (m : ℕ) : ContDiffOn ℂ ∞ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (Set.univ ×ˢ DomZ n) :=
  ((fzHol n m 0).2.2).contDiffOn_of_completeSpace

theorem Fd_eq (m : ℕ) {y : M2 n} (hy : y ∈ DomZ n) :
    Fd m y = fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (0, y) (1, 0) :=
  deriv_eq_fderiv_pair (fun p : ℂ × M2 n => fz m 0 p.1 p.2) 0 y
    (((fz_contDiffOn m).contDiffAt ((isOpen_univ.prod isOpen_domZ).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
      (by simp))

theorem Fd_contDiffOn (m : ℕ) : ContDiffOn ℂ ∞ (Fd (n := n) m) (DomZ n) := by
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod isOpen_domZ
  have h1 : ContDiffOn ℂ ∞ (fun p : ℂ × M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) p (1, 0))
      (Set.univ ×ˢ DomZ n) :=
    ((fz_contDiffOn m).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have h2 : ContDiffOn ℂ ∞ (fun y : M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (0, y) (1, 0)) (DomZ n) :=
    h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => ⟨Set.mem_univ _, hy⟩)
  exact h2.congr fun y hy => Fd_eq m hy

theorem fz_slice_contDiffOn (m : ℕ) (z : ℂ) : ContDiffOn ℂ ∞ (fz (n := n) m 0 z) (DomZ n) := by
  have hl : ContDiff ℂ ∞ (fun y : M2 n => ((z : ℂ), y)) := contDiff_const.prodMk contDiff_id
  have h := (fz_contDiffOn (n := n) m).comp hl.contDiffOn (fun y hy => (⟨Set.mem_univ _, hy⟩ : ((z : ℂ), y) ∈ Set.univ ×ˢ DomZ n))
  exact h

theorem djFd : DjFd := by
  intro n m j x hj1 hj hx
  set U : ℂ × M2 n → ℂ := fun p => fz m 0 p.1 p.2 with hUdef
  have hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ DomZ n) := fz_contDiffOn m
  have hD : IsOpen (DomZ n) := isOpen_domZ
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod hD
  have expand : ∀ F : M2 n → ℂ, ContDiffOn ℂ ∞ F (DomZ n) →
      detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        F (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
      ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) F x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1))) := by
    intro F hF
    have hrw : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        F (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
        (fun T => detD (fun S => F (x + LQ (blkA j) x T + LR (blkB j) x S))) := by
      funext T; congr 1; funext S; rw [mul_mX, LQ_apply, LR_apply]
    rw [hrw]
    exact detD_detD_comp F (DomZ n) hD hF x hx (LQ (blkA j) x) (LR (blkB j) x)
  have hcomm : ∀ (k : ℕ) (v : Fin k → M2 n), iteratedFDeriv ℂ k (Fd m) x v =
      deriv (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) 0 := fun k v =>
    iFD_deriv_comm U (DomZ n) hD hU x hx k v
  have hdiff : ∀ (k : ℕ) (v : Fin k → M2 n), DifferentiableAt ℂ (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) 0 := by
    intro k v
    have e : (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) =
        fun z => iteratedFDeriv ℂ k U (z, x) (fun i => ((0 : ℂ), v i)) :=
      funext fun z => iFD_slice U (DomZ n) hD hU z x hx k v
    rw [e]
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k U) (0, x) :=
      (hU.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hx⟩)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top k)
    have hl : DifferentiableAt ℂ (fun z : ℂ => (z, x)) 0 := differentiableAt_id.prodMk (differentiableAt_const x)
    exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × M2 n) ℂ (fun i => ((0 : ℂ), v i))).differentiableAt.comp
      (0 : ℂ) (hd.comp (0 : ℂ) hl)
  rw [expand (Fd m) (Fd_contDiffOn m)]
  simp_rw [hcomm]
  have hsum : deriv (fun z => ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) 0 =
      ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        deriv (fun z => iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) 0 := by
    rw [deriv_fun_sum (fun σ _ => DifferentiableAt.fun_sum (fun τ _ => (hdiff _ _).const_mul _))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [deriv_fun_sum (fun τ _ => (hdiff _ _).const_mul _)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [deriv_const_mul _ (hdiff _ _)]
  rw [← hsum]
  have hfz : (fun z => ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) =
      fun z => ((∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) *
        (fz m 0 z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹) := by
    funext z
    rw [← expand (fz m 0 z) (fz_slice_contDiffOn m z), djZ n m 0 j z x hj hx]
    ring
  rw [hfz]
  set A : ℂ → ℂ := fun z => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))
    with hAdef
  have hA : DifferentiableAt ℂ A 0 := by
    simp only [hAdef]
    exact (DifferentiableAt.fun_finsetProd fun i _ => (differentiableAt_const _).sub differentiableAt_id).mul
      (DifferentiableAt.fun_finsetProd fun i _ => ((differentiableAt_const _).sub differentiableAt_id))
  have hA0 : A 0 = 0 := by
    simp only [hAdef]
    rw [Finset.prod_eq_zero (i := 0) (by simp; omega) (by simp), zero_mul]
  have hg : DifferentiableAt ℂ (fun z => fz m 0 z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹) 0 := by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((u1 x).det * (ub1 x).det) ^ (-z)) 0 :=
      (differentiableAt_id.neg).const_cpow (Or.inl (Complex.slitPlane_ne_zero hx.2))
    simp only [fz]
    exact (((differentiableAt_const _).mul h1).mul_const _).mul_const _
  rw [deriv_fun_mul hA hg, hA0, zero_mul, add_zero]
  congr 1
  simp [fz, hF, f0]
end HSt
end Sw
end Rg
end PositivityTheory
end
end

section

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_matrix_mul {A B : ℂ → Matrix (Fin n) (Fin n) ℂ} {A' B' : Matrix (Fin n) (Fin n) ℂ}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun τ => A τ * B τ) (A' * B 0 + A 0 * B') 0 := by
  have hA' : HasDerivAt (fun τ => (A τ : Fin n → Fin n → ℂ)) (A' : Fin n → Fin n → ℂ) 0 := hA
  have hB' : HasDerivAt (fun τ => (B τ : Fin n → Fin n → ℂ)) (B' : Fin n → Fin n → ℂ) 0 := hB
  have h : HasDerivAt (fun τ => ((A τ * B τ : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ))
      ((A' * B 0 + A 0 * B' : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simp only [Matrix.mul_apply, Matrix.add_apply]
    rw [← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum fun k _ => ?_
    exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA' i) k).mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB' k) j)
  exact h

theorem fderiv_zOfE_raise (x : M2 n) (h : (u1 x).det ≠ 0) (S : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℂ zOfE x (x * raiseR S) = WM x * S * (u1 x)⁻¹ := by
  let v := x * raiseR S
  have hl := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hg := (da_zOfE x h).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
  simp only [id_eq, one_smul, Function.comp_def] at hg
  have hu : ∀ τ : ℂ, u1 (x + τ • v) = u1 x + τ • (u2 x * S) := fun τ => by
    rw [line_raise, first_cayley_block_mul_block, Matrix.mul_one, Matrix.mul_smul]
  have hN : ∀ τ : ℂ, Nm (x + τ • v) = Nm x + τ • (Nm' x * S) := fun τ => by
    rw [line_raise, Nm_mX, Matrix.mul_one, Matrix.mul_smul]
  have hc : Continuous fun τ : ℂ => (u1 x + τ • (u2 x * S)).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), (u1 x + τ • (u2 x * S)).det ≠ 0 :=
    hc.continuousAt.eventually_ne (by simpa using h)
  have hB := ((hasDerivAt_id (0 : ℂ)).smul_const (u2 x * S)).const_add (u1 x)
  simp only [id_eq, one_smul] at hB
  have hL := hasDerivAt_matrix_mul hg hB
  have hR := ((hasDerivAt_id (0 : ℂ)).smul_const (Nm' x * S)).const_add (Nm x)
  simp only [id_eq, one_smul] at hR
  have heq : (fun τ : ℂ => zOfE (x + τ • v) * (u1 x + τ • (u2 x * S))) =ᶠ[𝓝 0]
      fun τ => Nm x + τ • (Nm' x * S) := by
    filter_upwards [hev] with τ hτ
    rw [← hu, zOfE_eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (by rwa [hu])), Matrix.mul_one, hN]
  have hfin := hL.unique (hR.congr_of_eventuallyEq heq)
  simp only [zero_smul, add_zero] at hfin
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h
  have key : fderiv ℂ zOfE x v * u1 x = WM x * S := by
    refine (eq_sub_of_add_eq hfin).trans ?_
    rw [WM, show (-(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂) = Nm' x from rfl, Matrix.sub_mul, Matrix.mul_assoc (zOfE x)]
  calc fderiv ℂ zOfE x v = fderiv ℂ zOfE x v * u1 x * (u1 x)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one]
    _ = WM x * S * (u1 x)⁻¹ := congrArg (fun M => M * (u1 x)⁻¹) key

theorem toBlocks₁₁_mul' (A B : M2 n) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem toBlocks₁₂_mul' (A B : M2 n) :
    (A * B).toBlocks₁₂ = A.toBlocks₁₁ * B.toBlocks₁₂ + A.toBlocks₁₂ * B.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem mul_cm₁₁ (x : M2 n) : (x * Cm n).toBlocks₁₁ = Nm x := by
  simp [toBlocks₁₁_mul', Cm, Nm, Matrix.mul_smul]

theorem mul_cm₁₂ (x : M2 n) : (x * Cm n).toBlocks₁₂ = Nm' x := by
  simp [toBlocks₁₂_mul', Cm, Nm', Matrix.mul_smul, Matrix.mul_neg]

theorem det_ne_of_inG {x : M2 n} (hx : InG x) : x.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hx
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
  have h2 : (JJ n).det ≠ 0 := by
    intro h3
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [Matrix.det_mul, h3, zero_mul, Matrix.det_neg] at this
    simp at this
  exact h2 h1.symm

theorem det_cm_ne : (Cm n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (cm_mul_cmi (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem wm_det (x : M2 n) (hx : InG x) (h : (u1 x).det ≠ 0) : (WM x).det ≠ 0 := by
  intro hW
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hW
  set w := -(((u1 x)⁻¹ * u2 x) *ᵥ v)
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h
  have hM : (x * Cm n) *ᵥ Sum.elim w v = 0 := by
    rw [← fromBlocks_toBlocks (x * Cm n), fromBlocks_mulVec, mul_cm₁₁, mul_cm₁₂, mul_cm₂₁, mul_cm₂₂]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    have e1 : Nm x *ᵥ w + Nm' x *ᵥ v = WM x *ᵥ v := by
      simp only [w, WM, Matrix.mulVec_neg, Matrix.mulVec_mulVec, zOfE_eq, Matrix.sub_mulVec, Matrix.mul_assoc]
      rw [show -(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂ = Nm' x from rfl]; abel
    have e2 : u1 x *ᵥ w + u2 x *ᵥ v = 0 := by
      simp only [w, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1,
        Matrix.one_mul, neg_add_cancel]
    rw [e1, e2, hv]
    funext i; cases i <;> simp
  have hdet : (x * Cm n).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero (det_ne_of_inG hx) det_cm_ne
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hM
  exact hv0 (funext fun i => by simpa using congrFun h0 (Sum.inr i))

theorem cra2 : CauchyRiemannFacts := by
  refine ⟨fun n m e y => orbital_function_eq_weighted m e y, fun n x h0 h => ⟨da_zOfE x h, fun m e => da_F0E m e x h0 h, fun Q =>
    ⟨fderiv_zOfE_low x h Q, fun m e => fderiv_F0E_low m e x h0 h Q⟩, fun R => ?_, fun hx => wm_det x hx h⟩⟩
  rw [sig_low]
  exact fderiv_zOfE_raise x h Rᴴ

end PositivityTheory.Rg.Sw.HSt.CR
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def psi (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (u : GR n) : ℂ :=
  ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u) ∂μK

theorem psi_continuous (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [IsFiniteMeasure μK] : Continuous (psi m e μK) := by
  have hF : Continuous (Function.uncurry fun (u : GR n) (k : KR n) =>
      (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u)) := by
    show Continuous fun p : GR n × KR n => (F0 m 0 e (p.2 : GR n))⁻¹ * F0 m 0 e ((p.2 : GR n) * p.1)
    refine Continuous.mul ?_ ?_
    · exact ((Vac.continuous_weight_factor detU1 m 0 e).comp (continuous_subtype_val.comp continuous_snd)).inv₀
        fun p => Vac.spherical_section_ne_zero detU1 m 0 e _
    · exact (Vac.continuous_weight_factor detU1 m 0 e).comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have := continuous_parametric_integral_of_continuous (μ := μK) hF isCompact_univ
  have e : psi m e μK = fun u => ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u) ∂μK := rfl
  rw [e]
  simpa [Measure.restrict_univ] using this

theorem psi_one (m : ℕ) (e : ℤ) (μK : Measure (KR n)) : psi m e μK 1 = (μK Set.univ).toReal := by
  unfold psi
  simp only [mul_one]
  have h : ∀ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e (k : GR n) = 1 := fun k =>
    inv_mul_cancel₀ (Vac.spherical_section_ne_zero detU1 _ _ _ _)
  simp only [h]
  rw [integral_const]
  simp [Measure.real]

private theorem mR_conjTranspose_eq_mR_inv_of_KR (k : KR n) : (mR (k : GR n))ᴴ = mR ((k : GR n)⁻¹) := by
  have hk : (mR (k : GR n))ᴴ * mR (k : GR n) = 1 := (show InK (mR (k : GR n)) from k.2).2
  have h1 : mR (k : GR n) * mR ((k : GR n)⁻¹) = 1 := by
    rw [← mR_mul, mul_inv_cancel]
    simp [mR]
  calc (mR (k : GR n))ᴴ = (mR (k : GR n))ᴴ * (mR (k : GR n) * mR ((k : GR n)⁻¹)) := by
        rw [h1, Matrix.mul_one]
    _ = mR ((k : GR n)⁻¹) := by rw [← Matrix.mul_assoc, hk, Matrix.one_mul]

theorem cw_zero (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure]
    {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β) :
    cw m e ν μK β 0 = ∫ u : GR n, (β (mR u) : ℂ) * psi m e μK u ∂ν := by
  have hF := Vac.continuous_weight_factor (n := n) detU1 m 0 e
  have hFne : ∀ g, F0 (n := n) m 0 e g ≠ 0 := fun g => Vac.spherical_section_ne_zero detU1 m 0 e g
  have hCc : IsCompact (mR ⁻¹' (tsupport β)) := isCompact_preimage_mR hβs.isCompact
  have hk : Continuous (fun p : GR n × KR n => ((p.2 : GR n))) :=
    continuous_subtype_val.comp continuous_snd
  let A : GR n × KR n → ℂ := fun p =>
    F0 m 0 e p.1 * ((F0 m 0 e (p.2 : GR n))⁻¹ * (β (mR ((p.2 : GR n)⁻¹ * p.1)) : ℂ))
  let B : GR n × KR n → ℂ := fun p =>
    (β (mR p.1) : ℂ) * ((F0 m 0 e (p.2 : GR n))⁻¹ * F0 m 0 e ((p.2 : GR n) * p.1))
  have hAc : Continuous A := by
    refine (hF.comp continuous_fst).mul (((hF.comp hk).inv₀ fun p => hFne _).mul ?_)
    exact Complex.continuous_ofReal.comp
      (hβc.comp (PositivityTheory.Rg.Sw.AbsSt.continuous_mR.comp (hk.inv.mul continuous_fst)))
  have hBc : Continuous B := by
    refine (Complex.continuous_ofReal.comp (hβc.comp (PositivityTheory.Rg.Sw.AbsSt.continuous_mR.comp continuous_fst))).mul
      (((hF.comp hk).inv₀ fun p => hFne _).mul (hF.comp (hk.mul continuous_fst)))
  have hAs : HasCompactSupport A := by
    refine HasCompactSupport.intro
      ((((isCompact_univ (X := KR n)).prod hCc).image
        ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)).prod
        (isCompact_univ (X := KR n))) ?_
    intro p hp
    have hz : β (mR ((p.2 : GR n)⁻¹ * p.1)) = 0 := by
      by_contra hne
      apply hp
      refine ⟨⟨⟨p.2, (p.2 : GR n)⁻¹ * p.1⟩, ⟨Set.mem_univ _, subset_tsupport _ hne⟩, ?_⟩, Set.mem_univ _⟩
      simp
    simp [A, hz]
  have hBs : HasCompactSupport B := by
    refine HasCompactSupport.intro (hCc.prod (isCompact_univ (X := KR n))) ?_
    intro p hp
    have hz : β (mR p.1) = 0 := by
      by_contra hne
      exact hp ⟨subset_tsupport _ hne, Set.mem_univ _⟩
    simp [B, hz]
  have hAi : Integrable A (ν.prod μK) := hAc.integrable_of_hasCompactSupport hAs
  have hBi : Integrable B (ν.prod μK) := hBc.integrable_of_hasCompactSupport hBs
  calc cw m e ν μK β 0 = ∫ u, ∫ k, A (u, k) ∂μK ∂ν := by
        unfold cw
        congr 1
        ext u
        unfold phi tw
        rw [Complex.cpow_zero, mul_one, ← integral_const_mul]
        congr 1
        ext k
        simp only [A]
        rw [mR_conjTranspose_eq_mR_inv_of_KR, ← mR_mul]
    _ = ∫ k, ∫ u, A (u, k) ∂ν ∂μK := integral_integral_swap hAi
    _ = ∫ k, ∫ v, A ((k : GR n) * v, k) ∂ν ∂μK := by
        congr 1
        ext k
        exact (integral_mul_left_eq_self (fun u => A (u, k)) (k : GR n)).symm
    _ = ∫ k, ∫ v, B (v, k) ∂ν ∂μK := by
        congr 1
        ext k
        congr 1
        ext v
        simp only [A, B]
        rw [inv_mul_cancel_left]
        ring
    _ = ∫ v, ∫ k, B (v, k) ∂μK ∂ν := (integral_integral_swap hBi).symm
    _ = ∫ u : GR n, (β (mR u) : ℂ) * psi m e μK u ∂ν := by
        congr 1
        ext v
        simp only [B, psi]
        rw [integral_const_mul]

theorem exists_bump (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure] :
    ∃ β : M2 n → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ cw m e ν μK β 0 ≠ 0 := by
  have hpc : Continuous (psi m e μK) := psi_continuous m e μK
  have h1 : mR (1 : GR n) = 1 := by simp [mR]
  have hp1 : 0 < (psi m e μK 1).re := by
    rw [psi_one, Complex.ofReal_re]
    exact ENNReal.toReal_pos (isOpen_univ.measure_ne_zero μK Set.univ_nonempty) (measure_ne_top _ _)
  have hO : IsOpen {u : GR n | 0 < (psi m e μK u).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp hpc)
  obtain ⟨O, hOo, hOeq⟩ := isClosedEmbedding_mR.isInducing.isOpen_iff.mp hO
  have h1O : (1 : M2 n) ∈ O := by
    have h : (1 : GR n) ∈ mR ⁻¹' O := by
      rw [hOeq]
      exact hp1
    simpa [h1] using h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hOo 1 h1O
  let b : ContDiffBump (1 : M2 n) := ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨⇑b, b.contDiff, b.hasCompactSupport, ?_⟩
  rw [cw_zero m e ν μK b.continuous b.hasCompactSupport]
  set g : GR n → ℂ := fun u => (b (mR u) : ℂ) * psi m e μK u with hg
  have hgs : HasCompactSupport g := by
    have h := (b.hasCompactSupport.comp_isClosedEmbedding isClosedEmbedding_mR).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
    exact h.mul_right
  have hgc : Continuous g :=
    (Complex.continuous_ofReal.comp (b.continuous.comp PositivityTheory.Rg.Sw.AbsSt.continuous_mR)).mul hpc
  have hre : ∀ u, (g u).re = b (mR u) * (psi m e μK u).re := fun u => Complex.re_ofReal_mul _ _
  have hpos : 0 < ∫ u, (g u).re ∂ν := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp hgc) (hgs.comp_left Complex.zero_re) ?_ ?_
    · intro u
      show 0 ≤ (g u).re
      rw [hre]
      by_cases hu : b (mR u) = 0
      · simp [hu]
      · have hmem : mR u ∈ Metric.ball (1 : M2 n) r := by
          have hs : mR u ∈ Function.support b := hu
          rwa [b.support_eq] at hs
        have hu' : u ∈ mR ⁻¹' O := hball hmem
        rw [hOeq] at hu'
        exact mul_nonneg b.nonneg (le_of_lt hu')
    · show (g 1).re ≠ 0
      rw [hre, h1, b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul]
      exact ne_of_gt hp1
  intro h
  have hz : (∫ u, g u ∂ν).re = 0 := by
    rw [h]
    simp
  have hgi : Integrable g ν := hgc.integrable_of_hasCompactSupport hgs
  have hint := integral_re hgi
  simp only [RCLike.re_to_complex] at hint
  linarith

end PositivityTheory.Rg.Sw.HSt.Conv
end
end
