module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle002
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle004
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

@[expose] public section

section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

theorem analyticAt_determinant_power_zero_int (N : ℕ) (t : ℤ) : AnalyticAt ℂ (H N t) 0 := analyticAt_H N t 0 (by simp)

theorem analyticAt_fderiv_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (G : F → ℂ) (x v : F) (hG : AnalyticAt ℂ G x) : AnalyticAt ℂ (fun y => fderiv ℂ G y v) x := by
  have h2 : AnalyticAt ℂ (fun L : F →L[ℂ] ℂ => L v) (fderiv ℂ G x) :=
    (ContinuousLinearMap.apply ℂ ℂ v).analyticAt _
  exact h2.comp hG.fderiv

theorem ev_piF (N : ℕ) : ∀ᶠ X in 𝓝 (0 : Matrix (Fin N) (Fin (N + 1)) ℂ), (1 + piF X).det ≠ 0 := by
  have hc : Continuous fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => (1 + piF X).det := by
    unfold piF
    fun_prop
  have hz : piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ) = 0 := by
    ext k l
    simp [piF]
  have h0 : (1 + piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ)).det ≠ 0 := by
    simp [hz]
  exact hc.continuousAt.eventually_ne h0

theorem iconst_mul {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (G : F → ℂ) (x : F) (a : ℂ)
    (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin n → F) :
    iteratedFDeriv ℂ n (fun y => a * G y) x u = a * iteratedFDeriv ℂ n G x u := by
  have h := iteratedFDeriv_const_smul_apply' (a := a) (i := n) (hG.contDiffAt (n := n))
  simp only [smul_eq_mul] at h
  rw [h, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

theorem icompL {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (G : F → ℂ) (φ : E → F) (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hsmul : ∀ (c : ℂ) a, φ (c • a) = c • φ a)
    (x : E) (y : F) (hxy : φ x = y) (hG : AnalyticAt ℂ G y) (n : ℕ) (u : Fin n → E)
    (v : Fin n → F) (huv : ∀ i, φ (u i) = v i) :
    iteratedFDeriv ℂ n (G ∘ φ) x u = iteratedFDeriv ℂ n G y v := by
  let Lℓ : E →ₗ[ℂ] F := { toFun := φ, map_add' := hadd, map_smul' := hsmul }
  let L : E →L[ℂ] F := LinearMap.toContinuousLinearMap Lℓ
  have hL : ∀ z, L z = φ z := fun z => rfl
  obtain ⟨U, hUP, hUo, hyU⟩ := eventually_nhds_iff.1 hG.eventually_analyticAt
  have hU : ContDiffOn ℂ n G U := fun z hz => (hUP z hz).contDiffAt.contDiffWithinAt
  have hxU : L x ∈ U := by rw [hL, hxy]; exact hyU
  have hpre : IsOpen (L ⁻¹' U) := hUo.preimage L.continuous
  have key := L.iteratedFDerivWithin_comp_right hU hUo.uniqueDiffOn hpre.uniqueDiffOn hxU
    (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hpre (show x ∈ L ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen n hUo hxU] at key
  have hcomp : G ∘ φ = G ∘ L := rfl
  rw [hcomp, key, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  show iteratedFDeriv ℂ n G (φ x) (fun i => φ (u i)) = _
  rw [hxy]
  congr 1
  funext i
  exact huv i

theorem phiF_add (a b : Matrix (Fin N) (Fin (N + 1)) ℂ) : phiF (a + b) = phiF a + phiF b := by
  ext i j
  cases i using Fin.cases <;> simp [phiF_zero_row, phiF_succ_row]

theorem phiF_smul (c : ℂ) (a : Matrix (Fin N) (Fin (N + 1)) ℂ) : phiF (c • a) = c • phiF a := by
  ext i j
  cases i using Fin.cases <;> simp [phiF_zero_row, phiF_succ_row]

theorem piF_add (a b : Matrix (Fin N) (Fin (N + 1)) ℂ) : piF (a + b) = piF a + piF b := by
  ext i j; rfl

theorem piF_smul (c : ℂ) (a : Matrix (Fin N) (Fin (N + 1)) ℂ) : piF (c • a) = c • piF a := by
  ext i j; rfl

theorem phiF_zero : phiF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ) = 0 := by
  ext i j
  cases i using Fin.cases <;> simp [phiF_zero_row, phiF_succ_row]

theorem piF_zero : piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ) = 0 := by
  ext i j; rfl

theorem iterated_derivative_corner_case_int (t : ℤ) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) 0
        (fun k => Matrix.single k.succ (e k).succ 1) =
      (t : ℂ) * iteratedFDeriv ℂ N (H N t) 0 (fun k => Matrix.single k (e k) 1) := by
  have hA : AnalyticAt ℂ (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int (N + 1) t)
  have h1 := icompL (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) phiF phiF_add
    phiF_smul 0 0 phiF_zero hA N (fun k => Matrix.single k (e k).succ 1)
    (fun k => Matrix.single k.succ (e k).succ 1) (fun k => phiF_single k (e k).succ)
  rw [← h1]
  have hpi : piF = ⇑(piL N) := funext fun X => (piL_apply X).symm
  have hB : AnalyticAt ℂ (H N t ∘ piF) 0 := by
    rw [hpi]
    refine (analyticAt_H N t (piL N 0) ?_).comp ((piL N).analyticAt 0)
    rw [piL_apply, piF_zero, add_zero, det_one]
    exact one_ne_zero
  have hev : (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) ∘ phiF =ᶠ[𝓝 0]
      fun X => (t : ℂ) * (H N t ∘ piF) X := by
    filter_upwards [ev_piF N] with X hX
    exact fderiv_determinant_power_corner_int t X hX
  rw [(Filter.EventuallyEq.iteratedFDeriv ℂ hev N).eq_of_nhds, iconst_mul _ 0 _ hB]
  congr 1
  exact icompL (H N t) piF piF_add piF_smul 0 0 piF_zero (analyticAt_determinant_power_zero_int N t) N _ _
    (fun k => piF_single_succ k (e k))

end PositivityTheory.Rg.Sw.LVs.CK
end
end

section

noncomputable section

set_option linter.unusedSimpArgs false

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem isUnit_det_of_inG' {g : M2 n} (hg : InG g) : IsUnit g.det := by
  have h := congrArg Matrix.det hg
  rw [det_mul, det_mul, det_conjTranspose] at h
  have hJ : (JJ n).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [det_mul, h0, zero_mul, det_neg, det_one] at this
    simp at this
  refine isUnit_iff_ne_zero.2 fun h0 => hJ ?_
  rw [h0, mul_zero] at h
  exact h.symm

theorem mul_JJ_conjTranspose {g : M2 n} (hg : InG g) : g * JJ n * gᴴ = JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  have h2 : g * (-(JJ n) * gᴴ * JJ n) = 1 := mul_eq_one_comm.1 h1
  have h3 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = JJ n := by rw [h2, Matrix.one_mul]
  have h4 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = g * JJ n * gᴴ := by
    simp only [Matrix.mul_assoc, JJ_mul_JJ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_neg]
  rw [← h4, h3]

theorem lower_rel {g : M2 n} (hg : InG g) : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have h := congrArg Matrix.toBlocks₂₂ (mul_JJ_conjTranspose hg)
  rw [← fromBlocks_toBlocks g] at h
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
  simp only [Matrix.mul_zero, zero_add, Matrix.mul_neg, Matrix.mul_one, add_zero] at h
  have : -(g.toBlocks₂₂ * g.toBlocks₂₁ᴴ) + g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = 0 := by
    rw [← h]; simp
  rw [neg_add_eq_zero] at this
  exact this.symm

theorem first_cayley_block_mul_conjTranspose_eq {g : M2 n} (hg : InG g) :
    u1 g * (u1 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  have h := lower_rel hg
  simp only [u1, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h]
  match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]

theorem second_cayley_block_mul_conjTranspose_eq {g : M2 n} (hg : InG g) :
    u2 g * (u2 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  have h := lower_rel hg
  simp only [u2, conjTranspose_add, conjTranspose_neg, conjTranspose_smul, Complex.star_def, Complex.conj_I,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h]
  match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]

theorem inv_eq_of_inG {g : M2 n} (hg : InG g) : g⁻¹ = -(JJ n) * gᴴ * JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  exact Matrix.inv_eq_left_inv h1

theorem inverse_first_block_eq_of_group {g : M2 n} (hg : InG g) : ub1 g = (u1 g)ᴴ := by
  rw [ub1, inv_eq_of_inG hg, u1]
  conv_lhs => rw [← fromBlocks_toBlocks g]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, neg_zero, neg_neg]
  module

theorem posDef_lower {g : M2 n} (hg : InG g) :
    (g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ).PosDef := by
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_conjTranspose]
    exact (isUnit_det_of_inG' hg).star
  have hP : (gᴴᴴ * gᴴ).PosDef := Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 hu)
  rw [conjTranspose_conjTranspose] at hP
  have h2 := hP.submatrix (e := (Sum.inr : Fin n → Fin n ⊕ Fin n)) Sum.inr_injective
  convert h2 using 1
  conv_rhs => rw [← fromBlocks_toBlocks g]
  ext i j
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.submatrix]

theorem det_first_cayley_block_ne_zero {g : M2 n} (hg : InG g) : (u1 g).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (first_cayley_block_mul_conjTranspose_eq hg)
  rw [det_mul, h, zero_mul] at h1
  exact (posDef_lower hg).det_pos.ne' h1.symm

theorem det_second_cayley_block_ne_zero {g : M2 n} (hg : InG g) : (u2 g).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (second_cayley_block_mul_conjTranspose_eq hg)
  rw [det_mul, h, zero_mul] at h1
  exact (posDef_lower hg).det_pos.ne' h1.symm

theorem automorphy_first_mul_parabolic {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u1 (P * x) = P.toBlocks₂₂ * u1 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u1, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul]

theorem automorphy_second_mul_parabolic {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u2 (P * x) = P.toBlocks₂₂ * u2 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u2, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

theorem det_par {P : M2 n} (hP : P.toBlocks₂₁ = 0) : P.det = P.toBlocks₁₁.det * P.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks P, hP]
  exact det_fromBlocks_zero₂₁ _ _ _

theorem par_rel {P : M2 n} (hG : InG P) (hP : P.toBlocks₂₁ = 0) : P.toBlocks₁₁ᴴ * P.toBlocks₂₂ = 1 := by
  have h := congrArg Matrix.toBlocks₁₂ hG
  rw [← fromBlocks_toBlocks P, hP] at h
  simpa [JJ, fromBlocks_conjTranspose, fromBlocks_multiply] using h

theorem inverse_first_block_mul_parabolic {P x : M2 n} (hP : P.toBlocks₂₁ = 0) (hPu : IsUnit P.det) :
    ub1 (P * x) = ub1 x * (P.toBlocks₁₁)⁻¹ := by
  have hA : IsUnit P.toBlocks₁₁.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_left hPu
  have hD : IsUnit P.toBlocks₂₂.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_right hPu
  have hinv : P⁻¹ = fromBlocks (P.toBlocks₁₁)⁻¹ (-((P.toBlocks₁₁)⁻¹ * P.toBlocks₁₂ * (P.toBlocks₂₂)⁻¹)) 0
      (P.toBlocks₂₂)⁻¹ := by
    conv_lhs => rw [← fromBlocks_toBlocks P, hP]
    refine Matrix.inv_eq_right_inv ?_
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, Matrix.mul_neg,
      Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
    rw [← fromBlocks_one]
    congr 1 <;> simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
  rw [ub1, ub1, Matrix.mul_inv_rev, hinv]
  conv_lhs => rw [← fromBlocks_toBlocks x⁻¹]
  simp only [fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_zero, add_zero,
    Matrix.add_mul, Matrix.smul_mul]

theorem lower_mul_conjTranspose (g : M2 n) :
    (g * gᴴ).toBlocks₂₂ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  conv_lhs => rw [← fromBlocks_toBlocks g]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply]

theorem first_cayley_block_unitary {k : M2 n} (hk : InG k ∧ kᴴ * k = 1) : u1 k * (u1 k)ᴴ = 1 := by
  rw [first_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]
  simp [← fromBlocks_one]

theorem second_cayley_block_unitary {k : M2 n} (hk : InG k ∧ kᴴ * k = 1) : u2 k * (u2 k)ᴴ = 1 := by
  rw [second_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]
  simp [← fromBlocks_one]

end PositivityTheory.Rg.Sw.LVs
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Equivar : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℂ → ℂ) (A : Matrix ι ι ℂ), AnalyticAt ℂ F 0 →
    detD (fun T => F (A * T)) = A.det * detD F

def Reindex : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (F : Matrix κ κ ℂ → ℂ),
    AnalyticAt ℂ F 0 → detD (fun T : Matrix ι ι ℂ => F (T.reindex e e)) = detD F

def KappaFin : Prop :=
  ∀ (N : ℕ) (t : ℤ), detD (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det ^ t) =
    ∏ i ∈ Finset.range N, ((t : ℂ) + i)

end PositivityTheory.Rg.Sw.LVs
end
end

section

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def IterAffine : Prop :=
  ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (F : V → ℂ) (Ω : Set V), IsOpen Ω → ContDiffOn ℂ ∞ F Ω → ∀ c ∈ Ω, ∀ (L : W →L[ℂ] V) (k : ℕ),
      iteratedFDeriv ℂ k (fun w => F (c + L w)) 0 = (iteratedFDeriv ℂ k F c).compContinuousLinearMap (fun _ => L)

def IterSymm : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (F : V → ℂ) (Ω : Set V), IsOpen Ω → ContDiffOn ℂ ∞ F Ω →
    ∀ c ∈ Ω, ∀ (k : ℕ) (v : Fin k → V) (σ : Equiv.Perm (Fin k)), iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v

def IterNested : Prop :=
  ∀ (V W1 W2 : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W1] [NormedSpace ℂ W1]
    [NormedAddCommGroup W2] [NormedSpace ℂ W2] (F : V → ℂ) (Ω : Set V), IsOpen Ω → ContDiffOn ℂ ∞ F Ω → ∀ c ∈ Ω,
    ∀ (L1 : W1 →L[ℂ] V) (L2 : W2 →L[ℂ] V) (a b : ℕ) (u : Fin a → W1) (w : Fin b → W2),
      iteratedFDeriv ℂ a (fun t1 => iteratedFDeriv ℂ b (fun t2 => F (c + L1 t1 + L2 t2)) 0 w) 0 u =
        iteratedFDeriv ℂ (a + b) F c (Fin.append (fun i => L1 (u i)) (fun i => L2 (w i)))

variable {n : ℕ}

def bdiag (j : ℕ) (c c' : ℂ) (t : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a ∈ blkA j ∧ b ∈ blkA j then c * t a b else if a ∈ blkB j ∧ b ∈ blkB j then c' * t a b else 0

def DetDBlock : Prop :=
  ∀ (n j : ℕ) (c c' : ℂ) (ψ : Matrix (Fin n) (Fin n) ℂ → ℂ) (Ω : Set (Matrix (Fin n) (Fin n) ℂ)), IsOpen Ω → 0 ∈ Ω →
    ContDiffOn ℂ ∞ ψ Ω →
    detD (fun t => ψ (bdiag j c c' t)) =
      c ^ (blkA (n := n) j).card * c' ^ (blkB (n := n) j).card *
        detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          ψ (embOn (blkA j) T + embOn (blkB j) S)))

def CmI (n : ℕ) : M2 n := ((2 * Complex.I)⁻¹ : ℂ) • fromBlocks 1 (Complex.I • 1) (-1) (Complex.I • 1)

def rot (j : ℕ) (θ : ℝ) : M2 n :=
  Cm n * fromBlocks (diagonal fun a => if a ∈ blkA j then Complex.exp (θ * Complex.I) else Complex.exp (-θ * Complex.I)) 0 0
    (diagonal fun a => if a ∈ blkA j then Complex.exp (-θ * Complex.I) else Complex.exp (θ * Complex.I)) * CmI n

def zTop (j : ℕ) (r s : Fin n) : M2 n :=
  ((2 * Complex.I)⁻¹ : ℂ) •
    (if r ∈ blkA j ∧ s ∈ blkA j then fromBlocks 0 (single r s 1) 0 0
     else if r ∈ blkB j ∧ s ∈ blkB j then -fromBlocks 0 0 (single r s 1) 0
     else if r ∈ blkA j then fromBlocks (single r s 1) 0 0 0 else -fromBlocks 0 0 0 (single r s 1))

def zMid (j : ℕ) (r s : Fin n) : M2 n :=
  ((2 * Complex.I)⁻¹ : ℂ) •
    (if r ∈ blkA j ∧ s ∈ blkA j then fromBlocks (single r s 1) 0 0 (-single r s 1)
     else if r ∈ blkB j ∧ s ∈ blkB j then fromBlocks (single r s 1) 0 0 (-single r s 1)
     else if r ∈ blkA j then fromBlocks 0 (single r s 1) (-single r s 1) 0 else fromBlocks 0 (single r s 1) (-single r s 1) 0)

def zLow (j : ℕ) (r s : Fin n) : M2 n :=
  ((2 * Complex.I)⁻¹ : ℂ) •
    (if r ∈ blkA j ∧ s ∈ blkA j then -fromBlocks 0 0 (single r s 1) 0
     else if r ∈ blkB j ∧ s ∈ blkB j then fromBlocks 0 (single r s 1) 0 0
     else if r ∈ blkA j then -fromBlocks 0 0 0 (single r s 1) else fromBlocks (single r s 1) 0 0 0)

end PositivityTheory.Rg.Sw.LVs.TC
end
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw

namespace STD

variable {n : ℕ}

theorem dc_comp {Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ} {x : Vr n} (hΨ : DifferentiableAt ℂ Ψ (herm x))
    (a : Fin n × Fin n) :
    dc a (fun y => Ψ (herm y)) x = fderiv ℂ Ψ (herm x) (Matrix.single a.1 a.2 1) := by
  have hd : HasFDerivAt (fun y => Ψ (hermL n y)) (((fderiv ℂ Ψ (herm x)).restrictScalars ℝ).comp (hermL n)) x :=
    (hΨ.hasFDerivAt.restrictScalars ℝ).comp x (hermL n).hasFDerivAt
  have hf : fderiv ℝ (fun y => Ψ (herm y)) x = ((fderiv ℂ Ψ (herm x)).restrictScalars ℝ).comp (hermL n) :=
    hd.fderiv
  simp only [dc, hf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hermL_apply]
  rw [← herm_v, map_add (f := _), map_smul, smul_eq_mul]

theorem dList_ofFn {r : ℝ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hG : ContDiffOn ℂ ∞ G (Metric.ball 0 r)) :
    ∀ (k : ℕ) (m : Fin k → Fin n × Fin n) (x : Vr n), herm x ∈ Metric.ball 0 r →
      dList (List.ofFn m) (fun y => G (herm y)) x =
        iteratedFDeriv ℂ k G (herm x) (fun i => Matrix.single (m i).1 (m i).2 1)
  | 0, m, x, _ => by simp [dList]
  | k + 1, m, x, hx => by
    have hU : IsOpen ((hermL n) ⁻¹' Metric.ball 0 r) := Metric.isOpen_ball.preimage (hermL n).continuous
    let V : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ := fun i => Matrix.single (m i).1 (m i).2 1
    let Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ := fun H => iteratedFDeriv ℂ k G H (Fin.tail V)
    have hIt : DifferentiableOn ℂ (fun H => iteratedFDeriv ℂ k G H) (Metric.ball 0 r) := by
      have hWithin := hG.differentiableOn_iteratedFDerivWithin (m := k)
        (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
        Metric.isOpen_ball.uniqueDiffOn
      exact hWithin.congr (fun H hH => (iteratedFDerivWithin_of_isOpen k Metric.isOpen_ball hH).symm)
    have hItx : DifferentiableAt ℂ (iteratedFDeriv ℂ k G) (herm x) :=
      (hIt _ hx).differentiableAt (Metric.isOpen_ball.mem_nhds hx)
    have hΨd : DifferentiableAt ℂ Ψ (herm x) := hItx.continuousMultilinear_apply_const (Fin.tail V)
    have heq : dList (List.ofFn fun i : Fin k => m i.succ) (fun y => G (herm y)) =ᶠ[𝓝 x] fun y => Ψ (herm y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact dList_ofFn hG k (fun i => m i.succ) y hy
    rw [List.ofFn_succ]
    simp only [dList]
    have h1 : dc (m 0) (dList (List.ofFn fun i : Fin k => m i.succ) (fun y => G (herm y))) x =
        dc (m 0) (fun y => Ψ (herm y)) x := by
      simp only [dc, heq.fderiv_eq]
    rw [h1, dc_comp hΨd]
    exact (hItx.iteratedFDeriv_succ_apply_left' (m := V)).symm

end STD

end PositivityTheory.Rg.Sw.LVs
end
end
