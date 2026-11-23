module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle010
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContinuousOnIteratedFDerivTranslate
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem term_p (t : ℤ) (N : ℕ) (p : Fin (N + 1)) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ (N + 1) (H (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (p, e) k) 1) =
      iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 p 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (p, e) k.succ) 1) := by
  rw [ipeel0 (H (N + 1) t) 0 (analyticAt_determinant_power_zero_int (N + 1) t) N]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero]
  rfl

theorem rec_step (t : ℤ) (N : ℕ) : detD (H (N + 1) t) = ((t : ℂ) + N) * detD (H N t) := by
  rw [detD_fin _ _ (analyticAt_determinant_power_zero_int _ _), detD_fin _ _ (analyticAt_determinant_power_zero_int _ _),
    Finset.univ_perm_fin_succ, ← Finset.univ_product_univ, Finset.sum_map, Finset.sum_product,
    Fin.sum_univ_succ]
  simp only [Equiv.toEmbedding_apply, term_p, Equiv.Perm.decomposeFin.symm_sign, if_pos rfl]
  have h0 : ∀ e : Equiv.Perm (Fin N),
      (iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 (0 : Fin (N + 1)) 1)) 0)
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm ((0 : Fin (N + 1)), e) k.succ) 1) =
      t * iteratedFDeriv ℂ N (H N t) 0 (fun k => Matrix.single k (e k) 1) := by
    intro e
    simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    exact iterated_derivative_corner_case_int t e
  simp only [h0, if_true, one_mul, Fin.succ_ne_zero, if_false]
  cases N with
  | zero => simp
  | succ M =>
    simp only [iterated_derivative_column_case_int, Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg,
      Int.cast_one, neg_one_mul, neg_mul_neg]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, add_mul, Finset.mul_sum, Finset.mul_sum,
      nsmul_eq_mul, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;> push_cast <;> ring

theorem capelli_determinant_integer_rising (t : ℤ) : ∀ N : ℕ, detD (H N t) = ∏ i ∈ Finset.range N, ((t : ℂ) + i)
  | 0 => by
    rw [detD_fin 0 _ (analyticAt_determinant_power_zero_int 0 t)]
    simp [H, iteratedFDeriv_zero_apply]
  | N + 1 => by
    rw [rec_step, capelli_determinant_integer_rising t N, Finset.prod_range_succ]
    ring

end PositivityTheory.Rg.Sw.LVs.CK

namespace PositivityTheory.Rg.Sw.LVs

theorem kappaFin : KappaFin := fun N t => CK.capelli_determinant_integer_rising t N

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

variable {n : ℕ}

def matrixBlockRestriction (s t : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a ∈ s ∧ b ∈ t then x a b else 0

def matrixBlockRestrictionLinear (s t : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := matrixBlockRestriction s t
      map_add' := fun x y => by ext a b; simp only [matrixBlockRestriction, Matrix.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by
        ext a b; simp only [matrixBlockRestriction, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp }

@[simp] theorem block_part_linear_apply (s t : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ) : matrixBlockRestrictionLinear s t x = matrixBlockRestriction s t x := rfl

def conjL (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => g * (Cm n * fromBlocks (P x) (Q x) (R x) (S x) * CmI n)
      map_add' := fun x y => by
        simp only [map_add (f := _), ← fromBlocks_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply, ← fromBlocks_smul, Matrix.mul_smul, Matrix.smul_mul] }

@[simp] theorem conjL_apply (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) : conjL g P Q R S x = g * (Cm n * fromBlocks (P x) (Q x) (R x) (S x) * CmI n) := rfl

def rotL (g : M2 n) (j : ℕ) (θ : ℝ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H => g * (rot j θ * fromBlocks 0 H 0 0 * (rot j θ)⁻¹)
      map_add' := fun x y => by
        rw [show fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (x + y) 0 0 = fromBlocks 0 x 0 0 + fromBlocks 0 y 0 0 by
          rw [fromBlocks_add]; simp]
        simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        rw [show fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • x) 0 0 = c • fromBlocks 0 x 0 0 by
          rw [fromBlocks_smul]; simp]
        simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }

@[simp] theorem rotL_apply (g : M2 n) (j : ℕ) (θ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    rotL g j θ H = g * (rot j θ * fromBlocks 0 H 0 0 * (rot j θ)⁻¹) := rfl

theorem nU_eq (H : Matrix (Fin n) (Fin n) ℂ) : nU H = 1 + fromBlocks 0 H 0 0 := by
  rw [nU, ← fromBlocks_one, fromBlocks_add]; simp

theorem rot_mul_inv (j : ℕ) (θ : ℝ) : rot (n := n) j θ * (rot j θ)⁻¹ = 1 := inG_mul_inv (rot_inG j θ)

theorem rot_nU (g : M2 n) (j : ℕ) (θ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    g * rot j θ * nU H * (rot j θ)⁻¹ = g + rotL g j θ H := by
  simp only [nU_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc, rot_mul_inv, rotL_apply]

theorem rotL_single (g : M2 n) (j : ℕ) (θ : ℝ) (r s : Fin n) :
    Complex.exp (2 * θ * Complex.I) • rotL g j θ (single r s 1) =
      g * (Cm n * zLow j r s * CmI n) + Complex.exp (2 * θ * Complex.I) • (g * (Cm n * zMid j r s * CmI n)) +
        Complex.exp (2 * θ * Complex.I) ^ 2 • (g * (Cm n * zTop j r s * CmI n)) := by
  have hX : rot (n := n) j θ * fromBlocks 0 (single r s 1) 0 0 * (rot j θ)⁻¹ =
      rot j θ * nU (single r s 1) * (rot j θ)⁻¹ - 1 := by
    have h := rot_nU (1 : M2 n) j θ (single r s 1)
    simp only [Matrix.one_mul, rotL_apply] at h
    rw [h]
    abel
  rw [rotL_apply, hX, ← Matrix.mul_smul, rot_conj]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem block_part_single (s t : Finset (Fin n)) (r u : Fin n) :
    matrixBlockRestriction s t (single r u (1 : ℂ)) = if r ∈ s ∧ u ∈ t then single r u 1 else 0 := by
  ext a b
  by_cases h : r ∈ s ∧ u ∈ t
  · rw [if_pos h]
    simp only [matrixBlockRestriction, Matrix.single_apply]
    by_cases hab : r = a ∧ u = b
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h]
    · simp [hab]
  · rw [if_neg h]
    simp only [matrixBlockRestriction, Matrix.single_apply, Matrix.zero_apply]
    by_cases hab : r = a ∧ u = b
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h]
    · simp [hab]

theorem memB {j : ℕ} {a : Fin n} : a ∈ blkB j ↔ a ∉ blkA j := by simp [blkB]

def topL (g : M2 n) (j : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  conjL g (((2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkA j) (blkB j)) (((2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkA j) (blkA j))
    ((-(2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkB j) (blkB j)) ((-(2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkB j) (blkA j))

theorem topL_single (g : M2 n) (j : ℕ) (r s : Fin n) : topL g j (single r s 1) = g * (Cm n * zTop j r s * CmI n) := by
  simp only [topL, conjL_apply, ContinuousLinearMap.smul_apply, block_part_linear_apply, block_part_single, zTop]
  congr 2
  by_cases hr : r ∈ blkA j <;> by_cases hs : s ∈ blkA j <;>
    simp [hr, hs, memB, fromBlocks_smul, fromBlocks_neg]

end PositivityTheory.Rg.Sw.LVs.TC
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem rising_product_ne_zero (a : ℤ) (m : ℕ) (h : ∀ i : ℕ, i < m → (i : ℤ) + a ≠ 0) :
    ∏ i ∈ Finset.range m, ((a : ℂ) + (i : ℂ)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi h0
  apply h i (Finset.mem_range.1 hi)
  have : (((i : ℤ) + a : ℤ) : ℂ) = 0 := by push_cast; linear_combination h0
  exact_mod_cast this

theorem herm_isHermitian (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  simp only [herm, Matrix.conjTranspose_apply]
  apply Complex.ext <;> simp <;> ring

theorem inG_nU_herm (x : Fin n → Fin n → ℝ) : InG (nU (herm x)) := by
  have hH := herm_isHermitian x
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hH]

theorem fubini_step (p q : ℤ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (a b : M2 n) (ha : InG a) (hb : InG b) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    (hψ : IsSingTest ψ) :
    ∫ k, (∫ x, f0 p q (ι k * a * nU (herm x) * b) * ψ x) * (f0 p q (ι k))⁻¹ ∂μ =
      ∫ x, (∫ k, f0 p q (ι k * (a * nU (herm x) * b)) * (f0 p q (ι k))⁻¹ ∂μ) * ψ x := by
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hU0 : ∀ g : M2 n, InG g → g ∈ {x : M2 n | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} := fun g hg =>
    ⟨(gset_sub_dom hg).2.1, (gset_sub_dom hg).2.2.1⟩
  have hf0c : ContinuousOn (f0 (n := n) p q) {x : M2 n | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} :=
    (contDiffOn_scalar_section p q).continuousOn
  have hf0ne : ∀ k, f0 p q (ι k) ≠ 0 := fun k h => by
    have := scalar_section_mul_conjugate_section ((hK (ι k)).2 ⟨k, rfl⟩) p q; rw [h, zero_mul] at this; exact zero_ne_one this
  have hc : Continuous fun k => (f0 p q (ι k))⁻¹ :=
    (hf0c.comp_continuous hι (fun k => hU0 _ (hιG k))).inv₀ hf0ne
  have hherm : Continuous (herm (n := n)) := by
    unfold herm; fun_prop
  have hnU : Continuous fun x : Fin n → Fin n → ℝ => nU (herm x) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hmap : Continuous fun z : Kg × (Fin n → Fin n → ℝ) => ι z.1 * a * nU (herm z.2) * b :=
    (((hι.comp continuous_fst).mul continuous_const).mul (hnU.comp continuous_snd)).mul continuous_const
  set F : Kg × (Fin n → Fin n → ℝ) → ℂ := fun z => f0 p q (ι z.1 * a * nU (herm z.2) * b) * ψ z.2 *
    (f0 p q (ι z.1))⁻¹ with hFdef
  have hFc : Continuous F :=
    ((hf0c.comp_continuous hmap (fun z => hU0 _ (inG_mul (inG_mul (inG_mul (hιG z.1) ha) (inG_nU_herm z.2)) hb))).mul
      (hψ.1.comp continuous_snd)).mul (hc.comp continuous_fst)
  have hFs : HasCompactSupport F := by
    refine IsCompact.of_isClosed_subset (isCompact_univ.prod hψ.2.1) (isClosed_tsupport F) ?_
    refine closure_minimal (fun z hz => ⟨Set.mem_univ _, subset_tsupport ψ ?_⟩)
      (isClosed_univ.prod (isClosed_tsupport ψ))
    intro h0; apply hz; simp [hFdef, h0]
  have hFi : Integrable F (μ.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  have e1 : ∀ k, (∫ x, f0 p q (ι k * a * nU (herm x) * b) * ψ x) * (f0 p q (ι k))⁻¹ = ∫ x, F (k, x) := by
    intro k; rw [← integral_mul_const]
  have e2 : ∀ x, (∫ k, f0 p q (ι k * (a * nU (herm x) * b)) * (f0 p q (ι k))⁻¹ ∂μ) * ψ x = ∫ k, F (k, x) ∂μ := by
    intro x; rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hFdef, mul_assoc]; ring
  simp_rw [e1, e2]
  exact integral_integral_swap (f := fun k x => F (k, x)) hFi

theorem embOn_add (s : Finset (Fin n)) (T T' : Matrix s s ℂ) : embOn s (T + T') = embOn s T + embOn s T' := by
  ext a b; simp only [embOn, Matrix.add_apply]; split_ifs <;> simp

theorem embOn_smul (s : Finset (Fin n)) (c : ℂ) (T : Matrix s s ℂ) : embOn s (c • T) = c • embOn s T := by
  ext a b; simp only [embOn, Matrix.smul_apply]; split_ifs <;> simp

theorem WD_add (Q Q' R R' : Matrix (Fin n) (Fin n) ℂ) : WD (Q + Q') (R + R') = WD Q R + WD Q' R' := by
  have : fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (Q + Q') (R + R') 0 = fromBlocks 0 Q R 0 + fromBlocks 0 Q' R' 0 := by
    rw [Matrix.fromBlocks_add, add_zero]
  simp only [WD, this, Matrix.mul_add, Matrix.add_mul]

theorem WD_smul (c : ℂ) (Q R : Matrix (Fin n) (Fin n) ℂ) : WD (c • Q) (c • R) = c • WD Q R := by
  have : fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • Q) (c • R) 0 = c • fromBlocks 0 Q R 0 := by
    rw [Matrix.fromBlocks_smul, smul_zero]
  simp only [WD, this, Matrix.mul_smul, Matrix.smul_mul]

theorem WD_split (Q R : Matrix (Fin n) (Fin n) ℂ) : WD Q R = WD Q 0 + WD 0 R := by
  rw [← WD_add]; simp

def LQ (s : Finset (Fin n)) (x : M2 n) : Matrix s s ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => x * WD (embOn s T) 0
      map_add' := fun T T' => by
        have h := WD_add (embOn s T) (embOn s T') (0 : Matrix (Fin n) (Fin n) ℂ) 0
        rw [add_zero] at h
        rw [embOn_add, h, Matrix.mul_add]
      map_smul' := fun c T => by
        have h := WD_smul c (embOn s T) (0 : Matrix (Fin n) (Fin n) ℂ)
        rw [smul_zero] at h
        simp only [RingHom.id_apply]
        rw [embOn_smul, h, Matrix.mul_smul] }

def LR (s : Finset (Fin n)) (x : M2 n) : Matrix s s ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => x * WD 0 (embOn s T)
      map_add' := fun T T' => by
        have h := WD_add (0 : Matrix (Fin n) (Fin n) ℂ) 0 (embOn s T) (embOn s T')
        rw [add_zero] at h
        rw [embOn_add, h, Matrix.mul_add]
      map_smul' := fun c T => by
        have h := WD_smul c (0 : Matrix (Fin n) (Fin n) ℂ) (embOn s T)
        rw [smul_zero] at h
        simp only [RingHom.id_apply]
        rw [embOn_smul, h, Matrix.mul_smul] }

theorem LQ_apply (s : Finset (Fin n)) (x : M2 n) (T : Matrix s s ℂ) : LQ s x T = x * WD (embOn s T) 0 := rfl

theorem LR_apply (s : Finset (Fin n)) (x : M2 n) (T : Matrix s s ℂ) : LR s x T = x * WD 0 (embOn s T) := rfl

theorem mul_mX (x : M2 n) (Q R : Matrix (Fin n) (Fin n) ℂ) : x * mX 1 Q R 1 = x + x * WD Q 0 + x * WD 0 R := by
  rw [mX_eq, Matrix.mul_add, Matrix.mul_one, WD_split, Matrix.mul_add, add_assoc]

theorem fin_append_mul {a b : ℕ} (M : M2 n) (u : Fin a → M2 n) (v : Fin b → M2 n) :
    (fun i => M * Fin.append u v i) = Fin.append (fun i => M * u i) (fun i => M * v i) := by
  funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

theorem contDiff_mulLeft (M : M2 n) : ContDiff ℂ ∞ (fun x : M2 n => M * x) :=
  (LinearMap.mulLeft ℂ M).toContinuousLinearMap.contDiff

theorem contDiff_nU_sandwich (a b : M2 n) : ContDiff ℂ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun H => a * fromBlocks 0 H 0 0 * b
      map_add' := fun H H' => by
        have : (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (H + H') 0 0 : M2 n) = fromBlocks 0 H 0 0 + fromBlocks 0 H' 0 0 := by
          rw [Matrix.fromBlocks_add]; simp
        rw [this, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c H => by
        have : (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • H) 0 0 : M2 n) = c • fromBlocks 0 H 0 0 := by
          rw [Matrix.fromBlocks_smul]; simp
        simp only [RingHom.id_apply]
        rw [this, Matrix.mul_smul, Matrix.smul_mul] }
  have h : (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) = fun H => a * b + L.toContinuousLinearMap H := by
    funext H
    have : nU H = 1 + (fromBlocks 0 H 0 0 : M2 n) := by
      rw [nU, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]; simp
    simp only [L, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  rw [h]
  exact contDiff_const.add L.toContinuousLinearMap.contDiff

theorem iteratedFDeriv_mul_const_of (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (c : ℂ)
    (x : M2 n) (hx : x ∈ U) (N : ℕ) (v : Fin N → M2 n) :
    iteratedFDeriv ℂ N (fun y => F y * c) x v = iteratedFDeriv ℂ N F x v * c := by
  have hFx : ContDiffAt ℂ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
  have h := ContinuousLinearMap.iteratedFDeriv_comp_left ((ContinuousLinearMap.mul ℂ ℂ).flip c) hFx
    (i := N) (by exact_mod_cast le_top)
  have e : (fun y => F y * c) = (ContinuousLinearMap.mul ℂ ℂ).flip c ∘ F := by funext y; rfl
  rw [e, h]; rfl

theorem integrable_of_continuous_K {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasureOnCompacts μ] {f : Kg → ℂ} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f) (Set.subset_univ _))

theorem detD_detD_mul_const {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (x₀ : M2 n) (hx : x₀ ∈ U)
    (LA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : Matrix ιB ιB ℂ →L[ℂ] M2 n) (c : ℂ) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S) * c)) =
      detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) * c := by
  rw [detD_detD_comp (fun y => F y * c) U hU (hF.mul contDiffOn_const) x₀ hx LA LB,
    detD_detD_comp F U hU hF x₀ hx LA LB, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [iteratedFDeriv_mul_const_of F U hU hF c x₀ hx]; ring

end PositivityTheory.Rg.Sw.LVs
end
end
