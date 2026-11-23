module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_group_lower_left_block : Continuous (fun g : GR n => (mR g).toBlocks₂₁) := by
  exact continuous_mR.matrix_submatrix Sum.inr Sum.inl

theorem continuous_group_lower_right_block : Continuous (fun g : GR n => (mR g).toBlocks₂₂) := by
  exact continuous_mR.matrix_submatrix Sum.inr Sum.inr

theorem continuous_first_cayley_block_map : Continuous (fun g : GR n => u1 (mR g)) := by
  unfold u1
  exact ((continuous_group_lower_left_block (n := n)).const_smul Complex.I).add continuous_group_lower_right_block

theorem continuous_second_cayley_block_map : Continuous (fun g : GR n => u2 (mR g)) := by
  unfold u2
  exact ((continuous_group_lower_left_block (n := n)).const_smul Complex.I).neg.add continuous_group_lower_right_block

theorem continuous_weight_factor (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have hdet : Continuous (fun g : GR n => (mR g).det) := continuous_mR.matrix_det
  have h1 : Continuous (fun g : GR n => (u1 (mR g)).det) := continuous_first_cayley_block_map.matrix_det
  have h2 : Continuous (fun g : GR n => (u2 (mR g)).det) := continuous_second_cayley_block_map.matrix_det
  have hne : ∀ g : GR n, (mR g).det ≠ 0 := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g : GL (Fin n ⊕ Fin n) ℂ))).ne_zero
  show Continuous (fun g : GR n =>
    (mR g).det ^ e * ((u1 (mR g)).det ^ (-(p : ℤ)) * (u2 (mR g)).det ^ (-(q : ℤ))))
  exact (hdet.zpow₀ e fun g => Or.inl (hne g)).mul
    ((h1.zpow₀ _ fun g => Or.inl (hD n g).1).mul (h2.zpow₀ _ fun g => Or.inl (hD n g).2))

theorem continuous_hLoc (hD : CayleyBlocksInvertible) : Continuous (hLoc (n := n)) := by
  unfold hLoc
  exact ((continuous_first_cayley_block_map.matrix_det).norm.pow 2).inv₀ fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hD n g).1)

theorem hLoc_nonneg (g : GR n) : 0 ≤ hLoc g := by
  unfold hLoc
  positivity

theorem hLoc_pos (hD : CayleyBlocksInvertible) (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (hD n g).1) 2)

theorem first_cayley_block_one : u1 (mR (1 : GR n)) = 1 := by
  ext i j
  simp [u1, mR, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem second_cayley_block_one : u2 (mR (1 : GR n)) = 1 := by
  ext i j
  simp [u2, mR, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem weight_factor_one (p q : ℕ) (e : ℤ) : F0 (n := n) p q e 1 = 1 := by
  simp only [F0, f0, first_cayley_block_one, second_cayley_block_one]
  simp [mR]

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

def KMat (n : ℕ) : Set (M2 n) := {M | Mᴴ * M = 1 ∧ Mᴴ * JJ n * M = JJ n}

theorem isCompact_KMat : IsCompact (KMat n) := by
  have hsub : KMat n ⊆ Set.pi univ (fun _ : Fin n ⊕ Fin n => Set.pi univ (fun _ : Fin n ⊕ Fin n => Metric.closedBall (0:ℂ) 1)) := by
    intro M hM
    have hU : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hM.1
    intro i _ j _
    simpa using entry_norm_bound_of_unitary hU i j
  have hc : IsCompact (Set.pi univ (fun _ : Fin n ⊕ Fin n => Set.pi univ (fun _ : Fin n ⊕ Fin n => Metric.closedBall (0:ℂ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 1))
  refine hc.of_isClosed_subset ?_ hsub
  have hA : Continuous fun M : M2 n => Mᴴ * M :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  have hB : Continuous fun M : M2 n => Mᴴ * JJ n * M :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact (isClosed_eq hA continuous_const).inter (isClosed_eq hB continuous_const)

theorem isCompact_KR : IsCompact ((KR n : Subgroup (GR n)) : Set (GR n)) := by
  let φ : KMat n → GR n := fun M =>
    ⟨⟨M.1, M.1ᴴ, (mul_eq_one_comm).mp M.2.1, M.2.1⟩, M.2.2⟩
  have hφ : Continuous φ :=
    Continuous.subtype_mk (Units.continuous_iff.mpr
      ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩) _
  have hK : IsCompact (univ : Set (KMat n)) := isCompact_iff_isCompact_univ.mp isCompact_KMat
  have himg : φ '' univ = ((KR n : Subgroup (GR n)) : Set (GR n)) := by
    ext k
    constructor
    · rintro ⟨M, -, rfl⟩
      exact ⟨M.2.2, M.2.1⟩
    · intro hk
      refine ⟨⟨mR k, hk.2, hk.1⟩, trivial, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
  rw [← himg]
  exact hK.image hφ

instance compactSpace_KR_far : CompactSpace (KR n) := isCompact_iff_compactSpace.mp isCompact_KR

theorem continuous_first_cayley_block_map : Continuous (fun M : M2 n => u1 M) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply]
  fun_prop

theorem continuous_second_cayley_block_map : Continuous (fun M : M2 n => u2 M) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply]
  fun_prop

theorem det_mR_ne (g : GR n) : (mR g).det ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit).ne_zero

theorem continuous_weight_factor (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have hm : Continuous (mR : GR n → M2 n) := continuous_mR
  have hd : Continuous fun g : GR n => (mR g).det := hm.matrix_det
  have h1 : Continuous fun g : GR n => (u1 (mR g)).det := (continuous_first_cayley_block_map.comp hm).matrix_det
  have h2 : Continuous fun g : GR n => (u2 (mR g)).det := (continuous_second_cayley_block_map.comp hm).matrix_det
  unfold F0 f0
  exact (hd.zpow₀ e fun g => Or.inl (det_mR_ne g)).mul
    ((h1.zpow₀ _ fun g => Or.inl (hD n g).1).mul (h2.zpow₀ _ fun g => Or.inl (hD n g).2))

theorem weight_factor_ne_zero (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g ≠ 0 := by
  unfold F0 f0
  refine mul_ne_zero (zpow_ne_zero _ (det_mR_ne g)) (mul_ne_zero (zpow_ne_zero _ (hD n g).1) (zpow_ne_zero _ (hD n g).2))

theorem hLoc_pos (hD : CayleyBlocksInvertible) (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (hD n g).1) 2)

theorem continuous_hLoc (hD : CayleyBlocksInvertible) : Continuous (hLoc (n := n)) := by
  have h1 : Continuous fun g : GR n => (u1 (mR g)).det := (continuous_first_cayley_block_map.comp continuous_mR).matrix_det
  unfold hLoc
  exact (h1.norm.pow 2).inv₀ fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hD n g).1)

end PositivityTheory.Rg.Sw.AbsSt.Far
end
end

section

noncomputable section

open Matrix Filter Topology Set Polynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def lowM (n : ℕ) (s : ℝ) : M2 n := fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1

lemma lowM_mul (s s' : ℝ) : lowM n s * lowM n s' = lowM n (s + s') := by
  simp only [lowM, fromBlocks_multiply]
  simp [add_smul]

lemma lowM_zero : lowM n 0 = 1 := by
  unfold lowM; simp [fromBlocks_one]

def lowU (n : ℕ) (s : ℝ) : GL (Fin n ⊕ Fin n) ℂ :=
  ⟨lowM n s, lowM n (-s), by rw [lowM_mul, add_neg_cancel, lowM_zero], by rw [lowM_mul, neg_add_cancel, lowM_zero]⟩

def lowG (n : ℕ) (s : ℝ) : GR n := ⟨lowU n s, InG_lower s⟩

lemma lowG_cont : Continuous (lowG n) := by
  unfold lowG
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  have hc : Continuous (fun s : ℝ => lowM n s) := by
    unfold lowM
    exact Continuous.matrix_fromBlocks continuous_const continuous_const
      (Complex.continuous_ofReal.smul continuous_const) continuous_const
  exact ⟨hc, hc.comp continuous_neg⟩

lemma lowG_zero : lowG n 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact lowM_zero

lemma mR_mul (a b : GR n) : mR (a * b) = mR a * mR b := rfl

lemma lower_left_block_lowering_mul (y : GR n) (s : ℝ) :
    (mR (y * lowG n s)).toBlocks₂₁ = (mR y).toBlocks₂₁ + (s : ℂ) • (mR y).toBlocks₂₂ := by
  rw [mR_mul]
  show (mR y * lowM n s).toBlocks₂₁ = _
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  unfold lowM
  rw [fromBlocks_multiply]
  simp

lemma dense_cell (y : GR n) : y ∈ closure {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} := by
  classical
  obtain ⟨C, hC⟩ : ∃ C, C = (mR y).toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (mR y).toBlocks₂₂ := ⟨_, rfl⟩
  have hG : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hgg : mR y * mR y⁻¹ = 1 := by
    rw [← mR_mul, mul_inv_cancel]
    rfl
  have hJJ : JJ n * JJ n = -1 := by
    rw [JJ, fromBlocks_multiply]
    simp [← fromBlocks_one, fromBlocks_neg]
  have key : mR y * JJ n * (mR y)ᴴ = JJ n := by
    have h1 : (mR y)ᴴ * JJ n = JJ n * mR y⁻¹ := by
      calc (mR y)ᴴ * JJ n = (mR y)ᴴ * JJ n * (mR y * mR y⁻¹) := by rw [hgg, Matrix.mul_one]
        _ = ((mR y)ᴴ * JJ n * mR y) * mR y⁻¹ := by simp only [Matrix.mul_assoc]
        _ = JJ n * mR y⁻¹ := by rw [hG]
    calc mR y * JJ n * (mR y)ᴴ = mR y * JJ n * (mR y)ᴴ * (JJ n * JJ n) * (-1) := by
          rw [hJJ]; simp
      _ = mR y * JJ n * ((mR y)ᴴ * JJ n) * JJ n * (-1) := by simp only [Matrix.mul_assoc]
      _ = mR y * (JJ n * JJ n) * mR y⁻¹ * JJ n * (-1) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = JJ n := by
          rw [hJJ]
          simp [hgg]
  have hherm : C * Dᴴ = D * Cᴴ := by
    have hb := congrArg Matrix.toBlocks₂₂ key
    rw [← fromBlocks_toBlocks (mR y), JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply] at hb
    simp at hb
    rw [← hC, ← hD] at hb
    exact (neg_add_eq_zero.mp hb).symm
  have hpos : ((C * Cᴴ + D * Dᴴ).det) ≠ 0 := by
    have hu : IsUnit (mR y) := ⟨(y : GL (Fin n ⊕ Fin n) ℂ), rfl⟩
    open ComplexOrder in
    have hpd : ((mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr).PosDef :=
      (Matrix.PosDef.mul_conjTranspose_self _
        (Matrix.vecMul_injective_iff_isUnit.mpr hu)).submatrix Sum.inr_injective
    have he : (mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr = C * Cᴴ + D * Dᴴ := by
      change Matrix.toBlocks₂₂ (mR y * (mR y)ᴴ) = _
      rw [hC, hD]
      conv_lhs => rw [← fromBlocks_toBlocks (mR y), fromBlocks_conjTranspose, fromBlocks_multiply]
      simp
    rw [← he]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit |>.ne_zero
  have hprod : (C + Complex.I • D) * (C + Complex.I • D)ᴴ = C * Cᴴ + D * Dᴴ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_I]
    rw [← hherm, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  have hI : (C + Complex.I • D).det ≠ 0 := by
    intro h
    apply hpos
    rw [← hprod, Matrix.det_mul, h, zero_mul]
  let P : Polynomial ℂ :=
    Matrix.det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C)
  have hev : ∀ r : ℂ, P.eval r = (C + r • D).det := by
    intro r
    show Polynomial.evalRingHom r (Matrix.det _) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP : P ≠ 0 := fun h => hI (by rw [← hev, h, Polynomial.eval_zero])
  have hfin : {s : ℝ | P.eval (s : ℂ) = 0}.Finite := by
    apply Set.Finite.subset ((P.roots.toFinset.finite_toSet).preimage
      Complex.ofReal_injective.injOn)
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    simp [Polynomial.mem_roots hP, hs]
  have hT : Tendsto (fun s : ℝ => y * lowG n s) (𝓝[≠] (0 : ℝ)) (𝓝 y) := by
    have h0 : Tendsto (fun s : ℝ => y * lowG n s) (𝓝 0) (𝓝 (y * lowG n 0)) :=
      (continuous_const.mul lowG_cont).tendsto 0
    rw [lowG_zero, mul_one] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hT
  have hopen : ({s : ℝ | P.eval (s : ℂ) = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hfin.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with s hs hs0
  show ((mR (y * lowG n s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_lowering_mul, ← hC, ← hD, ← hev]
  intro h
  exact hs ⟨h, hs0⟩

end PositivityTheory.Rg.Sw.AbsSt.SZ
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.LocOpA

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem det_mR_ne (g : GR n) : (mR g).det ≠ 0 := by
  exact (Matrix.isUnits_det_units (g : GL (Fin n ⊕ Fin n) ℂ)).ne_zero

theorem continuous_toBlocks₂₁ : Continuous (fun M : M2 n => M.toBlocks₂₁) := continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inr i) (Sum.inl j)

theorem continuous_toBlocks₂₂ : Continuous (fun M : M2 n => M.toBlocks₂₂) := continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inr i) (Sum.inr j)

theorem continuous_det_first_block : Continuous (fun g : GR n => (u1 (mR g)).det) := by
  show Continuous fun g : GR n => (Complex.I • (mR g).toBlocks₂₁ + (mR g).toBlocks₂₂).det
  have h1 : Continuous fun g : GR n => (mR g).toBlocks₂₁ := continuous_toBlocks₂₁.comp continuous_mR
  have h2 : Continuous fun g : GR n => (mR g).toBlocks₂₂ := continuous_toBlocks₂₂.comp continuous_mR
  exact ((continuous_const (y := Complex.I)).smul h1 |>.add h2).matrix_det

theorem continuous_det_second_block : Continuous (fun g : GR n => (u2 (mR g)).det) := by
  show Continuous fun g : GR n => (-(Complex.I • (mR g).toBlocks₂₁) + (mR g).toBlocks₂₂).det
  have h1 : Continuous fun g : GR n => (mR g).toBlocks₂₁ := continuous_toBlocks₂₁.comp continuous_mR
  have h2 : Continuous fun g : GR n => (mR g).toBlocks₂₂ := continuous_toBlocks₂₂.comp continuous_mR
  exact ((continuous_const (y := Complex.I)).smul h1 |>.neg.add h2).matrix_det

theorem local_spherical_function_ne_zero (p q : ℤ) (g : GR n) : f0 p q (mR g) ≠ 0 := by
  unfold f0
  exact mul_ne_zero (zpow_ne_zero _ (det_first_block_ne_zero_group (inG_of g))) (zpow_ne_zero _ (det_second_cayley_block_ne (inG_of g)))

theorem weight_factor_ne_zero (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g ≠ 0 := by
  unfold F0
  exact mul_ne_zero (zpow_ne_zero _ (det_mR_ne g)) (local_spherical_function_ne_zero _ _ g)

theorem continuous_weight_factor (p q : ℕ) (e : ℤ) : Continuous (fun g : GR n => F0 p q e g) := by
  unfold F0 f0
  refine Continuous.mul (Continuous.zpow₀ (Continuous.matrix_det continuous_mR) e (fun g => Or.inl (det_mR_ne g))) ?_
  exact Continuous.mul (Continuous.zpow₀ continuous_det_first_block _ (fun g => Or.inl (det_first_block_ne_zero_group (inG_of g))))
    (Continuous.zpow₀ continuous_det_second_block _ (fun g => Or.inl (det_second_cayley_block_ne (inG_of g))))

theorem hLoc_pos (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  exact inv_pos.2 (pow_pos (norm_pos_iff.2 (det_first_block_ne_zero_group (inG_of g))) 2)

theorem continuous_hLoc : Continuous (fun g : GR n => hLoc g) := by
  unfold hLoc
  exact (continuous_det_first_block.norm.pow 2).inv₀ fun g =>
    (pow_pos (norm_pos_iff.2 (det_first_block_ne_zero_group (inG_of g))) 2).ne'

theorem toBlocks₂₁_one : (1 : M2 n).toBlocks₂₁ = 0 := by
  ext i j; simp [toBlocks₂₁]

theorem toBlocks₂₂_one : (1 : M2 n).toBlocks₂₂ = 1 := by
  ext i j; simp [toBlocks₂₂, Matrix.one_apply]

theorem weight_factor_one (p q : ℕ) (e : ℤ) : F0 p q e (1 : GR n) = 1 := by
  have h1 : mR (1 : GR n) = 1 := rfl
  simp [F0, f0, u1, u2, h1, toBlocks₂₁_one, toBlocks₂₂_one]

def kSet (n : ℕ) : Set (M2 n) := {M | InK M}

theorem isCompact_kSet : IsCompact (kSet n) := by
  have hcl : IsClosed (kSet n) := by
    have hc : Continuous fun M : M2 n => Mᴴ := continuous_id.matrix_conjTranspose
    exact (isClosed_eq ((hc.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const).inter
      (isClosed_eq (hc.matrix_mul continuous_id) continuous_const)
  have hbd : IsCompact (Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hbd.of_isClosed_subset hcl ?_
  intro M hM i _ j _
  have hu : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.2 hM.2
  simpa using entry_norm_bound_of_unitary hu i j

def kOf (M : kSet n) : KR n := ⟨mkG M.1 M.2.1, M.2⟩

theorem continuous_kOf : Continuous (kOf (n := n)) :=
  Continuous.subtype_mk (continuous_mkG continuous_subtype_val (fun M => M.2.1)) _

theorem surj_kOf : Function.Surjective (kOf (n := n)) := by
  intro k
  refine ⟨⟨mR (k : GR n), k.2⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Units.ext; rfl

instance instCompactKR : CompactSpace (KR n) := by
  have : CompactSpace (kSet n) := isCompact_iff_compactSpace.1 isCompact_kSet
  exact Function.Surjective.compactSpace continuous_kOf surj_kOf

end PositivityTheory.Rg.Sw.AbsSt.LocOpA
end
end

section

noncomputable section

open MeasureTheory Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

def BanachHol : Prop := ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (U : Set ℂ) (F : ℂ → X → ℂ), IsOpen U →
  ContinuousOn (fun y : ℂ × X => F y.1 y.2) (U ×ˢ univ) → (∀ x, DifferentiableOn ℂ (fun z => F z x) U) →
  ∃ Φ : ℂ → C(X, ℂ), DifferentiableOn ℂ Φ U ∧ ∀ z ∈ U, ∀ x, Φ z x = F z x

def DslopeFam : Prop := ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] (U : Set ℂ) (s₀ : ℂ) (F : ℂ → X → ℂ),
  IsOpen U → s₀ ∈ U → ContinuousOn (fun y : ℂ × X => F y.1 y.2) (U ×ˢ univ) → (∀ x, DifferentiableOn ℂ (fun z => F z x) U) →
  (∀ x, F s₀ x = 0) →
  ContinuousOn (fun y : ℂ × X => dslope (fun z => F z y.2) s₀ y.1) (U ×ˢ univ) ∧
    ∀ x, DifferentiableOn ℂ (fun z => dslope (fun z => F z x) s₀ z) U

def FactorL : Prop := ∀ (G : Type) [TopologicalSpace G] (S : Submodule ℂ (G → ℂ)) (l : (G → ℂ) → ℂ) (C : Set G),
  IsCompact C → (∀ F ∈ S, Continuous F) → (∀ (a : ℂ), ∀ F ∈ S, ∀ F' ∈ S, l (a • F + F') = a * l F + l F') →
  (∀ F ∈ S, ∀ M : ℝ, (∀ x ∈ C, ‖F x‖ ≤ M) → ‖l F‖ ≤ M) →
  ∃ L : C(C, ℂ) →L[ℂ] ℂ, ∀ F ∈ S, ∀ (hF : Continuous F), l F = L ⟨fun x => F x, hF.comp continuous_subtype_val⟩

def KRCpt : Prop := ∀ n : ℕ, CompactSpace (KR n)

end PositivityTheory.Rg.Sw.AbsSt
end
end
