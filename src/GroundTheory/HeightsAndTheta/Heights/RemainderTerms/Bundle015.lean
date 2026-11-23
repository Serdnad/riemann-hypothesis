module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle009
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

noncomputable section

def SchConcatExponent.rotateFun (r a : ℕ) (p : Fin (r + a)) : Fin (r + a) :=
  if h : (p : ℕ) < a then ⟨r + p, by omega⟩ else ⟨p - a, by have := p.isLt; omega⟩

def SchConcatExponent.rotateInv (r a : ℕ) (q : Fin (r + a)) : Fin (r + a) :=
  if h : (q : ℕ) < r then ⟨q + a, by omega⟩ else ⟨q - r, by have := q.isLt; omega⟩

theorem SchConcatExponent.rotateFun_val (r a : ℕ) (p : Fin (r + a)) :
    (SchConcatExponent.rotateFun r a p : ℕ) = if (p : ℕ) < a then r + p else p - a := by
  unfold SchConcatExponent.rotateFun; split <;> rfl

theorem SchConcatExponent.rotateInv_val (r a : ℕ) (q : Fin (r + a)) :
    (SchConcatExponent.rotateInv r a q : ℕ) = if (q : ℕ) < r then q + a else q - r := by
  unfold SchConcatExponent.rotateInv; split <;> rfl

def SchConcatExponent.rotate (r a : ℕ) : Equiv.Perm (Fin (r + a)) where
  toFun := SchConcatExponent.rotateFun r a
  invFun := SchConcatExponent.rotateInv r a
  left_inv p := by
    have hp := p.isLt
    apply Fin.ext
    rw [SchConcatExponent.rotateInv_val, SchConcatExponent.rotateFun_val]
    split_ifs <;> omega
  right_inv q := by
    have hq := q.isLt
    apply Fin.ext
    rw [SchConcatExponent.rotateFun_val, SchConcatExponent.rotateInv_val]
    split_ifs <;> omega

theorem SchConcatExponent.proof : SchConcatExponent.Statement := by
  intro r a c
  cases c with
  | first =>
    refine ⟨Equiv.refl _, fun lam hlam => ?_⟩
    funext p
    have hp := p.isLt
    by_cases h : (p : ℕ) < r
    · have := hlam ⟨p, h⟩
      simp [smallBlockOf, Schur.padPartition, h]
      omega
    · simp [smallBlockOf, Schur.padPartition, h]
      omega
  | last =>
    refine ⟨SchConcatExponent.rotate r a, fun lam hlam => ?_⟩
    funext p
    have hp := p.isLt
    simp only [Function.comp_apply]
    generalize hq : SchConcatExponent.rotate r a p = q
    have hv : (q : ℕ) = if (p : ℕ) < a then r + p else p - a := by
      rw [← hq]; exact SchConcatExponent.rotateFun_val r a p
    simp only [Schur.padPartition, smallBlockOf]
    by_cases h : (p : ℕ) < a
    · have hn : ¬ ((q : ℕ) < r) := by rw [hv, if_pos h]; omega
      rw [dite_eq_left h, dite_eq_right hn]
      simp only [Sum.elim_inr]
      rw [hv, if_pos h]
      omega
    · have h' : (p : ℕ) - a < r := by omega
      have hn : (q : ℕ) < r := by rw [hv, if_neg h]; exact h'
      rw [dite_eq_right h, dite_eq_left hn]
      simp only [Sum.elim_inl]
      have hqe : (⟨q, hn⟩ : Fin r) = ⟨(p : ℕ) - a, h'⟩ := Fin.ext (by rw [hv, if_neg h])
      rw [hqe, hv, if_neg h]
      have := hlam ⟨(p : ℕ) - a, h'⟩
      omega

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem sum_fin_staircase (k : ℕ) : ∑ i : Fin k, (k - 1 - (i : ℕ)) = k * (k - 1) / 2 := by
  have h := Finset.sum_range_reflect (fun i : ℕ => i) k
  rw [Fin.sum_univ_eq_sum_range (fun i => k - 1 - i) k, h, Finset.sum_range_id]

theorem SchNonHookResidues.proof (h1 : SchResidueCount.Statement) :
    SchNonHookResidues.Statement := by
  intro k nu hk hanti hsum hnot
  push Not at hnot
  obtain ⟨j, hj0, hj2⟩ := hnot
  have hk2 : 2 ≤ k := by have := j.isLt; omega
  by_contra hcon
  push Not at hcon
  set l : Fin k → ℕ := fun i => nu i + (k - 1 - (i : ℕ)) with hl
  have hinj : Function.Injective (fun i => l i % k) := by
    intro a b hab
    by_contra hne
    exact hcon a b hne hab
  have hle : ∀ i, nu i ≤ k := fun i =>
    hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hlt : ∀ i, l i < 2 * k := by
    intro i
    have := hle i
    have := i.isLt
    simp only [hl]
    omega
  have hcount := h1 k l hlt hinj
  have hsumL : ∑ i, l i = k + k * (k - 1) / 2 := by
    simp only [hl, Finset.sum_add_distrib, hsum, sum_fin_staircase]
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have h1le : nu j ≤ nu i1 := hanti (show i1 ≤ j by rw [Fin.le_iff_val_le_val]; simp [i1]; omega)
  have h0le : nu i1 ≤ nu i0 := hanti (show i0 ≤ i1 by rw [Fin.le_iff_val_le_val]; simp [i0, i1])
  have hsub : ({i0, i1} : Finset (Fin k)) ⊆ univ.filter fun i => k ≤ l i := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hv0 : (i0 : ℕ) = 0 := rfl
    have hv1 : (i1 : ℕ) = 1 := rfl
    rcases hx with rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hl, hv0, hv1] <;> omega
  have hcard : 2 ≤ (univ.filter fun i => k ≤ l i).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (by simp [i0, i1, Fin.ext_iff])] at this
  have hmul := Nat.mul_le_mul_left k hcard
  omega

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchConcatAlternant.alternant_comp_perm {N : ℕ} (w : Fin N → ℕ) (τ : Equiv.Perm (Fin N)) :
    alternant (w ∘ τ) = C ((Equiv.Perm.sign τ : ℤ) : ℚ) * alternant w := by
  unfold alternant
  have hM : (Matrix.of fun i i' : Fin N =>
      (X i : MvPolynomial (Fin N) ℚ) ^ (w ∘ τ) i') =
      (Matrix.of fun i i' : Fin N => (X i : MvPolynomial (Fin N) ℚ) ^ w i').submatrix id τ := rfl
  rw [hM, Matrix.det_permute', map_intCast]

theorem SchConcatAlternant.alternant_add_staircase {N : ℕ} (mu : Fin N → ℕ) :
    alternant (fun p : Fin N => mu p + (N - 1 - (p : ℕ))) =
      vandermondeOf (fun p : Fin N => (X p : MvPolynomial (Fin N) ℚ)) * schur (Fin N) mu := by
  rw [mul_comm, ← Schur.det_pow_add_staircase_eq, ← Matrix.det_transpose]
  rfl

theorem SchConcatAlternant.proof (h1 : SchAlternantRenamePlace.Statement)
    (h2 : SchConcatExponent.Statement) : SchConcatAlternant.Statement := by
  intro r a c
  obtain ⟨τ, hτ⟩ := h2 r a c
  refine ⟨((Equiv.Perm.sign τ : ℤ) : ℚ), ?_, fun lam hlam => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  · rw [h1, hτ lam hlam, SchConcatAlternant.alternant_comp_perm,
      SchConcatAlternant.alternant_add_staircase,
      Schur.schur_padPartition (Fin (r + a)) (fun i : Fin r => lam i - a) (r + a) (by omega), map_mul,
      rename_C]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchResidueCount.proof : SchResidueCount.Statement := by
  intro k l hlt hinj
  have hsplit : ∀ i, l i = l i % k + k * (if k ≤ l i then 1 else 0) := by
    intro i
    have hi := hlt i
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  have himg : (univ.image fun i => l i % k) = range k := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [mem_image, mem_univ, true_and] at hc
      obtain ⟨i, rfl⟩ := hc
      exact mem_range.2 (Nat.mod_lt _ i.pos)
    · rw [card_image_of_injective _ hinj, card_range, card_univ, Fintype.card_fin]
  have hres : ∑ i, l i % k = k * (k - 1) / 2 := by
    rw [← sum_range_id, ← himg, sum_image (fun i _ j _ h => hinj h)]
  calc ∑ i, l i = ∑ i, (l i % k + k * (if k ≤ l i then 1 else 0)) :=
        sum_congr rfl (fun i _ => hsplit i)
    _ = ∑ i, l i % k + k * (univ.filter fun i => k ≤ l i).card := by
        rw [sum_add_distrib, ← mul_sum, sum_boole, Nat.cast_id]
    _ = k * (k - 1) / 2 + k * (univ.filter fun i => k ≤ l i).card := by
        rw [hres]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem schurAtRoots_place_lt {r k : ℕ} (nu : Fin r → ℕ) (hanti : Antitone nu)
    (hsum : ∑ i, nu i = k) (i : Fin r) (hi : 1 ≤ nu i) : (i : ℕ) < k := by
  have h1 : (Iic i).card • 1 ≤ ∑ j ∈ Iic i, nu j :=
    Finset.card_nsmul_le_sum _ _ _ fun j hj => le_trans hi (hanti (Finset.mem_Iic.mp hj))
  have h2 : ∑ j ∈ Iic i, nu j ≤ ∑ j, nu j :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Fin.card_Iic, smul_eq_mul, mul_one] at h1
  omega

theorem SchSchurAtRootsOfUnity.proof (h1 : SchSchurRowsToK.Statement)
    (h2 : SchSchurEvalMatrix.Statement) (h3 : SchJTMatrixDetAtRoots.Statement) :
    SchSchurAtRootsOfUnity.Statement := by
  intro N r k nu hk hkN hanti hsum
  set nu' : Fin k → ℕ := fun i => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0 with hnu'
  have hplace := schurAtRoots_place_lt nu hanti hsum

  have hanti' : Antitone nu' := by
    intro i j hij
    simp only [hnu']
    by_cases hj : (j : ℕ) < r
    · have hi : (i : ℕ) < r := lt_of_le_of_lt (Fin.le_def.mp hij) hj
      rw [dif_pos hi, dif_pos hj]
      exact hanti (Fin.le_def.mpr (Fin.le_def.mp hij))
    · rw [dite_eq_right hj]; exact Nat.zero_le _

  have hsum' : ∑ i, nu' i = k := by
    set g : ℕ → ℕ := fun i => if h : i < r then nu ⟨i, h⟩ else 0 with hg
    have e1 : ∑ i, nu' i = ∑ i ∈ range k, g i := by
      rw [← Fin.sum_univ_eq_sum_range]
    have e2 : ∑ i, nu i = ∑ i ∈ range r, g i := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hg, dif_pos i.isLt]
    have hgk : ∀ i, k ≤ i → g i = 0 := by
      intro i hi
      simp only [hg]
      split_ifs with h
      · by_contra hne
        have := hplace ⟨i, h⟩ (Nat.one_le_iff_ne_zero.mpr hne)
        simp at this; omega
      · rfl
    have hgr : ∀ i, r ≤ i → g i = 0 := by
      intro i hi; simp only [hg]; rw [dite_eq_right (by omega)]
    have e3 : ∑ i ∈ range k, g i = ∑ i ∈ range (r + k), g i :=
      Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni =>
         hgk i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))
    have e4 : ∑ i ∈ range r, g i = ∑ i ∈ range (r + k), g i :=
      Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni =>
         hgr i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))
    rw [e1, e3, ← e4, ← e2, hsum]
  rw [h1 (Fin N) r k nu hanti hsum, h2 N k k _ hk hkN, h3 k nu' hk hanti' hsum']

  have hcond : (∀ i : Fin k, (i : ℕ) ≠ 0 → nu' i ≤ 1) ↔ (∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) := by
    constructor
    · intro H i hi0
      by_cases hz : nu i = 0
      · rw [hz]; exact Nat.zero_le _
      · have hik := hplace i (Nat.one_le_iff_ne_zero.mpr hz)
        have := H ⟨i, hik⟩ hi0
        simp only [hnu', dif_pos i.isLt] at this
        exact this
    · intro H i hi0
      simp only [hnu']
      split_ifs with h
      · exact H ⟨i, h⟩ hi0
      · exact Nat.zero_le _

  have hcard : (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu' i = 1).card =
      (univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card := by
    refine Finset.card_bij'
      (fun i hi => ⟨i, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi
        by_contra h; rw [dite_eq_right h] at hi; omega⟩)
      (fun i hi => ⟨i, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hplace i (by omega)⟩) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢
      obtain ⟨h0, h1⟩ := hi
      split_ifs at h1 with h
      exact ⟨h0, h1⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢
      refine ⟨hi.1, ?_⟩
      rw [dif_pos i.isLt]; exact hi.2
    · intro i hi; rfl
    · intro i hi; rfl
  simp only [hcond, hcard]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

noncomputable section

theorem rename_alternant_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (v : ι → ℕ) :
    rename e (alternant v) = alternant (v ∘ e.symm) := by
  unfold alternant
  rw [AlgHom.map_det, ← Matrix.det_submatrix_equiv_self e
    (Matrix.of fun p p' : κ => (X p : MvPolynomial κ ℚ) ^ (v ∘ e.symm) p')]
  congr 1
  ext i i'
  simp [Matrix.map_apply, Matrix.submatrix_apply]

def smallBlockEquiv (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a ≃ Fin (r + a) where
  toFun x := (smallBlockPlace r a c x).2
  invFun := smallBlockOf r a c
  left_inv := by
    intro x
    cases c <;> rcases x with i | j <;> simp [smallBlockPlace, smallBlockOf, yIndex, zIndex]
  right_inv := by
    intro p
    cases c <;> simp only [smallBlockOf] <;> split_ifs with h <;>
      apply Fin.ext <;> simp [smallBlockPlace, yIndex, zIndex] <;> omega

theorem SchAlternantRenamePlace.proof : SchAlternantRenamePlace.Statement := by
  intro r a c v
  have hg : smallBlockPlace r a c =
      (fun p : Fin (r + a) => ((0 : Fin 1), p)) ∘ smallBlockEquiv r a c := by
    funext x
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hs : (smallBlockEquiv r a c).symm = smallBlockOf r a c := rfl
  rw [hg, ← rename_rename]
  congr 1
  rw [rename_alternant_equiv, hs]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchSmallBlockProduct.sum_fin_staircase (r : ℕ) : ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r,
    Finset.sum_range_reflect (fun i => i) r, Finset.sum_range_id]

theorem SchSmallBlockProduct.vandermondeOf_X_comp {m : ℕ} {κ : Type*} (g : Fin m → κ) :
    vandermondeOf (fun i => (X (g i) : MvPolynomial κ ℚ)) =
      rename g (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ))) := by
  simp [vandermondeOf, map_prod, map_sub, rename_X]

theorem SchSmallBlockProduct.vandermondeOf_X_eq_alternant (m : ℕ) :
    vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun j : Fin m => m - 1 - (j : ℕ)) := by
  rw [← Schur.det_pow_staircase_eq_vandermondeOf, alternant, ← Matrix.det_transpose]
  rfl

theorem SchSmallBlockProduct.schur_mul_vandermondeOf_eq_alternant {m : ℕ} (lam : Fin m → ℕ) :
    schur (Fin m) lam * vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun i : Fin m => lam i + (m - 1 - (i : ℕ))) := by
  rw [← Schur.det_pow_add_staircase_eq, alternant, ← Matrix.det_transpose]
  rfl

theorem SchSmallBlockProduct.proof (h1 : SchAevalSignedRename.Statement)
    (h2 : SchAlternantHomogeneous.Statement) : SchSmallBlockProduct.Statement := by
  intro r a c lam
  set e : Fin r → ℕ := fun i => lam i + (r - 1 - (i : ℕ)) with he
  have hy : yRoot 1 r a c 0 = fun i => C c.sign * (X (yIndex 1 r a c 0 i) : RootRing 1 (r + a)) :=
    rfl
  have hz : zRoot 1 r a c 0 = fun i => (X (zIndex 1 r a c 0 i) : RootRing 1 (r + a)) := rfl

  have hVy : vandermondeOf (yRoot 1 r a c 0) =
      aeval (yRoot 1 r a c 0) (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ))) := by
    simp [vandermondeOf, map_prod, map_sub]

  have hdeg : ∑ i, e i = ∑ i, lam i + r * (r - 1) / 2 := by
    rw [he, Finset.sum_add_distrib, SchSmallBlockProduct.sum_fin_staircase]
  have hA : aeval (yRoot 1 r a c 0) (alternant e) =
      C (c.sign ^ (∑ i, lam i + r * (r - 1) / 2)) * rename (yIndex 1 r a c 0) (alternant e) := by
    rw [hy, ← hdeg]
    exact h1 (Fin r) (Fin 1 × Fin (r + a)) c.sign (yIndex 1 r a c 0) _ (alternant e) (h2 (Fin r) e)
  have hVz : vandermondeOf (zRoot 1 r a c 0) =
      rename (zIndex 1 r a c 0) (alternant fun j : Fin a => a - 1 - (j : ℕ)) := by
    rw [hz, SchSmallBlockProduct.vandermondeOf_X_comp, SchSmallBlockProduct.vandermondeOf_X_eq_alternant]
  have hplace_l : smallBlockPlace r a c ∘ Sum.inl = yIndex 1 r a c 0 := rfl
  have hplace_r : smallBlockPlace r a c ∘ Sum.inr = zIndex 1 r a c 0 := rfl
  rw [hVy, ← map_mul, SchSmallBlockProduct.schur_mul_vandermondeOf_eq_alternant, hA, hVz, map_mul, rename_rename,
    rename_rename, hplace_l, hplace_r, mul_assoc]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchBlockVandermondeOne.proof : SchBlockVandermondeOne.Statement := by
  intro N
  simp only [blockVandermonde, vandermondeOf, Fin.prod_univ_one, map_prod, map_sub, rename_X]

end GroundTheory.Heights₂.Heights.RestTerms
end
