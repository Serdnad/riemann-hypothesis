module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle009
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Equiv

namespace Comb

theorem add_index_le_of_strictAnti {m : ℕ} {f : Fin m → ℕ} (hf : StrictAnti f) (a b : Fin m)
    (hab : a ≤ b) : f b + (b : ℕ) ≤ f a + (a : ℕ) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have h1 := ih (by omega)
    have h2 : f ⟨n + 1, hb⟩ < f ⟨n, by omega⟩ := hf (by simp [Fin.lt_def])
    simp only at h1 ⊢
    omega

theorem CombSortShift.proof (h1 : CombSortLe.Statement) : CombSortShift.Statement := by
  intro m lam hlam q i hq hinj
  set u := Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) with hu
  obtain ⟨σ, hσ⟩ := exists_perm_strictAnti hinj
  have hge : ∀ k : Fin m, stair m k ≤ u (σ k) := by
    intro k
    have hk := add_index_le_of_strictAnti hσ k ⟨m - 1, by have := k.isLt; omega⟩ (by rw [Fin.le_def]; exact Nat.le_sub_one_of_lt k.isLt)
    simp only [Function.comp_apply] at hk
    simp only [stair]
    omega
  refine ⟨σ, fun k => u (σ k) - stair m k, ?_, ?_, ?_⟩
  · intro a b hab
    have h := add_index_le_of_strictAnti hσ a b hab
    have ha := hge a
    have hb := hge b
    simp only [Function.comp_apply, stair] at h ha hb ⊢
    omega
  · intro k
    have hl : Antitone (fun j => lam j + stair m j) := by
      intro a b hab
      have := hlam hab
      simp only [stair]
      have : (a : ℕ) ≤ b := hab
      omega
    have hul : ∀ j, u j ≤ lam j + stair m j := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [hu]
      · simp [hu, Function.update_of_ne hj]
    have := h1 m u (fun j => lam j + stair m j) σ hl hul hσ.antitone k
    show u (σ k) - stair m k ≤ lam k
    omega
  · intro k
    have := hge k
    show u (σ k) = u (σ k) - stair m k + stair m k
    omega

end Comb

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauOfWord.proof (h1 : CombCellOfWordMem.Statement)
    (h2 : CombCellOfWordInj.Statement) (h3 : CombCellOfWordMono.Statement) :
    CombTableauOfWord.Statement := by
  intro m lam _hlam w hw
  have hL : IsLattice w := by
    simp only [latticeWords, mem_filter] at hw
    exact hw.2.1
  let f : Fin (youngCells lam).card → youngCells lam := fun t => ⟨cellOfWord w t, h1 m lam w hw t⟩
  have hinj : Function.Injective f := by
    intro s t hst
    exact h2 m _ w (congrArg Subtype.val hst)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp⟩
  let T : youngCells lam ≃ Fin (youngCells lam).card := (Equiv.ofBijective f hbij).symm
  have hT : ∀ p : youngCells lam, cellOfWord w (T p) = p.1 := by
    intro p
    have : f (T p) = p := (Equiv.ofBijective f hbij).apply_symm_apply p
    exact congrArg Subtype.val this
  refine ⟨T, ?_, ?_⟩
  · intro p q hpq1 hpq2
    apply h3 m _ w hL
    · rw [hT p, hT q]; exact hpq1
    · rw [hT p, hT q]; exact hpq2
  · funext t
    show (T.symm t).1.1 = w t
    rfl

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem CombCardYoungCells.proof : CombCardYoungCells.Statement := by
  intro m lam
  classical
  unfold youngCells
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle : lam i ≤ ∑ j, lam j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (lam j)) (Finset.mem_univ i)
  have hset : (Finset.range (∑ j, lam j)).filter (fun c => c < lam i) = Finset.range (lam i) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.card_range (lam i), ← hset, Finset.card_filter]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Comb

theorem CombCfUpdateZero.proof : CombCfUpdateZero.Statement := by
  intro m A hA lam hlam i hpos hcase

  have key : (i : ℕ) + 1 < m ∧ ∀ h : (i : ℕ) + 1 < m, lam ⟨i + 1, h⟩ = lam i := by
    by_cases h0 : lam i = 0
    · have hs : 1 ≤ stair m i := by omega
      simp only [stair] at hs
      refine ⟨by omega, fun h => ?_⟩
      have := hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))
      omega
    · have hna : ¬ Antitone (Function.update lam i (lam i - 1)) := by
        rcases hcase with h | h
        · exact absurd h h0
        · exact h
      have hK : ∃ b : Fin m, i < b ∧ lam i ≤ lam b := by
        by_contra hK
        push Not at hK
        apply hna
        intro a b hab
        simp only [Function.update_apply]
        split_ifs with hb ha ha
        · exact le_rfl
        · have := hlam (show a ≤ i from hb ▸ hab)
          omega
        · have hib : i < b := lt_of_le_of_ne (ha ▸ hab) (fun e => hb e.symm)
          have := hK b hib
          omega
        · exact hlam hab
      obtain ⟨b, hib, hb⟩ := hK
      have hib' : (i : ℕ) < b := hib
      have hm : (i : ℕ) + 1 < m := by have := b.isLt; omega
      refine ⟨hm, fun h => ?_⟩
      have h1 := hlam (show i ≤ (⟨i + 1, h⟩ : Fin m) from Fin.le_iff_val_le_val.mpr (by simp))
      have h2 := hlam (show (⟨i + 1, h⟩ : Fin m) ≤ b from Fin.le_iff_val_le_val.mpr (by simp; omega))
      omega
  obtain ⟨hm, heq⟩ := key
  have hne : i ≠ (⟨i + 1, hm⟩ : Fin m) := by
    intro e
    have := congrArg Fin.val e
    simp at this
  apply cf_eq_zero_of_eq hA hne
  rw [Function.update_self, Function.update_of_ne hne.symm, heq hm]
  simp only [stair] at hpos ⊢
  omega

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Comb Equiv

theorem CombDetDescFactorial.proof : CombDetDescFactorial.Statement := by
  intro m l
  rw [vandermondeOf_eq_det]

  set v : Fin m → ℚ := fun i => (l i : ℚ)
  have hA : (Matrix.of fun i j : Fin m => ((l i).descFactorial (stair m j) : ℚ)) =
      (Matrix.of fun i j : Fin m => (descPochhammer ℚ (j : ℕ)).eval (v i)).submatrix
        id Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, v,
      descPochhammer_eval_eq_descFactorial, stair]
    rw [Fin.val_rev]
    congr 2
    omega
  have hB : (Matrix.of fun i j : Fin m => v i ^ (m - 1 - (j : ℕ))) =
      (Matrix.vandermonde v).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, Fin.val_rev,
      Matrix.vandermonde_apply]
    congr 1
    omega
  rw [hA, hB, Matrix.det_permute', Matrix.det_permute',
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
      (fun j => descPochhammer ℚ (j : ℕ))
      (fun j => descPochhammer_natDegree ℚ _)
      (fun j => monic_descPochhammer ℚ _)]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

open scoped Classical

open Comb

theorem CombPcntAppend.proof : CombPcntAppend.Statement := by
  intro m n q w s t i
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.append_left, Fin.val_castAdd]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.append_right, Fin.val_natAdd]
    have h : (n + (k : ℕ) < t) ↔ ((k : ℕ) < t - n) := by omega
    simp only [h]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Equiv

theorem CombSortLe.proof : CombSortLe.Statement := by
  intro m u l σ hl hul hu k
  obtain ⟨j, hjk, hkj⟩ : ∃ j : Fin m, j ≤ k ∧ k ≤ σ j := by
    by_contra h
    push Not at h
    have hcard : (Iic k).card ≤ (Iio k).card := by
      refine card_le_card_of_injOn σ ?_ σ.injective.injOn
      intro j hj
      simp only [coe_Iic, coe_Iio, Set.mem_Iic, Set.mem_Iio] at hj ⊢
      exact h j hj
    rw [Fin.card_Iic, Fin.card_Iio] at hcard
    omega
  calc u (σ k) ≤ u (σ j) := hu hjk
    _ ≤ l (σ j) := hul _
    _ ≤ l k := hl hkj

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Equiv

theorem CombSortShiftDistinct.proof : CombSortShiftDistinct.Statement := by
  intro m l hl q hq i j hij hqi hqj σ τ heq
  have hr := congrArg Set.range heq
  rw [σ.surjective.range_comp, τ.surjective.range_comp] at hr
  have hmem : l i ∈ Set.range (Function.update l j (l j - q)) :=
    ⟨i, by rw [Function.update_of_ne hij]⟩
  rw [← hr] at hmem
  obtain ⟨k, hk⟩ := hmem
  by_cases hki : k = i
  · subst hki
    rw [Function.update_self] at hk
    omega
  · rw [Function.update_of_ne hki] at hk
    exact hki (hl hk)

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem CombYoungRowCard.proof : CombYoungRowCard.Statement := by
  intro m lam i
  rw [← Finset.card_range (lam i)]
  refine Finset.card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p hp
    have hp' : p.1.1 = i := (mem_filter.1 hp).2
    have hc : p.1.2 < lam p.1.1 := (mem_filter.1 p.2).2
    rw [hp'] at hc
    exact mem_range.2 hc
  · intro p hp q hq h
    have hp' : p.1.1 = i := (mem_filter.1 hp).2
    have hq' : q.1.1 = i := (mem_filter.1 hq).2
    exact Subtype.ext (Prod.ext (hp'.trans hq'.symm) h)
  · intro c hc
    have hc' : c < lam i := mem_range.1 hc
    have hmem : ((i, c) : Fin m × ℕ) ∈ youngCells lam := by
      unfold youngCells
      refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_range.2 ?_⟩, hc'⟩
      exact lt_of_lt_of_le hc'
        (Finset.single_le_sum (fun j _ => Nat.zero_le (lam j)) (mem_univ i))
    exact ⟨⟨(i, c), hmem⟩, mem_filter.2 ⟨mem_univ _, rfl⟩, rfl⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Comb

theorem FrobeniusDimensionFormula.proof (h1 : CombTableEqWords.Statement)
    (h2 : CombCfAtStair.Statement) (h3 : CombCfVandermondePsumOne.Statement) :
    FrobeniusDimensionFormula.Statement := by
  intro m lam hlam
  have hsum : ∑ i, (lam i + stair m i) = ∑ i, stair m i + ∑ i, lam i := by
    rw [Finset.sum_add_distrib, add_comm]
  have e := h3 m (∑ i, lam i) (fun i => lam i + stair m i) hsum
  rw [h2 m (∑ i, lam i) lam hlam] at e
  rw [h1 m lam hlam, e]
  simp only [stair]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem vandermondeOf_X_fin_ne_zero (r : ℕ) :
    vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) ≠ 0 := by
  unfold vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
  refine sub_ne_zero.mpr fun h => hij ?_
  exact X_injective (R := ℚ) h

theorem vandermondeOf_X_isHomogeneous (r : ℕ) :
    (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ))).IsHomogeneous
      (r * (r - 1) / 2) := by
  have h := IsHomogeneous.prod (σ := Fin r) (R := ℚ) Finset.univ
    (fun i : Fin r => ∏ j ∈ Finset.Ioi i, ((X i : MvPolynomial (Fin r) ℚ) - X j))
    (fun i => ∑ _j ∈ Finset.Ioi i, 1)
    (fun i _ => IsHomogeneous.prod _ _ _ fun j _ =>
      (isHomogeneous_X ℚ i).sub (isHomogeneous_X ℚ j))
  have hdeg : ∑ i : Fin r, ∑ _j ∈ Finset.Ioi i, (1 : ℕ) = r * (r - 1) / 2 := by
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, ← Finset.sum_range_id]
    exact Finset.sum_range_reflect (fun i => i) r
  rw [hdeg] at h
  exact h

theorem psum_isHomogeneous (σ : Type*) [Fintype σ] (q : ℕ) :
    (psum σ ℚ q).IsHomogeneous q := by
  unfold psum
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i q

theorem FrobeniusCharacterFormula.proof (h1 : SchAltPartitionExpansion.Statement) :
    FrobeniusCharacterFormula.Statement := by
  intro r q m _hq
  set V := vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) with hVdef
  set S := psum (Fin r) ℚ q * psum (Fin r) ℚ 1 ^ m with hSdef
  have hprod : ((q :: List.replicate m 1).map fun k => psum (Fin r) ℚ k).prod = S := by
    simp [S, List.map_replicate, List.prod_replicate]
  have halt : Comb.IsAlt (V * S) := by
    have := Comb.isAlt_vandermonde_mul_prod (m := r) (q :: List.replicate m 1)
    rwa [hprod] at this
  have hhom : (V * S).IsHomogeneous (r * (r - 1) / 2 + (q + m)) := by
    have h := (vandermondeOf_X_isHomogeneous r).mul
      ((psum_isHomogeneous (Fin r) q).mul ((psum_isHomogeneous (Fin r) 1).pow m))
    rwa [one_mul] at h
  have hexp := h1 r (q + m) (V * S) halt hhom
  apply mul_left_cancel₀ (vandermondeOf_X_fin_ne_zero r)
  rw [Finset.mul_sum]
  refine hexp.trans (Finset.sum_congr rfl fun lam _ => ?_)
  simp only [symmetricGroupCharacter, hprod]
  ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

theorem SchAlternantHomogeneous.proof : SchAlternantHomogeneous.Statement := by
  intro ι _ _ e
  unfold alternant
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro σ _
  have h : IsHomogeneous (∏ i, (X (σ i) : MvPolynomial ι ℚ) ^ e i) (∑ i, e i) :=
    IsHomogeneous.prod _ _ _ (fun i _ => isHomogeneous_X_pow _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simp only [hs, Matrix.of_apply, one_smul, Units.neg_smul]
  · exact h
  · exact h.neg

end GroundTheory.Heights₂.Heights.RestTerms
end
