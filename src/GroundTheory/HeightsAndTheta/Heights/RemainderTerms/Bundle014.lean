module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchEvalPowerSumHom.eq_single_of_dvd {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (e : Fin N →₀ ℕ) (hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = k)
    (hd : ∀ i ∈ e.support, k ∣ (i : ℕ) + 1) :
    e = Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1 := by
  have hsum : ∑ i ∈ e.support, e i * ((i : ℕ) + 1) = k := by
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] at hw
    exact hw
  obtain ⟨j, hj⟩ : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hsum
    omega
  have hej : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have hjk : k ≤ (j : ℕ) + 1 := Nat.le_of_dvd (by omega) (hd j hj)
  rw [← Finset.add_sum_erase _ _ hj] at hsum
  have hmul : k ≤ e j * ((j : ℕ) + 1) := le_trans hjk (Nat.le_mul_of_pos_left _ hej)
  have hrest : ∑ i ∈ e.support.erase j, e i * ((i : ℕ) + 1) = 0 := by omega
  have hjm : e j * ((j : ℕ) + 1) = k := by omega
  have hej1 : e j = 1 := by nlinarith
  have hjv : j = (⟨k - 1, by omega⟩ : Fin N) := by
    rw [hej1, one_mul] at hjm
    exact Fin.ext (by simp; omega)
  have hother : ∀ i, i ≠ j → e i = 0 := by
    intro i hij
    by_contra hne
    have hi : i ∈ e.support.erase j :=
      Finset.mem_erase.mpr ⟨hij, Finsupp.mem_support_iff.mpr hne⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hrest) i hi
    rw [Nat.mul_eq_zero] at h0
    omega
  ext i
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [← h, ← hjv, hej1]
  · exact hother i (fun hij => h (hjv.symm.trans hij.symm))

theorem SchEvalPowerSumHom.proof (h1 : SchPowerSumAtRootsOfUnity.Statement) :
    SchEvalPowerSumHom.Statement := by
  intro N k hk1 hkN S hS
  have hzv : ∀ i : Fin N, aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1)) =
      if k ∣ (i : ℕ) + 1 then (k : ℂ) else 0 := fun i =>
    h1 N k ((i : ℕ) + 1) hk1 hkN (by omega)
  have hcomp : aeval (rootOfUnityPoint N k) (powerSumHom N S) =
      aeval (fun i : Fin N => aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1))) S := by
    rw [powerSumHom, ← AlgHom.comp_apply, comp_aeval]
  rw [hcomp]

  conv_lhs => rw [S.as_sum, map_sum]
  rw [Finset.sum_eq_single (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1)]
  · have hdvd : k ∣ ((⟨k - 1, by omega⟩ : Fin N) : ℕ) + 1 := by
      simp only [Nat.sub_add_cancel hk1, dvd_refl]
    rw [aeval_monomial, Finsupp.prod_single_index (by simp), pow_one, hzv, if_pos hdvd]
    simp [mul_comm]
  · intro e he hne
    rw [aeval_monomial]
    have hw := hS (MvPolynomial.mem_support_iff.mp he)
    obtain ⟨i, hi, hik⟩ : ∃ i ∈ e.support, ¬ k ∣ (i : ℕ) + 1 := by
      by_contra hcon
      push Not at hcon
      exact hne (SchEvalPowerSumHom.eq_single_of_dvd hk1 hkN e hw hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
    rw [hzv, if_neg hik, zero_pow (Finsupp.mem_support_iff.mp hi)]
  · intro h
    rw [MvPolynomial.notMem_support_iff.mp h, monomial_zero, map_zero]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchJTMatrixDetAtRoots.proof (h1 : SchRootOfUnityBialternant.Statement)
    (h2 : SchRootOfUnityRowsPerm.Statement) (h3 : SchRootOfUnityRowsEq.Statement)
    (h4 : SchHookResidues.Statement) (h5 : SchNonHookResidues.Statement)
    (h6 : SchRootOfUnityVandermondeNe.Statement) : SchJTMatrixDetAtRoots.Statement := by
  intro k nu hk hanti hsum
  have hV := h6 k hk
  have hB := h1 k nu hk

  have hstair : (Matrix.of fun i j : Fin k =>
      rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).det =
      vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := by
    rw [← Schur.det_pow_staircase_eq_vandermondeOf (fun j : Fin k => rootOfUnity k ^ (j : ℕ))]
    congr 1
    ext i j
    simp [Matrix.of_apply, pow_mul]
  split_ifs with hhook
  · obtain ⟨π, hres, hsign⟩ := h4 k nu hk hanti hsum hhook
    have hP := h2 k (fun i => nu i + (k - 1 - (i : ℕ))) π hk hres
    rw [hstair] at hP
    have hP' : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
          vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := hP
    rw [hB] at hP'
    have := mul_right_cancel₀ hV hP'
    rw [this, hsign]
    push_cast
    rfl
  · obtain ⟨i, i', hne, hres⟩ := h5 k nu hk hanti hsum hhook
    have hZ : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det = 0 :=
      h3 k (fun i => nu i + (k - 1 - (i : ℕ))) i i' hne hres
    rw [hB] at hZ
    exact (mul_eq_zero.mp hZ).resolve_right hV

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchurPowerSumCoefficient.proof (h1 : SchWeightedPreimage.Statement)
    (h2 : SchEvalPowerSumHom.Statement) (h3 : SchSchurHomogeneous.Statement)
    (h4 : SchSchurAtRootsOfUnity.Statement) : SchurPowerSumCoefficient.Statement := by
  intro N r k hk1 hkN nu hanti hsum
  have hhom := h3 (Fin N) r nu
  rw [hsum] at hhom
  obtain ⟨S, hS, hw⟩ := h1 N k (schur (Fin N) nu) (Schur.schur_isSymmetric (σ := Fin N) nu) hhom
  refine ⟨S, hS, ?_⟩
  have e1 := h2 N k hk1 hkN S hw
  rw [hS, h4 N r k nu hk1 hkN hanti hsum] at e1
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  apply Rat.cast_injective (α := ℂ)
  split_ifs with h
  · rw [if_pos h] at e1
    push_cast
    rw [eq_div_iff hk]
    linear_combination -e1
  · rw [if_neg h] at e1
    push_cast
    rcases mul_eq_zero.mp e1.symm with h0 | h0
    · exact absurd h0 hk
    · exact h0

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchHookResidues.proof : SchHookResidues.Statement := by
  intro k nu hk hanti hsum hhook
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  set s := univ.filter fun i : Fin (n + 1) => (i : ℕ) ≠ 0 ∧ nu i = 1 with hs
  set t := s.card with ht
  have down : ∀ i j : Fin (n + 1), (i : ℕ) ≠ 0 → i ≤ j → j ∈ s → i ∈ s := by
    intro i j hi hij hj
    simp only [hs, mem_filter, mem_univ, true_and] at hj ⊢
    have h1 := hanti hij
    have h2 := hhook i hi
    exact ⟨hi, by omega⟩
  have hA : ∀ j ∈ s, (j : ℕ) ≤ t := by
    intro j hj
    have hsub : Finset.Icc 1 (j : ℕ) ⊆ s.map Fin.valEmbedding := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_map]
      refine ⟨⟨m, by omega⟩, down _ j (show m ≠ 0 by omega)
        (by rw [Fin.le_iff_val_le_val]; show m ≤ (j : ℕ); omega) hj, rfl⟩
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hB : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → (i : ℕ) ≤ t → i ∈ s := by
    intro i hi hit
    by_contra hni
    have hsub : s.map Fin.valEmbedding ⊆ Finset.Ico 1 (i : ℕ) := by
      intro m hm
      rw [Finset.mem_map] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      have hj' := hj
      simp only [hs, mem_filter, mem_univ, true_and] at hj'
      rw [Finset.mem_Ico]
      refine ⟨by simp only [Fin.valEmbedding_apply]; omega, ?_⟩
      by_contra hle
      exact hni (down i j hi (by rw [Fin.le_iff_val_le_val]; simp at hle; omega) hj)
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hval : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → nu i = if (i : ℕ) ≤ t then 1 else 0 := by
    intro i hi
    have h1 := hhook i hi
    split_ifs with h
    · have := hB i hi h
      simp only [hs, mem_filter, mem_univ, true_and] at this
      exact this.2
    · have : nu i ≠ 1 := by
        intro h1'
        have := hA i (by simp only [hs, mem_filter, mem_univ, true_and]; exact ⟨hi, h1'⟩)
        omega
      omega
  have htn : t ≤ n := by
    have hsub : s ⊆ univ.erase 0 := by
      intro i hi
      simp only [hs, mem_filter, mem_univ, true_and] at hi
      exact Finset.mem_erase.mpr ⟨fun h => hi.1 (by simp [h]), mem_univ _⟩
    have := card_le_card hsub
    simpa [card_erase_of_mem] using this
  have hnu0 : nu 0 + t = n + 1 := by
    have hpt : ∀ i, nu i = (if i = 0 then nu 0 else 0) +
        (if (i : ℕ) ≠ 0 ∧ nu i = 1 then 1 else 0) := by
      intro i
      by_cases h0 : i = 0
      · subst h0; simp
      · have hi : (i : ℕ) ≠ 0 := fun h => h0 (Fin.ext (by simp [h]))
        have := hhook i hi
        rw [if_neg h0, zero_add]
        split_ifs with h <;> omega
    have hsum2 : ∑ i, nu i = nu 0 + t := by
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_boole]
      simp [t, s]
    omega
  refine ⟨(Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)))⁻¹, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := (Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1))).surjective i
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rcases lt_trichotomy (j : ℕ) t with h | h | h
    · have hlt : j < (⟨t, by omega⟩ : Fin (n + 1)) := Fin.lt_def.mpr h
      have hv : ((Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)) j : Fin (n + 1)) : ℕ) = j + 1 :=
        Fin.coe_cycleRange_of_lt hlt
      rw [hval _ (by rw [hv]; omega), hv, if_pos (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Fin.cycleRange_of_eq (Fin.ext h), Fin.val_zero]
      have h2 : nu 0 + (n + 1 - 1 - 0) = (n - t) + (n + 1) := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hgt : (⟨t, by omega⟩ : Fin (n + 1)) < j := Fin.lt_def.mpr h
      rw [Fin.cycleRange_of_gt hgt, hval j (by omega), if_neg (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [Equiv.Perm.sign_inv, Fin.sign_cycleRange]
    simp [t, s]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem prod_one_sub_rootOfUnityPoint (h1 : SchProdOneSubRootsOfUnity.Statement) {N k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∏ i : Fin N, (1 - Polynomial.C (rootOfUnityPoint N k i) * Polynomial.X) =
      (1 - Polynomial.X ^ k : Polynomial ℂ) := by
  let f : ℕ → Polynomial ℂ := fun i =>
    1 - Polynomial.C (if i < k then rootOfUnity k ^ i else 0) * Polynomial.X
  calc ∏ i : Fin N, (1 - Polynomial.C (rootOfUnityPoint N k i) * Polynomial.X)
      = ∏ i ∈ range N, f i := Fin.prod_univ_eq_prod_range f N
    _ = ∏ i ∈ range k, f i := by
        refine (prod_subset (range_subset_range.2 hkN) fun i _ hik => ?_).symm
        have : ¬ i < k := fun h => hik (mem_range.2 h)
        simp [f, this]
    _ = ∏ i ∈ range k, (1 - Polynomial.C (rootOfUnity k ^ i) * Polynomial.X) :=
        prod_congr rfl fun i hi => by simp [f, mem_range.1 hi]
    _ = 1 - Polynomial.X ^ k := h1 k hk

theorem SchCompleteAtRootsOfUnity.proof (h1 : SchProdOneSubRootsOfUnity.Statement)
    (h2 : SchCompleteGenerating.Statement) : SchCompleteAtRootsOfUnity.Statement := by
  intro N k d hk hkN
  let H : ℕ → ℂ := fun n => aeval (rootOfUnityPoint N k) (hsymm (Fin N) ℚ n)
  have hrec : ∀ n, H n - (if k ≤ n then H (n - k) else 0) = if n = 0 then 1 else 0 := by
    intro n
    have e := h2 N (rootOfUnityPoint N k) n
    rw [prod_one_sub_rootOfUnityPoint h1 hk hkN] at e
    rw [← e]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow, sub_mul,
      sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
    simp [H]
  show H d = _
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have e := hrec d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [if_neg (by omega), sub_zero, if_pos rfl] at e
      rw [e, if_pos (dvd_zero k)]
    · by_cases hkd : k ≤ d
      · rw [if_pos hkd, if_neg (show d ≠ 0 by omega), sub_eq_zero, ih (d - k) (by omega)] at e
        have hdvd : k ∣ d - k ↔ k ∣ d := by
          conv_rhs => rw [show d = d - k + k by omega]
          exact (Nat.dvd_add_self_right).symm
        rw [e]
        exact if_congr hdvd rfl rfl
      · rw [if_neg hkd, if_neg (show d ≠ 0 by omega), sub_zero] at e
        rw [e, if_neg]
        exact fun h => hkd (Nat.le_of_dvd hd h)

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchAevalSignedRename.proof : SchAevalSignedRename.Statement := by
  intro ι κ _ _ _ _ s g d P hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hd : (∑ i ∈ e.support, e i) = d := by
    have h := hP (mem_support_iff.mp he)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [rename_monomial, aeval_monomial, monomial_eq, Finsupp.prod_mapDomain_index
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [algebraMap_eq, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← C_pow]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum, hd]
  ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchSchurRowsToK.proof : SchSchurRowsToK.Statement := by
  intro σ _ _ r k nu hanti hsum
  by_cases hrk : r ≤ k
  · exact (Schur.schur_padPartition σ nu k hrk).symm
  · replace hrk : k < r := Nat.lt_of_not_le hrk
    have hzero : ∀ i : Fin r, k ≤ (i : ℕ) → nu i = 0 := by
      intro i hi
      by_contra hne
      have hpos : 1 ≤ nu i := Nat.one_le_iff_ne_zero.mpr hne
      have h1 : ∑ j ∈ Finset.Iic i, 1 ≤ ∑ j ∈ Finset.Iic i, nu j :=
        Finset.sum_le_sum fun j hj => le_trans hpos (hanti (Finset.mem_Iic.mp hj))
      have h2 : ∑ j ∈ Finset.Iic i, nu j ≤ ∑ j, nu j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Iic] at h1
      omega
    have heq : nu = Schur.padPartition r
        (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0) := by
      funext i
      simp only [Schur.padPartition]
      by_cases hik : (i : ℕ) < k
      · simp [hik, i.isLt]
      · simp only [hik, dite_false]
        exact hzero i (by omega)
    calc schur σ nu
        = schur σ (Schur.padPartition r
            (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0)) :=
          congrArg (schur σ) heq
      _ = _ := Schur.schur_padPartition σ _ r hrk.le

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem hsymm_isHomogeneous (σ : Type*) [Fintype σ] [DecidableEq σ] (n : ℕ) :
    (hsymm σ ℚ n).IsHomogeneous n := by
  rw [Schur.hsymm_eq_sum_finsuppAntidiag]
  refine IsHomogeneous.sum _ _ _ fun l hl => ?_
  have hsum : ∑ i, l i = n := (mem_finsuppAntidiag.mp hl).1
  rw [← hsum]
  exact IsHomogeneous.prod _ _ _ fun i _ => by
    simpa using (isHomogeneous_X ℚ i).pow (l i)

theorem SchSchurHomogeneous.proof : SchSchurHomogeneous.Statement := by
  intro σ _ _ r lam
  unfold schur
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun π _ => ?_
  rw [Units.smul_def]
  have hmem : (∏ i, (Matrix.of fun i j : Fin r =>
      completeSymmetric σ ((lam i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ))) (π i) i) ∈
      homogeneousSubmodule σ ℚ (∑ i, lam i) := by
    rw [mem_homogeneousSubmodule]
    by_cases h : ∀ i, 0 ≤ (lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)
    · have hdeg : ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)).toNat = ∑ i, lam i := by
        have h1 : ((∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)).toNat : ℕ) : ℤ) =
            ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)) := by
          push_cast
          exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h i)
        have h2 : ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)) = ∑ i, (lam i : ℤ) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Equiv.sum_comp π (fun i => (lam i : ℤ)), Equiv.sum_comp π (fun i => ((i : ℕ) : ℤ))]
          ring
        exact_mod_cast h1.trans h2
      rw [← hdeg]
      refine IsHomogeneous.prod _ _ _ fun i _ => ?_
      simp only [Matrix.of_apply, completeSymmetric, if_pos (h i)]
      exact hsymm_isHomogeneous σ _
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [completeSymmetric, not_le.mpr hi])]
      exact isHomogeneous_zero _ _ _
  exact zsmul_mem hmem _

end GroundTheory.Heights₂.Heights.RestTerms
end
