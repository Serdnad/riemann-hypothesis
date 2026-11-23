module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle002
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle011
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle001
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OneMemDualWeyl
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundOfEdgeCount
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CcDualWtAnti
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIso
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsTwoWeightIff
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem rowA_of_iwh {K : Type} [CommRing K] {k n : ℕ} {f : MvPolynomial (Fin k × Fin n) K} {μ : Fin k → ℕ}
    (h : IsWeightedHomogeneous (rowW k n) f μ) (a : Fin k) : RowA a f (μ a) := by
  intro u hu
  rw [← ldrow_weight_rowW, h hu]

theorem qt_cnt (m : ℕ) (i a' : Fin (m + 1)) :
    (∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ)) a' = if a' = i then 0 else 1 := by
  classical
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  split_ifs with h
  · subst h
    exact Finset.sum_eq_zero fun p _ => if_neg (Fin.succAbove_ne a' p).symm
  · obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq h
    rw [Finset.sum_eq_single q]
    · rw [if_pos rfl]
    · intro p _ hp
      exact if_neg fun e => hp (Fin.succAbove_right_injective e).symm
    · intro hq
      exact absurd (Finset.mem_univ q) hq

theorem qt_covY_iwh (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) :
    IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (covY K m i) (∑ p : Fin m, Pi.single (i.succAbove p) 1) := by
  have e : covY K m i = ((-1 : ℤ) ^ (i : ℕ)) • initMinor K (n := m + 1) i.succAbove (Nat.le_succ m) := by
    rw [zsmul_eq_mul]
    push_cast
    rfl
  rw [e, ← mem_weightedHomogeneousSubmodule]
  exact zsmul_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 (ldbasis_initMinor_rowHom K i.succAbove (Nat.le_succ m))) _

theorem dPsi_monomial (K : Type) [Field K] (m : ℕ) (v : XY (m + 1) →₀ ℕ) (c : K) :
    deltaB K m (PsiXY K m (monomial v c)) =
      C c * ((∏ i : Fin (m + 1), X (i, (0 : Fin (m + 1))) ^ v (Sum.inl i)) * ∏ i : Fin (m + 1), covY K m i ^ v (Sum.inr i)) := by
  have hx : ∀ i : Fin (m + 1), deltaB K m (PsiXY K m (X (Sum.inl i))) = X (i, 0) := by
    intro i
    simp [PsiXY, deltaB]
  have hy : ∀ i : Fin (m + 1), deltaB K m (PsiXY K m (X (Sum.inr i))) = covY K m i := by
    intro i
    simp only [PsiXY, deltaB, aeval_X, Sum.elim_inr, rename_rename]
    have : (Prod.snd ∘ Prod.mk false : Fin (m + 1) × Fin (m + 1) → Fin (m + 1) × Fin (m + 1)) = id := rfl
    rw [this, rename_id_apply]
  have hC : deltaB K m (PsiXY K m (C c)) = C c := by
    simp only [← algebraMap_eq, AlgHom.commutes]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, hx, hy, hC]

def qtW (m : ℕ) (v : XY (m + 1) →₀ ℕ) : Fin (m + 1) → ℕ :=
  0 + ((∑ i : Fin (m + 1), v (Sum.inl i) • (Pi.single i 1 : Fin (m + 1) → ℕ)) +
    ∑ i : Fin (m + 1), v (Sum.inr i) • ∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ))

theorem dPsi_monomial_iwh (K : Type) [Field K] (m : ℕ) (v : XY (m + 1) →₀ ℕ) (c : K) :
    IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (deltaB K m (PsiXY K m (monomial v c))) (qtW m v) := by
  rw [dPsi_monomial]
  refine (isWeightedHomogeneous_C _ c).mul (IsWeightedHomogeneous.mul ?_ ?_)
  · exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (isWeightedHomogeneous_X K (rowW (m + 1) (m + 1)) (i, 0)).pow _
  · exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (qt_covY_iwh K m i).pow _

theorem qtW_apply (m : ℕ) (v : XY (m + 1) →₀ ℕ) (a' : Fin (m + 1)) :
    qtW m v a' + v (Sum.inr a') = v (Sum.inl a') + yDeg v := by
  classical
  unfold qtW yDeg
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : ∑ i : Fin (m + 1), v (Sum.inl i) * (Pi.single i 1 : Fin (m + 1) → ℕ) a' = v (Sum.inl a') := by
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  have h2 : ∀ i : Fin (m + 1), (∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ) a') = if a' = i then 0 else 1 := by
    intro i
    rw [← Finset.sum_apply]
    exact qt_cnt m i a'
  have h3 : v (Sum.inr a') = ∑ i : Fin (m + 1), v (Sum.inr i) * (if a' = i then 1 else 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  rw [h1, add_assoc]
  congr 1
  simp only [h2]
  conv_lhs => rw [h3]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem cloudOne_of (h : ContractionStandardLattice) : CloudOne := by
  intro p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  obtain ⟨abelian₂, hK, hE, hI, nb, s, s', ka, hnb, hka, hs, hs', h24⟩ := h p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have hm1 : 1 ≤ mm + 1 := by omega
  have hloA : Antitone (lam - wtPQ (mm + 1) P Q) := caLo_anti mm ccl P Q lam hlam h0 hl hmid
  have hloA' : Antitone (dualWt (lam - wtPQ (mm + 1) P Q)) := cc_dualWt_anti _ hloA
  have hmuA : Antitone (wtPQ (mm + 1) P Q) := wtPQ_anti _ _ _ hm1
  have hmpA : Antitone (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl)) := wtPQ_anti _ _ _ hm1
  have hzeA : Antitone (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) := wtPQ_anti _ _ _ hm1
  have hlo0 : (lam - wtPQ (mm + 1) P Q) 0 = (ccl : ℤ) := by
    rw [lo_val mm ccl P Q lam h0 hl, ite_eq_left rfl]
  have hloL : (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
    rw [lo_val mm ccl P Q lam h0 hl, ite_eq_right (caLast_ne_zero mm), ite_eq_left rfl]
  have hloL' : dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
    unfold dualWt
    rw [Fin.rev_last, hlo0]
  refine ⟨abelian₂, hK, ?_, ?_⟩
  · rintro Λ ⟨g, hg, rfl⟩ v hv t ht
    rw [mem_invariant_sections_iff_integral hinj _ _ hmpA g hg]
    have hv0 := (mem_invariant_sections_iff_integral hinj _ lam hlam g hg v).1 hv
    have ht0 := (mem_invariant_sections_iff_integral hinj _ _ hloA' g hg t).1 ht
    have hvK : v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam) :=
      la_nablaLTw_le _ lam g hg v (H0_le_twisted_nabla _ lam hlam g hg hv)
    have htK : t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) :=
      la_nablaLTw_le _ _ g hg t (H0_le_twisted_nabla _ _ hloA' g hg ht)
    have h3 := hI _ hv0 _ ht0
    rw [map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g hg v hvK t htK, ← zpow_add₀ hg.ne_zero] at h3
    have he : lam (Fin.last (mm + 1)) + dualWt (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) =
        wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl) (Fin.last (mm + 1)) := by
      rw [hl, hloL', wtPQ_last]
      push_cast
      ring
    rwa [he] at h3
  · intro g hg
    have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
    refine ⟨nb, g.det ^ (2 * ccl) • rowAct R.Kf g⁻¹ (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))),
      fun b => g.det ^ ccl • rowAct R.Kf g⁻¹ (s b), fun a' => g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'), ka, hnb, hka, ?_, ?_⟩
    · intro a' b F hF
      have hF0 : rowAct R.Kf g F ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) P Q)) :=
        dualWeylRowStable R.Kf _ _ _ g F hF
      have e1 : F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b)) = g.det ^ ccl • rowAct R.Kf g⁻¹ (rowAct R.Kf g F * s b) := by
        rw [map_mul, rowAct_cancel_inv g hg, mul_smul_comm]
      have hsK := intO_le (O := R.O) _ _ _ (hs b).1
      have hsK' := intO_le (O := R.O) _ _ _ (hs' a').1
      have hv : rowAct R.Kf g F * s b ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam) := by
        have h4 := dualWeyl_mul R.Kf _ _ _ _ hF0 hsK
        rw [← nuOf_add _ _ hmuA hloA] at h4
        have e : wtPQ (mm + 1) P Q + (lam - wtPQ (mm + 1) P Q) = lam := by abel
        rwa [e] at h4
      show abelian₂ (blockEmb R.Kf true (F * (g.det ^ ccl • rowAct R.Kf g⁻¹ (s b))) *
        blockEmb R.Kf false (g.det ^ ccl • rowAct R.Kf g⁻¹ (s' a'))) = _
      rw [e1, map_smul, map_smul, smul_mul_smul_comm, map_smul, hE g⁻¹ hgi _ hv _ hsK', h24 a' b _ hF0]
      split_ifs
      · rw [map_smul, map_mul, rowAct_cancel_inv g hg, smul_smul, smul_mul_assoc, smul_smul]
        congr 1
        ring
      · rw [map_zero, smul_zero]
    · intro c hc
      have hgD : IsUnit (g * lb_D (mm + 1 + 1) 1 c).det := by
        rw [Matrix.det_mul]
        exact hg.mul (lb_D_det _ 1 c hc)
      have hzR : Row0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))) (2 * ccl + 2 * ccl) := by
        have h5 := highest_weight_first_entry (K := R.Kf) (mm + 1) _ (nuOf_anti _ hzeA)
        have h6 : nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) 0 = 2 * ccl + 2 * ccl := by
          unfold nuOf
          rw [wtPQ_zero, wtPQ_last]
          omega
        rwa [h6] at h5
      have hcz := core_id g hg c hc (2 * ccl) (2 * ccl) _ hzR
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD, wtPQ_last, hcz]
        exact hw_int _ _ (nuOf_anti _ hzeA)
      · rintro ⟨z', hz', he⟩
        have h7 := (mem_invariant_sections_iff_integral hinj _ _ hzeA _ hgD z').1 hz'
        rw [wtPQ_last] at h7
        apply hw_prim (O := R.O) (K := R.Kf) hinj R.w R.w_mem (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)))
        refine ⟨_, h7, ?_⟩
        rw [← hcz, he, smulO_eq R.w z', map_smul, smulO_eq R.w, smul_comm]
      · intro b
        have hR : Row0 (s b) (ccl + ccl) := by rw [← two_mul]; exact (hs b).2
        rw [mem_invariant_sections_iff_integral hinj _ _ hloA _ hgD, hloL, core_id g hg c hc ccl ccl _ hR]
        exact (hs b).1
      · intro a'
        have hR : Row0 (s' a') (ccl + ccl) := by rw [← two_mul]; exact (hs' a').2
        rw [mem_invariant_sections_iff_integral hinj _ _ hloA' _ hgD, hloL', core_id g hg c hc ccl ccl _ hR]
        exact (hs' a').1

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def qcOm (n s : ℕ) : Fin n → ℕ := fun t => if t.val < s then 1 else 0

theorem qc_shapeDeg_succ {n K : ℕ} (sz : Fin (K + 1) → ℕ) :
    (shapeDeg sz : Fin n → ℕ) = qcOm n (sz 0) + shapeDeg (fun k : Fin K => sz k.succ) := by
  funext t
  simp only [shapeDeg, qcOm, Pi.add_apply, Finset.card_filter]
  rw [Fin.sum_univ_succ]

theorem qc_shapeDeg_zero {n : ℕ} (sz : Fin 0 → ℕ) : (shapeDeg sz : Fin n → ℕ) = 0 := by
  funext t
  simp [shapeDeg]

theorem qc_initMinor_mem (R : Type) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs ∈ dualWeyl R r n (qcOm n s) := by
  have h := bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have h1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs := by
    simp [bideterminant]
  have h2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = qcOm n s := by
    funext t
    simp only [shapeDeg, qcOm, Finset.card_filter]
    simp
  rw [h1, h2] at h
  exact h

theorem qc_bidet_succ (R : Type) [CommRing R] {r n K : ℕ} (sz : Fin (K + 1) → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    bideterminant R sz hsz I = initMinor R (I 0) (hsz 0) *
      bideterminant R (fun k : Fin K => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ) := by
  unfold bideterminant
  rw [Fin.prod_univ_succ]

theorem qc_bidet_zero (R : Type) [CommRing R] {r n : ℕ} (sz : Fin 0 → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : bideterminant R sz hsz I = 1 := by
  simp [bideterminant]

theorem qc_pow_mem (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (y : MvPolynomial (Fin r × Fin n) R)
    (hy : y ∈ dualWeyl R r n ν) (k : ℕ) : y ^ k ∈ dualWeyl R r n (k • ν) := by
  induction k with
  | zero => rw [pow_zero, zero_smul]; exact one_mem_dualWeyl R r n
  | succ k ih => rw [pow_succ, succ_nsmul]; exact dualWeyl_mul R r n _ _ ih hy

theorem qc_full_minor (A : Type) [CommRing A] (r s : ℕ) (hs : s ≤ r) (I : Fin s → Fin r) (hI : StrictMono I)
    (h : s = r) : initMinor A I hs = detY A r := by
  subst h
  have hid : I = id := by
    exact (StrictMono.range_inj_of_wellFoundedLT hI strictMono_id).1
      (by rw [Set.range_id]; exact (Finite.injective_iff_surjective.1 hI.injective).range_eq)
  subst hid
  rfl

theorem qc_empty_minor (A : Type) [CommRing A] {r n : ℕ} (s : ℕ) (hs : s ≤ n) (I : Fin s → Fin r) (h : s = 0) :
    initMinor A I hs = 1 := by
  subst h
  unfold initMinor
  exact Matrix.det_isEmpty

theorem qcOm_zero (n : ℕ) : qcOm n 0 = 0 := by
  funext t
  simp [qcOm]

theorem qc_detDiv_bidet (A : Type) [CommRing A] (r : ℕ) : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r)
    (I : ∀ k, Fin (sz k) → Fin r), (∀ k, StrictMono (I k)) →
    ∃ (n : ℕ) (γ : Fin r → ℕ) (u₀ : MvPolynomial (Fin r × Fin r) A), (∀ t, shapeDeg sz t = γ t + n) ∧
      (∀ t : Fin r, t.val + 1 = r → γ t = 0) ∧ u₀ ∈ dualWeyl A r r γ ∧ bideterminant A sz hsz I = detY A r ^ n * u₀ := by
  intro K
  induction K with
  | zero =>
    intro sz hsz I _
    exact ⟨0, 0, 1, by intro t; rw [qc_shapeDeg_zero]; rfl, fun _ _ => rfl, one_mem_dualWeyl A r r,
      by rw [qc_bidet_zero, pow_zero, one_mul]⟩
  | succ K ih =>
    intro sz hsz I hI
    obtain ⟨n, γ, u₀, h1, h2, h3, h4⟩ :=
      ih (fun k => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ) (fun k => hI k.succ)
    by_cases hr : sz 0 = r
    · refine ⟨n + 1, γ, u₀, ?_, h2, h3, ?_⟩
      · intro t
        rw [qc_shapeDeg_succ, Pi.add_apply, h1 t]
        have : qcOm r (sz 0) t = 1 := by
          unfold qcOm
          rw [ite_eq_left (by rw [hr]; exact t.isLt)]
        omega
      · rw [qc_bidet_succ, h4, qc_full_minor A r _ (hsz 0) (I 0) (hI 0) hr]
        ring
    · refine ⟨n, qcOm r (sz 0) + γ, initMinor A (I 0) (hsz 0) * u₀, ?_, ?_,
        dualWeyl_mul A r r _ _ (qc_initMinor_mem A (I 0) (hsz 0)) h3, ?_⟩
      · intro t
        rw [qc_shapeDeg_succ, Pi.add_apply, Pi.add_apply, h1 t]
        omega
      · intro t ht
        rw [Pi.add_apply, h2 t ht, add_zero]
        unfold qcOm
        rw [ite_eq_right]
        have := hsz 0
        omega
      · rw [qc_bidet_succ, h4]
        ring

theorem detDivP : DetDivP := by
  intro A _ _ r Q β hr hβ u hu
  obtain ⟨b, ⟨-, hspan, -⟩, hb⟩ := sSBasis A r r (fun j => β j + Q)
  rw [← hspan] at hu
  refine Submodule.span_induction (p := fun u _ => ∃ u₀ ∈ dualWeyl A r r β, u = detY A r ^ Q * u₀) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨m, rfl⟩
    obtain ⟨-, -, K, sz, hsz, I, hsh, hI, hbm⟩ := hb m
    obtain ⟨n, γ, u₀, h1, h2, h3, h4⟩ := qc_detDiv_bidet A r K sz hsz I hI
    have h1' : ∀ t, β t + Q = γ t + n := by
      intro t
      have := h1 t
      rwa [hsh] at this
    have hl : γ ⟨r - 1, by omega⟩ = 0 := h2 _ (by show r - 1 + 1 = r; omega)
    have hn : Q ≤ n := by
      have := h1' ⟨r - 1, by omega⟩
      omega
    refine ⟨detY A r ^ (n - Q) * u₀, ?_, ?_⟩
    · have hd : detY A r ∈ dualWeyl A r r (qcOm r r) := by
        rw [← qc_full_minor A r r le_rfl id strictMono_id rfl]
        exact qc_initMinor_mem A id le_rfl
      have h5 := dualWeyl_mul A r r _ _ (qc_pow_mem A r r _ _ hd (n - Q)) h3
      have e : (n - Q) • qcOm r r + γ = β := by
        funext t
        have := h1' t
        simp only [Pi.add_apply, Pi.smul_apply, qcOm, t.isLt, ite_true, smul_eq_mul, mul_one]
        omega
      rwa [e] at h5
    · rw [hbm, h4, ← mul_assoc, ← pow_add]
      congr 2
      omega
  · exact ⟨0, Submodule.zero_mem _, by rw [mul_zero]⟩
  · rintro x y _ _ ⟨a, ha, rfl⟩ ⟨b', hb', rfl⟩
    exact ⟨a + b', Submodule.add_mem _ ha hb', by rw [mul_add]⟩
  · rintro c x _ ⟨a, ha, rfl⟩
    exact ⟨c • a, Submodule.smul_mem _ _ ha, by rw [mul_smul_comm]⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def genY (A : Type) [CommRing A] (r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) A) :=
  Matrix.of fun i j => X (i, j)

def TauP : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [CharZero O] [Field K] [Algebra O K], Function.Injective (algebraMap O K) →
    ∀ (r N e : ℕ) (α : Fin r → ℕ), 1 ≤ r → Antitone α → (∀ i, α i ≤ N) → (∀ i, e ≤ α i) → (∃ i, α i = e) →
    ∃ τ : MvPolynomial (Fin r × Fin r) K →ₗ[K] MvPolynomial (Fin r × Fin r) K,
      (∀ f' ∈ dualWeyl K r r (fun i => N - α i.rev), τ f' ∈ dualWeyl K r r (fun i => α i - e)) ∧
      (∀ f' ∈ intO O r (fun i => N - α i.rev), τ f' ∈ intO O r (fun i => α i - e)) ∧
      (∀ g ∈ intO O r (fun i => α i - e), ∃ f' ∈ intO O r (fun i => N - α i.rev), τ f' = g) ∧
      (∀ l : Matrix (Fin r) (Fin r) K, IsUnit l.det → ∀ f' ∈ dualWeyl K r r (fun i => N - α i.rev),
        rowAct K l.transpose (τ (rowAct K l f')) = l.det ^ (N - e) • τ f')

def SmithP : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 →
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] R.Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf),
        B (rowAct R.Kf g P) Q = B P (rowAct R.Kf g.transpose Q)) ∧
      (∀ P ∈ intO R.O (m + 1) ν, ∀ Q ∈ intO R.O (m + 1) ν, B P Q ∈ Set.range (algebraMap R.O R.Kf)) ∧
      ∃ (nb : ℕ) (x x' : Fin nb → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim (m + 1) (fun j => (ν j : ℤ)) ∧ (∀ b, ka b ≤ N0 (m + 1) * deF p (m + 1) (ν 0)) ∧
        (∀ b, x b ∈ intO R.O (m + 1) ν) ∧ (∀ a', x' a' ∈ intO R.O (m + 1) ν) ∧
        ∀ a' b, B (x b) (x' a') = if a' = b then (p : R.Kf) ^ ka b else 0

def BilinP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ)
    (B : MvPolynomial (Fin r × Fin r) K →ₗ[K] MvPolynomial (Fin r × Fin r) K →ₗ[K] K),
    ∃ L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K,
      ∀ f f', L (blockEmb K true f * blockEmb K false f') = B f f'

def DetFactsP : Prop :=
  ∀ (A : Type) [CommRing A] (r e : ℕ),
    detY A r ^ e ∈ dualWeyl A r r (fun _ => e) ∧
    ∀ l : Matrix (Fin r) (Fin r) A, rowAct A l (detY A r) = C l.det * detY A r

def NumP : Prop :=
  ∀ (p a c r ell : ℕ), 2 ≤ p → 1 ≤ r → ell ≤ c → c ≤ 8 * a → N0 r * deF p r ell ≤ ⌈kappaOneExponent p a (r + 1)⌉₊

end Formalism.MainNotions.flipOneThree.Pf

end
end
