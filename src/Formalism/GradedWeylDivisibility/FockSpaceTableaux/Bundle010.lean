module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle003
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleRowActionStable : DualWeylRowStable := by
  intro R _ r n ν g f hf
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  obtain ⟨hw, hc⟩ := hf
  refine ⟨isWH_algHom (rowAct R g) (colW r n) (colW r n)
    (rowAct_X_isWH g) hw, ?_⟩
  intro l j hlj
  rw [colAddGen_rowAct, rename_rowAct, hc l j hlj]

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem bideterminantDominance : BideterminantDominance := by
  classical
  intro R _ r n K sz hsz I m hm
  have hm' : m ∈ (∏ k : Fin K, initMinor R (I k) (hsz k)).support := hm
  refine ⟨fun k => ?_, ?_⟩
  · have h := support_prod_le_of_additive (rowPart k) (rowPart_zero k)
      (rowPart_add k) Finset.univ (fun k' => initMinor R (I k') (hsz k'))
      (fun k' => min k (sz k'))
      (fun k' _ m' hm'' => (initMinor_support (I k') (hsz k') m' hm'').1 k)
      m hm'
    exact h.trans_eq (sum_min_eq_shapeDeg sz hsz k)
  · have h := support_prod_eq_of_additive rowTot rowTot_zero
      rowTot_add Finset.univ (fun k' => initMinor R (I k') (hsz k')) sz
      (fun k' _ m' hm'' => (initMinor_support (I k') (hsz k') m' hm'').2)
      m hm'
    have h2 := sum_min_eq_shapeDeg sz hsz n
    have h3 : ∑ t : Fin n with t.val < n, shapeDeg sz t =
        ∑ t : Fin n, shapeDeg sz t :=
      Finset.sum_congr (Finset.filter_true_of_mem fun t _ => t.isLt) fun _ _ => rfl
    have h4 : ∑ k' : Fin K, min n (sz k') = ∑ k' : Fin K, sz k' :=
      Finset.sum_congr rfl fun k' _ => min_eq_right (hsz k')
    exact h.trans (h4.symm.trans (h2.trans h3))

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleSaturated : DualWeylSat := by
  intro R _ _ r n ν c f hc hcf
  rw [lsat_mem_dualWeyl] at hcf ⊢
  obtain ⟨hwh, hcol⟩ := hcf
  refine ⟨fun {d} hd => hwh ?_, fun l j hlj => ?_⟩
  · rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    exact mul_ne_zero hc hd
  · have h := hcol l j hlj
    rw [smul_eq_C_mul, map_mul, map_mul, algHom_C, algHom_C] at h
    exact mul_left_cancel₀ (by simpa using hc) h

end Formalism.GradedWeylDivisibility
end
end

section

namespace Formalism.GradedWeylDivisibility

open MvPolynomial

def hwrowExtNu {n : ℕ} (ν : Fin n → ℕ) (i : ℕ) : ℕ := if h : i < n then ν ⟨i, h⟩ else 0

theorem extNu_anti {n : ℕ} {ν : Fin n → ℕ} (hν : Antitone ν) {i j : ℕ} (hij : i ≤ j) :
    hwrowExtNu ν j ≤ hwrowExtNu ν i := by
  unfold hwrowExtNu
  by_cases hj : j < n
  · have hi : i < n := lt_of_le_of_lt hij hj
    rw [dite_eq_left hj, dite_eq_left hi]
    first
    | exact hν (Fin.mk_le_mk.2 hij)
    | exact hν (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  · rw [dite_eq_right hj]
    exact Nat.zero_le _

theorem sum_range_tsub_from (g : ℕ → ℕ) (hg : ∀ i j, i ≤ j → g j ≤ g i) (a : ℕ) :
    ∀ m, (∑ i ∈ Finset.range m, if a ≤ i then g i - g (i + 1) else 0) =
      if a < m then g a - g m else 0
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, sum_range_tsub_from g hg a m]
    have h1 := hg m (m + 1) (by omega)
    rcases lt_trichotomy a m with ham | ham | ham
    · have h2 := hg a m ham.le
      rw [if_pos ham, if_pos ham.le, if_pos (by omega)]
      omega
    · subst ham
      rw [if_neg (lt_irrefl _), if_pos le_rfl, if_pos (by omega)]
      omega
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem pow_nsmul' {σ M S : Type*} [CommSemiring S] [AddCommMonoid M]
    {w : σ → M} {φ : MvPolynomial σ S} {m : M} (hφ : IsWeightedHomogeneous w φ m) :
    ∀ k : ℕ, IsWeightedHomogeneous w (φ ^ k) (k • m) := by
  intro k
  induction k with
  | zero =>
    classical
    rw [pow_zero, zero_smul]
    intro d hd
    have hd0 : d = 0 := by
      by_contra h
      exact hd (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)])
    rw [hd0, map_zero]
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul hφ

theorem highestWeightVectorRowWeight : HWRowWeight := by
  intro R inst r n hn ν hν
  have hg : ∀ i j, i ≤ j → hwrowExtNu ν j ≤ hwrowExtNu ν i :=
    fun i j hij => extNu_anti hν hij
  have key : (rowNu (r := r) ν) =
      ∑ s : Fin n, (ν s - nuNext ν s) • (fun b : Fin r => if b.val < s.val + 1 then (1 : ℕ) else 0) := by
    funext a
    have hterm : ∀ s : Fin n, (ν s - nuNext ν s) * (if a.val < s.val + 1 then (1 : ℕ) else 0) =
        (fun i : ℕ => if a.val ≤ i then hwrowExtNu ν i - hwrowExtNu ν (i + 1) else 0) s.val := by
      intro s
      have hs : hwrowExtNu ν s.val = ν s := by
        first
        | simp [hwrowExtNu, s.isLt]
        | (unfold hwrowExtNu; rw [dite_eq_left s.isLt])
      have hs' : nuNext ν s = hwrowExtNu ν (s.val + 1) := rfl
      rw [hs', ← hs]
      by_cases h : a.val ≤ s.val
      · have h' : a.val < s.val + 1 := by omega
        simp [h, h']
      · have h' : ¬ a.val < s.val + 1 := by omega
        simp [h, h']
    have hsum : (∑ s : Fin n, (ν s - nuNext ν s) •
        (fun b : Fin r => if b.val < s.val + 1 then (1 : ℕ) else 0)) a =
        if a.val < n then hwrowExtNu ν a.val - hwrowExtNu ν n else 0 := by
      first
      | rw [Finset.sum_apply]
      | simp only [Finset.sum_apply]
      refine Eq.trans ?_ ((Fin.sum_univ_eq_sum_range
        (fun i : ℕ => if a.val ≤ i then hwrowExtNu ν i - hwrowExtNu ν (i + 1) else 0) n).trans
        (sum_range_tsub_from (hwrowExtNu ν) hg a.val n))
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      exact hterm s
    refine Eq.trans ?_ hsum.symm
    by_cases ha : a.val < n
    · have h0 : hwrowExtNu ν n = 0 := by
        first
        | simp [hwrowExtNu]
        | (unfold hwrowExtNu; rw [dite_eq_right (lt_irrefl n)])
      rw [if_pos ha, h0, Nat.sub_zero]
      all_goals first | rfl | simp [rowNu, hwrowExtNu, ha]
    · rw [if_neg ha]
      simp [rowNu, ha]
  rw [key]
  unfold hw
  apply IsWeightedHomogeneous.prod
  intro s _
  exact pow_nsmul'
    (lpMinor_rowHom R (s.val + 1)
      (Nat.succ_le_of_lt (lt_of_lt_of_le s.isLt hn)) (Nat.succ_le_of_lt s.isLt)) _

end Formalism.GradedWeylDivisibility
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lsat_spec_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp (colAddGen R l j) =
      colAdd R l j c := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]
  split_ifs <;> simp

theorem lsat_spec_rename {R : Type*} [CommRing R] {r n : ℕ} (c : R) :
    (aeval (fun o : Option (Fin r × Fin n) => Option.elim o (C c) X)).comp
      (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [rename_X]

theorem lsat_eval_colAddGen {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n)
    (x : Option (Fin r × Fin n) → R) :
    (aeval x).comp (colAddGen R l j) = (aeval (x ∘ some)).comp (colAdd R l j (x none)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, colAdd, aeval_X]
  split_ifs <;> simp

theorem dualWeylModuleMemIff : DualWeylPoint := by
  intro R _ _ _ r n ν f
  rw [lsat_mem_dualWeyl]
  refine and_congr_right fun _ => forall₂_congr fun l j => imp_congr_right fun _ => ?_
  constructor
  · intro h c
    let ψ : Option (Fin r × Fin n) → MvPolynomial (Fin r × Fin n) R :=
      fun o => Option.elim o (C c) X
    have h1 : aeval ψ (colAddGen R l j f) = aeval ψ (rename some f) := by rw [h]
    have e1 : aeval ψ (colAddGen R l j f) = colAdd R l j c f := by
      rw [← AlgHom.comp_apply, lsat_spec_colAddGen]
    have e2 : aeval ψ (rename some f) = f := by
      rw [← AlgHom.comp_apply, lsat_spec_rename, AlgHom.id_apply]
    rw [← e1, h1, e2]
  · intro h
    apply MvPolynomial.funext
    intro x
    have e := congrArg (fun φ => φ f) (lsat_eval_colAddGen (R := R) l j x)
    simp only [AlgHom.comp_apply, h] at e
    change aeval x (colAddGen R l j f) = aeval x (rename some f)
    rw [e, aeval_rename]

end Formalism.GradedWeylDivisibility
end
end
