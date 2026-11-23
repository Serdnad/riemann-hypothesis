module

public import Formalism.GradedWeylDivisibility.Bundle001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle005
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle003
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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

open scoped MonomialOrder

private theorem cmIdx_val_eq {r n : ℕ} (v : Fin r × Fin n) :
    ((cmIdx r n v : Fin (n * r)) : ℕ) = v.1.val + r * v.2.val := by
  first
  | rfl

private theorem col_lt_or_col_eq_row_lt_of_cmIdx_lt {r n : ℕ} {v w : Fin r × Fin n}
    (h : cmIdx r n v < cmIdx r n w) :
    v.2.val < w.2.val ∨ (v.2 = w.2 ∧ v.1 < w.1) := by
  have h0 : ((cmIdx r n v : Fin (n * r)) : ℕ) < ((cmIdx r n w : Fin (n * r)) : ℕ) := h
  rw [cmIdx_val_eq, cmIdx_val_eq] at h0
  have hv1 := v.1.isLt
  have hw1 := w.1.isLt
  rcases lt_trichotomy v.2.val w.2.val with h1 | h1 | h1
  · exact Or.inl h1
  · refine Or.inr ⟨Fin.ext h1, ?_⟩
    rw [h1] at h0
    show v.1.val < w.1.val
    omega
  · exfalso
    have hm : r * (w.2.val + 1) ≤ r * v.2.val := by
      first
      | exact Nat.mul_le_mul_left r h1
    rw [Nat.mul_add, Nat.mul_one] at hm
    first
    | omega

private theorem domCongr_cmIdx_apply_cmIdx {r n : ℕ} (x : Fin r × Fin n →₀ ℕ) (v : Fin r × Fin n) :
    (Finsupp.domCongr (cmIdx r n) x) (cmIdx r n v) = x v := by
  first
  | (simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]; done)

private theorem sum_single_castLE_apply' {r n s : ℕ} (τ : Fin s → Fin r) (hs : s ≤ n) (b : Fin r) (t : Fin n) :
    (∑ q : Fin s, Finsupp.single (τ q, Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
      if h : t.val < s then (if τ ⟨t.val, h⟩ = b then 1 else 0) else 0 := by
  rw [Finsupp.finsetSum_apply]
  by_cases h : t.val < s
  · rw [dite_eq_left h, Finset.sum_eq_single ⟨t.val, h⟩]
    · rw [Finsupp.single_apply]
      by_cases hb : τ ⟨t.val, h⟩ = b
      · have hp : (τ ⟨t.val, h⟩, Fin.castLE hs ⟨t.val, h⟩) = (b, t) := by
          first
          | exact Prod.ext hb (Fin.ext rfl)
        rw [if_pos hp, if_pos hb]
      · rw [if_neg, if_neg hb]
        intro he
        exact hb (congrArg Prod.fst he)
    · intro q _ hq
      rw [Finsupp.single_apply, if_neg]
      intro he
      apply hq
      apply Fin.ext
      have h2 : (Fin.castLE hs q).val = t.val := congrArg (fun x => (x.2 : ℕ)) he
      exact h2
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro q _
    rw [Finsupp.single_apply, if_neg]
    intro he
    apply h
    have h2 : (Fin.castLE hs q).val = t.val := congrArg (fun x => (x.2 : ℕ)) he
    have h3 := q.isLt
    have h4 : (Fin.castLE hs q).val = q.val := rfl
    omega

private theorem toLex_lt_of_eq_below_of_apply_lt {N : ℕ} (x y : Fin N →₀ ℕ) (i : Fin N)
    (h1 : ∀ j, j < i → x j = y j) (h2 : x i < y i) : toLex x < toLex y := by
  first
  | exact ⟨i, h1, h2⟩

private theorem colLex_lt_of_toLex_domCongr_cmIdx_lt {r n : ℕ} {c d : Fin r × Fin n →₀ ℕ}
    (h : toLex (Finsupp.domCongr (cmIdx r n) c) <
      toLex (Finsupp.domCongr (cmIdx r n) d)) :
    c ≺[colLex r n] d := h

theorem minorExponentLt : MinorExpLt := by
  intro r n s I hs hI σ hσ
  have hex : ∃ q, σ q ≠ q := by
    by_contra h
    push_neg at h
    apply hσ
    ext x
    first
    | (rw [h x]; rfl)
  obtain ⟨q0, hq0, hmin⟩ := (wellFounded_lt (α := Fin s)).has_min {q | σ q ≠ q} hex
  have hq0' : σ q0 ≠ q0 := hq0
  have hfix : ∀ q, q < q0 → σ q = q := fun q hq => by
    by_contra h
    exact hmin q h hq
  have hgt : q0 < σ q0 := by
    rcases lt_trichotomy (σ q0) q0 with h | h | h
    · exact absurd (σ.injective (hfix _ h)) h.ne
    · exact absurd h hq0'
    · exact h
  have hIlt : I q0 < I (σ q0) := hI hgt
  have hA : ∀ (b : Fin r) (t : Fin n),
      (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
        if h : t.val < s then (if I (σ ⟨t.val, h⟩) = b then 1 else 0) else 0 :=
    fun b t => sum_single_castLE_apply' (fun q => I (σ q)) hs b t
  have hB : ∀ (b : Fin r) (t : Fin n),
      (∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1 : Fin r × Fin n →₀ ℕ) (b, t) =
        if h : t.val < s then (if I ⟨t.val, h⟩ = b then 1 else 0) else 0 :=
    fun b t => sum_single_castLE_apply' I hs b t
  have hcq : (Fin.castLE hs q0).val = q0.val := rfl
  have ht0 : (Fin.castLE hs q0).val < s := q0.isLt
  have e1 : (⟨(Fin.castLE hs q0).val, ht0⟩ : Fin s) = q0 := Fin.ext rfl
  apply colLex_lt_of_toLex_domCongr_cmIdx_lt
  apply toLex_lt_of_eq_below_of_apply_lt _ _ (cmIdx r n (I q0, Fin.castLE hs q0))
  · intro j hj
    obtain ⟨v, rfl⟩ := (cmIdx r n).surjective j
    rw [domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx]
    obtain ⟨b, t⟩ := v
    rw [hA, hB]
    have hlt := col_lt_or_col_eq_row_lt_of_cmIdx_lt hj
    try dsimp only at hlt
    rcases hlt with hlt | ⟨rfl, hb⟩
    · have ht : t.val < s := by
        have := q0.isLt
        omega
      have hlt' : (⟨t.val, ht⟩ : Fin s) < q0 := by
        show t.val < q0.val
        omega
      rw [dite_eq_left ht, dite_eq_left ht, hfix _ hlt']
    · rw [dite_eq_left ht0, dite_eq_left ht0, e1, if_neg (lt_trans hb hIlt).ne', if_neg hb.ne']
  · rw [domCongr_cmIdx_apply_cmIdx, domCongr_cmIdx_apply_cmIdx, hA, hB]
    rw [dite_eq_left ht0, dite_eq_left ht0, e1, if_neg hIlt.ne', if_pos (rfl : I q0 = I q0)]
    exact Nat.zero_lt_one

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

section NonDomMain

variable {R : Type*} [CommRing R] {r n : ℕ}

def ndEv (R : Type*) [CommRing R] (r n : ℕ) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun o => o.elim 0 X

lemma ndEv_colAddGen (l j : Fin n) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEv R r n (colAddGen R l j g) = g := by
  have : (ndEv R r n).comp (colAddGen R (r := r) l j) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, colAddGen, aeval_X, AlgHom.id_apply]
    split_ifs <;> simp [ndEv]
  exact congrArg (fun φ => φ g) this

lemma ndEv_pderiv_colAddGen (l j : Fin n) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEv R r n (pderiv none (colAddGen R l j g)) = ndE R r n l j g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [colAddGen, derivation_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul,
      map_mul, map_mul, hp, ndEv_colAddGen, ndEv_colAddGen, smul_eq_mul, smul_eq_mul]
    congr 1
    simp only [ndE, mkDerivation_X, colAddGen, aeval_X]
    split_ifs <;> simp [ndEv, Derivation.leibniz, pderiv_X]

lemma nd_pderiv_none_rename (g : MvPolynomial (Fin r × Fin n) R) :
    pderiv none (rename (some : Fin r × Fin n → Option (Fin r × Fin n)) g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, add_zero]
  | mul_X p v hp => simp [Derivation.leibniz, hp, pderiv_X]

lemma ndE_eq_zero {l j : Fin n} {f : MvPolynomial (Fin r × Fin n) R}
    (h : colAddGen R l j f = rename some f) : ndE R r n l j f = 0 := by
  rw [← ndEv_pderiv_colAddGen, h, nd_pderiv_none_rename, map_zero]

lemma nd_iter_Eul_l {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {c : R}
    (hf : ndEul R r n l f = c • f) (k : ℕ) :
    ndEul R r n l ((ndF R r n l j)^[k] f) = (c - k) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply', nd_comm_EulF_l hlj, ih, Derivation.map_smul, Nat.cast_succ,
      show c - ((k : R) + 1) = (c - k) - 1 by ring, sub_smul (c - k) 1, one_smul]

lemma nd_iter_Eul_j {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {c : R}
    (hf : ndEul R r n j f = c • f) (k : ℕ) :
    ndEul R r n j ((ndF R r n l j)^[k] f) = (c + k) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply', nd_comm_EulF_j hlj, ih, Derivation.map_smul, Nat.cast_succ,
      show c + ((k : R) + 1) = (c + k) + 1 by ring, add_smul (c + k) 1, one_smul]

lemma nd_iter_E {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {cl cj : R}
    (hl : ndEul R r n l f = cl • f) (hj : ndEul R r n j f = cj • f) (hE : ndE R r n l j f = 0)
    (k : ℕ) :
    ndE R r n l j ((ndF R r n l j)^[k + 1] f) =
      (((k : R) + 1) * (cl - cj - k)) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero =>
    rw [zero_add, Function.iterate_one, nd_comm_EF hlj, hE, map_zero, hl, hj]
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_add, one_mul, sub_zero]
    rw [sub_smul]
  | succ k ih =>
    rw [Function.iterate_succ_apply' (ndF R r n l j) (k + 1) f, nd_comm_EF hlj, ih,
      Derivation.map_smul, nd_iter_Eul_l hlj hl, nd_iter_Eul_j hlj hj,
      ← Function.iterate_succ_apply' (ndF R r n l j) k f, ← sub_smul, ← add_smul]
    congr 1
    push_cast; ring

theorem nd_main [IsDomain R] [CharZero R] (ν : Fin n → ℕ) {l j : Fin n} (hlj : l < j)
    (hν : ν l < ν j) (f : MvPolynomial (Fin r × Fin n) R)
    (hhom : IsWeightedHomogeneous (colW r n) f ν) (hinv : colAddGen R l j f = rename some f) :
    f = 0 := by
  have hne : l ≠ j := ne_of_lt hlj
  have hl := ndEul_homog (R := R) hhom l
  have hj := ndEul_homog (R := R) hhom j
  have hE := ndE_eq_zero hinv
  set G : ℕ → MvPolynomial (Fin r × Fin n) R := fun k => (ndF R r n l j)^[k] f with hG

  have hN : G (ν l + 1) = 0 := by
    apply ndEul_neg_eq_zero l
    rw [hG]; dsimp only
    rw [nd_iter_Eul_l hne hl, Nat.cast_succ, show (ν l : R) - ((ν l : R) + 1) = -1 by ring,
      neg_one_smul]

  have hstep : ∀ k, G (k + 1) = 0 → G k = 0 := by
    intro k hk
    have h1 := nd_iter_E hne hl hj hE k
    rw [show (ndF R r n l j)^[k + 1] f = G (k + 1) from rfl, hk, map_zero] at h1
    have hc : (((k : R) + 1) * ((ν l : R) - (ν j : R) - k)) ≠ 0 := by
      refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
      have : (ν l : R) - (ν j : R) - k = (((ν l : ℤ) - ν j - k : ℤ) : R) := by push_cast; ring
      rw [this, Int.cast_ne_zero]
      omega
    exact (smul_eq_zero.1 h1.symm).resolve_left hc
  have hdown : ∀ d k, G (k + d) = 0 → G k = 0 := by
    intro d
    induction d with
    | zero => intro k hk; simpa using hk
    | succ d ih =>
      intro k hk
      exact hstep k (ih (k + 1) (by rw [show k + 1 + d = k + (d + 1) by omega]; exact hk))
  have := hdown (ν l + 1) 0 (by simpa using hN)
  simpa [hG] using this

theorem dualWeylModuleNonDominant : DualWeylNonDom := by
  intro R _ _ _ r n ν ⟨l, j, hlj, hν⟩
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [dualWeyl, Submodule.mem_inf, mem_weightedHomogeneousSubmodule] at hf
  obtain ⟨hhom, hinv⟩ := hf
  have h1 := Submodule.mem_iInf _ |>.1 hinv l
  have h2 := Submodule.mem_iInf _ |>.1 h1 j
  have h3 := Submodule.mem_iInf _ |>.1 h2 hlj
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply] at h3
  exact nd_main ν hlj hν f hhom h3

end NonDomMain

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem sum_initW_eq_shapeDeg {n K : ℕ} (sz : Fin K → ℕ) :
    (∑ k : Fin K, initW n (sz k)) = shapeDeg sz := by
  funext t
  rw [Finset.sum_apply]
  simp only [initW, shapeDeg, Finset.card_filter]

theorem bideterminantMem : BideterminantMem := by
  intro R _ r n K sz hsz I
  exact dualWeyl_of_eq
    (dualWeyl_prod Finset.univ (fun k => initW n (sz k))
      (fun k => initMinor R (I k) (hsz k))
      (fun k _ => initMinor_mem (I k) (hsz k)))
    (sum_initW_eq_shapeDeg sz)

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma LFocks_subAdj {σ : Type*} [Fintype σ] [DecidableEq σ] (U : Matrix σ σ ℂ)
    (f g : MvPolynomial σ ℂ) :
    fockF (sub U f) g = fockF f (sub U.conjTranspose g) := by
  induction f using MvPolynomial.induction_on generalizing g
  · rename_i a
    rw [LFocks_sub_C, LFocks_C_left, LFocks_C_left,
      LFocks_constantCoeff_sub]
  · rename_i p q hp hq
    rw [map_add (f := _), Formalism.REAL.fischerInner_add_left, Formalism.REAL.fischerInner_add_left, hp, hq]
  · rename_i p i hp
    rw [map_mul, LFocks_sub_X, mul_comm p (X i), Formalism.REAL.fischerInner_X_mul_left i p,
      LFocks_pderiv_sub, Formalism.REAL.fischerInner_sum_right, Finset.mul_sum, Formalism.REAL.fischerInner_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LFocks_C_mul_right, ← hp, Matrix.conjTranspose_apply, star_star,
      mul_comm (sub U p), mul_assoc, LFocks_C_mul_left,
      Formalism.REAL.fischerInner_X_mul_left]

theorem fischerInnerSubstitutionAdjoint : FockSubAdj :=
  fun _ _ _ U f g => LFocks_subAdj U f g

end Formalism.GradedWeylDivisibility
end
end
