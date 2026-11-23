module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle003
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
public import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def initW (n s : ℕ) : Fin n → ℕ := fun t => if t.val < s then 1 else 0

theorem sum_single_castLE {n s : ℕ} (hs : s ≤ n) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hs q) 1 : Fin n → ℕ)) = initW n s := by
  funext t
  rw [Finset.sum_apply]
  simp only [initW]
  by_cases h : t.val < s
  · rw [if_pos h, Finset.sum_eq_single ⟨t.val, h⟩]
    · have e : Fin.castLE hs ⟨t.val, h⟩ = t := Fin.ext rfl
      rw [e, Pi.single_eq_same]
    · intro q _ hq
      rw [Pi.single_apply, if_neg]
      intro htq
      apply hq
      subst htq
      exact Fin.ext rfl
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Pi.single_apply, if_neg]
    intro htq
    apply h
    subst htq
    exact q.isLt

theorem initMinor_isWeightedHomogeneous {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) :
    IsWeightedHomogeneous (colW r n) (initMinor R I hs) (initW n s) := by
  rw [← mem_weightedHomogeneousSubmodule]
  unfold initMinor
  rw [Matrix.det_apply]
  refine _root_.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule, ← sum_single_castLE hs]
  apply IsWeightedHomogeneous.prod
  intro q _
  exact isWeightedHomogeneous_X (R := R) (colW r n) (I (σ q), Fin.castLE hs q)

theorem algHom_det_of {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) {s : ℕ} (M : Fin s → Fin s → A) :
    φ (Matrix.of M).det = (Matrix.of fun p q => φ (M p q)).det := by
  rw [AlgHom.map_det]
  rfl

theorem colAddGen_X {R : Type*} [CommRing R] {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) :
    colAddGen R l j (X v) =
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) := by
  simp only [colAddGen, aeval_X]

theorem initMinor_invariant {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) (l j : Fin n) (hlj : l < j) :
    colAddGen R l j (initMinor R I hs) = rename some (initMinor R I hs) := by
  unfold initMinor
  rw [algHom_det_of, algHom_det_of]
  simp only [colAddGen_X, rename_X]
  by_cases hj : j.val < s
  · have hl : l.val < s := Nat.lt_trans (show l.val < j.val from hlj) hj
    have hjl : (⟨j.val, hj⟩ : Fin s) ≠ ⟨l.val, hl⟩ := by
      intro h
      exact hlj.ne' (Fin.ext (Fin.mk.inj_iff.mp h))
    rw [← Matrix.det_updateCol_add_smul_self
      (Matrix.of fun p q : Fin s =>
        (X (some (I p, Fin.castLE hs q)) : MvPolynomial (Option (Fin r × Fin n)) R)) hjl (X none)]
    congr 1
    ext p q
    simp only [Matrix.updateCol_apply, Matrix.of_apply]
    by_cases hq : q = ⟨j.val, hj⟩
    · subst hq
      have e1 : Fin.castLE hs ⟨j.val, hj⟩ = j := Fin.ext rfl
      have e2 : Fin.castLE hs ⟨l.val, hl⟩ = l := Fin.ext rfl
      rw [e1, e2]
      simp
    · have hne : Fin.castLE hs q ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        exact hq (Fin.ext hv)
      rw [if_neg hne, if_neg hq]
  · congr 1
    ext p q
    simp only [Matrix.of_apply]
    have hne : Fin.castLE hs q ≠ j := by
      intro h
      apply hj
      rw [← h]
      exact q.isLt
    rw [if_neg hne]

theorem initMinor_mem {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs ∈ dualWeyl R r n (initW n s) := by
  unfold dualWeyl
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact initMinor_isWeightedHomogeneous I hs
  · simp only [Submodule.mem_iInf]
    intro l j hlj
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact initMinor_invariant I hs l j hlj

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem rowDiv_add (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  simp only [rowDiv, map_add (f := _), Polynomial.coeff_add]

theorem rowDiv_smul (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (c : R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (c • f) = c • rowDiv R a b k f := by
  simp only [rowDiv, map_smul, Polynomial.coeff_smul]

def rowDivL (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) :
    MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R where
  toFun := rowDiv R a b k
  map_add' := rowDiv_add R a b k
  map_smul' := rowDiv_smul R a b k

@[simp] theorem rowDivL_apply (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) : rowDivL R a b k f = rowDiv R a b k f := rfl

theorem applyWord_nil (R : Type*) [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R [] f = f := rfl

theorem applyWord_cons (R : Type*) [CommRing R] {r n : ℕ} (x : Fin r × Fin r × ℕ)
    (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (x :: w) f = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) := rfl

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

set_option linter.unusedSimpArgs false

section NonDom

variable {R : Type*} [CommRing R] {r n : ℕ}

def ndEul (R : Type*) [CommRing R] (r n : ℕ) (s : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => (colW r n v s) • X v

def ndE (R : Type*) [CommRing R] (r n : ℕ) (l j : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.2 = j then X (v.1, l) else 0

def ndF (R : Type*) [CommRing R] (r n : ℕ) (l j : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.2 = l then X (v.1, j) else 0

lemma nd_weight_apply (s : Fin n) (m : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (fun v => colW r n v s) m = Finsupp.weight (colW r n) m s := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]

lemma ndEul_coeff (s : Fin n) (g : MvPolynomial (Fin r × Fin n) R) (m : Fin r × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (ndEul R r n s g) m =
      (Finsupp.weight (fun v => colW r n v s) m : R) * AddMonoidAlgebra.coeff g m := by
  classical
  induction g using MvPolynomial.induction_on generalizing m with
  | C a =>
    rw [derivation_C, AddMonoidAlgebra.coeff_zero, coeff_C]
    split_ifs with h
    · subst h; simp
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]
  | mul_X p v hp =>
    have hX : ndEul R r n s (X v) = colW r n v s • X v := mkDerivation_X _ _ _
    rw [Derivation.leibniz, hX, MvPolynomial.coeff_add, smul_eq_mul, smul_eq_mul,
      mul_smul_comm, MvPolynomial.coeff_smul, coeff_mul_X', coeff_X_mul']
    split_ifs with h
    · rw [hp]
      have hle : Finsupp.single v 1 ≤ m := by
        rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
      have hm : m = (m - Finsupp.single v 1) + Finsupp.single v 1 := (tsub_add_cancel_of_le hle).symm
      have hw : Finsupp.weight (fun v => colW r n v s) m =
          Finsupp.weight (fun v => colW r n v s) (m - Finsupp.single v 1) + colW r n v s := by
        conv_lhs => rw [hm]
        rw [map_add (f := _), Finsupp.weight_single, one_smul]
      rw [hw, nsmul_eq_mul]; push_cast; ring
    · simp

lemma ndEul_homog {g : MvPolynomial (Fin r × Fin n) R} {μ : Fin n → ℕ}
    (hg : IsWeightedHomogeneous (colW r n) g μ) (s : Fin n) :
    ndEul R r n s g = (μ s : R) • g := by
  ext m
  rw [ndEul_coeff, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases h : AddMonoidAlgebra.coeff g m = 0
  · simp [h]
  · rw [nd_weight_apply, hg h]

lemma ndEul_neg_eq_zero [IsDomain R] [CharZero R] {g : MvPolynomial (Fin r × Fin n) R}
    (s : Fin n) (h : ndEul R r n s g = -g) : g = 0 := by
  ext m
  have h1 := congrArg (AddMonoidAlgebra.coeff · m) h
  rw [ndEul_coeff, MvPolynomial.coeff_neg] at h1
  have h2 : ((Finsupp.weight (fun v => colW r n v s) m : R) + 1) * AddMonoidAlgebra.coeff g m = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (Nat.cast_add_one_ne_zero _)
  · simpa using h3

lemma nd_comm_EF {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndE R r n l j (ndF R r n l j g) =
      ndF R r n l j (ndE R r n l j g) + (ndEul R r n l g - ndEul R r n j g) := by
  have key : ⁅ndE R r n l j, ndF R r n l j⁆ = ndEul R r n l - ndEul R r n j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply, Derivation.sub_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply, Derivation.sub_apply] at this
  rw [← this]; abel

lemma nd_comm_EulF_l {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEul R r n l (ndF R r n l j g) = ndF R r n l j (ndEul R r n l g) - ndF R r n l j g := by
  have key : ⁅ndEul R r n l, ndF R r n l j⁆ = -ndF R r n l j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply, Derivation.neg_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply, Derivation.neg_apply] at this
  rw [sub_eq_iff_eq_add.1 this]; abel

lemma nd_comm_EulF_j {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEul R r n j (ndF R r n l j g) = ndF R r n l j (ndEul R r n j g) + ndF R r n l j g := by
  have key : ⁅ndEul R r n j, ndF R r n l j⁆ = ndF R r n l j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply] at this
  rw [sub_eq_iff_eq_add.1 this]; abel

end NonDom

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

open Formalism.REAL (fockF)

lemma ldiag_rowAct_diag_eq {r n : ℕ} (t : Fin r → ℂ) :
    rowAct ℂ (n := n) (Matrix.diagonal t) = aeval fun v : Fin r × Fin n => C (t v.1) * X v := by
  unfold rowAct
  congr 1
  funext v
  rw [Finset.sum_eq_single v.1]
  · simp [Matrix.diagonal_apply_eq]
  · intro b _ hb
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma ldiag_prod_rowDeg {r n : ℕ} (t : Fin r → ℂ) (u : Fin r × Fin n →₀ ℕ) :
    (u.prod fun v k => t v.1 ^ k) = ∏ a : Fin r, t a ^ rowDeg u a := by
  have h1 : (u.prod fun v k => t v.1 ^ k) = ∏ v : Fin r × Fin n, t v.1 ^ u v := by
    exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  rw [h1]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  try dsimp only
  rw [Finset.prod_pow_eq_pow_sum, rowDeg]

lemma ldiag_aeval_monomial {r n : ℕ} (t : Fin r → ℂ) (u : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    aeval (fun v : Fin r × Fin n => C (t v.1) * X v) (monomial u c) =
      monomial u (c * ∏ a : Fin r, t a ^ rowDeg u a) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, ← ldiag_prod_rowDeg,
    MvPolynomial.algebraMap_eq, MvPolynomial.C_mul]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  ring

lemma ldiag_coeff_rowAct_diag {r n : ℕ} (t : Fin r → ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (m : Fin r × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (rowAct ℂ (Matrix.diagonal t) f) m = AddMonoidAlgebra.coeff f m * ∏ a : Fin r, t a ^ rowDeg m a := by
  rw [ldiag_rowAct_diag_eq]
  induction f using MvPolynomial.induction_on'
  next u c =>
    rw [ldiag_aeval_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · rw [zero_mul]
  next p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, add_mul]

lemma ldiag_term (z : ℂ) (w : ℝ) (N : ℕ) :
    z * (w : ℂ) * star (z * (w : ℂ)) * (N : ℂ) = ((Complex.normSq z * w ^ 2 * N : ℝ) : ℂ) := by
  have hs : ∀ x : ℂ, star x = (starRingEnd ℂ) x := fun _ => rfl
  apply Complex.ext
  all_goals
    simp only [hs, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring

lemma ldiag_term0 (z : ℂ) (N : ℕ) :
    z * star z * (N : ℂ) = ((Complex.normSq z * N : ℝ) : ℂ) := by
  have hs : ∀ x : ℂ, star x = (starRingEnd ℂ) x := fun _ => rfl
  apply Complex.ext
  all_goals
    simp only [hs, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring

private theorem mul_sq_mul_le_sq_mul_mul_of_le {c N p q : ℝ} (hc : 0 ≤ c) (hN : 0 ≤ N) (hp : 0 ≤ p)
    (hpq : p ≤ q) : c * p ^ 2 * N ≤ q ^ 2 * (c * N) := by
  have h1 : p * p ≤ q * q := mul_self_le_mul_self hp hpq
  have h2 : 0 ≤ c * N := mul_nonneg hc hN
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  calc c * p ^ 2 * N = (p * p) * (c * N) := by ring
    _ ≤ (q * q) * (c * N) := h3
    _ = q ^ 2 * (c * N) := by ring

theorem fockDiagBound_of (h : DomPow) : FockDiagBound := by
  unfold DomPow at h
  unfold FockDiagBound
  intro r n t lam ht0 ht f hdom hsum
  have hcoeff : ∀ m, AddMonoidAlgebra.coeff (rowAct ℂ (Matrix.diagonal fun a => (t a : ℂ)) f) m =
      AddMonoidAlgebra.coeff f m * ((∏ a : Fin r, t a ^ rowDeg m a : ℝ) : ℂ) := by
    intro m
    simp only [ldiag_coeff_rowAct_diag, Complex.ofReal_prod, Complex.ofReal_pow]
  have hsupp : (rowAct ℂ (Matrix.diagonal fun a => (t a : ℂ)) f).support ⊆ f.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [hcoeff, h0, zero_mul])
  have hq : ∏ a : Fin r, t a ^ (2 * lam a) = (∏ a : Fin r, t a ^ lam a) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← pow_mul, Nat.mul_comm]
  rw [Formalism.REAL.fischerInner_eq_sum_of_subset _ _ _ hsupp,
    Formalism.REAL.fischerInner_eq_sum_of_subset f f f.support (Finset.Subset.refl _)]
  simp only [hcoeff, ldiag_term]
  simp only [ldiag_term0, Complex.re_sum, Complex.ofReal_re]
  rw [hq, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  have hP0 : 0 ≤ ∏ a : Fin r, t a ^ rowDeg m a :=
    Finset.prod_nonneg fun a _ => pow_nonneg (ht0 a) _
  have hPle := h r t (rowDeg m) lam ht0 ht (hdom m hm) (hsum m hm)
  exact mul_sq_mul_le_sq_mul_mul_of_le (Complex.normSq_nonneg _) (Nat.cast_nonneg _) hP0 hPle

end Formalism.GradedWeylDivisibility
end
end
