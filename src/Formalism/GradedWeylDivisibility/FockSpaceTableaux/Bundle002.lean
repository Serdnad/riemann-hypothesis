module

public import Formalism.GradedWeylDivisibility.StatementA
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma ldrow_rowAct_diag_eq {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R) :
    rowAct R (n := n) (Matrix.diagonal t) = aeval fun v : Fin k × Fin n => C (t v.1) * X v := by
  unfold rowAct
  congr 1
  funext v
  simp [Matrix.diagonal_apply, apply_ite C, ite_mul]

lemma ldrow_prod_rowDeg {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R) (u : Fin k × Fin n →₀ ℕ) :
    (u.prod fun v e => t v.1 ^ e) = ∏ a : Fin k, t a ^ rowDeg u a := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun v => pow_zero _), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  show ∏ y, t a ^ u (a, y) = _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

lemma ldrow_aeval_monomial {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R)
    (u : Fin k × Fin n →₀ ℕ) (c : R) :
    aeval (fun v : Fin k × Fin n => C (t v.1) * X v) (monomial u c) =
      monomial u (c * ∏ a : Fin k, t a ^ rowDeg u a) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (t v.1) : MvPolynomial (Fin k × Fin n) R) ^ e) =
      C (∏ a : Fin k, t a ^ rowDeg u a) := by
    rw [← ldrow_prod_rowDeg]
    simp only [Finsupp.prod, map_prod, map_pow]
  rw [hC, algebraMap_eq, map_mul]
  ring

lemma ldrow_coeff_rowAct_diag {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R)
    (f : MvPolynomial (Fin k × Fin n) R) (m : Fin k × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (rowAct R (Matrix.diagonal t) f) m = AddMonoidAlgebra.coeff f m * ∏ a : Fin k, t a ^ rowDeg m a := by
  rw [ldrow_rowAct_diag_eq]
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [ldrow_aeval_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, add_mul]

lemma ldrow_weight_rowW {k n : ℕ} (m : Fin k × Fin n →₀ ℕ) (a : Fin k) :
    Finsupp.weight (rowW k n) m a = rowDeg m a := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • rowW k n i) (fun i => zero_smul ℕ _),
    Finset.sum_apply,
    Fintype.sum_prod_type]
  unfold rowDeg
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    simp [rowW]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro s _
    simp [rowW, Pi.single_apply, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

section General

variable {R : Type*} [CommRing R] {σ τ M : Type*} [AddCommMonoid M]

theorem isWH_algHom_monomial (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (w : σ → M) (w' : τ → M)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (m : σ →₀ ℕ) (c : R) :
    IsWeightedHomogeneous w' (φ (monomial m c)) (Finsupp.weight w m) := by
  have hC : φ (C c) = C c := by
    rw [← MvPolynomial.algebraMap_eq]
    exact φ.commutes c
  rw [monomial_eq, map_mul, hC, Finsupp.prod, map_prod]
  simp only [map_pow]
  have h := (isWeightedHomogeneous_C w' c).mul
    (IsWeightedHomogeneous.prod m.support (fun v => φ (X v) ^ m v) (fun v => m v • w v)
      (fun v _ => (hφ v).pow (m v)))
  rw [zero_add] at h
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact h

theorem isWH_algHom (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (w : σ → M) (w' : τ → M)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) {f : MvPolynomial σ R} {d : M}
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w' (φ f) d := by

  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  have h := isWH_algHom_monomial φ w w' hφ s (AddMonoidAlgebra.coeff f s)
  rwa [hf (mem_support_iff.mp hs)] at h

private theorem weightedHomogeneousComponent_self_of_isWH {w : σ → M} {p : MvPolynomial σ R} {m : M}
    (hp : IsWeightedHomogeneous w p m) : weightedHomogeneousComponent w m p = p := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with h
  · rfl
  · by_contra hd
    exact h (hp (Ne.symm hd))

private theorem weightedHomogeneousComponent_eq_zero_of_isWH_ne {w : σ → M} {p : MvPolynomial σ R} {m μ : M}
    (hne : m ≠ μ) (hp : IsWeightedHomogeneous w p m) : weightedHomogeneousComponent w μ p = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  split_ifs with h
  · by_contra hd
    exact hne ((hp hd).symm.trans h)
  · rfl

theorem algHom_weightedHomogeneousComponent (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (w : σ → M) (w' : τ → M) (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (μ : M)
    (f : MvPolynomial σ R) :
    φ (weightedHomogeneousComponent w μ f) = weightedHomogeneousComponent w' μ (φ f) := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  simp only [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs := isWH_algHom_monomial φ w w' hφ s (AddMonoidAlgebra.coeff f s)
  have hm : IsWeightedHomogeneous w (monomial s (AddMonoidAlgebra.coeff f s)) (Finsupp.weight w s) :=
    isWeightedHomogeneous_monomial w s (AddMonoidAlgebra.coeff f s) rfl
  by_cases h : Finsupp.weight w s = μ
  · subst h
    rw [weightedHomogeneousComponent_self_of_isWH hm, weightedHomogeneousComponent_self_of_isWH hs]
  · rw [weightedHomogeneousComponent_eq_zero_of_isWH_ne h hm, weightedHomogeneousComponent_eq_zero_of_isWH_ne h hs,
      map_zero]

end General

theorem rowst_mem_dualWeyl_iff {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule, AlgHom.toLinearMap_apply]

def rowActO (R : Type*) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun o => Option.elim o (X none) (fun v => ∑ b : Fin r, C (g v.1 b) * X (some (b, v.2)))

theorem colAddGen_rowAct {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l j (rowAct R g f) = rowActO R g (colAddGen R l j f) := by
  have key : (colAddGen R l j).comp (rowAct R g) =
      (rowActO R g).comp (colAddGen R (r := r) l j) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩

    simp only [AlgHom.comp_apply, colAddGen, rowAct, rowActO, aeval_X, map_sum,
    map_mul, aeval_C, MvPolynomial.algebraMap_eq]
    by_cases h : t = j
    · simp only [h, if_true, aeval_X, map_add (f := _), map_mul, Option.elim]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    · simp [h]
  exact DFunLike.congr_fun key f

theorem rename_rowAct {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rename (some : Fin r × Fin n → Option (Fin r × Fin n)) (rowAct R g f) =
      rowActO R g (rename some f) := by
  have key : (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).comp (rowAct R g) =
      (rowActO R g).comp (rename some) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    simp [rowAct, rowActO, MvPolynomial.algebraMap_eq]
  exact DFunLike.congr_fun key f

theorem rowAct_X_isWH {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (v : Fin r × Fin n) : IsWeightedHomogeneous (colW r n) (rowAct R g (X v)) (colW r n v) := by
  simp only [rowAct, aeval_X]
  refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
  convert (isWeightedHomogeneous_C (colW r n) (g v.1 b)).mul
    (isWeightedHomogeneous_X (R := R) (colW r n) (b, v.2)) using 1
  simp [colW]

end Formalism.GradedWeylDivisibility
end
end

section

open Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma antitone_prod_pow_dominance (t : ℕ → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht : Antitone t) (μ lam : ℕ → ℕ) :
    ∀ N : ℕ, (∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a) →
      ∀ c : ℝ, 0 ≤ c → (∀ a < N, c ≤ t a) →
      (∏ a ∈ range N, t a ^ μ a) * c ^ (∑ a ∈ range N, lam a - ∑ a ∈ range N, μ a) ≤
        ∏ a ∈ range N, t a ^ lam a := by
  intro N
  induction N with
  | zero => intro _ c _ _; simp
  | succ N ih =>
    intro hS c hc hct
    have hSN : ∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a := fun k hk => hS k (by omega)
    have hN := hS N (by omega)
    have hN1 := hS (N + 1) le_rfl
    simp only [Finset.sum_range_succ, Finset.prod_range_succ] at hN1 ⊢
    set Pm := ∏ a ∈ range N, t a ^ μ a with hPm
    set Pl := ∏ a ∈ range N, t a ^ lam a with hPl
    set M := ∑ a ∈ range N, μ a with hM
    set L := ∑ a ∈ range N, lam a with hL
    have htN : 0 ≤ t N := ht0 N
    have hPm0 : 0 ≤ Pm := Finset.prod_nonneg fun a _ => pow_nonneg (ht0 a) _
    have hPl0 : 0 ≤ Pl := Finset.prod_nonneg fun a _ => pow_nonneg (ht0 a) _
    have hcN : c ≤ t N := hct N (by omega)
    rcases le_total (μ N) (lam N) with h | h
    · have e : L + lam N - (M + μ N) = (L - M) + (lam N - μ N) := by omega
      rw [e, pow_add]
      have ih' := ih hSN c hc (fun a ha => hct a (by omega))
      have h2 : t N ^ μ N * c ^ (lam N - μ N) ≤ t N ^ lam N := by
        calc t N ^ μ N * c ^ (lam N - μ N) ≤ t N ^ μ N * t N ^ (lam N - μ N) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc hcN _) (pow_nonneg htN _)
          _ = t N ^ lam N := by rw [← pow_add, Nat.add_sub_cancel' h]
      calc Pm * t N ^ μ N * (c ^ (L - M) * c ^ (lam N - μ N))
          = (Pm * c ^ (L - M)) * (t N ^ μ N * c ^ (lam N - μ N)) := by ring
        _ ≤ Pl * t N ^ lam N :=
          mul_le_mul ih' h2 (mul_nonneg (pow_nonneg htN _) (pow_nonneg hc _)) hPl0
    · have ih' := ih hSN (t N) htN (fun a ha => ht (show a ≤ N by omega))
      have e2 : t N ^ μ N * t N ^ (L + lam N - (M + μ N)) = t N ^ (L - M) * t N ^ lam N := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      calc Pm * t N ^ μ N * c ^ (L + lam N - (M + μ N))
          ≤ Pm * t N ^ μ N * t N ^ (L + lam N - (M + μ N)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc hcN _)
              (mul_nonneg hPm0 (pow_nonneg htN _))
        _ = Pm * t N ^ (L - M) * t N ^ lam N := by rw [mul_assoc, e2, ← mul_assoc]
        _ ≤ Pl * t N ^ lam N := mul_le_mul_of_nonneg_right ih' (pow_nonneg htN _)

lemma ldiag_domPow_nat (t : ℕ → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht : Antitone t) (μ lam : ℕ → ℕ) (N : ℕ)
    (hS : ∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a)
    (hT : ∑ a ∈ range N, μ a = ∑ a ∈ range N, lam a) :
    ∏ a ∈ range N, t a ^ μ a ≤ ∏ a ∈ range N, t a ^ lam a := by
  have h := antitone_prod_pow_dominance t ht0 ht μ lam N hS 0 le_rfl (fun a _ => ht0 a)
  rwa [hT, Nat.sub_self, pow_zero, mul_one] at h

def ldiagExt {α : Type*} [Zero α] {r : ℕ} (f : Fin r → α) (a : ℕ) : α :=
  if h : a < r then f ⟨a, h⟩ else 0

lemma ldiag_ext_fin {α : Type*} [Zero α] {r : ℕ} (f : Fin r → α) (a : Fin r) : ldiagExt f a = f a := by
  rw [ldiagExt, dif_pos a.isLt]

lemma ldiag_sum_filter_lt_eq_range {r : ℕ} (f : Fin r → ℕ) (k : ℕ) (hk : k ≤ r) :
    ∑ a : Fin r with a.val < k, f a = ∑ a ∈ range k, ldiagExt f a := by
  rw [Finset.sum_filter]
  have h1 : ∀ a : Fin r, (if a.val < k then f a else 0) =
      (fun i : ℕ => if i < k then ldiagExt f i else 0) a.val := fun a => by
    simp only [ldiag_ext_fin]
  rw [Finset.sum_congr rfl (fun a _ => h1 a),
    Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < k then ldiagExt f i else 0) r, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by omega, h⟩

lemma ldiag_sum_univ_eq_range {r : ℕ} (f : Fin r → ℕ) :
    ∑ a : Fin r, f a = ∑ a ∈ range r, ldiagExt f a := by
  have h := ldiag_sum_filter_lt_eq_range f r le_rfl
  simpa using h

lemma ldiag_prod_univ_eq_range {r : ℕ} (t : Fin r → ℝ) (μ : Fin r → ℕ) :
    ∏ a : Fin r, t a ^ μ a = ∏ a ∈ range r, ldiagExt t a ^ ldiagExt μ a := by
  rw [← Fin.prod_univ_eq_prod_range (fun i : ℕ => ldiagExt t i ^ ldiagExt μ i) r]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [ldiag_ext_fin]

theorem dominancePowerProduct_holds : DomPow := by
  intro r t μ lam ht0 ht hS hT
  rw [ldiag_prod_univ_eq_range, ldiag_prod_univ_eq_range]
  have hext0 : ∀ a, 0 ≤ ldiagExt t a := fun a => by
    unfold ldiagExt; split_ifs
    · exact ht0 _
    · exact le_rfl
  refine ldiag_domPow_nat (ldiagExt t) hext0 ?_ (ldiagExt μ) (ldiagExt lam) r ?_ ?_
  · intro a b hab
    by_cases hb : b < r
    · have ha : a < r := lt_of_le_of_lt hab hb
      simp only [ldiagExt, dif_pos ha, dif_pos hb]
      exact ht (show (⟨a, ha⟩ : Fin r) ≤ ⟨b, hb⟩ from hab)
    · simp only [ldiagExt, dif_neg hb]
      exact hext0 a
  · intro k hk
    rw [← ldiag_sum_filter_lt_eq_range μ k hk, ← ldiag_sum_filter_lt_eq_range lam k hk]
    exact hS k
  · rw [← ldiag_sum_univ_eq_range, ← ldiag_sum_univ_eq_range]
    exact hT

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lclosedeq_rowGen_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowGen S a b (map φ f) = Polynomial.map (map φ) (rowGen R a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [map_C, rowGen, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq, Polynomial.map_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, Polynomial.map_add (f := _)]
  | mul_X p v hp =>
    simp only [map_mul, map_X, hp, Polynomial.map_mul]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp [Polynomial.map_add (f := _), Polynomial.map_mul, map_X]

theorem lclosedeq_rowDiv_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv S a b k (map φ f) = map φ (rowDiv R a b k f) := by
  simp only [rowDiv, lclosedeq_rowGen_map, Polynomial.coeff_map]

theorem lclosedeq_applyWord_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord S w (map φ f) = map φ (applyWord R w f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [ih, lclosedeq_rowDiv_map]

theorem lclosedeq_lpMinor_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    map φ (lpMinor R (r := r) (n := n) s hr hn) = lpMinor S s hr hn := by
  unfold lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply, map_X]

theorem lclosedeq_hw_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (hn : n ≤ r) (ν : Fin n → ℕ) :
    map φ (hw R hn ν) = hw S hn ν := by
  simp only [hw, map_prod, map_pow, lclosedeq_lpMinor_map]

end Formalism.GradedWeylDivisibility
end
end

section

namespace Formalism.GradedWeylDivisibility

open MvPolynomial

theorem rowPartSum : RowNuSum := by
  classical
  intro r n ν hn k
  let g : ℕ → ℕ := fun i => if i < k then (if h : i < n then ν ⟨i, h⟩ else 0) else 0
  have hL : ∑ a : Fin r with a.val < k, rowNu (r := r) ν a = ∑ i ∈ Finset.range r, g i := by
    rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range g r]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [g, rowNu]
  have hR : ∑ t : Fin n with t.val < k, ν t = ∑ i ∈ Finset.range n, g i := by
    rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range g n]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [g, dif_pos t.isLt]
  rw [hL, hR]
  refine (Finset.sum_subset (fun i hi => ?_) (fun i hi hni => ?_)).symm
  · simp only [Finset.mem_range] at hi ⊢; omega
  · simp only [Finset.mem_range] at hi hni
    simp only [g, dif_neg hni, ite_self]

end Formalism.GradedWeylDivisibility
end

section

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem sum_fin_filter_lt_eq_range {N : ℕ} (G : ℕ → ℕ) (k : ℕ) :
    ∑ a : Fin N with a.val < k, G a.val = ∑ i ∈ Finset.range (min N k), G i := by
  rw [Finset.sum_filter]
  refine (Fin.sum_univ_eq_sum_range (fun i => if i < k then G i else 0) N).trans ?_
  show ∑ i ∈ Finset.range N, (if i < k then G i else 0) = _
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem rowNu_partial_sum {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r) (k : ℕ) :
    (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) = ∑ t : Fin n with t.val < k, ν t := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ, G = fun i => if h : i < n then ν ⟨i, h⟩ else 0 := ⟨_, rfl⟩
  have h1 : (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) =
      ∑ a : Fin r with a.val < k, G a.val :=
    Finset.sum_congr rfl fun a _ => by subst hG; rfl
  have h2 : (∑ t : Fin n with t.val < k, ν t) = ∑ t : Fin n with t.val < k, G t.val :=
    Finset.sum_congr rfl fun t _ => by subst hG; simp [t.isLt]
  rw [h1, h2, sum_fin_filter_lt_eq_range, sum_fin_filter_lt_eq_range]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hi'
    simp only [Finset.mem_range] at hi hi'
    have hin : ¬ i < n := by omega
    rw [hG]
    simp [hin]

end Formalism.GradedWeylDivisibility
end
end
