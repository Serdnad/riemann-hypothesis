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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem support_prod_le_of_additive {σ ι R : Type*} [CommSemiring R] [DecidableEq ι] [DecidableEq σ]
    (F : (σ →₀ ℕ) → ℕ) (hF0 : F 0 = 0) (hFa : ∀ a b, F (a + b) = F a + F b)
    (s : Finset ι) (f : ι → MvPolynomial σ R) (b : ι → ℕ)
    (hb : ∀ i ∈ s, ∀ m ∈ (f i).support, F m ≤ b i) :
    ∀ m ∈ (∏ i ∈ s, f i).support, F m ≤ ∑ i ∈ s, b i := by
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.prod_empty, mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp [hF0]
    · exact absurd rfl hm
  | insert i s hi ih =>
    intro m hm
    rw [Finset.prod_insert hi] at hm
    obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
    rw [hFa, Finset.sum_insert hi]
    exact Nat.add_le_add (hb i (mem_insert_self _ _) a ha)
      (ih (fun j hj => hb j (mem_insert_of_mem hj)) c hc)

theorem support_prod_eq_of_additive {σ ι R : Type*} [CommSemiring R] [DecidableEq ι] [DecidableEq σ]
    (F : (σ →₀ ℕ) → ℕ) (hF0 : F 0 = 0) (hFa : ∀ a b, F (a + b) = F a + F b)
    (s : Finset ι) (f : ι → MvPolynomial σ R) (b : ι → ℕ)
    (hb : ∀ i ∈ s, ∀ m ∈ (f i).support, F m = b i) :
    ∀ m ∈ (∏ i ∈ s, f i).support, F m = ∑ i ∈ s, b i := by
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    rw [Finset.prod_empty, mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp [hF0]
    · exact absurd rfl hm
  | insert i s hi ih =>
    intro m hm
    rw [Finset.prod_insert hi] at hm
    obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
    rw [hFa, Finset.sum_insert hi, hb i (mem_insert_self _ _) a ha,
      ih (fun j hj => hb j (mem_insert_of_mem hj)) c hc]

theorem rowDeg_add {r n : ℕ} (m m' : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    rowDeg (m + m') a = rowDeg m a + rowDeg m' a := by
  simp [rowDeg, Finset.sum_add_distrib]

theorem rowDeg_zero {r n : ℕ} (a : Fin r) : rowDeg (0 : Fin r × Fin n →₀ ℕ) a = 0 := by
  simp [rowDeg]

theorem rowDeg_single {r n : ℕ} (b a : Fin r) (s : Fin n) :
    rowDeg (Finsupp.single (b, s) 1) a = if b = a then 1 else 0 := by
  classical
  unfold rowDeg
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases h : b = a
  · subst h; simp
  · simp [h]

def rowPart {r n : ℕ} (k : ℕ) (m : Fin r × Fin n →₀ ℕ) : ℕ :=
  ∑ a : Fin r with a.val < k, rowDeg m a

theorem rowPart_zero {r n : ℕ} (k : ℕ) : rowPart k (0 : Fin r × Fin n →₀ ℕ) = 0 := by
  simp [rowPart, rowDeg_zero]

theorem rowPart_add {r n : ℕ} (k : ℕ) (m m' : Fin r × Fin n →₀ ℕ) :
    rowPart k (m + m') = rowPart k m + rowPart k m' := by
  simp [rowPart, rowDeg_add, Finset.sum_add_distrib]

theorem rowPart_single {r n : ℕ} (k : ℕ) (b : Fin r) (s : Fin n) :
    rowPart k (Finsupp.single (b, s) 1 : Fin r × Fin n →₀ ℕ) = if b.val < k then 1 else 0 := by
  classical
  unfold rowPart
  simp only [rowDeg_single]
  rw [Finset.sum_ite_eq]
  simp

def rowTot {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) : ℕ := ∑ a : Fin r, rowDeg m a

theorem rowTot_zero {r n : ℕ} : rowTot (0 : Fin r × Fin n →₀ ℕ) = 0 := by
  simp [rowTot, rowDeg_zero]

theorem rowTot_add {r n : ℕ} (m m' : Fin r × Fin n →₀ ℕ) :
    rowTot (m + m') = rowTot m + rowTot m' := by
  simp [rowTot, rowDeg_add, Finset.sum_add_distrib]

theorem rowTot_single {r n : ℕ} (b : Fin r) (s : Fin n) :
    rowTot (Finsupp.single (b, s) 1 : Fin r × Fin n →₀ ℕ) = 1 := by
  classical
  unfold rowTot
  simp only [rowDeg_single]
  simp

theorem support_X_subset' {σ R : Type*} [CommSemiring R] (v : σ) :
    (X v : MvPolynomial σ R).support ⊆ {Finsupp.single v 1} :=
  support_monomial_subset

theorem initMinor_term_support {R : Type*} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (σ : Equiv.Perm (Fin s)) (m : Fin r × Fin n →₀ ℕ)
    (hm : m ∈ (∏ i : Fin s, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)).support) :
    (∀ k, rowPart k m = #{p : Fin s | (I p).val < k}) ∧ rowTot m = s := by
  classical
  constructor
  · intro k
    have h := support_prod_eq_of_additive (rowPart k) (rowPart_zero k) (rowPart_add k) Finset.univ
      (fun i : Fin s => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (fun i => if (I (σ i)).val < k then 1 else 0)
      (by
        intro i _ m' hm'
        have := support_X_subset' (R := R) _ hm'
        rw [Finset.mem_singleton] at this
        subst this
        exact rowPart_single k _ _) m hm
    rw [h, Equiv.sum_comp σ (fun p => if (I p).val < k then 1 else 0), Finset.sum_boole]
    simp
  · have h := support_prod_eq_of_additive rowTot rowTot_zero rowTot_add Finset.univ
      (fun i : Fin s => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (fun _ => 1)
      (by
        intro i _ m' hm'
        have := support_X_subset' (R := R) _ hm'
        rw [Finset.mem_singleton] at this
        subst this
        exact rowTot_single _ _) m hm
    rw [h]; simp

theorem initMinor_support {R : Type*} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ (initMinor R I hs).support) :
    (∀ k, rowPart k m ≤ min k s) ∧ rowTot m = s := by
  classical
  by_cases hI : Function.Injective I
  · unfold initMinor at hm
    rw [Matrix.det_apply] at hm
    have h1 := support_sum hm
    rw [Finset.mem_biUnion] at h1
    obtain ⟨σ, -, hσ⟩ := h1
    rw [Units.smul_def] at hσ
    have hσ' := support_smul hσ
    simp only [Matrix.of_apply] at hσ'
    obtain ⟨hp, ht⟩ := initMinor_term_support I hs σ m hσ'
    refine ⟨fun k => ?_, ht⟩
    rw [hp k]
    refine le_min ?_ ?_
    · calc #{p : Fin s | (I p).val < k} ≤ #{a : Fin r | a.val < k} := by
            apply Finset.card_le_card_of_injOn I
            · intro p hp'
              simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hp' ⊢
              exact hp'
            · intro p _ q _ h; exact hI h
        _ = min r k := Fin.card_filter_val_lt
        _ ≤ k := min_le_right _ _
    · calc #{p : Fin s | (I p).val < k} ≤ #(Finset.univ : Finset (Fin s)) := Finset.card_filter_le _ _
        _ = s := by simp
  · exfalso
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨p, q, hpq, hne⟩ := hI
    have h0 : initMinor R I hs = 0 := by
      unfold initMinor
      apply Matrix.det_zero_of_row_eq hne
      funext j
      simp [hpq]
    rw [h0, support_zero] at hm
    exact Finset.notMem_empty _ hm

theorem sum_min_eq_shapeDeg {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : ℕ) :
    ∑ k' : Fin K, min k (sz k') = ∑ t : Fin n with t.val < k, shapeDeg sz t := by
  classical
  unfold shapeDeg
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k' _
  rw [Finset.sum_boole, Finset.filter_filter]
  have e : #{t : Fin n | t.val < k ∧ t.val < sz k'} = #{t : Fin n | t.val < min k (sz k')} := by
    congr 1; ext t; simp [lt_min_iff]
  rw [Nat.cast_id, e, Fin.card_filter_val_lt]
  have := hsz k'
  omega

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem rowdiv_mem_dualWeyl_iff (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

def CoeffHom {R : Type*} [CommRing R] {r n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R))
    (μ : Fin n → ℕ) : Prop :=
  ∀ k, IsWeightedHomogeneous (colW r n) (P.coeff k) μ

theorem CoeffHom.mul {R : Type*} [CommRing R] {r n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' : Fin n → ℕ}
    (hP : CoeffHom P μ) (hQ : CoeffHom Q μ') : CoeffHom (P * Q) (μ + μ') := by
  intro k
  rw [Polynomial.coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ fun x _ => (hP x.1).mul (hQ x.2)

theorem CoeffHom.one {R : Type*} [CommRing R] {r n : ℕ} :
    CoeffHom (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs
  · exact isWeightedHomogeneous_one R _
  · exact isWeightedHomogeneous_zero R _ _

theorem CoeffHom.pow {R : Type*} [CommRing R] {r n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ : Fin n → ℕ}
    (hP : CoeffHom P μ) (e : ℕ) : CoeffHom (P ^ e) (e • μ) := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact CoeffHom.one
  | succ e ih => rw [pow_succ, succ_nsmul]; exact ih.mul hP

theorem CoeffHom.prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → Fin n → ℕ)
    (h : ∀ i ∈ s, CoeffHom (P i) (μ i)) : CoeffHom (∏ i ∈ s, P i) (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CoeffHom.one (R := R) (r := r) (n := n))
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem CoeffHom.algebraMap {R : Type*} [CommRing R] {r n : ℕ} (c : R) :
    CoeffHom (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs
  · rw [MvPolynomial.algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  · exact isWeightedHomogeneous_zero R _ _

theorem CoeffHom.gen {R : Type*} [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    CoeffHom (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (colW r n v) := by
  intro k
  have hX : IsWeightedHomogeneous (colW r n) (X v : MvPolynomial (Fin r × Fin n) R) (colW r n v) :=
    isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (colW r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (colW r n v) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs
    · exact hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs
      · exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _

theorem CoeffHom.rowGen_monomial (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    CoeffHom (rowGen R a b (monomial d c)) (Finsupp.weight (colW r n) d) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine (CoeffHom.algebraMap c).mul ?_
  unfold Finsupp.prod Finsupp.sum
  exact CoeffHom.prod _ _ _ fun v _ => (CoeffHom.gen a b v).pow _

theorem rowDiv_homog (R : Type*) [CommRing R] {r n : ℕ} (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (colW r n) f ν) :
    IsWeightedHomogeneous (colW r n) (rowDiv R a b k f) ν := by
  unfold rowDiv
  conv => pattern f; rw [f.as_sum]

  rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := CoeffHom.rowGen_monomial R a b d (AddMonoidAlgebra.coeff f d) k
  rwa [hf (mem_support_iff.mp hd)] at this

def rowGenO (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R]
      Polynomial (MvPolynomial (Option (Fin r × Fin n)) R) :=
  aeval fun o => Option.elim o (Polynomial.C (X none)) fun v =>
    Polynomial.C (X (some v)) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (some (a, v.2))) else 0)

theorem rowGenO_comp_colAddGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (l j : Fin n) :
    (rowGenO R a b).comp (colAddGen R (r := r) l j) =
      (Polynomial.mapAlgHom (colAddGen R (r := r) l j)).comp (rowGen R a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, colAddGen, rowGen, rowGenO, aeval_X, Polynomial.coe_mapAlgHom]
  by_cases h2 : v.2 = j <;> by_cases h1 : v.1 = b <;>
    simp [h1, h2, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
      aeval_X] <;> ring

theorem rowGenO_comp_rename (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    (rowGenO R a b).comp (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
      (Polynomial.mapAlgHom (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n)))).comp
        (rowGen R a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, rename_X, rowGen, rowGenO, aeval_X, Polynomial.coe_mapAlgHom]
  by_cases h1 : v.1 = b <;>
    simp [h1, Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]

theorem rowDiv_colAddGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (l j : Fin n)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : colAddGen R l j f = rename some f) :
    colAddGen R l j (rowDiv R a b k f) = rename some (rowDiv R a b k f) := by
  have hA := congrArg (fun φ => φ f) (rowGenO_comp_colAddGen R a b l j)
  have hB := congrArg (fun φ => φ f) (rowGenO_comp_rename R (n := n) a b)
  simp only [AlgHom.comp_apply, Polynomial.coe_mapAlgHom] at hA hB
  rw [hf, hB] at hA
  have hk := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P k) hA
  simp only [Polynomial.coeff_map] at hk
  unfold rowDiv
  exact hk.symm

theorem dualWeylModuleRowDividedPowerStable : RowDivStable := by
  intro R _ r n ν a b k f hf
  rw [rowdiv_mem_dualWeyl_iff] at hf ⊢
  exact ⟨rowDiv_homog R ν a b k f hf.1, fun l j hlj => rowDiv_colAddGen R a b k l j f (hf.2 l j hlj)⟩

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem rowGen_X (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  rw [rowGen, aeval_X]

theorem rowGen_lpMinor (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (hab : a < b)
    (m : ℕ) (hr : m ≤ r) (hn : m ≤ n) :
    rowGen R a b (lpMinor R m hr hn) = Polynomial.C (lpMinor R m hr hn) := by
  classical
  unfold lpMinor
  rw [AlgHom.map_det, RingHom.map_det]
  set N : Matrix (Fin m) (Fin m) (MvPolynomial (Fin r × Fin n) R) :=
    Matrix.of fun p q : Fin m => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)
    with hN
  by_cases hb : b.val < m
  · have ha : a.val < m := lt_trans hab hb
    set i : Fin m := ⟨b.val, hb⟩ with hi
    set j : Fin m := ⟨a.val, ha⟩ with hj
    have hij : i ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp [hi, hj] at this
      exact absurd this (Fin.val_ne_of_ne (ne_of_lt hab)).symm
    have hM : (rowGen R a b).toRingHom.mapMatrix N =
        Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) i
          (((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) i +
            (Polynomial.X : Polynomial (MvPolynomial (Fin r × Fin n) R)) • ((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) j) := by
      ext p q
      by_cases hp : p = i
      · subst hp
        have h1 : Fin.castLE hr i = b := Fin.ext (by simp [hi])
        have h2 : Fin.castLE hr j = a := Fin.ext (by simp [hj])
        simp [hN, Matrix.updateRow_apply, rowGen_X, h1, h2, smul_eq_mul]
      · have h1 : Fin.castLE hr p ≠ b := by
          intro h
          apply hp
          exact Fin.ext (by have := congrArg Fin.val h; simpa [hi] using this)
        simp [hN, Matrix.updateRow_apply, rowGen_X, h1, hp]
    change ((rowGen R a b).toRingHom.mapMatrix N).det = _
    rw [hM, Matrix.det_updateRow_add_smul_self _ hij]
  · have hM : (rowGen R a b).toRingHom.mapMatrix N =
        (Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N := by
      ext p q
      have h1 : Fin.castLE hr p ≠ b := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [hN, rowGen_X, h1]
    change ((rowGen R a b).toRingHom.mapMatrix N).det = _
    rw [hM]

theorem rowGen_hw (R : Type*) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (a b : Fin r) (hab : a < b) :
    rowGen R a b (hw R hn ν) = Polynomial.C (hw R hn ν) := by
  simp only [hw, map_prod, map_pow, rowGen_lpMinor R a b hab]

theorem highestWeightVectorRaising : HWRaise := by
  intro R _ r n hn ν a b k hab hk
  unfold rowDiv
  rw [rowGen_hw R hn ν a b hab, Polynomial.coeff_C, if_neg (by omega)]

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

theorem ldtwist_map_rowAct {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L) {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (F : MvPolynomial (Fin k × Fin n) K) :
    map φ (rowAct K g F) = rowAct L (g.map φ) (map φ F) := by
  induction F using MvPolynomial.induction_on
  · rename_i a
    simp [rowAct]
  · rename_i p q hp hq
    simp only [map_add (f := _), hp, hq]
  · rename_i p v hp
    simp only [map_mul, hp]
    congr 1
    simp [rowAct, Matrix.map_apply]

end Formalism.GradedWeylDivisibility
end
