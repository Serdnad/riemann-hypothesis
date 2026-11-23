module

public import Formalism.MahlerMeasure.Bundle001
public import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Ring.Subring.Basic

@[expose] public section

section

namespace Formalism.GM

open Finset

theorem altVand (B : ℕ) : ∀ z l : ℕ,
    ∑ j ∈ range (l + 1), (-1 : ℚ) ^ j * (B.choose j : ℚ) * ((z + B + (l - j)).choose (l - j) : ℚ)
      = ((z + l).choose l : ℚ) := by
  induction B with
  | zero =>
    intro z l
    rw [Finset.sum_eq_single 0
      (fun j _ hj => by simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]) (by simp)]
    simp
  | succ B ih =>
    intro z l
    cases l with
    | zero => simp
    | succ m =>
      have h1 := ih (z + 1) (m + 1)
      have h2 := ih (z + 1) m
      rw [Finset.sum_range_succ'] at h1 ⊢
      have key : ∀ j ∈ range (m + 1),
          (-1 : ℚ) ^ (j + 1) * ((B + 1).choose (j + 1) : ℚ) *
              ((z + (B + 1) + (m + 1 - (j + 1))).choose (m + 1 - (j + 1)) : ℚ) =
            (-1 : ℚ) ^ (j + 1) * (B.choose (j + 1) : ℚ) *
                ((z + 1 + B + (m + 1 - (j + 1))).choose (m + 1 - (j + 1)) : ℚ) -
              (-1 : ℚ) ^ j * (B.choose j : ℚ) * ((z + 1 + B + (m - j)).choose (m - j) : ℚ) := by
        intro j hj
        have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have e1 : z + (B + 1) + (m + 1 - (j + 1)) = z + 1 + B + (m - j) := by omega
        have e2 : m + 1 - (j + 1) = m - j := by omega
        have e3 : z + 1 + B + (m + 1 - (j + 1)) = z + 1 + B + (m - j) := by omega
        rw [e1, e3, e2, Nat.choose_succ_succ', Nat.cast_add, pow_succ]
        ring
      rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, h2]
      simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero] at h1 ⊢
      rw [show z + (B + 1) + (m + 1) = z + 1 + B + (m + 1) by omega]
      have hp : ((z + 1 + (m + 1)).choose (m + 1) : ℚ) =
          ((z + 1 + m).choose m : ℚ) + ((z + (m + 1)).choose (m + 1) : ℚ) := by
        have e1 : (z + 1 + (m + 1)).choose (m + 1) = (z + 1 + m + 1).choose (m + 1) := by
          rw [show z + 1 + (m + 1) = z + 1 + m + 1 by omega]
        have e2 : (z + (m + 1)).choose (m + 1) = (z + 1 + m).choose (m + 1) := by
          rw [show z + (m + 1) = z + 1 + m by omega]
        rw [e1, e2, Nat.choose_succ_succ']
        push_cast
        ring
      linear_combination h1 + hp

theorem alternatingChooseSum : LevelSum := by
  intro A z l hzl
  unfold qch
  have hAl : (A.choose l : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [← altVand (A - z - l) z l, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjl : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hAj : (A.choose j : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hcm : (A.choose l : ℚ) * (l.choose j : ℚ) = (A.choose j : ℚ) * ((A - j).choose (l - j) : ℚ) := by
    exact_mod_cast Nat.choose_mul (n := A) (k := l) (s := j) (by omega)
  have he : z + (A - z - l) + (l - j) = A - j := by omega
  rw [he, div_eq_div_iff hAj hAl]
  linear_combination ((-1 : ℚ) ^ j * ((A - z - l).choose j : ℚ)) * hcm

end Formalism.GM
end

section

namespace Formalism.GM

open Finset Polynomial

theorem prod_natDegree_coeff {K ι : Type*} [CommRing K] (s : Finset ι) (f : ι → K[X]) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h
    have ha' : (f a).natDegree ≤ d a := h a (Finset.mem_insert_self a s)
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨Polynomial.natDegree_mul_le.trans (add_le_add ha' ih1),
      by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le ha' ih1, ih2]⟩

theorem term_natDegree_coeff {K : Type*} [CommRing K] (u : ℤˣ) (p : K[X]) (N : ℕ)
    (hp : p.natDegree ≤ N) :
    (u • p).natDegree ≤ N ∧ (u • p).coeff N = u • p.coeff N := by
  refine ⟨?_, ?_⟩
  · rw [Units.smul_def]
    exact (Polynomial.natDegree_smul_le _ _).trans hp
  · rw [Units.smul_def, Units.smul_def, Polynomial.coeff_smul]

theorem det_natDegree_coeff {K : Type*} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K[X]) (N : ℕ)
    (c : Equiv.Perm (Fin n) → Fin n → ℕ) (hc : ∀ σ, ∑ i, c σ i = N)
    (hA : ∀ σ i, (A (σ i) i).natDegree ≤ c σ i) :
    A.det.natDegree ≤ N ∧
      A.det.coeff N = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, (A (σ i) i).coeff (c σ i) := by
  have key : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natDegree ≤ N ∧
      (Equiv.Perm.sign σ • ∏ i, A (σ i) i).coeff N =
        Equiv.Perm.sign σ • ∏ i, (A (σ i) i).coeff (c σ i) := by
    intro σ
    obtain ⟨h1, h2⟩ := prod_natDegree_coeff univ (fun i => A (σ i) i) (c σ) (fun i _ => hA σ i)
    rw [hc σ] at h1 h2
    obtain ⟨k1, k2⟩ := term_natDegree_coeff (Equiv.Perm.sign σ) _ N h1
    exact ⟨k1, by rw [k2, h2]⟩
  rw [Matrix.det_apply]
  refine ⟨natDegree_sum_le_of_forall_le _ _ (fun σ _ => (key σ).1), ?_⟩
  rw [finsetSum_coeff]
  exact sum_congr rfl (fun σ _ => (key σ).2)

theorem determinant_block_leading_term : DetBlockLead := by
  unfold DetBlockLead
  intro K _ n A D e he hA
  set M : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0 with hM
  have hdeg : ∀ σ : Equiv.Perm (Fin n), ∀ i, (A (σ i) i).natDegree ≤ D - e i := by
    intro σ i
    have h3 := hA (σ i) i
    have h4 : e i ≤ max (e (σ i)) (e i) := le_max_right _ _
    omega
  obtain ⟨h1, h2⟩ := det_natDegree_coeff A (∑ i, (D - e i)) (fun _ i => D - e i)
    (fun _ => rfl) hdeg
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      ∏ i, (A (σ i) i).coeff (D - e i) = ∏ i, M (σ i) i := by
    intro σ
    by_cases hall : ∀ i, e (σ i) = e i
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      simp [hM, Matrix.of_apply, hall i]
    · push_neg at hall
      have hex : ∃ j, e j < e (σ j) := by
        by_contra hno
        push_neg at hno
        have hsum : ∑ j, e (σ j) = ∑ j, e j := Equiv.sum_comp σ e
        have hall' := (Finset.sum_eq_sum_iff_of_le (fun j _ => hno j)).1 hsum
        obtain ⟨i, hi⟩ := hall
        exact hi (hall' i (Finset.mem_univ i))
      obtain ⟨j, hj⟩ := hex
      have hne : e (σ j) ≠ e j := ne_of_gt hj
      have hL : (A (σ j) j).coeff (D - e j) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have h3 := hA (σ j) j
        have h4 : e (σ j) ≤ max (e (σ j)) (e j) := le_max_left _ _
        have h5 := he (σ j)
        omega
      have hR : M (σ j) j = 0 := by simp [hM, Matrix.of_apply, hne]
      rw [Finset.prod_eq_zero (f := fun i => (A (σ i) i).coeff (D - e i)) (Finset.mem_univ j) hL,
        Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ j) hR]
  have hdet : A.det.coeff (∑ i, (D - e i)) = M.det := by
    rw [h2, Matrix.det_apply]
    exact Finset.sum_congr rfl (fun σ _ => by rw [hprod σ])
  refine ⟨h1, hdet, fun hne => ?_⟩
  have hN : A.det.natDegree = ∑ i, (D - e i) :=
    le_antisymm h1 (Polynomial.le_natDegree_of_ne_zero (by rw [hdet]; exact hne))
  refine ⟨hN, ?_⟩
  rw [Polynomial.leadingCoeff, hN, hdet]

end Formalism.GM
end

section

namespace Formalism.GM

open Polynomial

def zpS (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {x | padicNorm p x ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, padicNorm.mul] at *
    exact mul_le_one₀ ha (padicNorm.nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact le_trans padicNorm.nonarchimedean (max_le ha hb)
  zero_mem' := by simp [padicNorm.zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, padicNorm.neg] at *
    exact ha

def zpT (p : ℕ) [Fact p.Prime] : Subring ℚ[X] where
  carrier := {P | ∀ n, P.coeff n ∈ zpS p}
  mul_mem' {a b} ha hb := by
    intro n
    rw [coeff_mul]
    exact Subring.sum_mem _ (fun x _ => Subring.mul_mem _ (ha _) (hb _))
  one_mem' := by
    intro n
    rw [coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' {a b} ha hb := by
    intro n
    rw [coeff_add]
    exact Subring.add_mem _ (ha n) (hb n)
  zero_mem' := by intro n; simp
  neg_mem' {a} ha := by
    intro n
    rw [coeff_neg]
    exact Subring.neg_mem _ (ha n)

lemma C_mem_zpT (p : ℕ) [Fact p.Prime] {a : ℚ} (ha : a ∈ zpS p) : C a ∈ zpT p := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact Subring.zero_mem _

lemma X_mem_zpT (p : ℕ) [Fact p.Prime] : (X : ℚ[X]) ∈ zpT p := by
  intro n
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

lemma div_mem_zpS (p k m : ℕ) [hp : Fact p.Prime] (hm1 : 1 ≤ m) (hm : m ≤ p ^ k) :
    ((p : ℚ) ^ k / m) ∈ zpS p := by
  show padicNorm p ((p : ℚ) ^ k / m) ≤ 1
  have hp1 : 1 < p := hp.out.one_lt
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hpk0 : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)

  have hv : multiplicity p m ≤ k := by
    have h1 : p ^ multiplicity p m ≤ m := Nat.le_of_dvd (by omega) (pow_multiplicity_dvd p m)
    exact (Nat.pow_le_pow_iff_right hp1).1 (h1.trans hm)
  have hval : padicValRat p ((p : ℚ) ^ k / m) = (k : ℤ) - multiplicity p m := by
    rw [padicValRat.div hpk0 hm0, show ((p : ℚ) ^ k) = ((p ^ k : ℕ) : ℚ) by push_cast; rfl,
      padicValRat.of_nat, padicValRat.of_nat, Nat.multiplicity_prime_pow]
  rw [padicNorm.eq_zpow_of_nonzero (div_ne_zero hpk0 hm0), hval]
  apply zpow_le_one_of_nonpos₀ (by exact_mod_cast hp1.le)
  omega

noncomputable def bB (c : ℚ) (i : ℕ) (t : ℤ) : ℚ[X] :=
  C ((i.factorial : ℚ)⁻¹) * (descPochhammer ℚ i).comp (C c * X + C (t : ℚ))

lemma bB_zero (c : ℚ) (t : ℤ) : bB c 0 t = 1 := by
  simp [bB]

private lemma descPochhammer_comp_add_one (Q : ℚ[X]) (i : ℕ) :
    (descPochhammer ℚ (i + 1)).comp (Q + 1) =
      (descPochhammer ℚ (i + 1)).comp Q + ((i : ℚ[X]) + 1) * (descPochhammer ℚ i).comp Q := by

  have h1 : (descPochhammer ℚ (i + 1)).comp (Q + 1) = (Q + 1) * (descPochhammer ℚ i).comp Q := by
    rw [descPochhammer_succ_left, mul_comp, X_comp, comp_assoc, sub_comp, X_comp, one_comp,
      add_sub_cancel_right]
  have h2 : (descPochhammer ℚ (i + 1)).comp Q = (descPochhammer ℚ i).comp Q * (Q - (i : ℚ[X])) := by
    rw [descPochhammer_succ_right, mul_comp, sub_comp, X_comp, natCast_comp]
  rw [h1, h2]
  ring

lemma bB_pascal (c : ℚ) (i : ℕ) (t : ℤ) : bB c (i + 1) (t + 1) = bB c (i + 1) t + bB c i t := by
  have hQ : C c * X + C (((t + 1 : ℤ)) : ℚ) = (C c * X + C (t : ℚ)) + 1 := by
    push_cast
    rw [C_add, C_1]
    ring
  simp only [bB]
  rw [hQ, descPochhammer_comp_add_one, Nat.factorial_succ]
  have hf : ((i.factorial : ℚ)) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hC : (C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹) * ((i : ℚ[X]) + 1) = C ((i.factorial : ℚ)⁻¹) := by
    rw [← C_1, ← C_eq_natCast, ← C_add, ← C_mul]
    congr 1
    push_cast
    field_simp
  rw [mul_add, ← mul_assoc, hC]

lemma bB_succ_zero (c : ℚ) (i : ℕ) : bB c (i + 1) 0 = C (c / (i + 1 : ℕ)) * X * bB c i (-1) := by
  simp only [bB]
  rw [descPochhammer_succ_left, mul_comp, X_comp, comp_assoc, sub_comp, X_comp, one_comp,
    Nat.factorial_succ]
  have hf : ((i.factorial : ℚ)) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
  have e1 : C c * X + C (((0 : ℤ)) : ℚ) - 1 = C c * X + C (((-1 : ℤ)) : ℚ) := by
    simp only [Int.cast_zero, C_0, add_zero, Int.cast_neg, Int.cast_one, C_neg, C_1]
    ring
  rw [e1]
  have hC : C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹ * C c = C (c / ((i + 1 : ℕ) : ℚ)) * C ((i.factorial : ℚ)⁻¹) := by
    rw [← C_mul, ← C_mul]
    congr 1
    push_cast
    field_simp
  simp only [Int.cast_zero, C_0, add_zero]
  calc C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹ * (C c * X * (descPochhammer ℚ i).comp (C c * X + C (((-1 : ℤ)) : ℚ)))
      = (C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹ * C c) * X * (descPochhammer ℚ i).comp (C c * X + C (((-1 : ℤ)) : ℚ)) := by ring
    _ = _ := by rw [hC]; ring

theorem bB_mem (p k : ℕ) [Fact p.Prime] : ∀ i, i ≤ p ^ k → ∀ t : ℤ, bB ((p : ℚ) ^ k) i t ∈ zpT p := by
  intro i
  induction i with
  | zero => intro _ t; rw [bB_zero]; exact Subring.one_mem _
  | succ i ih =>
    intro hi t
    have ih' := ih (by omega)
    have h0 : bB ((p : ℚ) ^ k) (i + 1) 0 ∈ zpT p := by
      rw [bB_succ_zero]
      refine Subring.mul_mem _ (Subring.mul_mem _ (C_mem_zpT p ?_) (X_mem_zpT p)) (ih' _)
      exact div_mem_zpS p k (i + 1) (by omega) hi
    induction t using Int.induction_on with
    | zero => exact h0
    | succ n hn => rw [bB_pascal]; exact Subring.add_mem _ hn (ih' _)
    | pred n hn =>
      have e := bB_pascal ((p : ℚ) ^ k) i (-(n : ℤ) - 1)
      rw [sub_add_cancel] at e
      rw [show bB ((p : ℚ) ^ k) (i + 1) (-(n : ℤ) - 1) = bB ((p : ℚ) ^ k) (i + 1) (-(n : ℤ)) - bB ((p : ℚ) ^ k) i (-(n : ℤ) - 1) by
        rw [e]; ring]
      exact Subring.sub_mem _ hn (ih' _)

theorem mahler_disc_bound : MahlerDisc := by
  intro p k i t₀ hp hi n
  haveI : Fact p.Prime := ⟨hp⟩
  exact bB_mem p k i hi t₀ n

end Formalism.GM
end
