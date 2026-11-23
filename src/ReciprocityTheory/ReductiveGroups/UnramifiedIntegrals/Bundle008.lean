module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle002
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
public import Mathlib.FieldTheory.Finite.Basic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

variable {K : Type} [Field K] [CharZero K] [DecidableEq K] (g2 g3 : K) (xs : Finset K)

theorem rootPoly_monic : (rootPoly xs).Monic := by
  unfold rootPoly
  exact monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)

theorem rootPoly_natDegree : (rootPoly xs).natDegree = xs.card := by
  unfold rootPoly
  rw [natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]
  simp

theorem rootPoly_eval (t : K) : (rootPoly xs).eval t = ∏ x ∈ xs, (t - x) := by
  unfold rootPoly
  rw [eval_prod]
  simp

theorem rootPoly_eval_ne {t : K} (ht : t ∉ xs) : (rootPoly xs).eval t ≠ 0 := by
  rw [rootPoly_eval, Finset.prod_ne_zero_iff]
  intro x hx h
  rw [sub_eq_zero] at h
  exact ht (h ▸ hx)

theorem rootPoly_eval_mem {t : K} (ht : t ∈ xs) : (rootPoly xs).eval t = 0 := by
  rw [rootPoly_eval]
  exact Finset.prod_eq_zero ht (sub_self t)

theorem rootPoly_erase {x : K} (hx : x ∈ xs) :
    rootPoly xs = (X - C x) * rootPoly (xs.erase x) := by
  unfold rootPoly
  exact (Finset.mul_prod_erase xs (fun y => (X - C y : K[X])) hx).symm

theorem veluNum_eval' (t : K) :
    (veluNum g2 g3 xs).eval t = t * (rootPoly xs).eval t ^ 2
      + ∑ x ∈ xs, (fW g2 g3 x + fW' g2 x / 2 * (t - x)) * (rootPoly (xs.erase x)).eval t ^ 2 := by
  unfold veluNum
  simp [eval_finsetSum]

theorem veluNum_eval {t : K} (ht : t ∉ xs) :
    (veluNum g2 g3 xs).eval t = veluFun g2 g3 xs t * (rootPoly xs).eval t ^ 2 := by
  rw [veluNum_eval']
  unfold veluFun
  rw [add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hne : t - x ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact ht (h ▸ hx)
  rw [rootPoly_erase xs hx]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  field_simp

theorem veluNum_natDegree_le : (veluNum g2 g3 xs).natDegree ≤ 2 * xs.card + 1 := by
  unfold veluNum
  refine natDegree_add_le_of_degree_le ?_ ?_
  · refine natDegree_mul_le.trans ?_
    have h1 := natDegree_pow_le (p := rootPoly xs) (n := 2)
    rw [rootPoly_natDegree] at h1
    rw [natDegree_X]
    omega
  · refine natDegree_sum_le_of_forall_le _ _ (fun x hx => ?_)
    refine natDegree_mul_le.trans ?_
    have h1 := natDegree_pow_le (p := rootPoly (xs.erase x)) (n := 2)
    rw [rootPoly_natDegree] at h1
    have h2 : (xs.erase x).card ≤ xs.card := Finset.card_erase_le
    have h3 : (C (fW g2 g3 x) + C (fW' g2 x / 2) * (X - C x) : K[X]).natDegree ≤ 1 := by
      refine natDegree_add_le_of_degree_le (by simp) ?_
      refine natDegree_mul_le.trans ?_
      simp
    omega

theorem veluNum_eval_mem {x : K} (hx : x ∈ xs) :
    (veluNum g2 g3 xs).eval x = fW g2 g3 x * (rootPoly (xs.erase x)).eval x ^ 2 := by
  rw [veluNum_eval', rootPoly_eval_mem xs hx, Finset.sum_eq_single_of_mem x hx]
  · simp
  · intro y _ hy
    rw [rootPoly_eval_mem (xs.erase y) (Finset.mem_erase.2 ⟨hy.symm, hx⟩)]
    simp

theorem veluNum_coprime (h : ∀ x ∈ xs, fW g2 g3 x ≠ 0) :
    IsCoprime (veluNum g2 g3 xs) (rootPoly xs ^ 2) := by
  refine IsCoprime.pow_right ?_
  unfold rootPoly
  refine IsCoprime.prod_right (fun x hx => ?_)
  refine IsCoprime.symm ?_
  rw [(irreducible_X_sub_C x).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot.def,
    veluNum_eval_mem g2 g3 xs hx]
  exact mul_ne_zero (h x hx) (pow_ne_zero 2 (rootPoly_eval_ne _ (Finset.notMem_erase x xs)))

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

variable {K : Type} [Field K] (U : PowerSeries K)

theorem homS_add (m : ℕ) (P Q : K[X]) : homS U m (P + Q) = homS U m P + homS U m Q := by
  simp only [homS, coeff_add, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem homS_sub (m : ℕ) (P Q : K[X]) : homS U m (P - Q) = homS U m P - homS U m Q := by
  simp only [homS, coeff_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem homS_zero (m : ℕ) : homS U m (0 : K[X]) = 0 := by
  simp [homS]

theorem homS_sum {ι : Type} (s : Finset ι) (m : ℕ) (f : ι → K[X]) :
    homS U m (∑ i ∈ s, f i) = ∑ i ∈ s, homS U m (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [homS_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, homS_add, ih]

theorem homS_monomial (m i : ℕ) (hi : i ≤ m) (a : K) :
    homS U m (monomial i a) = PowerSeries.C a * U ^ i * PowerSeries.X ^ (2 * (m - i)) := by
  unfold homS
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [coeff_monomial_of_ne a hb]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) h

theorem homS_mul (m n : ℕ) (P Q : K[X]) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) :
    homS U (m + n) (P * Q) = homS U m P * homS U n Q := by
  have eP : P = ∑ i ∈ Finset.range (m + 1), monomial i (P.coeff i) :=
    P.as_sum_range' (m + 1) (Nat.lt_succ_of_le hP)
  have eQ : Q = ∑ j ∈ Finset.range (n + 1), monomial j (Q.coeff j) :=
    Q.as_sum_range' (n + 1) (Nat.lt_succ_of_le hQ)
  have e : P * Q = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      monomial (i + j) (P.coeff i * Q.coeff j) := by
    conv_lhs => rw [eP, eQ]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [e, homS_sum]
  simp only [homS_sum]
  unfold homS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have := homS_monomial U (m + n) (i + j) (by omega) (P.coeff i * Q.coeff j)
  unfold homS at this
  rw [this]
  have h2 : 2 * (m + n - (i + j)) = 2 * (m - i) + 2 * (n - j) := by omega
  rw [h2, pow_add, pow_add, map_mul]
  ring

theorem homS_eq_zero (hU : PowerSeries.constantCoeff U = 1) (m : ℕ) (P : K[X]) (hP : P.natDegree ≤ m)
    (h : homS U m P = 0) : P = 0 := by
  have h1 : PowerSeries.coeff (2 * (m - P.natDegree)) (homS U m P) = P.leadingCoeff := by
    unfold homS

    rw [map_sum, Finset.sum_eq_single P.natDegree]
    · rw [PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_mul, map_pow, hU]
      simp
    · intro b hb hne
      have hb' : b ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        simp
    · intro hh
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hP)) hh
  rw [h, map_zero] at h1
  exact leadingCoeff_eq_zero.1 h1.symm

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section General

variable {R : Type*} [CommRing R] (p : ℕ)

def FrobFix (x : R) : Prop := ∃ f : ℕ, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x

variable {p}

theorem frobFix_iter {x : R} {f : ℕ} (h : (p : R) ∣ x ^ (p ^ f) - x) (k : ℕ) :
    (p : R) ∣ x ^ (p ^ (f * (k + 1))) - x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have e : x ^ (p ^ (f * (k + 1 + 1))) = (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) := by
      rw [← pow_mul, ← pow_add]
      congr 2
    rw [e]
    have h1 : (p : R) ∣ (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) - x ^ (p ^ f) :=
      dvd_trans ih (sub_dvd_pow_sub_pow _ _ _)
    have h2 := dvd_add h1 h
    rwa [sub_add_sub_cancel] at h2

theorem frobFix_common {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    ∃ f : ℕ, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x ∧ (p : R) ∣ y ^ (p ^ f) - y := by
  obtain ⟨f1, hf1, h1⟩ := hx
  obtain ⟨f2, hf2, h2⟩ := hy
  refine ⟨f1 * f2, Nat.mul_pos hf1 hf2, ?_, ?_⟩
  · have h := frobFix_iter h1 (f2 - 1)
    rwa [Nat.sub_add_cancel hf2] at h
  · have h := frobFix_iter h2 (f1 - 1)
    rwa [Nat.sub_add_cancel hf1, mul_comm] at h

theorem frobFix_mul {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) : FrobFix p (x * y) := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  refine ⟨f, hf, ?_⟩
  have e : (x * y) ^ (p ^ f) - x * y = x ^ (p ^ f) * (y ^ (p ^ f) - y) + y * (x ^ (p ^ f) - x) := by
    ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)

private theorem frobFix_add_lemma (hp : p.Prime) (x y : R) (n : ℕ) :
    (p : R) ∣ (x + y) ^ (p ^ n) - (x ^ (p ^ n) + y ^ (p ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : (p : R) ∣ ((x + y) ^ (p ^ n)) ^ p - (x ^ (p ^ n) + y ^ (p ^ n)) ^ p :=
      dvd_trans ih (sub_dvd_pow_sub_pow _ _ _)
    have hB : (p : R) ∣ (x ^ (p ^ n) + y ^ (p ^ n)) ^ p - ((x ^ (p ^ n)) ^ p + (y ^ (p ^ n)) ^ p) := by
      rw [add_pow_prime_eq hp, add_sub_cancel_left]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
    have e : ∀ a : R, a ^ (p ^ (n + 1)) = (a ^ (p ^ n)) ^ p := fun a => by
      rw [pow_succ, pow_mul]
    rw [e, e, e]
    have h := dvd_add hA hB
    rwa [sub_add_sub_cancel] at h

theorem frobFix_add (hp : p.Prime) {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    FrobFix p (x + y) := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  refine ⟨f, hf, ?_⟩
  have h3 := frobFix_add_lemma hp x y f
  have e : (x + y) ^ (p ^ f) - (x + y) =
      ((x + y) ^ (p ^ f) - (x ^ (p ^ f) + y ^ (p ^ f))) + (x ^ (p ^ f) - x) + (y ^ (p ^ f) - y) := by
    ring
  rw [e]
  exact dvd_add (dvd_add h3 h1) h2

theorem frobFix_neg_one (hp : p.Prime) : FrobFix p (-1 : R) := by
  refine ⟨1, one_pos, ?_⟩
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [show (-1 : R) ^ (2 ^ 1) - -1 = ((2 : ℕ) : R) by push_cast; ring]
  · rw [pow_one, hodd.neg_one_pow, sub_self]
    exact dvd_zero _

theorem frobFix_neg (hp : p.Prime) {x : R} (hx : FrobFix p x) : FrobFix p (-x) := by
  simpa using frobFix_mul (frobFix_neg_one (R := R) hp) hx

theorem frobFix_zero (hp : p.Prime) : FrobFix p (0 : R) :=
  ⟨1, one_pos, by rw [pow_one, zero_pow hp.ne_zero, sub_zero]; exact dvd_zero _⟩

theorem frobFix_one : FrobFix p (1 : R) :=
  ⟨1, one_pos, by simp⟩

theorem frobFix_root (hp : p.Prime) {x : R} {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n)
    (hx : x ^ n = 1) : FrobFix p x := by
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
  have htot : p ^ n.totient % n = 1 % n := Nat.ModEq.pow_totient hcop
  refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
  have key : ∀ m, x ^ m = x ^ (m % n) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hx, one_pow, mul_one]
  have hx' : x ^ (p ^ n.totient) = x := by
    rw [key, htot, ← key, pow_one]
  rw [hx', sub_self]
  exact dvd_zero _

end General

variable (l : ℕ) [Fact l.Prime]

theorem rmu_frob (x : ℂ_[l]) (hx : x ∈ Rmu l) :
    ∃ f : ℕ, 0 < f ∧ ∃ r ∈ Rmu l, x ^ (l ^ f) - x = (l : ℂ_[l]) * r := by
  have hp : l.Prime := Fact.out
  have key : ∀ (y : ℂ_[l]) (hy : y ∈ Subring.closure (muP l)), FrobFix l (⟨y, hy⟩ : Rmu l) := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
      obtain ⟨n, hn, hln, hzn⟩ := hz
      exact frobFix_root hp hn hln (Subtype.ext (by simpa using hzn))
    | zero => exact frobFix_zero hp
    | one => exact frobFix_one
    | add a b ha' hb' ha hb =>
      have e : (⟨a + b, Subring.add_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ + ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_add hp ha hb
    | neg a ha' ha =>
      have e : (⟨-a, Subring.neg_mem _ ha'⟩ : Rmu l) = -⟨a, ha'⟩ := Subtype.ext (by simp)
      rw [e]
      exact frobFix_neg hp ha
    | mul a b ha' hb' ha hb =>
      have e : (⟨a * b, Subring.mul_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ * ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_mul ha hb
  obtain ⟨f, hf, r, hr⟩ := key x hx
  refine ⟨f, hf, r, r.2, ?_⟩
  have h := congrArg Subtype.val hr
  simpa using h

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Polynomial

variable (l : ℕ) [Fact l.Prime]

theorem norm_natCast_Cl (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  rw [← PadicComplex.norm_extends' l (n : ℚ_[l])]
  congr 1
  simp

theorem norm_sub_le_max_Cl (a b : ℂ_[l]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ :=
  by simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max a (-b)

theorem norm_l_Cl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_Cl, Padic.norm_p]

theorem norm_natCast_Cl_of_not_dvd {n : ℕ} (hn : ¬ l ∣ n) : ‖(n : ℂ_[l])‖ = 1 := by
  rw [norm_natCast_Cl, Padic.norm_natCast_eq_one_iff]
  exact ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hn

theorem muP_norm {ζ : ℂ_[l]} (hζ : ζ ∈ muP l) : ‖ζ‖ = 1 := by
  obtain ⟨n, hn, -, h⟩ := hζ
  have : ‖ζ‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

theorem tch_norm_le {ξ : ℂ_[l]} (hξ : ξ ∈ Tch l) : ‖ξ‖ ≤ 1 := by
  rcases hξ with rfl | h
  · simp
  · exact (muP_norm l h).le

theorem tch_mul {ξ ξ' : ℂ_[l]} (h : ξ ∈ Tch l) (h' : ξ' ∈ Tch l) : ξ * ξ' ∈ Tch l := by
  rcases h with rfl | ⟨n, hn, hln, hζ⟩
  · rw [zero_mul]; exact Set.mem_insert _ _
  rcases h' with rfl | ⟨m, hm, hlm, hζ'⟩
  · rw [mul_zero]; exact Set.mem_insert _ _
  refine Set.mem_insert_of_mem _ ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  · intro hd
    rcases ((Fact.out : l.Prime).dvd_mul).1 hd with h1 | h1
    · exact hln h1
    · exact hlm h1
  · rw [mul_pow, pow_mul, hζ, one_pow, one_mul, mul_comm n m, pow_mul, hζ', one_pow]

theorem tch_inv {ξ : ℂ_[l]} (h : ξ ∈ Tch l) : ξ⁻¹ ∈ Tch l := by
  rcases h with rfl | ⟨n, hn, hln, hζ⟩
  · rw [inv_zero]; exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨n, hn, hln, by rw [inv_pow, hζ, inv_one]⟩

theorem tch_near (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (f : ℕ) (hf : 0 < f) (r : ℝ) (hr : r < 1)
    (h : ‖x ^ (l ^ f) - x‖ ≤ r) : ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ r := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hq : 2 ≤ l ^ f := le_trans hl (Nat.le_self_pow hf.ne' l)
  obtain ⟨m, hm⟩ : ∃ m, l ^ f = m + 1 := ⟨l ^ f - 1, by omega⟩
  have hm0 : 0 < m := by omega
  have hlm : ¬ l ∣ m := by
    intro hd
    have h1 : l ∣ m + 1 := hm ▸ dvd_pow_self l hf.ne'
    have h2 : l ∣ 1 := (Nat.dvd_add_right hd).1 h1
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h2)
  by_cases hsmall : ‖x‖ ≤ r
  · exact ⟨0, Set.mem_insert _ _, by simpa using hsmall⟩
  push Not at hsmall
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) h
  have hx1 : ‖x‖ = 1 := by
    have h1 : ‖x‖ ≤ max ‖x ^ (l ^ f)‖ ‖x ^ (l ^ f) - x‖ := by
      calc ‖x‖ = ‖x ^ (l ^ f) - (x ^ (l ^ f) - x)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le_max_Cl l _ _
    have h2 : ‖x‖ ≤ ‖x‖ ^ (l ^ f) := by
      rw [← norm_pow]
      rcases le_max_iff.1 h1 with h3 | h3
      · exact h3
      · linarith
    by_contra hne
    have hlt : ‖x‖ < 1 := lt_of_le_of_ne hx hne
    have hpos : 0 < ‖x‖ := lt_of_le_of_lt hr0 hsmall
    have := pow_lt_self_of_lt_one₀ hpos hlt (by omega : 1 < l ^ f)
    linarith
  have hxm : ‖x ^ m - 1‖ ≤ r := by
    have e : x ^ (l ^ f) - x = x * (x ^ m - 1) := by rw [hm]; ring
    rwa [e, norm_mul, hx1, one_mul] at h
  obtain ⟨ζ, hζroot, hζ⟩ := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_root_near l (X ^ m - C 1)
    (monic_X_pow_sub_C 1 hm0.ne') x
    (by simp only [eval_sub, eval_pow, eval_X, eval_C]; exact lt_of_le_of_lt hxm hr)
  have hζm : ζ ^ m = 1 := by
    have : ζ ^ m - 1 = 0 := by simpa using hζroot
    exact sub_eq_zero.1 this
  have hmu : ζ ∈ muP l := ⟨m, hm0, hlm, hζm⟩
  refine ⟨ζ, Set.mem_insert_of_mem _ hmu, ?_⟩
  have hζ1 : ‖ζ‖ = 1 := muP_norm l hmu
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ1
  have e1 : x - ζ = ζ * (x * ζ⁻¹ - 1) := by
    rw [mul_sub, mul_one, mul_comm x ζ⁻¹, ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  have e2 : x ^ m - 1 = (∑ i ∈ Finset.range m, (x * ζ⁻¹) ^ i) * (x * ζ⁻¹ - 1) := by
    rw [geom_sum_mul, mul_pow, inv_pow, hζm, inv_one, mul_one]
  have hy : ‖x * ζ⁻¹ - 1‖ = ‖x - ζ‖ := by rw [e1, norm_mul, hζ1, one_mul]
  rw [e2, norm_mul, ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_geom_sum_eq_one l (hy ▸ hζ)
    (norm_natCast_Cl_of_not_dvd l hlm), one_mul, hy] at hxm
  exact hxm

end ReciprocityTheory.ChartRestriction.L1
end
end
