module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle501
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.ValEx

theorem nat_bound (p N m : ℕ) (hp : 2 ≤ p) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ a v : ℕ, M ≤ a → p ^ v ≤ a → N * (m + v) ≤ a := by
  set T := 2 * N + m + 1 with hT
  have hT2 : T < 2 ^ T := Nat.lt_two_pow_self
  have hA : ∀ v, 2 * T ≤ v → N * (m + v) ≤ 2 ^ v := by
    intro v hv
    induction v, hv using Nat.le_induction with
    | base =>
      have hNT : N ≤ T := by omega
      have h1 : N * (m + 2 * T) ≤ T * T := by nlinarith [Nat.mul_le_mul_right m hNT]
      have h2 : T * T ≤ 2 ^ T * 2 ^ T := Nat.mul_le_mul hT2.le hT2.le
      calc N * (m + 2 * T) ≤ T * T := h1
        _ ≤ 2 ^ T * 2 ^ T := h2
        _ = 2 ^ (2 * T) := by rw [← pow_add, two_mul]
    | succ v hv ih =>
      have h3 : N ≤ 2 ^ v := by
        have : 2 ^ T ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [pow_succ]; nlinarith
  refine ⟨N * (m + 2 * T) + 1, by omega, fun a v ha hv => ?_⟩
  by_cases hvK : 2 * T ≤ v
  · calc N * (m + v) ≤ 2 ^ v := hA v hvK
      _ ≤ p ^ v := Nat.pow_le_pow_left hp v
      _ ≤ a := hv
  · have : N * (m + v) ≤ N * (m + 2 * T) := Nat.mul_le_mul_left _ (by omega)
    omega

def img (B : Type) {Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] (p m : ℕ) : AddSubgroup Q where
  carrier := {x | ∃ b : B, x = algebraMap B Q ((p : B) ^ m * b)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [mul_add, map_add (f := _)]⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by rw [mul_neg, map_neg]⟩

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type} [Fintype σ] [DecidableEq σ]

def box (σ : Type) [Fintype σ] (n : ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => n

def psum (z : σ → B) (f : MvPowerSeries σ Q) (n : ℕ) : Q :=
  MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q (box σ n) f)

theorem psum_eq (z : σ → B) (f : MvPowerSeries σ Q) (n : ℕ) :
    psum z f n = ∑ α ∈ Finset.Iic (box σ n),
      coeff α f * algebraMap B Q (α.prod fun i e => z i ^ e) := by

  simp only [psum, trunc', truncFinset_apply, map_sum, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_finsuppProd]
  simp [map_pow]

theorem exists_lt_of_not_mem_box {n : ℕ} {α : σ →₀ ℕ} (h : α ∉ Finset.Iic (box σ n)) :
    ∃ i, n < α i := by
  simpa [box, Finset.mem_Iic, Finsupp.le_def] using h

theorem box_mono {n n' : ℕ} (h : n ≤ n') : Finset.Iic (box σ n) ⊆ Finset.Iic (box σ n') :=
  Finset.Iic_subset_Iic.2 (Finsupp.le_def.2 fun i => by simpa [box] using h)

theorem term_mem (p : ℕ) [hp : Fact p.Prime] (hunit : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B))
    (z : σ → B) (hz : ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) (m : ℕ) :
    ∃ M : ℕ, ∀ (α : σ →₀ ℕ) (i : σ), M ≤ α i →
      coeff α f * algebraMap B Q (α.prod fun i e => z i ^ e) ∈ img B p m := by
  choose Nf hNf using hz
  set N := ∑ i, Nf i
  have hN : ∀ i, (p : B) ∣ z i ^ N := fun i => (hNf i).trans
    (pow_dvd_pow _ (Finset.single_le_sum (fun j _ => Nat.zero_le (Nf j)) (Finset.mem_univ i)))
  obtain ⟨M, hM1, hM⟩ := nat_bound p N m hp.out.two_le
  refine ⟨M, fun α i hi => ?_⟩
  have ha0 : α i ≠ 0 := by omega
  obtain ⟨v, u, hu, hau⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha0 p hp.out.ne_one
  have hcop : Nat.Coprime u p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu)
  obtain ⟨U, hU⟩ := hunit u hcop
  have hle : N * (m + v) ≤ α i := hM (α i) v hi (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) ⟨u, hau⟩)
  have hdz : (p : B) ^ (m + v) ∣ z i ^ (α i) :=
    (pow_dvd_pow_of_dvd (hN i) (m + v)).trans (by rw [← pow_mul]; exact pow_dvd_pow _ hle)
  have hprod : z i ^ (α i) ∣ α.prod fun j e => z j ^ e := by
    have hi' : i ∈ α.support := Finsupp.mem_support_iff.2 ha0
    unfold Finsupp.prod
    exact Finset.dvd_prod_of_mem (fun j => z j ^ α j) hi'
  obtain ⟨r, hr⟩ := hdz.trans hprod
  obtain ⟨b, -, hb⟩ := hf α i
  refine ⟨b * ↑U⁻¹ * r, ?_⟩
  rw [hr]
  rw [hau] at hb
  have hUU : (u : Q) * algebraMap B Q (↑U⁻¹ : B) = 1 := by
    rw [← map_natCast (algebraMap B Q), ← map_mul, ← hU, Units.mul_inv, map_one]
  simp only [map_mul, map_pow, map_natCast]
  push_cast at hb
  linear_combination ((p : Q) ^ m * algebraMap B Q (↑U⁻¹ : B) * algebraMap B Q r) * hb -
    (coeff α f * (p : Q) ^ (m + v) * algebraMap B Q r) * hUU

theorem cauchy (p : ℕ) [Fact p.Prime] (hunit : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B))
    (z : σ → B) (hz : ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) (m : ℕ) :
    ∃ M : ℕ, ∀ n n' : ℕ, M ≤ n → n ≤ n' → psum z f n' - psum z f n ∈ img B p m := by
  obtain ⟨M, hM⟩ := term_mem p hunit z hz f hf m
  refine ⟨M, fun n n' hn hnn' => ?_⟩
  rw [psum_eq, psum_eq, ← Finset.sum_sdiff (box_mono hnn'), add_sub_cancel_right]
  refine AddSubgroup.sum_mem _ fun α hα => ?_
  obtain ⟨i, hi⟩ := exists_lt_of_not_mem_box (Finset.mem_sdiff.1 hα).2
  exact hM α i (by omega)

end GlobalTheory.QLog.ValEx

namespace GlobalTheory.QLog


open ValEx in
theorem existsUnique_hasVal_of_dIn : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ]
    [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) →
    ∀ f : MvPowerSeries σ Q, DIn (⊤ : Ideal B) f → ∃! q : Q, HasVal p z f q := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz f hf
  haveI := hF.complete
  have hI : ∀ (k : ℕ) (x : B), x ∈ ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B) ↔
      ∃ e, x = (p : B) ^ k * e := by
    intro k x
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨e, he⟩; exact ⟨e, by rw [← he, mul_comm]⟩
    · rintro ⟨e, he⟩; exact ⟨e, by rw [he, mul_comm]⟩
  choose M hM using cauchy p hF.unit_coprime z hz f hf
  set K : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1), M k with hK
  have hMK : ∀ m, M m ≤ K m := fun m =>
    Finset.single_le_sum (fun k _ => Nat.zero_le (M k)) (Finset.mem_range.2 (Nat.lt_succ_self m))
  have hKmono : Monotone K := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))
  have h0 : ∀ n, psum z f (K n) - psum z f (K 0) ∈ img B p 0 := fun n =>
    hM 0 (K 0) (K n) (hMK 0) (hKmono (Nat.zero_le n))
  choose b hb using h0
  have hcau : ∀ {k n : ℕ}, k ≤ n →
      b k ≡ b n [SMOD ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B)] := by
    intro k n hkn
    rw [SModEq.sub_mem, hI]
    obtain ⟨e, he⟩ := hM k (K k) (K n) (hMK k) (hKmono hkn)
    refine ⟨-e, hF.inj ?_⟩
    have hbk := hb k
    have hbn := hb n
    simp only [pow_zero, one_mul, map_sub, map_mul, map_neg, map_pow, map_natCast] at hbk hbn he ⊢
    linear_combination hbn - hbk - he
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' b hcau
  have huniq : ∀ q1 q2, HasVal p z f q1 → HasVal p z f q2 → q1 = q2 := by
    intro q1 q2 h1 h2
    have hd : ∀ m, ∃ e : B, q1 - q2 = algebraMap B Q ((p : B) ^ m * e) := by
      intro m
      obtain ⟨N1, hN1⟩ := h1 m
      obtain ⟨N2, hN2⟩ := h2 m
      obtain ⟨e1, he1⟩ := hN1 (max N1 N2) (le_max_left _ _)
      obtain ⟨e2, he2⟩ := hN2 (max N1 N2) (le_max_right _ _)
      exact ⟨e1 - e2, by rw [mul_sub, map_sub, ← he1, ← he2]; ring⟩
    obtain ⟨c, hc⟩ := hd 0
    have hc0 : c = 0 := by
      refine IsHausdorff.haus' (I := Ideal.span {(p : B)}) c fun n => ?_
      rw [SModEq.sub_mem, sub_zero, hI]
      obtain ⟨e, he⟩ := hd n
      exact ⟨e, hF.inj (by rw [← he, hc, pow_zero, one_mul])⟩
    rw [← sub_eq_zero, hc, hc0, mul_zero, map_zero]
  have hq : HasVal p z f (psum z f (K 0) + algebraMap B Q L) := fun m => ⟨K m, fun N' hN' => by
    obtain ⟨e1, he1⟩ := (hI m _).1 (SModEq.sub_mem.1 (hL m))
    obtain ⟨e2, he2⟩ := hM m (K m) N' (hMK m) hN'
    have hbm := hb m
    have he1' := congrArg (algebraMap B Q) he1
    refine ⟨-e1 - e2, ?_⟩
    change psum z f (K 0) + algebraMap B Q L - psum z f N' = _
    simp only [pow_zero, one_mul, map_sub, map_mul, map_neg, map_pow, map_natCast] at hbm he1' he2 ⊢
    linear_combination -hbm - he1' - he2⟩
  exact ⟨_, hq, fun q' hq' => huniq _ _ hq' hq⟩

end GlobalTheory.QLog
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.HasValCong

open scoped Nat

section Ring

variable {B : Type} [CommRing B]

theorem pow_eq_pow_factorization_mul (p : ℕ) (hp : p.Prime) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) :
    ∀ n : ℕ, 0 < n → ∀ x ∈ J, ∃ y ∈ J, x ^ n = (p : B) ^ ((n)!.factorization p) * y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hx
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hmn : m < p * m := by
        have := hp.two_le
        nlinarith
      obtain ⟨y, hy, hxy⟩ := hJ x hx
      obtain ⟨y', hy', hyy⟩ := ih m hmn hm y hy
      refine ⟨y', hy', ?_⟩
      rw [Nat.factorization_factorial_mul hp, pow_mul, hxy, mul_pow, hyy, pow_add]
      ring
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact ⟨x, hx, by simp⟩
      obtain ⟨y, hy, hxy⟩ := ih k (by omega) hk x hx
      refine ⟨x * y, J.mul_mem_left x hy, ?_⟩
      have h0 : (k + 1).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
      rw [Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero k),
        Finsupp.coe_add, Pi.add_apply, h0, zero_add, pow_succ, hxy]
      ring

theorem pow_eq_factorial_mul (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (n : ℕ) (hn : 0 < n) (x : B) (hx : x ∈ J) :
    ∃ y ∈ J, x ^ n = ((n ! : ℕ) : B) * y := by
  obtain ⟨y, hy, hxy⟩ := pow_eq_pow_factorization_mul p hp J hJ n hn x hx
  obtain ⟨u, hu'⟩ := hu (n ! / p ^ (n !).factorization p)
    (Nat.coprime_ordCompl hp (Nat.factorial_ne_zero n)).symm
  refine ⟨(↑u⁻¹ : B) * y, J.mul_mem_left _ hy, ?_⟩
  have hfac : ((n ! : ℕ) : B) =
      (p : B) ^ (n !).factorization p * ((n ! / p ^ (n !).factorization p : ℕ) : B) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  rw [hxy, hfac, ← hu', mul_assoc, ← mul_assoc (u : B), Units.mul_inv, one_mul]

theorem sum_eq_mul_mem {ι : Type} (s : Finset ι) (c : B) (J : Ideal B) (f : ι → B)
    (h : ∀ i ∈ s, ∃ y ∈ J, f i = c * y) : ∃ y ∈ J, ∑ i ∈ s, f i = c * y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨y, hy, e⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨y', hy', e'⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact ⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', mul_add]⟩

theorem add_pow_sub_pow (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (a j : B) (hj : j ∈ J) (n : ℕ) :
    ∃ y ∈ J, (a + j) ^ n - a ^ n = (n : B) * y := by
  rcases n with _ | n
  · exact ⟨0, J.zero_mem, by simp⟩
  rw [add_comm a j, add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
  rw [add_sub_cancel_right]
  apply sum_eq_mul_mem
  intro k _
  obtain ⟨y, hy, hjy⟩ := pow_eq_factorial_mul p hp hu J hJ (k + 1) (Nat.succ_pos k) j hj
  refine ⟨((n.descFactorial k : ℕ) : B) * a ^ (n + 1 - (k + 1)) * y, J.mul_mem_left _ hy, ?_⟩
  have h : (n + 1).choose (k + 1) * (k + 1)! = (n + 1) * n.descFactorial k := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ]
  have h' : (((n + 1).choose (k + 1) : ℕ) : B) * (((k + 1)! : ℕ) : B) =
      ((n + 1 : ℕ) : B) * ((n.descFactorial k : ℕ) : B) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, h]
  rw [hjy]
  linear_combination (a ^ (n + 1 - (k + 1)) * y) * h'

end Ring

section Monomial

variable {B : Type} [CommRing B] {σ : Type}

theorem prod_pow_sub_prod_pow (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (α : σ → ℕ) (s : Finset σ) :
    ∃ b : σ → B, (∀ i, b i ∈ J) ∧
      ∏ i ∈ s, z i ^ α i - ∏ i ∈ s, z' i ^ α i = ∑ i ∈ s, (α i : B) * b i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ => J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨b, hb, e⟩ := ih
    obtain ⟨y, hy, ey⟩ := add_pow_sub_pow p hp hu J hJ (z' i) (z i - z' i) (hz i) (α i)
    have hzz : z' i + (z i - z' i) = z i := by ring
    rw [hzz] at ey
    refine ⟨Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k), ?_, ?_⟩
    · intro k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self]
        exact J.mul_mem_right _ hy
      · rw [Function.update_of_ne hk]
        exact J.mul_mem_left _ (hb k)
    · rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, Function.update_self]
      have h1 : ∑ k ∈ s, (α k : B) *
          Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k) k =
          z' i ^ α i * ∑ k ∈ s, (α k : B) * b k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hi hk)]
        ring
      rw [h1]
      linear_combination (∏ k ∈ s, z k ^ α k) * ey + z' i ^ α i * e

theorem sum_eq_map_mem {Q : Type} [CommRing Q] [Algebra B Q] {ι : Type} (s : Finset ι)
    (J : Ideal B) (f : ι → Q) (h : ∀ i ∈ s, ∃ b ∈ J, f i = algebraMap B Q b) :
    ∃ b ∈ J, ∑ i ∈ s, f i = algebraMap B Q b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨y, hy, e⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨y', hy', e'⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact ⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', map_add (f := _)]⟩

variable [Fintype σ] {Q : Type} [CommRing Q] [Algebra B Q]

theorem monomial_val_sub (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (α : σ →₀ ℕ) (a : Q) (ha : ∀ i, ∃ c : B, (α i : Q) * a = algebraMap B Q c) :
    ∃ b ∈ J, a * (∏ i, algebraMap B Q (z i) ^ α i) - a * ∏ i, algebraMap B Q (z' i) ^ α i =
      algebraMap B Q b := by
  choose c hc using ha
  obtain ⟨b, hb, e⟩ := prod_pow_sub_prod_pow p hp hu J hJ z z' hz α Finset.univ
  refine ⟨∑ i, b i * c i, J.sum_mem (fun i _ => J.mul_mem_right _ (hb i)), ?_⟩
  have e' := congrArg (algebraMap B Q) e

  simp only [map_sub, map_prod, map_pow, map_sum, map_mul, map_natCast] at e'

  rw [← mul_sub, e', Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← hc i]
  ring

theorem eval_sub_eval (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (P : MvPolynomial σ Q)
    (hP : ∀ (α : σ →₀ ℕ) i, ∃ c : B, (α i : Q) * P.coeff α = algebraMap B Q c) :
    ∃ b ∈ J, MvPolynomial.eval (fun i => algebraMap B Q (z i)) P -
      MvPolynomial.eval (fun i => algebraMap B Q (z' i)) P = algebraMap B Q b := by

  rw [P.as_sum, map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply sum_eq_map_mem
  intro v _
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  exact monomial_val_sub p hp hu J hJ z z' hz v (P.coeff v) (hP v)

end Monomial

theorem hasVal_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ]
    [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ J : Ideal B,
    (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (z' : σ → B) (f : MvPowerSeries σ Q) (q q' : Q),
    (∀ i, z i - z' i ∈ J) → DIn (⊤ : Ideal B) f → HasVal p z f q → HasVal p z' f q' →
    ∀ m : ℕ, ∃ b ∈ J, ∃ b' : B, q - q' = algebraMap B Q (b + p ^ m * b') := by
  intro p hpf B O Q _ _ _ _ θ hF σ _ _ z _ J hJ z' f q q' hzz hD hv hv' m
  have hp : p.Prime := hpf.out
  obtain ⟨N1, h1⟩ := hv m
  obtain ⟨N2, h2⟩ := hv' m
  obtain ⟨b1, e1⟩ := h1 (max N1 N2) (le_max_left _ _)
  obtain ⟨b2, e2⟩ := h2 (max N1 N2) (le_max_right _ _)
  have hP : ∀ (α : σ →₀ ℕ) i, ∃ c : B, (α i : Q) *
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => max N1 N2) f).coeff α =
        algebraMap B Q c := by
    intro α i
    rw [coeff_trunc']
    split_ifs
    · obtain ⟨c, -, hc⟩ := hD α i
      exact ⟨c, hc⟩
    · exact ⟨0, by simp⟩
  obtain ⟨b, hb, e⟩ := eval_sub_eval p hp hF.unit_coprime J hJ z z' hzz _ hP
  refine ⟨b, hb, b1 - b2, ?_⟩
  simp only [map_add (f := _), map_mul, map_sub, map_pow, map_natCast] at e1 e2 ⊢
  linear_combination e1 - e2 + e

end GlobalTheory.HasValCong
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem IsFrame.isLocalization_away {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O]
    [Algebra B Q] {θ : B →+* O} (h : IsFrame p Q θ) : IsLocalization.Away (p : B) Q := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, k, rfl⟩
    simpa [map_pow, map_natCast] using h.unit_p.pow k
  · intro q
    obtain ⟨k, b, hb⟩ := h.denom q
    refine ⟨⟨b, ⟨(p : B) ^ k, k, rfl⟩⟩, ?_⟩
    simp only [map_pow, map_natCast]
    rw [← hb, mul_comm]
  · intro x y hxy
    exact ⟨1, by simpa using h.inj hxy⟩

theorem frame_fraction_map : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∃ Θ : Q →+* C, ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b) := by
  intro p _ B O Q _ _ _ _ θ hQ C _ _ hC
  haveI := hQ.isLocalization_away
  refine ⟨IsLocalization.Away.lift (p : B) (g := (algebraMap O C).comp θ) ?_, fun b => ?_⟩
  · simpa [map_natCast] using hC.unit_p
  · exact IsLocalization.Away.lift_eq (p : B) _ b

end GlobalTheory.QLog
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SubstSub

theorem coeff_subst_up_mem : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] (S : Submodule B Q) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), (∀ i, constantCoeff (u i) = 0) → (∀ α, coeff α f ∈ S) → ∀ β, coeff β (subst (up Q u) f) ∈ S := by
  intro B Q _ _ _ σ τ _ S f u hu hf β
  have hc : ∀ i, constantCoeff (up Q u i) = 0 := fun i => by
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu, map_zero]
  have ha : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero hc
  rw [coeff_subst ha]
  refine finsum_induction (fun x => x ∈ S) S.zero_mem (fun x y hx hy => S.add_mem hx hy) ?_
  intro d
  have hp : (d.prod fun s e => (up Q u s) ^ e) = map (algebraMap B Q) (d.prod fun s e => (u s) ^ e) := by
    simp only [up, Finsupp.prod, map_prod, map_pow]
  simp only [hp, coeff_map, smul_eq_mul]
  rw [mul_comm, ← Algebra.smul_def]
  exact S.smul_mem _ (hf d)

end GlobalTheory.SubstSub
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

theorem _root_.GlobalTheory.T.coeff_formalGroupLawEvalPoints_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type} (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (op μ u v i) = coeff β (u i + v i) := by
  first | exact @GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one | exact GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one | (intros; apply GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one <;> assumption)
end
