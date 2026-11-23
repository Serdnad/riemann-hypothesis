module

public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

section Weight

variable {A : Type} [CommRing A]

def wI (L Q : A) (W e : ℕ) : Ideal A :=
  Ideal.span {z | ∃ a b : ℕ, e ≤ a * W + b ∧ z = L ^ a * Q ^ b}

theorem wI_mul (L Q : A) (W : ℕ) {e e' : ℕ} {z z' : A} (hz : z ∈ wI L Q W e)
    (hz' : z' ∈ wI L Q W e') : z * z' ∈ wI L Q W (e + e') := by
  have hle : wI L Q W e * wI L Q W e' ≤ wI L Q W (e + e') := by
    unfold wI
    rw [Ideal.span_mul_span']
    apply Ideal.span_mono
    rintro _ ⟨x, ⟨a, b, hab, rfl⟩, y, ⟨a', b', hab', rfl⟩, rfl⟩
    refine ⟨a + a', b + b', ?_, by ring⟩
    rw [add_mul]
    linarith
  exact hle (Ideal.mul_mem_mul hz hz')

theorem wI_zero (L Q : A) (W : ℕ) (z : A) : z ∈ wI L Q W 0 := by
  have h1 : (1 : A) ∈ wI L Q W 0 := Ideal.subset_span ⟨0, 0, Nat.zero_le _, by simp⟩
  simpa using Ideal.mul_mem_left _ z h1

theorem wI_pow (L Q : A) (W : ℕ) {e : ℕ} {z : A} (hz : z ∈ wI L Q W e) (n : ℕ) :
    z ^ n ∈ wI L Q W (n * e) := by
  induction n with
  | zero => simpa using wI_zero L Q W 1
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact wI_mul L Q W ih hz

theorem wI_prod (L Q : A) (W : ℕ) (f : ℕ → A) (e : ℕ → ℕ) (j : ℕ)
    (h : ∀ k < j, f k ∈ wI L Q W (e k)) :
    ∏ k ∈ Finset.range j, f k ∈ wI L Q W (∑ k ∈ Finset.range j, e k) := by
  induction j with
  | zero => simpa using wI_zero L Q W 1
  | succ j ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    exact wI_mul L Q W (ih fun k hk => h k (by omega)) (h j (by omega))

theorem wI_le (L Q : A) (W e c y : ℕ) (hW : 1 ≤ W) (h : c * W + y ≤ e + 1) :
    wI L Q W e ≤ Ideal.span {L ^ c, Q ^ y} := by
  rw [wI, Ideal.span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  by_cases hca : c ≤ a
  · have e1 : L ^ a * Q ^ b = L ^ c * (L ^ (a - c) * Q ^ b) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hca]
    rw [SetLike.mem_coe, e1]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  · push_neg at hca
    have h1 : (a + 1) * W ≤ c * W := Nat.mul_le_mul_right W hca
    rw [add_mul, one_mul] at h1
    have hyb : y ≤ b := by linarith
    have e1 : L ^ a * Q ^ b = Q ^ y * (L ^ a * Q ^ (b - y)) := by
      rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hyb]
    rw [SetLike.mem_coe, e1]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end Weight

theorem geom_nat (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (j : ℕ) :
    (∑ k ∈ Finset.range j, (ℓ - 1) * ℓ ^ k) + 1 = ℓ ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, add_right_comm, ih, pow_succ]
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring

theorem sign_character_at_j_holds : StatSigJ := by
  intro A _ ℓ hℓ x U p j y r c hj hr hp hcy
  have hW : 1 ≤ ℓ ^ (j - 1) := Nat.one_le_pow _ _ (by omega)
  have hpk : ∀ k < j, p k ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (ℓ ^ k) := by
    intro k hk
    refine (Ideal.span_le.mpr ?_) (hp k hk)
    intro z hz
    rcases hz with rfl | rfl
    · refine Ideal.subset_span ⟨1, 0, ?_, by simp⟩
      simp only [one_mul, add_zero]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    · exact Ideal.subset_span ⟨0, ℓ ^ k, by simp, by simp⟩
  have hP : ∏ k ∈ Finset.range j, p k ^ (ℓ - 1) ∈
      wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (ℓ ^ j - 1) := by
    have h1 := wI_prod (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (fun k => p k ^ (ℓ - 1))
      (fun k => (ℓ - 1) * ℓ ^ k) j (fun k hk => by
        have h2 := wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (hpk k hk) (ℓ - 1)
        exact h2)
    have hg := geom_nat ℓ (by omega) j
    have e : ∑ k ∈ Finset.range j, (ℓ - 1) * ℓ ^ k = ℓ ^ j - 1 := by omega
    rw [e] at h1
    exact h1
  have hx : x ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1 := by
    have hQ : x + (ℓ : A) ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1 :=
      Ideal.subset_span ⟨0, 1, by simp, by simp⟩
    have hL : (ℓ : A) ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1 :=
      Ideal.subset_span ⟨1, 0, by simpa using hW, by simp⟩
    have h := Ideal.sub_mem _ hQ hL
    rwa [add_sub_cancel_right] at h
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hmain := wI_mul (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1))
    (wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) hx r') (wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) hP (r' + 1))
  have hN : 1 ≤ ℓ ^ j := Nat.one_le_pow _ _ (by omega)
  have e2 : r' * 1 + (r' + 1) * (ℓ ^ j - 1) + 1 = (r' + 1) * ℓ ^ j := by
    rw [Nat.mul_sub_one]
    have h5 : (r' + 1) * 1 ≤ (r' + 1) * ℓ ^ j := Nat.mul_le_mul_left _ hN
    rw [mul_one] at h5
    omega
  have hin := wI_le (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) _ c y hW (by rw [e2]; exact hcy) hmain
  have hfin : x * (x ^ r' * (∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1)) ∈
      Ideal.span {(ℓ : A) ^ c * x, x * (x + (ℓ : A)) ^ y} := by
    have h1 := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) hin
    rw [Ideal.span_mul_span'] at h1
    refine Ideal.span_mono ?_ h1
    rintro _ ⟨u, hu, v, hv, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    rcases hv with rfl | rfl
    · exact Or.inl (mul_comm _ _)
    · exact Or.inr rfl
  have e3 : (U * x * ∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1) =
      U ^ (r' + 1) * (x * (x ^ r' * (∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1))) := by ring
  rw [e3]
  exact Ideal.mul_mem_left _ _ hfin

theorem residue_series_expansion_holds : StatResSeries := by
  intro n _ ℓ c s H hℓ hc hH hs i
  have hq : 0 < ℓ - 1 := by linarith
  have hq1 : 1 < ℓ - 1 := by linarith
  set f : ℕ → ℝ := fun a => (H (i + ((a + 1 : ℕ) : ZMod n)) + c + 3) / (ℓ - 1) ^ a with hf
  have hHle : ∀ k, H k ≤ ∑ k', H k' := fun k =>
    Finset.single_le_sum (f := H) (fun k _ => hH k) (Finset.mem_univ k)
  have hf0 : ∀ a, 0 ≤ f a := fun a =>
    div_nonneg (by linarith [hH (i + ((a + 1 : ℕ) : ZMod n))]) (pow_nonneg hq.le _)
  have hsum : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun a => ?_)
      ((summable_geometric_of_lt_one (inv_nonneg.mpr hq.le) (inv_lt_one_of_one_lt₀ hq1)).mul_left
        ((∑ k', H k') + c + 3))
    simp only [hf]
    rw [inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by linarith [hHle (i + ((a + 1 : ℕ) : ZMod n))])
      (pow_nonneg hq.le _)
  have hunroll : ∀ N : ℕ, s i ≤ ∑ a ∈ Finset.range N, f a + s (i + (N : ZMod n)) / (ℓ - 1) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hk := hs (i + ((N + 1 : ℕ) : ZMod n))
      have e : i + ((N + 1 : ℕ) : ZMod n) - 1 = i + (N : ZMod n) := by push_cast; ring
      rw [e] at hk
      have hpos : 0 < (ℓ - 1) ^ N := pow_pos hq N
      have h2 : s (i + (N : ZMod n)) / (ℓ - 1) ^ N ≤
          f N + s (i + ((N + 1 : ℕ) : ZMod n)) / (ℓ - 1) ^ (N + 1) := by
        have h3 := div_le_div_of_nonneg_right hk hpos.le
        rw [add_div, div_div, ← pow_succ'] at h3
        simpa only [hf] using h3
      rw [Finset.sum_range_succ]
      linarith
  have hrem : Filter.Tendsto (fun N : ℕ => s (i + (N : ZMod n)) / (ℓ - 1) ^ N) Filter.atTop
      (nhds 0) := by
    refine squeeze_zero_norm (a := fun N => (∑ k, |s k|) * ((ℓ - 1)⁻¹) ^ N) (fun N => ?_) ?_
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hq N), inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (Finset.single_le_sum (f := fun k => |s k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ _)) (pow_nonneg hq.le _)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hq.le)
        (inv_lt_one_of_one_lt₀ hq1)).const_mul (∑ k, |s k|)
  have hlim : Filter.Tendsto (fun N : ℕ => s i - s (i + (N : ZMod n)) / (ℓ - 1) ^ N)
      Filter.atTop (nhds (s i - 0)) := tendsto_const_nhds.sub hrem
  have hfin := le_of_tendsto' hlim (fun N => by
    have h1 := hunroll N
    have h2 := hsum.sum_le_tsum (Finset.range N) (fun a _ => hf0 a)
    linarith)
  rw [sub_zero] at hfin
  exact hfin

end Formalism.RepresentationBoundsCohomology.N2
end
end

section

namespace Formalism.RepresentationBoundsCohomology.N2.SumVal

open Finset

variable (ℓ : ℕ) [Fact ℓ.Prime]

lemma sum_Ioc_add (n w : ℕ) :
    (∑ k ∈ Ioc n (n + w), padicValNat ℓ k) + padicValNat ℓ n.factorial =
      padicValNat ℓ (n + w).factorial := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega), Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega) (Nat.factorial_ne_zero _), ← ih]
    ring

lemma sum_Ioc_eq (n w : ℕ) :
    (∑ k ∈ Ioc n (n + w), padicValNat ℓ k) =
      padicValNat ℓ w.factorial + padicValNat ℓ ((n + w).choose w) := by
  have h1 := sum_Ioc_add ℓ n w
  have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left w n)
  rw [Nat.add_sub_cancel] at h2
  rw [← h2, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.mul_ne_zero (Nat.choose_pos (Nat.le_add_left w n)).ne'
      (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.choose_pos (Nat.le_add_left w n)).ne' (Nat.factorial_ne_zero _)] at h1
  omega

lemma one_lt_cast : (1 : ℝ) < (ℓ : ℝ) := by
  exact_mod_cast (Fact.out : ℓ.Prime).one_lt

lemma val_factorial_le (w : ℕ) :
    (padicValNat ℓ w.factorial : ℝ) ≤ (w : ℝ) / ((ℓ : ℝ) - 1) := by
  have h := (Fact.out : ℓ.Prime).sub_one_mul_multiplicity_factorial (n := w)
  rw [← Nat.padicValNat_def] at h
  have h' : (ℓ - 1) * padicValNat ℓ w.factorial ≤ w := by rw [h]; exact Nat.sub_le _ _
  have hl := one_lt_cast ℓ
  rw [le_div_iff₀ (by linarith)]
  have e : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (Fact.out : ℓ.Prime).one_lt.le]; simp
  have h2 : (((ℓ - 1) * padicValNat ℓ w.factorial : ℕ) : ℝ) ≤ w := by exact_mod_cast h'
  rw [Nat.cast_mul, e] at h2
  linarith

lemma val_choose_le (N w : ℕ) :
    (padicValNat ℓ (N.choose w) : ℝ) ≤ Real.logb ℓ N := by
  have h1 : padicValNat ℓ (N.choose w) ≤ Nat.log ℓ N := by
    rw [Nat.padicValNat_def, ← Nat.factorization_def _ (Fact.out : ℓ.Prime)]
    exact Nat.factorization_choose_le_log
  calc (padicValNat ℓ (N.choose w) : ℝ) ≤ (Nat.log ℓ N : ℝ) := by exact_mod_cast h1
    _ ≤ Real.logb ℓ N := Real.natLog_le_logb N ℓ

lemma sum_nat_le (n y D : ℕ) (hD : 1 ≤ D) (T : Finset ℕ)
    (hT : ∀ k ∈ T, n < k ∧ k ≤ n + (y + 1) ∧ k ≤ D) :
    ((∑ k ∈ T, padicValNat ℓ k : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  set N' := min (n + (y + 1)) D with hN'
  have hsub : T ⊆ Ioc n N' := fun k hk => by
    obtain ⟨h1, h2, h3⟩ := hT k hk
    exact Finset.mem_Ioc.2 ⟨h1, le_min h2 h3⟩
  have hle : (∑ k ∈ T, padicValNat ℓ k) ≤ ∑ k ∈ Ioc n N', padicValNat ℓ k :=
    Finset.sum_le_sum_of_subset hsub
  have hl := one_lt_cast ℓ
  have hD0 : (0 : ℝ) ≤ Real.logb ℓ D := Real.logb_nonneg hl (by exact_mod_cast hD)
  by_cases hnN : n ≤ N'
  · obtain ⟨w, hw⟩ : ∃ w, N' = n + w := ⟨N' - n, by omega⟩
    rw [hw, sum_Ioc_eq] at hle
    have hwle : w ≤ y + 1 := by have := min_le_left (n + (y + 1)) D; omega
    have hND : n + w ≤ D := by have := min_le_right (n + (y + 1)) D; omega
    have e1 := val_factorial_le ℓ w
    have e2 := val_choose_le ℓ (n + w) w
    have e3 : (w : ℝ) / ((ℓ : ℝ) - 1) ≤ ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hwle) (by linarith)
    have e4 : Real.logb ℓ (n + w : ℕ) ≤ Real.logb ℓ D := by
      rcases Nat.eq_zero_or_pos (n + w) with h0 | h0
      · rw [h0, Nat.cast_zero, Real.logb_zero]; exact hD0
      · exact Real.logb_le_logb_of_le hl (by exact_mod_cast h0) (by exact_mod_cast hND)
    have e5 : ((∑ k ∈ T, padicValNat ℓ k : ℕ) : ℝ) ≤
        (padicValNat ℓ w.factorial : ℝ) + padicValNat ℓ ((n + w).choose w) := by exact_mod_cast hle
    linarith
  · have hE : Ioc n N' = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hE, Finset.sum_empty, Nat.le_zero] at hle
    rw [hle]
    have : (0 : ℝ) ≤ ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) := div_nonneg (by positivity) (by linarith)
    push_cast
    linarith

end Formalism.RepresentationBoundsCohomology.N2.SumVal

namespace Formalism.RepresentationBoundsCohomology.N2

open Finset

private theorem sum_padicValInt_sub_le_of_injective_bound (ℓ : ℕ) [Fact ℓ.Prime] (S' : Finset ℤ) (a : ℤ) (f : ℤ → ℤ)
    (n y D : ℕ) (hD : 1 ≤ D) (hf : ∀ b ∈ S', (n : ℤ) < f b ∧ f b ≤ n + (y + 1) ∧ f b ≤ D)
    (hinj : ∀ b ∈ S', ∀ b' ∈ S', f b = f b' → b = b')
    (hg : ∀ b ∈ S', padicValInt ℓ (a - b) = padicValNat ℓ (f b).toNat) :
    ((∑ b ∈ S', padicValInt ℓ (a - b) : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  have hsum : ∑ b ∈ S', padicValInt ℓ (a - b) =
      ∑ k ∈ S'.image (fun b => (f b).toNat), padicValNat ℓ k := by
    rw [Finset.sum_image]
    · exact Finset.sum_congr rfl hg
    · intro b hb b' hb' h
      have h' : (f b).toNat = (f b').toNat := h
      have h1 := (hf b hb).1
      have h2 := (hf b' hb').1
      exact hinj b hb b' hb' (by omega)
  rw [hsum]
  refine SumVal.sum_nat_le ℓ n y D hD _ ?_
  intro k hk
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hk
  obtain ⟨h1, h2, h3⟩ := hf b hb
  omega

private theorem sum_padicValInt_sub_le_of_lt_forall (ℓ : ℕ) [Fact ℓ.Prime] (m : ℤ) (y D : ℕ) (S' : Finset ℤ) (a : ℤ)
    (hS : S' ⊆ Finset.Icc m (m + y)) (hD : 1 ≤ D) (hSD : ∀ b ∈ S', |a - b| ≤ D)
    (hlt : ∀ b ∈ S', b < a) :
    ((∑ b ∈ S', padicValInt ℓ (a - b) : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  refine sum_padicValInt_sub_le_of_injective_bound ℓ S' a (fun b => a - b) (a - m - y - 1).toNat y D hD ?_ ?_ ?_
  · intro b hb
    have h1 := Finset.mem_Icc.1 (hS hb)
    have h2 := abs_le.1 (hSD b hb)
    have h3 := hlt b hb
    beta_reduce
    omega
  · intro b _ b' _ h
    have h' : a - b = a - b' := h
    omega
  · intro b hb
    have h3 := hlt b hb
    simp only [padicValInt, Nat.padicValNat_def]
    congr 1
    omega

private theorem sum_padicValInt_sub_le_of_gt_forall (ℓ : ℕ) [Fact ℓ.Prime] (m : ℤ) (y D : ℕ) (S' : Finset ℤ) (a : ℤ)
    (hS : S' ⊆ Finset.Icc m (m + y)) (hD : 1 ≤ D) (hSD : ∀ b ∈ S', |a - b| ≤ D)
    (hgt : ∀ b ∈ S', a < b) :
    ((∑ b ∈ S', padicValInt ℓ (a - b) : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  refine sum_padicValInt_sub_le_of_injective_bound ℓ S' a (fun b => b - a) (m - a - 1).toNat y D hD ?_ ?_ ?_
  · intro b hb
    have h1 := Finset.mem_Icc.1 (hS hb)
    have h2 := abs_le.1 (hSD b hb)
    have h3 := hgt b hb
    beta_reduce
    omega
  · intro b _ b' _ h
    have h' : b - a = b' - a := h
    omega
  · intro b hb
    have h3 := hgt b hb
    simp only [padicValInt, Nat.padicValNat_def]
    congr 1
    omega

theorem valuation_sum_at_endpoint : StatSumValEnd := by
  intro ℓ _ m y D S a hS ha hD hSD
  have hS' : S.erase a ⊆ Finset.Icc m (m + y) := (Finset.erase_subset a S).trans hS
  have hSD' : ∀ b ∈ S.erase a, |a - b| ≤ D := fun b hb => hSD b (Finset.mem_of_mem_erase hb)
  rcases ha with ha | ha
  · refine sum_padicValInt_sub_le_of_gt_forall ℓ m y D (S.erase a) a hS' hD hSD' fun b hb => ?_
    have h1 := Finset.mem_Icc.1 (hS' hb)
    have h2 := Finset.ne_of_mem_erase hb
    omega
  · refine sum_padicValInt_sub_le_of_lt_forall ℓ m y D (S.erase a) a hS' hD hSD' fun b hb => ?_
    have h1 := Finset.mem_Icc.1 (hS' hb)
    have h2 := Finset.ne_of_mem_erase hb
    omega

theorem valuation_sum_general_index : StatSumValGen := by
  intro ℓ _ m y D S a hS hD hSD
  have hS' : S.erase a ⊆ Finset.Icc m (m + y) := (Finset.erase_subset a S).trans hS
  have hSD' : ∀ b ∈ S.erase a, |a - b| ≤ D := fun b hb => hSD b (Finset.mem_of_mem_erase hb)
  rw [← Finset.sum_filter_add_sum_filter_not (S.erase a) (fun b => b < a), Nat.cast_add, two_mul]
  apply add_le_add
  · exact sum_padicValInt_sub_le_of_lt_forall ℓ m y D _ a ((Finset.filter_subset _ _).trans hS') hD
      (fun b hb => hSD' b (Finset.mem_of_mem_filter b hb)) (fun b hb => (Finset.mem_filter.1 hb).2)
  · refine sum_padicValInt_sub_le_of_gt_forall ℓ m y D _ a ((Finset.filter_subset _ _).trans hS') hD
      (fun b hb => hSD' b (Finset.mem_of_mem_filter b hb)) (fun b hb => ?_)
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
    have := Finset.ne_of_mem_erase hb1
    omega

end Formalism.RepresentationBoundsCohomology.N2
end
