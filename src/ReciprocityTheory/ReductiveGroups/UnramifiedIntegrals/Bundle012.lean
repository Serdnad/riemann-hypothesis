module

public import Formalism.FormalGroupLog.Statement
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle002
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle010
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle008

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def LeadAt (f : PowerSeries K) (r : ℝ) (i : ℕ) : Prop :=
  0 < r ∧ (∀ n, ‖coeff n f‖ ≤ r) ∧ (∀ n, n < i → ‖coeff n f‖ < r) ∧ ‖coeff i f‖ = r

theorem gauss_norm_add_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem gauss_norm_sum_lt {α : Type} (s : Finset α) (f : α → K) {r : ℝ} (hr : 0 < r)
    (h : ∀ a ∈ s, ‖f a‖ < r) : ‖∑ a ∈ s, f a‖ < r := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hr
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
    exact hle.trans_lt (h i hi)

theorem LeadAt.mul {f g : PowerSeries K} {r s : ℝ} {i j : ℕ} (hf : LeadAt f r i) (hg : LeadAt g s j) :
    LeadAt (f * g) (r * s) (i + j) := by
  obtain ⟨hr, hf1, hf2, hf3⟩ := hf
  obtain ⟨hs, hg1, hg2, hg3⟩ := hg
  have small : ∀ p q : ℕ, (p < i ∨ q < j) → ‖coeff p f * coeff q g‖ < r * s := by
    intro p q hpq
    rw [norm_mul]
    rcases hpq with hp | hq
    · calc ‖coeff p f‖ * ‖coeff q g‖ ≤ ‖coeff p f‖ * s :=
            mul_le_mul_of_nonneg_left (hg1 q) (norm_nonneg _)
        _ < r * s := mul_lt_mul_of_pos_right (hf2 p hp) hs
    · calc ‖coeff p f‖ * ‖coeff q g‖ ≤ r * ‖coeff q g‖ :=
            mul_le_mul_of_nonneg_right (hf1 p) (norm_nonneg _)
        _ < r * s := mul_lt_mul_of_pos_left (hg2 q hq) hr
  refine ⟨mul_pos hr hs, fun n => ?_, fun n hn => ?_, ?_⟩
  · rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_pos hr hs).le fun x _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hf1 _) (hg1 _) (norm_nonneg _) hr.le
  · rw [coeff_mul]
    refine gauss_norm_sum_lt _ _ (mul_pos hr hs) fun x hx => small _ _ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    omega
  · have hmem : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have hlt : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i + j)).erase (i, j), coeff x.1 f * coeff x.2 g‖ < r * s := by
      refine gauss_norm_sum_lt _ _ (mul_pos hr hs) fun x hx => small _ _ ?_
      obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      by_contra hc
      push Not at hc
      exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
    have hij : ‖coeff i f * coeff j g‖ = r * s := by rw [norm_mul, hf3, hg3]
    rw [gauss_norm_add_of_lt (by rwa [hij]), hij]

theorem leadAt_one : LeadAt (1 : PowerSeries K) 1 0 := by
  refine ⟨one_pos, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _), by simp⟩
  rw [coeff_one]
  split_ifs <;> simp

theorem leadAt_C {c : K} (hc : c ≠ 0) : LeadAt (C c : PowerSeries K) ‖c‖ 0 := by
  refine ⟨norm_pos_iff.mpr hc, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _), by simp⟩
  rw [coeff_C]
  split_ifs <;> simp

theorem leadAt_factor {A : PowerSeries K} (hA : IntegralPS A) (hA0 : constantCoeff A = 1) (x : K) :
    ∃ i, i ≤ 2 ∧ LeadAt (A - C x * X ^ 2) (max 1 ‖x‖) i := by
  have hc : ∀ n, coeff n (A - C x * X ^ 2) = coeff n A - if n = 2 then x else 0 := by
    intro n
    rw [map_sub, coeff_C_mul_X_pow]
  by_cases hx : ‖x‖ ≤ 1
  · refine ⟨0, by norm_num, ?_⟩
    rw [max_eq_left hx]
    refine ⟨one_pos, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero _), ?_⟩
    · rw [hc]
      split_ifs
      · rw [sub_eq_add_neg]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA n) (by rw [norm_neg]; exact hx))
      · rw [sub_zero]; exact hA n
    · rw [hc, if_neg (by norm_num), sub_zero, coeff_zero_eq_constantCoeff_apply, hA0, norm_one]
  · push Not at hx
    refine ⟨2, le_rfl, ?_⟩
    rw [max_eq_right hx.le]
    have h2 : ‖coeff 2 A - x‖ = ‖x‖ := by
      rw [sub_eq_neg_add, gauss_norm_add_of_lt (by rw [norm_neg]; exact (hA 2).trans_lt hx), norm_neg]
    refine ⟨one_pos.trans hx, fun n => ?_, fun n hn => ?_, ?_⟩
    · rw [hc]
      split_ifs with h
      · subst h; exact h2.le
      · rw [sub_zero]; exact (hA n).trans hx.le
    · rw [hc, if_neg (by omega), sub_zero]
      exact (hA n).trans_lt hx
    · rw [hc, if_pos rfl, h2]

theorem leadAt_prod {α : Type} (S : Finset α) (x : α → K) {A : PowerSeries K} (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) :
    ∃ i, i ≤ 2 * S.card ∧ LeadAt (∏ P ∈ S, (A - C (x P) * X ^ 2)) (∏ P ∈ S, max 1 ‖x P‖) i := by
  classical
  refine Finset.induction_on S ⟨0, le_rfl, by simpa using leadAt_one⟩ ?_
  intro a T ha ih
  obtain ⟨i, hi, h⟩ := ih
  obtain ⟨j, hj, h'⟩ := leadAt_factor hA hA0 (x a)
  refine ⟨j + i, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem ha]; omega
  · rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact h'.mul h

theorem gauss_bound {α : Type} (S : Finset α) (x : α → K) (A : PowerSeries K) (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) (c : K)
    (hG : IntegralPS (C c * ∏ P ∈ S, (A - C (x P) * X ^ 2))) :
    ‖c‖ * ∏ P ∈ S, max 1 ‖x P‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨i, -, h⟩ := leadAt_prod S x hA hA0
  have hl := (leadAt_C hc).mul h
  rw [← hl.2.2.2]
  exact hG _

theorem gauss_unit {α : Type} (S : Finset α) (x : α → K) (A : PowerSeries K) (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) (c : K) (hc : ‖c‖ * ∏ P ∈ S, max 1 ‖x P‖ = 1) :
    ∃ i, i ≤ 2 * S.card ∧ ‖coeff i (C c * ∏ P ∈ S, (A - C (x P) * X ^ 2))‖ = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨i, hi, h⟩ := leadAt_prod S x hA hA0
  have hl := (leadAt_C hc0).mul h
  exact ⟨0 + i, by omega, hl.2.2.2.trans hc⟩

theorem leadAt_first_unit {g : PowerSeries K} (hg : IntegralPS g) (h : ∃ i, ‖coeff i g‖ = 1) :
    ∃ i₀, (∀ i, ‖coeff i g‖ = 1 → i₀ ≤ i) ∧ LeadAt g 1 i₀ := by
  classical
  refine ⟨Nat.find h, fun i hi => Nat.find_min' h hi, one_pos, hg,
    fun n hn => lt_of_le_of_ne (hg n) (Nat.find_min h hn), Nat.find_spec h⟩

theorem unit_coeff_mul {f g : PowerSeries K} (hf : IntegralPS f) (hg : IntegralPS g)
    (hf0 : ‖constantCoeff f‖ = 1) (N : ℕ) (h : ∃ i, i ≤ N ∧ ‖coeff i g‖ = 1) :
    ∃ i, i ≤ N ∧ ‖coeff i (f * g)‖ = 1 := by
  obtain ⟨i, hiN, hi⟩ := h
  obtain ⟨i₀, hmin, hl⟩ := leadAt_first_unit hg ⟨i, hi⟩
  have hf' : LeadAt f 1 0 := ⟨one_pos, hf, fun n hn => absurd hn (Nat.not_lt_zero _),
    by rw [coeff_zero_eq_constantCoeff_apply, hf0]⟩
  have hm := hf'.mul hl
  refine ⟨0 + i₀, by have := hmin i hi; omega, ?_⟩
  rw [hm.2.2.2, one_mul]

theorem unit_coeff_of_sq {e : PowerSeries K} (he : IntegralPS e) (N : ℕ)
    (h : ∃ i, i ≤ 2 * N ∧ ‖coeff i (e ^ 2)‖ = 1) : ∃ i, i ≤ N ∧ ‖coeff i e‖ = 1 := by
  obtain ⟨i, hiN, hi⟩ := h
  have hex : ∃ j, ‖coeff j e‖ = 1 := by
    by_contra hno
    push Not at hno
    have hlt : ∀ n, ‖coeff n e‖ < 1 := fun n => lt_of_le_of_ne (he n) (hno n)
    have : ‖coeff i (e ^ 2)‖ < 1 := by
      rw [sq, coeff_mul]
      refine gauss_norm_sum_lt _ _ one_pos fun x _ => ?_
      rw [norm_mul]
      calc ‖coeff x.1 e‖ * ‖coeff x.2 e‖ ≤ ‖coeff x.1 e‖ * 1 :=
            mul_le_mul_of_nonneg_left (he _) (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hlt _
    exact this.ne hi
  obtain ⟨j, -, hl⟩ := leadAt_first_unit he hex
  have hm := hl.mul hl
  rw [one_mul, ← sq] at hm
  refine ⟨j, ?_, hl.2.2.2⟩
  by_contra hc
  push Not at hc
  exact (hm.2.2.1 i (by omega)).ne hi

theorem integral_of_sq_eq {e U G : PowerSeries K} (he : IntegralPS e) (he0 : constantCoeff e = 0)
    (hU : IntegralPS U) (hU0 : constantCoeff U = 1) (h : e ^ 2 = X ^ 2 * U * G) : IntegralPS G := by
  obtain ⟨e', rfl⟩ := (PowerSeries.X_dvd_iff).mpr he0
  have he' : IntegralPS e' := fun n => by
    have := he (n + 1)
    rwa [coeff_succ_X_mul] at this
  have h2 : e' ^ 2 = U * G := by
    have hX : (X : PowerSeries K) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [← mul_assoc, ← h]
    ring
  have hUi : IntegralPS U⁻¹ := integralPS_inv hU (by rw [hU0, norm_one])
  have hG : G = U⁻¹ * e' ^ 2 := by
    rw [h2, ← mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [hU0]; exact one_ne_zero), one_mul]
  rw [hG]
  exact integralPS_mul hUi (integralPS_pow he' 2)

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem disc_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ := by
  have hc : c ≠ 0 := h.1
  have hD : DD τ = (E₄ τ ^ 3 - E₆ τ ^ 2) / 1728 := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [g₂_eq h, g₃_eq h, hD]
  field_simp
  ring

theorem jInv_eq_jT {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) : jInv L = jT τ := by
  have hc : c ≠ 0 := h.1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hDD : DD τ ≠ 0 := DD_ne_zero τ
  show 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = E₄ τ ^ 3 / DD τ
  rw [disc_eq h, g₂_eq h]
  field_simp
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem rmu_le_kmu {x : ℂ_[l]} (hx : x ∈ Rmu l) : x ∈ Kmu l := by
  have h : Rmu l ≤ (Kmu l).toSubring := by
    rw [Rmu, Subring.closure_le]
    intro z hz
    exact Subfield.subset_closure hz
  exact h hx

theorem kmu_le_kur {x : ℂ_[l]} (hx : x ∈ Kmu l) : x ∈ MaximalUnramifiedExtension l := (Kmu l).le_topologicalClosure hx

theorem tch_mem_kur {ξ : ℂ_[l]} (hξ : ξ ∈ Tch l) : ξ ∈ MaximalUnramifiedExtension l := by
  rcases Set.mem_insert_iff.mp hξ with rfl | h
  · exact (MaximalUnramifiedExtension l).zero_mem
  · exact kmu_le_kur l (Subfield.subset_closure h)

theorem norm_sub_le_max_padic (x y : ℂ_[l]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.dist_triangle_max x 0 y
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, sub_zero, zero_sub, norm_neg] at h
  exact h

theorem norm_eq_of_norm_sub_lt_max {x y : ℂ_[l]} (h : ‖x - y‖ < max ‖x‖ ‖y‖) : ‖x‖ = ‖y‖ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := norm_sub_le_max_padic l x (x - y)
    rw [sub_sub_cancel] at h1
    rw [max_eq_right hlt.le] at h
    have h2 : max ‖x‖ ‖x - y‖ < ‖y‖ := max_lt hlt h
    linarith
  · have h1 := norm_sub_le_max_padic l y (y - x)
    rw [sub_sub_cancel] at h1
    rw [max_eq_left hgt.le, norm_sub_rev] at h
    have h2 : max ‖y‖ ‖y - x‖ < ‖x‖ := max_lt hgt h
    linarith

private theorem norm_natCast_l_padicComplex_eq_inv : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends (p := l) ((l : ℚ_[l]) : PadicAlgCl l)
  rw [PadicAlgCl.norm_extends, Padic.norm_p] at h
  have e : (((l : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  rw [e] at h
  exact h

theorem norm_prime_pos_complexPadic : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_natCast_l_padicComplex_eq_inv l]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : Nat.Prime l).pos)

theorem norm_prime_lt_one_complexPadic : ‖(l : ℂ_[l])‖ < 1 := by
  rw [norm_natCast_l_padicComplex_eq_inv l]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : Nat.Prime l).one_lt)

theorem kmu_discrete {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero]; exact norm_nonneg _
  obtain ⟨m, a, -, b, -, ha, hb, rfl⟩ := kmu_shape l hx hx0
  have hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [norm_mul, norm_div, ha, hb, norm_zpow]; simp
  rw [hn] at h1 ⊢
  have hm : 1 ≤ m := by
    by_contra hc
    have hm0 : m ≤ 0 := by omega
    have := one_le_zpow_of_nonpos₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm0
    linarith
  calc ‖(l : ℂ_[l])‖ ^ m ≤ ‖(l : ℂ_[l])‖ ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm
    _ = ‖(l : ℂ_[l])‖ := zpow_one _

theorem exists_teichmuller_rep_mod_prime {a : ℂ_[l]} (ha : a ∈ Rmu l) : ∃ ξ ∈ Tch l, ‖a - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨f, hf, r, hr, h⟩ := rmu_frob l a ha
  refine tch_near l a (rmu_norm_le l ha) f hf _ (norm_prime_lt_one_complexPadic l) ?_
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rmu_norm_le l hr)

theorem kmu_rep {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ ≤ 1) :
    ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  rcases lt_or_eq_of_le h1 with h1 | h1
  · exact ⟨0, Set.mem_insert _ _, by rw [sub_zero]; exact kmu_discrete l hx h1⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  obtain ⟨m, a, ha', b, hb', ha, hb, rfl⟩ := kmu_shape l hx hx0
  have hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [norm_mul, norm_div, ha, hb, norm_zpow]; simp
  rw [hn] at h1
  have hm : m = 0 := by
    rcases lt_trichotomy m 0 with h | h | h
    · have := one_lt_zpow_of_neg₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h
      linarith
    · exact h
    · have := zpow_lt_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h
      linarith
  subst hm
  obtain ⟨α, hα, hαa⟩ := exists_teichmuller_rep_mod_prime l ha'
  obtain ⟨β, hβ, hβb⟩ := exists_teichmuller_rep_mod_prime l hb'
  have hβ1 : ‖β‖ = 1 := by
    have h2 : ‖b - β‖ < max ‖b‖ ‖β‖ :=
      lt_of_le_of_lt hβb (lt_of_lt_of_le (norm_prime_lt_one_complexPadic l) (hb ▸ le_max_left _ _))
    rw [← norm_eq_of_norm_sub_lt_max l h2, hb]
  have hb0 : b ≠ 0 := by intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hβ0 : β ≠ 0 := by intro h; rw [h, norm_zero] at hβ1; exact zero_ne_one hβ1
  refine ⟨α * β⁻¹, tch_mul l hα (tch_inv l hβ), ?_⟩
  have he : (l : ℂ_[l]) ^ (0 : ℤ) * (a / b) - α * β⁻¹
      = ((a - α) * β - α * (b - β)) / (b * β) := by
    field_simp
    ring
  rw [he, norm_div, norm_mul b, hb, hβ1, mul_one, div_one]
  refine (norm_sub_le_max_padic l _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, hβ1, mul_one]; exact hαa
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (tch_norm_le l hα)).trans hβb

theorem kur_approx {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (e : ℝ) (he : 0 < e) :
    ∃ y ∈ Kmu l, ‖x - y‖ < e := by
  have hc : x ∈ closure ((Kmu l : Set ℂ_[l])) := hx
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hc e he
  exact ⟨y, hy, by rwa [dist_eq_norm] at hd⟩

theorem kur_discrete {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [norm_zero]
    exact norm_nonneg _
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨y, hy, hxy⟩ := kur_approx l hx ‖x‖ hpos
  have heq : ‖x‖ = ‖y‖ := norm_eq_of_norm_sub_lt_max l (lt_of_lt_of_le hxy (le_max_left _ _))
  rw [heq] at h1 ⊢
  exact kmu_discrete l hy h1

theorem kur_rep {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) :
    ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨y, hy, hxy⟩ := kur_approx l hx ‖(l : ℂ_[l])‖ (norm_prime_pos_complexPadic l)
  have hl1 := norm_prime_lt_one_complexPadic l
  have hy1 : ‖y‖ ≤ 1 := by
    have h := norm_sub_le_max_padic l x (x - y)
    rw [sub_sub_cancel] at h
    exact h.trans (max_le h1 (by linarith))
  obtain ⟨ξ, hξ, hyξ⟩ := kmu_rep l hy hy1
  refine ⟨ξ, hξ, ?_⟩
  have h := norm_sub_le_max_padic l (x - y) (ξ - y)
  rw [sub_sub_sub_cancel_right, norm_sub_rev ξ y] at h
  exact h.trans (max_le hxy.le hyξ)

end ReciprocityTheory.ChartRestriction.L1
end
end
