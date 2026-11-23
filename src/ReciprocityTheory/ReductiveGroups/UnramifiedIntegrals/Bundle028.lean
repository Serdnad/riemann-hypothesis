module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
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
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle027
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle014
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle021
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle022
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedValB

@[expose] public section

section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem three_dvd_of_norm_relations (l x : ℝ) (hl : 1 < l) (hx : 0 < x) (n a : ℤ) (t : ℕ)
    (h1 : x ^ 12 * (l ^ n) ^ 2 = 1) (h2 : x ^ (2 * t) * l ^ a = 1) (ht : ¬ 3 ∣ t) :
    ∃ m : ℤ, n = 3 * m := by
  have hl0 : 0 < l := by linarith
  have e1 : x ^ (12 * t) * l ^ (2 * n * t) = 1 := by
    have : (x ^ 12 * (l ^ n) ^ 2) ^ t = 1 := by rw [h1, one_pow]
    rw [mul_pow, ← pow_mul] at this
    rw [← this]
    congr 1
    rw [← zpow_natCast (l ^ n) 2, ← zpow_mul, ← zpow_natCast _ t, ← zpow_mul]
    congr 1
    push_cast
    ring
  have e2 : x ^ (12 * t) * l ^ (6 * a) = 1 := by
    have : (x ^ (2 * t) * l ^ a) ^ 6 = 1 := by rw [h2, one_pow]
    rw [mul_pow, ← pow_mul] at this
    rw [← this]
    congr 1
    · congr 1
      ring
    · rw [← zpow_natCast (l ^ a) 6, ← zpow_mul]
      congr 1
      push_cast
      ring
  have hx0 : x ^ (12 * t) ≠ 0 := (pow_pos hx _).ne'
  have e3 : l ^ (2 * n * t) = l ^ (6 * a) := mul_left_cancel₀ hx0 (e1.trans e2.symm)
  have e4 : 2 * n * t = 6 * a := zpow_right_injective₀ hl0 hl.ne' e3
  have e5 : (3 : ℤ) ∣ n * t := ⟨a, by linarith⟩
  have hp : Prime (3 : ℤ) := Int.prime_three
  rcases hp.dvd_or_dvd e5 with h | h
  · exact h
  · exact absurd (by exact_mod_cast h) ht

section Norms

variable (l : ℕ) [Fact l.Prime]

theorem norm_twentySeven_eq_one_of_five_le (h5 : 5 ≤ l) : ‖(27 : ℂ_[l])‖ = 1 := by
  have h : ¬ l ∣ 27 := by
    intro h
    have h3 : l ∣ 3 := (Fact.out : l.Prime).dvd_of_dvd_pow (show l ∣ 3 ^ 3 by simpa using h)
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  simpa using red_norm_natCast l h

theorem norm_1728_eq_one_of_five_le' (h5 : 5 ≤ l) : ‖(1728 : ℂ_[l])‖ = 1 := by
  have h : ¬ l ∣ 1728 := by
    intro h
    have h' : l ∣ 2 ^ 6 * 3 ^ 3 := by simpa using h
    rcases (Fact.out : l.Prime).dvd_mul.1 h' with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) ((Fact.out : l.Prime).dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) ((Fact.out : l.Prime).dvd_of_dvd_pow h3)
      omega
  simpa using red_norm_natCast l h

theorem norm_sub_1728_eq_one_of_norm_lt_one (h5 : 5 ≤ l) {J : ℂ_[l]} (hJ : ‖J‖ < 1) : ‖J - 1728‖ = 1 := by
  have h := norm_1728_eq_one_of_five_le' l h5
  have hne : ‖J‖ ≠ ‖-(1728 : ℂ_[l])‖ := by rw [norm_neg, h]; exact hJ.ne
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, h]
  exact max_eq_right hJ.le

theorem norm_weierstrass_coeff_small_j (h5 : 5 ≤ l) {J : ℂ_[l]} (hJ : ‖J‖ < 1) :
    ‖27 * J / (J - 1728)‖ = ‖J‖ ∧
      ‖(27 * J / (J - 1728)) ^ 3 - 27 * (27 * J / (J - 1728)) ^ 2‖ = ‖J‖ ^ 2 := by
  have h1 := norm_sub_1728_eq_one_of_norm_lt_one l h5 hJ
  have h27 := norm_twentySeven_eq_one_of_five_le l h5
  have h1728 := norm_1728_eq_one_of_five_le' l h5
  have hne : J - 1728 ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hc : ‖27 * J / (J - 1728)‖ = ‖J‖ := by
    rw [norm_div, norm_mul, h1, h27, one_mul, div_one]
  refine ⟨hc, ?_⟩
  have e : (27 * J / (J - 1728)) ^ 3 - 27 * (27 * J / (J - 1728)) ^ 2
      = (27 * J / (J - 1728)) ^ 2 * (27 * 1728 / (J - 1728)) := by
    field_simp
    ring
  rw [e, norm_mul, norm_pow, hc, norm_div, norm_mul, h1, h27, h1728]
  norm_num

end Norms

theorem valDiv3 (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    [Fact l.Prime] (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (ι : ℂ ≃+* ℂ_[l]) (hJ : ι (jInv L) ∈ MaximalUnramifiedExtension l)
    (hJ1 : ‖ι (jInv L)‖ ≤ 1) (h0 : ι (jInv L) ≠ 0) :
    ∃ m : ℤ, ‖ι (jInv L)‖ = (l : ℝ) ^ (3 * m) := by
  rcases hJ1.eq_or_lt with hJ1 | hJ1
  · exact ⟨0, by simpa using hJ1⟩
  have hj0 : jInv L ≠ 0 := fun h => h0 (by rw [h, map_zero])
  have hg2 : L.g₂ ≠ 0 := fun h => hj0 ((jInv_eq_zero_iff L).2 h)
  have hd3 : d ≠ 3 := by
    rintro rfl
    exact hg2 (g2_eq_zero_of_hasCMBy_three L hCM)
  have hsub := norm_sub_1728_eq_one_of_norm_lt_one l h5 hJ1
  have i27 : ι 27 = 27 := map_ofNat ι 27
  have i1728 : ι 1728 = 1728 := map_ofNat ι 1728
  have hg3 : L.g₃ ≠ 0 := by
    intro h
    have h' := (jInv_eq_iff L).2 h
    rw [h', i1728, sub_self, norm_zero] at hsub
    exact zero_ne_one hsub
  obtain ⟨L0, hCM0, hj, hc2, hc3⟩ := exists_cm_lattice_equal_invariants d L hCM hg2 hg3
  set J : ℂ_[l] := ι (jInv L) with hJdef
  have hι2 : ι L0.g₂ = 27 * J / (J - 1728) := by
    rw [hc2]; simp [hJdef, i27, i1728]
  have hι3 : ι L0.g₃ = 27 * J / (J - 1728) := by
    rw [hc3]; simp [hJdef, i27, i1728]
  obtain ⟨hnc, hnD⟩ := norm_weierstrass_coeff_small_j l h5 hJ1
  set c : ℂ_[l] := 27 * J / (J - 1728) with hcdef
  have hιD : ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2) = c ^ 3 - 27 * c ^ 2 := by
    simp [hι2, hι3, i27]
  have hJpos : 0 < ‖J‖ := norm_pos_iff.2 h0
  have hD0 : c ^ 3 - 27 * c ^ 2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnD
    exact (pow_pos hJpos 2).ne hnD
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (c ^ 3 - 27 * c ^ 2)⁻¹ (n := 12) (by norm_num)
  have hμ1 : μ ^ 12 * ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2) = 1 := by
    rw [hιD, hμ, inv_mul_cancel₀ hD0]
  have hμn : ‖μ‖ ^ 12 * ‖J‖ ^ 2 = 1 := by
    have := congrArg norm hμ1
    rwa [hιD, norm_mul, norm_pow, hnD, norm_one] at this
  have hμpos : 0 < ‖μ‖ := by
    rcases (norm_nonneg μ).eq_or_lt with h | h
    · rw [← h] at hμn
      norm_num at hμn
    · exact h
  have hn4 : ‖μ ^ 4 * ι L0.g₂‖ < 1 := by
    have e : ‖μ ^ 4 * ι L0.g₂‖ ^ 3 = ‖J‖ := by
      rw [hι2, norm_mul, norm_pow, hnc]
      calc (‖μ‖ ^ 4 * ‖J‖) ^ 3 = (‖μ‖ ^ 12 * ‖J‖ ^ 2) * ‖J‖ := by ring
        _ = ‖J‖ := by rw [hμn, one_mul]
    by_contra hcon
    have : 1 ≤ ‖μ ^ 4 * ι L0.g₂‖ ^ 3 := one_le_pow₀ (not_lt.1 hcon)
    rw [e] at this
    exact absurd hJ1 (not_lt.2 this)
  have hn6 : ‖μ ^ 6 * ι L0.g₃‖ = 1 := by
    have e : ‖μ ^ 6 * ι L0.g₃‖ ^ 2 = 1 := by
      rw [hι3, norm_mul, norm_pow, hnc]
      calc (‖μ‖ ^ 6 * ‖J‖) ^ 2 = ‖μ‖ ^ 12 * ‖J‖ ^ 2 := by ring
        _ = 1 := hμn
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 e
  obtain ⟨N, T, hlN, h3N, h3T, hT, hk⟩ :=
    kerProd d L0 hsq hd4 hCM0 l Fact.out h5 hld 3 (Or.inr ⟨rfl, hd3⟩)
  have hunit := unit_prod L0 l ι h5 μ hμ1 hn4.le hn6.le 3 N (Or.inl ⟨rfl, hn4⟩) hlN h3N T hT
  have hcK : c ∈ MaximalUnramifiedExtension l := by
    have h27 : (27 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
      exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 27
    have h1728 : (1728 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
      exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 1728
    exact div_mem (mul_mem h27 hJ) (sub_mem hJ h1728)
  have hP : ι (∏ z ∈ T, L0.weierstrassP z) ∈ MaximalUnramifiedExtension l := by
    have := hk ((MaximalUnramifiedExtension l).comap (ι : ℂ →+* ℂ_[l]))
      (by rw [Subfield.mem_comap]; simpa [hι2] using hcK)
      (by rw [Subfield.mem_comap]; simpa [hι3] using hcK)
      (by rw [Subfield.mem_comap]; exact omega_mem_kur d hsq hd4 l hld ι)
    simpa [Subfield.mem_comap] using this
  have hP0 : ι (∏ z ∈ T, L0.weierstrassP z) ≠ 0 := by
    intro h
    rw [h, norm_zero, mul_zero] at hunit
    exact zero_ne_one hunit
  obtain ⟨a, ha⟩ := kur_val l hP hP0
  obtain ⟨n, hn⟩ := kur_val l hJ h0
  have hl1 : (1 : ℝ) < l := by
    have : 1 < l := by omega
    exact_mod_cast this
  rw [ha] at hunit
  rw [hn] at hμn
  obtain ⟨m, hm⟩ := three_dvd_of_norm_relations l ‖μ‖ hl1 hμpos n a T.card hμn hunit h3T
  exact ⟨m, by rw [hn, hm]⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem valDiv2_even_of_pows {l t : ℝ} (hl : 1 < l) {a b : ℤ} {n : ℕ} (hn : ¬ 2 ∣ n)
    (h4 : t ^ 4 = l ^ b) (h1 : t ^ (2 * n) * l ^ a = 1) : ∃ m : ℤ, b = 2 * m := by
  have hl0 : l ≠ 0 := by positivity
  have e1 : l ^ (b * n + 2 * a) = 1 := by
    rw [zpow_add₀ hl0, zpow_mul, ← h4, zpow_natCast, mul_comm 2 a, zpow_mul]
    have h5 : (t ^ 4) ^ n = (t ^ (2 * n)) ^ 2 := by ring
    have h6 : (l ^ a) ^ (2 : ℤ) = (l ^ a) ^ 2 := by norm_cast
    rw [h5, h6, ← mul_pow, h1, one_pow]
  have e2 : b * n + 2 * a = 0 := (zpow_eq_one_iff_right₀ (by positivity) hl.ne').1 e1
  obtain ⟨k, hk⟩ : Odd n := Nat.not_even_iff_odd.1 (fun h => hn (even_iff_two_dvd.1 h))
  subst hk
  push_cast at e2
  exact ⟨-a - b * k, by linarith⟩

theorem norm_1728_eq_one_of_five_le (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) : ‖(1728 : ℂ_[l])‖ = 1 := by
  have hl : l.Prime := Fact.out
  have h : ¬ l ∣ 1728 := by
    intro h
    have h12 : l ∣ 12 := hl.dvd_of_dvd_pow (show l ∣ 12 ^ 3 by norm_num; exact h)
    have := Nat.le_of_dvd (by norm_num) h12
    interval_cases l <;> first | omega | exact absurd hl (by norm_num)
  simpa using red_norm_natCast l h

theorem valDiv2_norm_27 (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) : ‖(27 : ℂ_[l])‖ = 1 := by
  have hl : l.Prime := Fact.out
  have h : ¬ l ∣ 27 := by
    intro h
    have h12 : l ∣ 3 := hl.dvd_of_dvd_pow (show l ∣ 3 ^ 3 by norm_num; exact h)
    have := Nat.le_of_dvd (by norm_num) h12
    omega
  simpa using red_norm_natCast l h

theorem valDiv2 (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    [Fact l.Prime] (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (ι : ℂ ≃+* ℂ_[l]) (hJ : ι (jInv L) ∈ MaximalUnramifiedExtension l)
    (hJ1 : ‖ι (jInv L)‖ ≤ 1) (h0 : ι (jInv L) ≠ 1728) :
    ∃ m : ℤ, ‖ι (jInv L) - 1728‖ = (l : ℝ) ^ (2 * m) := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have n1728 := norm_1728_eq_one_of_five_le l h5
  have n27 := valDiv2_norm_27 l h5
  obtain ⟨J, hJdef⟩ : ∃ J, J = ι (jInv L) := ⟨_, rfl⟩
  rw [← hJdef] at hJ hJ1 h0 ⊢
  have hw0 : J - 1728 ≠ 0 := sub_ne_zero.2 h0
  have m1728 : (1728 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
    have := natCast_mem (MaximalUnramifiedExtension l) 1728
    exact_mod_cast this
  have m27 : (27 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
    have := natCast_mem (MaximalUnramifiedExtension l) 27
    exact_mod_cast this
  have hwK : J - 1728 ∈ MaximalUnramifiedExtension l := sub_mem hJ m1728
  obtain ⟨b, hb⟩ := kur_val l hwK hw0
  have hwle : ‖J - 1728‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hJ1 (by rw [norm_neg, n1728]))
  rcases hwle.eq_or_lt with h1 | hlt
  · exact ⟨0, by simpa using h1⟩
  have nJ : ‖J‖ = 1 := by
    have h : J = (J - 1728) + 1728 := by ring
    rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [n1728]; exact hlt.ne), n1728,
      max_eq_right hlt.le]
  have hJ0 : J ≠ 0 := by
    intro h
    rw [h, norm_zero] at nJ
    exact zero_ne_one nJ
  have hj0 : jInv L ≠ 0 := fun h => hJ0 (by rw [hJdef, h, map_zero])
  have hj1 : jInv L ≠ 1728 := fun h => h0 (by rw [hJdef, h, map_ofNat])
  have h2 : L.g₂ ≠ 0 := fun h => hj0 ((jInv_eq_zero_iff L).2 h)
  have h3 : L.g₃ ≠ 0 := fun h => hj1 ((jInv_eq_iff L).2 h)
  obtain ⟨L0, hCM0, -, hg2, hg3⟩ := exists_cm_lattice_equal_invariants d L hCM h2 h3
  obtain ⟨c, hc⟩ : ∃ c : ℂ_[l], c = 27 * J / (J - 1728) := ⟨_, rfl⟩
  have ig2 : ι L0.g₂ = c := by
    rw [hg2, hc, hJdef, map_div₀, map_mul, map_sub, map_ofNat, map_ofNat]
  have ig3 : ι L0.g₃ = c := by
    rw [hg3, hc, hJdef, map_div₀, map_mul, map_sub, map_ofNat, map_ofNat]
  have mc : c ∈ MaximalUnramifiedExtension l := by
    rw [hc]
    exact div_mem (mul_mem m27 hJ) hwK
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ‖J - 1728‖ := ⟨_, rfl⟩
  rw [← hx] at hb hlt ⊢
  have hx0 : 0 < x := by rw [hx]; exact norm_pos_iff.2 hw0
  have nc : ‖c‖ = x⁻¹ := by
    rw [hc, norm_div, norm_mul, n27, nJ, ← hx]
    simp
  have iD : ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2) = c ^ 2 * (27 * 1728 / (J - 1728)) := by
    rw [map_sub, map_mul, map_pow, map_pow, ig2, ig3, map_ofNat, hc]
    field_simp
    ring
  have nD : ‖ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2)‖ = (x⁻¹) ^ 3 := by
    rw [iD, norm_mul, norm_pow, nc, norm_div, norm_mul, n27, n1728, ← hx]
    ring
  have hD0 : ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2) ≠ 0 := norm_ne_zero_iff.1 (by rw [nD]; positivity)
  obtain ⟨μ, hμ'⟩ := IsAlgClosed.exists_pow_nat_eq (ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2))⁻¹
    (n := 12) (by norm_num)
  have hμ : μ ^ 12 * ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2) = 1 := by
    rw [hμ']
    exact inv_mul_cancel₀ hD0
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ‖μ‖ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact norm_nonneg _
  have ht12 : (t ^ 4) ^ 3 = x ^ 3 := by
    have h := congrArg norm hμ
    rw [norm_mul, norm_pow, nD, norm_one, ← ht] at h
    field_simp at h
    rw [← h]
    ring
  have ht4 : t ^ 4 = x := (pow_left_inj₀ (by positivity) hx0.le (by norm_num)).1 ht12
  have ht1 : t < 1 := by
    by_contra h
    have : 1 ≤ t ^ 4 := one_le_pow₀ (not_lt.1 h)
    linarith
  have n4 : ‖μ ^ 4 * ι L0.g₂‖ = 1 := by
    rw [ig2, norm_mul, norm_pow, nc, ← ht, ht4]
    exact mul_inv_cancel₀ hx0.ne'
  have n6 : ‖μ ^ 6 * ι L0.g₃‖ = t ^ 2 := by
    rw [ig3, norm_mul, norm_pow, nc, ← ht]
    have : t ^ 6 = x * t ^ 2 := by rw [← ht4]; ring
    rw [this]
    field_simp
  have n6lt : ‖μ ^ 6 * ι L0.g₃‖ < 1 := by
    rw [n6]
    exact pow_lt_one₀ ht0 ht1 (by norm_num)
  obtain ⟨N, T, hlN, h2N, h2T, hT, hk⟩ := kerProd d L0 hsq hd4 hCM0 l hl h5 hld 2 (Or.inl rfl)
  have hP : ι (∏ z ∈ T, L0.weierstrassP z) ∈ MaximalUnramifiedExtension l := by
    have := hk ((MaximalUnramifiedExtension l).comap (ι : ℂ →+* ℂ_[l])) (by rw [Subfield.mem_comap]; simpa [ig2] using mc)
      (by rw [Subfield.mem_comap]; simpa [ig3] using mc)
      (by rw [Subfield.mem_comap]; exact omega_mem_kur d hsq hd4 l hld ι)
    rw [Subfield.mem_comap] at this
    exact this
  have hU := unit_prod L0 l ι h5 μ hμ n4.le n6lt.le 2 N (Or.inr ⟨rfl, n6lt⟩) hlN h2N T hT
  have hP0 : ι (∏ z ∈ T, L0.weierstrassP z) ≠ 0 := by
    intro h
    rw [h, norm_zero, mul_zero] at hU
    exact zero_ne_one hU
  obtain ⟨a, ha⟩ := kur_val l hP hP0
  rw [ha, ← ht] at hU
  obtain ⟨m, hm⟩ := valDiv2_even_of_pows hl1 h2T (ht4.trans hb) hU
  exact ⟨m, by rw [hb, hm]⟩

end ReciprocityTheory.ChartRestriction.L1
end
end
