module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Topology.Algebra.Valued.NormedValued

@[expose] public section

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_sumicc :
    ∀ {M : Type} [AddCommMonoid M] {N : ℕ} [NeZero N] (G : ZMod N → M), ∑ a ∈ Icc 1 N, G (a : ZMod N) = ∑ a : ZMod N, G a := by
  intro M _ N _ G
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod N)) (fun x : ZMod N => if x.val = 0 then N else x.val)
    ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro x _
    have hx := ZMod.val_lt x
    refine Finset.mem_Icc.2 ?_
    split_ifs with h0
    · exact ⟨hN, le_rfl⟩
    · exact ⟨Nat.pos_of_ne_zero h0, hx.le⟩
  · intro a ha
    have ha' := Finset.mem_Icc.1 ha
    simp only [ZMod.val_natCast]
    rcases Nat.lt_or_ge a N with h | h
    · rw [Nat.mod_eq_of_lt h, if_neg (by omega)]
    · have hEq : a = N := by omega
      subst hEq
      simp
  · intro x _
    split_ifs with h0
    · rw [ZMod.natCast_self]
      exact ((ZMod.val_eq_zero x).1 h0).symm
    · exact ZMod.natCast_zmod_val x
  · intro a _
    rfl
end

section

open Finset UpperTheory.V.Bern

private theorem hasSum_hurwitzZeta (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (((n : ℝ) + x : ℝ) : ℂ) ^ (-s)) (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s) := by
  convert HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨h0, h1⟩ hs using 1
  ext1 n
  rw [Complex.cpow_neg, one_div]
  push_cast
  rfl

theorem UpperTheory.V.Bern.b_termsum :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → ∀ s : ℂ, 1 < s.re → ∑' n : ℕ, ((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (1 - (x : ℂ)) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s))) = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s - HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - (1 - (x : ℂ)) := by
  intro x hx0 hx1 s hs
  have hA := hasSum_hurwitzZeta x hx0.le hx1 s hs
  have hB := hasSum_hurwitzZeta 1 zero_le_one le_rfl s hs
  have hC : HasSum (fun n : ℕ => ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) (HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hB
    have e1 : (fun n : ℕ => ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) = fun n : ℕ => (((((n + 1 : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) := by
      funext n
      congr 1
      push_cast
      ring
    have e2 : ∑ i ∈ range 1, (((((i : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) = 1 := by
      simp
    rw [e1, ← e2]
    exact h
  have hT := (hA.sub hB).sub ((hB.sub hC).mul_left (1 - (x : ℂ)))
  rw [hT.tsum_eq]
  ring
end

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_sumval :
    ∀ (M : ℤ), M ≠ 0 → ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l ≤ Real.log |(M : ℝ)| := by
  intro M hM T hT
  have hN : M.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hM
  have hlog : Real.log |(M : ℝ)| = Real.log (M.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hlog, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l
      = ∑ l ∈ T, (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [Nat.factorization_def _ (hT l hl)]
        rfl
    _ = ∑ l ∈ T.filter (· ∈ M.natAbs.factorization.support),
          (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_filter_of_ne fun l _ h => ?_).symm
        rw [Finsupp.mem_support_iff]
        intro h0
        apply h
        simp [h0]
    _ ≤ ∑ p ∈ M.natAbs.factorization.support,
          (M.natAbs.factorization p : ℝ) * Real.log p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_
        · intro x hx
          exact (Finset.mem_filter.mp hx).2
        · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
end

section

open Finset UpperTheory.V.Bern

private theorem b_ultra_int {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] {y : Ω}
    (h : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := Ω)).integer y := h.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := Ω))).mem_of_integral h1
  have h3 : ‖y‖₊ ≤ 1 := h2
  exact_mod_cast h3

private theorem b_ultra_unit {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] (l : ℕ)
    [hl : Fact l.Prime] (hn : ‖(l : Ω)‖ = (l : ℝ)⁻¹) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) :
    ‖(m : Ω)‖ = 1 := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).mpr hm
  have h1 : (a : Ω) * l + b * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hlt : ‖(l : Ω)‖ < 1 := by rw [hn]; exact inv_lt_one_of_one_lt₀ hl1
  refine le_antisymm (IsUltrametricDist.norm_intCast_le_one Ω m) ?_
  by_contra hc
  push Not at hc
  have ha := IsUltrametricDist.norm_intCast_le_one Ω a
  have hb := IsUltrametricDist.norm_intCast_le_one Ω b
  have h2 := IsUltrametricDist.norm_add_le_max ((a : Ω) * l) ((b : Ω) * m)
  rw [h1, norm_one, norm_mul, norm_mul] at h2
  have h3 : ‖(a : Ω)‖ * ‖(l : Ω)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right ha (norm_nonneg _) hlt
  have h4 : ‖(b : Ω)‖ * ‖(m : Ω)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hb (norm_nonneg _) hc
  exact absurd h2 (not_le.mpr (max_lt h3 h4))

private theorem b_ultra_log {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] (l : ℕ)
    [hl : Fact l.Prime] (hn : ‖(l : Ω)‖ = (l : ℝ)⁻¹) (M : ℤ) (hM : M ≠ 0) :
    -Real.log ‖(M : Ω)‖ = (padicValInt l M : ℝ) * Real.log l := by
  obtain ⟨m, hm⟩ := padicValInt_dvd (p := l) M
  have hnd : ¬ (l : ℤ) ∣ m := by
    rintro ⟨c, hc⟩
    have : (l : ℤ) ^ (padicValInt l M + 1) ∣ M := ⟨c, by
      conv_lhs => rw [hm, hc]
      ring⟩
    rcases (padicValInt_dvd_iff _ _).mp this with h | h
    · exact hM h
    · omega
  have h1 : (M : Ω) = (l : Ω) ^ padicValInt l M * m := by
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) hm
  rw [h1, norm_mul, b_ultra_unit l hn m hnd, mul_one, norm_pow, hn, Real.log_pow, Real.log_inv]
  ring

theorem UpperTheory.V.Bern.b_ultra :
    ∀ {Ω ι : Type} [NormedField Ω] [IsUltrametricDist Ω] [CharZero Ω] (l : ℕ) [Fact l.Prime], ‖(l : Ω)‖ = (l : ℝ)⁻¹ → ∀ (S : Set ι) (x : ι → Ω) (D : ℕ) (M : ℤ), S.Finite → M ≠ 0 → (∀ i ∈ S, IsIntegral ℤ ((D : Ω) * x i)) → ∏ᶠ i ∈ S, (D : Ω) * x i = (M : Ω) → ∑ᶠ i ∈ S, max 0 (-Real.log ‖x i‖) ≤ (padicValInt l M : ℝ) * Real.log l := by
  intro Ω ι _ _ _ l _ hn S x D M hS hM hint hprod
  rw [finprod_mem_eq_finite_toFinset_prod _ hS] at hprod
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, ← b_ultra_log l hn M hM, ← hprod, norm_prod]
  have hM' : (M : Ω) ≠ 0 := by exact_mod_cast hM
  have hne : ∀ i ∈ hS.toFinset, (D : Ω) * x i ≠ 0 := by
    rw [← Finset.prod_ne_zero_iff, hprod]; exact hM'
  rw [Real.log_prod (fun i hi => norm_ne_zero_iff.mpr (hne i hi)), ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ∈ S := by simpa using hi
  have h0 := hne i hi
  have hD : (D : Ω) ≠ 0 := left_ne_zero_of_mul h0
  have hx : x i ≠ 0 := right_ne_zero_of_mul h0
  refine max_le ?_ ?_
  · have := Real.log_nonpos (norm_nonneg _) (b_ultra_int (hint i hi'))
    linarith
  · rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hD) (norm_ne_zero_iff.mpr hx)]
    have := Real.log_nonpos (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one Ω D)
    linarith
end

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primden :
    ∀ (k j : ℕ), j ≤ k → ∃ z : ℤ, (primorial (k + 1) : ℚ) * bernoulli j = z := by
  intro k j hjk
  have hdvd : ∀ p : ℕ, p.Prime → p ≤ k + 1 → p ∣ primorial (k + 1) := by
    intro p hp hpk
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩)
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | hodd
  · obtain ⟨z0, hz0⟩ := Bernoulli.vonStaudt_clausen m
    have h2 : m + m = 2 * m := by ring
    rw [h2]
    have hB : bernoulli (2 * m) = (z0 : ℚ) - ∑ p ∈ range (2 * m + 2) with Nat.Prime p ∧ p - 1 ∣ 2 * m, (1 : ℚ) / p := by
      rw [hz0]; ring
    refine ⟨(primorial (k + 1) : ℤ) * z0 - ∑ p ∈ range (2 * m + 2) with Nat.Prime p ∧ p - 1 ∣ 2 * m, ((primorial (k + 1) / p : ℕ) : ℤ), ?_⟩
    rw [Int.cast_sub, Int.cast_mul, Int.cast_sum]
    simp only [Int.cast_natCast]
    rw [hB, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter, Finset.mem_range] at hp
    have hpd : p ∣ primorial (k + 1) := hdvd p hp.2.1 (by omega)
    rw [Nat.cast_div hpd (Nat.cast_ne_zero.2 hp.2.1.ne_zero)]
    ring
  · rcases Nat.lt_or_ge 1 j with h1 | h1
    · exact ⟨0, by rw [bernoulli_eq_zero_of_odd hodd h1]; simp⟩
    · have hj : j = 1 := by
        obtain ⟨r, rfl⟩ := hodd
        omega
      subst hj
      obtain ⟨t, ht⟩ := hdvd 2 Nat.prime_two (by omega)
      refine ⟨-(t : ℤ), ?_⟩
      rw [bernoulli_one, ht]
      push_cast
      ring
end

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primval :
    ∀ {R : Type} [CommRing R] {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) (x : ZMod χ.conductor), χ.primitiveCharacter x = 0 ∨ ∃ u : (ZMod N)ˣ, χ.primitiveCharacter x = χ u := by
  intro R _ N _ χ x
  by_cases hx : IsUnit x
  · right
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective χ.conductor_dvd_level hx.unit
    refine ⟨u, ?_⟩
    conv_rhs => rw [← χ.changeLevel_primitiveCharacter]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.unitsMap_val, hu]
    · simp
    · exact χ.conductor_dvd_level
  · left
    exact MulChar.map_nonunit _ hx
end
