module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle637
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle624
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_prime_pow_smul_mem_localLattice : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [NormedField K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (v : T.V), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x : ↥T.L.T, (x : T.V) = (l : K) ^ n • v := by
  first | exact @GlobalTheory.LatPow.pow_smul_mem | exact GlobalTheory.LatPow.pow_smul_mem | (intros; apply GlobalTheory.LatPow.pow_smul_mem <;> assumption)
end

section

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.DpGood

theorem factorial_pow_mul (q : ℕ) : ∀ j : ℕ, ∃ D : ℕ, (j * q).factorial = q.factorial ^ j * D := by
  intro j
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨D, hD⟩ := ih
    refine ⟨((j + 1) * q).choose q * D, ?_⟩
    have h := Nat.choose_mul_factorial_mul_factorial (show q ≤ (j + 1) * q by nlinarith)
    have h2 : (j + 1) * q - q = j * q := by rw [add_mul, one_mul, Nat.add_sub_cancel]
    rw [h2, hD] at h
    rw [← h]; ring

theorem choose_eq (l q : ℕ) (hl : 1 ≤ l) (hq : 1 ≤ q) :
    (l * q).choose q = l * (l * q - 1).choose (q - 1) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hpos : 0 < l * (q' + 1) := by positivity
  have hn : l * (q' + 1) = (l * (q' + 1) - 1) + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
  have h := Nat.add_one_mul_choose_eq (l * (q' + 1) - 1) q'
  rw [← hn] at h
  simp only [Nat.add_sub_cancel]
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos q')
    (show (l * (q' + 1)).choose (q' + 1) * (q' + 1) = l * (l * (q' + 1) - 1).choose q' * (q' + 1) by
      rw [← h]; ring)

theorem fact_dvd (l q M : ℕ) (hl : 1 ≤ l) (hq : 1 ≤ q) (hM : l * q ≤ M) :
    ∃ G : ℕ, M.factorial = q.factorial ^ l * l * G := by
  obtain ⟨D, hD⟩ := factorial_pow_mul q (l - 1)
  obtain ⟨R, hR⟩ := Nat.factorial_dvd_factorial hM
  have h := Nat.choose_mul_factorial_mul_factorial (show q ≤ l * q by nlinarith)
  have h2 : l * q - q = (l - 1) * q := by rw [Nat.sub_mul, one_mul]
  rw [h2, hD, choose_eq l q hl hq] at h
  refine ⟨(l * q - 1).choose (q - 1) * D * R, ?_⟩
  have hl' : q.factorial ^ l = q.factorial ^ (l - 1) * q.factorial := by
    rw [← pow_succ]; congr 1; omega
  rw [hR, ← h, hl']; ring

theorem key (K : Type) [Field K] [CharZero K] (l : ℕ) (hl : 1 ≤ l) (q M : ℕ) (hM : l * q ≤ M) :
    ∃ c' : K, ∃ k : ℕ, (q.factorial : K)⁻¹ = (q.factorial : K)⁻¹ ^ l + (l : K) * c' ∧
      (M.factorial : K) * c' = k := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨0, 0, by simp, by simp⟩
  obtain ⟨G, hG⟩ := fact_dvd l q M hl hq hM
  obtain ⟨h, hh⟩ : ∃ h, q.factorial ^ (l - 1) = h + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (pow_pos (Nat.factorial_pos q) _)).symm⟩
  have hG0 : G ≠ 0 := by
    rintro rfl; exact Nat.factorial_ne_zero M (by simpa using hG)
  refine ⟨((G * h : ℕ) : K) / (M.factorial : K), G * h, ?_, ?_⟩
  · have hf : (q.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero q)
    have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hG0' : (G : K) ≠ 0 := Nat.cast_ne_zero.2 hG0
    have hl' : (q.factorial : K) ^ l = ((h : K) + 1) * q.factorial := by
      have : (q.factorial : K) ^ (l - 1) = (h : K) + 1 := by exact_mod_cast hh
      rw [← this, ← pow_succ]; congr 1; omega
    have hh0 : (h : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero h
    rw [hG]; push_cast
    rw [inv_pow, hl']
    field_simp
    ring
  · have hMf : (M.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero M)
    field_simp

section Mem

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem mono_mem (N : ℕ) (c : K) (k : ℕ) (h : ((N / e).factorial : K) * c = k) :
    (fun _ => monomial N c : ZMod a → K⟦X⟧) ∈ SdSet t K e := by
  refine ⟨fun m => if m = N then (k : Wq l a) else 0, fun r => ?_, fun τ m => ?_⟩
  · rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton N).subset fun m hm => ?_
    by_contra hne
    have hne' : m ≠ N := by simpa using hne
    exact hm (by simp only [if_neg hne']; exact dvd_zero _)
  · rw [coeff_monomial]
    split_ifs with hm
    · subst hm; simp [h]
    · simp [hm]

end Mem

end GlobalTheory.CrysPrism.DpGood

namespace GlobalTheory.CrysPrism


open DpGood in
theorem dpS_frob_good : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ n : ℕ,
    (dpS a e n : ZMod a → K⟦X⟧) ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e,
      frobTot K a l (dpS a e n) = (dpS a e n : ZMod a → K⟦X⟧) ^ l + (l : ZMod a → K⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t n
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  refine ⟨mono_mem t e n _ 1 ?_, ?_⟩
  · rw [Nat.cast_one]; exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have hM : l * (n / e) ≤ l * n / e := by
    rw [Nat.le_div_iff_mul_le (NeZero.pos e), mul_assoc]
    exact Nat.mul_le_mul_left l (Nat.div_mul_le_self n e)
  obtain ⟨c', k, hc, hk⟩ := key K l hl (n / e) (l * n / e) hM
  refine ⟨fun _ => monomial (l * n) c', mono_mem t e (l * n) c' k hk, ?_⟩
  funext τ
  have hfrob : frobTot K a l (dpS a e n) τ = frob K l ((dpS a e n) (τ - 1)) := rfl
  rw [hfrob, Pi.add_apply, Pi.pow_apply, Pi.mul_apply, Pi.natCast_apply]
  simp only [dpS]
  rw [frob, expand_monomial, monomial_pow, ← map_natCast (C : K →+* K⟦X⟧), ← smul_eq_C_mul,
    ← LinearMap.map_smul, ← map_add, smul_eq_mul, ← hc]

end GlobalTheory.CrysPrism
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem sdSet_eq_sum_add_mul (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) :
    ∀ F ∈ SdSet t K e, ∃ (N : ℕ) (v : ℕ → Wq l a), ∃ y ∈ SdSet t K e,
      F = ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n + (l : ZMod a → K⟦X⟧) * y := by
  rintro F ⟨w, hw, hF⟩
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : Wq l a) ≠ 0 := by
    have h := WittVector.p_nonzero l (Fq l a)
    exact h
  have h1 := hw 1
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at h1
  obtain ⟨N, hN⟩ := h1
  have h2 : ∀ n, ∃ z : Wq l a, (n < N → z = 0) ∧ (¬ n < N → w n = l * z) := by
    intro n
    by_cases h : n < N
    · exact ⟨0, fun _ => rfl, fun h' => absurd h h'⟩
    · obtain ⟨z, hz⟩ := hN n (not_lt.1 h)
      exact ⟨z, fun h' => absurd h' h, fun _ => by rw [hz, pow_one]⟩
  choose z hz0 hz using h2
  have hfac : ∀ n : ℕ, ((n / e).factorial : K) ≠ 0 := fun n => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  refine ⟨N, w, fun τ => PowerSeries.mk fun n => ((n / e).factorial : K)⁻¹ * algebraMap O K (emb t τ (z n)),
    ⟨z, fun r => ?_, fun τ n => ?_⟩, ?_⟩
  · filter_upwards [hw (r + 1)] with n hn
    by_cases h : n < N
    · rw [hz0 n h]; exact dvd_zero _
    · rw [hz n h, pow_succ'] at hn
      exact (mul_dvd_mul_iff_left hl0).1 hn
  · rw [coeff_mk, mul_inv_cancel_left₀ (hfac n)]
  · funext τ
    ext m
    apply mul_left_cancel₀ (hfac m)
    rw [hF]
    have hc : (l : K⟦X⟧) = C (l : K) := (map_natCast (C : K →+* K⟦X⟧) l).symm

    simp only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply, map_add (f := _), map_sum, cstS_apply, dpS,
    hc, coeff_C_mul, coeff_monomial, coeff_mk, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    by_cases h : m < N
    · rw [if_pos h, hz0 m h, map_zero, map_zero]
      field_simp [hfac m]
      ring
    · rw [if_neg h, hz m h, map_mul, map_mul, map_natCast, map_natCast]
      field_simp [hfac m]
      ring

end GlobalTheory.CrysPrism
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem factorial_mul_coeff_mem_S : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ (τ : ZMod a) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (F τ) ∈ S O K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF τ i
  obtain ⟨w, hw, hF⟩ := hF
  have key : ∀ n, ‖coeff n ((i.factorial : K⟦X⟧) * coeff i (F τ))‖ * wS K e n =
      ‖algebraMap O K (emb t τ (w (i, n)))‖ := fun n => by
    rw [← hF τ i n, wS, ← norm_mul, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1; ring
  rw [mem_S]
  simp only [key]
  refine ⟨fun n => norm_algebraMap_le _, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (norm_l_lt_one (K := K) l)
  have h : ∀ᶠ n in cofinite, (l : Wq l a) ^ r ∣ w (i, n) := by
    have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    exact h.preimage (f := fun n : ℕ => (i, n)) (fun _ _ _ _ h => by simpa using h)
  rw [Nat.cofinite_eq_atTop] at h
  filter_upwards [h] with n hn
  obtain ⟨c, hc⟩ := hn
  rw [Real.dist_eq, sub_zero, abs_norm, hc, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
    norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (norm_algebraMap_le _)) hr

end GlobalTheory.CrysPrism
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism

section SdClosed

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem lTo0_atTop {w : ℕ → Wq l a} : LTo0 l w ↔ ∀ r : ℕ, ∃ N, ∀ n ≥ N, (l : Wq l a) ^ r ∣ w n := by
  simp only [LTo0, Nat.cofinite_eq_atTop, eventually_atTop]

theorem sdSet_zero : (0 : ZMod a → K⟦X⟧) ∈ SdSet t K e :=
  ⟨0, fun r => Eventually.of_forall fun _ => dvd_zero _, fun τ n => by simp⟩

theorem sdSet_one : (1 : ZMod a → K⟦X⟧) ∈ SdSet t K e := by
  refine ⟨fun n => if n = 0 then 1 else 0, lTo0_atTop.2 fun r => ⟨1, fun n hn => ?_⟩, fun τ n => ?_⟩
  · rw [if_neg (by omega)]; exact dvd_zero _
  · rw [Pi.one_apply, coeff_one]
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]

theorem sdSet_neg {F : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) : -F ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨-w, fun r => (hw r).mono fun n hn => ?_, fun τ n => ?_⟩
  · simpa using hn
  · simp [hF τ n]

theorem sdSet_add {F G : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) (hG : G ∈ SdSet t K e) :
    F + G ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  refine ⟨w + w', fun r => ((hw r).and (hw' r)).mono fun n hn => ?_, fun τ n => ?_⟩
  · exact dvd_add hn.1 hn.2
  · simp [mul_add, hF τ n, hG τ n]

theorem fact_div_dvd (e i j : ℕ) : (i / e).factorial * (j / e).factorial ∣ ((i + j) / e).factorial :=
  (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
    (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div i j e))

theorem sdSet_mul {F G : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) (hG : G ∈ SdSet t K e) :
    F * G ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  let q : ℕ → ℕ → ℕ := fun i j => ((i + j) / e).factorial / ((i / e).factorial * (j / e).factorial)
  have hq : ∀ i j, ((i + j) / e).factorial = q i j * ((i / e).factorial * (j / e).factorial) := fun i j =>
    (Nat.div_mul_cancel (fact_div_dvd e i j)).symm
  refine ⟨fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, q p.1 p.2 • (w p.1 * w' p.2), ?_, fun τ n => ?_⟩
  · rw [lTo0_atTop] at hw hw' ⊢
    intro r
    obtain ⟨N, hN⟩ := hw r
    obtain ⟨N', hN'⟩ := hw' r
    refine ⟨N + N', fun n hn => Finset.dvd_sum fun p hp => ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [nsmul_eq_mul]
    apply Dvd.dvd.mul_left
    by_cases h1 : N ≤ p.1
    · exact (hN _ h1).mul_right _
    · exact (hN' _ (by omega)).mul_left _

  · rw [Pi.mul_apply, coeff_mul, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, map_mul, map_mul, ← hF τ p.1, ← hG τ p.2, ← hp, hq p.1 p.2]
    push_cast
    ring

theorem sd_sub_sdSet : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  let S : Subring (ZMod a → K⟦X⟧) :=
    { carrier := SdSet t K e
      zero_mem' := sdSet_zero t e
      one_mem' := sdSet_one t e
      add_mem' := fun hF hG => sdSet_add t e hF hG
      mul_mem' := fun hF hG => sdSet_mul t e hF hG
      neg_mem' := fun hF => sdSet_neg t e hF }
  intro F hF
  exact (Subring.closure_le.2 (fun x hx => hx) : Sd t K e ≤ S) hF

end SdClosed

theorem sdSet_closed : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  exact sd_sub_sdSet t e

end GlobalTheory.CrysPrism
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism

section Closed

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a]

theorem LTo0_zero {ι : Type} : LTo0 l (0 : ι → Wq l a) :=
  fun _ => Eventually.of_forall fun _ => dvd_zero _

theorem LTo0_add {ι : Type} {w w' : ι → Wq l a} (h : LTo0 l w) (h' : LTo0 l w') : LTo0 l (w + w') :=
  fun r => ((h r).and (h' r)).mono fun _ hp => dvd_add hp.1 hp.2

theorem LTo0_neg {ι : Type} {w : ι → Wq l a} (h : LTo0 l w) : LTo0 l (-w) :=
  fun r => (h r).mono fun _ hp => (dvd_neg).2 hp

theorem LTo0_single : LTo0 l (fun p : ℕ × ℕ => if p = (0, 0) then (1 : Wq l a) else 0) :=
  fun _ => (eventually_cofinite_ne ((0 : ℕ), (0 : ℕ))).mono fun _ hp => by simp [hp]

theorem LTo0_conv {w w' : ℕ × ℕ → Wq l a} (h : LTo0 l w) (h' : LTo0 l w')
    (c : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ) :
    LTo0 l (fun p : ℕ × ℕ => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p.1, ∑ y ∈ Finset.HasAntidiagonal.antidiagonal p.2,
      (c p.1 p.2 x y : Wq l a) * w (x.1, y.1) * w' (x.2, y.2)) := by
  intro r
  have hB := h r
  have hB' := h' r
  rw [Filter.eventually_cofinite] at hB hB' ⊢
  refine ((hB.prod hB').image fun pq : (ℕ × ℕ) × (ℕ × ℕ) => pq.1 + pq.2).subset ?_
  rintro ⟨i, n⟩ hp
  by_contra hni
  apply hp
  refine Finset.dvd_sum fun x hx => Finset.dvd_sum fun y hy => ?_
  by_cases h1 : (l : Wq l a) ^ r ∣ w (x.1, y.1)
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h1 _) _
  by_cases h2 : (l : Wq l a) ^ r ∣ w' (x.2, y.2)
  · exact dvd_mul_of_dvd_right h2 _
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  exact (hni ⟨((x.1, y.1), (x.2, y.2)), ⟨h1, h2⟩, by simp [Prod.mk_add_mk, hx, hy]⟩).elim

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem PPSet_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ PPSet t K e :=
  ⟨0, LTo0_zero, fun τ i n => by simp⟩

theorem PPSet_one : (1 : ZMod a → K⟦X⟧⟦X⟧) ∈ PPSet t K e := by
  refine ⟨_, LTo0_single, fun τ i n => ?_⟩
  simp only [Pi.one_apply, coeff_one]
  by_cases hi : i = 0
  · subst hi
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  · simp [hi]

theorem PPSet_add {F G : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) (hG : G ∈ PPSet t K e) :
    F + G ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  refine ⟨w + w', LTo0_add hw hw', fun τ i n => ?_⟩
  simp only [Pi.add_apply, map_add (f := _), mul_add, hF, hG]

theorem PPSet_neg {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) : -F ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨-w, LTo0_neg hw, fun τ i n => ?_⟩
  simp only [Pi.neg_apply, map_neg, mul_neg, hF]

theorem PPSet_mul {F G : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) (hG : G ∈ PPSet t K e) :
    F * G ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  let c : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ := fun i n x y =>
    (i.factorial * (n / e).factorial) /
      ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial))
  refine ⟨_, LTo0_conv hw hw' c, fun τ i n => ?_⟩
  have hc : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal i, ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n,
      i.factorial * (n / e).factorial =
        c i n x y * ((x.1.factorial * (y.1 / e).factorial) * (x.2.factorial * (y.2 / e).factorial)) := by
    intro x hx y hy
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
    refine (Nat.div_mul_cancel ?_).symm
    rw [mul_mul_mul_comm]
    apply mul_dvd_mul
    · rw [← hx]; exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
    · exact (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
        (Nat.factorial_dvd_factorial (by rw [← hy]; exact Nat.add_div_le_add_div _ _ _))

  simp only [Pi.mul_apply, coeff_mul, map_sum, Finset.mul_sum, map_mul, map_natCast]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [hc x hx y hy, ← hF τ x.1 y.1, ← hG τ x.2 y.2]
  push_cast
  ring

theorem PPd_subset_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∀ F ∈ PPd t K e, F ∈ PPSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF
  let S : Subring (ZMod a → K⟦X⟧⟦X⟧) :=
    { carrier := PPSet t K e
      mul_mem' := PPSet_mul t e
      one_mem' := PPSet_one t e
      add_mem' := PPSet_add t e
      zero_mem' := PPSet_zero t e
      neg_mem' := PPSet_neg t e }
  exact (Subring.closure_le (t := S)).2 le_rfl hF

end Closed

end GlobalTheory.CrysPrism
end
end
