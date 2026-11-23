module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle638
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle679
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle636
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle667
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPd t K e, F ∈ PPSet t K e := by
  first | exact @GlobalTheory.CrysPrism.PPd_subset_PPSet | exact GlobalTheory.CrysPrism.PPd_subset_PPSet | (intros; apply GlobalTheory.CrysPrism.PPd_subset_PPSet <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.factorial_mul_coeff_mem_dividedPowerSeriesSubring : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ (τ : ZMod a) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (F τ) ∈ S O K e := by
  first | exact @GlobalTheory.CrysPrism.factorial_mul_coeff_mem_S | exact GlobalTheory.CrysPrism.factorial_mul_coeff_mem_S | (intros; apply GlobalTheory.CrysPrism.factorial_mul_coeff_mem_S <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ x : (Wq l a)⟦X⟧, shP a sh (inclS t K (frobS l a x)) ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, shP a sh (inclS t K (frobS l a x)) - constP a K (inclS t K (frobS l a x)) = (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  first | exact @GlobalTheory.CrysPrism.ShMem.shP_frob_mem | exact GlobalTheory.CrysPrism.ShMem.shP_frob_mem | (intros; apply GlobalTheory.CrysPrism.ShMem.shP_frob_mem <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x : (Wq l a)⟦X⟧, inclS t K x ∈ SdSet t K e := by
  first | exact @GlobalTheory.CrysPrism.inclS_mem_SdSet | exact GlobalTheory.CrysPrism.inclS_mem_SdSet | (intros; apply GlobalTheory.CrysPrism.inclS_mem_SdSet <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.BK.GcdCore

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem powerSeries_coeff_norm_le_one_mul {f g : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (hg : ∀ n, ‖coeff n g‖ ≤ 1) (n : ℕ) :
    ‖coeff n (f * g)‖ ≤ 1 := by
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    zero_le_one zero_le_one (f := f) (g := g) (by simpa using hf) (by simpa using hg) n

theorem powerSeries_coeff_norm_le_one_add {f g : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (hg : ∀ n, ‖coeff n g‖ ≤ 1) (n : ℕ) :
    ‖coeff n (f + g)‖ ≤ 1 := by
  rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem powerSeries_coeff_norm_le_one_pow {f : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (m : ℕ) : ∀ n, ‖coeff n (f ^ m)‖ ≤ 1 := by
  induction m with
  | zero => intro n; rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ m ih => intro n; rw [pow_succ]; exact powerSeries_coeff_norm_le_one_mul ih hf n

theorem powerSeries_coeff_norm_le_one_X_pow (i : ℕ) : ∀ n, ‖coeff n ((X : K⟦X⟧) ^ i)‖ ≤ 1 := by
  intro n; rw [coeff_X_pow]; split_ifs <;> simp

theorem powerSeries_coeff_norm_le_one_frobeniusExpand (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) :
    ∀ n, ‖coeff n (frob K l f)‖ ≤ 1 := by
  intro n; rw [coeff_frob]; split_ifs
  · exact hf _
  · simp

theorem coeff_norm_le_one_eisensteinPolynomialPowPlusPrime (l e : ℕ) (hl : ‖(l : K)‖ < 1) : ∀ n, ‖coeff n (E K l e)‖ ≤ 1 := by
  intro n
  rw [E, ← map_natCast (C : K →+* K⟦X⟧)]
  refine powerSeries_coeff_norm_le_one_add (powerSeries_coeff_norm_le_one_X_pow e) (fun m => ?_) n
  rw [coeff_C]; split_ifs
  · exact hl.le
  · simp

theorem powerSeries_coeff_norm_le_one_finset_sum {ι : Type} (s : Finset ι) (f : ι → K⟦X⟧) (hf : ∀ i ∈ s, ∀ n, ‖coeff n (f i)‖ ≤ 1) :
    ∀ n, ‖coeff n (∑ i ∈ s, f i)‖ ≤ 1 :=
  Finset.sum_induction f (fun g => ∀ n, ‖coeff n g‖ ≤ 1) (fun _ _ ha hb => powerSeries_coeff_norm_le_one_add ha hb)
    (fun n => by simp) hf

theorem sum_X_pow_mul_frob_frobSlice (l : ℕ) [Fact l.Prime] (z : K⟦X⟧) :
    z = ∑ i ∈ Finset.range l, (X : K⟦X⟧) ^ i * frob K l (frobSlice l i z) := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n

  rw [map_sum]
  simp_rw [coeff_X_pow_mul', coeff_frob, coeff_frobSlice]
  rw [Finset.sum_eq_single (n % l)]
  · have h1 : n % l ≤ n := Nat.mod_le n l
    have h2 : l ∣ n - n % l := Nat.dvd_sub_mod n
    rw [if_pos h1, if_pos h2, Nat.mul_div_cancel' h2, Nat.sub_add_cancel h1]
  · intro i hi hne
    split_ifs with h1 h2
    · exfalso
      obtain ⟨c, hc⟩ := h2
      have hn : n = i + l * c := by omega
      apply hne
      rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_range.2 (Nat.mod_lt n hl)) h

theorem one_mem_of_frobenius_stable_ideals_boundedPowerSeries (GEN : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (J : Set K⟦X⟧), (∀ x ∈ J, ∀ y ∈ J, x + y ∈ J) → (∀ x ∈ J, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J) → (∃ g ∈ J, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → ∃ Δ ∈ J, (∀ n, ‖coeff n Δ‖ ≤ 1) ∧ (∃ n, ‖coeff n Δ‖ = 1) ∧ ∀ h ∈ J, (∀ n, ‖coeff n h‖ ≤ 1) → ∃ q : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ h = Δ * q)
  (CYCLE : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (l e a M N : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (Δ k k' : ZMod a → K⟦X⟧), (∀ τ n, ‖coeff n (Δ τ)‖ ≤ 1) → (∀ τ, ∃ n, ‖coeff n (Δ τ)‖ = 1) → (∀ τ n, ‖coeff n (k τ)‖ ≤ 1) → (∀ τ n, ‖coeff n (k' τ)‖ ≤ 1) → (∀ τ, k τ * k' τ = E K l e ^ N) → (∀ τ, Δ τ * k τ = E K l e ^ M * frob K l (Δ (τ - 1))) → ∀ τ, ‖constantCoeff (Δ τ)‖ = 1)
  (UNITA : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (f : K⟦X⟧), (∀ n, ‖coeff n f‖ ≤ 1) → ‖constantCoeff f‖ = 1 → ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ 1) ∧ f * g = 1) :
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (l e a M₁ M₂ : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (J : ZMod a → Set K⟦X⟧), (∀ τ, ∀ x ∈ J τ, ∀ y ∈ J τ, x + y ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∃ c : ℝ, ∀ n, ‖coeff n x‖ ≤ c) → (∀ τ, ∃ g ∈ J τ, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → (∀ τ, ∀ h ∈ J (τ - 1), E K l e ^ M₁ * frob K l h ∈ J τ) → (∀ τ, ∀ h ∈ J τ, ∀ i < l, frobSlice l i (E K l e ^ M₂ * h) ∈ J (τ - 1)) → ∀ τ, (1 : K⟦X⟧) ∈ J τ := by
  intro K _ _ _ l e a M₁ M₂ _ _ he hl0 hl1 J hadd hmul _ hprim hphi hsl
  choose Δ hΔJ hΔ1 hΔp hΔdiv using fun τ => GEN K (J τ) (hadd τ) (hmul τ) (hprim τ)
  have hE := coeff_norm_le_one_eisensteinPolynomialPowPlusPrime (K := K) l e hl1

  have hk : ∀ τ, ∃ k : K⟦X⟧, (∀ n, ‖coeff n k‖ ≤ 1) ∧
      Δ τ * k = E K l e ^ M₁ * frob K l (Δ (τ - 1)) := by
    intro τ
    obtain ⟨q, hq1, hq⟩ := hΔdiv τ _ (hphi τ _ (hΔJ (τ - 1)))
      (powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_pow hE M₁) (powerSeries_coeff_norm_le_one_frobeniusExpand l (hΔ1 (τ - 1))))
    exact ⟨q, hq1, hq.symm⟩
  choose k hk1 hk using hk

  have hm : ∀ τ i, ∃ m : K⟦X⟧, i < l → (∀ n, ‖coeff n m‖ ≤ 1) ∧
      frobSlice l i (E K l e ^ M₂ * Δ τ) = Δ (τ - 1) * m := by
    intro τ i
    by_cases hi : i < l
    · have hs1 : ∀ n, ‖coeff n (frobSlice l i (E K l e ^ M₂ * Δ τ))‖ ≤ 1 := fun n => by
        rw [coeff_frobSlice]; exact powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_pow hE M₂) (hΔ1 τ) _
      obtain ⟨q, hq1, hq⟩ := hΔdiv (τ - 1) _ (hsl τ _ (hΔJ τ) i hi) hs1
      exact ⟨q, fun _ => ⟨hq1, hq⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose m hm using hm
  set k' : ZMod a → K⟦X⟧ := fun τ => ∑ i ∈ Finset.range l, (X : K⟦X⟧) ^ i * frob K l (m τ i) with hk'def
  have hk'1 : ∀ τ n, ‖coeff n (k' τ)‖ ≤ 1 := fun τ =>
    powerSeries_coeff_norm_le_one_finset_sum _ _ fun i hi => powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_X_pow i) (powerSeries_coeff_norm_le_one_frobeniusExpand l (hm τ i (Finset.mem_range.1 hi)).1)
  have hk' : ∀ τ, E K l e ^ M₂ * Δ τ = frob K l (Δ (τ - 1)) * k' τ := by
    intro τ
    rw [sum_X_pow_mul_frob_frobSlice (K := K) l (E K l e ^ M₂ * Δ τ), hk'def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(hm τ i (Finset.mem_range.1 hi)).2, map_mul]
    ring
  have hne : ∀ τ, Δ τ ≠ 0 := fun τ h => by
    obtain ⟨n, hn⟩ := hΔp τ
    rw [h, map_zero, norm_zero] at hn
    exact zero_ne_one hn
  have hkk : ∀ τ, k τ * k' τ = E K l e ^ (M₁ + M₂) := by
    intro τ
    apply mul_left_cancel₀ (hne τ)
    calc Δ τ * (k τ * k' τ) = E K l e ^ M₁ * (frob K l (Δ (τ - 1)) * k' τ) := by
          rw [← mul_assoc, hk τ, mul_assoc]
      _ = Δ τ * E K l e ^ (M₁ + M₂) := by rw [← hk' τ, pow_add]; ring
  have hc := CYCLE K l e a M₁ (M₁ + M₂) he hl0 hl1 Δ k k' hΔ1 hΔp hk1 hk'1 hkk hk
  intro τ
  obtain ⟨g, hg1, hg⟩ := UNITA K (Δ τ) (hΔ1 τ) (hc τ)
  have := hmul τ _ (hΔJ τ) g ⟨1, hg1⟩
  rwa [mul_comm, hg] at this

theorem one_mem : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (l e a M₁ M₂ : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (J : ZMod a → Set K⟦X⟧), (∀ τ, ∀ x ∈ J τ, ∀ y ∈ J τ, x + y ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∃ c : ℝ, ∀ n, ‖coeff n x‖ ≤ c) → (∀ τ, ∃ g ∈ J τ, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → (∀ τ, ∀ h ∈ J (τ - 1), E K l e ^ M₁ * frob K l h ∈ J τ) → (∀ τ, ∀ h ∈ J τ, ∀ i < l, frobSlice l i (E K l e ^ M₂ * h) ∈ J (τ - 1)) → ∀ τ, (1 : K⟦X⟧) ∈ J τ :=
  one_mem_of_frobenius_stable_ideals_boundedPowerSeries GlobalTheory.T.exists_primitive_generator_boundedMultiple_set GlobalTheory.T.norm_constantCoeff_eq_one_of_eisenstein_frobenius_cycle GlobalTheory.T.exists_integral_inverse_powerSeries_of_unit_constantCoeff

end GlobalTheory.BK.GcdCore
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.hsum_mul_eisensteinCompletion_pow_integral : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl), ∃ (N : ℕ) (x : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (x τ i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
  first | exact @GlobalTheory.BKGal.JumpDR.hsum_mul_Ehat_pow | exact GlobalTheory.BKGal.JumpDR.hsum_mul_Ehat_pow | (intros; apply GlobalTheory.BKGal.JumpDR.hsum_mul_Ehat_pow <;> assumption)
end

section

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem invT_invT_gl {R : Type} [CommRing R] (g : GL (Fin a) R) : invT a R (invT a R g) = g := by
  apply Units.ext
  change ((invT a R g)⁻¹).valᵀ = g.val
  rw [← map_inv]
  change ((g⁻¹)⁻¹).valᵀᵀ = g.val
  rw [inv_inv, Matrix.transpose_transpose]

theorem map_invT_gl {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  apply Units.ext
  change p.mapMatrix ((g⁻¹).valᵀ) = ((GeneralLinearGroup.map p g)⁻¹).valᵀ
  rw [← map_inv]
  ext i j
  rfl

theorem invT_infGL (y : GL (Fin a) (Cinf E)) : invT a (Ad E) (infGL E a y) = infGL E a (invT a (Cinf E) y) := by
  apply ga_ext
  · rw [map_invT_gl, pInf_infGL, pInf_infGL]
  · rw [map_invT_gl, pFin_infGL, pFin_infGL, map_one]

theorem norm_toL_transpose (x : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL xᵀ‖ = ‖toL x‖ := by
  have key : ∀ y : Matrix (Fin a) (Fin a) (Cinf E), ‖toL yᵀ‖ ≤ ‖toL y‖ := fun y =>
    pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i => pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun j =>
      (norm_le_pi_norm (toL y j) i).trans (norm_le_pi_norm (toL y) j)
  refine le_antisymm (key x) ?_
  simpa using key xᵀ

theorem height_invT (y : GL (Fin a) (Cinf E)) : height (invT a (Cinf E) y) = height y := by
  change 1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((invT a (Cinf E) y)⁻¹).val‖ = 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖
  rw [← map_inv]
  change 1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((y⁻¹)⁻¹).valᵀ‖ = _
  rw [inv_inv, norm_toL_transpose, norm_toL_transpose]
  ring

theorem isRapidInf_invT {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : IsRapidInf ν k γ) : IsRapidInf ν k (fun x => invT a (Cinf E) (γ x)) := by
  refine ⟨hk.1, ?_, fun N => ?_⟩
  · refine Measurable.of_eval fun i => Measurable.of_eval fun j => Measurable.of_eval fun w => ?_
    set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ :=
      Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
    have e : (fun x => ((invT a (Cinf E) (γ x) : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w) =
        fun x => (((p (γ x))⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i := by
      funext x
      rw [← map_inv]; rfl
    rw [e]
    have hγ : ∀ i' j', Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)) i' j' := fun i' j' =>
      (measurable_pi_apply j').comp ((measurable_pi_apply i').comp hk.2.1)
    exact measurable_comp_GL (F := fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i)
      ((Units.continuous_coe_inv : Continuous fun g : GL (Fin a) ℂ =>
        ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)).matrix_elem j i)
      fun i' j' => (measurable_pi_apply w).comp (hγ i' j')
  · simp only [height_invT]
    exact hk.2.2 N

theorem kerInf_comp_invT {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (F : GA E a → ℂ) (g : GA E a) :
    kerInf ν k γ F (invT a (Ad E) g) =
      kerInf ν k (fun x => invT a (Cinf E) (γ x)) (fun h => F (invT a (Ad E) h)) g := by
  unfold kerInf
  congr 1
  funext x
  show k x * F (invT a (Ad E) g * infGL E a (γ x)) =
    k x * F (invT a (Ad E) (g * infGL E a (invT a (Cinf E) (γ x))))
  rw [map_mul, invT_infGL, invT_invT_gl]

theorem comp_invT_mem_mspanR (π : CuspSub E a) (F : GA E a → ℂ) (hF : F ∈ mspanR π) :
    (fun g => F (invT a (Ad E) g)) ∈ mspanR π.contra := by
  let T : Submodule ℂ (GA E a → ℂ) :=
    (rspan π.contra).comap (LinearMap.funLeft ℂ ℂ (invT a (Ad E)))
  have memT : ∀ G : GA E a → ℂ, G ∈ T ↔ (fun g => G (invT a (Ad E) g)) ∈ rspan π.contra := fun G =>
    Submodule.mem_comap
  have hle : rspan π ≤ T := by
    refine rspan_le (fun φ hφ => ?_) (fun F hF h => ?_) fun F hF X _ ν _ k γ hk => ?_
    · rw [memT]
      have h1 : UpperTheory.V.TC.dualFn E a φ ∈ π.contra.V := Submodule.mem_map_of_mem hφ
      exact mem_rspan h1
    · rw [memT] at hF ⊢
      have h2 := rt_mem_rspan hF (invT a (Ad E) h)
      have e : (fun g => F (invT a (Ad E) g * h)) = fun g => F (invT a (Ad E) (g * invT a (Ad E) h)) := by
        funext g; rw [map_mul, invT_invT_gl]
      rw [e]; exact h2
    · rw [memT] at hF ⊢
      have h3 := kerInf_mem_rspan hF ν (isRapidInf_invT hk)
      have e : (fun g => kerInf ν k γ F (invT a (Ad E) g)) =
          kerInf ν k (fun x => invT a (Cinf E) (γ x)) (fun h => F (invT a (Ad E) h)) :=
        funext fun g => kerInf_comp_invT ν k γ F g
      rw [e]; exact h3
  rw [← rspan_eq_mspanR] at hF ⊢
  exact (memT F).1 (hle hF)

theorem invT_mem_mspanR_contra : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra :=
  fun _ _ _ _ _ π F hF => comp_invT_mem_mspanR π F hF

end GlobalTheory.JSW
end
end

section

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem factorial_pow_dvd_factorial_mul (q k : ℕ) : q.factorial ^ k ∣ (k * q).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (Nat.mul_dvd_mul_right ih _).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem exists_factorial_quot (l q : ℕ) (hl : 0 < l) :
    ∃ (A B : ℕ) (D : ℤ), A * q.factorial = (l * q).factorial ∧ B * q.factorial ^ l = (l * q).factorial ∧
      (A : ℤ) = B + l * D := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨1, 1, 0, by simp, by simp, by simp⟩
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  obtain ⟨c, hc⟩ := factorial_pow_dvd_factorial_mul (p + 1) k
  have h1 := Nat.add_choose_mul_factorial_mul_factorial (k * (p + 1)) (p + 1)
  have h2 := Nat.add_one_mul_choose_eq (k * (p + 1) + p) p
  have h3 : (k * (p + 1) + (p + 1)).choose (p + 1) = (k + 1) * (k * (p + 1) + p).choose p := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos p)
    rw [← add_assoc, ← h2]; simp only [Nat.succ_eq_add_one]; ring
  have h4 : (k + 1) * (p + 1) = k * (p + 1) + (p + 1) := by ring
  set m := (k * (p + 1) + p).choose p
  refine ⟨(k + 1) * m * (k * (p + 1)).factorial, (k + 1) * m * c,
    (m * (k * (p + 1)).factorial : ℕ) - (m * c : ℕ), ?_, ?_, ?_⟩
  · rw [h4, ← h1, h3]
  · rw [h4, ← h1, h3, hc]; ring
  · push_cast; ring

section

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ) [NeZero e]

theorem intCast_div_factorial_mem_QSet (z : ℤ) (m : ℕ) :
    (fun _ => C (C ((z : K) / (m.factorial : K)) * X ^ (e * m)) : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  classical
  refine ⟨Pi.single (0, e * m) (z : Wq l a), ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW, coeff_C]
  by_cases hi : i = 0
  · subst hi
    rw [if_pos rfl, coeff_C_mul, coeff_X_pow]
    by_cases hn : n = e * m
    · subst hn
      simp [dpDen, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (NeZero.ne e))]
    · rw [if_neg hn, Pi.single_eq_of_ne (by simpa using hn)]; simp
  · rw [if_neg hi, Pi.single_eq_of_ne (by simp [hi])]; simp

end

theorem dFam_mem_goodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ q : ℕ, dFam a K e q ∈ GoodSet t e φ₂ := by
  intro l hl a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _ q
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  obtain ⟨A, B, D, hA, hB, hD⟩ := exists_factorial_quot l q hl.out.pos
  have hq : (q.factorial : K) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
  have hlq : ((l * q).factorial : K) ≠ 0 := by exact_mod_cast (l * q).factorial_ne_zero
  have hA' : (A : K) * q.factorial = (l * q).factorial := by exact_mod_cast hA
  have hB' : (B : K) * (q.factorial : K) ^ l = (l * q).factorial := by exact_mod_cast hB
  have hD' : (A : K) = B + l * D := by exact_mod_cast hD
  have eA : (q.factorial : K)⁻¹ = ((A : ℤ) : K) / (l * q).factorial := by
    rw [Int.cast_natCast]; field_simp; rw [← hA']; ring
  have eB : ((q.factorial : K)⁻¹) ^ l = (B : K) / (l * q).factorial := by
    rw [eq_div_iff hlq, ← hB', mul_left_comm, ← mul_pow, inv_mul_cancel₀ hq, one_pow, mul_one]
  have hf : frob2 φ₂ (dFam a K e q) =
      fun _ => C (C (((A : ℤ) : K) / ((l * q).factorial : K)) * X ^ (e * (l * q))) := by
    funext τ
    change φ₂ (dFam a K e q (τ - 1)) = _
    simp only [dFam]
    rw [hC, map_mul, map_pow, frob_C, frob_X, ← pow_mul, eA]
    congr 3; ring
  refine ⟨?_, ?_, _, intCast_div_factorial_mem_QSet t K e D (l * q), ?_⟩
  · have := intCast_div_factorial_mem_QSet t K e 1 q
    rw [Int.cast_one, one_div] at this
    exact this
  · rw [hf]; exact intCast_div_factorial_mem_QSet t K e _ _
  · rw [hf]
    funext τ
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, dFam]
    rw [← map_pow, ← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), ← map_mul, ← map_add (f := _), mul_pow, ← map_pow, eB,
      ← pow_mul, ← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc (C (l : K)), ← map_mul,
      show e * q * l = e * (l * q) by ring, ← add_mul, ← map_add, Int.cast_natCast, hD']
    congr 3; ring

end GlobalTheory.CrysPrism
end
end

section

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem dpDen_mul_dvd_add (e i₁ i₂ n₁ n₂ : ℕ) :
    dpDen e i₁ n₁ * dpDen e i₂ n₂ ∣ dpDen e (i₁ + i₂) (n₁ + n₂) := by
  unfold dpDen
  have h1 := Nat.factorial_mul_factorial_dvd_factorial_add i₁ i₂
  have h2 : (n₁ / e).factorial * (n₂ / e).factorial ∣ ((n₁ + n₂) / e).factorial :=
    (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
      (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div n₁ n₂ e))
  have h3 := mul_dvd_mul h1 h2
  rwa [mul_mul_mul_comm] at h3

theorem mul_mem_QSet_of_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t x hx y hy
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨w', rfl⟩ := hy
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨fun p => ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1, ∑ r ∈ Finset.HasAntidiagonal.antidiagonal p.2,
    ((dpDen e p.1 p.2 / (dpDen e q.1 r.1 * dpDen e q.2 r.2) : ℕ) : Wq l a) *
      (w (q.1, r.1) * w' (q.2, r.2)), ?_⟩
  funext τ
  ext i n

  rw [coeff_ofW, Pi.mul_apply, coeff_mul, map_sum, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun q hq => ?_

  rw [coeff_mul, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [coeff_ofW, coeff_ofW]
  simp only [map_mul, map_natCast]
  have hd := dpDen_mul_dvd_add e q.1 q.2 r.1 r.2
  rw [Finset.HasAntidiagonal.mem_antidiagonal.1 hq, Finset.HasAntidiagonal.mem_antidiagonal.1 hr] at hd
  have h1 : (dpDen e q.1 r.1 : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  have h2 : (dpDen e q.2 r.2 : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  have h3 : (dpDen e i n : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  rw [Nat.cast_div hd (by push_cast; exact mul_ne_zero h1 h2)]
  push_cast
  field_simp

end GlobalTheory.CrysPrism
end
end
