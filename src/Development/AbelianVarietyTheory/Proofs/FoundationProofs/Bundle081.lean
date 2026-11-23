module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubringNoMonicFactorisationSpecialisation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoDimRepQuadraticRelation
public import Mathlib.RingTheory.ClassGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle044
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowerSeriesCompletionEmbedding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.Order.Int.LeastGreatest

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem monic_root_norm_le_one_add_sum :
    ∀ (n : ℕ) (s : Fin n → ℂ) (y : ℂ), y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0 →
      ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  intro n s y h
  have hS : 0 ≤ ∑ j, ‖s j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  by_cases hy : ‖y‖ ≤ 1
  · linarith
  push_neg at hy
  cases n with
  | zero => simp at h
  | succ m =>
    have hyn : y ^ (m + 1) = -∑ j, s j * y ^ (j : ℕ) := eq_neg_of_add_eq_zero_left h
    have h1 : ‖y‖ ^ (m + 1) ≤ ∑ j, ‖s j‖ * ‖y‖ ^ (j : ℕ) := by
      rw [← norm_pow, hyn, norm_neg]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [norm_mul, norm_pow]
    have h2 : ∑ j : Fin (m + 1), ‖s j‖ * ‖y‖ ^ (j : ℕ) ≤ (∑ j, ‖s j‖) * ‖y‖ ^ m := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact pow_le_pow_right₀ hy.le (Nat.lt_succ_iff.mp j.isLt)
    have h3 : ‖y‖ ^ (m + 1) = ‖y‖ * ‖y‖ ^ m := pow_succ' _ _
    have hpos : 0 < ‖y‖ ^ m := pow_pos (by linarith) m
    have h4 : ‖y‖ ≤ ∑ j, ‖s j‖ := by
      have h5 := h1.trans h2
      rw [h3] at h5
      exact le_of_mul_le_mul_right h5 hpos
    linarith

end GlobalTheory
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.ValMax

variable {Ω : Type} [Field Ω]

theorem val_int_le_one (V : ValuationSubring Ω) (z : ℤ) : V.valuation (z : Ω) ≤ 1 :=
  V.valuation_le_one ⟨_, intCast_mem V z⟩

theorem val_nat_eq_one (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {n : ℕ} (hn : ¬ q ∣ n) : V.valuation (n : Ω) = 1 := by
  have hc : IsCoprime (q : ℤ) n :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : Ω) * (q : Ω) + (b : Ω) * (n : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) hab
    push_cast at this
    exact this
  have hle : V.valuation (n : Ω) ≤ 1 := by simpa using val_int_le_one V (n : ℤ)
  by_contra hne
  have hlt : V.valuation (n : Ω) < 1 := lt_of_le_of_ne hle hne
  have ha : V.valuation ((a : Ω) * (q : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_int_le_one V a)) hV
  have hb : V.valuation ((b : Ω) * (n : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_int_le_one V b)) hlt
  have := V.valuation.map_add_lt ha hb
  rw [h1, map_one] at this
  exact lt_irrefl _ this

theorem val_nat_eq_pow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, V.valuation (n : Ω) = V.valuation (q : Ω) ^ e := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one
  refine ⟨e, ?_⟩
  push_cast
  rw [map_mul, map_pow, val_nat_eq_one V hq hV hm, mul_one]

variable [Algebra ℚ Ω]

theorem val_q_ne_zero (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime) :
    V.valuation (q : Ω) ≠ 0 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rw [Valuation.ne_zero_iff]
  exact Nat.cast_ne_zero.2 hq.ne_zero

theorem val_rat_eq_zpow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {r : ℚ} (hr : r ≠ 0) :
    ∃ e : ℤ, V.valuation (algebraMap ℚ Ω r) = V.valuation (q : Ω) ^ e := by
  have h0 := val_q_ne_zero V hq
  obtain ⟨e1, h1⟩ := val_nat_eq_pow V hq hV (n := r.num.natAbs)
    (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hr))
  obtain ⟨e2, h2⟩ := val_nat_eq_pow V hq hV (n := r.den) r.den_nz
  have h3 : V.valuation ((r.num : ℤ) : Ω) = V.valuation (q : Ω) ^ e1 := by
    rw [← h1]
    rcases Int.natAbs_eq r.num with h | h
    · conv_lhs => rw [h]
      simp only [Int.cast_natCast]
    · conv_lhs => rw [h]
      simp only [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]
  refine ⟨(e1 : ℤ) - e2, ?_⟩
  have h4 : algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) / ((r.den : ℕ) : Ω) := by
    conv_lhs => rw [← Rat.num_div_den r]
    rw [map_div₀, map_intCast, map_natCast]
  rw [h4, map_div₀, h3, h2, zpow_sub₀ h0, zpow_natCast, zpow_natCast]

theorem val_pow_sub (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0)
    {i k : ℕ} (h : V.valuation (r • x ^ i) = V.valuation (s • x ^ (i + k))) :
    ∃ e : ℤ, V.valuation x ^ k = V.valuation (q : Ω) ^ e := by
  have h0 := val_q_ne_zero V hq
  obtain ⟨e1, h1⟩ := val_rat_eq_zpow V hq hV hr
  obtain ⟨e2, h2⟩ := val_rat_eq_zpow V hq hV hs
  have hx0 : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, h1, h2, map_pow, map_pow, pow_add,
    mul_comm (V.valuation x ^ i), ← mul_assoc] at h
  have h3 := mul_right_cancel₀ (pow_ne_zero i hx0) h
  refine ⟨e1 - e2, ?_⟩
  rw [zpow_sub₀ h0, h3, mul_div_cancel_left₀ _ (zpow_ne_zero _ h0)]

theorem val_pow_eq_zpow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) (hi : IsIntegral ℚ x) :
    ∃ k : ℕ, 0 < k ∧ k ≤ (minpoly ℚ x).natDegree ∧
      ∃ e : ℤ, V.valuation x ^ k = V.valuation (q : Ω) ^ e := by
  classical
  set p := minpoly ℚ x with hp
  set f : ℕ → Ω := fun i => p.coeff i • x ^ i with hf
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1), f i = 0 := by
    rw [← Polynomial.aeval_eq_sum_range]
    exact minpoly.aeval ℚ x
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (p.natDegree + 1))
    (fun i => V.valuation (f i)) ⟨0, by simp⟩
  have hj0 : V.valuation (f j) ≠ 0 := by
    intro h
    have h1 := hmax p.natDegree (by simp)
    have h2 : f p.natDegree = x ^ p.natDegree := by
      have : p.coeff p.natDegree = 1 := (minpoly.monic hi).coeff_natDegree
      simp only [hf, this, one_smul]
    rw [h, h2, le_zero_iff, Valuation.zero_iff] at h1
    exact pow_ne_zero _ hx h1
  have hex : ∃ i ∈ Finset.range (p.natDegree + 1) \ {j}, ¬ V.valuation (f i) < V.valuation (f j) := by
    by_contra hcon
    push Not at hcon
    have := V.valuation.map_sum_eq_of_lt hj hcon
    rw [hsum, map_zero] at this
    exact hj0 this.symm
  obtain ⟨i, hi', hlt⟩ := hex
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hi'
  have heq : V.valuation (f i) = V.valuation (f j) :=
    le_antisymm (hmax i hi'.1) (not_lt.1 hlt)
  have hcj : p.coeff j ≠ 0 := by
    intro h
    apply hj0
    simp only [hf, h, zero_smul, map_zero]
  have hci : p.coeff i ≠ 0 := by
    intro h
    apply hj0
    rw [← heq]
    simp only [hf, h, zero_smul, map_zero]
  have hi1 := Finset.mem_range.1 hi'.1
  have hj1 := Finset.mem_range.1 hj
  rcases lt_or_gt_of_ne hi'.2 with hij | hij
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij.le
    exact ⟨k, by omega, by omega, val_pow_sub V hq hV hx hci hcj heq⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij.le
    exact ⟨k, by omega, by omega, val_pow_sub V hq hV hx hcj hci heq.symm⟩

theorem val_pow_factorial (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) (hi : IsIntegral ℚ x) {n : ℕ}
    (hn : (minpoly ℚ x).natDegree ≤ n) :
    ∃ e : ℤ, V.valuation x ^ n.factorial = V.valuation (q : Ω) ^ e := by
  obtain ⟨k, hk0, hk, e, he⟩ := val_pow_eq_zpow V hq hV hx hi
  obtain ⟨m, hm⟩ := Nat.dvd_factorial hk0 (hk.trans hn)
  exact ⟨e * m, by rw [hm, pow_mul, he, _root_.zpow_mul, zpow_natCast]⟩

theorem natDegree_minpoly_le {K L : Type} [Field K] [Field L] [Algebra K L]
    (F : IntermediateField K L) [FiniteDimensional K F] {x : L} (hx : x ∈ F) :
    (minpoly K x).natDegree ≤ Module.finrank K F := by
  have h1 : (minpoly K (⟨x, hx⟩ : F)).natDegree ≤ Module.finrank K F :=
    minpoly.natDegree_le _
  rwa [IntermediateField.minpoly_eq] at h1

theorem exists_max_valuation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (F : IntermediateField ℚ Ω), FiniteDimensional ℚ F → ∀ (q : ℕ), q.Prime → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (ι : Type) (a : ι → Ω) (c : Ω), c ≠ 0 → (∀ i, a i ∈ F) → (∀ i, c * a i ∈ V) → (∃ i, a i ≠ 0) → ∃ i, a i ≠ 0 ∧ ∀ i', V.valuation (a i') ≤ V.valuation (a i) := by
  intro Ω _ _ _ F hF q hq V hV ι a c hc haF hca hex
  rw [ValuationSubring.mem_nonunits_iff] at hV
  have h0 := val_q_ne_zero V hq
  have hpos : 0 < V.valuation (q : Ω) := zero_lt_iff.2 h0
  have hint : ∀ x : Ω, IsIntegral ℚ x := fun x =>
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral
  set n := Module.finrank ℚ F + (minpoly ℚ c).natDegree with hn
  obtain ⟨e0, he0⟩ := val_pow_factorial V hq hV hc (hint c) (n := n) (by omega)
  have hall : ∀ i, a i ≠ 0 →
      ∃ e : ℤ, V.valuation (a i) ^ n.factorial = V.valuation (q : Ω) ^ e := by
    intro i hi
    refine val_pow_factorial V hq hV hi (hint _) ?_
    exact (natDegree_minpoly_le F (haF i)).trans (Nat.le_add_right _ _)
  obtain ⟨e, ⟨i, hi, he⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun e : ℤ => ∃ i, a i ≠ 0 ∧ V.valuation (a i) ^ n.factorial = V.valuation (q : Ω) ^ e)
    ⟨-e0, by
      rintro z ⟨i, -, hz⟩
      have h1 : V.valuation (c * a i) ≤ 1 := V.valuation_le_one ⟨_, hca i⟩
      have h2 : V.valuation (c * a i) ^ n.factorial ≤ 1 := pow_le_one' h1 _
      rw [map_mul, mul_pow, he0, hz, ← zpow_add₀ h0, ← zpow_zero (V.valuation (q : Ω)),
        zpow_le_zpow_iff_right_of_lt_one₀ hpos hV] at h2
      omega⟩
    (by
      obtain ⟨i, hi⟩ := hex
      obtain ⟨e, he⟩ := hall i hi
      exact ⟨e, i, hi, he⟩)
  refine ⟨i, hi, fun i' => ?_⟩
  by_cases hi' : a i' = 0
  · rw [hi', map_zero]
    exact zero_le'
  obtain ⟨e', he'⟩ := hall i' hi'
  have h1 : V.valuation (a i') ^ n.factorial ≤ V.valuation (a i) ^ n.factorial := by
    rw [he, he', zpow_le_zpow_iff_right_of_lt_one₀ hpos hV]
    exact hmin e' ⟨i', hi', he'⟩
  by_contra hcon
  exact absurd h1 (not_le.2 (pow_lt_pow_left₀ (not_le.1 hcon) zero_le' n.factorial_ne_zero))

end GlobalTheory.ValMax
end

section

open Polynomial

namespace GlobalTheory

theorem exists_ne_zero_forall_point_extend_subalgebra :
    ∀ (k A R : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [CommRing R] [IsDomain R] [Algebra k R] (ξ : A →ₐ[k] R),
    Function.Injective ξ → ∀ T : Finset R,
    ∃ (a : A) (S : Subalgebra k R) (hξ : ∀ u, ξ u ∈ S), a ≠ 0 ∧ (∀ t ∈ T, t ∈ S) ∧
      ∀ φ : A →ₐ[k] k, φ a ≠ 0 → ∃ ψ : S →ₐ[k] k, ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := by
  intro k A R _ _ _ _ _ _ _ _ _ ξ hinj T
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  set S : Subalgebra k R := Algebra.adjoin k (ξ '' (s : Set A) ∪ (T : Set R)) with hSdef
  have hξ : ∀ u, ξ u ∈ S := by
    intro u
    have hu : u ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have : ξ u ∈ (Algebra.adjoin k (s : Set A)).map ξ := ⟨u, hu, rfl⟩
    rw [AlgHom.map_adjoin] at this
    exact Algebra.adjoin_mono Set.subset_union_left this
  have hT : ∀ t ∈ T, t ∈ S := fun t ht => Algebra.subset_adjoin (Set.subset_union_right ht)
  have hSfg : S.FG := Subalgebra.fg_def.2
    ⟨_, (s.finite_toSet.image ξ).union T.finite_toSet, rfl⟩
  haveI : Algebra.FiniteType k S := (Subalgebra.fg_iff_finiteType S).1 hSfg
  let f : A →ₐ[k] S := ξ.codRestrict S hξ
  letI : Algebra A S := f.toRingHom.toAlgebra
  haveI : IsScalarTower k A S := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  haveI : Algebra.FiniteType A S := Algebra.FiniteType.of_restrictScalars_finiteType k A S
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hfinj : Function.Injective (algebraMap A S) := by
    intro x y h
    apply hinj
    have := congrArg Subtype.val h
    exact this
  have hfp : Algebra.FinitePresentation A S := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  have hc := PrimeSpectrum.isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr hfp)
  obtain ⟨q, hq, H⟩ := exists_basicOpen_subset_of_isConstructible_of_bot_mem hc
    ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hfinj)⟩
  refine ⟨q, S, hξ, hq, hT, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom_extend_of_ker_mem_range_comap (A := S) φ.toRingHom
    (H ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime _⟩ (by simpa [RingHom.mem_ker] using hφ))
  have hψu : ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := fun u => by
    have := RingHom.congr_fun hψ u
    exact this
  refine ⟨{ ψ with commutes' := fun c => ?_ }, hψu⟩
  have h1 : (algebraMap k S c) = ⟨ξ (algebraMap k A c), hξ _⟩ := by
    ext; simp
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe]
  rw [h1, hψu, φ.commutes]

end GlobalTheory
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_subring_no_monic_factorisation_specialisation : ∀ {F : Type} [Field F] [IsAlgClosed F] (Φ : Polynomial (Polynomial F)), Φ.Monic → Irreducible Φ → ∃ s : Finset F, ∃ Ψ : Polynomial (Polynomial (Subring.closure (s : Set F))), Ψ.map (Polynomial.mapRingHom (Subring.closure (s : Set F)).subtype) = Φ ∧ ∀ (k : Type) [Field k] (φ : Subring.closure (s : Set F) →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic → A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
  first | exact @GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation | exact GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation | (intros; apply GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.two_dim_rep_quadratic_relation : ∀ {E : Type} [Field E] [IsAlgClosed E], (2 : E) ≠ 0 → ∀ {G : Type} [Group G] (ρ : G →* GL (Fin 2) E), (∀ W : Submodule E (Fin 2 → E), (∀ g w, w ∈ W → (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U] (σ : G →* Module.End E U), (∀ g, σ g * σ g - Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) • σ g + Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) • (1 : Module.End E U) = 0) → ∃ (m : ℕ) (π : Fin m → U →ₗ[E] (Fin 2 → E)) (s : Fin m → (Fin 2 → E) →ₗ[E] U), (∀ i g, π i ∘ₗ σ g = Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E) ∘ₗ π i) ∧ (∀ i g, σ g ∘ₗ s i = s i ∘ₗ Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E)) ∧ (∀ i j, π i ∘ₗ s j = if i = j then LinearMap.id else 0) ∧ ∑ i, s i ∘ₗ π i = LinearMap.id := by
  first | exact @GlobalTheory.CayleyHamiltonId.isotypic_of_quadratic_relation | exact GlobalTheory.CayleyHamiltonId.isotypic_of_quadratic_relation | (intros; apply GlobalTheory.CayleyHamiltonId.isotypic_of_quadratic_relation <;> assumption)
end

section

open Polynomial

namespace GlobalTheory

theorem classGroup_nthPower_of_codim_one_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  intro k A _ _ _ _ _ _ _ N _hN hyp hf c
  obtain ⟨f, hf0, hfm⟩ := hf
  obtain ⟨_hfin, hmax, hadd, _hle⟩ := GlobalTheory.T.dedekind_finiteType_ideal_codimension k A
  have nz : ∀ I : Ideal A, I ≠ ⊥ → I ∈ nonZeroDivisors (Ideal A) := fun I hI =>
    mem_nonZeroDivisors_of_ne_zero hI
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hI0 : (I : Ideal A) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  by_cases hex : ∃ P₀ : Ideal A, P₀.IsMaximal ∧ P₀ ≠ ⊥
  swap
  · push_neg at hex
    have htop : (I : Ideal A) = ⊤ := by
      by_contra h
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ h
      exact hI0 (le_bot_iff.mp (hex M hM ▸ hIM))
    refine ⟨1, ?_⟩
    have : I = 1 := Subtype.ext (by rw [htop]; exact Ideal.one_eq_top.symm)
    rw [this, map_one, one_pow]
  obtain ⟨P₀, hP₀, hP₀ne⟩ := hex
  let H : Subgroup (ClassGroup A) := (powMonoidHom N : ClassGroup A →* ClassGroup A).range
  let π : ClassGroup A →* ClassGroup A ⧸ H := QuotientGroup.mk' H
  have hπ : ∀ d : ClassGroup A, π (d ^ N) = 1 := fun d =>
    (QuotientGroup.eq_one_iff _).mpr ⟨d, rfl⟩
  let γ : ClassGroup A := ClassGroup.mk0 ⟨P₀, nz P₀ hP₀ne⟩
  have hbot : ¬ (⊥ : Ideal A).IsMaximal := fun h =>
    hP₀ne (h.eq_of_le hP₀.ne_top bot_le).symm
  have hjac : ∀ x : A, x ≠ 0 → ∃ Q : Ideal A, Q.IsMaximal ∧ x ∉ Q := by
    intro x hx
    haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
    have hj : (⊥ : Ideal A).jacobson = ⊥ :=
      IsJacobsonRing.out' _ (Ideal.isPrime_bot).isRadical
    by_contra hne
    push_neg at hne
    apply hx
    have : x ∈ (⊥ : Ideal A).jacobson := by
      rw [Ideal.jacobson]
      exact Submodule.mem_sInf.mpr fun J hJ => hne J hJ.2
    rw [hj] at this
    exact (Submodule.mem_bot A).mp this
  have hmaxcls : ∀ (P : Ideal A) (hP : P.IsMaximal) (hPne : P ≠ ⊥),
      π (ClassGroup.mk0 ⟨P, nz P hPne⟩) = π γ := by
    intro P hP hPne
    obtain ⟨a₀, ha₀, H0⟩ := hyp P₀ hP₀ (nz P₀ hP₀ne)
    obtain ⟨a₁, ha₁, H1⟩ := hyp P hP (nz P hPne)
    obtain ⟨Q, hQ, hQa⟩ := hjac (a₀ * a₁) (mul_ne_zero ha₀ ha₁)
    have hQne : Q ≠ ⊥ := by rintro rfl; exact hbot hQ
    obtain ⟨d, hd⟩ := H0 Q hQ (fun h => hQa (Q.mul_mem_right _ h)) (nz Q hQne)
    obtain ⟨e, he⟩ := H1 Q hQ (fun h => hQa (Q.mul_mem_left _ h)) (nz Q hQne)
    have h1 := congrArg π hd
    have h2 := congrArg π he
    rw [map_mul, hπ, mul_one] at h1 h2
    rw [← h2, h1]
  have hall : ∀ J : Ideal A, ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J) := by
    intro J
    refine UniqueFactorizationMonoid.induction_on_prime (P := fun J : Ideal A => ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J)) J ?_ ?_ ?_
    · intro h; exact absurd rfl (nonZeroDivisors.ne_zero h)
    · intro x hx h
      have hx' : x = ⊤ := Ideal.isUnit_iff.mp hx
      subst hx'
      have e1 : (⟨⊤, h⟩ : nonZeroDivisors (Ideal A)) = 1 := Subtype.ext Ideal.one_eq_top.symm
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [e1, map_one, map_one, Module.finrank_zero_of_subsingleton, pow_zero]
    · intro a p ha hp ih h
      have hpne : p ≠ ⊥ := hp.ne_zero
      have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpne
      have e1 : (⟨p * a, h⟩ : nonZeroDivisors (Ideal A)) = ⟨p, nz p hpne⟩ * ⟨a, nz a ha⟩ := rfl
      rw [e1, map_mul, map_mul, hmaxcls p hpmax hpne, ih (nz a ha), hadd p a hpne ha,
        (hmax p hpmax).1, pow_add, pow_one]
  have hγN : π γ ^ N = 1 := by rw [← map_pow]; exact hπ γ
  have hspan : Ideal.span {f} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hf0
  have hγ1 : π γ = 1 := by
    have e := hall _ (nz _ hspan)
    have e0 : ClassGroup.mk0 (⟨Ideal.span {f}, nz _ hspan⟩ : nonZeroDivisors (Ideal A)) = 1 :=
      (ClassGroup.mk0_eq_one_iff _).mpr ⟨⟨f, rfl⟩⟩
    rw [e0, map_one] at e
    calc π γ = π γ ^ (1 % N) := by rw [← pow_eq_pow_mod 1 hγN, pow_one]
      _ = π γ ^ (Module.finrank k (A ⧸ Ideal.span {f}) % N) := by rw [hfm]
      _ = 1 := by rw [← pow_eq_pow_mod _ hγN, ← e]
  have hc := hall I.1 I.2
  rw [hγ1, one_pow] at hc
  have hmem : ClassGroup.mk0 I ∈ H := (QuotientGroup.eq_one_iff _).mp hc
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, hd.symm⟩

end GlobalTheory
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_power_series_completion_embedding : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (Q : Ideal A), Q.IsMaximal → Q ≠ ⊥ → ∃ (σ : A →ₐ[k] PowerSeries k) (π : A), σ π = PowerSeries.X ∧ Function.Injective σ ∧ (∀ (m : ℕ) (u : A), u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ σ u) ∧ ∀ (m : ℕ) (φ : PowerSeries k), ∃ u : A, (PowerSeries.X : PowerSeries k) ^ m ∣ φ - σ u := by
  first | exact @GlobalTheory.CurveCompletion.exists_completion_embedding | exact GlobalTheory.CurveCompletion.exists_completion_embedding | (intros; apply GlobalTheory.CurveCompletion.exists_completion_embedding <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_rootOfUnity_close_of_pow_reduces_one : ∀ {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field K] [Algebra Ω K] (W : ValuationSubring K) (x : K) (N : ℕ), 0 < N → W.valuation (x ^ N - 1) < 1 → ∃ ζ : Ω, ζ ^ N = 1 ∧ W.valuation (x - algebraMap Ω K ζ) < 1 := by
  first | exact @GlobalTheory.exists_root_of_unity_close_of_pow_close | exact GlobalTheory.exists_root_of_unity_close_of_pow_close | (intros; apply GlobalTheory.exists_root_of_unity_close_of_pow_close <;> assumption)
end
