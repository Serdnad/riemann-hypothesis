module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.SetTheory.Cardinal.Continuum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle091
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle083
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle084
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle079
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle085
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle086
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle087
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
import Mathlib.FieldTheory.IsAlgClosed.Classification
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem algClosed_continuum_ringEquiv_complex_extending :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C], Cardinal.mk C = Cardinal.continuum →
      ∀ (K : Type) [Field K] [NumberField K] (i : K →+* C) (s : K →+* ℂ),
        ∃ e : C ≃+* ℂ, ∀ x, e (i x) = s x := by
  intro C _ _ _ hC K _ _ i s
  obtain ⟨e₀⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := C) (L := ℂ)
    (by rw [hC]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [hC, Cardinal.mk_complex]))
  haveI : Countable K :=
    Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.symm.toEquiv
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq K (e₀.toRingHom.comp i) s
  exact ⟨e₀.trans τ, fun x => hτ x⟩

end GlobalTheory
end

section

namespace GlobalTheory

theorem pow_prime_sub_one_norm_le : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by
  intro l _ n _ _ X k hX i j
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  set t : ℝ := (l : ℝ) ^ (-((k : ℤ) + 2)) with ht
  have t0 : 0 ≤ t := by positivity
  have tl : t ≤ (l : ℝ)⁻¹ := by
    rw [ht, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1.le (by omega)
  have t1 : t ≤ 1 := tl.trans (inv_le_one_of_one_le₀ hl1.le)
  have hrhs : (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) = t * (l : ℝ)⁻¹ := by
    rw [ht, show -(((k + 1 : ℕ) : ℤ) + 2) = -((k : ℤ) + 2) + (-1) by push_cast; ring,
      zpow_add₀ hl0, zpow_neg_one]
  rw [hrhs]
  set Y := X - 1 with hY
  have hXY : X = 1 + Y := by rw [hY]; abel
  have hR := GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq ℚ_[l] n Y t t0 t1 hX l i j
  have hsplit : (X ^ l - 1) i j = ((1 + Y) ^ l - 1 - ((l : ℕ) : ℚ_[l]) • Y) i j + (((l : ℕ) : ℚ_[l]) • Y) i j := by
    rw [hXY]; simp
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · calc _ ≤ t ^ 2 := hR
      _ = t * t := sq t
      _ ≤ t * (l : ℝ)⁻¹ := mul_le_mul_of_nonneg_left tl t0
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Padic.norm_p, mul_comm]
    exact mul_le_mul_of_nonneg_right (hX i j) (by positivity)

end GlobalTheory
end

section

open scoped PowerSeries Pointwise

namespace GlobalTheory.FrobIdealDeg

open PowerSeries

variable {O : Type} [CommRing O] (l : ℕ) (hl : 2 ≤ l) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
  (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) =
    if l ∣ m then PowerSeries.coeff (m / l) f else 0)

noncomputable def comps (f : O⟦X⟧) : Fin l → O⟦X⟧ :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).exists.choose

include hφ in
lemma comps_spec (f : O⟦X⟧) :
    f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (comps l hl φ hφ f j) :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).exists.choose_spec

lemma comps_eq {f : O⟦X⟧} {c : Fin l → O⟦X⟧}
    (h : f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (c j)) : comps l hl φ hφ f = c :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).unique (comps_spec l hl φ hφ f) h

lemma comps_add (f f' : O⟦X⟧) :
    comps l hl φ hφ (f + f') = comps l hl φ hφ f + comps l hl φ hφ f' := by
  apply comps_eq
  simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  rw [← comps_spec l hl φ hφ f, ← comps_spec l hl φ hφ f']

lemma comps_zero : comps l hl φ hφ (0 : O⟦X⟧) = 0 := by
  apply comps_eq
  simp

lemma comps_mul_phi (c f : O⟦X⟧) (k : Fin l) :
    comps l hl φ hφ (φ c * f) k = c * comps l hl φ hφ f k := by
  have : comps l hl φ hφ (φ c * f) = fun k => c * comps l hl φ hφ f k := by
    apply comps_eq
    conv_lhs => rw [comps_spec l hl φ hφ f]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring
  rw [this]

include hl hφ in
lemma phi_X : φ PowerSeries.X = PowerSeries.X ^ l := by
  ext m
  rw [hφ, PowerSeries.coeff_X_pow]
  by_cases h1 : l ∣ m
  · obtain ⟨q, rfl⟩ := h1
    rw [if_pos (dvd_mul_right l q), Nat.mul_div_cancel_left q (by omega), PowerSeries.coeff_X]
    by_cases hq : q = 1
    · subst hq; simp
    · rw [if_neg hq, if_neg]
      intro h2
      apply hq
      have : l * q = l * 1 := by simpa using h2
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
  · rw [if_neg h1, if_neg]
    rintro rfl
    exact h1 dvd_rfl

lemma comps_X_pow (t : ℕ) :
    comps l hl φ hφ (PowerSeries.X ^ t) ⟨t % l, Nat.mod_lt _ (Nat.lt_of_lt_of_le (by norm_num) hl)⟩ =
      PowerSeries.X ^ (t / l) := by
  have : comps l hl φ hφ (PowerSeries.X ^ t) = fun j =>
      if j = (⟨t % l, Nat.mod_lt _ (Nat.lt_of_lt_of_le (by norm_num) hl)⟩ : Fin l) then PowerSeries.X ^ (t / l) else 0 := by
    apply comps_eq
    simp only [apply_ite φ, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [map_pow, phi_X l hl φ hφ, ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [this]; simp

lemma descend (J : Ideal O⟦X⟧) (b : ℕ) (f : O⟦X⟧)
    (hf : f ∈ J.map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b}) (k : Fin l) :
    comps l hl φ hφ f k ∈ J ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  clear hf
  rw [comps_add, Pi.add_apply]
  refine Submodule.add_mem_sup ?_ ?_
  · have key : ∀ r : O⟦X⟧, comps l hl φ hφ (r * x) k ∈ J := by
      change x ∈ Submodule.span O⟦X⟧ (φ '' (J : Set O⟦X⟧)) at hx
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, hj, rfl⟩ := hz
        intro r
        rw [mul_comm, comps_mul_phi]
        exact J.mul_mem_right _ hj
      | zero =>
        intro r
        rw [mul_zero, comps_zero]
        exact J.zero_mem
      | add z w _ _ hz hw =>
        intro r
        rw [mul_add, comps_add, Pi.add_apply]
        exact J.add_mem (hz r) (hw r)
      | smul s z _ hz =>
        intro r
        rw [smul_eq_mul, ← mul_assoc]
        exact hz (r * s)
    simpa using key 1
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e : c * (l : O⟦X⟧) ^ b = φ ((l : O⟦X⟧) ^ b) * c := by
      rw [map_pow, map_natCast, mul_comm]
    rw [e, comps_mul_phi]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

lemma pow_mem_binom (e h b : ℕ) (hb : 1 ≤ b) :
    (PowerSeries.X : O⟦X⟧) ^ (e * (h + b - 1)) ∈
      Ideal.span {(PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h} ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  have : (PowerSeries.X : O⟦X⟧) ^ (e * (h + b - 1)) =
      ((PowerSeries.X ^ e + (l : O⟦X⟧)) + (-(l : O⟦X⟧))) ^ (h + b - 1) := by
    rw [pow_mul]; congr 1; ring
  rw [this]
  apply Ideal.add_pow_mem_of_pow_mem_of_le (m := h) (n := b)
  · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  · rw [neg_pow]
    exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  · omega

end GlobalTheory.FrobIdealDeg

namespace GlobalTheory


open GlobalTheory.FrobIdealDeg in
theorem frobenius_ideal_degree_bound : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l →
    ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) =
      if l ∣ m then PowerSeries.coeff (m / l) f else 0) →
    ∀ (a e h b : ℕ) [NeZero a] (I : ZMod a → Ideal O⟦X⟧), 1 ≤ b → h + b ≤ l →
    (∀ τ, ∃ s : ℕ, PowerSeries.X ^ s ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b}) →
    (∀ τ, ∀ x ∈ I τ, (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h * x ∈ (I (τ - 1)).map φ) →
    ∀ τ, (PowerSeries.X : O⟦X⟧) ^ (e * (h + b)) ∈ (I τ).map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  intro O _ l hl φ hφ a e h b _ I hb hhb hs hI
  classical
  have step : ∀ τ t, (PowerSeries.X : O⟦X⟧) ^ t ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} →
      (PowerSeries.X : O⟦X⟧) ^ (t + e * (h + b - 1)) ∈
        (I (τ - 1)).map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
    intro τ t ht
    have hK := pow_mem_binom (O := O) l e h b hb
    obtain ⟨r1, hr1, r2, hr2, hr⟩ := Submodule.mem_sup.mp hK
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ht
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr1
    rw [pow_add, ← hxy, ← hr]
    have hring : (x + y) * (c * (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h + r2) =
        c * ((PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h * x) +
          (y * (c * (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h + r2) + x * r2) := by ring
    rw [hring]
    exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (hI τ x hx))
      (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hy) (Ideal.mul_mem_left _ _ hr2))
  let s : ZMod a → ℕ := fun τ => Nat.find (hs τ)
  have hspec : ∀ τ, (PowerSeries.X : O⟦X⟧) ^ s τ ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} :=
    fun τ => Nat.find_spec (hs τ)
  have down : ∀ τ, l * s τ ≤ s (τ + 1) + e * (h + b - 1) := by
    intro τ
    have h1 := step (τ + 1) (s (τ + 1)) (hspec (τ + 1))
    rw [add_sub_cancel_right] at h1
    have h2 := descend l hl φ hφ (I τ) b _ h1 ⟨(s (τ + 1) + e * (h + b - 1)) % l,
      Nat.mod_lt _ (by omega)⟩
    rw [comps_X_pow] at h2
    have h3 : s τ ≤ (s (τ + 1) + e * (h + b - 1)) / l := Nat.find_min' _ h2
    calc l * s τ ≤ l * ((s (τ + 1) + e * (h + b - 1)) / l) := Nat.mul_le_mul_left _ h3
      _ ≤ s (τ + 1) + e * (h + b - 1) := Nat.mul_div_le _ _
  obtain ⟨τ0, -, hmax⟩ := Finset.exists_max_image Finset.univ s Finset.univ_nonempty
  obtain ⟨n, hn⟩ : ∃ n, h + b - 1 = n := ⟨_, rfl⟩
  have hnl : n + 1 ≤ l := by omega
  have hS : s τ0 ≤ e := by
    have d := down τ0
    have m := hmax (τ0 + 1) (Finset.mem_univ _)
    rw [hn] at d
    by_contra hc
    push_neg at hc
    nlinarith
  intro τ
  have h1 := step (τ + 1) (s (τ + 1)) (hspec (τ + 1))
  rw [add_sub_cancel_right] at h1
  refine Ideal.pow_mem_of_pow_mem _ h1 ?_
  have m := hmax (τ + 1) (Finset.mem_univ _)
  have : e * (h + b) = e * (h + b - 1) + e := by
    rw [← Nat.mul_add_one]; congr 1; omega
  omega

end GlobalTheory
end

section

open scoped NNReal
open Polynomial

namespace GlobalTheory

theorem pow_dvd_pow_mul_pow_of_homogeneous_relation {R : Type*} [CommRing R] (v x : R)
    (q : ℕ → R) (n N : ℕ) (h0 : IsUnit (q 0))
    (h : x ^ N * ∑ i ∈ Finset.range (n + 1), q i * v ^ i * x ^ (n - i) = 0) (j : ℕ) :
    v ^ j ∣ v ^ (N + n) * x ^ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j ≤ N + n
    · exact Dvd.dvd.mul_right (pow_dvd_pow v hj) _
    · obtain ⟨d, rfl⟩ : ∃ d, j = N + n + d := ⟨j - (N + n), by omega⟩
      rw [Finset.sum_range_succ'] at h
      have key : q 0 * (v ^ (N + n) * x ^ (N + n + d)) =
          - ∑ i ∈ Finset.range n,
            v ^ (N + n) * x ^ d * x ^ N * (q (i + 1) * v ^ (i + 1) * x ^ (n - (i + 1))) := by
        rw [← Finset.mul_sum]
        simp only [pow_zero, mul_one, Nat.sub_zero] at h
        linear_combination (v ^ (N + n) * x ^ d) * h
      rw [← h0.dvd_mul_left, key, dvd_neg]
      refine Finset.dvd_sum fun i hi => ?_
      have hi' : i < n := Finset.mem_range.1 hi
      obtain ⟨e, rfl⟩ : ∃ e, n = i + 1 + e := ⟨n - (i + 1), by omega⟩
      obtain ⟨w, hw⟩ := ih (N + e + d) (by omega)
      refine ⟨q (i + 1) * w, ?_⟩
      rw [Nat.add_sub_cancel_left]
      linear_combination (q (i + 1) * v ^ (i + 1)) * hw

theorem bounded_powers_or_exists_valuationSubring_dvd :
    ∀ (R : Type) [CommRing R] (u x : R) (M : ℕ), u ∈ nonZeroDivisors R →
      (∀ r, IsUnit (1 - u * r)) →
      (∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n) ∨
        ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L)
          (f : R →+* ↥V), f u ≠ 0 ∧ ¬ IsUnit (f u) ∧ f x ∣ f u ^ M := by
  intro R _ u x M hu hJ
  let T := Localization.Away (u * x)
  have hux : IsUnit (algebraMap R T (u * x)) := IsLocalization.Away.algebraMap_isUnit (u * x)
  rw [map_mul, IsUnit.mul_iff] at hux
  obtain ⟨huT, hxT⟩ := hux
  obtain ⟨y, hy⟩ := hxT.exists_right_inv
  let t : T := algebraMap R T u ^ M * y
  have ht : algebraMap R T x * t = algebraMap R T u ^ M := by
    simp only [t]
    linear_combination (algebraMap R T u ^ M) * hy
  let S := Algebra.adjoin R ({t} : Set T)
  by_cases hS : IsUnit (algebraMap R S u)
  · left
    obtain ⟨⟨z, hz⟩, hz1⟩ := hS.exists_right_inv
    have hz2 : algebraMap R T u * z = 1 := congrArg Subtype.val hz1
    have hz' := hz
    simp only [S] at hz'
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz'
    obtain ⟨p, hp⟩ := hz'
    have hp' : aeval t p = z := hp
    set q : R[X] := 1 - C u * p with hq
    have hq0 : aeval t q = 0 := by
      simp [hq, hp', hz2]
    have hc : IsUnit (q.coeff 0) := by
      simpa [hq] using hJ (p.coeff 0)
    have hsum : algebraMap R T
        (∑ i ∈ Finset.range (q.natDegree + 1),
          q.coeff i * (u ^ M) ^ i * x ^ (q.natDegree - i)) = 0 := by
      have h1 : algebraMap R T x ^ q.natDegree * aeval t q = 0 := by rw [hq0, mul_zero]
      rw [aeval_eq_sum_range, Finset.mul_sum] at h1

      rw [map_sum, ← h1]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hi'
      rw [he, Nat.add_sub_cancel_left, Algebra.smul_def]
      simp only [map_mul, map_pow]
      rw [← ht]
      ring
    obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (u * x)) T _).1 hsum
    simp only [mul_pow, mul_assoc] at hN
    have hN' := (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hu N)).1 hN
    refine ⟨M * (N + q.natDegree), fun j => ?_⟩
    rw [pow_mul, pow_mul]
    refine pow_dvd_pow_mul_pow_of_homogeneous_relation (u ^ M) x q.coeff _ N hc ?_ j
    simpa only [mul_assoc] using hN'
  · right
    obtain ⟨L, _, _, V, f, hf1, hf2⟩ := GlobalTheory.T.exists_valuationSubring_algClosed_not_isUnit S _ hS
    refine ⟨L, inferInstance, inferInstance, V, f.comp (algebraMap R S), ?_, hf1, ?_⟩
    · refine hf2 _ (mem_nonZeroDivisors_iff_right.2 fun s hs => ?_)
      have h1 : (s : T) * algebraMap R T u = 0 := congrArg Subtype.val hs
      exact Subtype.ext (huT.mul_left_eq_zero.1 h1)
    · refine ⟨f ⟨t, Algebra.self_mem_adjoin_singleton R t⟩, ?_⟩
      simp only [RingHom.comp_apply]
      rw [← map_mul, ← map_pow]
      congr 1
      exact Subtype.ext ht.symm

end GlobalTheory
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.charpoly_monoidAlgebraLift_eq_of_charpoly_eq : ∀ {k G : Type} [Field k] [Monoid G] (n : ℕ) (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ g, (ρ g).charpoly = (σ g).charpoly) → ∀ a : MonoidAlgebra k G, (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ a).charpoly = (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G σ a).charpoly := by
  first | exact @GlobalTheory.charpoly_lift_eq_of_charpoly_eq | exact GlobalTheory.charpoly_lift_eq_of_charpoly_eq | (intros; apply GlobalTheory.charpoly_lift_eq_of_charpoly_eq <;> assumption)
end

section

namespace GlobalTheory

theorem norm_mul_sub_one_le_of_norm_sub_one_le {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] (X Y : Matrix n n E) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ t) (hY : ∀ i j, ‖(Y - 1) i j‖ ≤ t) :
    ∀ i j, ‖(X * Y - 1) i j‖ ≤ t := by
  intro i j
  have hXY : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]; abel
  have hp := GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n (X - 1) (Y - 1) t t h0 h0 hX hY i j
  have htt : t * t ≤ t := by nlinarith
  rw [hXY, Matrix.add_apply, Matrix.add_apply]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp.trans htt))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i j) (hY i j))

theorem congruenceSubgroups_GL_padic : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n],
    ∃ Γ : ℕ → Subgroup (GL n ℚ_[l]), ∀ k X, X ∈ Γ k ↔
      ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  intro l _ n _ _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : ∀ k : ℕ, 0 ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) ∧ (l : ℝ) ^ (-((k : ℤ) + 2)) < 1 := by
    intro k
    refine ⟨zpow_nonneg (by linarith) _, zpow_lt_one_of_neg₀ hl (by omega)⟩
  refine ⟨fun k => {
    carrier := {X | ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))}
    one_mem' := by
      intro i j
      simpa using (ht k).1
    mul_mem' := by
      intro X Y hX hY
      simp only [Set.mem_setOf_eq, Units.val_mul] at *
      exact norm_mul_sub_one_le_of_norm_sub_one_le _ _ _ (ht k).1 (ht k).2.le hX hY
    inv_mem' := by
      intro X hX
      simp only [Set.mem_setOf_eq] at *
      exact GlobalTheory.T.ultrametric_matrix_inv_near_one ℚ_[l] n (X : Matrix n n ℚ_[l]) ((X⁻¹ : GL n ℚ_[l]) : Matrix n n ℚ_[l]) _
        (ht k).1 (ht k).2 (Units.inv_mul X) hX }, fun k X => Iff.rfl⟩

end GlobalTheory
end

section

open Matrix

theorem _root_.GlobalTheory.T.relIndex_standardLattice_transpose_inv_dvr : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (h : GL (Fin r) K), ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map ((((h⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ.mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup.relIndex ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup := by
  first | exact @GlobalTheory.IndexTranspose.relIndex_transpose_inv | exact GlobalTheory.IndexTranspose.relIndex_transpose_inv | (intros; apply GlobalTheory.IndexTranspose.relIndex_transpose_inv <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.setLIntegral_average_abelian_quotient_alt : ∀ (G A : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (Γ U : Subgroup G) [DiscreteTopology Γ], IsClosed (U : Set G) → (∀ γ ∈ Γ, ∀ u ∈ U, γ⁻¹ * u * γ ∈ U) → (∃ K : Set G, IsCompact K ∧ ∀ u ∈ U, ∃ γ ∈ Γ, γ ∈ U ∧ γ * u ∈ K) → ∀ (ι : A → G), (∀ x y, ι (x + y) = ι x * ι y) → Measurable ι → (∀ x, ι x ∈ U) → ∀ (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀], (∀ b ∈ A₀, ι b ∈ Γ) → ∀ (D : Set A), IsAddFundamentalDomain A₀ D ν → ν D = 1 → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (Φ : G → ENNReal), Measurable Φ → (∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) → (∀ u ∈ U, ∃ y : A, ∀ g, Φ (u * g) = Φ (ι y * g)) → ∫⁻ g in 𝓕, Φ g ∂μ = ∫⁻ g in 𝓕, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂μ := by
  first | exact @GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient | exact GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient | (intros; apply GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient <;> assumption)
end

section

open Matrix Finset
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.matrixGaussSum_mul_dual_eq_card_pow_sq : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) * (∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ⁻¹ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) = (Fintype.card k : R) ^ (r ^ 2) := by
  first | exact @GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow | exact GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow | (intros; apply GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow <;> assumption)
end
