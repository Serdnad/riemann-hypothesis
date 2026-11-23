module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle494
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle463
import GroundTheory.LocalFields.Uniqueness
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem unit_of_sub_mem {A : Type} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {x z : A} (hx : IsUnit x) (h : z - x ∈ I) : IsUnit z := by
  have hj := (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot I h)) (↑hx.unit⁻¹ : A)
  have e : z = x * ((z - x) * ↑hx.unit⁻¹ + 1) := by
    linear_combination (-(z - x)) * hx.mul_val_inv
  rw [e]
  exact hx.mul hj

private theorem prod_one_add {A : Type} [CommRing A] (b : ℕ → A) (r : A) (d : ℕ) :
    ∃ c, ∏ i ∈ Finset.range d, (1 + b i * r) =
      1 + (∑ i ∈ Finset.range d, b i) * r + r ^ 2 * c := by
  induction d with
  | zero => exact ⟨0, by simp⟩
  | succ d ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (∑ i ∈ Finset.range d, b i) * b d + r * c * b d, ?_⟩
    rw [Finset.prod_range_succ, Finset.sum_range_succ, hc]
    ring

private theorem itN_mul {A : Type} [CommRing A] (τ : A ≃+* A) (d : ℕ) (y w : A) :
    itN τ d (y * w) = itN τ d y * itN τ d w := by
  have key : ∀ i, (⇑τ)^[i] (y * w) = (⇑τ)^[i] y * (⇑τ)^[i] w := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]
  simp only [itN, key, Finset.prod_mul_distrib]

private theorem itN_fixed {A : Type} [CommRing A] (τ : A ≃+* A) (d : ℕ)
    (hd : ∀ x, τ^[d] x = x) (y : A) : τ (itN τ d y) = itN τ d y := by
  unfold itN
  rw [map_prod]
  simp only [← Function.iterate_succ_apply' (⇑τ)]
  cases d with
  | zero => simp
  | succ m =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i => (⇑τ)^[i] y), hd y]
    rfl

private theorem step {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A) (d : ℕ)
    (hd : ∀ x, τ^[d] x = x) (a : A) (ha : ∑ i ∈ Finset.range d, τ^[i] a = 1)
    (x : A) (hτx : τ x = x) (n : ℕ) (hn : n ≠ 0) (y : A) (hu : IsUnit (itN τ d y))
    (h : itN τ d y - x ∈ I ^ n) :
    ∃ y', y' - y ∈ I ^ n ∧ itN τ d y' - x ∈ I ^ (n + 1) := by
  set N := itN τ d y with hN
  set v : A := ↑hu.unit⁻¹ with hv
  have hNv : N * v = 1 := hu.mul_val_inv
  have hNfix : τ N = N := itN_fixed τ d hd y
  have hvfix : τ v = v := by
    have h1 : τ N * τ v = 1 := by rw [← map_mul, hNv, map_one]
    rw [hNfix] at h1
    calc τ v = (N * v) * τ v := by rw [hNv, one_mul]
      _ = v * (N * τ v) := by ring
      _ = v := by rw [h1, mul_one]
  have hwfix : τ ((x - N) * v) = (x - N) * v := by rw [map_mul, map_sub, hτx, hNfix, hvfix]
  have hit : ∀ i (z : A), (⇑τ)^[i] z = ((τ : A →+* A) ^ i) z := by
    intro i z
    rw [RingHom.coe_pow]
    rfl
  have hwit : ∀ i, (⇑τ)^[i] ((x - N) * v) = (x - N) * v := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ih, hwfix]
  have hwI : (x - N) * v ∈ I ^ n := by
    apply Ideal.mul_mem_right
    rw [← neg_sub]
    exact neg_mem h
  obtain ⟨c, hc⟩ := prod_one_add (fun i => (⇑τ)^[i] a) ((x - N) * v) d
  beta_reduce at hc
  refine ⟨y * (1 + a * ((x - N) * v)), ?_, ?_⟩
  · have e : y * (1 + a * ((x - N) * v)) - y = (y * a) * ((x - N) * v) := by ring
    rw [e]
    exact Ideal.mul_mem_left _ _ hwI
  · have e1 : itN τ d (1 + a * ((x - N) * v)) = ∏ i ∈ Finset.range d, (1 + (⇑τ)^[i] a * ((x - N) * v)) := by
      unfold itN
      apply Finset.prod_congr rfl
      intro i _
      rw [hit, map_add (f := _), map_one, map_mul, ← hit, ← hit, hwit]
    rw [itN_mul, ← hN, e1, hc, ha]
    have e2 : N * (1 + 1 * ((x - N) * v) + ((x - N) * v) ^ 2 * c) - x = N * c * ((x - N) * v) ^ 2 := by
      linear_combination (x - N) * hNv
    rw [e2]
    apply Ideal.mul_mem_left
    have h2 : ((x - N) * v) ^ 2 ∈ I ^ (n * 2) := by
      rw [pow_mul]
      exact Ideal.pow_mem_pow hwI 2
    exact Ideal.pow_le_pow_right (by omega) h2

private theorem tau_pow_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (n : ℕ) {z : A} (h : z ∈ I ^ n) : τ z ∈ I ^ n := by
  have h1 : Ideal.map τ I ≤ I := Ideal.map_le_iff_le_comap.mpr (fun x hx => hI x hx)
  have h2 : τ z ∈ Ideal.map τ (I ^ n) := Ideal.mem_map_of_mem τ h
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

private theorem iter_pow_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (n i : ℕ) {z : A} (h : z ∈ I ^ n) : τ^[i] z ∈ I ^ n := by
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact tau_pow_mem I τ hI n ih

private theorem itN_sub_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (d n : ℕ) {u v : A} (h : u - v ∈ I ^ n) :
    itN τ d u - itN τ d v ∈ I ^ n := by
  have hs : ∀ i, (⇑τ)^[i] u - (⇑τ)^[i] v ∈ I ^ n := by
    intro i
    have e : ∀ j, (⇑τ)^[j] u - (⇑τ)^[j] v = (⇑τ)^[j] (u - v) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ← map_sub, ih]
    rw [e]
    exact iter_pow_mem I τ hI n i h
  unfold itN
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have e2 : (∏ i ∈ Finset.range d, (⇑τ)^[i] u) * (⇑τ)^[d] u - (∏ i ∈ Finset.range d, (⇑τ)^[i] v) * (⇑τ)^[d] v
        = (∏ i ∈ Finset.range d, (⇑τ)^[i] u - ∏ i ∈ Finset.range d, (⇑τ)^[i] v) * (⇑τ)^[d] u
          + (∏ i ∈ Finset.range d, (⇑τ)^[i] v) * ((⇑τ)^[d] u - (⇑τ)^[d] v) := by
      ring
    rw [e2]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ih) (Ideal.mul_mem_left _ _ (hs d))

private theorem mem_smul_top {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (z : A) :
    z ∈ (I ^ n • ⊤ : Submodule A A) ↔ z ∈ I ^ n := by
  simp

theorem normAdic : NormAdic := by
  intro A _ I _ τ d hd hI a ha x y hx hτx hy
  have hunit : ∀ n : ℕ, ∀ z : A, itN τ d z - x ∈ I ^ (n + 1) → IsUnit (itN τ d z) := by
    intro n z hz
    exact unit_of_sub_mem I hx (Ideal.pow_le_self (Nat.succ_ne_zero n) hz)
  have hstep : ∀ n : ℕ, ∀ z : A, itN τ d z - x ∈ I ^ (n + 1) →
      ∃ z', z' - z ∈ I ^ (n + 1) ∧ itN τ d z' - x ∈ I ^ (n + 1 + 1) := by
    intro n z hz
    exact step I τ d hd a ha x hτx (n + 1) (Nat.succ_ne_zero n) z (hunit n z hz) hz
  choose! g hg1 hg2 using hstep
  let f : ℕ → A := fun k => Nat.rec (motive := fun _ => A) y (fun k z => g k z) k
  have hf0 : f 0 = y := rfl
  have hfs : ∀ k, f (k + 1) = g k (f k) := fun k => rfl
  have hfN : ∀ k, itN τ d (f k) - x ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa [hf0] using hy
    | succ k ih =>
      rw [hfs]
      exact hg2 k (f k) ih
  have hfd : ∀ k, f (k + 1) - f k ∈ I ^ (k + 1) := by
    intro k
    rw [hfs]
    exact hg1 k (f k) (hfN k)
  have hcauchy : ∀ m k, f m - f (m + k) ∈ I ^ m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : f m - f (m + (k + 1)) = (f m - f (m + k)) - (f (m + k + 1) - f (m + k)) := by
        rw [← add_assoc]
        ring
      rw [e]
      refine Ideal.sub_mem _ ih ?_
      exact Ideal.pow_le_pow_right (by omega) (hfd (m + k))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance (f := f) (by
    intro m n hmn
    rw [SModEq.sub_mem, mem_smul_top]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hcauchy m k)
  refine ⟨L, ?_⟩
  have hzero := IsHausdorff.haus (I := I) (M := A) inferInstance (itN τ d L - x) (by
    intro n
    rw [SModEq.sub_mem, sub_zero, mem_smul_top]
    have h1 : itN τ d L - itN τ d (f n) ∈ I ^ n := by
      apply itN_sub_mem I τ hI d n
      have h0 := SModEq.sub_mem.mp (hL n)
      rw [mem_smul_top] at h0
      rw [← neg_sub]
      exact neg_mem h0
    have h2 : itN τ d (f n) - x ∈ I ^ n := Ideal.pow_le_pow_right (by omega) (hfN n)
    have e : itN τ d L - x = (itN τ d L - itN τ d (f n)) + (itN τ d (f n) - x) := by ring
    rw [e]
    exact Ideal.add_mem _ h1 h2)
  exact sub_eq_zero.mp hzero

end UpperTheory.Gal.InertialTypesAlt.L
end

section

open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem pow_finrank_aut {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    (s : K ≃ₐ[k] K) : s ^ Module.finrank k K = 1 := by
  classical
  have h1 : Nat.card (⊤ : Subgroup (K ≃ₐ[k] K)) ∣ Module.finrank k K := by
    rw [← IntermediateField.finrank_fixedField_eq_card,
      ← (letI : Module.Free (IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K))) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank k (IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K))) K)]
    exact dvd_mul_left _ _
  rw [Subgroup.card_top] at h1
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard s).trans h1)

private theorem partial_twConj {k K : Type} [Field k] [Field K] [Algebra k K] (s : K ≃ₐ[k] K) (n : ℕ)
    (δ g : GL (Fin n) K) (m : ℕ) :
    (List.ofFn fun j : Fin m => GlobalTheory.LBC.galAct (s ^ (j : ℕ)) n (g⁻¹ * δ * GlobalTheory.LBC.galAct s n g)).prod =
      g⁻¹ * (List.ofFn fun j : Fin m => GlobalTheory.LBC.galAct (s ^ (j : ℕ)) n δ).prod * GlobalTheory.LBC.galAct (s ^ m) n g := by
  induction m with
  | zero => simp [GlobalTheory.LBC.galAct_one]
  | succ m ih =>
    rw [List.ofFn_succ', List.ofFn_succ', List.prod_concat, List.prod_concat]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    have e : GlobalTheory.LBC.galAct (s ^ m) n (GlobalTheory.LBC.galAct s n g) = GlobalTheory.LBC.galAct (s ^ (m + 1)) n g := by
      rw [pow_succ, GlobalTheory.LBC.galAct_mul, MonoidHom.comp_apply]
    rw [map_mul, map_mul, map_inv, e]
    group

private theorem norm_tw {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] (s : K ≃ₐ[k] K)
    (n : ℕ) (δ g : GL (Fin n) K) :
    GlobalTheory.LBC.norm k s (g⁻¹ * δ * GlobalTheory.LBC.galAct s n g) = g⁻¹ * GlobalTheory.LBC.norm k s δ * g := by
  unfold GlobalTheory.LBC.norm
  rw [partial_twConj, pow_finrank_aut, GlobalTheory.LBC.galAct_one, MonoidHom.id_apply]

private theorem fb_eq_of_isFinNorm {F₀ F₁ : Type} [Field F₀] [Field F₁] [Algebra F₀ F₁] [Finite F₁]
    (sb : F₁ ≃ₐ[F₀] F₁) {n : ℕ} (fb : GL (Fin n) F₀ → ℂ) (hfb : ∀ a b, fb (b⁻¹ * a * b) = fb a)
    {δ : GL (Fin n) F₁} {γ γ' : GL (Fin n) F₀} (h : IsFinNorm sb δ γ) (h' : IsFinNorm sb δ γ') :
    fb γ' = fb γ := by
  have hc : IsConj γ' γ := GlobalTheory.Shin.isConj_of_isConj_incl F₀ F₁ n γ' γ (h'.trans h.symm)
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have := hfb γ' c⁻¹
  rw [inv_inv] at this
  rw [← this, hc]

end UpperTheory.Gal.InertialTypesAlt.L

theorem UpperTheory.Gal.InertialTypesAlt.L.liftVal :
    UpperTheory.Gal.InertialTypesAlt.L.LiftVal := by
  intro F₀ F₁ _ _ _ _ _ sb _ n fb hfb
  haveI : FiniteDimensional F₀ F₁ := Module.Finite.of_finite
  refine ⟨fun δ γ h => ?_, fun δ x => ?_⟩
  · have hex : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ := ⟨γ, h⟩
    rw [GlobalTheory.DZA.normLift, dite_eq_left hex]
    exact UpperTheory.Gal.InertialTypesAlt.L.fb_eq_of_isFinNorm sb fb hfb h hex.choose_spec
  · have hiff : ∀ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ ↔ GlobalTheory.DZA.IsFinNorm sb δ γ := by
      intro γ
      have hc : IsConj (GlobalTheory.LBC.norm F₀ sb δ) (GlobalTheory.LBC.norm F₀ sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x)) := by
        rw [UpperTheory.Gal.InertialTypesAlt.L.norm_tw]
        refine isConj_iff.mpr ⟨x⁻¹, ?_⟩
        simp
      exact ⟨fun h => IsConj.trans h hc.symm, fun h => IsConj.trans h hc⟩
    have hfun : (fun γ => GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ) =
        fun γ => GlobalTheory.DZA.IsFinNorm sb δ γ := funext fun γ => propext (hiff γ)
    by_cases hex : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ
    · obtain ⟨γ, hγ⟩ := hex
      have h1 : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ := ⟨γ, hγ⟩
      have h2 : ∃ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ := ⟨γ, (hiff γ).2 hγ⟩
      rw [GlobalTheory.DZA.normLift, GlobalTheory.DZA.normLift, dite_eq_left h1, dite_eq_left h2]
      exact (UpperTheory.Gal.InertialTypesAlt.L.fb_eq_of_isFinNorm sb fb hfb ((hiff _).1 h2.choose_spec) h1.choose_spec).symm
    · have h2 : ¬ ∃ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ :=
        fun ⟨γ, hγ⟩ => hex ⟨γ, (hiff γ).1 hγ⟩
      rw [GlobalTheory.DZA.normLift, GlobalTheory.DZA.normLift, dite_eq_right hex, dite_eq_right h2]
end

section

noncomputable section

open ValuativeRel

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K]

private theorem mem_int' (s : K ≃ₐ[k] K) (x : 𝒪[K]) : s (x : K) ∈ 𝒪[K] := by
  have hx := x.2
  rw [Valuation.mem_integer_iff] at hx ⊢
  rwa [GroundTheory.LocalField.valuation_algEquiv_apply k K s (x : K)]

variable {F₀ F₁ : Type} [Field F₀] [Fintype F₀] [Field F₁] [Algebra F₀ F₁]
    {rk : 𝒪[k] →+* F₀} {rK : 𝒪[K] →+* F₁} {s : K ≃ₐ[k] K} {sb : F₁ ≃ₐ[F₀] F₁}

private theorem pow_red' (h : IsRes rk rK s sb) (j : ℕ) (x y : 𝒪[K]) (hy : (y : K) = (s ^ j) x) :
    rK y = (sb ^ j) (rK x) := by
  induction j generalizing y with
  | zero =>
    have hyx : y = x := Subtype.ext (by simpa using hy)
    subst hyx
    simp
  | succ j ih =>
    let z : 𝒪[K] := ⟨(s ^ j) x, mem_int' (s ^ j) x⟩
    have hz : rK z = (sb ^ j) (rK x) := ih z rfl
    have hyz : (y : K) = s (z : K) := by
      rw [hy, pow_succ']
      rfl
    rw [h.gal z y hyz, hz, pow_succ']
    rfl

private theorem finrank_dvd' [Fintype F₁] (h : IsRes rk rK s sb) :
    Module.finrank k K ∣ orderOf s := by
  classical
  haveI : Algebra.IsAlgebraic F₀ F₁ := Algebra.IsAlgebraic.of_finite F₀ F₁
  have hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [h.frob z]
    rfl
  have hone : sb ^ orderOf s = 1 := by
    ext w
    obtain ⟨x, rfl⟩ := h.onto₁ w
    have := pow_red' h (orderOf s) x x (by rw [pow_orderOf_eq_one]; rfl)
    rw [AlgEquiv.one_apply, ← this]
  rw [← h.deg, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁, ← hsb]
  exact orderOf_dvd_of_pow_eq_one hone

private theorem isGalois_of_isRes [Fintype F₁] (h : IsRes rk rK s sb) : IsGalois k K := by
  classical
  have hd := finrank_dvd' h
  have hpos : 0 < orderOf s := orderOf_pos s
  have hle1 : orderOf s ≤ Fintype.card (K ≃ₐ[k] K) := orderOf_le_card_univ
  have hle2 : Fintype.card (K ≃ₐ[k] K) ≤ Module.finrank k K := AlgEquiv.card_le
  have hle3 : Module.finrank k K ≤ orderOf s := Nat.le_of_dvd hpos hd
  apply IsGalois.of_card_aut_eq_finrank
  rw [Nat.card_eq_fintype_card]
  omega

end

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.derive :
    UpperTheory.Gal.InertialTypesAlt.L.Derive := by
  intro k K _ _ _ _ _ _ _ _ _ hc F₀ F₁ _ _ _ _ _ rk rK s sb h
  haveI hv : ValuativeExtension k K := GlobalTheory.LBC.Inh.valuativeExtension hc
  have hpos : 0 < Module.finrank k K := by
    rw [← h.deg]
    exact Module.finrank_pos
  haveI hf : FiniteDimensional k K := Module.finite_of_finrank_pos hpos
  exact ⟨hv, hf, isGalois_of_isRes h⟩
end
end

section

theorem UpperTheory.Gal.InertialTypesAlt.L.hilbert_ninety_frobenius_twisted_finite_algebra :
    UpperTheory.Gal.InertialTypesAlt.L.FrobeniusTwistedHilbertNinety := by
  intro F₀ F₁ _ _ _ _ _ sb hsb A _ _ _ τ hτ hd c hc
  classical
  have hfrob : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hsb]
  have hgen : ∀ t : F₁ ≃ₐ[F₀] F₁, t ∈ Subgroup.zpowers sb := by
    intro t
    obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F₀ F₁).2 t
    rw [← hi, ← hfrob]
    exact Subgroup.npow_mem_zpowers _ _
  have hG : UpperTheory.ConvolutionTheory.D.IsGal sb (Module.finrank F₀ F₁) := UpperTheory.ConvolutionTheory.D.galField F₀ F₁ sb hgen
  let S : Subring A := (τ : A →+* A).eqLocus (RingHom.id A)
  let f : F₀ →+* S := ((algebraMap F₁ A).comp (algebraMap F₀ F₁)).codRestrict S (fun z => by
    change τ (algebraMap F₁ A (algebraMap F₀ F₁ z)) = algebraMap F₁ A (algebraMap F₀ F₁ z)
    rw [hτ, AlgEquiv.commutes])
  letI : Algebra F₀ S := f.toAlgebra
  haveI : Module.Finite F₀ S := Module.Finite.of_finite
  let σ : A ≃ₐ[S] A := AlgEquiv.ofRingEquiv (f := τ) (fun r => r.2)
  have hpow : ∀ (j : ℕ) (x : A), (σ ^ j) x = τ^[j] x := by
    intro j x
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, Function.iterate_succ_apply']
      rfl
  have hpowF : ∀ (j : ℕ) (z : F₁), τ^[j] (algebraMap F₁ A z) = algebraMap F₁ A ((sb ^ j) z) := by
    intro j z
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, hτ, pow_succ', AlgEquiv.mul_apply]
  have hGal : UpperTheory.ConvolutionTheory.D.IsGal σ (Module.finrank F₀ F₁) := by
    refine ⟨hG.pos, AlgEquiv.ext fun x => ?_, Subtype.val_injective, fun r hr => ⟨⟨r, hr⟩, rfl⟩, ?_⟩
    · rw [hpow, hd]; rfl
    · obtain ⟨s, x, y, h⟩ := hG.sep
      refine ⟨s, fun i => algebraMap F₁ A (x i), fun i => algebraMap F₁ A (y i), fun j hj => ?_⟩

      simp only [hpow, hpowF, ← map_mul, ← map_sum]
      rw [h j hj]
      split_ifs <;> simp
  have hu : IsUnit c := by
    have h1 : c ∣ UpperTheory.Gal.InertialTypesAlt.L.itN τ (Module.finrank F₀ F₁) c :=
      Finset.dvd_prod_of_mem (fun i => τ^[i] c) (Finset.mem_range.2 hG.pos)
    rw [hc] at h1
    exact isUnit_of_dvd_one h1
  obtain ⟨z, hz⟩ := UpperTheory.ConvolutionTheory.D.h90 F₀ F₀ S A σ _ hGal hu.unit (by
    simp only [hpow, IsUnit.unit_spec]
    exact hc)
  exact ⟨z, hz⟩
end
