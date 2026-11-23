module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle064
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle068
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

namespace GroundTheory.LocalField.FormalGroup

open IsLocalRing

section Approximation

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem smodEq_pow_iff_sub_mem {x y : R} {n : ℕ} :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem exists_limit_of_approx [IsPrecomplete I R] (P : ℕ → R → Prop)
    (hstep : ∀ n x, P n x → ∃ y, y - x ∈ I ^ n ∧ P (n + 1) y) {x₀ : R} (h₀ : P 0 x₀) :
    ∃ x, ∀ n, ∃ y, P n y ∧ x - y ∈ I ^ n :=
  by apply _root_.UpperTheory.Reformulated.B.Qp1.exists_limit_of_approx <;> assumption

theorem exists_eq_zero_of_approx [IsAdicComplete I R] (F : R → R)
    (hF : ∀ n x y, x - y ∈ I ^ n → F x - F y ∈ I ^ n)
    (hstep : ∀ n x, F x ∈ I ^ n → ∃ y, y - x ∈ I ^ n ∧ F y ∈ I ^ (n + 1))
    {m : ℕ} {x₀ : R} (h₀ : F x₀ ∈ I ^ m) : ∃ x, F x = 0 ∧ x - x₀ ∈ I ^ m := by
  obtain ⟨x, hx⟩ := exists_limit_of_approx I (fun n y => F y ∈ I ^ (m + n) ∧ y - x₀ ∈ I ^ m)
    (fun n y ⟨h1, h2⟩ => by
      obtain ⟨z, hz1, hz2⟩ := hstep (m + n) y h1
      refine ⟨z, Ideal.pow_le_pow_right (by omega) hz1, hz2, ?_⟩
      have e : z - x₀ = (z - y) + (y - x₀) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) hz1) h2)
    ⟨by simpa using h₀, by simp⟩
  refine ⟨x, ?_, ?_⟩
  · refine IsHausdorff.haus (I := I) inferInstance _ fun n => ?_
    rw [smodEq_pow_iff_sub_mem, sub_zero]
    obtain ⟨y, ⟨hy1, _⟩, hy⟩ := hx n
    have e : F x = (F x - F y) + F y := by ring
    rw [e]
    exact Ideal.add_mem _ (hF n x y hy) (Ideal.pow_le_pow_right (by omega) hy1)
  · obtain ⟨y, ⟨_, hy2⟩, hy⟩ := hx m
    have e : x - x₀ = (x - y) + (y - x₀) := by ring
    rw [e]
    exact Ideal.add_mem _ hy hy2

end Approximation

section HidaSetting

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

theorem isLocalHom_of_map_maximalIdeal
    (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsLocalHom (algebraMap A B) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 h
  have := Ideal.mem_map_of_mem (algebraMap A B) hm
  rw [hunr] at this
  exact (mem_maximalIdeal _).1 this ha

theorem irreducible_algebraMap (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    {π : A} (hπ : Irreducible π) : Irreducible (algebraMap A B π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hπ ⊢
  rw [← hunr, hπ, Ideal.map_span, Set.image_singleton]

theorem mem_maximalIdeal_pow_iff {ϖ : B} (hϖ : Irreducible ϖ) {x : B} {n : ℕ} :
    x ∈ maximalIdeal B ^ n ↔ ϖ ^ n ∣ x := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

end HidaSetting

section Solve

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Finite (ResidueField A)] [IsAlgClosed (ResidueField B)]
  (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))

theorem one_lt_card_residueField : 1 < Nat.card (ResidueField A) :=
  Finite.one_lt_card


include hσ in
theorem exists_residue_sub_mul_add_eq_zero (v w : B) :
    ∃ z : B, residue B (σ z - v * z + w) = 0 := by
  open Polynomial in
  set q := Nat.card (ResidueField A)
  have hq : 1 < q := one_lt_card_residueField
  set a := residue B v
  set b := residue B w
  have hlow : (C b - C a * X : (ResidueField B)[X]).degree < (X ^ q : (ResidueField B)[X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast (by omega : 0 < q))
    · exact lt_of_le_of_lt (degree_C_mul_X_le a) (by exact_mod_cast hq)
  have hdeg : (X ^ q + (C b - C a * X) : (ResidueField B)[X]).degree = q := by
    rw [degree_add_eq_left_of_degree_lt hlow, degree_X_pow]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (X ^ q + (C b - C a * X) : (ResidueField B)[X])
    (by rw [hdeg]; exact_mod_cast (by omega : q ≠ 0))
  obtain ⟨z', rfl⟩ := residue_surjective z
  refine ⟨z', ?_⟩
  simp only [IsRoot, eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hz
  rw [map_add (f := _), map_sub, map_mul, hσ]
  linear_combination hz

variable {π : A} (hπB : Irreducible (algebraMap A B π))
include hσ hπB

theorem exists_sub_mul_eq_of_mem [IsAdicComplete (maximalIdeal B) B] (v c : B) {m : ℕ} {x₀ : B}
    (h₀ : σ x₀ - v * x₀ - c ∈ maximalIdeal B ^ m) :
    ∃ x, σ x - v * x = c ∧ x - x₀ ∈ maximalIdeal B ^ m := by
  set ϖ := algebraMap A B π
  have hσϖ : ∀ (n : ℕ) (t : B), σ (ϖ ^ n * t) = ϖ ^ n * σ t := by
    intro n t
    rw [map_mul, map_pow, AlgHom.commutes]
  obtain ⟨x, hx, hxm⟩ := exists_eq_zero_of_approx (maximalIdeal B) (fun x => σ x - v * x - c)
    (fun n x y hxy => by
      rw [mem_maximalIdeal_pow_iff hπB] at hxy ⊢
      obtain ⟨t, ht⟩ := hxy
      refine ⟨σ t - v * t, ?_⟩
      have : x = y + ϖ ^ n * t := by rw [← ht]; ring
      simp only [this, map_add (f := _), hσϖ]
      ring)
    (fun n x hx => by
      rw [mem_maximalIdeal_pow_iff hπB] at hx
      obtain ⟨w, hw⟩ := hx
      obtain ⟨z, hz⟩ := exists_residue_sub_mul_add_eq_zero σ hσ v w
      rw [residue_eq_zero_iff, hπB.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
      obtain ⟨t, ht⟩ := hz
      refine ⟨x + ϖ ^ n * z, ?_, ?_⟩
      · rw [mem_maximalIdeal_pow_iff hπB]
        exact ⟨z, by ring⟩
      · rw [mem_maximalIdeal_pow_iff hπB]
        refine ⟨t, ?_⟩
        simp only [map_add (f := _), hσϖ]
        have e : σ x - v * x - c = ϖ ^ n * w := hw
        linear_combination e + ϖ ^ n * ht)
    h₀
  exact ⟨x, sub_eq_zero.1 (by simpa using hx), hxm⟩

theorem exists_units_eq_mul [IsAdicComplete (maximalIdeal B) B] (v : Bˣ) :
    ∃ η : Bˣ, σ η = v * η := by
  set q := Nat.card (ResidueField A)
  have hq : 1 < q := one_lt_card_residueField
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (residue B v) (n := q - 1) (by omega)
  have hv0 : residue B v ≠ 0 := (residue_ne_zero_iff_isUnit _).2 v.isUnit
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact hv0 hz.symm
  obtain ⟨z', rfl⟩ := residue_surjective z
  have h₀ : σ z' - v * z' - 0 ∈ maximalIdeal B ^ 1 := by
    rw [pow_one, ← residue_eq_zero_iff, sub_zero, map_sub, map_mul, hσ]
    have e : residue B z' ^ q = residue B z' ^ (q - 1) * residue B z' := by
      rw [← pow_succ]; congr 1; omega
    rw [e, hz, sub_self]
  obtain ⟨x, hx, hxm⟩ := exists_sub_mul_eq_of_mem σ hσ hπB v 0 h₀
  have hxu : IsUnit x := by
    rw [← residue_ne_zero_iff_isUnit]
    rw [pow_one, ← residue_eq_zero_iff, map_sub, sub_eq_zero] at hxm
    rwa [hxm]
  refine ⟨hxu.unit, ?_⟩
  simpa [sub_eq_zero] using hx

end Solve

section Kernel

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Finite (ResidueField A)] [IsAlgClosed (ResidueField B)] [IsAdicComplete (maximalIdeal B) B]
  (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))

include hunr hσ
end Kernel
end FormalGroup
end LocalField
end GroundTheory
end

section

namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries

section Subst

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem le_order_subst_sub_subst {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {f g : MvPowerSeries σ R} {n : ℕ∞}
    (h : n ≤ order (f - g)) : n ≤ order (subst a f - subst a g) := by
  rw [← subst_sub ha]
  refine le_trans ?_ (le_order_subst ha (f - g))
  have h1 : 1 ≤ ⨅ i, (a i).order :=
    le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha0 i)
  calc n ≤ 1 * order (f - g) := by simpa using h
    _ ≤ _ := by gcongr

private def Close (n k : ℕ∞) (u v : MvPowerSeries τ S) : Prop :=
  k ≤ order u ∧ k ≤ order v ∧ n + k ≤ order (u - v) + 1

private lemma close_one (n : ℕ∞) : Close n 0 (1 : MvPowerSeries τ S) 1 := by
  refine ⟨by simp, by simp, ?_⟩
  simp

private lemma close_mul {n k l : ℕ∞} {u v u' v' : MvPowerSeries τ S} (h : Close n k u v)
    (h' : Close n l u' v') : Close n (k + l) (u * u') (v * v') := by
  obtain ⟨hu, hv, huv⟩ := h
  obtain ⟨hu', hv', huv'⟩ := h'
  refine ⟨(add_le_add hu hu').trans (le_order_mul), (add_le_add hv hv').trans (le_order_mul), ?_⟩
  have e : u * u' - v * v' = (u - v) * u' + v * (u' - v') := by ring
  rw [e]
  refine le_trans ?_ (add_le_add min_order_le_add le_rfl)
  rw [← min_add_add_right]
  refine le_min ?_ ?_
  · calc n + (k + l) = (n + k) + l := by rw [add_assoc]
      _ ≤ (order (u - v) + 1) + order u' := add_le_add huv hu'
      _ = (order (u - v) + order u') + 1 := by rw [add_right_comm]
      _ ≤ order ((u - v) * u') + 1 := add_le_add le_order_mul le_rfl
  · calc n + (k + l) = k + (n + l) := by rw [add_left_comm]
      _ ≤ order v + (order (u' - v') + 1) := add_le_add hv huv'
      _ = (order v + order (u' - v')) + 1 := by rw [add_assoc]
      _ ≤ order (v * (u' - v')) + 1 := add_le_add le_order_mul le_rfl

private lemma close_pow {n k : ℕ∞} {u v : MvPowerSeries τ S} (h : Close n k u v) (m : ℕ) :
    Close n (m * k) (u ^ m) (v ^ m) := by
  induction m with
  | zero => simpa using close_one (τ := τ) (S := S) n
  | succ m ih =>
    have := close_mul ih h
    rw [pow_succ, pow_succ]
    convert this using 1
    push_cast
    ring

private lemma close_prod {ι : Type*} (s : Finset ι) {n : ℕ∞} {k : ι → ℕ∞}
    {u v : ι → MvPowerSeries τ S} (h : ∀ i ∈ s, Close n (k i) (u i) (v i)) :
    Close n (∑ i ∈ s, k i) (∏ i ∈ s, u i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using close_one (τ := τ) (S := S) n
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact close_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma close_monomial {n : ℕ∞} {a b : σ → MvPowerSeries τ S}
    (h : ∀ i, Close n 1 (a i) (b i)) (d : σ →₀ ℕ) :
    Close n (d.degree : ℕ∞) (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  have := close_prod d.support (k := fun i => (d i : ℕ∞) * 1) (u := fun i => a i ^ d i)
    (v := fun i => b i ^ d i) (fun i _ => close_pow (h i) (d i))
  simpa [Finsupp.prod, Finsupp.degree_apply] using this

theorem add_le_order_subst_sub_subst {a b : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (hb : HasSubst b) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hb0 : ∀ i, constantCoeff (b i) = 0) {n : ℕ∞} (hab : ∀ i, n ≤ order (a i - b i))
    {f : MvPowerSeries σ R} {m : ℕ∞} (hf : m ≤ order f) :
    n + m ≤ order (subst a f - subst b f) + 1 := by
  have hclose : ∀ i, Close n 1 (a i) (b i) := fun i =>
    ⟨one_le_order_iff_constCoeff_eq_zero.2 (ha0 i),
      one_le_order_iff_constCoeff_eq_zero.2 (hb0 i), add_le_add (hab i) le_rfl⟩

  have hcoeff : ∀ e : τ →₀ ℕ, (e.degree : ℕ∞) + 1 < n + m →
      coeff e (subst a f - subst b f) = 0 := by
    intro e he
    rw [map_sub, coeff_subst ha, coeff_subst hb,
      ← finsum_sub_distrib (coeff_subst_finite ha f e) (coeff_subst_finite hb f e)]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    by_cases hd : coeff d f = 0
    · simp [hd]
    rw [← smul_sub, ← map_sub]
    obtain ⟨-, -, hdc⟩ := close_monomial hclose d
    have hmd : m ≤ (d.degree : ℕ∞) := hf.trans (order_le hd)
    have : (e.degree : ℕ∞) + 1 < order ((d.prod fun s e => a s ^ e) -
        (d.prod fun s e => b s ^ e)) + 1 :=
      he.trans_le ((add_le_add le_rfl hmd).trans hdc)
    rw [coeff_of_lt_order ((ENat.add_lt_add_iff_right ENat.one_ne_top).1 this), smul_zero]
  by_contra hlt
  rw [not_le] at hlt
  have hfin : (order (subst a f - subst b f)).toNat = order (subst a f - subst b f) := by
    refine ENat.natCast_toNat fun htop => ?_
    rw [htop] at hlt
    simp at hlt
  obtain ⟨e, he, hdeg⟩ := exists_coeff_ne_zero_and_order hfin
  exact he (hcoeff e (by rw [hdeg]; exact hlt))

end Subst

section FixedPoint

variable {σ R : Type*} [CommRing R]

theorem existsUnique_fixedPoint (Φ : MvPowerSeries σ R → MvPowerSeries σ R)
    (hΦ : ∀ f g : MvPowerSeries σ R, ∀ n : ℕ, (n : ℕ∞) ≤ order (f - g) →
      ((n + 1 : ℕ) : ℕ∞) ≤ order (Φ f - Φ g)) :
    ∃! f, Φ f = f :=
  _root_.UpperTheory.Reformulated.B.Ydb5.existsUnique_fixedPoint Φ hΦ

end FixedPoint

end GroundTheory.LocalField.FormalGroup
end
