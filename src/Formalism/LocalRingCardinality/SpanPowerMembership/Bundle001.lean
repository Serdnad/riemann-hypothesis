module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Basic.Finite.Prod

@[expose] public section

section

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions

end Formalism.BasicNotions.Examples₂
end
end

section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open MonoidAlgebra

variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

def tens (x : ∀ i, MonoidAlgebra k (G i)) : MonoidAlgebra k (∀ i, G i) :=
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g => ∏ i, (x i).coeff (g i)

theorem tens_coeff (x : ∀ i, MonoidAlgebra k (G i)) (g : ∀ i, G i) :
    (tens x).coeff g = ∏ i, (x i).coeff (g i) := rfl

theorem coeff_mul_fintype {Γ : Type} [Group Γ] [Fintype Γ] (x y : MonoidAlgebra k Γ) (g : Γ) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]

theorem tens_mul (x y : ∀ i, MonoidAlgebra k (G i)) : tens x * tens y = tens fun i => x i * y i := by
  classical
  have : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [coeff_mul_fintype, tens_coeff]
  simp only [tens_coeff, coeff_mul_fintype, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

theorem tens_eq_zero (x : ∀ i, MonoidAlgebra k (G i)) (i : I) (h : x i = 0) : tens x = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [tens_coeff]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)

theorem tens_single [DecidableEq I] (g : ∀ i, G i) : tens (fun i => (single (g i) 1 : MonoidAlgebra k (G i))) = single g 1 := by
  classical
  apply MonoidAlgebra.coeff_injective
  ext h
  rw [tens_coeff, MonoidAlgebra.coeff_single_apply]
  simp only [MonoidAlgebra.coeff_single_apply]
  by_cases e : g = h
  · subst e; simp
  · rw [if_neg e]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp e
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem commute_of_single {Γ : Type} [Group Γ] (z : MonoidAlgebra k Γ)
    (h : ∀ g : Γ, z * single g 1 = single g 1 * z) (a : MonoidAlgebra k Γ) : z * a = a * z := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]
  | single g r =>
    have e : (single g r : MonoidAlgebra k Γ) = r • single g 1 := by rw [smul_single', mul_one]
    rw [e, mul_smul_comm, smul_mul_assoc, h]

theorem tens_central (x : ∀ i, MonoidAlgebra k (G i)) (h : ∀ i a, x i * a = a * x i)
    (a : MonoidAlgebra k (∀ i, G i)) : tens x * a = a * tens x := by
  classical
  refine commute_of_single _ (fun g => ?_) a
  rw [← tens_single, tens_mul, tens_mul]
  exact congrArg tens (funext fun i => h i _)

variable {L : I → Type} [∀ i, Fintype (L i)] [DecidableEq I] (E : ∀ i, L i → MonoidAlgebra k (G i))
  (S : (∀ i, L i) → Prop)


open Classical in
def eSum : MonoidAlgebra k (∀ i, G i) :=
  open Classical in ∑ a : (∀ i, L i), if S a then tens (fun i => E i (a i)) else 0

variable (hidem : ∀ i l, E i l * E i l = E i l) (hcen : ∀ i l a, E i l * a = a * E i l)
  (horth : ∀ i l l', l ≠ l' → E i l * E i l' = 0)

include hcen in
theorem eSum_central (a : MonoidAlgebra k (∀ i, G i)) : eSum E S * a = a * eSum E S := by
  classical
  unfold eSum
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs
  · exact tens_central _ (fun i => hcen i _) a
  · simp

include hidem horth in
theorem tens_mul_tens (a b : ∀ i, L i) : tens (fun i => E i (a i)) * tens (fun i => E i (b i)) =
    open Classical in if a = b then tens (fun i => E i (a i)) else 0 := by
  rw [tens_mul]
  split_ifs with e
  · subst e; exact congrArg tens (funext fun i => hidem i _)
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp e
    exact tens_eq_zero _ i (horth i _ _ hi)

include hidem horth in
theorem eSum_mul_tens (b : ∀ i, L i) : eSum E S * tens (fun i => E i (b i)) =
    open Classical in if S b then tens (fun i => E i (b i)) else 0 := by
  classical
  unfold eSum
  rw [Finset.sum_mul, Finset.sum_eq_single b]
  · split_ifs
    · rw [tens_mul_tens E hidem horth, if_pos rfl]
    · simp
  · intro a _ hab
    split_ifs
    · rw [tens_mul_tens E hidem horth, if_neg hab]
    · simp
  · intro h; exact absurd (Finset.mem_univ b) h

include hidem horth in
theorem eSum_idem : eSum E S * eSum E S = eSum E S := by
  classical
  conv_lhs => rhs; unfold eSum
  rw [Finset.mul_sum]
  unfold eSum
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with hb
  · have := eSum_mul_tens E S hidem horth b
    rw [if_pos hb] at this
    exact this
  · simp


theorem eSum_coeff (g : ∀ i, G i) : (eSum E S).coeff g =
    open Classical in ∑ a : (∀ i, L i), if S a then ∏ i, (E i (a i)).coeff (g i) else 0 := by
  classical
  unfold eSum
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rfl
  · rfl

end Formalism.BasicNotions.Examples₂.NZ
end
end

section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.GatR

open QuadraticAlgebra IsLocalRing

variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {ϖ : W}

theorem om_sq : (ω : QuadraticAlgebra W ϖ 0) ^ 2 = algebraMap W _ ϖ := by
  rw [sq, algebraMap_eq]; ext <;> simp

theorem om_pow (n : ℕ) : (ω : QuadraticAlgebra W ϖ 0) ^ (2 * n) = algebraMap W _ (ϖ ^ n) := by
  rw [pow_mul, om_sq, map_pow]

theorem isUnit_of_re (hϖ : Irreducible ϖ) (z : QuadraticAlgebra W ϖ 0) (h : IsUnit z.re) : IsUnit z := by
  rw [isUnit_iff_norm_isUnit, norm_def]
  by_contra hn
  have h1 : ϖ * z.im * z.im ∈ nonunits W := fun hu =>
    hϖ.not_isUnit (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu))
  have h2 := nonunits_add (show _ ∈ nonunits W from hn) h1
  have e : z.re * z.re + 0 * z.re * z.im - ϖ * z.im * z.im + ϖ * z.im * z.im = z.re * z.re := by ring
  rw [e] at h2
  exact h2 (h.mul h)

theorem om_not_isUnit (hϖ : Irreducible ϖ) : ¬ IsUnit (ω : QuadraticAlgebra W ϖ 0) := by
  rw [isUnit_iff_norm_isUnit, norm_def]
  simp only [omega_re, omega_im]
  intro h
  have e : (0 : W) * 0 + 0 * 0 * 1 - ϖ * 1 * 1 = -ϖ := by ring
  rw [e, IsUnit.neg_iff] at h
  exact hϖ.not_isUnit h

theorem fact (hϖ : Irreducible ϖ) (z : QuadraticAlgebra W ϖ 0) (hz : z ≠ 0) :
    ∃ (n : ℕ) (u : QuadraticAlgebra W ϖ 0), IsUnit u ∧ z = ω ^ n * u := by
  have caseB : ∀ (j : ℕ) (v : Wˣ) (a' : W), z.im = v * ϖ ^ j → z.re = ϖ ^ (j + 1) * a' →
      ∃ (n : ℕ) (u : QuadraticAlgebra W ϖ 0), IsUnit u ∧ z = ω ^ n * u := fun j v a' h1 h2 => by
    refine ⟨2 * j + 1, ⟨v, a'⟩, isUnit_of_re hϖ _ v.isUnit, ?_⟩
    rw [pow_succ, om_pow, algebraMap_eq]
    ext
    · simp only [re_mul, im_mul, omega_re, omega_im, re_C, im_C, h2]; ring
    · simp only [re_mul, im_mul, omega_re, omega_im, re_C, im_C, h1]; ring
  by_cases ha : z.re = 0
  · have hb : z.im ≠ 0 := fun hb => hz (by ext <;> simp [ha, hb])
    obtain ⟨j, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
    exact caseB j v 0 hv (by rw [ha, mul_zero])
  · obtain ⟨i, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    by_cases hd : ϖ ^ i ∣ z.im
    · obtain ⟨b', hb'⟩ := hd
      refine ⟨2 * i, ⟨u, b'⟩, isUnit_of_re hϖ _ u.isUnit, ?_⟩
      rw [om_pow, algebraMap_eq]
      ext
      · simp [← map_pow, hu]; ring
      · simp [← map_pow, hb']
    · have hb : z.im ≠ 0 := fun hb => hd (by rw [hb]; exact dvd_zero _)
      obtain ⟨j, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
      have hji : j < i := by
        by_contra hc
        exact hd (hv ▸ Dvd.dvd.mul_left (pow_dvd_pow ϖ (not_lt.mp hc)) _)
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hji
      exact caseB j v (u * ϖ ^ c) hv (by rw [hu]; ring)

theorem om_pow_ne_zero (hϖ : Irreducible ϖ) (n : ℕ) : (ω : QuadraticAlgebra W ϖ 0) ^ n ≠ 0 := by
  intro h
  have h2 : (ω : QuadraticAlgebra W ϖ 0) ^ (2 * n) = 0 := by rw [two_mul, pow_add, h, mul_zero]
  rw [om_pow, map_eq_zero_iff _ algebraMap_injective] at h2
  exact pow_ne_zero n hϖ.ne_zero h2

theorem isDomain (hϖ : Irreducible ϖ) : IsDomain (QuadraticAlgebra W ϖ 0) := by
  have : NoZeroDivisors (QuadraticAlgebra W ϖ 0) := ⟨fun {x y} hxy => by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hc.1
    obtain ⟨m, v, hv, rfl⟩ := fact hϖ y hc.2
    have e : ω ^ n * u * (ω ^ m * v) = ω ^ (n + m) * (u * v) := by ring
    rw [e] at hxy
    exact om_pow_ne_zero hϖ (n + m) ((hu.mul hv).mul_left_eq_zero.mp hxy)⟩
  exact NoZeroDivisors.to_isDomain _

theorem om_irreducible (hϖ : Irreducible ϖ) : Irreducible (ω : QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  refine ⟨om_not_isUnit hϖ, fun x y hxy => ?_⟩
  have h0 : (ω : QuadraticAlgebra W ϖ 0) ≠ 0 := by simpa using om_pow_ne_zero hϖ 1
  have hx : x ≠ 0 := fun h => h0 (by rw [hxy, h, zero_mul])
  have hy : y ≠ 0 := fun h => h0 (by rw [hxy, h, mul_zero])
  obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hx
  obtain ⟨m, v, hv, rfl⟩ := fact hϖ y hy
  rcases n with _ | n
  · left; simpa using hu
  rcases m with _ | m
  · right; simpa using hv
  exfalso
  have e : (ω : QuadraticAlgebra W ϖ 0) * 1 = ω * (ω * (ω ^ (n + m) * (u * v))) := by
    rw [mul_one]; conv_lhs => rw [hxy]
    ring
  exact om_not_isUnit hϖ (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ h0 e).symm)

theorem isDVR (hϖ : Irreducible ϖ) :
    haveI := isDomain hϖ; IsDiscreteValuationRing (QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨ω, om_irreducible hϖ, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hx
  exact ⟨n, hu.unit, rfl⟩

theorem mem_span_om_pow (m : ℕ) (z : QuadraticAlgebra W ϖ 0) :
    z ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ (2 * m)} ↔ ϖ ^ m ∣ z.re ∧ ϖ ^ m ∣ z.im := by
  rw [Ideal.mem_span_singleton, om_pow, algebraMap_eq]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨t.re, by simp [← map_pow]⟩, ⟨t.im, by simp [← map_pow]⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, b⟩, by ext <;> simp [← map_pow, ha, hb]⟩

theorem isAdicComplete (hϖ : Irreducible ϖ) (hC : IsAdicComplete (Ideal.span {ϖ}) W) :
    haveI := isDomain hϖ; haveI := isDVR hϖ
    IsAdicComplete (maximalIdeal (QuadraticAlgebra W ϖ 0)) (QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  have := isDVR hϖ
  have keyO : ∀ (n : ℕ) (x y : QuadraticAlgebra W ϖ 0),
      x ≡ y [SMOD (maximalIdeal (QuadraticAlgebra W ϖ 0) ^ n • ⊤ : Submodule _ (QuadraticAlgebra W ϖ 0))] ↔
        x - y ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} := fun n x y => by
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, (om_irreducible hϖ).maximalIdeal_eq,
      Ideal.span_singleton_pow]
  have keyW : ∀ (n : ℕ) (x y : W),
      x ≡ y [SMOD (Ideal.span {ϖ} ^ n • ⊤ : Submodule W W)] ↔ ϖ ^ n ∣ x - y := fun n x y => by
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hle : ∀ {m n : ℕ}, m ≤ n → Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} ≤ Ideal.span {ω ^ m} :=
    fun h => (Ideal.span_singleton_le_span_singleton).mpr (pow_dvd_pow _ h)
  refine { toIsHausdorff := inferInstance, prec' := fun f hf => ?_ }
  have hf' : ∀ {m n : ℕ}, m ≤ n → f (2 * m) - f (2 * n) ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ (2 * m)} :=
    fun h => (keyO _ _ _).mp (hf (Nat.mul_le_mul_left 2 h))
  obtain ⟨a, ha⟩ := hC.toIsPrecomplete.prec' (fun m => (f (2 * m)).re)
    (fun {m n} h => (keyW _ _ _).mpr (by simpa using ((mem_span_om_pow m _).mp (hf' h)).1))
  obtain ⟨b, hb⟩ := hC.toIsPrecomplete.prec' (fun m => (f (2 * m)).im)
    (fun {m n} h => (keyW _ _ _).mpr (by simpa using ((mem_span_om_pow m _).mp (hf' h)).2))
  refine ⟨⟨a, b⟩, fun n => (keyO _ _ _).mpr ?_⟩
  have h1 : f n - f (2 * n) ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} :=
    (keyO _ _ _).mp (hf (by omega))
  have h2 : f (2 * n) - ⟨a, b⟩ ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} :=
    hle (by omega : n ≤ 2 * n) ((mem_span_om_pow n _).mpr
      ⟨by simpa using (keyW _ _ _).mp (ha n), by simpa using (keyW _ _ _).mp (hb n)⟩)
  have e : f n - ⟨a, b⟩ = (f n - f (2 * n)) + (f (2 * n) - ⟨a, b⟩) := by ring
  rw [e]
  exact add_mem h1 h2

end Formalism.BasicNotions.Examples₂.GatR
end
end
