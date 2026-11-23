module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic

@[expose] public section

section

open Finset

namespace GlobalTheory

theorem prod_interval_mirror_split (a i : ℕ) (hi : i < a) (f : ℕ → ℝ) :
    ∏ p ∈ (Finset.range (2 * a + 1)).filter (fun p => i < p ∧ i + p ≤ 2 * a), f p
      = (∏ k ∈ Finset.Ioo i a, f k * f (2 * a - k)) * (f a * f (2 * a - i)) := by
  have hS : (Finset.range (2 * a + 1)).filter (fun p => i < p ∧ i + p ≤ 2 * a)
      = Finset.Ioo i a ∪ insert a (Finset.Ioo a (2 * a - i) ∪ {2 * a - i}) := by
    ext p
    simp only [mem_filter, mem_range, mem_union, mem_insert, mem_Ioo, mem_singleton]
    omega
  rw [hS, prod_union, prod_insert, prod_union, prod_singleton]
  · have hm : ∏ p ∈ Finset.Ioo a (2 * a - i), f p = ∏ k ∈ Finset.Ioo i a, f (2 * a - k) := by
      refine Finset.prod_nbij' (fun p => 2 * a - p) (fun k => 2 * a - k) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        simp only [mem_Ioo] at hx ⊢
        omega
      · intro x hx
        simp only [mem_Ioo] at hx ⊢
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        congr 1
        omega
    rw [hm, prod_mul_distrib]
    ring
  all_goals first
    | (rw [Finset.disjoint_left]
       intro x hx hx'
       simp only [mem_union, mem_insert, mem_Ioo, mem_singleton] at hx hx'
       omega)
    | (simp only [mem_union, mem_Ioo, mem_singleton]
       omega)

private theorem prod_filter_gt_eq_prod_Ioo (a : ℕ) (i : Fin a) (h : ℕ → ℝ) :
    ∏ k ∈ Finset.univ.filter (fun k : Fin a => i < k), h k = ∏ k ∈ Finset.Ioo (i : ℕ) a, h k := by
  refine Finset.prod_nbij (fun k => (k : ℕ)) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    simp only [mem_Ioo]
    exact ⟨hk, k.isLt⟩
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro k hk
    simp only [Finset.mem_coe, mem_Ioo] at hk
    exact ⟨⟨k, hk.2⟩, Finset.mem_coe.2 (mem_filter.2 ⟨mem_univ _, Fin.lt_def.2 hk.1⟩), rfl⟩
  · intro k _
    rfl

theorem prod_first_blocks_by_layers (a : ℕ) (g : ℕ → ℕ → ℝ) :
    ∏ b ∈ ((Finset.range a) ×ˢ (Finset.range (2 * a + 1))).filter
        (fun b : ℕ × ℕ => b.1 < b.2 ∧ b.1 + b.2 ≤ 2 * a), g b.1 b.2
      = (∏ i : Fin a, ∏ k ∈ Finset.univ.filter (fun k : Fin a => i < k),
          g i k * g i (2 * a - k)) * ∏ i : Fin a, g i a * g i (2 * a - i) := by
  rw [Finset.prod_filter, Finset.prod_product]
  have step : ∀ i ∈ Finset.range a,
      (∏ p ∈ Finset.range (2 * a + 1), if i < p ∧ i + p ≤ 2 * a then g i p else 1)
        = (∏ k ∈ Finset.Ioo i a, g i k * g i (2 * a - k)) * (g i a * g i (2 * a - i)) := by
    intro i hi
    rw [← Finset.prod_filter]
    exact prod_interval_mirror_split a i (mem_range.1 hi) (g i)
  refine (Finset.prod_congr rfl step).trans ?_
  rw [prod_mul_distrib]
  congr 1
  · rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ k ∈ Finset.Ioo i a, g i k * g i (2 * a - k)) a]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact (prod_filter_gt_eq_prod_Ioo a i (fun k => g i k * g i (2 * a - k))).symm
  · exact (Fin.prod_univ_eq_prod_range (fun i => g i a * g i (2 * a - i)) a).symm

end GlobalTheory
end

section

open Matrix Finset Real

namespace GlobalTheory


open Matrix Finset Real in
theorem _root_.GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt (a : ℕ) (j : Fin a → ℤ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k, if i < k then j i * j k else 0 := by
  have h : ∀ i k : Fin a, j i * j k = (if i < k then j i * j k else 0) +
      (if k < i then j k * j i else 0) + (if i = k then j i ^ 2 else 0) := by
    intro i k
    rcases lt_trichotomy i k with hik | hik | hik
    · simp [hik, hik.ne, not_lt.mpr hik.le]
    · subst hik; simp [sq]
    · simp [hik, hik.ne', not_lt.mpr hik.le, mul_comm]
  calc (∑ i, j i) ^ 2 = ∑ i, ∑ k, j i * j k := by rw [sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ k, ((if i < k then j i * j k else 0) + (if k < i then j k * j i else 0) +
          (if i = k then j i ^ 2 else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => h i k
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i k => if k < i then j k * j i else 0)]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring


open Matrix Finset Real in
theorem _root_.GlobalTheory.dim_unipotent_radical_identities :
    ∀ (a : ℕ) (j : Fin a → ℤ) (n : ℤ), let J := ∑ i, j i; let n₀ := n - 2 * J; let dimN := 4 * (∑ i, ∑ k, if i < k then j i * j k else 0) + 2 * J * n₀ + ∑ i, j i ^ 2; dimN = 2 * J ^ 2 - ∑ i, j i ^ 2 + 2 * J * n₀ ∧ n ^ 2 = n₀ ^ 2 + 2 * ∑ i, j i ^ 2 + 2 * dimN ∧ dimN ≤ 2 * J * n := by
  intro a j n
  dsimp only
  have key := _root_.GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt a j
  have hQ : 0 ≤ ∑ i, j i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (j i)
  generalize (∑ i, ∑ k, if i < k then j i * j k else 0) = S at key ⊢
  generalize (∑ i, j i ^ 2) = Q at key hQ ⊢
  generalize (∑ i, j i) = J at key ⊢
  refine ⟨by linear_combination (-2) * key, by linear_combination 4 * key, ?_⟩
  nlinarith [key, sq_nonneg J, hQ]

end GlobalTheory
end

section

universe u_1 u_2

namespace GlobalTheory.NonzeroSmulMemSpanLattice

theorem exists_ne_zero_smul_mem {E : Type u_1} {V : Type u_2} [Field E] [NumberField E]
    [AddCommGroup V] [Module E V] [Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    (Λ : Submodule (NumberField.RingOfIntegers E) V) (hΛ : Submodule.IsFullLattice E Λ) (v : V) :
    ∃ o : NumberField.RingOfIntegers E, o ≠ 0 ∧ o • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set V) := by
    rw [hΛ.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem b hax
    · rw [mul_smul]; exact Λ.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨n, d, hd, hc⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap (NumberField.RingOfIntegers E) E d ≠ 0 := by
      intro h
      exact hd0 ((IsFractionRing.injective (NumberField.RingOfIntegers E) E) (by simpa using h))
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have key : (d * a) • c • x = n • a • x := by
      rw [← algebraMap_smul E (d * a), ← algebraMap_smul E n, ← algebraMap_smul E a,
        smul_smul, smul_smul, ← hc, map_mul]
      congr 1
      field_simp
    rw [key]
    exact Λ.smul_mem n hax

end GlobalTheory.NonzeroSmulMemSpanLattice
end

section

namespace GlobalTheory.SmulMemComapLattice

open NumberField

theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (L : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤) (v : V) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hax
    · rw [mul_smul]; exact L.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap R K q ≠ 0 := by
      simpa using hq0
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have : (q * a) • (algebraMap R K p / algebraMap R K q) • x = p • a • x := by
      rw [← algebraMap_smul K (q * a), ← algebraMap_smul K p, ← algebraMap_smul K a x,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ hax

theorem isLattice_comap_subtype {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsFullLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Submodule.comap (LinearMap.restrictScalars (𝓞 K) W.subtype) Λ) := by
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (LinearMap.restrictScalars (𝓞 K) W.subtype) :=
      W.injective_subtype
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    exact Submodule.FG.of_le hΛ.fg (Submodule.map_comap_le _ _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.SmulMemComapLattice
end

section

namespace GlobalTheory.IntegralMultiple

open NumberField

theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ a : 𝓞 E, (a : E) = (m : E) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y, hy, ⟨y • c, hint⟩, ?_⟩
  simp [zsmul_eq_mul]

theorem coe_smul_mem {E : Type} [Field E] [NumberField E] {j : ℕ}
    (Λ : Submodule (𝓞 E) (Fin j → E)) (r : 𝓞 E) {v : Fin j → E} (hv : v ∈ Λ) :
    (r : E) • v ∈ Λ := by
  have := Λ.smul_mem r hv
  rwa [← algebraMap_smul E r v] at this

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {j : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin j → E)),
    Submodule.IsFullLattice E Λ → ∀ (x : Fin j → E), ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ (↑n : E) • x ∈ Λ := by
  intro E _ _ j Λ hΛ x
  let S : Submodule E (Fin j → E) :=
    { carrier := {x | ∃ n : ℤ, n ≠ 0 ∧ (n : E) • x ∈ Λ}
      add_mem' := by
        rintro a b ⟨n, hn, ha⟩ ⟨m, hm, hb⟩
        refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
        have h1 := coe_smul_mem Λ (m : 𝓞 E) ha
        have h2 := coe_smul_mem Λ (n : 𝓞 E) hb
        convert Λ.add_mem h1 h2 using 1
        simp only [smul_add, smul_smul, map_intCast, Int.cast_mul]
        push_cast
        rw [mul_comm (m : E) (n : E)]
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro c v ⟨n, hn, hv⟩
        obtain ⟨m, hm, a, ha⟩ := exists_int_mul_integral c
        refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
        have h := coe_smul_mem Λ a hv
        convert h using 1
        rw [smul_smul, smul_smul, ha]
        push_cast
        ring_nf }
  have hle : Submodule.span E (Λ : Set (Fin j → E)) ≤ S := by
    rw [Submodule.span_le]
    intro v hv
    exact ⟨1, one_ne_zero, by simpa using hv⟩
  rw [hΛ.span_eq_top] at hle
  exact hle Submodule.mem_top

end GlobalTheory.IntegralMultiple
end

section

namespace GlobalTheory.IntMulIntegerSmulMemLattice

open NumberField

theorem exists_int_mul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ r : 𝓞 E, (r : E) = (d : E) * c := by
  have hQ : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hZ : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hQ
  obtain ⟨d, hd, hint⟩ := hZ.exists_integral_multiple
  refine ⟨d, hd, ⟨d • c, hint⟩, ?_⟩
  change d • c = (d : E) * c
  rw [zsmul_eq_mul]

theorem exists_int_smul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ (0 : ℤ) ∧ (m : 𝓞 E) • w ∈ Λ := by
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    rw [hΛ.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : ((a * b : ℤ) : 𝓞 E) • (x + y)
        = (b : 𝓞 E) • ((a : 𝓞 E) • x) + (a : 𝓞 E) • ((b : 𝓞 E) • y) := by
      rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (b : 𝓞 E) (a : 𝓞 E)]
    rw [h]
    exact Λ.add_mem (Λ.smul_mem _ hax) (Λ.smul_mem _ hby)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨d, hd, r, hr⟩ := exists_int_mul_eq_integer c
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    have h : ((d * a : ℤ) : 𝓞 E) • (c • x) = r • ((a : 𝓞 E) • x) := by
      funext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_intCast, Algebra.algebraMap_self,
        RingHom.id_apply, Int.cast_mul, map_mul]
      have hr' : algebraMap (𝓞 E) E r = (d : E) * c := hr
      rw [hr', Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      ring
    rw [h]
    exact Λ.smul_mem _ hax

end GlobalTheory.IntMulIntegerSmulMemLattice
end

section

namespace GlobalTheory.IntSmulIntegerEq

theorem exists_int_smul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers E,
      algebraMap (NumberField.RingOfIntegers E) E a = M • c := by
  have hQ : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hZ : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hQ
  obtain ⟨M, hM, hint⟩ := hZ.exists_integral_multiple
  exact ⟨M, hM, ⟨M • c, hint⟩, rfl⟩

theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (w : Fin n → E) : ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, h₁, hx⟩ := hx
    obtain ⟨N₂, h₂, hy⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero h₁ h₂, ?_⟩
    have e : (N₁ * N₂) • (x + y) = N₂ • (N₁ • x) + N₁ • (N₂ • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm N₂ N₁]
    rw [e]
    exact L.add_mem (zsmul_mem hx N₂) (zsmul_mem hy N₁)
  | smul c x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, a, ha⟩ := exists_int_smul_eq_integer c
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have e : (M * N) • (c • x) = a • (N • x) := by
      rw [← algebraMap_smul E a, ha, smul_assoc, mul_smul, smul_comm N c x]
    rw [e]
    exact L.smul_mem a hx

end GlobalTheory.IntSmulIntegerEq
end

section

namespace GlobalTheory.SpanInfEq

open NumberField

theorem exists_smul_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsFullLattice K L) (v : V) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ h₁
    · rw [mul_smul]; exact L.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers K) c
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero hb) hd, ?_⟩
    have hb' : algebraMap (RingOfIntegers K) K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have : (b * d) • ((algebraMap (RingOfIntegers K) K a / algebraMap (RingOfIntegers K) K b) • x)
        = a • (d • x) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K d, ← algebraMap_smul K a, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ h

theorem span_inf_eq {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsFullLattice K L) (T : Submodule K V) :
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (RingOfIntegers K) T) : Set V) = T := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · intro v hv
    obtain ⟨d, hd, h⟩ := exists_smul_mem L hL v
    have hd' : algebraMap (RingOfIntegers K) K d ≠ 0 := by
      intro h0
      exact hd ((map_eq_zero_iff _ (IsFractionRing.injective (RingOfIntegers K) K)).mp h0)
    have hdT : d • v ∈ Submodule.restrictScalars (RingOfIntegers K) T := by
      rw [← algebraMap_smul K d v]
      exact T.smul_mem _ hv
    have hmem : d • v ∈ L ⊓ Submodule.restrictScalars (RingOfIntegers K) T :=
      Submodule.mem_inf.mpr ⟨h, hdT⟩
    have : v = (algebraMap (RingOfIntegers K) K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [inst_5 : IsScalarTower (NumberField.RingOfIntegers K) K V]
    (L : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsFullLattice K L →
    ∀ (T : Submodule K V),
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (NumberField.RingOfIntegers K) T) : Set V) = T :=
  fun L hL T => span_inf_eq L hL T

end GlobalTheory.SpanInfEq
end
