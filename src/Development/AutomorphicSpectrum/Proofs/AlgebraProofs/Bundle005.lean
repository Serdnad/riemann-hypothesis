module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg


open AddMonoidAlgebra in
theorem ker_eq_span_single_sub_one :
    ∀ (k X A : Type) [Field k] [AddCommGroup X] [CommRing A] [Nontrivial A] [Bialgebra k A]
      (φ : AddMonoidAlgebra k X →ₐc[k] A), Function.Surjective φ →
      ∃ Y : AddSubgroup X, RingHom.ker (φ : AddMonoidAlgebra k X →+* A) =
        Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
  intro k X A _ _ _ _ _ φ _
  classical
  obtain ⟨u, hu⟩ : ∃ u : X → A, ∀ x, u x = φ (AddMonoidAlgebra.single x 1) := ⟨_, fun _ => rfl⟩
  have hmul : ∀ x y, u (x + y) = u x * u y := by
    intro x y
    rw [hu, hu, hu, ← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
  have hzero : u 0 = 1 := by
    rw [hu, ← AddMonoidAlgebra.one_def, map_one]
  have hinv : ∀ x, u x * u (-x) = 1 := by
    intro x
    rw [← hmul, add_neg_cancel, hzero]
  have hgl : ∀ x, IsGroupLikeElem k (u x) := fun x => by
    rw [hu]
    exact (AddMonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k) x).map φ
  let Y : AddSubgroup X :=
    { carrier := {x | u x = 1}
      zero_mem' := hzero
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hmul, ha, hb, one_mul]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        simpa [ha] using hinv a }
  have hY : ∀ x, x ∈ Y ↔ u x = 1 := fun _ => Iff.rfl
  refine ⟨Y, ?_⟩
  have hker : ∀ f, f ∈ RingHom.ker (φ : AddMonoidAlgebra k X →+* A) ↔ φ f = 0 :=
    fun f => RingHom.mem_ker
  have hle : Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} ≤
      RingHom.ker (φ : AddMonoidAlgebra k X →+* A) := by
    rw [Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, hker, map_sub, map_one, ← hu, (hY y).mp hy, sub_self]
  refine le_antisymm ?_ hle
  intro f hf
  rw [hker] at hf
  let r : X → X := fun x => (QuotientAddGroup.mk x : X ⧸ Y).out
  have hr : ∀ x, (QuotientAddGroup.mk (r x) : X ⧸ Y) = QuotientAddGroup.mk x :=
    fun x => Quotient.out_eq _
  have hcoset : ∀ x (c : k), AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c ∈
      Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
    intro x c
    have e : AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c =
        AddMonoidAlgebra.single (r x) c * (AddMonoidAlgebra.single (-(r x) + x) 1 - 1) := by
      rw [mul_sub, mul_one, AddMonoidAlgebra.single_mul_single, mul_one, add_neg_cancel_left]
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, QuotientAddGroup.eq.mp (hr x), rfl⟩)
  obtain ⟨G, hG⟩ : ∃ G : AddMonoidAlgebra k X,
      G = f.coeff.sum (fun x c => AddMonoidAlgebra.single (r x) c) := ⟨_, rfl⟩
  have hfG : f - G ∈ Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
    have e : f - G = f.coeff.sum
        (fun x c => AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c) := by
      rw [Finsupp.sum_sub, AddMonoidAlgebra.sum_coeff_single, hG]
    rw [e]
    unfold Finsupp.sum
    exact Ideal.sum_mem _ (fun x _ => hcoset x _)
  have hφ : ∀ g : AddMonoidAlgebra k X, φ g = Finsupp.linearCombination k u g.coeff := by
    intro g
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single g]
    rw [map_finsuppSum, Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr (fun x _ => ?_)
    rw [hu, show AddMonoidAlgebra.single x (g.coeff x) =
      g.coeff x • AddMonoidAlgebra.single x (1 : k) by rw [AddMonoidAlgebra.smul_single', mul_one],
      map_smul]
  have hG0 : φ G = 0 := by
    have h1 : φ (f - G) = 0 := (hker _).mp (hle hfG)
    rw [map_sub, hf, zero_sub, neg_eq_zero] at h1
    exact h1
  have hinj : Set.InjOn u (Set.range r) := by
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ h
    have hm : -(r x) + r x' ∈ Y := by
      rw [hY, hmul]
      have h2 : u (-(r x)) * u (r x) = 1 := by
        rw [mul_comm]
        exact hinv _
      rw [← h]
      exact h2
    have e1 : (QuotientAddGroup.mk (r x) : X ⧸ Y) = QuotientAddGroup.mk (r x') :=
      QuotientAddGroup.eq.mpr hm
    have e2 : (QuotientAddGroup.mk x : X ⧸ Y) = QuotientAddGroup.mk x' :=
      (hr x).symm.trans (e1.trans (hr x'))
    show (QuotientAddGroup.mk x : X ⧸ Y).out = (QuotientAddGroup.mk x' : X ⧸ Y).out
    rw [e2]
  have hli : LinearIndepOn k u (Set.range r) := by
    rw [linearIndepOn_iff_image hinj]
    refine (linearIndepOn_isGroupLikeElem (R := k) (A := A)).mono ?_
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact hgl (r x)
  have hsupp : G.coeff ∈ Finsupp.supported k k (Set.range r) := by
    rw [hG, AddMonoidAlgebra.coeff_finsuppSum]
    unfold Finsupp.sum
    exact Submodule.sum_mem _ (fun x _ => Finsupp.single_mem_supported k _ (Set.mem_range_self x))
  have hGc : G.coeff = 0 := by
    rw [linearIndepOn_iff] at hli
    exact hli _ hsupp (by rw [← hφ]; exact hG0)
  have hGz : G = 0 := AddMonoidAlgebra.coeff_injective hGc
  simpa [hGz] using hfG

end GlobalTheory.CompanionTheory.CommAlg
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat

section
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem mul_zpow_mul_inv_pow_mul_zpow_lemma {G : Type*} [CommGroup G] (x y g : G) (k j a : ℤ)
    (M : ℕ) :
    (x * g ^ k) ^ a * ((y * g ^ j) ^ M)⁻¹ = x ^ a * (y ^ M)⁻¹ * g ^ (k * a - j * M) := by
  rw [mul_zpow, ← zpow_mul, mul_pow, ← zpow_natCast (g ^ j), ← zpow_mul, zpow_sub, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem dvrOrder_exists_eq_unit_mul_zpow_iff {t : R} (ht : Irreducible t) (v : Rˣ) (e : ℤ) :
    (∃ r : R, algebraMap R K r = algebraMap R K v * algebraMap R K t ^ e) ↔ 0 ≤ e := by
  have ht0 : algebraMap R K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero
  constructor
  · rintro ⟨r, hr⟩
    by_contra he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, e = -((n + 1 : ℕ) : ℤ) := ⟨(-e - 1).toNat, by omega⟩
    have key : algebraMap R K (r * t ^ (n + 1)) = algebraMap R K v := by
      rw [map_mul, map_pow, hr, hn, zpow_neg, zpow_natCast, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ ht0), mul_one]
    have hu : IsUnit (r * t ^ (n + 1)) := by
      rw [IsFractionRing.injective R K key]
      exact v.isUnit
    rw [pow_succ] at hu
    exact ht.1 (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu))
  · intro he
    lift e to ℕ using he
    exact ⟨v * t ^ e, by rw [map_mul, map_pow, zpow_natCast]⟩

theorem dvrOrder_exists_unit_eq_unit_mul_zpow_iff {t : R} (ht : Irreducible t) (v : Rˣ) (e : ℤ) :
    (∃ r : Rˣ, algebraMap R K r = algebraMap R K v * algebraMap R K t ^ e) ↔ e = 0 := by
  constructor
  · rintro ⟨r, hr⟩
    have ht0 : algebraMap R K t ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero
    have h1 : 0 ≤ e := (GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) ht v e).1 ⟨r, hr⟩
    have h2 : 0 ≤ -e := by
      refine (GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) ht r (-e)).1 ⟨v, ?_⟩
      rw [hr, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ ht0), mul_one]
    omega
  · rintro rfl
    exact ⟨v, by rw [zpow_zero, mul_one]⟩

end

theorem dvr_order_integral_unit_iff : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ϖ : R) (s : K), ϖ ≠ 0 → ¬ IsUnit ϖ → s ≠ 0 → ∃ (m : ℕ) (n : ℤ), 0 < m ∧ ∀ (M : ℕ) (a : ℤ), ((∃ r : R, algebraMap R K r * s ^ M = algebraMap R K ϖ ^ a) ↔ (M : ℤ) * n ≤ a * m) ∧ ((∃ r : Rˣ, algebraMap R K r * s ^ M = algebraMap R K ϖ ^ a) ↔ (M : ℤ) * n = a * m) := by
  intro R K _ _ _ _ _ _ ϖ s hϖ hϖu hs
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  obtain ⟨φ, hφ⟩ : ∃ φ : Rˣ →* Kˣ, ∀ x : Rˣ, ((φ x : Kˣ) : K) = algebraMap R K x :=
    ⟨Units.map (algebraMap R K).toMonoidHom, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Kˣ, (g : K) = algebraMap R K π := ⟨Units.mk0 _ hπ0, rfl⟩
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ hπ
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      apply hϖu
      rw [hu, h, pow_zero, mul_one]
      exact u.isUnit
    · exact h
  have hϖK : algebraMap R K ϖ = algebraMap R K u * algebraMap R K π ^ (k : ℤ) := by
    rw [hu, map_mul, map_pow, zpow_natCast]
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R) s
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hs
    rw [← hxy, map_zero, zero_div]
  obtain ⟨i, w₁, hx⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  obtain ⟨l, w₂, hy'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  obtain ⟨w, hw⟩ : ∃ w : Rˣ, w = w₁ * w₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = (i : ℤ) - l := ⟨_, rfl⟩
  have hsK : s = algebraMap R K w * algebraMap R K π ^ j := by
    rw [← hxy, hx, hy', hw, hj]
    simp only [Units.val_mul, map_mul, map_units_inv, map_pow, zpow_sub₀ hπ0, zpow_natCast]
    ring
  refine ⟨k, j, hk, fun M a => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v : Rˣ, v = u ^ a * (w ^ M)⁻¹ := ⟨_, rfl⟩
  have hU : (φ u * g ^ (k : ℤ)) ^ a * ((φ w * g ^ j) ^ M)⁻¹ =
      φ v * g ^ ((k : ℤ) * a - j * M) := by
    rw [mul_zpow_mul_inv_pow_mul_zpow_lemma, hv, map_mul, map_zpow, map_inv, map_pow]
  have hU' := congrArg (fun z : Kˣ => (z : K)) hU
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, hφ, hg] at hU'
  have hX : ∀ r : K, r * s ^ M = algebraMap R K ϖ ^ a ↔
      r = algebraMap R K v * algebraMap R K π ^ ((k : ℤ) * a - j * M) := by
    intro r
    rw [← hU', ← hϖK, ← hsK, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hs)]
  constructor
  · rw [exists_congr fun r : R => hX (algebraMap R K r),
      GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_eq_unit_mul_zpow_iff (K := K) hπ v ((k : ℤ) * a - j * M)]
    constructor <;> intro h <;> linarith
  · rw [exists_congr fun r : Rˣ => hX (algebraMap R K r),
      GlobalTheory.CompanionTheory.Ar.Flat.dvrOrder_exists_unit_eq_unit_mul_zpow_iff (K := K) hπ v ((k : ℤ) * a - j * M)]
    constructor <;> intro h <;> linarith

end GlobalTheory.CompanionTheory.Ar.Flat
end
