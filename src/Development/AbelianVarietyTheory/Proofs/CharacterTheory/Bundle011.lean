module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Module.PID
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.FieldTheory.Finite.Extension
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem card_nonregular_residues_le (q n : ℕ) (hq : 2 ≤ q) (hn : 0 < n) :
    ((Finset.Ioo 0 (q ^ n - 1)).filter
      (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])).card ≤
      ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) := by
  classical
  have hsub : ((Finset.Ioo 0 (q ^ n - 1)).filter
      (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])) ⊆
      n.primeFactors.biUnion (fun p => (Finset.Ioo 0 (q ^ (n / p) - 1)).image
        (fun k => k * ((q ^ n - 1) / (q ^ (n / p) - 1)))) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Ioo] at hj
    obtain ⟨⟨hj0, hjN⟩, e, he, hje⟩ := hj
    rw [Finset.mem_Ioo] at he
    have hqe : 1 ≤ q ^ e := Nat.one_le_pow _ _ (by omega)
    have h1 : q ^ n - 1 ∣ j * (q ^ e - 1) := by
      rw [Nat.mul_sub_one]
      exact (Nat.modEq_iff_dvd' (Nat.le_mul_of_pos_right j hqe)).1 hje.symm
    have h2 : q ^ n - 1 ∣ j * (q ^ Nat.gcd e n - 1) := by
      rw [← Nat.pow_sub_one_gcd_pow_sub_one, ← Nat.gcd_mul_left]
      exact Nat.dvd_gcd h1 (Dvd.intro_left j rfl)
    obtain ⟨m, hm⟩ := Nat.gcd_dvd_right e n
    have hglt : Nat.gcd e n < n := lt_of_le_of_lt (Nat.gcd_le_left n he.1) he.2
    have hm1 : m ≠ 1 := by
      rintro rfl
      omega
    obtain ⟨p, hp, r, hr⟩ := Nat.exists_prime_and_dvd hm1
    have hnp : n = p * (Nat.gcd e n * r) := by
      conv_lhs => rw [hm, hr]
      ring
    have hd : n / p = Nat.gcd e n * r := Nat.div_eq_of_eq_mul_right hp.pos hnp
    have hpn : p ∣ n := ⟨_, hnp⟩
    have hd0 : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos).ne'
    have h3 : q ^ n - 1 ∣ j * (q ^ (n / p) - 1) :=
      h2.trans (Nat.mul_dvd_mul_left j
        (Nat.pow_sub_one_dvd_pow_sub_one q ⟨r, hd⟩))
    have h4 : q ^ (n / p) - 1 ∣ q ^ n - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one q (Nat.div_dvd_of_dvd hpn)
    have hD : 0 < q ^ (n / p) - 1 := by
      have := Nat.one_lt_pow hd0 (show 1 < q by omega)
      omega
    obtain ⟨M, hM⟩ := h4
    rw [Finset.mem_biUnion]
    refine ⟨p, Nat.mem_primeFactors.2 ⟨hp, hpn, hn.ne'⟩, ?_⟩
    rw [hM, mul_comm j] at h3
    obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left hD h3
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Ioo.2 ⟨?_, ?_⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    · rw [hM, hk, mul_comm _ M] at hjN
      exact lt_of_mul_lt_mul_left hjN (Nat.zero_le _)
    · rw [hM, Nat.mul_div_cancel_left _ hD, hk, mul_comm]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine Finset.sum_le_sum fun p _ => Finset.card_image_le.trans ?_
  rw [Nat.card_Ioo]
  omega

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem sepIneq_four_mul_add_five_le (k : ℕ) (hk : 5 ≤ k) : 4 * k + 5 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

theorem sepIneq_sum_lt (q n : ℕ) (hq : 2 ≤ q) :
    ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < q ^ (n / 2 + 1) := by
  have hinj : Set.InjOn (fun p => n / p) (n.primeFactors : Set ℕ) := by
    intro a ha b hb hab
    have ha' := Nat.mem_primeFactors.1 (Finset.mem_coe.1 ha)
    have hb' := Nat.mem_primeFactors.1 (Finset.mem_coe.1 hb)
    have h1 := Nat.div_div_self ha'.2.1 ha'.2.2
    have h2 := Nat.div_div_self hb'.2.1 hb'.2.2
    simp only at hab
    rw [← h1, ← h2, hab]
  calc ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) ≤ ∑ p ∈ n.primeFactors, q ^ (n / p) :=
        Finset.sum_le_sum fun p _ => Nat.sub_le _ _
    _ = ∑ k ∈ n.primeFactors.image (fun p => n / p), q ^ k :=
        (Finset.sum_image (f := fun k => q ^ k) hinj).symm
    _ < q ^ (n / 2 + 1) := by
        apply Nat.geomSum_lt hq
        intro k hk
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
        have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
        exact Nat.lt_succ_of_le (Nat.div_le_div_left hp2 (by norm_num))

theorem sepIneq_large (q n : ℕ) (hq : 2 ≤ q) (hn : 11 ≤ n) :
    (n - 1) ^ 2 + 4 * n ^ 2 * ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < 2 * n * (q ^ n - 1) := by
  have hS := sepIneq_sum_lt q n hq
  set S := ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2)
  obtain ⟨k, hk⟩ : ∃ k, n = (n / 2 + 1) + k := ⟨n - (n / 2 + 1), by omega⟩
  have hk5 : 5 ≤ k := by omega
  have h1 : 2 * n + 1 ≤ q ^ k := by
    have := sepIneq_four_mul_add_five_le k hk5
    have h2 : 2 ^ k ≤ q ^ k := Nat.pow_le_pow_left hq k
    omega
  have h2 : q ^ k ≤ q ^ (n / 2 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : q ^ n = q ^ (n / 2 + 1) * q ^ k := by rw [← pow_add, ← hk]
  rw [h3]
  set Q := q ^ (n / 2 + 1)
  set R := q ^ k
  have h4 : Q * (2 * n + 1) ≤ Q * R := Nat.mul_le_mul_left _ h1
  obtain ⟨T, hT⟩ : ∃ T, Q * R = T + 1 := ⟨Q * R - 1, by
    have : 0 < Q * R := Nat.mul_pos (by omega) (by omega)
    omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hT] at h4 ⊢
  simp only [Nat.add_sub_cancel]
  have h5 : 2 * (m + 1) + 1 ≤ Q := le_trans h1 h2
  have h6 : 2 * (m + 1) * (Q * (2 * (m + 1) + 1)) ≤ 2 * (m + 1) * (T + 1) := Nat.mul_le_mul_left _ h4
  have h7 : 4 * (m + 1) ^ 2 * S ≤ 4 * (m + 1) ^ 2 * Q := Nat.mul_le_mul_left _ hS.le
  have h8 : 2 * (m + 1) * (2 * (m + 1) + 1) ≤ 2 * (m + 1) * Q := Nat.mul_le_mul_left _ h5
  nlinarith

theorem sepIneq_sub (t k c : ℕ) (hc : c ≤ 2) (hk : 0 < k) : (((2 + t) ^ k - c : ℕ) : ℤ) = (2 + (t : ℤ)) ^ k - c := by
  have : 2 ≤ (2 + t) ^ k := le_trans (by omega) (Nat.le_self_pow hk.ne' _)
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl

theorem sep_numerical_ineq : ∀ q n : ℕ, 2 ≤ q → 0 < n → ¬ (q = 2 ∧ (n = 4 ∨ n = 6)) → (n - 1) ^ 2 + 4 * n ^ 2 * ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < 2 * n * (q ^ n - 1) := by
  intro q n hq hn hex
  rcases le_or_gt 11 n with h | h
  · exact sepIneq_large q n hq h
  obtain ⟨t, rfl⟩ : ∃ t, q = 2 + t := ⟨q - 2, by omega⟩
  have e1 : Nat.primeFactors 1 = ∅ := by simp
  have e2 : Nat.primeFactors 2 = {2} := by decide +kernel
  have e3 : Nat.primeFactors 3 = {3} := by decide +kernel
  have e4 : Nat.primeFactors 4 = {2} := by decide +kernel
  have e5 : Nat.primeFactors 5 = {5} := by decide +kernel
  have e6 : Nat.primeFactors 6 = {2, 3} := by decide +kernel
  have e7 : Nat.primeFactors 7 = {7} := by decide +kernel
  have e8 : Nat.primeFactors 8 = {2} := by decide +kernel
  have e9 : Nat.primeFactors 9 = {3} := by decide +kernel
  have e10 : Nat.primeFactors 10 = {2, 5} := by decide +kernel
  have ht : (0 : ℤ) ≤ t := by positivity
  have s1 := fun k hk => sepIneq_sub t k 1 (by omega) hk
  have s2 := fun k hk => sepIneq_sub t k 2 (by omega) hk
  have ht1 : n = 4 ∨ n = 6 → (1 : ℤ) ≤ t := by omega
  have p2 : (0:ℤ) ≤ t^2 := by positivity
  have p3 : (0:ℤ) ≤ t^3 := by positivity
  have p4 : (0:ℤ) ≤ t^4 := by positivity
  have p5 : (0:ℤ) ≤ t^5 := by positivity
  have p6 : (0:ℤ) ≤ t^6 := by positivity
  have p7 : (0:ℤ) ≤ t^7 := by positivity
  have p8 : (0:ℤ) ≤ t^8 := by positivity
  have p9 : (0:ℤ) ≤ t^9 := by positivity
  have p10 : (0:ℤ) ≤ t^10 := by positivity
  interval_cases n
  · rw [e1]; simp
  · rw [e2, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith [sq_nonneg ((t:ℤ))]
  · rw [e3, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e4, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    have := ht1 (by norm_num)
    nlinarith
  · rw [e5, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e6, Finset.sum_pair (by norm_num)]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    have := ht1 (by norm_num)
    nlinarith
  · rw [e7, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e8, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e9, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e10, Finset.sum_pair (by norm_num)]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL

theorem finrank_ker_lsmul_pow_quotient {F : Type} [Field F] (f : F[X]) (hf : f ≠ 0) (e j : ℕ) :
    Module.finrank F (LinearMap.ker
      ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F)) =
      f.natDegree * min j e := by
  have hle : Ideal.span {f ^ e} ≤ Ideal.span {f ^ min j e} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow f (min_le_right j e))
  haveI : Module.Finite F (F[X] ⧸ Ideal.span {f ^ e}) :=
    (AdjoinRoot.powerBasis (pow_ne_zero e hf)).finite
  let π := (Ideal.Quotient.factorₐ F hle).toLinearMap
  have hπ : LinearMap.range π = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact Ideal.Quotient.factor_surjective hle
  have hker : LinearMap.ker π = LinearMap.range
      ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : π (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl
    have h2 : ∀ y : F[X],
        ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F)
          (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (f ^ j * y) := fun y => rfl
    rw [LinearMap.mem_ker, h1, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      LinearMap.mem_range]
    constructor
    · rintro ⟨c, rfl⟩
      rcases le_total j e with h | h
      · exact ⟨Ideal.Quotient.mk _ c, by rw [h2, min_eq_left h]⟩
      · refine ⟨0, ?_⟩
        rw [map_zero, min_eq_right h, eq_comm, Ideal.Quotient.eq_zero_iff_mem,
          Ideal.mem_span_singleton]
        exact dvd_mul_right _ _
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [h2, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
      have h3 : f ^ min j e ∣ f ^ j * y - x := (pow_dvd_pow f (min_le_right j e)).trans hy
      have h4 : f ^ min j e ∣ f ^ j * y := (pow_dvd_pow f (min_le_left j e)).mul_right y
      simpa using dvd_sub h4 h3
  have h1 := LinearMap.finrank_range_add_finrank_ker π
  have h2 := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F)
  rw [hπ, hker, finrank_top, finrank_quotient_span_eq_natDegree, natDegree_pow] at h1
  rw [mul_comm]
  omega

def piDropTrivial {R : Type} [Ring R] {ι : Type} (M : ι → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (P : ι → Prop) [DecidablePred P] (h : ∀ i, ¬ P i → Subsingleton (M i)) :
    ((i : ι) → M i) ≃ₗ[R] ((i : {i // P i}) → M i) where
  toFun x i := x i
  invFun y i := if hi : P i then y ⟨i, hi⟩ else 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext i
    by_cases hi : P i
    · simp [hi]
    · haveI := h i hi
      exact Subsingleton.elim _ _
  right_inv y := by
    funext i
    simp [i.2]

def kerAevalEquivPi {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] (g : Module.End F V)
    {ι : Type} (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module F (M i)]
    [∀ i, Module F[X] (M i)] [∀ i, IsScalarTower F F[X] (M i)]
    (φ : Module.AEval' g ≃ₗ[F[X]] ((i : ι) → M i)) (p : F[X]) :
    LinearMap.ker (aeval g p) ≃ₗ[F]
      ((i : ι) → LinearMap.ker ((LinearMap.lsmul F[X] (M i) p).restrictScalars F)) where
  toFun x i := ⟨φ (Module.AEval'.of g x) i, by
    have hx : aeval g p • (x : V) = 0 := x.2
    have : p • φ (Module.AEval'.of g x) = 0 := by
      rw [← map_smul, ← Module.AEval.of_aeval_smul, hx, map_zero, map_zero]
    exact congrFun this i⟩
  invFun y := ⟨(Module.AEval'.of g).symm (φ.symm fun i => y i), by
    have : p • (fun i => (y i : M i)) = 0 := funext fun i => (y i).2
    change aeval g p • (Module.AEval'.of g).symm (φ.symm fun i => (y i : M i)) = 0
    rw [← Module.AEval.of_symm_smul, ← map_smul, this, map_zero, map_zero]⟩
  map_add' x y := by
    funext i
    apply Subtype.ext
    change φ (Module.AEval'.of g ((x : V) + y)) i =
      φ (Module.AEval'.of g x) i + φ (Module.AEval'.of g y) i
    rw [map_add (f := _), map_add (f := _), Pi.add_apply]
  map_smul' c x := by
    funext i
    apply Subtype.ext
    change φ (Module.AEval'.of g (c • (x : V))) i = c • φ (Module.AEval'.of g x) i
    rw [map_smul, LinearMapClass.map_smul_of_tower φ, Pi.smul_apply]
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    funext i
    apply Subtype.ext
    simp

theorem primary_structure : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X]) (m : ℕ), Irreducible f → aeval g (f ^ m) = 0 → ∃ (d : ℕ) (e : Fin d → ℕ), (∀ i, 0 < e i) ∧ Nonempty (Module.AEval' g ≃ₗ[F[X]] ((i : Fin d) → F[X] ⧸ Ideal.span {f ^ e i})) ∧ ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = f.natDegree * ∑ i, min j (e i) := by
  intro F _ V _ _ _ g f m hf hm
  classical
  have hT : Module.IsTorsion' (Module.AEval' g) (Submonoid.powers f) := by
    rw [Submodule.isTorsion'_powers_iff]
    intro x
    refine ⟨m, ?_⟩
    apply (Module.AEval'.of g).symm.injective
    rw [Module.AEval.of_symm_smul, hm, zero_smul, map_zero]
  obtain ⟨d, k, ⟨φ⟩⟩ := Module.torsion_by_prime_power_decomposition hf hT
  let σ := Fintype.equivFin {i : Fin d // 0 < k i}
  let ψ : Module.AEval' g ≃ₗ[F[X]]
      ((i : Fin (Fintype.card {i : Fin d // 0 < k i})) → F[X] ⧸ Ideal.span {f ^ k (σ.symm i)}) :=
    φ ≪≫ₗ DirectSum.linearEquivFunOnFintype F[X] (Fin d) (fun i => F[X] ⧸ Ideal.span {f ^ k i}) ≪≫ₗ
      piDropTrivial (fun i => F[X] ⧸ Ideal.span {f ^ k i}) (fun i => 0 < k i) (fun i hi => by
        have : k i = 0 := by omega
        rw [Ideal.Quotient.subsingleton_iff, this, pow_zero, Ideal.span_singleton_one]) ≪≫ₗ
      LinearEquiv.piCongrLeft' F[X] (fun i : {i : Fin d // 0 < k i} => F[X] ⧸ Ideal.span {f ^ k i}) σ
  refine ⟨_, fun i => k (σ.symm i), fun i => (σ.symm i).2, ⟨ψ⟩, fun j => ?_⟩
  haveI : ∀ e : ℕ, Module.Finite F (F[X] ⧸ Ideal.span {f ^ e}) := fun e =>
    (AdjoinRoot.powerBasis (pow_ne_zero e hf.ne_zero)).finite
  rw [(kerAevalEquivPi g _ ψ (f ^ j)).finrank_eq, Module.finrank_pi_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => finrank_ker_lsmul_pow_quotient f hf.ne_zero _ j

end GlobalTheory.CuspGL
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem eq_zero_of_finsum_mul_star_pow_eq_zero {K : Type} [Field K] (θ : K →* ℂ)
    (hθ : ∀ x y : K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (N : ℕ) (hN : 0 < N) (c : K → ℂ)
    (h : ∀ l : ℕ, ∑ᶠ α ∈ {α : K | α ^ N = 1}, c α * star (θ α ^ l) = 0) :
    ∀ α ∈ {α : K | α ^ N = 1}, c α = 0 := by
  classical
  have hS : {α : K | α ^ N = 1} = ((Polynomial.nthRootsFinset N (1 : K) : Finset K) : Set K) := by
    ext x
    simp [Polynomial.mem_nthRootsFinset hN]
  intro β hβ
  have hβ' : β ^ N = 1 := hβ
  set S := Polynomial.nthRootsFinset N (1 : K) with hSdef
  have hmem : ∀ x, x ∈ S ↔ x ^ N = 1 := fun x => Polynomial.mem_nthRootsFinset hN 1
  have h' : ∀ l : ℕ, ∑ α ∈ S, c α * star (θ α ^ l) = 0 := by
    intro l
    have := h l
    rwa [hS, finsum_mem_coe_finset] at this
  have hpow : ∀ x : K, x ^ N = 1 → θ x ^ N = 1 := fun x hx => by rw [← map_pow, hx, map_one]
  have hunit : ∀ x : K, x ^ N = 1 → star (θ x) * θ x = 1 := by
    intro x hx
    have h1 : ‖θ x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (hpow x hx) hN.ne'
    have := Complex.conj_mul' (θ x)
    rw [h1] at this
    simpa using this
  have hne : ∀ x : K, x ^ N = 1 → x ≠ 0 := by
    rintro x hx rfl
    rw [zero_pow hN.ne'] at hx
    exact zero_ne_one hx
  have key : ∀ α ∈ S, ∑ l ∈ Finset.range N, (θ β * star (θ α)) ^ l
      = if α = β then (N : ℂ) else 0 := by
    intro α hα
    have hα' := (hmem α).1 hα
    split_ifs with hab
    · subst hab
      rw [mul_comm, hunit α hα']
      simp
    · have hz : θ β * star (θ α) ≠ 1 := by
        intro hz
        apply hab
        apply hθ α β (hne α hα') (hne β hβ')
        calc θ α = (θ β * star (θ α)) * θ α := by rw [hz, one_mul]
          _ = θ β := by rw [mul_assoc, hunit α hα', mul_one]
      rw [geom_sum_eq hz, mul_pow, ← star_pow, hpow β hβ', hpow α hα']
      simp
  have hsum : ∑ l ∈ Finset.range N, θ β ^ l * ∑ α ∈ S, c α * star (θ α ^ l) = 0 := by
    simp only [h', mul_zero, Finset.sum_const_zero]
  have h2 : ∑ l ∈ Finset.range N, θ β ^ l * ∑ α ∈ S, c α * star (θ α ^ l)
      = ∑ α ∈ S, c α * ∑ l ∈ Finset.range N, (θ β * star (θ α)) ^ l := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow, star_pow]
    ring
  rw [h2, Finset.sum_congr rfl (fun α hα => by rw [key α hα])] at hsum
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', (hmem β).2 hβ', if_true] at hsum
  exact (mul_eq_zero.1 hsum).resolve_right (Nat.cast_ne_zero.2 hN.ne')

theorem torus_fourier_injective : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → ∀ c : AlgebraicClosure F → ℂ, (∀ l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, c α * star (θ α ^ l) = 0) → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, c α = 0 := by
  intro F _ _ θ hθ n hn c h
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hN : 0 < Nat.card F ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' hq)
  exact eq_zero_of_finsum_mul_star_pow_eq_zero θ hθ _ hN c h

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exponent_regular_of_natDegree_minpoly_pow : ∀ (F : Type) [Field F] [Finite F] (d k : ℕ) (ζ : AlgebraicClosure F), 0 < d → orderOf ζ = Nat.card F ^ d - 1 → (minpoly F (ζ ^ k)).natDegree = d → ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1] := by
  intro F _ _ d k ζ _ hord hdeg i hi hid hmod
  have h1 : ζ ^ (Nat.card F ^ d - 1) = 1 := by
    rw [← hord]; exact pow_orderOf_eq_one ζ
  have h2 : (ζ ^ k) ^ (Nat.card F ^ i) = ζ ^ k := by
    rw [← pow_mul]; exact pow_eq_pow_of_modEq hmod h1
  have hint : IsIntegral F (ζ ^ k) := Algebra.IsIntegral.isIntegral _
  have hdvd : minpoly F (ζ ^ k) ∣ (X ^ (Nat.card F ^ i) - X : F[X]) := by
    apply minpoly.dvd
    simp only [map_sub, map_pow, aeval_X, h2, sub_self]
  have h3 := (minpoly.irreducible hint).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd
  rw [hdeg] at h3
  exact absurd (Nat.le_of_dvd hi h3) (not_le.mpr hid)

end GlobalTheory.CuspGL
end
