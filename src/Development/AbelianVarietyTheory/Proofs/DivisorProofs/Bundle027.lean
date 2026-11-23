module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Totient
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open Polynomial

namespace GlobalTheory.CharDeg

theorem card_fiber_eq_of_sum_eq {M : Type} [Monoid M] {n : ℕ} (f g : Fin n → (M →* ℂ))
    (h : ∀ x, ∑ j, f j x = ∑ j, g j x) (ψ : M →* ℂ) :
    Nat.card {j // f j = ψ} = Nat.card {j // g j = ψ} := by
  classical
  have hli := linearIndependent_monoidHom M ℂ
  set s : Finset (M →* ℂ) := Finset.univ.image f ∪ Finset.univ.image g ∪ {ψ} with hs
  have key : ∀ u : Fin n → (M →* ℂ), (∀ j, u j ∈ s) →
      ∑ φ ∈ s, ((Finset.univ.filter fun j => u j = φ).card : ℂ) • (φ : M → ℂ) = ∑ j, (u j : M → ℂ) := by
    intro u hu
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := s) (g := u) (fun j _ => hu j)
      (fun j => (u j : M → ℂ))]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have hc : ∑ j ∈ Finset.univ.filter (fun j => u j = φ), (u j : M → ℂ)
        = ∑ j ∈ Finset.univ.filter (fun j => u j = φ), (φ : M → ℂ) :=
      Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]
    rw [hc, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hzero : ∑ φ ∈ s, (((Finset.univ.filter fun j => f j = φ).card : ℂ)
      - ((Finset.univ.filter fun j => g j = φ).card : ℂ)) • (φ : M → ℂ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [key f (fun j => by simp [hs]), key g (fun j => by simp [hs]), sub_eq_zero]
    funext x
    simp [Finset.sum_apply, h x]
  have hψ := linearIndependent_iff'.mp hli s _ hzero ψ (by simp [hs])
  rw [sub_eq_zero, Nat.cast_inj] at hψ
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using hψ

theorem sum_eq_of_prod_eq {n : ℕ} (a b : Fin n → ℂ)
    (h : ∏ j, (X - C (a j)) = ∏ j, (X - C (b j))) : ∑ j, a j = ∑ j, b j := by
  have := congrArg Polynomial.nextCoeff h
  rw [Polynomial.prod_X_sub_C_nextCoeff, Polynomial.prod_X_sub_C_nextCoeff] at this
  exact neg_inj.mp this

end GlobalTheory.CharDeg
end

section

namespace GlobalTheory

theorem exists_pow_eq_one_isUnit_one_sub_pow (T : Type) [CommRing T] [IsDomain T] (q : ℕ) (hq0 : 0 < q) (hq : IsUnit (q : T))
    (hT : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    ∃ ζ : T, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k) := by
  classical
  haveI : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨x, hx⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
    (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 hq0)
  have hprim : IsPrimitiveRoot x q := (Polynomial.isRoot_cyclotomic_iff).1 hx
  refine ⟨x, hprim.pow_eq_one, fun k hk hkq => ?_⟩
  set S := Polynomial.nthRootsFinset q (1 : T) with hS
  have h1S : (1 : T) ∈ S := (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (one_pow _)
  have hprod := Polynomial.X_pow_sub_one_eq_prod hq0 hprim
  rw [← Finset.mul_prod_erase S _ h1S] at hprod
  have hgeom : (Polynomial.X - Polynomial.C (1 : T)) * ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = Polynomial.X ^ q - 1 := by
    rw [Polynomial.C_1]; exact mul_geom_sum _ _
  have hne : (Polynomial.X - Polynomial.C (1 : T)) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
  have hcan : ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = ∏ ζ ∈ S.erase 1, (Polynomial.X - Polynomial.C ζ) :=
    mul_left_cancel₀ hne (hgeom.trans hprod)
  have hev := congrArg (Polynomial.eval (1 : T)) hcan
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_C] at hev
  have hmem : x ^ k ∈ S.erase 1 := by
    refine Finset.mem_erase.2 ⟨hprim.pow_ne_one_of_pos_of_lt hk.ne' hkq, ?_⟩
    exact (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow])
  have hdvd : (1 - x ^ k) ∣ (q : T) := hev ▸ Finset.dvd_prod_of_mem _ hmem
  exact isUnit_of_dvd_unit hdvd hq

end GlobalTheory
end

section

namespace GlobalTheory

theorem abs_factorial_mul_eval_sub_top_le (d : ℕ) (p : Polynomial ℚ) (hp : p.natDegree ≤ d) :
    ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℚ) * p.eval (m : ℚ) - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d|
      ≤ C * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
  obtain ⟨C, hC⟩ := exists_nat_ge ((d.factorial : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|)
  refine ⟨C, fun m => ?_⟩
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hf : (0 : ℚ) ≤ d.factorial := Nat.cast_nonneg _
  rw [Polynomial.eval_eq_sum_range' (n := d + 1) (Nat.lt_succ_of_le hp), Finset.sum_range_succ]
  have e : (d.factorial : ℚ) * (∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i + p.coeff d * (m : ℚ) ^ d)
      - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d
      = (d.factorial : ℚ) * ∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i := by ring
  rw [e, abs_mul, abs_of_nonneg hf]
  have hX : (0 : ℚ) ≤ (d : ℚ) * ((m : ℚ) + 1) ^ (d - 1) := by positivity
  have h1 : |∑ i ∈ Finset.range d, p.coeff i * (m : ℚ) ^ i|
      ≤ (∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i < d := Finset.mem_range.mp hi
    rw [abs_mul, abs_of_nonneg (pow_nonneg hm i)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have a1 : (m : ℚ) ^ i ≤ ((m : ℚ) + 1) ^ i := pow_le_pow_left₀ hm (by linarith) i
    have a2 : ((m : ℚ) + 1) ^ i ≤ ((m : ℚ) + 1) ^ (d - 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have a3 : (1 : ℚ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have a4 : (0 : ℚ) ≤ ((m : ℚ) + 1) ^ (d - 1) := by positivity
    exact a1.trans (a2.trans (le_mul_of_one_le_left a4 a3))
  calc _ ≤ (d.factorial : ℚ) * ((∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1))) :=
        mul_le_mul_of_nonneg_left h1 hf
    _ = ((d.factorial : ℚ) * ∑ i ∈ Finset.range d, |p.coeff i|) * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC hX

end GlobalTheory
end

section

namespace GlobalTheory.PrimeDivisorOfPolynomialValue

open Polynomial

theorem exists_eval_mul_ne (f : ℤ[X]) (hf : 0 < f.natDegree) (c a : ℤ) (ha : a ≠ 0) :
    ∃ k : ℤ, f.eval (a * k) ≠ c ∧ f.eval (a * k) ≠ -c := by

  have hdeg : 0 < (f.comp (C a * X)).natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X a ha, mul_one]
    exact hf
  have hne : ∀ b : ℤ, f.comp (C a * X) - C b ≠ 0 := fun b h => by
    rw [sub_eq_zero] at h
    rw [h, natDegree_C] at hdeg
    exact lt_irrefl 0 hdeg
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset
    ((f.comp (C a * X) - C c).roots.toFinset ∪ (f.comp (C a * X) - C (-c)).roots.toFinset)
  refine ⟨k, fun e => hk (Finset.mem_union_left _ ?_), fun e => hk (Finset.mem_union_right _ ?_)⟩
  · rw [Multiset.mem_toFinset, mem_roots (hne c)]
    simp [e]
  · rw [Multiset.mem_toFinset, mem_roots (hne (-c))]
    simp [e]

theorem exists_prime_gt_dvd_eval :
    ∀ (f : Polynomial ℤ), (0 : ℕ) < Polynomial.natDegree f → ∀ (n : ℕ),
      ∃ (p : ℕ), Nat.Prime p ∧ n < p ∧ ∃ (x : ℤ), (↑p : ℤ) ∣ Polynomial.eval x f := by
  intro f hf n

  have of_root : ∀ x, f.eval x = 0 → ∃ p, Nat.Prime p ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
    intro x hx
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, hp, hnp, x, by rw [hx]; exact dvd_zero _⟩
  by_cases h0 : f.eval 0 = 0
  · exact of_root 0 h0
  have hfac : ((n.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  obtain ⟨k, hk1, hk2⟩ := exists_eval_mul_ne f hf (f.eval 0) _ (mul_ne_zero h0 hfac)
  by_cases hx : f.eval (f.eval 0 * n.factorial * k) = 0
  · exact of_root _ hx

  obtain ⟨q, hq⟩ := Polynomial.sub_dvd_eval_sub (f.eval 0 * n.factorial * k) 0 f
  have hft : f.eval (f.eval 0 * n.factorial * k) = f.eval 0 * (1 + n.factorial * k * q) := by
    linear_combination hq
  have ht1 : (1 + (n.factorial : ℤ) * k * q) ≠ 1 := fun h => hk1 (by rw [hft, h, mul_one])
  have ht2 : (1 + (n.factorial : ℤ) * k * q) ≠ -1 := fun h => hk2 (by rw [hft, h, mul_neg_one])
  have hnat : (1 + (n.factorial : ℤ) * k * q).natAbs ≠ 1 := by
    intro h
    rcases Int.natAbs_eq_iff.1 h with h | h
    · exact ht1 (by simpa using h)
    · exact ht2 (by simpa using h)
  have hp := Nat.minFac_prime hnat
  have hpt : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (1 + (n.factorial : ℤ) * k * q) :=
    Int.ofNat_dvd_left.2 (Nat.minFac_dvd _)
  refine ⟨_, hp, ?_, _, by rw [hft]; exact dvd_mul_of_dvd_right hpt _⟩

  by_contra hle
  rw [not_lt] at hle
  have h3 : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (n.factorial : ℤ) * k * q :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (Nat.dvd_factorial hp.pos hle)) _) _
  have h4 := dvd_sub hpt h3
  rw [add_sub_cancel_right] at h4
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.1 (by simpa using h4))

end GlobalTheory.PrimeDivisorOfPolynomialValue
end

section

open IsLocalRing

namespace GlobalTheory

open Polynomial

theorem absIntClosed_localization_and_quotient : ∀ (T : Type) [CommRing T], (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∀ (M : Submonoid T), 0 ∉ M → (IsDomain (Localization M) ∧ ∀ f : Polynomial (Localization M), f.Monic → 0 < f.natDegree → ∃ x : (Localization M), f.eval x = 0)) ∧ (∀ (p : Ideal T), p.IsPrime → (IsDomain (T ⧸ p) ∧ ∀ f : Polynomial (T ⧸ p), f.Monic → 0 < f.natDegree → ∃ x : (T ⧸ p), f.eval x = 0)) := by
  intro T _ ⟨hdom, hroot⟩
  refine ⟨fun M hM => ?_, fun p hp => ?_⟩
  · have hle : M ≤ nonZeroDivisors T := le_nonZeroDivisors_of_noZeroDivisors hM
    haveI : IsDomain (Localization M) := IsLocalization.isDomain_localization hle
    refine ⟨inferInstance, fun f hf hdeg => ?_⟩
    have hl := IsLocalization.scaleRoots_commonDenom_mem_lifts M f
      (by rw [hf.leadingCoeff]; exact one_mem _)
    obtain ⟨g, hg, hgdeg, hgm⟩ :=
      lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff _).2 hf)
    rw [natDegree_scaleRoots] at hgdeg
    obtain ⟨y, hy⟩ := hroot g hgm (hgdeg ▸ hdeg)
    set s : Localization M :=
      algebraMap T (Localization M) (IsLocalization.commonDenom M f.support f.coeff) with hs
    have hu : IsUnit s := IsLocalization.map_units _ _
    refine ⟨algebraMap T (Localization M) y * ↑hu.unit⁻¹, ?_⟩
    have key := scaleRoots_eval_mul f (algebraMap T (Localization M) y * ↑hu.unit⁻¹) s
    have hsr : s * (algebraMap T (Localization M) y * ↑hu.unit⁻¹) =
        algebraMap T (Localization M) y := by
      rw [mul_left_comm, IsUnit.mul_val_inv, mul_one]
    rw [hsr, ← hg, eval_map, eval₂_hom, hy, map_zero] at key
    exact ((hu.pow _).mul_right_eq_zero).1 key.symm
  · haveI := hp
    haveI : IsDomain (T ⧸ p) := Ideal.Quotient.isDomain p
    refine ⟨inferInstance, fun f hf hdeg => ?_⟩
    have hl : f ∈ lifts (Ideal.Quotient.mk p) :=
      (mem_lifts _).2 (map_surjective _ Ideal.Quotient.mk_surjective f)
    obtain ⟨g, hg, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic hl hf
    obtain ⟨y, hy⟩ := hroot g hgm (hgdeg ▸ hdeg)
    refine ⟨Ideal.Quotient.mk p y, ?_⟩
    rw [← hg, eval_map, eval₂_hom, hy, map_zero]

end GlobalTheory
end

section

open TensorProduct Polynomial

namespace GlobalTheory.NakAug

theorem eval_notMem_of_monic {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] (p : A[X])
    (hmon : p.Monic) (hc : ∀ k, p.coeff k ∈ P ^ (p.natDegree - k)) (t : A) (ht : t ∉ P) :
    p.eval t ∉ P := by
  intro hmem
  rw [eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_mul] at hmem
  have hs : ∑ i ∈ Finset.range p.natDegree, p.coeff i * t ^ i ∈ P := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    have hi' : i < p.natDegree := Finset.mem_range.mp hi
    exact Ideal.pow_le_self (by omega) (hc i)
  have : t ^ p.natDegree ∈ P := by
    have := P.sub_mem hmem hs
    simpa using this
  exact ht (Ideal.IsPrime.mem_of_pow_mem inferInstance _ this)

theorem exists_notMem_smul_eq_zero {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (P : Ideal A) [P.IsPrime] (t : A) (ht : t ∉ P)
    (h : ∀ m : M, t • m ∈ P • (⊤ : Submodule A M)) :
    ∃ g : A, g ∉ P ∧ ∀ m : M, g • m = 0 := by
  obtain ⟨p, hmon, -, hc, h0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A
      (algebraMap A (Module.End A M) t) P (by
        rintro _ ⟨m, rfl⟩
        simpa [Module.algebraMap_end_apply] using h m)
  refine ⟨p.eval t, eval_notMem_of_monic P p hmon hc t ht, fun m => ?_⟩
  rw [aeval_algebraMap_apply_eq_algebraMap_eval] at h0
  have := congrArg (fun φ : Module.End A M => φ m) h0
  simpa [Module.algebraMap_end_apply] using this

theorem exists_notMem_smul_eq_zero_of_submodule {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (P : Ideal A) [P.IsPrime] (N : Submodule A M) (hN : N.FG) (t : A) (ht : t ∉ P)
    (h : ∀ m ∈ N, t • m ∈ P • N) :
    ∃ g : A, g ∉ P ∧ ∀ m ∈ N, g • m = 0 := by
  haveI : Module.Finite A N := Module.Finite.iff_fg.mpr hN
  obtain ⟨g, hg, h0⟩ := exists_notMem_smul_eq_zero (M := N) P t ht (fun m => by
    have hm := h m m.2
    have hmap : P • N = (P • (⊤ : Submodule A N)).map N.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
    rw [hmap] at hm
    obtain ⟨z, hz, hzm⟩ := hm
    have : z = t • m := Subtype.ext (by simpa using hzm)
    exact this ▸ hz)
  exact ⟨g, hg, fun m hm => by simpa using congrArg Subtype.val (h0 ⟨m, hm⟩)⟩

theorem exists_uniform_notMem {A M M' : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] [Module.Finite A M] (P : Ideal A) [hP : P.IsPrime]
    (S : Submodule A M') (D : M →ₗ[A] M') (h : ∀ b, ∃ f : A, f ∉ P ∧ f • D b ∈ S) :
    ∃ f : A, f ∉ P ∧ ∀ b, f • D b ∈ S := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule A M).FG)
  have key : ∀ t : Finset M, ∃ f : A, f ∉ P ∧ ∀ b ∈ t, f • D b ∈ S := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
    | insert a t ha ih =>
      obtain ⟨F, hF, hFt⟩ := ih
      obtain ⟨fa, hfa, hfaa⟩ := h a
      refine ⟨fa * F, fun hm => (hP.mem_or_mem hm).elim hfa hF, fun b hb => ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rw [mul_comm, mul_smul]; exact S.smul_mem _ hfaa
      · rw [mul_smul]; exact S.smul_mem _ (hFt b hb)
  obtain ⟨f, hf, hfs⟩ := key s
  refine ⟨f, hf, fun b => ?_⟩
  have hle : Submodule.span A (s : Set M) ≤ S.comap (f • D) := by
    rw [Submodule.span_le]
    intro b hb
    exact hfs b hb
  have hb : b ∈ Submodule.span A (s : Set M) := hs ▸ Submodule.mem_top
  simpa using hle hb

theorem augmentation_agrees_after_inverting
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [Module.Finite A B]
    (P : Ideal A) [hP : P.IsPrime] (ε : B →ₐ[A] A) (α : B →ₐ[A] B) (d : ℕ) (hd : (d : A) ∉ P)
    (h2 : ∀ x ∈ RingHom.ker ε, α x - (d : B) * x ∈ (RingHom.ker ε) ^ 2)
    (h3 : ∀ b, ∃ f : A, f ∉ P ∧ f • (α b - algebraMap A B (ε b)) ∈ P.map (algebraMap A B)) :
    ∃ g : A, g ∉ P ∧ ∀ b, g • (α b - algebraMap A B (ε b)) = 0 := by
  classical
  set J : Ideal B := RingHom.ker ε with hJdef
  set Q : Ideal B := P.map (algebraMap A B) with hQdef
  haveI : IsNoetherian A B := isNoetherian_of_isNoetherianRing_of_finite A B

  let D : B →ₗ[A] B := α.toLinearMap - (Algebra.linearMap A B).comp ε.toLinearMap
  have hDapp : ∀ b, D b = α b - algebraMap A B (ε b) := fun b => rfl
  obtain ⟨f, hf, hfD⟩ := exists_uniform_notMem P (Q.restrictScalars A) D
    (fun b => by simpa only [hDapp, Submodule.restrictScalars_mem] using h3 b)
  have hmemJ : ∀ x, x ∈ J ↔ ε x = 0 := fun x => RingHom.mem_ker
  have hφ : ∀ b, b - algebraMap A B (ε b) ∈ J := fun b => by
    rw [hmemJ, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hαφ : ∀ b, α (b - algebraMap A B (ε b)) = α b - algebraMap A B (ε b) := fun b => by
    rw [map_sub, AlgHom.commutes]
  have hαJ : ∀ x ∈ J, α x ∈ J := fun x hx => by
    have h := h2 x hx
    have e : α x = (α x - (d : B) * x) + (d : B) * x := by ring
    rw [e]
    exact J.add_mem (Ideal.pow_le_self two_ne_zero h) (J.mul_mem_left _ hx)

  have hfαQ : ∀ x ∈ J, algebraMap A B f * α x ∈ Q := fun x hx => by
    have h := hfD x
    rw [hDapp, (hmemJ x).mp hx, map_zero, sub_zero, Algebra.smul_def] at h
    exact h

  have hL1 : ∀ y ∈ Q, y ∈ J → y ∈ P • J.restrictScalars A := fun y hyQ hyJ => by
    let φ : B →ₗ[A] B := LinearMap.id - (Algebra.linearMap A B).comp ε.toLinearMap
    have hy : y ∈ P • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]; exact hyQ
    have h1 : φ y ∈ (P • (⊤ : Submodule A B)).map φ := Submodule.mem_map_of_mem hy
    rw [Submodule.map_smul''] at h1
    have hle : (⊤ : Submodule A B).map φ ≤ J.restrictScalars A := by
      rintro _ ⟨b, -, rfl⟩
      exact hφ b
    have hφy : φ y = y := by
      show y - algebraMap A B (ε y) = y
      rw [(hmemJ y).mp hyJ, map_zero, sub_zero]
    rw [hφy] at h1
    exact Submodule.smul_mono le_rfl hle h1

  have hs : ∃ s : A, s ∉ P ∧ ∀ x ∈ J, algebraMap A B s * x ∈ J ^ 2 := by
    let L : B →ₗ[A] B ⧸ J ^ 2 := (Ideal.Quotient.mkₐ A (J ^ 2)).toLinearMap
    have hL : ∀ x, L x = Ideal.Quotient.mk (J ^ 2) x := fun x => rfl
    let N : Submodule A (B ⧸ J ^ 2) := (J.map (Ideal.Quotient.mk (J ^ 2))).restrictScalars A
    have hNfg : N.FG := IsNoetherian.noetherian N
    obtain ⟨s, hs, hs0⟩ := exists_notMem_smul_eq_zero_of_submodule P N hNfg (f * d)
      (fun hm => (hP.mem_or_mem hm).elim hf hd) (fun m hm => by
        obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hm
        have e1 : (f * (d : A)) • Ideal.Quotient.mk (J ^ 2) x
            = L (algebraMap A B f * α x) := by
          rw [← hL, ← map_smul, hL, hL, Ideal.Quotient.eq, Algebra.smul_def, map_mul, map_natCast]
          have : algebraMap A B f * (d : B) * x - algebraMap A B f * α x
              = - (algebraMap A B f * (α x - (d : B) * x)) := by ring
          rw [this]
          exact (J ^ 2).neg_mem ((J ^ 2).mul_mem_left _ (h2 x hx))
        rw [e1]
        have hy := hL1 _ (hfαQ x hx) (J.mul_mem_left _ (hαJ x hx))
        have h1 : L (algebraMap A B f * α x) ∈ (P • J.restrictScalars A).map L :=
          Submodule.mem_map_of_mem hy
        rw [Submodule.map_smul''] at h1
        refine Submodule.smul_mono le_rfl ?_ h1
        rintro _ ⟨z, hz, rfl⟩
        exact Ideal.mem_map_of_mem _ hz)
    refine ⟨s, hs, fun x hx => ?_⟩
    have h0 := hs0 _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk (J ^ 2)) hx)
    rw [← hL, ← map_smul, hL, Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def] at h0
    exact h0
  obtain ⟨s, hsP, hsJ⟩ := hs

  set K : Ideal B := J.map α with hKdef
  have hKfg : (K.restrictScalars A).FG := IsNoetherian.noetherian _
  have hJ2 : ∀ y ∈ J ^ 2, algebraMap A B f * α y ∈ Q * K := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy (fun y1 hy1 y2 hy2 => ?_) (fun a b ha hb => ?_)
    · rw [map_mul, ← mul_assoc]
      exact Ideal.mul_mem_mul (hfαQ y1 hy1) (Ideal.mem_map_of_mem α hy2)
    · rw [map_add (f := _), mul_add]; exact Ideal.add_mem _ ha hb
  have hKt : ∀ m ∈ K.restrictScalars A, (s * f) • m ∈ P • K.restrictScalars A := by
    intro m hm
    rw [← Ideal.smul_restrictScalars, Submodule.restrictScalars_mem, Ideal.smul_eq_mul,
      Algebra.smul_def]
    rw [Submodule.restrictScalars_mem] at hm
    refine Submodule.span_induction (p := fun m _ => algebraMap A B (s * f) * m ∈ Q * K)
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨x, hx, rfl⟩
      have e : algebraMap A B (s * f) * α x = algebraMap A B f * α (algebraMap A B s * x) := by
        rw [map_mul, map_mul, AlgHom.commutes]; ring
      rw [e]; exact hJ2 _ (hsJ x hx)
    · simp
    · intro x y _ _ hx hy; rw [mul_add]; exact Ideal.add_mem _ hx hy
    · intro b x _ hx; rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ b hx
  obtain ⟨g, hg, hg0⟩ := exists_notMem_smul_eq_zero_of_submodule P (K.restrictScalars A) hKfg
    (s * f) (fun hm => (hP.mem_or_mem hm).elim hsP hf) hKt
  refine ⟨g, hg, fun b => ?_⟩
  rw [← hαφ]
  exact hg0 _ (Ideal.mem_map_of_mem α (hφ b))

end GlobalTheory.NakAug
end
