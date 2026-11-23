module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.CobDim

lemma eval_polySlash (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (x : ℂ) :
    (slP w g p).eval x = ∑ i ∈ Finset.range (w + 1), p.coeff i *
      (((g 0 0 : ℤ) : ℂ) * x + ((g 0 1 : ℤ) : ℂ)) ^ i * (((g 1 0 : ℤ) : ℂ) * x + ((g 1 1 : ℤ) : ℂ)) ^ (w - i) := by
  simp [slP, LinearMap.sum_apply, eval_finsetSum, mul_assoc]

lemma natDeg_lt {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) : p.natDegree < w + 1 := by
  by_cases h : p = 0
  · simp [h]
  · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)

def upU (M : ℕ) : SL(2, ℤ) := ⟨!![1, (M : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩

lemma upU_mem (M : ℕ) : upU M ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [upU]

def loU (M : ℕ) : SL(2, ℤ) := ⟨!![1, 0; (M : ℤ), 1], by simp [Matrix.det_fin_two]⟩

lemma loU_mem (M : ℕ) : loU M ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [loU]

lemma eval_shift {w M : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (h : slP w (mat (upU M)) p = p) (x : ℂ) : p.eval (x + M) = p.eval x := by
  have h1 := eval_polySlash w (mat (upU M)) p x
  rw [h] at h1
  rw [h1, eval_eq_sum_range' (natDeg_lt hp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [upU, mat, add_comm]

lemma eq_const_of_shift {w M : ℕ} (hM : 0 < M) {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (h : slP w (mat (upU M)) p = p) : p = C (p.eval 0) := by
  have hroot : ∀ n : ℕ, (p - C (p.eval 0)).IsRoot ((n : ℂ) * M) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := eval_shift hp h ((n : ℂ) * M)
      simp only [IsRoot, eval_sub, eval_C] at ih ⊢
      push_cast
      rw [add_mul, one_mul, this, ih]
  have hinf : {x | (p - C (p.eval 0)).IsRoot x}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ) * M) ?_ hroot
    intro a b hab
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    exact_mod_cast mul_right_cancel₀ hM' hab
  exact sub_eq_zero.1 (eq_zero_of_infinite_isRoot _ hinf)

lemma const_eq_zero {w M : ℕ} (hM : 0 < M) (hw : 1 ≤ w) (c : ℂ) (h : slP w (mat (loU M)) (C c) = C c) : c = 0 := by
  have h1 := eval_polySlash w (mat (loU M)) (C c) 1
  rw [h, eval_C, Finset.sum_eq_single 0] at h1
  · simp [loU, mat] at h1
    have hne : ((M : ℂ) + 1) ^ w ≠ 1 := by
      have : (M + 1) ^ w ≠ 1 := by
        have : 1 < (M + 1) ^ w := Nat.one_lt_pow (by omega) (by omega)
        omega
      exact_mod_cast this
    by_contra hc
    exact hne (by
      have := h1.symm
      field_simp at this
      linear_combination this)
  · intro i _ hi
    simp [coeff_C, hi]
  · simp

end GlobalTheory.HeckeFamilyMatrices.CobDim

open GlobalTheory.HeckeFamilyMatrices.CobDim in
theorem GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ), 0 < M → 1 ≤ w →
    CongruenceSubgroup.Gamma M ≤ Γ → Module.finrank ℂ (B1 Γ w) = w + 1 := by
  intro M Γ w hM hw hΓ
  unfold B1
  rw [LinearMap.finrank_range_of_inj, (degreeLTEquiv ℂ (w + 1)).finrank_eq, Module.finrank_fin_fun]
  intro p q hpq
  rw [← sub_eq_zero, ← map_sub] at hpq
  rw [← sub_eq_zero]
  set r := p - q with hr
  have hfix : ∀ γ : Γ, slP w (mat γ) (r : ℂ[X]) = r := by
    intro γ
    have := congrFun hpq γ
    simpa [sub_eq_zero] using this
  have hc := eq_const_of_shift hM r.2 (hfix ⟨upU M, hΓ (upU_mem M)⟩)
  have h0 : (r : ℂ[X]).eval 0 = 0 := by
    apply const_eq_zero hM hw
    rw [← hc]
    exact hfix ⟨loU M, hΓ (loU_mem M)⟩
  ext1
  rw [hc, h0]
  simp
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem eval_polySlash : ∀ (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (z : ℂ), p ∈ degreeLT ℂ (w + 1) → ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ≠ 0 → (slP w g p).eval z = ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ w * p.eval (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))) := by
  intro w g p z hp hz
  have hn : p.natDegree < w + 1 := by
    rcases eq_or_ne p 0 with rfl | h
    · simp
    · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)
  have hs : slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
    simp [slP, LinearMap.sum_apply, LinearMap.toSpanSingleton_apply]
  rw [hs, eval_finsetSum, eval_eq_sum_range' hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [eval_smul, eval_mul, eval_pow, eval_add, eval_C, eval_X, smul_eq_mul]
  rw [div_pow, ← Nat.sub_add_cancel hi', pow_add]
  rw [Nat.sub_add_cancel hi']
  have hD : ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ i ≠ 0 := pow_ne_zero _ hz
  have e := mul_inv_cancel₀ hD
  linear_combination (-(p.coeff i * ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) ^ i *
    ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ (w - i))) * e

end GlobalTheory.HeckeFamilyMatrices
end

section

noncomputable section

open Polynomial Matrix
open scoped MatrixGroups

namespace GlobalTheory.HeckeFamilyMatrices.SlPAct

abbrev rowA (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)

abbrev rowB (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i • (rowA g ^ i * rowB g ^ (w - i)) := by
  simp [slP, LinearMap.sum_apply, rowA, rowB]

theorem slP_X_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) {i : ℕ} (hi : i ≤ w) :
    slP w g (X ^ i) = rowA g ^ i * rowB g ^ (w - i) := by
  rw [polySlash_apply]
  simp only [coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) h

theorem eq_sum_of_mem {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) :
    p = ∑ i ∈ Finset.range (w + 1), C (p.coeff i) * X ^ i := by
  by_cases h0 : p = 0
  · subst h0; simp
  · apply as_sum_range_C_mul_X_pow'
    rw [natDegree_lt_iff_degree_lt h0]
    exact mem_degreeLT.1 hp

theorem mem_of_natDegree_le {w : ℕ} {q : ℂ[X]} (h : q.natDegree ≤ w) : q ∈ degreeLT ℂ (w + 1) := by
  rw [mem_degreeLT]
  exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le h)

theorem natDegree_rows_le (g : Matrix (Fin 2) (Fin 2) ℤ) {i w : ℕ} (hi : i ≤ w) :
    (rowA g ^ i * rowB g ^ (w - i)).natDegree ≤ w := by
  have hA : (rowA g).natDegree ≤ 1 := natDegree_linear_le
  have hB : (rowB g).natDegree ≤ 1 := natDegree_linear_le
  calc (rowA g ^ i * rowB g ^ (w - i)).natDegree
      ≤ (rowA g ^ i).natDegree + (rowB g ^ (w - i)).natDegree := natDegree_mul_le
    _ ≤ i * 1 + (w - i) * 1 := add_le_add (natDegree_pow_le_of_le i hA) (natDegree_pow_le_of_le _ hB)
    _ = w := by omega

theorem polySlash_mem (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) : slP w g p ∈ degreeLT ℂ (w + 1) := by
  rw [polySlash_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (mem_of_natDegree_le ?_)
  exact natDegree_rows_le g (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

theorem polySlash_one (w : ℕ) {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) : slP w 1 p = p := by
  rw [polySlash_apply]
  conv_rhs => rw [eq_sum_of_mem hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_eq_C_mul, rowA, rowB]

theorem polySlash_conj (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) := by

  rw [polySlash_apply, polySlash_apply, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_pow, coeff_map, rowA, rowB]

theorem slP_C_mul_X_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (c : ℂ) {i : ℕ} (hi : i ≤ w) :
    slP w g (C c * X ^ i) = c • (rowA g ^ i * rowB g ^ (w - i)) := by
  rw [← smul_eq_C_mul, map_smul, slP_X_pow w g hi]

theorem polySlash_mul {m n : ℕ} (g : Matrix (Fin 2) (Fin 2) ℤ) {u v : ℂ[X]}
    (hu : u ∈ degreeLT ℂ (m + 1)) (hv : v ∈ degreeLT ℂ (n + 1)) :
    slP (m + n) g (u * v) = slP m g u * slP n g v := by
  have e : u * v = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      C (u.coeff i * v.coeff j) * X ^ (i + j) := by
    conv_lhs => rw [eq_sum_of_mem hu, eq_sum_of_mem hv]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [C_mul, pow_add]; ring

  rw [e, map_sum, polySlash_apply m g u, polySlash_apply n g v, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [slP_C_mul_X_pow _ _ _ (by omega)]
  have : m + n - (i + j) = (m - i) + (n - j) := by omega
  rw [this, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, C_mul, pow_add, pow_add]
  ring

theorem pow_mem {a : ℕ} {u : ℂ[X]} (hu : u ∈ degreeLT ℂ 2) : u ^ a ∈ degreeLT ℂ (a + 1) := by
  apply mem_of_natDegree_le
  have h1 : u.natDegree ≤ 1 := by
    by_cases h0 : u = 0
    · simp [h0]
    · have := (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hu); omega
  calc (u ^ a).natDegree ≤ a * 1 := natDegree_pow_le_of_le a h1
    _ = a := by omega

theorem polySlash_pow (g : Matrix (Fin 2) (Fin 2) ℤ) {u : ℂ[X]} (hu : u ∈ degreeLT ℂ 2) (a : ℕ) :
    slP a g (u ^ a) = slP 1 g u ^ a := by
  induction a with
  | zero =>
    have := slP_X_pow 0 g (i := 0) le_rfl
    simpa using this
  | succ a ih =>
    rw [pow_succ, polySlash_mul g (pow_mem hu) hu, ih, pow_succ]

theorem rowA_mem (g : Matrix (Fin 2) (Fin 2) ℤ) : rowA g ∈ degreeLT ℂ 2 := mem_of_natDegree_le natDegree_linear_le
theorem rowB_mem (g : Matrix (Fin 2) (Fin 2) ℤ) : rowB g ∈ degreeLT ℂ 2 := mem_of_natDegree_le natDegree_linear_le

theorem polySlash_one_linear (h : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℂ) :
    slP 1 h (C x * X + C y) = C x * rowA h + C y * rowB h := by
  have e1 := slP_X_pow 1 h (i := 1) le_rfl
  have e0 := slP_X_pow 1 h (i := 0) (by omega)
  simp only [pow_one, pow_zero, one_mul, mul_one, Nat.sub_self, Nat.sub_zero] at e1 e0
  have e0' : slP 1 h (C y) = C y * rowB h := by
    calc slP 1 h (C y) = slP 1 h (y • (1 : ℂ[X])) := by rw [smul_eq_C_mul, mul_one]
      _ = y • rowB h := by rw [map_smul, e0]
      _ = C y * rowB h := smul_eq_C_mul _
  rw [map_add (f := _), e0', ← smul_eq_C_mul, map_smul, e1, smul_eq_C_mul]

theorem polySlash_one_rowA (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (rowA g) = rowA (g * h) := by
  rw [rowA, polySlash_one_linear]
  simp only [rowA, rowB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_one_rowB (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (rowB g) = rowB (g * h) := by
  rw [rowB, polySlash_one_linear]
  simp only [rowA, rowB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_rowA_pow_mul_rowB_pow (g h : Matrix (Fin 2) (Fin 2) ℤ) (a b : ℕ) :
    slP (a + b) h (rowA g ^ a * rowB g ^ b) = rowA (g * h) ^ a * rowB (g * h) ^ b := by
  rw [polySlash_mul h (pow_mem (rowA_mem g)) (pow_mem (rowB_mem g)), polySlash_pow h (rowA_mem g),
    polySlash_pow h (rowB_mem g), polySlash_one_rowA, polySlash_one_rowB]

theorem polySlash_polySlash (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w (g * h) p = slP w h (slP w g p) := by

  rw [polySlash_apply w g p, map_sum, polySlash_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [map_smul]
  congr 1
  have := polySlash_rowA_pow_mul_rowB_pow g h i (w - i)
  rw [Nat.add_sub_cancel' hi'] at this
  exact this.symm

theorem polySlash_act : ∀ (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) →
    slP w g p ∈ degreeLT ℂ (w + 1) ∧ slP w (g * h) p = slP w h (slP w g p) ∧ slP w 1 p = p ∧
      (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) :=
  fun w g h p hp => ⟨polySlash_mem w g p, polySlash_polySlash w g h p, polySlash_one w hp, polySlash_conj w g p⟩

end GlobalTheory.HeckeFamilyMatrices.SlPAct
end
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem polySlash_map_conj (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, lcoeff_apply, Polynomial.map_sum, Polynomial.map_smul,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    map_intCast, coeff_map, Polynomial.map_intCast, Polynomial.map_natCast]

theorem eichler_smul (w : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    eichler w (c • f) τ = c • eichler w f τ := by
  simp only [eichler, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_C_mul, ← mul_assoc, ← C_mul]
  congr 2
  have : ∀ t : ℝ, ((c • f) ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I) =
      c * ((f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) := by
    intro t; simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp_rw [this, intervalIntegral.integral_const_mul]
  ring

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

theorem polynomialMapCoeffConj_mem_eichlerShimuraCocycles (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : Γ → ℂ[X]) (hz : z ∈ Z1 Γ w) : cj z ∈ Z1 Γ w := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨fun γ => ?_, fun γ δ => ?_⟩
  · have := h1 γ
    rw [mem_degreeLT] at this ⊢
    exact lt_of_le_of_lt (degree_map_le) this
  · simp only [cj, h2, Polynomial.map_add (f := _), polySlash_map_conj]

theorem polynomialMapCoeffConj_mem_eichlerShimuraCoboundaries (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : Γ → ℂ[X]) (hz : z ∈ B1 Γ w) : cj z ∈ B1 Γ w := by
  obtain ⟨⟨p, hp⟩, rfl⟩ := hz
  have hp' : p.map (starRingEnd ℂ) ∈ degreeLT ℂ (w + 1) := by
    rw [mem_degreeLT] at hp ⊢
    exact lt_of_le_of_lt (degree_map_le) hp
  refine ⟨⟨p.map (starRingEnd ℂ), hp'⟩, ?_⟩
  funext γ
  simp only [cj, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply,
    LinearMap.sub_apply, LinearMap.id_apply, Polynomial.map_sub, polySlash_map_conj]

theorem per_smul (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (f : ℍ → ℂ) (c : ℂ) :
    per Γ w (c • f) = c • per Γ w f := by
  funext γ
  simp only [per, Pi.smul_apply, eichler_smul, map_smul]

theorem cj_mem_Z1_cj_mem_B1_per_smul : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ), (∀ z ∈ Z1 Γ w, cj z ∈ Z1 Γ w) ∧
    (∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w) ∧ ∀ (f : ℍ → ℂ) (c : ℂ), per Γ w (c • f) = c • per Γ w f :=
  fun Γ w => ⟨polynomialMapCoeffConj_mem_eichlerShimuraCocycles Γ w, polynomialMapCoeffConj_mem_eichlerShimuraCoboundaries Γ w, per_smul Γ w⟩

end GlobalTheory.HeckeFamilyMatrices
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.Sieg.CthMult

end GlobalTheory.Sieg.CthMult


open scoped UpperHalfPlane MatrixGroups Manifold in
theorem _root_.GlobalTheory.Sieg.cthFac_multipliable : ∀ (c : ℕ) (q t : ℂ), ‖q‖ < 1 → t ≠ 0 →
    Multipliable (fun m : ℕ => _root_.GlobalTheory.Sieg.cthFac c q t (m + 1)) := by
  intro c q t hq _
  set g : ℂ → ℂ := fun u => (1 - u * t) ^ c ^ 2 * (1 - u * t⁻¹) ^ c ^ 2 /
    ((1 - u * t ^ c) * (1 - u * (t ^ c)⁻¹)) with hg
  have hgd : DifferentiableAt ℂ g 0 := by
    apply DifferentiableAt.div (by fun_prop) (by fun_prop)
    simp
  have hg0 : g 0 = 1 := by simp [hg]
  have hbig : (fun m : ℕ => g (q ^ (m + 1)) - 1) =O[Filter.atTop] (fun m : ℕ => q ^ (m + 1)) := by
    have h := hgd.isBigO_sub
    rw [hg0] at h
    simp only [sub_zero] at h
    have ht : Filter.Tendsto (fun m : ℕ => q ^ (m + 1)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (Filter.tendsto_add_atTop_nat 1)
    exact h.comp_tendsto ht
  have hsum : Summable (fun m : ℕ => ‖g (q ^ (m + 1)) - 1‖) := by
    refine summable_of_isBigO_nat (g := fun m : ℕ => ‖q‖ ^ (m + 1)) ?_ ?_
    · exact (summable_geometric_of_lt_one (norm_nonneg _) hq).comp_injective (add_left_injective 1)
    · simpa [norm_pow] using hbig.norm_left.norm_right
  have hmul := multipliable_one_add_of_summable hsum
  simpa [hg, _root_.GlobalTheory.Sieg.cthFac] using hmul
end
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem cosetTrace_fixed_props : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)], ∀ z ∈ Fix L N, (∀ g : G, g • cosetTrace N z = cosetTrace N z) ∧ (v z ≤ 1 → v (cosetTrace N z) ≤ 1) ∧ ∀ e : L, (∀ g : G, g • e = e) → cosetTrace N (e * z) = e * cosetTrace N z := by
  intro L _ v G _ _ hv N _ z hz
  have hfix : ∀ n : G, n ∈ N → n • z = z := fun n hn => hz ⟨n, hn⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g
    unfold cosetTrace
    rw [Finset.smul_sum]
    have key : ∀ q : G ⧸ N, g • q.out • z = (g • q).out • z := by
      intro q
      have h1 : (QuotientGroup.mk (g * q.out) : G ⧸ N) = g • q := by
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have h2 : ((g • q).out)⁻¹ * (g * q.out) ∈ N := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', h1]
      have h3 : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out)) := by group
      rw [smul_smul, h3, mul_smul, hfix _ h2]
    simp_rw [key]
    exact Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ N => q.out • z)
  · intro hz1
    unfold cosetTrace
    apply Valuation.map_sum_le
    intro q _
    rw [hv]; exact hz1
  · intro e he
    unfold cosetTrace
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [smul_mul', he]

end GlobalTheory.AlmostEt
end
