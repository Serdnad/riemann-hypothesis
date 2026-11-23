module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped ComplexConjugate
open Set MeasureTheory

namespace PositivityTheory.Rg.Rsw.L.LPosExt

variable {X : Type} [TopologicalSpace X]

def swAlg (A : Submodule ℂ (X → ℂ)) (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) (hstar : ∀ f ∈ A, star f ∈ A)
    (K : Set X) : StarSubalgebra ℂ C(K, ℂ) where
  carrier := {h | ∃ c : ℂ, ∃ a ∈ A, ∀ x : K, h x = c + a x}
  mul_mem' := by
    rintro h h' ⟨c, a, ha, hh⟩ ⟨c', a', ha', hh'⟩
    refine ⟨c * c', c • a' + c' • a + a * a', A.add_mem (A.add_mem (A.smul_mem _ ha') (A.smul_mem _ ha))
      (hmul _ ha _ ha'), fun x => ?_⟩
    simp only [ContinuousMap.mul_apply, hh, hh', Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  one_mem' := ⟨1, 0, A.zero_mem, fun x => by simp⟩
  add_mem' := by
    rintro h h' ⟨c, a, ha, hh⟩ ⟨c', a', ha', hh'⟩
    refine ⟨c + c', a + a', A.add_mem ha ha', fun x => ?_⟩
    simp only [ContinuousMap.add_apply, hh, hh', Pi.add_apply]
    ring
  zero_mem' := ⟨0, 0, A.zero_mem, fun x => by simp⟩
  algebraMap_mem' r := ⟨r, 0, A.zero_mem, fun x => by simp [Algebra.algebraMap_eq_smul_one]⟩
  star_mem' := by
    rintro h ⟨c, a, ha, hh⟩
    refine ⟨conj c, star a, hstar a ha, fun x => ?_⟩
    simp [ContinuousMap.star_apply, hh, Pi.star_apply]

theorem approx (A : Submodule ℂ (X → ℂ)) (hc : ∀ f ∈ A, Continuous f)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) (hstar : ∀ f ∈ A, star f ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y) {K : Set X} (hK : IsCompact K) {b : X → ℂ} (hbA : b ∈ A)
    (hbK : ∀ x ∉ K, b x = 0) {g : X → ℂ} (hg : Continuous g) (hgb : ∀ x, g x ≠ 0 → b x = 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ h ∈ A, ∀ x, ‖h x - g x‖ ≤ ε * ‖b x‖ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  set S := swAlg A hmul hstar K
  have hS : S.SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hf, hfxy⟩ := hsep x y (fun h => hxy (Subtype.ext h))
    let F : C(K, ℂ) := ⟨fun z => f z, (hc f hf).comp continuous_subtype_val⟩
    exact ⟨F, ⟨F, ⟨0, f, hf, fun z => by simp [F]⟩, rfl⟩, hfxy⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hS
  let gK : C(K, ℂ) := ⟨fun z => g z, hg.comp continuous_subtype_val⟩
  have hgK : gK ∈ S.topologicalClosure := by rw [htop]; trivial
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at hgK
  obtain ⟨p, hpS, hp⟩ := hgK ε hε
  obtain ⟨c, a, ha, hpa⟩ := hpS
  refine ⟨c • b + b * a, A.add_mem (A.smul_mem _ hbA) (hmul _ hbA _ ha), fun x => ?_⟩
  by_cases hx : x ∈ K
  · have h1 : ‖p ⟨x, hx⟩ - gK ⟨x, hx⟩‖ ≤ ε := by
      have := ContinuousMap.norm_coe_le_norm (p - gK) ⟨x, hx⟩
      rw [dist_comm, dist_eq_norm] at hp
      exact (this.trans hp.le)
    have h2 : g x = b x * g x := by
      by_cases h0 : g x = 0
      · simp [h0]
      · simp [hgb x h0]
    have h3 : c • b x + b x * a x - g x = b x * (p ⟨x, hx⟩ - gK ⟨x, hx⟩) := by
      rw [hpa ⟨x, hx⟩]
      simp only [gK, ContinuousMap.coe_mk]
      rw [h2] at *
      nth_rewrite 1 [h2]
      simp only [smul_eq_mul]
      ring
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply]
    rw [h3, norm_mul, mul_comm ε]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  · have hb := hbK x hx
    have hg0 : g x = 0 := by
      by_contra h0
      have := hgb x h0
      rw [hb] at this
      exact zero_ne_one this
    simp [hb, hg0]

theorem zero_of_le (d : ℂ) (C : ℝ) (h : ∀ ε : ℝ, 0 < ε → ‖d‖ ≤ ε * C) : d = 0 := by
  have hC : 0 ≤ C := by have := h 1 one_pos; linarith [norm_nonneg d]
  have : ∀ ε : ℝ, 0 < ε → dist d 0 ≤ ε := by
    intro ε hε
    rw [dist_zero_right]
    refine (h (ε / (C + 1)) (by positivity)).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  exact eq_of_forall_dist_le this

end PositivityTheory.Rg.Rsw.L.LPosExt
end
end

section

noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

theorem lmajASeq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
    (f : Fin k → SchwartzMap V ℂ) (q : V → ℝ) (hq0 : ∀ y, 0 ≤ q y) (A : ℝ) (hA : 0 ≤ A)
    (hqA : ∀ y, q y ≤ A * ‖y‖ ^ 2) :
    ∃ b : ℕ → ℝ, (∀ n, 0 ≤ b n) ∧ (∀ j : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ j)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i y, (N : ℝ) ≤ q y → ‖f i y‖ ≤ ε * b ⌊q y⌋₊ := by
  set S : ℕ → ℝ := fun j => ∑ i, (Finset.Iic (2 * j, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (f i) with hS
  set D : ℕ → ℝ := fun j => (1 + A) ^ j * (2 ^ (2 * j) * S j) with hDdef
  have hS0 : ∀ j, 0 ≤ S j := fun j => Finset.sum_nonneg fun i _ => apply_nonneg _ _
  have hD0 : ∀ j, 0 ≤ D j := fun j =>
    mul_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (by positivity) (hS0 j))
  have hD : ∀ j i y, (1 + q y) ^ j * ‖f i y‖ ≤ D j := by
    intro j i y
    have h1 : 1 + q y ≤ (1 + A) * (1 + ‖y‖) ^ 2 := by
      have := hqA y; have hy := norm_nonneg y; nlinarith [mul_nonneg hA hy]
    have h2 : (1 + ‖y‖) ^ (2 * j) * ‖f i y‖ ≤ 2 ^ (2 * j) * S j := by
      have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2 * j, 0)) (k := 2 * j)
        (n := 0) le_rfl le_rfl (f i) y
      rw [norm_iteratedFDeriv_zero] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Finset.single_le_sum (f := fun i => (Finset.Iic (2 * j, 0)).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (f i)) (fun i _ => apply_nonneg _ _)
        (Finset.mem_univ i)
    calc (1 + q y) ^ j * ‖f i y‖ ≤ ((1 + A) * (1 + ‖y‖) ^ 2) ^ j * ‖f i y‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith [hq0 y]) h1 j) (norm_nonneg _)
      _ = (1 + A) ^ j * ((1 + ‖y‖) ^ (2 * j) * ‖f i y‖) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ D j := mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) _)
  set m : ℕ → ℝ := fun n => ⨅ j : ℕ, D j / (1 + (n : ℝ)) ^ j with hm
  have hbdd : ∀ n : ℕ, BddBelow (Set.range fun j : ℕ => D j / (1 + (n : ℝ)) ^ j) :=
    fun n => ⟨0, by rintro _ ⟨j, rfl⟩; exact div_nonneg (hD0 j) (by positivity)⟩
  have hm0 : ∀ n, 0 ≤ m n := fun n => le_ciInf fun j => div_nonneg (hD0 j) (by positivity)
  have hmle : ∀ n j, m n ≤ D j / (1 + (n : ℝ)) ^ j := fun n j => ciInf_le (hbdd n) j
  have hfm : ∀ i y, ‖f i y‖ ≤ m ⌊q y⌋₊ := by
    intro i y
    refine le_ciInf fun j => ?_
    rw [le_div_iff₀ (by positivity)]
    have hn : (⌊q y⌋₊ : ℝ) ≤ q y := Nat.floor_le (hq0 y)
    calc ‖f i y‖ * (1 + (⌊q y⌋₊ : ℝ)) ^ j ≤ (1 + q y) ^ j * ‖f i y‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j)
            (norm_nonneg _)
      _ ≤ D j := hD j i y
  set b : ℕ → ℝ := fun n => Real.sqrt (m n) with hb
  have hbdec : ∀ j n, b n ≤ Real.sqrt (D (2 * j)) / (1 + (n : ℝ)) ^ j := by
    intro j n
    have hpos : 0 < (1 + (n : ℝ)) ^ j := by positivity
    calc b n ≤ Real.sqrt (D (2 * j) / (1 + (n : ℝ)) ^ (2 * j)) := Real.sqrt_le_sqrt (hmle n (2 * j))
      _ = Real.sqrt (D (2 * j)) / (1 + (n : ℝ)) ^ j := by
          rw [Real.sqrt_div (hD0 _), pow_mul', Real.sqrt_sq hpos.le]
  have hsum2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    refine ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).congr
      fun n => ?_
    push_cast; ring
  have hbs : ∀ j : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ j) := by
    intro j
    refine (hsum2.mul_left (Real.sqrt (D (2 * (j + 2))) * 2 ^ j)).of_nonneg_of_le
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (fun n => ?_)
    have hpos : 0 < (1 + (n : ℝ)) := by positivity
    have h1 := hbdec (j + 2) n
    have h2 : ((n : ℝ) + 2) ^ j ≤ 2 ^ j * (1 + (n : ℝ)) ^ j := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) j
    calc b n * ((n : ℝ) + 2) ^ j ≤ Real.sqrt (D (2 * (j + 2))) / (1 + (n : ℝ)) ^ (j + 2) *
          (2 ^ j * (1 + (n : ℝ)) ^ j) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = Real.sqrt (D (2 * (j + 2))) * 2 ^ j * (1 / ((n : ℝ) + 1) ^ 2) := by
          field_simp; ring
  refine ⟨b, fun n => Real.sqrt_nonneg _, hbs, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt (D (2 * 1)) / ε)
  refine ⟨N, fun i y hy => ?_⟩
  have hNn : N ≤ ⌊q y⌋₊ := Nat.le_floor hy
  have hbε : b ⌊q y⌋₊ ≤ ε := by
    have h1 := hbdec 1 ⌊q y⌋₊
    rw [pow_one] at h1
    have hNr : (N : ℝ) ≤ (⌊q y⌋₊ : ℝ) := by exact_mod_cast hNn
    have h3 := (div_lt_iff₀ hε).mp hN
    have h4 : Real.sqrt (D (2 * 1)) / (1 + (⌊q y⌋₊ : ℝ)) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  calc ‖f i y‖ ≤ m ⌊q y⌋₊ := hfm i y
    _ = b ⌊q y⌋₊ * b ⌊q y⌋₊ := (Real.mul_self_sqrt (hm0 _)).symm
    _ ≤ ε * b ⌊q y⌋₊ := mul_le_mul_of_nonneg_right hbε (Real.sqrt_nonneg _)

end PositivityTheory.Rg.Rsw.L.LMajor

end
end
