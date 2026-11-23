module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhFar

open CompanionTheory.RgExh.U

theorem x_bound {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (a0 : ι) (h0 : a0 ∈ s) (B M K : ℝ) (hK0 : 0 ≤ K)
    (hy : ∀ a ∈ s, |y a| ≤ B) (hM : ∀ a ∈ s, |x a0 - x a| ≤ M) (hK : |∑ a ∈ s, (y a - x a)| ≤ K) :
    |x a0| ≤ B + M + K := by
  have hm : (1 : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨a0, h0⟩
  have e : (s.card : ℝ) * x a0 = ∑ a ∈ s, y a - ∑ a ∈ s, (y a - x a) + ∑ a ∈ s, (x a0 - x a) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have h1 : |∑ a ∈ s, y a| ≤ (s.card : ℝ) * B := by
    calc |∑ a ∈ s, y a| ≤ ∑ a ∈ s, |y a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ s, B := Finset.sum_le_sum hy
      _ = (s.card : ℝ) * B := by simp
  have h2 : |∑ a ∈ s, (x a0 - x a)| ≤ (s.card : ℝ) * M := by
    calc |∑ a ∈ s, (x a0 - x a)| ≤ ∑ a ∈ s, |x a0 - x a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ s, M := Finset.sum_le_sum hM
      _ = (s.card : ℝ) * M := by simp
  have h3 : (s.card : ℝ) * |x a0| ≤ (s.card : ℝ) * B + K + (s.card : ℝ) * M := by
    have : |(s.card : ℝ) * x a0| = (s.card : ℝ) * |x a0| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (s.card : ℝ))]
    rw [← this, e]
    calc _ ≤ |∑ a ∈ s, y a - ∑ a ∈ s, (y a - x a)| + |∑ a ∈ s, (x a0 - x a)| := abs_add_le _ _
      _ ≤ |∑ a ∈ s, y a| + |∑ a ∈ s, (y a - x a)| + |∑ a ∈ s, (x a0 - x a)| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  have h4 : (s.card : ℝ) * |x a0| ≤ (s.card : ℝ) * (B + M + K) := by nlinarith
  exact le_of_mul_le_mul_left h4 (by linarith)

theorem fiber_bound {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (a0 : ι) (M X K : ℝ) (hX0 : 0 ≤ X)
    (hX : |x a0| ≤ X) (hM : ∀ a ∈ s, |x a - x a0| ≤ M) (hK : |∑ a ∈ s, (y a - x a)| ≤ K) :
    ∑ a ∈ s, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - 2 * X * K ≤ ∑ a ∈ s, (y a ^ 2 - x a ^ 2) := by
  have h1 : ∀ a ∈ s, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) + 2 * x a0 * (y a - x a) ≤ y a ^ 2 - x a ^ 2 := by
    intro a ha
    have he : (x a - x a0) ^ 2 ≤ M ^ 2 := sq_le_sq' (by linarith [(abs_le.mp (hM a ha)).1])
      (abs_le.mp (hM a ha)).2
    nlinarith [sq_nonneg ((y a - x a) + 2 * (x a - x a0))]
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
  have h3 : -(2 * X * K) ≤ 2 * x a0 * ∑ a ∈ s, (y a - x a) := by
    have : |x a0 * ∑ a ∈ s, (y a - x a)| ≤ X * K := by
      rw [abs_mul]
      exact mul_le_mul hX hK (abs_nonneg _) hX0
    nlinarith [(abs_le.mp this).1]
  linarith

theorem total_bound {n : ℕ} (x y : Fin n → ℝ) (lev : Fin n → ℕ) (M X K : ℝ) (hX0 : 0 ≤ X) (hK0 : 0 ≤ K)
    (hX : ∀ a, |x a| ≤ X) (hM : ∀ a b, lev a = lev b → |x a - x b| ≤ M)
    (hK : ∀ c, |∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a)| ≤ K) :
    ∑ a, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - n * (2 * X * K) ≤ ∑ a, (y a ^ 2 - x a ^ 2) := by
  have hmaps : ∀ a ∈ (univ : Finset (Fin n)), lev a ∈ univ.image lev :=
    fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ a)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun a => y a ^ 2 - x a ^ 2),
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun a => (y a - x a) ^ 2 / 2 - 2 * M ^ 2)]
  have hcard : ((univ.image lev).card : ℝ) ≤ n := by
    have := Finset.card_image_le (s := (univ : Finset (Fin n))) (f := lev)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h1 : ∑ c ∈ univ.image lev, (∑ a ∈ univ.filter (fun a => lev a = c),
      ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - 2 * X * K) ≤
      ∑ c ∈ univ.image lev, ∑ a ∈ univ.filter (fun a => lev a = c), (y a ^ 2 - x a ^ 2) := by
    refine Finset.sum_le_sum fun c hc => ?_
    obtain ⟨a0, -, rfl⟩ := Finset.mem_image.mp hc
    refine fiber_bound _ x y a0 M X K hX0 (hX a0) (fun a ha => ?_) (hK _)
    exact hM a a0 (Finset.mem_filter.mp ha).2
  rw [Finset.sum_sub_distrib] at h1
  simp only [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((univ.image lev).card : ℝ) * (2 * X * K) ≤ n * (2 * X * K) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  linarith

theorem two_bound {n : ℕ} (d : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) (D : ℝ) (hD : 0 ≤ D)
    (h : D ≤ |d a - d b|) : D ^ 2 / 2 ≤ ∑ c, d c ^ 2 := by
  have h1 : d a ^ 2 + d b ^ 2 ≤ ∑ c, d c ^ 2 := by
    rw [← Finset.sum_pair (f := fun c => d c ^ 2) hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have h2 : D ^ 2 ≤ (d a - d b) ^ 2 := by
    rw [← sq_abs (d a - d b)]
    exact pow_le_pow_left₀ hD h 2
  nlinarith [sq_nonneg (d a + d b)]

theorem farNum : FarNum := by
  intro n C δ K hδ
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = |C| := ⟨_, rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = |K| := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = n * Lc n := ⟨_, rfl⟩
  have hC0 : 0 ≤ C' := hC' ▸ abs_nonneg _
  have hK0 : 0 ≤ K' := hK' ▸ abs_nonneg _
  have hM0 : 0 ≤ M := by rw [hMdef, Lc]; positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * n * M ^ 2 + 2 * n * K' * (M + K') + 2 * (n : ℝ) ^ 2 * (M + K') + (n : ℝ) ^ 3
      + n * C' ^ 2 + K' := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = 2 * n * K' * C' + 2 * (n : ℝ) ^ 2 * C' := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ Bc := by rw [hBc]; positivity
  refine ⟨1 + 2 * M / δ + 16 * (A + Bc) / δ ^ 2, ?_⟩
  intro χ x r lev σ N _ _ hr hsp hblk hineq hsep hbd hN a b hab
  by_contra hne
  have hq1 : 0 ≤ 2 * M / δ := by positivity
  have hq2 : 0 ≤ 16 * (A + Bc) / δ ^ 2 := by positivity
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hδN : 2 * M ≤ δ * N := by
    have : 2 * M / δ ≤ N := by linarith
    rw [div_le_iff₀ hδ] at this
    linarith
  have hδ2 : 16 * (A + Bc) + δ ^ 2 ≤ δ ^ 2 * N := by
    have : 16 * (A + Bc) / δ ^ 2 ≤ N - 1 := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith

  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun a => (χ (σ a)).re := ⟨_, rfl⟩
  have hyb : ∀ a, |y a| ≤ C' * N := by
    intro a
    rw [hy]
    refine (hbd (σ a)).1.trans ?_
    rw [hC']
    exact mul_le_mul_of_nonneg_right (le_abs_self C) hN0
  have hblk' : ∀ c, |∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a)| ≤ K' := by
    intro c
    have h1 := Complex.abs_re_le_norm (∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a)
      - ∑ a ∈ univ.filter (fun a => lev a = c), ((x a : ℝ) : ℂ))
    have h2 : (∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a)
      - ∑ a ∈ univ.filter (fun a => lev a = c), ((x a : ℝ) : ℂ)).re
        = ∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a) := by
      rw [hy, Finset.sum_sub_distrib]
      simp [Complex.re_sum]
    rw [h2] at h1
    exact h1.trans ((hblk c).trans (hK' ▸ le_abs_self K))
  have hspM : ∀ a b, lev a = lev b → |x a - x b| ≤ M := fun a b h => hMdef ▸ hsp a b h

  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = C' * N + M + K' := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hX : ∀ a, |x a| ≤ X := by
    intro a
    rw [hXdef]
    refine x_bound (univ.filter fun c => lev c = lev a) x y a (by simp) _ _ _ hK0
      (fun c _ => hyb c) (fun c hc => hspM a c (Finset.mem_filter.mp hc).2.symm) (hblk' _)

  have hlow := total_bound x y lev M X K' hX0 hK0 hX hspM hblk'
  have hD : (δ * N - M) ^ 2 / 2 ≤ ∑ c, (y c - x c) ^ 2 := by
    refine two_bound (fun c => y c - x c) a b hne _ (by linarith) ?_
    have h1 : δ * N ≤ |y a - y b| := by
      rw [hy]
      exact hsep (σ a) (σ b) (fun h => hne (σ.injective h))
    have h2 := hspM a b hab
    have h3 : |y a - y b| ≤ |(y a - x a) - (y b - x b)| + |x a - x b| := by
      have : y a - y b = ((y a - x a) - (y b - x b)) + (x a - x b) := by ring
      rw [this]
      exact abs_add_le _ _
    show δ * N - M ≤ |(y a - x a) - (y b - x b)|
    linarith

  have hYsum : ∑ a, y a ^ 2 = ∑ a, (χ a).re ^ 2 := by
    rw [hy]
    exact Equiv.sum_comp σ (fun a => (χ a).re ^ 2)
  have hIm : ∑ a, (χ a).im ^ 2 ≤ n * C' ^ 2 := by
    calc ∑ a, (χ a).im ^ 2 ≤ ∑ _a : Fin n, C' ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [← sq_abs (χ a).im]
          exact pow_le_pow_left₀ (abs_nonneg _) ((hbd a).2.trans (hC' ▸ le_abs_self C)) 2
      _ = n * C' ^ 2 := by simp
  have hxr : ∑ a, (x a - r a) ^ 2 ≤ ∑ a, x a ^ 2 + n * (2 * X * n + (n : ℝ) ^ 2) := by
    have : ∀ a ∈ (univ : Finset (Fin n)), (x a - r a) ^ 2 ≤ x a ^ 2 + (2 * X * n + (n : ℝ) ^ 2) := by
      intro a _
      have h1 : |x a * r a| ≤ X * n := by
        rw [abs_mul]
        exact mul_le_mul (hX a) (hr a) (abs_nonneg _) hX0
      have h2 : r a ^ 2 ≤ (n : ℝ) ^ 2 := by
        rw [← sq_abs (r a)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hr a) 2
      nlinarith [(abs_le.mp h1).1]
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_refl _
  have hKK : K ≤ K' := hK' ▸ le_abs_self K
  rw [Finset.sum_sub_distrib] at hineq
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div] at hlow
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlow
  have hδM : (δ * N / 2) ^ 2 ≤ (δ * N - M) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have h5 : (δ * N) ^ 2 / 16 ≤ n * (2 * M ^ 2) + n * (2 * X * K') + n * (2 * X * n + (n : ℝ) ^ 2)
      + n * C' ^ 2 + K' := by
    linarith
  have e2 : n * (2 * M ^ 2) + n * (2 * X * K') + n * (2 * X * n + (n : ℝ) ^ 2) + n * C' ^ 2 + K'
      = A + Bc * N := by
    rw [hA, hBc, hXdef]
    ring
  rw [e2] at h5
  have h6 : 16 * (A + Bc) < δ ^ 2 * N := by linarith [pow_pos hδ 2]
  have h7 : 16 * (A + Bc) * N < δ ^ 2 * N * N := mul_lt_mul_of_pos_right h6 (by linarith)
  have e3 : (δ * N) ^ 2 = δ ^ 2 * N * N := by ring
  have h8 : A ≤ A * N := le_mul_of_one_le_right hA0 hN1
  rw [e3] at h5
  linarith

end GlobalTheory.CompanionTheory.RgExhFar
end
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgClusterOrder

def rootHt {n : ℕ} (i : Pos n) : ℕ := (i.1.2 : ℕ) - (i.1.1 : ℕ)

theorem exists_sorted_list {α : Type} (S : Finset α) (h : α → ℕ) :
    ∃ l : List α, l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ S) ∧ l.Pairwise (fun a b => h a ≤ h b) := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], List.nodup_nil, by simp, List.Pairwise.nil⟩
    · obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image S h hne
      obtain ⟨l, hnd, hmem, hs⟩ := ih (S.erase m) (Finset.erase_ssubset hm)
      refine ⟨m :: l, ?_, ?_, ?_⟩
      · refine List.nodup_cons.2 ⟨?_, hnd⟩
        intro hml
        exact (Finset.mem_erase.1 ((hmem m).1 hml)).1 rfl
      · intro i
        rw [List.mem_cons, hmem, Finset.mem_erase]
        constructor
        · rintro (rfl | hi)
          · exact hm
          · exact hi.2
        · intro hi
          by_cases him : i = m
          · exact Or.inl him
          · exact Or.inr ⟨him, hi⟩
      · refine List.pairwise_cons.2 ⟨?_, hs⟩
        intro b hb
        exact hmin b (Finset.mem_of_mem_erase ((hmem b).1 hb))

theorem adC_ne_zero_cases {n : ℕ} {p q : Fin n} {i k : Pos n} (h : adC p q i k ≠ 0) :
    (q = i.1.1 ∧ k.1 = (p, i.1.2)) ∨ (i.1.2 = p ∧ k.1 = (i.1.1, q)) := by
  by_contra hc
  rw [not_or] at hc
  exact h (by simp only [adC, if_neg hc.1, if_neg hc.2, sub_self])

theorem mem_inside_iff {n : ℕ} {ε : Fin n → Bool} {lev : Fin n → ℕ} (hlev : Monotone lev) (i : Pos n) :
    i ∈ om ε ∧ i ∉ omU ε lev ↔ ε i.1.1 = ε i.1.2 ∧ lev i.1.1 = lev i.1.2 := by
  have hle : lev i.1.1 ≤ lev i.1.2 := hlev (le_of_lt i.2)
  simp only [CompanionTheory.D.LK.om, omU, Finset.mem_filter, Finset.mem_univ, true_and, cpt, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, le_antisymm hle (not_lt.1 (h2 h1))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun _ => by omega⟩

theorem exists_inside_order : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ), Monotone lev →
    ∃ l : List (Pos n), l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ om ε ∧ i ∉ omU ε lev) ∧
      ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post := by
  intro n ε lev hlev
  classical
  obtain ⟨l, hnd, hmem, hs⟩ := exists_sorted_list ((om ε).filter (· ∉ omU ε lev)) (rootHt (n := n))
  have hmem' : ∀ i, i ∈ l ↔ i ∈ om ε ∧ i ∉ omU ε lev := fun i => by
    rw [hmem, Finset.mem_filter]
  refine ⟨l, hnd, hmem', ?_⟩
  intro pre f post hl e he k hk
  have hfl : f ∈ l := by simp [hl]
  obtain ⟨he1, he2⟩ := (mem_inside_iff hlev e).1 ((hmem' e).1 he)
  obtain ⟨hf1, hf2⟩ := (mem_inside_iff hlev f).1 ((hmem' f).1 hfl)
  have hf0 : (f.1.1 : ℕ) < f.1.2 := f.2

  have hkey : (ε k.1.1 = ε k.1.2 ∧ lev k.1.1 = lev k.1.2) ∧ rootHt f < rootHt k := by
    rcases adC_ne_zero_cases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [← h1] at hf1 hf2 ⊢
        exact he1.trans hf1
      · simp only [← h1] at hf1 hf2 ⊢
        exact he2.trans hf2
      · have : (e.1.2 : ℕ) = f.1.1 := congrArg Fin.val h1
        simp only [rootHt, h2]
        omega
    · rw [h2]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [h1] at hf1 hf2 ⊢
        exact hf1.trans he1
      · simp only [h1] at hf1 hf2 ⊢
        exact hf2.trans he2
      · have : (f.1.2 : ℕ) = e.1.1 := congrArg Fin.val h1
        simp only [rootHt, h2]
        omega
  have hkl : k ∈ l := (hmem' k).2 ((mem_inside_iff hlev k).2 hkey.1)
  rw [hl] at hkl hs
  rcases List.mem_append.1 hkl with hpre | hrest
  · have := (List.pairwise_append.1 hs).2.2 k hpre f (by simp)
    omega
  · rcases List.mem_cons.1 hrest with rfl | hpost
    · exact absurd hkey.2 (lt_irrefl _)
    · exact hpost

end GlobalTheory.CompanionTheory.RgClusterOrder
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp

open Finset
open CompanionTheory.D.LK (Pos Cn ann cre lift sg)
open CompanionTheory.RgExh.U

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cre_ann_ne (i k : Pos n) (x : Cn n V) (A : Finset (Pos n))
    (h : (cre k * ann i : Module.End ℂ (Cn n V)) x A ≠ 0) :
    k ∈ A ∧ i ∉ A.erase k ∧ x (insert i (A.erase k)) ≠ 0 := by
  change (if k ∈ A then sg k A • (if i ∈ A.erase k then 0 else
    sg i (A.erase k) • x (insert i (A.erase k))) else 0) ≠ 0 at h
  by_cases hk : k ∈ A
  · by_cases hi : i ∈ A.erase k
    · rw [if_pos hk, if_pos hi, smul_zero] at h
      exact absurd rfl h
    · refine ⟨hk, hi, fun hx => ?_⟩
      rw [if_pos hk, if_neg hi, hx, smul_zero, smul_zero] at h
      exact h rfl
  · rw [if_neg hk] at h
    exact absurd rfl h

theorem lF_ne (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cn n V) (A : Finset (Pos n))
    (h : lF E p q x A ≠ 0) :
    x A ≠ 0 ∨ ∃ i k : Pos n, adC p q i k ≠ 0 ∧ (cre k * ann i : Module.End ℂ (Cn n V)) x A ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, hall⟩ := hcon
  apply h
  change ((lift n (E p q) + adL p q : Module.End ℂ (Cn n V)) x) A = 0
  rw [LinearMap.add_apply, Pi.add_apply, CompanionTheory.D.LK.lift_apply, h0, map_zero, zero_add]
  unfold adL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply]
  by_cases hc : adC p q i k = 0
  · rw [hc, zero_smul]
  · rw [hall i k hc, smul_zero]

theorem inU_of_adC {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {i k : Pos n}
    (h : adC p q i k ≠ 0) (hi : inU lev i) : inU lev k := by
  unfold adC at h
  unfold inU at hi ⊢
  by_cases h1 : q = (i : Fin n × Fin n).1 ∧ (k : Fin n × Fin n) = (p, (i : Fin n × Fin n).2)
  · rw [h1.2]
    show lev p < lev (i : Fin n × Fin n).2
    rw [hpq, h1.1]
    exact hi
  · by_cases h2 : (i : Fin n × Fin n).2 = p ∧ (k : Fin n × Fin n) = ((i : Fin n × Fin n).1, q)
    · rw [h2.2]
      show lev (i : Fin n × Fin n).1 < lev q
      rw [← hpq, ← h2.1]
      exact hi
    · rw [if_neg h1, if_neg h2, sub_zero] at h
      exact absurd rfl h

theorem lF_suppIn_deg (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (_hlev : Monotone lev) (x : Cn n V)
    (hx : SuppIn (inU lev) x) (p q : Fin n) (hpq : lev p = lev q) :
    SuppIn (inU lev) (lF E p q x) ∧ ∀ j, Deg j x → Deg j (lF E p q x) := by
  unfold SuppIn at hx ⊢
  unfold Deg
  constructor
  · intro A hA l hl
    rcases lF_ne E p q x A hA with h0 | ⟨i, k, hc, hne⟩
    · exact hx A h0 l hl
    · obtain ⟨hk, hi, hx'⟩ := cre_ann_ne i k x A hne
      have hsupp := hx _ hx'
      by_cases hlk : l = k
      · subst hlk
        exact inU_of_adC hpq hc (hsupp i (Finset.mem_insert_self _ _))
      · exact hsupp l (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hlk, hl⟩))
  · intro j hj A hA
    rcases lF_ne E p q x A hA with h0 | ⟨i, k, hc, hne⟩
    · exact hj A h0
    · obtain ⟨hk, hi, hx'⟩ := cre_ann_ne i k x A hne
      have hcard := hj _ hx'
      rw [Finset.card_insert_of_notMem hi, Finset.card_erase_of_mem hk] at hcard
      have hpos : 0 < A.card := Finset.card_pos.2 ⟨k, hk⟩
      omega

end GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp
end
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgExh

theorem suppIn_deg_cre_prod : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (P : Pos n → Prop) (l : List (Pos n)) (x : Cn n V) (j : ℕ),
    (∀ i ∈ l, P i) → SuppIn P x → Deg j x →
      SuppIn P (((l.map cre).prod : Module.End ℂ (Cn n V)) x) ∧
        Deg (j + l.length) (((l.map cre).prod : Module.End ℂ (Cn n V)) x) := by
  intro n V _ _ P l x j hl hx hd
  induction l with
  | nil => simpa using And.intro hx hd
  | cons i l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hl k (List.mem_cons_of_mem i hk)
    have hi : P i := hl i List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons]
    constructor
    · intro A hA k hk
      obtain ⟨h1, h2⟩ := CompanionTheory.D.LK.cre_ne hA
      by_cases hki : k = i
      · exact hki ▸ hi
      · exact ih1 _ h2 k (Finset.mem_erase.2 ⟨hki, hk⟩)
    · intro A hA
      obtain ⟨h1, h2⟩ := CompanionTheory.D.LK.cre_ne hA
      have h3 := ih2 _ h2
      have h4 := Finset.card_erase_add_one h1
      omega

end GlobalTheory.CompanionTheory.RgExh
end

section


theorem _root_.GlobalTheory.T.QuantumDeterminantTensor : CompanionTheory.RgExh.Hk.QdetTens := by
  first | exact @GlobalTheory.CompanionTheory.RgExh.qdetTens | exact GlobalTheory.CompanionTheory.RgExh.qdetTens | (intros; apply GlobalTheory.CompanionTheory.RgExh.qdetTens <;> assumption)
end
