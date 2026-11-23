module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle021
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem finite_box_inter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) (A : Set (𝓞 F)) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ A}.Finite := (finite_boxSet hK hF T).subset fun _ hn => hn.1

theorem sum_le_sum_shift (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {A B : Set (𝓞 F)}
    {T T' : ℝ} (y : 𝓞 F) (hy0 : ∀ w, 0 ≤ rEmb w y) (hyT : ∀ w, rEmb w y + T ≤ T')
    (hAB : ∀ n ∈ A, n + y ∈ B) :
    ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ A}, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) ≤
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T' ∧ n ∈ B},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
  classical
  have hA := finite_box_inter hK hF T A
  have hB := finite_box_inter hK hF T' B
  rw [finsum_mem_eq_finite_toFinset_sum _ hA, finsum_mem_eq_finite_toFinset_sum _ hB]
  have key : ∀ n ∈ hA.toFinset, n + y ∈ hB.toFinset ∧
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) ≤
        (Ideal.absNorm (Ideal.span {n + y}) : ℝ) ^ (m - 1) := by
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    obtain ⟨hnb, hnA⟩ := hn
    have hb : ∀ w, 0 < rEmb w n ∧ rEmb w n ≤ T := (mem_boxSet_iff hK hF).1 hnb
    have hny : n + y ∈ boxSet K F T' := by
      rw [mem_boxSet_iff hK hF]
      intro w
      rw [map_add (f := _)]
      constructor
      · linarith [(hb w).1, hy0 w]
      · linarith [(hb w).2, hyT w]
    refine ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨hny, hAB n hnA⟩, ?_⟩
    have hle : (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ (Ideal.absNorm (Ideal.span {n + y}) : ℝ) := by
      rw [absNorm_eq_prod_of_mem hK hF hnb, absNorm_eq_prod_of_mem hK hF hny]
      apply Finset.prod_le_prod₀
      · intro w _
        exact (hb w).1.le
      · intro w _
        rw [map_add (f := _)]
        linarith [hy0 w]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hle _
  calc ∑ n ∈ hA.toFinset, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1)
      ≤ ∑ n ∈ hA.toFinset, (Ideal.absNorm (Ideal.span {n + y}) : ℝ) ^ (m - 1) :=
        Finset.sum_le_sum fun n hn => (key n hn).2
    _ = ∑ n ∈ hA.toFinset.image (· + y), (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
        rw [Finset.sum_image (fun a _ b _ h => add_right_cancel h)]
    _ ≤ ∑ n ∈ hB.toFinset, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
          exact (key n hn).1
        · intro _ _ _
          positivity

theorem exists_shifts {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (x₀ : 𝓞 F) :
    ∃ (y y' : 𝓞 F) (R : ℝ), (∀ w, 0 ≤ rEmb w y ∧ rEmb w y ≤ R) ∧ (∀ w, 0 ≤ rEmb w y' ∧ rEmb w y' ≤ R) ∧
      (∀ n, n - x₀ ∈ I → n + y ∈ I) ∧ ∀ n, n ∈ I → n + y' - x₀ ∈ I := by
  classical
  have hN0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  have hNmem : ((Ideal.absNorm I : ℕ) : 𝓞 F) ∈ I := Ideal.absNorm_mem I
  obtain ⟨C, hCw⟩ : ∃ C : ℝ, ∀ w : {w : InfinitePlace F // w.IsReal}, |rEmb w x₀| ≤ C :=
    ⟨∑ w : {w : InfinitePlace F // w.IsReal}, |rEmb w x₀|, fun w =>
      Finset.single_le_sum (f := fun w => |rEmb w x₀|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)⟩
  obtain ⟨c, hc⟩ := exists_nat_ge C
  have hN1 : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
  have hcN : C ≤ ((c * Ideal.absNorm I : ℕ) : ℝ) := by
    push_cast
    have h0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    nlinarith
  have hmem : ((c * Ideal.absNorm I : ℕ) : 𝓞 F) ∈ I := by
    rw [Nat.cast_mul]
    exact I.mul_mem_left _ hNmem
  refine ⟨((c * Ideal.absNorm I : ℕ) : 𝓞 F) - x₀, ((c * Ideal.absNorm I : ℕ) : 𝓞 F) + x₀,
    ((c * Ideal.absNorm I : ℕ) : ℝ) + C, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [map_sub, map_natCast]
    have h := abs_le.1 (hCw w)
    constructor <;> linarith [h.1, h.2]
  · intro w
    rw [map_add (f := _), map_natCast]
    have h := abs_le.1 (hCw w)
    constructor <;> linarith [h.1, h.2]
  · intro n hn
    have e : n + (((c * Ideal.absNorm I : ℕ) : 𝓞 F) - x₀) =
        (n - x₀) + ((c * Ideal.absNorm I : ℕ) : 𝓞 F) := by ring
    rw [e]
    exact I.add_mem hn hmem
  · intro n hn
    have e : n + (((c * Ideal.absNorm I : ℕ) : 𝓞 F) + x₀) - x₀ =
        n + ((c * Ideal.absNorm I : ℕ) : 𝓞 F) := by ring
    rw [e]
    exact I.add_mem hn hmem

theorem tendsto_ratio (e : ℕ) :
    Tendsto (fun j : ℕ => (((j : ℝ) ^ 2) ^ e) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ e)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun j : ℕ => (j : ℝ) / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    refine (tendsto_natCast_div_add_atTop (1 : ℝ)).congr fun j => ?_
    push_cast
    rfl
  have h2 := (h1.pow 2).pow e
  simp only [one_pow] at h2
  exact h2.congr fun j => by rw [div_pow, div_pow]

private theorem tendsto_scaled_of_interleaved_tendsto (D : ℕ) {u v : ℕ → ℝ} {L : ℝ}
    (hv : Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-(D : ℤ)) * v j) atTop (𝓝 L))
    (hup : ∀ᶠ j in atTop, u j ≤ v (j + 1))
    (hlo : ∀ᶠ j in atTop, v j ≤ u (j + 1)) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-(D : ℤ)) * u j) atTop (𝓝 L) := by
  have hg : ∀ j : ℕ, ((j : ℝ) ^ 2) ^ (-(D : ℤ)) = (((j : ℝ) ^ 2) ^ D)⁻¹ := fun j => by
    rw [zpow_neg, zpow_natCast]
  simp only [hg] at hv ⊢
  have hs := tendsto_ratio D
  have hs1 : Tendsto (fun j : ℕ => ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)) atTop (𝓝 1) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)) atTop (𝓝 1) := by
    have h := hs1.inv₀ one_ne_zero
    simpa only [inv_div, inv_one] using h
  have hv2 : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1))
      atTop (𝓝 L) :=
    (hv.comp (tendsto_add_atTop_nat 1)).comp (tendsto_add_atTop_nat 1)
  have lowT : Tendsto (fun j : ℕ => (((j : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
      ((((j : ℝ) ^ 2) ^ D)⁻¹ * v j)) atTop (𝓝 L) := by
    simpa only [one_mul] using hs.mul hv
  have upT : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
      (((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1))) atTop (𝓝 L) := by
    simpa only [one_mul] using ht.mul hv2
  have hup1 : ∀ᶠ j in atTop, u (j + 1) ≤ v (j + 1 + 1) := (tendsto_add_atTop_nat 1).eventually hup
  rw [← tendsto_add_atTop_iff_nat 1]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lowT upT ?_ ?_
  · filter_upwards [hlo, eventually_ge_atTop 1] with j hj hj1
    have hj0 : ((j : ℝ) ^ 2) ^ D ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega)))
    have hpos : 0 ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ := by positivity
    calc (((j : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) * ((((j : ℝ) ^ 2) ^ D)⁻¹ * v j)
        = ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v j := by
          rw [div_mul_eq_mul_div, ← mul_assoc, mul_inv_cancel₀ hj0, one_mul, div_eq_inv_mul]
      _ ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * u (j + 1) := mul_le_mul_of_nonneg_left hj hpos
  · filter_upwards [hup1] with j hj
    have hpos : 0 ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ := by positivity
    have h0 : ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)))
    calc ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * u (j + 1)
        ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1) := mul_le_mul_of_nonneg_left hj hpos
      _ = ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
          (((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1)) := by
          rw [div_mul_eq_mul_div, ← mul_assoc, mul_inv_cancel₀ h0, one_mul, div_eq_inv_mul]

theorem tendsto_sum_coset (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (x₀ : 𝓞 F) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ I},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ))) := by
  obtain ⟨y, y', R, hy, hy', hyI, hy'I⟩ := exists_shifts hI x₀
  obtain ⟨j0, hj0⟩ := exists_nat_ge R
  refine tendsto_scaled_of_interleaved_tendsto _ (tendsto_sum_ideal hK hF hm hI) ?_ ?_
  · filter_upwards [eventually_ge_atTop j0] with j hj
    have hRj : R ≤ (j : ℝ) := le_trans hj0 (by exact_mod_cast hj)
    refine sum_le_sum_shift hK hF m (A := {n | n - x₀ ∈ I}) (B := (I : Set (𝓞 F)))
      (T := (j : ℝ) ^ 2) (T' := ((j + 1 : ℕ) : ℝ) ^ 2) y (fun w => (hy w).1) ?_ ?_
    · intro w
      have h1 := (hy w).2
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      nlinarith
    · intro n hn
      exact hyI n hn
  · filter_upwards [eventually_ge_atTop j0] with j hj
    have hRj : R ≤ (j : ℝ) := le_trans hj0 (by exact_mod_cast hj)
    refine sum_le_sum_shift hK hF m (A := (I : Set (𝓞 F))) (B := {n | n - x₀ ∈ I})
      (T := (j : ℝ) ^ 2) (T' := ((j + 1 : ℕ) : ℝ) ^ 2) y' (fun w => (hy' w).1) ?_ ?_
    · intro w
      have h1 := (hy' w).2
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      nlinarith
    · intro n hn
      exact hy'I n hn

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences

open idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem exists_trace_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (N : ℕ) : ∃ a : 𝓞 K, a + star a - 1 ∈ extP K 𝔭 ^ N := by
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := exists_inv_theta hθ N
  refine ⟨θ * e, ?_⟩
  have hJ := conjO_mem_pow hF 𝔭 N
  have h1 : (conjO K θ - θ) * conjO K e - 1 ∈ extP K 𝔭 ^ N := by
    have h := hJ _ he
    simp only [map_sub, map_mul, map_one] at h
    rw [L3.conjO_conjO θ] at h
    exact h
  have h2 : (θ - conjO K θ) * (e + conjO K e) ∈ extP K 𝔭 ^ N := by
    have e2 : (θ - conjO K θ) * (e + conjO K e) =
        ((θ - conjO K θ) * e - 1) - ((conjO K θ - θ) * conjO K e - 1) := by ring
    rw [e2]
    exact Ideal.sub_mem _ he h1
  have h3 : e + conjO K e ∈ extP K 𝔭 ^ N := mem_of_unit_mul_mem hθ h2
  have e3 : θ * e + star (θ * e) - 1 =
      ((θ - conjO K θ) * e - 1) + conjO K θ * (e + conjO K e) := by
    rw [idealPowerSpanBounds.star_def, map_mul]
    ring
  rw [e3]
  exact Ideal.add_mem _ he (Ideal.mul_mem_left _ _ h3)

theorem exists_tr_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {N : ℕ} {z : 𝓞 K} (hz : z ∉ extP K 𝔭 ^ N) :
    ∃ b : 𝓞 K, trF hF (b * z) ∉ 𝔭 ^ N := by
  by_contra hall
  push_neg at hall
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  have htr : ∀ b : 𝓞 K, b * z + conjO K (b * z) ∈ extP K 𝔭 ^ N := by
    intro b
    rw [← trF_spec hF]
    exact (mem_pow_iff 𝔭 N _).mpr (hall b)
  have h1 := htr 1
  have h2 := htr θ
  rw [one_mul] at h1
  rw [map_mul] at h2
  have h3 : (θ - conjO K θ) * conjO K z ∈ extP K 𝔭 ^ N := by
    have e : (θ - conjO K θ) * conjO K z =
        θ * (z + conjO K z) - (θ * z + conjO K θ * conjO K z) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) h2
  have h4 : conjO K z ∈ extP K 𝔭 ^ N := mem_of_unit_mul_mem hθ h3
  apply hz
  have h5 := conjO_mem_pow hF 𝔭 N _ h4
  rwa [L3.conjO_conjO z] at h5

theorem exists_solve_scalar (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c k : ℕ} (hck : c ≤ k) {z₀ : 𝓞 K} (hz : z₀ ∉ extP K 𝔭 ^ (c + 1)) {s : 𝓞 K}
    (hs : s ∈ extP K 𝔭 ^ k) (hs' : star s - s ∈ extP K 𝔭 ^ (k + 1)) :
    ∃ r ∈ extP K 𝔭 ^ (k - c), z₀ * r + star (z₀ * r) - s ∈ extP K 𝔭 ^ (k + 1) := by
  obtain ⟨a, ha⟩ := exists_trace_one hK hF h𝔭 (k + 1)
  have has : a * s ∈ extP K 𝔭 ^ k := Ideal.mul_mem_left _ a hs
  have hσ : trF hF (a * s) ∈ 𝔭 ^ k := trF_mem_pow hF 𝔭 k has
  have hσs : ι (trF hF (a * s)) - s ∈ extP K 𝔭 ^ (k + 1) := by
    rw [trF_spec, map_mul]
    have e : a * s + conjO K a * conjO K s - s =
        (a + star a - 1) * s + conjO K a * (star s - s) := by
      rw [idealPowerSpanBounds.star_def, idealPowerSpanBounds.star_def]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hs')
  obtain ⟨b, hb⟩ := exists_tr_notMem hK hF h𝔭 hz
  obtain ⟨r', hr', hfill⟩ := idealPowerSpanBounds.exists_fill h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) hb hck hσ
  refine ⟨b * ι r', Ideal.mul_mem_left _ b ((mem_pow_iff 𝔭 (k - c) r').mpr hr'), ?_⟩
  have hlin : trF hF (z₀ * (b * ι r')) = r' * trF hF (b * z₀) := by
    have e : z₀ * (b * ι r') = r' • (b * z₀) := by
      rw [Algebra.smul_def]
      ring
    rw [e, map_smul, smul_eq_mul]
  have hsum : z₀ * (b * ι r') + star (z₀ * (b * ι r')) = ι (r' * trF hF (b * z₀)) := by
    rw [← hlin, trF_spec, idealPowerSpanBounds.star_def]
  rw [hsum]
  have e2 : ι (r' * trF hF (b * z₀)) - s =
      -ι (trF hF (a * s) - trF hF (b * z₀) * r') + (ι (trF hF (a * s)) - s) := by
    simp only [map_sub, map_mul]
    ring
  rw [e2]
  exact Ideal.add_mem _ (neg_mem ((mem_pow_iff 𝔭 (k + 1) _).mpr hfill)) hσs

variable {m : Type} [Fintype m] [DecidableEq m]

theorem mul_entries_mem {r : Type} {J : Ideal (𝓞 K)} (M : Matrix m m (𝓞 K)) {R : Matrix m r (𝓞 K)}
    (hR : ∀ i j, R i j ∈ J) (i : m) (j : r) : (M * R) i j ∈ J := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_left _ _ (hR l j))

theorem exists_solve_matrix (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c k : ℕ} (hck : c + 1 ≤ k) {H X : Matrix m m (𝓞 K)} {D : 𝓞 F}
    (hD : H.det = ι D) (hDc : D ∉ 𝔭 ^ (c + 1)) (hX : ∀ i j, (Xᴴ * H * X - H) i j ∈ extP K 𝔭 ^ k)
    {W : Matrix m m (𝓞 K)} (hW : ∀ i j, W i j ∈ extP K 𝔭 ^ k) :
    ∃ Y : Matrix m m (𝓞 K), (∀ i j, Y i j ∈ extP K 𝔭 ^ (k - c)) ∧
      ∀ i j, (Xᴴ * H * Y - W) i j ∈ extP K 𝔭 ^ (k + 1) := by
  have hck' : c ≤ k := by omega
  have hfill := fun i j => exists_fillO (K := K) h𝔭 hDc hck' (hW i j)
  choose V hV hV' using hfill
  obtain ⟨R, hR⟩ : ∃ R : Matrix m m (𝓞 K), R = H.adjugate * Matrix.of V := ⟨_, rfl⟩
  have hRmem : ∀ i j, R i j ∈ extP K 𝔭 ^ (k - c) := by
    intro i j
    rw [hR]
    exact mul_entries_mem _ (fun a b => hV a b) i j
  refine ⟨X * R, fun i j => mul_entries_mem X hRmem i j, ?_⟩
  intro i j
  have e : Xᴴ * H * (X * R) - W = (Xᴴ * H * X - H) * R + (H * R - W) := by
    first
    | noncomm_ring
    | (simp only [Matrix.sub_mul, Matrix.mul_assoc]; abel)
  have e1 : H * R = H.det • Matrix.of V := by
    rw [hR, ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
  rw [e, Matrix.add_apply]
  refine Ideal.add_mem _ ?_ ?_
  · rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ (fun l _ => ?_)
    have h1 : (Xᴴ * H * X - H) i l * R l j ∈ extP K 𝔭 ^ (k + (k - c)) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul (hX i l) (hRmem l j)
    exact Ideal.pow_le_pow_right (by omega) h1
  · rw [Matrix.sub_apply, e1, Matrix.smul_apply, Matrix.of_apply, hD, smul_eq_mul]
    have h2 := neg_mem (hV' i j)
    rw [neg_sub] at h2
    exact h2

end Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
end
end
