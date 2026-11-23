module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

section

namespace GlobalTheory

namespace PowerSeriesInv

theorem coeff_inv_norm_le (a : ℕ → ℂ) (M R : ℝ) (hR : 0 < R) (ha0 : a 0 ≠ 0)
    (hM : ∀ n, ‖a n‖ ≤ M * R ^ n) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹‖ ≤ ‖a 0‖⁻¹ * (R * (1 + M / ‖a 0‖)) ^ n := by
  have hc0 : PowerSeries.constantCoeff (PowerSeries.mk a) = a 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  set A := ‖a 0‖ with hA
  have hA0 : 0 < A := norm_pos_iff.mpr ha0
  have hMA : A ≤ M := by simpa using hM 0
  have hM0 : 0 < M := lt_of_lt_of_le hA0 hMA
  set m := M / A with hm
  have hm0 : 0 < m := div_pos hM0 hA0
  set K := R * (1 + m) with hK
  set q := (1 + m)⁻¹ with hq
  have hK0 : 0 < K := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hRK : R = K * q := by
    rw [hK, hq, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  have hqA : q / (1 - q) = A / M := by
    have hqpos : 0 < q := by positivity
    have h1q : 1 - q = m * q := by
      have : (1 + m) * q = 1 := mul_inv_cancel₀ (by positivity)
      linarith
    rw [h1q, hm]
    field_simp
  have hgeom : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (if 1 ≤ k then q ^ k else 0) ≤ A / M := by
    intro n
    rw [Finset.sum_range_succ']
    simp only [show ∀ k : ℕ, 1 ≤ k + 1 from fun k => by omega, if_true,
      show ¬ (1 ≤ 0) from by omega, if_false, add_zero]
    simp_rw [pow_succ]
    rw [← Finset.sum_mul]
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq0 hq1
    rw [← Finset.range_eq_Ico, pow_zero] at h
    calc (∑ i ∈ Finset.range n, q ^ i) * q ≤ 1 / (1 - q) * q := by gcongr
      _ = q / (1 - q) := by ring
      _ = A / M := hqA
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [PowerSeries.coeff_inv]
  split_ifs with hn
  · subst hn
    simp [hc0, hA]
  · have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        ‖(if p.2 < n then PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖ ≤
          M * A⁻¹ * K ^ n * (if 1 ≤ p.1 then q ^ p.1 else 0) := by
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      split_ifs with h1 h2 h2
      · rw [norm_mul, PowerSeries.coeff_mk]
        calc ‖a p.1‖ * ‖PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹‖
            ≤ (M * R ^ p.1) * (A⁻¹ * K ^ p.2) :=
              mul_le_mul (hM _) (ih _ h1) (norm_nonneg _) (by positivity)
          _ = M * A⁻¹ * K ^ n * q ^ p.1 := by
              rw [hRK, ← hp, mul_pow, pow_add]; ring
      · omega
      · simp only [norm_zero]; positivity
      · simp
    calc ‖-(PowerSeries.constantCoeff (PowerSeries.mk a))⁻¹ *
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (if p.2 < n then PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖
        = A⁻¹ * ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (if p.2 < n then
            PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖ := by
          rw [norm_mul, norm_neg, norm_inv, hc0]
      _ ≤ A⁻¹ * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, M * A⁻¹ * K ^ n * (if 1 ≤ p.1 then q ^ p.1 else 0) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
            (by positivity)
      _ = A⁻¹ * (M * A⁻¹ * K ^ n *
            ∑ k ∈ Finset.range (n + 1), (if 1 ≤ k then q ^ k else 0)) := by
          rw [← Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      _ ≤ A⁻¹ * (M * A⁻¹ * K ^ n * (A / M)) := by
          gcongr
          exact hgeom n
      _ = A⁻¹ * K ^ n := by
          field_simp

theorem hasSum_inv :
    ∀ (a : ℕ → ℂ) (ρ : ℝ), 0 < ρ → a 0 ≠ 0 → (∀ x : ℂ, ‖x‖ < ρ → Summable fun n => a n * x ^ n) →
      ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ x : ℂ, ‖x‖ < ρ' → (∑' n, a n * x ^ n) ≠ 0 ∧
        HasSum (fun n => PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n)
          (∑' n, a n * x ^ n)⁻¹ := by
  intro a ρ hρ ha0 hs
  set x0 : ℂ := ((ρ / 2 : ℝ) : ℂ) with hx0def
  have hx0 : ‖x0‖ = ρ / 2 := by
    rw [hx0def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsum := hs x0 (by rw [hx0]; linarith)
  have htend := hsum.tendsto_atTop_zero.norm
  obtain ⟨M, hM⟩ := htend.bddAbove_range
  set R : ℝ := 2 / ρ with hRdef
  have hR : 0 < R := by positivity
  have hMa : ∀ n, ‖a n‖ ≤ M * R ^ n := by
    intro n
    have h1 : ‖a n * x0 ^ n‖ ≤ M := hM ⟨n, rfl⟩
    rw [norm_mul, norm_pow, hx0] at h1
    have h2 : (ρ / 2) ^ n * R ^ n = 1 := by
      rw [← mul_pow, hRdef, div_mul_div_comm, mul_comm ρ 2, div_self (by positivity), one_pow]
    calc ‖a n‖ = ‖a n‖ * (ρ / 2) ^ n * R ^ n := by rw [mul_assoc, h2, mul_one]
      _ ≤ M * R ^ n := by gcongr
  have hA0 : 0 < ‖a 0‖ := norm_pos_iff.mpr ha0
  have hM0 : 0 < M := lt_of_lt_of_le hA0 (by simpa using hMa 0)
  set K := R * (1 + M / ‖a 0‖) with hKdef
  have hK : 0 < K := by positivity
  refine ⟨min (ρ / 2) K⁻¹, by positivity, ?_⟩
  intro x hx
  have hx1 : ‖x‖ < ρ / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : ‖x‖ < K⁻¹ := lt_of_lt_of_le hx (min_le_right _ _)
  have hRx : R * ‖x‖ < 1 := by
    rw [hRdef, div_mul_eq_mul_div, div_lt_one hρ]; linarith
  have hKx : K * ‖x‖ < 1 := by
    have := mul_lt_mul_of_pos_left hx2 hK
    rwa [mul_inv_cancel₀ hK.ne'] at this
  have hsa : Summable fun n => ‖a n * x ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity) hRx).mul_left M)
    rw [norm_mul, norm_pow]
    calc ‖a n‖ * ‖x‖ ^ n ≤ M * R ^ n * ‖x‖ ^ n := by gcongr; exact hMa n
      _ = M * (R * ‖x‖) ^ n := by ring
  have hsb : Summable fun n => ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity) hKx).mul_left ‖a 0‖⁻¹)
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹‖ * ‖x‖ ^ n
        ≤ ‖a 0‖⁻¹ * K ^ n * ‖x‖ ^ n := by
          gcongr; exact coeff_inv_norm_le a M R hR ha0 hMa n
      _ = ‖a 0‖⁻¹ * (K * ‖x‖) ^ n := by ring_nf
  have hc0 : PowerSeries.constantCoeff (PowerSeries.mk a) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]; exact ha0
  have hc : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      a kl.1 * x ^ kl.1 * (PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹ * x ^ kl.2) =
        (if n = 0 then 1 else 0) := by
    intro n
    have h := congrArg (PowerSeries.coeff n) (PowerSeries.mul_inv_cancel (PowerSeries.mk a) hc0)
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at h
    calc ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          a kl.1 * x ^ kl.1 * (PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹ * x ^ kl.2)
        = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (PowerSeries.coeff kl.1 (PowerSeries.mk a) *
            PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹) * x ^ n := by
          refine Finset.sum_congr rfl (fun kl hkl => ?_)
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
          rw [← hkl, pow_add, PowerSeries.coeff_mk]; ring
      _ = (if n = 0 then 1 else 0) := by
          rw [← Finset.sum_mul, h]; split_ifs with hn <;> simp [hn]
  have key : (∑' n, a n * x ^ n) * (∑' n, PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n) = 1 := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb, tsum_congr hc]
    exact tsum_ite_eq 0 1
  refine ⟨left_ne_zero_of_mul_eq_one key, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right key]
  exact (Summable.of_norm hsb).hasSum

end PowerSeriesInv

end GlobalTheory
end

section

open MeasureTheory Filter Topology Metric Set

namespace GlobalTheory

theorem translate_chart_ball_distortion
    (V M G : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup M]
    [NormedSpace ℝ M] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (e : V → G)
    (m : G → M) (ι : V →ₗᵢ[ℝ] M) (L : G → M →L[ℝ] M) (he : Continuous e) (he0 : e 0 = 1)
    (hd : HasStrictFDerivAt (fun x => m (e x)) ι.toContinuousLinearMap 0)
    (hL : ContinuousAt L 1) (hL1 : L 1 = ContinuousLinearMap.id ℝ M)
    (hm : ∀ g h, m (g * h) = L g (m h))
    (hopen : ∀ r : ℝ, 0 < r → e '' ball 0 r ∈ 𝓝 (1 : G)) (κ : ℝ) (hκ : 1 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ ball (0 : V) δ, ∀ r ∈ Ioo (0 : ℝ) δ,
      (fun g => e x * g) '' (e '' ball 0 r) ⊆ e '' ball x (κ * r) ∧
      e '' ball x r ⊆ (fun g => e x * g) '' (e '' ball 0 (κ * r)) := by
  set ε : ℝ := (κ - 1) / (2 * (3 + 2 * κ)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  have hε1 : ε < 1 / 4 := by
    rw [hε, div_lt_iff₀ (by linarith)]
    linarith
  have hκε : (1 + ε) ^ 2 < κ * (1 - ε) ^ 2 := by
    have h3 : ε * (3 + 2 * κ) = (κ - 1) / 2 := by
      rw [hε]
      field_simp
    nlinarith [mul_pos (sub_pos.mpr hκ) (mul_pos hε0 hε0)]
  obtain ⟨η, hη0, hη⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.bound hε0)
  have hD : ∀ a b : V, ‖a‖ < η → ‖b‖ < η →
      ‖m (e a) - m (e b) - ι (a - b)‖ ≤ ε * ‖a - b‖ := by
    intro a b ha hb
    have h := @hη (a, b) (by
      simp only [Prod.dist_eq, dist_zero_right]
      exact max_lt ha hb)
    simpa using h
  have hLc : ContinuousAt (fun x => L (e x)) 0 := hL.comp_of_eq he.continuousAt he0
  obtain ⟨η2, hη20, hη2⟩ := Metric.continuousAt_iff.mp hLc ε hε0
  have hLx : ∀ x : V, ‖x‖ < η2 → ∀ v : M, ‖L (e x) v - v‖ ≤ ε * ‖v‖ := by
    intro x hx v
    have h1 := hη2 (by rwa [dist_zero_right] : dist x 0 < η2)
    simp only [he0, hL1, dist_eq_norm] at h1
    have h2 := (L (e x) - ContinuousLinearMap.id ℝ M).le_opNorm v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg v))
  have hU : e '' ball 0 η ∈ 𝓝 (1 : G) := hopen η hη0
  have hφ : Continuous (fun p : V × V => e p.1 * e p.2) :=
    (he.comp continuous_fst).mul (he.comp continuous_snd)
  have hψ : Continuous (fun p : V × V => (e p.1)⁻¹ * e p.2) :=
    (he.comp continuous_fst).inv.mul (he.comp continuous_snd)
  have hφU : (fun p : V × V => e p.1 * e p.2) ⁻¹' (e '' ball 0 η) ∈ 𝓝 ((0 : V), (0 : V)) :=
    hφ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)
  have hψU : (fun p : V × V => (e p.1)⁻¹ * e p.2) ⁻¹' (e '' ball 0 η) ∈
      𝓝 ((0 : V), (0 : V)) :=
    hψ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)
  obtain ⟨η3, hη30, hη3⟩ := Metric.mem_nhds_iff.mp hφU
  obtain ⟨η4, hη40, hη4⟩ := Metric.mem_nhds_iff.mp hψU
  have hφ' : ∀ a b : V, ‖a‖ < η3 → ‖b‖ < η3 → ∃ z, ‖z‖ < η ∧ e z = e a * e b := by
    intro a b ha hb
    have hab : (a, b) ∈ ball ((0 : V), (0 : V)) η3 := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_zero_right]
      exact max_lt ha hb
    obtain ⟨z, hz, hze⟩ := hη3 hab
    exact ⟨z, mem_ball_zero_iff.mp hz, hze⟩
  have hψ' : ∀ a b : V, ‖a‖ < η4 → ‖b‖ < η4 → ∃ z, ‖z‖ < η ∧ e z = (e a)⁻¹ * e b := by
    intro a b ha hb
    have hab : (a, b) ∈ ball ((0 : V), (0 : V)) η4 := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_zero_right]
      exact max_lt ha hb
    obtain ⟨z, hz, hze⟩ := hη4 hab
    exact ⟨z, mem_ball_zero_iff.mp hz, hze⟩
  have h0η : ‖(0 : V)‖ < η := by simpa using hη0
  refine ⟨min (η / 2) (min η2 (min (η3 / 2) (η4 / 2))),
    lt_min (by linarith) (lt_min hη20 (lt_min (by linarith) (by linarith))), ?_⟩
  intro x hx r hr
  rw [mem_ball_zero_iff] at hx
  obtain ⟨hr0, hrδ⟩ := hr
  have b1 : ‖x‖ < η / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have b2 : ‖x‖ < η2 := lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
  have b3 : ‖x‖ < η3 / 2 := lt_of_lt_of_le hx
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have b4 : ‖x‖ < η4 / 2 := lt_of_lt_of_le hx
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have r1 : r < η / 2 := lt_of_lt_of_le hrδ (min_le_left _ _)
  have r3 : r < η3 / 2 := lt_of_lt_of_le hrδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have r4 : r < η4 / 2 := lt_of_lt_of_le hrδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmx : ∀ y, m (e x * e y) - m (e x) = L (e x) (m (e y) - m (e 0)) := by
    intro y
    rw [map_sub, he0, ← hm, ← hm, mul_one]
  constructor
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [mem_ball_zero_iff] at hy
    obtain ⟨z, hz, hze⟩ := hφ' x y (by linarith) (by linarith)
    refine ⟨z, ?_, hze⟩
    rw [mem_ball, dist_eq_norm]
    have e1 := hD z x hz (by linarith)
    have e2 := hD y 0 (by linarith) h0η
    rw [sub_zero] at e2
    have e3 := hLx x b2 (m (e y) - m (e 0))
    rw [hze, hmx y] at e1
    have nι : ‖ι (z - x)‖ = ‖z - x‖ := ι.norm_map _
    have nιy : ‖ι y‖ = ‖y‖ := ι.norm_map _
    set v := m (e y) - m (e 0) with hv
    have t1 : ‖z - x‖ ≤ ‖L (e x) v‖ + ε * ‖z - x‖ := by
      have h := norm_sub_norm_le (ι (z - x)) (L (e x) v)
      have h' : ‖ι (z - x) - L (e x) v‖ = ‖L (e x) v - ι (z - x)‖ := norm_sub_rev _ _
      linarith
    have t2 : ‖L (e x) v‖ ≤ (1 + ε) * ‖v‖ := by
      have h := norm_sub_norm_le (L (e x) v) v
      linarith
    have t3 : ‖v‖ ≤ (1 + ε) * ‖y‖ := by
      have h := norm_sub_norm_le v (ι y)
      linarith
    have k1 : (1 - ε) * ‖z - x‖ ≤ (1 + ε) ^ 2 * ‖y‖ := by
      have := mul_le_mul_of_nonneg_left t3 (by linarith : (0 : ℝ) ≤ 1 + ε)
      linarith only [t1, t2, this]
    have k2 : (1 + ε) ^ 2 * ‖y‖ < (1 + ε) ^ 2 * r := mul_lt_mul_of_pos_left hy (by positivity)
    have k3 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r := mul_lt_mul_of_pos_right hκε hr0
    have k4 : κ * (1 - ε) ^ 2 * r ≤ κ * (1 - ε) * r := by
      have h1 : (1 - ε) ^ 2 ≤ 1 - ε := by
        rw [sq]
        exact mul_le_of_le_one_left (by linarith) (by linarith)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by linarith)) hr0.le
    have k5 : (1 - ε) * ‖z - x‖ < (1 - ε) * (κ * r) := by linarith only [k1, k2, k3, k4]
    exact lt_of_mul_lt_mul_left k5 (by linarith)
  · rintro _ ⟨w, hw, rfl⟩
    rw [mem_ball, dist_eq_norm] at hw
    have hwx := norm_sub_norm_le w x
    obtain ⟨y, hyη, hye⟩ := hψ' x w (by linarith) (by linarith)
    have hexy : e w = e x * e y := by rw [hye, mul_inv_cancel_left]
    refine ⟨e y, ⟨y, ?_, rfl⟩, hexy.symm⟩
    rw [mem_ball_zero_iff]
    have e1 := hD w x (by linarith) (by linarith)
    have e2 := hD y 0 hyη h0η
    rw [sub_zero] at e2
    have e3 := hLx x b2 (m (e y) - m (e 0))
    rw [hexy, hmx y] at e1
    have nι : ‖ι (w - x)‖ = ‖w - x‖ := ι.norm_map _
    have nιy : ‖ι y‖ = ‖y‖ := ι.norm_map _
    set v := m (e y) - m (e 0) with hv
    have s1 : ‖L (e x) v‖ ≤ (1 + ε) * ‖w - x‖ := by
      have h := norm_sub_norm_le (L (e x) v) (ι (w - x))
      linarith
    have s2 : (1 - ε) * ‖v‖ ≤ ‖L (e x) v‖ := by
      have h := norm_sub_norm_le v (L (e x) v)
      have h' : ‖v - L (e x) v‖ = ‖L (e x) v - v‖ := norm_sub_rev _ _
      linarith
    have s3 : (1 - ε) * ‖y‖ ≤ ‖v‖ := by
      have h := norm_sub_norm_le (ι y) v
      have h' : ‖ι y - v‖ = ‖v - ι y‖ := norm_sub_rev _ _
      linarith
    have k1 : (1 - ε) ^ 2 * ‖y‖ ≤ (1 - ε) * ‖v‖ := by
      have := mul_le_mul_of_nonneg_left s3 (by linarith : (0 : ℝ) ≤ 1 - ε)
      linarith only [this]
    have k2 : (1 + ε) * ‖w - x‖ < (1 + ε) * r := mul_lt_mul_of_pos_left hw (by linarith)
    have k3 : (1 + ε) * r ≤ (1 + ε) ^ 2 * r := by
      linarith only [mul_pos hε0 hr0, mul_pos (mul_pos hε0 hε0) hr0]
    have k4 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r := mul_lt_mul_of_pos_right hκε hr0
    have k5 : (1 - ε) ^ 2 * ‖y‖ < (1 - ε) ^ 2 * (κ * r) := by
      linarith only [k1, s2, s1, k2, k3, k4]
    exact lt_of_mul_lt_mul_left k5 (pow_pos (by linarith) 2).le

end GlobalTheory
end

section

open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem gram_det_index_sublattice (U V ι κ : Type) [AddCommGroup U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : U →ₗ[ℤ] V) (u : ι → U) (v : κ → U) (hc : Fintype.card ι = Fintype.card κ)
    (hv : ∀ k, v k ∈ Submodule.span ℤ (Set.range u)) :
    ∃ m : ℕ, (Matrix.gram ℝ fun k => φ (v k)).det = (m : ℝ) ^ 2 * (Matrix.gram ℝ fun i => φ (u i)).det ∧
      ∀ i, (m : ℤ) • u i ∈ Submodule.span ℤ (Set.range v) := by
  let e : ι ≃ κ := Fintype.equivOfCardEq hc
  choose A hA using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hv (e i))
  let Am : Matrix ι ι ℤ := Matrix.of A
  have hAm : ∀ i j, Am i j = A i j := fun _ _ => rfl
  let Ar : Matrix ι ι ℝ := Am.map (Int.castRingHom ℝ)
  have hAr : ∀ i j, Ar i j = (A i j : ℝ) := fun _ _ => rfl
  have hphi : ∀ i, φ (v (e i)) = ∑ j, (A i j : ℝ) • φ (u j) := by
    intro i

    rw [← hA i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have h1 : (Matrix.gram ℝ fun k => φ (v k)).submatrix e e
      = Ar * (Matrix.gram ℝ fun i => φ (u i)) * Arᵀ := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, hAr]
    rw [hphi i, hphi j, inner_sum]
    simp only [sum_inner, real_inner_smul_left, real_inner_smul_right, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hdetA : Ar.det = (Am.det : ℝ) := by
    have := (Int.castRingHom ℝ).map_det Am
    simpa [Ar] using this.symm
  refine ⟨Am.det.natAbs, ?_, ?_⟩
  · have h2 := Matrix.det_submatrix_equiv_self e (Matrix.gram ℝ fun k => φ (v k))
    rw [← h2, h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetA]
    have h3 : ((Am.det.natAbs : ℕ) : ℝ) ^ 2 = (Am.det : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [h3]; ring
  · intro i
    have hkey : Am.det • u i = ∑ k, Am.adjugate i k • v (e k) := by
      have h4 : ∀ j, (Am.adjugate * Am) i j = Am.det * (1 : Matrix ι ι ℤ) i j := by
        intro j
        rw [Matrix.adjugate_mul, Matrix.smul_apply, smul_eq_mul]
      calc Am.det • u i = ∑ j, (Am.det * (1 : Matrix ι ι ℤ) i j) • u j := by
            simp [Matrix.one_apply, ite_smul]
        _ = ∑ j, (∑ k, Am.adjugate i k * A k j) • u j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← h4 j, Matrix.mul_apply]; rfl
        _ = ∑ k, Am.adjugate i k • v (e k) := by
            simp only [Finset.sum_smul, ← hA, Finset.smul_sum, mul_smul]
            exact Finset.sum_comm
    have hmem : Am.det • u i ∈ Submodule.span ℤ (Set.range v) := by
      rw [hkey]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨e k, rfl⟩)
    rcases Int.natAbs_eq Am.det with h | h
    · rw [← h]; exact hmem
    · have : ((Am.det.natAbs : ℕ) : ℤ) = -Am.det := by omega
      rw [this, neg_smul]
      exact Submodule.neg_mem _ hmem

end GlobalTheory
end
