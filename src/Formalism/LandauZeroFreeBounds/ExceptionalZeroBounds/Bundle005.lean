module

public import Formalism.LandauZeroFreeBounds.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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

@[expose] public section

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma one_le_natCast (q : ℕ) [NeZero q] : (1 : ℝ) ≤ q := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)

lemma log_two_le_log_mul_abs_add_two (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq := one_le_natCast q
  apply Real.log_le_log (by norm_num)
  nlinarith [abs_nonneg t]

lemma log_mul_abs_add_two_pos (q : ℕ) [NeZero q] (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_log_mul_abs_add_two q t)

lemma inRegion_mono' {c c' : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (h : c ≤ c') (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at *
  have hL := log_mul_abs_add_two_pos q s.im
  have := div_le_div_of_nonneg_right h hL.le
  linarith

lemma re_pos_of_inRegion {c : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hc : c ≤ 1 / 2) (hs : InRegion c q s) :
    0 < s.re := by
  unfold InRegion at hs
  have hL := log_two_le_log_mul_abs_add_two q s.im
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := div_le_div_of_nonneg_right hc hLpos.le
  have h2 : (1 / 2 : ℝ) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ (1 / 2) / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) h2pos hL
  have h3 : (1 / 2 : ℝ) / Real.log 2 < 1 := by
    rw [div_lt_one h2pos]; linarith [Real.log_two_gt_d9]
  linarith

lemma one_sub_div_log_le_re {c cz : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hcz : 0 < cz) (h : c ≤ cz)
    (hs : InRegion c q s) : 1 - cz / Real.log (|s.im| + 2) ≤ s.re := by
  unfold InRegion at hs
  have hq := one_le_natCast q
  have hT : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hlogT : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith)
  have hle : Real.log (|s.im| + 2) ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h1 := div_le_div_of_nonneg_right h hLpos.le
  have h2 := div_le_div_of_nonneg_left hcz.le hlogT hle
  linarith

theorem zeroFreeRegionExceptionalZeroOfBounds : ZFRDirichletOf := by
  intro hZ hT hN hL hS h2
  obtain ⟨cz, hcz, hZ⟩ := hZ
  obtain ⟨cN, hcN, hN⟩ := hN
  obtain ⟨δ, cS, hδ, hcS, hS⟩ := hS
  obtain ⟨cL, hcL, hL⟩ := hL δ hδ
  obtain ⟨c2, hc2, h2⟩ := h2
  set c := min (min (min cz cN) (min cL cS)) (min c2 (1 / 2)) with hc
  have hc0 : 0 < c := lt_min (lt_min (lt_min hcz hcN) (lt_min hcL hcS)) (lt_min hc2 (by norm_num))
  have hccz : c ≤ cz := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hccN : c ≤ cN := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hccL : c ≤ cL := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hccS : c ≤ cS := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcc2 : c ≤ c2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc12 : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc0, ?_⟩
  intro q _ χ s hs hz

  have key : ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), InRegion c q s → IsLZero χ s →
      χ ^ 2 = 1 ∧ χ ≠ 1 ∧ |s.im| < δ / Real.log ((q : ℝ) * (|s.im| + 2)) := by
    intro χ s hs hz
    obtain ⟨hne, h0⟩ := hz
    have hχ1 : χ ≠ 1 := by
      rintro rfl
      have hs1 : s ≠ 1 := hne.resolve_left (fun h => h rfl)
      have hre := re_pos_of_inRegion hc12 hs
      exact hZ s hs1 (one_sub_div_log_le_re hcz hccz hs) (hT q s hre hs1 h0)
    have hsq : χ ^ 2 = 1 := by
      by_contra hsq
      exact hN q χ s hsq (inRegion_mono' hccN hs) h0
    refine ⟨hsq, hχ1, ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hL q χ s hsq hχ1 hlt (inRegion_mono' hccL hs) h0
  obtain ⟨hsq, hχ1, hsm⟩ := key χ s hs hz
  obtain ⟨him, hder, -⟩ := hS q χ hsq hχ1 s s hsm hsm (inRegion_mono' hccS hs)
    (inRegion_mono' hccS hs) hz.2 hz.2
  refine ⟨hsq, hχ1, him, hder, ?_⟩
  intro χ' s' hs' hz'
  obtain ⟨hsq', hχ1', hsm'⟩ := key χ' s' hs' hz'
  have him' := (hS q χ' hsq' hχ1' s' s' hsm' hsm' (inRegion_mono' hccS hs')
    (inRegion_mono' hccS hs') hz'.2 hz'.2).1
  have hχeq : χ' = χ := by
    by_contra hne
    have es : ((s.re : ℝ) : ℂ) = s := Complex.ext (by simp) (by simp [him])
    have es' : ((s'.re : ℝ) : ℂ) = s' := Complex.ext (by simp) (by simp [him'])
    have r1 : InRegion c2 q ((s.re : ℝ) : ℂ) := by rw [es]; exact inRegion_mono' hcc2 hs
    have r2 : InRegion c2 q ((s'.re : ℝ) : ℂ) := by rw [es']; exact inRegion_mono' hcc2 hs'
    rcases h2 q χ χ' hsq hsq' hχ1 hχ1' (Ne.symm hne) s.re s'.re r1 r2 with h | h
    · exact h (by rw [es]; exact hz.2)
    · exact h (by rw [es']; exact hz'.2)
  refine ⟨hχeq, ?_⟩
  rw [hχeq] at hz'
  exact (hS q χ hsq hχ1 s s' hsm hsm' (inRegion_mono' hccS hs) (inRegion_mono' hccS hs')
    hz.2 hz'.2).2.2

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + t * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra hc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ) (not_lt.mp hc) hρ
  have hwre : ((σ : ℂ) + t * I - ρ).re = σ - ρ.re := by simp
  have hw0 : (σ : ℂ) + t * I - ρ ≠ 0 := fun h => by
    have h' : ((σ : ℂ) + t * I - ρ).re = 0 := by rw [h, Complex.zero_re]
    linarith
  rw [one_div, Complex.inv_re]
  exact div_pos (by rw [hwre]; linarith) (Complex.normSq_pos.mpr hw0)

lemma re_one_div_ofReal_add_mul_I (x y : ℝ) :
    (1 / ((x : ℂ) + y * I)).re = x / (x ^ 2 + y ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_add_mul_I]
  simp

lemma two_le_mul_abs_add_two (q : ℕ) [NeZero q] (t : ℝ) : 2 ≤ (q : ℝ) * (|t| + 2) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  nlinarith [abs_nonneg t]

lemma log_mul_abs_two_mul_le (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ 2 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht := abs_nonneg t
  have e : 2 * Real.log ((q : ℝ) * (|t| + 2)) = Real.log (((q : ℝ) * (|t| + 2)) ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [abs_mul, abs_two, e]
  apply Real.log_le_log (by positivity)
  have h1 : (q : ℝ) * (2 * |t| + 2) ≤ (q : ℝ) * (|t| + 2) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have h2 : (q : ℝ) * (|t| + 2) ^ 2 ≤ ((q : ℝ) * (|t| + 2)) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  linarith

theorem realCharZeroFreeLargeHeightOfBounds : RealLargeTOf := by
  intro hLZ hLD hPos hTriv δ hδ
  obtain ⟨C₁, hC₁⟩ := hLZ
  obtain ⟨C₂, hC₂0, hC₂⟩ := hLD
  obtain ⟨C₃, hC₃⟩ := hTriv
  have hM₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hM₃ : 0 ≤ max C₃ 0 := le_max_right _ _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * max C₁ 0 + 2 * max C₃ 0 + 6 * C₂ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min (δ / 2) (min (1 / 10) (1 / (4 * K + 1))) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have ha1 : a ≤ δ / 2 := by rw [ha]; exact min_le_left _ _
  have ha2 : a ≤ 1 / 10 := by rw [ha]; exact (min_le_right _ _).trans (min_le_left _ _)
  have ha3 : a ≤ 1 / (4 * K + 1) := by rw [ha]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hKa : K * a ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at ha3
    nlinarith
  have hδa : a ^ 2 / (4 * δ ^ 2) ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q _ χ s hχ2 hχ1 hδt hreg hzero
  have hreg' : 1 - a / 8 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hreg
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log ((q : ℝ) * (|s.im| + 2)) := ⟨_, rfl⟩
  rw [← hLdef] at hreg' hδt
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL : 1 / 2 < L := by
    rw [hLdef]
    exact lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) (two_le_mul_abs_add_two q s.im))
  have hLpos : 0 < L := by linarith
  have hβ1 : s.re < 1 := by
    by_contra hc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ1) (not_lt.mp hc)
      hzero
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 1 + a / L := ⟨_, rfl⟩
  have haL : 0 < a / L := div_pos ha0 hLpos
  have haL5 : a / L ≤ 1 / 5 := by
    rw [div_le_iff₀ hLpos]
    linarith
  have hσ1 : 1 < σ := by linarith
  have hσ65 : σ ≤ 6 / 5 := by linarith
  have ha8 : a / 8 / L = (a / L) / 8 := by ring
  have hσβ : σ - s.re ≤ 9 / 8 * (a / L) := by linarith
  have hσβpos : 0 < σ - s.re := by linarith
  obtain ⟨Z, m, hZ, hm1, -, hbd⟩ := hC₁ q χ hχ1 s.im
  have hsZ : s ∈ Z := by
    rw [hZ]
    refine ⟨?_, hzero⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hd : s - ((11 / 10 : ℂ) + s.im * I) = ((s.re - 11 / 10 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have : a / L / 8 ≤ 1 / 40 := by linarith
    constructor <;> linarith
  have hterm : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re := fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _)
      (re_one_div_sub_zero_pos χ hχ1 ρ ((hZ ρ).mp hρ).2 σ s.im hσ1).le
  have hs_term : (1 / ((σ : ℂ) + s.im * I - s)).re = 1 / (σ - s.re) := by
    have hd : (σ : ℂ) + s.im * I - s = ((σ - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hd, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hsum : 1 / (σ - s.re) ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re := by
    refine le_trans ?_ (Finset.single_le_sum hterm hsZ)
    rw [hs_term]
    have h1 : (1 : ℝ) ≤ m s := by exact_mod_cast hm1 s hsZ
    have h0 : 0 ≤ 1 / (σ - s.re) := by positivity
    nlinarith
  have hu : 8 / 9 * (L / a) ≤ 1 / (σ - s.re) := by
    have h1 := one_div_le_one_div_of_le hσβpos hσβ
    have e : 1 / (9 / 8 * (a / L)) = 8 / 9 * (L / a) := by field_simp
    rw [e] at h1
    exact h1
  have hP := (hPos q σ hσ1).1 χ s.im
  rw [hχ2] at hP
  have h1 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ L / a + C₂ := by
    have h := hC₂ q 1 (σ : ℂ) (by simpa using hσ1)
    have e : 1 / ((σ : ℂ).re - 1) = L / a := by
      rw [Complex.ofReal_re, hσ, add_sub_cancel_left, one_div_div]
    rw [e] at h
    exact (Complex.re_le_norm _).trans h
  have h2 := hbd σ hσ1 hσ65
  rw [← hLdef] at h2
  have h3 := hC₃ q σ (2 * s.im) hσ1 (by linarith)
  have hpole := re_one_div_ofReal_add_mul_I (σ - 1) (2 * s.im)
  push_cast at h3 hpole
  rw [hpole] at h3
  have ht2 : δ ^ 2 / L ^ 2 ≤ s.im ^ 2 := by
    have h0 : 0 ≤ δ / L := by positivity
    have h := pow_le_pow_left₀ h0 hδt 2
    rwa [div_pow, sq_abs] at h
  have hσ1' : σ - 1 = a / L := by rw [hσ]; ring
  have hpb : (σ - 1) / ((σ - 1) ^ 2 + (2 * s.im) ^ 2) ≤ a * L / (4 * δ ^ 2) := by
    rw [hσ1']
    have hden : 0 < (a / L) ^ 2 + (2 * s.im) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have e : a / L = a * L / (4 * δ ^ 2) * (4 * (δ ^ 2 / L ^ 2)) := by field_simp
    have hc : 0 ≤ a * L / (4 * δ ^ 2) := by positivity
    calc a / L = a * L / (4 * δ ^ 2) * (4 * (δ ^ 2 / L ^ 2)) := e
      _ ≤ a * L / (4 * δ ^ 2) * ((a / L) ^ 2 + (2 * s.im) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hc
        nlinarith [sq_nonneg (a / L)]
  have hX0 : 0 ≤ Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
    Real.log_nonneg (by have := two_le_mul_abs_add_two q (2 * s.im); linarith)
  have hX : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ 2 * L := by
    rw [hLdef]; exact log_mul_abs_two_mul_le q s.im
  have hC3X : C₃ * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ max C₃ 0 * (2 * L) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0).trans (mul_le_mul_of_nonneg_left hX hM₃)
  have hC1L : C₁ * L ≤ max C₁ 0 * L := mul_le_mul_of_nonneg_right (le_max_left _ _) hLpos.le
  have hw : 0 < L / a := div_pos hLpos ha0
  have hKL : K * L ≤ L / a / 4 := by
    calc K * L = K * a * (L / a) := by field_simp
      _ ≤ 1 / 4 * (L / a) := mul_le_mul_of_nonneg_right hKa hw.le
      _ = L / a / 4 := by ring
  have hKL' : K * L = 4 * max C₁ 0 * L + 2 * max C₃ 0 * L + 6 * C₂ * L := by rw [hK]; ring
  have hPw : a * L / (4 * δ ^ 2) ≤ L / a / 16 := by
    calc a * L / (4 * δ ^ 2) = a ^ 2 / (4 * δ ^ 2) * (L / a) := by field_simp
      _ ≤ 1 / 16 * (L / a) := mul_le_mul_of_nonneg_right hδa hw.le
      _ = L / a / 16 := by ring
  have hC2 : 3 * C₂ ≤ 6 * C₂ * L := by
    have h := mul_nonneg hC₂0 (show (0 : ℝ) ≤ 2 * L - 1 by linarith)
    linarith
  linarith [h1, h2, h3, hpb, hC3X, hC1L, hsum, hu, hKL, hKL', hPw, hC2, hP]

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_sub_le_re_of_mem_closedBall {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : z₀.re - r ≤ w.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have h1 := Complex.abs_re_le_norm (w - z₀)
  have h2 := neg_abs_le (w - z₀).re
  rw [Complex.sub_re] at h1 h2
  linarith

lemma norm_le_norm_add_of_mem_closedBall {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : ‖w‖ ≤ ‖z₀‖ + r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  calc ‖w‖ = ‖z₀ + (w - z₀)‖ := by rw [add_sub_cancel]
    _ ≤ ‖z₀‖ + ‖w - z₀‖ := norm_add_le _ _
    _ ≤ ‖z₀‖ + r := by linarith

lemma norm_center_le (t : ℝ) : ‖(11 / 10 : ℂ) + t * I‖ ≤ 11 / 10 + |t| := by
  have h1 : ‖(11 / 10 : ℂ)‖ = 11 / 10 := by
    rw [show (11 / 10 : ℂ) = ((11 / 10 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num)]
  have h2 : ‖(t : ℂ) * I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc ‖(11 / 10 : ℂ) + t * I‖ ≤ ‖(11 / 10 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    _ = 11 / 10 + |t| := by rw [h1, h2]

lemma re_sum_div_sub (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) :
    (∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)).re = ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (z - ρ)).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [div_eq_mul_one_div, show ((m ρ : ℕ) : ℂ) = ((m ρ : ℝ) : ℂ) by norm_cast, Complex.re_ofReal_mul]

lemma log_le_div_log_two_mul (C₁ L : ℝ) (hC₁ : 1 ≤ C₁) (hL : Real.log 2 ≤ L) :
    Real.log (22 * C₁) ≤ Real.log (22 * C₁) / Real.log 2 * L := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 ≤ Real.log (22 * C₁) := Real.log_nonneg (by linarith)
  rw [div_mul_eq_mul_div, le_div_iff₀ h2]
  exact mul_le_mul_of_nonneg_left hL ha

theorem localZeroSumBoundOfBounds : LocalZerosOf := by
  intro hLan hGr hInv
  obtain ⟨C, hC⟩ := hGr
  set C₁ : ℝ := max C 1 with hC₁def
  have hC₁ : 1 ≤ C₁ := le_max_right _ _
  have hCC : C ≤ C₁ := le_max_left _ _
  refine ⟨120 * (1 + Real.log (22 * C₁) / Real.log 2), ?_⟩
  intro q _ χ hχ t
  set z₀ : ℂ := (11 / 10 : ℂ) + t * I with hz₀
  have hz₀re : z₀.re = 11 / 10 := by
    rw [hz₀, Complex.add_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]
    norm_num
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have ht0 : 0 ≤ |t| := abs_nonneg t
  set M : ℝ := 22 * C₁ * q * (|t| + 2) with hM
  have hM1 : 1 ≤ M := by
    have h1 : 1 ≤ C₁ * q := by nlinarith
    nlinarith
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall z₀ (3 / 5)) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have hnz : ∀ s : ℂ, 1 < s.re → DirichletCharacter.LFunction χ s ≠ 0 := fun s hs =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
  have hf0 : DirichletCharacter.LFunction χ z₀ ≠ 0 := hnz z₀ (by rw [hz₀re]; norm_num)
  have hlow : 1 / 11 ≤ ‖DirichletCharacter.LFunction χ z₀‖ := by
    have h := hInv q χ z₀ (by rw [hz₀re]; norm_num)
    rw [hz₀re, show (11 / 10 : ℝ) / (11 / 10 - 1) = 11 by norm_num] at h
    have hpos : 0 < ‖DirichletCharacter.LFunction χ z₀‖ := norm_pos_iff.2 hf0
    rw [inv_le_comm₀ hpos (by norm_num)] at h
    calc (1 / 11 : ℝ) = (11 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := h
  have hbound : ∀ z ∈ Metric.closedBall z₀ (3 / 5),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := by
    intro z hz
    have hre : 1 / 2 ≤ z.re := by
      have := re_sub_le_re_of_mem_closedBall hz
      rw [hz₀re] at this
      linarith
    have h1 := hC q χ hχ z hre
    have hn : ‖z‖ ≤ 11 / 10 + |t| + 3 / 5 := by
      have := norm_le_norm_add_of_mem_closedBall hz
      have := norm_center_le t
      linarith
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ C * q * (1 + ‖z‖) := h1
      _ ≤ C₁ * q * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hq0) (by linarith)
      _ ≤ C₁ * q * (2 * (|t| + 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hq0)
      _ = M * (1 / 11) := by rw [hM]; ring
      _ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := mul_le_mul_of_nonneg_left hlow (by linarith)
  obtain ⟨Z, m, hZ, hm1, hm2, -, happrox⟩ :=
    hLan (DirichletCharacter.LFunction χ) z₀ (3 / 5) M (by norm_num) hM1 hdiff hf0 hbound
  refine ⟨Z, m, ?_, hm1, hm2, ?_⟩
  · intro ρ
    rw [hZ ρ, show (3 / 5 : ℝ) / 3 = 1 / 5 by norm_num]
  · intro σ hσ1 hσ2
    set s : ℂ := (σ : ℂ) + t * I with hs
    have hsre : s.re = σ := by
      rw [hs, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]
    have hsball : s ∈ Metric.closedBall z₀ ((3 / 5) / 6) := by
      rw [Metric.mem_closedBall, dist_eq_norm, show (3 / 5 : ℝ) / 6 = 1 / 10 by norm_num]
      have hd : s - z₀ = ((σ - 11 / 10 : ℝ) : ℂ) := by
        rw [hs, hz₀]
        push_cast
        ring
      rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hfs : DirichletCharacter.LFunction χ s ≠ 0 := hnz s (by rw [hsre]; exact hσ1)
    have hA := happrox s hsball hfs
    have hpos1 : 0 < 22 * C₁ := by linarith
    have hpos2 : 0 < (q : ℝ) * (|t| + 2) := by positivity
    have hL : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    have hlogM : Real.log M ≤
        (1 + Real.log (22 * C₁) / Real.log 2) * Real.log ((q : ℝ) * (|t| + 2)) := by
      have hMe : M = (22 * C₁) * ((q : ℝ) * (|t| + 2)) := by rw [hM]; ring
      rw [hMe, Real.log_mul hpos1.ne' hpos2.ne']
      have := log_le_div_log_two_mul C₁ _ hC₁ hL
      nlinarith
    have hre := Complex.abs_re_le_norm
      (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
    have hre' := neg_abs_le
      (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re
    rw [Complex.sub_re, re_sum_div_sub] at hre hre'
    have h72 : 72 * Real.log M / (3 / 5) = 120 * Real.log M := by ring
    rw [h72] at hA
    have hneg : (negLD χ s).re =
        -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s).re := by
      rw [negLD, Complex.neg_re]
    rw [hneg]
    nlinarith

end Formalism.ZeroFreeDirichlet
end
end
