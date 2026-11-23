module

public import Formalism.LandauZeroFreeBounds.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos_ter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + t * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    push_neg at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hρ
  have hwre : ((σ : ℂ) + t * I - ρ).re = σ - ρ.re := by simp
  have hwpos : 0 < ((σ : ℂ) + t * I - ρ).re := by rw [hwre]; linarith
  have hw0 : (σ : ℂ) + t * I - ρ ≠ 0 := fun h => by rw [h] at hwpos; simp at hwpos
  rw [one_div, Complex.inv_re]
  exact div_pos hwpos (Complex.normSq_pos.mpr hw0)

lemma sum_mult_re_one_div_sub_zeros_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : Finset ℂ)
    (m : ℂ → ℕ) (hZ : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + t * I - ρ)).re := by
  exact Finset.sum_nonneg fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_ter χ hχ ρ (hZ ρ hρ) σ t hσ).le



theorem zeroFreeNonRealCharOfBounds : NoZeroComplexOf := by
  unfold NoZeroComplexOf LocalZeros LLogDerivRight Positivity NoZeroComplex InRegion
  intro hLZ hLD hPos
  obtain ⟨C0, hC0⟩ := hLZ
  obtain ⟨C1, hC1nn, hC1⟩ := hLD
  set K : ℝ := |C0| with hK
  have hKnn : 0 ≤ K := abs_nonneg _
  set A : ℝ := 6 * K + 5 * C1 + 1 with hA
  have hApos : 0 < A := by rw [hA]; linarith
  set δ : ℝ := min (1 / 10) (1 / (2 * A)) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 10 := min_le_left _ _
  have hδ2 : δ ≤ 1 / (2 * A) := min_le_right _ _
  refine ⟨δ / 8, by positivity, ?_⟩
  intro q _ χ s hχ2 hreg hzero
  have hχ : χ ≠ 1 := fun h => hχ2 (by rw [h, one_pow])
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set ℓ := Real.log ((q : ℝ) * (|s.im| + 2)) with hℓ
  have hlog2 : Real.log 2 ≤ ℓ :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hℓ69 : (0.69 : ℝ) < ℓ := lt_of_lt_of_le hl2 hlog2
  have hℓpos : 0 < ℓ := by linarith
  have hβ1 : s.re < 1 := by
    by_contra h
    push_neg at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hzero
  have hsmall : δ / 8 / ℓ ≤ 1 / 10 := by
    rw [div_le_iff₀ hℓpos]
    linarith
  have hβ9 : 9 / 10 ≤ s.re := by linarith
  set σ : ℝ := 1 + δ / ℓ with hσ
  have hvpos : 0 < δ / ℓ := div_pos hδpos hℓpos
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 6 / 5 := by
    have : δ / ℓ ≤ 1 / 5 := by
      rw [div_le_iff₀ hℓpos]
      linarith
    linarith
  set u : ℝ := 1 / δ with hu

  have b0 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ ℓ * u + C1 := by
    have h1 := hC1 q 1 (σ : ℂ) (by simpa using hσ1)
    have h2 := Complex.re_le_norm (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ))
    have h3 : 1 / ((σ : ℂ).re - 1) = ℓ * u := by
      rw [Complex.ofReal_re, hσ, hu, add_sub_cancel_left, one_div_div, div_eq_mul_one_div]
    rw [h3] at h1
    linarith

  obtain ⟨Z, m, hZ, hm1, -, hbd⟩ := hC0 q χ hχ s.im
  have hsZ : s ∈ Z := by
    refine (hZ s).mpr ⟨?_, hzero⟩
    have e : s - ((11 / 10 : ℂ) + s.im * I) = ((s.re - 11 / 10 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [mem_closedBall_iff_norm, e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hterm : 1 / (σ - s.re) ≤ (m s : ℝ) * (1 / ((σ : ℂ) + s.im * I - s)).re := by
    have e : (σ : ℂ) + s.im * I - s = ((σ - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    have e2 : (1 / ((σ - s.re : ℝ) : ℂ)).re = 1 / (σ - s.re) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [e, e2]
    have hm : (1 : ℝ) ≤ (m s : ℝ) := by exact_mod_cast hm1 s hsZ
    have hpos : 0 < 1 / (σ - s.re) := by apply div_pos one_pos; linarith
    nlinarith
  have hsum : (m s : ℝ) * (1 / ((σ : ℂ) + s.im * I - s)).re ≤
      ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re :=
    Finset.single_le_sum (f := fun ρ => (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re)
      (fun ρ hρ => mul_nonneg (Nat.cast_nonneg _)
        (re_one_div_sub_zero_pos_ter χ hχ ρ ((hZ ρ).mp hρ).2 σ s.im hσ1).le) hsZ
  have hgap : σ - s.re ≤ (9 / 8) * (δ / ℓ) := by
    have : δ / 8 / ℓ = (δ / ℓ) / 8 := by ring
    rw [hσ]
    linarith
  have hgappos : 0 < σ - s.re := by linarith
  have hinv : (8 / 9) * (ℓ * u) ≤ 1 / (σ - s.re) := by
    have h1 := one_div_le_one_div_of_le hgappos hgap
    have h2 : 1 / ((9 / 8) * (δ / ℓ)) = (8 / 9) * (ℓ * u) := by
      rw [hu]
      field_simp
    linarith
  have b1 : (negLD χ ((σ : ℂ) + s.im * I)).re ≤ K * ℓ - (8 / 9) * (ℓ * u) := by
    have h1 := hbd σ hσ1 hσ2
    rw [← hℓ] at h1
    have h2 : C0 * ℓ ≤ K * ℓ := mul_le_mul_of_nonneg_right (le_abs_self C0) hℓpos.le
    linarith

  obtain ⟨Z2, m2, hZ2, -, -, hbd2⟩ := hC0 q (χ ^ 2) hχ2 (2 * s.im)
  have hL2 : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ 2 * ℓ := by
    have ha := abs_nonneg s.im
    have h1 : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ Real.log (((q : ℝ) * (|s.im| + 2)) ^ 2) := by
      apply Real.log_le_log
      · rw [abs_mul, abs_two]
        positivity
      · rw [abs_mul, abs_two]
        nlinarith [mul_le_mul_of_nonneg_right hq (sq_nonneg (|s.im| + 2))]
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hL2nn : 0 ≤ Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg (2 * s.im)])
  have b2 : (negLD (χ ^ 2) ((σ : ℂ) + 2 * s.im * I)).re ≤ 2 * (K * ℓ) := by
    have h1 := hbd2 σ hσ1 hσ2
    push_cast at h1
    have h2 := sum_mult_re_one_div_sub_zeros_nonneg (χ ^ 2) hχ2 Z2 m2 (fun ρ hρ => ((hZ2 ρ).mp hρ).2) σ (2 * s.im) hσ1
    push_cast at h2
    have h3 : C0 * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ K * Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C0) hL2nn
    have h4 : K * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ K * (2 * ℓ) :=
      mul_le_mul_of_nonneg_left hL2 hKnn
    have h5 : K * (2 * ℓ) = 2 * (K * ℓ) := by ring
    linarith

  have hP := (hPos q σ hσ1).1 χ s.im
  have hu2 : 2 * A ≤ u := by
    have h1 := one_div_le_one_div_of_le hδpos hδ2
    rw [one_div_one_div] at h1
    exact h1
  have cu : 12 * (K * ℓ) + 10 * (C1 * ℓ) + 2 * ℓ ≤ ℓ * u := by
    have h1 := mul_le_mul_of_nonneg_left hu2 hℓpos.le
    have e : ℓ * (2 * A) = 12 * (K * ℓ) + 10 * (C1 * ℓ) + 2 * ℓ := by rw [hA]; ring
    linarith
  have c1 : 3 * C1 ≤ 5 * (C1 * ℓ) := by
    have := mul_le_mul_of_nonneg_left hℓ69.le hC1nn
    linarith
  have hKl : 0 ≤ K * ℓ := mul_nonneg hKnn hℓpos.le
  have hCl : 0 ≤ C1 * ℓ := mul_nonneg hC1nn hℓpos.le
  linarith

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hρ
  have hz : ((σ : ℂ) - ρ).re = σ - ρ.re := by simp
  have hpos : 0 < ((σ : ℂ) - ρ).re := by rw [hz]; linarith
  have hne : ((σ : ℂ) - ρ) ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  rw [one_div, Complex.inv_re]
  exact div_pos hpos (Complex.normSq_pos.mpr hne)

lemma re_one_div_ofReal_sub (σ : ℝ) (ρ : ℂ) :
    (1 / ((σ : ℂ) - ρ)).re = (σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma mul_le_div_sq_add_sq (T X G : ℝ) (hT : 0 < T) (h1 : 1 ≤ T * X) (h2 : T * X ≤ 11 / 10)
    (h3 : |T * G| ≤ 1 / 10) : 4 / 5 * T ≤ X / (X ^ 2 + G ^ 2) := by
  have hX : 0 < X := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hv : (T * G) ^ 2 ≤ 1 / 100 := by
    have := sq_abs (T * G)
    nlinarith [abs_nonneg (T * G)]
  have key : T * (4 / 5 * T * (X ^ 2 + G ^ 2)) ≤ T * X := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ T * X) (by linarith : 0 ≤ 11 / 10 - T * X)]
  have := le_of_mul_le_mul_left key hT
  rw [le_div_iff₀ (add_pos_of_pos_of_nonneg (pow_pos hX 2) (sq_nonneg G))]
  exact this

theorem realCharZeroSmallHeightOfBounds : RealSmallTOf := by
  intro hLZ hLD hPos hConj
  obtain ⟨C, hC⟩ := hLZ
  obtain ⟨C₀, hC₀, hLD⟩ := hLD
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hCCp : C ≤ Cp := le_max_left _ _
  set K : ℝ := 2 * C₀ + Cp with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  set W : ℝ := 10 * (K + 1) with hW
  have hW10 : 10 ≤ W := by rw [hW]; linarith
  have hWpos : 0 < W := by linarith
  refine ⟨1 / (10 * W), 1 / (10 * W), by positivity, by positivity, ?_⟩
  intro q _ χ hχ2 hχ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)

  obtain ⟨Z, m, hZ, hm1, hm2, hb⟩ := hC q χ hχ 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hZ hb
  set L₀ := Real.log ((q : ℝ) * 2) with hL₀
  have hlog2 := Real.log_two_gt_d9
  have hL₀2 : Real.log 2 ≤ L₀ := Real.log_le_log (by norm_num) (by nlinarith)
  have hL₀h : 1 / 2 < L₀ := by norm_num at hlog2; linarith
  have hL₀pos : 0 < L₀ := by linarith
  set T : ℝ := W * L₀ with hT
  have hTpos : 0 < T := mul_pos hWpos hL₀pos
  have hT5 : 5 ≤ T := by rw [hT]; nlinarith
  have hTe : T = 10 * (K * L₀) + 10 * L₀ := by rw [hT, hW]; ring
  have hKL : K * L₀ = 2 * (C₀ * L₀) + Cp * L₀ := by rw [hK]; ring
  set σ : ℝ := 1 + 1 / T with hσ
  have hσ1 : 1 < σ := by
    have : 0 < 1 / T := by positivity
    linarith
  have hσ2 : σ ≤ 6 / 5 := by
    have : 1 / T ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hT5
    linarith

  have hF1 : ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤ (11 * K + 10) * L₀ := by
    have hP := (hPos q σ hσ1).2.1 χ hχ2
    have h0 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ T + C₀ := by
      have h := hLD q 1 (σ : ℂ) (by simpa using hσ1)
      have e : 1 / ((σ : ℂ).re - 1) = T := by
        rw [Complex.ofReal_re, hσ, add_sub_cancel_left, one_div_one_div]
      rw [e] at h
      exact (Complex.re_le_norm _).trans h
    have h1 := hb σ hσ1 hσ2
    have h2 : C * L₀ ≤ Cp * L₀ := mul_le_mul_of_nonneg_right hCCp hL₀pos.le
    have h3 : C₀ ≤ 2 * (C₀ * L₀) := by nlinarith
    have h4 : (11 * K + 10) * L₀ = 11 * (K * L₀) + 10 * L₀ := by ring
    rw [h4]
    linarith

  have hnn : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re := fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos' χ hχ ρ ((hZ ρ).mp hρ).2 σ hσ1).le

  have hcons : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
      InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 →
      ρ ∈ Z ∧ 4 / 5 * T ≤ (1 / ((σ : ℂ) - ρ)).re := by
    intro ρ hi hr hz
    unfold InRegion at hr
    obtain ⟨Lρ, hLρdef⟩ : ∃ x : ℝ, x = Real.log ((q : ℝ) * (|ρ.im| + 2)) := ⟨_, rfl⟩
    rw [← hLρdef] at hi hr
    have hLρ : L₀ ≤ Lρ := by
      rw [hLρdef, hL₀]
      exact Real.log_le_log (by positivity) (by nlinarith [abs_nonneg ρ.im])
    have hdiv : 1 / (10 * W) / Lρ ≤ 1 / (10 * T) := by
      have := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1 / (10 * W)) hL₀pos hLρ
      have e : 1 / (10 * W) / L₀ = 1 / (10 * T) := by rw [hT, div_div, mul_assoc]
      linarith
    have hβ1 : ρ.re < 1 := by
      by_contra h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hz
    have hβ : 1 - 1 / (10 * T) ≤ ρ.re := by linarith
    have hγ : |ρ.im| ≤ 1 / (10 * T) := by linarith
    have hsmall : 1 / (10 * T) ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hTT : T * (1 / (10 * T)) = 1 / 10 := by field_simp
    refine ⟨(hZ ρ).mpr ⟨?_, hz⟩, ?_⟩
    · rw [Metric.mem_closedBall, Complex.dist_eq]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e0 : (11 / 10 : ℂ) = ((11 / 10 : ℝ) : ℂ) := by push_cast; rfl
      rw [e0, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      have : |ρ.re - 11 / 10| ≤ 1 / 10 + 1 / (10 * T) := by
        rw [abs_le]; constructor <;> linarith
      linarith
    · rw [re_one_div_ofReal_sub]
      have hTσ : T * (σ - ρ.re) = T * (1 - ρ.re) + 1 := by
        rw [hσ]; field_simp; ring
      have hA : 0 < T * (1 - ρ.re) := mul_pos hTpos (by linarith)
      have hB : T * (1 - ρ.re) ≤ T * (1 / (10 * T)) :=
        mul_le_mul_of_nonneg_left (by linarith) hTpos.le
      apply mul_le_div_sq_add_sq T (σ - ρ.re) ρ.im hTpos
      · rw [hTσ]; linarith
      · rw [hTσ]; linarith
      · rw [abs_mul, abs_of_pos hTpos]
        have := mul_le_mul_of_nonneg_left hγ hTpos.le
        linarith
  have hbig : (11 * K + 10) * L₀ < 8 / 5 * T := by
    have : 0 ≤ K * L₀ := mul_nonneg hK0 hL₀pos.le
    nlinarith

  have htwo : ∀ ρ₁ ρ₂ : ℂ,
      (|ρ₁.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₁.im| + 2)) ∧
        InRegion (1 / (10 * W)) q ρ₁ ∧ DirichletCharacter.LFunction χ ρ₁ = 0) →
      (|ρ₂.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₂.im| + 2)) ∧
        InRegion (1 / (10 * W)) q ρ₂ ∧ DirichletCharacter.LFunction χ ρ₂ = 0) →
      ρ₁ ≠ ρ₂ → False := by
    rintro ρ₁ ρ₂ ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ hne
    obtain ⟨h1Z, h1r⟩ := hcons ρ₁ a1 b1 c1
    obtain ⟨h2Z, h2r⟩ := hcons ρ₂ a2 b2 c2
    have hsub : ({ρ₁, ρ₂} : Finset ℂ) ⊆ Z := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1Z
      · exact h2Z
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ _ => hnn ρ hρ)
    rw [Finset.sum_pair hne] at hs
    have hm1' : (1 : ℝ) ≤ m ρ₁ := by exact_mod_cast hm1 ρ₁ h1Z
    have hm2' : (1 : ℝ) ≤ m ρ₂ := by exact_mod_cast hm1 ρ₂ h2Z
    have hr1 : 0 ≤ (1 / ((σ : ℂ) - ρ₁)).re := by linarith
    have hr2 : 0 ≤ (1 / ((σ : ℂ) - ρ₂)).re := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1') hr1, mul_nonneg (sub_nonneg.mpr hm2') hr2]

  have hdouble : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
      InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 →
      deriv (DirichletCharacter.LFunction χ) ρ = 0 → False := by
    intro ρ a b c hd
    obtain ⟨hρZ, hρr⟩ := hcons ρ a b c
    have hs := Finset.single_le_sum hnn hρZ
    have hm : (2 : ℝ) ≤ m ρ := by exact_mod_cast hm2 ρ hρZ hd
    have hr : 0 ≤ (1 / ((σ : ℂ) - ρ)).re := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hr]
  intro s s' hs hs' hrs hrs' hz hz'
  have hsim : s.im = 0 := by
    by_contra hne
    refine htwo s (starRingEnd ℂ s) ⟨hs, hrs, hz⟩ ⟨?_, ?_, ?_⟩ ?_
    · simpa [Complex.conj_im, abs_neg] using hs
    · unfold InRegion at hrs ⊢
      simpa [Complex.conj_re, Complex.conj_im, abs_neg] using hrs
    · rw [hConj q χ hχ2 hχ s, hz, map_zero]
    · intro h
      apply hne
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
  refine ⟨hsim, fun hd => hdouble s hs hrs hz hd, ?_⟩
  by_contra hne
  exact htwo s' s ⟨hs', hrs', hz'⟩ ⟨hs, hrs, hz⟩ hne

end Formalism.ZeroFreeDirichlet
end
end

section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma one_sub_prime_cpow_neg_ne_zero (p : ℕ) (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.1 h).symm
  have h2 := congrArg norm h1
  rw [norm_natCast_cpow_of_pos hp.pos, norm_one, neg_re] at h2
  have h3 : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  linarith

theorem trivialCharZerosOfZeta : TrivZeros := by
  intro q _ s hs hs1 h0
  have hmul := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs1
  have h0' : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s = 0 := by
    rw [← hmul]
    exact h0
  rcases mul_eq_zero.1 h0' with h | h
  · exfalso
    obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.1 h
    exact one_sub_prime_cpow_neg_ne_zero p (Nat.prime_of_mem_primeFactors hp) hs hp0
  · exact h

lemma conj_apply_of_sq_eq_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (a : ZMod q) :
    starRingEnd ℂ (χ a) = χ a := by
  by_cases ha : IsUnit a
  · have h2 : χ a * χ a = 1 := by
      rw [← sq, ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply ha]
    rcases mul_self_eq_one_iff.1 h2 with h | h
    · rw [h, map_one]
    · rw [h, map_neg, map_one]
  · rw [MulChar.map_nonunit χ ha, map_zero]

lemma conj_LFunction_conj_of_sq_eq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (z : ℂ) (hz : 1 < z.re) :
    starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)) =
      DirichletCharacter.LFunction χ z := by
  have hz' : 1 < (starRingEnd ℂ z).re := by rwa [Complex.conj_re]
  rw [DirichletCharacter.LFunction_eq_LSeries χ hz', DirichletCharacter.LFunction_eq_LSeries χ hz,
    LSeries, LSeries, Complex.conj_tsum]
  congr 1
  funext m
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs with hm
  · exact map_zero _
  · show starRingEnd ℂ (χ m / (m : ℂ) ^ starRingEnd ℂ z) = χ m / (m : ℂ) ^ z
    have harg : (m : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    rw [map_div₀, conj_apply_of_sq_eq_one χ hχ, Complex.cpow_conj _ _ harg, map_natCast (starRingEnd ℂ) m,
      Complex.conj_conj]

theorem realCharConj : RealConj := by
  intro q _ χ hχ h1 s
  have hL : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction h1
  have hG : Differentiable ℂ
      (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))) := by
    intro z
    have := (hL (starRingEnd ℂ z)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have heq : (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))) =
      DirichletCharacter.LFunction χ := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (analyticOnNhd_univ_iff_differentiable.2 hG)
      (analyticOnNhd_univ_iff_differentiable.2 hL) ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact conj_LFunction_conj_of_sq_eq_one χ hχ z hz
  have := congrFun heq (starRingEnd ℂ s)
  simp only [Complex.conj_conj] at this
  exact this.symm

end Formalism.ZeroFreeDirichlet
end
end
