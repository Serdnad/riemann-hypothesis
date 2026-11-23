module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneSubConjMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SummableNinePowMulInvSqSucc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionEqTsumOfOneLt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
public import Mathlib.NumberTheory.Harmonic.Bounds
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LWide

theorem disc (r R : ℝ) (hr : 0 < r) (hrR : r < R) (hR : R < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℂ → ℂ) (c : ℂ) (a M : ℝ), 0 < a → Differentiable ℂ F → F c ≠ 0 →
      (∀ z, ‖z - c‖ ≤ a → ‖F z‖ ≤ M) →
      {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0}.Finite ∧
      (∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0}, (analyticOrderNatAt F w : ℝ))
        ≤ C * (1 + Real.log (M / ‖F c‖)) ∧
      ∀ s : ℂ, ‖s - c‖ ≤ r * a → F s ≠ 0 →
        a * ‖deriv F s / F s - ∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0},
          (analyticOrderNatAt F w : ℂ) / (s - w)‖ ≤ C * (1 + Real.log (M / ‖F c‖)) := by
  obtain ⟨C, hC, H⟩ := LogDerivZeros.main r R hr hrR hR
  refine ⟨C, hC, fun F c a M ha hF hc hM => ?_⟩
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set φ : ℂ → ℂ := fun z => c + a * z with hφ
  have hφn : ∀ z, ‖φ z - c‖ = a * ‖z‖ := fun z => by
    simp [hφ, abs_of_pos ha]
  have hφd : ∀ z, HasDerivAt φ a z := fun z => by
    simpa [hφ] using ((hasDerivAt_id z).const_mul (a : ℂ)).const_add c
  have hφa : ∀ z, AnalyticAt ℂ φ z := fun z => by
    simp only [hφ]; fun_prop
  have hφ0 : φ 0 = c := by simp [hφ]
  have hinj : Function.Injective φ := fun x y h => by
    simpa [hφ, hac] using h
  have hsurj : ∀ w, φ ((w - c) / a) = w := fun w => by
    simp only [hφ]; field_simp; ring
  obtain ⟨⟨h1, h2⟩, h3⟩ := H (F ∘ φ) M
    (fun z _ => (hF.analyticAt _).comp (hφa z)) (by simpa [hφ0] using hc)
    (fun z hz => hM _ (by
      rw [hφn]; exact mul_le_of_le_one_right ha.le (by simpa using hz)))
  have hset : {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0} = φ '' {w : ℂ | ‖w‖ ≤ R ∧ (F ∘ φ) w = 0} := by
    ext w
    constructor
    · rintro ⟨hw, hw0⟩
      refine ⟨(w - c) / a, ⟨?_, by simpa [hsurj] using hw0⟩, hsurj w⟩
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le, div_le_iff₀ ha]
      exact hw
    · rintro ⟨z, ⟨hz, hz0⟩, rfl⟩
      refine ⟨?_, hz0⟩
      rw [hφn, mul_comm]
      gcongr
  have hord : ∀ z, analyticOrderNatAt (F ∘ φ) z = analyticOrderNatAt F (φ z) := fun z => by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_comp_of_deriv_ne_zero (hφa z) (by rw [(hφd z).deriv]; exact hac)]
  simp only [hord, Function.comp_apply (f := F) (g := φ) (x := 0), hφ0] at h2 h3
  rw [hset]
  refine ⟨h1.image _, ?_, fun s hs hs0 => ?_⟩
  · rw [finsum_mem_image hinj.injOn]
    exact h2
  · obtain ⟨z, rfl⟩ : ∃ z, φ z = s := ⟨_, hsurj s⟩
    rw [finsum_mem_image hinj.injOn]
    rw [hφn, mul_comm] at hs
    have h4 := h3 z (le_of_mul_le_mul_right hs ha) hs0
    refine le_trans (le_of_eq ?_) h4
    have hd : deriv (F ∘ φ) z = deriv F (φ z) * a :=
      ((hF (φ z)).hasDerivAt.comp z (hφd z)).deriv
    rw [hd, finsum_mem_eq_finite_toFinset_sum _ h1, finsum_mem_eq_finite_toFinset_sum _ h1]
    conv_lhs => rw [← Real.norm_of_nonneg ha.le, ← Complex.norm_real, ← norm_mul]
    congr 1
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · simp only [Function.comp_apply]; ring
    · refine Finset.sum_congr rfl fun w _ => ?_
      have : φ z - φ w = a * (z - w) := by simp only [hφ]; ring
      rw [this, ← mul_div_assoc, mul_div_mul_left _ _ hac]

theorem logDeriv_LFunction_strip : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ LFunction χ w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℝ)) ≤ C * Real.log (q * (|s.im| + 2)) ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|s.im| + 2)) := by
  obtain ⟨C, hC, H⟩ := disc (4 / 5) (14 / 15) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B, hB, G⟩ := norm_LFunction_le_poly_left
  refine ⟨C * (2 * (1 + |Real.log (512 * B)|) + 4), by positivity, ?_⟩
  intro q _ χ hχ s hs1 hs2 hs0
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set c : ℂ := 2 + s.im * I with hc
  have hcre : c.re = 2 := by simp [hc]
  have hcn : ‖c‖ ≤ 2 + |s.im| := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp
  have hlow : 1 / 2 ≤ ‖LFunction χ c‖ := by
    have := LLower.norm_LFunction_ge q χ c (by rw [hcre]; norm_num)
    rw [hcre] at this
    linarith
  have ht := abs_nonneg s.im
  set X : ℝ := q * (|s.im| + 2) with hX
  have hX2 : 2 ≤ X := by nlinarith
  have hlX : 1 / 2 ≤ Real.log X := by
    have := Real.log_le_log (by norm_num) hX2
    linarith [Real.log_two_gt_d9]
  have hpos : 0 < ‖LFunction χ c‖ := by linarith
  obtain ⟨h1, h2, h3⟩ := H (LFunction χ) c (15 / 4) (256 * B * X ^ 4) (by norm_num)
    (differentiable_LFunction hχ) (norm_pos_iff.1 hpos) (fun z hz => by
      have hre : -(7 / 4 : ℝ) ≤ z.re := by
        have := (abs_le.1 ((Complex.abs_re_le_norm (z - c)).trans hz)).1
        rw [sub_re, hcre] at this
        linarith
      refine (G q χ hχ z hre).trans ?_
      have hzn : ‖z‖ + 2 ≤ 4 * (|s.im| + 2) := by
        have := norm_le_norm_sub_add z c
        linarith
      calc B * (q : ℝ) ^ 4 * (‖z‖ + 2) ^ 4 ≤ B * (q : ℝ) ^ 4 * (4 * (|s.im| + 2)) ^ 4 := by gcongr
        _ = _ := by rw [hX]; ring)
  have e : (14 / 15 : ℝ) * (15 / 4) = 7 / 2 := by norm_num
  rw [e] at h1 h2 h3
  have hsc : ‖s - c‖ ≤ 4 / 5 * (15 / 4) := by
    have : s - c = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h4 := h3 s hsc hs0
  have hlog : Real.log (256 * B * X ^ 4 / ‖LFunction χ c‖) ≤ Real.log (512 * B) + 4 * Real.log X := by
    have hX0 : 0 < X := by linarith
    have : 256 * B * X ^ 4 / ‖LFunction χ c‖ ≤ 512 * B * X ^ 4 := by
      rw [div_le_iff₀ hpos]
      have : 0 < B * X ^ 4 := by positivity
      nlinarith
    refine (Real.log_le_log (by positivity) this).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hfin : C * (1 + Real.log (256 * B * X ^ 4 / ‖LFunction χ c‖))
      ≤ C * (2 * (1 + |Real.log (512 * B)|) + 4) * Real.log X := by
    rw [mul_assoc C]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    have h5 := le_abs_self (Real.log (512 * B))
    have h6 := abs_nonneg (Real.log (512 * B))
    nlinarith
  refine ⟨h1, h2.trans hfin, le_trans ?_ (h4.trans hfin)⟩
  exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)

end GlobalTheory.LWide
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.DirichletDeriv

theorem rpow_neg_le {q n : ℕ} (hn : 1 ≤ n) (hnq : n ≤ q) {x : ℝ}
    (hx : 1 - 2 / Real.log (3 * q) ≤ x) : (n : ℝ) ^ (-x) ≤ Real.exp 2 * (n : ℝ)⁻¹ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnq' : (n : ℝ) ≤ q := by exact_mod_cast hnq
  have hL : 0 < Real.log (3 * q) := Real.log_pos (by linarith)
  have hl : Real.log n ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have h1 : (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ (2 / Real.log (3 * q) + (-1)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  refine h1.trans ?_
  rw [Real.rpow_add (by linarith), Real.rpow_neg_one]
  gcongr
  rw [Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  rw [← mul_div_assoc, div_le_iff₀ hL]
  linarith

theorem norm_LFunction_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (h1 : 1 - 2 / Real.log (3 * q) ≤ s.re) (h2 : 1 / 20 ≤ s.re) (h3 : ‖s‖ ≤ 2) :
    ‖LFunction χ s‖ ≤ 84 * Real.exp 2 * Real.log (3 * q) := by
  have hq : 1 ≤ q := NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : 0 < s.re := by linarith
  have hL : 1 ≤ Real.log (3 * q) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hl : Real.log q ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have hE : 0 < Real.exp 2 := Real.exp_pos 2
  have ht := GlobalTheory.DirichletTail.norm_LFunction_sub_sum_le q χ hχ s hs q hq
  have hd : ‖s‖ / s.re ≤ 40 := by rw [div_le_iff₀ hs]; linarith
  have ht2 : 2 * q * (1 + ‖s‖ / s.re) * (q : ℝ) ^ (-s.re) ≤ 82 * Real.exp 2 := by
    calc 2 * q * (1 + ‖s‖ / s.re) * (q : ℝ) ^ (-s.re)
        ≤ 2 * q * (1 + 40) * (Real.exp 2 * (q : ℝ)⁻¹) := by
          gcongr
          exact rpow_neg_le hq le_rfl h1
      _ = 82 * Real.exp 2 := by field_simp; ring
  have hsum : ‖∑ n ∈ Finset.Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
      ≤ Real.exp 2 * (1 + Real.log q) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Icc 1 q, ‖χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.Icc 1 q, Real.exp 2 * (n : ℝ)⁻¹ := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rw [Finset.mem_Icc] at hn
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
          exact (mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans
            (rpow_neg_le hn.1 hn.2 h1)
      _ = Real.exp 2 * (harmonic q : ℝ) := by
          rw [← Finset.mul_sum, harmonic_eq_sum_Icc]; push_cast; rfl
      _ ≤ Real.exp 2 * (1 + Real.log q) := by
          gcongr
          exact harmonic_le_one_add_log q
  have h4 := norm_le_norm_sub_add (LFunction χ s)
    (∑ n ∈ Finset.Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-s))
  nlinarith

theorem exists_norm_deriv_LFunction_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ σ : ℝ,
      1 - 1 / Real.log (3 * q) ≤ σ → σ ≤ 1 →
        ‖deriv (LFunction χ) σ‖ ≤ C * Real.log (3 * q) ^ 2 := by
  refine ⟨336 * Real.exp 2, by positivity, fun q _ χ hχ σ h1 h2 => ?_⟩
  have hq : 2 ≤ q := by
    have h0 := NeZero.pos q
    by_contra h
    obtain rfl : q = 1 := by omega
    exact hχ (DirichletCharacter.level_one χ)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hL : 1.38 ≤ Real.log (3 * q) := by
    have h4 : Real.log (2 ^ 2) ≤ Real.log (3 * q) := Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h4
    push_cast at h4
    linarith [Real.log_two_gt_d9]
  set L := Real.log (3 * q) with hLdef
  have hL0 : 0 < L := by linarith
  have hinv : 1 / L ≤ 3 / 4 := by rw [div_le_iff₀ hL0]; linarith
  have hinv0 : 0 < 1 / L := by positivity
  have hr : 0 < 1 / L / 4 := by positivity
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := LFunction χ) (c := (σ : ℂ))
    (C := 84 * Real.exp 2 * L) hr (differentiable_LFunction hχ).diffContOnCl (fun z hz => by
      rw [mem_sphere_iff_norm] at hz
      have hre := Complex.abs_re_le_norm (z - σ)
      rw [hz, Complex.sub_re, Complex.ofReal_re, abs_le] at hre
      have h2L : 2 / L = 2 * (1 / L) := by ring
      refine norm_LFunction_le χ hχ (by rw [← hLdef, h2L]; linarith [hre.1]) (by linarith [hre.1]) ?_
      have h5 := norm_le_norm_sub_add z (σ : ℂ)
      rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h5
      linarith)
  refine key.trans (le_of_eq ?_)
  field_simp
  ring

end GlobalTheory.DirichletDeriv
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem sum_Icc_three_quarters_pow_le (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (3 / 4 : ℝ) ^ j ≤ 3 - 3 * (3 / 4 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [pow_succ]
    linarith

theorem powerSum_weighted_ineq {ι : Type} (S : Finset ι) (z : ι → ℂ) (b : ι → ℕ) (i₀ : ι)
    (L δ x : ℝ) (hi : i₀ ∈ S) (hb : 1 ≤ b i₀) (hL : 1 ≤ L) (hδ : 0 < δ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) (hz : 1 / (1 + x) ≤ ‖z i₀‖) (hS : (∑ i ∈ S, (b i : ℝ)) ≤ L)
    (hp : ∀ j : ℕ, 1 ≤ j → (∑ i ∈ S, (b i : ℂ) * z i ^ j).re ≤ 2 * j * δ + L / 2 ^ j) (J : ℕ) :
    (J : ℝ) / 4 - 7 * L ≤ 4 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J := by
  classical
  obtain ⟨i₁, hi₁, hmax⟩ := Finset.exists_max_image (S.filter fun i => 1 ≤ b i)
    (fun i => ‖z i‖) ⟨i₀, Finset.mem_filter.2 ⟨hi, hb⟩⟩
  obtain ⟨hi₁S, hb₁⟩ := Finset.mem_filter.1 hi₁
  set R : ℝ := ‖z i₁‖ with hR
  have h1x : 0 < 1 + x := by linarith
  have hRge : 1 / (1 + x) ≤ R := hz.trans (hmax i₀ (Finset.mem_filter.2 ⟨hi, hb⟩))
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hRge
  have hRinv : R⁻¹ ≤ 1 + x := by
    rw [inv_le_comm₀ hRpos h1x, ← one_div]; exact hRge
  have hRinv0 : 0 ≤ R⁻¹ := by positivity
  set θ : ℝ := Complex.arg (z i₁) with hθ
  obtain ⟨hF1, hF2⟩ := GlobalTheory.T.neg_one_le_sum_fejer_cos_re_pow_and_lower_bound J θ
  set c : ℕ → ℝ := fun j => (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) with hc
  set F : ℂ → ℝ := fun w => ∑ j ∈ Finset.Icc 1 J, c j * (w ^ j).re with hF
  have hF1' : ∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ F w := hF1
  have hF2' : (J : ℝ) / 4 - 3 / 4 ≤ F (Complex.exp (θ * I)) := hF2
  set w : ι → ℂ := fun i => ((R⁻¹ : ℝ) : ℂ) * z i with hw
  have hw₁ : w i₁ = Complex.exp (θ * I) := by
    have h := Complex.norm_mul_exp_arg_mul_I (z i₁)
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
    show ((R⁻¹ : ℝ) : ℂ) * z i₁ = _
    rw [← h]
    push_cast
    rw [← hR, ← hθ, ← mul_assoc, inv_mul_cancel₀ hR', one_mul]
  have hwn : ∀ i ∈ S, 1 ≤ b i → ‖w i‖ ≤ 1 := by
    intro i hiS hbi
    have := hmax i (Finset.mem_filter.2 ⟨hiS, hbi⟩)
    show ‖((R⁻¹ : ℝ) : ℂ) * z i‖ ≤ 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hRinv0, inv_mul_le_iff₀ hRpos, mul_one]
    exact this

  have hlow : (J : ℝ) / 4 - L ≤ ∑ i ∈ S, (b i : ℝ) * F (w i) := by
    have hnn : ∀ i ∈ S, 0 ≤ (b i : ℝ) * (F (w i) + 1) := by
      intro i hiS
      rcases Nat.eq_zero_or_pos (b i) with h0 | h0
      · simp [h0]
      · have := hF1' _ (hwn i hiS h0)
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have h1 := Finset.single_le_sum hnn hi₁S
    have hb1 : (1 : ℝ) ≤ b i₁ := by exact_mod_cast hb₁
    have h2 := hF1' _ (hwn i₁ hi₁S hb₁)
    have h3 : F (w i₁) + 1 ≤ (b i₁ : ℝ) * (F (w i₁) + 1) := by nlinarith
    have h4 : ∑ i ∈ S, (b i : ℝ) * (F (w i) + 1)
        = ∑ i ∈ S, (b i : ℝ) * F (w i) + ∑ i ∈ S, (b i : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [← hw₁] at hF2'
    linarith

  have hex : ∑ i ∈ S, (b i : ℝ) * F (w i)
      = ∑ j ∈ Finset.Icc 1 J, c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re) := by
    simp only [hF, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have e1 : (w i ^ j).re = R⁻¹ ^ j * (z i ^ j).re := by
      show ((((R⁻¹ : ℝ) : ℂ) * z i) ^ j).re = _
      rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    have e2 : ((b i : ℂ) * z i ^ j).re = (b i : ℝ) * (z i ^ j).re := by
      rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    rw [e1, e2]; ring

  have hup : ∀ j ∈ Finset.Icc 1 J,
      c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re)
        ≤ 4 * J * δ * (1 + x) ^ J + 2 * L * (3 / 4 : ℝ) ^ j := by
    intro j hj
    obtain ⟨hj1, hjJ⟩ := Finset.mem_Icc.1 hj
    have hjJ' : (j : ℝ) ≤ J := by exact_mod_cast hjJ
    have hJ1 : (0 : ℝ) < J + 1 := by positivity
    have ha0 : 0 ≤ 1 - (j : ℝ) / (J + 1) := by
      rw [sub_nonneg, div_le_one hJ1]; linarith
    have ha1 : 1 - (j : ℝ) / (J + 1) ≤ 1 := by
      have : 0 ≤ (j : ℝ) / (J + 1) := by positivity
      linarith
    have hcos1 := Real.cos_le_one (j * θ)
    have hcos2 := Real.neg_one_le_cos (j * θ)
    have hc0 : 0 ≤ c j := mul_nonneg ha0 (by linarith)
    have hc2 : c j ≤ 2 := by
      show (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) ≤ 2
      nlinarith
    have hq : R⁻¹ ^ j ≤ (1 + x) ^ j := pow_le_pow_left₀ hRinv0 hRinv j
    have hq2 : (1 + x) ^ j ≤ (1 + x) ^ J := pow_le_pow_right₀ (by linarith) hjJ
    have hq3 : (1 + x) ^ j ≤ (3 / 2 : ℝ) ^ j := pow_le_pow_left₀ h1x.le (by linarith) j
    have hB0 : 0 ≤ 2 * j * δ + L / 2 ^ j := by positivity
    have s1 : R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re
        ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j) :=
      (mul_le_mul_of_nonneg_left (hp j hj1) (by positivity)).trans
        (mul_le_mul_of_nonneg_right hq hB0)
    have s2 : (1 + x) ^ j * (2 * j * δ) ≤ (1 + x) ^ J * (2 * J * δ) := by gcongr
    have s3 : (1 + x) ^ j * (L / 2 ^ j) ≤ (3 / 2 : ℝ) ^ j * (L / 2 ^ j) := by gcongr
    have s4 : (3 / 2 : ℝ) ^ j * (L / 2 ^ j) = L * (3 / 4 : ℝ) ^ j := by
      have : (3 / 4 : ℝ) ^ j = (3 / 2 : ℝ) ^ j / 2 ^ j := by rw [← div_pow]; norm_num
      rw [this]; ring
    have s5 : 0 ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j) := by positivity
    calc c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re)
        ≤ c j * ((1 + x) ^ j * (2 * j * δ + L / 2 ^ j)) := mul_le_mul_of_nonneg_left s1 hc0
      _ ≤ 2 * ((1 + x) ^ j * (2 * j * δ + L / 2 ^ j)) := mul_le_mul_of_nonneg_right hc2 s5
      _ ≤ _ := by rw [mul_add ((1 + x) ^ j)]; linarith
  have hsum := Finset.sum_le_sum hup
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul] at hsum
  have hg := sum_Icc_three_quarters_pow_le J
  have hg0 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ J := by positivity
  have hg' : 2 * L * ∑ j ∈ Finset.Icc 1 J, (3 / 4 : ℝ) ^ j ≤ 2 * L * 3 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have : (J : ℝ) * (4 * J * δ * (1 + x) ^ J) = 4 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J := by ring
  linarith

theorem powerSum_repulsion :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (b : ι → ℕ) (i₀ : ι) (L δ x : ℝ), i₀ ∈ S → 1 ≤ b i₀ → 1 ≤ L → 0 < δ → 0 ≤ x → x ≤ 1 / 2 → 1 / (1 + x) ≤ ‖z i₀‖ → (∑ i ∈ S, (b i : ℝ)) ≤ L → (∀ j : ℕ, 1 ≤ j → (∑ i ∈ S, (b i : ℂ) * z i ^ j).re ≤ 2 * j * δ + L / 2 ^ j) → Real.log (1 / (C * L * δ)) / (C * L) ≤ x := by
  refine ⟨2080, by norm_num, ?_⟩
  intro ι S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp
  have h := powerSum_weighted_ineq S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp ⌈64 * L⌉₊
  set J : ℕ := ⌈64 * L⌉₊ with hJ
  have hJ1 : 64 * L ≤ J := Nat.le_ceil _
  have hJ2 : (J : ℝ) ≤ 65 * L := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 64 * L by linarith)
    linarith
  have hJ0 : (0 : ℝ) < J := by linarith
  have hP : (1 + x) ^ J ≤ Real.exp (x * J) := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) J
  have hP0 : 0 < (1 + x) ^ J := by positivity
  have h1 : (J : ℝ) * 1 ≤ J * (32 * J * δ * (1 + x) ^ J) := by nlinarith
  have h2 : 1 ≤ 32 * J * δ * (1 + x) ^ J := le_of_mul_le_mul_left h1 hJ0
  have h3 : 32 * J * δ * (1 + x) ^ J ≤ 2080 * L * δ * Real.exp (x * J) := by
    have : 32 * (J : ℝ) ≤ 2080 * L := by linarith
    gcongr
  have hD : 0 < 2080 * L * δ := by positivity
  have h4 : 1 / (2080 * L * δ) ≤ Real.exp (x * J) := by
    rw [div_le_iff₀ hD]; linarith
  have h5 : Real.log (1 / (2080 * L * δ)) ≤ x * J :=
    (Real.log_le_iff_le_exp (by positivity)).2 h4
  rw [div_le_iff₀ (by positivity)]
  have : x * J ≤ x * (2080 * L) := mul_le_mul_of_nonneg_left (by linarith) hx0
  linarith

end GlobalTheory
end
