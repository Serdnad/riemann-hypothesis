module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationTowerLevelAlgebraPrescribed
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle146
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle145
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.TermDiff

lemma rpow_neg_sub_le {x y p : ℝ} (hx : 1/2 ≤ x) (hxy : x ≤ y) (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    |x ^ (-p) - y ^ (-p)| ≤ 8 * (y - x) / y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  set r := x / y with hr
  have hr0 : 0 < r := div_pos hx0 hy0
  have hr1 : r ≤ 1 := (div_le_one hy0).2 hxy
  have hyr : y ^ (-p) = x ^ (-p) * r ^ p := by
    rw [hr, Real.div_rpow hx0.le hy0.le, Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
    have : 0 < x ^ p := Real.rpow_pos_of_pos hx0 p
    have : 0 < y ^ p := Real.rpow_pos_of_pos hy0 p
    field_simp
  have hrp1 : r ^ p ≤ 1 := Real.rpow_le_one hr0.le hr1 hp0
  have hrp2 : r ^ (2:ℝ) ≤ r ^ p := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hp2
  have hr2 : r ^ (2:ℝ) = r ^ 2 := Real.rpow_two r
  have hxp : x ^ (-p) ≤ 4 := by
    rw [Real.rpow_neg hx0.le, ← Real.inv_rpow hx0.le]
    have h1 : x⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hx0 (by norm_num)]; linarith
    calc x⁻¹ ^ p ≤ (2:ℝ) ^ p := Real.rpow_le_rpow (inv_nonneg.2 hx0.le) h1 hp0
      _ ≤ (2:ℝ) ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
      _ = 4 := by norm_num
  have hxp0 : 0 ≤ x ^ (-p) := Real.rpow_nonneg hx0.le _
  rw [hyr]
  have e : x ^ (-p) - x ^ (-p) * r ^ p = x ^ (-p) * (1 - r ^ p) := by ring
  rw [e, abs_of_nonneg (mul_nonneg hxp0 (by linarith))]
  have h1r : 1 - r ^ p ≤ 2 * (1 - r) := by
    have : 1 - r^2 ≤ 2 * (1 - r) := by nlinarith [mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hr1)]
    rw [hr2] at hrp2
    linarith
  have h1r' : 1 - r = (y - x) / y := by rw [hr]; field_simp
  calc x ^ (-p) * (1 - r ^ p) ≤ 4 * (2 * (1 - r)) :=
        mul_le_mul hxp h1r (by linarith) (by norm_num)
    _ = 8 * (y - x) / y := by rw [h1r']; ring

lemma norm_pow_sub_pow_le (z w : ℂ) (n : ℕ) (M : ℝ) (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ‖w ^ (n+1) - z ^ (n+1)‖ ≤ (n+1) * M ^ n * ‖w - z‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  gcongr
  have hM : 0 ≤ M := (norm_nonneg z).trans hz
  calc ‖∑ i ∈ Finset.range (n+1), w ^ i * z ^ (n + 1 - 1 - i)‖
      ≤ ∑ i ∈ Finset.range (n+1), ‖w ^ i * z ^ (n + 1 - 1 - i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), M ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖w‖ ^ i * ‖z‖ ^ (n + 1 - 1 - i) ≤ M ^ i * M ^ (n + 1 - 1 - i) := by gcongr
          _ = M ^ n := by rw [← pow_add]; congr 1; omega
    _ = (n+1) * M ^ n := by simp

lemma inv_pow_sub_le (j : ℕ) (z w : ℂ) (hz : 0 < ‖z‖) (hwz : ‖w - z‖ ≤ ‖z‖ / 2) :
    ‖(z ^ j)⁻¹ - (w ^ j)⁻¹‖ ≤ j * 4 ^ j * ‖w - z‖ / ‖z‖ ^ (j + 1) := by
  have hW1 : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
    have := norm_sub_le w (w - z); simpa using this
  have hW2 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
    have := norm_add_le z (w - z); simpa using this
  have hWl : ‖z‖ / 2 ≤ ‖w‖ := by linarith
  have hW0 : 0 < ‖w‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hz
  have hw0 : w ≠ 0 := norm_pos_iff.1 hW0
  cases j with
  | zero => simp
  | succ n =>
    rw [inv_sub_inv (pow_ne_zero _ hz0) (pow_ne_zero _ hw0), norm_div, norm_mul, norm_pow, norm_pow]
    have hM : ‖w‖ ≤ 2 * ‖z‖ := by linarith
    have hnum := norm_pow_sub_pow_le z w n (2 * ‖z‖) (by linarith) hM
    have hden : ‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1) ≤ ‖z‖ ^ (n+1) * ‖w‖ ^ (n+1) := by gcongr
    have hdpos : 0 < ‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1) := by positivity
    calc ‖w ^ (n+1) - z ^ (n+1)‖ / (‖z‖ ^ (n+1) * ‖w‖ ^ (n+1))
        ≤ ((n+1) * (2 * ‖z‖) ^ n * ‖w - z‖) / (‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1)) :=
          div_le_div₀ (by positivity) hnum hdpos hden
      _ = (n+1) * 2 ^ (2 * n + 1) * ‖w - z‖ / ‖z‖ ^ (n + 2) := by
          rw [div_pow, mul_pow]; field_simp; ring
      _ ≤ ((n+1 : ℕ) : ℝ) * 4 ^ (n+1) * ‖w - z‖ / ‖z‖ ^ (n + 1 + 1) := by
          push_cast
          gcongr
          calc (2:ℝ) ^ (2 * n + 1) ≤ 2 ^ (2 * n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
            _ = 4 ^ (n+1) := by rw [show 2 * n + 2 = 2 * (n+1) by ring, pow_mul]; norm_num

theorem first_diff : ∀ j : ℕ, ∃ C : ℝ, ∀ (s : ℝ) (z a : ℂ), 0 ≤ s → s ≤ 1 → 1 ≤ ‖z‖ → 2 * ‖a‖ ≤ ‖z‖ → ‖trm j s z - trm j s (z + a)‖ ≤ C * ‖a‖ / ‖z‖ ^ (j + 1) := by
  intro j
  refine ⟨j * 4 ^ j + 8 * 2 ^ j, ?_⟩
  intro s z a hs0 hs1 hz ha
  have hZ : 0 < ‖z‖ := by linarith
  have hwz : (z + a) - z = a := by ring
  have hA : ‖(z + a) - z‖ ≤ ‖z‖ / 2 := by rw [hwz]; linarith
  have hW1 : ‖z‖ ≤ ‖z + a‖ + ‖a‖ := by
    have := norm_sub_le (z + a) a; simpa using this
  have hW2 : ‖z + a‖ ≤ ‖z‖ + ‖a‖ := norm_add_le z a
  have hWl : ‖z‖ / 2 ≤ ‖z + a‖ := by linarith
  have hW0 : 0 < ‖z + a‖ := by linarith
  have hv : ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)
  have hdv : ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)‖ ≤ 8 * ‖a‖ / ‖z‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, neg_mul]
    rcases le_total ‖z‖ ‖z + a‖ with h | h
    · refine (rpow_neg_sub_le (by linarith) h (by linarith) (by linarith)).trans ?_
      rw [div_le_div_iff₀ hW0 hZ]
      nlinarith
    · rw [abs_sub_comm]
      refine (rpow_neg_sub_le (by linarith) h (by linarith) (by linarith)).trans ?_
      gcongr
      linarith
  have hu' : ‖((z + a) ^ j)⁻¹‖ ≤ 2 ^ j / ‖z‖ ^ j := by
    rw [norm_inv, norm_pow, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 1 * ‖z‖ ^ j = 2 ^ j * (‖z‖ / 2) ^ j := by rw [div_pow]; field_simp
      _ ≤ 2 ^ j * ‖z + a‖ ^ j := by gcongr
  have hdu := inv_pow_sub_le j z (z + a) hZ hA
  rw [hwz] at hdu
  unfold trm
  have e : (z ^ j)⁻¹ * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((z + a) ^ j)⁻¹ * ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)
      = ((z ^ j)⁻¹ - ((z + a) ^ j)⁻¹) * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ)
        + ((z + a) ^ j)⁻¹ * (((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)) := by ring
  rw [e]
  calc _ ≤ ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹‖ * ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ)‖
        + ‖((z + a) ^ j)⁻¹‖ * ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)‖ :=
          norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (j * 4 ^ j * ‖a‖ / ‖z‖ ^ (j + 1)) * 1 + (2 ^ j / ‖z‖ ^ j) * (8 * ‖a‖ / ‖z‖) := by
          gcongr
    _ = (j * 4 ^ j + 8 * 2 ^ j) * ‖a‖ / ‖z‖ ^ (j + 1) := by
          field_simp; ring

end GlobalTheory.EisM.TermDiff
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem polyB_summable_norm_mul_pow {a : ℕ → ℂ} (ha : PolyB a) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ‖a n‖ * r ^ n := by
  obtain ⟨C, A, h⟩ := ha
  have hs : Summable fun n : ℕ => C * 2 ^ A * ((n : ℝ) ^ A * r ^ n + r ^ n) := by
    refine Summable.mul_left _ (Summable.add ?_ ?_)
    · exact summable_pow_mul_geometric_of_norm_lt_one A (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    · exact summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 _)) (fun n => ?_) hs
  have hb : ((n : ℝ) + 1) ^ A ≤ 2 ^ A * ((n : ℝ) ^ A + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_add, one_pow]
      have : (1 : ℝ) ≤ 2 ^ A := one_le_pow₀ (by norm_num)
      nlinarith [pow_nonneg (le_refl (0:ℝ)) A]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : ((n : ℝ) + 1) ^ A ≤ (2 * n) ^ A := pow_le_pow_left₀ (by positivity) (by linarith) A
      rw [mul_pow] at this
      nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) A]
  have hC : 0 ≤ C := le_trans (norm_nonneg _) ((h 0).trans (by simp))
  calc ‖a n‖ * r ^ n ≤ C * ((n : ℝ) + 1) ^ A * r ^ n :=
        mul_le_mul_of_nonneg_right (h n) (pow_nonneg hr0 _)
    _ ≤ C * (2 ^ A * ((n : ℝ) ^ A + 1)) * r ^ n := by gcongr
    _ = C * 2 ^ A * ((n : ℝ) ^ A * r ^ n + r ^ n) := by ring

theorem exists_upperHalfPlane_exp_eq {q : ℂ} (h0 : q ≠ 0) (h1 : ‖q‖ < 1) :
    ∃ τ : ℍ, ∀ n : ℕ, cexp (2 * π * Complex.I * n * τ) = q ^ n := by
  have hπ : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have him : 0 < (Complex.log q / (2 * π * Complex.I)).im := by
    have e : Complex.log q / (2 * π * Complex.I) = -Complex.I * Complex.log q / (2 * π) := by
      field_simp
      ring_nf
      simp [Complex.I_sq]
    rw [e]
    have : (-Complex.I * Complex.log q / (2 * π)).im = - (Complex.log q).re / (2 * π) := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]
      simp
    rw [this, Complex.log_re]
    have hl : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.mpr h0) h1
    have : 0 < 2 * π := by positivity
    apply div_pos (by simpa using hl) this
  refine ⟨⟨_, him⟩, fun n => ?_⟩
  have : 2 * π * Complex.I * (n : ℂ) * ((⟨_, him⟩ : ℍ) : ℂ) = n * Complex.log q := by
    field_simp
  rw [this, Complex.exp_nat_mul, Complex.exp_log h0]

theorem qs_injective : ∀ a b : ℕ → ℂ, PolyB a → PolyB b → qs a = qs b → a = b := by
  intro a b ha hb hab
  set c : ℕ → ℂ := fun n => a n - b n with hcdef
  have hsum : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun n : ℕ => ‖c n‖ * r ^ n := by
    intro r h0 h1
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg h0 _)) (fun n => ?_)
      ((polyB_summable_norm_mul_pow ha h0 h1).add (polyB_summable_norm_mul_pow hb h0 h1))
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg h0 _)
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hrad : ((1 / 2 : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable_norm ?_
    have := hsum (1 / 2) (by norm_num) (by norm_num)
    refine this.congr (fun n => ?_)
    rw [hp, FormalMultilinearSeries.ofScalars_norm]
    simp
  have hpos : 0 < p.radius := lt_of_lt_of_le (by simp) hrad
  have hP := p.hasFPowerSeriesOnBall hpos
  have hval : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → p.sum q = 0 := by
    intro q h0 h1
    obtain ⟨τ, hτ⟩ := exists_upperHalfPlane_exp_eq h0 h1
    have ha' : Summable fun n => a n * q ^ n := Summable.of_norm (by
      simpa [norm_mul, norm_pow] using polyB_summable_norm_mul_pow ha (norm_nonneg q) h1)
    have hb' : Summable fun n => b n * q ^ n := Summable.of_norm (by
      simpa [norm_mul, norm_pow] using polyB_summable_norm_mul_pow hb (norm_nonneg q) h1)
    have e := congrFun hab τ
    simp only [qs, hτ] at e
    show ∑' n, p n (fun _ => q) = 0
    simp only [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, hcdef, sub_mul]
    rw [Summable.tsum_sub ha' hb', e, sub_self]
  have hcont : ContinuousAt p.sum 0 := hP.continuousOn.continuousAt (Metric.eball_mem_nhds 0 hpos)
  have h0 : p.sum 0 = 0 := by
    have hev : p.sum =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)]
        with q hq0 hq1
      exact hval q hq0 (by simpa using hq1)
    exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hev.symm)
  have hloc : p.sum =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact h0
    · exact hval q hq0 (by simpa using hq)
  have hpz : p = 0 := hP.hasFPowerSeriesAt.eq_zero_of_eventually hloc
  funext n
  have hn : p n = 0 := by rw [hpz]; rfl
  have : c n = 0 := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp hn
  exact sub_eq_zero.mp this

end GlobalTheory.EisM
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.FormalId

variable {R : Type} [CommRing R]

theorem uo_mul_vo (l : ℕ) (hl : 0 < l) (a b : ℕ → R) : Uo l (mul a (Vo l b)) = mul (Uo l a) b := by
  funext n
  simp only [Uo, mul, Vo, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun p => (l * p.1, l * p.2)) (fun p => (p.1 / l, p.2 / l))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    exact ⟨by rw [← mul_add, hp], dvd_mul_right _ _⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    have h3 : l ∣ p.1 := by
      have : l ∣ p.1 + p.2 := by rw [h1]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_left h2).mp this
    rw [← Nat.add_div_of_dvd_right h3, h1, Nat.mul_div_cancel_left _ hl]
  · intro p _
    simp [Nat.mul_div_cancel_left _ hl]
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨h1, h2⟩ := hp
    have h3 : l ∣ p.1 := by
      have : l ∣ p.1 + p.2 := by rw [h1]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_left h2).mp this
    ext <;> simp [Nat.mul_div_cancel' h3, Nat.mul_div_cancel' h2]
  · intro p _
    simp [Nat.mul_div_cancel_left _ hl]

theorem mul_comm' (a b : ℕ → R) : mul a b = mul b a := by
  funext n
  simp only [mul]
  conv_lhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  simp [_root_.mul_comm]

theorem mul_add_right' (a b b' : ℕ → R) : mul a (b + b') = mul a b + mul a b' := by
  funext n
  simp [mul, _root_.mul_add, Finset.sum_add_distrib]

theorem mul_add_left' (a a' b : ℕ → R) : mul (a + a') b = mul a b + mul a' b := by
  rw [mul_comm', mul_add_right', mul_comm' b, mul_comm' b]

theorem mul_lin (a b b' : ℕ → R) (c c' : R) :
    mul a (c • b + c' • b') = c • mul a b + c' • mul a b' := by
  funext n
  simp only [mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring

theorem zero_mul' (b : ℕ → R) : mul 0 b = 0 := by
  funext n; simp [mul]

theorem uo_dep (l : ℕ) (a : ℕ → R) : Uo l (dep l a) = 0 := by
  funext n; simp [Uo, dep]

theorem uo_vo (l : ℕ) (hl : 0 < l) (a : ℕ → R) : Uo l (Vo l a) = a := by
  funext n; simp [Uo, Vo, Nat.mul_div_cancel_left _ hl]

theorem dep_add (l : ℕ) (hl : 0 < l) (a : ℕ → R) : a = dep l a + Vo l (Uo l a) := by
  funext n
  by_cases h : l ∣ n
  · simp [dep, Vo, Uo, h, Nat.mul_div_cancel' h]
  · simp [dep, Vo, Uo, h]

theorem uo_add (l : ℕ) (x y : ℕ → R) : Uo l (x + y) = Uo l x + Uo l y := rfl

theorem uo_mul_dep (l : ℕ) (hl : 0 < l) (a b : ℕ → R) :
    Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b) := by
  have e : Uo l (mul a b) = Uo l (mul (dep l a) (dep l b)) + mul (Uo l a) (Uo l b) := by
    conv_lhs => rw [dep_add l hl a, dep_add l hl b]
    rw [mul_add_left', mul_add_right', mul_add_right', uo_add, uo_add, uo_add,
      uo_mul_vo l hl, uo_dep, zero_mul', mul_comm' (Vo l (Uo l a)) (dep l b), uo_mul_vo l hl, uo_dep,
      zero_mul', uo_mul_vo l hl, uo_vo l hl]
    abel
  rw [e]; abel

theorem to_vo (l k q : ℕ) (c : R) (a : ℕ → R) (hq : q.Coprime l) (hq0 : 0 < q) :
    To k c q (Vo l a) = Vo l (To k c q a) := by
  funext n
  simp only [To, Vo]
  by_cases hn : l ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp
    have h1 : l ∣ q * (l * m) := ⟨q * m, by ring⟩
    rw [if_pos h1, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl,
      show q * (l * m) = l * (q * m) by ring, Nat.mul_div_cancel_left _ hl]
    congr 1
    by_cases hqm : q ∣ m
    · obtain ⟨t, rfl⟩ := hqm
      rw [if_pos ⟨l * t, by ring⟩, if_pos (dvd_mul_right _ _),
        show l * (q * t) = q * (l * t) by ring, Nat.mul_div_cancel_left _ hq0, Nat.mul_div_cancel_left _ hq0,
        if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl]
    · rw [if_neg hqm, if_neg]
      intro h
      exact hqm ((Nat.Coprime.dvd_of_dvd_mul_left hq h))
  · have h1 : ¬ l ∣ q * n := fun h => hn (Nat.Coprime.dvd_of_dvd_mul_left hq.symm h)
    rw [if_neg h1, if_neg hn]
    by_cases hqn : q ∣ n
    · rw [if_pos hqn, if_neg]
      · simp
      · intro h
        obtain ⟨t, ht⟩ := hqn
        apply hn
        rw [ht, Nat.mul_div_cancel_left _ hq0] at h
        exact Dvd.dvd.mul_left h q |> fun h' => by rw [ht]; exact h'
    · simp [hqn]

theorem lam_lin (B : ℕ) (c a b : ℕ → R) (x y : R) :
    lam B c (x • a + y • b) = x * lam B c a + y * lam B c b := by
  simp only [lam, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.EisM.FormalId

theorem GlobalTheory.EisM.formal_identities : ∀ (R : Type) [CommRing R] (l : ℕ), 0 < l → (∀ a b : ℕ → R, Uo l (mul a (Vo l b)) = mul (Uo l a) b) ∧ (∀ a b : ℕ → R, Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b)) ∧ (∀ a b : ℕ → R, mul a b = mul b a) ∧ (∀ (a b b' : ℕ → R) (c c' : R), mul a (c • b + c' • b') = c • mul a b + c' • mul a b') ∧ (∀ (k q : ℕ) (c : R) (a : ℕ → R), q.Coprime l → 0 < q → To k c q (Vo l a) = Vo l (To k c q a)) ∧ (∀ (B : ℕ) (c a b : ℕ → R) (x y : R), lam B c (x • a + y • b) = x * lam B c a + y * lam B c b) := by
  intro R _ l hl
  exact ⟨FormalId.uo_mul_vo l hl, FormalId.uo_mul_dep l hl, FormalId.mul_comm', FormalId.mul_lin,
    fun k q c a hq hq0 => FormalId.to_vo l k q c a hq hq0, FormalId.lam_lin⟩
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem zs_eq_mul_dep_eis : ∀ (k l j : ℕ) (u v A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zs k l u v (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c A u)) (dep l (eis (j + 1) c' (fun y => A' y * v y) fun _ => 1)) := by
  intro k l j u v A A' c c' hjk
  funext n
  unfold Zs mul
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : l ∣ p.1 ∨ l ∣ p.2
  · have hz : dep l (eis (k - 1 - j) c A u) p.1 * dep l (eis (j + 1) c' (fun y => A' y * v y) fun _ => 1) p.2 = 0 := by
      rcases h with h | h <;> simp [dep, h]
    rw [hz]
    simp [h]
  · push_neg at h
    obtain ⟨h1, h2⟩ := h
    have p1 : p.1 ≠ 0 := fun e => h1 (e ▸ dvd_zero l)
    have p2 : p.2 ≠ 0 := fun e => h2 (e ▸ dvd_zero l)
    simp only [dep, eis, h1, h2, p1, p2, if_false, or_self]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
    have hx0 : (x.1 : ℂ) ≠ 0 := by
      have := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have : x.1 ≠ 0 := fun e => p1 (by rw [← this, e, zero_mul])
      exact_mod_cast this
    have hk : k - 2 = (k - 1 - j - 1) + j := by omega
    have hj : j + 1 - 1 = j := by omega
    rw [hk, hj, pow_add, div_pow]
    field_simp

end GlobalTheory
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module (integralClosure (O0 p) Ω) M] (μ ν : M), (Polynomial.aeval (zS T n) (Polynomial.derivative (Polynomial.cyclotomic (p ^ n) (O0 p)))) • μ = 0 → ((p : (integralClosure (O0 p) Ω)) ^ n * qS T n ^ (p ^ n - 1)) • ν = 0 → ∃ D : (integralClosure (O0 p) Ω) → M, IsDerOn (levelAlg T n) D ∧ D (zS T n) = μ ∧ D (qS T n) = ν := by
  first | exact @GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg | exact GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg | (intros; apply GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_meromorphic_root_of_mem_modularFunctionTower_Un : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧ X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m := by
  first | exact @GlobalTheory.KZ.MeroRoot.exists_mero_root | exact GlobalTheory.KZ.MeroRoot.exists_mero_root | (intros; apply GlobalTheory.KZ.MeroRoot.exists_mero_root <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

theorem _root_.GlobalTheory.T.integral_of_expansionSum_eq_primePow_mul_isEval : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p), (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp p (e t)) → ∀ (v : ℕ) (o : Ω), IsInt (p := p) o → ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * o → ∃ (c : ℤ → Ω) (x' : Ω), Ev ψ c o x' := by
  first | exact @GlobalTheory.GeoFix.Divide.divide_ev | exact GlobalTheory.GeoFix.Divide.divide_ev | (intros; apply GlobalTheory.GeoFix.Divide.divide_ev <;> assumption)
end
