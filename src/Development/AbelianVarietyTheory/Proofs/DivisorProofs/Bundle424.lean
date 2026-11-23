module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle365
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay

noncomputable section
namespace GlobalTheory.HeckeTwo.TermDecay

theorem norm_qZ_mul_exp (σ : ℂ) (ν : ℝ) (a : ℤ) (b m : ℕ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    ‖qZ σ a b m y t * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))‖ =
      (t ^ 2 + y ^ 2) ^ (-((a : ℝ) / 2 + b + σ.re)) * |y| ^ m := by
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  unfold qZ
  rw [norm_mul, norm_mul, norm_mul, norm_zpow, hnu, Complex.norm_cpow_eq_rpow_re_of_pos hQ,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hre : (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one, Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hQ.le,
    ← Real.rpow_add hQ]
  congr 2
  simp
  ring

theorem integral_rpow_sq_add_sq (e : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ∫ t : ℝ, (t ^ 2 + y ^ 2) ^ (-e) = |y| ^ (1 - 2 * e) * ∫ s : ℝ, (1 + s ^ 2) ^ (-e) := by
  have hc : 0 < |y| := abs_pos.2 hy
  have hpt : ∀ t : ℝ, (t ^ 2 + y ^ 2) ^ (-e) = |y| ^ (-2 * e) * (1 + (t / |y|) ^ 2) ^ (-e) := by
    intro t
    have h1 : t ^ 2 + y ^ 2 = |y| ^ 2 * (1 + (t / |y|) ^ 2) := by
      field_simp
      rw [sq_abs]
      ring
    rw [h1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.Measure.integral_comp_div (fun s : ℝ => (1 + s ^ 2) ^ (-e)) |y|, abs_abs, smul_eq_mul,
    ← mul_assoc, show 1 - 2 * e = -2 * e + 1 by ring, Real.rpow_add_one hc.ne']

theorem norm_intZ_le : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, y ≠ 0 →
      ‖intZ σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) := by
  intro K hK hKH a b m hab
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun σ hσ => by simp at hσ⟩
  obtain ⟨σ₀, hσ₀K, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  have hσ₀ : -1 / 2 < σ₀.re := hKH hσ₀K
  have hab' : (2 : ℝ) ≤ a + 2 * b := by exact_mod_cast hab
  set e₀ : ℝ := (a : ℝ) / 2 + b + σ₀.re with he₀
  have he₀1 : 1 / 2 < e₀ := by rw [he₀]; linarith
  have hg₀ : MeasureTheory.Integrable (fun s : ℝ => (1 + s ^ 2) ^ (-e₀)) := by
    have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := MeasureTheory.volume) (r := 2 * e₀) (by simp; linarith)
    refine this.congr (MeasureTheory.ae_of_all _ fun s => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  refine ⟨∫ s : ℝ, (1 + s ^ 2) ^ (-e₀), ?_⟩
  intro σ hσ ν y hy
  set e : ℝ := (a : ℝ) / 2 + b + σ.re with he
  have hee : e₀ ≤ e := by
    have := hmin hσ
    simp only [Set.mem_setOf_eq] at this
    rw [he, he₀]; linarith
  have hc : 0 < |y| := abs_pos.2 hy
  have hmono : (∫ s : ℝ, (1 + s ^ 2) ^ (-e)) ≤ ∫ s : ℝ, (1 + s ^ 2) ^ (-e₀) :=
    MeasureTheory.integral_mono_of_nonneg (MeasureTheory.ae_of_all _ fun s => by positivity) hg₀
      (MeasureTheory.ae_of_all _ fun s =>
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg s]) (by linarith))
  calc ‖intZ σ ν a b m y‖
      ≤ ∫ t : ℝ, ‖qZ σ a b m y t * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m := by
        simp_rw [norm_qZ_mul_exp σ ν a b m hy]
        rw [he]
    _ = (|y| ^ (1 - 2 * e) * ∫ s : ℝ, (1 + s ^ 2) ^ (-e)) * |y| ^ m := by
        rw [MeasureTheory.integral_mul_const, integral_rpow_sq_add_sq e hy]
    _ ≤ (|y| ^ (1 - 2 * e) * ∫ s : ℝ, (1 + s ^ 2) ^ (-e₀)) * |y| ^ m := by
        gcongr
    _ = (∫ s : ℝ, (1 + s ^ 2) ^ (-e₀)) * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) := by
        rw [← Real.rpow_natCast, mul_comm (|y| ^ (1 - 2 * e)), mul_assoc, ← Real.rpow_add hc, he]
        congr 2
        ring

end GlobalTheory.HeckeTwo.TermDecay
end
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay

noncomputable section
namespace GlobalTheory.HeckeTwo.TermDecay

theorem continuous_qZ (σ : ℂ) (a : ℤ) (b m : ℕ) {y : ℝ} (hy : y ≠ 0) : Continuous (qZ σ a b m y) := by
  unfold qZ
  have h1 : Continuous fun t : ℝ => ((t : ℂ) + (y : ℂ) * I) ^ (-a) :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + (y : ℂ) * I).zpow₀ (-a)
      fun t => Or.inl (GlobalTheory.HeckeTwo.TermSmooth.u_ne hy t)
  have h2 : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) :=
    (by fun_prop : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))).cpow continuous_const
      fun t => Complex.ofReal_mem_slitPlane.2 (by positivity)
  exact (h1.mul h2).mul continuous_const

theorem norm_qZ (σ : ℂ) (a : ℤ) (b m : ℕ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    ‖qZ σ a b m y t‖ = (t ^ 2 + y ^ 2) ^ (-((a : ℝ) / 2 + b + σ.re)) * |y| ^ m := by
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  unfold qZ
  rw [norm_mul, norm_mul, norm_zpow, hnu, Complex.norm_cpow_eq_rpow_re_of_pos hQ,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_eq_rpow, ← Real.rpow_intCast,
    ← Real.rpow_mul hQ.le, ← Real.rpow_add hQ]
  congr 2
  simp
  ring

theorem integrable_qZ : ∀ σ ∈ halfPlane, ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∀ y : ℝ, y ≠ 0 →
    MeasureTheory.Integrable (qZ σ a b m y) := by
  intro σ hσ a b m hab y hy
  have hσ' : -1 / 2 < σ.re := hσ
  set e : ℝ := (a : ℝ) / 2 + b + σ.re with he
  have hab' : (2 : ℝ) ≤ a + 2 * b := by exact_mod_cast hab
  have he1 : 1 / 2 < e := by rw [he]; linarith
  set κ := min 1 (y ^ 2) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  refine (((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (r := 2 * e) (by simp; linarith)).const_mul
    (κ ^ (-e) * |y| ^ m))).mono' (continuous_qZ σ a b m hy).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t => ?_)
  rw [norm_qZ σ a b m hy t]
  have hQk : κ * (1 + ‖t‖ ^ 2) ≤ t ^ 2 + y ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    have h1 : κ ≤ 1 := min_le_left _ _
    have h2 : κ ≤ y ^ 2 := min_le_right _ _
    nlinarith [sq_nonneg t]
  have hA : (t ^ 2 + y ^ 2) ^ (-e) ≤ κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2) := by
    rw [show -(2 * e) / 2 = -e by ring, ← Real.mul_rpow hκ0.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hQk (by linarith)
  calc (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m ≤ (κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2)) * |y| ^ m :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

end GlobalTheory.HeckeTwo.TermDecay
end
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.cutoff_quot_wint_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ : ℝ) (θ : ℝ → ℝ), Continuous θ → (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) → wint n (fun y : U => z y) (fun x : U => (θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x) (fun x : U => GlobalTheory.OTY.TwEst.wt A E β z x) ≤ ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hm hpsi δ θ hθ hθ1
  have hma : Measurable (fun y : Y => (θ (δ * psi A L s y) : ℂ) * GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y) :=
    (Complex.measurable_ofReal.comp (hθ.measurable.comp (hpsi.const_mul δ))).mul hm
  have key := htr _ (fun _ => 1) hma measurable_const (fun _ _ => zero_le_one)
  simp only [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe, one_mul, mul_one] at key
  unfold wint
  rw [← key]
  refine le_trans (setLIntegral_mono' hU.measurableSet ?_) (setLIntegral_le_lintegral U _)
  intro y hy
  apply ENNReal.ofReal_le_ofReal
  have e : GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y = GlobalTheory.OTY.TwEst.quot A h β y :=
    GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
  rw [e]
  unfold WeightedAtlas.nsq
  rw [hq y hy, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hθ1 _).1]
  obtain ⟨h0, h1⟩ := hθ1 (δ * psi A L s y)
  have h2 : θ (δ * psi A L s y) ^ 2 ≤ 1 := by nlinarith
  set t := θ (δ * psi A L s y)
  set b := ‖β (A.pick y) y‖
  set q := ‖GlobalTheory.OTY.TwEst.quot A h β y‖
  generalize hc : Real.exp _ = c
  have hc0 : 0 ≤ c := hc ▸ (Real.exp_pos _).le
  have h3 : 0 ≤ (b * q) ^ 2 * c := by positivity
  calc b ^ 2 * c * (t * q) ^ 2 = t ^ 2 * ((b * q) ^ 2 * c) := by ring
    _ ≤ 1 * ((b * q) ^ 2 * c) := mul_le_mul_of_nonneg_right h2 h3
    _ = _ := one_mul _
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.lhs_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ (δ T : ℝ) (θ : ℝ → ℝ) (F0 : U → ℂ), Continuous θ → Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - β i x * GlobalTheory.OTY.TwEst.ext0 U F0 x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖(θ (δ * psi A L s x) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β x - F0 x‖ ^ 2 * (wT T (δ * psi A L s x) * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x)))) ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hqm hpsi δ T θ F0 hθ hF0
  have hm : Measurable fun y => δ * psi A L s y := hpsi.const_mul δ
  have hwc : Continuous (wT T) := by
    unfold wT
    refine continuous_const.div₀ (by fun_prop) fun x => ?_
    have : 0 ≤ min (x ^ 2) ((T + 1) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    linarith
  have hw0 : ∀ x, 0 ≤ wT T x := by
    intro x
    unfold wT
    have : 0 ≤ min (x ^ 2) ((T + 1) ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
    positivity
  have key := htr (fun y => (θ (δ * psi A L s y) : ℂ) *
      GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y - GlobalTheory.OTY.TwEst.ext0 U F0 y)
    (fun y => wT T (δ * psi A L s y) * Real.exp (-psi A L s y))
    (((Complex.measurable_ofReal.comp (hθ.measurable.comp hm)).mul hqm).sub hF0)
    ((hwc.measurable.comp hm).mul (Real.measurable_exp.comp hpsi.neg))
    (fun y _ => mul_nonneg (hw0 _) (Real.exp_pos _).le)
  refine Eq.trans ?_ (key.trans ?_)
  · refine setLIntegral_congr_fun hU.measurableSet fun y hy => ?_
    have h1 : GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) y
        = GlobalTheory.OTY.TwEst.quot A h β y :=
      GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
    have h2 : (θ (δ * psi A L s y) : ℂ) * h (A.pick y) y
        - β (A.pick y) y * GlobalTheory.OTY.TwEst.ext0 U F0 y
        = β (A.pick y) y * ((θ (δ * psi A L s y) : ℂ) * GlobalTheory.OTY.TwEst.quot A h β y
          - GlobalTheory.OTY.TwEst.ext0 U F0 y) := by
      rw [hq y hy]; ring
    simp only [h1]
    congr 1
    unfold WeightedAtlas.nsq
    simp only [h2, norm_mul, mul_pow]
    ring
  · refine lintegral_congr fun x => ?_
    simp only [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
    congr 2
    rw [neg_add, Real.exp_add]
    ring
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.rhs_le_manifold : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ δ T : ℝ, ∫⁻ x in {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1}, ENNReal.ofReal (‖GlobalTheory.OTY.TwEst.quot A h β x‖ ^ 2 * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x))) ∂vol n (fun y : U => z y) ≤ ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A E L s U z β h hU htr hq hm hpsi δ T
  set S : Set Y := {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1} with hS
  have hδ : Measurable fun y => δ * psi A L s y := hpsi.const_mul δ
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const hδ).inter (measurableSet_le hδ measurable_const)
  have hw : Measurable (S.indicator fun y => Real.exp (-psi A L s y)) :=
    (Real.measurable_exp.comp hpsi.neg).indicator hSm
  have key := htr _ _ hm hw (fun y _ => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y)
  have hS' : MeasurableSet {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} :=
    measurable_subtype_coe hSm
  rw [← lintegral_indicator hS']
  refine le_trans (le_of_eq ?_) (le_trans key.ge ?_)
  · refine lintegral_congr fun x => ?_
    rw [GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe]
    by_cases hx : (x : Y) ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} from hx), ← Real.exp_add]
      congr 3
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1} from hx)]
      simp
  · rw [← lintegral_indicator hSm, ← lintegral_indicator hU.measurableSet]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ U
    · rw [Set.indicator_of_mem hy]
      by_cases hx : y ∈ S
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        have h0 := GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y) ⟨y, hy⟩
        simp only at h0
        rw [h0]
        apply le_of_eq
        congr 2
        unfold WeightedAtlas.nsq
        rw [hq y hy, norm_mul]
        ring
      · rw [Set.indicator_of_notMem hx]
        simp
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.TwEst.quot_holo_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), ∀ (la : La) (U Ω : Set Y) (β h : ι → Y → ℂ), IsOpen U → IsOpen Ω →
    A.IsFrameOn la U β → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) →
    (∀ i, DifferentiableOn ℂ (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) ∧
    Measurable (_root_.GlobalTheory.OTY.TwEst.ext0 U (fun y : U => _root_.GlobalTheory.OTY.TwEst.quot A h β y)) ∧
    ∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * _root_.GlobalTheory.OTY.TwEst.quot A h β y := by
  intro n Y _ _ _ _ _ ι La _ A la U Ω β h hU hΩ hβ hh h0
  classical
  obtain ⟨⟨hβhol, hβcoc⟩, hβne⟩ := hβ
  obtain ⟨hhhol, hhcoc⟩ := hh
  have hq : ∀ y, _root_.GlobalTheory.OTY.TwEst.quot A h β y = h (A.pick y) y / β (A.pick y) y := fun y => by
    unfold _root_.GlobalTheory.OTY.TwEst.quot; rfl
  have hβi : ∀ i, ∀ y ∈ (A.chart i).source, y ∈ U → β i y ≠ 0 := by
    intro i y hy hyU hzero
    apply hβne y hyU
    rw [hβcoc (A.pick y) i y hyU (A.mem_pick y) hy, hzero, mul_zero]
  have hqe : ∀ i, ∀ y ∈ (A.chart i).source, y ∈ U →
      _root_.GlobalTheory.OTY.TwEst.quot A h β y = h i y / β i y := by
    intro i y hy hyU
    rw [hq]
    by_cases hyΩ : y ∈ Ω
    · rw [hhcoc (A.pick y) i y hyΩ (A.mem_pick y) hy, hβcoc (A.pick y) i y hyU (A.mem_pick y) hy,
        mul_div_mul_left _ _ (A.g_ne la _ _ y (A.mem_pick y) hy)]
    · rw [h0 _ _ hyΩ, h0 _ _ hyΩ, zero_div, zero_div]
  have hdiff : ∀ i, DifferentiableOn ℂ (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω)) := by
    intro i
    set S := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) with hS
    have h1 : DifferentiableOn ℂ (h i ∘ (A.chart i).symm) S :=
      (hhhol i).mono fun v hv => ⟨hv.1, hv.2.2⟩
    have h2 : DifferentiableOn ℂ (β i ∘ (A.chart i).symm) S :=
      (hβhol i).mono fun v hv => ⟨hv.1, hv.2.1⟩
    have h3 : ∀ v ∈ S, (β i ∘ (A.chart i).symm) v ≠ 0 := fun v hv =>
      hβi i _ ((A.chart i).map_target hv.1) hv.2.1
    have hd : DifferentiableOn ℂ
        (fun v => (h i ∘ (A.chart i).symm) v * ((β i ∘ (A.chart i).symm) v)⁻¹) S :=
      h1.mul (h2.inv h3)
    refine hd.congr fun v hv => ?_
    simp only [Function.comp_apply, ← div_eq_mul_inv]
    exact hqe i _ ((A.chart i).map_target hv.1) hv.2.1
  refine ⟨hdiff, ?_, fun y hy => ?_⟩
  · have hopen : IsOpen (U ∩ Ω) := hU.inter hΩ
    have hcont : ContinuousOn (_root_.GlobalTheory.OTY.TwEst.quot A h β) (U ∩ Ω) := by
      intro y hy
      set i := A.pick y
      have hys : y ∈ (A.chart i).source := A.mem_pick y
      have hset : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω)) :=
        (A.chart i).isOpen_inter_preimage_symm hopen
      have hmem : A.chart i y ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) :=
        ⟨(A.chart i).map_source hys, by
          simp only [Set.mem_preimage, (A.chart i).left_inv hys]; exact hy⟩
      have hca : ContinuousAt (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) (A.chart i y) :=
        ((hdiff i).continuousOn).continuousAt (hset.mem_nhds hmem)
      have hcomp : ContinuousAt ((_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) ∘ A.chart i) y :=
        hca.comp ((A.chart i).continuousAt hys)
      refine (hcomp.congr ?_).continuousWithinAt
      filter_upwards [(A.chart i).open_source.mem_nhds hys] with w hw
      simp [(A.chart i).left_inv hw]
    have heq : _root_.GlobalTheory.OTY.TwEst.ext0 U (fun y : U => _root_.GlobalTheory.OTY.TwEst.quot A h β y) =
        (U ∩ Ω).piecewise (_root_.GlobalTheory.OTY.TwEst.quot A h β) 0 := by
      funext y
      unfold _root_.GlobalTheory.OTY.TwEst.ext0
      by_cases hyU : y ∈ U
      · by_cases hyΩ : y ∈ Ω
        · simp [hyU, hyΩ, Set.piecewise]
        · simp [hyU, hyΩ, Set.piecewise, hq, h0 _ _ hyΩ]
      · simp [hyU, Set.piecewise]
    rw [heq]
    exact hcont.measurable_piecewise continuousOn_const hopen.measurableSet
  · rw [hq, mul_div_cancel₀ _ (hβne y hy)]
end

section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem lintegral_hB_one_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  have hg : ∀ w : Low 2 → ℂ, gB 1 w = 1 := by
    intro w
    simp [gB, colGram, lminor]
  have hset : {w : Low 2 → ℂ | ∀ p : Low 2, (p.1.2 : ℕ) < 1 → 1 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
      = Metric.closedBall (0 : Low 2 → ℂ) 1 := by
    ext w
    simp only [Set.mem_setOf_eq, mem_closedBall_zero_iff]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    constructor
    · intro h p
      have hp := p.2
      have h1 : (p.1.2 : ℕ) < p.1.1 := hp
      have h2 : (p.1.1 : ℕ) < 2 := p.1.1.isLt
      exact h p (by omega) (by omega)
    · intro h p _ _
      exact h p
  have hfun : hB 1 = Set.indicator (Metric.closedBall (0 : Low 2 → ℂ) 1) (fun _ => (1 : ℝ≥0∞)) := by
    funext w
    simp only [hB, hset, hg, ENNReal.ofReal_one]
  rw [hfun, lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul]
  exact measure_closedBall_lt_top

end GlobalTheory.IntBall
end

section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem measurable_hB : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by
  intro r p0
  have hlow : Continuous (fun w : Low r → ℂ => lowMat w) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [lowMat]
    split_ifs <;> first | exact continuous_apply _ | exact continuous_const
  have hblk : Continuous (fun w : Low r → ℂ => blkW p0 w) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hent : ∀ a b : Fin r, Continuous (fun w : Low r → ℂ => lowMat w a b) := fun a b =>
      (continuous_apply b).comp ((continuous_apply a).comp hlow)
    by_cases h : p0 = 1
    · simp only [blkW, h, if_true]
      exact hent _ _
    · simp only [blkW, h, if_false]
      exact hent _ _
  have hcg : ∀ k, Continuous (fun w : Low r → ℂ => colGram (blkW p0 w) k) := by
    intro k
    simp only [colGram, lminor]
    exact (((hblk.matrix_conjTranspose.matrix_mul hblk).matrix_submatrix _ _).matrix_det).norm
  have hg : Measurable (fun w : Low r → ℂ => gB p0 w) := by
    have hz : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by
      rw [zpow_neg]; norm_cast
    simp only [gB, hz]
    refine Finset.measurable_prod _ fun k _ => ?_
    exact ((hcg k.castSucc).measurable.pow_const 2).inv
  have hS : IsClosed {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply p).norm continuous_const
  unfold hB
  exact (ENNReal.measurable_ofReal.comp hg).indicator hS.measurableSet

end GlobalTheory.IntBall
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.sections_invertibleLocus_of_basisFunctor : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : ∀ S, (T ⟶ S) → F.obj S, Desc.IsSec F (fun S u ↦ IsUnit (mp F u e)) x ∧ ∀ t (u : T ⟶ G.obj t), IsUnit (mp F u e) → x (G.obj t) u = s t u := by
  first | exact @GlobalTheory.CatCoh.Desc.sec_of_basis_unit | exact GlobalTheory.CatCoh.Desc.sec_of_basis_unit | (intros; apply GlobalTheory.CatCoh.Desc.sec_of_basis_unit <;> assumption)
end
