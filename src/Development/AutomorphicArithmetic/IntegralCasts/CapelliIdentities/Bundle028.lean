module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Geometry.Manifold.StructureGroupoid
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

theorem UpperTheory.Reformulated.B.DYga2.main.{u_1} :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [inst_3 : MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] {A : ℕ},
      Module.finrank ℝ E < A →
        (0 : ℕ) < Module.finrank ℝ E →
          ∃ (c : ℝ),
            (0 : ℝ) ≤ c ∧
              ∀ (η : ℝ),
                (0 : ℝ) < η →
                  ∀ (F : Finset E),
                    (∀ y ∈ F, ∀ y' ∈ F, y ≠ y' → η ≤ ‖y - y'‖ ^ Module.finrank ℝ E) →
                      ∑ y ∈ F, (((1 : ℝ) + ‖y‖) ^ A)⁻¹ ≤ c * ((1 : ℝ) + η⁻¹) := by
  intro E _ _ _ _ _ μ _ A hA hd
  set d := Module.finrank ℝ E with hd_def

  set w : E → ℝ := fun x => ((1 + ‖x‖) ^ A)⁻¹ with hw
  have hwpos : ∀ x, 0 < w x := fun x => by
    have : (0:ℝ) < 1 + ‖x‖ := by positivity
    simp only [hw]; positivity
  have hint : MeasureTheory.Integrable w μ := by
    have h := integrable_one_add_norm (E := E) (μ := μ) (r := (A:ℝ)) (by exact_mod_cast hA)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    have : (0:ℝ) < 1 + ‖x‖ := by positivity
    simp only [hw]
    rw [Real.rpow_neg this.le, Real.rpow_natCast]
  set I : ℝ := ∫ x, w x ∂μ with hI
  have hI0 : 0 ≤ I := MeasureTheory.integral_nonneg fun x => (hwpos x).le
  set V : ℝ := μ.real (Metric.ball (0:E) 1) with hV
  have hVpos : 0 < V := by
    refine ENNReal.toReal_pos ?_ ?_
    · exact (Metric.measure_ball_pos μ 0 one_pos).ne'
    · exact MeasureTheory.measure_ball_lt_top.ne
  refine ⟨2 ^ A * I / V * 2 ^ d, by positivity, ?_⟩
  intro η hη F hF
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set r : ℝ := η ^ ((d:ℝ)⁻¹) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos hη _
  have hrd : r ^ d = η := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hη.le, inv_mul_cancel₀ hdR, Real.rpow_one]
  set s : ℝ := min (r / 2) 1 with hs
  have hspos : 0 < s := lt_min (by positivity) one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hs2 : 2 * s ≤ r := by
    have : s ≤ r / 2 := min_le_left _ _
    linarith

  have hkey : 1 ≤ s ^ d * (2 ^ d * (1 + η⁻¹)) := by
    have hη' : 0 < η⁻¹ := inv_pos.mpr hη
    rcases le_total (r / 2) 1 with h | h
    · have : s = r / 2 := min_eq_left h
      rw [this, div_pow, hrd]
      have h2 : (2:ℝ) ^ d ≠ 0 := by positivity
      have : η / 2 ^ d * (2 ^ d * (1 + η⁻¹)) = η + 1 := by
        field_simp
      rw [this]; linarith
    · have : s = 1 := min_eq_right h
      rw [this, one_pow, one_mul]
      have : (1:ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      nlinarith

  have hball : ∀ y : E, μ.real (Metric.ball y s) = s ^ d * V := by
    intro y
    have := MeasureTheory.Measure.addHaar_ball_of_pos μ y hspos
    simp only [MeasureTheory.Measure.real, hV]
    rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

  have hcomp : ∀ y x : E, x ∈ Metric.ball y s → (2 ^ A)⁻¹ * w y ≤ w x := by
    intro y x hx
    have hxy : ‖x‖ ≤ ‖y‖ + s := by
      have h1 : ‖x - y‖ < s := by simpa [dist_eq_norm] using hx
      have h2 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
        have := norm_add_le y (x - y)
        simpa using this
      linarith
    have hle : 1 + ‖x‖ ≤ 2 * (1 + ‖y‖) := by
      have := norm_nonneg y
      linarith
    have hx0 : (0:ℝ) < 1 + ‖x‖ := by positivity
    have hy0 : (0:ℝ) < 1 + ‖y‖ := by positivity
    have hp : (1 + ‖x‖) ^ A ≤ 2 ^ A * (1 + ‖y‖) ^ A := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hx0.le hle A
    simp only [hw]
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) hp

  have hone : ∀ y : E, (2 ^ A)⁻¹ * w y * (s ^ d * V) ≤ ∫ x in Metric.ball y s, w x ∂μ := by
    intro y
    have := MeasureTheory.setIntegral_ge_of_const_le_real (μ := μ) (f := w) (c := (2 ^ A)⁻¹ * w y)
      (s := Metric.ball y s) Metric.isOpen_ball.measurableSet MeasureTheory.measure_ball_lt_top.ne
      (fun x hx => hcomp y x hx) hint.integrableOn
    rw [hball] at this
    exact this

  have hdisj : Set.Pairwise (F : Set E) (Function.onFun Disjoint fun y => Metric.ball y s) := by
    intro y hy y' hy' hne
    refine Metric.ball_disjoint_ball ?_
    have h1 := hF y hy y' hy' hne
    have h2 : r ≤ ‖y - y'‖ := by
      rw [← hrd] at h1
      exact le_of_pow_le_pow_left₀ hd.ne' (norm_nonneg _) h1
    rw [dist_eq_norm]
    linarith
  have hsum : ∑ y ∈ F, ∫ x in Metric.ball y s, w x ∂μ ≤ I := by
    rw [← MeasureTheory.integral_biUnion_finset F (fun y _ => Metric.isOpen_ball.measurableSet) hdisj
      (fun y _ => hint.integrableOn)]
    exact MeasureTheory.setIntegral_le_integral hint
      (Filter.Eventually.of_forall fun x => (hwpos x).le)
  have htot : (2 ^ A)⁻¹ * (s ^ d * V) * ∑ y ∈ F, w y ≤ I := by
    refine le_trans ?_ hsum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    calc _ = (2 ^ A)⁻¹ * w y * (s ^ d * V) := by ring
      _ ≤ _ := hone y
  have hS0 : 0 ≤ ∑ y ∈ F, w y := Finset.sum_nonneg fun y _ => (hwpos y).le
  have hsd : 0 < s ^ d := by positivity
  have hfin : ∑ y ∈ F, w y ≤ 2 ^ A * I / V * (1 / s ^ d) := by
    have h2 : (0:ℝ) < 2 ^ A := by positivity
    rw [show 2 ^ A * I / V * (1 / s ^ d) = (2 ^ A * I) / (s ^ d * V) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left htot h2.le
    calc _ = 2 ^ A * ((2 ^ A)⁻¹ * (s ^ d * V) * ∑ y ∈ F, w y) := by field_simp
      _ ≤ _ := this
  have hinv : 1 / s ^ d ≤ 2 ^ d * (1 + η⁻¹) := by
    rw [div_le_iff₀ hsd]
    linarith [hkey, mul_comm (s ^ d) (2 ^ d * (1 + η⁻¹))]
  calc ∑ y ∈ F, ((1 + ‖y‖) ^ A)⁻¹ = ∑ y ∈ F, w y := rfl
    _ ≤ 2 ^ A * I / V * (1 / s ^ d) := hfin
    _ ≤ 2 ^ A * I / V * (2 ^ d * (1 + η⁻¹)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 ^ A * I / V * 2 ^ d * (1 + η⁻¹) := by ring
end

section

private lemma int_of_isIntegral_cast (q : ℚ) (h : IsIntegral ℤ (q : ℂ)) : ∃ n : ℤ, (n : ℚ) = q := by
  have h1 : IsIntegral ℤ (algebraMap ℚ ℂ q) := by simpa using h
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff ).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨n, by simpa using hn⟩

private lemma int_of_sq_mul (d : ℕ) (hd : d.Prime) (q : ℚ) (m : ℤ)
    (h : q ^ 2 * (d : ℚ) = m) : ∃ n : ℤ, (n : ℚ) = q := by
  have hq : q * (q.den : ℚ) = q.num := Rat.mul_den_eq_num q
  have h1 : q.num ^ 2 * (d : ℤ) = m * (q.den : ℤ) ^ 2 := by
    have : ((q.num : ℚ)) ^ 2 * (d : ℚ) = (m : ℚ) * (q.den : ℚ) ^ 2 := by
      rw [← hq, ← h]; ring
    exact_mod_cast this
  have hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    simpa [Int.gcd] using q.reduced
  have h2 : (q.den : ℤ) ^ 2 ∣ (d : ℤ) :=
    hc.dvd_of_dvd_mul_left ⟨m, by rw [h1]; ring⟩
  have h3 : q.den * q.den ∣ d := by
    have : q.den ^ 2 ∣ d := by exact_mod_cast h2
    rwa [sq] at this
  have h4 : q.den = 1 := Nat.isUnit_iff.1 (hd.prime.squarefree _ h3)
  refine ⟨q.num, ?_⟩
  rw [← hq, h4]; simp

private lemma even_sub_of_norm (d : ℕ) (hd : d.Prime) (x y n : ℤ)
    (h : x ^ 2 + y ^ 2 * (d : ℤ) = 4 * n) : Even (x - y) := by
  obtain ⟨s, hs | hs⟩ := Int.even_or_odd' x <;> obtain ⟨t, ht | ht⟩ := Int.even_or_odd' y
  · exact ⟨s - t, by omega⟩
  · exfalso
    have h1 : (d : ℤ) = 4 * (n - s ^ 2 - (t ^ 2 + t) * d) := by
      rw [hs, ht] at h; linear_combination h
    have h2 : 2 * 2 ∣ d := by
      have : ((4 : ℕ) : ℤ) ∣ (d : ℤ) := ⟨_, by exact_mod_cast h1⟩
      exact_mod_cast this
    have h3 := Nat.isUnit_iff.1 (hd.prime.squarefree _ h2)
    omega
  · exfalso
    have h1 : (1 : ℤ) = 4 * (n - s ^ 2 - s - t ^ 2 * d) := by
      rw [hs, ht] at h; linear_combination h
    omega
  · exact ⟨s - t, by omega⟩

theorem UpperTheory.integral_quadratic_half_int :
    ∀ (d : ℕ), d.Prime → ∀ (a b : ℚ), IsIntegral ℤ ((a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) → ∃ x y : ℤ, Even (x - y) ∧ (a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) = ((x : ℂ) + (y : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) / 2 := by
  intro d hd a b h
  have hr : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    have : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
    exact_mod_cast this
  generalize Real.sqrt (d : ℝ) = r at h hr ⊢
  have h' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
    have h0 := map_isIntegral_int (starRingEnd ℂ) h
    have e : (starRingEnd ℂ) ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        = (a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ)) := by
      simp only [map_add (f := _), map_mul, map_ratCast, Complex.conj_I, Complex.conj_ofReal]
      ring
    rwa [e] at h0
  obtain ⟨x, hx⟩ := int_of_isIntegral_cast (2 * a) (by
    have e : ((2 * a : ℚ) : ℂ) = ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        + ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
      push_cast; ring
    rw [e]; exact h.add h')
  obtain ⟨n, hn⟩ := int_of_isIntegral_cast (a ^ 2 + b ^ 2 * d) (by
    have e : ((a ^ 2 + b ^ 2 * d : ℚ) : ℂ) = ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        * ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
      push_cast
      linear_combination (b : ℂ) ^ 2 * (r : ℂ) ^ 2 * Complex.I_sq - (b : ℂ) ^ 2 * hr
    rw [e]; exact h.mul h')
  obtain ⟨y, hy⟩ := int_of_sq_mul d hd (2 * b) (4 * n - x ^ 2) (by
    push_cast
    rw [hn, hx]; ring)
  refine ⟨x, y, even_sub_of_norm d hd x y n ?_, ?_⟩
  · have : (x : ℚ) ^ 2 + (y : ℚ) ^ 2 * (d : ℚ) = 4 * n := by
      rw [hx, hy, hn]; ring
    exact_mod_cast this
  · have hx' : (x : ℂ) = 2 * (a : ℂ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hx
    have hy' : (y : ℂ) = 2 * (b : ℂ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hy
    rw [hx', hy']; ring
end

section

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.CmOK :
    ℕ → ℤ → ℤ → ℕ → Prop :=
    fun (a : ℕ) (b c : ℤ) (d : ℕ) ↦
      (4 : ℤ) * (↑a : ℤ) * c = b ^ (2 : ℕ) + (↑d : ℤ) ∧ Odd a ∧ d % (8 : ℕ) = (7 : ℕ) ∧ Nat.Prime d

noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta :
    ℤ → ℕ → ℂ :=
    fun (b : ℤ) (d : ℕ) ↦ ((↑b : ℂ) + Complex.I * (↑√(↑d : ℝ) : ℂ)) / (2 : ℂ)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.KF :
    ℤ → ℕ → IntermediateField ℚ ℂ :=
    fun (b : ℤ) (d : ℕ) ↦ ℚ⟮UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d⟯

private theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq (b : ℤ) (d : ℕ) :
    UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d =
      (b : ℂ) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d - ((b : ℂ) ^ 2 + (d : ℂ)) / 4 := by
  have h : ((√(d : ℝ) : ℝ) : ℂ) * ((√(d : ℝ) : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  unfold UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta
  linear_combination (((√(d : ℝ) : ℝ) : ℂ) * ((√(d : ℝ) : ℝ) : ℂ) / 4) * Complex.I_mul_I - (1 / 4 : ℂ) * h

private theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_integral (b : ℤ) (d : ℕ) :
    IsIntegral ℚ (UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (b : ℚ) * Polynomial.X
    + Polynomial.C (((b : ℚ) ^ 2 + (d : ℚ)) / 4), ?_, ?_⟩
  · monicity!
  · have h := UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq b d
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, eq_ratCast]
    push_cast
    linear_combination h

theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.kap_repr :
    ∀ {a : ℕ} {b c : ℤ} {d : ℕ},
      UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.CmOK a b c d →
        ∀ {x : ℂ}, x ∈ UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.KF b d → ∃ (u : ℚ) (v : ℚ), x = (↑u : ℂ) + (↑v : ℂ) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d := by
  intro a b c d _ x hx
  have hx' : x ∈ Algebra.adjoin ℚ {UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_integral b d).isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by simp [hy]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    refine ⟨u * u' - v * v' * (((b : ℚ) ^ 2 + (d : ℚ)) / 4), u * v' + v * u' + v * v' * b, ?_⟩
    push_cast
    linear_combination ((v : ℂ) * (v' : ℂ)) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq b d
end

section

open Filter Asymptotics NumberField

private theorem UpperTheory.Reformulated.B.Qp7.partial_sums_isBigO (K : Type*) [Field K] [NumberField K] :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
        (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  have hlim := (Ideal.tendsto_norm_le_div_atTop K).comp tendsto_natCast_atTop_atTop
  have hO : (fun n : ℕ ↦ (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} : ℝ))
      =O[atTop] fun n : ℕ ↦ (n : ℝ) := by
    refine isBigO_of_div_tendsto_nhds ?_ _ hlim
    filter_upwards [eventually_ne_atTop 0] with n hn h
    exact absurd (Nat.cast_eq_zero.mp h) hn
  simp only [Real.rpow_one]
  refine IsBigO.trans (isBigO_of_le _ fun n ↦ ?_) hO
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc ∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)
      ≤ ∑ k ∈ Finset.Icc 0 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left zero_le_one)
          fun _ _ _ ↦ by positivity
    _ = _ := by
        rw [← Nat.cast_sum, ← Finset.card_preimage_eq_sum_card_image_eq
          (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
        simp [Set.coe_eq_subtype]

private theorem UpperTheory.Reformulated.B.Qp7.summable_count_mul (K : Type*) [Field K] [NumberField K] {σ : ℝ}
    (hσ : 1 < σ) :
    Summable fun n : ℕ ↦
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ σ)⁻¹ := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := (σ : ℂ))
    (UpperTheory.Reformulated.B.Qp7.partial_sums_isBigO K) (fun _ ↦ Nat.cast_nonneg _) zero_le_one
    (by simpa using hσ)
  refine h.norm.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    simp [Real.zero_rpow (zero_lt_one.trans hσ).ne']
  · simp [div_eq_mul_inv]

theorem UpperTheory.Reformulated.B.Qp7.summable_absNorm_rpow_inv.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] {σ : ℝ},
    (1 : ℝ) < σ →
      Summable fun (I : Ideal (NumberField.RingOfIntegers K)) ↦
        ((↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) I) : ℝ) ^ σ)⁻¹ := by
  intro K _ _ σ hσ
  have hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    fun n ↦ (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ Ideal.absNorm I)).summable_iff,
    summable_sigma_of_nonneg (fun _ ↦ by simp only [Function.comp_apply]; positivity)]
  refine ⟨fun n ↦ Summable.of_finite, ?_⟩
  refine (UpperTheory.Reformulated.B.Qp7.summable_count_mul K hσ).congr fun n ↦ ?_
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((Ideal.absNorm I.1 : ℝ) ^ σ)⁻¹ = ((n : ℝ) ^ σ)⁻¹ := fun I ↦ by rw [I.2]
  simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, this, tsum_const, nsmul_eq_mul]
end

section

noncomputable def UpperTheory.Reformulated.B.Qk29.dot.{v} :
    {ι : Type v} → (ι →₀ ℕ) → (ι → ℝ) → ℝ :=
    fun {ι : Type v} (n : ι →₀ ℕ) (r : ι → ℝ) ↦ n.sum fun (i : ι) (k : ℕ) ↦ (↑k : ℝ) * r i

noncomputable def UpperTheory.Reformulated.B.Qk29.MonoWtGe.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → ℝ → (ι → ℝ) → ℝ → (ι →₀ ℕ) → K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (n : ι →₀ ℕ) (c : K) ↦
      ‖c‖ ≤ pi ^ (w - UpperTheory.Reformulated.B.Qk29.dot n r)

noncomputable def UpperTheory.Reformulated.B.Qk29.WtGe.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → ℝ → (ι → ℝ) → ℝ → MvPowerSeries ι K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (f : MvPowerSeries ι K) ↦
      ∀ (n : ι →₀ ℕ), UpperTheory.Reformulated.B.Qk29.MonoWtGe pi r w n ((MvPowerSeries.coeff n : MvPowerSeries ι K → K) f)

private theorem UpperTheory.Reformulated.B.Qk29.dot_add {ι : Type*} (a b : ι →₀ ℕ) (r : ι → ℝ) :
    UpperTheory.Reformulated.B.Qk29.dot (a + b) r = UpperTheory.Reformulated.B.Qk29.dot a r + UpperTheory.Reformulated.B.Qk29.dot b r := by
  unfold UpperTheory.Reformulated.B.Qk29.dot
  apply Finsupp.sum_add_index'
  · intro i; simp
  · intro i m n; push_cast; ring

private theorem UpperTheory.Reformulated.B.Qk29.wtGe_one {K : Type*} [NormedField K] {ι : Type*} {pi : ℝ}
    (hpi : 0 < pi) (r : ι → ℝ) : UpperTheory.Reformulated.B.Qk29.WtGe pi r 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h
    simp [UpperTheory.Reformulated.B.Qk29.dot]
  · rw [norm_zero]
    exact (Real.rpow_pos_of_pos hpi _).le

private theorem UpperTheory.Reformulated.B.Qk29.wtGe_mul {K : Type*} [NormedField K] {ι : Type*}
    [IsUltrametricDist K] {pi : ℝ} (hpi : 0 < pi) {r : ι → ℝ} {a b : ℝ}
    {f g : MvPowerSeries ι K} (hf : UpperTheory.Reformulated.B.Qk29.WtGe pi r a f)
    (hg : UpperTheory.Reformulated.B.Qk29.WtGe pi r b g) : UpperTheory.Reformulated.B.Qk29.WtGe pi r (a + b) (f * g) := by
  classical
  intro n
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe
  rw [MvPowerSeries.coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_pos_of_pos hpi _).le
  intro p hp
  have hn : p.1 + p.2 = n := by simpa using hp
  have h1 := hf p.1
  have h2 := hg p.2
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe at h1 h2
  have he : a + b - UpperTheory.Reformulated.B.Qk29.dot n r =
      (a - UpperTheory.Reformulated.B.Qk29.dot p.1 r) + (b - UpperTheory.Reformulated.B.Qk29.dot p.2 r) := by
    rw [← hn, UpperTheory.Reformulated.B.Qk29.dot_add]; ring
  rw [he, Real.rpow_add hpi, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_pos_of_pos hpi _).le

theorem UpperTheory.Reformulated.B.Qk29.wtGe_prod.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} [IsUltrametricDist K] {pi : ℝ},
      (0 : ℝ) < pi →
        ∀ {r : ι → ℝ} {α : Type w} (s : Finset α) (wt : α → ℝ) (F : α → MvPowerSeries ι K),
          (∀ i ∈ s, UpperTheory.Reformulated.B.Qk29.WtGe pi r (wt i) (F i)) → UpperTheory.Reformulated.B.Qk29.WtGe pi r (∑ i ∈ s, wt i) (∏ i ∈ s, F i) := by
  intro K inst ι _ pi hpi r α s wt F h
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UpperTheory.Reformulated.B.Qk29.wtGe_one hpi r
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact UpperTheory.Reformulated.B.Qk29.wtGe_mul hpi (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end
