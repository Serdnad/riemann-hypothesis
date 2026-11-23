module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

namespace GlobalTheory.CartanInt

theorem cosh_const_numerical_bound (p q : ℕ) :
    (18 / 5 * max 1 (3 / 2 * ((p + q : ℕ) : ℝ) ^ 2) / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2) * (9 / 2) ^ (p ^ 2 + q ^ 2) / Real.pi ^ (p * q) * (2 ^ (2 * (p + q) * min p q) * (2 * Real.pi / (2 / ((((p + q : ℕ) : ℝ) + 1) / 2)) ^ 2) ^ (p * q)) ≤ Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2)) := by
  rcases Nat.eq_zero_or_pos (p + q) with h0 | hpos
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp hq
    simp
  have hsq : (p + q) ^ 2 = (p ^ 2 + q ^ 2) + 2 * (p * q) := by ring
  have hmin : 2 * (p + q) * min p q ≤ 4 * (p * q) := by
    rcases le_total p q with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have hR : Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2))
      = (((p + q : ℕ) : ℝ) + 2) ^ (3 * (p + q) ^ 2) := by
    have : (3 * ((p + q : ℕ) : ℝ) ^ 2) = ((3 * (p + q) ^ 2 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [hR, hsq]
  have ha : (1 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hpos
  generalize ((p + q : ℕ) : ℝ) = a at ha
  generalize p ^ 2 + q ^ 2 = d
  generalize 2 * (p + q) * min p q = m at hmin
  generalize p * q = n at hmin
  have ha0 : 0 < a := by linarith
  have hpi := Real.pi_pos
  have hmax : max 1 (3 / 2 * a ^ 2) = 3 / 2 * a ^ 2 := max_eq_right (by nlinarith)
  have h1 : 18 / 5 * (3 / 2 * a ^ 2) / a = 27 / 5 * a := by field_simp; ring
  have h2 : 2 * Real.pi / (2 / ((a + 1) / 2)) ^ 2 = Real.pi * ((a + 1) ^ 2 / 8) := by
    field_simp; ring
  rw [hmax, h1, h2]
  have h3 : (2 : ℝ) ^ m ≤ 16 ^ n := by
    calc (2 : ℝ) ^ m ≤ 2 ^ (4 * n) := pow_le_pow_right₀ (by norm_num) hmin
      _ = 16 ^ n := by rw [pow_mul]; norm_num
  have h4 : 27 / 5 * a * (9 / 2) ≤ (a + 2) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (a - 1)) (show (0 : ℝ) ≤ a + 8 by linarith)]
  have h5 : 8 * a * (a + 1) ≤ (a + 2) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (a - 1)) ha0.le]
  have h6 : (27 / 5 * a) ^ 2 * 16 * ((a + 1) ^ 2 / 8) ≤ (a + 2) ^ 6 := by
    have h7 : (8 * a * (a + 1)) ^ 2 ≤ ((a + 2) ^ 3) ^ 2 := by gcongr
    have h8 : 0 ≤ (a * (a + 1)) ^ 2 := by positivity
    nlinarith
  calc (27 / 5 * a) ^ (d + 2 * n) * (9 / 2) ^ d / Real.pi ^ n *
        (2 ^ m * (Real.pi * ((a + 1) ^ 2 / 8)) ^ n)
      ≤ (27 / 5 * a) ^ (d + 2 * n) * (9 / 2) ^ d / Real.pi ^ n *
        (16 ^ n * (Real.pi * ((a + 1) ^ 2 / 8)) ^ n) := by gcongr
    _ = (27 / 5 * a * (9 / 2)) ^ d * ((27 / 5 * a) ^ 2 * 16 * ((a + 1) ^ 2 / 8)) ^ n := by
        rw [pow_add, pow_mul, mul_pow Real.pi, mul_pow (27 / 5 * a) (9 / 2),
          mul_pow _ ((a + 1) ^ 2 / 8), mul_pow _ (16 : ℝ)]
        field_simp
    _ ≤ ((a + 2) ^ 3) ^ d * ((a + 2) ^ 6) ^ n := by gcongr
    _ = (a + 2) ^ (3 * (d + 2 * n)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring

end GlobalTheory.CartanInt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

namespace GlobalTheory.CartanInt

theorem invariant_measure_lower_bound_of_chart :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Fintype ι] (mK : Measure G) [IsProbabilityMeasure mK] (K U : Set G) (θ : (ι → ℝ) → G) (T δ : ℝ), Continuous θ → IsClosed U → mK Kᶜ = 0 → (∀ R, Measure.map (fun x => θ R * x) mK = mK) → 0 < δ → 0 ≤ T → (∀ x ∈ K, ∃ R₀ : ι → ℝ, (∀ i, |R₀ i| ≤ T) ∧ ∀ R : ι → ℝ, (∀ i, |R i - R₀ i| ≤ δ) → (θ R)⁻¹ * x ∈ U) → ENNReal.ofReal ((δ / (T + δ)) ^ Fintype.card ι) ≤ mK U := by
  intro G ι _ _ _ _ _ _ _ mK _ K U θ T δ hθ hU hK hinv hδ hT hch
  have hTδ : 0 < T + δ := by linarith
  set Q : Set (ι → ℝ) := Metric.closedBall 0 (T + δ) with hQ
  set S : Set ((ι → ℝ) × G) := {p | (θ p.1)⁻¹ * p.2 ∈ U} with hS
  have hSc : IsClosed S := hU.preimage (by fun_prop : Continuous fun p : (ι → ℝ) × G => (θ p.1)⁻¹ * p.2)
  have hSm : MeasurableSet S := hSc.measurableSet
  have hQv : volume Q = ENNReal.ofReal ((2 * (T + δ)) ^ Fintype.card ι) :=
    Real.volume_pi_closedBall _ hTδ.le
  have hsec : ∀ R, mK (Prod.mk R ⁻¹' S) = mK U := by
    intro R
    have hm : MeasurableSet (Prod.mk R ⁻¹' S) := measurable_prodMk_left hSm
    conv_lhs => rw [← hinv R]
    rw [Measure.map_apply (by fun_prop) hm]
    congr 1
    ext x
    simp [hS]
  have h1 : ((volume.restrict Q).prod mK) S = mK U * volume Q := by
    rw [Measure.prod_apply hSm]
    simp [hsec]
  have h2 : ENNReal.ofReal ((2 * δ) ^ Fintype.card ι) ≤ ((volume.restrict Q).prod mK) S := by
    rw [Measure.prod_apply_symm hSm]
    have hae : ∀ᵐ x ∂mK, x ∈ K := hK
    calc ENNReal.ofReal ((2 * δ) ^ Fintype.card ι)
        = ∫⁻ _x, ENNReal.ofReal ((2 * δ) ^ Fintype.card ι) ∂mK := by simp
      _ ≤ _ := by
        refine lintegral_mono_ae (hae.mono fun x hx => ?_)
        obtain ⟨R₀, hR₀, hR⟩ := hch x hx
        have hm : MeasurableSet ((fun R => (R, x)) ⁻¹' S) := measurable_prodMk_right hSm
        rw [Measure.restrict_apply hm, ← Real.volume_pi_closedBall R₀ hδ.le]
        refine measure_mono fun R hRm => ?_
        have hd : ∀ i, |R i - R₀ i| ≤ δ := fun i => by
          have := (dist_pi_le_iff hδ.le).1 (Metric.mem_closedBall.1 hRm) i
          rwa [Real.dist_eq] at this
        refine ⟨hR R hd, ?_⟩
        rw [hQ, Metric.mem_closedBall, dist_pi_le_iff hTδ.le]
        intro i
        have h3 := abs_le.1 (hd i)
        have h4 := abs_le.1 (hR₀ i)
        rw [Real.dist_eq, Pi.zero_apply, sub_zero, abs_le]
        constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
  rw [h1, hQv] at h2
  have hpos : 0 < (2 * (T + δ)) ^ Fintype.card ι := by positivity
  have he : (δ / (T + δ)) ^ Fintype.card ι
      = (2 * δ) ^ Fintype.card ι / (2 * (T + δ)) ^ Fintype.card ι := by
    rw [← div_pow, mul_div_mul_left _ _ (two_ne_zero)]
  rw [he, ENNReal.ofReal_div_of_pos hpos]
  exact ENNReal.div_le_of_le_mul h2

end GlobalTheory.CartanInt
end
