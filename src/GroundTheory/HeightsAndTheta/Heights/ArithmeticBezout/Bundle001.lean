module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def SectionComponents.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (J : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F),
    (∀ P ∈ J.minimalPrimes, ∀ Q ∈ J.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ Q)) →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    ∀ P ∈ J.minimalPrimes, ∀ W : Ideal (MvPolynomial (Fin n) F),
      W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ↔ W ∈ (J ⊔ Ideal.span {f}).minimalPrimes ∧ P ≤ W

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def MinimalPrimeComap.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] (σ : K →+* L) (ι : Type) (I : Ideal (MvPolynomial ι K)),
    I.IsPrime → ∀ P ∈ (I.map (MvPolynomial.map σ)).minimalPrimes,
      P.comap (MvPolynomial.map σ) = I

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

def polyTangent {n : ℕ} (S : Set (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    Submodule ℂ (Fin n → ℂ) where
  carrier := {v | ∀ q ∈ S, ∑ j, eval p (pderiv j q) * v j = 0}
  add_mem' {v w} hv hw q hq := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hv hw ⊢
    rw [hv q hq, hw q hq, add_zero]
  zero_mem' q _ := by simp
  smul_mem' c v hv q hq := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum] at hv ⊢
    rw [hv q hq, mul_zero]

def PolyLocalGenerators.Statement : Prop :=
  ∀ (n m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = m →
    ∀ p : Fin n → ℂ, (∀ q ∈ J, eval p q = 0) →
      finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p) = m →
      ∃ (q : Fin (n - m) → MvPolynomial (Fin n) ℂ) (g : MvPolynomial (Fin n) ℂ),
        (∀ i, q i ∈ J) ∧ eval p g ≠ 0 ∧ finrank ℂ (polyTangent (Set.range q) p) = m ∧
        ∀ r ∈ J, g * r ∈ Ideal.span (Set.range q)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def KernelProjMeasurable.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (n k : ℕ)
    (L : X → Matrix (Fin k) (Fin n) ℂ), Continuous L →
      Measurable fun x => (LinearMap.ker (Matrix.toEuclideanLin (L x))).starProjection

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set
open scoped Pointwise

noncomputable section

namespace SphereMean

theorem setAverage_smul_measure {α : Type*} [MeasurableSpace α] (μ : Measure α) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (s : Set α) (g : α → ℝ) :
    ⨍ x in s, g x ∂(c • μ) = ⨍ x in s, g x ∂μ := by
  have hc : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  rw [setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_measure, measureReal_def,
    measureReal_def]
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [mul_inv]
  field_simp

section Linear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem setAverage_comp_linearEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F)
    [ν.IsAddHaarMeasure] (L : E ≃L[ℝ] F) (s : Set F) (g : F → ℝ) :
    ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂ν := by
  have hmap : (map L μ).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hmp : MeasurePreserving L μ (map L μ) := ⟨L.continuous.measurable, rfl⟩
  have he : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have h1 : ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂(map L μ) := by
    rw [setAverage_eq, setAverage_eq, hmp.setIntegral_preimage_emb he, measureReal_def,
      measureReal_def, he.map_apply]
  have h2 : map L μ = addHaarScalarFactor (map L μ) ν • ν := isAddLeftInvariant_eq_smul _ _
  have hpos := addHaarScalarFactor_pos_of_isAddHaarMeasure (map L μ) ν
  rw [h1, h2]
  rw [show (addHaarScalarFactor (map L μ) ν • ν) =
      ((addHaarScalarFactor (map L μ) ν : ENNReal) • ν) from rfl]
  exact setAverage_smul_measure ν (by simpa using hpos.ne') ENNReal.coe_ne_top s g

end Linear

def sqNorm {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ j, ‖x j‖ ^ 2

def ballSet (n : ℕ) (s : ℝ) : Set (Fin n → ℂ) := {x | sqNorm x < s}

theorem sqNorm_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_sqNorm (n : ℕ) : Continuous (sqNorm (n := n)) := by
  unfold sqNorm
  fun_prop

theorem measurable_sqNorm (n : ℕ) : Measurable (sqNorm (n := n)) :=
  (continuous_sqNorm n).measurable

theorem isOpen_ballSet (n : ℕ) (s : ℝ) : IsOpen (ballSet n s) :=
  isOpen_lt (continuous_sqNorm n) continuous_const

theorem measurableSet_ballSet (n : ℕ) (s : ℝ) : MeasurableSet (ballSet n s) :=
  (isOpen_ballSet n s).measurableSet

theorem sqNorm_smul {n : ℕ} (c : ℝ) (x : Fin n → ℂ) : sqNorm (c • x) = c ^ 2 * sqNorm x := by
  simp only [sqNorm, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]

theorem ballSet_eq_smul {n : ℕ} {s : ℝ} (hs : 0 < s) : ballSet n s = √s • ballSet n 1 := by
  have h : 0 < √s := Real.sqrt_pos.mpr hs
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ h.ne']
  simp only [ballSet, mem_ofPred_eq, sqNorm_smul, inv_pow, Real.sq_sqrt hs.le]
  rw [inv_mul_lt_iff₀ hs, mul_one]

theorem finrank_fun_complex (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem volume_ballSet {n : ℕ} {s : ℝ} (hs : 0 < s) :
    volume (ballSet n s) = ENNReal.ofReal (s ^ n) * volume (ballSet n 1) := by
  rw [ballSet_eq_smul hs, addHaar_smul, finrank_fun_complex, pow_mul, Real.sq_sqrt hs.le,
    abs_of_nonneg (pow_nonneg hs.le n)]

theorem ballSet_subset_closedBall (n : ℕ) : ballSet n 1 ⊆ Metric.closedBall 0 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  have h1 : ‖x j‖ ^ 2 ≤ sqNorm x :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ‖x j‖ ^ 2 < 1 := lt_of_le_of_lt h1 hx
  nlinarith [norm_nonneg (x j)]

theorem volume_ballSet_one_ne_top (n : ℕ) : volume (ballSet n 1) ≠ ⊤ :=
  (measure_mono (ballSet_subset_closedBall n)).trans_lt measure_closedBall_lt_top |>.ne

theorem volume_ballSet_one_pos (n : ℕ) : 0 < volume (ballSet n 1) :=
  (isOpen_ballSet n 1).measure_pos volume ⟨0, by simp [ballSet, sqNorm]⟩

end SphereMean

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set Real

noncomputable section

namespace SphereMean

def polyP (m : ℕ) (s : ℝ) : ℝ := ∑ j ∈ Finset.range (m + 1), (1 - s) ^ j / (m + 1)

def polyR (m : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (1 - (1 - s) ^ (j + 1)) / ((j + 1) * (m + 1))

def primG (m : ℕ) (s : ℝ) : ℝ := (1 - (1 - s) ^ (m + 1)) / (m + 1) * log s - polyR m s

theorem mul_polyP (m : ℕ) (s : ℝ) : s * polyP m s = (1 - (1 - s) ^ (m + 1)) / (m + 1) := by
  have h := geom_sum_mul (1 - s) (m + 1)
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold polyP
  rw [← Finset.sum_div, eq_div_iff hm, mul_div_assoc', div_mul_cancel₀ _ hm]
  linear_combination (-1 : ℝ) * h

theorem hasDerivAt_one_sub_pow (k : ℕ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - s) ^ k) (-((k : ℝ) * (1 - s) ^ (k - 1))) s := by
  have := (hasDerivAt_pow k (1 - s)).comp s ((hasDerivAt_id s).const_sub 1)
  simpa [Function.comp_def] using this

theorem hasDerivAt_polyR (m : ℕ) (s : ℝ) : HasDerivAt (polyR m) (polyP m s) s := by
  unfold polyR polyP
  apply HasDerivAt.fun_sum
  intro j _
  have h2 := ((hasDerivAt_one_sub_pow (j + 1) s).const_sub 1).div_const (((j : ℝ) + 1) * (m + 1))
  refine h2.congr_deriv ?_
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.add_sub_cancel, neg_neg]
  push_cast
  field_simp

theorem primG_eq (m : ℕ) (s : ℝ) : primG m s = polyP m s * (s * log s) - polyR m s := by
  rw [primG, ← mul_polyP]
  ring

theorem continuous_polyP (m : ℕ) : Continuous (polyP m) := by
  unfold polyP
  fun_prop

theorem continuous_polyR (m : ℕ) : Continuous (polyR m) := by
  unfold polyR
  fun_prop

theorem continuous_primG (m : ℕ) : Continuous (primG m) := by
  have : primG m = fun s => polyP m s * (s * log s) - polyR m s := funext (primG_eq m)
  rw [this]
  exact ((continuous_polyP m).mul continuous_mul_log).sub (continuous_polyR m)

theorem hasDerivAt_primG (m : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (primG m) ((1 - s) ^ m * log s) s := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => (1 - (1 - s) ^ (m + 1)) / (m + 1)) ((1 - s) ^ m) s := by
    have := ((hasDerivAt_one_sub_pow (m + 1) s).const_sub 1).div_const ((m : ℝ) + 1)
    refine this.congr_deriv ?_
    rw [Nat.add_sub_cancel, neg_neg]
    push_cast
    field_simp
  have h2 := (h1.mul (hasDerivAt_log hs.ne')).sub (hasDerivAt_polyR m s)
  have h3 : HasDerivAt (primG m)
      ((1 - s) ^ m * log s + (1 - (1 - s) ^ (m + 1)) / (↑m + 1) * s⁻¹ - polyP m s) s := h2
  refine h3.congr_deriv ?_
  have := mul_polyP m s
  have hP : polyP m s = (1 - (1 - s) ^ (m + 1)) / (m + 1) * s⁻¹ := by
    rw [← this]; field_simp
  rw [hP]
  ring

theorem primG_zero (m : ℕ) : primG m 0 = 0 := by
  simp [primG, polyR]

theorem primG_one (m : ℕ) : primG m 1 = -(harmonic (m + 1) : ℝ) / (m + 1) := by
  simp only [primG, polyR, sub_self, log_one, mul_zero, zero_sub, ne_eq, add_eq_zero,
    one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero]
  rw [harmonic]
  push_cast
  rw [neg_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  field_simp

theorem integral_disc_weight (m : ℕ) :
    ∫ y in (0 : ℝ)..1, y * (1 - y ^ 2) ^ m = 1 / (2 * ((m : ℝ) + 1)) := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hd : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => -(1 - y ^ 2) ^ (m + 1) / (2 * (m + 1)))
      (y * (1 - y ^ 2) ^ m) y := by
    intro y _
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
    have := (HasDerivAt.comp (h := fun x : ℝ => x ^ 2) y (hasDerivAt_one_sub_pow (m + 1) (y ^ 2))
      hp).neg.div_const (2 * ((m : ℝ) + 1))
    have h3 : HasDerivAt (fun y : ℝ => -(1 - y ^ 2) ^ (m + 1) / (2 * (m + 1)))
        (-(-((((m + 1 : ℕ) : ℝ)) * (1 - y ^ 2) ^ (m + 1 - 1)) * (2 * y)) / (2 * ((m : ℝ) + 1))) y :=
      this
    refine h3.congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := fun y => y * (1 - y ^ 2) ^ m) hd
    (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  field_simp
  simp

theorem integral_disc_log_weight (m : ℕ) :
    ∫ y in (0 : ℝ)..1, y * log y * (1 - y ^ 2) ^ m = -(harmonic (m + 1) : ℝ) / (4 * (m + 1)) := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hc : ContinuousOn (fun y : ℝ => primG m (y ^ 2) / 4) (Icc 0 1) :=
    ((continuous_primG m).comp (continuous_pow 2)).div_const 4 |>.continuousOn
  have hd : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y : ℝ => primG m (y ^ 2) / 4)
      (y * log y * (1 - y ^ 2) ^ m) y := by
    intro y hy
    have hy2 : 0 < y ^ 2 := pow_pos hy.1 2
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
    have := (HasDerivAt.comp (h := fun x : ℝ => x ^ 2) y (hasDerivAt_primG m hy2) hp).div_const 4
    have h3 : HasDerivAt (fun y : ℝ => primG m (y ^ 2) / 4)
        ((1 - y ^ 2) ^ m * log (y ^ 2) * (2 * y) / 4) y := this
    refine h3.congr_deriv ?_
    rw [log_pow]
    push_cast
    ring
  have hi : IntervalIntegrable (fun y : ℝ => y * log y * (1 - y ^ 2) ^ m) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_mul_log.mul (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hd hi]
  simp only [one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, primG_one,
    primG_zero, zero_div, sub_zero]
  field_simp

end SphereMean

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def AreaMultiplicityWeight.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (A : Set E) (f : E → E)
    (f' : E → E →L[ℝ] E), MeasurableSet A → (∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) →
      AEMeasurable (fun y => (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞)) μ ∧
        ∀ g : E → ℝ≥0∞, Measurable g →
          ∫⁻ x in A, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ =
            ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) * g y ∂μ

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem isHomogeneous_of_mem_minimalPrimes {I P : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hP : P ∈ I.minimalPrimes) :
    P.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  have hcore : (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal.IsPrime :=
    hP.1.1.homogeneousCore
  have hle : I ≤ (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hP.1.2)
  have hcoreP := Ideal.toIdeal_homogeneousCore_le (homogeneousSubmodule (Fin n) ℂ) P
  rw [Ideal.IsHomogeneous.iff_eq]
  exact le_antisymm hcoreP (hP.2 ⟨hcore, hle⟩ hcoreP)

end GroundTheory.Heights₂.Heights
end
