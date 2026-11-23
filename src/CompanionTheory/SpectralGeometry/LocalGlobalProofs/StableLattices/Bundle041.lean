module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Bundle001
public import Formalism.PeriodIntegrals.Bundle018
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowFormPermutationSplit.Bundle001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.UniformSpace.Matrix
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul

@[expose] public section

section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.OdeRoots

theorem energy_pointwise (z x y : ℂ) (s e : ℝ) (hz : z.re < s) (he : 0 ≤ e) :
    2 * (inner ℝ x (z * x + y)) * e + ‖x‖ ^ 2 * (e * (-2 * s)) ≤
      -(s - z.re) * (‖x‖ ^ 2 * e) + (1 / (s - z.re)) * (‖y‖ ^ 2 * e) := by
  have ha : 0 < s - z.re := sub_pos.2 hz
  have h1 : inner ℝ x (z * x + y) = z.re * ‖x‖ ^ 2 + inner ℝ x y := by
    rw [inner_add_right]
    congr 1
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have h2 : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  rw [h1]
  set a := s - z.re with hadef
  set p := ‖x‖
  set q := ‖y‖
  have hs : s = a + z.re := by rw [hadef]; ring
  have h3 : 0 ≤ (a * p - q) ^ 2 / a := by positivity
  have h4 : (a * p - q) ^ 2 / a = a * p ^ 2 - 2 * (p * q) + (1 / a) * q ^ 2 := by
    field_simp
    ring
  have h5 : 2 * (z.re * p ^ 2 + inner ℝ x y) + p ^ 2 * (-2 * s) ≤
      -a * p ^ 2 + (1 / a) * q ^ 2 := by
    rw [hs]
    nlinarith
  have := mul_le_mul_of_nonneg_right h5 he
  nlinarith

theorem odeA : CompanionTheory.RgExh.Dec.N.OdeA := by
  intro z s hz f g hf hg hgi
  have ha : 0 < s - z.re := sub_pos.2 hz
  set a := s - z.re with hadef

  let ft : ℝ → ℂ := fun t => f (max t 0)
  have hfon : ContinuousOn f (Ici 0) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hft : Continuous ft :=
    hfon.comp_continuous (continuous_id.max continuous_const) (fun t => mem_Ici.2 (le_max_right _ _))
  have hfe : ∀ t, 0 ≤ t → ft t = f t := fun t ht => by simp [ft, max_eq_left ht]
  let E : ℝ → ℝ := fun t => Real.exp (-2 * s * t)
  have hE : Continuous E := by fun_prop
  have hEpos : ∀ t, 0 ≤ E t := fun t => (Real.exp_pos _).le
  let U : ℝ → ℝ := fun t => ‖ft t‖ ^ 2 * E t
  let V : ℝ → ℝ := fun t => ‖g t‖ ^ 2 * E t
  have hU : Continuous U := by fun_prop
  have hV : Continuous V := by fun_prop
  have hUn : ∀ t, 0 ≤ U t := fun t => mul_nonneg (by positivity) (hEpos t)
  have hVn : ∀ t, 0 ≤ V t := fun t => mul_nonneg (by positivity) (hEpos t)
  let D : ℝ → ℝ := fun t =>
    2 * (inner ℝ (ft t) (z * ft t + g t)) * E t + ‖ft t‖ ^ 2 * (E t * (-2 * s))
  have hD : Continuous D := by
    have : Continuous fun t => inner ℝ (ft t) (z * ft t + g t) :=
      Continuous.inner hft (by fun_prop)
    fun_prop
  have hDle : ∀ t, D t ≤ -a * U t + (1 / a) * V t := fun t =>
    energy_pointwise z (ft t) (g t) s (E t) hz (hEpos t)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt (fun x => ‖f x‖ ^ 2 * E x) (D t) t := by
    intro t ht
    have h1 := (hf t ht).norm_sq
    have h2 : HasDerivAt E (E t * (-2 * s)) t := by
      have := ((hasDerivAt_id t).const_mul (-2 * s)).exp
      simpa [E] using this
    have e : D t = 2 * (inner ℝ (f t) (z * f t + g t)) * E t + ‖f t‖ ^ 2 * (E t * (-2 * s)) := by
      simp only [D, hfe t ht]
    rw [e]
    exact h1.mul h2

  have hVlin : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (V t)) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hgi
    refine lintegral_congr fun t => ?_
    simp only [V, E]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
  have hVint : IntegrableOn V (Ioi 0) :=
    ⟨hV.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hVn)).2 hVlin⟩
  set C : ℝ := ∫ t in Ioi (0 : ℝ), V t with hC
  have hVle : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, V t ≤ C := by
    intro T hT
    rw [intervalIntegral.integral_of_le hT]
    exact setIntegral_mono_set hVint (ae_of_all _ hVn) (ae_of_all _ Ioc_subset_Ioi_self)
  have hbound : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, U t ≤ (U 0 + (1 / a) * C) / a := by
    intro T hT
    have hI : ∫ t in (0 : ℝ)..T, D t = ‖f T‖ ^ 2 * E T - ‖f 0‖ ^ 2 * E 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => ‖f x‖ ^ 2 * E x) (fun t ht => ?_)
        (hD.intervalIntegrable _ _)
      rw [uIcc_of_le hT] at ht
      exact hderiv t ht.1
    have hmono : ∫ t in (0 : ℝ)..T, D t ≤ ∫ t in (0 : ℝ)..T, (-a * U t + (1 / a) * V t) :=
      intervalIntegral.integral_mono_on hT (hD.intervalIntegrable _ _)
        (((continuous_const.mul hU).add (continuous_const.mul hV)).intervalIntegrable _ _)
        (fun t _ => hDle t)
    have hsplit : ∫ t in (0 : ℝ)..T, (-a * U t + (1 / a) * V t) =
        -a * (∫ t in (0 : ℝ)..T, U t) + (1 / a) * ∫ t in (0 : ℝ)..T, V t := by
      have c1 : IntervalIntegrable (fun t => -a * U t) volume 0 T :=
        (continuous_const.mul hU).intervalIntegrable _ _
      have c2 : IntervalIntegrable (fun t => (1 / a) * V t) volume 0 T :=
        (continuous_const.mul hV).intervalIntegrable _ _
      rw [intervalIntegral.integral_add c1 c2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hT0 : 0 ≤ ‖f T‖ ^ 2 * E T := mul_nonneg (by positivity) (hEpos T)
    have hU0 : U 0 = ‖f 0‖ ^ 2 * E 0 := by simp only [U, hfe 0 le_rfl]
    have hVa : (1 / a) * ∫ t in (0 : ℝ)..T, V t ≤ (1 / a) * C :=
      mul_le_mul_of_nonneg_left (hVle T hT) (by positivity)
    rw [le_div_iff₀ ha]
    rw [hI, hsplit] at hmono
    nlinarith
  have hUint : IntegrableOn U (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      ((U 0 + (1 / a) * C) / a) 0 (l := atTop) (b := fun T : ℝ => T)
      (fun T => (hU.integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self) tendsto_id ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hUn _)] using hbound T hT
  have hfin := hUint.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  simp only [U, E, hfe t ht0]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm_eq_enorm]

end GlobalTheory.CompanionTheory.OdeRoots
end
end

section

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.GradFlag

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

def pM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A - A)

def qM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A + A)

theorem J_mul (h : IsGrad ε A) : Formalism.REAL.Jm ε * A = -(A * Formalism.REAL.Jm ε) := by
  obtain ⟨hg, hH, -, -⟩ := h
  have h0 : Aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * A = 0 := hg
  rw [hH] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem A4 (h : A * A * A = A) : A * A * A * A = A * A := by rw [h]

theorem pM_idem (h : A * A * A = A) : pM A * pM A = pM A := by
  have h4 := A4 h
  unfold pM
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub, ← mul_assoc, h4, h]
  module

theorem pM_mul_qM (h : A * A * A = A) : pM A * qM A = 0 := by
  have h4 := A4 h
  unfold pM qM
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_add, add_mul, mul_sub, ← mul_assoc, h4, h]
  module

theorem J_mul_pM (h : IsGrad ε A) : Formalism.REAL.Jm ε * pM A = qM A * Formalism.REAL.Jm ε := by
  have hJ := J_mul h
  have h2 : Formalism.REAL.Jm ε * (A * A) = A * A * Formalism.REAL.Jm ε := by
    rw [← mul_assoc, hJ, neg_mul, mul_assoc, hJ, mul_neg, neg_neg, mul_assoc]
  unfold pM qM
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, add_mul, h2, hJ, sub_neg_eq_add]

theorem trace_qM (h : IsGrad ε A) : Matrix.trace (qM A) = Matrix.trace (pM A) := by
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have : qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε := by
    rw [J_mul_pM h, mul_assoc, hJJ, mul_one]
  rw [this, Matrix.trace_mul_comm, ← mul_assoc, hJJ, one_mul]

theorem pM_conjTranspose (h : Aᴴ = A) : (pM A)ᴴ = pM A := by
  unfold pM
  simp [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, h]

theorem isProj (h : A * A * A = A) : LinearMap.IsProj (Vm A) (Matrix.toLin' (pM A)) := by
  refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  change Matrix.toLin' (pM A) (Matrix.toLin' (pM A) y) = Matrix.toLin' (pM A) y
  rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, pM_idem h]

theorem trace_pM (h : A * A * A = A) : Matrix.trace (pM A) = (rk A : ℂ) := by
  have := (isProj h).trace
  rw [Matrix.trace_toLin'_eq] at this
  exact this

theorem one_le_rk (h : IsGrad ε A) : 1 ≤ rk A := by
  obtain ⟨-, -, h3, hA⟩ := id h
  by_contra hc
  have h0 : rk A = 0 := by omega
  have hb : Vm A = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hP : pM A = 0 := by
    have : Matrix.toLin' (pM A) = 0 := LinearMap.range_eq_bot.mp hb
    simpa using this
  have hQ : qM A = 0 := by
    have hJJ := Formalism.REAL.Jm_mul_self ε
    have : qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε := by
      rw [J_mul_pM h, mul_assoc, hJJ, mul_one]
    rw [this, hP]; simp
  apply hA
  have : A = qM A - pM A := by unfold pM qM; module
  rw [this, hP, hQ, sub_zero]

theorem isotropic (h : IsGrad ε A) {x y : Fin n → ℂ} (hx : x ∈ Vm A) (hy : y ∈ Vm A) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  obtain ⟨-, hH, h3, -⟩ := id h
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  change star (pM A *ᵥ u) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (pM A *ᵥ v)) = 0
  have hz : pM A * (Formalism.REAL.Jm ε * pM A) = 0 := by
    rw [J_mul_pM h, ← mul_assoc, pM_mul_qM h3, zero_mul]
  rw [star_mulVec, pM_conjTranspose hH, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, hz]
  simp

theorem flagFacts : FlagFacts := by
  intro n ε A h
  obtain ⟨-, -, h3, -⟩ := id h
  refine ⟨one_le_rk h, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [W]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h0 : W A 0 = ⊥ := rfl
    have h1 : W A 1 = Vm A := rfl
    change Module.finrank ℂ (W A 1) = Module.finrank ℂ (W A 0) + rk A
    rw [h0, h1, finrank_bot, zero_add]
    rfl
  · intro x hx y hy
    exact isotropic h hx hy
  · have hj : (Matrix.trace ((1 / 2 : ℂ) • (A * A + A))).re = (rk A : ℝ) := by
      change (Matrix.trace (qM A)).re = _
      rw [trace_qM h, trace_pM h3]
      simp
    unfold rhoA
    simp only [hj]

end GlobalTheory.CompanionTheory.GradFlag
end
end

section

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RightRule

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec

variable {n : ℕ}

def RightOK (ε : Fin n → Bool) (X : GMod n) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) : Prop :=
  ∀ (u : X.V) (Y : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε Y → ∀ g, Formalism.REAL.inUJ ε g →
    HasDerivAt (fun t : ℝ => c u (g * NormedSpace.exp ((t : ℂ) • Y))) (c (∑ a, ∑ b, Y a b • X.E a b u) g) 0

set_option backward.isDefEq.respectTransparency false in
theorem exp_entry (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Y) i j) (Y i j) 0 := by
  have e1 : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Y) i j) =
      fun t : ℝ => Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp (t • Y)) := by
    funext t
    have : (t : ℂ) • Y = t • Y := by ext a b; simp [Complex.real_smul]
    rw [this]; rfl
  have e2 : Y i j = Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp ((0 : ℝ) • Y) * Y) := by
    simp [NormedSpace.exp_zero]
  rw [e1, e2]
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0)

theorem mul_exp_entry (g Y : Matrix (Fin n) (Fin n) ℂ) (j i : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • Y)) j i) ((g * Y) j i) 0 := by
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum (u := Finset.univ) (A := fun l (t : ℝ) => g j l * NormedSpace.exp ((t : ℂ) • Y) l i)
    fun l _ => (exp_entry Y l i).const_mul (g j l)

theorem mul_exp_zero (g Y : Matrix (Fin n) (Fin n) ℂ) : g * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = g := by
  simp [NormedSpace.exp_zero]

theorem tens_action (X : GMod n) (Y : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → X.V) (i : Fin n) :
    (∑ a, ∑ b, Y a b • (tens X).E a b u) i = (∑ a, ∑ b, Y a b • X.E a b (u i)) + ∑ b, Y i b • u b := by
  show (∑ a, ∑ b, (Y a b • tensE X a b u : Fin n → X.V)) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, tensE_apply, smul_add, sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
  simp

theorem tens_ok {ε : Fin n → Bool} {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    (h : RightOK ε X c) (j : Fin n) : RightOK ε (tens X) (tensCoef X c j) := by
  intro u Y hY g hg
  have h1 : ∀ i, HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • Y)) j i *
      c (u i) (g * NormedSpace.exp ((t : ℂ) • Y)))
      ((g * Y) j i * c (u i) g + g j i * c (∑ a, ∑ b, Y a b • X.E a b (u i)) g) 0 := by
    intro i
    refine ((mul_exp_entry g Y j i).fun_mul (h (u i) Y hY g hg)).congr_deriv ?_
    simp only [mul_exp_zero]
  have h2 := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun i (t : ℝ) => (g * NormedSpace.exp ((t : ℂ) • Y)) j i * c (u i) (g * NormedSpace.exp ((t : ℂ) • Y)))
    fun i _ => h1 i
  refine h2.congr_deriv ?_
  have e : ∀ i, c ((∑ a, ∑ b, Y a b • (tens X).E a b u) i) g =
      c (∑ a, ∑ b, Y a b • X.E a b (u i)) g + ∑ b, Y i b * c (u b) g := by
    intro i
    refine (congrArg (fun v => c v g) (tens_action X Y u i)).trans ?_

    simp only [map_add (f := _), Pi.add_apply, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  show _ = ∑ i, g j i * c ((∑ a, ∑ b, Y a b • (tens X).E a b u) i) g
  refine Eq.trans ?_ (sum_congr rfl fun i _ => congrArg (g j i * ·) (e i).symm)
  simp only [mul_add, sum_add_distrib, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem step_ok {ε : Fin n → Bool} {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    (h : RightOK ε X c) (z : ℂ) (j : Fin n) : RightOK ε (step X z) (stepCoef X z c j) := by
  intro u Y hY g hg
  let S : (step X z).V →ₗ[ℂ] (tens X).V := (stepSub X z).subtype
  have hS : ∀ a b w, S ((step X z).E a b w) = (tens X).E a b (S w) := fun _ _ _ => rfl
  have e : S (∑ a, ∑ b, Y a b • (step X z).E a b u) = ∑ a, ∑ b, Y a b • (tens X).E a b (S u) := by

    simp only [map_sum, map_smul, hS]
  have h1 := tens_ok h j (S u) Y hY g hg
  refine h1.congr_deriv ?_
  show tensCoef X c j _ g = tensCoef X c j (S _) g
  rw [e]

theorem path_ok {ε : Fin n → Bool} : ∀ (ss : List (Fin n)) (X : GMod n)
    (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (χ : Fin n → ℂ) (js : List (Fin n)),
    RightOK ε X c → RightOK ε (path X χ ss) (pathCoef X c χ ss js)
  | [], _, _, _, _, h => h
  | s :: ss, X, c, χ, js, h => path_ok ss (step X (χ s)) (stepCoef X (χ s) c (js.headD s)) (χ + Pi.single s 1) js.tail
      (step_ok h _ _)

theorem base_ok {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (ξ : H) :
    RightOK ε ⟨D, E, hK.gl⟩ (baseCoef σ D ξ) := by
  intro u Y hY g hg
  let L : H →L[ℝ] ℂ := ((innerSL ℂ ξ).comp (σ g)).restrictScalars ℝ
  have h1 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hK.real Y hY u)
  have e : (fun t : ℝ => baseCoef σ D ξ u (g * NormedSpace.exp ((t : ℂ) • Y))) =
      L ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) (u : H) := by
    funext t
    show ⟪ξ, σ (g * NormedSpace.exp ((t : ℂ) • Y)) (u : H)⟫_ℂ = ⟪ξ, σ g (σ (NormedSpace.exp ((t : ℂ) • Y)) (u : H))⟫_ℂ
    rw [hσ.1.2 g hg _ (Formalism.REAL.exp_indefinite_unitary_holds n ε Y hY t)]
    rfl
  rw [e]
  refine h1.congr_deriv ?_
  show ⟪ξ, σ g (∑ a, ∑ b, Y a b • (E a b u : H))⟫_ℂ = ⟪ξ, σ g ((∑ a, ∑ b, Y a b • E a b u : D) : H)⟫_ℂ
  simp only [Submodule.coe_sum, Submodule.coe_smul]

theorem rightRule : CompanionTheory.RgExh.Dec.N.RightRule := by
  intro n ε H _ _ _ σ D E hK χ ss hσ i u X hX g hg
  exact path_ok ss ⟨D, E, hK.gl⟩ (baseCoef σ D (i.1 : H)) χ i.2 (base_ok hK hσ _) u X hX g hg

end GlobalTheory.CompanionTheory.RightRule
end
end

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgTransport

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

theorem anti_list_prod {A B : Type} [Ring A] [Ring B] (f : A → B) (h1 : f 1 = 1)
    (hm : ∀ x y, f (x * y) = f y * f x) (l : List A) :
    f l.prod = (l.map f).reverse.prod := by
  induction l with
  | nil => simpa using h1
  | cons a l ih => simp [List.prod_cons, hm, ih]

theorem anti_Tm {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₗ[ℂ] B) (h1 : f 1 = 1)
    {m : ℕ} (E : Fin m → Fin m → A) (v : ℂ) (a b : Fin m) :
    f (Tm E v a b) = Tm (fun a b => f (E b a)) v b a := by
  have hal : f (algebraMap ℂ A v) = algebraMap ℂ B v := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, h1]
  unfold Tm
  by_cases h : a = b
  · subst h; simp [hal]
  · simp [h, Ne.symm h]

theorem qdet_eq_qminorRow_rev {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E)
    (u : ℂ) : qdet E u = PI.qminorRow E (id ∘ Fin.revPerm) (id ∘ Fin.revPerm) u := by
  have hrow : PI.RowForm := quantum_minor_row_form
  rw [← hrow A m m E hE, quantumMinorRowSkew_holds A m m E id _ Fin.revPerm u,
    quantumMinorColSkew_holds A m m E hE id id Fin.revPerm u, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  rfl

theorem qdet_anti {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₗ[ℂ] B) (h1 : f 1 = 1)
    (hm : ∀ x y, f (x * y) = f y * f x) {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E) (u : ℂ) :
    qdet (fun a b => f (E b a)) u = f (qdet E u) := by
  rw [qdet_eq_qminorRow_rev E hE]
  unfold qdet qminor PI.qminorRow

  rw [map_sum]
  refine (Fintype.sum_equiv (PI.UnitaryGroupMassFormula.QmRowForm.revConj m) _ _ (fun σ => ?_)).symm
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, PI.UnitaryGroupMassFormula.QmRowForm.sign_revConj,
    anti_list_prod f h1 hm, List.map_ofFn, PI.UnitaryGroupMassFormula.QmRowForm.reverse_ofFn']
  congr 2
  refine List.ofFn_inj.mpr (funext fun k => ?_)
  simp only [Function.comp_apply, anti_Tm f h1, id]
  show Tm _ _ _ _ = Tm _ _ (Fin.revPerm (σ (Fin.revPerm k))) _
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  congr 1
  rw [Nat.cast_sub (by omega : (k : ℕ) + 1 ≤ m)]
  push_cast
  ring

end GlobalTheory.CompanionTheory.RgTransport
end
end
