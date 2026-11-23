module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

namespace GlobalTheory.DerivativeOfAdditiveContinuous

theorem hasDerivAt_of_continuous_of_map_add (χ : ℝ → ℂ) (hc : Continuous χ)
    (hadd : ∀ s t : ℝ, χ (s + t) = χ s * χ t) (h0 : χ (0 : ℝ) = (1 : ℂ)) (s : ℝ) :
    HasDerivAt χ (deriv χ (0 : ℝ) * χ s) s := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hc 0 (1 / 2) (by norm_num)
  set η := δ / 2 with hη
  have hη0 : 0 < η := by positivity
  set c := ∫ t in (0 : ℝ)..η, χ t with hcdef
  have hc0 : c ≠ 0 := by
    have hsplit : c = (η : ℂ) + ∫ t in (0 : ℝ)..η, (χ t - 1) := by
      rw [hcdef, intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const]
      simp
    have hbound : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ ≤ 1 / 2 * |η - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le hη0.le] at ht
      have h1 : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
        linarith [ht.2]
      have h2 := hball t h1
      rw [dist_eq_norm, h0] at h2
      exact h2.le
    intro hzero
    rw [hsplit] at hzero
    have h3 : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ = η := by
      rw [eq_neg_of_add_eq_zero_right hzero, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hη0]
    rw [h3, sub_zero, abs_of_pos hη0] at hbound
    linarith
  set F : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, χ t with hF
  have hFd : ∀ x, HasDerivAt F (χ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hrep : ∀ x, χ x * c = F (x + η) - F x := by
    intro x
    have h1 : ∫ t in (0 : ℝ)..η, χ (x + t) = χ x * c := by
      simp only [hadd]
      rw [intervalIntegral.integral_const_mul]
    have h2 : ∫ t in (0 : ℝ)..η, χ (x + t) = ∫ t in x..(x + η), χ t := by
      rw [intervalIntegral.integral_comp_add_left]
      simp
    rw [← h1, h2, hF]
    simp only
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have hdiff : ∀ x, DifferentiableAt ℝ χ x := by
    intro x
    have hχ : χ = fun y => (F (y + η) - F y) / c := by
      funext y
      rw [← hrep y, mul_div_cancel_right₀ _ hc0]
    rw [hχ]
    exact (((hFd (x + η)).comp_add_const x η).sub (hFd x)).differentiableAt.div_const c
  have hd0 : HasDerivAt χ (deriv χ 0) (s - s) := by
    rw [sub_self]
    exact (hdiff 0).hasDerivAt
  have hcomp : HasDerivAt (fun y => χ (y - s)) (deriv χ 0) s := hd0.comp_sub_const s s
  have hmul := hcomp.const_mul (χ s)
  have hfun : (fun y => χ s * χ (y - s)) = χ := by
    funext y
    rw [← hadd]
    congr 1
    ring
  rw [hfun] at hmul
  rw [mul_comm]
  exact hmul

end GlobalTheory.DerivativeOfAdditiveContinuous
end

section

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory.TransDecay

theorem seminorm_mul_shift_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ h : 𝓢(V, ℂ)) (hχ : HasCompactSupport (χ : V → ℂ)) (l m M : ℕ) :
    ∃ C : ℝ, ∀ (v : V) (k' : 𝓢(V, ℂ)), (∀ x, k' x = χ x * h (x + v)) →
      SchwartzMap.seminorm ℂ l m k' ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  obtain ⟨r, hr⟩ := hχ.isCompact.isBounded.subset_closedBall (0 : V)
  set R := max r 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hxR : ∀ x ∈ tsupport (χ : V → ℂ), ‖x‖ ≤ R := fun x hx => by
    have := hr hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set S := ((Finset.Iic (M, m)).sup fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h
  have hS0 : 0 ≤ S := apply_nonneg _ _
  set A := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨R ^ l * A * ((1 + R) ^ M * (2 ^ M * S)), fun v k' hk' => ?_⟩
  have hvpos : 0 < (1 + ‖v‖) ^ M := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ l m k' (by positivity) fun x => ?_
  have hfun : (k' : V → ℂ) = fun y => χ y * h (y + v) := funext hk'
  rw [hfun]
  have hsh : ContDiff ℝ (⊤ : ℕ∞) (fun y => h (y + v)) :=
    (h.smooth ⊤).comp (contDiff_id.add contDiff_const)
  have hL := norm_iteratedFDeriv_mul_le (χ.smooth ⊤) hsh x (n := m) (by exact_mod_cast le_top)
  have hterm : ∀ i ∈ Finset.range (m + 1), ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
      ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖) ≤
      R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ) * ((1 + R) ^ M * (2 ^ M * S)) *
        ((1 + ‖v‖) ^ M)⁻¹ := by
    intro i _
    by_cases hx : x ∈ tsupport (χ : V → ℂ)
    · have hx1 := hxR x hx
      rw [iteratedFDeriv_comp_add_right]
      have hj : (1 + ‖x + v‖) ^ M * ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ ≤ 2 ^ M * S :=
        SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, m)) le_rfl (Nat.sub_le _ _) h (x + v)
      have hv : 1 + ‖v‖ ≤ (1 + R) * (1 + ‖x + v‖) := by
        have : ‖v‖ ≤ ‖x + v‖ + ‖x‖ := by
          calc ‖v‖ = ‖(x + v) - x‖ := by simp
            _ ≤ _ := norm_sub_le _ _
        nlinarith [norm_nonneg (x + v)]
      have hD : ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ ≤
          (1 + R) ^ M * (2 ^ M * S) * ((1 + ‖v‖) ^ M)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hvpos]
        calc ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ * (1 + ‖v‖) ^ M
            ≤ ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ * ((1 + R) * (1 + ‖x + v‖)) ^ M := by gcongr
          _ = (1 + R) ^ M * ((1 + ‖x + v‖) ^ M * ‖iteratedFDeriv ℝ (m - i) h (x + v)‖) := by
            rw [mul_pow]; ring
          _ ≤ (1 + R) ^ M * (2 ^ M * S) := by gcongr
      have hχi : ‖iteratedFDeriv ℝ i χ x‖ ≤ SchwartzMap.seminorm ℂ 0 i χ :=
        SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ χ i x
      calc ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
            ‖iteratedFDeriv ℝ (m - i) h (x + v)‖)
          ≤ R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ *
            ((1 + R) ^ M * (2 ^ M * S) * ((1 + ‖v‖) ^ M)⁻¹)) := by gcongr
        _ = _ := by ring
    · have h0 : iteratedFDeriv ℝ i χ x = 0 := by
        by_contra hne
        exact hx (support_iteratedFDeriv_subset i (Function.mem_support.2 hne))
      rw [h0, norm_zero, mul_zero, zero_mul, mul_zero]
      positivity
  calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ m (fun y => χ y * h (y + v)) x‖
      ≤ ‖x‖ ^ l * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (m + 1), ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ) *
          ((1 + R) ^ M * (2 ^ M * S)) * ((1 + ‖v‖) ^ M)⁻¹ := Finset.sum_le_sum hterm
    _ = R ^ l * A * ((1 + R) ^ M * (2 ^ M * S)) * ((1 + ‖v‖) ^ M)⁻¹ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]

theorem decay : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (a : V) (f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      ∫ x, T f' x * starRingEnd ℂ (T g' x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ) →
    ∀ (χ ψ h : SchwartzMap V ℂ), HasCompactSupport (χ : V → ℂ) → ∀ M : ℕ, ∃ C : ℝ,
      ∀ (v : V) (k ψv : SchwartzMap V ℂ), (∀ x, k x = χ (x - v) * h x) → (∀ x, ψv x = ψ (x - v)) →
        ‖∫ x, T k x * starRingEnd ℂ (T ψv x) ∂μ‖ ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  intro V _ _ _ _ _ μ _ T hinv χ ψ h hχ M
  have hp : Continuous ((SchwartzMap.seminorm ℂ 0 0 : Seminorm ℂ 𝓢(V, ℂ)).comp
      (T : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))) :=
    ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (0, 0)).comp T.continuous
  obtain ⟨s, C0, -, hC0⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) _ hp
  have hA : ∀ i : ℕ × ℕ, ∃ C : ℝ, ∀ (v : V) (k' : 𝓢(V, ℂ)), (∀ x, k' x = χ x * h (x + v)) →
      SchwartzMap.seminorm ℂ i.1 i.2 k' ≤ C * ((1 + ‖v‖) ^ M)⁻¹ :=
    fun i => seminorm_mul_shift_le χ h hχ i.1 i.2 M
  choose Cf hCf using hA
  set Cs := ∑ i ∈ s, |Cf i|
  have hCs : 0 ≤ Cs := Finset.sum_nonneg fun i _ => abs_nonneg _
  set I := ∫ x, ‖T ψ x‖ ∂μ
  have hint : Integrable (fun x => ‖T ψ x‖) μ := (SchwartzMap.integrable (T ψ)).norm
  refine ⟨(C0 : ℝ) * Cs * I, fun v k ψv hk hψv => ?_⟩
  set k' := SchwartzMap.compSubConstCLM ℂ (-v) k
  have hk' : ∀ x, k' x = k (x + v) := by
    intro x; simp [k', SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  have hk'' : ∀ x, k' x = χ x * h (x + v) := by intro x; rw [hk', hk]; simp
  have hψ : ∀ x, ψ x = ψv (x + v) := by intro x; rw [hψv]; simp
  rw [← hinv v k k' ψv ψ hk' hψ]
  have hsup : (s.sup (schwartzSeminormFamily ℂ V ℂ)) k' ≤ Cs * ((1 + ‖v‖) ^ M)⁻¹ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
    calc schwartzSeminormFamily ℂ V ℂ i k' ≤ Cf i * ((1 + ‖v‖) ^ M)⁻¹ := hCf i v k' hk''
      _ ≤ |Cf i| * ((1 + ‖v‖) ^ M)⁻¹ := by gcongr; exact le_abs_self _
      _ ≤ Cs * ((1 + ‖v‖) ^ M)⁻¹ := by
        gcongr
        exact Finset.single_le_sum (f := fun i => |Cf i|) (fun i _ => abs_nonneg _) hi
  have hTk : ∀ x, ‖T k' x‖ ≤ (C0 : ℝ) * (Cs * ((1 + ‖v‖) ^ M)⁻¹) := by
    intro x
    have h2 := hC0 k'
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h2
    calc ‖T k' x‖ ≤ SchwartzMap.seminorm ℂ 0 0 (T k') := SchwartzMap.norm_le_seminorm ℂ _ x
      _ ≤ (C0 : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) k' := h2
      _ ≤ _ := by gcongr
  calc ‖∫ x, T k' x * starRingEnd ℂ (T ψ x) ∂μ‖
      ≤ ∫ x, ((C0 : ℝ) * (Cs * ((1 + ‖v‖) ^ M)⁻¹)) * ‖T ψ x‖ ∂μ := by
        refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun x => ?_)
        rw [norm_mul, RCLike.norm_conj]
        gcongr
        exact hTk x
    _ = (C0 : ℝ) * Cs * I * ((1 + ‖v‖) ^ M)⁻¹ := by rw [integral_const_mul]; ring

end GlobalTheory.TransDecay
end

section

open scoped ContDiff

namespace GlobalTheory

theorem schwartz_shift_iteratedFDeriv_bound
    {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : SchwartzMap V ℂ) (a : V) (p : E →L[ℝ] V) (n M : ℕ) (R : ℝ) :
    ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖ ≤ C * ((1 + ‖y‖) ^ M)⁻¹ := by
  set S : ℝ := 2 ^ M * (Finset.Iic (M, n)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f with hS
  set B : ℝ := ‖a‖ + ‖p‖ * max R 0 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨‖p‖ ^ n * ((1 + B) ^ M * S), fun y t ht => ?_⟩
  have hy0 : 0 < (1 + ‖y‖) ^ M := by positivity

  have hcomp : (fun t => f (y + a + p t)) = (fun v => f (y + a + v)) ∘ p := rfl
  have hg : ContDiff ℝ ∞ (fun v => f (y + a + v)) :=
    (f.smooth ⊤).comp (contDiff_const.add contDiff_id)
  have e1 := ContinuousLinearMap.iteratedFDeriv_comp_right p hg t (i := n)
    (by exact_mod_cast le_top)
  have e2 : iteratedFDeriv ℝ n (fun v => f (y + a + v)) (p t)
      = iteratedFDeriv ℝ n f (y + a + p t) := iteratedFDeriv_comp_add_left n (y + a) (p t)
  set v := y + a + p t with hv
  have hD : ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖
      ≤ ‖p‖ ^ n * ‖iteratedFDeriv ℝ n f v‖ := by
    rw [hcomp, e1, e2]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [Finset.prod_const, mul_comm]

  have hdec : (1 + ‖v‖) ^ M * ‖iteratedFDeriv ℝ n f v‖ ≤ S :=
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M, n)) le_rfl le_rfl f v

  have hpt : ‖p t‖ ≤ ‖p‖ * max R 0 :=
    (p.le_opNorm t).trans (mul_le_mul_of_nonneg_left (ht.trans (le_max_left _ _)) (norm_nonneg _))
  have hyv : 1 + ‖y‖ ≤ (1 + ‖v‖) * (1 + B) := by
    have : y = v - a - p t := by rw [hv]; abel
    have h1 : ‖y‖ ≤ ‖v‖ + ‖a‖ + ‖p t‖ := by
      rw [this]
      calc ‖v - a - p t‖ ≤ ‖v - a‖ + ‖p t‖ := norm_sub_le _ _
        _ ≤ ‖v‖ + ‖a‖ + ‖p t‖ := by gcongr; exact norm_sub_le _ _
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith [mul_nonneg hv0 hB0]
  have hyM : (1 + ‖y‖) ^ M ≤ (1 + ‖v‖) ^ M * (1 + B) ^ M := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hyv M
  have hDf0 : 0 ≤ ‖iteratedFDeriv ℝ n f v‖ := norm_nonneg _
  have key : (1 + ‖y‖) ^ M * ‖iteratedFDeriv ℝ n f v‖ ≤ (1 + B) ^ M * S := by
    calc (1 + ‖y‖) ^ M * ‖iteratedFDeriv ℝ n f v‖
        ≤ (1 + ‖v‖) ^ M * (1 + B) ^ M * ‖iteratedFDeriv ℝ n f v‖ :=
          mul_le_mul_of_nonneg_right hyM hDf0
      _ = (1 + B) ^ M * ((1 + ‖v‖) ^ M * ‖iteratedFDeriv ℝ n f v‖) := by ring
      _ ≤ (1 + B) ^ M * S := mul_le_mul_of_nonneg_left hdec (by positivity)
  have hf' : ‖iteratedFDeriv ℝ n f v‖ ≤ (1 + B) ^ M * S * ((1 + ‖y‖) ^ M)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hy0, mul_comm]; exact key
  calc ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖
      ≤ ‖p‖ ^ n * ‖iteratedFDeriv ℝ n f v‖ := hD
    _ ≤ ‖p‖ ^ n * ((1 + B) ^ M * S * ((1 + ‖y‖) ^ M)⁻¹) :=
        mul_le_mul_of_nonneg_left hf' (by positivity)
    _ = ‖p‖ ^ n * ((1 + B) ^ M * S) * ((1 + ‖y‖) ^ M)⁻¹ := by ring

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem one_add_pow_le_two_pow_mul_one_add_pow (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + a ^ n) := by
        have : 0 ≤ a ^ n := pow_nonneg ha n
        nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) n]
  · calc (1 + a) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow 2 a n
      _ ≤ 2 ^ n * (1 + a ^ n) := by
        have : 0 ≤ (2:ℝ) ^ n := by positivity
        nlinarith


open Real in
theorem fourier_inversion_real_linear_forms :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : SchwartzMap V ℂ),
    ∃ (m : ℕ) (A : EuclideanSpace ℝ (Fin m) →L[ℝ] (V →L[ℝ] ℝ)) (φ : EuclideanSpace ℝ (Fin m) → ℂ),
      Continuous φ ∧ (∀ n : ℕ, Integrable (fun w => (1 + ‖w‖) ^ n * ‖φ w‖)) ∧
      ∀ x, ψ x = ∫ w, φ w * Complex.exp ((A w x : ℂ) * Complex.I) := by
  intro V _ _ _ ψ
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let ψ' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm ψ
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V →L[ℝ] ℝ :=
    (2 * π) • (((ContinuousLinearMap.compL ℝ V _ ℝ).flip (e : V →L[ℝ] _)).comp (innerSL ℝ))
  have hA : ∀ w x, A w x = 2 * π * inner ℝ w (e x) := by
    intro w x
    simp [A]
  let Φ : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ := FourierTransform.fourier ψ'
  refine ⟨Module.finrank ℝ V, A, (Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ),
    Φ.continuous, fun n => ?_, fun x => ?_⟩
  · have hi : Integrable (fun w : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) =>
        2 ^ n * (‖Φ w‖ + ‖w‖ ^ n * ‖Φ w‖)) :=
      ((Φ.integrable_pow_mul volume 0).norm.add (Φ.integrable_pow_mul volume n) |>.congr
        (Filter.Eventually.of_forall fun w => by simp)).const_mul _
    refine hi.mono' (by fun_prop) (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (1 + ‖w‖) ^ n * ‖Φ w‖ ≤ 2 ^ n * (1 + ‖w‖ ^ n) * ‖Φ w‖ :=
          mul_le_mul_of_nonneg_right (one_add_pow_le_two_pow_mul_one_add_pow _ (norm_nonneg _) n) (norm_nonneg _)
      _ = 2 ^ n * (‖Φ w‖ + ‖w‖ ^ n * ‖Φ w‖) := by ring
  · have h1 : ψ x = ψ' (e x) := by
      simp [ψ']
    have h2 := congrArg (fun f : SchwartzMap _ ℂ => f (e x))
      (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ) ψ')
    rw [h1, ← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    congr 1
    ext w
    rw [hA, smul_eq_mul, mul_comm]

end GlobalTheory
end

section

open scoped Matrix

namespace GlobalTheory

theorem matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span :
    ∀ (g : ℕ) (H H' : Matrix (Fin g) (Fin g) ℂ) (S : Set (Fin g → ℂ)),
    Submodule.span ℝ S = ⊤ →
    (∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ H.mulVec (star b)).im = (a ⬝ᵥ H'.mulVec (star b)).im) → H = H' := by
  intro g H H' S hS h
  set D := H - H' with hD
  have hS0 : ∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ D.mulVec (star b)).im = 0 := by
    intro a ha b hb
    simp only [hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, h a ha b hb, sub_self]
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun a b => (a ⬝ᵥ D.mulVec (star b)).im)
      (by intro a a' b; simp [add_dotProduct])
      (by intro r a b; simp [smul_dotProduct])
      (by intro a b b'; simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (by intro r a b; simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  have hB : B = 0 := by
    apply LinearMap.ext_on hS
    intro a ha
    apply LinearMap.ext_on hS
    intro b hb
    simpa [B] using hS0 a ha b hb
  have hall : ∀ a b, (a ⬝ᵥ D.mulVec (star b)) = 0 := by
    intro a b
    have h1 : (a ⬝ᵥ D.mulVec (star b)).im = 0 := by
      have := congrArg (fun f => f a b) hB
      simpa [B] using this
    have h2 : ((Complex.I • a) ⬝ᵥ D.mulVec (star b)).im = 0 := by
      have := congrArg (fun f => f (Complex.I • a) b) hB
      simpa [B] using this
    rw [smul_dotProduct, smul_eq_mul, Complex.mul_im] at h2
    simp at h2
    exact Complex.ext h2 h1
  have hDz : D = 0 := by
    ext i j
    have := hall (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec_single_one, Pi.star_single] using this
  exact sub_eq_zero.mp hDz

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem lattice_hom_finite_image_of_trivial_on_multiples :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (G : Type) [Group G] (e : (Fin g → ℂ) → G) (N : ℕ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z w, e (z + w) = e z * e w) → 0 < N →
    (∀ l ∈ Λ, e ((N : ℂ) • l) = 1) → (e '' (Λ : Set (Fin g → ℂ))).Finite := by
  intro g Λ G _ e N hd hspan hadd hN hker
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let f : (Module.Free.ChooseBasisIndex ℤ Λ → Fin N) → G :=
    fun a => e (∑ i, ((a i : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ))
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨l, hl, rfl⟩
  set x : Λ := ⟨l, hl⟩ with hxdef
  let c : Module.Free.ChooseBasisIndex ℤ Λ → ℤ := fun i => b.repr x i
  let q : Λ := ∑ i, (c i / N) • b i
  have hc : ∀ i, 0 ≤ c i % (N : ℤ) := fun i => Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  refine ⟨fun i => ⟨(c i % (N : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_lt_of_pos (c i) (by exact_mod_cast hN : (0 : ℤ) < N)
    omega
  · have hl' : l = (N : ℂ) • ((q : Λ) : Fin g → ℂ) +
        ∑ i, (((c i % (N : ℤ)).toNat : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ) := by
      have hx : l = ((∑ i, c i • b i : Λ) : Fin g → ℂ) := by
        rw [b.sum_repr x]
      rw [hx]
      simp only [q, Submodule.coe_sum, Submodule.coe_smul, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.toNat_of_nonneg (hc i)]
      have hN' : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_cast
      rw [hN', Int.cast_smul_eq_zsmul, smul_smul, ← add_smul]
      have h2 := Int.mul_ediv_add_emod (c i) (N : ℤ)
      congr 1
      linarith
    refine Eq.trans ?_ (congrArg e hl').symm
    rw [hadd, hker _ q.2, one_mul]

end GlobalTheory
end
end
