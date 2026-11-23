module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableA
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableWeightA
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.IsMultiHomogChartMonomial
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Bundle001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem PtsBddConv.maDensity_div_const {D : ℕ} (ψ : Fin D → (Fin D → ℂ) → ℝ) (r : ℝ) (z : Fin D → ℂ) :
    maDensity (fun j y => ψ j y / r) z = r⁻¹ ^ D * maDensity ψ z := by
  have hH : ∀ j, cxHessian (fun y => ψ j y / r) z = (((r⁻¹ : ℝ) : ℂ)) • cxHessian (ψ j) z := by
    intro j
    have h1 : (fun y => ψ j y / r) = r⁻¹ • ψ j := by
      funext y
      simp [div_eq_inv_mul]
    have h2 : fderiv ℝ (fderiv ℝ (fun y => ψ j y / r)) = r⁻¹ • fderiv ℝ (fderiv ℝ (ψ j)) := by
      rw [h1, fderiv_const_smul_field]
      exact fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ (ψ j)) r⁻¹
    ext a b
    simp only [cxHessian, h2, Pi.smul_apply, smul_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hS : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (fun y => ψ k y / r) z).det =
      ((r⁻¹ ^ D : ℝ) : ℂ) * ((-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (ψ k) z).det) := by
    intro S
    simp only [hH, ← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin]
    push_cast
    ring
  simp only [maDensity, mixedDisc, hS, ← Finset.mul_sum]
  rw [show (1 / (D.factorial : ℂ)) * (((r⁻¹ ^ D : ℝ) : ℂ) *
      ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (ψ k) z).det) =
      ((r⁻¹ ^ D : ℝ) : ℂ) * ((1 / (D.factorial : ℂ)) *
      ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (ψ k) z).det) by ring,
    Complex.re_ofReal_mul]
  ring

theorem PtsBddConv.proof (hAbs : Inter.PtsAbsIntegrable.Statement) : PtsBddConv.Statement := by
  intro K _ ι _ P e L r g g₀ N C s₀ hP hL hr hN hs₀ hg hlim
  classical

  have key : ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
      Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y,
        sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀ y w) ∧
      Tendsto (fun s => ptsIntegralAt P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s)) (𝓝[>] 0)
        (𝓝 (ptsIntegralAt P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀)) := by
    intro Ψ hΨ
    have hfin : ∀ y, (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).Finite := fibreFinite K ι P e Ψ hP hΨ
    have hL' : ∀ j : Fin e, IsSmoothHerm ((fun _ => L) j) := fun _ => hL
    have hone : IsSectionOn P (oneLine (ι := ι)) 1 := by
      refine ⟨0, fun k => by simp [oneLine, HermLine.ofWeight], fun m hm k => ?_,
        fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
      rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp
    have hB := hAbs K ι P e Ψ (fun _ => L) oneLine 1 hP hΨ hL' isSmoothHerm_oneLine hone

    have hbd : ∀ (h : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ hγ : ∃ γ, IsSheet P Ψ y w γ, |h (hγ.choose y)| ≤ C) →
        |sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) h y w| ≤
          C * r⁻¹ ^ e * |sheetDensity P Ψ (pot fun _ => L) (logNorm oneLine 1) y w| := by
      intro h y w hh
      by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
      · simp only [sheetDensity, dif_pos hγ, logNorm_oneLine, one_mul, pot]
        rw [PtsBddConv.maDensity_div_const (fun _ y' => Real.log (L.h (hγ.choose y'))) r y, abs_mul, abs_mul,
          abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) e), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hh hγ)
          (pow_nonneg (inv_nonneg.mpr hr.le) e)) (abs_nonneg _)
      · simp only [sheetDensity, dif_neg hγ, abs_zero, mul_zero, le_refl]
    have hsum : ∀ (h : ((Σ k, ι k) → ℂ) → ℝ) y, (∀ w (hγ : ∃ γ, IsSheet P Ψ y w γ), |h (hγ.choose y)| ≤ C) →
        ‖∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) h y w‖ ≤
          C * r⁻¹ ^ e * ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, |sheetDensity P Ψ (pot fun _ => L) (logNorm oneLine 1) y w| := by
      intro h y hh
      rw [Real.norm_eq_abs, finsum_mem_eq_finite_toFinset_sum _ (hfin y),
        finsum_mem_eq_finite_toFinset_sum _ (hfin y), Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => hbd h y w (hh w))

    set S : Set (Fin e → ℂ) := {y | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} with hSdef
    have hS : volume S = 0 := hN Ψ hΨ
    have hSae : ∀ᵐ y, y ∉ S := measure_eq_zero_iff_ae_notMem.mp hS
    have hpt : ∀ y w (hγ : ∃ γ, IsSheet P Ψ y w γ), hγ.choose y ∈ mcPts P ∧ Ψ (segre (hγ.choose y)) = Fin.cons 1 y :=
      fun y w hγ => ⟨hγ.choose_spec.2.self_of_nhds.2.1, hγ.choose_spec.2.self_of_nhds.2.2⟩
    have hoff : ∀ y ∉ S, ∀ w (hγ : ∃ γ, IsSheet P Ψ y w γ), hγ.choose y ∉ N :=
      fun y hy w hγ hz => hy ⟨_, (hpt y w hγ).1, hz, (hpt y w hγ).2⟩

    have hmeas : ∀ s, 0 < s → s < s₀ → AEStronglyMeasurable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y,
        sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s) y w) volume := by
      intro s hs hs1
      obtain ⟨-, hgc, hgt⟩ := hg s hs hs1
      set M := toMeasurable volume S with hMdef
      have hMm : MeasurableSet M := measurableSet_toMeasurable _ _
      have hSM : S ⊆ M := subset_toMeasurable _ _
      have hM0 : volume M = 0 := by rw [hMdef, measure_toMeasurable]; exact hS
      obtain ⟨g', hg'⟩ : ∃ g' : ((Σ k, ι k) → ℂ) → ℝ, ∀ z,
          g' z = if ∃ y ∈ M, Ψ (segre z) = Fin.cons 1 y then 0 else g s z := ⟨_, fun _ => rfl⟩
      obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin
      have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
        (hlift m y hy).1.continuousAt.continuousWithinAt
      have hcons : ∀ {y y' : Fin e → ℂ}, (Fin.cons 1 y : Fin (e + 1) → ℂ) = Fin.cons 1 y' → y = y' := by
        intro y y' h
        simpa using congrArg Fin.tail h
      set v : ℕ → (Fin e → ℂ) → ℝ := fun m => (B m \ M).piecewise (fun y => g s (γ m y)) 0 with hvdef
      have hvm : ∀ m, Measurable (v m) := by
        intro m
        refine ContinuousOn.measurable_piecewise ?_ continuousOn_const ((hBo m).measurableSet.diff hMm)
        refine hgc.comp ((hγc m).mono Set.sdiff_subset) fun y hy => ⟨(hlift m y hy.1).2.1, fun hz => ?_⟩
        exact hy.2 (hSM ⟨_, (hlift m y hy.1).2.1, hz, (hlift m y hy.1).2.2⟩)
      have hind0 := sheetIndep K ι P e Ψ (fun _ => L) oneLine 1 hP hΨ hL' isSmoothHerm_oneLine hone
      have hae := PtsSumMeasurableWeight.aestronglyMeasurable_fibreSum_of_lifts
        (fun (_ : Fin e) z => Real.log (L.h z) / r) g' id measurable_id rfl hfin B γ hBo hlift hcov
        (fun m y => v m y * maDensity (fun j y' => (fun (_ : Fin e) z => Real.log (L.h z) / r) j (γ m y')) y)
        (fun m => (hvm m).mul (PtsSumMeasurable.measurable_maDensity _))
        (fun m y hy => by
          rw [hg']
          simp only [hvdef]
          by_cases hyM : y ∈ M
          · rw [if_pos ⟨y, hyM, (hlift m y hy).2.2⟩,
              Set.piecewise_eq_of_notMem _ _ _ (fun h : y ∈ B m \ M => h.2 hyM)]
            simp
          · have hne : ¬ ∃ y' ∈ M, Ψ (segre (γ m y)) = Fin.cons 1 y' := by
              rintro ⟨y', hy'M, h⟩
              obtain rfl := hcons (((hlift m y hy).2.2).symm.trans h)
              exact hyM hy'M
            rw [if_neg hne, Set.piecewise_eq_of_mem (B m \ M) _ _ (Set.mem_sdiff_of_mem hy hyM)])
        (by
          filter_upwards [hind0] with y hy w γ₁ γ₂ h₁ h₂
          have hd := hy w γ₁ γ₂ h₁ h₂
          simp only [logNorm_oneLine, one_mul, pot] at hd
          have hm₁ : γ₁ y ∈ mcPts P := h₁.2.self_of_nhds.2.1
          have hm₂ : γ₂ y ∈ mcPts P := h₂.2.self_of_nhds.2.1
          have hseg : segre (γ₁ y) = segre (γ₂ y) := h₁.1.trans h₂.1.symm
          choose i0 hi0 using hm₁.1
          obtain ⟨hc0, hc⟩ := eq_bsmul_of_segre_eq i0 hi0 hseg
          have hgg : g s (γ₂ y) = g s (γ₁ y) := by
            rw [hc]
            exact hgt _ (fun k => div_ne_zero (hc0 k) (hi0 k)) _ hm₁
          rw [PtsBddConv.maDensity_div_const (fun _ y' => Real.log (L.h (γ₁ y'))) r y,
            PtsBddConv.maDensity_div_const (fun _ y' => Real.log (L.h (γ₂ y'))) r y, hd, hg', hg', hseg, hgg])
      refine hae.congr ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hM0] with y hy
      refine finsum_mem_congr rfl fun w _ => ?_
      by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
      · simp only [id, sheetDensity, dif_pos hγ]
        have hne : ¬ ∃ y' ∈ M, Ψ (segre (hγ.choose y)) = Fin.cons 1 y' := by
          rintro ⟨y', hy'M, h⟩
          obtain rfl := hcons ((hpt y w hγ).2.symm.trans h)
          exact hy hy'M
        rw [hg', if_neg hne]
      · simp only [id, sheetDensity, dif_neg hγ]

    have hlimpt : ∀ᵐ y, Tendsto (fun s => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y,
        sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s) y w) (𝓝[>] 0)
        (𝓝 (∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀ y w)) := by
      filter_upwards [hSae] with y hy
      rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
      simp only [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
      refine tendsto_finsetSum _ fun w _ => ?_
      by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
      · simp only [sheetDensity, dif_pos hγ]
        exact (hlim _ (hpt y w hγ).1 (hoff y hy w hγ)).mul_const _
      · simp only [sheetDensity, dif_neg hγ]
        exact tendsto_const_nhds
    have hbound := hB.const_mul (C * r⁻¹ ^ e)

    have hg₀ : ∀ z ∈ mcPts P, z ∉ N → |g₀ z| ≤ C := fun z hz hzN =>
      le_of_tendsto ((continuous_abs.tendsto _).comp (hlim z hz hzN))
        (by filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs using (hg s hs.1 hs.2).1 z hz)
    set u : ℕ → ℝ := fun n => s₀ / 2 * (1 / ((n : ℝ) + 1)) with hudef
    have hupos : ∀ n, 0 < u n := fun n => by positivity
    have hult : ∀ n, u n < s₀ := fun n => by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      calc u n ≤ s₀ / 2 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
        _ < s₀ := by linarith
    have hu : Tendsto u atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hupos⟩
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (s₀ / 2)
      rw [mul_zero] at h
      exact h
    have hmeas₀ := aestronglyMeasurable_of_tendsto_ae atTop (fun n => hmeas (u n) (hupos n) (hult n))
      (by filter_upwards [hlimpt] with y hy using hy.comp hu)
    refine ⟨hbound.mono' hmeas₀ ?_, ?_⟩
    · filter_upwards [hSae] with y hy
      exact hsum g₀ y fun w hγ => hg₀ _ (hpt y w hγ).1 (hoff y hy w hγ)
    · refine tendsto_integral_filter_of_dominated_convergence _
        (by filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs using hmeas s hs.1 hs.2) ?_ hbound hlimpt
      filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      exact Eventually.of_forall fun y => hsum (g s) y fun w hγ => (hg s hs.1 hs.2).1 _ (hpt y w hγ).1
  refine ⟨fun Ψ hΨ => (key Ψ hΨ).1, ?_⟩
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ
  · simp only [dif_pos hΨ]
    exact (key _ hΨ.choose_spec).2
  · simp only [dif_neg hΨ]
    exact tendsto_const_nhds

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem BoundaryNull.proof : BoundaryNull.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D
  classical
  exact BoundaryPtsNull.proof II Ψ K ι Ω E D

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped Matrix ComplexOrder

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ} {y : (Σ k, ι k) → Ω}
  {W : ChartBundle ℤ (segreCoord y) N E} {Xo : Set ((Σ k, ι k) → ℂ)}

namespace HermMetric

section ToTwin

variable {P : Ideal (MRing ι)} {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} {χ : Fin nc → SncChart P n Bd}


open Classical in
def gramMatrixInFamily (hA : HermMetric y W Xo χ) (z : (Σ k, ι k) → ℂ) (b : Fin N → E) :
    Matrix (Fin N) (Fin N) ℂ :=
  if hz : ∃ l, InFrameDomain y (hA.chart l) (hA.fr l) z then
    if hS : ∃ S : Matrix (Fin N) (Fin N) Ω, ∀ q, b q = ∑ p, S p q • hA.b hz.choose p then
      (HermMetricEq.valM y hS.choose z)ᴴ * hA.gram hz.choose z * HermMetricEq.valM y hS.choose z
    else 0
  else 0

theorem gramMatrix_change_of_frame (hA : HermMetric y W Xo χ) (hXo : Xo ⊆ mcPts (mCoordIdeal y))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ Xo) {l : Fin hA.m} (hd : InFrameDomain y (hA.chart l) (hA.fr l) z)
    {b : Fin N → E} {S : Matrix (Fin N) (Fin N) Ω}
    (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) z) (hb : ∀ q, b q = ∑ p, S p q • hA.b l p) :
    hA.gramMatrixInFamily z b = (HermMetricEq.valM y S z)ᴴ * hA.gram l z * HermMetricEq.valM y S z := by
  have hzP := hXo hz
  have hex : ∃ l, InFrameDomain y (hA.chart l) (hA.fr l) z := ⟨l, hd⟩
  have hd0 : InFrameDomain y (hA.chart hex.choose) (hA.fr hex.choose) z := hex.choose_spec
  obtain ⟨T, hT, hTe⟩ := HermMetricEq.exists_coeff (hA.isFrame hex.choose) hzP hd0
    (HermMetricEq.isFrameAt_of_isFrameOver (hA.isFrame l) hzP hd).1
  have hbT : ∀ q, b q = ∑ p, (T * S) p q • hA.b hex.choose p := by
    intro q
    rw [hb q]
    simp only [hTe, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => ?_
    rw [mul_comm]
  have hS' : ∃ S' : Matrix (Fin N) (Fin N) Ω, ∀ q, b q = ∑ p, S' p q • hA.b hex.choose p :=
    ⟨T * S, hbT⟩
  have hchoose : hS'.choose = T * S := HermMetricEq.coeff_unique (hA.isFrame hex.choose).2.2.2.1
    fun q => (hS'.choose_spec q).symm.trans (hbT q)
  have hTS : HermMetricEq.valM y (T * S) z = HermMetricEq.valM y T z * HermMetricEq.valM y S z :=
    HermMetricEq.valM_eq hzP (HermMetricEq.isValueAt_mul (fun p q => (hT p q).isValueAt hzP)
      (fun p q => (hS p q).isValueAt hzP))
  have hcompat := hA.compat hex.choose l z hz hd0 hd T hTe (HermMetricEq.valM y T z)
    (fun p q => HermMetricEq.isValueAt_iff.2 ((hT p q).isValueAt hzP))
  rw [gramMatrixInFamily, dite_eq_left hex, dite_eq_left hS', hchoose, hTS, hcompat]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem contDiffAt_valAt {m : ℕ} {O : Set (Fin m → ℂ)} {γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ}
    (hO : IsOpen O) (hγ : AnalyticOnNhd ℂ γ O) (hU : ∀ w ∈ O, γ w ∈ mcPts (mCoordIdeal y))
    {w : Fin m → ℂ} (hw : w ∈ O) {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (γ w)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => IndefiniteRowSideFullHecke.LowerBoundFree.valAt y a (γ w')) w := by
  obtain ⟨v, d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  have hcoord : ∀ p, AnalyticAt ℂ (fun w' => γ w' p) w := fun p =>
    ((ContinuousLinearMap.proj p : ((Σ k, ι k) → ℂ) →L[ℂ] ℂ).analyticAt (γ w)).comp (hγ w hw)
  have hG := analyticAt_eval_comp (F := γ) hcoord g
  have hH := analyticAt_eval_comp (F := γ) hcoord h
  have hF : AnalyticAt ℂ (fun w' => eval (γ w') (map (Int.castRingHom ℂ) g) /
      eval (γ w') (map (Int.castRingHom ℂ) h)) w := hG.div hH hz
  have hev : (fun w' => IndefiniteRowSideFullHecke.LowerBoundFree.valAt y a (γ w')) =ᶠ[𝓝 w] fun w' =>
      eval (γ w') (map (Int.castRingHom ℂ) g) / eval (γ w') (map (Int.castRingHom ℂ) h) := by
    have h1 : ∀ᶠ w' in 𝓝 w, eval (γ w') (map (Int.castRingHom ℂ) h) ≠ 0 :=
      hH.continuousAt.eventually_ne hz
    filter_upwards [h1, hO.mem_nhds hw] with w' h1 h2
    exact IndefiniteRowSideFullHecke.LowerBoundFree.valAt_eq (hU w' h2)
      ⟨d, g, h, hg, hh, hy, hyg, h1, by rw [div_mul_cancel₀ _ h1]⟩
  exact (hF.contDiffAt.restrict_scalars ℝ).congr_of_eventuallyEq hev

end ToTwin

section OfTwin

end OfTwin

namespace Example

open Line

end Example

end HermMetric

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem PivotMinorFlag.full : PivotMinorFlag.Statement := by
  intro R _ n M a b hab
  exact ⟨⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩, pivotMinor_eq_flagMinor M a b hab⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel

def VerticalTwistGenDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (a : K → ℤ)
    (s : Finset ℕ) (b : ℕ → K → ℤ) (f g : ℕ → MRing ι),
    IsArithVar P (d + 1) → (∀ p ∈ s, p.Prime ∧ IsVerticalDivisorAt P p (b p) (f p) (g p)) →
    genDeg P d (a + ∑ p ∈ s, b p) = genDeg P d a

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
