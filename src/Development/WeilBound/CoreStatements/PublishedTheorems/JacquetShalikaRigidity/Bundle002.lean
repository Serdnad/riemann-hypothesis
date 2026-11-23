module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LogNormEstimates

theorem log_le {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (h1 : a ≤ D) (h2 : D ≤ b) :
    |Real.log D| ≤ |Real.log a| + |Real.log b| := by
  have l1 := Real.log_le_log ha h1
  have l2 := Real.log_le_log hD h2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]

theorem norm_le {p : ℂ} {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (h : p ≠ 0 → a ≤ D ∧ D ≤ b) (z z₀ : ℂ) :
    ‖p * (D : ℂ) ^ z‖ ≤ ‖p * (D : ℂ) ^ z₀‖ * Real.exp ((|Real.log a| + |Real.log b|) * |z.re - z₀.re|) := by
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨h1, h2⟩ := h hp
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  have e : D ^ z.re = D ^ z₀.re * D ^ (z.re - z₀.re) := by
    rw [← Real.rpow_add hD]; congr 1; ring
  rw [e, ← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_def_of_pos hD]
  apply Real.exp_le_exp.2
  calc Real.log D * (z.re - z₀.re) ≤ |Real.log D * (z.re - z₀.re)| := le_abs_self _
    _ = |Real.log D| * |z.re - z₀.re| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (log_le hD ha h1 h2) (abs_nonneg _)

theorem re_eq (p : ℂ) {D : ℝ} (hD : 0 < D) (σ u : ℝ) :
    (p * (D : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re = D ^ σ * (p * (D : ℂ) ^ ((u : ℂ) * Complex.I)).re := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hD.ne'), ← Complex.ofReal_cpow hD.le σ,
    show p * (((D ^ σ : ℝ) : ℂ) * (D : ℂ) ^ ((u : ℂ) * Complex.I)) =
      ((D ^ σ : ℝ) : ℂ) * (p * (D : ℂ) ^ ((u : ℂ) * Complex.I)) by ring, Complex.re_ofReal_mul]

set_option synthInstance.maxHeartbeats 400000 in
theorem msc {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} :
    MeasurableSingletonClass (GA E k) := inferInstance

end LogNormEstimates

theorem log_norm_estimate_of_Q : Q1 → D0 → N3 → C0 → D1 := by
  intro hQ1 hD0 hN3 hC0
  unfold D1 ForMu
  intro E _ _ _ k μ _ hk β hβ S P u z₀ hPc hPinv hP1 hpos hint
  obtain ⟨hDpos, hDmul, hDc, -, hDUU, -⟩ := hD0 E k
  obtain ⟨hG0o, h1G0, hG0inv, -⟩ := hC0 E k S
  obtain ⟨hNP, -, -, hN0⟩ := hN3 E k
  obtain ⟨hνs, hνinv, -⟩ := hNP 0 (by omega)
  obtain ⟨a, b, ha, hab⟩ := hpos
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hDmul 1 1
    simp only [mul_one] at h
    exact (mul_left_cancel₀ (hDpos 1).ne' (by rw [mul_one]; exact h.symm))
  have hG0m : MeasurableSet (G0 (k := k) S) := hG0o.measurableSet
  have hcont : ∀ z : ℂ, Continuous fun g : GA E k => P g * (Dt g : ℂ) ^ z := fun z =>
    hPc.mul ((Complex.continuous_ofReal.comp hDc).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g))
  set L := |Real.log a| + |Real.log b| with hL
  have hL0 : 0 ≤ L := by positivity
  have hdom : ∀ g ∈ G0 (k := k) S, ∀ z : ℂ,
      ‖P g * (Dt g : ℂ) ^ z‖ ≤ ‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * |z.re - z₀.re|) := by
    intro g hg z
    exact LogNormEstimates.norm_le (hDpos g) ha (fun hp => ⟨(hab g hg hp).1, (hab g hg hp).2.1⟩) z z₀
  have hintG : ∀ z : ℂ, Integrable (fun g => P g * (Dt g : ℂ) ^ z) ((μ.withDensity β).restrict (G0 S)) := by
    intro z
    refine Integrable.mono' ((hint.norm.mul_const (Real.exp (L * |z.re - z₀.re|))).restrict)
      (hcont z).aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem hG0m fun g hg => hdom g hg z
  refine ⟨fun z₁ => ?_, fun σ => ?_⟩
  · have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (μ.withDensity β).restrict (G0 S))
      (F := fun z g => P g * (Dt g : ℂ) ^ z)
      (F' := fun z g => P g * (Dt g : ℂ) ^ z * ((Real.log (Dt g) : ℝ) : ℂ)) (x₀ := z₁)
      (bound := fun g => ‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * (|z₁.re - z₀.re| + 1)) * L) (Metric.ball_mem_nhds z₁ zero_lt_one)
      (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable) (hintG z₁)
      ((hcont z₁).mul (Complex.continuous_ofReal.comp (hDc.log fun g => (hDpos g).ne'))).aestronglyMeasurable
      ?_ (((hint.norm.mul_const _).mul_const _).restrict) ?_
    · exact hderiv.2.differentiableAt
    · refine ae_restrict_of_forall_mem hG0m fun g hg z hz => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hp : P g = 0
      · simp only [hp, zero_mul, norm_zero]; positivity
      have hlog := LogNormEstimates.log_le (hDpos g) ha (hab g hg hp).1 (hab g hg hp).2.1
      have hz' : |z.re - z₀.re| ≤ |z₁.re - z₀.re| + 1 := by
        have h1 : |z.re - z₁.re| ≤ 1 := by
          have := Complex.abs_re_le_norm (z - z₁)
          rw [Metric.mem_ball, dist_eq_norm] at hz
          rw [Complex.sub_re] at this; linarith
        calc |z.re - z₀.re| = |(z.re - z₁.re) + (z₁.re - z₀.re)| := by ring_nf
          _ ≤ |z.re - z₁.re| + |z₁.re - z₀.re| := abs_add_le _ _
          _ ≤ _ := by linarith
      have e1 := hdom g hg z
      have e2 : Real.exp (L * |z.re - z₀.re|) ≤ Real.exp (L * (|z₁.re - z₀.re| + 1)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz' hL0)
      calc ‖P g * (Dt g : ℂ) ^ z‖ * |Real.log (Dt g)|
          ≤ (‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * (|z₁.re - z₀.re| + 1))) * L := by
            apply mul_le_mul _ hlog (abs_nonneg _) (by positivity)
            exact e1.trans (mul_le_mul_of_nonneg_left e2 (norm_nonneg _))
        _ = _ := rfl
    · refine Filter.Eventually.of_forall fun g z _ => ?_
      have hD := hDpos g
      have h := ((hasDerivAt_id z).const_cpow (c := (Dt g : ℂ))
        (Or.inl (Complex.ofReal_ne_zero.2 hD.ne'))).const_mul (P g)
      have e : P g * ((Dt g : ℂ) ^ id z * Complex.log (Dt g) * 1) =
          P g * (Dt g : ℂ) ^ z * ((Real.log (Dt g) : ℝ) : ℂ) := by
        rw [Complex.ofReal_log hD.le]; simp only [id, mul_one]; ring
      exact h.congr_deriv e
  · set f : GA E k → ℝ := fun g => (P g * (Dt g : ℂ) ^ ((u : ℂ) * Complex.I)).re with hf
    have hfc : Continuous f := Complex.continuous_re.comp (hcont _)
    set O : Set (GA E k) := G0 S ∩ {g | 0 < f g} with hO
    have hOo : IsOpen O := hG0o.inter (isOpen_lt continuous_const hfc)
    have hOm : MeasurableSet O := hOo.measurableSet
    have h1O : (1 : GA E k) ∈ O := by
      refine ⟨h1G0, ?_⟩
      show 0 < (P 1 * ((Dt (1 : GA E k) : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I)).re
      rw [hD1, Complex.ofReal_one, Complex.one_cpow, mul_one]; exact hP1
    have hOinv : ∀ n g, UU 0 n → (n * g ∈ O ↔ g ∈ O) := by
      intro n g hn
      simp only [hO, hf, Set.mem_inter_iff, Set.mem_setOf_eq, hG0inv n g hn, hPinv n hn g, hDmul, hDUU 0 n hn,
        one_mul]
    haveI : MeasurableSingletonClass (GA E k) := LogNormEstimates.msc
    set_option synthInstance.maxHeartbeats 400000 in
    have hμO : μ O ≠ 0 := (hOo.measure_pos μ ⟨1, h1O⟩).ne'
    have hβO : μ.withDensity β O ≠ 0 := by
      intro h0
      apply hμO
      have hin : ∀ g, ∫⁻ r, O.indicator 1 (r * g) ∂nuP E k 0 = O.indicator 1 g * nuP E k 0 Set.univ := by
        intro g
        rw [← lintegral_const]
        apply lintegral_congr_ae
        filter_upwards [(hN0 hk).1] with r hr
        by_cases hg : g ∈ O
        · simp [Set.indicator_apply, hg, (hOinv r g hr).2 hg]
        · simp [Set.indicator_apply, hg, mt (hOinv r g hr).1 hg]
      have key := hQ1 (GA E k) μ (Measure.dirac 1) (nuP E k 0) {1} (fun _ => 1) β
        (by rw [Measure.map_dirac' measurable_inv, inv_one]) (by rw [ae_dirac_eq]; exact rfl)
        ⟨measurable_const, fun g => by simp⟩ hβ.1
        (fun g => by
          simp only [lintegral_dirac, mul_one]
          calc ∫⁻ r, β (r⁻¹ * g) ∂nuP E k 0 = ∫⁻ r, β (r * g) ∂(Measure.map (fun h => h⁻¹) (nuP E k 0)) :=
                (lintegral_map (hβ.1.comp (measurable_mul_const g)) measurable_inv).symm
            _ = 1 := by rw [hνinv]; exact hβ.2 g)
        (O.indicator 1) (measurable_one.indicator hOm) (by rintro h rfl g; simp)
      have hw : μ.withDensity (fun _ => (1 : ℝ≥0∞)) = μ := withDensity_one
      rw [hw, lintegral_indicator_one hOm] at key
      rw [key]
      simp_rw [hin]
      rw [lintegral_mul_const _ (measurable_one.indicator hOm), lintegral_indicator_one hOm, h0, zero_mul]
    intro hzero
    have hFi := hintG ((σ : ℂ) + u * Complex.I)
    have hre := integral_re hFi
    rw [hzero] at hre
    simp only [RCLike.re_to_complex, Complex.zero_re] at hre
    have hpos' := (setIntegral_pos_iff_support_of_nonneg_ae (s := G0 S) (μ := μ.withDensity β)
      (f := fun g => (P g * (Dt g : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re)
      (ae_restrict_of_forall_mem hG0m fun g hg => ?_) hFi.re).2 ?_
    · linarith
    · by_cases hp : P g = 0
      · simp [hp]
      show 0 ≤ (P g * (Dt g : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re
      rw [LogNormEstimates.re_eq _ (hDpos g)]
      exact mul_nonneg (Real.rpow_nonneg (hDpos g).le _) (hab g hg hp).2.2
    · refine lt_of_lt_of_le (pos_iff_ne_zero.2 hβO) (measure_mono fun g hg => ⟨?_, hg.1⟩)
      rw [Function.mem_support, LogNormEstimates.re_eq _ (hDpos g)]
      exact (mul_pos (Real.rpow_pos_of_pos (hDpos g) σ) hg.2).ne'

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace RhoSigmaFinite

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem uu_eq_one {u : GA E k} {j : ℕ} (hj : k ≤ j) (hu : UU j u) : u = 1 :=
  Units.ext <| Matrix.ext fun i c => by rw [hu.2.2 i c (by omega), Units.val_one]


variable (E k) in
def rho : Measure (GA E k) := Measure.sum fun ξ : RowT E k k => Measure.dirac (ratGL E k (gam ξ))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem rho_sFinite [Countable (RowT E k k)] : SFinite (rho E k) := by
  rw [rho]; infer_instance

omit [_root_.NumberField.IsTotallyComplex E] in
theorem lint_rho (F : GA E k → ℝ≥0∞) : ∫⁻ r, F r ∂rho E k = ∑' ξ : RowT E k k, F (ratGL E k (gam ξ)) := by
  rw [rho, lintegral_sum_measure]
  simp only [lintegral_dirac]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem int_rho (Φ : GA E k → ℂ) (hΦ : Measurable Φ) (g : GA E k) :
    ∫ r, Φ (r * g) ∂rho E k = sumF Φ g := by
  by_cases hi : Integrable (fun r => Φ (r * g)) (rho E k)
  · rw [rho, integral_sum_measure hi, sumF]
    simp only [integral_dirac]
  · rw [integral_undef hi, sumF, tsum_eq_zero_of_not_summable]
    intro hs
    apply hi
    refine ⟨(hΦ.comp (measurable_mul_const g)).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lint_rho]
    have h1 : Summable fun ξ : RowT E k k => ‖Φ (ratGL E k (gam ξ) * g)‖₊ :=
      NNReal.summable_coe.mp (by simpa using hs.norm)
    have h2 := ENNReal.tsum_coe_ne_top_iff_summable.mpr h1
    simpa [enorm_eq_nnnorm] using h2.lt_top

end RhoSigmaFinite

open RhoSigmaFinite in
set_option synthInstance.maxHeartbeats 400000 in
theorem unipotent_integral_of : Q1 → Q2 → N0 → N3 → CosetIntegralParabolic → U0 := by
  intro hQ1 hQ2 hN0 hN3 hN4a E _ _ _ k μ _ hk β hβ
  have : Countable (RowT E k k) := (hN0 E k k hk le_rfl).2.2.2.2.2.2.1
  have : SFinite (rho E k) := rho_sFinite
  obtain ⟨hsf, hinv, hae⟩ := (hN3 E k).1 (k - 1) (by omega)
  have key : ∀ g, ∑' ξ : RowT E k k, ∫⁻ h, β ((ratGL E k (gam ξ))⁻¹ * h * g) ∂nuP E k (k - 1) = 1 := by
    intro g
    rw [← hN4a E k k hk le_rfl (fun h => β (h * g)) (hβ.1.comp (measurable_mul_const g))]
    exact hβ.2 g
  set β' : GA E k → ℝ≥0∞ := fun g => ∑' ξ : RowT E k k, β ((ratGL E k (gam ξ))⁻¹ * g) with hβ'
  have hwt : IsWt (nuP E k (k - 1)) β' := by
    refine ⟨Measurable.tsum fun ξ => hβ.1.comp (measurable_const_mul _), fun g => ?_⟩
    simp only [hβ']
    rw [lintegral_tsum (f := fun ξ h => β ((ratGL E k (gam ξ))⁻¹ * (h * g)))
      fun ξ => (hβ.1.comp ((measurable_const_mul _).comp (measurable_mul_const g))).aemeasurable]
    simpa only [mul_assoc] using key g
  have hH : ∀ᵐ h ∂nuP E k (k - 1), h ∈ {x : GA E k | ∃ γ, IsMir (k - 1) γ ∧ ratGL E k γ = x} := by
    filter_upwards [hae] with h ⟨γ, u, hγ, hu, hh⟩
    rw [hh, uu_eq_one (by omega) hu, mul_one]
    exact ⟨γ, hγ, rfl⟩
  have hone : ∀ g, ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k (k - 1) ∂rho E k = 1 := fun g => by
    rw [lint_rho]; exact key g
  refine ⟨β', hwt, fun Φ hΦ hΦi => ?_, fun Φ hΦ hΦi hint => ?_⟩
  · have := hQ1 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ
      (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g)
    rw [this]
    simp only [lint_rho]
  · have := (hQ2 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ
      (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g) hint).2
    rw [this]
    simp only [int_rho Φ hΦ]

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SmoothVectorHyp

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

structure Hyp (E : Type) [Field E] [NumberField E] (k : ℕ) : Prop where
  cont : Continuous (dmin : GA E k → ℝ)
  pos : ∀ g : GA E k, 0 < dmin g
  rt : ∀ h : GA E k, ∃ B : ℝ, 1 ≤ B ∧ ∀ g, dmin (g * h) ≤ B * dmin g

lemma min_le_of (a b D : ℝ) (hD : 1 ≤ D) (h : a ≤ D * b) : min 1 a ≤ D * min 1 b := by
  rcases le_total 1 b with h1 | h1
  · rw [min_eq_left h1]; exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right h1]; exact (min_le_right _ _).trans h

lemma wt_pos (H : Hyp E k) (M : ℕ) (g : GA E k) : 0 < wt M g :=
  pow_pos (lt_min one_pos (H.pos g)) M

lemma wt_le_one (H : Hyp E k) (M : ℕ) (g : GA E k) : wt M g ≤ 1 :=
  pow_le_one₀ (le_min zero_le_one (H.pos g).le) (min_le_left _ _)

lemma wt_cont (H : Hyp E k) (M : ℕ) : Continuous (wt M : GA E k → ℝ) :=
  (continuous_const.min H.cont).pow M

lemma wt_le (H : Hyp E k) (M : ℕ) (g c : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (h : dmin (g * c) ≤ D * dmin g) : wt M (g * c) ≤ D ^ M * wt M g := by
  unfold wt
  rw [← mul_pow]
  exact pow_le_pow_left₀ (le_min zero_le_one (H.pos _).le) (min_le_of _ _ _ hD h) M

def W (H : Hyp E k) (M : ℕ) : XB E k :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => ((wt M g : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (wt_cont H M)) 1 fun g => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_pos H M g).le]
      exact wt_le_one H M g

lemma ratio_cont (H : Hyp E k) (M : ℕ) (h : GA E k) :
    Continuous fun g : GA E k => ((wt M (g * h) / wt M g : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp
    (((wt_cont H M).comp (continuous_mul_const h)).div (wt_cont H M) fun g => (wt_pos H M g).ne')

lemma ratio_le (H : Hyp E k) (M : ℕ) (h g : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (hd : dmin (g * h) ≤ D * dmin g) : ‖((wt M (g * h) / wt M g : ℝ) : ℂ)‖ ≤ D ^ M := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (wt_pos H M _).le (wt_pos H M g).le), div_le_iff₀ (wt_pos H M g)]
  exact wt_le H M g h D hD hd

def Q (H : Hyp E k) (M : ℕ) (h : GA E k) : XB E k :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => ((wt M (g * h) / wt M g : ℝ) : ℂ))
    (ratio_cont H M h) ((H.rt h).choose ^ M) fun g =>
      ratio_le H M h g _ (H.rt h).choose_spec.1 ((H.rt h).choose_spec.2 g)

lemma norm_Q_le (H : Hyp E k) (M : ℕ) (h : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (hd : ∀ g, dmin (g * h) ≤ D * dmin g) : ‖Q H M h‖ ≤ D ^ M :=
  (BoundedContinuousFunction.norm_le (pow_nonneg (zero_le_one.trans hD) M)).mpr fun g =>
    ratio_le H M h g D hD (hd g)

def rho (H : Hyp E k) (M : ℕ) : GA E k →* (XB E k →L[ℂ] XB E k) where
  toFun h := (ContinuousLinearMap.mul ℂ (XB E k) (Q H M h)).comp (Rt E k h)
  map_one' := by
    ext x g
    change ((wt M (g * 1) / wt M g : ℝ) : ℂ) * x (g * 1) = x g
    rw [mul_one, div_self (wt_pos H M g).ne', Complex.ofReal_one, one_mul]
  map_mul' h h' := by
    ext x g
    change ((wt M (g * (h * h')) / wt M g : ℝ) : ℂ) * x (g * (h * h')) =
      ((wt M (g * h) / wt M g : ℝ) : ℂ) * (((wt M (g * h * h') / wt M (g * h) : ℝ) : ℂ) * x (g * h * h'))
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    have := (wt_pos H M (g * h)).ne'
    field_simp

lemma rho_apply (H : Hyp E k) (M : ℕ) (h g : GA E k) (x : XB E k) :
    rho H M h x g = ((wt M (g * h) / wt M g : ℝ) : ℂ) * x (g * h) := rfl

def J (H : Hyp E k) (M : ℕ) : XB E k →L[ℂ] XB E k := ContinuousLinearMap.mul ℂ (XB E k) (W H M)

lemma J_apply (H : Hyp E k) (M : ℕ) (x : XB E k) (g : GA E k) : J H M x g = (wt M g : ℂ) * x g := rfl

lemma inter (H : Hyp E k) (M : ℕ) (h : GA E k) (x : XB E k) : J H M (rho H M h x) = Rt E k h (J H M x) := by
  ext g
  rw [J_apply, rho_apply, Rt_apply, J_apply, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  have := (wt_pos H M g).ne'
  field_simp

lemma inj (H : Hyp E k) (M : ℕ) : Function.Injective (J H M) := by
  intro x y hxy
  ext g
  have e := congrArg (fun z : XB E k => z g) hxy
  simp only [J_apply] at e
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (wt_pos H M g).ne') e

variable [_root_.NumberField.IsTotallyComplex E]

lemma smv (H : Hyp E k) (M : ℕ) (x : XB E k) (hx : SmV ((rho H M).comp (infGL E k)) x) :
    SmV (repI E k) (J H M x) := by
  have e : orb (repI E k) (J H M x) = fun A => J H M (orb ((rho H M).comp (infGL E k)) x A) := by
    funext A
    unfold orb
    split_ifs with hA
    · exact (inter H M _ x).symm
    · exact (map_zero (J H M)).symm
  unfold SmV
  rw [e]
  exact hx.continuousLinearMap_comp ((J H M).restrictScalars ℝ)

end SmoothVectorHyp

theorem secondCohomologyBound_of_boundaryBound : H0 → K1 → K2 := by
  intro hH hK E _ _ _ k hk M
  obtain ⟨h1, -, -, -, -, ⟨B, N, -, h6⟩, -⟩ := hH E k
  obtain ⟨kc, kpos, kle, -, kcpt, -⟩ := hK E k hk
  have H : SmoothVectorHyp.Hyp E k := ⟨kc, kpos, fun h => by
    obtain ⟨B, hB, hB'⟩ := kcpt {h} isCompact_singleton
    exact ⟨B, hB, hB' h rfl⟩⟩
  refine ⟨SmoothVectorHyp.rho H M, SmoothVectorHyp.J H M, ⟨fun x g => rfl, SmoothVectorHyp.inter H M, SmoothVectorHyp.inj H M, ?_⟩,
    fun x hx => SmoothVectorHyp.smv H M x hx⟩
  have hne : Nonempty {ξ : Fin k → E // ξ ≠ 0} :=
    ⟨⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hk⟩)⟩⟩
  refine ⟨max B 1 ^ M, N * M, pow_nonneg (zero_le_one.trans (le_max_right _ _)) M, fun y x => ?_⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ := ⟨_, rfl⟩
  rw [← hP]
  have hP1 : 1 ≤ P := by
    rw [hP]
    linarith [norm_nonneg (Matrix.of.symm y.val : LieI (InfinitePlace E) k),
      norm_nonneg (Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)]
  have hPinv : 1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm y⁻¹⁻¹.val : LieI (InfinitePlace E) k)‖ = P := by
    rw [inv_inv, hP]; ring
  have hD : 1 ≤ max B 1 * P ^ N := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hP1)
  have hDpos : 0 < max B 1 * P ^ N := zero_lt_one.trans_le hD
  have hd : ∀ g, dmin (g * infGL E k y) ≤ max B 1 * P ^ N * dmin g := by
    intro g
    rw [← div_le_iff₀' hDpos]
    show _ ≤ ⨅ ξ : {ξ : Fin k → E // ξ ≠ 0}, ht g ξ.1
    refine le_ciInf fun ξ => ?_
    rw [div_le_iff₀' hDpos]
    calc dmin (g * infGL E k y) ≤ ht (g * infGL E k y) ξ.1 := kle _ _ ξ.2
      _ ≤ B * (1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ +
          ‖(Matrix.of.symm y⁻¹⁻¹.val : LieI (InfinitePlace E) k)‖) ^ N *
            ht (g * infGL E k y * infGL E k y⁻¹) ξ.1 := h6 y⁻¹ _ ξ.1 ξ.2
      _ = B * P ^ N * ht g ξ.1 := by
          rw [hPinv, mul_assoc g, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ ≤ max B 1 * P ^ N * ht g ξ.1 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (zero_le_one.trans hP1) _))
            (h1 g ξ.1 ξ.2).le
  change ‖SmoothVectorHyp.Q H M (infGL E k y) * Rt E k (infGL E k y) x‖ ≤ _
  calc ‖SmoothVectorHyp.Q H M (infGL E k y) * Rt E k (infGL E k y) x‖
        ≤ ‖SmoothVectorHyp.Q H M (infGL E k y)‖ * ‖Rt E k (infGL E k y) x‖ := norm_mul_le _ _
    _ = ‖SmoothVectorHyp.Q H M (infGL E k y)‖ * ‖x‖ := by rw [norm_Rt]
    _ ≤ (max B 1 * P ^ N) ^ M * ‖x‖ :=
        mul_le_mul_of_nonneg_right (SmoothVectorHyp.norm_Q_le H M _ _ hD hd) (norm_nonneg _)
    _ = max B 1 ^ M * P ^ (N * M) * ‖x‖ := by rw [mul_pow, ← pow_mul]

end PositivityTheory.AdelicQuotientData

end
end
