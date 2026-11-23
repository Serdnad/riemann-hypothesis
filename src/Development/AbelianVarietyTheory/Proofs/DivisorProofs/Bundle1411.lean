module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

set_option autoImplicit false in
open Filter Topology MeasureTheory in
open scoped ComplexOrder Matrix in
private lemma ofReal_norm_sum_mul_sq_eq_double_sum_conj {ι : Type} [Fintype ι] (c w : ι → ℂ) :
    ((‖∑ i, c i * w i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * (w i * (starRingEnd ℂ) (w j)) := by

  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring


set_option autoImplicit false in
open Filter Topology MeasureTheory in
open scoped ComplexOrder Matrix in
theorem _root_.GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form (S : Type) (Y : S → Type)
    [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι]
    [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ)
    (h : _root_.GlobalTheory.HSAmp.IsFam μ v) :
    (_root_.GlobalTheory.HSAmp.gram μ v).IsHermitian ∧ ∀ c : ι → ℂ,
      (∀ σ, Integrable (_root_.GlobalTheory.HSAmp.cmb v c σ) (μ σ)) ∧
      0 ≤ _root_.GlobalTheory.HSAmp.l2 μ v c ∧
      (_root_.GlobalTheory.HSAmp.l2 μ v c : ℂ) =
        ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * _root_.GlobalTheory.HSAmp.gram μ v i j := by
  haveI : Fintype S := @Fintype.ofFinite S h.finite
  have hint := h.integrable
  have hterm : ∀ (c : ι → ℂ) (σ : S), Integrable (fun y => ∑ i, ∑ j,
      c i * (starRingEnd ℂ) (c j) * (v σ y i * (starRingEnd ℂ) (v σ y j))) (μ σ) :=
    fun c σ => integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hint σ i j).const_mul _
  refine ⟨?_, fun c => ⟨fun σ => ?_, ?_, ?_⟩⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, _root_.GlobalTheory.HSAmp.gram, Matrix.of_apply,
      finsum_eq_sum_of_fintype]
    rw [star_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Complex.star_def, ← integral_conj]
    congr 1 with y
    simp [mul_comm]
  · refine (hterm c σ).re.congr (ae_of_all _ fun y => ?_)
    simp only [_root_.GlobalTheory.HSAmp.cmb]
    rw [← ofReal_norm_sum_mul_sq_eq_double_sum_conj c (v σ y)]
    exact Complex.ofReal_re _
  · unfold _root_.GlobalTheory.HSAmp.l2
    exact finsum_nonneg fun σ => integral_nonneg fun y => by
      simp only [_root_.GlobalTheory.HSAmp.cmb]
      positivity
  · unfold _root_.GlobalTheory.HSAmp.l2 _root_.GlobalTheory.HSAmp.gram
    simp only [Matrix.of_apply, finsum_eq_sum_of_fintype]
    have key : ∀ σ, ((∫ y, _root_.GlobalTheory.HSAmp.cmb v c σ y ∂μ σ : ℝ) : ℂ) =
        ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ := by
      intro σ
      simp only [_root_.GlobalTheory.HSAmp.cmb]
      rw [← integral_complex_ofReal,
        integral_congr_ae (ae_of_all _ fun y => ofReal_norm_sum_mul_sq_eq_double_sum_conj c (v σ y)),
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (hint σ i j).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hint σ i j).const_mul _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    rw [Complex.ofReal_sum]
    simp only [key, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end GlobalTheory.HSAmp
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.VolDens

theorem meas_integral_in_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D) (c : AlgChart p σ D) (S : Set (CxPts p σ))
    (F : CxPts p σ → ℝ), MeasurableSet S → S ⊆ c.e.source → Continuous F →
    ω.meas S = ∫⁻ v in c.e '' S, ENNReal.ofReal (ω.dens c (c.e.symm v)) ∧
    ∫ y in S, F y ∂ω.meas = ∫ v in c.e '' S, F (c.e.symm v) * ω.dens c (c.e.symm v) := by
  intro k _ X _ p D hX σ ω c S F hS hc hF
  haveI : SecondCountableTopology (CxPts p σ) :=
    CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  have hmeas : ∀ A : Set (CxPts p σ), MeasurableSet A → A ⊆ c.e.source →
      ω.meas A = ∫⁻ v in c.e '' A, ENNReal.ofReal (ω.dens c (c.e.symm v)) := by
    intro A hA hAc
    rw [VolDens.meas, ChartGlue.glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
      rw [ω.trans c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) c hA hAc,
      ChartGlue.chartMeas_apply_of_subset _ _ hA hAc]
  refine ⟨hmeas S hS hc, ?_⟩
  have hSm : MeasurableSet (c.e '' S) := ChartGlue.measurableSet_image c.e hS hc
  have hSt : c.e '' S ⊆ c.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.e.map_source (hc hy)
  set f : _ → ENNReal := fun v => ENNReal.ofReal (ω.dens c (c.e.symm v)) with hf
  set ν := (volume.restrict (c.e '' S)).withDensity f with hν
  have haem : AEMeasurable c.e.symm ν :=
    ((c.e.continuousOn_symm.mono hSt).aemeasurable hSm).mono_ac (withDensity_absolutelyContinuous _ _)
  have hrest : ω.meas.restrict S = Measure.map c.e.symm ν := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.map_apply_of_aemeasurable haem hA,
      hmeas (A ∩ S) (hA.inter hS) (Set.inter_subset_right.trans hc), hν, withDensity_apply' _ _,
      Measure.restrict_restrict' hSm]
    congr 2
    ext v
    constructor
    · rintro ⟨y, ⟨hyA, hyS⟩, rfl⟩
      exact ⟨by simpa [c.e.left_inv (hc hyS)] using hyA, ⟨y, hyS, rfl⟩⟩
    · rintro ⟨hvA, y, hyS, rfl⟩
      exact ⟨y, ⟨by simpa [c.e.left_inv (hc hyS)] using hvA, hyS⟩, rfl⟩
  have hfm : AEMeasurable f (volume.restrict (c.e '' S)) := by
    refine (ENNReal.measurable_ofReal.comp_aemeasurable ?_)
    refine ContinuousOn.aemeasurable ?_ hSm
    refine (ω.cont c).comp (c.e.continuousOn_symm.mono hSt) ?_
    intro v hv
    exact c.e.map_target (hSt hv)
  rw [hrest, integral_map haem hF.aestronglyMeasurable, hν,
    integral_withDensity_eq_integral_toReal_smul₀ hfm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun hSm fun v hv => ?_
  have hpos := ω.pos c _ (c.e.map_target (hSt hv))
  simp only [hf, smul_eq_mul, ENNReal.toReal_ofReal hpos.le, mul_comm]

end GlobalTheory.HSAmp.VolDens
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.VolFin

open GlobalTheory.ChartGlue
open scoped ENNReal

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem meas_eq [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D) (c : AlgChart p σ D)
    {S : Set (CxPts p σ)} (hS : MeasurableSet S) (hc : S ⊆ c.e.source) :
    ω.meas S = ∫⁻ v in c.e '' S, ENNReal.ofReal (ω.dens c (c.e.symm v)) := by
  rw [VolDens.meas, glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
    rw [ω.trans c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) c hS hc,
    chartMeas_apply_of_subset _ _ hS hc]

theorem continuousOn_dens (ω : VolDens p σ D) (c : AlgChart p σ D) :
    ContinuousOn (fun v => ω.dens c (c.e.symm v)) c.e.target :=
  (ω.cont c).comp c.e.continuousOn_symm fun _ hv => c.e.map_target hv

theorem exists_open_lt_top [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D)
    (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ∃ O : Set (CxPts p σ), IsOpen O ∧ y ∈ O ∧ ω.meas O < ∞ := by
  set g := fun v => ω.dens c (c.e.symm v)
  have hv0 : c.e y ∈ c.e.target := c.e.map_source hy
  have hg : ContinuousAt g (c.e y) :=
    (continuousOn_dens ω c).continuousAt (c.e.open_target.mem_nhds hv0)
  have h1 : ∀ᶠ v in 𝓝 (c.e y), g v < g (c.e y) + 1 :=
    hg.eventually (gt_mem_nhds (lt_add_one _))
  have h2 : ∀ᶠ v in 𝓝 (c.e y), v ∈ c.e.target := c.e.open_target.mem_nhds hv0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε,
    c.e.isOpen_inter_preimage Metric.isOpen_ball, ⟨hy, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩, ?_⟩
  have hO : MeasurableSet (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε) :=
    (c.e.isOpen_inter_preimage Metric.isOpen_ball).measurableSet
  rw [meas_eq ω c hO Set.inter_subset_left]
  have hsub : c.e '' (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε) ⊆ Metric.ball (c.e y) ε := by
    rintro _ ⟨z, hz, rfl⟩; exact hz.2
  calc ∫⁻ v in c.e '' (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε), ENNReal.ofReal (g v)
      ≤ ∫⁻ v in Metric.ball (c.e y) ε, ENNReal.ofReal (g v) :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
    _ ≤ ∫⁻ _ in Metric.ball (c.e y) ε, ENNReal.ofReal (g (c.e y) + 1) := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
          fun v hv => ENNReal.ofReal_le_ofReal (hball v hv).1.le)
    _ = ENNReal.ofReal (g (c.e y) + 1) * volume (Metric.ball (c.e y) ε) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

theorem meas_pos [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D)
    (c : AlgChart p σ D) {U : Set (CxPts p σ)} (hU : IsOpen U) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hyU : y ∈ U) : ω.meas U ≠ 0 := by
  set g := fun v => ω.dens c (c.e.symm v)
  have hv0 : c.e y ∈ c.e.target := c.e.map_source hy
  have hg : ContinuousAt g (c.e y) :=
    (continuousOn_dens ω c).continuousAt (c.e.open_target.mem_nhds hv0)
  have hpos : 0 < g (c.e y) := by
    simp only [g, c.e.left_inv hy]; exact ω.pos c y hy
  have h1 : ∀ᶠ v in 𝓝 (c.e y), g (c.e y) / 2 < g v :=
    hg.eventually (lt_mem_nhds (half_lt_self hpos))
  have h2 : ∀ᶠ v in 𝓝 (c.e y), v ∈ c.e.target ∩ c.e.symm ⁻¹' U :=
    (isOpen_over c.e hU).mem_nhds (mem_over c.e hy hyU)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  have hA : MeasurableSet (c.e.source ∩ U) := (c.e.open_source.inter hU).measurableSet
  have hsub : Metric.ball (c.e y) ε ⊆ c.e '' (c.e.source ∩ U) := by
    rw [c.e.image_source_inter_eq']; exact fun v hv => (hball v hv).2
  refine (lt_of_lt_of_le ?_ (measure_mono (μ := ω.meas) (Set.inter_subset_right :
    c.e.source ∩ U ⊆ U))).ne'
  rw [meas_eq ω c hA Set.inter_subset_left]
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (g (c.e y) / 2) * volume (Metric.ball (c.e y) ε) :=
        ENNReal.mul_pos (ENNReal.ofReal_pos.2 (half_pos hpos)).ne' (Metric.measure_ball_pos _ _ hε).ne'
    _ = ∫⁻ _ in Metric.ball (c.e y) ε, ENNReal.ofReal (g (c.e y) / 2) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ v in Metric.ball (c.e y) ε, ENNReal.ofReal (g v) :=
        lintegral_mono_ae (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
          fun v hv => ENNReal.ofReal_le_ofReal (hball v hv).1.le)
    _ ≤ ∫⁻ v in c.e '' (c.e.source ∩ U), ENNReal.ofReal (g v) :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

end GlobalTheory.HSAmp.VolFin


open GlobalTheory.HSAmp.VolFin in
theorem GlobalTheory.HSAmp.volDens_meas_finite_openPos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D),
    IsFiniteMeasure ω.meas ∧ ω.meas.IsOpenPosMeasure := by
  intro k _ X _ p D hX hS σ ω
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  haveI := hX.compactSpace σ
  obtain ⟨R⟩ := hS σ
  haveI : IsLocallyFiniteMeasure ω.meas := ⟨fun y => by
    obtain ⟨i, hi⟩ := R.cover y
    obtain ⟨O, hO, hyO, hfin⟩ := exists_open_lt_top ω (R.chart i) hi
    exact ⟨O, hO.mem_nhds hyO, hfin⟩⟩
  refine ⟨inferInstance, ⟨fun U hU ⟨y, hyU⟩ => ?_⟩⟩
  obtain ⟨i, hi⟩ := R.cover y
  exact meas_pos ω (R.chart i) hU hi hyU
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem exists_locRing_closedPoint_centre : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (A : Subalgebra ℂ κ'),
    Algebra.Smooth ℂ A → A.toSubring ≤ F.ring.toSubring →
    (∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B), RatRes (algebraMap ℂ κ') B ∧
      A.toSubring ≤ B ∧ B ≤ F.ring.toSubring ∧
      ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro κ' _ _ F A hsm hAF hfrac
    haveI : IsFractionRing A κ' := IsFractionRing.of_field A κ' fun z => by
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac z
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by simp [← e, hb0]⟩
    let ι : A →+* F.ring := (algebraMap A κ').codRestrict F.ring (fun x => hAF x.2)
    let q : Ideal A := (IsLocalRing.maximalIdeal F.ring).comap ι
    have hq : q ≠ ⊤ := by
      intro h
      have h1 : (1 : A) ∈ q := h ▸ Submodule.mem_top
      exact (IsLocalRing.mem_maximalIdeal _).1 (show ι 1 ∈ _ from h1) (by simp)
    obtain ⟨n, hn, hqn⟩ := Ideal.exists_le_maximal q hq
    have hinv : ∀ s ∈ n.primeCompl, ((s : A) : κ')⁻¹ ∈ F.ring := by
      intro s hs
      have hs' : ι s ∉ IsLocalRing.maximalIdeal F.ring := fun h => hs (hqn h)
      have hu : IsUnit (ι s) := by
        by_contra h
        exact hs' ((IsLocalRing.mem_maximalIdeal _).2 h)
      obtain ⟨u, hu⟩ := hu.exists_right_inv
      have e : ((s : A) : κ') * (u : κ') = 1 := congrArg Subtype.val hu
      rw [← eq_inv_of_mul_eq_one_right e]
      exact u.2
    have hle : n.primeCompl ≤ nonZeroDivisors A := n.primeCompl_le_nonZeroDivisors
    let B0 : Subalgebra A κ' := Localization.subalgebra.ofField κ' n.primeCompl hle
    haveI : IsLocalization.AtPrime B0 n := Localization.subalgebra.isLocalization_ofField κ' _ hle
    have hAB : A.toSubring ≤ B0.toSubring := fun x hx => B0.algebraMap_mem (⟨x, hx⟩ : A)
    have hc : ∀ a, algebraMap ℂ κ' a ∈ B0.toSubring := fun a => hAB (A.algebraMap_mem a)
    letI : Algebra ℂ B0 := ((algebraMap A B0).comp (algebraMap ℂ A)).toAlgebra
    haveI : IsScalarTower ℂ A B0 := IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := A) (A := B0) rfl
    have hloc : IsLocalRing B0 := IsLocalization.AtPrime.isLocalRing B0 n
    refine ⟨B0.toSubring, ⟨hc, hloc, ?_, ?_⟩, ?_, hAB, ?_, ?_⟩
    · show (algebraMap ℂ B0).EssFiniteType
      refine RingHom.EssFiniteType.comp ?_ ?_
      · exact RingHom.essFiniteType_algebraMap.2 inferInstance
      · exact RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization B0 n.primeCompl)
    · intro f
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac f
      exact ⟨a, hAB ha, b, hAB hb, hb0, e⟩
    · intro r hr
      let r' : B0 := ⟨r, hr⟩
      letI : Field (A ⧸ n) := Ideal.Quotient.field n
      haveI : Module.Finite ℂ (A ⧸ n) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ n)
      have hsurj : Function.Surjective (algebraMap ℂ (A ⧸ n)) :=
        IsAlgClosed.algebraMap_bijective_of_isIntegral.2
      let e := IsLocalization.AtPrime.equivQuotMaximalIdeal n B0
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm (Ideal.Quotient.mk _ r'))
      obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk n x)
      refine ⟨a, ?_⟩
      let z : B0 := algebraMap A B0 (algebraMap ℂ A a)
      have hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal B0) z = Ideal.Quotient.mk _ r' := by
        rw [← e.apply_symm_apply (Ideal.Quotient.mk _ r'), ← hx, ← ha]
        exact (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk n B0 (algebraMap ℂ A a)).symm
      have hm : r' - z ∈ IsLocalRing.maximalIdeal B0 := Ideal.Quotient.eq.1 hz.symm
      have hnu := (nonUnit_iff (R := B0.toSubring) (r' - z)).2 ((IsLocalRing.mem_maximalIdeal _).1 hm)
      exact hnu
    · rintro x ⟨a, s, hs, rfl⟩
      exact F.ring.toSubring.mul_mem (hAF a.2) (hinv s hs)
    · show (algebraMap ℂ B0).FormallySmooth
      haveI : Algebra.FormallyEtale A B0 := Algebra.FormallyEtale.of_isLocalization n.primeCompl
      haveI : Algebra.FormallySmooth ℂ B0 := Algebra.FormallySmooth.comp ℂ A B0
      exact RingHom.formallySmooth_algebraMap.2 inferInstance

end GlobalTheory.FieldPair
end

section

open GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem finrank_ratF_eq_mul_rank (k K : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [Field K] [CharZero K]
    (ι : k →+* K) (D : ℕ) (x : Fin (D + 1) → K) (hι : Function.Injective ι)
    (hy : AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0)) :
    Module.finrank (ratF x) K = Module.finrank (Subfield.closure (Set.range ι ∪ Set.range fun j : Fin D => x j.succ / x 0)) K * Module.finrank ℤ k ∧ Function.Injective (MvPolynomial.eval₂Hom ι fun j : Fin D => x j.succ / x 0) := by
  classical
  set y : Fin D → K := fun j => x j.succ / x 0 with hydef
  letI : Algebra k K := ι.toAlgebra
  have hyk : AlgebraicIndependent k y := hy.extendScalars_of_isIntegral k
  have hinj : Function.Injective (MvPolynomial.eval₂Hom ι y) := hyk
  refine ⟨?_, hinj⟩
  haveI : CharZero k := ι.charZero
  haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  set F : Subfield K := ratF x with hF
  have hyF : ∀ j, y j ∈ F := fun j => Subfield.subset_closure ⟨j, rfl⟩
  set n := Module.finrank ℤ k with hn
  let b := Module.finBasis ℤ k
  set R : Subring K := Subring.closure (Set.range y) with hRdef
  have hR : R ≤ (MvPolynomial.eval₂Hom (Int.castRingHom K) y).range :=
    (Subring.closure_le).2 (by rintro _ ⟨j, rfl⟩; exact ⟨MvPolynomial.X j, by simp⟩)
  have hli : LinearIndependent F (fun i => ι (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i₀
    have hg' : ∑ i, (g i : K) * ι (b i) = 0 := hg
    have hfrac : ∀ i, ∃ a ∈ R, ∃ c ∈ R, c ≠ 0 ∧ (g i : K) = a / c := by
      intro i
      obtain ⟨a, ha, c, hc, e⟩ := Subfield.mem_closure_iff.1 (g i).2
      by_cases h0 : c = 0
      · exact ⟨0, R.zero_mem, 1, R.one_mem, one_ne_zero, by rw [← e, h0, div_zero, zero_div]⟩
      · exact ⟨a, ha, c, hc, h0, e.symm⟩
    choose a ha c hc hc0 hgac using hfrac
    set Q : K := ∏ j, c j with hQdef
    have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hc0 j
    have hp : ∀ i, Q * (g i : K) = a i * ∏ j ∈ Finset.univ.erase i, c j := by
      intro i
      rw [hgac i, hQdef, ← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i)]
      field_simp [hc0 i]
    have hpR : ∀ i, Q * (g i : K) ∈ R := fun i => by
      rw [hp i]; exact R.mul_mem (ha i) (Subring.prod_mem _ fun j _ => hc j)
    choose P hP using fun i => hR (hpR i)
    have hsum : ∑ i, Q * (g i : K) * ι (b i) = 0 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hg', mul_zero]
    have hcomp : ι.comp (Int.castRingHom k) = Int.castRingHom K := RingHom.ext_int _ _
    have hev : MvPolynomial.eval₂Hom ι y
        (∑ i, MvPolynomial.C (b i) * MvPolynomial.map (Int.castRingHom k) (P i)) = 0 := by

      simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_map_hom, hcomp, hP]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
      ring
    have hP0 := hinj (hev.trans (map_zero _).symm)
    have hPi : ∀ i, P i = 0 := by
      intro i
      ext m
      have hm := congrArg (AddMonoidAlgebra.coeff · m) hP0
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
        MvPolynomial.coeff_zero, Finsupp.zero_apply, eq_intCast] at hm
      have hm' : ∑ j, AddMonoidAlgebra.coeff (P j) m • b j = 0 := by
        rw [← hm]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [zsmul_eq_mul, mul_comm]
      rw [MvPolynomial.coeff_zero]
      exact Fintype.linearIndependent_iff.1 b.linearIndependent _ hm' i
    have h1 : Q * (g i₀ : K) = 0 := by rw [← hP i₀, hPi i₀, map_zero]
    exact Subtype.ext ((mul_eq_zero.1 h1).resolve_left hQ)
  have hV : Module.finrank F (Submodule.span F (Set.range fun i => ι (b i))) = n := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  let E : IntermediateField F K := IntermediateField.adjoin F (Set.range ι)
  have halg : ∀ z ∈ Set.range ι, IsAlgebraic F z := by
    rintro _ ⟨a, rfl⟩
    have h1 : IsIntegral ℤ (ι a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map ι.toIntAlgHom
    exact (h1.tower_top (A := F)).isAlgebraic
  have hEsub : Subalgebra.toSubmodule E.toSubalgebra = Submodule.span F (Set.range fun i => ι (b i)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, Algebra.adjoin_eq_span]
      refine Submodule.span_le.2 ?_
      intro z hz
      have hcl : Submonoid.closure (Set.range ι) ≤ MonoidHom.mrange ι :=
        Submonoid.closure_le.2 (by rintro _ ⟨a, rfl⟩; exact ⟨a, rfl⟩)
      obtain ⟨a, rfl⟩ := hcl hz
      have hsr := b.sum_repr a
      change ι a ∈ _

      rw [← hsr, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul]
      exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => ι (b i)) i)) _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin F _ ⟨b i, rfl⟩
  have hEF : Module.finrank F E = n := by
    have : Module.finrank F E = Module.finrank F (Subalgebra.toSubmodule E.toSubalgebra) := rfl
    rw [this, hEsub, hV]
  have hsub : E.toSubfield = Subfield.closure (Set.range ι ∪ Set.range y) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
      · rintro _ ⟨z, rfl⟩
        exact (Subfield.closure_le.2 (Set.subset_union_right.trans Subfield.subset_closure)) z.2
      · exact Set.subset_union_left.trans Subfield.subset_closure
    · refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
      · exact fun z hz => IntermediateField.subset_adjoin F _ hz
      · rintro _ ⟨j, rfl⟩; exact E.algebraMap_mem ⟨y j, hyF j⟩
  have htow := Module.finrank_mul_finrank F E K
  have hEK : Module.finrank E.toSubfield K = Module.finrank E K := rfl
  rw [← hsub, hEK, ← htow, hEF, mul_comm]

end GlobalTheory.HSAmp
end
