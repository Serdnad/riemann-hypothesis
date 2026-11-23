module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle002
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle010
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Bundle002
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace SectionPairing

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

def pairing (W : Weight L) (n : ℕ) (s t : Fin A.n → X → ℂ) (x : X) : ℂ :=
  conj (s (chartIdx A x) x) * t (chartIdx A x) x *
    ((Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) : ℝ) : ℂ)

theorem mem_chartIdx (x : X) : x ∈ (A.chart (chartIdx A x)).source :=
  Classical.choose_spec (A.cover x)

theorem pairing_eq (W : Weight L) (n : ℕ) {s t : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (ht : t ∈ L.sections n) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    pairing W n s t x = conj (s j x) * t j x * ((Real.exp (-(n : ℝ) * W.φ j x) : ℝ) : ℂ) := by
  have hi := mem_chartIdx (A := A) x
  set i := chartIdx A x
  have hix : x ∈ (A.chart i).source ∩ (A.chart j).source := ⟨hi, hx⟩
  have hg := L.ne_zero i j x hix
  have ha : (0 : ℝ) < ‖L.g i j x‖ ^ 2 := pow_pos (norm_pos_iff.2 hg) 2
  have hexp : Real.exp (-(n : ℝ) * (W.φ j x + Real.log (‖L.g i j x‖ ^ 2))) =
      Real.exp (-(n : ℝ) * W.φ j x) / (‖L.g i j x‖ ^ 2) ^ n := by
    rw [show -(n : ℝ) * (W.φ j x + Real.log (‖L.g i j x‖ ^ 2)) =
        -(n : ℝ) * W.φ j x - n * Real.log (‖L.g i j x‖ ^ 2) by ring, Real.exp_sub,
      Real.exp_nat_mul, Real.exp_log ha]
  have hc : conj (L.g i j x ^ n) * L.g i j x ^ n = (((‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ) := by
    rw [map_pow, ← mul_pow, Complex.conj_mul']
    push_cast
    ring
  have hne : (((‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_pos ha n).ne'
  rw [pairing, hs.2.1 i j x hix, ht.2.1 i j x hix, W.compat i j x hix, hexp]
  calc conj (L.g i j x ^ n * s j x) * (L.g i j x ^ n * t j x) *
        ((Real.exp (-(n : ℝ) * W.φ j x) / (‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ)
      = (conj (L.g i j x ^ n) * L.g i j x ^ n) *
          (conj (s j x) * t j x * ((Real.exp (-(n : ℝ) * W.φ j x) : ℝ) : ℂ)) /
          (((‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ) := by
        rw [map_mul, Complex.ofReal_div]
        ring
    _ = conj (s j x) * t j x * ((Real.exp (-(n : ℝ) * W.φ j x) : ℝ) : ℂ) := by
        rw [hc]
        field_simp

theorem pairing_self (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    pairing W n s s x = ((ptNormSq W n s x : ℝ) : ℂ) := by
  rw [pairing, ptNormSq, Complex.conj_mul']
  push_cast
  ring

theorem continuousAt_of_chart {β : Type*} [TopologicalSpace β] {f : X → β} (j : Fin A.n)
    (hf : ContinuousOn (f ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source))
    {x : X} (hx : x ∈ (A.chart j).source) : ContinuousAt f x := by
  have hy : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hx⟩
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart j).open_source
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    (hf.continuousAt (hopen.mem_nhds hy)).comp ((A.chart j).continuousAt hx)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy
  simp [(A.chart j).left_inv hy]

theorem pairing_continuous (W : Weight L) (n : ℕ) {s t : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) (ht : t ∈ L.sections n) : Continuous (pairing W n s t) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hx := mem_chartIdx (A := A) x
  set j := chartIdx A x
  have h1 : ContinuousAt (s j) x := continuousAt_of_chart j (hs.1 j j).continuousOn hx
  have h2 : ContinuousAt (t j) x := continuousAt_of_chart j (ht.1 j j).continuousOn hx
  have h3 : ContinuousAt (W.φ j) x := continuousAt_of_chart j (W.smooth j j).continuousOn hx
  have h : ContinuousAt
      (fun y ↦ conj (s j y) * t j y * ((Real.exp (-(n : ℝ) * W.φ j y) : ℝ) : ℂ)) x := by
    have h4 : ContinuousAt (fun y ↦ ((Real.exp (-(n : ℝ) * W.φ j y) : ℝ) : ℂ)) x :=
      Complex.continuous_ofReal.continuousAt.comp
        (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul h3))
    exact ((Complex.continuous_conj.continuousAt.comp h1).mul h2).mul h4
  refine h.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy
  exact (pairing_eq W n hs ht j hy).symm

theorem ptNormSq_continuous (W : Weight L) (n : ℕ) {s : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) : Continuous (ptNormSq W n s) := by
  have h := Complex.continuous_re.comp (pairing_continuous W n hs hs)
  refine h.congr fun x ↦ ?_
  simp [pairing_self]

theorem ptNormSq_nonneg (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    0 ≤ ptNormSq W n s x := by
  unfold ptNormSq
  positivity

variable [MeasurableSpace X] [BorelSpace X]

theorem isOpenPosMeasure (dV : SmoothVolume A) : dV.μ.IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 ↦ ?_⟩
  obtain ⟨x, hxU⟩ := hne
  have hx := mem_chartIdx (A := A) x
  set j := chartIdx A x
  set T := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U
  have hTo : IsOpen T := (A.chart j).isOpen_inter_preimage_symm hU
  have hTx : A.chart j x ∈ T :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hxU⟩
  have hlin := dV.chart_lintegral j (U.indicator 1) (measurable_one.indicator hU.measurableSet)
  have hleft : ∫⁻ x in (A.chart j).source, U.indicator 1 x ∂dV.μ = 0 := by
    rw [lintegral_indicator_one hU.measurableSet, Measure.restrict_apply hU.measurableSet]
    exact measure_mono_null inter_subset_left h0
  have hT : ∫⁻ y in T, ENNReal.ofReal (dV.dens j y) = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ y in T, ENNReal.ofReal (dV.dens j y)
        = ∫⁻ y in T, U.indicator 1 ((A.chart j).symm y) * ENNReal.ofReal (dV.dens j y) :=
          setLIntegral_congr_fun hTo.measurableSet fun y hy ↦ by
            rw [Set.indicator_of_mem (show (A.chart j).symm y ∈ U from hy.2), Pi.one_apply, one_mul]
      _ ≤ ∫⁻ y in (A.chart j).target,
            U.indicator 1 ((A.chart j).symm y) * ENNReal.ofReal (dV.dens j y) :=
          lintegral_mono_set inter_subset_left
      _ = 0 := by rw [← hlin, hleft]
  have hmeas : AEMeasurable (fun y ↦ ENNReal.ofReal (dV.dens j y)) (volume.restrict T) :=
    (((dV.smooth j).continuousOn.mono inter_subset_left).aemeasurable
      hTo.measurableSet).ennreal_ofReal
  have hae := (lintegral_eq_zero_iff' hmeas).1 hT
  rw [Filter.EventuallyEq, ae_restrict_iff' hTo.measurableSet] at hae
  have hzero : volume T = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with y hy hyT
    have := hy hyT
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
    exact absurd (dV.pos j y hyT.1) (not_lt.2 this)
  exact (hTo.measure_pos volume ⟨_, hTx⟩).ne' hzero

end SectionPairing

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem ComplexFormsOnPoints.proof (hR : PrimeComplexRadical.Statement)
    (hM : ComplexMinimalPrimesContract.Statement) : ComplexFormsOnPoints.Statement := by
  intro K _ ι _ P hP hrel F hF
  have hrad := hR (Σ k, ι k) P hP
  apply hrad
  rw [← Ideal.sInf_minimalPrimes]
  refine Ideal.mem_sInf.2 fun {Q} hQ => ?_
  have hQp : Q.IsPrime := hQ.1.1
  have hc := hM (Σ k, ι k) P hP Q hQ
  choose i hi using hrel

  let h0 : MRing ι := ∏ k, X ⟨k, i k⟩
  have h0P : h0 ∉ P := by
    intro hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 hmem
    exact hi k hk
  have hQh : map (Int.castRingHom ℂ) h0 ∉ Q := by
    intro hmem
    apply h0P
    rw [← hc]
    exact Ideal.mem_comap.2 hmem
  have hPQ : ∀ f ∈ P, map (Int.castRingHom ℂ) f ∈ Q := by
    intro f hf
    rw [← hc] at hf
    exact Ideal.mem_comap.1 hf
  have hv : F * map (Int.castRingHom ℂ) h0 ∈ vanishingIdeal ℂ (zeroLocus ℂ Q) := by
    rw [mem_vanishingIdeal_iff]
    intro z hz
    have hz : ∀ p ∈ Q, eval z p = 0 := hz
    change eval z _ = 0
    have hzh : eval z (map (Int.castRingHom ℂ) h0) = ∏ k, z ⟨k, i k⟩ := by
      simp [h0, map_prod]
    by_cases h0z : eval z (map (Int.castRingHom ℂ) h0) = 0
    · rw [map_mul, h0z, mul_zero]
    · have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := by
        rw [hzh] at h0z
        exact fun k => Finset.prod_ne_zero_iff.1 h0z k (Finset.mem_univ k)
      have hzP : z ∈ mcPts P := ⟨fun k => ⟨i k, hne k⟩, fun f hf => hz _ (hPQ f hf)⟩
      rw [map_mul, hF z hzP, zero_mul]
  rw [vanishingIdeal_zeroLocus_eq_radical, hQp.radical] at hv
  exact (hQp.mem_or_mem hv).resolve_right hQh

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights
  GroundTheory.Heights₂.Heights.CP

noncomputable section

def PolydiscSubmean.Statement : Prop :=
  ∀ (D n : ℕ) (lam : Fin D → ℝ) (R : ℝ) (f : (Fin D → ℂ) → ℂ), 0 < n → 0 < R →
    (∀ j, 0 ≤ lam j) → AnalyticOnNhd ℂ f (Metric.closedBall 0 (R / Real.sqrt n)) →
    ‖f 0‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R ≤
      ∫ z in Metric.closedBall (0 : Fin D → ℂ) (R / Real.sqrt n),
        ‖f z‖ ^ 2 * Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2)

def LocalBergmanBound.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), W.IsSemipositive →
    ∀ (V : ℕ → Submodule ℂ (Fin A.n → X → ℂ)) [∀ n, FiniteDimensional ℂ (V n)],
      (∀ n, V n ≤ L.sections n) → ∀ (x : X) (ε : ℝ), 0 < ε →
        ∀ᶠ n : ℕ in atTop, bergman W dV (V n) n x ≤ (bergmanDens W dV x + ε) * (n : ℝ) ^ D

def UniformBergmanBound.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A), W₀.IsSemipositive → W₁.IsSemipositive →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V], V ≤ L.sections n →
        ∀ x : X, bergman (W₀.lerp W₁ t) dV V n x ≤ C * (n : ℝ) ^ D

def IntegralOfBergman.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A) (n : ℕ) (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V],
    V ≤ L.sections n → ∫ x, bergman W dV V n x ∂dV.μ = Module.finrank ℂ V

def L1Convergence.Statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (g : ℕ → Ω → ℝ)
    (b : Ω → ℝ) (C : ℝ), (∀ n, Integrable (g n) μ) → Integrable b μ →
    (∀ n x, 0 ≤ g n x ∧ g n x ≤ C) →
    (∀ (x : Ω) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, g n x ≤ b x + ε) →
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∫ x, b x ∂μ - ε ≤ ∫ x, g n x ∂μ) →
    Tendsto (fun n => ∫ x, |g n x - b x| ∂μ) atTop (𝓝 0)

def BergmanL1Convergence.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), W.IsSemipositive →
    ∀ (V : ℕ → Submodule ℂ (Fin A.n → X → ℂ)) [∀ n, FiniteDimensional ℂ (V n)],
      (∀ n, V n ≤ L.sections n) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (∫ x, bergmanDens W dV x ∂dV.μ - ε) * (n : ℝ) ^ D ≤ Module.finrank ℂ (V n)) →
      Tendsto (fun n : ℕ => ∫ x, |((n : ℝ) ^ D)⁻¹ * bergman W dV (V n) n x - bergmanDens W dV x|
        ∂dV.μ) atTop (𝓝 0)

lemma lerp_self_φ {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) (t : ℝ) : (W.lerp W t).φ = W.φ := by
  funext j x
  simp [Weight.lerp]

def MetricChange.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A), W₀.IsSemipositive → W₁.IsSemipositive →
    ∀ (V : ℕ → Submodule ℂ (Fin A.n → X → ℂ)) [∀ n, FiniteDimensional ℂ (V n)],
      (∀ n, V n ≤ L.sections n) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (∫ x, bergmanDens (W₀.lerp W₁ t) dV x ∂dV.μ - ε) * (n : ℝ) ^ D ≤
          Module.finrank ℂ (V n)) →
      ∀ (e : ∀ n, Module.Basis (Fin (Module.finrank ℂ (V n))) ℂ (V n)) (ε : ℝ), 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          |chiGram W₁ dV n (fun a => (e n a : Fin A.n → X → ℂ)) -
              chiGram W₀ dV n (fun a => (e n a : Fin A.n → X → ℂ)) -
            (n : ℝ) ^ (D + 1) / 2 * ∫ t in (0 : ℝ)..1,
              ∫ x, Weight.diff W₁ W₀ x * bergmanDens (W₀.lerp W₁ t) dV x ∂dV.μ| ≤
            ε * (n : ℝ) ^ (D + 1)

def SupNormAgainstL2.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), W.IsSemipositive →
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ s ∈ L.sections n, ∀ x : X,
      Real.sqrt (ptNormSq W n s x) ≤ C * Real.sqrt ((n : ℝ) ^ D) * Real.sqrt (sectionL2NormSq W dV n s)) ∧
    ∀ (n : ℕ), ∀ s ∈ L.sections n, ∀ M : ℝ, (∀ x : X, Real.sqrt (ptNormSq W n s x) ≤ M) →
      Real.sqrt (sectionL2NormSq W dV n s) ≤ M

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RatioFieldDeg

variable {ι : Type}

def quotCone {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ)) (hu : coordIdeal ℤ u = I) :
    MvPolynomial ι ℤ ⧸ I →+* Polynomial E :=
  Ideal.Quotient.lift I (coneMap ℤ u).toRingHom (fun a ha => by rw [← hu] at ha; exact ha)

theorem quotCone_injective {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) : Function.Injective (quotCone u I hu) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem, ← hu, coordIdeal, RingHom.mem_ker]
  simpa [quotCone] using ha

theorem isDomain_quot {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) : IsDomain (MvPolynomial ι ℤ ⧸ I) :=
  Function.Injective.isDomain _ (quotCone_injective u I hu)

theorem charZero_frac {E : Type} [Field E] [CharZero E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) [IsDomain (MvPolynomial ι ℤ ⧸ I)] :
    CharZero (FractionRing (MvPolynomial ι ℤ ⧸ I)) := by
  have hg : Function.Injective ((algebraMap (Polynomial E) (RatFunc E)).comp (quotCone u I hu)) :=
    (IsFractionRing.injective (Polynomial E) (RatFunc E)).comp (quotCone_injective u I hu)
  refine ⟨fun n m h => ?_⟩
  have h' := congrArg (IsFractionRing.lift hg) h
  simp only [map_natCast] at h'
  exact Nat.cast_injective h'

section

variable (I : Ideal (MvPolynomial ι ℤ)) [IsDomain (MvPolynomial ι ℤ ⧸ I)]

def coord (i : ι) : FractionRing (MvPolynomial ι ℤ ⧸ I) :=
  algebraMap _ _ (Ideal.Quotient.mk I (X i))

variable [CharZero (FractionRing (MvPolynomial ι ℤ ⧸ I))]

def ratField {κ : Type} (s : κ → ι) : IntermediateField ℚ (FractionRing (MvPolynomial ι ℤ ⧸ I)) :=
  IntermediateField.adjoin ℚ {t | ∃ k l, t = coord I (s k) / coord I (s l)}

theorem projDeg_eq {E : Type} [Field E] [CharZero E] (u : ι → E) (hu : coordIdeal ℤ u = I) {D : ℕ}
    (e : Fin (D + 1) → ι) :
    projDeg u e = IntermediateField.relfinrank (ratField I e) (ratField I id) := by
  have hg : Function.Injective ((algebraMap (Polynomial E) (RatFunc E)).comp (quotCone u I hu)) :=
    (IsFractionRing.injective (Polynomial E) (RatFunc E)).comp (quotCone_injective u I hu)
  let f : FractionRing (MvPolynomial ι ℤ ⧸ I) →ₐ[ℚ] RatFunc E := (IsFractionRing.lift hg).toRatAlgHom
  let c : E →ₐ[ℚ] RatFunc E := (RatFunc.C : E →+* RatFunc E).toRatAlgHom
  have hx : ∀ i, f (coord I i) = RatFunc.C (u i) * RatFunc.X := by
    intro i
    simp [f, coord, IsFractionRing.lift_algebraMap, quotCone, coneMap, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X]
  have hr : ∀ i j, f (coord I i / coord I j) = c (u i / u j) := by
    intro i j
    rw [map_div₀, hx, hx, mul_div_mul_right _ _ RatFunc.X_ne_zero]
    simp [c, map_div₀]
  have hmap : ∀ {κ : Type} (s : κ → ι), (ratField I s).map f = (fnField (u ∘ s)).map c := by
    intro κ s
    rw [ratField, fnField, IntermediateField.adjoin_map, IntermediateField.adjoin_map]
    congr 1
    ext t
    simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply]
    constructor
    · rintro ⟨_, ⟨k, l, rfl⟩, rfl⟩
      exact ⟨_, ⟨k, l, rfl⟩, (hr _ _).symm⟩
    · rintro ⟨_, ⟨k, l, rfl⟩, rfl⟩
      exact ⟨_, ⟨k, l, rfl⟩, hr _ _⟩
  rw [← IntermediateField.relfinrank_map_map (ratField I e) (ratField I id) f, hmap, hmap,
    IntermediateField.relfinrank_map_map]
  rfl

end

theorem proof : RatioFieldDeg.Statement := by
  intro ι E₁ E₂ _ _ _ _ u v D e h
  have : IsDomain (MvPolynomial ι ℤ ⧸ coordIdeal ℤ u) := isDomain_quot u _ rfl
  have : CharZero (FractionRing (MvPolynomial ι ℤ ⧸ coordIdeal ℤ u)) := charZero_frac u _ rfl
  rw [projDeg_eq (coordIdeal ℤ u) u rfl e, projDeg_eq (coordIdeal ℤ u) v h.symm e]

end RatioFieldDeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section


open Classical in
def projMat {κ : Type} {D : ℕ} (e : Fin (D + 1) → Ix κ) : ∀ _ : Unit, Fin (D + 1) → κ → ℤ :=
  fun _ k i => if (e k).2 = i then 1 else 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def segreCoords {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [CommRing Ω] (y : (Σ k, ι k) → Ω) :
    Ix ((k : K) → ι k) → Ω :=
  fun p => ∏ k, y ⟨k, p.2 k⟩

def SegreArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) →
    IsArithVar (ι := GlobalTheory ((k : K) → ι k)) (coordIdeal ℤ (segreCoords y)) (D + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
