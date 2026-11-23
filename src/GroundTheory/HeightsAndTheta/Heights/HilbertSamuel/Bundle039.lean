module

import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensChartSum
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle013
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle036
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmoothChartVolume
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqSumMultihomogeneousComponents
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.A
open scoped ENNReal ContDiff ComplexConjugate Matrix

noncomputable section

namespace BergmanDensIntegrable

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem weight_contDiffOn {L : HolLineBundle A} (W : Weight L) (j : Fin A.n) :
    ContDiffOn ℝ ∞ (W.φ j ∘ (A.chart j).symm) (A.chart j).target :=
  (W.smooth j j).mono fun _ hy => ⟨hy, (A.chart j).map_target hy⟩

theorem trans_source_eq (j k : Fin A.n) :
    ((A.chart j).symm.trans (A.chart k)).source =
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]

theorem trans_target_eq (j k : Fin A.n) :
    ((A.chart j).symm.trans (A.chart k)).target =
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source := by
  rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target]

theorem trans_analytic (j k : Fin A.n) :
    AnalyticOnNhd ℂ ((A.chart j).symm.trans (A.chart k))
      ((A.chart j).symm.trans (A.chart k)).source := by
  rw [trans_source_eq, OpenPartialHomeomorph.coe_trans]
  exact A.holo j k

theorem hessC_weight_trans {L : HolLineBundle A} (W : Weight L) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    hessC (W.φ j ∘ (A.chart j).symm) y =
      (jacC ((A.chart j).symm.trans (A.chart k)) y)ᵀ *
        hessC (W.φ k ∘ (A.chart k).symm) (((A.chart j).symm.trans (A.chart k)) y) *
        (jacC ((A.chart j).symm.trans (A.chart k)) y).map (starRingEnd ℂ) := by
  apply GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.hessC_weight_trans <;> assumption

theorem chernTopDens_trans {L : HolLineBundle A} (W : Weight L) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    chernTopDens W j y = Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det *
      chernTopDens W k (((A.chart j).symm.trans (A.chart k)) y) := by
  unfold chernTopDens
  rw [hessC_weight_trans W j k hy]
  set J := jacC ((A.chart j).symm.trans (A.chart k)) y
  set H := hessC (W.φ k ∘ (A.chart k).symm) (((A.chart j).symm.trans (A.chart k)) y)
  set c : ℂ := ((1 / Real.pi : ℝ) : ℂ)
  have h1 : c • (Jᵀ * H * J.map (starRingEnd ℂ)) = Jᵀ * (c • H) * J.map (starRingEnd ℂ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have h2 : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h2,
    show J.det * (c • H).det * starRingEnd ℂ J.det = ((Complex.normSq J.det : ℝ) : ℂ) * (c • H).det by
      rw [← Complex.mul_conj]; ring,
    Complex.re_ofReal_mul]
  ring

variable [MeasurableSpace X] [BorelSpace X]

theorem lintegral_dens_trans (dV : SmoothVolume A) (j k : Fin A.n)
    (f : (Fin D → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in ((A.chart j).symm.trans (A.chart k)).source, f y * ENNReal.ofReal (dV.dens j y) =
      ∫⁻ y in ((A.chart j).symm.trans (A.chart k)).source,
        ENNReal.ofReal (Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det) *
          (f y * ENNReal.ofReal (dV.dens k (((A.chart j).symm.trans (A.chart k)) y))) := by
  apply GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.lintegral_dens_trans <;> assumption


omit [MeasurableSpace X] [BorelSpace X] in
theorem jacC_trans_continuousOn (j k : Fin A.n) :
    ContinuousOn (jacC ((A.chart j).symm.trans (A.chart k)))
      ((A.chart j).symm.trans (A.chart k)).source := by
  have h := (trans_analytic (A := A) j k).fderiv.continuousOn
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  exact (continuous_apply a).comp_continuousOn
    ((ContinuousLinearMap.apply ℂ _ (Pi.single b 1)).continuous.comp_continuousOn h)

theorem dens_trans (dV : SmoothVolume A) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    dV.dens j y = Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det *
      dV.dens k (((A.chart j).symm.trans (A.chart k)) y) := by
  apply GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.dens_trans <;> assumption

variable {L : HolLineBundle A}

def densIn (W : Weight L) (dV : SmoothVolume A) (j : Fin A.n) (x : X) : ℝ :=
  chernTopDens W j (A.chart j x) / ((D.factorial : ℝ) * dV.dens j (A.chart j x))

theorem densIn_eq (W : Weight L) (dV : SmoothVolume A) (j k : Fin A.n) {x : X}
    (hx : x ∈ (A.chart j).source ∩ (A.chart k).source) :
    densIn W dV j x = densIn W dV k x := by
  have hy : A.chart j x ∈ ((A.chart j).symm.trans (A.chart k)).source := by
    rw [trans_source_eq]
    exact ⟨(A.chart j).map_source hx.1,
      Set.mem_preimage.2 (by rw [(A.chart j).left_inv hx.1]; exact hx.2)⟩
  have hT : ((A.chart j).symm.trans (A.chart k)) (A.chart j x) = A.chart k x := by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, (A.chart j).left_inv hx.1]
  have hc := chernTopDens_trans W j k hy
  have hd := dens_trans dV j k hy
  rw [hT] at hc hd
  set n := Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) (A.chart j x)).det
  have hpos : 0 < dV.dens j (A.chart j x) := dV.pos j _ ((A.chart j).map_source hx.1)
  have hn : n ≠ 0 := by
    intro h0; rw [hd, h0, zero_mul] at hpos; exact lt_irrefl 0 hpos
  unfold densIn
  rw [hc, hd, show (D.factorial : ℝ) * (n * dV.dens k (A.chart k x)) =
    n * ((D.factorial : ℝ) * dV.dens k (A.chart k x)) by ring, mul_div_mul_left _ _ hn]


omit [BorelSpace X] in
theorem densIn_continuousAt (W : Weight L) (dV : SmoothVolume A) (j : Fin A.n) {x : X}
    (hx : x ∈ (A.chart j).source) : ContinuousAt (densIn W dV j) x := by
  have hy : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hx
  have hnhds : (A.chart j).target ∈ 𝓝 (A.chart j x) := (A.chart j).open_target.mem_nhds hy
  have hH : ContinuousAt (hessC (W.φ j ∘ (A.chart j).symm)) (A.chart j x) :=
    (hessC_continuousOn _ _ (A.chart j).open_target
      ((weight_contDiffOn W j).of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp |
        exact WithTop.coe_le_coe.2 le_top))).continuousAt hnhds
  have hdet : Continuous fun M : Matrix (Fin D) (Fin D) ℂ =>
      (D.factorial : ℝ) * ((((1 / Real.pi : ℝ) : ℂ) • M).det).re := by fun_prop
  have hC : ContinuousAt (chernTopDens W j) (A.chart j x) := hdet.continuousAt.comp hH
  have hdens : ContinuousAt (dV.dens j) (A.chart j x) :=
    (dV.smooth j).continuousOn.continuousAt hnhds
  have hc := (A.chart j).continuousAt hx
  refine (hC.comp hc).div (continuousAt_const.mul (hdens.comp hc)) ?_
  exact mul_ne_zero (by exact_mod_cast (Nat.factorial_pos D).ne') (dV.pos j _ hy).ne'

theorem bergmanDens_continuous (W : Weight L) (dV : SmoothVolume A) :
    Continuous (bergmanDens W dV) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hx : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hev : densIn W dV (chartIdx A x) =ᶠ[𝓝 x] bergmanDens W dV := by
    filter_upwards [(A.chart (chartIdx A x)).open_source.mem_nhds hx] with x' hx'
    exact densIn_eq W dV _ _ ⟨hx', Classical.choose_spec (A.cover x')⟩
  exact (densIn_continuousAt W dV _ hx).congr hev

end BergmanDensIntegrable

theorem BergmanDensIntegrable.proof : BergmanDensIntegrable.Statement := by
  intro D X _ _ _ _ _ A L W dV
  have := dV.isProb
  exact integrableOn_univ.1
    ((BergmanDensIntegrable.bergmanDens_continuous W dV).continuousOn.integrableOn_compact
      isCompact_univ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreRepresentatives

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] in
theorem isMultiHomog_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {f : MRingOver R ι}
    {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (map φ f : MRingOver S ι) a :=
  fun m hm => hf m (support_map_subset φ f hm)


omit [Fintype K] in
theorem isMultiHomog_lincomb {f g : MRingOver ℂ ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) (c d : ℂ) : IsMultiHomog (C c * f - C d * g) a := by
  classical
  intro m hm
  rw [C_mul', C_mul'] at hm
  rcases Finset.mem_union.1 (support_sub _ _ _ hm) with h | h
  · exact hf m (support_smul h)
  · exact hg m (support_smul h)

theorem eval_smul {s : MRingOver ℂ ι} {a : K → ℕ} (hs : IsMultiHomog s a) (r : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : eval (fun p => r p.1 * z p) s = (∏ k, r k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ p : (Σ k, ι k), r p.1 ^ d p) = ∏ k, r k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, r k ^ d ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem eval_eq_zero_of_homog {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ f ∈ mCoordIdeal y, (∃ a, IsMultiHomog f a) → eval z (map (Int.castRingHom ℂ) f) = 0)
    (f : MRing ι) (hf : f ∈ mCoordIdeal y) : eval z (map (Int.castRingHom ℂ) f) = 0 := by

  rw [eq_sum_multihomogeneous_components f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun b _ => hz _ ?_ ⟨b, isMultiHomog_i2comp b f⟩
  exact i2comp_mem (CoordinateConeArithVar.isMultiHomogIdeal y) b hf

end FibreRepresentatives


open FibreRepresentatives in
theorem FibreRepresentatives.proof (h : AvoidFormFinite.Statement) : FibreRepresentatives.Statement := by
  intro K _ ι _ Ω _ y D e L he hL hL0 ζ
  classical
  set Lc : Fin (D + 1) → MRingOver ℂ ι := fun j => map (Int.castRingHom ℂ) (L j) with hLc
  by_cases hζ : ζ = 0
  · refine ⟨∅, by simp, fun z hz ⟨t, ht⟩ => ?_⟩
    obtain ⟨j, hj⟩ := hL0 z hz
    exact absurd (by simpa [hζ] using ht j) hj
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ζ j₀ ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hζ (funext hne)
  let S : Set (MRingOver ℂ ι) :=
    {g | ∃ f ∈ mCoordIdeal y, (∃ a, IsMultiHomog f a) ∧ g = map (Int.castRingHom ℂ) f} ∪
      Set.range fun j => C (ζ j₀) * Lc j - C (ζ j) * Lc j₀

  have key : ∀ z : (Σ k, ι k) → ℂ, ((∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval z s = 0) ↔
      (z ∈ mcPts (mCoordIdeal y) ∧ ∃ t : ℂ, ∀ j, eval z (Lc j) = t * ζ j) := by
    intro z
    constructor
    · rintro ⟨hb, hS⟩
      refine ⟨⟨hb, eval_eq_zero_of_homog y z fun f hf ha => hS _ (Or.inl ⟨f, hf, ha, rfl⟩)⟩,
        eval z (Lc j₀) / ζ j₀, fun j => ?_⟩
      have h1 := hS _ (Or.inr ⟨j, rfl⟩)
      simp only [map_sub, map_mul, eval_C] at h1
      field_simp
      linear_combination h1
    · rintro ⟨hz, t, ht⟩
      refine ⟨hz.1, fun s hs => ?_⟩
      rcases hs with ⟨f, hf, -, rfl⟩ | ⟨j, rfl⟩
      · exact hz.2 f hf
      · simp only [map_sub, map_mul, eval_C, ht]
        ring
  have hSh : ∀ s ∈ S, ∃ a, IsMultiHomog s a := by
    rintro s (⟨f, -, ⟨a, ha⟩, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨a, isMultiHomog_map _ ha⟩
    · exact ⟨e, isMultiHomog_lincomb (isMultiHomog_map _ (hL j)) (isMultiHomog_map _ (hL j₀)) _ _⟩
  have hG : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) →
      eval z (Lc j₀) ≠ 0 := by
    intro z hb hS h0
    obtain ⟨hz, t, ht⟩ := (key z).1 ⟨hb, hS⟩
    have ht0 : t = 0 := by
      have := ht j₀
      rw [h0] at this
      exact (mul_eq_zero.1 this.symm).resolve_right hj₀
    obtain ⟨j, hj⟩ := hL0 z hz
    exact hj (by simpa [hLc, ht0] using ht j)
  obtain ⟨T, hT⟩ := h K ι S (Lc j₀) e he (isMultiHomog_map _ (hL j₀)) hSh hG
  refine ⟨T.filter fun t => (∀ k, ∃ i, t ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval t s = 0, fun z hz => ?_,
    fun z hz hfib => ?_⟩
  · exact (key z).1 (Finset.mem_filter.1 hz).2
  · obtain ⟨hb, hS⟩ := (key z).2 ⟨hz, hfib⟩
    obtain ⟨t, htT, r, hr, rfl⟩ := hT z hb hS
    have hinv : t = fun p => (r p.1)⁻¹ * (r p.1 * t p) := by
      funext p
      rw [← mul_assoc, inv_mul_cancel₀ (hr p.1), one_mul]
    refine ⟨t, Finset.mem_filter.2 ⟨htT, fun k => ?_, fun s hs => ?_⟩, r, hr, rfl⟩
    · obtain ⟨i, hi⟩ := hb k
      exact ⟨i, fun h0 => hi (by simp [h0])⟩
    · obtain ⟨a, ha⟩ := hSh s hs
      rw [hinv, eval_smul ha (fun k => (r k)⁻¹), hS s hs, mul_zero]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem ClosedPtFibreLift.proof (hG : GradedSubmodules.Statement) (hSES : KH.CechSESStatement)
    (hSky : ClosedPtSkyscraper.Statement) (hKer : LocIdealKer.Statement) : ClosedPtFibreLift.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d _ _ h𝓜 hP hH1 I hI x hx
  have hPh : IsMultiHomogIdeal P := hP.1.2.1
  obtain ⟨h𝓝', h𝓝''⟩ := (hG S K ι M 𝓜 h𝓜).2 P hPh

  have hyd : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ x ∈
      KH.locPart ι (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) (KH.cellMon S I.1) d := by
    obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx
    rw [GenSESStep.locMap_mk]
    exact GenSESStep.mk_mem_locPart _ t a ht ⟨m, hm, rfl⟩

  have hkill : ∀ p ∈ P, ∀ n : M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M), p • n = 0 := by
    intro p hp n
    induction n using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hp Submodule.mem_top

  obtain ⟨z'', hz'', hz''I⟩ := hSky S K ι _ _ P d h𝓝'' hP hkill I hI _ hyd

  have hg : KH.IsMGradedMap S ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) 𝓜
      (P • ⊤ : Submodule (MRingOver S ι) M).subtype := fun _ _ hm => hm
  have hh : KH.IsMGradedMap S ι 𝓜 (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M))
      (P • ⊤ : Submodule (MRingOver S ι) M).mkQ := fun _ m hm => ⟨m, hm, rfl⟩
  obtain ⟨z, hz, hzmap⟩ := (hSES S K ι _ M _ _ 𝓜 _ _ _ h𝓝' h𝓜 h𝓝'' hg hh
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) d 0).2.2.2.2.1 hH1 z'' hz''
  refine ⟨z, hz, ?_⟩
  have hzI : z I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d := Submodule.mem_pi.mp hz.1 I (Set.mem_univ _)

  refine (hKer S K ι M 𝓜 P (KH.cellMon S I.1) d h𝓜 hPh (fun _ ht => GenSESStep.cellMon_homog ht) _
    (sub_mem hx hzI)).2 ?_
  have e : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = z'' I :=
    congrFun hzmap I
  rw [map_sub]
  change _ - GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = 0
  rw [e, hz''I, sub_self]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem PullRatiosAlgebraic.proof (h₁ : PullConeNull.Statement) (h₂ : PullConeDegree.Statement)
    (h₃ : PullGradedAlgebraic.Statement) : PullRatiosAlgebraic.Statement := by
  intro K _ ι _ Ω _ _ y D e L hy he hL hz
  obtain ⟨N, hN⟩ := h₁ K ι Ω y D L hz
  exact h₃ K ι Ω y D e L (fun k => e k + N * Fintype.card (ι k)) hy he hL
    (fun d g hg hd => h₂ K ι Ω y D e L N hy hL hN d g hg hd)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormGoodPrimeIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ (p : ℕ) (hp : p.Prime), ¬ HasCommonZeroModP y L p hp →
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
        (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
          ∀ m : Fin (D + 1) →₀ ℕ, 0 ≤ padicValRat p ((c (Module.finrank (pullField y L) Ω)).coeff m)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelChartPoly.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (R : Subalgebra ℤ Ω)
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k),
    ∀ σ ∈ Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩),
      ∃ N : ℕ, σ * (∏ k, y ⟨k, c k⟩) ^ N ∈ relSecM R y (fun _ => N)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem ResVolume.proof : ResVolume.Statement := by
  intro K _ ι _ P J e R _ _ hP
  obtain ⟨z, hzP, hzJ⟩ := exists_mcPts_not_mem_mcPts hP R.nondeg
  obtain ⟨x, -⟩ := R.surj z hzP hzJ
  have : Nonempty R.X := ⟨x⟩
  exact ChartVolume.exists_isSmoothVolume R.A

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
