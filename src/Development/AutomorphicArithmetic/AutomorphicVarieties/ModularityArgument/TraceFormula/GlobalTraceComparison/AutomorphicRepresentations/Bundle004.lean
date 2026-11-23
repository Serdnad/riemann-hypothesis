module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle070
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory Filter Topology

private lemma flip_half (β : ℝ → ℝ) (hi : Integrable β) (h1 : ∫ t, β t = 1) (c : ℝ) :
    Integrable (fun s : ℝ => β (-(s + c) - s)) ∧ ∫ s : ℝ, β (-(s + c) - s) = 1 / 2 := by
  have e : ∀ s : ℝ, β (-(s + c) - s) = (fun y => β (y - c)) ((-2 : ℝ) * s) := by
    intro s
    show β _ = β _
    congr 1
    ring
  have hg : Integrable (fun y => β (y - c)) := hi.comp_sub_right c
  refine ⟨?_, ?_⟩
  · simp_rw [e]
    exact hg.comp_mul_left' (by norm_num)
  · simp_rw [e]
    rw [Measure.integral_comp_mul_left (fun y => β (y - c)) (-2 : ℝ),
      integral_sub_right_eq_self β c, h1]
    norm_num

private lemma flip_core {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z] (ν : Measure X) [SFinite ν]
    (μ : Measure Z) [SFinite μ] (l : X → ℝ) (l' : Z → ℝ) (F : ℝ → X → ℂ) (m : Z → ℂ) (d : X → ℝ)
    (hl : Measurable l) (hl' : Measurable l') (hF : Measurable (Function.uncurry F))
    (hm : Integrable m μ) (hd : Integrable d ν)
    (hb : ∀ s x, |s - l x| ≤ 1 → ‖F s x‖ ≤ d x)
    (hh : ∀ (s : ℝ) (u : ℝ → ℂ), Continuous u → HasCompactSupport u →
      ∫ x, F s x * u (l x) ∂ν = ∫ z, m z * u (-(s + l' z)) ∂μ)
    (β : ℝ → ℝ) (hc : Continuous β) (hs : HasCompactSupport β) (h0 : ∀ t, 0 ≤ β t)
    (h1 : ∫ t, β t = 1) (hr : ∀ t, β t ≠ 0 → |t| ≤ 1) :
    Integrable (fun x => ∫ s : ℝ, F s x * (β (l x - s) : ℂ)) ν ∧
      (∀ x, ‖∫ s : ℝ, F s x * (β (l x - s) : ℂ)‖ ≤ d x) ∧
      ∫ x, (∫ s : ℝ, F s x * (β (l x - s) : ℂ)) ∂ν = (∫ z, m z ∂μ) / 2 := by
  have hi : Integrable β := hc.integrable_of_hasCompactSupport hs
  have hd0 : ∀ x, 0 ≤ d x := fun x => (norm_nonneg _).trans (hb (l x) x (by simp))
  have hpt : ∀ x s, ‖F s x * (β (l x - s) : ℂ)‖ ≤ d x * β (l x - s) := by
    intro x s
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _)]
    by_cases h : β (l x - s) = 0
    · simp [h]
    · have := hr _ h
      rw [abs_sub_comm] at this
      exact mul_le_mul_of_nonneg_right (hb s x this) (h0 _)
  have hmeas : Measurable (fun p : X × ℝ => F p.2 p.1 * (β (l p.1 - p.2) : ℂ)) := by
    have a : Measurable (fun p : X × ℝ => F p.2 p.1) :=
      hF.comp (measurable_snd.prodMk measurable_fst)
    have b : Measurable (fun p : X × ℝ => β (l p.1 - p.2)) :=
      hc.measurable.comp ((hl.comp measurable_fst).sub measurable_snd)
    exact a.mul (Complex.measurable_ofReal.comp b)
  have hsec : ∀ x, Integrable (fun s : ℝ => F s x * (β (l x - s) : ℂ)) := by
    intro x
    have hmaj : Integrable (fun s : ℝ => d x * β (l x - s)) := (hi.comp_sub_left (l x)).const_mul _
    refine hmaj.mono' ?_ (Eventually.of_forall fun s => hpt x s)
    exact (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hle : ∀ x, ∫ s : ℝ, ‖F s x * (β (l x - s) : ℂ)‖ ≤ d x := by
    intro x
    have hmaj : Integrable (fun s : ℝ => d x * β (l x - s)) := (hi.comp_sub_left (l x)).const_mul _
    calc ∫ s : ℝ, ‖F s x * (β (l x - s) : ℂ)‖ ≤ ∫ s : ℝ, d x * β (l x - s) :=
          integral_mono (hsec x).norm hmaj (fun s => hpt x s)
      _ = d x := by
          rw [integral_const_mul, integral_sub_left_eq_self β volume (l x), h1, mul_one]
  have hprod : Integrable (fun p : X × ℝ => F p.2 p.1 * (β (l p.1 - p.2) : ℂ)) (ν.prod volume) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall hsec, ?_⟩
    refine hd.mono' hmeas.aestronglyMeasurable.norm.integral_prod_right' (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hle x
  refine ⟨hprod.integral_prod_left, fun x => (norm_integral_le_integral_norm _).trans (hle x), ?_⟩
  have hsw := integral_integral_swap (f := fun x (s : ℝ) => F s x * (β (l x - s) : ℂ)) hprod
  rw [hsw]
  have hstep : ∀ s : ℝ, ∫ x, F s x * (β (l x - s) : ℂ) ∂ν =
      ∫ z, m z * (β (-(s + l' z) - s) : ℂ) ∂μ := by
    intro s
    have hu : HasCompactSupport (fun t : ℝ => ((β (t - s) : ℝ) : ℂ)) := by
      have : HasCompactSupport (fun t : ℝ => β (t - s)) := hs.comp_homeomorph (Homeomorph.subRight s)
      exact this.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
    exact hh s (fun t => ((β (t - s) : ℝ) : ℂ)) (by fun_prop) hu
  simp_rw [hstep]
  have hmeas2 : AEStronglyMeasurable
      (fun p : ℝ × Z => m p.2 * (β (-(p.1 + l' p.2) - p.1) : ℂ)) ((volume : Measure ℝ).prod μ) := by
    have a : AEStronglyMeasurable (fun p : ℝ × Z => m p.2) ((volume : Measure ℝ).prod μ) :=
      hm.aestronglyMeasurable.comp_snd
    have b : Measurable (fun p : ℝ × Z => β (-(p.1 + l' p.2) - p.1)) :=
      hc.measurable.comp (((measurable_fst.add (hl'.comp measurable_snd)).neg).sub measurable_fst)
    exact a.mul (Complex.measurable_ofReal.comp b).aestronglyMeasurable
  have hnorm : ∀ z, ∫ s : ℝ, ‖m z * (β (-(s + l' z) - s) : ℂ)‖ = ‖m z‖ / 2 := by
    intro z
    have : ∀ s : ℝ, ‖m z * (β (-(s + l' z) - s) : ℂ)‖ = ‖m z‖ * β (-(s + l' z) - s) := by
      intro s
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _)]
    simp_rw [this]
    rw [integral_const_mul, (flip_half β hi h1 (l' z)).2]
    ring
  have hprod2 : Integrable (fun p : ℝ × Z => m p.2 * (β (-(p.1 + l' p.2) - p.1) : ℂ))
      ((volume : Measure ℝ).prod μ) := by
    rw [integrable_prod_iff' hmeas2]
    refine ⟨Eventually.of_forall fun z => ?_, ?_⟩
    · have := (flip_half β hi h1 (l' z)).1.ofReal (𝕜 := ℂ)
      exact this.const_mul (m z)
    · simp_rw [hnorm]
      exact hm.norm.div_const 2
  have hsw2 := integral_integral_swap (f := fun (s : ℝ) z => m z * (β (-(s + l' z) - s) : ℂ)) hprod2
  rw [hsw2]
  have hin : ∀ z, ∫ s : ℝ, m z * (β (-(s + l' z) - s) : ℂ) = m z / 2 := by
    intro z
    rw [integral_const_mul, integral_complex_ofReal, (flip_half β hi h1 (l' z)).2]
    push_cast
    ring
  simp_rw [hin]
  exact integral_div 2 m

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.flip_pf :
    Flip := by
  intro X Z _ _ ν _ μ _ l l' F m d hl hl' hF hFc hm hd hb hh
  have hmeas : Measurable (fun x => F (l x) x) := hF.comp (hl.prodMk measurable_id)
  refine ⟨hd.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun x => hb (l x) x (by simp)), ?_⟩
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun k =>
    ⟨1 / (2 * ((k : ℝ) + 1)), 1 / ((k : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      exact one_div_lt_one_div_of_lt this (by linarith)⟩
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let β : ℕ → ℝ → ℝ := fun k => (φ k).normed volume
  have hr : ∀ k t, β k t ≠ 0 → |t| ≤ 1 := by
    intro k t ht
    have hmem : t ∈ Function.support ((φ k).normed volume) := ht
    rw [(φ k).support_normed_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
    have : (φ k).rOut ≤ 1 := by
      show 1 / ((k : ℝ) + 1) ≤ 1
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := by positivity
      linarith
    linarith
  have hcore := fun k => flip_core ν μ l l' F m d hl hl' hF hm hd hb hh (β k)
    (φ k).continuous_normed (φ k).hasCompactSupport_normed (fun t => (φ k).nonneg_normed t)
    (φ k).integral_normed (hr k)
  have hlim : Tendsto (fun k => ∫ x, (∫ s : ℝ, F s x * (β k (l x - s) : ℂ)) ∂ν) atTop
      (𝓝 (∫ x, F (l x) x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence d (fun k => (hcore k).1.aestronglyMeasurable) hd
      (fun k => Eventually.of_forall (hcore k).2.1) (Eventually.of_forall fun x => ?_)
    have := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure ℝ))
      (g := fun s => F s x) hφ (hFc x) (l x)
    refine this.congr fun k => ?_
    rw [convolution_eq_swap]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp [β, mul_comm]
  have hconst : Tendsto (fun k => ∫ x, (∫ s : ℝ, F s x * (β k (l x - s) : ℂ)) ∂ν) atTop
      (𝓝 ((∫ z, m z ∂μ) / 2)) := by
    simp_rw [fun k => (hcore k).2.2]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hconst
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PS

open MeasureTheory

section Abs

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem fix_proj (S : Submodule ℂ K) [S.HasOrthogonalProjection] (m : K →L[ℂ] K)
    (hs : ∀ x y, inner ℂ (m x) y = inner ℂ x (m y)) (hS : ∀ x ∈ S, m x ∈ S) (w : K) (hw : m w = w) :
    m (S.starProjection w) = S.starProjection w := by
  set p := S.starProjection w with hp
  have hpS : p ∈ S := Submodule.starProjection_apply_mem S w
  have hq : w - p ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal w
  have hmq : m (w - p) ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal] at hq ⊢
    intro u hu
    rw [← hs]
    exact hq _ (hS u hu)
  have h1 : m p - p ∈ S := S.sub_mem (hS p hpS) hpS
  have h2 : m p - p ∈ Sᗮ := by
    have e : m p - p = (w - p) - m (w - p) := by
      rw [map_sub, hw]; abel
    rw [e]
    exact Sᗮ.sub_mem hq hmq
  have h3 : m p - p = 0 := by
    have := (Submodule.mem_orthogonal S _).1 h2 _ h1
    exact inner_self_eq_zero.1 this
  exact sub_eq_zero.1 h3

end Abs

section Mul

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} (c : X → ℝ)

private noncomputable def mulL (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  by apply _root_.UpperTheory.Reformulated.B.MultiplicationNormBound.mulL <;> assumption

private theorem mulL_ae (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f : Lp ℂ 2 ν) :
    (mulL c hc hb f : X → ℂ) =ᵐ[ν] fun x => (c x : ℂ) * (f : X → ℂ) x :=
  by apply _root_.UpperTheory.Reformulated.B.MulLinearAe.mulL_ae <;> assumption

private theorem mulL_inner (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f g : Lp ℂ 2 ν) :
    inner ℂ (mulL c hc hb f) g = inner ℂ f (mulL c hc hb g) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulL_ae c hc hb f, mulL_ae c hc hb g] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

private def mulS (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) :
    PiLp 2 (fun _ : Unit => Lp ℂ 2 ν) →L[ℂ] PiLp 2 (fun _ : Unit => Lp ℂ 2 ν) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Unit => Lp ℂ 2 ν)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i : Unit => (mulL c hc hb).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => Lp ℂ 2 ν) i)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Unit => Lp ℂ 2 ν)).toContinuousLinearMap)

private theorem mulS_apply (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1)
    (f : PiLp 2 (fun _ : Unit => Lp ℂ 2 ν)) (i : Unit) : mulS c hc hb f i = mulL c hc hb (f i) := rfl

private theorem mulS_inner (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1)
    (f g : PiLp 2 (fun _ : Unit => Lp ℂ 2 ν)) :
    inner ℂ (mulS c hc hb f) g = inner ℂ f (mulS c hc hb g) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulS_apply, mulS_apply, mulL_inner]

end Mul

section Cut

private def chi (a b s : ℝ) : ℝ := max 0 (1 - (max (a - s) 0 + max (s - b) 0))

private theorem chi_cont (a b : ℝ) : Continuous (chi a b) := by
  unfold chi
  fun_prop

private theorem chi_abs (a b s : ℝ) : |chi a b s| ≤ 1 := by
  have h1 : 0 ≤ max (a - s) 0 := le_max_right _ _
  have h2 : 0 ≤ max (s - b) 0 := le_max_right _ _
  have h3 : 0 ≤ chi a b s := le_max_left _ _
  rw [abs_of_nonneg h3]
  exact max_le zero_le_one (by linarith)

private theorem chi_eq_one {a b s : ℝ} (h : s ∈ Set.Icc a b) : chi a b s = 1 := by
  have h1 : max (a - s) 0 = 0 := max_eq_right (by linarith [h.1])
  have h2 : max (s - b) 0 = 0 := max_eq_right (by linarith [h.2])
  simp [chi, h1, h2]

private theorem chi_ne_one {a b s : ℝ} (h : s ∉ Set.Icc a b) : chi a b s ≠ 1 := by
  intro e
  have h1 : 0 ≤ max (a - s) 0 := le_max_right _ _
  have h2 : 0 ≤ max (s - b) 0 := le_max_right _ _
  have h3 : 1 ≤ 1 - (max (a - s) 0 + max (s - b) 0) := by
    unfold chi at e
    rcases max_choice (0 : ℝ) (1 - (max (a - s) 0 + max (s - b) 0)) with h | h
    · rw [h] at e; norm_num at e
    · rw [h] at e; exact e.ge
  have h4 : a - s ≤ 0 := by linarith [le_max_left (a - s) 0]
  have h5 : s - b ≤ 0 := by linarith [le_max_left (s - b) 0]
  exact h ⟨by linarith, by linarith⟩

end Cut

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PS

end

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PS PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc MeasureTheory in
attribute [local instance] PositivityTheory.Rg.BcB.E.borelH in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pSupp_pf :
    PSupp := by
  intro E _ _ _ n D π a b v hv
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  have hl : Continuous (ldet : H E n 0 → ℝ) := continuous_ldet
  set c : H E n 0 → ℝ := fun x => chi a b (ldet x) with hcdef
  have hc : Measurable c := ((chi_cont a b).comp hl).measurable
  have hb : ∀ x, |c x| ≤ 1 := fun x => chi_abs a b _
  have hgen : ∀ f : Hs (ι := Unit) D, IsPiVec D π f → IsPiVec D π (mulS c hc hb f) := by
    intro f hf i
    obtain ⟨ψ, hψ, u, hu, hus, he⟩ := hf i
    refine ⟨ψ, hψ, fun s => (chi a b s : ℂ) * u s,
      (Complex.continuous_ofReal.comp (chi_cont a b)).mul hu, hus.mul_left, ?_⟩
    rw [mulS_apply]
    filter_upwards [mulL_ae c hc hb (f i), he] with x h1 h2
    rw [h1, h2]
    simp only [hcdef]
    ring
  have hS : ∀ f ∈ piSp D π Unit, mulS c hc hb f ∈ piSp D π Unit := by
    have hle : Submodule.span ℂ {f | IsPiVec D π f} ≤
        (piSp D π Unit).comap (mulS (ν := D.ν) c hc hb).toLinearMap := by
      refine Submodule.span_le.2 fun f hf => ?_
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (hgen f hf))
    have hcl : IsClosed (((piSp D π Unit).comap
        (mulS (ν := D.ν) c hc hb).toLinearMap : Submodule ℂ _) : Set (Hs (ι := Unit) D)) :=
      (show IsClosed (piSp D π Unit : Set (Hs (ι := Unit) D)) from
        Submodule.isClosed_topologicalClosure _).preimage (mulS c hc hb).continuous
    exact fun f hf => Submodule.topologicalClosure_minimal _ hle hcl hf
  have hv1 : mulL c hc hb v = v := by
    refine Lp.ext ?_
    filter_upwards [mulL_ae c hc hb v, hv] with x h1 h2
    rw [h1]
    by_cases hx : ldet x ∈ Set.Icc a b
    · simp [hcdef, chi_eq_one hx]
    · simp [h2 hx]
  have hw : mulS c hc hb (vecM v fun _ : Unit => 1) = vecM v fun _ : Unit => 1 := by
    ext1 i
    rw [mulS_apply]
    show mulL c hc hb ((1 : ℂ) • v) = (1 : ℂ) • v
    rw [one_smul, hv1]
  have key := fix_proj (piSp D π Unit) (mulS c hc hb) (mulS_inner c hc hb) hS _ hw
  have h2 : mulL c hc hb (P0 D π v) = P0 D π v := by
    have := congrArg (fun f : Hs (ι := Unit) D => f ()) key
    exact this
  have h3 := mulL_ae c hc hb (P0 D π v)
  rw [h2] at h3
  filter_upwards [h3] with x h4 hx
  have h5 : ((c x : ℂ) - 1) * (P0 D π v : H E n 0 → ℂ) x = 0 := by
    rw [sub_mul, one_mul, ← h4, sub_self]
  rcases mul_eq_zero.1 h5 with h6 | h6
  · exfalso
    have h7 : (c x : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [sub_eq_zero.1 h6]; simp
    exact chi_ne_one hx (Complex.ofReal_injective h7)
  · exact h6
end
