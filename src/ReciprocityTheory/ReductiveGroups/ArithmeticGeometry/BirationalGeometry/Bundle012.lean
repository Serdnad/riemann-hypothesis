module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeG
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem divSupp_one (P : Ideal (MRing ι)) : divSupp P 1 = ∅ := by
  ext W
  simp only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hW
  have hp := hW.1
  have htop : (⊤ : Ideal (MRing ι)) ≤ W := by
    have h2 := hp.2
    rwa [Ideal.span_singleton_one, sup_top_eq] at h2
  exact fun _ => hp.1.ne_top (top_le_iff.1 htop)

theorem logNorm_ofWeight_one (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (z : (Σ k, ι k) → ℂ) :
    logNorm (HermLine.ofWeight u hu) 1 z = u z := by
  simp [logNorm, HermLine.ofWeight, Real.exp_neg, Real.log_exp]

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
  intro m hm k
  rw [MvPolynomial.support_one] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  simp

theorem metricChange : MetricChangeStatement := by
  intro K _ ι _ I hI P n L A u hu hP hL hA hsm
  have hB : IsSmoothHerm (HermLine.ofWeight u hu) := by
    show ContDiffOn ℝ _ (fun z => Real.exp (-u z)) _
    exact hsm.neg.exp
  have h1 : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hlog : logNorm (HermLine.ofWeight u hu) 1 = u := funext (logNorm_ofWeight_one u hu)
  have hrec : recR I P L (HermLine.ofWeight u hu) 1 = -ptsIntegral P (pot L) u := by
    unfold recR
    rw [divSupp_one]
    simp only [finsum_mem_empty, zero_sub, arInt, hlog]
    rfl
  rw [hI.2.1 P n L A _ hP hL hA hB,
    hI.2.2 P n L _ 1 (fun _ => 0) hP hL hB (fun _ => rfl) isMultiHomog_one h1, hrec]
  ring

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

def LogAbsLocIntStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (f : (Fin D → ℂ) → ℂ), IsOpen U → AnalyticOnNhd ℂ f U →
    LocallyIntegrableOn (fun z => Real.log ‖f z‖) U volume

theorem analyticAt_eval_poly {D : ℕ} {σ : Type*} (p : MvPolynomial σ ℂ)
    {γ : (Fin D → ℂ) → σ → ℂ} {u : Fin D → ℂ} (hγ : ∀ i, AnalyticAt ℂ (fun v => γ v i) u) :
    AnalyticAt ℂ (fun v => eval (γ v) p) u := by
  induction p using MvPolynomial.induction_on
  · simpa using analyticAt_const
  · rename_i p q hp hq
    have h := hp.add hq
    simp only [map_add (f := _)]
    exact h
  · rename_i p i hp
    have h := hp.mul (hγ i)
    simp only [map_mul, MvPolynomial.eval_X]
    exact h

theorem abs_log_div_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |Real.log (a / b)| ≤ |Real.log a| + |Real.log b| := by
  rcases ha.eq_or_lt with h | h
  · subst h
    simp
  · rw [Real.log_div h.ne' hb.ne', abs_le]
    constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
      le_abs_self (Real.log b), neg_abs_le (Real.log b)]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem brIntegrable_of (hLA : LogAbsLocIntStatement) (R : AnLogRes P J e)
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  classical
  obtain ⟨a, hAa, hsa, -⟩ := hs
  have hpot : ∀ i, IsPotential R.A (potOf R (L i)) := fun i => isPotential_potOf R (hL i)
  intro j Kc hKt hKc
  have hdens := locDensCont R.A (fun i => potOf R (L i)) hpot j
  have hloc : LocallyIntegrableOn
      (fun y => logNorm A s (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)))
      (R.A.chart j).target volume := by
    intro y0 hy0
    let x0 := (R.A.chart j).symm y0
    let V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0
    have hVo : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
    have hy0V : y0 ∈ V := ⟨hy0, R.mem_U x0⟩
    let γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun v => R.lift x0 ((R.A.chart j).symm v)
    let F : (Fin e → ℂ) → ℂ := fun v => eval (γ v) (map (Int.castRingHom ℂ) s)
    let H : (Fin e → ℂ) → ℝ := fun v => A.h (γ v)
    have hγa : ∀ y ∈ V, ∀ p, AnalyticAt ℂ (fun v => γ v p) y := fun y hy p => R.holo x0 p j y hy
    have hFan : AnalyticOnNhd ℂ F V := fun y hy => analyticAt_eval_poly _ (hγa y hy)
    have hγc : ContinuousOn γ V := continuousOn_pi.mpr (fun p => (R.holo x0 p j).continuousOn)
    have hnz : ∀ y ∈ V, ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := fun y hy => (R.mem x0 _ hy.2).1
    have hHpos : ∀ y ∈ V, 0 < H y := fun y hy => A.pos _ (hnz y hy)
    have hHc : ContinuousOn H V := hA.continuousOn.comp hγc (fun y hy => hnz y hy)
    have hlogH : ContinuousOn (fun y => Real.log (H y)) V := hHc.log (fun y hy => (hHpos y hy).ne')
    have hlogF : LocallyIntegrableOn (fun y => Real.log ‖F y‖) V volume := hLA e V F hVo hFan
    have hinv : ∀ y ∈ V, logNorm A s (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) =
        Real.log (‖F y‖ / H y) := by
      intro y hy
      obtain ⟨c, hc, hcz⟩ := R.compat ((R.A.chart j).symm y) x0 ((R.A.chart j).symm y)
        ⟨R.mem_U _, hy.2⟩
      rw [hcz]
      have h1 := logNorm_bsmul A hAa hsa hc (R.lift x0 ((R.A.chart j).symm y))
      exact h1
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hVo y0 hy0V
    have hBV : Metric.closedBall y0 (δ / 2) ⊆ V :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hBc : IsCompact (Metric.closedBall y0 (δ / 2)) := isCompact_closedBall y0 (δ / 2)
    have hBm : MeasurableSet (Metric.closedBall y0 (δ / 2)) :=
      Metric.isClosed_closedBall.measurableSet
    refine ⟨Metric.closedBall y0 (δ / 2),
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y0 (by linarith)), ?_⟩
    have hmeas : AEStronglyMeasurable (fun y => Real.log (‖F y‖ / H y))
        (volume.restrict (Metric.closedBall y0 (δ / 2))) := by
      have hF' : AEMeasurable (fun y => ‖F y‖) (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        ((hFan.continuousOn.mono hBV).aestronglyMeasurable hBm).norm.aemeasurable
      have hH' : AEMeasurable H (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        ((hHc.mono hBV).aestronglyMeasurable hBm).aemeasurable
      exact (Real.measurable_log.comp_aemeasurable (hF'.div hH')).aestronglyMeasurable
    have hint : IntegrableOn (fun y => Real.log (‖F y‖ / H y)) (Metric.closedBall y0 (δ / 2))
        volume := by
      have hb : Integrable (fun y => |Real.log ‖F y‖| + |Real.log (H y)|)
          (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        (Integrable.abs (hlogF.integrableOn_compact_subset hBV hBc)).add
          (Integrable.abs ((hlogH.mono hBV).integrableOn_compact hBc))
      refine hb.mono' hmeas ?_
      refine (ae_restrict_iff' hBm).mpr (Filter.Eventually.of_forall (fun y hy => ?_))
      rw [Real.norm_eq_abs]
      exact abs_log_div_le (norm_nonneg _) (hHpos y (hBV hy))
    exact hint.congr_fun (fun y hy => (hinv y (hBV hy)).symm) hBm
  exact (hloc.integrableOn_compact_subset hKt hKc).mul_continuousOn (hdens.mono hKt) hKc

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem ptsIntegral_eq_mInt' (hE : ResExistsStatement) (hB : ResBridgeStatement) {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e : ℕ}
    (R : AnLogRes P J e) {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRing ι}
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    ptsIntegral P (pot L) (logNorm A s) =
      ReciprocityTheory.AnForm.M.mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) :=
  ptsIntegral_eq_mInt hE hB goodProjExists R hP hL hA hs

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def goodT (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (j : Fin A.n) : Set (Fin e → ℂ) :=
  {u | u ∈ (A.chart j).target ∧ AnalyticAt ℂ (q ∘ (A.chart j).symm) u ∧
    LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0}

theorem isOpen_goodT (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (j : Fin A.n) :
    IsOpen (goodT A q j) := by
  rw [isOpen_iff_mem_nhds]
  rintro u ⟨hut, han, hdet⟩
  have h1 : ∀ᶠ v in 𝓝 u, v ∈ (A.chart j).target := (A.chart j).open_target.mem_nhds hut
  have h2 : ∀ᶠ v in 𝓝 u, AnalyticAt ℂ (q ∘ (A.chart j).symm) v := han.eventually_analyticAt
  have hc : ContinuousAt (fun v => ContinuousLinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) v)) u :=
    ContinuousLinearMap.continuous_det.continuousAt.comp han.fderiv.continuousAt
  have h3 : ∀ᶠ v in 𝓝 u, ContinuousLinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) v) ≠ 0 :=
    hc.eventually_ne hdet
  filter_upwards [h1, h2, h3] with v a b c
  exact ⟨a, b, c⟩

theorem target_diff_goodT_subset (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (j : Fin A.n) :
    (A.chart j).target \ goodT A q j ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' S := by
  rintro u ⟨hut, hug⟩
  refine ⟨hut, ?_⟩
  by_contra hS
  apply hug
  have hx := (A.chart j).map_target hut
  have hr : (A.chart j) ((A.chart j).symm u) = u := (A.chart j).right_inv hut
  obtain ⟨h1, h2⟩ := hq _ hS j hx
  rw [hr] at h1 h2
  exact ⟨hut, h1, h2⟩

theorem integrableOn_chart [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Pt : ChartPartition A) (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) *
      locDens A Φ j u) (A.chart j).target := by
  have hχc : ContinuousOn (fun u => Pt.χ j ((A.chart j).symm u)) (A.chart j).target := by
    have := ((Pt.smooth j) j).continuousOn
    simpa [Function.comp_def] using this
  have hKc : IsCompact ((A.chart j) '' tsupport (Pt.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart j).continuousOn.mono (Pt.tsupport_subset j))
  have hKt : (A.chart j) '' tsupport (Pt.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (Pt.tsupport_subset j hx)
  have hI := hg j _ hKt hKc
  have hI2 : IntegrableOn (fun u => Pt.χ j ((A.chart j).symm u) *
      (g ((A.chart j).symm u) * locDens A Φ j u)) ((A.chart j) '' tsupport (Pt.χ j)) := by
    first
      | exact hI.continuousOn_mul (hχc.mono hKt) hKc
      | exact IntegrableOn.continuousOn_mul (hχc.mono hKt) hI hKc
  simp only [mul_assoc]
  refine hI2.of_forall_diff_eq_zero (A.chart j).open_target.measurableSet ?_
  rintro u ⟨hut, huK⟩
  have hn : (A.chart j).symm u ∉ tsupport (Pt.χ j) := fun h =>
    huK ⟨_, h, (A.chart j).right_inv hut⟩
  have h0 : Pt.χ j ((A.chart j).symm u) = 0 := by
    first
      | exact image_eq_zero_of_nmem_tsupport hn
      | exact image_eq_zero_of_notMem_tsupport hn
  rw [h0, zero_mul]

theorem goodT_fibre_eq (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) :
    goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y} =
      (A.chart j) '' ((A.chart j).source ∩ (q ⁻¹' {y} \ S)) := by
  ext u
  constructor
  · rintro ⟨hu, hy'⟩
    have hx := (A.chart j).map_target hu.1
    have hxS : (A.chart j).symm u ∉ S := fun hS => hy ⟨u, ⟨hu, hS⟩, hy'⟩
    exact ⟨(A.chart j).symm u, ⟨hx, hy', hxS⟩, (A.chart j).right_inv hu.1⟩
  · rintro ⟨x, ⟨hx, hqx, hxS⟩, rfl⟩
    have hl : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hx
    obtain ⟨h1, h2⟩ := hq x hxS j hx
    refine ⟨⟨(A.chart j).map_source hx, h1, h2⟩, ?_⟩
    show q ((A.chart j).symm (A.chart j x)) ∈ ({y} : Set (Fin e → ℂ))
    rw [hl]
    exact hqx

theorem fib_term (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (Pt : ChartPartition A) (g : X → ℝ) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source)
    (hxS : x ∉ S) :
    Pt.χ j ((A.chart j).symm (A.chart j x)) * g ((A.chart j).symm (A.chart j x)) *
        locDens A Φ j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
      Pt.χ j x * (g x * pushDens A Φ q x) := by
  have hxc : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hl : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hx
  have hut : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hx
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart (chartIdx A x)).source :=
    ⟨hut, by
      show (A.chart j).symm (A.chart j x) ∈ (A.chart (chartIdx A x)).source
      rw [hl]
      exact hxc⟩
  have hD := locDensChart A Φ hΦ j (chartIdx A x) (A.chart j x) hut hmem.2
  rw [hl] at hD
  have hTan : AnalyticAt ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :=
    A.holo j (chartIdx A x) _ hmem
  have hTu : (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) = A.chart (chartIdx A x) x := by
    simp [hl]
  obtain ⟨hqc, -⟩ := hq x hxS (chartIdx A x) hxc
  obtain ⟨-, hdj⟩ := hq x hxS j hx
  have heq : (q ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j x)]
      (q ∘ (A.chart (chartIdx A x)).symm) ∘ (A.chart (chartIdx A x) ∘ (A.chart j).symm) := by
    have hopen : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart (chartIdx A x)).source ∈
        𝓝 (A.chart j x) :=
      ((A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
        (A.chart (chartIdx A x)).open_source).mem_nhds hmem
    filter_upwards [hopen] with y hy
    simp only [Function.comp_apply]
    rw [(A.chart (chartIdx A x)).left_inv hy.2]
  have hfd : fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) =
      (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x)).comp
        (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x)) := by
    rw [heq.fderiv_eq, fderiv_comp _ (by rw [hTu]; exact hqc.differentiableAt)
      hTan.differentiableAt, hTu]
  have hdet : LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
    rw [hfd]
    exact LinearMap.det_comp _ _
  have hT0 : ‖LinearMap.det (fderiv ℂ (A.chart (chartIdx A x) ∘ (A.chart j).symm) (A.chart j x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    rw [hdet, h, mul_zero] at hdj
    exact hdj rfl
  have hQ0 : ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    rw [hdet, h, zero_mul] at hdj
    exact hdj rfl
  rw [hl, jacN, pushDens, hD, hdet, norm_mul, mul_pow]
  field_simp

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
