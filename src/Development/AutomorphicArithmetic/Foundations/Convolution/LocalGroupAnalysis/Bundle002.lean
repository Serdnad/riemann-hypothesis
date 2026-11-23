module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

section

noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

section

variable {G T : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [T2Space T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]

private lemma uni_comap (μ : Measure G) (hμ : Uni μ) (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    Uni (μ.comap fun u : U => (u : G)) := by
  obtain ⟨h1, h2⟩ := hμ
  haveI := h1
  haveI := h2
  have hUm : MeasurableSet (U : Set G) := hU.measurableSet
  have emb : MeasurableEmbedding (fun u : U => (u : G)) := MeasurableEmbedding.subtype_coe hUm
  have hH : (μ.comap U.subtype).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) μ hU.isOpenEmbedding_subtypeVal
  refine ⟨hH, ⟨?_⟩⟩
  ext s hs
  rw [Measure.inv_apply, emb.comap_apply, emb.comap_apply]
  have e : (fun u : U => (u : G)) '' s⁻¹ = ((fun u : U => (u : G)) '' s)⁻¹ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u⁻¹, hu, by simp⟩
    · intro hx
      obtain ⟨u, hu, hux⟩ := hx
      refine ⟨u⁻¹, by simpa using hu, ?_⟩
      have hux' : (u : G) = x⁻¹ := hux
      simp [hux']
  rw [e, Measure.measure_inv]

private def ext0 (U : Subgroup G) (r : U → ℝ≥0∞) : G → ℝ≥0∞ :=
  Function.extend (fun u : U => (u : G)) r 0

private lemma ext0_coe (U : Subgroup G) (r : U → ℝ≥0∞) (u : U) : ext0 U r (u : G) = r u :=
  Subtype.val_injective.extend_apply _ _ _

private lemma extendByZero_not_mem (U : Subgroup G) (r : U → ℝ≥0∞) {g : G} (hg : g ∉ U) : ext0 U r g = 0 := by
  unfold ext0
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨u, rfl⟩
    exact hg u.2

private lemma nrm_on_coset (j : T →* G) (ν : Measure T) (U : Subgroup G)
    (hV : MeasurableSet ((U.comap j : Subgroup T) : Set T)) (i : U.comap j →* U)
    (hi : ∀ t, (i t : G) = j t) (r : U → ℝ≥0∞)
    (h₀ : ∀ x, ∫⁻ t, r (i t * x) ∂(ν.comap fun t : U.comap j => (t : T)) = 1) (u : U) :
    ∫⁻ t, ext0 U r (j t * u) ∂ν = 1 := by
  have e : (fun t => ext0 U r (j t * u)) =
      ((U.comap j : Subgroup T) : Set T).indicator (fun t => ext0 U r (j t * u)) := by
    funext t
    by_cases ht : t ∈ U.comap j
    · rw [Set.indicator_of_mem (by exact ht)]
    · rw [Set.indicator_of_notMem (by exact ht)]
      apply extendByZero_not_mem
      intro hmem
      apply ht
      have h2 : j t = (j t * u) * (u : G)⁻¹ := by group
      rw [Subgroup.mem_comap, h2]
      exact U.mul_mem hmem (U.inv_mem u.2)
  have h := lintegral_subtype_comap hV (μ := ν) (fun t => ext0 U r (j t * u))
  rw [e, lintegral_indicator hV, ← h, ← h₀ u]
  refine lintegral_congr fun t => ?_
  have h3 : j (t : T) * (u : G) = ((i t * u : U) : G) := by simp [hi]
  rw [h3, ext0_coe]

open Classical in
private lemma isNrm_glue (j : T →* G) (ν : Measure T) (hν : Uni ν) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (hV : MeasurableSet ((U.comap j : Subgroup T) : Set T))
    (i : U.comap j →* U) (hi : ∀ t, (i t : G) = j t) (r : U → ℝ≥0∞)
    (h₀ : IsNrm i (ν.comap fun t : U.comap j => (t : T)) r) (r' : G → ℝ≥0∞) (h' : IsNrm j ν r') :
    IsNrm j ν ((Set.range j * (U : Set G)).piecewise (ext0 U r) r') := by
  haveI := hν.2
  haveI := hν.1
  haveI : ν.IsMulRightInvariant := by
    have h2 : (ν.inv).IsMulRightInvariant := inferInstance
    rwa [Measure.IsInvInvariant.inv_eq_self] at h2
  have hS : IsOpen (Set.range j * (U : Set G)) := hU.mul_left
  have hm : Measurable (ext0 U r) :=
    (MeasurableEmbedding.subtype_coe hU.measurableSet).measurable_extend h₀.1 measurable_const
  refine ⟨hm.piecewise hS.measurableSet h'.1, fun x => ?_⟩
  by_cases hx : x ∈ Set.range j * (U : Set G)
  · obtain ⟨_, ⟨s, rfl⟩, u, hu, rfl⟩ := hx
    have e : ∀ t, (Set.range j * (U : Set G)).piecewise (ext0 U r) r' (j t * (j s * u)) =
        ext0 U r (j (t * s) * u) := by
      intro t
      rw [Set.piecewise_eq_of_mem, map_mul, mul_assoc]
      exact ⟨j (t * s), ⟨_, rfl⟩, u, hu, by simp [mul_assoc]⟩
    refine Eq.trans (lintegral_congr e) ((lintegral_mul_right_eq_self (μ := ν)
      (fun t => ext0 U r (j t * u)) s).trans ?_)
    exact nrm_on_coset j ν U hV i hi r h₀.2 ⟨u, hu⟩
  · have e : ∀ t, (Set.range j * (U : Set G)).piecewise (ext0 U r) r' (j t * x) = r' (j t * x) := by
      intro t
      apply Set.piecewise_eq_of_notMem
      intro hm2
      apply hx
      obtain ⟨_, ⟨s, rfl⟩, u, hu, hxe⟩ := hm2
      refine ⟨j (t⁻¹ * s), ⟨_, rfl⟩, u, hu, ?_⟩
      have hxe' : j s * u = j t * x := hxe
      change j (t⁻¹ * s) * u = x
      rw [map_mul, map_inv, mul_assoc, hxe', inv_mul_cancel_left]
    exact (lintegral_congr e).trans (h'.2 x)

end

end UpperTheory.ConvolutionTheory.G

open MeasureTheory Topology UpperTheory.ConvolutionTheory.G in
theorem UpperTheory.ConvolutionTheory.G.quotOpen_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotOpen := by
  classical
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν h U hU i hi
  obtain ⟨hμ, hj, hν⟩ := id h
  have hV : IsOpen ((U.comap j : Subgroup T) : Set T) := hU.preimage hj.continuous
  have hUm : MeasurableSet (U : Set G) := hU.measurableSet
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  haveI : SecondCountableTopology (U.comap j) :=
    TopologicalSpace.Subtype.secondCountableTopology ((U.comap j : Subgroup T) : Set T)
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (U.comap j) := hV.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hUc : IsClosedEmbedding (fun u : U => (u : G)) :=
    (Subgroup.isClosed_of_isOpen U hU).isClosedEmbedding_subtypeVal
  have hVc : IsClosedEmbedding (fun t : U.comap j => (t : T)) :=
    (Subgroup.isClosed_of_isOpen _ hV).isClosedEmbedding_subtypeVal
  have hic : IsClosedEmbedding i := by
    have h1 : IsClosedEmbedding ((fun u : U => (u : G)) ∘ i) := by
      have h2 : ((fun u : U => (u : G)) ∘ i) = j ∘ (fun t : U.comap j => (t : T)) := by
        funext t
        exact hi t
      rw [h2]
      exact hj.comp hVc
    exact (IsClosedEmbedding.of_comp_iff hUc).1 h1
  have hs : Pair (μ.comap fun u : U => (u : G)) i (ν.comap fun t : U.comap j => (t : T)) :=
    ⟨uni_comap μ hμ U hU, hic, uni_comap ν hν _ hV⟩
  refine ⟨hs, fun F hFm hFi hFs => ?_⟩
  obtain ⟨r₀, -, hr₀, -⟩ := hN U (U.comap j) _ i _ hs
  obtain ⟨r', -, hr', -⟩ := hN G T μ j ν h
  have hg := isNrm_glue j ν hν U hU hV.measurableSet i hi _ hr₀ _ hr'
  obtain ⟨hQ1, -, hQ3⟩ := hE G T μ j ν h F hFm hFi _ hg
  have hFm' : Measurable (fun u : U => F u) := hFm.comp measurable_subtype_coe
  have hFi' : ∀ (t : U.comap j) (g : U), F ((i t * g : U) : G) = F g := by
    intro t g
    simp [hi, hFi]
  obtain ⟨hq1, -, hq3⟩ := hE U (U.comap j) _ i _ hs (fun u => F u) hFm' hFi' _ hr₀
  have key : (fun x => F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ)) =
      (U : Set G).indicator (fun x => F x * (((ext0 U fun u => (r₀ u : ENNReal)) x).toReal : ℂ)) := by
    funext x
    by_cases hxU : x ∈ (U : Set G)
    · rw [Set.indicator_of_mem hxU, Set.piecewise_eq_of_mem]
      exact ⟨1, ⟨1, map_one j⟩, x, hxU, one_mul x⟩
    · rw [Set.indicator_of_notMem hxU]
      by_cases hxS : x ∈ Set.range j * (U : Set G)
      · rw [Set.piecewise_eq_of_mem _ _ _ hxS, extendByZero_not_mem U _ hxU]
        simp
      · have : F x = 0 := by
          by_contra h0
          exact hxS (hFs x h0)
        simp [this]
  have cmp : (fun x => F x * (((ext0 U fun u => (r₀ u : ENNReal)) x).toReal : ℂ)) ∘
      (fun u : U => (u : G)) = fun u : U => F u * (((r₀ u : ENNReal)).toReal : ℂ) := by
    funext u
    simp only [Function.comp]
    rw [show ext0 U (fun u => (r₀ u : ENNReal)) (u : G) = _ from ext0_coe U _ u]
  have i1 : Integrable (fun x => F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ)) μ ↔
      Integrable (fun u : U => F u * (((r₀ u : ENNReal)).toReal : ℂ))
        (μ.comap fun u : U => (u : G)) := by
    rw [key, integrable_indicator_iff hUm, integrableOn_iff_comap_subtypeVal hUm]
    exact Iff.of_eq (congrArg (fun f => Integrable f (μ.comap fun u : U => (u : G))) cmp)
  have i2 : ∫ x, F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ) ∂μ =
      ∫ u : U, F u * (((r₀ u : ENNReal)).toReal : ℂ) ∂(μ.comap fun u : U => (u : G)) := by
    rw [key, integral_indicator hUm, ← integral_subtype_comap hUm]
    exact congrArg (fun f => ∫ u : U, f u ∂(μ.comap fun u : U => (u : G))) cmp
  exact ⟨hQ1.trans (i1.trans hq1.symm), hQ3.trans (i2.trans hq3.symm)⟩
end
end

section

open MeasureTheory Topology
open scoped ENNReal

theorem UpperTheory.ConvolutionTheory.G.quotMap_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotMap := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν hP μ' j' ν' hP' e y hμ hν F hF hinv
  obtain ⟨ρ0, -, hρ, -⟩ := hN G' T' μ' j' ν' hP'
  set ρ : G' → ℝ≥0∞ := fun g => (ρ0 g : ℝ≥0∞) with hρdef
  have hjc : Continuous j := hP.2.1.continuous
  have hj'c : Continuous j' := hP'.2.1.continuous
  have hec : Continuous e := e.continuous_toFun
  have hejc : Continuous (fun t => e (j t)) := hec.comp hjc
  haveI := hP.2.2.1
  haveI := hP'.1.1
  haveI := hP'.1.2
  have hrange : ∀ t, e (j t) ∈ Set.range j' := by
    have hcl : IsClosed (Set.range j') := hP'.2.1.isClosed_range
    have ho : IsOpen (Set.range j')ᶜ := hcl.isOpen_compl
    have h0 : (ν.map (fun t => e (j t))) (Set.range j')ᶜ = 0 := by
      rw [hν, Measure.map_apply hj'c.measurable ho.measurableSet]
      have : j' ⁻¹' (Set.range j')ᶜ = ∅ := by
        ext t; simp
      rw [this, measure_empty]
    rw [Measure.map_apply hejc.measurable ho.measurableSet] at h0
    have he := (ho.preimage hejc).eq_empty_of_measure_zero h0
    intro t
    by_contra hc
    have : t ∈ (fun t => e (j t)) ⁻¹' (Set.range j')ᶜ := hc
    rw [he] at this
    exact this
  have hφ : Measurable (fun g : G => e g * y) := (hec.mul continuous_const).measurable
  have hF1 : Measurable (fun g => F (e g * y)) := hF.comp hφ
  have hinv1 : ∀ t g, (fun g => F (e g * y)) (j t * g) = (fun g => F (e g * y)) g := by
    intro t g
    obtain ⟨t', ht'⟩ := hrange t
    simp only [map_mul, ← ht', mul_assoc, hinv]
  have hρ1 : UpperTheory.ConvolutionTheory.G.IsNrm j ν (fun g => ρ (e g * y)) := by
    refine ⟨hρ.1.comp hφ, fun x => ?_⟩
    have hm : Measurable (fun z : G' => ρ (z * (e x * y))) := hρ.1.comp (measurable_mul_const _)
    have h1 := lintegral_map (μ := ν) hm hejc.measurable
    have h2 := lintegral_map (μ := ν') hm hj'c.measurable
    rw [hν, h2, hρ.2] at h1
    simp only [map_mul, mul_assoc]
    exact h1.symm
  haveI : μ'.IsMulRightInvariant := by
    have h : μ'.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at h
  have hmp : MeasurePreserving (fun g : G => e g * y) μ μ' :=
    (measurePreserving_mul_right μ' y).comp ⟨hec.measurable, hμ⟩
  have hemb : MeasurableEmbedding (fun g : G => e g * y) :=
    (e.toHomeomorph.trans (Homeomorph.mulRight y)).measurableEmbedding
  obtain ⟨a1, -, a3⟩ := hE G T μ j ν hP _ hF1 hinv1 _ hρ1
  obtain ⟨b1, -, b3⟩ := hE G' T' μ' j' ν' hP' F hF hinv ρ hρ
  refine ⟨?_, ?_⟩
  · rw [a1, b1]
    exact hmp.integrable_comp_emb hemb (g := fun x => F x * ((ρ x).toReal : ℂ))
  · rw [a3, b3]
    exact hmp.integral_comp hemb (fun x => F x * ((ρ x).toReal : ℂ))
end

section

open MeasureTheory in
theorem UpperTheory.ConvolutionTheory.G.quotFub_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotFub := by
  intro _ hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP X _ m _ F hF hinv ρ hρ hfin
  haveI : μ.IsHaarMeasure := hP.1.1
  have hρm : Measurable (fun x => ((ρ x).toReal : ℂ)) :=
    Complex.measurable_ofReal.comp hρ.1.ennreal_toReal
  have hH : Measurable (Function.uncurry fun (a : X) (x : G) => F a x * ((ρ x).toReal : ℂ)) :=
    hF.mul (hρm.comp measurable_snd)
  have hint : Integrable (Function.uncurry fun (a : X) (x : G) => F a x * ((ρ x).toReal : ℂ)) (m.prod μ) := by
    refine ⟨hH.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ hH.enorm.aemeasurable]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hfin)
    refine lintegral_mono fun a => lintegral_mono fun x => ?_
    simp only [Function.uncurry, enorm_mul]
    gcongr
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  have hGm : Measurable (fun g => ∫ a, F a g ∂m) :=
    (hF.stronglyMeasurable.integral_prod_left).measurable
  have hGi : ∀ t g, (fun g => ∫ a, F a g ∂m) (j t * g) = (fun g => ∫ a, F a g ∂m) g := by
    intro t g
    simp only [hinv]
  obtain ⟨h1, -, h3⟩ := hE G T μ j ν hP _ hGm hGi ρ hρ
  have hmul : ∀ x, (∫ a, F a x ∂m) * ((ρ x).toReal : ℂ) = ∫ a, F a x * ((ρ x).toReal : ℂ) ∂m :=
    fun x => (integral_mul_const _ _).symm
  refine ⟨h1.2 ?_, ?_⟩
  · simp only [hmul]
    exact hint.integral_prod_right
  · rw [h3]
    simp only [hmul]
    rw [← integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    exact ((hE G T μ j ν hP (F a) (hF.of_uncurry_left) (hinv a) ρ hρ).2.2).symm
end

section

open MeasureTheory Topology
open scoped ENNReal

private theorem lintegral_pi_one {ι : Type} [Fintype ι] {T : ι → Type} [∀ i, MeasurableSpace (T i)]
    (ν : ∀ i, Measure (T i)) [∀ i, SigmaFinite (ν i)] (f : ∀ i, T i → NNReal)
    (hf : ∀ i, Measurable (f i)) (h1 : ∀ i, ∫⁻ t, (f i t : ℝ≥0∞) ∂(ν i) = 1) :
    ∫⁻ t, ((∏ i, f i (t i) : NNReal) : ℝ≥0∞) ∂(Measure.pi ν) = 1 := by
  have hint : ∀ i, Integrable (fun t => (f i t : ℝ)) (ν i) := fun i => by
    have := integrable_toReal_of_lintegral_ne_top (μ := ν i) (f := fun t => (f i t : ℝ≥0∞))
      (hf i).coe_nnreal_ennreal.aemeasurable (by rw [h1 i]; exact ENNReal.one_ne_top)
    simpa using this
  have hI : ∀ i, ∫ t, (f i t : ℝ) ∂(ν i) = 1 := fun i => by
    have := lintegral_coe_eq_integral (f i) (hint i)
    rw [h1 i] at this
    exact ENNReal.ofReal_eq_one.1 this.symm
  have hP : Integrable (fun t : ∀ i, T i => ((∏ i, f i (t i) : NNReal) : ℝ)) (Measure.pi ν) := by
    simp only [NNReal.coe_prod]
    exact Integrable.fintype_prod_dep hint
  rw [lintegral_coe_eq_integral _ hP]
  simp only [NNReal.coe_prod]
  rw [integral_fintype_prod_eq_prod (fun i t => (f i t : ℝ))]
  simp [hI]

theorem UpperTheory.ConvolutionTheory.G.quotPi_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotPi := by
  intro hN hE ι _ G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP J hJ
  haveI : ∀ i, (μ i).IsHaarMeasure := fun i => (hP i).1.1
  haveI : ∀ i, (μ i).IsInvInvariant := fun i => (hP i).1.2
  haveI : ∀ i, (ν i).IsHaarMeasure := fun i => (hP i).2.2.1
  haveI : ∀ i, (ν i).IsInvInvariant := fun i => (hP i).2.2.2
  have hJe : (J : (∀ i, T i) → ∀ i, G i) = Pi.map (fun i => (j i : T i → G i)) := by
    funext t i
    exact hJ t i
  have hPair : UpperTheory.ConvolutionTheory.G.Pair (Measure.pi μ) J (Measure.pi ν) := by
    refine ⟨⟨inferInstance, inferInstance⟩, ?_, ⟨inferInstance, inferInstance⟩⟩
    rw [hJe]
    exact IsClosedEmbedding.piMap fun i => (hP i).2.1
  refine ⟨hPair, fun F hF => ?_⟩
  choose ρ hρc hρn _ using fun i => hN (G i) (T i) (μ i) (j i) (ν i) (hP i)
  have hR : UpperTheory.ConvolutionTheory.G.IsNrm J (Measure.pi ν)
      (fun g => ((∏ i, ρ i (g i) : NNReal) : ℝ≥0∞)) := by
    refine ⟨?_, fun x => ?_⟩
    · exact (Finset.measurable_prod _ fun i _ =>
        (hρc i).measurable.comp (measurable_pi_apply i)).coe_nnreal_ennreal
    · have := lintegral_pi_one ν (fun i t => ρ i (j i t * x i))
        (fun i => ((hρc i).comp ((hP i).2.1.continuous.mul continuous_const)).measurable)
        (fun i => (hρn i).2 (x i))
      simpa only [Pi.mul_apply, hJ] using this
  have hFm : Measurable fun g : ∀ i, G i => ∏ i, F i (g i) :=
    Finset.measurable_prod _ fun i _ => (hF i).1.comp (measurable_pi_apply i)
  have hFi : ∀ t g, (fun g : ∀ i, G i => ∏ i, F i (g i)) (J t * g) =
      (fun g : ∀ i, G i => ∏ i, F i (g i)) g := fun t g => by
    simp only [Pi.mul_apply, hJ, (hF _).2]
  obtain ⟨h1, -, h2⟩ := hE _ _ _ _ _ hPair _ hFm hFi _ hR
  have hloc := fun i => hE (G i) (T i) (μ i) (j i) (ν i) (hP i) (F i) (hF i).1 (hF i).2 _ (hρn i)
  have hfun : (fun x : ∀ i, G i => (∏ i, F i (x i)) *
      ((((∏ i, ρ i (x i) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ)) =
      fun x => ∏ i, (F i (x i) * (((ρ i (x i) : ℝ≥0∞).toReal : ℝ) : ℂ)) := by
    funext x
    simp only [ENNReal.coe_toReal, NNReal.coe_prod, Complex.ofReal_prod, Finset.prod_mul_distrib]
  refine ⟨fun hq => h1.2 ?_, ?_⟩
  · rw [hfun]
    exact Integrable.fintype_prod_dep
      (f := fun i x => F i x * (((ρ i x : ℝ≥0∞).toReal : ℝ) : ℂ)) fun i => (hloc i).1.1 (hq i)
  · rw [h2, hfun, integral_fintype_prod_eq_prod
      (fun i x => F i x * (((ρ i x : ℝ≥0∞).toReal : ℝ) : ℂ))]
    exact Finset.prod_congr rfl fun i _ => (hloc i).2.2.symm
end
