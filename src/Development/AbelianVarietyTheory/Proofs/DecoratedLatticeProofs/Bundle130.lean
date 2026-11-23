module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal NNReal
open Filter

noncomputable section

namespace GlobalTheory.Unf

open GlobalTheory.Tw

section InductionInStages
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem lintegral_eq_cutoff_inner {T : Subgroup G} {μ : Measure G} {μT : Measure T}
    [SFinite μ] [μ.IsMulLeftInvariant] [SFinite μT] [μT.IsInvInvariant]
    {β : G → NNReal} (hβ : IsCosetCutoff T μT β) {H : G → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ x, H x ∂μ = ∫⁻ x, (β x : ℝ≥0∞) * ∫⁻ t : T, H (t * x) ∂μT ∂μ := by
  have hb : Measurable fun x => (β x : ℝ≥0∞) := hβ.1.coe_nnreal_ennreal
  have hmul : Measurable fun p : G × T => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have hmul' : Measurable fun p : G × T => ((p.2⁻¹ : T) : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd.inv).mul measurable_fst
  have e1 : ∀ x, (β x : ℝ≥0∞) * ∫⁻ t : T, H (t * x) ∂μT = ∫⁻ t : T, β x * H (t * x) ∂μT := fun x =>
    (lintegral_const_mul' _ _ ENNReal.coe_ne_top).symm
  rw [lintegral_congr e1, lintegral_lintegral_swap ((hb.comp measurable_fst).mul (hH.comp hmul)).aemeasurable]
  have e2 : ∀ t : T, ∫⁻ x, β x * H (t * x) ∂μ = ∫⁻ x, β ((t⁻¹ : T) * x) * H x ∂μ := fun t => by
    rw [← lintegral_mul_left_eq_self (μ := μ) (fun x => β ((t⁻¹ : T) * x) * H x) t]
    simp
  rw [lintegral_congr e2,
    ← lintegral_lintegral_swap (f := fun x (t : T) => β ((t⁻¹ : T) * x) * H x)
      ((hb.comp hmul').mul (hH.comp measurable_fst)).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [lintegral_mul_const _ (f := fun t : T => (β ((t⁻¹ : T) * x) : ℝ≥0∞)) (hb.comp (hmul'.comp measurable_prodMk_left)),
    lintegral_inv_eq_self (μ := μT) (fun t : T => (β (t * x) : ℝ≥0∞)), hβ.2, one_mul]

theorem map_val_eq_map_stages {R₀ R : Subgroup G} (μ₀ : Measure R₀) (μR : Measure R) [SFinite μ₀]
    {U : Type} [MeasurableSpace U] (ν : Measure U) {j : U → G} (hj : Measurable j)
    (hst : ∀ F : G → ℝ≥0∞, Measurable F → ∫⁻ r : R, F r ∂μR = ∫⁻ u, ∫⁻ r : R₀, F (r * j u) ∂μ₀ ∂ν) :
    μR.map Subtype.val = (ν.prod μ₀).map (fun p : U × R₀ => (p.2 : G) * j p.1) := by
  have hm : Measurable (fun p : U × R₀ => (p.2 : G) * j p.1) :=
    (measurable_subtype_coe.comp measurable_snd).mul (hj.comp measurable_fst)
  have key : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ y, F y ∂(μR.map Subtype.val) = ∫⁻ y, F y ∂((ν.prod μ₀).map (fun p : U × R₀ => (p.2 : G) * j p.1)) := by
    intro F hF
    rw [lintegral_map hF measurable_subtype_coe, lintegral_map hF hm, lintegral_prod (f := fun p : U × R₀ => F ((p.2 : G) * j p.1)) (hF.comp hm).aemeasurable]
    exact hst F hF
  ext A hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA]
  exact key _ (measurable_one.indicator hA)

end InductionInStages

theorem invariant_integral_in_stages : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (R₀ R : Subgroup G), IsClosed (R₀ : Set G) → IsClosed (R : Set G) → ∀ (μ₀ : Measure R₀) (μR : Measure R), μ₀.IsHaarMeasure → μ₀.IsInvInvariant → μR.IsHaarMeasure → μR.IsInvInvariant → ∀ (U : Type) [MeasurableSpace U] (ν : Measure U) [SFinite ν] (j : U → G), Measurable j → (∀ F : G → ENNReal, Measurable F → ∫⁻ r : R, F r ∂μR = ∫⁻ u, ∫⁻ r : R₀, F (r * j u) ∂μ₀ ∂ν) → ∀ f : G → ℂ, Measurable f → (∀ r ∈ R₀, ∀ g, f (r * g) = f g) → (∀ g, Integrable (fun u => f (j u * g)) ν) → (∃ z', IsQuotIntL1 μR μ (fun g => ((∫ u, ‖f (j u * g)‖ ∂ν : ℝ) : ℂ)) z') → ∀ z, IsQuotIntL1 μR μ (fun g => ∫ u, f (j u * g) ∂ν) z → IsQuotIntL1 μ₀ μ f z := by
  intro G _ _ _ _ _ _ _ _ μ _ R₀ R hR₀ hR μ₀ μR _ _ _ _ U _ ν _ j hj hst f hf hinv hint hz' z hz
  obtain ⟨z', hz'⟩ := hz'
  have : LocallyCompactSpace R₀ := hR₀.locallyCompactSpace
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  have : SecondCountableTopology R₀ := TopologicalSpace.Subtype.secondCountableTopology (R₀ : Set G)
  have : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  obtain ⟨β₀, -, hβ₀⟩ := exists_isCosetCutoff (μT := μ₀) hR₀
  obtain ⟨β, -, hβ⟩ := exists_isCosetCutoff (μT := μR) hR
  obtain ⟨F, hF⟩ : ∃ F : G → ℂ, F = fun x => (β₀ x : ℝ) • f x := ⟨_, rfl⟩
  have hFm : Measurable F := by rw [hF]; exact hβ₀.1.coe_nnreal_real.smul hf
  have hc0 : ∀ y, Integrable (fun r : R₀ => (β₀ (r * y) : ℝ)) μ₀ ∧ ∫ r : R₀, (β₀ (r * y) : ℝ) ∂μ₀ = 1 :=
    fun y => integrable_of_lintegral_eq_one (hβ₀.1.comp (measurable_subtype_coe.mul_const y)) (hβ₀.2 y)
  have hFe : ∀ y, ∀ r : R₀, F (r * y) = (β₀ (r * y) : ℝ) • f y := fun y r => by
    rw [hF]
    show (β₀ (r * y) : ℝ) • f (r * y) = _
    rw [hinv r r.2 y]
  have hFr : ∀ y, Integrable (fun r : R₀ => F (r * y)) μ₀ ∧ ∫ r : R₀, F (r * y) ∂μ₀ = f y := fun y => by
    simp only [hFe y]
    exact ⟨(hc0 y).1.smul_const _, by rw [integral_smul_const, (hc0 y).2, one_smul]⟩
  have hFn : ∀ y, ∫ r : R₀, ‖F (r * y)‖ ∂μ₀ = ‖f y‖ := fun y => by
    simp only [hFe y, norm_smul, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    rw [integral_mul_const, (hc0 y).2, one_mul]
  have hFn' : ∀ y, ∫⁻ r : R₀, ‖F (r * y)‖ₑ ∂μ₀ = ‖f y‖ₑ := fun y => by
    have e : ∀ r : R₀, ‖F (r * y)‖ₑ = (β₀ (r * y) : ℝ≥0∞) * ‖f y‖ₑ := fun r => by
      rw [hFe y r, enorm_smul]
      simp
    rw [lintegral_congr e, lintegral_mul_const' _ _ enorm_ne_top, hβ₀.2, one_mul]
  have hm : Measurable (fun p : U × R₀ => (p.2 : G) * j p.1) :=
    (measurable_subtype_coe.comp measurable_snd).mul (hj.comp measurable_fst)
  have hM := map_val_eq_map_stages μ₀ μR ν hj hst
  have hP : ∀ h, Integrable ((fun y => F (y * h)) ∘ fun p : U × R₀ => (p.2 : G) * j p.1) (ν.prod μ₀) := fun h => by
    refine (integrable_prod_iff ((hFm.comp (measurable_mul_const h)).comp hm).aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine Eventually.of_forall fun u => ?_
      simpa [Function.comp_def, mul_assoc] using (hFr (j u * h)).1
    · have e : ∀ u, ∫ r : R₀, ‖((fun y => F (y * h)) ∘ fun p : U × R₀ => (p.2 : G) * j p.1) (u, r)‖ ∂μ₀ = ‖f (j u * h)‖ :=
        fun u => by simpa [Function.comp_def, mul_assoc] using hFn (j u * h)
      exact (hint h).norm.congr (Eventually.of_forall fun u => (e u).symm)
  have hRint : ∀ h, Integrable (fun r : R => F (r * h)) μR := fun h => by
    have hi : Integrable (fun y => F (y * h)) (μR.map Subtype.val) := by
      rw [hM]
      exact (integrable_map_measure (hFm.comp (measurable_mul_const h)).aestronglyMeasurable hm.aemeasurable).2 (hP h)
    exact hi.comp_measurable measurable_subtype_coe
  have hRval : ∀ h, ∫ r : R, F (r * h) ∂μR = ∫ u, f (j u * h) ∂ν := fun h => by
    have e1 : ∫ r : R, F (r * h) ∂μR = ∫ y, F (y * h) ∂(μR.map Subtype.val) :=
      (integral_map measurable_subtype_coe.aemeasurable (hFm.comp (measurable_mul_const h)).aestronglyMeasurable).symm
    rw [e1, hM, integral_map (f := fun y => F (y * h)) hm.aemeasurable (hFm.comp (measurable_mul_const h)).aestronglyMeasurable]
    have e2 := integral_prod _ (hP h)
    simp only [Function.comp_def] at e2
    rw [e2]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simpa [mul_assoc] using (hFr (j u * h)).2
  have hGint : Integrable F μ := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_eq_cutoff_inner hβ hFm.enorm]
    have e : ∀ x, ∫⁻ r : R, ‖F (r * x)‖ₑ ∂μR = ∫⁻ u, ‖f (j u * x)‖ₑ ∂ν := fun x => by
      rw [hst (fun y => ‖F (y * x)‖ₑ) (hFm.comp (measurable_mul_const x)).enorm]
      refine lintegral_congr fun u => ?_
      have h1 := hFn' (j u * x)
      simp only [mul_assoc] at h1 ⊢
      exact h1
    simp only [e]
    obtain ⟨hi, -⟩ := hz'.cutoff hβ
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) hi.2
    rw [enorm_smul, ← ofReal_integral_norm_eq_lintegral_enorm (hint x)]
    simp [Real.enorm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hq : IsQuotIntL1 μR μ (fun g => ∫ u, f (j u * g) ∂ν) (∫ x, F x ∂μ) :=
    ⟨F, hGint, hRint, fun h => (hRval h).symm, rfl⟩
  exact ⟨F, hGint, fun h => (hFr h).1, fun h => (hFr h).2.symm, hz.unique hR hq⟩

end GlobalTheory.Unf
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.QuotFubini

theorem existsUnique_mul_mem {G : Type} [Group G] {Γ R : Subgroup G} (hΓ : Γ ≤ R) {S : Set G}
    (hS : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ S) (h : G) (r : R) :
    ∃! γ : Γ.subgroupOf R, γ • r ∈ {r : R | (r : G) * h ∈ S} := by
  obtain ⟨γ, h1, h2⟩ := hS ((r : G) * h)
  refine ⟨⟨⟨γ, hΓ γ.2⟩, γ.2⟩, ?_, fun δ hδ => ?_⟩
  · change ((γ : G) * r) * h ∈ S
    rw [mul_assoc]; exact h1
  · have h3 : (⟨((δ : R) : G), δ.2⟩ : Γ) = γ := by
      refine h2 _ ?_
      have : (((δ : R) : G) * r) * h ∈ S := hδ
      rw [mul_assoc] at this
      exact this
    ext
    exact congrArg (fun x : Γ => (x : G)) h3

end GlobalTheory.QuotFubini

namespace GlobalTheory


open GlobalTheory.QuotFubini in
theorem quot_fubini_mean : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (R Γ : Subgroup G), Γ ≤ R → IsClosed (R : Set G) → Countable Γ → DiscreteTopology Γ → ∀ (μR : Measure R), μR.IsHaarMeasure → ∀ (𝓡 : Set R) (𝓑 : Set G), IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR → IsFundamentalDomain Γ 𝓑 μ → ∀ f : G → ℂ, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → IsQuotIntL1 μR μ (fun h => ∫ r in 𝓡, f ((r : G) * h) ∂μR) (∫ g in 𝓑, f g ∂μ) := by
  intro G _ _ _ _ _ _ _ _ μ _ R Γ hΓR hR hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑 f hf hfΓ hf𝓑 hf𝓡
  obtain ⟨-, S, hSm, hS⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain Γ
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hSfd : IsFundamentalDomain Γ S μ := IsFundamentalDomain.mk' hSm.nullMeasurableSet hS
  have hfΓ' : ∀ (γ : Γ) (x : G), f (γ • x) = f x := fun γ x => hfΓ γ γ.2 x
  have hmh : ∀ h : G, Measurable (fun r : R => (r : G) * h) := fun h =>
    (continuous_subtype_val.mul continuous_const).measurable
  have hSh : ∀ h : G, MeasurableSet {r : R | (r : G) * h ∈ S} := fun h => hmh h hSm
  have hShfd : ∀ h : G, IsFundamentalDomain (Γ.subgroupOf R) {r : R | (r : G) * h ∈ S} μR := fun h =>
    IsFundamentalDomain.mk' (hSh h).nullMeasurableSet (existsUnique_mul_mem hΓR hS h)
  have hfR : ∀ h : G, ∀ (γ : Γ.subgroupOf R) (r : R), f (((γ • r : R) : G) * h) = f ((r : G) * h) := by
    intro h γ r
    change f ((((γ : R) : G) * r) * h) = _
    rw [mul_assoc]; exact hfΓ _ γ.2 _
  have hind : ∀ h : G, (fun r : R => S.indicator f ((r : G) * h)) =
      {r : R | (r : G) * h ∈ S}.indicator (fun r : R => f ((r : G) * h)) := by
    intro h; ext r
    by_cases hr : (r : G) * h ∈ S
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem (show r ∈ {r : R | (r : G) * h ∈ S} from hr)]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem (show r ∉ {r : R | (r : G) * h ∈ S} from hr)]
  refine ⟨S.indicator f, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrable_indicator_iff hSm).2 ((hSfd.integrableOn_iff h𝓑 hfΓ').2 hf𝓑)
  · rw [hind h]
    exact (integrable_indicator_iff (hSh h)).2 (((hShfd h).integrableOn_iff h𝓡 (hfR h)).2 (hf𝓡 h))
  · rw [hind h, integral_indicator (hSh h)]
    exact (h𝓡.setIntegral_eq (hShfd h) (hfR h))
  · rw [integral_indicator hSm]
    exact h𝓑.setIntegral_eq hSfd hfΓ'

end GlobalTheory
end
