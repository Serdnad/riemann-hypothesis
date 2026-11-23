module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Aesop.Main
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle139
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle119
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle177
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeNonzeroVectorPairNormalForms
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle178
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
open scoped Pointwise

noncomputable section

namespace GlobalTheory.IwConst.VagBody

theorem integral_squeeze {X : Type} [MeasurableSpace X] (ν : Measure X) (φ : X → ℝ) (A B : Set X)
    (hφ : Measurable φ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hB' : ν B ≠ ⊤)
    (h0 : ∀ x, 0 ≤ φ x) (h1 : ∀ x, φ x ≤ 1) (hA1 : ∀ x ∈ A, φ x = 1) (hB0 : ∀ x, x ∉ B → φ x = 0) :
    ν.real A ≤ ∫ x, φ x ∂ν ∧ ∫ x, φ x ∂ν ≤ ν.real B := by
  have hsub : A ⊆ B := by
    intro x hx
    by_contra hxB
    have h := hA1 x hx
    rw [hB0 x hxB] at h
    exact zero_ne_one h
  have hA' : ν A ≠ ⊤ := ne_top_of_le_ne_top hB' (measure_mono hsub)
  have lo : ∀ x, A.indicator (fun _ => (1:ℝ)) x ≤ φ x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, hA1 x hx]
    · simp only [Set.indicator, hx, if_false]
      exact h0 x
  have hi : ∀ x, φ x ≤ B.indicator (fun _ => (1:ℝ)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      exact h1 x
    · simp only [Set.indicator, hx, if_false]
      exact le_of_eq (hB0 x hx)
  have iB : Integrable (B.indicator fun _ => (1:ℝ)) ν :=
    (integrable_indicator_iff hB).2 (integrableOn_const hB')
  have iA : Integrable (A.indicator fun _ => (1:ℝ)) ν :=
    (integrable_indicator_iff hA).2 (integrableOn_const hA')
  have iφ : Integrable φ ν := by
    refine iB.mono' hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact hi x
  have eA : ∫ x, A.indicator (fun _ => (1:ℝ)) x ∂ν = ν.real A := by
    rw [integral_indicator_const _ hA, smul_eq_mul, mul_one]
  have eB : ∫ x, B.indicator (fun _ => (1:ℝ)) x ∂ν = ν.real B := by
    rw [integral_indicator_const _ hB, smul_eq_mul, mul_one]
  refine ⟨?_, ?_⟩
  · rw [← eA]
    exact integral_mono iA iφ lo
  · rw [← eB]
    exact integral_mono iφ iB hi

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem isCompact_body (ρ : V → ℝ) (hc : Continuous ρ) (h0 : ∀ v, 0 ≤ ρ v)
    (hs : ∀ s : ℝ, 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) (hd : ∀ v, ρ v = 0 → v = 0) (t : ℝ) :
    IsCompact {v | ρ v ≤ t} := by
  obtain ⟨m, hm, hmρ⟩ : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Metric.sphere (0 : V) 1, m ≤ ρ u := by
    rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨u0, hu0, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hne hc.continuousOn
      refine ⟨ρ u0, ?_, fun u hu => isMinOn_iff.1 hmin u hu⟩
      rcases (h0 u0).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : u0 = 0 := hd u0 h.symm
        rw [mem_sphere_zero_iff_norm, hz, norm_zero] at hu0
        exact zero_ne_one hu0
  have hbd : ∀ v, m * ‖v‖ ≤ ρ v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, norm_zero, mul_zero]
      exact h0 0
    · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
      have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 := hmρ _ hu
      have h2 : ρ v = ‖v‖ * ρ (‖v‖⁻¹ • v) := by
        rw [← hs ‖v‖ (norm_nonneg v), smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [h2]
      nlinarith
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hc continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : V)) (r := t / m)).subset ?_
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hm]
  have h3 := hbd v
  have h4 : ρ v ≤ t := hv
  nlinarith


omit [FiniteDimensional ℝ V] in
theorem body_eq_smul (ρ : V → ℝ) (hs : ∀ s : ℝ, 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) {t : ℝ} (ht : 0 < t) :
    {v | ρ v ≤ t} = t • {v | ρ v ≤ 1} := by
  ext v
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', Set.mem_setOf_eq, Set.mem_setOf_eq,
    hs _ (inv_nonneg.2 ht.le), inv_mul_le_iff₀ ht, mul_one]


omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem exists_cutoff (ρ : V → ℝ) (hc : Continuous ρ) {s t : ℝ} (hst : s < t) :
    ∃ φ : V → ℝ, Continuous φ ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 1) ∧ (∀ x, ρ x ≤ s → φ x = 1) ∧
      ∀ x, ¬ ρ x ≤ t → φ x = 0 := by
  have hpos : 0 < t - s := sub_pos.2 hst
  refine ⟨fun x => max 0 (min 1 ((t - ρ x) / (t - s))), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.max (continuous_const.min ((continuous_const.sub hc).div_const _))
  · intro x
    exact le_max_left _ _
  · intro x
    exact max_le zero_le_one (min_le_left _ _)
  · intro x hx
    have h1 : 1 ≤ (t - ρ x) / (t - s) := by
      rw [le_div_iff₀ hpos]
      linarith
    show max 0 (min 1 ((t - ρ x) / (t - s))) = 1
    rw [min_eq_left h1, max_eq_right zero_le_one]
  · intro x hx
    have h1 : (t - ρ x) / (t - s) ≤ 0 := by
      rw [div_le_iff₀ hpos]
      push_neg at hx
      linarith
    show max 0 (min 1 ((t - ρ x) / (t - s))) = 0
    exact max_eq_left (le_trans (min_le_right _ _) h1)

theorem tendsto_body : ∀ (α V : Type) [MeasurableSpace α] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure α) [IsFiniteMeasure μ] (c : α → V) (lam : Measure V) [lam.IsAddHaarMeasure] (d : ℕ) (ρ : V → ℝ), Measurable c → Continuous ρ → (∀ v, 0 ≤ ρ v) → (∀ (s : ℝ), 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) → (∀ v, ρ v = 0 → v = 0) → Vag μ c lam d → Filter.Tendsto (fun r : ℝ => μ {g | ρ (c g) ≤ r} / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam {v | ρ v ≤ 1})) := by
  intro α V _ _ _ _ _ _ μ _ c lam _ d ρ hcm hρ h0 hs hd hv
  have hK : ∀ t, IsCompact {v | ρ v ≤ t} := fun t => isCompact_body ρ hρ h0 hs hd t
  have hfin : ∀ t, lam {v | ρ v ≤ t} ≠ ⊤ := fun t => (hK t).measure_lt_top.ne
  have hmV : ∀ t, MeasurableSet {v | ρ v ≤ t} := fun t =>
    measurableSet_le hρ.measurable measurable_const
  have hmα : ∀ t, MeasurableSet {g | ρ (c g) ≤ t} := fun t =>
    measurableSet_le (hρ.measurable.comp hcm) measurable_const
  have hmβ : ∀ r t : ℝ, MeasurableSet {g | ρ (r • c g) ≤ t} := fun r t =>
    measurableSet_le (hρ.measurable.comp (hcm.const_smul r)) measurable_const
  have hhom : ∀ r : ℝ, 0 < r → ∀ v, ρ (r⁻¹ • v) = r⁻¹ * ρ v := fun r hr v =>
    hs _ (inv_nonneg.2 hr.le) v
  have hscale : ∀ x : ℝ, 0 < x →
      lam.real {v | ρ v ≤ x} = x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1} := by
    intro x hx
    simp only [measureReal_def]
    rw [body_eq_smul ρ hs hx, Measure.addHaar_smul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), abs_of_pos (pow_pos hx _)]
  have hcont : Filter.Tendsto (fun x : ℝ => x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})
      (nhds 1) (nhds (lam.real {v | ρ v ≤ 1})) := by
    have h : Filter.Tendsto (fun x : ℝ => x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})
        (nhds 1) (nhds ((1 : ℝ) ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})) :=
      ((continuous_pow _).mul continuous_const).tendsto 1
    rwa [one_pow, one_mul] at h
  have up : ∀ a, lam.real {v | ρ v ≤ 1} < a → ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} < a := by
    intro a ha
    have h2 := hcont.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    obtain ⟨x, hxa, hx⟩ := ((h2.eventually (gt_mem_nhds ha)).and (Ioo_mem_nhdsGT one_lt_two)).exists
    obtain ⟨φ, hφc, hφ0, hφ1, hφA, hφB⟩ := exists_cutoff ρ hρ hx.1
    have hsupp : HasCompactSupport φ := HasCompactSupport.intro (hK x) (fun v hv' => hφB v hv')
    have hlim : ∫ v, φ v ∂lam < a := by
      have h3 := (integral_squeeze lam φ _ _ hφc.measurable (hmV 1) (hmV x) (hfin x) hφ0 hφ1
        hφA hφB).2
      have h4 := hscale x (by linarith [hx.1])
      linarith
    filter_upwards [(hv φ hφc hsupp).eventually (gt_mem_nhds hlim), self_mem_nhdsWithin] with r hr hr0
    have hr0' : 0 < r := hr0
    have hsq := (integral_squeeze μ (fun g => φ (r⁻¹ • c g)) _ _
      (hφc.measurable.comp (hcm.const_smul r⁻¹)) (hmα r) (hmβ r⁻¹ x) (measure_ne_top _ _)
      (fun g => hφ0 _) (fun g => hφ1 _)
      (fun g hg => hφA _ (by rw [hhom r hr0', inv_mul_le_iff₀ hr0', mul_one]; exact hg))
      (fun g hg => hφB _ hg)).1
    calc (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r}
        ≤ (r ^ d)⁻¹ * ∫ g, φ (r⁻¹ • c g) ∂μ :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.2 (pow_nonneg hr0'.le d))
      _ < a := hr
  have lo : ∀ a, a < lam.real {v | ρ v ≤ 1} → ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      a < (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} := by
    intro a ha
    have h2 := hcont.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    obtain ⟨x, hxa, hx⟩ := ((h2.eventually (lt_mem_nhds ha)).and (Ioo_mem_nhdsLT zero_lt_one)).exists
    obtain ⟨φ, hφc, hφ0, hφ1, hφA, hφB⟩ := exists_cutoff ρ hρ hx.2
    have hsupp : HasCompactSupport φ := HasCompactSupport.intro (hK 1) (fun v hv' => hφB v hv')
    have hlim : a < ∫ v, φ v ∂lam := by
      have h3 := (integral_squeeze lam φ _ _ hφc.measurable (hmV x) (hmV 1) (hfin 1) hφ0 hφ1
        hφA hφB).1
      have h4 := hscale x hx.1
      linarith
    filter_upwards [(hv φ hφc hsupp).eventually (lt_mem_nhds hlim), self_mem_nhdsWithin] with r hr hr0
    have hr0' : 0 < r := hr0
    have hsq := (integral_squeeze μ (fun g => φ (r⁻¹ • c g)) _ _
      (hφc.measurable.comp (hcm.const_smul r⁻¹)) (hmβ r⁻¹ x) (hmα r) (measure_ne_top _ _)
      (fun g => hφ0 _) (fun g => hφ1 _) (fun g hg => hφA _ hg)
      (fun g hg => hφB _ (by rw [hhom r hr0', inv_mul_le_iff₀ hr0', mul_one]; exact hg))).2
    calc a < (r ^ d)⁻¹ * ∫ g, φ (r⁻¹ • c g) ∂μ := hr
      _ ≤ (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.2 (pow_nonneg hr0'.le d))
  have hreal : Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r})
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam.real {v | ρ v ≤ 1})) :=
    tendsto_order.2 ⟨lo, up⟩
  have h5 := ENNReal.tendsto_ofReal hreal
  rw [measureReal_def, ENNReal.ofReal_toReal (hfin 1)] at h5
  refine h5.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : 0 < r := hr
  have hp : 0 < r ^ d := pow_pos hr0 d
  rw [measureReal_def, ENNReal.ofReal_mul (inv_nonneg.2 hp.le),
    ENNReal.ofReal_toReal (measure_ne_top _ _), div_eq_mul_inv, ENNReal.ofReal_inv_of_pos hp, mul_comm]

end GlobalTheory.IwConst.VagBody
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.CloseLevi

variable {n : ℕ} {ε : Fin n → Bool}

theorem isClosed_stab {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} := by
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) := GlobalTheory.FlagLeviGroup.continuous_uMat
  have h : {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} =
      ⋂ i, ⋂ y ∈ (W i : Set (Fin n → ℂ)),
        (fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [h]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => ?_
  exact (W i).closed_of_finiteDimensional.preimage (hc.matrix_mulVec continuous_const)

theorem mem_flagM_of_keeps {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) {l : Formalism.REAL.UJ ε}
    (hl : l ∈ maxK ε) (h : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i) : l ∈ flagM ε W := by
  have hl' : (uMat l)ᴴ * uMat l = 1 := hl
  show ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i
  intro i y hy
  exact ⟨h i y hy, GlobalTheory.FlagLeviGroup.inv_keeps hl' (W i) (h i) y hy⟩

private theorem exists_unit_valuation_le_subset_nhds {G : Type} [Group G] [TopologicalSpace G] {f : G → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) (h1 : ∀ g, f g = 0 ↔ g = 1) (hB : IsCompact {g | f g ≤ 1})
    {O : Set G} (hO : IsOpen O) (h1O : (1 : G) ∈ O) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ g, f g < ρ → g ∈ O := by
  have hC : IsCompact ({g | f g ≤ 1} ∩ Oᶜ) := hB.inter_right hO.isClosed_compl
  rcases ({g | f g ≤ 1} ∩ Oᶜ).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun g hg => ?_⟩
    by_contra hgO
    have hgC : g ∈ ({g | f g ≤ 1} ∩ Oᶜ) := ⟨le_of_lt hg, hgO⟩
    rw [hE] at hgC
    simpa using hgC
  · obtain ⟨c, ⟨_, hcO⟩, hmin⟩ := hC.exists_isMinOn hne hf.continuousOn
    have hc : 0 < f c := by
      rcases (h0 c).lt_or_eq with h | h
      · exact h
      · exfalso
        have hc1 : c = 1 := (h1 c).1 h.symm
        rw [hc1] at hcO
        exact absurd h1O hcO
    refine ⟨min 1 (f c), lt_min one_pos hc, fun g hg => ?_⟩
    by_contra hgO
    have hgC : g ∈ ({g | f g ≤ 1} ∩ Oᶜ) := ⟨(lt_of_lt_of_le hg (min_le_left _ _)).le, hgO⟩
    have hcg : f c ≤ f g := isMinOn_iff.1 hmin g hgC
    exact absurd (lt_of_lt_of_le hg (min_le_right _ _)) (not_lt.2 hcg)

theorem close_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {f : G → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) (h1 : ∀ g, f g = 0 ↔ g = 1) (hB : IsCompact {g | f g ≤ 1})
    {K P L : Set G} (hK : IsCompact K) (hP : IsClosed P) (hL : ∀ k ∈ K, k⁻¹ ∈ P → k⁻¹ ∈ L) {t : ℝ} (ht : 0 < t) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ P, ∀ k ∈ K, f (p * k) ≤ r → ∃ l ∈ L, f (l * k) < t := by

  have hloc : ∀ k ∈ K, ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k),
      ∀ p ∈ P, f (p * z.2) ≤ z.1 → ∃ l ∈ L, f (l * z.2) < t := by
    intro k hk
    by_cases hkP : k⁻¹ ∈ P
    ·
      have hkL := hL k hk hkP
      have hc : Continuous fun x : G => f (k⁻¹ * x) := hf.comp (continuous_const.mul continuous_id)
      have hopen : IsOpen {x : G | f (k⁻¹ * x) < t} := isOpen_lt hc continuous_const
      have hmem : k ∈ {x : G | f (k⁻¹ * x) < t} := by
        show f (k⁻¹ * k) < t
        rw [inv_mul_cancel, (h1 1).2 rfl]
        exact ht
      have hev : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.2 ∈ {x : G | f (k⁻¹ * x) < t} :=
        (continuous_snd.tendsto ((0 : ℝ), k)).eventually_mem (hopen.mem_nhds hmem)
      filter_upwards [hev] with z hz
      intro p _ _
      exact ⟨k⁻¹, hkL, hz⟩
    ·
      have hcont : Continuous (fun q : G × G => q.1 * q.2⁻¹) := continuous_fst.mul continuous_snd.inv
      have hopen : IsOpen ((fun q : G × G => q.1 * q.2⁻¹) ⁻¹' Pᶜ) := hP.isOpen_compl.preimage hcont
      have hmem : ((1 : G), k) ∈ (fun q : G × G => q.1 * q.2⁻¹) ⁻¹' Pᶜ := by
        show (1 : G) * k⁻¹ ∈ Pᶜ
        rw [one_mul]
        exact hkP
      obtain ⟨O, V, hO, hV, h1O, hkV, hOV⟩ := isOpen_prod_iff.1 hopen 1 k hmem
      obtain ⟨ρ, hρ, hρO⟩ := exists_unit_valuation_le_subset_nhds hf h0 h1 hB hO h1O
      have e1 : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.1 < ρ :=
        (continuous_fst.tendsto ((0 : ℝ), k)).eventually (gt_mem_nhds hρ)
      have e2 : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.2 ∈ V :=
        (continuous_snd.tendsto ((0 : ℝ), k)).eventually_mem (hV.mem_nhds hkV)
      filter_upwards [e1, e2] with z hz1 hz2
      intro p hp hpz
      exfalso
      have hO' : p * z.2 ∈ O := hρO _ (lt_of_le_of_lt hpz hz1)
      have hmem' := hOV (Set.mk_mem_prod hO' hz2)
      simp only [Set.mem_preimage, mul_inv_cancel_right, Set.mem_compl_iff] at hmem'
      exact hmem' hp
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
    (P := fun r x => ∀ p ∈ P, f (p * x) ≤ r → ∃ l ∈ L, f (l * x) < t) hloc
  have hpos : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r := eventually_mem_nhdsWithin
  obtain ⟨r, hr, hrK⟩ := (hpos.and (hev.filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨r, hr, fun p hp k hk hpk => hrK k hk p hp hpk⟩

theorem nrm_uMat_eq_zero (g : Formalism.REAL.UJ ε) : nrm (uMat g - 1) = 0 ↔ g = 1 := by
  rw [nrm_eq_zero, sub_eq_zero]
  constructor
  · intro h
    apply Subtype.ext
    exact Units.ext h
  · rintro rfl
    exact GlobalTheory.FlagLeviGroup.uMat_one

theorem close_levi : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧
    ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, nrm (uMat (u * m * k) - 1) ≤ r →
      ∃ l ∈ maxK ε ∩ flagM ε W, nrm (uMat (l * k) - 1) < t := by
  intro n ε a j W hW t ht

  have hL : ∀ k ∈ maxK ε, k⁻¹ ∈ {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} →
      k⁻¹ ∈ maxK ε ∩ flagM ε W := by
    intro k hk hkP
    have hk' : k⁻¹ ∈ maxK ε := (GlobalTheory.FlagLeviGroup.compactSub (ε := ε)).inv_mem hk
    exact Set.mem_inter hk' (mem_flagM_of_keeps W hk' hkP)
  obtain ⟨r, hr, hrP⟩ := close_of_compact (G := Formalism.REAL.UJ ε) (f := fun g => nrm (uMat g - 1))
    (continuous_nrm_uMat ε) (fun g => nrm_nonneg _) (fun g => nrm_uMat_eq_zero g) (isCompact_hsBall ε 1)
    (isCompact_maxK ε) (isClosed_stab W) hL ht
  refine ⟨r, hr, fun u hu m hm k hk hle => ?_⟩
  have hm' : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
  have hum : u * m ∈ {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} := by
    rw [Set.mem_setOf_eq]
    intro i y hy
    rw [GlobalTheory.FlagLeviGroup.uMat_mul, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.FlagMeas.UnipRad.keeps hW u hu i _ (hm' i y hy).1
  exact hrP (u * m) hum k hk hle

end GlobalTheory.IwConst.CloseLevi
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.FlagMem

variable {n : ℕ} {ε : Fin n → Bool}

theorem form_mul (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat g *ᵥ y)) = star (uMat g⁻¹ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  simpa using GlobalTheory.FlagLeviGroup.form_inv g⁻¹ x y

theorem Jm_mul_self : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem Jm_mul_conjTranspose (m : Formalism.REAL.UJ ε) :
    Formalism.REAL.Jm ε * (uMat m)ᴴ = uMat m⁻¹ * Formalism.REAL.Jm ε := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * uMat m⁻¹ = ((uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m) * uMat m⁻¹ := by rw [hm]
      _ = _ := by rw [Matrix.mul_assoc, GlobalTheory.FlagLeviGroup.uMat_mul_inv, Matrix.mul_one]
  calc Formalism.REAL.Jm ε * (uMat m)ᴴ
      = Formalism.REAL.Jm ε * ((uMat m)ᴴ * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = _ := by rw [← h1, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

theorem form_conjTranspose (m : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat m)ᴴ *ᵥ y)) = star ((uMat m⁻¹)ᴴ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Jm_mul_conjTranspose, ← Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

theorem lowers_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    (∀ u ∈ flagN ε W, uMat u - 1 ∈ lowers ε W) ∧
      ∀ m ∈ flagM ε W, uMat m ∈ keeps ε W ∧ (uMat m)ᴴ ∈ keeps ε W := by
  intro n ε a j W hW
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · obtain ⟨N, hN⟩ := (GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW).1
    have hu' : u⁻¹ ∈ flagN ε W := by
      rw [← hN] at hu ⊢
      exact N.inv_mem hu
    simp only [lowers, Submodule.mem_inf, Submodule.mem_iInf, mem_into, Matrix.sub_mulVec, Matrix.one_mulVec]
    refine ⟨⟨hu.1, hu.2⟩, fun i y hy x hx => ?_⟩
    have h := hy _ (hu'.1 i x hx)
    rw [star_sub, sub_dotProduct] at h
    rw [Matrix.mulVec_sub, dotProduct_sub, form_mul]
    exact h
  · have hm' : m⁻¹ ∈ flagM ε W := (GlobalTheory.FlagLeviGroup.leviSub (ε := ε) W).inv_mem hm
    simp only [GlobalTheory.IwConst.keeps, Submodule.mem_inf, Submodule.mem_iInf, mem_into]
    refine ⟨⟨fun i y hy => (hm i y hy).1, fun i y hy x hx => ?_⟩,
      ⟨fun i y hy => (hm i y hy).2, fun i y hy x hx => ?_⟩⟩
    · rw [form_mul]
      exact hy _ (hm' i x hx).1
    · rw [form_conjTranspose]
      exact hy _ (hm' i x hx).2

end GlobalTheory.IwConst.FlagMem
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.exists_smooth_average_eq_of_mem_lowKSub' : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (w : H), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → w ∈ lowKSub ε lam σ → w ≠ 0 → ∀ u ∈ lowKSub ε lam σ, ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g : UJ ε, F (fun i j => umat g i j) • σ (umat g) w ∂(muG ε) := by
  first | exact @GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub | exact GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub | (intros; apply GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.lattice_nonzero_vector_pair_normal_forms : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ), ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → (∀ 𝔞 Λ', 𝔞 ≠ ⊥ → Submodule.IsFullLattice E Λ' → Submodule.IsFullLattice E (Lf 𝔞 Λ') ∧ Pi.single 0 1 ∈ Lf 𝔞 Λ') ∧ (∀ Λ : Submodule (𝓞 E) (Fin (k + 1) → E), Submodule.IsFullLattice E Λ → ∀ x ∈ Λ, x ≠ 0 → ∃ (γ : GL (Fin (k + 1)) E) (𝔞 : Ideal (𝓞 E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), 𝔞 ≠ ⊥ ∧ Submodule.IsFullLattice E Λ' ∧ (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ x = Pi.single 0 1 ∧ ∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ y ∈ Lf 𝔞 Λ' ↔ y ∈ Λ) ∧ ∀ 𝔞 𝔟 Λ₁ Λ₂, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → Submodule.IsFullLattice E Λ₁ → Submodule.IsFullLattice E Λ₂ → ∀ γ : GL (Fin (k + 1)) E, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Pi.single 0 1 = Pi.single 0 1 → ((∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ y ∈ Lf 𝔟 Λ₂ ↔ y ∈ Lf 𝔞 Λ₁) ↔ 𝔞 = 𝔟 ∧ (∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).submatrix Fin.succ Fin.succ *ᵥ y ∈ Λ₂ ↔ y ∈ Λ₁) ∧ ∀ y ∈ Λ₁, ∀ t ∈ 𝔞, (t : E) * ((fun b => (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) 0 b.succ) ⬝ᵥ y) ∈ (algebraMap (𝓞 E) E).range) := by
  first | exact @GlobalTheory.LatVecPair.classes | exact GlobalTheory.LatVecPair.classes | (intros; apply GlobalTheory.LatVecPair.classes <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.smallBall_asymptotics_pi_weighted : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)] (ρ : ∀ i, X i → ℝ) (d : ι → ℕ) (w : ι → ℝ), (∀ i, Measurable (ρ i)) → (∀ i x, 0 ≤ ρ i x) → (∀ i, 0 < w i) → (∀ i, Filter.Tendsto (fun r : ℝ => ν i {x | Real.sqrt (ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1)))) → Filter.Tendsto (fun r : ℝ => Measure.pi ν {x | Real.sqrt (∑ i, w i * ρ i (x i)) ≤ r} / ENNReal.ofReal (r ^ ∑ i, d i)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (∏ i, w i ^ (-((d i : ℝ) / 2))) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (∑ i, d i))) 1))) := by
  first | exact @GlobalTheory.smallBall_pi_weight | exact GlobalTheory.smallBall_pi_weight | (intros; apply GlobalTheory.smallBall_pi_weight <;> assumption)
end
