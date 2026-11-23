module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle115
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle170
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem translate_inter_null {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    (μ : Measure G) (fund : Set G) (hμ : ∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) (hf : MeasurableSet fund)
    (hd : ∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) {a b : G} (ha : a ∈ Γ) (hb : b ∈ Γ)
    (hab : a ≠ b) :
    μ ((fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund) = 0 := by
  have hc : a⁻¹ * b ∈ Γ := Γ.mul_mem (Γ.inv_mem ha) hb
  have hc1 : a⁻¹ * b ≠ 1 := fun h => hab (inv_mul_eq_one.mp h)
  have hset : (fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund
      ⊆ (fun y => a⁻¹ * y) ⁻¹' ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund) := by
    rintro y ⟨h1, h2⟩
    refine ⟨⟨b⁻¹ * y, h2, ?_⟩, h1⟩
    show a⁻¹ * b * (b⁻¹ * y) = a⁻¹ * y
    group
  refine measure_mono_null hset (nonpos_iff_eq_zero.mp ?_)
  calc μ ((fun y => a⁻¹ * y) ⁻¹' ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund))
      ≤ μ.map (fun y => a⁻¹ * y) ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund) :=
        MeasureTheory.Measure.le_map_apply (measurable_const_mul _).aemeasurable _
    _ = 0 := by rw [hμ _ (Γ.inv_mem ha)]; exact hd _ hc hc1

private theorem withDensity_preimage_inv_mul_eq_setLIntegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) (Φ : G → ENNReal) (hΦ : Measurable Φ) (a : G) (hμa : μ.map (fun y => a * y) = μ)
    (fund : Set G) (hf : MeasurableSet fund) :
    μ.withDensity Φ ((fun y => a⁻¹ * y) ⁻¹' fund) = ∫⁻ g in fund, Φ (a * g) ∂μ := by
  classical
  have hT : MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' fund) := hf.preimage (measurable_const_mul _)
  rw [withDensity_apply _ hT, ← lintegral_indicator hT, ← lintegral_indicator hf]
  have hm : Measurable (((fun y => a⁻¹ * y) ⁻¹' fund).indicator Φ) := hΦ.indicator hT
  have key := MeasureTheory.lintegral_map (μ := μ) hm (measurable_const_mul a)
  rw [hμa] at key
  rw [key]
  congr 1
  funext x
  by_cases hx : x ∈ fund
  · have hx' : a * x ∈ (fun y => a⁻¹ * y) ⁻¹' fund := by
      show a⁻¹ * (a * x) ∈ fund
      rwa [inv_mul_cancel_left]
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
  · have hx' : a * x ∉ (fun y => a⁻¹ * y) ⁻¹' fund := by
      show a⁻¹ * (a * x) ∉ fund
      rwa [inv_mul_cancel_left]
    rw [Set.indicator_apply, Set.indicator_apply, if_neg hx', if_neg hx]

private theorem withDensity_preimage_mul_eq_of_invariant {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) (Φ : G → ENNReal) (hΦ : Measurable Φ) (s : G) (hμs : μ.map (fun y => s * y) = μ)
    (hΦs : ∀ g, Φ (s * g) = Φ g) (Q : Set G) (hQ : MeasurableSet Q) :
    μ.withDensity Φ ((fun y => s * y) ⁻¹' Q) = μ.withDensity Φ Q := by
  classical
  have hT : MeasurableSet ((fun y => s * y) ⁻¹' Q) := hQ.preimage (measurable_const_mul _)
  rw [withDensity_apply _ hT, withDensity_apply _ hQ, ← lintegral_indicator hT, ← lintegral_indicator hQ]
  have key := MeasureTheory.lintegral_map (μ := μ) (hΦ.indicator hQ) (measurable_const_mul s)
  rw [hμs] at key
  rw [key]
  congr 1
  funext y
  by_cases hy : s * y ∈ Q
  · have hy' : y ∈ (fun y => s * y) ⁻¹' Q := hy
    rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy, hΦs]
  · have hy' : y ∉ (fun y => s * y) ⁻¹' Q := hy
    rw [Set.indicator_apply, Set.indicator_apply, if_neg hy', if_neg hy]

theorem lintegral_tsum_cosets_eq_covol : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ S : Subgroup G) (μ : Measure G) (fund : Set G) (Φ : G → ENNReal) (ι : Type) [Countable ι] (r : ι → G), (Γ : Set G).Countable → S ≤ Γ → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → Measurable Φ → (∀ γ ∈ S, ∀ g, Φ (γ * g) = Φ g) → (∀ i, r i ∈ Γ) → (∀ γ ∈ Γ, ∃! i, γ * (r i)⁻¹ ∈ S) → ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ = covol (S : Set G) (μ.withDensity Φ) Set.univ := by
  intro G _ _ _ Γ S μ fund Φ ι _ r hΓ hSΓ hμ hf hcov hd hΦ hΦS hr hrep
  have hTm : ∀ a : G, MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' fund) :=
    fun a => hf.preimage (measurable_const_mul _)
  have hSc : (S : Set G).Countable := hΓ.mono hSΓ
  have hD0m : MeasurableSet (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) := MeasurableSet.iUnion fun i => hTm _
  have hnull : ∀ a b : G, a ∈ Γ → b ∈ Γ → a ≠ b →
      μ.withDensity Φ ((fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund) = 0 :=
    fun a b ha hb hab => withDensity_absolutelyContinuous μ Φ
      (translate_inter_null Γ μ fund hμ hf hd ha hb hab)
  have hL : ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ
      = μ.withDensity Φ (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) := by
    rw [lintegral_tsum (f := fun i g => Φ (r i * g)) fun i => (hΦ.comp (measurable_const_mul (r i))).aemeasurable]
    rw [measure_iUnion₀ ?_ fun i => (hTm _).nullMeasurableSet]
    · exact tsum_congr fun i =>
        (withDensity_preimage_inv_mul_eq_setLIntegral μ Φ hΦ (r i) (hμ _ (hr i)) fund hf).symm
    · intro i j hij
      refine hnull _ _ (hr i) (hr j) fun he => hij ?_
      have h1 : r i * (r i)⁻¹ ∈ S := by simpa using S.one_mem
      exact (hrep _ (hr i)).unique h1 (by rw [he]; simpa using S.one_mem)
  rw [hL]
  unfold GlobalTheory.FlagMeas.covol
  apply le_antisymm
  · refine le_iInf fun D => le_iInf fun hDm => le_iInf fun hDc => ?_
    calc μ.withDensity Φ (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund)
        ≤ μ.withDensity Φ (⋃ s ∈ (S : Set G), (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ (fun y => s * y) ⁻¹' D) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨s, hs, hsx⟩ := hDc x (Set.mem_univ x)
          exact Set.mem_biUnion hs ⟨hx, hsx⟩
      _ ≤ ∑' p : (S : Set G), μ.withDensity Φ ((⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ (fun y => (p : G) * y) ⁻¹' D) :=
          measure_biUnion_le _ hSc _
      _ = ∑' p : (S : Set G), μ.withDensity Φ ((fun y => (p : G)⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) := by
          refine tsum_congr fun p => ?_
          have hpS : (p : G) ∈ S := p.2
          rw [← withDensity_preimage_mul_eq_of_invariant μ Φ hΦ (p : G) (hμ _ (hSΓ hpS)) (fun g => hΦS _ hpS g) _
            ((hD0m.preimage (measurable_const_mul _)).inter hDm)]
          congr 1
          ext y
          simp only [Set.mem_inter_iff, Set.mem_preimage, inv_mul_cancel_left]
      _ = μ.withDensity Φ (⋃ s ∈ (S : Set G), (fun y => s⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) := by
          refine (measure_biUnion₀ hSc ?_ fun s _ =>
            ((hD0m.preimage (measurable_const_mul _)).inter hDm).nullMeasurableSet).symm
          intro s hs s' hs' hne
          have hsub : ((fun y => s⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) ∩
              ((fun y => s'⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) ⊆
              ⋃ i, ⋃ j, (fun y => (s * r i)⁻¹ * y) ⁻¹' fund ∩ (fun y => (s' * r j)⁻¹ * y) ⁻¹' fund := by
            rintro y ⟨⟨hy1, -⟩, hy2, -⟩
            simp only [Set.mem_preimage, Set.mem_iUnion] at hy1 hy2
            obtain ⟨i, hi⟩ := hy1
            obtain ⟨j, hj⟩ := hy2
            simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, _root_.mul_inv_rev, mul_assoc]
            exact ⟨i, j, hi, hj⟩
          refine measure_mono_null hsub (measure_iUnion_null fun i => measure_iUnion_null fun j => ?_)
          refine hnull _ _ (Γ.mul_mem (hSΓ hs) (hr i)) (Γ.mul_mem (hSΓ hs') (hr j)) fun he => hne ?_
          have h1 : s * r i * (r i)⁻¹ ∈ S := by rw [mul_inv_cancel_right]; exact hs
          have h2 : s * r i * (r j)⁻¹ ∈ S := by rw [he, mul_inv_cancel_right]; exact hs'
          have hij := (hrep _ (Γ.mul_mem (hSΓ hs) (hr i))).unique h1 h2
          subst hij
          exact mul_right_cancel he
      _ ≤ μ.withDensity Φ D := measure_mono (Set.iUnion₂_subset fun _ _ => Set.inter_subset_right)
  · refine iInf_le_of_le _ (iInf_le_of_le hD0m (iInf_le _ ?_))
    intro x _
    obtain ⟨γ, hγ, hγx⟩ := hcov x
    obtain ⟨i, hi, -⟩ := hrep γ⁻¹ (Γ.inv_mem hγ)
    refine ⟨(γ⁻¹ * (r i)⁻¹)⁻¹, S.inv_mem hi, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
    show (r i)⁻¹ * ((γ⁻¹ * (r i)⁻¹)⁻¹ * x) ∈ fund
    have e : (r i)⁻¹ * ((γ⁻¹ * (r i)⁻¹)⁻¹ * x) = γ * x := by group
    rw [e]; exact hγx

end GlobalTheory.StabUnfold
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.StrictDom

open Topology Filter

theorem exists_small_eq_zero (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Λ, (∀ (w : InfinitePlace E) a, w (y a) < δ) → y = 0 := by
  first
  | exact @_root_.GlobalTheory.SmallIntegerVanishing.main
  | exact _root_.GlobalTheory.SmallIntegerVanishing.main
  | (apply _root_.GlobalTheory.SmallIntegerVanishing.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmallIntegerVanishing.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmallIntegerVanishing.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmallIntegerVanishing.main ..)

theorem eventually_eq_one (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsFullLattice E Λ)
    (x : InfinitePlace E → Fin j → Fin j → ℂ) (hx : ∀ w, (Matrix.of (x w)).det ≠ 0) :
    ∀ᶠ h in 𝓝 x, ∀ γ : Matrix (Fin j) (Fin j) E, (∀ y ∈ Λ, γ *ᵥ y ∈ Λ) →
      (∀ w : InfinitePlace E, Matrix.of (h w) = γ.map w.embedding * Matrix.of (x w)) → γ = 1 := by
  classical
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_eq_zero E j Λ hΛ.fg
  obtain ⟨s, hs⟩ := hΛ.fg
  have hev : ∀ᶠ h in 𝓝 x, ∀ y ∈ s, ∀ (w : InfinitePlace E) (a : Fin j),
      ‖((Matrix.of (h w) * (Matrix.of (x w))⁻¹) *ᵥ (fun b => w.embedding (y b))) a
        - w.embedding (y a)‖ < δ := by
    refine (Filter.eventually_all_finset s).2 fun y _ => Filter.eventually_all.2 fun w =>
      Filter.eventually_all.2 fun a => ?_
    have hc : Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ =>
        ‖((Matrix.of (h w) * (Matrix.of (x w))⁻¹) *ᵥ (fun b => w.embedding (y b))) a
          - w.embedding (y a)‖ := by
      have h1 : Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (h w) :=
        continuous_apply w
      exact (((continuous_apply a).comp
        ((h1.matrix_mul continuous_const).matrix_mulVec continuous_const)).sub continuous_const).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hx w)), Matrix.one_mulVec]
    simpa using hδ
  filter_upwards [hev] with h hh γ hγ hw
  have hfix : ∀ y ∈ s, γ *ᵥ y = y := fun y hy => by
    have hyΛ : y ∈ Λ := hs ▸ Submodule.subset_span hy
    refine sub_eq_zero.1 (hsmall _ (Λ.sub_mem (hγ y hyΛ) hyΛ) fun w a => ?_)
    have := hh y hy w a
    rw [hw w, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hx w)),
      Matrix.mul_one] at this
    rw [← InfinitePlace.norm_embedding_eq, Pi.sub_apply, map_sub, RingHom.map_mulVec]
    exact this
  have hspan : Submodule.span E (s : Set (Fin j → E)) = ⊤ := by
    have := Submodule.IsFullLattice.span_eq_top (self := hΛ)
    rwa [← hs, Submodule.span_span_of_tower] at this
  have hall : ∀ y, γ *ᵥ y = y := fun y => by
    have hy : y ∈ Submodule.span E (s : Set (Fin j → E)) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact hfix y hy
    | zero => simp
    | add y y' _ _ h h' => rw [Matrix.mulVec_add, h, h']
    | smul c y _ h => rw [Matrix.mulVec_smul, h]
  exact Matrix.ext_of_mulVec_single fun i => by rw [hall, Matrix.one_mulVec]

theorem exists_strictDomain : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ → ∀ e : GL (Fin j) E → MatInf E j, (∀ γ w a b, e γ w a b = w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)) → ∀ S : Subgroup (GL (Fin j) E), (∀ γ ∈ S, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ) → ∃ D : Set (MatInf E j), MeasurableSet D ∧ D ⊆ {g | 0 < GlobalTheory.FlagMeas.detNorm E j g} ∧ ∀ g, 0 < GlobalTheory.FlagMeas.detNorm E j g → ∃! γ : GL (Fin j) E, γ ∈ S ∧ e γ * g ∈ D := by
  intro E _ _ j Λ hΛ e he S hS
  have hof : ∀ γ w, Matrix.of (e γ w) = (γ : Matrix (Fin j) (Fin j) E).map w.embedding :=
    fun γ w => by ext a b; exact he γ w a b
  have hpos : ∀ γ (g : MatInf E j), 0 < GlobalTheory.FlagMeas.detNorm E j g → 0 < GlobalTheory.FlagMeas.detNorm E j (e γ * g) := fun γ g hg => by
    rw [MeanDual.detNorm_mul]
    refine mul_pos ((MeanDual.detNorm_pos_iff E j _).2 fun w => ?_) hg
    rw [hof, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)
  have hone : ∀ g : MatInf E j, e 1 * g = g := fun g => MeanDual.matInf_ext E j fun w => by
    rw [MeanDual.of_mul, hof]; simp
  have hmul : ∀ γ γ' (g : MatInf E j), e (γ * γ') * g = e γ * (e γ' * g) := fun γ γ' g =>
    MeanDual.matInf_ext E j fun w => by
      simp only [MeanDual.of_mul, hof, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  have hcont : ∀ γ, Continuous fun g : InfinitePlace E → Fin j → Fin j → ℂ =>
      (show InfinitePlace E → Fin j → Fin j → ℂ from (e γ * (show MatInf E j from g) : MatInf E j)) := fun γ =>
    continuous_pi fun w => (continuous_const.matrix_mul
      (show Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (h w) from
        continuous_apply w) : Continuous fun h : InfinitePlace E → Fin j → Fin j → ℂ =>
          Matrix.of (e γ w) * Matrix.of (h w))
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin j) (Fin j) E) := inferInstanceAs (Countable (Fin j → Fin j → E))
  haveI : Countable (GL (Fin j) E) := Units.val_injective.countable
  let U : Set (InfinitePlace E → Fin j → Fin j → ℂ) := {g | 0 < GlobalTheory.FlagMeas.detNorm E j g}
  have hU : MeasurableSet U := MeanDual.measurableSet_detNorm_pos E j
  letI : MulAction S U :=
    { smul := fun γ g => ⟨(e γ * (show MatInf E j from g.1) : MatInf E j), hpos γ g.1 g.2⟩
      one_smul := fun g => Subtype.ext (hone g.1)
      mul_smul := fun γ γ' g => Subtype.ext (hmul γ γ' g.1) }
  have hsm : ∀ (γ : S) (g : U), (γ • g).1 = (e γ * (show MatInf E j from g.1) : MatInf E j) :=
    fun _ _ => rfl
  have hc : ∀ γ : S, Continuous fun g : U => γ • g := fun γ =>
    ((hcont γ).comp continuous_subtype_val).subtype_mk _
  haveI : MeasurableConstSMul S U := ⟨fun γ => (hc γ).measurable⟩
  have hdisc : ∀ x : U, ∃ V ∈ 𝓝 x, ∀ γ : S, γ • x ∈ V → γ = 1 := fun x => by
    have h := eventually_eq_one E j Λ hΛ x.1 ((MeanDual.detNorm_pos_iff E j _).1 x.2)
    refine ⟨_, continuous_subtype_val.continuousAt.eventually h, fun γ hγ => ?_⟩
    refine Subtype.ext (Units.ext (hγ _ (fun y hy => (hS γ γ.2 y).2 hy) fun w => ?_))
    rw [← hof]; rfl
  have hfree : ∀ (γ : S) (x : U), γ • x = x → γ = 1 := fun γ x h => by
    obtain ⟨V, hV, hV'⟩ := hdisc x
    exact hV' γ (h.symm ▸ mem_of_mem_nhds hV)
  obtain ⟨D, hD, hcov, hu⟩ := exists_measurableSet_orbitSection_of_discreteOrbits (G := S) (X := U)
    (fun γ => (isClosed_eq (hc γ) continuous_id).measurableSet)
    (fun x => by
      obtain ⟨V, hV, hV'⟩ := hdisc x
      exact ⟨V, hV, fun γ hγ => by rw [hV' γ hγ, one_smul]⟩)
  refine ⟨Subtype.val '' D, hU.subtype_image hD, ?_, fun g hg => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · obtain ⟨γ, hγ⟩ := hcov ⟨g, hg⟩
    refine ⟨γ, ⟨γ.2, _, hγ, rfl⟩, ?_⟩
    rintro k ⟨hk, x, hx, hxe⟩
    have hx' : x = (⟨k, hk⟩ : S) • (⟨g, hg⟩ : U) := Subtype.ext hxe
    have := hu _ hγ (⟨k, hk⟩ * γ⁻¹) (by rw [mul_smul, inv_smul_smul, ← hx']; exact hx)
    exact congrArg Subtype.val (mul_inv_eq_one.1 (hfree _ _ this))

end GlobalTheory.StrictDom
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadicalDimSum

theorem two_mul_pairs_add_sq {ι : Type} [LinearOrder ι] (s : Finset ι) (f : ι → ℕ) :
    2 * (∑ i ∈ s, ∑ k ∈ s.filter (fun k => i < k), f i * f k) + ∑ i ∈ s, f i ^ 2 = (∑ i ∈ s, f i) ^ 2 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    have h2 : (insert a s).filter (fun k => a < k) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact lt_irrefl _
      · exact not_lt.mpr (ha x hx).le
    have h3 : ∑ i ∈ s, ∑ k ∈ (insert a s).filter (fun k => i < k), f i * f k
        = ∑ i ∈ s, ∑ k ∈ s.filter (fun k => i < k), f i * f k + (∑ i ∈ s, f i) * f a := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.filter_insert, if_pos (ha i hi), Finset.sum_insert (by simp [hna])]
      ring
    simp only [Finset.sum_insert hna]
    rw [h2, Finset.sum_empty, h3,
      show (f a + ∑ i ∈ s, f i) ^ 2 = f a ^ 2 + 2 * (∑ i ∈ s, f i) * f a + (∑ i ∈ s, f i) ^ 2 by ring,
      ← ih]
    ring

theorem sum_shift_eq (N : ℕ) (r : ℕ → ℕ) (hr : ∀ b, N ≤ b → r b = 0) (b : ℕ) :
    ∑ c ∈ range N, r (b + c + 1) = ∑ k ∈ (range N).filter (fun k => b < k), r k := by
  have e : ∑ c ∈ range N, r (b + c + 1) = ∑ k ∈ Ico (b + 1) (b + 1 + N), r k := by
    rw [Finset.sum_Ico_eq_sum_range, show b + 1 + N - (b + 1) = N by omega]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    congr 1
    omega
  rw [e]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_Ico]
    omega
  · intro k hk hk'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_and, not_lt] at hk hk'
    apply hr
    by_contra h
    exact absurd (hk' (by omega)) (by omega)

theorem dimN_eq_sum_pairs : ∀ (n a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → dimN n j = ∑ c ∈ Finset.range (2 * a + 1), ∑ b ∈ Finset.range (2 * a + 1), r b * r (b + c + 1) := by
  intro n a j r hj ha hz
  have hpairs : ∑ c ∈ range (2 * a + 1), ∑ b ∈ range (2 * a + 1), r b * r (b + c + 1)
      = ∑ b ∈ range (2 * a + 1), ∑ k ∈ (range (2 * a + 1)).filter (fun k => b < k), r b * r k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_shift_eq (2 * a + 1) r hz b]
  have hsum : ∑ b ∈ range (2 * a + 1), r b = 2 * ∑ i, j i + (n - 2 * ∑ i, j i) := by
    have h : ∑ b ∈ range (2 * a + 1), r b = ∑ i : Fin a, (r i + r (2 * a - i)) + r a :=
      GlobalTheory.DoubledFlag.sum_range_double a r
    rw [h, ha]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hj i).1, (hj i).2]
    ring
  have hsq : ∑ b ∈ range (2 * a + 1), r b ^ 2 = 2 * ∑ i, j i ^ 2 + (n - 2 * ∑ i, j i) ^ 2 := by
    have h : ∑ b ∈ range (2 * a + 1), r b ^ 2 = ∑ i : Fin a, (r i ^ 2 + r (2 * a - i) ^ 2) + r a ^ 2 :=
      GlobalTheory.DoubledFlag.sum_range_double a (fun b => r b ^ 2)
    rw [h, ha]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hj i).1, (hj i).2]
    ring
  have h1 := two_mul_pairs_add_sq (range (2 * a + 1)) r
  have h2 := two_mul_pairs_add_sq (univ : Finset (Fin a)) j
  rw [hsum, hsq] at h1
  rw [hpairs, GlobalTheory.FlagMeas.dimN]
  nlinarith [h1, h2]

end GlobalTheory.RadicalDimSum
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Cheb

theorem isClosed_GG (k r : ℕ) : IsClosed (GG k r) := by
  unfold GG UH
  exact isClosed_eq (by fun_prop) continuous_const

theorem measurableSet_len_gt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (T : ℝ) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} := by
  obtain ⟨u, hu, h⟩ := continuousOn_iff'.1 ((LenCont.lA_Sg_continuousOn k r z).1 a) (Set.Ioi T) isOpen_Ioi
  have h1 : MeasurableSet (α := Mt k r) u := IsOpen.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

theorem cheb_one {X : Type*} [MeasurableSpace X] (ν : Measure X) (l : X → ℝ) (f : X → ℝ≥0∞) (E : Set X)
    (hE : MeasurableSet E) (T : ℝ) (hT : 0 < T) (hl : ∀ x ∈ E, T < l x) (n : ℕ) :
    ∫⁻ x in E, f x ∂ν ≤ ENNReal.ofReal ((T ^ n)⁻¹) * ∫⁻ x, ENNReal.ofReal (l x ^ n) * f x ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (setLIntegral_mono' hE fun x hx => ?_) (setLIntegral_le_lintegral E _)
  have hTn : 0 < T ^ n := pow_pos hT n
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hTn.le)]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal, inv_mul_eq_div, one_le_div hTn]
  exact pow_le_pow_left₀ hT.le (hl x hx).le n

theorem tail_mass_le : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ), 1 ≤ H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → ∀ i : ℕ, ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z (Matrix.of x))}, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal ((r + 1) * 4 ^ q * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
  intro k r Wp _ _ _ z νS Φ q H₁ hH _ _ hM i
  rcases i with _ | j
  · refine (setLIntegral_le_lintegral _ _).trans ?_
    refine le_mul_of_one_le_left' ?_
    rw [ENNReal.one_le_ofReal]
    have h1 : (1 : ℝ) ≤ 4 ^ q := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    simp only [pow_zero, one_pow, inv_one, mul_one]
    nlinarith
  · set T : ℝ := 2 ^ (j + 1) * H₁ / 2 with hTdef
    have hT' : T = 2 ^ j * H₁ := by rw [hTdef]; ring
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hT1 : 1 ≤ T := by rw [hT']; nlinarith
    have hsub : {x : Mt k r | Matrix.of x ∈ GG k r ∧ (j + 1 = 0 ∨ T < Sg k r z (Matrix.of x))} ⊆
        ⋃ a : Fin (r + 1), {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} := by
      rintro x ⟨hx, h | h⟩
      · omega
      · unfold Sg at h
        rw [Finset.lt_fold_max] at h
        rcases h with h | ⟨a, -, h⟩
        · linarith
        · exact Set.mem_iUnion.2 ⟨a, hx, h⟩
    refine (lintegral_mono_set hsub).trans ((lintegral_iUnion_le _ _).trans ?_)
    rw [tsum_fintype]
    have hone : ∀ a : Fin (r + 1),
        ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a},
          (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤
          ENNReal.ofReal (4 ^ q * ((2 ^ (j + 1) : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
      intro a
      refine (cheb_one νS (fun x => lA k r z (Matrix.of x) a) _ _ (measurableSet_len_gt k r z a T) T
        (by linarith) (fun x hx => hx.2) (2 * q)).trans ?_
      refine (mul_le_mul_right (hM a) _).trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have hH0 : H₁ ≠ 0 := by linarith
      have h4 : (4 : ℝ) ^ q = 2 ^ (2 * q) := by rw [pow_mul]; norm_num
      rw [hT', h4, pow_succ, mul_pow, mul_pow]
      field_simp
    refine (Finset.sum_le_sum fun a _ => hone a).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, mul_assoc ((r : ℝ) + 1),
      ENNReal.ofReal_mul (p := (r : ℝ) + 1) (by positivity)]
    congr 2
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl

end GlobalTheory.Amp.Cheb
end
end
