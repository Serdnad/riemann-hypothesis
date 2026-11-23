module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle027
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianNormFibreMeasureEqPolarCoordinates
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadricPointGaugeSectionMulBlockCompare
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerronIntegralShiftPrimitiveLFunction
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle031
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange : ∀ (R : Type) [CommRing R] (r n : ℕ), GlRel (rowE R r n) ∧ (∀ a b f, rowE R r n a b f = rowDiv R a b 1 f) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R), map φ (gel R r n k f) = gel S r n k (map φ f) := by
  first | exact @GlobalTheory.Alc.rowOperators_main | exact GlobalTheory.Alc.rowOperators_main | (intros; apply GlobalTheory.Alc.rowOperators_main <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.hermitianNormFibreMeasure_eq_polar_coordinates : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), SignCompat e → ∀ fib : ℝ → Measure (Sp P Q), IsDxDq fib → ∀ S : Set (Sp P Q), MeasurableSet S → (∀ y ∈ S, y (e none) ≠ 0) → fib (sg (e none)) S = (2 : ℝ≥0∞) ^ (P' + Q') * (volume : Measure (ℝ × Sp P' Q')) {t | t.1 ∈ Set.Ioo (-Real.pi) Real.pi ∧ polarPt e t ∈ S} := by
  first | exact @GlobalTheory.FibrePolar.fibre_eq_polar | exact GlobalTheory.FibrePolar.fibre_eq_polar | (intros; apply GlobalTheory.FibrePolar.fibre_eq_polar <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.quadricPointGauge_section_mul_block_compare : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q), IsBlockEmb e j → ∀ t : ℝ, 1 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ (y : Sp P Q) (a : UpqT P Q), ptGauge e y < δ → act a (baseVec e) = y → (∀ b, ‖UpqT.mat a (e none) (e (some b))‖ = ‖y (e (some b))‖) → (∀ i b, ‖(UpqT.mat a - 1) (e (some i)) (e (some b))‖ = ‖y (e (some i))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖) → ∀ g : UpqT P' Q', ptGauge e y + gauge g ≤ t * gauge (a * j g) ∧ gauge (a * j g) ≤ t * (ptGauge e y + gauge g) := by
  first | exact @GlobalTheory.SectionGaugeCompare.gauge_section_mul_block | exact GlobalTheory.SectionGaugeCompare.gauge_section_mul_block | (intros; apply GlobalTheory.SectionGaugeCompare.gauge_section_mul_block <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.ResidueBoxVolume


open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
theorem _root_.GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    (∃ y : v.adicCompletionIntegers F, x = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0) ↔ Valued.v x < 1 := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hy
    exact lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).1 y.2) hy
  · intro hx
    refine ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 hx.le⟩, rfl, ?_⟩
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hx.ne

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
theorem _root_.GlobalTheory.ResidueBoxVolume.isOpen_val_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen {x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | Valued.v x < 1} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Valued.mem_nhds]
  refine ⟨1, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hy' : y = (y - x) + x := by ring
  rw [hy']
  exact Valuation.map_add_lt _ (by simpa using hy) hx

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem mem_residue_box_singleton_iff (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (s : ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)) (x : V) :
    (∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)) ↔
    ∀ i, ∃ y : v.adicCompletionIntegers F, e x i = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = s i := by
  simp only [Set.mem_singleton_iff, funext_iff]
  constructor
  · rintro ⟨y, h1, h2⟩ i
    exact ⟨y i, h1 i, h2 i⟩
  · intro h
    choose y hy1 hy2 using h
    exact ⟨y, hy1, hy2⟩

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
private theorem exists_residue_eq_iff_exists_residue_sub_eq_zero {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (c : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) (t : v.adicCompletionIntegers F)
    (ht : IsLocalRing.residue (v.adicCompletionIntegers F) t = c) :
    (∃ y : v.adicCompletionIntegers F, a = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = c) ↔
    ∃ y : v.adicCompletionIntegers F, a - t = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0 := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    exact ⟨y - t, rfl, by rw [map_sub, hy, ht, sub_self]⟩
  · rintro ⟨y, hy, hy0⟩
    refine ⟨y + t, ?_, by rw [map_add (f := _), hy0, ht, zero_add]⟩
    show a = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) + (t : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    rw [← hy]
    ring

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem exists_residueBox_eq_preimage_add_lemma_2 (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (s : ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :
    ∃ w : V, {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)} =
      (fun x => x + w) ⁻¹' {x | ∃ y : ι → v.adicCompletionIntegers F,
        (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  choose t ht using fun i => IsLocalRing.residue_surjective (s i)
  refine ⟨-e.symm (fun i => (t i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_residue_box_singleton_iff, Pi.zero_apply,
    map_add, map_neg, map_sub, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply,
    Pi.neg_apply, Pi.sub_apply, ← sub_eq_add_neg]
  exact forall_congr' fun i => exists_residue_eq_iff_exists_residue_sub_eq_zero v _ _ _ (ht i)

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem measurableSet_residue_box_zero (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) :
    MeasurableSet {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  have h : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} =
      ⋂ i, (fun x => e x i) ⁻¹' {a : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | Valued.v a < 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, mem_residue_box_singleton_iff,
      Pi.zero_apply, _root_.GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff]
  rw [h]
  exact (isOpen_iInter_of_finite fun i =>
    (_root_.GlobalTheory.ResidueBoxVolume.isOpen_val_lt_one v).preimage ((continuous_apply i).comp e.continuous)).measurableSet

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem measure_residueBox_lemma (μ : Measure V) [μ.IsAddHaarMeasure]
    (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (S : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    μ {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} =
    S.ncard * μ {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  classical
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    _root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hS : S.Finite := S.toFinite
  have hunion : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} =
      ⋃ s ∈ hS.toFinset, {x | ∃ y : ι → v.adicCompletionIntegers F,
        (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · rintro ⟨y, h1, h2⟩
      exact ⟨_, h2, y, h1, rfl⟩
    · rintro ⟨s, hs, y, h1, rfl⟩
      exact ⟨y, h1, hs⟩
  rw [hunion, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun s _ => ?_, Finset.sum_const, nsmul_eq_mul,
      Set.ncard_eq_toFinset_card S hS]
    obtain ⟨w, hw⟩ := exists_residueBox_eq_preimage_add_lemma_2 e s
    rw [hw, measure_preimage_add_right]
  · intro s _ s' _ hss'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨y, h1, h2⟩ ⟨y', h1', h2'⟩
    apply hss'
    have hyy : y = y' := funext fun i => Subtype.ext ((h1 i).symm.trans (h1' i))
    subst hyy
    rw [Set.mem_singleton_iff] at h2 h2'
    rw [← h2, ← h2']
  · intro s _
    obtain ⟨w, hw⟩ := exists_residueBox_eq_preimage_add_lemma_2 e s
    rw [hw]
    exact (measurableSet_residue_box_zero e).preimage (continuous_add_const w).measurable


open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
theorem _root_.GlobalTheory.ResidueBoxVolume.measureReal_residueBox (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) (S : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    μ.real {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} * (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ^ Fintype.card ι = (S.ncard : ℝ) * μ.real {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} := by
  have hB : {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} =
      {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ Set.univ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, and_true]
    constructor
    · intro h
      exact ⟨fun i => ⟨e x i, h i⟩, fun i => rfl⟩
    · rintro ⟨y, hy⟩ i
      rw [hy i]
      exact (y i).2
  rw [hB, measureReal_def, measureReal_def, measure_residueBox_lemma μ e Set.univ, measure_residueBox_lemma μ e S,
    Set.ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card (α := ι), ENNReal.toReal_mul,
    ENNReal.toReal_mul]
  simp only [Nat.cast_pow, ENNReal.toReal_natCast, ENNReal.toReal_pow]
  ring

end GlobalTheory.ResidueBoxVolume
end

section

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Set Topology
open scoped ENNReal

namespace GlobalTheory.FibreProd

theorem le_of_lintegral_ball_eq {X : Type} [PseudoMetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (G H : X → ℝ≥0∞) (b : X) (hG : ContinuousAt G b) (hH : ContinuousAt H b)
    (h : ∀ r > 0, ∫⁻ x in Metric.ball b r, G x ∂ν = ∫⁻ x in Metric.ball b r, H x ∂ν) :
    H b ≤ G b := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  obtain ⟨d, hd1, hd2⟩ := exists_between hc2
  have e : ∀ᶠ x in 𝓝 b, G x < c ∧ d < H x :=
    (hG.eventually (gt_mem_nhds hc1)).and (hH.eventually (lt_mem_nhds hd2))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 e
  have h1 : ∫⁻ x in Metric.ball b r, G x ∂ν ≤ c * ν (Metric.ball b r) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).1.le
  have h2 : d * ν (Metric.ball b r) ≤ ∫⁻ x in Metric.ball b r, H x ∂ν := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).2.le
  have h3 : c * ν (Metric.ball b r) < d * ν (Metric.ball b r) :=
    ENNReal.mul_lt_mul_left (Metric.measure_ball_pos ν b hr).ne' measure_ball_lt_top.ne hd1
  exact absurd (h2.trans ((h r hr).symm.le.trans h1)) h3.not_ge

theorem lintegral_preimage {V X : Type} [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X}
    {f : V → X} {U : Set V} {B : Set X} {fib : X → Measure V}
    (hf : Measurable f) (hU : IsOpen U) (h : IsFibreFamily μ f id U ν B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ U → φ v = 0)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))
  have e1 : ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ v in U, (f ⁻¹' S).indicator φ v ∂μ := by
    rw [← lintegral_indicator hU.measurableSet]
    congr 1
    funext v
    by_cases hv : v ∈ U
    · rw [indicator_of_mem hv]
    · rw [indicator_of_notMem hv]
      exact indicator_apply_eq_zero.2 fun _ => hs v hv
  rw [e1, h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb : ∀ᵐ v ∂(fib b), f v = b := by
    have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ U := h.1 b
    filter_upwards [this] with v hv using hv.1
  by_cases hbS : b ∈ S
  · rw [indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_mem (by simpa [hv] using hbS) _
  · rw [indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_notMem (by simpa [hv] using hbS) _

theorem lintegral_fibre_prod : ∀ (T V : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ₀ : Measure V) [SigmaFinite μ₀] (q : V → ℝ), Continuous q → ∀ U : Set V, IsOpen U → ∀ fib : ℝ → Measure V, IsFibreFamily μ₀ q id U (volume : Measure ℝ) Set.univ fib → ∀ B : Set (T → ℝ), IsOpen B → ∀ Fib : (T → ℝ) → Measure (T → V), IsFibreFamily (Measure.pi fun _ : T => μ₀) (fun x ρ => q (x ρ)) id Set.univ (volume : Measure (T → ℝ)) B Fib → ∀ b ∈ B, ∀ φ : T → V → ℝ, (∀ ρ, Continuous (φ ρ) ∧ HasCompactSupport (φ ρ) ∧ tsupport (φ ρ) ⊆ U ∧ ∀ y, 0 ≤ φ ρ y) → ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b) = ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
  intro T V _ _ _ _ _ _ μ₀ _ q hq U hU fib hfib B hB Fib hFib b hb φ hφ
  classical
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  have hΦc : Continuous fun x : T → V => ∏ ρ, φ ρ (x ρ) :=
    continuous_finsetProd _ fun ρ _ => (hφ ρ).1.comp (continuous_apply ρ)
  have hΦs : HasCompactSupport fun x : T → V => ∏ ρ, φ ρ (x ρ) := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun ρ => (hφ ρ).2.1) fun x hx => ?_
    rw [mem_univ_pi, not_forall] at hx
    obtain ⟨ρ, hρ⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ ρ) (image_eq_zero_of_notMem_tsupport hρ)
  obtain ⟨hI, hC⟩ := hFib.2.2 _ hΦc hΦs (subset_univ _)
  have hm : ∀ ρ, Measurable fun y => ENNReal.ofReal (φ ρ y) := fun ρ =>
    ENNReal.measurable_ofReal.comp (hφ ρ).1.measurable
  have hGc : ContinuousOn (fun b => ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b)) B := by
    refine (ENNReal.continuous_ofReal.comp_continuousOn hC).congr fun b hb => ?_
    have := ofReal_integral_eq_lintegral_ofReal (hI b hb)
      (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun ρ _ => (hφ ρ).2.2.2 _)
    simp only [Function.comp_apply]
    rw [this]
    congr 1
    funext x
    rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => (hφ ρ).2.2.2 _]
  have hg : ∀ ρ t, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) = ENNReal.ofReal (∫ y, φ ρ y ∂(fib t)) :=
    fun ρ t => (ofReal_integral_eq_lintegral_ofReal
      ((hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).1 t (mem_univ _))
      (Filter.Eventually.of_forall (hφ ρ).2.2.2)).symm
  have hgc : ∀ ρ, Continuous fun t => ∫ y, φ ρ y ∂(fib t) := fun ρ =>
    continuousOn_univ.1 (hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).2
  have hgm : ∀ ρ, Measurable fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) := fun ρ => by
    simp only [hg]
    exact ENNReal.measurable_ofReal.comp (hgc ρ).measurable
  have hHc : Continuous fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
    have : (fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ))) =
        fun b => ENNReal.ofReal (∏ ρ, ∫ y, φ ρ y ∂(fib (b ρ))) := by
      funext b
      rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => integral_nonneg (hφ ρ).2.2.2]
      simp only [hg]
    rw [this]
    exact ENNReal.continuous_ofReal.comp
      (continuous_finsetProd _ fun ρ _ => (hgc ρ).comp (continuous_apply ρ))
  have key : ∀ r > 0, ∫⁻ c in Metric.ball b r, ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib c) =
      ∫⁻ c in Metric.ball b r, ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ)) := by
    intro r hr
    have hQ : Measurable fun (x : T → V) ρ => q (x ρ) :=
      (continuous_pi fun ρ => hq.comp (continuous_apply ρ)).measurable
    rw [← lintegral_preimage hQ isOpen_univ hFib (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)))
      (Finset.measurable_prod _ fun ρ _ => (hm ρ).comp (measurable_pi_apply ρ))
      (fun v hv => absurd (mem_univ v) hv) _ measurableSet_ball,
      ← lintegral_indicator measurableSet_ball, ball_pi b hr]
    have e1 : ∀ x : T → V, ((fun (x : T → V) ρ => q (x ρ)) ⁻¹'
        (Set.pi univ fun ρ => Metric.ball (b ρ) r)).indicator
        (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ))) x =
        ∏ ρ, (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)) (x ρ) := by
      intro x
      by_cases hx : ∀ ρ, x ρ ∈ q ⁻¹' Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    have e2 : ∀ c : T → ℝ, (Set.pi univ fun ρ => Metric.ball (b ρ) r).indicator
        (fun c => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ))) c =
        ∏ ρ, (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)) (c ρ) := by
      intro c
      by_cases hx : ∀ ρ, c ρ ∈ Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    simp only [e1, e2]
    rw [volume_pi, GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)))
        (fun ρ => (hm ρ).indicator (hq.measurable measurableSet_ball)),
      GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)))
        (fun ρ => (hgm ρ).indicator measurableSet_ball)]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [lintegral_indicator (s := Metric.ball (b ρ) r) measurableSet_ball]
    refine lintegral_preimage hq.measurable hU hfib _ (hm ρ) (fun v hv => ?_) _ measurableSet_ball
    rw [image_eq_zero_of_notMem_tsupport fun h => hv ((hφ ρ).2.2.1 h), ENNReal.ofReal_zero]
  have hGb := hGc.continuousAt (hB.mem_nhds hb)
  exact le_antisymm
    (le_of_lintegral_ball_eq volume _ _ b hHc.continuousAt hGb fun r hr => (key r hr).symm)
    (le_of_lintegral_ball_eq volume _ _ b hGb hHc.continuousAt key)

end GlobalTheory.FibreProd
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.perron_integral_shift_primitive_LFunction : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧ ‖(1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ in (-T')..T', (-(deriv (LFunction χ) (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / LFunction χ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I))) - (if N = 1 then (u : ℂ) else 0) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by
  first | exact @GlobalTheory.PerronShift.perron_shift | exact GlobalTheory.PerronShift.perron_shift | (intros; apply GlobalTheory.PerronShift.perron_shift <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

theorem _root_.GlobalTheory.T.neg_re_logDeriv_principalLFunction_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  first | exact @GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le | exact GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le | (intros; apply GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le <;> assumption)
end
