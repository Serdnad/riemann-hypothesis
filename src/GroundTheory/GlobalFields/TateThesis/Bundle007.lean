module

public import GroundTheory.GlobalFields.TateThesis.Bundle005
public import GroundTheory.GlobalFields.TateThesis.LatticePoisson
public import GroundTheory.GlobalFields.TateThesis.Bundle006
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import GroundTheory.GlobalFields.Adele.Bundle002
import GroundTheory.GlobalFields.Adele.Topology
public import GroundTheory.GlobalFields.Adele.Bundle001
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
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
public import Mathlib.MeasureTheory.Integral.Pi
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
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

@[expose] public section

section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace FourierTransform SchwartzMap nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem idealLattice_summable_norm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (f : 𝓢(mixedSpace K, ℂ))
    (a : mixedSpace K) : Summable fun α : idealLattice K I => ‖f (α + a)‖ := by
  simpa [add_comm] using summable_norm_comp_add (idealLattice K I) f a

theorem traceDualIdeal_summable_norm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K, ℂ)) (a : mixedSpace K) :
    Summable fun β : idealLattice K (traceDualIdeal K I) =>
      ‖mixedFourier K f β * 𝐞 (mixedTraceForm K β a)‖ := by
  have h := summable_norm_comp_add (idealLattice K (traceDualIdeal K I)) (mixedFourierSchwartz K f) 0
  simpa [norm_mul, Circle.norm_coe, mixedFourierSchwartz_apply] using h

theorem idealLattice_poisson_summation (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K, ℂ)) (a : mixedSpace K) :
    ∑' α : idealLattice K I, f (α + a) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|(discr K : ℝ)|)⁻¹ •
        ∑' β : idealLattice K (traceDualIdeal K I),
          mixedFourier K f β * 𝐞 (mixedTraceForm K β a) := by
  set L := euclideanIdealLattice K I
  set F : 𝓢(euclidean.mixedSpace K, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K).symm f
  have hF : (F : euclidean.mixedSpace K → ℂ) = f ∘ (mixedToEuclidean K).symm := rfl
  have h := lattice_poisson_summation L F (mixedToEuclidean K a)

  let eL : idealLattice K I ≃ L :=
    { toFun := fun α => ⟨mixedToEuclidean K α, by
        rw [mem_euclideanIdealLattice, ContinuousLinearEquiv.symm_apply_apply]; exact α.2⟩
      invFun := fun ℓ => ⟨(mixedToEuclidean K).symm ℓ, ℓ.2⟩
      left_inv := fun α => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun ℓ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }

  let eD : idealLattice K (traceDualIdeal K I) ≃ dualLattice L :=
    { toFun := fun β => ⟨mixedToEuclideanConj K β, by
        rw [dualLattice_euclideanIdealLattice, mem_euclideanConjIdealLattice,
          ContinuousLinearEquiv.symm_apply_apply]; exact β.2⟩
      invFun := fun μ => ⟨(mixedToEuclideanConj K).symm μ, by
        have hμ : (μ : euclidean.mixedSpace K) ∈ euclideanConjIdealLattice K (traceDualIdeal K I) := by
          rw [← dualLattice_euclideanIdealLattice]
          exact μ.2
        exact hμ⟩
      left_inv := fun β => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun μ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }
  have hlhs : ∑' ℓ : L, F (ℓ + mixedToEuclidean K a) = ∑' α : idealLattice K I, f (α + a) := by
    rw [← Equiv.tsum_eq eL]
    refine tsum_congr fun α => ?_
    change f ((mixedToEuclidean K).symm (mixedToEuclidean K α + mixedToEuclidean K a)) = _
    rw [← map_add (f := _), ContinuousLinearEquiv.symm_apply_apply]
  have hrhs : ∑' μ : dualLattice L, 𝓕 (F : euclidean.mixedSpace K → ℂ) μ *
      𝐞 ⟪(μ : euclidean.mixedSpace K), mixedToEuclidean K a⟫ =
      ∑' β : idealLattice K (traceDualIdeal K I),
        mixedFourier K f β * 𝐞 (mixedTraceForm K β a) := by
    rw [← Equiv.tsum_eq eD]
    refine tsum_congr fun β => ?_
    change 𝓕 (F : euclidean.mixedSpace K → ℂ) (mixedToEuclideanConj K β) *
      𝐞 ⟪mixedToEuclideanConj K β, mixedToEuclidean K a⟫ = _
    rw [hF, ← mixedFourier_eq, inner_mixedToEuclideanConj_mixedToEuclidean]
  rw [hlhs, hrhs, covolume_euclideanIdealLattice] at h
  exact h

end

end GroundTheory.Global
end

section

open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal

namespace GroundTheory.Global

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem countable_quotient_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : Countable (G ⧸ W) := by
  have : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hW
  have h : IsLindelof (Set.univ : Set (G ⧸ W)) := by
    rw [← Set.image_univ_of_surjective (QuotientGroup.mk_surjective (s := W))]
    exact isLindelof_univ.image QuotientGroup.continuous_mk
  exact Set.countable_univ_iff.1 h.countable_of_discrete

variable {K}

theorem hasSum_integral_ideleMeasure_of_invariant {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (W : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ)
    (hWo : IsOpen (W : Set (FiniteAdeleRing (𝓞 K) K)ˣ)) {F : IdeleGroup K → E} (hFi : Integrable F (ideleMeasure K))
    (hF : ∀ x : IdeleGroup K, ∀ w ∈ W, F (x * (IdeleGroup.prodEquiv K).symm (1, w)) = F x) :
    HasSum (fun c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W ↦ (finiteIdeleMeasure K W).toReal •
        ∫ a, F ((IdeleGroup.prodEquiv K).symm (a, c.out)) ∂infiniteIdeleMeasure K)
      (∫ x, F x ∂ideleMeasure K) := by
  have hc : Countable ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W) := countable_quotient_of_isOpen hWo
  set μ := (infiniteIdeleMeasure K).prod (finiteIdeleMeasure K)
  set G : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ → E :=
    fun p ↦ F ((IdeleGroup.prodEquiv K).symm p)
  have hG : Integrable G μ :=
    (integrable_map_equiv (IdeleGroup.prodEquiv K).symm.toHomeomorph.toMeasurableEquiv F).1 hFi

  set S : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W → Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
    fun c ↦ QuotientGroup.mk ⁻¹' {c}
  have : DiscreteTopology ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W) := QuotientGroup.discreteTopology hWo
  have hSm : ∀ c, MeasurableSet (S c) := fun c ↦
    (isOpen_discrete ({c} : Set ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W))).preimage
      QuotientGroup.continuous_mk |>.measurableSet
  have hSW : ∀ c, S c = (fun b ↦ c.out⁻¹ * b) ⁻¹' (W : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
    intro c
    ext b
    simp only [S, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rw [eq_comm, QuotientGroup.eq]
  have hmeasS : ∀ c, finiteIdeleMeasure K (S c) = finiteIdeleMeasure K W := fun c ↦ by
    rw [hSW c, measure_preimage_mul]
  have hGS : ∀ c, ∀ a, ∀ b ∈ S c, G (a, b) = G (a, c.out) := by
    intro c a b hb
    rw [hSW c] at hb
    have hw : c.out⁻¹ * b ∈ W := hb
    have : (a, b) = (a, c.out) * (1, c.out⁻¹ * b) := by simp
    simp only [G]
    rw [this, map_mul, hF _ _ hw]
  have hT : ∀ c, MeasurableSet ((Set.univ : Set (InfiniteAdeleRing K)ˣ) ×ˢ S c) := fun c ↦
    MeasurableSet.univ.prod (hSm c)
  have hTd : Pairwise (Function.onFun Disjoint
      fun c ↦ (Set.univ : Set (InfiniteAdeleRing K)ˣ) ×ˢ S c) := by
    intro c d hcd
    refine Set.disjoint_left.2 fun p hp hq ↦ hcd ?_
    exact hp.2.symm.trans hq.2
  have hTu : ⋃ c, (Set.univ : Set (InfiniteAdeleRing K)ˣ) ×ˢ S c = Set.univ := by
    refine Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ⟨(p.2 : _ ⧸ W), trivial, rfl⟩
  have h := hasSum_integral_iUnion hT hTd hG.integrableOn
  rw [hTu, Measure.restrict_univ] at h
  rw [integral_ideleMeasure]
  convert h using 1
  funext c
  symm
  have e : μ.restrict (Set.univ ×ˢ S c) =
      (infiniteIdeleMeasure K).prod ((finiteIdeleMeasure K).restrict (S c)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e, integral_prod _ (by rw [← e]; exact hG.integrableOn), ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
  simp only
  rw [setIntegral_congr_fun (hSm c) fun b hb ↦ hGS c a b hb, setIntegral_const, Measure.real,
    hmeasS c]

theorem hasSum_integral_ideleMeasure_of_invariant_finiteIntegralUnits {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F : IdeleGroup K → E}
    (hFi : Integrable F (ideleMeasure K))
    (hF : ∀ x : IdeleGroup K, ∀ w ∈ finiteIntegralUnits K,
      F (x * (IdeleGroup.prodEquiv K).symm (1, w)) = F x) :
    HasSum (fun c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K ↦
        ∫ a, F ((IdeleGroup.prodEquiv K).symm (a, c.out)) ∂infiniteIdeleMeasure K)
      (∫ x, F x ∂ideleMeasure K) := by
  have h := hasSum_integral_ideleMeasure_of_invariant (finiteIntegralUnits K)
    (isOpen_finiteIntegralUnits K) hFi hF
  simpa [finiteIdeleMeasure_finiteIntegralUnits] using h

end

end GroundTheory.Global
end

section

open NumberField IsDedekindDomain Topology Filter MeasureTheory NumberField.mixedEmbedding
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap Classical

namespace GroundTheory.Global

noncomputable section

open InfinitePlace InfinitePlace.Completion

section Completion

variable {K : Type*} [Field K]

theorem norm_isometryEquivRealOfIsReal {w : InfinitePlace K} (hw : w.IsReal) (z : w.Completion) :
    ‖isometryEquivRealOfIsReal hw z‖ = ‖z‖ :=
  (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) z

theorem norm_isometryEquivComplexOfIsComplex {w : InfinitePlace K} (hw : w.IsComplex)
    (z : w.Completion) : ‖isometryEquivComplexOfIsComplex hw z‖ = ‖z‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) z

theorem one_le_mult (w : InfinitePlace K) : (1 : ℝ) ≤ w.mult := by
  unfold InfinitePlace.mult
  split_ifs <;> norm_num

theorem mult_le_two (w : InfinitePlace K) : (w.mult : ℝ) ≤ 2 := by
  unfold InfinitePlace.mult
  split_ifs <;> norm_num

theorem lintegral_one_add_norm_rpow_neg_lt_top (w : InfinitePlace K) {r : ℝ} (hr : 2 < r) :
    ∫⁻ z, ENNReal.ofReal ((1 + ‖z‖) ^ (-r)) ∂infinitePlaceMeasure w < ∞ := by
  have hm : Measurable fun z : w.Completion ↦ ENNReal.ofReal ((1 + ‖z‖) ^ (-r)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_const.add continuous_norm).rpow_const fun z ↦
        Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg z)).ne').measurable
  by_cases hw : w.IsReal
  · rw [infinitePlaceMeasure_of_isReal hw,
      lintegral_map hm (isometryEquivRealOfIsReal hw).symm.continuous.measurable]
    have h : ∀ y : ℝ, ‖(isometryEquivRealOfIsReal hw).symm y‖ = ‖y‖ := fun y ↦ by
      rw [← norm_isometryEquivRealOfIsReal hw, IsometryEquiv.apply_symm_apply]
    simp_rw [h]
    exact finite_integral_one_add_norm (by simp; linarith)
  · have hc := not_isReal_iff_isComplex.1 hw
    rw [infinitePlaceMeasure_of_isComplex hc,
      lintegral_map hm (isometryEquivComplexOfIsComplex hc).symm.continuous.measurable]
    have h : ∀ y : ℂ, ‖(isometryEquivComplexOfIsComplex hc).symm y‖ = ‖y‖ := fun y ↦ by
      rw [← norm_isometryEquivComplexOfIsComplex hc, IsometryEquiv.apply_symm_apply]
    simp_rw [h]
    have : ((2 : ℝ≥0∞) • (volume : Measure ℂ)).IsAddHaarMeasure :=
      Measure.IsAddHaarMeasure.smul _ (by norm_num) (by simp)
    exact finite_integral_one_add_norm (by simp [Complex.finrank_real_complex]; linarith)

theorem lintegral_unitsMeasure_le {F : Type*} [NormedField F] [LocallyCompactSpace F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F) (m : ℕ)
    {g : F → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ u, g u ∂unitsMeasure μ m ≤ ∫⁻ z, ENNReal.ofReal (‖z‖ ^ m)⁻¹ * g z ∂μ := by
  have he := measurableEmbedding_units_val (F := F)
  calc ∫⁻ u, g u ∂unitsMeasure μ m
      = ∫⁻ z, g z ∂(Measure.map Units.val (unitsMeasure μ m)) := (he.lintegral_map g).symm
    _ = ∫⁻ z in Set.range Units.val, g z
          ∂(μ.withDensity fun x ↦ ENNReal.ofReal (‖x‖ ^ m)⁻¹) := by
        rw [unitsMeasure, he.map_comap]
    _ ≤ ∫⁻ z, g z ∂(μ.withDensity fun x ↦ ENNReal.ofReal (‖x‖ ^ m)⁻¹) :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ z, ENNReal.ofReal (‖z‖ ^ m)⁻¹ * g z ∂μ := by
        rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_density_unitsMeasure m) hg]
        rfl

def placeZetaBound (w : InfinitePlace K) (σ : ℝ) (k : ℕ) (z : (w.Completion)ˣ) : ℝ :=
  ‖(z : w.Completion)‖ ^ ((w.mult : ℝ) * σ) / (1 + ‖(z : w.Completion)‖) ^ k

theorem continuous_placeZetaBound (w : InfinitePlace K) {σ : ℝ} (hσ : 0 ≤ σ) (k : ℕ) :
    Continuous fun z : w.Completion ↦ ‖z‖ ^ ((w.mult : ℝ) * σ) / (1 + ‖z‖) ^ k :=
  (continuous_norm.rpow_const fun _ ↦ Or.inr (mul_nonneg (Nat.cast_nonneg _) hσ)).div
    ((continuous_const.add continuous_norm).pow k) fun _ ↦ by positivity

theorem integrable_placeZetaBound (w : InfinitePlace K) {σ : ℝ} (hσ : 1 ≤ σ) {k : ℕ}
    (hk : 2 * σ + 2 < k) : Integrable (placeZetaBound w σ k) (infinitePlaceUnitsMeasure w) := by
  have hG := continuous_placeZetaBound w (by linarith : (0 : ℝ) ≤ σ) k
  refine ⟨(hG.comp Units.continuous_val).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z ↦ by
    unfold placeZetaBound; positivity)]
  refine (lintegral_unitsMeasure_le (infinitePlaceMeasure w) w.mult
    (g := fun z ↦ ENNReal.ofReal (‖z‖ ^ ((w.mult : ℝ) * σ) / (1 + ‖z‖) ^ k))
    (ENNReal.measurable_ofReal.comp hG.measurable)).trans_lt ?_
  refine lt_of_le_of_lt (lintegral_mono fun z ↦ ?_)
    (lintegral_one_add_norm_rpow_neg_lt_top w (r := k - 2 * σ) (by linarith))
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hm1 := one_le_mult w
  have hm2 := mult_le_two w
  set t := ‖z‖
  have ht : 0 ≤ t := norm_nonneg _
  have ha : 1 ≤ 1 + t := by linarith
  have hapos : 0 < 1 + t := by linarith
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by positivity), zero_div, mul_zero]
    positivity
  · have e1 : (t ^ w.mult)⁻¹ * (t ^ ((w.mult : ℝ) * σ) / (1 + t) ^ k) =
        t ^ ((w.mult : ℝ) * σ - w.mult) * ((1 + t) ^ (k : ℝ))⁻¹ := by
      rw [← Real.rpow_natCast t w.mult, ← Real.rpow_natCast (1 + t) k, Real.rpow_sub hpos,
        div_eq_mul_inv, div_eq_mul_inv]
      ring
    have e2 : (1 + t) ^ (-((k : ℝ) - 2 * σ)) = (1 + t) ^ (2 * σ) * ((1 + t) ^ (k : ℝ))⁻¹ := by
      rw [← Real.rpow_neg hapos.le, ← Real.rpow_add hapos]
      congr 1
      ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc t ^ ((w.mult : ℝ) * σ - w.mult) ≤ (1 + t) ^ ((w.mult : ℝ) * σ - w.mult) :=
          Real.rpow_le_rpow ht (by linarith) (by nlinarith)
      _ ≤ (1 + t) ^ (2 * σ) := Real.rpow_le_rpow_of_exponent_le ha (by nlinarith)

end Completion

variable {K : Type*} [Field K] [NumberField K]

def infiniteZetaBound (σ : ℝ) (k : ℕ) (a : (InfiniteAdeleRing K)ˣ) : ℝ :=
  ∏ w : InfinitePlace K, ‖(a : InfiniteAdeleRing K) w‖ ^ ((w.mult : ℝ) * σ) /
    (1 + ‖(a : InfiniteAdeleRing K) w‖) ^ k

theorem integrable_infiniteZetaBound {σ : ℝ} (hσ : 1 ≤ σ) {k : ℕ} (hk : 2 * σ + 2 < k) :
    Integrable (infiniteZetaBound (K := K) σ k) (infiniteIdeleMeasure K) := by
  have h := Integrable.fintype_prod_dep (𝕜 := ℝ) (f := fun w : InfinitePlace K ↦ placeZetaBound w σ k)
    (μ := fun w ↦ infinitePlaceUnitsMeasure w) fun w ↦ integrable_placeZetaBound w hσ hk
  rw [infiniteIdeleMeasure]
  refine (integrable_map_equiv (infiniteUnitsEquiv K).symm.toHomeomorph.toMeasurableEquiv _).2 ?_
  exact h

theorem norm_le_norm_homeomorphMixedSpace (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    ‖x w‖ ≤ ‖homeomorphMixedSpace K x‖ := by
  by_cases hw : w.IsReal
  · have h1 : (homeomorphMixedSpace K x).1 ⟨w, hw⟩ = isometryEquivRealOfIsReal hw (x w) := rfl
    calc ‖x w‖ = ‖(homeomorphMixedSpace K x).1 ⟨w, hw⟩‖ := by
          rw [h1, norm_isometryEquivRealOfIsReal]
      _ ≤ ‖(homeomorphMixedSpace K x).1‖ := norm_le_pi_norm _ _
      _ ≤ ‖homeomorphMixedSpace K x‖ := norm_fst_le _
  · have hc := not_isReal_iff_isComplex.1 hw
    have h1 : (homeomorphMixedSpace K x).2 ⟨w, hc⟩ =
        isometryEquivComplexOfIsComplex hc (x w) := rfl
    calc ‖x w‖ = ‖(homeomorphMixedSpace K x).2 ⟨w, hc⟩‖ := by
          rw [h1, norm_isometryEquivComplexOfIsComplex]
      _ ≤ ‖(homeomorphMixedSpace K x).2‖ := norm_le_pi_norm _ _
      _ ≤ ‖homeomorphMixedSpace K x‖ := norm_snd_le _

theorem exists_norm_schwartz_le_prod (φ : 𝓢(mixedSpace K, ℂ)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x : InfiniteAdeleRing K,
      ‖φ (homeomorphMixedSpace K x)‖ ≤ C * ∏ w, ((1 + ‖x w‖) ^ k)⁻¹ := by
  set d := Fintype.card (InfinitePlace K)
  set C := 2 ^ (k * d) *
    (Finset.Iic (k * d, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) φ
  refine ⟨C, by positivity, fun x ↦ ?_⟩
  set y := homeomorphMixedSpace K x
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k * d, 0)) le_rfl le_rfl φ y
  rw [norm_iteratedFDeriv_zero] at h1
  have hprod : ∏ w, (1 + ‖x w‖) ^ k ≤ (1 + ‖y‖) ^ (k * d) := by
    calc ∏ w, (1 + ‖x w‖) ^ k ≤ ∏ _w : InfinitePlace K, (1 + ‖y‖) ^ k :=
          Finset.prod_le_prod₀ (fun w _ ↦ by positivity) fun w _ ↦
            pow_le_pow_left₀ (by positivity) (by linarith [norm_le_norm_homeomorphMixedSpace x w]) k
      _ = (1 + ‖y‖) ^ (k * d) := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hpos : 0 < ∏ w, (1 + ‖x w‖) ^ k := Finset.prod_pos fun w _ ↦ by positivity
  rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖φ y‖ * ∏ w, (1 + ‖x w‖) ^ k ≤ ‖φ y‖ * (1 + ‖y‖) ^ (k * d) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (1 + ‖y‖) ^ (k * d) * ‖φ y‖ := mul_comm _ _
    _ ≤ C := h1

end

end GroundTheory.Global
end
