module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import Mathlib.Topology.Separation.CompletelyRegular
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

namespace VarIntAdd

theorem ringKrullDim_eq_of_injective_finite {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hfin : f.Finite) : ringKrullDim S = ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hfin.to_isIntegral⟩
  apply le_antisymm
  · have hg : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
      intro q₁ q₂ hq
      have hlt : q₁.asIdeal < q₂.asIdeal := hq
      obtain ⟨hle, x, hx2, hx1⟩ := SetLike.lt_iff_le_and_exists.mp hlt
      show q₁.asIdeal.comap (algebraMap R S) < q₂.asIdeal.comap (algebraMap R S)
      exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hx2, hx1⟩
        (Algebra.IsIntegral.isIntegral x)
    exact Order.krullDim_le_of_strictMono _ hg
  · refine iSup_le fun l => ?_
    have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
      intro r hr
      have : f r = 0 := hr
      rw [show r = 0 from hinj (by rw [this, map_zero])]
      exact Ideal.zero_mem _
    obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker
    have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPo.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    exact le_iSup_of_le L (by rw [hlen])

theorem ringKrullDim_of_isFiniteProjection {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin k) (Fin n) ℂ} (hA : IsFiniteProjection J A) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = k := by
  rw [ringKrullDim_eq_of_injective_finite (projHom J A).toRingHom hA.injective hA.finite,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem chartDens_add {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin k) (Fin n) ℂ}
    (hfin : ∀ y, (fibre J A y).Finite) (f g : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ) :
    chartDens J A (f + g) φ = chartDens J A f φ + chartDens J A g φ := by
  funext y
  simp only [chartDens, sheetSum, Pi.add_apply]
  rw [← finsum_mem_add_distrib (hfin y)]
  refine finsum_mem_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem abs_chartDens_le {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin k) (Fin n) ℂ}
    (hfin : ∀ y, (fibre J A y).Finite) (w : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ)
    (y : Fin k → ℂ) : |chartDens J A w φ y| ≤ chartAbsDens J A w φ y := by
  simp only [chartDens, chartAbsDens, sheetSum]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
  split_ifs <;> simp

end VarIntAdd

theorem VarIntAdd.proof (hCM : ChartMassCompact.Statement) : VarIntAdd.Statement := by
  intro n k J f g φ hJ hfc hfs hgc hgs hφ
  unfold varInt
  split_ifs with h
  · set A := h.choose
    have hA : IsFiniteProjection J A := h.choose_spec
    have hd := VarIntAdd.ringKrullDim_of_isFiniteProjection hA
    have hfin : ∀ y, (fibre J A y).Finite := fun y => (FibreBound.proof n k J A hJ hd hA y).2.1
    have hint : ∀ w : (Fin n → ℂ) → ℝ, Continuous w → HasCompactSupport w →
        Integrable (chartDens J A w φ) := by
      intro w hwc hws
      have hm := SheetSumMeasurable.proof n k J A w φ hJ hd hA hwc.measurable hφ
      refine (hCM n k J A w φ hJ hd hA hwc.continuousOn hφ (Or.inl hws)).mono'
        hm.1.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs]
      exact VarIntAdd.abs_chartDens_le hfin w φ y
    unfold chartInt
    rw [VarIntAdd.chartDens_add hfin, integral_add' (hint f hfc hfs) (hint g hgc hgs)]
  · simp

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal NNReal

noncomputable section

namespace VarMassNearSmall

variable {n d : ℕ}

theorem abs_sheetSum_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ} (hFG : ∀ x s, |F x s| ≤ G x s)
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    |sheetSum J A F y| ≤ sheetSum J A G y := by
  classical
  unfold sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs with h
  · exact hFG x _
  · simp

theorem volume_eq_zero_of_hausdorff {S : Set (Fin d → ℂ)} (hS : μH[((2 * d : ℕ) : ℝ)] S = 0) :
    volume S = 0 := by
  let E : ((Σ _ : Fin d, Fin 2) → ℝ) ≃L[ℝ] (Fin d → ℂ) :=
    (Pi.basis (fun _ : Fin d => Complex.basisOneI)).equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin d, Fin 2) = 2 * d := by
    simp [Fintype.card_sigma, mul_comm]
  have hT : volume (E ⁻¹' S) = 0 := by
    rw [← hausdorffMeasure_pi_real, hcard]
    have h := E.symm.lipschitzWith.hausdorffMeasure_image_le (d := ((2 * d : ℕ) : ℝ)) (by positivity) S
    rw [hS, mul_zero, nonpos_iff_eq_zero, ContinuousLinearEquiv.image_symm_eq_preimage] at h
    exact h
  have : (Measure.map E volume).IsAddHaarMeasure := E.isAddHaarMeasure_map volume
  have hac : (volume : Measure (Fin d → ℂ)) ≪ Measure.map E volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply hac
  exact (E.toHomeomorph.toMeasurableEquiv.map_apply S).trans hT

theorem volume_image_eq_zero (W I : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hI : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < d) :
    volume (A.mulVec '' (zeroSet W ∩ zeroSet I)) = 0 := by
  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ I)) < d :=
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective le_sup_right)).trans_lt hI
  have h0 := NullSmaller.proof n d (W ⊔ I) hdim
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin d → ℂ) :=
    (Matrix.mulVecLin A).toContinuousLinearMap.comp (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap
  have hsub : A.mulVec '' (zeroSet W ∩ zeroSet I) ⊆ L '' zeroSetEuc (W ⊔ I) := by
    rintro _ ⟨x, ⟨hxW, hxI⟩, rfl⟩
    refine ⟨(EuclideanSpace.equiv (Fin n) ℂ).symm x, fun q hq => ?_, by simp only [L, ContinuousLinearMap.comp_apply]; rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
    have hx : (fun i => ((EuclideanSpace.equiv (Fin n) ℂ).symm x) i) = x := rfl
    rw [hx, map_add (f := _), hxW a ha, hxI b hb, add_zero]
  refine volume_eq_zero_of_hausdorff (le_antisymm ?_ bot_le)
  calc μH[((2 * d : ℕ) : ℝ)] (A.mulVec '' (zeroSet W ∩ zeroSet I))
      ≤ μH[((2 * d : ℕ) : ℝ)] (L '' zeroSetEuc (W ⊔ I)) := measure_mono hsub
    _ ≤ _ := L.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [h0, mul_zero]

end VarMassNearSmall


open VarMassNearSmall in
theorem VarMassNearSmall.proof (hCMC : ChartMassCompact.Statement) : VarMassNearSmall.Statement := by
  classical
  intro n d W I φ f hW hdim hφ hI hf hfc δ hδ
  by_cases hA : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection W A
  swap
  · refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun χ _ _ _ => ?_⟩
    unfold varInt
    rw [dite_eq_right hA, abs_zero]
    exact hδ.le
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection W A := hA.choose_spec
  have hvar : ∀ g, varInt W d g φ = ∫ y, chartDens W A g φ y := fun g => by
    unfold varInt chartInt
    rw [dite_eq_left hA]
  have hfin : ∀ y, (fibre W A y).Finite := fun y => (FibreBound.proof n d W A hW hdim hAf y).2.1
  have hS : IsClosed (zeroSet I) := SheetSumMeasurable.isClosed_zeroSet I
  set U : ℕ → Set (Fin n → ℂ) := fun k => Metric.thickening (1 / ((k : ℝ) + 1)) (zeroSet I) with hU
  set F : ℕ → (Fin d → ℂ) → ℝ := fun k => chartAbsDens W A ((U k).indicator fun x => |f x|) φ with hF
  set G := chartAbsDens W A (fun x => |f x|) φ with hG
  have hGi : Integrable G := hCMC n d W A _ φ hW hdim hAf (continuous_abs.comp hf).continuousOn hφ
    (Or.inl (hfc.comp_left abs_zero))
  have hFm : ∀ k, Measurable (F k) := fun k => (SheetSumMeasurable.proof n d W A _ φ hW hdim hAf
    ((continuous_abs.comp hf).measurable.indicator Metric.isOpen_thickening.measurableSet) hφ).2
  have hFG : ∀ k y, ‖F k y‖ ≤ G y := by
    intro k y
    rw [Real.norm_eq_abs]
    refine abs_sheetSum_le W A (fun x s => ?_) (hfin y)
    rw [abs_abs, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    by_cases hx : x ∈ U k
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact abs_nonneg _
  have hlim : ∀ᵐ y, Tendsto (fun k => F k y) atTop (𝓝 0) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_image_eq_zero W I A hI)] with y hy
    have hx : ∀ x ∈ fibre W A y, ∀ᶠ k in atTop, x ∉ U k := by
      intro x hxf
      have hxS : x ∉ zeroSet I := fun h => hy ⟨x, ⟨hxf.1, h⟩, hxf.2⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl x hxS
      obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
      filter_upwards [eventually_ge_atTop K] with k hk hxU
      obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.1 hxU
      have hKk : (K : ℝ) + 1 ≤ (k : ℝ) + 1 := by
        have : (K : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have hle : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hKk
      exact hball (show dist z x < ε by rw [dist_comm]; linarith) hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_all_finite (hfin y)).2 hx] with k hk
    symm
    show sheetSum W A _ y = 0
    unfold sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    refine Finset.sum_eq_zero fun x hxm => ?_
    rw [Set.Finite.mem_toFinset] at hxm
    split_ifs <;> simp [Set.indicator_of_notMem (hk x hxm)]
  have hT := tendsto_integral_of_dominated_convergence G (fun k => (hFm k).aestronglyMeasurable) hGi
    (fun k => Eventually.of_forall (hFG k)) hlim
  simp only [integral_zero] at hT
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hT).2 δ hδ).exists
  refine ⟨U k, Metric.isOpen_thickening, Metric.self_subset_thickening (by positivity) _,
    fun χ hχ hχ1 hχU => ?_⟩
  have hFi : Integrable (F k) := hGi.mono' (hFm k).aestronglyMeasurable (Eventually.of_forall (hFG k))
  have hpt : ∀ y, ‖chartDens W A (fun x => χ x * f x) φ y‖ ≤ F k y := by
    intro y
    rw [Real.norm_eq_abs]
    refine abs_sheetSum_le W A (fun x s => ?_) (hfin y)
    by_cases hx : x ∈ U k
    · rw [Set.indicator_of_mem hx, abs_mul, abs_mul, abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) (hχ1 x)) (abs_nonneg _)
    · have h0 : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hχU h)
      simp only [h0, zero_mul, abs_zero]
      positivity
  have h1 := norm_integral_le_of_norm_le hFi (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs, ← hvar] at h1
  exact h1.trans hk.le

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace ChartIntCountAdd

variable {n d : ℕ}

theorem hasSum_indicator {E : ℕ → Set (Fin n → ℂ)} (hE : Pairwise (Function.onFun Disjoint E))
    (g : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) :
    HasSum (fun i => (E i).indicator g x) ((⋃ i, E i).indicator g x) := by
  by_cases hx : x ∈ ⋃ i, E i
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    have hval : (⋃ i, E i).indicator g x = (E j).indicator g x := by
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hj]
    rw [hval]
    refine hasSum_single j fun i hi => ?_
    have hxi : x ∉ E i := fun hxi => Set.disjoint_left.1 (hE hi) hxi hj
    simp [hxi]
  · have h0 : ∀ i, (E i).indicator g x = 0 := fun i => by
      have hxi : x ∉ E i := fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩)
      simp [hxi]
    have hu : (⋃ i, E i).indicator g x = 0 := by simp only [Set.indicator_of_notMem hx]
    simp only [h0, hu]
    exact hasSum_zero


open Classical in
theorem sheetSum_eq_sum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) :
    sheetSum J A F y =
      ∑ x ∈ hfin.toFinset, (if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0) := by
  unfold sheetSum
  exact finsum_mem_eq_finite_toFinset_sum _ hfin

theorem hasSum_sheetSum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : ℕ → (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (hF : ∀ x s, HasSum (fun i => F i x s) (G x s)) :
    HasSum (fun i => sheetSum J A (F i) y) (sheetSum J A G y) := by
  classical
  simp only [sheetSum_eq_sum hfin]
  refine hasSum_sum fun x _ => ?_
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h]; exact hF x _
  · simp only [dif_neg h]; exact hasSum_zero

theorem abs_sheetSum_le {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) :
    |sheetSum J A F y| ≤ sheetSum J A (fun x s => |F x s|) y := by
  classical
  rw [sheetSum_eq_sum hfin, sheetSum_eq_sum hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h, le_refl]
  · simp only [dif_neg h, abs_zero, le_refl]

theorem sheetSum_mono {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ}
    (hFG : ∀ x s, F x s ≤ G x s) : sheetSum J A F y ≤ sheetSum J A G y := by
  classical
  rw [sheetSum_eq_sum hfin, sheetSum_eq_sum hfin]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h]; exact hFG x _
  · simp only [dif_neg h, le_refl]

theorem indicator_mul (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    S.indicator f x * c = S.indicator (fun z => f z * c) x := by
  by_cases hx : x ∈ S <;> simp [hx]

theorem abs_indicator_mul (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    |S.indicator f x * c| = S.indicator (fun z => |f z * c|) x := by
  by_cases hx : x ∈ S <;> simp [hx]

theorem abs_indicator_mul_le (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    |S.indicator f x * c| ≤ |f x * c| := by
  by_cases hx : x ∈ S <;> simp [hx] <;> positivity

end ChartIntCountAdd


open ChartIntCountAdd in
theorem ChartIntCountAdd.proof (hCM : ChartMassCompact.Statement) : ChartIntCountAdd.Statement := by
  intro n d W A f φ E hW hdim hA hf hfc hφ hEm hE
  have hfin : ∀ y, (fibre W A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n d W A hW hdim hA y).2.1
  have hmeas : ∀ g : (Fin n → ℂ) → ℝ, Measurable g →
      Measurable (chartDens W A g φ) ∧ Measurable (chartAbsDens W A g φ) := fun g hg =>
    SheetSumMeasurable.proof n d W A g φ hW hdim hA hg hφ
  have hgm : ∀ i, Measurable ((E i).indicator f) := fun i => hf.measurable.indicator (hEm i)
  have hgu : Measurable ((⋃ i, E i).indicator f) := hf.measurable.indicator (MeasurableSet.iUnion hEm)

  have hdens : ∀ y, HasSum (fun i => chartDens W A ((E i).indicator f) φ y)
      (chartDens W A ((⋃ i, E i).indicator f) φ y) := by
    intro y
    unfold chartDens
    refine hasSum_sheetSum (hfin y) _ _ fun x s => ?_
    simp only [indicator_mul]
    exact hasSum_indicator hE _ x
  have habs : ∀ y, HasSum (fun i => chartAbsDens W A ((E i).indicator f) φ y)
      (chartAbsDens W A ((⋃ i, E i).indicator f) φ y) := by
    intro y
    unfold chartAbsDens
    refine hasSum_sheetSum (hfin y) _ _ fun x s => ?_
    simp only [abs_indicator_mul]
    exact hasSum_indicator hE _ x

  have hdom : Integrable (chartAbsDens W A ((⋃ i, E i).indicator f) φ) := by
    refine (hCM n d W A f φ hW hdim hA hf.continuousOn hφ (Or.inl hfc)).mono'
      (hmeas _ hgu).2.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    unfold chartAbsDens
    refine (abs_sheetSum_le (hfin y) _).trans (sheetSum_mono (hfin y) fun x s => ?_)
    rw [abs_abs]
    exact abs_indicator_mul_le _ _ _ _
  have hsum : (fun y => ∑' i, chartAbsDens W A ((E i).indicator f) φ y) =
      chartAbsDens W A ((⋃ i, E i).indicator f) φ := funext fun y => (habs y).tsum_eq
  exact hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun i => chartDens W A ((E i).indicator f) φ)
    (f := chartDens W A ((⋃ i, E i).indicator f) φ)
    (fun i => chartAbsDens W A ((E i).indicator f) φ)
    (fun i => (hmeas _ (hgm i)).1.aestronglyMeasurable)
    (fun i => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact abs_sheetSum_le (hfin y) _)
    (ae_of_all _ fun y => (habs y).summable)
    (by rw [hsum]; exact hdom)
    (ae_of_all _ hdens)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence

theorem CMRingUnmixed.proof : CMRingUnmixed.Statement := by
  intro A _ _ p hp
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)
  obtain ⟨hprime, y, hy⟩ := isAssociatedPrime_iff.mp hp
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg
  rw [← hy, ← hdim] at hD
  have heq : ringKrullDim (A ⧸ p) = ringKrullDim A :=
    le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD
  refine ⟨⟨⟨hprime, bot_le⟩, fun q hq hqp => ?_⟩, heq⟩
  by_contra hpq
  have hlt : q < p := lt_of_le_of_ne hqp fun h => hpq (h ▸ le_rfl)
  have hq' : q.IsPrime := hq.1
  have h1 := Order.coheight_add_one_le (α := PrimeSpectrum A) (a := ⟨p, hprime⟩) (b := ⟨q, hq'⟩) hlt
  have h2 : ringKrullDim (A ⧸ q) ≤ ringKrullDim A :=
    ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  rw [ringKrullDim_quotient_eq_coheight, hdim] at h2
  rw [ringKrullDim_quotient_eq_coheight, hdim] at heq
  have e1 : Order.coheight (⟨p, hprime⟩ : PrimeSpectrum A) = (rs.length : ℕ∞) := by exact_mod_cast heq
  have e2 : Order.coheight (⟨q, hq'⟩ : PrimeSpectrum A) ≤ (rs.length : ℕ∞) := by exact_mod_cast h2
  rw [e1] at h1
  have h3 : ((rs.length + 1 : ℕ) : ℕ∞) ≤ (rs.length : ℕ) := by exact_mod_cast h1.trans e2
  have h4 : rs.length + 1 ≤ rs.length := by exact_mod_cast h3
  omega

end GroundTheory.Heights₂.Heights
end
