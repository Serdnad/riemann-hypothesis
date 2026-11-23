module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle001
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle003

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace LatticeCountVolume

theorem measure_le_encard_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (La : Submodule ℤ E) [DiscreteTopology La] [IsZLattice ℝ La]
    (S T : Set E) (hS : MeasurableSet S) (hST : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ T) {F : Set E}
    (fund : IsAddFundamentalDomain La F μ) :
    μ S ≤ (({x : E | x ∈ La ∧ x ∈ T}.encard : ℕ∞) : ℝ≥0∞) * μ F := by
  have : MeasurableVAdd La E := (inferInstance : MeasurableVAdd La.toAddSubgroup E)
  have : VAddInvariantMeasure La E μ :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup E μ)
  have : Countable La := inferInstance
  set A := {x : E | x ∈ La ∧ x ∈ T} with hAdef
  have key : ∀ y : E, ∑' g : La, S.indicator (1 : E → ℝ≥0∞) (g +ᵥ y) ≤
      ((A.encard : ℕ∞) : ℝ≥0∞) := by
    intro y
    set U : Set La := {g | (g : E) + y ∈ S} with hUdef
    have h1 : ∑' g : La, S.indicator (1 : E → ℝ≥0∞) (g +ᵥ y) =
        ∑' g : La, U.indicator (1 : La → ℝ≥0∞) g := by
      congr 1
    rw [h1, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    refine ENat.toENNReal_le.mpr ?_
    rcases U.eq_empty_or_nonempty with hU | ⟨g₀, hg₀⟩
    · simp [hU]
    refine Set.encard_le_encard_of_injOn (f := fun g : La => (g : E) - g₀) ?_ ?_
    · intro g hg
      refine ⟨La.sub_mem g.2 g₀.2, ?_⟩
      have hsub : (g : E) - g₀ = ((g : E) + y) - ((g₀ : E) + y) := by abel
      show (g : E) - g₀ ∈ T
      rw [hsub]
      exact hST _ hg _ hg₀
    · intro g _ g' _ h
      exact Subtype.ext (sub_left_injective h)
  calc μ S = ∫⁻ z, S.indicator 1 z ∂μ := (lintegral_indicator_one hS).symm
    _ = ∑' g : La, ∫⁻ z in F, S.indicator 1 (g +ᵥ z) ∂μ := fund.lintegral_eq_tsum'' _
    _ = ∫⁻ z in F, ∑' g : La, S.indicator 1 (g +ᵥ z) ∂μ :=
        (lintegral_tsum fun g => ((measurable_one.indicator hS).comp
          (measurable_const_vadd g)).aemeasurable).symm
    _ ≤ ∫⁻ _ in F, ((A.encard : ℕ∞) : ℝ≥0∞) ∂μ := lintegral_mono fun z => key z
    _ = ((A.encard : ℕ∞) : ℝ≥0∞) * μ F := setLIntegral_const _ _


open scoped Classical in
theorem proof : LatticeCountVolume.Statement := by
  intro E _ _ _ _ _ μ _ La _ _ S T hS hST
  set b := Module.Free.chooseBasis ℤ La
  have fund := ZLattice.isAddFundamentalDomain b μ
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain La μ fund
  have hFtop : μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  rw [hcov, measureReal_def, ENNReal.ofReal_toReal hFtop]
  exact measure_le_encard_mul μ La S T hS hST fund

end LatticeCountVolume

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace


open scoped Classical in
theorem EmbeddingSumPlaces.proof : EmbeddingSumPlaces.Statement := by
  intro F _ _ g hg
  rw [← Finset.univ.sum_fiberwise (fun σ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have h : ∀ σ ∈ ({σ | InfinitePlace.mk σ = w} : Finset (F →+* ℂ)), g σ = g w.embedding := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    subst hσ
    rcases embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h, hg]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast card_filter_mk_eq w

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Metric
open scoped ENNReal NNReal

namespace MixedBoxCount


open scoped Classical in
theorem finite_box (F : Type) [Field F] [NumberField F] (La : Submodule ℤ (mixedSpace F))
    [DiscreteTopology La] (f : InfinitePlace F → ℝ) (hf : ∀ w, 0 < f w) :
    {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.Finite := by
  have hsub : {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w} ⊆
      closedBall 0 (∑ w, f w) ∩ (La : Set (mixedSpace F)) := by
    rintro y ⟨hyL, hy⟩
    refine ⟨?_, hyL⟩
    rw [mem_closedBall_zero_iff, norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun w _ => (hy w).trans ?_
    exact Finset.single_le_sum (fun v _ => (hf v).le) (Finset.mem_univ w)
  refine Set.Finite.subset ?_ hsub
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete


open scoped Classical in
theorem normAtPlace_lt_of_mem (F : Type) [Field F] [NumberField F] (g : InfinitePlace F → ℝ≥0)
    {x : mixedSpace F} (hx : x ∈ convexBodyLT F g) (w : InfinitePlace F) : normAtPlace w x < g w := by
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw]
    have := hx.1 ⟨w, hw⟩ (Set.mem_univ _)
    simpa [mem_ball_zero_iff] using this
  · rw [normAtPlace_apply_of_isComplex hw]
    have := hx.2 ⟨w, hw⟩ (Set.mem_univ _)
    simpa [mem_ball_zero_iff] using this

end MixedBoxCount


open scoped Classical in
theorem MixedBoxCount.proof (h : LatticeCountVolume.Statement) : MixedBoxCount.Statement := by
  intro F _ _ La _ _ f hf
  have hfin := MixedBoxCount.finite_box F La f hf
  refine ⟨hfin, ?_⟩
  set B := {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w} with hB
  let g : InfinitePlace F → ℝ≥0 := fun w => ⟨f w / 2, (half_pos (hf w)).le⟩
  have hS : MeasurableSet (convexBodyLT F g) :=
    (MeasurableSet.univ_pi fun _ => measurableSet_ball).prod
      (MeasurableSet.univ_pi fun _ => measurableSet_ball)
  have hdiff : ∀ x ∈ convexBodyLT F g, ∀ y ∈ convexBodyLT F g,
      x - y ∈ {z : mixedSpace F | ∀ w, normAtPlace w z ≤ f w} := by
    intro x hx y hy w
    have h1 := MixedBoxCount.normAtPlace_lt_of_mem F g hx w
    have h2 := MixedBoxCount.normAtPlace_lt_of_mem F g hy w
    have h3 := normAtPlace_add_le w x (-y)
    rw [normAtPlace_neg, ← sub_eq_add_neg] at h3
    have : ((g w : ℝ≥0) : ℝ) = f w / 2 := rfl
    linarith
  have hle := h (mixedSpace F) volume La (convexBodyLT F g) _ hS hdiff
  have hset : {x : mixedSpace F | x ∈ La ∧ x ∈ {z : mixedSpace F | ∀ w, normAtPlace w z ≤ f w}} = B := rfl
  rw [hset, convexBodyLT_volume, ← hfin.cast_ncard_eq] at hle
  have hcpos := ZLattice.covolume_pos La volume
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hle
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hcpos.le, NNReal.coe_prod,
    NNReal.coe_pow, ENat.toENNReal_coe, ENNReal.toReal_natCast] at hreal
  have hg : ∀ w, ((g w : ℝ≥0) : ℝ) = f w / 2 := fun _ => rfl
  simp only [hg] at hreal
  have hNpos : 0 < B.ncard :=
    (Set.ncard_pos hfin).mpr ⟨0, La.zero_mem, fun w => by simp [(hf w).le]⟩
  have hN : (0 : ℝ) < (B.ncard : ℝ) := by exact_mod_cast hNpos
  have hc : (0 : ℝ) < (convexBodyLTFactor F : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (convexBodyLTFactor_ne_zero F))
  have hfac : ∀ w, 0 < (f w / 2) ^ mult w := fun w => pow_pos (half_pos (hf w)) _
  have hprod : 0 < ∏ w, (f w / 2) ^ mult w := Finset.prod_pos fun w _ => hfac w
  have hlog := Real.log_le_log (mul_pos hc hprod) hreal
  rw [Real.log_mul hc.ne' hprod.ne', Real.log_mul hN.ne' hcpos.ne',
    Real.log_prod (fun w _ => (hfac w).ne')] at hlog
  have hl : ∀ w, Real.log ((f w / 2) ^ mult w) = (mult w : ℝ) * Real.log (f w) - (mult w : ℝ) * Real.log 2 :=
    fun w => by rw [Real.log_pow, Real.log_div (hf w).ne' two_ne_zero, mul_sub]
  have hcast : (∑ w : InfinitePlace F, (mult w : ℝ)) = (Module.finrank ℚ F : ℝ) := by
    exact_mod_cast sum_mult_eq
  simp only [hl, Finset.sum_sub_distrib, ← Finset.sum_mul, hcast] at hlog
  linarith

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ExistsUniqueRelabel

section RingEquiv

variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R ≃+* R')

theorem mem_map_iff (I : Ideal R) (x : R) : φ x ∈ I.map (φ : R →+* R') ↔ x ∈ I := by
  rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]

theorem map_mem_minimalPrimes {J W : Ideal R} (h : W ∈ J.minimalPrimes) :
    W.map (φ : R →+* R') ∈ (J.map (φ : R →+* R')).minimalPrimes := by
  rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv]
  exact Ideal.minimalPrimes_comap_of_surjective (f := (φ.symm : R' →+* R)) φ.symm.surjective h

theorem map_mem_minimalPrimes_iff {J W : Ideal R} :
    W.map (φ : R →+* R') ∈ (J.map (φ : R →+* R')).minimalPrimes ↔ W ∈ J.minimalPrimes := by
  refine ⟨fun h => ?_, map_mem_minimalPrimes φ⟩
  have := map_mem_minimalPrimes φ.symm h
  rwa [Ideal.map_of_equiv, Ideal.map_of_equiv] at this

theorem ringKrullDim_quot_map (V : Ideal R) :
    ringKrullDim (R' ⧸ V.map (φ : R →+* R')) = ringKrullDim (R ⧸ V) :=
  (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V _ φ rfl)).symm

theorem length_map (V W : Ideal R) [W.IsPrime] [(W.map (φ : R →+* R')).IsPrime] (hVW : V ≤ W)
    (x : R) :
    Module.length (Localization.AtPrime (W.map (φ : R →+* R')))
        (LocalizedModule (W.map (φ : R →+* R')).primeCompl
          (R' ⧸ (V.map (φ : R →+* R') ⊔ Ideal.span {φ x}))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ (V ⊔ Ideal.span {x}))) := by
  set V' := V.map (φ : R →+* R')
  set W' := W.map (φ : R →+* R')
  have hVW' : V' ≤ W' := Ideal.map_mono hVW
  have : (W'.map (Ideal.Quotient.mk V')).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hVW')
  have h' := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.isLocData_atPrime_quot V' W' hVW'
  letI : Algebra R (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) :=
    ((algebraMap R' (Localization.AtPrime (W'.map (Ideal.Quotient.mk V')))).comp
      (φ : R →+* R')).toAlgebra
  have hal : ∀ r, algebraMap R (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) r =
      algebraMap R' (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) (φ r) := fun r => rfl
  have hS : ∀ s : R', s ∈ W'.primeCompl → φ.symm s ∈ W.primeCompl := by
    intro s hs h
    apply hs
    rw [← φ.apply_symm_apply s]
    exact (mem_map_iff φ W _).2 h
  have h : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData R
      (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) W.primeCompl V := by
    refine ⟨fun s hs => ?_, fun y => ?_, fun r hr => ?_, fun v hv => ?_⟩
    · rw [hal]
      exact h'.1 _ (fun h => hs ((mem_map_iff φ W s).1 h))
    · obtain ⟨r, s, hs, e⟩ := h'.2.1 y
      refine ⟨φ.symm r, φ.symm s, hS s hs, ?_⟩
      rw [hal, hal, φ.apply_symm_apply, φ.apply_symm_apply]
      exact e
    · rw [hal] at hr
      obtain ⟨s, hs, e⟩ := h'.2.2.1 _ hr
      refine ⟨φ.symm s, hS s hs, ?_⟩
      rw [← mem_map_iff φ V, map_mul, φ.apply_symm_apply]
      exact e
    · rw [hal]
      exact h'.2.2.2 _ ((mem_map_iff φ V v).2 hv)
  exact (h'.length_eq (φ x)).trans (h.length_eq x).symm

end RingEquiv

section MRing

variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

variable (e : K ≃ K') (σ : (Σ k, ι k) ≃ (Σ k', ι' k')) (hσ : ∀ p, (σ p).1 = e p.1)




include hσ












end MRing

end ExistsUniqueRelabel

universe u v w v' w'

end GroundTheory.Heights₂.Heights.Targets
end
end
