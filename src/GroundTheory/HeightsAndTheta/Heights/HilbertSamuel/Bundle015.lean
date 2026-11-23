module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem TranscRatioDeg.proof : TranscRatioDeg.Statement := by
  intro ι E _ _ u D e w i₀ Φ _ _ hi₀ he hw ht hΦ
  have ht0 : w 0 ≠ 0 := by
    intro h0
    apply ht
    rw [h0]
    exact isAlgebraic_zero
  have hwk : ∀ k, w k = w 0 * (u (e k) / u (e 0)) := fun k => by
    rw [mul_div_assoc', ← hw k, mul_div_cancel_right₀ _ (he 0)]

  have hfn : ∀ {κ : Type} (v : κ → E) (K : Subfield E), (∀ i j, v i / v j ∈ K) →
      ∀ x ∈ fnField v, x ∈ K := by
    intro κ v K hK x hx
    have : (fnField v).toSubfield ≤ K := by
      unfold fnField
      rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro _ (⟨q, rfl⟩ | ⟨i, j, rfl⟩)
      · rw [eq_ratCast]
        exact SubfieldClass.ratCast_mem K q
      · exact hK i j
    exact this hx
  have hrat : ∀ i j, u i / u j ∈ fnField u := fun i j =>
    IntermediateField.subset_adjoin ℚ _ ⟨i, j, rfl⟩
  have hle : fnField (u ∘ e) ≤ fnField u := fun x hx =>
    hfn (u ∘ e) (fnField u).toSubfield (fun k l => hrat (e k) (e l)) x hx
  set F₀ := fnField (u ∘ e)
  set A := IntermediateField.extendScalars hle
  set L := IntermediateField.adjoin F₀ {w 0}

  have hL : ∀ x, x ∈ L ↔ x ∈ Subfield.closure (Set.range w) := by
    have h1 : L.toSubfield ≤ Subfield.closure (Set.range w) := by
      rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro _ (⟨⟨x, hx⟩, rfl⟩ | h)
      · refine hfn (u ∘ e) _ (fun k l => ?_) x hx
        have : (u ∘ e) k / (u ∘ e) l = w k / w l := by
          rw [hwk k, hwk l]
          field_simp [ht0, he 0, he l]
          simp only [Function.comp_apply]
          ring
        rw [this]
        exact div_mem (Subfield.subset_closure ⟨k, rfl⟩) (Subfield.subset_closure ⟨l, rfl⟩)
      · rw [Set.mem_singleton_iff.1 h]
        exact Subfield.subset_closure ⟨0, rfl⟩
    have h2 : Subfield.closure (Set.range w) ≤ L.toSubfield := by
      rw [Subfield.closure_le]
      rintro _ ⟨k, rfl⟩
      rw [hwk k]
      have hr : u (e k) / u (e 0) ∈ F₀ := IntermediateField.subset_adjoin ℚ _ ⟨k, 0, rfl⟩
      exact mul_mem (IntermediateField.mem_adjoin_simple_self F₀ (w 0))
        (IntermediateField.algebraMap_mem L (⟨_, hr⟩ : F₀))
    exact fun x => ⟨fun hx => h1 hx, fun hx => h2 hx⟩
  have hLset : Set.range (algebraMap L E) = (Subfield.closure (Set.range w) : Set E) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (hL _).1 y.2
    · intro hx
      exact ⟨⟨x, (hL x).2 hx⟩, rfl⟩

  have hQ : ∀ x ∈ fnField u, x ∈ Subfield.closure (Set.range u) := hfn u _ fun i j =>
    div_mem (Subfield.subset_closure ⟨i, rfl⟩) (Subfield.subset_closure ⟨j, rfl⟩)
  have htA : Transcendental A (w 0) :=
    TranscRatioDeg.transcendental_of_subfield (Subfield.closure (Set.range u)) (fun x => hQ _ x.2)
      (algebraMap A E).injective (TranscRatioDeg.transcendental_subfieldClosure u (w 0) ht)
  have key := TranscRatioDeg.finrank_adjoin_eq_of_transcendental A htA
  have hproj : projDeg u e = Module.finrank F₀ A := IntermediateField.relfinrank_eq_finrank_of_le hle
  rw [hproj, ← key]
  apply TranscRatioDeg.finrank_adjoin_congr
  · rw [hΦ]
    apply SetLike.ext'
    rw [RingHom.coe_fieldRange, hLset]
  · rw [← RingHom.coe_fieldRange, hΦ, hLset]
    apply le_antisymm
    · rw [Subfield.closure_le]
      rintro _ (h | ⟨i, rfl⟩)
      · exact Subfield.subset_closure (Or.inl h)
      · exact Subfield.subset_closure (Or.inr (hrat i i₀))
    · rw [Subfield.closure_le]
      rintro x (h | h)
      · exact Subfield.subset_closure (Or.inl h)
      · refine hfn u _ (fun i j => ?_) x h
        have : u i / u j = (u i / u i₀) / (u j / u i₀) := by
          rw [div_div_div_cancel_right₀ hi₀]
        rw [this]
        exact div_mem (Subfield.subset_closure (Or.inr ⟨i, rfl⟩))
          (Subfield.subset_closure (Or.inr ⟨j, rfl⟩))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem PrimeZariskiDense.eval_eq_zero_of_mem_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {F : MvPolynomial (Σ k, ι k) ℂ}
    (hF : F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))) : eval z F = 0 := by
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z) := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact hz.2 f hf
  exact RingHom.mem_ker.mp (hle hF)

theorem PrimeZariskiDense.proof (h1 : ComplexFormsOnPoints.Statement) (h2 : PrimeComplexRadical.Statement)
    (h3 : ComplexMinimalPrimesContract.Statement) : PrimeZariskiDense.Statement := by
  intro K _ ι _ P j hP hj g hg z hz
  by_cases hrel : IsRelevant P
  · set Pc := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPc
    have hgj : g * map (Int.castRingHom ℂ) j ∈ Pc := by
      refine h1 K ι P hP hrel _ fun w hw => ?_
      rw [map_mul]
      by_cases hjw : eval w (map (Int.castRingHom ℂ) j) = 0
      · rw [hjw, mul_zero]
      · rw [hg w hw hjw, zero_mul]
    have hrad : Pc.radical = Pc := (h2 (Σ k, ι k) P hP).radical
    have hgPc : g ∈ Pc := by
      rw [← hrad, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
      intro Q hQ
      change Q ∈ Pc.minimalPrimes at hQ
      have hQp : Q.IsPrime := hQ.1.1
      have hjQ : map (Int.castRingHom ℂ) j ∉ Q := by
        intro h
        apply hj
        rw [← h3 (Σ k, ι k) P hP Q hQ, Ideal.mem_comap]
        exact h
      exact (hQp.mem_or_mem (hQ.1.2 hgj)).resolve_right hjQ
    exact PrimeZariskiDense.eval_eq_zero_of_mem_map P hz hgPc
  · exfalso
    simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
    obtain ⟨k, hk⟩ := hrel
    obtain ⟨i, hi⟩ := hz.1 k
    apply hi
    simpa using hz.2 _ (hk i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem MetricMaxComparison.proof : MetricMaxComparison.Statement := by
  intro K _ ι _ A hA

  let blk : (k : K) → ((Σ k, ι k) → ℂ) → (ι k → ℂ) := fun k z i => z ⟨k, i⟩
  have hblkc : ∀ k, Continuous (blk k) := fun k => continuous_pi fun i => continuous_apply _
  let S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ‖blk k z‖ = 1}
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hS : S = ⋂ k, (fun z => ‖blk k z‖) ⁻¹' {1} := by ext z; simp [S]
      rw [hS]
      exact isClosed_iInter fun k => isClosed_singleton.preimage (hblkc k).norm
    · refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro p
      calc ‖z p‖ = ‖blk p.1 z p.2‖ := rfl
        _ ≤ ‖blk p.1 z‖ := norm_le_pi_norm _ _
        _ = 1 := hz p.1
  have hSU : S ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : blk k z = 0 := funext h
    have h1 : ‖blk k z‖ = 1 := hz k
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨C0, hC0⟩ := hSc.exists_bound_of_continuousOn (hA.continuousOn.mono hSU)
  refine ⟨max C0 1, le_max_right _ _, fun z hz => ?_⟩
  have hn : ∀ k, 0 < ‖blk k z‖ := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact norm_pos_iff.mpr fun h0 => hi (congrFun h0 i)
  let c : K → ℂ := fun k => ((‖blk k z‖⁻¹ : ℝ) : ℂ)
  have hc0 : ∀ k, c k ≠ 0 := fun k => by
    simp only [c, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (hn k).ne'
  have hcn : ∀ k, ‖c k‖ = ‖blk k z‖⁻¹ := fun k => by
    simp only [c, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (inv_pos.mpr (hn k))
  have hwS : (fun p : Σ k, ι k => c p.1 * z p) ∈ S := fun k => by
    have h1 : blk k (fun p : Σ k, ι k => c p.1 * z p) = c k • blk k z := rfl
    rw [h1, norm_smul, hcn, inv_mul_cancel₀ (hn k).ne']
  have hmax : (HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) A.a).h z = ∏ k, ‖blk k z‖ ^ A.a k := rfl
  have hprod : (∏ k, ‖blk k z‖ ^ A.a k) * (∏ k, ‖c k‖ ^ A.a k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hcn, ← mul_zpow, mul_inv_cancel₀ (hn k).ne', one_zpow]
  have hz' : A.h z = (∏ k, ‖blk k z‖ ^ A.a k) * A.h (fun p : Σ k, ι k => c p.1 * z p) := by
    rw [A.smul c z hc0, ← mul_assoc, hprod, one_mul]
  have hpos : 0 ≤ ∏ k, ‖blk k z‖ ^ A.a k :=
    Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
  have hbw : A.h (fun p : Σ k, ι k => c p.1 * z p) ≤ max C0 1 := by
    have h1 := hC0 _ hwS
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  rw [hmax, hz', mul_comm (max C0 1)]
  exact mul_le_mul_of_nonneg_left hbw hpos

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem NonvanishingDense.aeval_map_rat {σ : Type} (z : σ → ℂ) (g : MvPolynomial σ ℤ) :
    aeval z (map (Int.castRingHom ℚ) g) = eval z (map (Int.castRingHom ℂ) g) := by
  rw [aeval_def, eval₂_map, eval_map]
  congr 1

theorem NonvanishingDense.proof (h : RatPrimeDense.Statement) : NonvanishingDense.Statement := by
  intro K _ ι _ P d f hP hf z hz
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, -⟩ := hP
  let _ : Algebra (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) := algebraMvPolynomial
  have hφ : ∀ g, algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) g =
      map (Int.castRingHom ℚ) g := fun g => by
    change map (algebraMap ℤ ℚ) g = _
    congr 1
  have hdisj : Disjoint ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)) : Set (MRing ι)) ↑P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, hn, rfl⟩ hnP
    have : n ∈ P.comap (C : ℤ →+* MRing ι) := hnP
    rw [hhor, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hn this
  set Pq := Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ)) P
  have hPq : Pq.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors ℤ).map C) _ P hprime hdisj
  have hunder : Pq.comap (algebraMap _ _) = P :=
    IsLocalization.under_map_of_isPrime_disjoint ((nonZeroDivisors ℤ).map C) _ hprime hdisj
  have hfq : map (Int.castRingHom ℚ) f ∉ Pq := fun h' => hf (by
    rw [← hunder, Ideal.mem_comap, hφ]; exact h')

  have hzero : ∀ w : (Σ k, ι k) → ℂ, (∀ g ∈ P, eval w (map (Int.castRingHom ℂ) g) = 0) →
      ∀ g ∈ Pq, aeval w g = 0 := by
    intro w hw g hg
    have hle : Pq ≤ RingHom.ker (aeval w : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] ℂ).toRingHom := by
      refine Ideal.map_le_iff_le_comap.mpr fun g' hg' => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ]
      change aeval w (map (Int.castRingHom ℚ) g') = 0
      rw [NonvanishingDense.aeval_map_rat]
      exact hw g' hg'
    exact hle hg
  have hz' : z ∈ closure {w : (Σ k, ι k) → ℂ | (∀ g ∈ Pq, aeval w g = 0) ∧
      aeval w (map (Int.castRingHom ℚ) f) ≠ 0} := h _ Pq _ hPq hfq (hzero z hz.2)
  have hU : IsOpen {w : (Σ k, ι k) → ℂ | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  refine closure_mono ?_ (hU.inter_closure ⟨hz.1, hz'⟩)
  rintro w ⟨hwU, hwP, hwf⟩
  refine ⟨⟨hwU, fun g hg => ?_⟩, ?_⟩
  · rw [← NonvanishingDense.aeval_map_rat, ← hφ]
    exact hwP _ (Ideal.mem_map_of_mem _ hg)
  · rwa [← NonvanishingDense.aeval_map_rat]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace NormCountBounded

section Coords

variable {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

theorem aeval_mul_zpow_mem (x : Ix κ → Ω) (c : κ) {τ : ℕ} {g : MRing (GlobalTheory κ)}
    (hg : IsMultiHomog g (fun _ => τ)) :
    aeval x g * x ⟨(), c⟩ ^ (-(τ : ℤ)) ∈ chartRingZ (ι := GlobalTheory κ) x (fun _ => c) := by
  have hsum : ∀ m ∈ g.support, ∑ p ∈ m.support, m p = τ := by
    intro m hm
    rw [Finset.sum_subset (Finset.subset_univ m.support) (fun p _ hp => by simpa using hp),
      Fintype.sum_sigma]
    simpa using hg m hm ()
  have key : aeval x g * x ⟨(), c⟩ ^ (-(τ : ℤ)) =
      aeval (fun p : Ix κ => x p / x ⟨(), c⟩) g := by
    conv_lhs => rw [g.as_sum]
    conv_rhs => rw [g.as_sum]

    rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
    simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum m hm,
      zpow_neg, zpow_natCast]
    ring
  rw [key, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem secM_le_chartLat (x : Ix κ → Ω) (τ : ℕ) :
    secM (ι := GlobalTheory κ) x (fun _ => τ) ≤ chartLat (ι := GlobalTheory κ) x 1 τ := by
  intro s hs
  have hle : Submodule.span ℤ {s | ∃ g : MRing (GlobalTheory κ), IsMultiHomog g (fun _ => τ) ∧ aeval x g = s} ≤
      (chartLat (ι := GlobalTheory κ) x 1 τ).toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩ c _
    have hc : c = fun _ => c () := rfl
    rw [hc]
    simpa using aeval_mul_zpow_mem x (c ()) hg
  exact hle hs

end Coords

section Counts

variable {Ω : Type} [Field Ω]

theorem norm_count_bounded {h : ℕ → ℝ} {C : ℝ} (D : ℕ) (hC : ∀ τ, h τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1)) :
    ∃ B, ∀ᶠ τ in atTop, h τ / ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤ B := by
  refine ⟨|C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ), eventually_atTop.2 ⟨1, fun τ hτ => ?_⟩⟩
  have hτ' : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
  have hfac : (0 : ℝ) < (D + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hden : 0 < (τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  rw [div_le_iff₀ hden]
  have h1 : ((τ : ℝ) + 1) ^ (D + 1) ≤ 2 ^ (D + 1) * (τ : ℝ) ^ (D + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc h τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1) := hC τ
    _ ≤ |C| * ((τ : ℝ) + 1) ^ (D + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 ^ (D + 1) * (τ : ℝ) ^ (D + 1)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = |C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) * ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
      field_simp

end Counts

end NormCountBounded

namespace NormCountBounded

end NormCountBounded


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def subGrading {S : Type*} [CommRing S] {K : Type*} {ι : K → Type*} {M : Type*} [AddCommGroup M]
    [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (N : Submodule (MRingOver S ι) M) (c : K → ℤ) : Submodule S N :=
  (𝓜 c).comap (N.subtype.restrictScalars S)

def quotGrading {S : Type*} [CommRing S] {K : Type*} {ι : K → Type*} {N : Type*} [AddCommGroup N]
    [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N]
    (𝓝 : (K → ℤ) → Submodule S N) (L : Submodule (MRingOver S ι) N) (c : K → ℤ) : Submodule S (N ⧸ L) :=
  (𝓝 c).map (L.mkQ.restrictScalars S)

def GradedSubquot.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (G H : Set M),
    KH.IsMGraded S ι 𝓜 → (∀ x ∈ G, ∃ c, x ∈ 𝓜 c) → (∀ x ∈ H, ∃ c, x ∈ 𝓜 c) →
    Submodule.span (MRingOver S ι) G ≤ Submodule.span (MRingOver S ι) H →
    KH.IsMGraded S ι (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) ∧
      KH.IsMGraded S ι (quotGrading (subGrading 𝓜 (Submodule.span (MRingOver S ι) H))
        ((Submodule.span (MRingOver S ι) G).comap (Submodule.span (MRingOver S ι) H).subtype))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def ArithKleiman.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (D + 1) → P0 ≤ P → IsSemipositiveRel P0 P A →
    NefOnFibres P A.a → IsConjInvariantH A →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A]) →
    0 ≤ II K ι P (D + 1) (fun _ => A)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
