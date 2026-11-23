module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle188
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle284
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle272
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle242
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle295
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle252
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle015
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle035
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LiStatOf
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle027
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
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
import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FolnerLower

section LinAlg

variable {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

omit [FiniteDimensional ℂ G] in
theorem hs_eq_sum (A : H →L[ℂ] G) : hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hs_adjoint [CompleteSpace H] [CompleteSpace G] (A : H →L[ℂ] G) :
    hsNormSq (ContinuousLinearMap.adjoint A) = hsNormSq A := by
  rw [hs_eq_sum, hs_eq_sum]
  have h1 : ∀ j, ‖ContinuousLinearMap.adjoint A (stdOrthonormalBasis ℂ G j)‖ ^ 2 =
      ∑ i, ‖⟪stdOrthonormalBasis ℂ H i, ContinuousLinearMap.adjoint A (stdOrthonormalBasis ℂ G j)⟫_ℂ‖ ^ 2 :=
    fun j => ((stdOrthonormalBasis ℂ H).sum_sq_norm_inner_right _).symm
  have h2 : ∀ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 =
      ∑ j, ‖⟪A (stdOrthonormalBasis ℂ H i), stdOrthonormalBasis ℂ G j⟫_ℂ‖ ^ 2 :=
    fun i => ((stdOrthonormalBasis ℂ G).sum_sq_norm_inner_left _).symm
  simp_rw [h1, h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]

omit [FiniteDimensional ℂ G] in
theorem hs_isom_comp (U : G →L[ℂ] G) (hU : ∀ v, ‖U v‖ = ‖v‖) (A : H →L[ℂ] G) :
    hsNormSq (U.comp A) = hsNormSq A := by
  rw [hs_eq_sum, hs_eq_sum]
  simp [hU]

theorem hs_unitary [CompleteSpace H] [CompleteSpace G] (U : G →L[ℂ] G) (hU : ∀ v, ‖U v‖ = ‖v‖)
    (V : H →L[ℂ] H) (hV : ∀ v, ‖ContinuousLinearMap.adjoint V v‖ = ‖v‖) (A : H →L[ℂ] G) :
    hsNormSq (U.comp (A.comp V)) = hsNormSq A := by
  rw [hs_isom_comp U hU, ← hs_adjoint, ContinuousLinearMap.adjoint_comp, hs_isom_comp _ hV, hs_adjoint]

omit [FiniteDimensional ℂ G] in
theorem hs_continuous : Continuous (hsNormSq : (H →L[ℂ] G) → ℝ) := by
  have : (hsNormSq : (H →L[ℂ] G) → ℝ) = fun A => ∑ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 :=
    funext hs_eq_sum
  rw [this]
  fun_prop

end LinAlg

theorem exists_compact_approx {X E : Type} [PseudoMetricSpace X] [ProperSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ μ' : Measure X) [SFinite μ] [SFinite μ'] (S S' : Set X) (hS : IsClosed S) (hS' : IsClosed S')
    (h0 : μ Sᶜ = 0) (h0' : μ' S'ᶜ = 0) (F : X × X → E) (hF : Integrable F (μ.prod μ')) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ C C' : Set X, IsCompact C ∧ C ⊆ S ∧ IsCompact C' ∧ C' ⊆ S' ∧
      ∀ A A' : Set X, MeasurableSet A → MeasurableSet A' → C ⊆ A → C' ⊆ A' →
        ‖∫ p, F p ∂((μ.restrict A).prod (μ'.restrict A')) - ∫ p, F p ∂(μ.prod μ')‖ < δ := by
  obtain ⟨o⟩ := ‹Nonempty X›
  let K : ℕ → Set (X × X) := fun n =>
    ((S ∩ Metric.closedBall o n) ×ˢ (S' ∩ Metric.closedBall o n))ᶜ
  have hKm : ∀ n, MeasurableSet (K n) := fun n =>
    ((hS.inter Metric.isClosed_closedBall).measurableSet.prod
      (hS'.inter Metric.isClosed_closedBall).measurableSet).compl
  have hKa : Antitone K := by
    intro m n hmn
    have hb : Metric.closedBall o (m : ℝ) ⊆ Metric.closedBall o n :=
      Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    exact Set.compl_subset_compl.2
      (Set.prod_mono (Set.inter_subset_inter_right _ hb) (Set.inter_subset_inter_right _ hb))
  have hlim := tendsto_setIntegral_of_antitone (f := fun p => ‖F p‖) (μ := μ.prod μ') hKm hKa
    ⟨0, hF.norm.integrableOn⟩
  have hnull : (μ.prod μ') (⋂ n, K n) = 0 := by
    have hsub : (⋂ n, K n) ⊆ (Sᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ S'ᶜ) := by
      intro p hp
      by_contra hc
      simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true, true_and,
        not_or, not_not] at hc
      obtain ⟨n, hn⟩ := exists_nat_ge (max (dist p.1 o) (dist p.2 o))
      exact Set.mem_iInter.1 hp n ⟨⟨hc.1, (le_max_left _ _).trans hn⟩, hc.2, (le_max_right _ _).trans hn⟩
    refine measure_mono_null hsub (measure_union_null ?_ ?_) <;> rw [Measure.prod_prod]
    · rw [h0, zero_mul]
    · rw [h0', mul_zero]
  rw [setIntegral_measure_zero _ hnull] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  refine ⟨S ∩ Metric.closedBall o n, S' ∩ Metric.closedBall o n,
    (isCompact_closedBall o n).inter_left hS, Set.inter_subset_left,
    (isCompact_closedBall o n).inter_left hS', Set.inter_subset_left, fun A A' hA hA' hCA hCA' => ?_⟩
  rw [Measure.prod_restrict, ← integral_add_compl (hA.prod hA') hF, sub_add_cancel_left, norm_neg]
  refine (norm_integral_le_integral_norm _).trans_lt (lt_of_le_of_lt ?_ hn)
  refine setIntegral_mono_set hF.norm.integrableOn (Eventually.of_forall fun p => norm_nonneg _)
    (Eventually.of_forall fun p hp => ?_)
  exact Set.compl_subset_compl.2 (Set.prod_mono hCA hCA') hp

theorem le_liminf_of_ratio (b : ENNReal) (hb : b ≠ ⊤) (u m m' n n' : ℕ → ENNReal)
    (hn : ∀ j, 0 < n j ∧ n j < ⊤) (hn' : ∀ j, 0 < n' j ∧ n' j < ⊤)
    (h : Tendsto (fun j => m j / n j) atTop (𝓝 1)) (h' : Tendsto (fun j => m' j / n' j) atTop (𝓝 1))
    (hu : ∀ j, b * (m j * m' j) ≤ u j) : b ≤ liminf (fun j => u j / (n j * n' j)) atTop := by
  have ht : Tendsto (fun j => b * (m j / n j * (m' j / n' j))) atTop (𝓝 (b * (1 * 1))) :=
    ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul h (Or.inl one_ne_zero) h' (Or.inl one_ne_zero))
      (Or.inr hb)
  rw [mul_one, mul_one] at ht
  rw [← ht.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun j => ?_)
  have e : b * (m j / n j * (m' j / n' j)) = b * (m j * m' j) / (n j * n' j) := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl (hn j).1.ne') (Or.inl (hn j).2.ne)]
    ring
  rw [e]
  exact ENNReal.div_le_div_right (hu j) _

variable {k r : ℕ}

theorem measurableSet_rmul_image {t : Mat k r} (ht : IsUnit t.det) {A : Set (Mt k r)}
    (hA : MeasurableSet A) : MeasurableSet (rmulM t '' A) := by
  have : rmulM t '' A = rmulM t⁻¹ ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : rmulM t⁻¹ (rmulM t y) = y := Matrix.mul_nonsing_inv_cancel_right t (Matrix.of y) ht
      rw [Set.mem_preimage, this]; exact hy
    · intro hx
      exact ⟨_, hx, Matrix.nonsing_inv_mul_cancel_right t (Matrix.of x) ht⟩
  rw [this]
  exact (continuous_rmulM _).measurable hA

theorem subset_rmul_image {t : Mt k r} (ht : IsUnit (Matrix.of t : Mat k r).det) {C Oc Om : Set (Mt k r)}
    (h : ∀ c ∈ C, ∀ x ∈ Oc, lmulM (Matrix.of c) x ∈ Om) (hO : invM t ∈ Oc) :
    C ⊆ rmulM (Matrix.of t) '' Om := fun c hc =>
  ⟨_, h c hc _ hO, Matrix.nonsing_inv_mul_cancel_right (Matrix.of t) (Matrix.of c) ht⟩

theorem hsNormSq_Iint_le_liminf : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ Om Om' : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om → IsFolner (Sset k r z') μS' Om' → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∀ γ ∈ Greg k r z z', ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' γ)) ≤ Filter.liminf (fun j => (∫⁻ p, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' (Matrix.of (act2 γ p)))) ∂(μS.prod μS')) / (μS (Om j) * μS' (Om' j))) Filter.atTop := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' Om Om' hF hF'
    x hx y hy ξ ξ' γ hγ
  have hint := (GlobalTheory.T.besselOrbitalIntegral_eq_inv_deg_smul k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' y hy x hx ξ ξ' γ hγ).1
  have hcl := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hS.1 hS.2.1).2.2.2.1
  have hcl' := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hS'.1 hS'.2.1).2.2.2.1
  have hP := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hS.1 hS.2.1 hS.2.2.1
  have hP' := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z' c' π' hS'.1 hS'.2.1 hS'.2.2.1
  have hinv := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hS.1 hS.2.1 μS).1 hS.2.2.2.1).2
  have hinv' := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z' hS'.1 hS'.2.1 μS').1 hS'.2.2.2.1).2
  haveI := hS.2.2.2.1.1
  haveI := hS'.2.2.2.1.1
  have h0 := hS.2.2.2.1.2.2.1
  have h0' := hS'.2.2.2.1.2.2.1
  refine ENNReal.le_of_forall_nnreal_lt fun b hb => ?_
  have hb' : (b : ℝ) < hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' γ) := by
    rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg b.coe_nonneg] at hb
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    ((hs_continuous (H := Wq) (G := Wp)).continuousAt.eventually (lt_mem_nhds hb'))
  obtain ⟨C, C', hC, hCS, hC', hCS', happ⟩ := exists_compact_approx μS μS'
    {x | Matrix.of x ∈ Sset k r z} {x | Matrix.of x ∈ Sset k r z'} hcl.2.1 hcl'.2.1 h0 h0' _ hint hδ
  obtain ⟨Oc, hOc, hlim⟩ := hF.2 C hC hCS
  obtain ⟨Oc', hOc', hlim'⟩ := hF'.2 C' hC' hCS'
  refine le_liminf_of_ratio b ENNReal.coe_ne_top _ _ _ _ _ (fun j => (hF.1 j).2.2.2)
    (fun j => (hF'.1 j).2.2.2) hlim hlim' fun j => ?_
  have e1 : μS (Oc j) = μS (invM ⁻¹' Oc j) := by
    rw [← Measure.map_apply measurable_invM (hOc j).1, hinv]
  have e2 : μS' (Oc' j) = μS' (invM ⁻¹' Oc' j) := by
    rw [← Measure.map_apply measurable_invM (hOc' j).1, hinv']
  rw [e1, e2, ← Measure.prod_prod, ← lintegral_indicator_const
    ((measurable_invM (hOc j).1).prod (measurable_invM (hOc' j).1))]
  have hae : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.1 ∈ Sset k r z ∧ Matrix.of p.2 ∈ Sset k r z' :=
    (Measure.quasiMeasurePreserving_fst.ae (p := fun x => Matrix.of x ∈ Sset k r z) h0).and
      (Measure.quasiMeasurePreserving_snd.ae (p := fun x => Matrix.of x ∈ Sset k r z') h0')
  refine lintegral_mono_ae (hae.mono fun p hp => ?_)
  by_cases hm : p ∈ (invM ⁻¹' Oc j) ×ˢ (invM ⁻¹' Oc' j)
  swap
  · rw [Set.indicator_of_notMem hm]; exact zero_le
  rw [Set.indicator_of_mem hm, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hu : IsUnit (Matrix.of p.1 : Mat k r).det := WeylGroupFacts.isUnit_of_uh (hcl.1 hp.1)
  have hu' : IsUnit (Matrix.of p.2 : Mat k r).det := WeylGroupFacts.isUnit_of_uh (hcl'.1 hp.2)
  have heq := GlobalTheory.T.Iint_equivariant_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' x y ξ ξ' (Om j) (Om' j)
    (hF.1 j).1 (hF'.1 j).1 γ hγ.1 _ hp.1 _ hp.2
  have ha : (Matrix.of (act2 γ p) : Mat k r) = Matrix.of p.1 * γ * (Matrix.of p.2)⁻¹ := rfl
  rw [ha, heq, hs_unitary _ (hP.2.1.2.1 _ hp.1)]
  · refine (hball ?_).le
    rw [dist_eq_norm]
    exact happ _ _ (measurableSet_rmul_image hu (hF.1 j).1) (measurableSet_rmul_image hu' (hF'.1 j).1)
      (subset_rmul_image hu (hOc j).2.2 hm.1) (subset_rmul_image hu' (hOc' j).2.2 hm.2)
  · rw [← (hP'.2.2.1 _ hp.2).2, ContinuousLinearMap.adjoint_adjoint]
    exact hP'.2.1.2.1 _ hp.2

end GlobalTheory.SgInf.FolnerLower
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem phiIntegral_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp,
    Integrable (fun y : Mt k r => coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ) μG ∧
    ∫ y, coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ ∂μG =
      ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have hHaarG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hHaarS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  haveI : SigmaFinite μG := hHaarG.1
  haveI : SigmaFinite μS := hHaarS.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hF := GlobalTheory.T.integrable_bessel_fubini_integrand_prod k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have haeG : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.2 hHaarG.2.2.1
  have haeS : ∀ᵐ t ∂μS, Matrix.of t ∈ Sset k r z := ae_iff.2 hHaarS.2.2.1
  have hae : ∀ᵐ y ∂μG, coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ =
      ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) *
        ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS :=
    haeG.mono fun y hy => GlobalTheory.T.matrixCoeff_mul_inner_besselFunctional_eq_integral k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ y hy
  refine ⟨hF.integral_prod_left.congr (hae.mono fun y hy => hy.symm), ?_⟩
  rw [integral_congr_ae hae, integral_integral_swap hF]
  have hin : ∀ᵐ t ∂μS, (∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) *
        ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μG) =
      (⟪u₁, u⟫_ℂ / (d : ℂ)) * (⟪v, σ (Matrix.of t)⁻¹ v⟫_ℂ * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ) := by
    filter_upwards [haeS] with t ht
    rw [integral_mul_const, GlobalTheory.T.besselSchur_translated_matrixCoefficient k r σ w a μG d hStd u u₁ v _ (hcl.2.2.2.1.1 ht)]
    ring
  rw [integral_congr_ae hin, integral_const_mul, GlobalTheory.T.besselSubgroupIntegral_eq_inner_besselForm k r σ w a μG d z c π μS hStd hSide v hv ξ]
  ring

theorem innerIntegral_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν →
    ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp,
    Integrable (fun x : Mt k r => ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x),
      Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ) ν ∧
    ∫ x, ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ ∂ν =
      ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ
  have hHaarG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hHaarS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hUnS := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hSide.1 hSide.2.1 μS).1 hHaarS
  obtain ⟨-, hνG, -, hWeil, -⟩ := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hHaarG hHaarS hUnS hν
  obtain ⟨hφ, hφint⟩ := phiIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  obtain ⟨hWi, hWe⟩ := hWeil ℂ _ hφ
  have haeν : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := ae_iff.2 hνG
  have hae : ∀ᵐ x ∂ν, (∫ s, (fun y : Mt k r => coef σ u v (Matrix.of y) *
        ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ) (lmulM (Matrix.of s) x) ∂μS) =
      ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ :=
    haeν.mono fun x hx => (GlobalTheory.T.inner_besselFunctional_eq_integral_subgroup k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ x hx).symm
  refine ⟨hWi.congr hae, ?_⟩
  rw [← integral_congr_ae hae, ← hWe, hφint]

theorem normIdentity_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) ∧ Integrable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν ∧ MemLp (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) 2 ν ∧ ∫ x, ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ ∂ν = ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) ∧ 0 ≤ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).re ∧ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).im = 0 := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ
  have hw1 : ‖w‖ = 1 := hStd.2.2.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hwD : w ∈ DD σ w := by
    have h1 := mem_DD σ w hcl.1.2.2.1
    rwa [hStd.2.1.1.1, ContinuousLinearMap.one_apply] at h1
  have hAi := GlobalTheory.T.integrable_matrixCoefficient_quotientMeasure k r σ w a μG d z c π μS hStd hSide ν hν u hu v hv ξ
  obtain ⟨hIi, -⟩ := innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν u hu u hu v hv ξ
  have hIe := (innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ).2
  have hsq : Integrable (fun x : Mt k r => ‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖ ^ 2) ν := by
    refine hIi.re.congr (Filter.Eventually.of_forall fun x => ?_)
    exact inner_self_eq_norm_sq _
  obtain ⟨-, hwe⟩ := innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν w hwD w hwD v hv ξ
  have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
  have hL : (∫ x, ⟪Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)⟫_ℂ ∂ν)
      = ((∫ x, ‖Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext x
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [hL, hww, one_mul] at hwe
  have hX : ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ =
      ((d * ∫ x, ‖Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [eq_div_iff hd'] at hwe
    rw [← hwe]; push_cast; ring
  refine ⟨GlobalTheory.T.besselFunctional_equivariant_unipotent_character k r σ w a μG d z c π μS hStd hSide u hu v hv ξ, hAi,
    (memLp_two_iff_integrable_sq_norm hAi.aestronglyMeasurable).2 hsq, hIe, ?_, ?_⟩
  · rw [hX, Complex.ofReal_re]
    exact mul_nonneg hd.le (integral_nonneg fun x => by positivity)
  · rw [hX, Complex.ofReal_im]

end GlobalTheory.SgInf
end

section

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

namespace GlobalTheory.Mass.MaxFormula

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] in
theorem nondegenerate_of_pos {h : V →ₗ⋆[K] V →ₗ[K] K} [NumberField K] (hd : IsTotPosDef h) :
    h.Nondegenerate := by
  have han : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x h0 φ
    simp [hx] at this
  exact ⟨fun x hx => han x (hx x), fun x hx => han x (hx x)⟩

theorem localMassFactor_eq_of_mem_badPrimes (hK : IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : IsMaxLat h M) {P : Ideal (𝓞 K)}
    (hP : P ∈ badP h M) :
    lamP h M (P.comap (algebraMap (𝓞 F) (𝓞 K))) =
      ((qIn P : ℝ) ^ Module.finrank K V - (-1) ^ Module.finrank K V) / ((qIn P : ℝ) + 1) := by
  have hnd := nondegenerate_of_pos hd
  obtain ⟨hc, hq2, hq, -⟩ := (GlobalTheory.MaxLatStruct.main K V h hK hs hnd M hM).2.2.2 P hP
  have hPm : P.IsMaximal := hP.1
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  have h𝔭 : 𝔭.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) P
  obtain ⟨hJ1, hJ2⟩ := jordan_splitting_exists K F V hK hF h hs
  have hfull := hM.1.1
  have hlat := hfull.toIsLattice
  obtain ⟨b, a, hJ⟩ := hJ1 ⊤ M (fun x _ hx => hnd.1 x fun y => hx y trivial)
    ⟨hlat.fg, hfull.span_eq_top⟩ hM.1.2 𝔭 h𝔭
  obtain ⟨i, hi, hj⟩ := GlobalTheory.T.jordan_exponents_maximal_hermitian_lattice_bad_prime K F V hK hF h hs hd M hM P hP b a hJ
  have hv : vd h M 𝔭 = 1 := by
    rw [hJ2 M hlat 𝔭 h𝔭 b a hJ, vJof, Finset.sum_eq_single i (fun j _ => hj j) (by simp)]
    exact hi
  have hcJ : cJof 𝔭 a = 1 := by
    rw [cJof, Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun h1 => by_contra fun h2 => h1 (hj j h2), ?_⟩
    rintro rfl
    rw [hi]
    exact one_ne_zero
  have hN : Ideal.absNorm 𝔭 = qIn P := by
    have := absNorm_comap_inert hK hF hPm hc
    rw [hq] at this
    exact Nat.pow_left_injective two_ne_zero this
  have hη : etaF K F 𝔭 = -1 := by rw [h𝔭def, etaF_comap hK hF hPm, if_pos hc]
  have hdisc : (discAut h ⊤ M 𝔭 : ℝ) = (qIn P : ℝ) + 1 := by
    have hq0 : (qIn P : ℝ) ≠ 0 := by exact_mod_cast (by omega : qIn P ≠ 0)
    rw [GlobalTheory.T.discriminantModule_isometries_eq_normOne_residues K F V hK hF h hs M hlat 𝔭 h𝔭 b a hJ i hi hj,
      ThirdPropositionSlot.normRepCount_extP hK hF h𝔭 le_rfl, ThirdPropositionSlot.alphaStd_one, hη, hN]
    field_simp
    ring
  have hm : 1 ≤ Module.finrank K V := by
    have := i.pos
    rwa [finrank_top] at this
  obtain ⟨m, hm'⟩ : ∃ m, Module.finrank K V = m + 1 := ⟨_, (Nat.sub_add_cancel hm).symm⟩
  have hpos := alphaStd_pos hK hF h𝔭 m
  have hq0 : (0 : ℝ) < qIn P := by exact_mod_cast (by omega : 0 < qIn P)
  rw [lamP, alpha_discriminant_holds K F V hK hF h hs hd M hlat hM.1.2 𝔭 h𝔭 b a hJ, hv, hcJ, hdisc, hm',
    Nat.add_sub_cancel, mul_one]
  have hstep : alphaStd K 𝔭 (m + 1) =
      alphaStd K 𝔭 m * (1 - (-1) ^ (m + 1) * ((qIn P : ℝ) ^ (m + 1))⁻¹) := by
    rw [alphaStd, Finset.prod_Icc_succ_top (by omega), hη, hN, zpow_neg, zpow_natCast, ← hN, ← hη]
    rfl
  rw [hstep, hN]
  field_simp

theorem lamG_eq_lamMax (hK : IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : IsMaxLat h M) :
    lamG F h M = lamMax h M := by
  have hst := GlobalTheory.MaxLatStruct.main K V h hK hs (nondegenerate_of_pos hd) M hM
  have hfin := hst.1
  let g : {P // P ∈ hfin.toFinset} → {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} := fun P =>
    ⟨P.1.comap (algebraMap (𝓞 F) (𝓞 K)), by
      have : P.1.IsMaximal := (hfin.mem_toFinset.1 P.2).1
      exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) P.1⟩
  have hg : Function.Injective g := by
    intro P Q hPQ
    have hP := hfin.mem_toFinset.1 P.2
    have hQ := hfin.mem_toFinset.1 Q.2
    have := (comap_eq_comap_iff hK hF hP.1 hQ.1).1 (congrArg Subtype.val hPQ)
    rw [(hst.2.2.2 P.1 hP).1, or_self] at this
    exact Subtype.ext this.symm
  rw [lamG, lamMax, finprod_mem_eq_finite_toFinset_prod _ hfin,
    tprod_eq_prod (s := hfin.toFinset.attach.image g), Finset.prod_image fun _ _ _ _ e => hg e,
    ← Finset.prod_attach hfin.toFinset]
  · exact Finset.prod_congr rfl fun P _ => localMassFactor_eq_of_mem_badPrimes hK hF hs hd hM (hfin.mem_toFinset.1 P.2)
  · intro 𝔭 h𝔭
    obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
    have hlat := hM.1.1
    apply localMassFactor_of_valuation_eq_zero hK hF hs hd hlat hM.1.2 𝔭.2
    rw [← hP𝔭]
    refine (isUnimodularAt_iff_vd hK hF hs hd hlat hM.1.2 hP).1 (by_contra fun hb => h𝔭 ?_)
    exact Finset.mem_image.2 ⟨⟨P, hfin.mem_toFinset.2 ⟨hP, hb⟩⟩, Finset.mem_attach _ _,
      Subtype.ext hP𝔭⟩

theorem main : MaxMass := by
  intro K _ _ _ hK n hn
  obtain ⟨F, _, _, _, hF⟩ := exists_fixF K hK
  obtain ⟨c₁, -, hall⟩ := massConst_all binary_hermitian_represents liStat hK hF
  refine ⟨c₁ * ∏ j ∈ Finset.Icc 2 n, massRatioRightSide K j, fun V _ _ _ _ _ h hs hp hr M hM => ?_⟩
  have hd : IsTotPosDef h := fun x hx φ => hp φ x hx
  rw [hall n hn V h M hs hd hr hM.1.1 hM.1.2, lamG_eq_lamMax hK hF hs hd hM]

end GlobalTheory.Mass.MaxFormula
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.countedVector_isCuspForm : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) := by
  first | exact @GlobalTheory.RowCusp.row_isCuspFn | exact GlobalTheory.RowCusp.row_isCuspFn | (intros; apply GlobalTheory.RowCusp.row_isCuspFn <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.hermitian_spaces_same_signature_isometric : SameKindIsometric := by
  first | exact @GlobalTheory.FlagMeas.sameKindIsometric | exact GlobalTheory.FlagMeas.sameKindIsometric | (intros; apply GlobalTheory.FlagMeas.sameKindIsometric <;> assumption)
end
