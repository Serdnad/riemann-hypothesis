module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivBalancedOrderLocus
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Bundle001
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.BlowupDataOfSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.Bundle001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.SetTheory.ZFC.PSet
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
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Mathlib.Tactic.TypeStar

@[expose] public section

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReductionEmptyOrderLocus

private theorem blowupMorphism_mem_orderAtLeastLocus {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) (hm : 1 ≤ m)
    (hsm : ∀ i, i ≤ s.length → AlgebraicGeometry.Smooth (MarkedSequenceOfBlowups.projectionToSpec s i))
    (hno : ∀ i, i ≤ s.length → AlgebraicGeometry.IsNoetherian (s.schemeAt i))
    (i : ℕ) (hi : i < s.length) (z : s.schemeAt (i + 1))
    (hz : z ∈ orderAtLeastLocus (s.ideal (i + 1)) m) :
    (s.transitionMapSucc i) z ∈ orderAtLeastLocus (s.ideal i) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  have := hsm i hi.le
  have := hno (i + 1) hi
  have hsnc : HasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec s i) (s.center i) (s.boundary i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc i hi
  have hord : (↑(s.center i).support : Set (s.schemeAt i)) ⊆ orderAtLeastLocus (s.ideal i) n :=
    (s.center_order i hi).trans
      (orderAtLeastLocus_subset_of_le (s.ideal i) (Nat.le_succ n))
  have hI : s.ideal i ≤ s.center i ^ n :=
    le_pow_of_hasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec s i) (s.center i) (s.ideal i)
      (s.boundary i) hsnc n hord
  have hpb : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have key := orderAtLeastLocus_controlledTransform_subset_preimage k
      (MarkedSequenceOfBlowups.projectionToSpec s i) (s.transitionMapSucc i) (s.center i) (s.boundary i) hsnc hpb
      (s.ideal i) n hI
  have hmul : Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) ^ n *
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1))
      = (s.ideal i).comap (s.transitionMapSucc i) := by
    rw [← mul_assoc, ← pow_succ]
    exact s.ideal_succ i hi
  have heq := eq_controlledTransform_of_mul_eq_comap (s.transitionMapSucc i) (s.center i) (s.ideal i) n hpb hI
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1)) hmul
  have hz' : z ∈ orderAtLeastLocus
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1)) (n + 1) := by
    rw [mem_orderAtLeastLocus_iff] at hz ⊢
    exact hz.trans ((self_le_add_left _ _).trans
      (add_orderAt_le_orderAt_mul (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i))
        (s.ideal (i + 1)) z))
  rw [heq] at hz'
  exact key hz'

private theorem projectionToBase_mem_orderAtLeastLocus {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) (s : T.SequenceOfBlowups) :
    ∀ i, i ≤ s.length → ∀ z : s.schemeAt i,
      z ∈ orderAtLeastLocus (s.ideal i) T.mult → (s.projectionToBase i) z ∈ orderAtLeastLocus T.ideal T.mult := by
  have := hV.charZero
  intro i
  induction i with
  | zero =>
      intro _ z hz
      rw [markedSequenceOfBlowups_ideal_zero s, MarkedSequenceOfBlowups.projectionToBase_zero s, orderAtLeastLocus_comap_iso_hom_eq_preimage] at hz
      rw [MarkedSequenceOfBlowups.projectionToBase_zero s]
      exact hz
  | succ i ih =>
      intro hi z hz
      rw [MarkedSequenceOfBlowups.projectionToBase_succ_apply]
      refine ih (Nat.le_of_succ_le hi) _ ?_
      exact blowupMorphism_mem_orderAtLeastLocus s hV.one_le_mult
        (fun j hj => MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s j hj)
        (fun j hj => MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s j hj)
        i (Nat.lt_of_succ_le hi) z hz

theorem center_disjoint_range_of_preimage_orderAtLeastLocus_eq_empty
    {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) {Y : Scheme.{u}} (h : Y ⟶ T.scheme)
    (hempty : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) = ∅) (s : T.SequenceOfBlowups) :
    ∀ i < s.length, ∀ z : s.schemeAt i, z ∈ (s.center i).support →
      ∀ y : Y, h y ≠ (s.projectionToBase i) z := by
  intro i hi z hz y hy
  have hz' : z ∈ (↑((s.center i).support) : Set (s.schemeAt i)) := hz
  have hzc : z ∈ orderAtLeastLocus (s.ideal i) T.mult := s.center_order i hi hz'
  have himg := projectionToBase_mem_orderAtLeastLocus hV s i hi.le z hzc
  rw [← hy] at himg
  have hmem : y ∈ (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) := himg
  rw [hempty] at hmem
  simp at hmem

theorem isPullbackSequenceOfBlowups_of_preimage_orderAtLeastLocus_empty
    {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) {Y : Scheme.{u}} (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Flat h]
    (hempty : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) = ∅) (s : T.SequenceOfBlowups)
    (B' : SequenceOfBlowups Y) (hB' : B'.length = 0) :
    IsPullbackBlowupSequence h B' s.toSequenceOfBlowups := by
  have hdisj := center_disjoint_range_of_preimage_orderAtLeastLocus_eq_empty hV h hempty s
  refine (SequenceOfBlowupsPullback.ofBlowupDataOfSeq
      (SequenceOfBlowupsPullback.ofCentersMissImage h (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups)
        (by
          intro i hi z hz y
          rw [BlowupSequenceData.ofSequenceOfBlowups_projectionToBase]
          exact hdisj i hi z hz y)
        (BlowupSequenceData.ofSequenceOfBlowups B') (by exact hB'))).isPullbackSequenceOfBlowups

theorem divisorFamily_isPullbackSequenceOfBlowups_of_orderAtLeastLocus_empty
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (_hj : j < T.boundary.length)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h]
    (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (_hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
    (_hne : (orderAtLeastLocus T.ideal T.mult).Nonempty)
    (hempty : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅)
    (B' : SequenceOfBlowups Y) (hB' : B'.length = 0) :
    IsPullbackBlowupSequence h B' ((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups := by
  have := hV.charZero
  have := hV.smooth
  have hsub : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) ⊆ ∅ := by
    intro y hy
    have hy' : y ∈ orderAtLeastLocus (T.ideal.comap h) T.mult := by
      rw [orderAtLeastLocus_comap T.base T.structMap h T.ideal T.mult]
      exact hy
    have hy2 : y ∈ orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult := hy'
    rw [hempty] at hy2
    exact hy2
  exact isPullbackSequenceOfBlowups_of_preimage_orderAtLeastLocus_empty hV h (Set.subset_empty_iff.mp hsub)
    ((canonicalAlgorithmRules hres).divisorFamily L j T) B' hB'

end DivisorReductionEmptyOrderLocus

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isClopen_of_pairwise_disjoint_irreducibleComponents {S : Type*} [TopologicalSpace S]
    [NoetherianSpace S]
    (hsep : ∀ C₁ ∈ irreducibleComponents S, ∀ C₂ ∈ irreducibleComponents S,
      C₁ ≠ C₂ → Disjoint C₁ C₂)
    {K : Set S} (hK : K ∈ irreducibleComponents S) : IsClopen K := by
  have hKc : IsClosed K := isClosed_of_mem_irreducibleComponents K hK
  have hcompl : Kᶜ = ⋃₀ (irreducibleComponents S \ {K}) := by
    ext x
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩, ?_⟩
      · simp only [Set.mem_singleton_iff]
        intro h
        exact hx (by rw [← h]; exact (irreducibleComponent_property x).2.1 rfl)
      · exact (irreducibleComponent_property x).2.1 rfl
    · rintro ⟨C, ⟨hC, hCK⟩, hxC⟩ hxK
      have hne : C ≠ K := by
        intro h
        exact hCK (by simp [h])
      exact Set.disjoint_left.mp (hsep C hC K hK hne) hxC hxK
  have hfin : (irreducibleComponents S \ {K}).Finite :=
    Set.Finite.subset NoetherianSpace.finite_irreducibleComponents Set.sdiff_subset
  refine ⟨hKc, ?_⟩
  rw [← isClosed_compl_iff, hcompl, Set.sUnion_eq_biUnion]
  exact hfin.isClosed_biUnion (fun C hC => isClosed_of_mem_irreducibleComponents C hC.1)

theorem connectedComponent_subset_of_mem_irreducibleComponents {S : Type*} [TopologicalSpace S]
    [NoetherianSpace S]
    (hsep : ∀ C₁ ∈ irreducibleComponents S, ∀ C₂ ∈ irreducibleComponents S,
      C₁ ≠ C₂ → Disjoint C₁ C₂)
    {K : Set S} (hK : K ∈ irreducibleComponents S) {x : S} (hx : x ∈ K) :
    connectedComponent x ⊆ K :=
  (isClopen_of_pairwise_disjoint_irreducibleComponents hsep hK).connectedComponent_subset hx

namespace DivisorReduction

private theorem smooth_subschemeι_comp_structureMorphism (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := List.getElem_mem hj
  have hDiv : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hV.snc).1 _ hmem
  exact ((isSmoothDivisor_iff _ _).mp hDiv).2

private theorem noetherianSpace_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) :
    NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme := by
  have := hV.isNoetherian
  have : NoetherianSpace ↥T.scheme := inferInstance
  exact (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
    (T.boundary.get ⟨j, hj⟩).subschemeι).isInducing.noetherianSpace

private theorem ker_ι_comp_ne_top {X Z : Scheme.{u}} (hX : NoetherianSpace ↥X) (V : X.Opens)
    (g : X ⟶ Z) (x : ↥X) (hx : x ∈ V) :
    AlgebraicGeometry.Scheme.Hom.ker (V.ι ≫ g) ≠ ⊤ := by
  have := hX
  have : NoetherianSpace ↥V.toScheme := inferInstanceAs (NoetherianSpace ↥(V : Set ↥X))
  intro h
  have : AlgebraicGeometry.QuasiCompact (V.ι ≫ g) := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hx' : x ∈ Set.range ⇑V.ι := by simpa using hx
  obtain ⟨y, hy⟩ := hx'
  have h3 : ⇑g x ∈ ((AlgebraicGeometry.Scheme.Hom.ker (V.ι ≫ g)).support : Set ↥Z) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
    exact subset_closure ⟨y, by simp [hy]⟩
  rw [h] at h3
  simp at h3

theorem nonzeroOnComponents_comap_lowerIdealWithoutBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hBalanced : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ) (hj : j < T.boundary.length)
    (hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤) :
    NonzeroOnComponents
      ((DivisorReduction.lowerIdealWithoutBlowup T).comap (T.boundary.get ⟨j, hj⟩).subschemeι) := by
  classical
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    smooth_subschemeι_comp_structureMorphism T hV j hj
  have hNoe : NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have := hNoe
  have hbal : IsDerivBalanced T.base T.structMap T.ideal T.mult := hBalanced
  have hcs : orderAtLeastLocus T.ideal T.mult = (T.ideal.support : Set ↥T.scheme) :=
    orderAtLeastLocus_eq_support_of_isDerivBalanced T.base T.structMap T.ideal T.mult hbal hV.one_le_mult
  have hdisj : ∀ C₁ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
      C₁ ≠ C₂ → Disjoint C₁ C₂ :=
    irreducibleComponentsDisjointOfSmooth T.base (T.boundary.get ⟨j, hj⟩).subscheme
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) hsm
  have hopen := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  rw [DivisorReduction.containedComponentsIdeal_eq_ker T j hj hopen] at hZ
  have hI : DivisorReduction.lowerIdealWithoutBlowup T = T.ideal := by
    show T.ideal.comap (𝟙 T.scheme) = T.ideal
    simp
  rw [hI, nonzeroOnComponents_iff]
  intro C hC hsub
  obtain ⟨x, hxC⟩ := hC.1.nonempty
  have hCsub : C ⊆ ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult := by
    intro y hy
    have h1 : y ∈ ((T.ideal.comap (T.boundary.get ⟨j, hj⟩).subschemeι).support :
        Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := hsub hy
    rw [Set.mem_preimage, hcs]
    simpa [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] using h1
  have hxV : connectedComponent x ⊆
      ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    fun z hz => hCsub (connectedComponent_subset_of_mem_irreducibleComponents hdisj hC hxC hz)
  exact absurd hZ (ker_ι_comp_ne_top hNoe _ _ x hxV)

theorem isAdmissible_restrictToDivisor (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (_hOB : T.IsOrderBoundedByMult) (hBalanced : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ)
    (hj : j < T.boundary.length) (hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤) :
    (DivisorReduction.restrictToDivisor T j hj).IsAdmissible := by
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    smooth_subschemeι_comp_structureMorphism T hV j hj
  have := hsm
  have hlft : AlgebraicGeometry.LocallyOfFiniteType
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  have hqc : AlgebraicGeometry.QuasiCompact
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  have hsnc0 : InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      ((T.boundary.eraseIdx j).map fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) :=
    inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx T.structMap T.boundary hV.snc j hj
  have hbd : DivisorReduction.lowerBoundaryWithoutBlowup T = T.boundary := by
    show List.map (fun D => D.comap (𝟙 T.scheme)) T.boundary = T.boundary
    simp
  have hsnc : InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
        (List.take (T.boundary.length - 1) ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
    rw [hbd, List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hj))]
    exact hsnc0
  exact ⟨hV.charZero, hlft,
    nonzeroOnComponents_comap_lowerIdealWithoutBlowup T hV hBalanced j hj hZ, hV.one_le_mult, hqc, hsm, hsnc⟩

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem le_ker_comp_subschemeι {X : Scheme.{u}} (D : X.IdealSheafData) {W : Scheme.{u}}
    (g : W ⟶ D.subscheme) : D ≤ AlgebraicGeometry.Scheme.Hom.ker (g ≫ D.subschemeι) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι D).ge.trans
    (AlgebraicGeometry.Scheme.Hom.le_ker_comp g _)

abbrev boundaryComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    Set ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
  {x | connectedComponent x ⊆
    ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' FunctorialResolution.EmbeddedResolution.orderAtLeastLocus T.ideal T.mult}

abbrev boundaryComponentsInOrderLocusOpens (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    (T.boundary.get ⟨j, hj⟩).subscheme.Opens :=
  ⟨boundaryComponentsInOrderLocus T j hj, h⟩

theorem one_le_mult_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) : 1 ≤ T.mult :=
  hV.one_le_mult

theorem isSmoothDivisor_boundary_comap_isoObjZero (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (s : T.SequenceOfBlowups) :
    IsSmoothDivisor (s.projectionToSpec 0) ((T.boundary.get ⟨j, hj⟩).comap s.isoZero.hom) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := by
    simp only [List.get_eq_getElem]
    exact List.getElem_mem hj
  have hD : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).1 _ hmem
  rw [MarkedSequenceOfBlowups.projectionToSpec_zero]
  exact PrincipalizationIsoTransport.isSmoothDivisor_comap_iso T.structMap s.toSequenceOfBlowups.isoZero _ hD

theorem containedComponentsIdeal_eq_ker_of_isOpen (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (h : IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    containedComponentsIdeal T j hj =
      AlgebraicGeometry.Scheme.Hom.ker
        ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) :=
  containedComponentsIdeal_eq_ker_ι_comp_subschemeι_of_isOpen T j hj h

theorem containedComponentsIdeal_eq_top_of_not_isOpen_locus (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (h : ¬ IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    containedComponentsIdeal T j hj = ⊤ :=
  containedComponentsIdeal_eq_top_of_not_isOpen_setOf_connectedComponent T j hj h

theorem support_containedComponentsIdeal_subset_support_boundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) :
    ((containedComponentsIdeal T j hj).support : Set ↥T.scheme) ⊆
      ((T.boundary.get ⟨j, hj⟩).support : Set ↥T.scheme) := by
  by_cases h : IsOpen (boundaryComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_ker_of_isOpen T j hj h]
    exact SetLike.coe_subset_coe.mpr
      (AlgebraicGeometry.Scheme.IdealSheafData.support_antitone
        (le_ker_comp_subschemeι (T.boundary.get ⟨j, hj⟩) (boundaryComponentsInOrderLocusOpens T j hj h).ι))
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen_locus T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot]
    exact Set.empty_subset _

def PreimageSupportEqComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) : Prop :=
  ∀ h : IsOpen (boundaryComponentsInOrderLocus T j hj),
    ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
        ((AlgebraicGeometry.Scheme.Hom.ker
            ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫
              (T.boundary.get ⟨j, hj⟩).subschemeι)).support : Set ↥T.scheme) =
      boundaryComponentsInOrderLocus T j hj

theorem isOpen_preimage_support_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (hc : PreimageSupportEqComponentsInOrderLocus T j hj) :
    IsOpen (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
      ((containedComponentsIdeal T j hj).support : Set ↥T.scheme)) := by
  by_cases h : IsOpen (boundaryComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_ker_of_isOpen T j hj h, hc h]
    exact h
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen_locus T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot,
      Set.preimage_empty]
    exact isOpen_empty

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem orderAtLeastLocus_withBoundary_baseChange_eq_preimage (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (K : Type u) [Field K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData) (m : ℕ) :
    orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal m =
      (fieldBaseChangeProjection T K f) ⁻¹' orderAtLeastLocus T.ideal m := by
  haveI : CharZero T.base := hV.charZero
  haveI : CharZero K := (RingHom.charZero_iff f.injective).mp hV.charZero
  haveI : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  exact orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal m

end FunctorialResolution.EmbeddedResolution
end
