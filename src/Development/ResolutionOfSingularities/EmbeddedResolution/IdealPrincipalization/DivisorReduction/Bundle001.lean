module

import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IsomorphismTransport
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem isPushforwardBlowupSeq_of_ofSequenceOfBlowups {S X : Scheme.{u}} (ι : S ⟶ X) [IsClosedImmersion ι]
    (B : SequenceOfBlowups S) (B' : SequenceOfBlowups X)
    (h : IsPushforwardBlowupSeq ι (BlowupSequenceData.ofSequenceOfBlowups B).toSequenceOfBlowups B') : IsPushforwardBlowupSeq ι B B' := by
  unfold IsPushforwardBlowupSeq at h ⊢
  simp only [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism] at h
  exact h

private theorem heq_toSequenceOfBlowups_of_eq (L : PrincipalizationAssignment.{u}) {A B : MarkedIdealWithBoundary.{u}} (h : A = B) :
    HEq ((L A).toSequenceOfBlowups) ((L B).toSequenceOfBlowups) := by
  subst h
  rfl

theorem isPushforwardSequenceOfBlowups_of_length_eq_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hlenZero : BS.length = 0) (hB : B.length = 0) :
    IsPushforwardBlowupSeq ι BS B := by
  apply FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_length_eq_zero <;> assumption

theorem isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups)
    {Y : Scheme.{u}} (ι : T.scheme ⟶ Y) [IsClosedImmersion ι] (B : SequenceOfBlowups Y)
    (h : IsPushforwardBlowupSeq ι (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.toSequenceOfBlowups B) :
    IsPushforwardBlowupSeq ι s.toSequenceOfBlowups B := by
  rw [MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence] at h
  exact isPushforwardBlowupSeq_of_ofSequenceOfBlowups ι s.toSequenceOfBlowups B h

namespace DivisorReduction

theorem comap_lowerIdealWithoutBlowup_of_eq_imageIdealSheaf (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    (DivisorReduction.lowerIdealWithoutBlowup T).comap (T.boundary.get ⟨j, hj⟩).subschemeι = J := by
  unfold DivisorReduction.lowerIdealWithoutBlowup
  rw [Scheme.IdealSheafData.comap_id, him]
  exact Blowup.comap_map_of_isClosedImmersion _ J

theorem map_comap_take_eraseIdx_lowerBoundaryWithoutBlowup (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
        (List.take (T.boundary.length - 1) ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j)) =
      List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) (T.boundary.eraseIdx j) := by
  unfold DivisorReduction.lowerBoundaryWithoutBlowup
  have h1 : List.map (fun D : T.scheme.IdealSheafData => D.comap (𝟙 T.scheme)) T.boundary
      = T.boundary := by
    simp [Scheme.IdealSheafData.comap_id]
  rw [h1]
  have hlen : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  rw [← hlen, List.take_length]

theorem restrictToDivisor_eq_withSchemeIdealBoundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    DivisorReduction.restrictToDivisor T j hj =
      T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j)) := by
  have h1 := DivisorReduction.comap_lowerIdealWithoutBlowup_of_eq_imageIdealSheaf T j hj J him
  have h2 := DivisorReduction.map_comap_take_eraseIdx_lowerBoundaryWithoutBlowup T j hj
  unfold DivisorReduction.restrictToDivisor DivisorReduction.restrictToBoundaryDivisor MarkedIdealWithBoundary.withSchemeIdealBoundary
  rw [h1, h2]

end DivisorReduction

theorem isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : ∀ hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap, T.IsBalanced hft)
    (hj : j < T.boundary.length) (hm : T.mult = 1)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (hVJ : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).IsAdmissible)
    (hdimJ : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).krullDimSucc < T.krullDimSucc)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    IsPushforwardBlowupSeq (T.boundary.get ⟨j, hj⟩).subschemeι
      (L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j)))).toSequenceOfBlowups
      ((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups := by
  have : AlgebraicGeometry.IsNoetherian T.scheme :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · have hsub : (↑T.ideal.support : Set ↥T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult := by
      intro x hx
      rw [hm]
      exact (mem_orderAtLeastLocus_one_iff T.ideal x).mpr hx
    rw [hcs] at hsub
    have hsupp : (↑T.ideal.support : Set ↥T.scheme) = ∅ := Set.subset_empty_iff.mp hsub
    have hItop : T.ideal = ⊤ :=
      (Scheme.IdealSheafData.eq_top_iff_support_eq_empty T.ideal).mpr hsupp
    have hJtop : J = ⊤ := by
      have h2 : (imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J).comap
          (T.boundary.get ⟨j, hj⟩).subschemeι = J :=
        Blowup.comap_map_of_isClosedImmersion (T.boundary.get ⟨j, hj⟩).subschemeι J
      rw [← him, hItop] at h2
      rw [← h2]
      simp
    have h0 : orderAtLeastLocus (⊤ : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData) 1
        = (∅ : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := by
      simp [orderAtLeastLocus_top_eq_empty]
    have hcsJ : orderAtLeastLocus
        (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).ideal
        (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).mult =
        (∅ : Set ↥(T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).scheme) := by
      rw [MarkedIdealWithBoundary.withSchemeIdealBoundary_ideal, MarkedIdealWithBoundary.withSchemeIdealBoundary_mult, hJtop, hm]
      exact h0
    refine isPushforwardSequenceOfBlowups_of_length_eq_zero _ _ _ ?_ ?_
    · exact hL.trivial_of_coSupport_empty _ hVJ (lt_of_lt_of_le hdimJ hdim) hcsJ
    · exact divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO
        (hD hV.locallyOfFiniteType) hj hcs
  · have hpretop : DivisorReduction.containedComponentsIdeal T j hj = ⊤ :=
      hfacts.preIdeal_eq_top_of_imageIdeal T hV j hj J hm hVJ him
    rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO
        (hD hV.locallyOfFiniteType) hcs with
      ⟨-, hpr, hmk0, hstep⟩ | ⟨hne, -⟩
    · have hT : DivisorReduction.restrictToDivisor T j hj =
          T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)) :=
        DivisorReduction.restrictToDivisor_eq_withSchemeIdealBoundary T j hj J him
      have hHeq : HEq ((L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups)
          ((L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)))).toSequenceOfBlowups) := heq_toSequenceOfBlowups_of_eq L hT
      have hE : (L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups =
          (L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)))).toSequenceOfBlowups := eq_of_heq hHeq
      rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq, hstep hmk0, ← hE,
        BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
      have inst : IsClosedImmersion (T.boundary.get ⟨j, hj⟩).subschemeι := inferInstance
      exact @isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence (DivisorReduction.restrictToDivisor T j hj)
        (L (DivisorReduction.restrictToDivisor T j hj)) T.scheme
        (T.boundary.get ⟨j, hj⟩).subschemeι inst _
        (isPushforwardBlowupSeq_ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr)
    · exact absurd hpretop hne

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem iSup_le_zero_nat {Y : Scheme.{u}} (G : ℕ → Y.IdealSheafData) :
    (⨆ l, ⨆ _ : l ≤ 0, G l) = G 0 := by
  simp only [Nat.le_zero]
  exact iSup_iSup_eq_left

namespace BlowupSequenceData

theorem controlledTransform_congr {X : Scheme.{u}} (d : BlowupSequenceData X) (I I' : X.IdealSheafData)
    (h : I.comap (d.projectionToBase 0) = I'.comap (d.projectionToBase 0)) (m t : ℕ) :
    d.controlledTransform I m t = d.controlledTransform I' m t := by
  induction t with
  | zero =>
    rw [controlledTransform_zero, controlledTransform_zero, ← d.projectionToBase_zero]
    exact h
  | succ t ih =>
    rw [controlledTransform_succ, controlledTransform_succ, ih]

theorem boundary_congr {X : Scheme.{u}} (d : BlowupSequenceData X) (E E' : List X.IdealSheafData)
    (h : List.map (fun D => D.comap (d.projectionToBase 0)) E = List.map (fun D => D.comap (d.projectionToBase 0)) E')
    (t : ℕ) :
    d.boundaryFrom E t = d.boundaryFrom E' t := by
  induction t with
  | zero =>
    rw [boundary_zero, boundary_zero, ← d.projectionToBase_zero]
    exact h
  | succ t ih =>
    rw [boundary_succ, boundary_succ, ih]

theorem pow_controlledTransform_le_pow_controlledTransform_succ {X : Scheme.{u}} (d : BlowupSequenceData X)
    (K A : X.IdealSheafData) (m l t : ℕ)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (d.map t) (d.center t)))
    (hK : ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ (m - l) * B =
        (d.controlledTransform K (m - l) t).comap (d.map t))
    (hA : ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ m * B = (d.controlledTransform A m t).comap (d.map t))
    (hle : d.controlledTransform K (m - l) t ^ m ≤ d.controlledTransform A m t ^ (m - l)) :
    d.controlledTransform K (m - l) (t + 1) ^ m ≤ d.controlledTransform A m (t + 1) ^ (m - l) := by
  have hpowMul := d.pow_exceptionalIdeal_mul_controlledTransform_succ K (m - l) t hK
  have hAs := d.pow_exceptionalIdeal_mul_controlledTransform_succ A m t hA
  have hcomap : (d.controlledTransform K (m - l) t ^ m).comap (d.map t) ≤
      (d.controlledTransform A m t ^ (m - l)).comap (d.map t) :=
    Scheme.IdealSheafData.comap_mono _ hle
  rw [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow, ← hpowMul, ← hAs,
    mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (m - l) m] at hcomap
  exact (hcart.pow (m * (m - l))).le_of_mul_le_mul hcomap

end BlowupSequenceData

theorem orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le (k : Type u) [Field k] [CharZero k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (K A : Y.IdealSheafData) (l m : ℕ) (hlm : l < m) (h : K ^ m ≤ A ^ (m - l)) :
    orderAtLeastLocus A m ⊆ orderAtLeastLocus K (m - l) := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx
  rw [mem_orderAtLeastLocus_iff]
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hml : 1 ≤ m - l := by omega
  have h1 : orderAt (A ^ (m - l)) x ≤ orderAt (K ^ m) x := orderAt_le_of_le h x
  rw [orderAt_pow k p A (m - l) x, orderAt_pow k p K m x] at h1
  have h2 : ((m - l : ℕ) : ℕ∞) * ((m : ℕ) : ℕ∞) ≤ ((m - l : ℕ) : ℕ∞) * orderAt A x :=
    (natCast_mul_le_mul_iff hml m (orderAt A x)).mpr hx
  have h3 : ((m : ℕ) : ℕ∞) * ((m - l : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) * orderAt K x := by
    calc ((m : ℕ) : ℕ∞) * ((m - l : ℕ) : ℕ∞)
        = ((m - l : ℕ) : ℕ∞) * ((m : ℕ) : ℕ∞) := mul_comm _ _
      _ ≤ ((m - l : ℕ) : ℕ∞) * orderAt A x := h2
      _ ≤ ((m : ℕ) : ℕ∞) * orderAt K x := h1
  exact (natCast_mul_le_mul_iff hm (m - l) (orderAt K x)).mp h3

theorem comap_iSup_le_nat {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (n : ℕ) (G : ℕ → Y.IdealSheafData) :
    (⨆ l ≤ n, G l).comap f = ⨆ l ≤ n, (G l).comap f := by
  induction n with
  | zero => rw [iSup_le_zero_nat, iSup_le_zero_nat]
  | succ n ih =>
    rw [Nat.iSup_le_succ, Nat.iSup_le_succ, Scheme.IdealSheafData.comap_sup, ih]

theorem mem_support_iSup_le_nat {Y : Scheme.{u}} (n : ℕ) (G : ℕ → Y.IdealSheafData) (y : Y)
    (h : ∀ l ≤ n, y ∈ (G l).support) : y ∈ (⨆ l ≤ n, G l).support := by
  revert h
  induction n with
  | zero =>
    intro h
    rw [iSup_le_zero_nat]
    exact h 0 le_rfl
  | succ n ih =>
    intro h
    rw [Nat.iSup_le_succ, mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_sup]
    refine sup_le ?_ ?_
    · exact (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp
        (ih fun l hl => h l (hl.trans (Nat.le_succ n)))
    · exact (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp (h (n + 1) le_rfl)

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

noncomputable abbrev divisorEmbedding : (restrictToBoundaryDivisor T j hj I₀ E₀).scheme ⟶ T.scheme :=
  (T.boundary.get ⟨j, hj⟩).subschemeι

noncomputable abbrev ambientBlowupSeqStructureMorphism (t : ℕ) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t ⟶ Spec (CommRingCat.of T.base) :=
  (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap

noncomputable abbrev ambientDerivIdeal [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (l t : ℕ) : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t).IdealSheafData :=
  (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform
    (derivIdealSheafIterate T.base T.structMap l I₀) (T.mult - l) t

theorem embeddingIntoAmbient_comp_projectionToBase (t : ℕ) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
      s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀ := by
  induction t with
  | zero =>
    have h0 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero = Iso.refl T.scheme :=
      ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
    rw [BlowupSequenceData.projectionToBase_zero, h0, embeddingIntoAmbient_zero, MarkedSequenceOfBlowups.projectionToBase_zero, Iso.refl_hom]
    exact Category.comp_id _
  | succ t ih =>
    have hmap := embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t
    have hstruct : s.transitionMapSucc t ≫ s.projectionToBase t = s.projectionToBase (t + 1) := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
      exact SequenceOfBlowups.transitionMap_comp_projectionToBase s.toSequenceOfBlowups (Nat.le_succ t)
    have e1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase (t + 1) =
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) :=
      congrArg (fun f => embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫ f)
        (BlowupSequenceData.projectionToBase_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) t)
    have e2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) =
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t :=
      (Category.assoc _ _ _).symm
    have e3 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
        (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t :=
      congrArg (fun f => f ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) hmap
    have e4 : (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
        s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) :=
      Category.assoc _ _ _
    have e5 : s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) =
        s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) :=
      congrArg (fun f => s.transitionMapSucc t ≫ f) ih
    have e6 : s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) =
        (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀ :=
      (Category.assoc _ _ _).symm
    have e7 : (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀ =
        s.projectionToBase (t + 1) ≫ divisorEmbedding T j hj I₀ E₀ :=
      congrArg (fun f => f ≫ divisorEmbedding T j hj I₀ E₀) hstruct
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))

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

private theorem exists_lift_pullback_subschemeι_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    ∃ ψ : Limits.pullback h D.subschemeι ⟶ D'.subscheme,
      ψ ≫ D'.subschemeι = Limits.pullback.fst h D.subschemeι := by
  have hle : D'.subschemeι.ker ≤ (Limits.pullback.fst h D.subschemeι).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hD]
    exact le_rfl
  exact ⟨AlgebraicGeometry.IsClosedImmersion.lift D'.subschemeι
      (Limits.pullback.fst h D.subschemeι) hle, by simp⟩

theorem isPullback_subschemeMapOfComap (X Y : Scheme.{u}) (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    IsPullback (subschemeMapOfComap h D D' hD) D'.subschemeι D.subschemeι h := by
  have hcomm : subschemeMapOfComap h D D' hD ≫ D.subschemeι = D'.subschemeι ≫ h :=
    subschemeMapOfComap_comp h D D' hD
  obtain ⟨ψ, hψ⟩ := exists_lift_pullback_subschemeι_comap h D D' hD
  have h1 : Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm ≫ ψ = 𝟙 _ := by
    rw [← cancel_mono D'.subschemeι, Category.assoc, hψ, Category.id_comp]
    exact Limits.pullback.lift_fst _ _ _
  have h2 : ψ ≫ Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm = 𝟙 _ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
      exact hψ
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.id_comp,
        ← cancel_mono D.subschemeι, Category.assoc, hcomm, ← Category.assoc, hψ]
      exact Limits.pullback.condition
  refine (IsPullback.of_iso_pullback ⟨hcomm.symm⟩
    { hom := Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm
      inv := ψ
      hom_inv_id := h1
      inv_hom_id := h2 } ?_ ?_).flip
  · exact Limits.pullback.lift_fst _ _ _
  · exact Limits.pullback.lift_snd _ _ _

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end
