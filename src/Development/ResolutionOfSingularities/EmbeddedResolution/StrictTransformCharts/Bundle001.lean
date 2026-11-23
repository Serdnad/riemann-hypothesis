module

public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.Bundle001
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
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
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart

@[expose] public section

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private def natSuccAbove (j i : ℕ) : ℕ := if i < j then i else i + 1

private theorem natSuccAbove_ne (j i : ℕ) : natSuccAbove j i ≠ j := by
  unfold natSuccAbove
  split_ifs with h <;> omega

private theorem natSuccAbove_inj (j i i' : ℕ) (h : natSuccAbove j i = natSuccAbove j i') : i = i' := by
  unfold natSuccAbove at h
  split_ifs at h <;> omega

private theorem getElem_eraseIdx_natSuccAbove {α : Type u} (l : List α) (j i : ℕ)
    (hi : i < (l.eraseIdx j).length) (hs : natSuccAbove j i < l.length) :
    (l.eraseIdx j)[i]'hi = l[natSuccAbove j i]'hs := by
  unfold natSuccAbove at hs ⊢
  rw [List.getElem_eraseIdx]
  split <;> simp [*]

private def complOrderEmbPreimage (m : ℕ) (S : Finset (Fin m)) (s : Fin m) : Option (Fin (m - S.card)) :=
  if hs : s ∈ S then none else some (Classical.choose (exists_complOrderEmb_eq m S hs))

private theorem mem_of_complOrderEmbPreimage_eq_none (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (h : complOrderEmbPreimage m S s = none) : s ∈ S := by
  by_contra hs
  unfold complOrderEmbPreimage at h
  rw [dite_eq_right hs] at h
  simp at h

private theorem complOrderEmb_of_complOrderEmbPreimage_eq_some (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (u : Fin (m - S.card)) (h : complOrderEmbPreimage m S s = some u) : complOrderEmb m S u = s := by
  by_cases hs : s ∈ S
  · exfalso
    unfold complOrderEmbPreimage at h
    rw [dite_eq_left hs] at h
    simp at h
  · unfold complOrderEmbPreimage at h
    rw [dite_eq_right hs] at h
    have hu : Classical.choose (exists_complOrderEmb_eq m S hs) = u := Option.some.inj h
    rw [← hu]
    exact Classical.choose_spec (exists_complOrderEmb_eq m S hs)

private def transportSuccAboveToCompl {m : ℕ} (S : Finset (Fin m)) (j : ℕ) (a : ℕ → Option (Fin m))
    (i : ℕ) : Option (Fin (m - S.card)) :=
  (a (natSuccAbove j i)).bind (complOrderEmbPreimage m S)

private theorem transportSuccAboveToCompl_eq_some {m : ℕ} (S : Finset (Fin m)) (j : ℕ)
    (a : ℕ → Option (Fin m)) (i : ℕ) (u : Fin (m - S.card))
    (h : transportSuccAboveToCompl S j a i = some u) : a (natSuccAbove j i) = some (complOrderEmb m S u) := by
  rcases hs : a (natSuccAbove j i) with _ | s
  · exfalso
    unfold transportSuccAboveToCompl at h
    rw [hs] at h
    simp at h
  · have h' : complOrderEmbPreimage m S s = some u := by
      unfold transportSuccAboveToCompl at h
      rw [hs] at h
      exact h
    rw [complOrderEmb_of_complOrderEmbPreimage_eq_some m S s u h']

private theorem transportSuccAboveToCompl_eq_none {m : ℕ} (S : Finset (Fin m)) (j : ℕ)
    (a : ℕ → Option (Fin m)) (i : ℕ) (h : transportSuccAboveToCompl S j a i = none) :
    a (natSuccAbove j i) = none ∨ ∃ s, a (natSuccAbove j i) = some s ∧ s ∈ S := by
  rcases hs : a (natSuccAbove j i) with _ | s
  · exact Or.inl rfl
  · refine Or.inr ⟨s, rfl, ?_⟩
    have h' : complOrderEmbPreimage m S s = none := by
      unfold transportSuccAboveToCompl at h
      rw [hs] at h
      exact h
    exact mem_of_complOrderEmbPreimage_eq_none m S s h'

theorem inStrictNormalCrossingPosition_of_forall_etaleChart {Y : Scheme.{u}} {k : Type u} [Field k]
    (q : Y ⟶ Spec (CommRingCat.of k)) (L : List Y.IdealSheafData)
    (h : ∀ x : ↥Y, ∃ (U : Y.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart q U m)
      (a : ℕ → Option (Fin m)),
      (∀ i < L.length, ∀ i' < L.length, ∀ t : Fin m, a i = some t → a i' = some t → i = i') ∧
      (∀ (i : ℕ) (hi : i < L.length), a i = none → restrictIdeal L[i] U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < L.length) (t : Fin m),
        a i = some t → restrictIdeal L[i] U = c.coordIdeal {t})) :
    InStrictNormalCrossingPosition q L := by
  refine (inStrictNormalCrossingPosition_iff q L).mpr ⟨?_, fun x => inStrictNormalCrossingPositionAt_of_exists_etaleChart (h x)⟩
  intro D hD
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hD
  refine isSmoothDivisor_of_locally_coordIdeal _ ?_
  intro x
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := h x
  refine ⟨U, hxU, m, c, ?_⟩
  rcases hai : a i with _ | t
  · exact Or.inl (h2 i hi hai)
  · exact Or.inr ⟨t, h3 i hi t hai⟩

theorem exists_etaleChart_comap_subschemeι_eraseIdx {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (j : ℕ) (hj : j < E.length) (z : ↥((E[j]'hj).subscheme)) :
    ∃ (U : ((E[j]'hj).subscheme).Opens) (_ : z ∈ U) (m : ℕ)
      (c : EtaleChart ((E[j]'hj).subschemeι ≫ p) U m) (a : ℕ → Option (Fin m)),
      (∀ i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length,
        ∀ i' < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length,
        ∀ t : Fin m, a i = some t → a i' = some t → i = i') ∧
      (∀ (i : ℕ) (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length),
        a i = none →
          restrictIdeal (((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]) U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length)
        (t : Fin m), a i = some t →
          restrictIdeal (((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]) U =
            c.coordIdeal {t}) := by
  classical
  obtain ⟨-, hpos⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
  have hx : (E[j]'hj).subschemeι.base z ∈ (E[j]'hj).support := by
    have hmem : (E[j]'hj).subschemeι.base z ∈ Set.range (E[j]'hj).subschemeι.base :=
      Set.mem_range_self z
    simpa using hmem
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := (hpos ((E[j]'hj).subschemeι.base z)).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU
  have hV : IsAffineOpen V := hVB
  rcases haj : a j with _ | t
  · refine absurd hx ?_
    refine AlgebraicGeometry.Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top _ ?_ hxU
    rw [← restrictIdeal_eq_comap_ι]
    exact h2 j hj haj
  · have hzmem : z ∈ (E[j]'hj).subschemeι ⁻¹ᵁ V := hxV
    have h2V : ∀ (i : ℕ) (hi : i < E.length), a i = none → restrictIdeal (E[i]'hi) V = ⊤ :=
      fun i hi hn => restrictIdeal_eq_top_of_le _ hVU (h2 i hi hn)
    have h3V : ∀ (i : ℕ) (hi : i < E.length) (s : Fin m), a i = some s →
        restrictIdeal (E[i]'hi) V = (c.restrict hVU).coordIdeal {s} :=
      fun i hi s hsm => restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (E[i]'hi) {s} (h3 i hi s hsm)
    have hZV : restrictIdeal (E[j]'hj) V = (c.restrict hVU).coordIdeal {t} := h3V j hj t haj
    have hlen : ∀ i, i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length →
        natSuccAbove j i < E.length := by
      intro i hi
      rw [List.length_map] at hi
      have h0 := List.length_eraseIdx_add_one hj
      unfold natSuccAbove
      split_ifs with hc <;> omega
    have helem : ∀ (i : ℕ)
        (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length),
        ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]'hi =
          (E[natSuccAbove j i]'(hlen i hi)).comap (E[j]'hj).subschemeι := by
      intro i hi
      have hi' : i < (E.eraseIdx j).length := by
        rw [List.length_map] at hi
        exact hi
      have he : (E.eraseIdx j)[i]'hi' = E[natSuccAbove j i]'(hlen i hi) :=
        getElem_eraseIdx_natSuccAbove E j i hi' (hlen i hi)
      rw [List.getElem_map]
      exact congrArg (fun D => D.comap (E[j]'hj).subschemeι) he
    refine ⟨(E[j]'hj).subschemeι ⁻¹ᵁ V, hzmem, m - ({t} : Finset (Fin m)).card,
      (c.restrict hVU).restrictToSubscheme hV (E[j]'hj) {t} hZV,
      transportSuccAboveToCompl {t} j a, ?_, ?_, ?_⟩
    · intro i hi i' hi' u hu hu'
      exact natSuccAbove_inj j i i'
        (h1 (natSuccAbove j i) (hlen i hi) (natSuccAbove j i') (hlen i' hi')
          (complOrderEmb m {t} u) (transportSuccAboveToCompl_eq_some {t} j a i u hu)
          (transportSuccAboveToCompl_eq_some {t} j a i' u hu'))
    · intro i hi hn
      rw [helem i hi]
      rcases transportSuccAboveToCompl_eq_none {t} j a i hn with hnone | ⟨s, hsome, hsmem⟩
      · exact restrictIdeal_comap_subschemeι_eq_top (E[j]'hj) V _
          (h2V (natSuccAbove j i) (hlen i hi) hnone)
      · exfalso
        have h0 : a (natSuccAbove j i) = some t := by
          rw [hsome, Finset.mem_singleton.mp hsmem]
        exact natSuccAbove_ne j i (h1 (natSuccAbove j i) (hlen i hi) j hj t h0 haj)
    · intro i hi u hu
      rw [helem i hi]
      exact (c.restrict hVU).restrictToSubscheme_coordIdeal_singleton hV (E[j]'hj) {t} hZV u
        (E[natSuccAbove j i]'(hlen i hi))
        (h3V (natSuccAbove j i) (hlen i hi) (complOrderEmb m {t} u)
          (transportSuccAboveToCompl_eq_some {t} j a i u hu))

theorem inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (j : ℕ) (hj : j < E.length) :
    InStrictNormalCrossingPosition ((E[j]'hj).subschemeι ≫ p)
      ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι) :=
  inStrictNormalCrossingPosition_of_forall_etaleChart ((E[j]'hj).subschemeι ≫ p)
    ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)
    (exists_etaleChart_comap_subschemeι_eraseIdx p E hE j hj)

theorem inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx_of_eq {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (j : ℕ) (hj : j < E.length) (D : X.IdealSheafData) (hD : E[j]'hj = D) :
    InStrictNormalCrossingPosition (D.subschemeι ≫ p)
      ((E.eraseIdx j).map fun F => F.comap D.subschemeι) := by
  subst hD
  exact inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx p E hE j hj

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {Z : X.IdealSheafData}
  {E : List X.IdealSheafData}

theorem hasStrictNormalCrossingsWith_exceptionalIdeal (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    HasStrictNormalCrossingsWith (π ≫ p) (Blowup.exceptionalIdeal π Z) [] := by
  rw [hasStrictNormalCrossingsWith_iff]
  intro x hx
  rw [Blowup.exceptionalIdeal_eq_comap] at hx
  have hy : π.base x ∈ Z.support := by
    simp only [Scheme.IdealSheafData.support_comap] at hx
    exact hx
  obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hy
  have hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U := hyU
  obtain ⟨s, hs, hxs⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU
  refine ⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxs, m,
    (blowupChartOfIsBlowup π c S hπ hZU s hs).chart, fun _ => none, {s}, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · exact BlowupChart.restrictIdeal_exceptionalIdeal
      (blowupChartOfIsBlowup π c S hπ hZU s hs) Z hs hZU

theorem isSmoothDivisor_exceptionalIdeal (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    IsSmoothDivisor (π ≫ p) (Blowup.exceptionalIdeal π Z) := by
  have hsmooth : Smooth ((Blowup.exceptionalIdeal π Z).subschemeι ≫ (π ≫ p)) :=
    smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith (Blowup.exceptionalIdeal π Z) []
      (hasStrictNormalCrossingsWith_exceptionalIdeal hZ hπ)
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact hπ.1
  exact (isSmoothDivisor_iff (π ≫ p) (Blowup.exceptionalIdeal π Z)).mpr ⟨hcart, hsmooth⟩

private theorem smooth_ι_comp_of_etaleChart {Y : Scheme.{u}} {K : Type u}
    [Field K] {q : Y ⟶ Spec (CommRingCat.of K)} {V : Y.Opens} {n : ℕ} (c : EtaleChart q V n) :
    Smooth (V.ι ≫ q) := by
  have := c.isEtale
  have hsm : Smooth c.map := inferInstance
  have hsa : Smooth (affineSpaceFinToSpec K n) := affineSpaceIsSmooth K n
  rw [← c.comp_struct]
  infer_instance

theorem smooth_comp_of_isBlowupAlongIdealSheaf [Smooth p] (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    Smooth (π ≫ p) := by
  have key : ∀ x : ↥X₁, ∃ V : X₁.Opens, x ∈ V ∧ Smooth (V.ι ≫ (π ≫ p)) := by
    intro x
    by_cases hxs : π.base x ∈ Z.support
    · obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hxs
      have hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U := hyU
      obtain ⟨s, hs, hxB⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU
      exact ⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxB,
        smooth_ι_comp_of_etaleChart (blowupChartOfIsBlowup π c S hπ hZU s hs).chart⟩
    · refine ⟨π ⁻¹ᵁ Z.support.compl, hxs, ?_⟩
      have : IsIso (AlgebraicGeometry.morphismRestrict π Z.support.compl) :=
        Blowup.blowupIsIsoOffCenter X X₁ π Z hπ
      have h1 : (π ⁻¹ᵁ Z.support.compl).ι ≫ (π ≫ p) =
          AlgebraicGeometry.morphismRestrict π Z.support.compl ≫
            (Scheme.Opens.ι Z.support.compl ≫ p) := by
        rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      rw [h1]
      infer_instance
  choose U hU hsm using key
  have hUtop : iSup U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  exact smooth_of_iSup_eq_top (π ≫ p) U hUtop hsm

end FunctorialResolution.EmbeddedResolution
end
