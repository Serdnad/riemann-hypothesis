module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StalkKrullDimension
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.Bundle001
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.Bundle003
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDimensionBound
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
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
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Tactic.TypeStar
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing

@[expose] public section

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem mem_irreducibleComponents_iff_isIrreducible_and_maximal {α : Type*}
    [TopologicalSpace α] (s : Set α) :
    s ∈ irreducibleComponents α ↔
      IsIrreducible s ∧ ∀ t : Set α, IsIrreducible t → s ⊆ t → t ⊆ s :=
  ⟨fun h => ⟨h.1, fun _ ht hst => h.2 ht hst⟩, fun h => ⟨h.1, fun t ht hst => h.2 t ht hst⟩⟩

private theorem maximal_irreducible_subset_range_iff {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : Topology.IsClosedEmbedding f) {S : Set β}
    (hr : Set.range f = S) (C : Set β) :
    (IsIrreducible C ∧ C ⊆ S ∧ ∀ C' : Set β, IsIrreducible C' → C ⊆ C' → C' ⊆ S → C' = C)
      ↔ ∃ D ∈ irreducibleComponents α, f '' D = C := by
  constructor
  · rintro ⟨hirr, hsub, hmax⟩
    have hCr : C ⊆ Set.range f := by rw [hr]; exact hsub
    have himg : f '' (f ⁻¹' C) = C := Set.image_preimage_eq_of_subset hCr
    refine ⟨f ⁻¹' C, (mem_irreducibleComponents_iff_isIrreducible_and_maximal _).mpr ⟨?_, ?_⟩, himg⟩
    · exact isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hirr hCr
    · intro t ht hDt x hx
      have himgt : IsIrreducible (f '' t) := ht.image f hf.continuous.continuousOn
      have hCt : C ⊆ f '' t := by
        rw [← himg]
        exact Set.image_mono hDt
      have htS : f '' t ⊆ S := by
        rw [← hr]
        exact Set.image_subset_range _ _
      have heq : f '' t = C := hmax _ himgt hCt htS
      have hmem : f x ∈ C := by
        rw [← heq]
        exact ⟨x, hx, rfl⟩
      exact hmem
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨hDirr, hDmax⟩ := (mem_irreducibleComponents_iff_isIrreducible_and_maximal _).mp hD
    refine ⟨hDirr.image f hf.continuous.continuousOn, ?_, ?_⟩
    · rw [← hr]
      exact Set.image_subset_range _ _
    · intro C' hC' hsub' hS'
      have hC'r : C' ⊆ Set.range f := by rw [hr]; exact hS'
      have hirr' : IsIrreducible (f ⁻¹' C') :=
        isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hC' hC'r
      have hDD : D ⊆ f ⁻¹' C' := fun x hx => hsub' ⟨x, hx, rfl⟩
      have h1 : f ⁻¹' C' ⊆ D := hDmax _ hirr' hDD
      have h2 : f '' (f ⁻¹' C') = C' := Set.image_preimage_eq_of_subset hC'r
      apply Set.Subset.antisymm
      · rw [← h2]
        exact Set.image_mono h1
      · exact hsub'

theorem mem_intersectionComponents_iff_exists_irreducibleComponent {Y : Scheme.{u}}
    (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) (C : Set ↥Y) :
    C ∈ intersectionComponents L J ↔
      ∃ D ∈ irreducibleComponents ↥(intersectionIdeal L J).subscheme,
        ⇑(intersectionIdeal L J).subschemeι '' D = C := by
  have hemb : Topology.IsClosedEmbedding ⇑(intersectionIdeal L J).subschemeι :=
    Scheme.Hom.isClosedEmbedding (intersectionIdeal L J).subschemeι
  have hrange : Set.range ⇑(intersectionIdeal L J).subschemeι
      = (↑(intersectionIdeal L J).support : Set ↥Y) :=
    Scheme.IdealSheafData.range_subschemeι _
  exact maximal_irreducible_subset_range_iff hemb hrange C

theorem isClosed_of_mem_intersectionComponents {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (C : Set ↥Y) (hC : C ∈ intersectionComponents L J) : IsClosed C := by
  obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent L J C).mp hC
  exact (Scheme.Hom.isClosedEmbedding (intersectionIdeal L J).subschemeι).isClosedMap _
    (isClosed_of_mem_irreducibleComponents _ hD)

theorem intersectionComponents_finite (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) : (intersectionComponents T.boundary J).Finite := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have h : intersectionComponents T.boundary J =
      (fun D => ⇑(intersectionIdeal T.boundary J).subschemeι '' D) ''
        irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme := by
    ext C
    rw [mem_intersectionComponents_iff_exists_irreducibleComponent]
    exact Iff.rfl
  rw [h]
  exact Set.Finite.image _ (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ..)

private theorem irreducibleComponents_eq_of_inter_nonempty_of_smooth (T : MarkedIdealWithBoundary.{u})
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap)) :
    ∀ C₁ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
        (C₁ ∩ C₂).Nonempty → C₁ = C₂ := by
  have := hsm
  rintro C₁ h₁ C₂ h₂ ⟨x, hx₁, hx₂⟩
  exact irreducibleComponents_eq_of_stalk_isDomain _
    (fun z => isDomain_stalk_of_smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap) z)
    h₁ h₂ hx₁ hx₂

theorem intersectionComponents_disjoint_of_smooth (T : MarkedIdealWithBoundary.{u})
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap))
    (C C' : Set ↥T.scheme) (hC : C ∈ intersectionComponents T.boundary J)
    (hC' : C' ∈ intersectionComponents T.boundary J) (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp hC
  obtain ⟨D', hD', rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp hC'
  have hinj : Function.Injective ⇑(intersectionIdeal T.boundary J).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (intersectionIdeal T.boundary J).subschemeι).injective
  rw [Set.disjoint_left]
  rintro x ⟨d, hd, rfl⟩ ⟨d', hd', he⟩
  have hdd : d' = d := hinj he
  subst hdd
  have hDD : D = D' :=
    irreducibleComponents_eq_of_inter_nonempty_of_smooth T J hsm D hD D' hD' ⟨d', hd, hd'⟩
  exact hne (by rw [hDD])

theorem isOpen_preimage_sUnion_intersectionComponents (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap))
    (𝒞 : Set (Set ↥T.scheme)) (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J) :
    IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞) := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have hinj : Function.Injective ⇑(intersectionIdeal T.boundary J).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (intersectionIdeal T.boundary J).subschemeι).injective
  have key : ⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞 =
      ⋃₀ {D : Set ↥(intersectionIdeal T.boundary J).subscheme |
        D ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme ∧
          ⇑(intersectionIdeal T.boundary J).subschemeι '' D ∈ 𝒞} := by
    apply Set.Subset.antisymm
    · rintro x hx
      obtain ⟨C, hC𝒞, hxC⟩ := hx
      obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp (h𝒞 hC𝒞)
      obtain ⟨d, hd, hde⟩ := hxC
      have hdx : d = x := hinj hde
      subst hdx
      exact ⟨D, ⟨hD, hC𝒞⟩, hd⟩
    · rintro x ⟨D, ⟨hD, hD𝒞⟩, hxD⟩
      exact ⟨⇑(intersectionIdeal T.boundary J).subschemeι '' D, hD𝒞, ⟨x, hxD, rfl⟩⟩
  rw [key]
  exact isOpen_sUnion_of_subset_irreducibleComponents
    (irreducibleComponents_eq_of_inter_nonempty_of_smooth T J hsm) (fun D hD => hD.1)

theorem componentUnionIdeal_support_eq_sUnion (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme))
    (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J)
    (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme) = ⋃₀ 𝒞 := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have hqc : QuasiCompact ((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
      (intersectionIdeal T.boundary J).subschemeι) := inferInstance
  have hsub : ⋃₀ 𝒞 ⊆ Set.range ⇑(intersectionIdeal T.boundary J).subschemeι := by
    rintro x ⟨C, hC, hxC⟩
    obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp (h𝒞 hC)
    obtain ⟨d, hd, rfl⟩ := hxC
    exact ⟨d, rfl⟩
  have h0 : ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫ (intersectionIdeal T.boundary J).subschemeι)
      = ⇑(intersectionIdeal T.boundary J).subschemeι ∘ ⇑(componentUnionOpens T.boundary J 𝒞 hop).ι := rfl
  have hr2 : Set.range ⇑(componentUnionOpens T.boundary J 𝒞 hop).ι
      = ⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞 :=
    Scheme.Opens.range_ι _
  have hrange : Set.range ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
      (intersectionIdeal T.boundary J).subschemeι) = ⋃₀ 𝒞 := by
    rw [h0, Set.range_comp, hr2]
    exact Set.image_preimage_eq_of_subset hsub
  have hfin : 𝒞.Finite := (intersectionComponents_finite T hT J).subset h𝒞
  have hclosed : IsClosed (⋃₀ 𝒞) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion
      (fun C hC => isClosed_of_mem_intersectionComponents T.boundary J C (h𝒞 hC))
  have h1 : (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme)
      = closure (Set.range ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
          (intersectionIdeal T.boundary J).subschemeι)) :=
    Scheme.Hom.support_ker _
  rw [h1, hrange]
  exact hclosed.closure_eq

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCodimension

theorem lt_krullDimSucc_of_le_ringKrullDim_stalk (X : Scheme.{u}) (x : ↥X) (n : ℕ)
    (hn : (n : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (hfin : topologicalKrullDim ↥X ≠ ⊤) : n < krullDimSucc X := by
  have hn' : ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := hn
  have hle : ((n : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X :=
    le_trans hn' (ringKrullDim_stalk_le_topologicalKrullDim X x)
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  by_cases hb : topologicalKrullDim ↥X = ⊥
  · rw [hb] at hle
    exact absurd (le_bot_iff.mp hle) WithBot.coe_ne_bot
  · obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hb
    rw [← he] at hle hfin ⊢
    have he' : e ≠ ⊤ := by
      intro hcon
      apply hfin
      rw [hcon]
      simp
    lift e to ℕ using he' with m
    rw [withBotSuccToNat_coe]
    have hmm : ((m : ℕ∞)).toNat = m := by simp
    rw [hmm]
    have hnm : n ≤ m := by exact_mod_cast hle
    omega

theorem card_lt_krullDimSucc_of_mem_intersectionComponents : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      C ∈ intersectionComponents T.boundary J → J.card < krullDimSucc T.scheme := by
  classical
  intro T hT J C hC
  have hC' : IsIrreducible C ∧ C ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) ∧
      ∀ C' : Set ↥T.scheme, IsIrreducible C' → C ⊆ C' →
        C' ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) → C' = C :=
    (mem_intersectionComponents_iff T.boundary J C).mp hC
  obtain ⟨hirr, hsub, -⟩ := hC'
  obtain ⟨x, hxC⟩ := hirr.nonempty
  have hxsupp : x ∈ (intersectionIdeal T.boundary J).support := hsub hxC
  have hxj : ∀ j ∈ J, x ∈ (T.boundary.get j).support := by
    intro j hj
    rw [mem_support_iff_stalkIdeal_ne_top]
    intro htop
    rw [mem_support_iff_stalkIdeal_ne_top] at hxsupp
    have hle : T.boundary.get j ≤ intersectionIdeal T.boundary J := by
      rw [intersectionIdeal_eq_iSup]
      exact le_iSup₂ (f := fun (i : Fin T.boundary.length) (_ : i ∈ J) => T.boundary.get i) j hj
    have h1 := stalkIdeal_mono hle x
    rw [htop] at h1
    exact hxsupp (top_le_iff.mp h1)
  obtain ⟨-, hsnc⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hT.snc
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := (hsnc x).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp T.scheme.isBasis_affineOpens hxU
  have hV : IsAffineOpen V := hVB
  have hex : ∀ j : Fin T.boundary.length, j ∈ J → ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    have hne : a (j : ℕ) ≠ none := by
      intro hj'
      have htop := hnone (j : ℕ) j.isLt hj'
      have hx' := hxj j hj
      rw [List.get_eq_getElem] at hx'
      exact Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top _ htop hxU hx'
    exact Option.ne_none_iff_exists'.mp hne
  choose F hFspec using hex
  have hGinj : Function.Injective
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2) := by
    intro p q h
    have h1 : a (q.1 : ℕ) = some (F p.1 p.2) := by
      rw [hFspec q.1 q.2]
      exact congrArg Option.some h.symm
    have h2 := hinj (p.1 : ℕ) p.1.isLt (q.1 : ℕ) q.1.isLt (F p.1 p.2) (hFspec p.1 p.2) h1
    exact Subtype.ext (Fin.val_injective h2)
  have hcard : (J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)).card = J.card := by
    rw [Finset.card_image_of_injective _ hGinj, Finset.card_attach]
  let d : EtaleChart T.structMap V m := {
    map := T.scheme.homOfLE hVU ≫ c.map
    comp_struct := by rw [Category.assoc, c.comp_struct, ← Category.assoc, Scheme.homOfLE_ι]
    isEtale := by
      have := c.isEtale
      infer_instance }
  have hmem : ∀ t ∈ J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2),
      d.coord t ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    intro t ht
    obtain ⟨p, -, hpt⟩ := Finset.mem_image.mp ht
    have hat : a (p.1 : ℕ) = some t := by
      rw [hFspec p.1 p.2]
      exact congrArg Option.some hpt
    have hU' := hsome (p.1 : ℕ) p.1.isLt t hat
    have hV' : restrictIdeal T.boundary[p.1.val] V = d.coordIdeal {t} := by
      have h' : T.boundary[p.1.val].comap U.ι =
          (coordSubspaceIdeal _ m {t}).comap c.map := by
        rw [← restrictIdeal_eq_comap_ι, hU', EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
      rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
      change _ = (coordSubspaceIdeal _ m {t}).comap (T.scheme.homOfLE hVU ≫ c.map)
      rw [Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp,
        Scheme.homOfLE_ι]
    have hx' := hxj p.1 p.2
    rw [List.get_eq_getElem] at hx'
    exact coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton hV
      d t _ hV' x hxV hx'
  have hle2 := card_le_ringKrullDim_stalk hV d x hxV
    (J.attach.image (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)) hmem
  have hfin : topologicalKrullDim ↥T.scheme ≠ ⊤ := ne_of_lt hT.topologicalKrullDim_lt_top
  have hlt := lt_krullDimSucc_of_le_ringKrullDim_stalk T.scheme x _ hle2 hfin
  rwa [hcard] at hlt

theorem card_lt_krullDimSucc_of_nonempty (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (hJ : (intersectionComponents T.boundary J).Nonempty) :
    J.card < krullDimSucc T.scheme := by
  obtain ⟨C, hC⟩ := hJ
  exact card_lt_krullDimSucc_of_mem_intersectionComponents T hT J C hC

end MonomialCodimension

end FunctorialResolution.EmbeddedResolution
end
