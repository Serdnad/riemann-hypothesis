module

public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionData
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

def pullbackIsoLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    ((pullback s.lastStructMap (d.cover.f i) : Scheme.{u}) ≅ (d.seq i).lastObj) :=
  (pullbackSymmetry s.lastStructMap (d.cover.f i)).trans (d.lastObjIsoPullback i).symm

theorem pullbackIsoLastObj_hom_lastStructMap (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (d.pullbackIsoLastObj i).hom ≫ (d.seq i).lastStructMap = pullback.snd s.lastStructMap (d.cover.f i) := by
  rw [pullbackIsoLastObj]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← d.lastObjIsoPullback_hom_fst i, Iso.inv_hom_id_assoc]
  exact pullbackSymmetry_hom_comp_fst _ _

theorem isProper_lastStructMap (d : LocalResolutionData k f s) : IsProper s.lastStructMap := by
  have key : ∀ i : d.cover.I₀, IsProper (d.seq i).lastStructMap := by
    intro i
    obtain ⟨-, h, -⟩ := d.isResolution i
    exact h
  obtain ⟨-, h2⟩ := (inferInstance :
    MorphismProperty.IsLocalAtTarget (@IsProper) Scheme.zariskiPrecoverage)
  refine h2 (R := d.cover.presieve₀) d.cover.mem₀ ?_
  intro U g _inst hg
  obtain ⟨i⟩ := hg
  rw [← d.pullbackIsoLastObj_hom_lastStructMap i]
  have := key i
  infer_instance

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem chartToLastObj_comp_lastStructMap_assoc (d : LocalResolutionData k f s) (j : d.cover.I₀) :
    d.chartToLastObj j ≫ (s.lastStructMap ≫ f) = (d.seq j).lastStructMap ≫ (d.cover.f j ≫ f) := by
  rw [← Category.assoc, d.chartToLastObj_comp_lastStructMap j, Category.assoc]

private theorem ringHom_smooth_appTop_of_smooth {A B : Scheme.{u}} [AlgebraicGeometry.IsAffine B]
    (g : A ⟶ B) (𝒲 : Scheme.OpenCover.{u, u} A)
    [∀ i, AlgebraicGeometry.IsAffine (𝒲.X i)]
    (hg : AlgebraicGeometry.Smooth g) (i : 𝒲.I₀) :
    RingHom.Smooth ((𝒲.f i ≫ g).appTop.hom) :=
  (AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover 𝒲).mp hg i

private theorem smooth_of_ringHom_smooth_appTop {A B : Scheme.{u}} [AlgebraicGeometry.IsAffine B]
    (g : A ⟶ B) (𝒲 : Scheme.OpenCover.{u, u} A)
    [∀ i, AlgebraicGeometry.IsAffine (𝒲.X i)]
    (h : ∀ i : 𝒲.I₀, RingHom.Smooth ((𝒲.f i ≫ g).appTop.hom)) :
    AlgebraicGeometry.Smooth g :=
  (AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover 𝒲).mpr h

private theorem smooth_chartToLastObj_comp (d : LocalResolutionData k f s) (j : d.cover.I₀) :
    AlgebraicGeometry.Smooth (d.chartToLastObj j ≫ (s.lastStructMap ≫ f)) := by
  rw [d.chartToLastObj_comp_lastStructMap_assoc j]
  exact (d.isResolution j).1

private theorem smooth_appTop_affineCover_chartToLastObj (d : LocalResolutionData k f s) (j : d.cover.I₀)
    (a : ((d.seq j).lastObj.affineCover).I₀) :
    RingHom.Smooth (((((d.seq j).lastObj.affineCover).f a ≫ d.chartToLastObj j)
      ≫ (s.lastStructMap ≫ f)).appTop.hom) := by
  have h := ringHom_smooth_appTop_of_smooth (d.chartToLastObj j ≫ (s.lastStructMap ≫ f))
    ((d.seq j).lastObj.affineCover) (smooth_chartToLastObj_comp d j) a
  rw [Category.assoc]
  exact h

theorem smooth_lastStructMap_comp (d : LocalResolutionData k f s) :
    AlgebraicGeometry.Smooth (s.lastStructMap ≫ f) := by
  have haffine : ∀ i : (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).I₀,
      AlgebraicGeometry.IsAffine
        ((d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).X i) := by
    rintro ⟨j, a⟩
    exact inferInstanceAs (AlgebraicGeometry.IsAffine (((d.lastObjCover.X j).affineCover).X a))
  refine smooth_of_ringHom_smooth_appTop (s.lastStructMap ≫ f)
    (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover) ?_
  rintro ⟨j, a⟩
  exact smooth_appTop_affineCover_chartToLastObj d j a

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem isPullback_chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsPullback (d.chartToLastObj i) ((d.seq i).lastStructMap) s.lastStructMap (d.cover.f i) := by
  have hsq : CommSq ((d.seq i).lastStructMap) (d.chartToLastObj i) (d.cover.f i) s.lastStructMap :=
    ⟨(d.chartToLastObj_comp_lastStructMap i).symm⟩
  have h : IsPullback ((d.seq i).lastStructMap) (d.chartToLastObj i) (d.cover.f i) s.lastStructMap :=
    IsPullback.of_iso_pullback hsq (d.lastObjIsoPullback i) (d.lastObjIsoPullback_hom_fst i)
      (d.chartToLastObj_eq i).symm
  exact h.flip

private theorem isIso_pullback_snd_restrict_smoothLocus (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsIso (pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus)) := by
  have hp := isPullback_morphismRestrict s.lastStructMap f.smoothLocus
  have hc := isPullback_morphismRestrict (d.cover.f i) f.smoothLocus
  have ht := isPullback_morphismRestrict ((d.seq i).lastStructMap) (d.cover.f i ⁻¹ᵁ f.smoothLocus)
  have hbig := ht.paste_vert (d.isPullback_chartToLastObj i).flip
  have hw : (((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus)) ≫
        (d.cover.f i ∣_ f.smoothLocus)) ≫ f.smoothLocus.ι
      = ((((d.seq i).lastStructMap ⁻¹ᵁ (d.cover.f i ⁻¹ᵁ f.smoothLocus)).ι) ≫ d.chartToLastObj i)
        ≫ s.lastStructMap := by
    rw [Category.assoc, hc.w]
    exact hbig.w
  have hsq : IsPullback ((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus))
      (hp.lift _ _ hw) (d.cover.f i ∣_ f.smoothLocus) (s.lastStructMap ∣_ f.smoothLocus) := by
    refine IsPullback.of_bot ?_ ?_ hp
    · rw [hp.lift_snd, hc.w]
      exact hbig
    · rw [hp.lift_fst]
  have hiso : IsIso ((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus)) := by
    rw [d.preimage_smoothLocus_cover_map i]
    exact (d.isResolution i).2.2.1
  have hcomp : IsIso (hsq.flip.isoPullback.hom ≫
      pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus)) := by
    rw [hsq.flip.isoPullback_hom_snd]
    exact hiso
  exact IsIso.of_isIso_comp_left hsq.flip.isoPullback.hom
    (pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus))

private theorem exists_restrict_smoothLocus_apply_eq (d : LocalResolutionData k f s) :
    ∀ x : ↥(f.smoothLocus.toScheme), ∃ (i : d.cover.I₀)
      (y : ↥((d.cover.f i ⁻¹ᵁ f.smoothLocus).toScheme)),
        (d.cover.f i ∣_ f.smoothLocus) y = x := by
  intro x
  have hsup : (⨆ i, (d.cover.f i).opensRange) = ⊤ := d.cover.iSup_opensRange
  have hx : (x.1 : ↥X) ∈ (⨆ i, (d.cover.f i).opensRange : X.Opens) := by
    rw [hsup]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hi' : (x.1 : ↥X) ∈ Set.range (d.cover.f i).base := hi
  obtain ⟨y₀, hy₀⟩ := hi'
  have hmem : y₀ ∈ (d.cover.f i ⁻¹ᵁ f.smoothLocus) := by
    show (d.cover.f i).base y₀ ∈ f.smoothLocus
    rw [hy₀]
    exact x.2
  refine ⟨i, ⟨y₀, hmem⟩, ?_⟩
  have h2 := congrFun (morphismRestrict_base (d.cover.f i) f.smoothLocus) ⟨y₀, hmem⟩
  refine h2.trans (Subtype.ext ?_)
  exact hy₀

private def smoothLocusOpenCover (d : LocalResolutionData k f s) :
    Scheme.OpenCover.{u, u} (f.smoothLocus.toScheme) :=
  Scheme.Cover.mkOfCovers d.cover.I₀
    (fun i => (d.cover.f i ⁻¹ᵁ f.smoothLocus).toScheme)
    (fun i => d.cover.f i ∣_ f.smoothLocus)
    (exists_restrict_smoothLocus_apply_eq d)
    (fun i => show IsOpenImmersion (d.cover.f i ∣_ f.smoothLocus) from inferInstance)

theorem isIso_lastStructMap_restrict_smoothLocus (d : LocalResolutionData k f s) :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by
  have hh : ∀ i : d.cover.I₀, MorphismProperty.isomorphisms Scheme.{u}
      (Scheme.Cover.pullbackHom (smoothLocusOpenCover d) (s.lastStructMap ∣_ f.smoothLocus) i) := by
    intro i
    exact isIso_pullback_snd_restrict_smoothLocus d i
  have key : MorphismProperty.isomorphisms Scheme.{u} (s.lastStructMap ∣_ f.smoothLocus) :=
    IsZariskiLocalAtTarget.of_openCover (smoothLocusOpenCover d) hh
  exact key

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

private theorem comp_base_apply {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (z : ↥A) :
    (a ≫ b).base z = b.base (a.base z) := by
  simp

private theorem hom_base_inv_base_apply {A B : Scheme.{u}} (e : A ≅ B) (z : ↥B) :
    e.hom.base (e.inv.base z) = z := by
  rw [← comp_base_apply, e.inv_hom_id]
  simp

private theorem mem_support_comap_of_mem_support {Z W : Scheme.{u}} (g : Z ⟶ W) (I : W.IdealSheafData)
    (z : ↥Z) (hz : g.base z ∈ I.support) : z ∈ (I.comap g).support := by
  rw [Scheme.IdealSheafData.support_comap]
  exact hz

theorem centersLieOver_smoothLocusComplement (d : LocalResolutionData k f s) :
    s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
  intro i hi x hx
  obtain ⟨i₀, u, hu⟩ : ∃ (i₀ : d.cover.I₀) (u : ↥(d.cover.X i₀)),
      (d.cover.f i₀).base u = (s.projectionToBase i).base x := by
    obtain ⟨u, hu⟩ := d.cover.covers ((s.projectionToBase i).base x)
    exact ⟨d.cover.idx ((s.projectionToBase i).base x), u, hu⟩
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback u x hu
  have hw1' : (pullback.fst (d.cover.f i₀) (s.projectionToBase i)).base w = u := hw1
  have hw2' : (pullback.snd (d.cover.f i₀) (s.projectionToBase i)).base w = x := hw2
  have hws : w ∈ ((s.center i).comap (pullback.snd (d.cover.f i₀) (s.projectionToBase i))).support := by
    refine mem_support_comap_of_mem_support _ _ _ ?_
    rw [hw2']
    exact hx
  obtain ⟨l, hl, hr⟩ := (d.exists_reindex_eq_iff_exists_mem_support i₀ i hi).2 ⟨w, hws⟩
  subst hr
  have ht : ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈ ((d.seq i₀).center l).support := by
    rw [d.localSequence_center_eq_comap i₀ l hl]
    refine mem_support_comap_of_mem_support _ _ _ ?_
    rw [comp_base_apply, hom_base_inv_base_apply, hw2']
    exact hx
  have key : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w)
      = (pullback.fst (d.cover.f i₀) (s.projectionToBase (d.reindex i₀ l))).base w := by
    rw [← d.schemeAtIsoPullback_hom_fst i₀ l hl.le, comp_base_apply, hom_base_inv_base_apply]
  have hres := d.isResolution i₀
  unfold FunctorialResolution.EmbeddedResolution.IsStrongResolution at hres
  obtain ⟨-, -, -, -, hC, -⟩ := hres
  have hCt : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈
      ((smoothLocusComplement (d.cover.f i₀ ≫ f) : TopologicalSpace.Closeds ↥(d.cover.X i₀)) :
        Set ↥(d.cover.X i₀)) := hC l hl _ ht
  rw [← d.preimage_smoothLocusComplement_cover_map i₀] at hCt
  have hfin : (d.cover.f i₀).base
      (((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w)) ∈
      ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X) := hCt
  show (s.projectionToBase (d.reindex i₀ l)).base x ∈
    ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X)
  rw [← hu, ← hw1', ← key]
  exact hfin

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution
end

section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem dense_preimage_smoothLocus (d : LocalResolutionData k f s) :
    Dense ((s.lastStructMap ⁻¹ᵁ f.smoothLocus : TopologicalSpace.Opens ↥(s.lastObj)) : Set ↥(s.lastObj)) := by
  rw [dense_iff_inter_open]
  intro V hV hVne
  obtain ⟨x, hxV⟩ := hVne
  obtain ⟨i, y, hy⟩ := d.exists_chartToLastObj_eq x
  have hres := (d.isResolution i).2.2.2.1
  have hW : IsOpen (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) :=
    ((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj))).2
  have hyW : y ∈ (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) := by
    show (d.chartToLastObj i).base y ∈ V
    rw [hy]
    exact hxV
  obtain ⟨z, hz1, hz2⟩ := dense_iff_inter_open.mp hres _ hW ⟨y, hyW⟩
  refine ⟨(d.chartToLastObj i).base z, hz1, ?_⟩
  have hmem : ((d.seq i).lastStructMap).base z ∈ (d.cover.f i) ⁻¹ᵁ f.smoothLocus := by
    rw [d.preimage_smoothLocus_cover_map i]
    exact hz2
  have hbase : (s.lastStructMap).base ((d.chartToLastObj i).base z)
      = (d.cover.f i).base (((d.seq i).lastStructMap).base z) := by
    have h := congrArg (fun m : (d.seq i).lastObj ⟶ X => m.base z) (d.chartToLastObj_comp_lastStructMap i)
    simpa using h
  show (s.lastStructMap).base ((d.chartToLastObj i).base z) ∈ f.smoothLocus
  rw [hbase]
  exact hmem

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end
