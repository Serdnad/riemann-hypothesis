module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem preimage_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  simp

private theorem image_preimage_of_le {X : Scheme.{u}} (U A : X.Opens) (hA : A ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ A) = A := by
  apply le_antisymm
  · rintro z ⟨w, hw, rfl⟩
    exact hw
  · intro z hz
    exact ⟨⟨z, hA hz⟩, hz, rfl⟩

private theorem basicOpen_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (s : ↑(Y.presheaf.obj (Opposite.op U))) :
    X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s) =
      V ⊓ f ⁻¹ᵁ Y.basicOpen s := by
  simp [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.preimage_basicOpen]

private theorem algebraMap_basicOpen_eq_presheaf_map {X : Scheme.{u}} {U : X.Opens}
    (s : ↑(X.presheaf.obj (Opposite.op U))) :
    algebraMap ↑(X.presheaf.obj (Opposite.op U))
        ↑(X.presheaf.obj (Opposite.op (X.basicOpen s))) =
      (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom :=
  rfl

private theorem isStandardSmoothOfRelativeDimension_appLE_basicOpen_target {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) {U : Y.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {V : X.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (s : ↑(Y.presheaf.obj (Opposite.op U)))
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom)
    (hle : X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s) ≤
      f ⁻¹ᵁ Y.basicOpen s) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f (Y.basicOpen s)
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)) hle).hom := by
  have i1 : IsLocalization.Away s ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen s))) :=
    hU.isLocalization_basicOpen s
  have i2 : IsLocalization.Away ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)
      ↑(X.presheaf.obj (Opposite.op
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) :=
    hV.isLocalization_basicOpen _
  have i3 : IsLocalization
      (Submonoid.map (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom (Submonoid.powers s))
      ↑(X.presheaf.obj (Opposite.op
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) := by
    rw [Submonoid.map_powers]
    exact i2
  have key := RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves n
    (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom (Submonoid.powers s)
    ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen s)))
    ↑(X.presheaf.obj (Opposite.op
      (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) hs
  convert key using 1
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  rw [IsLocalization.map_comp, algebraMap_basicOpen_eq_presheaf_map,
    algebraMap_basicOpen_eq_presheaf_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, AlgebraicGeometry.Scheme.Hom.map_appLE,
    AlgebraicGeometry.Scheme.Hom.appLE_map]

private theorem isStandardSmoothOfRelativeDimension_appLE_basicOpen_source {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) {U : Y.Opens}
    {V : X.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom)
    (t : ↑(X.presheaf.obj (Opposite.op V))) (hle : X.basicOpen t ≤ f ⁻¹ᵁ U) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U (X.basicOpen t) hle).hom := by
  have : IsLocalization.Away t ↑(X.presheaf.obj (Opposite.op (X.basicOpen t))) :=
    hV.isLocalization_basicOpen t
  have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0
      (algebraMap ↑(X.presheaf.obj (Opposite.op V))
        ↑(X.presheaf.obj (Opposite.op (X.basicOpen t)))) :=
    RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway _ t
  have hcomp := h0.comp hs
  rw [zero_add, algebraMap_basicOpen_eq_presheaf_map, ← CommRingCat.hom_comp,
    AlgebraicGeometry.Scheme.Hom.appLE_map] at hcomp
  exact hcomp

private theorem isStandardSmoothOfRelativeDimension_appLE_congr {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) {U U' : Y.Opens}
    {V V' : X.Opens} (hU : U' = U) (hV : V' = V) (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U')
    (hstd : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U' V' e').hom := by
  subst hU
  subst hV
  exact hstd

private theorem exists_affineChart_isStandardSmoothOfRelativeDimension {X X' : Scheme.{u}}
    (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] (A₀ : X.Opens) (B₀ : X'.Opens)
    (hB₀ : B₀ ≤ φ ⁻¹ᵁ A₀) (y : ↥X') (hy : y ∈ B₀) :
    ∃ (A : X.Opens) (B : X'.Opens), AlgebraicGeometry.IsAffineOpen A ∧
      AlgebraicGeometry.IsAffineOpen B ∧ A ≤ A₀ ∧ B ≤ B₀ ∧ y ∈ B ∧
      ∃ e : B ≤ φ ⁻¹ᵁ A, RingHom.IsStandardSmoothOfRelativeDimension r
        (AlgebraicGeometry.Scheme.Hom.appLE φ A B e).hom := by
  obtain ⟨U, hU, V, hV, hyV, e, hstd⟩ :=
    (AlgebraicGeometry.smoothOfRelativeDimension_iff r φ).mp inferInstance y
  obtain ⟨s, hsA₀, hys⟩ := hU.exists_basicOpen_le (⟨φ.base y, hB₀ hy⟩ : ↥A₀) (e hyV)
  have hB₁eq : X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) =
      V ⊓ φ ⁻¹ᵁ X.basicOpen s := basicOpen_appLE φ e s
  have hB₁le : X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) ≤
      φ ⁻¹ᵁ X.basicOpen s := by
    rw [hB₁eq]
    exact inf_le_right
  have hB₁aff : AlgebraicGeometry.IsAffineOpen
      (X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s)) := hV.basicOpen _
  have hyB₁ : y ∈ X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) := by
    rw [hB₁eq]
    exact ⟨hyV, hys⟩
  have hstd₁ :=
    isStandardSmoothOfRelativeDimension_appLE_basicOpen_target φ r hU hV e s hstd hB₁le
  obtain ⟨t, htB₀, hyt⟩ := hB₁aff.exists_basicOpen_le (⟨y, hy⟩ : ↥B₀) hyB₁
  have hBle : X'.basicOpen t ≤ φ ⁻¹ᵁ X.basicOpen s :=
    le_trans (X'.basicOpen_le t) hB₁le
  exact ⟨X.basicOpen s, X'.basicOpen t, hU.basicOpen s, hB₁aff.basicOpen t, hsA₀, htB₀, hyt,
    hBle, isStandardSmoothOfRelativeDimension_appLE_basicOpen_source φ r hB₁aff hB₁le hstd₁ t hBle⟩

theorem smoothOfRelativeDimension_resLE {X X' : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] (U₀ : X.Opens) (V₀ : X'.Opens)
    (h : V₀ ≤ φ ⁻¹ᵁ U₀) :
    AlgebraicGeometry.SmoothOfRelativeDimension r (φ.resLE U₀ V₀ h) := by
  rw [AlgebraicGeometry.smoothOfRelativeDimension_iff]
  intro x
  have hx : V₀.ι.base x ∈ V₀ := by
    have hmem : V₀.ι.base x ∈ AlgebraicGeometry.Scheme.Hom.opensRange V₀.ι := ⟨x, rfl⟩
    rwa [AlgebraicGeometry.Scheme.Opens.opensRange_ι] at hmem
  obtain ⟨A, B, hA, hB, hAU₀, hBV₀, hxB, e, hstd⟩ :=
    exists_affineChart_isStandardSmoothOfRelativeDimension φ r U₀ V₀ h (V₀.ι.base x) hx
  have hpre : (φ.resLE U₀ V₀ h) ⁻¹ᵁ (U₀.ι ⁻¹ᵁ A) = V₀.ι ⁻¹ᵁ (φ ⁻¹ᵁ A) := by
    rw [← preimage_comp, ← preimage_comp, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]
  have he' : V₀.ι ⁻¹ᵁ B ≤ (φ.resLE U₀ V₀ h) ⁻¹ᵁ (U₀.ι ⁻¹ᵁ A) := by
    rw [hpre]
    exact fun z hz => e hz
  refine ⟨U₀.ι ⁻¹ᵁ A, hA.preimage_of_isOpenImmersion U₀.ι (by simp [hAU₀]),
    V₀.ι ⁻¹ᵁ B, hB.preimage_of_isOpenImmersion V₀.ι (by simp [hBV₀]), hxB, he', ?_⟩
  rw [AlgebraicGeometry.Scheme.Hom.resLE_appLE]
  exact isStandardSmoothOfRelativeDimension_appLE_congr φ r (image_preimage_of_le U₀ A hAU₀)
    (image_preimage_of_le V₀ B hBV₀) e _ hstd

instance instSmoothOfRelativeDimensionResLE {X X' : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] (U₀ : X.Opens) (V₀ : X'.Opens)
    (h : V₀ ≤ φ ⁻¹ᵁ U₀) :
    AlgebraicGeometry.SmoothOfRelativeDimension r (φ.resLE U₀ V₀ h) :=
  smoothOfRelativeDimension_resLE φ r U₀ V₀ h

end FunctorialResolution.EmbeddedResolution
end

section

namespace AlgebraicGeometry

open CategoryTheory

universe u

namespace IsOpenImmersion

theorem bijective_appLE_of_image_eq {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f]
    (O : B.Opens) (S : A.Opens) (e : S ≤ f ⁻¹ᵁ O) (h : f ''ᵁ S = O) :
    Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appLE f O S e)) := by
  subst h
  have : IsIso (Scheme.Hom.appLE f (f ''ᵁ S) S e) := by
    rw [← Scheme.Hom.appIso_hom' f S]
    infer_instance
  constructor
  · intro a b hab
    have h1 : (CommRingCat.Hom.hom (Scheme.Hom.appLE f (f ''ᵁ S) S e ≫
          inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) a
        = (CommRingCat.Hom.hom (Scheme.Hom.appLE f (f ''ᵁ S) S e ≫
          inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) b := by
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, hab]
    rw [IsIso.hom_inv_id] at h1
    simpa only [CommRingCat.hom_id, RingHom.id_apply] using h1
  · intro y
    refine ⟨(CommRingCat.Hom.hom (inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) y, ?_⟩
    have h3 := congrArg (fun mm => (CommRingCat.Hom.hom mm) y)
      (IsIso.inv_hom_id (Scheme.Hom.appLE f (f ''ᵁ S) S e))
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] using h3

end IsOpenImmersion

end AlgebraicGeometry
end

section

namespace FunctorialResolution.EmbeddedResolution

open Set TopologicalSpace

theorem isClosed_sUnion_of_subset_irreducibleComponents {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsClosed (⋃₀ 𝒜) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents ..
  have hsub : 𝒜 ⊆ irreducibleComponents X := fun C hC => h𝒜 C hC
  rw [Set.sUnion_eq_biUnion]
  exact (hfin.subset hsub).isClosed_biUnion
    (fun C hC => isClosed_of_mem_irreducibleComponents _ (h𝒜 C hC))

theorem isOpen_sUnion_of_subset_irreducibleComponents {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X]
    (hsep : ∀ C₁ ∈ irreducibleComponents X, ∀ C₂ ∈ irreducibleComponents X,
      (C₁ ∩ C₂).Nonempty → C₁ = C₂)
    {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsOpen (⋃₀ 𝒜) := by
  have key : (⋃₀ 𝒜)ᶜ = ⋃₀ (irreducibleComponents X \ 𝒜) := by
    apply Set.Subset.antisymm
    · intro y hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩,
        mem_irreducibleComponent ..⟩
      intro hmem
      exact hy ⟨irreducibleComponent y, hmem, mem_irreducibleComponent ..⟩
    · intro y hyc
      obtain ⟨C, ⟨hC, hCA⟩, hyC⟩ := hyc
      show y ∉ ⋃₀ 𝒜
      intro hy
      obtain ⟨D, hD, hyD⟩ := hy
      have heq : C = D := hsep C hC D (h𝒜 D hD) ⟨y, hyC, hyD⟩
      rw [heq] at hCA
      exact hCA hD
  rw [← isClosed_compl_iff, key]
  exact isClosed_sUnion_of_subset_irreducibleComponents (fun C hC => hC.1)

theorem irreducibleComponents_eq_of_stalk_isDomain (X : AlgebraicGeometry.Scheme)
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) {C₁ C₂ : Set X}
    (h₁ : C₁ ∈ irreducibleComponents X) (h₂ : C₂ ∈ irreducibleComponents X)
    {x : X} (hx₁ : x ∈ C₁) (hx₂ : x ∈ C₂) : C₁ = C₂ := by
  have := hX x
  obtain ⟨ξ₁, hg₁⟩ := QuasiSober.sober h₁.1 (isClosed_of_mem_irreducibleComponents _ h₁)
  obtain ⟨ξ₂, hg₂⟩ := QuasiSober.sober h₂.1 (isClosed_of_mem_irreducibleComponents _ h₂)
  have hξ₁ : closure {ξ₁} = C₁ := hg₁
  have hξ₂ : closure {ξ₂} = C₂ := hg₂
  have hrange : Set.range (X.fromSpecStalk x).base = {y | y ⤳ x} :=
    AlgebraicGeometry.Scheme.range_fromSpecStalk ..
  have hm₁ : ξ₁ ∈ Set.range (X.fromSpecStalk x).base := by
    rw [hrange]
    exact specializes_iff_mem_closure.mpr (by rw [hξ₁]; exact hx₁)
  have hm₂ : ξ₂ ∈ Set.range (X.fromSpecStalk x).base := by
    rw [hrange]
    exact specializes_iff_mem_closure.mpr (by rw [hξ₂]; exact hx₂)
  have hcont : Continuous (X.fromSpecStalk x).base := (X.fromSpecStalk x).continuous
  have hirrU : IsIrreducible (Set.univ : Set (PrimeSpectrum (X.presheaf.stalk x))) :=
    IrreducibleSpace.isIrreducible_univ ..
  have himg : IsIrreducible (Set.range (X.fromSpecStalk x).base) := by
    rw [← Set.image_univ]
    exact hirrU.image _ hcont.continuousOn
  have hcl : IsIrreducible (closure (Set.range (X.fromSpecStalk x).base)) := himg.closure
  have hs₁ : C₁ ⊆ closure (Set.range (X.fromSpecStalk x).base) := by
    rw [← hξ₁]
    exact closure_mono (Set.singleton_subset_iff.mpr hm₁)
  have hs₂ : C₂ ⊆ closure (Set.range (X.fromSpecStalk x).base) := by
    rw [← hξ₂]
    exact closure_mono (Set.singleton_subset_iff.mpr hm₂)
  have e₁ : closure (Set.range (X.fromSpecStalk x).base) ⊆ C₁ := h₁.2 hcl hs₁
  have e₂ : closure (Set.range (X.fromSpecStalk x).base) ⊆ C₂ := h₂.2 hcl hs₂
  exact Set.Subset.antisymm (hs₁.trans e₂) (hs₂.trans e₁)

end FunctorialResolution.EmbeddedResolution
end
