module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FunctorialResolution.EmbeddedResolution

namespace SmoothEtaleChart

private theorem exists_etale_mvPolynomial_ulift {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}
    (g : MvPolynomial (Fin n) R →+* S) (hg : g.Etale) (f : R →+* S)
    (hf : g.comp MvPolynomial.C = f) :
    ∃ g' : MvPolynomial (ULift.{u} (Fin n)) R →+* S,
      g'.comp MvPolynomial.C = f ∧ g'.Etale := by
  set E : MvPolynomial (ULift.{u} (Fin n)) R ≃+* MvPolynomial (Fin n) R :=
    (MvPolynomial.renameEquiv R (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)).toRingEquiv with hE
  refine ⟨g.comp E.toRingHom, ?_, RingHom.Etale.respectsIso.right g E hg⟩
  refine RingHom.ext fun a => ?_
  have h1 : E (MvPolynomial.C a) = MvPolynomial.C a := by
    simp [hE]
  have h2 : g (MvPolynomial.C a) = f a := by rw [← hf]; rfl
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, h1, h2]

private theorem exists_etale_over_affineSpace_of_isStandardSmooth {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (hφ : RingHom.IsStandardSmooth (CommRingCat.Hom.hom φ)) :
    ∃ (d : ℕ) (g : Spec S ⟶ AffineSpace (ULift.{u} (Fin d)) (Spec R)),
      Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) (Spec R) ↘ Spec R) = Spec.map φ := by
  obtain ⟨n, gr, hgrC, hgrEt⟩ := hφ.exists_etale_mvPolynomial
  obtain ⟨g', hg'C, hg'Et⟩ := exists_etale_mvPolynomial_ulift gr hgrEt _ hgrC
  have hSpecEt : Etale (Spec.map (CommRingCat.ofHom g')) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact hg'Et
  have hcomp : CommRingCat.ofHom (MvPolynomial.C :
      ↑R →+* MvPolynomial (ULift.{u} (Fin n)) ↑R) ≫ CommRingCat.ofHom g' = φ :=
    CommRingCat.hom_ext hg'C
  refine ⟨n, Spec.map (CommRingCat.ofHom g') ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv, inferInstance, ?_⟩
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  exact congrArg Spec.map hcomp

private theorem resLE_eq_isoSpec_conj_SpecMap_appLE {X Y : Scheme.{u}} (h : Y ⟶ X) {W : X.Opens}
    {V : Y.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V) (e : V ≤ h ⁻¹ᵁ W) :
    hV.isoSpec.hom ≫ Spec.map (h.appLE W V e) ≫ hW.isoSpec.inv = h.resLE W V e := by
  rw [← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι]
  simp only [Category.assoc]
  rw [hW.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec h hW hV e, ← hV.isoSpec_inv_ι]
  simp

private theorem exists_etale_over_affineSpace_resLE_of_isStandardSmooth {X Y : Scheme.{u}} (h : Y ⟶ X)
    {W : X.Opens} {V : Y.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen V) (e : V ≤ h ⁻¹ᵁ W)
    (hstd : RingHom.IsStandardSmooth (CommRingCat.Hom.hom (h.appLE W V e))) :
    ∃ (d : ℕ) (g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme),
      Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e := by
  obtain ⟨d, g₀, hg₀et, hg₀⟩ :=
    exists_etale_over_affineSpace_of_isStandardSmooth (h.appLE W V e) hstd
  have := hg₀et
  have : IsIso (AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv) :=
    ⟨⟨AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.hom, by
        rw [← AffineSpace.map_comp, Iso.inv_hom_id, AffineSpace.map_id], by
        rw [← AffineSpace.map_comp, Iso.hom_inv_id, AffineSpace.map_id]⟩⟩
  have : Etale hV.isoSpec.hom := inferInstance
  have : Etale (AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv) := inferInstance
  refine ⟨d, hV.isoSpec.hom ≫ g₀ ≫ AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv,
    inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, AffineSpace.map_over, ← Category.assoc g₀, hg₀]
  exact resLE_eq_isoSpec_conj_SpecMap_appLE h hW hV e

private theorem smooth_resLE {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h] (W : X.Opens)
    (V : Y.Opens) (e : V ≤ h ⁻¹ᵁ W) : Smooth (h.resLE W V e) := by
  rw [HasRingHomProperty.iff_appLE (P := @Smooth)]
  intro U U' e'
  rw [Scheme.Hom.resLE_appLE]
  exact HasRingHomProperty.appLE @Smooth h ‹Smooth h›
    ⟨W.ι ''ᵁ U.1, U.2.image_of_isOpenImmersion _⟩
    ⟨V.ι ''ᵁ U'.1, U'.2.image_of_isOpenImmersion _⟩ _

private theorem exists_affineOpen_etale_over_affineSpace_resLE_le {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h]
    (y : Y) (W₀ : X.Opens) (hW₀ : h.base y ∈ W₀) (V₀ : Y.Opens) (hV₀ : y ∈ V₀) :
    ∃ (W : X.Opens) (V : Y.Opens) (d : ℕ) (e : V ≤ h ⁻¹ᵁ W),
      IsAffineOpen W ∧ IsAffineOpen V ∧ y ∈ V ∧ W ≤ W₀ ∧ V ≤ V₀ ∧
      ∃ g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme,
        Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e := by
  have e₀ : (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens) ≤ h ⁻¹ᵁ W₀ := inf_le_right
  have hy' : y ∈ (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens) := ⟨hV₀, hW₀⟩
  have : Smooth (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀) := smooth_resLE h W₀ _ e₀
  obtain ⟨W', hW', V', hV', hyV', e', hstd⟩ :=
    Smooth.exists_isStandardSmooth (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀) ⟨y, hy'⟩
  have h1 : h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀ ≫ W₀.ι = (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ≫ h := by
    rw [Scheme.Hom.resLE_comp_ι]
  have hb : ∀ z : ↥(V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens),
      h.base ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι.base z)
        = W₀.ι.base ((h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).base z) := by
    intro z
    exact (congrArg (fun m : (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).toScheme ⟶ X => m.base z) h1).symm
  have hWle : (W₀.ι ''ᵁ W' : X.Opens) ≤ W₀ := by
    rintro x ⟨z, -, rfl⟩
    exact z.2
  have hVle : ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) ≤ V₀ := by
    rintro x ⟨z, -, rfl⟩
    exact z.2.1
  have e : ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) ≤ h ⁻¹ᵁ (W₀.ι ''ᵁ W') := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨(h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).base z, e' hz, (hb z).symm⟩
  have hWaff : IsAffineOpen (W₀.ι ''ᵁ W' : X.Opens) := hW'.image_of_isOpenImmersion W₀.ι
  have hVaff : IsAffineOpen ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) :=
    hV'.image_of_isOpenImmersion _
  have happ : (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).appLE W' V' e'
      = h.appLE (W₀.ι ''ᵁ W') ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V') e :=
    Scheme.Hom.resLE_appLE h e₀ W' V' e'
  rw [happ] at hstd
  obtain ⟨d, g, hg, hgπ⟩ := exists_etale_over_affineSpace_resLE_of_isStandardSmooth h hWaff hVaff e hstd
  exact ⟨W₀.ι ''ᵁ W', (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V', d, e, hWaff, hVaff,
    ⟨⟨y, hy'⟩, hyV', rfl⟩, hWle, hVle, g, hg, hgπ⟩

theorem exists_isAffineOpen_etale_resLE_le {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h]
    (y : Y) (W₀ : X.Opens) (hW₀ : h.base y ∈ W₀) (V₀ : Y.Opens) (hV₀ : y ∈ V₀) :
    ∃ (W : X.Opens) (V : Y.Opens) (d : ℕ) (e : V ≤ h ⁻¹ᵁ W),
      IsAffineOpen W ∧ IsAffineOpen V ∧ y ∈ V ∧ W ≤ W₀ ∧ V ≤ V₀ ∧
      ∃ g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme,
        Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e :=
  exists_affineOpen_etale_over_affineSpace_resLE_le h y W₀ hW₀ V₀ hV₀

end SmoothEtaleChart

end FunctorialResolution.EmbeddedResolution
end

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceIndexedBy (k : Type u) [Field k] (n : Type u) : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace n (Spec (CommRingCat.of k))

abbrev affineSpaceIndexedByToSpec (k : Type u) [Field k] (n : Type u) :
    affineSpaceIndexedBy k n ⟶ Spec (CommRingCat.of k) :=
  affineSpaceIndexedBy k n ↘ Spec (CommRingCat.of k)

def pullbackCoord {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) : Γ(Y, ⊤) :=
  f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i)

@[simp]
theorem pullbackCoord_def {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord f i = f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) := rfl

def coordVectorInl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun a => pullbackCoord f (ULift.up a)) (fun _ => 0) i.down

def coordVectorInr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun _ => 0) (fun b => pullbackCoord f (ULift.up b)) i.down

@[simp]
theorem coordVectorInr_inl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (a : Fin n) :
    coordVectorInr n m f (ULift.up (Sum.inl a)) = 0 := rfl

@[simp]
theorem coordVectorInr_inr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (b : Fin m) :
    coordVectorInr n m f (ULift.up (Sum.inr b)) = pullbackCoord f (ULift.up b) := rfl

end FunctorialResolution.EmbeddedResolution
end
end

section

namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

private theorem algebraMap_mem_map_of_mul_mem {S : Type*} [CommRing S] (G : S) (T : Type*)
    [CommRing T] [Algebra S T] [IsLocalization (Submonoid.powers G) T] (J : Ideal S) (g r x : S)
    (hG : G = g * r) (hgx : g * x ∈ J) :
    algebraMap S T x ∈ Ideal.map (algebraMap S T) J := by
  have hGu : IsUnit (algebraMap S T G) :=
    IsLocalization.map_units T (⟨G, Submonoid.mem_powers G⟩ : Submonoid.powers G)
  rw [hG, map_mul] at hGu
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_left hGu
  have hx : algebraMap S T x = (↑u⁻¹ : T) * algebraMap S T (g * x) := by
    rw [map_mul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hx]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hgx)

theorem exists_away_map_ideal_eq {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime]
    (A : Type*) [CommRing A] [Algebra S A] [IsLocalization q.primeCompl A]
    (I J : Ideal S) (hI : I.FG) (hJ : J.FG)
    (h : Ideal.map (algebraMap S A) I = Ideal.map (algebraMap S A) J) :
    ∃ g : S, g ∉ q ∧
      Ideal.map (algebraMap S (Localization.Away g)) I =
        Ideal.map (algebraMap S (Localization.Away g)) J := by
  classical
  obtain ⟨tI, htI⟩ := hI
  obtain ⟨tJ, htJ⟩ := hJ
  have keyI : ∀ u : S, ∃ g : S, g ∈ q.primeCompl ∧ (u ∈ I → g * u ∈ J) := by
    intro u
    by_cases hu : u ∈ I
    · have hmem : algebraMap S A u ∈ Ideal.map (algebraMap S A) J := by
        rw [← h]
        exact Ideal.mem_map_of_mem _ hu
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A] at hmem
      obtain ⟨g, hg, hgu⟩ := hmem
      exact ⟨g, hg, fun _ => hgu⟩
    · exact ⟨1, Submonoid.one_mem _, fun hh => absurd hh hu⟩
  have keyJ : ∀ v : S, ∃ g : S, g ∈ q.primeCompl ∧ (v ∈ J → g * v ∈ I) := by
    intro v
    by_cases hv : v ∈ J
    · have hmem : algebraMap S A v ∈ Ideal.map (algebraMap S A) I := by
        rw [h]
        exact Ideal.mem_map_of_mem _ hv
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A] at hmem
      obtain ⟨g, hg, hgv⟩ := hmem
      exact ⟨g, hg, fun _ => hgv⟩
    · exact ⟨1, Submonoid.one_mem _, fun hh => absurd hh hv⟩
  choose gI hgI hgIu using keyI
  choose gJ hgJ hgJu using keyJ
  let G : S := (∏ u ∈ tI, gI u) * ∏ v ∈ tJ, gJ v
  have hGmem : G ∈ q.primeCompl :=
    Submonoid.mul_mem _ (Submonoid.prod_mem _ fun u _ => hgI u)
      (Submonoid.prod_mem _ fun v _ => hgJ v)
  refine ⟨G, hGmem, le_antisymm ?_ ?_⟩
  · rw [← htI, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ tI := Finset.mem_coe.mp hu
    have huI : u ∈ I := by
      rw [← htI]
      exact Ideal.subset_span hu
    have hGeq : G = gI u * ((∏ z ∈ tI.erase u, gI z) * ∏ v ∈ tJ, gJ v) := by
      show (∏ z ∈ tI, gI z) * (∏ v ∈ tJ, gJ v) = _
      rw [← Finset.mul_prod_erase tI gI hu']
      ring
    exact algebraMap_mem_map_of_mul_mem G (Localization.Away G) J (gI u)
      ((∏ z ∈ tI.erase u, gI z) * ∏ v ∈ tJ, gJ v) u hGeq (hgIu u huI)
  · rw [← htJ, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ tJ := Finset.mem_coe.mp hv
    have hvJ : v ∈ J := by
      rw [← htJ]
      exact Ideal.subset_span hv
    have hGeq : G = gJ v * ((∏ u ∈ tI, gI u) * ∏ z ∈ tJ.erase v, gJ z) := by
      show (∏ u ∈ tI, gI u) * (∏ z ∈ tJ, gJ z) = _
      rw [← Finset.mul_prod_erase tJ gJ hv']
      ring
    exact algebraMap_mem_map_of_mul_mem G (Localization.Away G) I (gJ v)
      ((∏ u ∈ tI, gI u) * ∏ z ∈ tJ.erase v, gJ z) v hGeq (hgJu v hvJ)

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

section

namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]

section

variable [Algebra (MvPolynomial ι k) S]

noncomputable def coord (i : ι) : S := algebraMap (MvPolynomial ι k) S (MvPolynomial.X i)

theorem coord_def (i : ι) :
    coord k ι S i = algebraMap (MvPolynomial ι k) S (MvPolynomial.X i) := rfl

end

section

variable [Algebra (MvPolynomial ι k) S] [Algebra k S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]

include ι

theorem exists_basisKaehler :
    ∃ b : Module.Basis ι S (KaehlerDifferential k S),
      ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i) := by
  have h : IsBaseChange S (KaehlerDifferential.map k k (MvPolynomial ι k) S) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale k (MvPolynomial ι k) S
  refine ⟨(Algebra.TensorProduct.basis S
    (KaehlerDifferential.mvPolynomialBasis k ι)).map h.equiv, fun i => ?_⟩
  simp only [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, IsBaseChange.equiv_tmul, one_smul,
    KaehlerDifferential.map_D]
  rfl

noncomputable def basisKaehler : Module.Basis ι S (KaehlerDifferential k S) :=
  (exists_basisKaehler k ι S).choose

@[simp] theorem basisKaehler_apply (i : ι) :
    basisKaehler k ι S i = KaehlerDifferential.D k S (coord k ι S i) :=
  (exists_basisKaehler k ι S).choose_spec i

noncomputable def partialDeriv (i : ι) : Derivation k S S :=
  ((basisKaehler k ι S).coord i).compDer (KaehlerDifferential.D k S)

noncomputable def partialDerivLinear (i : ι) : S →ₗ[k] S :=
  (partialDeriv k ι S i).toLinearMap

theorem partialLinear_leibniz (i : ι) :
    ∀ a b : S, partialDerivLinear k ι S i (a * b)
      = a • partialDerivLinear k ι S i b + b • partialDerivLinear k ι S i a :=
  (partialDeriv k ι S i).leibniz

theorem partialDeriv_apply (i : ι) (s : S) :
    partialDeriv k ι S i s = (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i := rfl

@[simp] theorem partialDeriv_coord [DecidableEq ι] (i j : ι) :
    partialDeriv k ι S i (coord k ι S j) = if i = j then (1 : S) else 0 := by
  rw [partialDeriv_apply, ← basisKaehler_apply k ι S j, Module.Basis.repr_self,
    Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

theorem partialDeriv_coord_self (i : ι) :
    partialDeriv k ι S i (coord k ι S i) = 1 := by
  rw [partialDeriv_apply, ← basisKaehler_apply k ι S i, Module.Basis.repr_self,
    Finsupp.single_eq_same]

theorem partialDeriv_coord_of_ne (i j : ι) (h : i ≠ j) :
    partialDeriv k ι S i (coord k ι S j) = 0 := by
  classical
  rw [partialDeriv_coord k ι S i j, ite_eq_right h]

omit [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S] in
private theorem sum_smul_derivation_apply (c : ι → S) (f : ι → Derivation k S S)
    (s : S) (t : Finset ι) :
    (∑ i ∈ t, c i • f i) s = ∑ i ∈ t, c i * f i s := by
  induction t using Finset.cons_induction_on
  · simp
  · rename_i a u hu ih
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    rfl

theorem eq_sum_smul_partialDeriv [Fintype ι] (D : Derivation k S S) :
    D = ∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i := by
  ext s
  have hsum : (∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i) s
      = ∑ i : ι, D (coord k ι S i) * partialDeriv k ι S i s :=
    sum_smul_derivation_apply k ι S (fun i => D (coord k ι S i))
      (partialDeriv k ι S) s Finset.univ
  rw [hsum]
  have h1 : D s = D.liftKaehlerDifferential (KaehlerDifferential.D k S s) := by
    rw [Derivation.liftKaehlerDifferential_comp_D]
  have h2 : KaehlerDifferential.D k S s
      = ∑ i : ι, (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i
          • basisKaehler k ι S i :=
    ((basisKaehler k ι S).sum_repr (KaehlerDifferential.D k S s)).symm

  rw [h1, h2, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, basisKaehler_apply, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul,
    ← partialDeriv_apply]
  exact mul_comm _ _

theorem span_range_partialDeriv [Finite ι] :
    Submodule.span S (Set.range (partialDeriv k ι S)) = (⊤ : Submodule S (Derivation k S S)) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  refine Submodule.eq_top_iff'.mpr fun D => ?_
  rw [eq_sum_smul_partialDeriv k ι S D]
  exact sum_mem fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end
