module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle003
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionData
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private noncomputable def extendAlgHomLastVarZero {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] A) :
    MvPolynomial (ULift.{u} (Fin (n + 1))) k →ₐ[k] A :=
  MvPolynomial.aeval fun i : ULift.{u} (Fin (n + 1)) =>
    Fin.lastCases (motive := fun _ => A) 0 (fun j => f (MvPolynomial.X j)) i.down

private theorem extension_X_last_eq_zero {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] A) :
    extendAlgHomLastVarZero f (MvPolynomial.X (ULift.up (Fin.last n))) = 0 := by
  simp [extendAlgHomLastVarZero]

private theorem extension_surjective {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f) :
    Function.Surjective (extendAlgHomLastVarZero f) := by
  intro a
  obtain ⟨q, rfl⟩ := hf a
  refine ⟨MvPolynomial.rename
    (fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1)))) q, ?_⟩
  show MvPolynomial.aeval (fun i : ULift.{u} (Fin (n + 1)) =>
      Fin.lastCases (motive := fun _ => A) 0 (fun j => f (MvPolynomial.X j)) i.down)
      (MvPolynomial.rename (fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1)))) q)
      = f q
  rw [MvPolynomial.aeval_rename]
  have h : ((fun i : ULift.{u} (Fin (n + 1)) =>
      Fin.lastCases (motive := fun _ => A) 0 (fun j => f (MvPolynomial.X j)) i.down) ∘
      fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1))))
      = fun j : Fin n => f (MvPolynomial.X j) := by
    funext j
    simp
  rw [h]
  exact DFunLike.congr_fun (MvPolynomial.aeval_unique f).symm q

private noncomputable def toAffineSpaceOfAlgHom {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    {m : Type u} [Algebra k ↥Γ(Y, ⊤)] (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤)) :
    Y ⟶ affineSpaceIndexedBy k m :=
  Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    (AffineSpace.SpecIso m (CommRingCat.of k)).inv

private theorem isoSpec_hom_comp_spec_map_appTop {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) :
    Y.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop) = p := by
  have h2 : Y.isoSpec.hom = Y.toSpecΓ := rfl
  rw [h2, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality p,
    ← SpecMap_ΓSpecIso_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

private theorem isClosedImmersion_embedding_and_comp_eq {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    {m : Type u} [Algebra k ↥Γ(Y, ⊤)] (p : Y ⟶ Spec (CommRingCat.of k))
    (halg : algebraMap k ↥Γ(Y, ⊤)
      = (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom))
    (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤)) (hg : Function.Surjective g) :
    IsClosedImmersion (toAffineSpaceOfAlgHom Y g) ∧
      toAffineSpaceOfAlgHom Y g ≫ (affineSpaceIndexedBy k m ↘ Spec (CommRingCat.of k)) = p := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  constructor
  · show IsClosedImmersion (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv)
    infer_instance
  · show (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv) ≫
      (affineSpaceIndexedBy k m ↘ Spec (CommRingCat.of k)) = p
    rw [Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
    have h2 : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial m k) ≫
        CommRingCat.ofHom g.toRingHom
        = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop := by
      refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
      show g (MvPolynomial.C a) = _
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, halg]
    rw [h2]
    exact isoSpec_hom_comp_spec_map_appTop Y p

private theorem isIrreducible_univ_affineSpaceIndexedBy (k : Type u) [Field k] (m : Type u) :
    IsIrreducible (Set.univ : Set ↥(affineSpaceIndexedBy k m)) := by
  have h0 : IsIrreducible (Set.univ : Set ↥(Spec (CommRingCat.of (MvPolynomial m k)))) :=
    IrreducibleSpace.isIrreducible_univ (PrimeSpectrum (MvPolynomial m k))
  have h1 := h0.image (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm)
    (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm).continuous.continuousOn
  rwa [Set.image_univ,
    (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm).surjective.range_eq] at h1

private theorem eq_univ_of_mem_irreducibleComponents_of_isIrreducible_univ {X : Type u} [TopologicalSpace X]
    (h : IsIrreducible (Set.univ : Set X)) {T : Set X} (hT : T ∈ irreducibleComponents X) :
    T = Set.univ :=
  Set.eq_univ_of_univ_subset (hT.2 h (Set.subset_univ T))

private theorem support_ker_ne_univ_of_map_X_eq_zero {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    {m : Type u} [Algebra k ↥Γ(Y, ⊤)] (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤))
    (x₀ : m) (hx₀ : g (MvPolynomial.X x₀) = 0) [QuasiCompact (toAffineSpaceOfAlgHom Y g)] :
    ((toAffineSpaceOfAlgHom Y g).ker.support : Set ↥(affineSpaceIndexedBy k m)) ≠ Set.univ := by
  intro hcon
  have hcomp : toAffineSpaceOfAlgHom Y g ≫ (AffineSpace.SpecIso m (CommRingCat.of k)).hom
      = Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) := by
    show (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).hom = _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmem0 : ∀ w : PrimeSpectrum ↥Γ(Y, ⊤),
      (MvPolynomial.X x₀ : MvPolynomial m k) ∈
        ((Spec.map (CommRingCat.ofHom g.toRingHom)).base w).asIdeal := by
    intro w
    show g (MvPolynomial.X x₀) ∈ w.asIdeal
    rw [hx₀]
    exact Ideal.zero_mem _
  obtain ⟨v, hv, hvcont, hvsurj⟩ :
      ∃ v : ↥(affineSpaceIndexedBy k m) → PrimeSpectrum (MvPolynomial m k),
        (∀ y : ↥Y, v ((toAffineSpaceOfAlgHom Y g).base y)
            = (Spec.map (CommRingCat.ofHom g.toRingHom)).base (Y.isoSpec.hom.base y)) ∧
          Continuous v ∧ Function.Surjective v := by
    refine ⟨fun x => (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))) x, ?_, ?_, ?_⟩
    · intro y
      exact congrArg
        (fun φ : Y ⟶ Spec (CommRingCat.of (MvPolynomial m k)) => φ.base y) hcomp
    · exact (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))).continuous
    · exact (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))).surjective
  have hrange : ∀ y : ↥Y,
      (MvPolynomial.X x₀ : MvPolynomial m k) ∈ (v ((toAffineSpaceOfAlgHom Y g).base y)).asIdeal := by
    intro y
    rw [hv y]
    exact hmem0 _
  have hsub : Set.range (toAffineSpaceOfAlgHom Y g).base ⊆
      v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
    rintro _ ⟨y, rfl⟩
    have : v ((toAffineSpaceOfAlgHom Y g).base y) ∈
        PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact hrange y
    exact this
  have hsupp : ((toAffineSpaceOfAlgHom Y g).ker.support : Set ↥(affineSpaceIndexedBy k m))
      = closure (Set.range (toAffineSpaceOfAlgHom Y g).base) := Scheme.Hom.support_ker _
  have huniv : (Set.univ : Set ↥(affineSpaceIndexedBy k m)) ⊆
      v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
    rw [← hcon, hsupp]
    exact closure_minimal hsub ((PrimeSpectrum.isClosed_zeroLocus _).preimage hvcont)
  obtain ⟨ξ, hξ⟩ := hvsurj ⟨⊥, Ideal.isPrime_bot⟩
  have hmem : ξ ∈ v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} :=
    huniv (Set.mem_univ ξ)
  rw [Set.mem_preimage, hξ, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hmem
  have h6 : (MvPolynomial.X x₀ : MvPolynomial m k) = 0 := Ideal.mem_bot.mp hmem
  have h7 : (1 : k) = 0 := by
    have h8 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single x₀ 1)) h6
    simp at h8
  exact one_ne_zero h7

theorem affineEmbedsIntoAffineSpace : AffineEmbedsIntoAffineSpace.{u} := by
  intro k _ Y _ p _
  have hft : RingHom.FiniteType (p.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := p)).mp inferInstance
  have hiso : Function.Surjective ⇑((Scheme.ΓSpecIso (CommRingCat.of k)).inv) := by
    intro x
    exact ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom x, by simp⟩
  have hφ : RingHom.FiniteType
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom) := by
    rw [CommRingCat.hom_comp]
    exact hft.comp (RingHom.FiniteType.of_surjective _ hiso)
  let _ : Algebra k ↥Γ(Y, ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom).toAlgebra
  have halg : algebraMap k ↥Γ(Y, ⊤)
      = (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom) := rfl
  have hfta : Algebra.FiniteType k ↥Γ(Y, ⊤) := hφ
  obtain ⟨n, f, hfsurj⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp hfta
  obtain ⟨hci, hover⟩ := isClosedImmersion_embedding_and_comp_eq Y p halg (extendAlgHomLastVarZero f) (extension_surjective f hfsurj)
  have := hci
  refine ⟨n + 1, toAffineSpaceOfAlgHom Y (extendAlgHomLastVarZero f), hci, ?_, hover⟩
  have hne := support_ker_ne_univ_of_map_X_eq_zero Y (extendAlgHomLastVarZero f) (ULift.up (Fin.last n)) (extension_X_last_eq_zero f)
  have hirr := isIrreducible_univ_affineSpaceIndexedBy k (ULift.{u} (Fin (n + 1)))
  have key : ∀ T ∈ irreducibleComponents ↥(affineSpaceIndexedBy k (ULift.{u} (Fin (n + 1)))),
      ¬ T ⊆ ((toAffineSpaceOfAlgHom Y (extendAlgHomLastVarZero f)).ker.support :
        Set ↥(affineSpaceIndexedBy k (ULift.{u} (Fin (n + 1))))) := by
    intro T hT hsubT
    refine hne (Set.eq_univ_of_univ_subset ?_)
    rw [← eq_univ_of_mem_irreducibleComponents_of_isIrreducible_univ hirr hT]
    exact hsubT
  exact key

end FunctorialResolution.EmbeddedResolution
end

section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem algebra_smooth_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    Algebra.Smooth k (MvPolynomial (ULift.{u} (Fin n)) k) :=
  ⟨inferInstance, inferInstance⟩

private theorem ringHom_smooth_algebraMap_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    RingHom.Smooth (algebraMap k (MvPolynomial (ULift.{u} (Fin n)) k)) :=
  RingHom.smooth_algebraMap.mpr (algebra_smooth_mvPolynomial k n)

private theorem specIso_inv_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n : ℕ) :
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k)) :=
  AffineSpace.SpecIso_inv_over _

private theorem affineSpaceIndexedByToSpec_eq (k : Type u) [Field k] (n : ℕ) :
    affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k)) := by
  rw [← specIso_inv_comp_affineSpaceIndexedByToSpec k n, Iso.hom_inv_id_assoc]

theorem affineSpaceIsSmooth : AffineSpaceIsSmooth.{u} := by
  intro k _ n
  have hC : AlgebraicGeometry.Smooth
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k))) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Smooth)).mpr (ringHom_smooth_algebraMap_mvPolynomial k n)
  rw [affineSpaceIndexedByToSpec_eq k n]
  infer_instance

theorem nilIsStrictNormalCrossingsOnAffineSpace : NilIsStrictNormalCrossingsOnAffineSpace.{u} := by
  intro k _ n
  refine ⟨by simp, fun x => ⟨⊤, trivial, n,
    ⟨(⊤ : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens).ι, rfl, ?_⟩,
    fun _ => none, by simp, by simp, by simp⟩⟩
  infer_instance

end FunctorialResolution.EmbeddedResolution
end

section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

private theorem support_vanishingIdeal_eq {Y : Scheme.{u}} (Z : Closeds ↥Y) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := rfl

private theorem comap_vanishingIdeal_of_isOpenImmersion {Y T : Scheme.{u}} (g : T ⟶ Y)
    [IsOpenImmersion g] (Z : Closeds ↥Y) (W : Closeds ↥T)
    (hW : (W : Set ↥T) = g.base ⁻¹' (Z : Set ↥Y)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap g
      = Scheme.IdealSheafData.vanishingIdeal W := by
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap g).radical
      = (Scheme.IdealSheafData.vanishingIdeal Z).comap g := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    rw [Scheme.IdealSheafData.radical_ideal,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact ((PrimeSpectrum.isRadical_vanishingIdeal _).comap _).radical
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap g).support = W := by
    rw [Scheme.IdealSheafData.support_comap, support_vanishingIdeal_eq]
    exact TopologicalSpace.Closeds.ext hW.symm
  rw [← hsupp, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

private theorem isRegularParameterSystem_map_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : Fin n → R)
    (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n (fun i => e (x i)) := by
  unfold IsRegularParameterSystem at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor
  · have hmax : Ideal.comap (e : R →+* S) (IsLocalRing.maximalIdeal S)
        = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective (e : R →+* S) e.surjective)
    have hm : Ideal.map (e : R →+* S) (IsLocalRing.maximalIdeal R)
        = IsLocalRing.maximalIdeal S := by
      rw [← hmax]
      exact Ideal.map_comap_of_surjective (e : R →+* S) e.surjective _
    have himg : Ideal.span (Set.range fun i => e (x i))
        = Ideal.map (e : R →+* S) (Ideal.span (Set.range x)) := by
      rw [Ideal.map_span]
      congr 1
      ext b
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [himg, h1, hm]
  · rw [h2]
    exact ringKrullDim_eq_of_ringEquiv e

private theorem isRegularParameterSystem_of_ringEquiv_apply_eq {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : Fin n → R) (y : Fin n → S)
    (hxy : ∀ i, e (x i) = y i) (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n y := by
  have hy : y = fun i => e (x i) := (funext fun i => hxy i).symm
  subst hy
  exact isRegularParameterSystem_map_ringEquiv e n x h

private theorem surjective_iso_inv {A B : CommRingCat.{u}} (e : A ≅ B) :
    Function.Surjective (CommRingCat.Hom.hom e.inv) := by
  intro a
  refine ⟨(CommRingCat.Hom.hom e.hom) a, ?_⟩
  simp

private theorem map_eqToHom_germ {T : Scheme.{u}} {U V : T.Opens}
    (h : Opposite.op U = Opposite.op V) (z : ↥T) (hz : z ∈ U) (hz' : z ∈ V) :
    T.presheaf.map (eqToHom h) ≫ T.presheaf.germ V z hz' = T.presheaf.germ U z hz := by
  have h' : U = V := congrArg Opposite.unop h
  subst h'
  simp

private theorem appIso_inv_germ_stalkMap {Y T : Scheme.{u}} (g : T ⟶ Y) [IsOpenImmersion g]
    (U : T.Opens) (z : ↥T) (hz : z ∈ U) (hgz : g.base z ∈ (g ''ᵁ U : Y.Opens)) :
    (Scheme.Hom.appIso g U).inv ≫ Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz ≫
        Scheme.Hom.stalkMap g z = T.presheaf.germ U z hz := by
  have h1 : Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz ≫ Scheme.Hom.stalkMap g z
      = Scheme.Hom.app g (g ''ᵁ U) ≫ T.presheaf.germ (g ⁻¹ᵁ (g ''ᵁ U)) z hgz :=
    Scheme.Hom.germ_stalkMap g (g ''ᵁ U) z hgz
  rw [h1, ← Category.assoc]
  simp
  exact map_eqToHom_germ _ z hz hgz

private theorem appIso_inv_germ_stalkMap_apply {Y T : Scheme.{u}} (g : T ⟶ Y) [IsOpenImmersion g]
    (U : T.Opens) (z : ↥T) (hz : z ∈ U) (hgz : g.base z ∈ (g ''ᵁ U : Y.Opens))
    (a : Γ(T, U)) :
    (ConcreteCategory.hom (Scheme.Hom.stalkMap g z))
        ((ConcreteCategory.hom (Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz))
          ((ConcreteCategory.hom (Scheme.Hom.appIso g U).inv) a))
      = (ConcreteCategory.hom (T.presheaf.germ U z hz)) a := by
  have h := congrArg (fun m : Γ(T, U) ⟶ T.presheaf.stalk z => (ConcreteCategory.hom m) a)
    (appIso_inv_germ_stalkMap g U z hz hgz)
  simpa only [CommRingCat.comp_apply] using h

theorem chartToLastObj_preimage_smoothLocusComplement (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (d.chartToLastObj i).base ⁻¹'
        (s.lastStructMap.base ⁻¹' ((smoothLocusComplement f : Closeds ↥X) : Set ↥X))
      = (d.seq i).lastStructMap.base ⁻¹'
        ((smoothLocusComplement (d.cover.f i ≫ f) : Closeds ↥(d.cover.X i)) : Set ↥(d.cover.X i)) := by
  have hcomp := d.chartToLastObj_comp_lastStructMap i
  have hsl := d.preimage_smoothLocusComplement_cover_map i
  ext x
  simp only [Set.mem_preimage]
  have hx : s.lastStructMap.base ((d.chartToLastObj i).base x)
      = (d.cover.f i).base ((d.seq i).lastStructMap.base x) := by
    have h := congrArg (fun g : (d.seq i).lastObj ⟶ X => g.base x) hcomp
    simpa using h
  rw [hx, ← Set.mem_preimage, hsl]

theorem comap_reducedInverseImage_chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (reducedInverseImage s.lastStructMap (smoothLocusComplement f)).comap (d.chartToLastObj i)
      = reducedInverseImage (d.seq i).lastStructMap (smoothLocusComplement (d.cover.f i ≫ f)) := by
  have h1 := d.chartToLastObj_preimage_smoothLocusComplement i
  unfold reducedInverseImage
  exact comap_vanishingIdeal_of_isOpenImmersion (d.chartToLastObj i) _ _ h1.symm

private theorem isStrictNormalCrossingsDivisor_of_openCover {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (H : ∀ y : ↥Y, ∃ (T : Scheme.{u}) (g : T ⟶ Y) (_ : IsOpenImmersion g) (z : ↥T),
      g.base z = y ∧ IsStrictNormalCrossingsDivisor (I.comap g)) : IsStrictNormalCrossingsDivisor I := by
  intro y
  obtain ⟨T, g, hg, z, hzy, hSNC⟩ := H y
  subst hzy
  have := hg
  obtain ⟨hreg, U, hzU, n, F, J, hpar, hid⟩ := hSNC z
  have : IsRegularLocalRing ↑(T.presheaf.stalk z) := hreg
  obtain ⟨E, hE⟩ : ∃ E : (↑(Y.presheaf.stalk (g.base z)) : Type u) ≃+* ↑(T.presheaf.stalk z),
      ∀ x, E x = (ConcreteCategory.hom (Scheme.Hom.stalkMap g z)) x :=
    ⟨(asIso (Scheme.Hom.stalkMap g z)).commRingCatIsoToRingEquiv, fun _ => rfl⟩
  have hgz : g.base z ∈ (g ''ᵁ (U : T.Opens) : Y.Opens) := ⟨z, hzU, rfl⟩
  have hVaff : IsAffineOpen (g ''ᵁ (U : T.Opens)) :=
    (U.2 : IsAffineOpen (U : T.Opens)).image_of_isOpenImmersion g
  have hsurj : Function.Surjective
      (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) :=
    surjective_iso_inv (Scheme.Hom.appIso g (U : T.Opens))
  refine ⟨IsRegularLocalRing.of_ringEquiv E.symm,
    ⟨g ''ᵁ (U : T.Opens), hVaff⟩, hgz, n,
    fun i => (ConcreteCategory.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) (F i), J, ?_, ?_⟩
  · refine isRegularParameterSystem_of_ringEquiv_apply_eq E.symm n _ _ ?_ hpar
    intro i
    have hgerm := appIso_inv_germ_stalkMap_apply g (U : T.Opens) z hzU hgz (F i)
    rw [← hE] at hgerm
    rw [← hgerm, E.symm_apply_apply]
  · have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I g U
    rw [hid] at h1
    have h2 : Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
        (Ideal.span {∏ i ∈ J, F i})
        = Ideal.span {∏ i ∈ J,
            (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) (F i)} := by
      rw [Ideal.map_span, Set.image_singleton, map_prod]
    have h3 : Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
        (Ideal.comap (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
          (I.ideal ⟨g ''ᵁ (U : T.Opens), hVaff⟩))
        = I.ideal ⟨g ''ᵁ (U : T.Opens), hVaff⟩ :=
      Ideal.map_comap_of_surjective _ hsurj _
    exact (h3.symm.trans
      (congrArg (Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv))
        h1.symm)).trans h2

theorem isStrictNormalCrossingsDivisor_reducedInverseImage (d : LocalResolutionData k f s) [LocallyOfFinitePresentation f] :
    IsStrictNormalCrossingsDivisor (reducedInverseImage s.lastStructMap (smoothLocusComplement f)) := by
  refine isStrictNormalCrossingsDivisor_of_openCover _ ?_
  intro y
  obtain ⟨i, z, hz⟩ := d.exists_chartToLastObj_eq y
  refine ⟨(d.seq i).lastObj, d.chartToLastObj i, inferInstance, z, hz, ?_⟩
  rw [d.comap_reducedInverseImage_chartToLastObj i]
  exact (d.isResolution i).2.2.2.2.2

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution
end
