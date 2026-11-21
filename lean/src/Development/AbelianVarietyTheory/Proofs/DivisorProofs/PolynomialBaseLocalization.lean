import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsIntClosedLocalizationAndQuotient

/-! # Localizing the base of a polynomial strict henselization -/

namespace GlobalTheory.LocAcyc

open IsLocalRing Polynomial CategoryTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

/-- Precomposing with a ring equivalence preserves strict henselizations. -/
theorem isStrictHenselisation_comp_ringEquiv
    {R R' O : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] [CommRing O] [IsLocalRing O]
    {φ : R →+* O} (h : IsStrictHenselisation φ) (e : R' ≃+* R) :
    IsStrictHenselisation (φ.comp e.toRingHom) := by
  obtain ⟨hh, hs, hlocal, hetale⟩ := h
  refine ⟨hh, hs, ⟨fun a ha => ?_⟩, ?_⟩
  · have hu : IsUnit (e a) := hlocal.map_nonunit _ ha
    simpa using hu.map e.symm
  · haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
      RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
    unfold IsIndEtale at hetale ⊢
    rw [CommRingCat.ofHom_comp]
    haveI : IsIso (CommRingCat.ofHom e.toRingHom) :=
      inferInstanceAs (IsIso e.toCommRingCatIso.hom)
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr hetale

/-- A property that descends from localizations can be proved after localizing the base at the
contraction of the chosen prime of the polynomial algebra. -/
theorem polynomialClaim_of_localization
    (claim : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O], Prop)
    (hlocal : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O]
      [Algebra T O] [Algebra T[X] O] [IsScalarTower T T[X] O], AbsIntClosed T →
      ∀ (P : Ideal T[X]) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
      φ.comp (algebraMap T[X] _) = algebraMap T[X] O → IsStrictHenselisation φ →
      P.comap (C : T →+* T[X]) = maximalIdeal T → claim T O)
    (descends : ∀ (T T' O : Type) [CommRing T] [IsDomain T] [CommRing T'] [CommRing O]
      [Algebra T T'] [Algebra T O] [Algebra T' O] [IsScalarTower T T' O]
      (M : Submonoid T) [IsLocalization M T'], M ≤ nonZeroDivisors T →
      (∀ s : M, IsUnit (algebraMap T O s)) → claim T' O → claim T O)
    (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsLocalRing O]
    [Algebra T O] [Algebra T[X] O] [IsScalarTower T T[X] O] (hAIC : AbsIntClosed T)
    (P : Ideal T[X]) [P.IsPrime] (φ : Localization.AtPrime P →+* O)
    (hφ : φ.comp (algebraMap T[X] _) = algebraMap T[X] O) (hSH : IsStrictHenselisation φ) :
    claim T O := by
  let p : Ideal T := P.comap (C : T →+* T[X])
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2
  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  haveI : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  haveI : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])
  letI : Algebra T[X] T'[X] := Polynomial.algebra T T'
  haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  let P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X])
  haveI hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.comap_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    rw [← IsLocalization.map_comap p.primeCompl T' (P'.comap C),
      ← IsLocalization.map_comap p.primeCompl T' (maximalIdeal T'),
      IsLocalization.AtPrime.comap_maximalIdeal T' p]
    congr 1
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']
  haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  exact descends T T' O p.primeCompl hle hunit
    (hlocal T' O hAIC' P' φ' hφ' (isStrictHenselisation_comp_ringEquiv hSH e.symm.toRingEquiv) hmax)

end GlobalTheory.LocAcyc
