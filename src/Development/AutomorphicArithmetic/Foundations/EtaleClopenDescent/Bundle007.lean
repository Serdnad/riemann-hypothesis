module

public import Development.EtaleCohomology.EtaleSheaves.Bundle076
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle024
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle002
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IntegralClosureRangeIsLocalizationIdempotent
public import Development.EtaleCohomology.EtaleSheaves.Bundle077
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut TopologicalSpace

namespace UpperTheory.Cb

private def rho (R : Type) [CommRing R] (V : (Spec (CommRingCat.of R)).Opens) : R →+* Γ(Spec (CommRingCat.of R), V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom

private theorem away_rho (R : Type) [CommRing R] (f : R) (V : (Spec (CommRingCat.of R)).Opens)
    (hV : ((show Opens (PrimeSpectrum R) from V) : Set (PrimeSpectrum R)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) :
    @IsLocalization.Away R _ f Γ(Spec (CommRingCat.of R), V) _ (rho R V).toAlgebra := by
  have hb : V = (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f) := by
    rw [basicOpen_eq_of_affine]
    exact Opens.ext hV
  have h := (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_of_eq_basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f) (homOfLE le_top : V ⟶ ⊤) hb
  let φ : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI := ((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom.toAlgebra
  have h2 := (IsLocalization.isLocalization_iff_of_base_ringEquiv (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)) Γ(Spec (CommRingCat.of R), V) φ.symm).1 h
  have hp : Submonoid.map φ.symm (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)) = Submonoid.powers f := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (φ.symm_apply_apply f)
  rw [hp] at h2
  exact h2

private theorem loc_part {W : Type} [CommRing W] (hW : ProdACF W) (q : PrimeSpectrum W)
    (V : (Spec (CommRingCat.of W)).Opens) (hV : IsCompact (V : Set (Spec (CommRingCat.of W)))) :
    ∃ S : Submonoid Γ(Spec (CommRingCat.of W), V), (∀ s ∈ S, IsIdempotentElem s) ∧
      @IsLocalization _ _ S
        Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)),
          Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ⁻¹ᵁ V) _
        (Scheme.Hom.app (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))) V).hom.toAlgebra := by
  obtain ⟨e, he, hVe⟩ := UpperTheory.isCompact_open_eq_basicOpen_idempotent_of_prodACF hW V hV
  obtain ⟨T, hT, hTL⟩ := UpperTheory.exists_idempotent_submonoid_isLocalization_atPrime hW q
  let j := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  letI : Algebra W Γ(Spec (CommRingCat.of W), V) := (rho W V).toAlgebra
  letI : Algebra (Localization.AtPrime q.asIdeal) Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)), j ⁻¹ᵁ V) :=
    (rho _ (j ⁻¹ᵁ V)).toAlgebra
  haveI : IsLocalization.Away e Γ(Spec (CommRingCat.of W), V) := away_rho W e V hVe
  haveI : IsLocalization.Away (algebraMap W (Localization.AtPrime q.asIdeal) e)
      Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)), j ⁻¹ᵁ V) := by
    refine away_rho (Localization.AtPrime q.asIdeal) (algebraMap W (Localization.AtPrime q.asIdeal) e) (j ⁻¹ᵁ V) ?_
    ext x
    have := Set.ext_iff.1 hVe (PrimeSpectrum.comap (algebraMap W (Localization.AtPrime q.asIdeal)) x)
    exact this
  refine UpperTheory.exists_idempotent_submonoid_isLocalization_away (L := Localization.AtPrime q.asIdeal) e he T (fun s hs => (hT s hs).1) (j.app V).hom ?_
  intro r
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  have key : (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫
      (Spec (CommRingCat.of W)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op ≫ j.app V =
      CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime q.asIdeal))).inv ≫
        (Spec (CommRingCat.of (Localization.AtPrime q.asIdeal))).presheaf.map (homOfLE le_top : j ⁻¹ᵁ V ⟶ ⊤).op := by
    rw [j.naturality, reassoc_of% h1]
    rfl
  exact congr($key r)

private theorem sec_part {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] {U : Y.Opens} (hU : IsAffineOpen U)
    (hle : f ⁻¹ᵁ U ≤ f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U)) :
    Function.Injective (f.toNormalization.appLE _ _ hle).hom ∧
    ∀ b, b ∈ (f.toNormalization.appLE _ _ hle).hom.range ↔ (f.app U).hom.IsIntegralElem b := by
  letI := (f.app U).hom.toAlgebra
  have h := f.normalizationObjIso_hom_val hU
  have h2 : f.toNormalization.appLE _ _ hle = _ := h.symm
  rw [h2]
  have hb := ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).hom
  constructor
  · intro x y hxy
    exact hb.1 (Subtype.ext hxy)
  · intro b
    constructor
    · rintro ⟨x, rfl⟩
      exact ((f.normalizationObjIso hU).hom.hom x).2
    · intro hbi
      obtain ⟨x, hx⟩ := hb.2 ⟨b, hbi⟩
      exact ⟨x, congrArg Subtype.val hx⟩

private theorem hleN {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (U : Y.Opens) :
    f ⁻¹ᵁ U ≤ f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) := by
  have h : f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) = f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
  exact h.ge

private theorem appLE_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

end UpperTheory.Cb

theorem UpperTheory.Cb.etale_finite_presentation_model_exists :
    LateralTheory.E.BuildCut.LimInt → LateralTheory.E.t_E2Cut.Cont → LateralTheory.E.t_E2Cut.MV → LateralTheory.E.SysFMPf.FMex := by
  intro _ _ _ P _ _ W _ w hW q
  let j := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  let m := GlobalTheory.normalizationLift (j ≫ w) (j ≫ w.toNormalization) w.fromNormalization (𝟙 P) (by simp)
  have e1 : j ≫ w.toNormalization = (j ≫ w).toNormalization ≫ m :=
    (GlobalTheory.toNormalization_normalizationLift _ _ _ _ _).symm
  have e2 : m ≫ w.fromNormalization = (j ≫ w).fromNormalization :=
    (GlobalTheory.normalizationLift_comp (j ≫ w) (j ≫ w.toNormalization) w.fromNormalization (𝟙 P) (by simp)).trans
      (Category.comp_id _)
  have hmi : IsIntegralHom m := GlobalTheory.isIntegralHom_normalizationLift _ _ _ _ _
  obtain ⟨hmono, hflat⟩ := UpperTheory.mono_flat_of_affine_appLE_flat_epi w.fromNormalization (j ≫ w).fromNormalization m e2 (fun U hU hle => by
    obtain ⟨S, hS, hL⟩ := loc_part hW q (w ⁻¹ᵁ U) (w.isCompact_preimage hU.isCompact)
    obtain ⟨ht, hr⟩ := sec_part w hU (hleN w U)
    obtain ⟨ht', hr'⟩ := sec_part (j ≫ w) hU (hleN (j ≫ w) U)
    have key : w.toNormalization.appLE _ _ (hleN w U) ≫ j.app (w ⁻¹ᵁ U) =
        m.appLE _ _ hle ≫ (j ≫ w).toNormalization.appLE _ _ (hleN (j ≫ w) U) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq e1 _ _ _
    refine UpperTheory.integralClosure_range_isLocalization_idempotent (w.app U).hom (j.app (w ⁻¹ᵁ U)).hom _ _ _ ht ht' hr (fun b => (hr' b).trans Iff.rfl) ?_ S hS hL
    intro c
    exact congr($key c))
  exact ⟨m, e1, e2, hmono, hflat, inferInstance⟩

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf
  LateralTheory.E.LeafGlueIsProperPf

namespace UpperTheory.Cb

private lemma ringLift {Q R K : Type} [CommRing Q] [CommRing R] [CommRing K] (j : R →+* K)
    (hj : Function.Injective j) (ψ : Q →+* K) (h : ∀ q, ψ q ∈ j.range) :
    ∃ g : Q →+* R, j.comp g = ψ := by
  let e : R ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b hab => hj (congrArg Subtype.val hab), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict j.range h), ?_⟩
  ext q
  change ((e (e.symm (ψ.codRestrict j.range h q)) : j.range) : K) = ψ q
  rw [e.apply_symm_apply]
  rfl

private lemma compat {X : Scheme.{0}} {Ω Q : Type} [Field Ω] [CommRing Q] [Algebra Ω Q]
    (c : X ⟶ Sp Ω) (i : Sp Q ⟶ X)
    (hc : i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    (S : ValuativeCommSq c) (ψ : Q →+* S.K)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ i = S.i₁)
    (w : CommRingCat.of Ω ⟶ CommRingCat.of S.R) (hw : Spec.map w = S.i₂) :
    ψ.comp (algebraMap Ω Q) = (algebraMap S.R S.K).comp w.hom := by
  have h1 := S.commSq.w
  rw [← hψ, ← hw, Category.assoc, hc, ← Spec.map_comp, ← Spec.map_comp] at h1
  have h2 := Spec.map_injective h1
  ext a
  have h3 := congrArg (fun f => f.hom a) h2
  simpa using h3

private lemma closeSq {X : Scheme.{0}} {Ω Q : Type} [Field Ω] [CommRing Q] [Algebra Ω Q]
    (c : X ⟶ Sp Ω) (i : Sp Q ⟶ X)
    (hc : i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    (S : ValuativeCommSq c) (ψ : Q →+* S.K)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ i = S.i₁)
    (hR : ∀ q, ψ q ∈ (algebraMap S.R S.K).range) : S.commSq.HasLift := by
  have hinj : Function.Injective (algebraMap S.R S.K) := IsFractionRing.injective S.R S.K
  obtain ⟨g, hg⟩ := ringLift (algebraMap S.R S.K) hinj ψ hR
  have hw : Spec.map (Spec.preimage S.i₂) = S.i₂ := Spec.map_preimage _
  have hcomp := compat c i hc S ψ hψ (Spec.preimage S.i₂) hw
  have hgψ : CommRingCat.ofHom g ≫ CommRingCat.ofHom (algebraMap S.R S.K) = CommRingCat.ofHom ψ := by
    rw [← CommRingCat.ofHom_comp, hg]
  refine ⟨⟨⟨Spec.map (CommRingCat.ofHom g) ≫ i, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, ← Spec.map_comp, hgψ, hψ]
  · rw [Category.assoc, hc, ← Spec.map_comp, ← hw]
    congr 1
    ext a
    apply hinj
    have h1 := congrArg (fun f => f a) hcomp
    have h2 := congrArg (fun f => f (algebraMap Ω Q a)) hg
    simp only [RingHom.comp_apply] at h1 h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [h2, h1]

private lemma closedCase {Ω P R K : Type} [Field Ω] [CommRing P] [IsDomain P] [Algebra Ω P]
    [Algebra.FiniteType Ω P] (hd : ringKrullDim P = 1) [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (ω : Ω →+* R) (ψ : P →+* K)
    (hω : ψ.comp (algebraMap Ω P) = (algebraMap R K).comp ω)
    (hker : ¬ Function.Injective ψ) (q : P) : ψ q ∈ (algebraMap R K).range := by
  haveI hdim : Ring.KrullDimLE 1 P := by
    rw [Ring.krullDimLE_iff, hd]
    rfl
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hne : RingHom.ker ψ ≠ ⊥ := fun h => hker ((RingHom.injective_iff_ker_eq_bot ψ).mpr h)
  haveI : (RingHom.ker ψ).IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot ‹_› hne
  letI : Field (P ⧸ RingHom.ker ψ) := Ideal.Quotient.field _
  haveI : Module.Finite Ω (P ⧸ RingHom.ker ψ) :=
    finite_of_finite_type_of_isJacobsonRing Ω (P ⧸ RingHom.ker ψ)
  obtain ⟨p, hmon, hp⟩ : IsIntegral Ω (Ideal.Quotient.mk (RingHom.ker ψ) q) :=
    Algebra.IsIntegral.isIntegral _
  have hpq : Polynomial.aeval q p ∈ RingHom.ker ψ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk Ω,
      ← Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Polynomial.aeval_def]
    exact hp
  rw [RingHom.mem_ker, Polynomial.aeval_def, Polynomial.hom_eval₂, hω,
    ← Polynomial.eval₂_map] at hpq
  have hi : IsIntegral R (ψ q) := ⟨p.map ω, hmon.map ω, hpq⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact ⟨y, hy⟩

private lemma genericVal {Ω L R K : Type} [Field Ω] [Field L] [Algebra Ω L] [CommRing R] [IsDomain R]
    [ValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ω : Ω →+* R) (f : L →+* K)
    (h : f.comp (algebraMap Ω L) = (algebraMap R K).comp ω) :
    ∃ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) ∧
      ∀ x ∈ V, f x ∈ (algebraMap R K).range := by
  let V : ValuationSubring L :=
    { (algebraMap R K).range.comap f with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger R (f x) with hx | hx
        · left
          obtain ⟨y, hy⟩ := hx
          exact ⟨y, hy⟩
        · right
          obtain ⟨y, hy⟩ := hx
          refine ⟨y, ?_⟩
          change algebraMap R K y = f x⁻¹
          rw [map_inv₀]
          exact hy }
  refine ⟨V, fun a => ?_, fun x hx => hx⟩
  refine ⟨ω a, ?_⟩
  have h1 := congrArg (fun g => g a) h
  simp only [RingHom.comp_apply] at h1
  exact h1.symm

private lemma chart {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {X : Scheme.{0}}
    (c : X ⟶ Sp Ω) (P Q : Subalgebra Ω L) (iP : Sp P ⟶ X) (iQ : Sp Q ⟶ X)
    (hP : iP ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω P)))
    (hQ : iQ ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    [Algebra.FiniteType Ω P] (hd : ringKrullDim P = 1) [IsFractionRing P L]
    (hV : ∀ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) →
      (P : Set L) ⊆ V ∨ (Q : Set L) ⊆ V)
    (hag : ∀ (K : Type) [Field K] (f : L →+* K),
      Spec.map (CommRingCat.ofHom (f.comp (algebraMap P L))) ≫ iP =
        Spec.map (CommRingCat.ofHom (f.comp (algebraMap Q L))) ≫ iQ)
    (S : ValuativeCommSq c) (φ : P →+* S.K)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ iP = S.i₁) : S.commSq.HasLift := by
  have hw : Spec.map (Spec.preimage S.i₂) = S.i₂ := Spec.map_preimage _
  have hcomp := compat c iP hP S φ hφ (Spec.preimage S.i₂) hw
  by_cases hinj : Function.Injective φ
  · let f : L →+* S.K := IsFractionRing.lift hinj
    have hf : f.comp (algebraMap P L) = φ :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    have hfΩ : f.comp (algebraMap Ω L) =
        (algebraMap S.R S.K).comp (Spec.preimage S.i₂).hom := by
      rw [IsScalarTower.algebraMap_eq Ω P L, ← RingHom.comp_assoc, hf, hcomp]
    obtain ⟨V, hΩV, hVR⟩ := genericVal (Spec.preimage S.i₂).hom f hfΩ
    rcases hV V hΩV with hPV | hQV
    · refine closeSq c iP hP S φ hφ fun q => ?_
      rw [← hf]
      exact hVR _ (hPV q.2)
    · have hψ : Spec.map (CommRingCat.ofHom (f.comp (algebraMap Q L))) ≫ iQ = S.i₁ := by
        rw [← hag S.K f, hf, hφ]
      exact closeSq c iQ hQ S _ hψ fun q => hVR _ (hQV q.2)
  · exact closeSq c iP hP S φ hφ (closedCase hd (Spec.preimage S.i₂).hom φ hcomp hinj)

end UpperTheory.Cb

open UpperTheory.Cb in
theorem UpperTheory.Cb.properGluing_existence :
    LateralTheory.E.LeafGlueIsProperPf.LeafGlueExistence := by
  intro Ω L _ _ _ A B u h G S
  obtain ⟨-, -, -, hfA, hfB, -, -, hdA, hdB, hFA, hFB, hadj, hV⟩ := h
  haveI := hfA
  haveI := hfB
  haveI := hFA
  haveI := hFB
  haveI := G.hiA
  haveI := G.hiB
  have hagA : ∀ (K : Type) [Field K] (f : L →+* K),
      Spec.map (CommRingCat.ofHom (f.comp (algebraMap A L))) ≫ G.iA =
        Spec.map (CommRingCat.ofHom (f.comp (algebraMap B L))) ≫ G.iB := by
    intro K _ f
    have eA : f.comp (algebraMap A L) = (f.comp (algebraMap (Dr Ω A u) L)).comp
        (Subalgebra.inclusion (le_Dr_A A u)).toRingHom := by
      ext x
      rfl
    have eB : f.comp (algebraMap B L) = (f.comp (algebraMap (Dr Ω A u) L)).comp
        (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom := by
      ext x
      rfl
    rw [eA, eB]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, G.agree]
  obtain ⟨x0⟩ : Nonempty (Spec (CommRingCat.of S.K)) := inferInstance
  have hx : S.i₁ x0 ∈ Set.range G.iA ∪ Set.range G.iB := by
    rw [G.cover]
    trivial
  rcases hx with hA | hB
  · have hr : Set.range S.i₁ ⊆ Set.range G.iA := by
      rintro _ ⟨y, rfl⟩
      rwa [Subsingleton.elim y x0]
    have hg := IsOpenImmersion.lift_fac G.iA S.i₁ hr
    refine chart G.c0 A B G.iA G.iB G.hcA G.hcB hdA hV hagA S
      (Spec.preimage (IsOpenImmersion.lift G.iA S.i₁ hr)).hom ?_
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]
  · have hr : Set.range S.i₁ ⊆ Set.range G.iB := by
      rintro _ ⟨y, rfl⟩
      rwa [Subsingleton.elim y x0]
    have hg := IsOpenImmersion.lift_fac G.iB S.i₁ hr
    refine chart G.c0 B A G.iB G.iA G.hcB G.hcA hdB (fun V hV' => (hV V hV').symm)
      (fun K _ f => (hagA K f).symm) S
      (Spec.preimage (IsOpenImmersion.lift G.iB S.i₁ hr)).hom ?_
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]
end
end
