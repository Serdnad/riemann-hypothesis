module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle011
public import Mathlib.RingTheory.Smooth.Locus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSmoothAtOfSmoothQuotientPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.StalkGlue

theorem sec_ext {X : Scheme.{0}} (U : X.Opens) (s t : Γ(X, U))
    (h : ∀ (x : X) (hx : x ∈ U), (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom t) :
    s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t h

theorem germ_map {X : Scheme.{0}} {U V : X.Opens} (i : V ⟶ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom ((X.presheaf.map i.op).hom s) =
      (X.presheaf.germ U x (i.le hx)).hom s :=
  TopCat.Presheaf.germ_res_apply X.presheaf i x hx s

theorem exists_section {X : Scheme.{0}} (U : X.Opens) (g : ∀ (x : X), x ∈ U → X.presheaf.stalk x)
    (H : ∀ x : X, x ∈ U → ∃ (W : X.Opens) (h : W ≤ U) (t : Γ(X, W)), x ∈ W ∧
      ∀ (y : X) (hy : y ∈ W), g y (h hy) = (X.presheaf.germ W y hy).hom t) :
    ∃ s : Γ(X, U), ∀ (x : X) (hx : x ∈ U), (X.presheaf.germ U x hx).hom s = g x hx := by
  choose W hW t hx ht using H
  have hcov : U ≤ iSup (fun p : U => W p.1 p.2) := fun x hxU =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun p : U => W p.1 p.2) U
    (fun p => homOfLE (hW p.1 p.2)) hcov (fun p => t p.1 p.2) (by
      intro p q
      apply sec_ext (W p.1 p.2 ⊓ W q.1 q.2)
      intro y hy
      exact (germ_map (TopologicalSpace.Opens.infLELeft _ _) y hy _).trans
        (((ht p.1 p.2 y hy.1).symm.trans (ht q.1 q.2 y hy.2)).trans
          (germ_map (TopologicalSpace.Opens.infLERight _ _) y hy _).symm))
  refine ⟨s, fun x hxU => ?_⟩
  have h1 : (X.presheaf.map (homOfLE (hW x hxU)).op).hom s = t x hxU := hs ⟨x, hxU⟩
  rw [ht x hxU x (hx x hxU), ← h1]
  exact (germ_map (homOfLE (hW x hxU)) x (hx x hxU) s).symm

theorem exists_vf : ∀ (K : Type) [Field K] (X : Over (Sp K)) (δ : ∀ x : X.left, X.left.presheaf.stalk x →+ X.left.presheaf.stalk x), (∀ x a b, δ x (a * b) = a * δ x b + b * δ x a) → (∀ (U : X.left.Opens) (x : X.left) (hx : x ∈ U) (c : K), δ x ((X.left.presheaf.germ U x hx).hom (cstK X U c)) = 0) → (∀ (U : X.left.Opens) (s : Γ(X.left, U)) (x : X.left), x ∈ U → ∃ (W : X.left.Opens) (h : W ≤ U) (t : Γ(X.left, W)), x ∈ W ∧ ∀ (y : X.left) (hy : y ∈ W), δ y ((X.left.presheaf.germ U y (h hy)).hom s) = (X.left.presheaf.germ W y hy).hom t) → ∃ D : VF X, ∀ (U : X.left.Opens) (s : Γ(X.left, U)) (x : X.left) (hx : x ∈ U), (X.left.presheaf.germ U x hx).hom (D.D U s) = δ x ((X.left.presheaf.germ U x hx).hom s) := by
  intro K _ X δ hL hc hloc
  choose D hD using fun (U : X.left.Opens) (s : Γ(X.left, U)) =>
    exists_section U (fun x hx => δ x ((X.left.presheaf.germ U x hx).hom s)) (hloc U s)
  refine ⟨⟨fun U => AddMonoidHom.mk' (D U) (fun a b => ?_), fun U a b => ?_, fun U c => ?_,
    fun U V h a => ?_⟩, fun U s x hx => hD U s x hx⟩
  · apply sec_ext
    intro x hx
    simp only [map_add (f := _), hD]
  · apply sec_ext
    intro x hx
    simp only [AddMonoidHom.mk'_apply, map_add (f := _), map_mul, hD, hL]
  · apply sec_ext
    intro x hx
    simp only [AddMonoidHom.mk'_apply, map_zero, hD, hc]
  · apply sec_ext
    intro x hx
    simp only [AddMonoidHom.mk'_apply]
    rw [hD, germ_map, germ_map, hD]

end GlobalTheory.SS.StalkGlue
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.PowCmp
section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

def cstR (M : Model R A) (U : M.Y.left.Opens) : R →+* Γ(M.Y.left, U) :=
  (M.Y.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem j_cstR (M : Model R A) (U : M.Y.left.Opens) (r : R) :
    (M.j.app U).hom (cstR M U r) = cstK A _ (algebraMap R K r) := by
  have e := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  have h1 : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U = (M.j ≫ M.Y.hom).appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h2 : (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top
      = (A.hom ≫ spMap (algebraMap R K)).appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    exact (Scheme.Hom.comp_appLE A.hom (spMap (algebraMap R K)) ⊤ _ _).symm
  have h3 : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U = (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [h1, h2]; simp only [M.j_hom]
  have h4 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) h3
  exact h4.trans (congrArg (A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top).hom e.symm)

theorem not_isUnit_cstR [IsLocalRing R] (M : Model R A) (U : M.Y.left.Opens) (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty)
    {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) : ¬ IsUnit (cstR M U π) := by
  intro hu
  obtain ⟨y, hy, hs⟩ := h
  have h1 : M.Y.left.basicOpen (cstR M U π) = U := M.Y.left.basicOpen_of_isUnit hu
  have h2 : M.Y.left.basicOpen (cstR M U π) = U ⊓ M.Y.hom ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π) :=
    Scheme.basicOpen_appLE M.Y.hom U ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)
  rw [h1, basicOpen_eq_of_affine (R := CommRingCat.of R) π] at h2
  have h4 := (h2.le hy).2
  have h6 : M.Y.hom y = IsLocalRing.closedPoint R := hs
  have h7 : π ∉ PrimeSpectrum.asIdeal (M.Y.hom y) := h4
  rw [h6] at h7
  exact h7 hπ

theorem j_app_injective [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens) :
    Function.Injective (M.j.app U).hom := by
  have := M.smooth
  have : IsDominant (spMap (algebraMap R K)) :=
    ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  have : IsSchemeTheoreticallyDominant (pullback.fst M.Y.hom (spMap (algebraMap R K))) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K))).flip
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : IsSchemeTheoreticallyDominant M.j := by unfold Model.j; infer_instance
  have : QuasiCompact M.j := by unfold Model.j; infer_instance
  exact M.j.app_injective U

end

theorem le_of_zpow_mul_unit_eq : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) (M : Model R A) (W : M.Y.left.Opens), ((W : Set M.Y.left) ∩ M.sp).Nonempty → ∀ (σ s : Γ(M.Y.left, W)) (a b : ℤ), IsUnit σ → cstK A (M.j ⁻¹ᵁ W) (algebraMap R K π ^ a) * (M.j.app W).hom σ = cstK A (M.j ⁻¹ᵁ W) (algebraMap R K π ^ b) * (M.j.app W).hom s → b ≤ a := by
  intro R K _ _ _ _ _ _ π hirr A M U hU σ s a b hs e'
  by_contra hlt
  have hπ : π ∈ IsLocalRing.maximalIdeal R := hirr.not_isUnit
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + (k + 1 : ℕ) := ⟨(b - a - 1).toNat, by omega⟩
  have hp : algebraMap R K π ≠ 0 := by simpa using hirr.ne_zero
  have hu : IsUnit (cstK A (M.j ⁻¹ᵁ U) (algebraMap R K π ^ a)) := (IsUnit.mk0 _ (zpow_ne_zero a hp)).map _
  rw [hk, zpow_add₀ hp, map_mul, _root_.mul_assoc, zpow_natCast, ← map_pow, ← j_cstR, ← map_mul] at e'
  have := j_app_injective M U (hu.mul_left_cancel e')
  rw [this, pow_succ, map_mul] at hs
  exact not_isUnit_cstR M U hU hπ (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hs))

end GlobalTheory.SS.PowCmp
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_pow_factor_free {B S M M' : Type} [CommRing B] [CommRing S] [Algebra B S] (b : B)
    [IsLocalization (Submonoid.powers b) S] [AddCommGroup M] [Module B M] [Module.FinitePresentation B M]
    [AddCommGroup M'] [Module B M'] [Module S M'] [IsScalarTower B S M'] [Module.Projective S M']
    (f : M →ₗ[B] M') [IsLocalizedModule (Submonoid.powers b) f] :
    ∃ (c n : ℕ) (s : M →ₗ[B] (Fin n → B)) (t : (Fin n → B) →ₗ[B] M), t ∘ₗ s = b ^ c • LinearMap.id := by
  classical
  have : Module.FinitePresentation S M' := _root_.FinitePresentation.of_isBaseChange f
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers b) S f).mp inferInstance)
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' S M'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property p LinearMap.id hp
  let eS := Finsupp.linearEquivFunOnFinite S S (Fin n)
  let eB := Finsupp.linearEquivFunOnFinite B B (Fin n)
  let ℓ : (Fin n →₀ B) →ₗ[B] (Fin n →₀ S) := Finsupp.mapRange.linearMap (Algebra.linearMap B S)
  let p' : (Fin n →₀ S) →ₗ[S] M' := p ∘ₗ eS.toLinearMap
  let σ' : M' →ₗ[S] (Fin n →₀ S) := eS.symm.toLinearMap ∘ₗ σ
  have hpσ : ∀ x, p' (σ' x) = x := fun x => by
    simpa [p', σ'] using LinearMap.congr_fun hσ x
  obtain ⟨h, s₁, hh⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers b) ℓ ((σ'.restrictScalars B) ∘ₗ f)
  obtain ⟨t, s₂, ht⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers b) f ((p'.restrictScalars B) ∘ₗ ℓ)
  have key : f ∘ₗ (t ∘ₗ h) = f ∘ₗ ((s₂ * s₁) • LinearMap.id) := by
    refine LinearMap.ext fun m => ?_
    have e1 : f (t (h m)) = (s₂ : B) • p' (ℓ (h m)) := by
      simpa [Submonoid.smul_def] using LinearMap.congr_fun ht (h m)
    have e2 : ℓ (h m) = (s₁ : B) • σ' (f m) := by
      simpa [Submonoid.smul_def] using LinearMap.congr_fun hh m
    have e3 : p' ((s₁ : B) • σ' (f m)) = (s₁ : B) • f m := by
      have := (p'.restrictScalars B).map_smul (s₁ : B) (σ' (f m))
      rw [LinearMap.coe_restrictScalars] at this
      rw [this, hpσ]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, e3, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, Submonoid.smul_def, map_smul, Submonoid.coe_mul,
      mul_smul]
  obtain ⟨s₃, hs₃⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule (Submonoid.powers b) f _ _ key
  obtain ⟨k₁, hk₁⟩ := s₁.2
  obtain ⟨k₂, hk₂⟩ := s₂.2
  obtain ⟨k₃, hk₃⟩ := s₃.2
  dsimp only at hk₁ hk₂ hk₃
  refine ⟨k₃ + (k₂ + k₁), n, eB.toLinearMap ∘ₗ h, ((s₃ : B) • t) ∘ₗ eB.symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun m => ?_
  have hm := LinearMap.congr_fun hs₃ m
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def,
    Submonoid.coe_mul] at hm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, hm,
    ← hk₁, ← hk₂, ← hk₃, pow_add, pow_add, mul_smul, mul_smul, mul_smul]

theorem defect_bounded : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∃ c : ℕ, ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (a : B →ₐ[R] R'), Defect a π c := by
  intro R _ _ _ π _ B _ _ _ hsm
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨c, n, s, t, hts⟩ := exists_pow_factor_free (S := Localization.Away (algebraMap R B π))
    (M' := Ω[Localization.Away (algebraMap R B π)⁄R]) (algebraMap R B π)
    (KaehlerDifferential.map R R B (Localization.Away (algebraMap R B π)))
  refine ⟨c, fun R' _ _ _ a => ?_⟩
  letI := a.toRingHom.toAlgebra
  intro w hw
  obtain ⟨⟨r, hr⟩, hrw⟩ := hw
  have hsw : s.baseChange R' w = 0 := by
    have h0 : r • s.baseChange R' w = 0 := by
      have hrw' : r • w = 0 := hrw
      rw [← LinearMap.map_smul, hrw', map_zero]
    exact (smul_eq_zero.mp h0).resolve_left (nonZeroDivisors.ne_zero hr)
  have hcomp : (t.baseChange R') (s.baseChange R' w) = (algebraMap R B π ^ c) • w := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hts, LinearMap.baseChange_smul,
      LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply]
  rw [hsw, map_zero] at hcomp
  have hπ : algebraMap R R' π = algebraMap B R' (algebraMap R B π) := (a.commutes π).symm
  rw [hπ, ← map_pow, algebraMap_smul, ← hcomp]

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.CompatCrit

theorem section_open {G X V : Scheme.{0}} [IsReduced G] (p : G ⟶ X) [IsSeparated p] (s : V ⟶ G)
    [IsDominant s] [IsOpenImmersion (s ≫ p)] :
    IsOpenImmersion s ∧ ∀ x : G, p x ∈ Set.range (s ≫ p) → x ∈ Set.range s := by
  let t : V ⟶ pullback p (s ≫ p) := pullback.lift s (𝟙 V) (by simp)
  have h1 : t ≫ pullback.fst p (s ≫ p) = s := pullback.lift_fst _ _ _
  have h2 : t ≫ pullback.snd p (s ≫ p) = 𝟙 V := pullback.lift_snd _ _ _
  have : IsClosedImmersion (t ≫ pullback.snd p (s ≫ p)) := by rw [h2]; infer_instance
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t (pullback.snd p (s ≫ p))
  have : IsDominant (t ≫ pullback.fst p (s ≫ p)) := by rw [h1]; infer_instance
  have : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t (pullback.fst p (s ≫ p))
  have : Surjective t := surjective_of_isDominant_of_isClosed_range t t.isClosedEmbedding.isClosed_range
  have : IsReduced (pullback p (s ≫ p)) := isReduced_of_isOpenImmersion (pullback.fst p (s ≫ p))
  have : IsIso t := isIso_of_isClosedImmersion_of_surjective t
  refine ⟨by rw [← h1]; infer_instance, fun x hx => ?_⟩
  have hx' : x ∈ Set.range (pullback.fst p (s ≫ p)) := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨v, rfl⟩ := t.surjective y
  exact ⟨v, by rw [← Scheme.Hom.comp_apply, h1]⟩

theorem isOpenImmersion_of_sections {G X : Scheme.{0}} [IsReduced G] (p : G ⟶ X) [IsSeparated p]
    (h : ∀ x : G, ∃ (V : Scheme.{0}) (s : V ⟶ G), IsDominant s ∧ IsOpenImmersion (s ≫ p) ∧ x ∈ Set.range s) :
    IsOpenImmersion p := by
  refine IsOpenImmersion.of_forall_source_exists p (fun x y hxy => ?_) (fun x => ?_)
  · obtain ⟨V, s, _, _, u, rfl⟩ := h x
    obtain ⟨v, rfl⟩ := (section_open p s).2 y ⟨u, by rw [← hxy, Scheme.Hom.comp_apply]⟩
    have : u = v := (s ≫ p).isOpenEmbedding.injective (by simpa using hxy)
    rw [this]
  · obtain ⟨V, s, _, _, hx⟩ := h x
    exact ⟨V, s, (section_open p s).1, hx, inferInstance⟩

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_j (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have h : IsPullback M.e.inv.left A.hom (pullback.snd M.Y.hom (spMap (algebraMap R K))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using Over.w M.e.inv⟩
  simpa [Model.j] using h.paste_horiz (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))

theorem exists_model (M : Model R A) {G : Scheme.{0}} (p : G ⟶ M.Y.left) [IsOpenImmersion p]
    [QuasiCompact p] (i : A.left ⟶ G) (hi : i ≫ p = M.j) :
    ∃ e : (Over.pullback (spMap (algebraMap R K))).obj (Over.mk (p ≫ M.Y.hom)) ≅ A,
      e.inv.left ≫ pullback.fst (p ≫ M.Y.hom) (spMap (algebraMap R K)) = i := by
  have h : IsPullback i (𝟙 _) p M.j := IsPullback.of_vert_isIso_mono ⟨by simp [hi]⟩
  have h' := h.paste_vert (isPullback_j M)
  rw [Category.id_comp] at h'
  exact ⟨(Over.isoMk h'.isoPullback (by simp)).symm, by simp⟩

theorem mem_range_j [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A)
    (y : M.Y.left) (hy : y ∉ M.sp) : y ∈ Set.range M.j := by
  have h1 : (M.Y.hom y : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap R K)) := by
    rw [PrimeSpectrum.localization_comap_range K (nonZeroDivisors R)]
    have hb : (M.Y.hom y : PrimeSpectrum R).asIdeal = ⊥ := by
      by_contra hb
      exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
        ((M.Y.hom y : PrimeSpectrum R).isPrime.isMaximal hb)))
    show Disjoint _ _
    rw [hb, Set.disjoint_left]
    intro a ha ha'
    exact nonZeroDivisors.ne_zero ha ha'
  obtain ⟨t, ht⟩ := h1
  obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_j M) y t ht.symm
  exact ⟨a, ha⟩

end GlobalTheory.SS.CompatCrit

namespace GlobalTheory.SS
open CompatCrit

theorem compat_of_isoAt_closure : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [IsIntegral A.left] (M N : Model R A) (δ : A.left ⟶ (M.Y ⊗ N.Y).left), δ ≫ (fst M.Y N.Y).left = M.j → δ ≫ (snd M.Y N.Y).left = N.j → (∀ z ∈ closure (Set.range δ), IsClosed {z} → (fst M.Y N.Y).left z ∈ M.sp → IsoAt M N (𝟙 A) ((fst M.Y N.Y).left z)) → Compat M N := by
  intro R K _ _ _ _ _ ⟨hD, _, _, hF⟩ A _ M N δ h₁ h₂ H
  have := M.smooth; have := M.sep; have := M.qc; have := N.smooth; have := N.sep; have := N.qc
  have : IsOpenImmersion (spMap (algebraMap R K)) := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    (schemeDominant_specMap_iff _).2 (IsFractionRing.injective R K)
  have jM : IsOpenImmersion M.j := MorphismProperty.of_isPullback (isPullback_j M).flip ‹_›
  have jN : IsOpenImmersion N.j := MorphismProperty.of_isPullback (isPullback_j N).flip ‹_›
  have qM : QuasiCompact M.j := MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_j M).flip inferInstance
  have dM : IsSchemeTheoreticallyDominant M.j := .of_isPullback (isPullback_j M).flip
  have s₁ : IsSeparated (fst M.Y N.Y).left := inferInstanceAs (IsSeparated (pullback.fst M.Y.hom N.Y.hom))
  have s₂ : IsSeparated (snd M.Y N.Y).left := inferInstanceAs (IsSeparated (pullback.snd M.Y.hom N.Y.hom))
  have c₁ : QuasiCompact (fst M.Y N.Y).left := inferInstanceAs (QuasiCompact (pullback.fst M.Y.hom N.Y.hom))
  have : QuasiCompact (δ ≫ (fst M.Y N.Y).left) := by rw [h₁]; infer_instance
  have qδ : QuasiCompact δ := QuasiCompact.of_comp δ (fst M.Y N.Y).left
  have : IsReduced δ.image := IsSchemeTheoreticallyDominant.isReduced δ.toImage
  let p := δ.imageι ≫ (fst M.Y N.Y).left
  let q := δ.imageι ≫ (snd M.Y N.Y).left
  have hp : δ.toImage ≫ p = M.j := (δ.toImage_imageι_assoc _).trans h₁
  have hq : δ.toImage ≫ q = N.j := (δ.toImage_imageι_assoc _).trans h₂
  have : CompactSpace M.Y.left := QuasiCompact.compactSpace_of_compactSpace M.Y.hom
  have : CompactSpace δ.image := QuasiCompact.compactSpace_of_compactSpace p
  let S : Set δ.image := {x | ∃ (V : Scheme.{0}) (s : V ⟶ δ.image), IsDominant s ∧ IsOpenImmersion (s ≫ p) ∧
    IsOpenImmersion (s ≫ q) ∧ x ∈ Set.range s}
  have hSo : IsOpen S := by
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro x ⟨V, s, a, b, c, hx⟩
    have := (section_open p s).1
    exact ⟨Set.range s, fun y hy => ⟨V, s, a, b, c, hy⟩, s.isOpenEmbedding.isOpen_range, hx⟩
  have hS : ∀ x, x ∈ S := by
    by_contra hne
    obtain ⟨x, hx, hc⟩ := hSo.isClosed_compl.exists_closed_singleton (not_forall.1 hne)
    apply hx
    by_cases hsp : p x ∈ M.sp
    · have hz : δ.imageι x ∈ closure (Set.range δ) := by
        have h := image_closure_subset_closure_image δ.imageι.continuous
          ⟨x, δ.toImage.denseRange x, rfl⟩
        refine closure_mono ?_ h
        rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]⟩
      have hcz : IsClosed {δ.imageι x} := by
        simpa using δ.imageι.isClosedEmbedding.isClosedMap _ hc
      obtain ⟨U, g, hU, ⟨e₁, e₂⟩, hg⟩ := H _ hz hcz hsp
      let t : U.toScheme ⟶ (M.Y ⊗ N.Y).left := pullback.lift U.ι g e₁.symm
      have t₁ : t ≫ (fst M.Y N.Y).left = U.ι := pullback.lift_fst _ _ _
      have t₂ : t ≫ (snd M.Y N.Y).left = g := pullback.lift_snd _ _ _
      have : IsSchemeTheoreticallyDominant (M.j ∣_ U) := .of_isPullback (isPullback_morphismRestrict M.j U).flip
      have hw : (M.j ∣_ U) ≫ t = (M.j ⁻¹ᵁ U).ι ≫ δ := by
        refine pullback.hom_ext ?_ ?_
        · change ((M.j ∣_ U) ≫ t) ≫ (fst M.Y N.Y).left = (_ ≫ δ) ≫ (fst M.Y N.Y).left
          rw [Category.assoc, Category.assoc, t₁, h₁, morphismRestrict_ι]
        · change ((M.j ∣_ U) ≫ t) ≫ (snd M.Y N.Y).left = (_ ≫ δ) ≫ (snd M.Y N.Y).left
          rw [Category.assoc, Category.assoc, t₂, h₂, e₂]; simp
      let s := closureLift δ t (M.j ∣_ U) _ hw
      have sp : s ≫ p = U.ι := (closureLift_imageι_assoc δ t _ _ hw _).trans t₁
      have sq : s ≫ q = g := (closureLift_imageι_assoc δ t _ _ hw _).trans t₂
      have : IsDominant (M.j ⁻¹ᵁ U).ι := ⟨by
        rw [DenseRange, Scheme.Opens.range_ι]
        refine (M.j ⁻¹ᵁ U).isOpen.dense ?_
        obtain ⟨a, ha⟩ := M.j.denseRange.exists_mem_open U.isOpen ⟨_, hU⟩
        exact ⟨a, ha⟩⟩
      have : IsDominant ((M.j ∣_ U) ≫ s) := by
        simp only [s, comp_closureLift]; infer_instance
      have ds : IsDominant s := IsDominant.of_comp (M.j ∣_ U) s
      have op : IsOpenImmersion (s ≫ p) := by rw [sp]; infer_instance
      refine ⟨_, s, ds, op, by rw [sq]; exact hg, (section_open p s).2 x ?_⟩
      rw [sp, Scheme.Opens.range_ι]
      exact hU
    · have op : IsOpenImmersion (δ.toImage ≫ p) := by rw [hp]; exact jM
      refine ⟨_, δ.toImage, inferInstance, op, by rw [hq]; exact jN, (section_open p _).2 x ?_⟩
      rw [hp]
      exact mem_range_j M _ hsp
  have op : IsOpenImmersion p := isOpenImmersion_of_sections p fun x => by
    obtain ⟨V, s, a, b, -, hx⟩ := hS x
    exact ⟨V, s, a, b, hx⟩
  have oq : IsOpenImmersion q := isOpenImmersion_of_sections q fun x => by
    obtain ⟨V, s, a, -, c, hx⟩ := hS x
    exact ⟨V, s, a, c, hx⟩
  obtain ⟨e, he⟩ := exists_model M p δ.toImage hp
  let W : Model R A := ⟨Over.mk (p ≫ M.Y.hom), e, inferInstanceAs (Smooth (p ≫ M.Y.hom)),
    inferInstanceAs (IsSeparated (p ≫ M.Y.hom)), inferInstanceAs (QuasiCompact (p ≫ M.Y.hom))⟩
  have hW : W.j = δ.toImage := he
  let i : W.Y ⟶ M.Y ⊗ N.Y := Over.homMk δ.imageι (by simp [W, p])
  refine ⟨W, i ≫ fst _ _, i ≫ snd _ _, op, oq, ?_, ?_, ?_⟩
  · rw [hW]; exact hp
  · rw [hW]; exact hq
  · rw [lift_comp_fst_snd]
    exact inferInstanceAs (IsClosedImmersion δ.imageι)

end GlobalTheory.SS
end

section

namespace GlobalTheory.SmoothAdic

open TensorProduct IsLocalRing

theorem isSmoothAt_of_smooth_quotient_pow : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (C : Type) [CommRing C] [Algebra R C] [Algebra.FiniteType R C], (∀ e : ℕ, Algebra.Smooth (R ⧸ I ^ (e + 1)) (TensorProduct R (R ⧸ I ^ (e + 1)) C)) → ∀ (q : Ideal C) [q.IsPrime], q.comap (algebraMap R C) = IsLocalRing.maximalIdeal R → Algebra.IsSmoothAt R q := by
  intro R _ _ _ I hI C _ _ _ h q _ hq
  refine GlobalTheory.SmoothLimit.isSmoothAt_of_smooth_quotient_pow (V := R) (A := C) (fun e => ?_) q hq
  have hle : I ^ (e + 1) ≤ maximalIdeal R ^ (e + 1) :=
    Ideal.pow_right_mono (le_maximalIdeal hI) (e + 1)
  let _ : Algebra (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1)) :=
    (Ideal.Quotient.factor hle).toAlgebra
  have : IsScalarTower R (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := h e
  exact Algebra.Smooth.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1))
      (R ⧸ maximalIdeal R ^ (e + 1)) C)

end GlobalTheory.SmoothAdic
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.splitTorus_to_abelianVariety_const : ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : splitTorus (Sp K) X ⟶ B, ∃ b : 𝟙_ (Over (Sp K)) ⟶ B, f = toUnit _ ≫ b := by
  first | exact @GlobalTheory.splitTorus_to_abelian_const | exact GlobalTheory.splitTorus_to_abelian_const | (intros; apply GlobalTheory.splitTorus_to_abelian_const <;> assumption)
end
