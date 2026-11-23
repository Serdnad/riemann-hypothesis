module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle243
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AffGlue

structure Data (T : Scheme.{0}) where

  M : ∀ V : T.Opens, IsAffineOpen V → Type

  grp : ∀ V hV, AddCommGroup (M V hV)

  mod : ∀ V hV, Module Γ(T, V) (M V hV)

  ρ : ∀ {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V'), V' ≤ V → M V hV →+ M V' hV'
  ρ_smul : ∀ {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (a : Γ(T, V)) (m : M V hV), ρ hV hV' h (a • m) = resG T h a • ρ hV hV' h m
  ρ_self : ∀ {V : T.Opens} (hV : IsAffineOpen V) (h : V ≤ V) (m : M V hV), ρ hV hV h m = m
  ρ_ρ : ∀ {V V' V'' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hV'' : IsAffineOpen V'') (h : V' ≤ V) (h' : V'' ≤ V') (m : M V hV),
    ρ hV' hV'' h' (ρ hV hV' h m) = ρ hV hV'' (h'.trans h) m

  loc_surj : ∀ {V : T.Opens} (hV : IsAffineOpen V) (f : Γ(T, V)) (hD : IsAffineOpen (T.basicOpen f))
    (m : M (T.basicOpen f) hD), ∃ (n : ℕ) (x : M V hV),
      resG T (T.basicOpen_le f) f ^ n • m = ρ hV hD (T.basicOpen_le f) x

  loc_inj : ∀ {V : T.Opens} (hV : IsAffineOpen V) (f : Γ(T, V)) (hD : IsAffineOpen (T.basicOpen f))
    (x : M V hV), ρ hV hD (T.basicOpen_le f) x = 0 → ∃ n : ℕ, f ^ n • x = 0

attribute [instance] Data.grp Data.mod

variable {T : Scheme.{0}} (D : Data T)

variable {D}

end GlobalTheory.AffGlue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem spMap_factor_residueField_of_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω]
    (g : Sp Ω ⟶ Sp R) (hg : ∀ w, g w = closedPoint R) :
    ∃ κ : ResidueField R →+* Ω, g = spMap (κ.comp (residue R)) := by
  set φ : R →+* Ω := (Spec.preimage g).hom with hφ
  have hgφ : g = spMap φ := by
    simp only [spMap, hφ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hker : ∀ x ∈ maximalIdeal R, φ x = 0 := by
    intro x hx
    let w : Sp Ω := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 := hg w
    rw [hgφ] at h1
    have h2 : (spMap φ w).asIdeal = Ideal.comap φ ⊥ := rfl
    rw [h1, closedPoint] at h2
    have : x ∈ Ideal.comap φ ⊥ := h2 ▸ hx
    simpa using this
  refine ⟨Ideal.Quotient.lift (maximalIdeal R) φ hker, ?_⟩
  rw [hgφ]
  congr 2

end GlobalTheory.Mum
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.OpenImmDim

theorem topologicalKrullDim_eq_of_isOpenImmersion : ∀ (F : Type) [Field F] (X V : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp F) (ℓ : V ⟶ X) [LocallyOfFiniteType p] [IsOpenImmersion ℓ]
    [Nonempty V], topologicalKrullDim V = topologicalKrullDim X := by
  intro F _ X V _ p ℓ _ _ _
  have hne : ((ℓ.opensRange : X.Opens) : Set X).Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨ℓ v, by rw [Scheme.Hom.coe_opensRange]; exact ⟨v, rfl⟩⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F p ℓ.opensRange hne]
  exact (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding ℓ.isOpenEmbedding.isEmbedding
    (by rw [Scheme.Hom.coe_opensRange])).symm

end GlobalTheory.OpenImmDim
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.lift_ringHom_affine_open_of_artinian_scheme_lift : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → ∀ (U : (Sp B).Opens), IsAffineOpen U → ∀ (V : X.Opens), IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : Γ(Sp B, U) →+* C) (φ₀ : Γ(X, V) →+* C₀), φ₀.comp ((s.appLE U V e).hom) = π.comp β → ∃ φ : Γ(X, V) →+* C, π.comp φ = φ₀ ∧ φ.comp ((s.appLE U V e).hom) = β) := by
  first | exact @GlobalTheory.lift_ringHom_of_scheme_lift | exact GlobalTheory.lift_ringHom_of_scheme_lift | (intros; apply GlobalTheory.lift_ringHom_of_scheme_lift <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_basicOpen_cover_affineOpen_spec : ∀ (S : Type) [CommRing S] (Y : Scheme.{0}) (u : Sp S ⟶ Y),
    ∃ (n : ℕ) (s : Fin n → S) (W : Fin n → Y.Opens), Ideal.span (Set.range s) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧ ∀ i, (spMap (algebraMap S (Localization.Away (s i))) ≫ u) ⁻¹ᵁ W i = ⊤ := by
  first | exact @GlobalTheory.SecGlue.exists_basicOpen_cover_affine | exact GlobalTheory.SecGlue.exists_basicOpen_cover_affine | (intros; apply GlobalTheory.SecGlue.exists_basicOpen_cover_affine <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.preimage_eq_of_square_zero_thickening : ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (Y : Scheme.{0}) (u w : Sp S ⟶ Y), spMap q ≫ u = spMap q ≫ w → ∀ V : Y.Opens, u ⁻¹ᵁ V = w ⁻¹ᵁ V := by
  first | exact @GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero | exact GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero | (intros; apply GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' : ∀ (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) (q : X ⟶ Sp R), GeneralizingMap q → ∀ x : X, Order.coheight x ≤ 1 → (q x).asIdeal ≠ ⊥ → ∃ π : R, Prime π ∧ (q x).asIdeal = Ideal.span {π} := by
  first | exact @GlobalTheory.exists_prime_eq_span_of_coheight_le_one | exact GlobalTheory.exists_prime_eq_span_of_coheight_le_one | (intros; apply GlobalTheory.exists_prime_eq_span_of_coheight_le_one <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_glue_spec_localizationAway_morphisms : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (e : ∀ i, Sp (Localization.Away (s i)) ⟶ Y),
    (∀ i j, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) ≫ e i =
      spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) ≫ e j) →
    ∃ a : Sp S ⟶ Y, ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = e i := by
  first | exact @GlobalTheory.SecGlue.glue_away | exact GlobalTheory.SecGlue.glue_away | (intros; apply GlobalTheory.SecGlue.glue_away <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_factor_closedImmersion_of_affine_points : ∀ {X Z T : Scheme.{0}} (i : Z ⟶ X), IsClosedImmersion i → ∀ (g : T ⟶ X), (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ T), ∃ y : Sp R' ⟶ Z, y ≫ i = x ≫ g) → ∃ z : T ⟶ Z, z ≫ i = g := by
  first | (exact @GlobalTheory.factor_closedImmersion_of_affine_points) | (exact GlobalTheory.factor_closedImmersion_of_affine_points) | (intros; apply GlobalTheory.factor_closedImmersion_of_affine_points <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

theorem _root_.GlobalTheory.T.irreducibleSpace_pullback_field_of_irreducible_cover : ∀ {F : Type} [Field F] {X : Scheme.{0}} (h : X ⟶ Sp F) (k : Type) [Field k] (f : F →+* k) (U : X.Opens),
    IsIrreducible (U : Set X) →
    (∀ y ∈ U, ∃ V : X.Opens, V ≤ U ∧ y ∈ V ∧ IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f))) →
    IrreducibleSpace ↑(pullback (U.ι ≫ h) (spMap f)) := by
  first | exact @GlobalTheory.irreducibleSpace_pullback_of_cover | exact GlobalTheory.irreducibleSpace_pullback_of_cover | (intros; apply GlobalTheory.irreducibleSpace_pullback_of_cover <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (a b : Sp S ⟶ Y),
    (∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = spMap (algebraMap S (Localization.Away (s i))) ≫ b) →
    a = b := by
  first | exact @GlobalTheory.SecGlue.hom_ext_of_span_eq_top | exact GlobalTheory.SecGlue.hom_ext_of_span_eq_top | (intros; apply GlobalTheory.SecGlue.hom_ext_of_span_eq_top <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R'), IsLocalHom φ → Function.Injective φ → ∀ (Y : Scheme.{0}) (x y : Sp R ⟶ Y), spMap φ ≫ x = spMap φ ≫ y → x = y := by
  first | exact @GlobalTheory.spec_local_hom_ext_of_injective | exact GlobalTheory.spec_local_hom_ext_of_injective | (intros; apply GlobalTheory.spec_local_hom_ext_of_injective <;> assumption)
end
