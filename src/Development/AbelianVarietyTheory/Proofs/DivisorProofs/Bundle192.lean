module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory

theorem IdealSheafData.ideal_comap_affineOpen_of_isAffine {X Y : Scheme.{0}} [IsAffine Y]
    (f : X ⟶ Y) (K : Y.IdealSheafData) (W : X.affineOpens) :
    (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (by simp)).hom (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  haveI : IsAffine (W.1 : Scheme) := W.2
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (K.comap f) W.1.ι
    ⟨⊤, isAffineOpen_top _⟩
  rw [← Scheme.IdealSheafData.comap_comp, IdealSheafData.ideal_comap_top_of_isAffine] at h1
  have hc : (W.1.ι ≫ f).appTop ≫ (W.1.ι.appIso ⊤).inv = f.appLE ⊤ (W.1.ι ''ᵁ ⊤) (by simp) := by
    simp [Scheme.Hom.appLE]; exact Category.comp_id _
  have hs : Function.Surjective (W.1.ι.appIso ⊤).inv.hom :=
    (W.1.ι.appIso ⊤).commRingCatIsoToRingEquiv.symm.surjective
  have h2 : (K.comap f).ideal ⟨W.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ =
      Ideal.map (f.appLE ⊤ (Subtype.val (⟨W.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ : X.affineOpens)) (by simp)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    rw [← hc, CommRingCat.hom_comp, ← Ideal.map_map, h1, Ideal.map_comap_of_surjective _ hs]
  have hW : (⟨W.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ : X.affineOpens) = W :=
    Subtype.ext (by simp)
  have key : ∀ V : X.affineOpens, V = W →
      (K.comap f).ideal V = Ideal.map (f.appLE ⊤ V.1 (fun _ _ => trivial)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) →
      (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (fun _ _ => trivial)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    rintro V rfl h; exact h
  exact key _ hW h2

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem clopen_cut_closedImmersion : ∀ {X Z₁ : Scheme.{0}} (i : Z₁ ⟶ X), IsClosedImmersion i → ∀ (U : X.Opens), IsClosed (U : Set X) → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), ((∃ z : T ⟶ Z, z ≫ j = g) ↔ (∃ y : T ⟶ Z₁, y ≫ i = g) ∧ Set.range g.base ⊆ (U : Set X)) := by
  intro X Z₁ i hi U hU
  have hVc : IsClosed (Set.range (i ⁻¹ᵁ U).ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact hU.preimage i.base.hom.continuous
  haveI : IsClosedImmersion (i ⁻¹ᵁ U).ι := IsClosedImmersion.of_isPreimmersion _ hVc
  refine ⟨(i ⁻¹ᵁ U), (i ⁻¹ᵁ U).ι ≫ i, inferInstance, fun T g => ?_⟩
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z ≫ (i ⁻¹ᵁ U).ι, by simp⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    have : ((i ⁻¹ᵁ U).ι.base (z.base t)) ∈ (i ⁻¹ᵁ U : Set Z₁) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
    simpa [Scheme.Hom.comp_base] using this
  · rintro ⟨⟨y, rfl⟩, hg⟩
    have h : Set.range y.base ⊆ Set.range (i ⁻¹ᵁ U).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      have := hg ⟨t, rfl⟩
      simpa using this
    exact ⟨IsOpenImmersion.lift (i ⁻¹ᵁ U).ι y h, by rw [← Category.assoc, IsOpenImmersion.lift_fac]⟩

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem isIso_restrict_of_closedImmersion_near_generic :
    ∀ {W W' Y Y₁ : Scheme.{0}} [IsIntegral W] [IsIntegral W'] (i : W ⟶ Y) [IsClosedImmersion i] (h : W' ⟶ W)
      (c : W' ⟶ Y₁) [IsClosedImmersion c] (s₁ : Y₁ ⟶ Y) (U : Y.Opens), IsIso (s₁ ∣_ U) → h ≫ i = c ≫ s₁ →
      i (genericPoint W) ∈ U → (∃ w', h w' = genericPoint W) →
      ∃ U' : W.Opens, (U' : Set W).Nonempty ∧ IsIso (h ∣_ U') := by
  intro W W' Y Y₁ _ _ i _ h c _ s₁ U hiso hcomm hη hw
  obtain ⟨w', hw'⟩ := hw
  refine ⟨i ⁻¹ᵁ U, ⟨genericPoint W, hη⟩, ?_⟩
  have hi : IsClosedImmersion (i ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› U
  have hc : IsClosedImmersion (c ∣_ (s₁ ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› _
  have h1 : IsClosedImmersion ((c ≫ s₁) ∣_ U) := by
    rw [morphismRestrict_comp]
    have hs : IsClosedImmersion (s₁ ∣_ U) := inferInstance
    exact @IsClosedImmersion.comp _ _ _ _ _ hc hs
  have h2 : IsClosedImmersion ((h ≫ i) ∣_ U) := by
    rw [hcomm]; exact h1
  rw [morphismRestrict_comp] at h2
  have h3 : IsClosedImmersion (h ∣_ (i ⁻¹ᵁ U)) :=
    @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ _ (i ∣_ U) hi h2
  have hw'U : w' ∈ h ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    show h w' ∈ i ⁻¹ᵁ U
    rw [hw']; exact hη
  have h4 : Surjective (h ∣_ (i ⁻¹ᵁ U)) := by
    constructor
    intro x
    have hcl : IsClosed (Set.range (h ∣_ (i ⁻¹ᵁ U))) := (h ∣_ (i ⁻¹ᵁ U)).isClosedEmbedding.isClosed_range
    let p : (h ⁻¹ᵁ (i ⁻¹ᵁ U) : Scheme) := ⟨w', hw'U⟩
    have hp : ((h ∣_ (i ⁻¹ᵁ U)) p).1 = genericPoint W := by
      rw [morphismRestrict_base_coe]; exact hw'
    have hsp : (h ∣_ (i ⁻¹ᵁ U)) p ⤳ x := by
      rw [← (i ⁻¹ᵁ U).ι.isOpenEmbedding.toIsInducing.specializes_iff]
      have : (i ⁻¹ᵁ U).ι ((h ∣_ (i ⁻¹ᵁ U)) p) = genericPoint W := hp
      rw [this]
      exact (genericPoint_spec W).specializes (Set.mem_univ _)
    exact hsp.mem_closed hcl ⟨p, rfl⟩
  exact isIso_of_isClosedImmersion_of_surjective _

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem GlobalTheory.lift_of_reduced_of_support {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    [IsReduced T] (g : T ⟶ Y) (hg : ∀ t, g t ∈ i.ker.support) : ∃ h : T ⟶ X, h ≫ i = g := by
  have hle : i.ker ≤ g.ker := by
    refine (Scheme.IdealSheafData.le_ofIdeals_iff (I := i.ker)).mpr ?_
    intro U a ha
    rw [RingHom.mem_ker]
    apply eq_zero_of_basicOpen_eq_bot
    rw [← Scheme.preimage_basicOpen]
    ext t
    simp only [Scheme.Hom.mem_preimage, Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro ht
    have h1 := (Scheme.IdealSheafData.mem_support_iff.mp (hg t)) U
    exact (Y.mem_zeroLocus_iff _ _).mp h1 a ha ht
  exact ⟨IsClosedImmersion.lift i g hle, IsClosedImmersion.lift_fac _ _ _⟩
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.closedImmersion_baseChange_ker_mem_map_affine : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → ∀ W : X.Opens, IsAffineOpen W → ∀ s : Γ(X', p ⁻¹ᵁ W), (i'.app (p ⁻¹ᵁ W)).hom s = 0 → s ∈ Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) := by
  first | exact @GlobalTheory.closedImmersion_baseChange_ker_mem_map | exact GlobalTheory.closedImmersion_baseChange_ker_mem_map | (intros; apply GlobalTheory.closedImmersion_baseChange_ker_mem_map <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem _root_.GlobalTheory.T.exists_pow_mul_app_eq_zero_near_of_represented' : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop), (∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t)) → ∀ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), IsClosedImmersion i → (∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t) → ∀ (W : S.Opens) (s c : Γ(S, W)), (∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app (S.basicOpen s)).hom ((S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom c) = 0) → ∀ y : S, y ∈ U → y ∈ W → ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 := by
  first | exact @GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented | exact GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented | (intros; apply GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented; all_goals assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_factor_closedImmersion_of_locally_on_source : ∀ (Z A Y : Scheme.{0}) (a : A ⟶ Z), IsClosedImmersion a → ∀ (g : Y ⟶ Z), (∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ ∃ z : W.toScheme ⟶ A, z ≫ a = W.ι ≫ g) → ∃ z : Y ⟶ A, z ≫ a = g := by
  first | exact @GlobalTheory.exists_factor_closedImmersion_of_locally | exact GlobalTheory.exists_factor_closedImmersion_of_locally | (intros; apply GlobalTheory.exists_factor_closedImmersion_of_locally <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_affine_nbhd_preimage_le_of_closed_cover : ∀ (Y Y₁ Y₂ X : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) [IsClosedImmersion j₁] [IsClosedImmersion j₂] (a₁ : Y₁ ⟶ X) (a₂ : Y₂ ⟶ X), (∀ y : Y, (∃ y₁, j₁ y₁ = y) ∨ ∃ y₂, j₂ y₂ = y) → (∀ (y₁ : Y₁) (y₂ : Y₂), j₁ y₁ = j₂ y₂ → a₁ y₁ = a₂ y₂) → ∀ y : Y, ∃ (W : Y.Opens) (U : X.affineOpens), IsAffineOpen W ∧ y ∈ W ∧ j₁ ⁻¹ᵁ W ≤ a₁ ⁻¹ᵁ U.1 ∧ j₂ ⁻¹ᵁ W ≤ a₂ ⁻¹ᵁ U.1 := by
  first | exact @GlobalTheory.closedCover_affine_nbhd_maps_into_affine | exact GlobalTheory.closedCover_affine_nbhd_maps_into_affine | (intros; apply GlobalTheory.closedCover_affine_nbhd_maps_into_affine <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.isClosedImmersion_surjective_to_colimit : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens) (F : 𝒰 ⥤ Scheme.{0}) [∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected] (X : Scheme.{0}) (G : B₀.Opens → X.Opens) (hG : Monotone G), (∀ x : X, ∃ U ∈ 𝒰, x ∈ G U) → ∀ (e : ∀ U : 𝒰, (G U.1).toScheme ⟶ F.obj U), (∀ U, IsClosedImmersion (e U)) → (∀ U, Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), X.homOfLE (hG h) ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → ∀ j : X ⟶ colimit F, (∀ U : 𝒰, (G U.1).ι ≫ j = e U ≫ colimit.ι F U) → IsClosedImmersion j ∧ Surjective j ∧ ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1 := by
  first | exact @GlobalTheory.GlueColim.isClosedImmersion_surjective_preimage | exact GlobalTheory.GlueColim.isClosedImmersion_surjective_preimage | (intros; apply GlobalTheory.GlueColim.isClosedImmersion_surjective_preimage <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.isPushout_thickenings_of_isPullback_sections : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → Surjective j₁ → Surjective j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → IsPushout i₁ i₂ j₁ j₂ := by
  first | exact @GlobalTheory.ThickPush.isPushout_of_isPullback_sections | exact GlobalTheory.ThickPush.isPushout_of_isPullback_sections | (intros; apply GlobalTheory.ThickPush.isPushout_of_isPullback_sections <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.local_ring_points_ideal_criterion : ∀ (A : Type) [CommRing A] [IsLocalRing A] (X Y : Scheme.{0}) (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X), IsClosedImmersion j → ∀ J : Ideal A, (∀ (R : Type) [CommRing R] [IsLocalRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ) → ∀ (R : Type) [CommRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ := by
  first | exact @GlobalTheory.factor_closedImmersion_iff_of_local | exact GlobalTheory.factor_closedImmersion_iff_of_local | (intros; apply GlobalTheory.factor_closedImmersion_iff_of_local <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry

theorem _root_.GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open : ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧ (f.stalkMap y).hom.EssFiniteType := by
  first | exact @GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | exact GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | (intros; apply GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict <;> assumption)
end
