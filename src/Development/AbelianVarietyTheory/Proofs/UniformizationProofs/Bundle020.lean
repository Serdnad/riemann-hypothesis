module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem stalkMap_injective_of_flat' {Y Z : Scheme.{0}} (ρ : Z ⟶ Y) [Flat ρ] (z : Z) :
    Function.Injective (ρ.stalkMap z).hom := by

  let _ := (ρ.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z) := Flat.stalkMap ρ z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z)) :=
    (by infer_instance : IsLocalHom (ρ.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z)

theorem corr_of_val_flat_surjective {X Y Z : Scheme.{0}} (ρ : Z ⟶ Y) [Flat ρ] [Surjective ρ] {L : LB X}
    (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ z J, Good L z J → val t ρ z J = val t' ρ z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by

  have : Epi ρ := Flat.epi_of_flat_of_surjective ρ
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨z, rfl⟩ := ρ.surjective y
  obtain ⟨J', hJ', hJJ'⟩ := exists_good L hL z (fun ψ : Y ⟶ X => ρ ≫ ψ) J
    (fun a b hab => congrArg J ((cancel_epi ρ).1 hab)) (fun ψ => by simpa using hJ ψ)
  have hpull : (fun ψ : Y ⟶ X => J' (ρ ≫ ψ)) = J := funext hJJ'
  have e₁ := (values_natural X Y Y Z L K φ ε (𝟙 Y) ρ z J' hJ').2.2.1 t
  have e₂ := (values_natural X Y Y Z L K' φ' ε' (𝟙 Y) ρ z J' hJ').2.2.1 t'
  rw [Category.comp_id, hpull] at e₁ e₂

  apply Units.ext
  apply stalkMap_injective_of_flat' ρ z
  rw [← e₁, ← e₂, h z J' hJ']

theorem corr_of_val_field_extension : ∀ (K₀ F : Type) [Field K₀] [Field F] (f : K₀ →+* F) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Spec (CommRingCat.of K₀) ⟶ X)) (ε : K → ℤ) (φ' : K' → (Spec (CommRingCat.of K₀) ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')), (∀ z J, Good L z J → val t (Spec.map (CommRingCat.ofHom f)) z J = val t' (Spec.map (CommRingCat.ofHom f)) z J) → LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro K₀ F _ _ f X L hL K K' _ _ φ ε φ' ε' t t' h

  have hff : (CommRingCat.ofHom f).hom.FaithfullyFlat := by
    let _ := f.toAlgebra
    show Module.FaithfullyFlat K₀ F
    infer_instance
  obtain ⟨h₁, h₂⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).2 hff
  exact corr_of_val_flat_surjective (Spec.map (CommRingCat.ofHom f)) hL h

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ThickeningDetermines in
theorem sec_eq_zero_of_thickenings_of_section (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R)))
    [Smooth H.hom] [GeometricallyConnected H.hom] (e : 𝟙_ _ ⟶ H) (N : LB H.left) (hN : N.IsLB)
    (s : LB.Sec N) (hs : ∀ (n : ℕ) j, ((fstG I n H).left.app _).hom (s.f j) = 0) (j) :
    s.f j = 0 := by
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres H.hom
  have key := isIso_of_isClosedImmersion_of_thickenings R I hI H e (fun p ↦ inferInstance)
  refine eq_zero_of_secIdeal_eq_bot hN s ?_ j
  have := key _ (secIdeal hN s).subschemeι fun n ↦ by
    have : IsClosedImmersion (thick R I n) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : QuasiCompact (fstG I n H).left :=
      inferInstanceAs (QuasiCompact (pullback.fst H.hom (thick R I n)))
    exact ⟨IsClosedImmersion.lift _ (fstG I n H).left (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact secIdeal_le_ker hN s _ (hs n)), IsClosedImmersion.lift_fac _ _ _⟩
  rw [← Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)]
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.1 this

theorem app_sec_eq_zero_of_sval {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type}
    [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y)
    (h : ∀ (z : Z) (J), Good L z J → sval d r z J = 0) (j) : (r.app _).hom (d.f j) = 0 := by
  apply TopCat.Presheaf.section_ext Z.sheaf _
  intro z hz
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have e := sec_trans d r z (j := j) hz (Good.mem hI φ r)
  have e' : gs r z (LB.wchart L φ j) (d.f j) = 0 :=
    e.trans ((congrArg _ (h z I hI)).trans (mul_zero _))
  exact ((gs_eq r z _ hz _).symm.trans e').trans (map_zero _).symm

theorem sec_eq_zero_of_sval_finite_level : ∀ (R : Type) [CommRing R] (I : Ideal R) (T B : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [GrpObj B] [Smooth B.hom] [GeometricallyConnected B.hom], (∀ r ∈ I, scal T.hom r ∈ Ideal.jacobson (⊥ : Ideal Γ(T.left, ⊤))) → ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → ((T ⊗ B).left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (T ⊗ B).hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ j, d.f j = 0 := by
  intro R _ I T B _ _ _ _ _ hI X L hL K _ φ ε d hd j
  let ψ : CommRingCat.of R ⟶ Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop
  have hψ : T.left.isoSpec.hom ≫ Spec.map ψ = T.hom := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  let H : Over (Spec (CommRingCat.of Γ(T.left, ⊤))) :=
    Over.mk (pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom)
  have : Smooth H.hom := inferInstanceAs (Smooth (pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom))
  have : GeometricallyConnected H.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_iso (IsPullback.of_hasPullback T.hom B.hom).flip (Iso.refl _) (Iso.refl _)
        T.left.isoSpec (Iso.refl _) (fst' := pullback.snd T.hom B.hom) (snd' := H.hom)
        (f' := B.hom) (g' := Spec.map ψ) (by simp) (Category.id_comp _).symm (by simp)
        (by simp [hψ])) ‹GeometricallyConnected B.hom›
  let σ : T ⟶ T ⊗ B := lift (𝟙 T) (toUnit T ≫ η[B])
  have hσ : σ.left ≫ pullback.fst T.hom B.hom = 𝟙 _ :=
    congrArg CommaMorphism.left (lift_fst (𝟙 T) (toUnit T ≫ η[B]))
  let e : 𝟙_ _ ⟶ H := Over.homMk (T.left.isoSpec.inv ≫ σ.left) (by
    change (T.left.isoSpec.inv ≫ σ.left) ≫ pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom = 𝟙 _
    rw [Category.assoc, reassoc_of% hσ, Iso.inv_hom_id])
  refine sec_eq_zero_of_thickenings_of_section Γ(T.left, ⊤) (I.map ψ.hom)
    (Ideal.map_le_iff_le_comap.2 hI) H e (LB.LinComb L φ ε) (DVR.linComb_isLB L hL φ ε) d
    (fun n j ↦ app_sec_eq_zero_of_sval hL d _ (hd n _ _ ⟨pullback.snd H.hom (thick _ (I.map ψ.hom) n) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.map ψ.hom) ^ (n + 1)) ψ.hom
          (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map))), ?_⟩) j) j
  change _ = pullback.fst H.hom (thick _ (I.map ψ.hom) n) ≫ pullback.fst T.hom B.hom ≫ T.hom
  have h1 : pullback.fst T.hom B.hom ≫ T.hom = H.hom ≫ Spec.map ψ :=
    (congrArg (pullback.fst T.hom B.hom ≫ ·) hψ.symm).trans (Category.assoc _ _ _).symm
  rw [h1, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory
end
