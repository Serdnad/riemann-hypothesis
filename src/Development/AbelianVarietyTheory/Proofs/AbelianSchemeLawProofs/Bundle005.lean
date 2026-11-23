module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem forall_geometricallyIntegral_of_smooth_of_geometricallyConnected :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f :=
  fun _ _ f _ _ ↦ geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres f

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FunDescent

noncomputable def coord : Γ(Spec (CommRingCat.of (Polynomial ℤ)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X

theorem hom_ext {Z : Scheme.{0}} {g h : Z ⟶ Spec (CommRingCat.of (Polynomial ℤ))}
    (e : g.appTop.hom coord = h.appTop.hom coord) : g = h := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv]
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext'
  · exact RingHom.ext_int _ _
  · exact e

theorem exists_hom {Z : Scheme.{0}} (f : Γ(Z, ⊤)) :
    ∃ g : Z ⟶ Spec (CommRingCat.of (Polynomial ℤ)), g.appTop.hom coord = f := by
  let φ : CommRingCat.of (Polynomial ℤ) ⟶ Γ(Z, ⊤) :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) f)
  refine ⟨ΓSpec.adjunction.homEquiv Z (Opposite.op _) φ.op, ?_⟩
  have := congrArg (fun ψ => ψ.hom Polynomial.X) (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ)
  refine this.trans ?_
  simp [φ]

theorem comp_appTop_apply {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom a = g.appTop.hom (h.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem appTop_injective {X Y : Scheme.{0}} (π : X ⟶ Y) [Epi π] :
    Function.Injective π.appTop.hom := by
  intro a b hab
  obtain ⟨g, rfl⟩ := exists_hom a
  obtain ⟨h, rfl⟩ := exists_hom b
  rw [← comp_appTop_apply, ← comp_appTop_apply] at hab
  rw [(cancel_epi π).1 (hom_ext hab)]

theorem exists_appTop_eq {X Y : Scheme.{0}} (π : X ⟶ Y) [EffectiveEpi π] (f : Γ(X, ⊤))
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X), g₁ ≫ π = g₂ ≫ π →
      g₁.appTop.hom f = g₂.appTop.hom f) :
    ∃ a, π.appTop.hom a = f := by
  obtain ⟨g, rfl⟩ := exists_hom f
  have H : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ X), g₁ ≫ π = g₂ ≫ π → g₁ ≫ g = g₂ ≫ g := by
    intro Z g₁ g₂ e
    apply hom_ext
    rw [comp_appTop_apply, comp_appTop_apply]
    exact hf Z g₁ g₂ e
  refine ⟨(EffectiveEpi.desc π g H).appTop.hom coord, ?_⟩
  rw [← comp_appTop_apply, EffectiveEpi.fac]

noncomputable def res {X : Scheme.{0}} (U : X.Opens) : Γ(X, U) ⟶ Γ(U.toScheme, ⊤) :=
  U.ι.appLE U ⊤ (by simp)

theorem res_bijective {X : Scheme.{0}} (U : X.Opens) : Function.Bijective (res U).hom := by
  have : res U = U.topIso.inv := by
    simp [res, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  rw [this]
  exact U.topIso.symm.commRingCatIsoToRingEquiv.bijective

theorem res_comp_appTop {X Z : Scheme.{0}} (U : X.Opens) (g : Z ⟶ U.toScheme) (k : Z ⟶ X)
    (e : k = g ≫ U.ι) (h : ⊤ ≤ k ⁻¹ᵁ U) :
    res U ≫ g.appTop = k.appLE U ⊤ h := by
  subst e
  rw [res, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _

theorem res_square {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) :
    res U ≫ (π ∣_ U).appTop = π.app U ≫ res (π ⁻¹ᵁ U) := by
  rw [res_comp_appTop U (π ∣_ U) ((π ⁻¹ᵁ U).ι ≫ π) (morphismRestrict_ι π U).symm (by simp),
    res, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

theorem res_square_apply {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) :
    (π ∣_ U).appTop.hom ((res U).hom a) = (res (π ⁻¹ᵁ U)).hom ((π.app U).hom a) :=
  congrArg (fun ψ => ψ.hom a) (res_square π U)

theorem app_injective {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π] (U : Y.Opens) :
    Function.Injective (π.app U).hom := by
  have : Surjective (π ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  have : Epi (π ∣_ U) := Flat.epi_of_flat_of_surjective _
  intro a b hab
  apply (res_bijective U).1
  apply appTop_injective (π ∣_ U)
  rw [res_square_apply, res_square_apply, hab]

theorem isUnit_of_isUnit_app {X Y : Scheme.{0}} (π : X ⟶ Y) [Surjective π] (U : Y.Opens)
    (a : Γ(Y, U)) (ha : IsUnit ((π.app U).hom a)) : IsUnit a := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ U a fun y hy => ?_
  obtain ⟨x, rfl⟩ := π.surjective y
  have h1 : X.basicOpen ((π.app U).hom a) = π ⁻¹ᵁ U := X.basicOpen_of_isUnit ha
  have h2 : x ∈ π ⁻¹ᵁ (Y.basicOpen a) := by
    rw [Scheme.preimage_basicOpen]
    exact h1.ge hy
  exact (Y.mem_basicOpen a (π x) hy).1 h2

theorem exists_app_eq {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π] [QuasiCompact π]
    (U : Y.Opens) (f : Γ(X, π ⁻¹ᵁ U))
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (h₁ : ⊤ ≤ g₁ ⁻¹ᵁ (π ⁻¹ᵁ U))
      (h₂ : ⊤ ≤ g₂ ⁻¹ᵁ (π ⁻¹ᵁ U)), g₁ ≫ π = g₂ ≫ π →
      (g₁.appLE _ ⊤ h₁).hom f = (g₂.appLE _ ⊤ h₂).hom f) :
    ∃ a, (π.app U).hom a = f := by
  have : Surjective (π ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  obtain ⟨b, hb⟩ := exists_appTop_eq (π ∣_ U) ((res (π ⁻¹ᵁ U)).hom f) (by
    intro Z g₁ g₂ e
    have k : ∀ g : Z ⟶ (π ⁻¹ᵁ U).toScheme, ⊤ ≤ (g ≫ (π ⁻¹ᵁ U).ι) ⁻¹ᵁ (π ⁻¹ᵁ U) := by
      intro g; simp
    have := hf Z (g₁ ≫ (π ⁻¹ᵁ U).ι) (g₂ ≫ (π ⁻¹ᵁ U).ι) (k _) (k _) (by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% e])
    rw [← res_comp_appTop _ g₁ _ rfl, ← res_comp_appTop _ g₂ _ rfl] at this
    exact this)
  obtain ⟨a, rfl⟩ := (res_bijective U).2 b
  refine ⟨a, (res_bijective _).1 ?_⟩
  rw [← res_square_apply, hb]

end GlobalTheory.FunDescent

namespace GlobalTheory

theorem invariant_functions_descend :
    ∀ (S : Scheme.{0}) (G B T : Over S) [GrpObj G] [GrpObj B] [GrpObj T] (q : G ⟶ B) (i : T ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∀ (U : B.left.Opens), Function.Injective (q.left.app U).hom ∧ (∀ a : Γ(B.left, U), IsUnit ((q.left.app U).hom a) → IsUnit a) ∧ ∀ f : Γ(G.left, q.left ⁻¹ᵁ U), (∀ (Z : Over S) (t : Z ⟶ T) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ U)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ U)), (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom f = (g.left.appLE _ ⊤ h₂).hom f) → ∃ a : Γ(B.left, U), (q.left.app U).hom a = f := by
  intro S G B T _ _ _ q i hq hi _ _ _ hP U
  refine ⟨FunDescent.app_injective _ U, FunDescent.isUnit_of_isUnit_app _ U, fun f hf => ?_⟩
  refine FunDescent.exists_app_eq q.left U f fun Z g₁ g₂ h₁ h₂ e => ?_
  let Z' : Over S := Over.mk (g₂ ≫ G.hom)
  let k₂ : Z' ⟶ G := Over.homMk g₂ rfl
  let k₁ : Z' ⟶ G := Over.homMk g₁ (by
    change g₁ ≫ G.hom = g₂ ≫ G.hom
    rw [← Over.w q, reassoc_of% e])
  have e' : k₁ ≫ q = k₂ ≫ q := Over.OverMorphism.ext e
  have w : (k₁ * k₂⁻¹) ≫ q = toUnit Z' ≫ η[B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
    rfl
  have ht : (hP.lift _ _ w ≫ i) * k₂ = k₁ := by
    rw [hP.lift_fst, inv_mul_cancel_right]
  have := hf Z' (hP.lift _ _ w) k₂
  rw [ht] at this
  exact this h₁ h₂

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.eq_comp_section_of_surjective_appTop {X T Y : Scheme.{0}} [IsAffine Y] (p : X ⟶ T)
    (ε : T ⟶ X) (g : X ⟶ Y) (h : ε ≫ p = 𝟙 T) (hs : Function.Surjective p.appTop.hom) :
    g = p ≫ ε ≫ g := by
  refine ext_of_isAffine ?_
  ext a
  obtain ⟨b, hb⟩ := hs (g.appTop.hom a)
  have hεp : ε.appTop.hom (p.appTop.hom b) = b := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, h]
    simp
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [← hb, hεp]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.local_rigidity : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g := by
  intro X T Y p ε g h hp hsurj t y hfib
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have hZ : IsClosed (p '' (g ⁻¹ᵁ W : Set X)ᶜ) :=
    p.isClosedMap _ (g ⁻¹ᵁ W).isOpen.isClosed_compl
  let V : T.Opens := ⟨(p '' (g ⁻¹ᵁ W : Set X)ᶜ)ᶜ, hZ.isOpen_compl⟩
  have htV : t ∈ V := by
    rintro ⟨x, hx, rfl⟩
    exact hx (show g x ∈ W from (hfib x rfl).symm ▸ hyW)
  have hsub : p ⁻¹ᵁ V ≤ g ⁻¹ᵁ W := by
    intro x hx
    by_contra hxW
    exact hx ⟨x, hxW, rfl⟩
  have hεV : V ≤ ε ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    intro s hs
    change p (ε s) ∈ V
    rw [← Scheme.Hom.comp_apply, h]
    exact hs
  haveI : IsAffine W := hW
  refine ⟨V, htV, ?_⟩
  have hsec : ε.resLE (p ⁻¹ᵁ V) V hεV ≫ p ∣_ V = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, h]
    simp
  have hsV : Function.Surjective (p ∣_ V).appTop.hom := by
    rw [morphismRestrict_appTop]
    have hiso := ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)
    exact hiso.2.comp (hsurj (V.ι ''ᵁ ⊤))
  have key := congrArg (· ≫ W.ι)
    (_root_.GlobalTheory.eq_comp_section_of_surjective_appTop (p ∣_ V) (ε.resLE (p ⁻¹ᵁ V) V hεV)
      (g.resLE W (p ⁻¹ᵁ V) hsub) hsec hsV)
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι] at key
  rw [key, Scheme.Hom.resLE_comp_ι_assoc, ← Category.assoc (p ∣_ V), morphismRestrict_ι,
    Category.assoc]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothDescent

open TensorProduct

theorem exists_common_model (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B]
    [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] :
    ∃ (A B₁ C₁ : Type) (_ : CommRing A) (_ : Algebra A R) (_ : CommRing B₁) (_ : CommRing C₁)
      (_ : Algebra A B₁) (_ : Algebra A C₁), IsNoetherianRing A ∧ Algebra.Smooth A B₁ ∧
      Algebra.Smooth A C₁ ∧ Nonempty (R ⊗[A] B₁ ≃ₐ[R] B) ∧ Nonempty (R ⊗[A] C₁ ≃ₐ[R] C) := by
  obtain ⟨A₁, B₁, _, _, hA₁, _, ⟨eB⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R B
  obtain ⟨A₂, C₁, _, _, hA₂, _, ⟨eC⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R C
  let A : Subalgebra ℤ R := A₁ ⊔ A₂
  let : Algebra A₁ A := (Subalgebra.inclusion (le_sup_left : A₁ ≤ A)).toRingHom.toAlgebra
  let : Algebra A₂ A := (Subalgebra.inclusion (le_sup_right : A₂ ≤ A)).toRingHom.toAlgebra
  have : IsScalarTower A₁ A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A₂ A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType ℤ A := (Subalgebra.fg_iff_finiteType A).mp (hA₁.sup hA₂)
  exact ⟨A, A ⊗[A₁] B₁, A ⊗[A₂] C₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ A, inferInstance,
    inferInstance, ⟨(Algebra.TensorProduct.cancelBaseChange A₁ A R R B₁).trans eB.symm⟩,
    ⟨(Algebra.TensorProduct.cancelBaseChange A₂ A R R C₁).trans eC.symm⟩⟩

variable {A R B₁ C₁ : Type} [CommRing A] [CommRing R] [CommRing B₁] [CommRing C₁] [Algebra A R]
  [Algebra A B₁] [Algebra A C₁]

noncomputable abbrev incl (C₁ : Type) [CommRing C₁] [Algebra A C₁] (S : Subalgebra A R) :
    S ⊗[A] C₁ →ₐ[A] R ⊗[A] C₁ :=
  Algebra.TensorProduct.map S.val (AlgHom.id A C₁)

theorem range_incl_mono {S T : Subalgebra A R} (h : S ≤ T) :
    (incl C₁ S).range ≤ (incl C₁ T).range := by
  have e : incl C₁ S = (incl C₁ T).comp
      (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A C₁)) :=
    Algebra.TensorProduct.ext' fun _ _ => rfl
  rw [e]
  exact AlgHom.range_comp_le_range _ _

theorem exists_fg_mem_range_incl (x : R ⊗[A] C₁) :
    ∃ S : Subalgebra A R, S.FG ∧ x ∈ (incl C₁ S).range := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Subalgebra.fg_bot, zero_mem _⟩
  | tmul r c =>
    exact ⟨Algebra.adjoin A {r}, ⟨{r}, by simp⟩,
      (AlgHom.mem_range _).mpr ⟨⟨r, Algebra.subset_adjoin rfl⟩ ⊗ₜ c, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨S, hS, hxS⟩ := hx
    obtain ⟨T, hT, hyT⟩ := hy
    exact ⟨S ⊔ T, hS.sup hT,
      add_mem (range_incl_mono le_sup_left hxS) (range_incl_mono le_sup_right hyT)⟩

theorem exists_fg_subset_range_incl (t : Finset (R ⊗[A] C₁)) :
    ∃ S : Subalgebra A R, S.FG ∧ (t : Set (R ⊗[A] C₁)) ⊆ (incl C₁ S).range := by
  classical
  refine Finset.induction_on t ⟨⊥, Subalgebra.fg_bot, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨S, hS, hSt⟩ := ih
  obtain ⟨T, hT, haT⟩ := exists_fg_mem_range_incl (C₁ := C₁) a
  refine ⟨S ⊔ T, hS.sup hT, ?_⟩
  rw [Finset.coe_insert, Set.insert_subset_iff]
  exact ⟨range_incl_mono le_sup_right haT,
    hSt.trans (SetLike.coe_subset_coe.mpr (range_incl_mono le_sup_left))⟩

theorem exists_fg_range_le [Algebra.FiniteType A B₁] (φ : B₁ →ₐ[A] R ⊗[A] C₁) :
    ∃ S : Subalgebra A R, S.FG ∧ φ.range ≤ (incl C₁ S).range := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A B₁).FG)
  obtain ⟨S, hS, hsub⟩ := exists_fg_subset_range_incl (C₁ := C₁) (s.image φ)
  refine ⟨S, hS, ?_⟩
  rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rwa [Finset.coe_image] at hsub

theorem incl_injective [Module.Flat A C₁] (S : Subalgebra A R) :
    Function.Injective (incl C₁ S) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) S.val.toLinearMap
    Subtype.val_injective

theorem exists_lift {D E : Type} [CommRing D] [CommRing E] [Algebra A D] [Algebra A E]
    (φ : B₁ →ₐ[A] E) (i : D →ₐ[A] E) (hi : Function.Injective i) (h : φ.range ≤ i.range) :
    ∃ ψ : B₁ →ₐ[A] D, ∀ b, i (ψ b) = φ b := by
  let e := AlgEquiv.ofInjective i hi
  let φ' := φ.codRestrict i.range fun b => h (AlgHom.mem_range_self φ b)
  refine ⟨e.symm.toAlgHom.comp φ', fun b => ?_⟩
  have h1 : ((e (e.symm (φ' b)) : i.range) : E) = (φ' b : E) := by rw [e.apply_symm_apply]
  exact h1

theorem cancel_one_tmul (S : Subalgebra A R) (x : S ⊗[A] C₁) :
    Algebra.TensorProduct.cancelBaseChange A S R R C₁ (1 ⊗ₜ x) = incl C₁ S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s c => simp [Algebra.TensorProduct.cancelBaseChange_tmul, incl, Algebra.smul_def]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add (f := _), hx, hy, map_add (f := _)]

theorem incl_tmul (S : Subalgebra A R) (s : S) (c : C₁) :
    incl C₁ S (s ⊗ₜ c) = (s : R) • ((1 : R) ⊗ₜ[A] c) := by
  simp [incl, TensorProduct.smul_tmul']

theorem incl_smul (S : Subalgebra A R) (s : S) (x : S ⊗[A] C₁) :
    incl C₁ S (s • x) = (s : R) • incl C₁ S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s' c => simp [incl, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

noncomputable def extend (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) : S ⊗[A] B₁ →ₐ[S] D :=
  Algebra.TensorProduct.lift (Algebra.ofId S D) ψ fun _ _ => Commute.all _ _

theorem extend_tmul (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) (s : S) (b : B₁) :
    extend S ψ (s ⊗ₜ b) = s • ψ b := by
  simp [extend, Algebra.smul_def]

theorem incl_extend (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁)
    (ψ : B₁ →ₐ[A] S ⊗[A] C₁) (h : ∀ b, incl C₁ S (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    incl C₁ S (extend S ψ x) = F (incl B₁ S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => rw [extend_tmul, incl_smul, h, incl_tmul, map_smul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

theorem val_extend (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R)
    (ψ : B₁ →ₐ[A] S) (h : ∀ b, S.val (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    S.val (extend S ψ x) = F (incl B₁ S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
    rw [extend_tmul, smul_eq_mul, map_mul, h, incl_tmul, map_smul, smul_eq_mul]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

end GlobalTheory.SmoothDescent

namespace GlobalTheory

open TensorProduct SmoothDescent

theorem exists_noetherian_model_of_smooth :
    ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] (f g : B →ₐ[R] C) (r : B →ₐ[R] R), ∃ (R₀ B₀ C₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (_ : Algebra R₀ R) (_ : CommRing B₀) (_ : CommRing C₀) (_ : Algebra R₀ B₀) (_ : Algebra R₀ C₀) (f₀ g₀ : B₀ →ₐ[R₀] C₀) (r₀ : B₀ →ₐ[R₀] R₀) (β' : TensorProduct R₀ R B₀ ≃ₐ[R] B) (δ' : TensorProduct R₀ R C₀ ≃ₐ[R] C), Module.Flat R₀ B₀ ∧ Module.Flat R₀ C₀ ∧ ∀ b : B₀, f (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ f₀ b) ∧ g (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ g₀ b) ∧ r (β' (1 ⊗ₜ b)) = algebraMap R₀ R (r₀ b) := by
  intro R B C _ _ _ _ _ _ _ f g r
  obtain ⟨A, B₁, C₁, _, _, _, _, _, _, hA, hB, hC, ⟨eB⟩, ⟨eC⟩⟩ := exists_common_model R B C
  let F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁ := (eC.symm.toAlgHom.comp f).comp eB.toAlgHom
  let G : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁ := (eC.symm.toAlgHom.comp g).comp eB.toAlgHom
  let ρ : R ⊗[A] B₁ →ₐ[R] R := r.comp eB.toAlgHom
  let j : B₁ →ₐ[A] R ⊗[A] B₁ := Algebra.TensorProduct.includeRight
  let φF : B₁ →ₐ[A] R ⊗[A] C₁ := (F.restrictScalars A).comp j
  let φG : B₁ →ₐ[A] R ⊗[A] C₁ := (G.restrictScalars A).comp j
  let φr : B₁ →ₐ[A] R := (ρ.restrictScalars A).comp j
  obtain ⟨S₁, hS₁, h₁⟩ := exists_fg_range_le (C₁ := C₁) φF
  obtain ⟨S₂, hS₂, h₂⟩ := exists_fg_range_le (C₁ := C₁) φG
  have h₃ : φr.range.FG := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map φr Algebra.FiniteType.out
  let S : Subalgebra A R := S₁ ⊔ S₂ ⊔ φr.range
  have : Algebra.FiniteType A S := (Subalgebra.fg_iff_finiteType S).mp ((hS₁.sup hS₂).sup h₃)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing A S
  have hF : φF.range ≤ (incl C₁ S).range :=
    h₁.trans (range_incl_mono (le_sup_left.trans le_sup_left))
  have hG : φG.range ≤ (incl C₁ S).range :=
    h₂.trans (range_incl_mono (le_sup_right.trans le_sup_left))
  have hr : φr.range ≤ S.val.range := by
    rw [Subalgebra.range_val]
    exact le_sup_right
  obtain ⟨ψF, hψF⟩ := exists_lift φF (incl C₁ S) (incl_injective S) hF
  obtain ⟨ψG, hψG⟩ := exists_lift φG (incl C₁ S) (incl_injective S) hG
  obtain ⟨ψr, hψr⟩ := exists_lift φr S.val Subtype.val_injective hr
  refine ⟨S, S ⊗[A] B₁, S ⊗[A] C₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, extend S ψF, extend S ψG, extend S ψr,
    (Algebra.TensorProduct.cancelBaseChange A S R R B₁).trans eB,
    (Algebra.TensorProduct.cancelBaseChange A S R R C₁).trans eC, inferInstance, inferInstance,
    fun b => ⟨?_, ?_, ?_⟩⟩
  · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul,
      incl_extend S F ψF hψF]
    simp [F]
  · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul,
      incl_extend S G ψG hψG]
    simp [G]
  · rw [AlgEquiv.trans_apply, cancel_one_tmul]
    change _ = S.val (extend S ψr b)
    rw [val_extend S ρ ψr hψr]
    simp [ρ]

end GlobalTheory
end
