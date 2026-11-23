module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle010
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.extension_descends_of_isIntegral : ∀ (R R₂ : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (g : R →+* R₂) (gam : FractionRing R →+* FractionRing R₂), (∀ r, gam (algebraMap R _ r) = algebraMap R₂ _ (g r)) → g.IsIntegral → ∀ (X : Scheme.{0}) (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing R) ⟶ X) (χ₂ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R₂ ⟶ X), _root_.ReciprocityTheory.ChartRestriction.G.Out.jK R₂ ≫ χ₂ = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap gam ≫ y → ∃ χ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ X, _root_.ReciprocityTheory.ChartRestriction.G.Out.jK R ≫ χ = y ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap g ≫ χ = χ₂ := by
  intro R R₂ _ _ _ _ _ _ g gam hgam hint X y χ₂ hcomm
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap _root_.ReciprocityTheory.ChartRestriction.G.Out.jK at *
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := χ₂ (IsLocalRing.closedPoint R₂)) (U := ⊤) trivial
  have hmem : ∀ p, χ₂ p ∈ U := fun p =>
    ((IsLocalRing.specializes_closedPoint (R := R₂) p).map χ₂.continuous).mem_open U.2 hxU
  have h₂ : Set.range χ₂ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact hmem p
  have hy : Set.range y ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    let q : ↥(Spec (CommRingCat.of (FractionRing R₂))) :=
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
    have hp : (Spec.map (CommRingCat.ofHom gam)) q = p := Subsingleton.elim _ _
    have e := Scheme.Hom.comp_apply
      (Spec.map (CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂)))) χ₂ q
    rw [hcomm, Scheme.Hom.comp_apply, hp] at e
    rw [e]
    exact hmem _
  set χ₂' := IsOpenImmersion.lift U.ι χ₂ h₂ with hχ₂'
  set y' := IsOpenImmersion.lift U.ι y hy with hy'
  have hc' : Spec.map (CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂))) ≫ χ₂' =
      Spec.map (CommRingCat.ofHom gam) ≫ y' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hχ₂', hy', IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, hcomm]
  set a₂ := Spec.preimage (χ₂' ≫ hU.isoSpec.hom) with ha₂
  set b := Spec.preimage (y' ≫ hU.isoSpec.hom) with hb
  have hab : a₂ ≫ CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂)) =
      b ≫ CommRingCat.ofHom gam := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ha₂, hb, Spec.map_preimage, Spec.map_preimage,
      ← Category.assoc, ← Category.assoc, hc']
  have e1 : ∀ a, gam (b.hom a) = algebraMap R₂ _ (a₂.hom a) := fun a =>
    (congrArg (fun f => f.hom a) hab).symm
  have hcomp : gam.comp (algebraMap R (FractionRing R)) =
      (algebraMap R₂ (FractionRing R₂)).comp g :=
    RingHom.ext hgam
  have hpt : ∀ a, b.hom a ∈ (algebraMap R (FractionRing R)).range := by
    intro a
    obtain ⟨p, hpm, hp⟩ := hint (a₂.hom a)
    rw [RingHom.mem_range]
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    refine ⟨p, hpm, gam.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, e1, hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
  let e := RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
    ⟨fun u v h => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩
  let φ : Γ(X, U) →+* R := e.symm.toRingHom.comp (b.hom.codRestrict _ hpt)
  have hφ : ∀ a, algebraMap R (FractionRing R) (φ a) = b.hom a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply ⟨b.hom a, hpt a⟩)
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv ≫ U.ι, ?_, ?_⟩
  · have hφb : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = b := by
      ext a
      exact hφ a
    rw [← Category.assoc, ← Spec.map_comp, hφb, hb, Spec.map_preimage, Category.assoc,
      Iso.hom_inv_id_assoc, hy', IsOpenImmersion.lift_fac]
  · have hφa : CommRingCat.ofHom φ ≫ CommRingCat.ofHom g = a₂ := by
      ext a
      apply IsFractionRing.injective R₂ (FractionRing R₂)
      change algebraMap R₂ _ (g (φ a)) = algebraMap R₂ _ (a₂.hom a)
      rw [← hgam, hφ, e1]
    rw [← Category.assoc, ← Spec.map_comp, hφa, ha₂, Spec.map_preimage, Category.assoc,
      Iso.hom_inv_id_assoc, hχ₂', IsOpenImmersion.lift_fac]

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

open TensorProduct

namespace GlobalTheory

namespace GenericIso

theorem isIso_iff_of_isPullback {P X' Y X : Scheme.{0}} {a : P ⟶ X'} {b : P ⟶ Y} {h : X' ⟶ X}
    {g : Y ⟶ X} (H : IsPullback a b h g) : IsIso b ↔ IsIso (pullback.snd h g) := by
  rw [← H.isoPullback_hom_snd, isIso_comp_left_iff]

theorem isIso_snd_comp {X' Y X Z : Scheme.{0}} (h : X' ⟶ X) (g : Y ⟶ X) (k : Z ⟶ Y)
    (H : IsIso (pullback.snd h g)) : IsIso (pullback.snd h (k ≫ g)) := by
  have := (IsPullback.of_hasPullback (pullback.snd h g) k).paste_horiz
    (IsPullback.of_hasPullback h g)
  exact (isIso_iff_of_isPullback this).1 inferInstance

theorem isPullback_over {S T : Scheme.{0}} (t : T ⟶ S) {X' X : Over S} (h : X' ⟶ X) :
    IsPullback (pullback.fst X'.hom t) ((Over.pullback t).map h).left h.left
      (pullback.fst X.hom t) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback X.hom t)
  · have e : ((Over.pullback t).map h).left ≫ pullback.snd X.hom t = pullback.snd X'.hom t :=
      pullback.lift_snd _ _ _
    rw [e, Over.w h]
    exact IsPullback.of_hasPullback X'.hom t
  · exact (pullback.lift_fst _ _ _).symm

theorem isIso_over_iff {S T : Scheme.{0}} (t : T ⟶ S) {X' X : Over S} (h : X' ⟶ X) :
    IsIso ((Over.pullback t).map h) ↔ IsIso (pullback.snd h.left (pullback.fst X.hom t)) := by
  rw [← isIso_iff_of_isPullback (isPullback_over t h)]
  exact (isIso_iff_of_reflects_iso _ (Over.forget T)).symm

section Affine

variable {R A₀ A : Type} [CommRing R] [CommRing A₀] [CommRing A] [Algebra R A₀] [Algebra R A]
  (f : A₀ →ₐ[R] A) (B : Type) [CommRing B] [Algebra R B]

theorem isPullback_tensor (A : Type) [CommRing A] [Algebra R A] :
    IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R B A)).flip

theorem isPullback_tensor_map :
    IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R B) f).toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A₀)).toRingHom)) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_tensor B A₀)
  · convert isPullback_tensor (R := R) B A using 1
    · rw [← Spec.map_comp]
      congr 1
      ext b
      simp
    · rw [← Spec.map_comp]
      congr 1
      ext b
      simp
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1

theorem isIso_spec_iff {C D : Type} [CommRing C] [CommRing D] (φ : C →+* D) :
    IsIso (Spec.map (CommRingCat.ofHom φ)) ↔ Function.Bijective φ := by
  rw [isIso_SpecMap_iff]
  rfl

theorem bijective_of_faithfullyFlat (C : Type) [CommRing C] [Algebra R C] [Algebra B C]
    [IsScalarTower R B C] [Module.FaithfullyFlat B C]
    (H : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R C) f)) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R B) f) := by
  have e : LinearMap.lTensor C (f.toLinearMap.baseChange B) =
      ((AlgebraTensorModule.cancelBaseChange R B B C A).symm.toLinearMap ∘ₗ
        AlgebraTensorModule.lTensor B C f.toLinearMap) ∘ₗ
        (AlgebraTensorModule.cancelBaseChange R B B C A₀).toLinearMap := by
    ext
    simp
  have h1 : Function.Bijective (LinearMap.lTensor C (f.toLinearMap.baseChange B)) := by
    rw [e]
    exact ((AlgebraTensorModule.cancelBaseChange R B B C A).symm.bijective.comp H).comp
      (AlgebraTensorModule.cancelBaseChange R B B C A₀).bijective
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective B C _).1 h1

theorem bijective_residueField (K : Type) [Field K] [Algebra R K] (x : PrimeSpectrum R)
    (hx : x.asIdeal = RingHom.ker (algebraMap R K))
    (H : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R K) f)) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R x.asIdeal.ResidueField) f) := by
  have h1 : x.asIdeal ≤ RingHom.ker (algebraMap R K) := hx.le
  have h2 : x.asIdeal.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap R K) := fun r hr => by
    change IsUnit (algebraMap R K r)
    rw [isUnit_iff_ne_zero]
    intro h0
    exact hr (hx.ge h0)
  let : Algebra x.asIdeal.ResidueField K :=
    (Ideal.ResidueField.lift x.asIdeal (algebraMap R K) h1 h2).toAlgebra
  have : IsScalarTower R x.asIdeal.ResidueField K :=
    .of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap _ _ h1 h2 r).symm
  exact bijective_of_faithfullyFlat f _ K H

end Affine

end GenericIso

open GenericIso

theorem isIso_generic_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X' X : Over (Sp R))
      [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      (h : X' ⟶ X) [IsAffineHom h.left] (Sg : Set (Sp R)), Dense Sg →
      (∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
        IsIso ((Over.pullback t).map h)) → IsIso ((Over.pullback (Out.jK R)).map h) := by
  intro R _ _ _ X' X _ _ _ h _ Sg hD H
  rw [isIso_over_iff]
  refine IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms _)
    (X.left.affineCover.pullback₁ (pullback.fst X.hom (Out.jK R))) fun (i : X.left.affineCover.I₀) => ?_

  obtain ⟨A₀, u, hu₀, ⟨e, he⟩⟩ : ∃ (A₀ : CommRingCat.{0}) (u : Spec A₀ ⟶ X.left)
      (_ : IsOpenImmersion u), ∃ e : X.left.affineCover.X i ⟶ Spec A₀,
      e ≫ u = X.left.affineCover.f i :=
    ⟨_, (X.left.affineCover.X i).isoSpec.inv ≫ X.left.affineCover.f i, inferInstance,
      (X.left.affineCover.X i).isoSpec.hom, by simp⟩
  have : IsAffine (pullback h.left u) := isAffine_of_isAffineHom (pullback.snd h.left u)
  obtain ⟨A, j, hj, f, sq⟩ : ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X'.left)
      (_ : IsOpenImmersion j) (f : A₀ ⟶ A), IsPullback j (Spec.map f) h.left u := by
    obtain ⟨f, hf⟩ := Spec.map_surjective
      ((pullback h.left u).isoSpec.inv ≫ pullback.snd h.left u)
    refine ⟨_, (pullback h.left u).isoSpec.inv ≫ pullback.fst h.left u, inferInstance, f, ?_⟩
    rw [hf]
    exact IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩
      (pullback h.left u).isoSpec.symm rfl rfl
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ X.hom)
  let : Algebra R A₀ := φ.hom.toAlgebra
  let : Algebra R A := (φ ≫ f).hom.toAlgebra
  let F : A₀ →ₐ[R] A := ⟨f.hom, fun _ => rfl⟩
  have : Algebra.FiniteType R A₀ := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have : Algebra.FiniteType R A := by
    have : LocallyOfFiniteType (Spec.map (φ ≫ f)) := by
      rw [Spec.map_comp, hφ, ← Category.assoc, ← sq.w, Category.assoc, Over.w h]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap R A₀)) = u ≫ X.hom := hφ
  have key : ∀ (B : Type) [CommRing B] [Algebra R B],
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R B) F) ↔
      IsIso (pullback.snd h.left (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A₀)).toRingHom) ≫ u)) := by
    intro B _ _
    rw [← isIso_iff_of_isPullback ((isPullback_tensor_map F B).paste_horiz sq), isIso_spec_iff]
    rfl
  have hfib : ∀ x : PrimeSpectrum R, x ∈ (Sg : Set (PrimeSpectrum R)) → Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id R x.asIdeal.ResidueField) F) := by
    intro x hx
    obtain ⟨K, _, t, ht, hiso⟩ := H x hx
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
    let : Algebra R K := ψ.hom.toAlgebra
    refine bijective_residueField F K x ?_ ((key K).2 ?_)
    · have : Spec.map ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = x :=
        ht.le (Set.mem_range_self _)
      rw [← this]
      rfl
    · have w := (isPullback_tensor (R := R) K A₀).w
      rw [hφ', ← Category.assoc] at w
      have := isIso_snd_comp _ _ (pullback.lift _ _ w) ((isIso_over_iff _ h).1 hiso)
      rwa [pullback.lift_fst] at this
  obtain ⟨a, ha0, ha⟩ := exists_baseChange_injective_of_dense.{0} F hD fun x hx => (hfib x hx).1
  obtain ⟨b, hb0, hb⟩ := exists_baseChange_surjective_of_dense.{0} F hD fun x hx => (hfib x hx).2
  have hu : ∀ c : R, c ≠ 0 → IsUnit (algebraMap R (FractionRing R) c) := fun c hc =>
    IsLocalization.map_units (M := nonZeroDivisors R) _ ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩
  have hK := (key (FractionRing R)).1 ⟨ha _ (hu a ha0), hb _ (hu b hb0)⟩
  let q := pullback.fst X.hom (Out.jK R)
  have w : (pullback.snd q (X.left.affineCover.f i) ≫ e) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A₀)) =
      (pullback.fst q (X.left.affineCover.f i) ≫ pullback.snd X.hom (Out.jK R)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    rw [hφ', Category.assoc, reassoc_of% he, ← pullback.condition_assoc, Category.assoc,
      pullback.condition]
  have h3 := isIso_snd_comp _ _ ((isPullback_tensor (R := R) (FractionRing R) A₀).lift _ _ w) hK
  rw [IsPullback.lift_fst_assoc, Category.assoc, he, ← pullback.condition] at h3
  have sq2 := (IsPullback.of_hasPullback (pullback.snd h.left q)
    (pullback.fst q (X.left.affineCover.f i))).paste_horiz (IsPullback.of_hasPullback h.left q)
  exact (isIso_iff_of_isPullback sq2).2 h3

end GlobalTheory
end
