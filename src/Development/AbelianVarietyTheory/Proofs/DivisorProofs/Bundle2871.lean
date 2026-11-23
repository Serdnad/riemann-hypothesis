module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle025
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Mathlib.RingTheory.LocalRing.Module
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem finiteFlat_proper_baseChange_facts : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsFinite k ∧ QuasiCompact p' ∧ QuasiSeparated p' ∧ Function.Surjective k'.base ∧ IsClosedMap (p' ≫ k).base ∧ IsClosedMap p.base ∧ (∀ V : Y.Opens, IsAffineOpen V → IsCompact (p ⁻¹ᵁ V : Set Z) ∧ IsQuasiSeparated (p ⁻¹ᵁ V : Set Z)) ∧ ∃ (d : ℕ) (b : Fin d → R'), ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, ρ (c l) * b l := by
  intro R R' _ _ _ _ ρ hinj hfin hflat Z Y Z' Y' p p' y y' k k' hk hk' hp
  have h1 : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).mpr hfin
  have h2 : IsFinite k := MorphismProperty.of_isPullback (P := @IsFinite) hk.flip h1
  have h3 : IsProper p' := MorphismProperty.of_isPullback (P := @IsProper) hk' hp
  have h4 : Surjective (spMap ρ) :=
    ⟨RingHom.IsIntegral.comap_surjective hfin.to_isIntegral hinj⟩
  have h5 : Surjective k := MorphismProperty.of_isPullback (P := @Surjective) hk.flip h4
  have h6 : Surjective k' := MorphismProperty.of_isPullback (P := @Surjective) hk'.flip h5
  refine ⟨h2, inferInstance, inferInstance, h6.surj, (p' ≫ k).isClosedMap, p.isClosedMap, ?_, ?_⟩
  · intro V hV
    refine ⟨QuasiCompact.isCompact_preimage (f := p) _ V.isOpen hV.isCompact, ?_⟩
    haveI : IsAffine V := hV
    haveI : QuasiSeparatedSpace (p ⁻¹ᵁ V : Z.Opens).toScheme :=
      quasiSeparatedSpace_of_quasiSeparated (p ∣_ V)
    exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (p ⁻¹ᵁ V).isOpen).mpr this
  · letI := ρ.toAlgebra
    haveI : Module.Finite R R' := hfin
    haveI : Module.Flat R R' := hflat
    haveI : Module.Free R R' := Module.free_of_flat_of_isLocalRing
    let b := Module.finBasis R R'
    refine ⟨_, b, fun r' => ⟨b.repr r', ?_, ?_⟩⟩
    · exact (b.sum_repr r').symm
    · intro c hc
      have : r' = ∑ l, c l • b l := hc
      rw [this, b.repr_sum_self]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open scoped TensorProduct

namespace GlobalTheory.Mum

theorem mem_range_of_tmul_eq_tmul {R A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A]
    [IsDomain A] [Algebra R A] (hinj : Function.Injective (algebraMap R A)) (a : A) (ha : IsIntegral R a)
    (h : algebraMap A (FractionRing A) a ⊗ₜ[R] (1 : FractionRing A) =
      (1 : FractionRing A) ⊗ₜ[R] algebraMap A (FractionRing A) a) :
    a ∈ Set.range (algebraMap R A) := by
  have hRL : Function.Injective (algebraMap R (FractionRing A)) := by
    rw [IsScalarTower.algebraMap_eq R A (FractionRing A)]
    exact (IsFractionRing.injective A (FractionRing A)).comp hinj
  haveI : FaithfulSMul R (FractionRing A) := (faithfulSMul_iff_algebraMap_injective R _).mpr hRL
  letI : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra R (FractionRing A)
  haveI := FractionRing.isScalarTower_liftAlgebra R (FractionRing A)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (FractionRing R) (FractionRing A))
    (LinearMap.ker_eq_bot.mpr (algebraMap (FractionRing R) (FractionRing A)).injective)
  have hφ1 : φ 1 = 1 := by simpa using congr($hφ 1)
  let Φ : FractionRing A ⊗[R] FractionRing A →ₗ[R] FractionRing A :=
    LinearMap.mul' R (FractionRing A) ∘ₗ
      TensorProduct.map ((Algebra.linearMap (FractionRing R) (FractionRing A) ∘ₗ φ).restrictScalars R) LinearMap.id
  have key := congr(Φ $h)
  simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.restrictScalars_apply,
    Algebra.linearMap_apply, LinearMap.id_apply, LinearMap.mul'_apply, hφ1, map_one] at key
  replace key : algebraMap (FractionRing R) (FractionRing A) (φ (algebraMap A (FractionRing A) a)) =
      algebraMap A (FractionRing A) a := by
    convert key using 1
    · exact (_root_.mul_one _).symm
    · exact (_root_.one_mul _).symm
  have hint : IsIntegral R (φ (algebraMap A (FractionRing A) a)) := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R (FractionRing R) (FractionRing A))
      (algebraMap (FractionRing R) (FractionRing A)).injective]
    change IsIntegral R (algebraMap (FractionRing R) (FractionRing A) _)
    rw [key]
    exact ha.map (IsScalarTower.toAlgHom R A (FractionRing A))
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨r, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A), hr, key]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_range_appTop_of_fst_eq_snd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (S : Scheme.{0})
    (π : S ⟶ Sp R), IsProper π → IsIntegral S → Function.Injective π.appTop.hom → ∀ x : Γ(S, ⊤),
    (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom := by
  intro R _ _ _ S π hP hI hinj x hx
  obtain ⟨s⟩ : Nonempty S := hI.nonempty
  obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨s, hsU⟩⟩
  let res := S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
  have hres : Function.Injective res.hom := map_injective_of_isIntegral S _
  have happ : ∀ t, (π.appLE ⊤ U le_top).hom t = res.hom (π.appTop.hom t) := fun t => rfl
  let ρ : R →+* Γ(S, U) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ π.appLE ⊤ U le_top).hom
  letI : Algebra R Γ(S, U) := ρ.toAlgebra
  have hρ : ∀ t, (π.appLE ⊤ U le_top).hom t = algebraMap R Γ(S, U) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom t) := by
    intro t
    change _ = ρ _
    simp only [ρ, CommRingCat.hom_comp, RingHom.comp_apply]
    congr 1
    exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) t).symm
  have hρinj : Function.Injective (algebraMap R Γ(S, U)) := by
    intro a b hab
    have h1 : ∀ c, algebraMap R Γ(S, U) c = res.hom (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
      fun c => rfl
    rw [h1, h1] at hab
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective (hinj (hres hab))
  haveI : UniversallyClosed π := inferInstance
  have hxint : IsIntegral R (res.hom x) := by
    obtain ⟨p, hpm, hp⟩ := isIntegral_appTop_of_universallyClosed π x
    refine ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap R Γ(S, U)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = res.hom.comp π.appTop.hom := by
      ext t
      exact (hρ t).symm.trans (happ t)
    rw [hc, ← Polynomial.hom_eval₂, hp, map_zero]
  have H : IsPullback (pullback.fst π π) (pullback.snd π π) π π := IsPullback.of_hasPullback π π
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := U) (UX := U) le_top le_top rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H le_top le_top rfl (isAffineOpen_top _) hU hU)
  let j₁ : Γ(S, U) →+* FractionRing Γ(S, U) ⊗[R] FractionRing Γ(S, U) :=
    Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap Γ(S, U) (FractionRing Γ(S, U)))
  let j₂ : Γ(S, U) →+* FractionRing Γ(S, U) ⊗[R] FractionRing Γ(S, U) :=
    (Algebra.TensorProduct.includeRight : FractionRing Γ(S, U) →ₐ[R] _).toRingHom.comp
      (algebraMap Γ(S, U) (FractionRing Γ(S, U)))
  have hw : π.appLE ⊤ U le_top ≫ (CommRingCat.ofHom j₁ : Γ(S, U) ⟶ CommRingCat.of _) =
      π.appLE ⊤ U le_top ≫ (CommRingCat.ofHom j₂ : Γ(S, U) ⟶ CommRingCat.of _) := by
    ext t
    change j₁ ((π.appLE ⊤ U le_top).hom t) = j₂ ((π.appLE ⊤ U le_top).hom t)
    rw [hρ]
    show algebraMap Γ(S, U) (FractionRing Γ(S, U)) (algebraMap R Γ(S, U) _) ⊗ₜ[R] (1 : FractionRing Γ(S, U)) =
      (1 : FractionRing Γ(S, U)) ⊗ₜ[R] algebraMap Γ(S, U) (FractionRing Γ(S, U)) (algebraMap R Γ(S, U) _)
    rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hd1 := congr(($(po.inl_desc _ _ hw)).hom (res.hom x))
  have hd2 := congr(($(po.inr_desc _ _ hw)).hom (res.hom x))
  have e1 : ∀ (f : pullback π π ⟶ S) (h : pullback.fst π π ⁻¹ᵁ U ⊓ pullback.snd π π ⁻¹ᵁ U ≤ f ⁻¹ᵁ U),
      (f.appLE U _ h).hom (res.hom x) =
        ((pullback π π).presheaf.map (homOfLE (le_top : pullback.fst π π ⁻¹ᵁ U ⊓ pullback.snd π π ⁻¹ᵁ U ≤ ⊤)).op).hom
          (f.appTop.hom x) := by
    intro f h
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have hj : j₁ (res.hom x) = j₂ (res.hom x) := by
    refine hd1.symm.trans (Eq.trans ?_ hd2)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, e1, e1, hx]
  obtain ⟨r, hr⟩ := mem_range_of_tmul_eq_tmul hρinj _ hxint hj
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r, hres ?_⟩
  rw [← happ]
  exact hr

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LocIso

theorem isPullback_resLE_opensRange {W W' Y Z T S : Scheme.{0}} (π : Z ⟶ Y) (s : Z ⟶ T) (b : Y ⟶ S)
    (c : T ⟶ S) (i : W ⟶ Y) [IsOpenImmersion i] (k : W' ⟶ Z) (p : W' ⟶ W)
    (h₁ : IsPullback k p π i) (h₂ : IsPullback p (k ≫ s) (i ≫ b) c) :
    IsPullback (π.resLE i.opensRange (π ⁻¹ᵁ i.opensRange) le_rfl) ((π ⁻¹ᵁ i.opensRange).ι ≫ s)
      (i.opensRange.ι ≫ b) c := by
  let e : W ≅ i.opensRange.toScheme := IsOpenImmersion.isoOfRangeEq i i.opensRange.ι (by simp)
  have he : e.hom ≫ i.opensRange.ι = i := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hR : IsPullback (π.resLE i.opensRange (π ⁻¹ᵁ i.opensRange) le_rfl) (π ⁻¹ᵁ i.opensRange).ι
      i.opensRange.ι π := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; exact isPullback_morphismRestrict π _
  have hW : IsPullback (p ≫ e.hom) k i.opensRange.ι π := by
    refine IsPullback.of_iso h₁.flip (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [he]
  let φ := IsPullback.isoIsPullback _ _ hW hR
  refine IsPullback.of_iso h₂ φ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (IsPullback.isoIsPullback_hom_fst _ _ hW hR).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoIsPullback_hom_snd]
  · simp [← he]
  · simp

theorem isLocalization_tensor (R R' C' : Type) [CommRing R] [CommRing R'] [CommRing C'] [Algebra R R']
    [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (C : Subalgebra R C') (f g : C)
    (hcok : ∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val
      (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _))
    (hker : ∀ t : TensorProduct R C R', (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C')
      fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) :
    letI : Algebra (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) :=
      ((algebraMap C' _).comp (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C')
        fun _ _ => Commute.all _ _).toRingHom).toAlgebra
    IsLocalization (Submonoid.powers ((f * g) ⊗ₜ[R] (1 : R'))) (Localization.Away (algebraMap C C' (f * g))) := by
  set Φ := Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _ with hΦdef
  letI : Algebra (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) :=
    ((algebraMap C' _).comp Φ.toRingHom).toAlgebra
  have hΦ : ∀ c : C, Φ (c ⊗ₜ[R] (1 : R')) = algebraMap C C' c := fun c => by simp [Φ]
  have halg : ∀ t, algebraMap (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) t =
      algebraMap C' _ (Φ t) := fun t => rfl
  have hpow : ∀ n : ℕ, ((f * g) ⊗ₜ[R] (1 : R')) ^ n = ((g ^ n) ⊗ₜ[R] (1 : R')) * ((f ^ n) ⊗ₜ[R] (1 : R')) := by
    intro n
    rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_pow, one_pow, _root_.mul_one, _root_.mul_comm (g ^ n)]
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [halg, map_pow, hΦ, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow n
  · intro z
    obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap C C' (f * g))) z
    obtain ⟨k, t, ht⟩ := hcok a
    refine ⟨⟨t * ((g ^ k) ⊗ₜ[R] (1 : R')), ⟨((f * g) ⊗ₜ[R] (1 : R')) ^ (m + k), m + k, rfl⟩⟩, ?_⟩
    rw [halg, halg, map_pow Φ, hΦ, map_mul Φ, hΦ, ht, pow_add, map_mul (algebraMap C' _), ← _root_.mul_assoc, hz,
      ← map_mul (algebraMap C' _)]
    refine congrArg (algebraMap C' _) ?_
    have hco : ∀ c : C, algebraMap C C' c = (c : C') := fun _ => rfl
    simp only [hco, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    ring
  · intro x y hxy
    rw [halg, halg] at hxy
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap C C' (f * g))) hxy
    have h0 : Φ (((f * g) ⊗ₜ[R] (1 : R')) ^ m * (x - y)) = 0 := by
      rw [map_mul, map_pow, hΦ, map_sub, mul_sub]
      exact sub_eq_zero.mpr hm
    obtain ⟨n, hn⟩ := hker _ h0
    refine ⟨⟨((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m), n + m, rfl⟩, ?_⟩
    change ((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m) * x = ((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m) * y
    rw [← sub_eq_zero, ← mul_sub, pow_add, hpow, _root_.mul_assoc, _root_.mul_assoc, hn, mul_zero]

theorem exists_smooth_basicOpen_iso : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X : Over (Sp R)) (Z : Scheme.{0}) (π : Z ⟶ X.left) (s : Z ⟶ Sp R') (hX : π ≫ X.hom = s ≫ spMap (algebraMap R R')) (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (C : Subalgebra R C') (j : Sp C' ⟶ Z) (l : Sp C ⟶ X.left) [IsOpenImmersion l], IsPullback j (spMap (algebraMap C C')) π l → j ≫ s = spMap (algebraMap R' C') → l ≫ X.hom = spMap (algebraMap R C) → ∀ f g : C, (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) → (∀ t : TensorProduct R C R', (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) → Algebra.Smooth R (Localization.Away g) → ∀ q : Sp C, f ∉ q.asIdeal → g ∉ q.asIdeal → ∃ V : X.left.Opens, l q ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ s) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap (algebraMap R R'))) := by
  intro R R' _ _ _ X Z π s hX C' _ _ _ _ C j l _ hP hj hl f g hcok hker hsm q hf hg
  let A := Localization.Away (f * g)
  let A' := Localization.Away (algebraMap C C' (f * g))
  let φ : A →+* A' := IsLocalization.Away.map A A' (algebraMap C C') (f * g)
  have hφ : φ.comp (algebraMap C A) = (algebraMap C' A').comp (algebraMap C C') := IsLocalization.map_comp _
  have hLoc : IsPushout (CommRingCat.ofHom (algebraMap C C')) (CommRingCat.ofHom (algebraMap C A))
      (CommRingCat.ofHom (algebraMap C' A')) (CommRingCat.ofHom φ) := by
    have : IsLocalization ((Submonoid.powers (f * g)).map (algebraMap C C')) A' := by
      rw [Submonoid.map_powers]; infer_instance
    exact CommRingCat.isPushout_of_isLocalization _ _ hφ (Submonoid.powers (f * g))
  haveI : IsOpenImmersion (spMap (algebraMap C A)) := IsOpenImmersion.of_isLocalization (f * g)
  have h₁ : IsPullback (spMap (algebraMap C' A') ≫ j) (spMap φ) π (spMap (algebraMap C A) ≫ l) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ hLoc).paste_horiz hP
  have hRing : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R' A')) := by
    let Φ := Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _
    letI : Algebra (TensorProduct R C R') A' := ((algebraMap C' A').comp Φ.toRingHom).toAlgebra
    have hL := isLocalization_tensor R R' C' C f g hcok hker
    have Q1 := CommRingCat.isPushout_tensorProduct R C R'
    have : IsLocalization ((Submonoid.powers (f * g)).map
        (Algebra.TensorProduct.includeLeftRingHom : C →+* TensorProduct R C R')) A' := by
      rw [Submonoid.map_powers]; exact hL
    have H : φ.comp (algebraMap C A) = (algebraMap (TensorProduct R C R') A').comp
        Algebra.TensorProduct.includeLeftRingHom := by
      rw [hφ]
      ext c
      simp [RingHom.algebraMap_toAlgebra, Φ]
    have Q2 := CommRingCat.isPushout_of_isLocalization (S := TensorProduct R C R') (Rₘ := A) (Sₘ := A')
      Algebra.TensorProduct.includeLeftRingHom φ H (Submonoid.powers (f * g))
    have Q := (Q1.flip.paste_vert Q2).flip
    convert Q using 1
    · ext r; simp [RingHom.algebraMap_toAlgebra, Φ, ← IsScalarTower.algebraMap_apply]
  have hs : (spMap (algebraMap C' A') ≫ j) ≫ s = spMap (algebraMap R' A') := by
    rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hb : (spMap (algebraMap C A) ≫ l) ≫ X.hom = spMap (algebraMap R A) := by
    rw [Category.assoc, hl, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h₂ : IsPullback (spMap φ) ((spMap (algebraMap C' A') ≫ j) ≫ s)
      ((spMap (algebraMap C A) ≫ l) ≫ X.hom) (spMap (algebraMap R R')) := by
    rw [hs, hb]; exact isPullback_SpecMap_of_isPushout _ _ _ _ hRing
  have hG := isPullback_resLE_opensRange π s X.hom (spMap (algebraMap R R')) _ _ _ h₁ h₂
  refine ⟨(spMap (algebraMap C A) ≫ l).opensRange, ?_, isAffineOpen_opensRange _, ?_, ?_⟩
  · obtain ⟨w, hw⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C A)) := by
      rw [PrimeSpectrum.localization_away_comap_range A (f * g)]
      exact fun h => (q.isPrime.mem_or_mem h).elim hf hg
    refine ⟨w, ?_⟩
    first
      | exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg l hw)
      | exact (Scheme.comp_base_apply _ _ _).trans (congrArg l hw)
      | exact congrArg l hw
  · let B := Localization.Away (algebraMap C (Localization.Away g) f)
    haveI : Algebra.Smooth R B := Algebra.Smooth.comp R (Localization.Away g) B
    haveI : Algebra.Smooth R A :=
      Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (f * g)) B A).restrictScalars R)
    haveI : Smooth (spMap (algebraMap R A)) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
    let e := IsOpenImmersion.isoOfRangeEq (spMap (algebraMap C A) ≫ l)
      (spMap (algebraMap C A) ≫ l).opensRange.ι (by simp)
    have hfac : e.hom ≫ (spMap (algebraMap C A) ≫ l).opensRange.ι = spMap (algebraMap C A) ≫ l :=
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have : (spMap (algebraMap C A) ≫ l).opensRange.ι ≫ X.hom = e.inv ≫ spMap (algebraMap R A) := by
      calc _ = e.inv ≫ (e.hom ≫ (spMap (algebraMap C A) ≫ l).opensRange.ι) ≫ X.hom := by simp
        _ = _ := by rw [hfac, hb]
    rw [this]; infer_instance
  · convert (inferInstance : IsIso hG.isoPullback.hom)
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hG.isoPullback_hom_fst.symm
    · exact (pullback.lift_snd _ _ _).trans hG.isoPullback_hom_snd.symm

end GlobalTheory.Mum.LocIso
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_separable_point_of_smooth : ∀ (R : Type) [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom →
    ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra (ResidueField R) k') (_ : Module.Finite (ResidueField R) k')
      (_ : Algebra.IsSeparable (ResidueField R) k') (x : Sp k' ⟶ U.left),
      x ≫ U.hom = spMap ((algebraMap (ResidueField R) k').comp (residue R)) ∧ Set.range x ⊆ O := by
  intro R _ _ U hU O hO
  obtain ⟨W, _, _, _, ε, y, hy, hyO⟩ := GlobalTheory.exists_etale_point_of_smooth U.hom R
    (SeparableClosure (ResidueField R)) (𝟙 _) O (by obtain ⟨u, hu, e⟩ := hO; exact ⟨u, hu, e⟩)
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R W).FG)
  let k' : IntermediateField (ResidueField R) (SeparableClosure (ResidueField R)) :=
    IntermediateField.adjoin (ResidueField R) (ε '' (s : Set W))
  have hfin : FiniteDimensional (ResidueField R) k' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hsep : Algebra.IsSeparable (ResidueField R) k' := Algebra.IsSeparable.of_algHom _ _ k'.val
  have hle : Algebra.adjoin R (s : Set W) ≤ (k'.toSubalgebra.restrictScalars R).comap ε :=
    Algebra.adjoin_le fun w hw => IntermediateField.subset_adjoin _ _ ⟨w, hw, rfl⟩
  have hmem : ∀ w, ε w ∈ k' := fun w => hle (hs ▸ Algebra.mem_top)
  let g : W →+* k' := ε.toRingHom.codRestrict k' hmem
  set_option synthInstance.maxHeartbeats 200000 in
    refine ⟨k', inferInstance, inferInstance, hfin, hsep, Spec.map (CommRingCat.ofHom g) ≫ y, ?_, ?_⟩
  · rw [Category.assoc, hy, Category.comp_id, ← Spec.map_comp]
    congr 2
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    congr 1
    change ε (algebraMap R W r) = algebraMap (ResidueField R) _ (residue R r)
    rw [ε.commutes]
    exact IsScalarTower.algebraMap_apply R (ResidueField R) _ r
  · rintro _ ⟨z, rfl⟩
    exact hyO ⟨_, rfl⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.HenselLift

theorem exists_lift_mem_open (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
    (hc : IsAdicComplete (maximalIdeal R') R') (ρ : R →+* R') (U : Over (Sp R)) (hU : Smooth U.hom)
    (x₀ : Sp (ResidueField R') ⟶ U.left) (hx : x₀ ≫ U.hom = spMap ((residue R').comp ρ))
    (O : U.left.Opens) (hO : Set.range x₀ ⊆ O) :
    ∃ a : Sp R' ⟶ U.left, a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  obtain ⟨y, hy⟩ : ∃ y, x₀ (closedPoint (ResidueField R')) = y := ⟨_, rfl⟩
  obtain ⟨α, hs, hα⟩ := GlobalTheory.HenselZero.exists_formallySmooth_stalk (O := CommRingCat.of R) U.hom y
  obtain ⟨χ₀, hχ₀⟩ := GlobalTheory.HenselZero.exists_factor_stalk (T := CommRingCat.of (ResidueField R')) x₀ (y := y) hy
  letI := α.hom.toAlgebra
  letI := ρ.toAlgebra
  haveI : Algebra.FormallySmooth R (U.left.presheaf.stalk y) := hs
  haveI := hc
  have e₁ : α ≫ χ₀ = CommRingCat.ofHom ((residue R').comp ρ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hχ₀, hx]
  let f : U.left.presheaf.stalk y →ₐ[R] R' ⧸ maximalIdeal R' :=
    { χ₀.hom with commutes' := fun r => congrArg (fun g => g.hom r) e₁ }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := maximalIdeal R') f
  have hg' : CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom (residue R') = χ₀ := by
    ext a
    exact congr($hg a)
  refine ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y, ?_, ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp]
    congr 1
    ext r
    exact g.commutes r
  · have hcl : (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y) (closedPoint R') = y := by
      have h1 : Spec.map (CommRingCat.ofHom (residue R')) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
          U.left.fromSpecStalk y = x₀ := by
        rw [← Spec.map_comp_assoc, hg', hχ₀]
      have h2 := congrArg (fun h => h (closedPoint (ResidueField R'))) h1
      simp only [Scheme.Hom.comp_apply] at h2
      rw [hy] at h2
      refine Eq.trans ?_ h2
      exact congrArg (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y)
        (comap_closedPoint (residue R')).symm
    rintro _ ⟨p, rfl⟩
    refine Specializes.mem_open ((specializes_closedPoint p).map (Scheme.Hom.continuous _)) O.isOpen ?_
    rw [hcl]
    exact hO ⟨_, hy⟩

end GlobalTheory.HenselLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem geomFibre_restrict_open_connected : ∀ (H Q Z : Scheme.{0}) (U : H.Opens) (f : H ⟶ Q) (ν : Z ⟶ Q), (∀ h : H, f h ∈ Set.range ν → h ∈ U) → ConnectedSpace (pullback f ν : Scheme.{0}) → ConnectedSpace (pullback (U.ι ≫ f) ν : Scheme.{0}) := by
  intro H Q Z U f ν hU hc
  have hs : IsIso (pullback.snd U.ι (pullback.fst f ν)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [Scheme.Hom.opensRange_pullbackSnd]
    refine top_unique fun z _ => ?_
    show pullback.fst f ν z ∈ U.ι.opensRange
    rw [Scheme.Opens.opensRange_ι]
    refine hU _ ⟨pullback.snd f ν z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  let e := Scheme.homeoOfIso ((pullbackRightPullbackFstIso f ν U.ι).symm ≪≫
    asIso (pullback.snd U.ι (pullback.fst f ν)))
  exact e.connectedSpace_iff.2 hc

end GlobalTheory.Mum
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.finite_flat_local_baseChange_of_proper_properties : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsFinite k ∧ QuasiCompact p' ∧ QuasiSeparated p' ∧ Function.Surjective k'.base ∧ IsClosedMap (p' ≫ k).base ∧ IsClosedMap p.base ∧ (∀ V : Y.Opens, IsAffineOpen V → IsCompact (p ⁻¹ᵁ V : Set Z) ∧ IsQuasiSeparated (p ⁻¹ᵁ V : Set Z)) ∧ ∃ (d : ℕ) (b : Fin d → R'), ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, ρ (c l) * b l := by
  first | exact @GlobalTheory.finiteFlat_proper_baseChange_facts | exact GlobalTheory.finiteFlat_proper_baseChange_facts | (intros; apply GlobalTheory.finiteFlat_proper_baseChange_facts <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mem_range_appTop_of_fibreSquare_projections_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → IsIntegral S → Function.Injective π.appTop.hom → ∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom := by
  first | exact @GlobalTheory.Mum.mem_range_appTop_of_fst_eq_snd | exact GlobalTheory.Mum.mem_range_appTop_of_fst_eq_snd | (intros; apply GlobalTheory.Mum.mem_range_appTop_of_fst_eq_snd <;> assumption)

end
end
