module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle372
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SqZeroPb

def liftHom {K : Type} [Field K] {V W₁ W₂ : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁]
    [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂]
    (e : V ≃ₗ[K] W₁ × W₂) {T : Type} [CommRing T]
    (a : T →+* TrivSqZeroExt K W₁) (b : T →+* TrivSqZeroExt K W₂)
    (h : ∀ t, (a t).fst = (b t).fst) : T →+* TrivSqZeroExt K V where
  toFun t := TrivSqZeroExt.inl (a t).fst + TrivSqZeroExt.inr (e.symm ((a t).snd, (b t).snd))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, zero_add, smul_eq_mul, op_smul_eq_smul, smul_zero]
      rw [← map_smul, ← map_smul, ← map_add (f := _)]
      congr 1
      ext <;> simp [h]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_add (f := _), TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add]
      rw [show ((a x).snd + (a y).snd, (b x).snd + (b y).snd)
          = ((a x).snd, (b x).snd) + ((a y).snd, (b y).snd) from rfl, map_add]

end GlobalTheory.SqZeroPb

open GlobalTheory.SqZeroPb in
theorem GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt : ∀ (K : Type) [Field K] (V W₁ W₂ : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁] [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂] (p : V →ₗ[K] W₁) (q : V →ₗ[K] W₂), Function.Bijective (LinearMap.prod p q) → IsPullback (CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom) := by
  intro K _ V W₁ W₂ _ _ _ _ _ _ _ _ _ _ _ _ p q hpq
  let e := LinearEquiv.ofBijective (LinearMap.prod p q) hpq
  have he : ∀ v, e v = (p v, q v) := fun v => rfl
  have hw : CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom =
      CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom := by
    ext x; simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => CommRingCat.ofHom (liftHom e s.fst.hom s.snd.hom ?_)) ?_ ?_ ?_)
  · intro t
    have := congrArg (fun φ => φ.hom t) s.condition
    simpa using this
  · intro s
    ext t : 2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom]
    · simp [liftHom]
      exact congrArg Prod.fst (e.apply_symm_apply _)
  · intro s
    ext t : 2
    have hc := congrArg (fun φ => φ.hom t) s.condition
    simp at hc
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, hc]
    · simp [liftHom]
      exact congrArg Prod.snd (e.apply_symm_apply _)
  · intro s m hm1 hm2
    ext t : 2
    have h1 := congrArg (fun φ => φ.hom t) hm1
    have h2 := congrArg (fun φ => φ.hom t) hm2
    simp at h1 h2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, ← h1]
    · simp [liftHom, ← h1, ← h2]
      rw [LinearEquiv.eq_symm_apply]
      rfl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.FerrandGlue

theorem kernel_nilpotent : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₂ → Nontrivial R₀ → IsNilpotent (RingHom.ker g₁.hom) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₂ hR₀
  have hT := (Types.isPullback_iff _ _ _ _).1 (hP.map (forget CommRingCat))
  have hf₁ : Function.Surjective f₁ := by
    intro r
    obtain ⟨s, hs⟩ := hg₂ (g₁ r)
    obtain ⟨p, hp, -⟩ := hT.2.2 r s hs.symm
    exact ⟨p, hp⟩
  let J : Ideal P := (RingHom.ker g₁.hom).comap f₁.hom
  have hJ : J ≤ IsLocalRing.maximalIdeal P := IsLocalRing.le_maximalIdeal (by
    intro h
    have h1 : (1 : P) ∈ J := h ▸ Submodule.mem_top
    simp [J] at h1)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := P)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, ?_⟩
  have hmap : RingHom.ker g₁.hom = J.map f₁.hom := (Ideal.map_comap_of_surjective _ hf₁ _).symm
  rw [hmap, ← Ideal.map_pow, Ideal.zero_eq_bot, eq_bot_iff]
  calc (J ^ n).map f₁.hom ≤ ((IsLocalRing.maximalIdeal P) ^ n).map f₁.hom := Ideal.map_mono (Ideal.pow_right_mono hJ n)
    _ = ⊥ := by rw [hn, Ideal.zero_eq_bot, Ideal.map_bot]

theorem thickening_of_isPullback : ∀ (R₁ R₀ : CommRingCat.{0}) (g : R₁ ⟶ R₀) (Y₁ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₀ : Y₀ ⟶ Spec R₀) (i : Y₀ ⟶ Y₁), IsPullback i p₀ p₁ (Spec.map g) → Function.Surjective g → IsNilpotent (RingHom.ker g.hom) → IsClosedImmersion i ∧ Surjective i := by
  intro R₁ R₀ g Y₁ Y₀ p₁ p₀ i h hg hn
  have hc : IsClosedImmersion (Spec.map g) := IsClosedImmersion.spec_of_surjective g hg
  have hs : Surjective (Spec.map g) := by
    constructor
    intro x
    obtain ⟨n, hn⟩ := hn
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g.hom : Set R₁) := fun a ha => by
      refine x.isPrime.mem_of_pow_mem n ?_
      have := Ideal.pow_mem_pow ha n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      rw [this]
      exact zero_mem _
    rw [← range_comap_of_surjective _ g.hom hg] at hx
    exact hx
  exact ⟨MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hc,
    MorphismProperty.of_isPullback (P := @Surjective) h.flip hs⟩

theorem ferrand_glue_artinian : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → IsPullback i₂ Y₀.hom Y₂.hom (Spec.map g₂) → Flat Y₁.hom → Flat Y₂.hom → ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧ Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂ Y₁ Y₂ Y₀ i₁ i₂ h₁ h₂ hf₁ hf₂
  by_cases hR₀ : Subsingleton R₀
  · exact GlobalTheory.T.glue_flat_over_pullback_of_subsingleton P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hR₀ hloc hart hg₁ hg₂ Y₁ Y₂ Y₀ i₁ i₂ h₁ h₂ hf₁ hf₂
  rw [not_subsingleton_iff_nontrivial] at hR₀
  have hn₁ := kernel_nilpotent P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₂ hR₀
  have hn₂ := kernel_nilpotent P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip hloc hart hg₁ hR₀
  obtain ⟨hc₁, hs₁⟩ := thickening_of_isPullback R₁ R₀ g₁ Y₁.left Y₀.left Y₁.hom Y₀.hom i₁ h₁ hg₁ hn₁
  obtain ⟨hc₂, hs₂⟩ := thickening_of_isPullback R₂ R₀ g₂ Y₂.left Y₀.left Y₂.hom Y₀.hom i₂ h₂ hg₂ hn₂
  obtain ⟨Y, j₁, j₂, hw, hpo, hj₁, hj₂, hV⟩ := GlobalTheory.T.exists_pushout_of_nilpotent_thickenings' Y₀.left Y₁.left Y₂.left i₁ i₂ hc₁ hc₂ hs₁ hs₂
    (GlobalTheory.T.isNilpotent_ker_app_of_isPullback_of_nilpotent R₁ R₀ g₁ Y₁.left Y₀.left Y₁.hom Y₀.hom i₁ h₁ hg₁ hn₁)
    (GlobalTheory.T.isNilpotent_ker_app_of_isPullback_of_nilpotent R₂ R₀ g₂ Y₂.left Y₀.left Y₂.hom Y₀.hom i₂ h₂ hg₂ hn₂)
  have hcomm : i₁ ≫ Y₁.hom ≫ Spec.map f₁ = i₂ ≫ Y₂.hom ≫ Spec.map f₂ := by
    rw [← Category.assoc, h₁.w, ← Category.assoc, h₂.w, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hP.w]
  let y : Y ⟶ Spec P := hpo.desc (Y₁.hom ≫ Spec.map f₁) (Y₂.hom ≫ Spec.map f₂) hcomm
  obtain ⟨k₁, k₂, kf⟩ := GlobalTheory.T.flat_ferrandPushout_over_fibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁.left Y₂.left Y₀.left Y₁.hom Y₂.hom Y₀.hom i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw hj₁ hj₂ hV y (hpo.inl_desc _ _ _) (hpo.inr_desc _ _ _)
  exact ⟨Over.mk y, j₁, j₂, k₁, k₂, kf, hpo⟩

end GlobalTheory.FerrandGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SmoothDescent

theorem smoothOfRelativeDimension_of_etale_cover_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  intro K _ _ X Y π s d _ _ _ hd
  have : Smooth (π ≫ s) := SmoothOfRelativeDimension.smooth d _
  have : Smooth s := smooth_of_comp_of_etale_of_surjective π s
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  choose n W hW hn using H1.exists_dim s
  have key (y : Y) : n y = d := by
    obtain ⟨x, rfl⟩ := π.surjective y
    have := hn (π x)
    have h₁ : SmoothOfRelativeDimension (0 + n (π x)) ((π ∣_ W (π x)) ≫ (W (π x)).ι ≫ s) := inferInstance
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h₁
    have h₂ : SmoothOfRelativeDimension (0 + d) ((π ⁻¹ᵁ W (π x)).ι ≫ π ≫ s) := inferInstance
    simpa using H1.dim_unique _ h₁ h₂ ⟨x, hW (π x)⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W ?_ fun y => key y ▸ hn y
  rw [← top_le_iff]
  rintro y -
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩

end GlobalTheory.SmoothDescent
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaFin

theorem isFinite_fromNormalization_and_normal : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → IsFinite f.fromNormalization ∧ Geo.Tor.IsNormalScheme f.normalization := by
  intro o F _ _ _ _ _ _ b n X s f _ _ hinj hfrac hX _ _ _ hw _
  letI : Algebra o F := b.toAlgebra
  haveI : IsFractionRing o F := by
    refine ⟨fun d => ?_, fun x => ?_, fun {x y} h => ?_⟩
    · refine IsUnit.mk0 _ ?_
      change b d ≠ 0
      exact (map_ne_zero_iff b hinj).mpr (nonZeroDivisors.ne_zero d.2)
    · obtain ⟨a, d, hd, e⟩ := hfrac x
      refine ⟨⟨a, ⟨d, mem_nonZeroDivisors_of_ne_zero fun h0 => hd (by rw [h0, map_zero])⟩⟩, e⟩
    · exact ⟨1, by simpa using hinj h⟩
  haveI : CharZero o := ⟨fun m k h => by
    have := congrArg b h
    simp only [map_natCast] at this
    exact Nat.cast_injective this⟩
  haveI : IsDedekindDomain (CommRingCat.of o) := ‹IsDedekindDomain o›
  haveI : CharZero (CommRingCat.of o) := ‹CharZero o›
  haveI hN : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hX
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  haveI : IsProper (PSpace.str o n) := isProper_str o n
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  refine ⟨GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := CommRingCat.of o) f
    (PSpace.str o n) F s hw, ?_⟩
  exact GlobalTheory.IsNormalScheme.pred _

end GlobalTheory.ThetaFin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

open scoped TensorProduct

namespace GlobalTheory

open Algebra in
theorem finiteType_of_finiteType_quotient_map_nilpotent {P A : Type} [CommRing P] [CommRing A]
    [Algebra P A] (I : Ideal P) (hI : IsNilpotent I)
    [h : Algebra.FiniteType P (A ⧸ I.map (algebraMap P A))] : Algebra.FiniteType P A := by
  set J := I.map (algebraMap P A)
  obtain ⟨s, hs⟩ := h.out
  classical
  let t : Finset A := s.image (fun x => Quotient.out x)
  have hmk : (Ideal.Quotient.mkₐ P J) '' (t : Set A) = (s : Set (A ⧸ J)) := by
    ext x; simp [t]
  let C := Algebra.adjoin P (t : Set A)
  have key : ∀ b : A, ∃ c ∈ C, b - c ∈ J := by
    intro b
    have hb : Ideal.Quotient.mkₐ P J b ∈ (C.map (Ideal.Quotient.mkₐ P J)) := by
      rw [AlgHom.map_adjoin, hmk, hs]; trivial
    obtain ⟨c, hc, hcb⟩ := hb
    exact ⟨c, hc, Ideal.Quotient.eq.mp (by simpa using hcb.symm)⟩
  have base : (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ I • ⊤ := by
    intro b _
    obtain ⟨c, hc, hbc⟩ := key b
    have : b - c ∈ I • (⊤ : Submodule P A) := by
      rw [Ideal.smul_top_eq_map]; exact hbc
    have := Submodule.add_mem_sup (show c ∈ Subalgebra.toSubmodule C from hc) this
    simpa using this
  have step : ∀ n : ℕ, (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ (I ^ n) • ⊤ := by
    intro n
    induction n with
    | zero =>
      intro b _
      exact Submodule.mem_sup_right (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial)
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      calc (I ^ n) • (⊤ : Submodule P A) ≤ (I ^ n) • (Subalgebra.toSubmodule C ⊔ I • ⊤) :=
            Submodule.smul_mono le_rfl base
        _ = (I ^ n) • Subalgebra.toSubmodule C ⊔ (I ^ n) • (I • ⊤) := Submodule.smul_sup _ _ _
        _ ≤ Subalgebra.toSubmodule C ⊔ (I ^ (n + 1)) • ⊤ := by
            rw [pow_succ, Submodule.mul_smul]
            exact sup_le_sup_right Submodule.smul_le_right _
  obtain ⟨N, hN⟩ := hI
  have hC : Subalgebra.toSubmodule C = ⊤ := by
    have := step N
    rw [hN, Submodule.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
    exact top_le_iff.mp this
  exact ⟨⟨t, Algebra.toSubmodule_eq_top.mp hC⟩⟩

theorem finiteType_of_finiteType_tensor_nilpotent {P A R : Type} [CommRing P] [CommRing A]
    [CommRing R] [Algebra P A] [Algebra P R] (hs : Function.Surjective (algebraMap P R))
    (hn : IsNilpotent (RingHom.ker (algebraMap P R)))
    (h : (Algebra.TensorProduct.includeRight : R →ₐ[P] A ⊗[P] R).toRingHom.FiniteType) :
    Algebra.FiniteType P A := by
  have h1 : Algebra.FiniteType P (A ⊗[P] R) := by
    rw [← RingHom.finiteType_algebraMap,
      ← (Algebra.TensorProduct.includeRight : R →ₐ[P] A ⊗[P] R).comp_algebraMap]
    exact h.comp (RingHom.FiniteType.of_surjective _ hs)
  let f : P →ₐ[P] R := Algebra.ofId P R
  have hf : Function.Surjective f := hs
  let I : Ideal P := RingHom.ker f
  let e1 : (A ⧸ I.map (algebraMap P A)) ≃ₐ[P] A ⊗[P] (P ⧸ I) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).restrictScalars P
  let e2 : A ⊗[P] (P ⧸ I) ≃ₐ[P] A ⊗[P] R :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Ideal.quotientKerAlgEquivOfSurjective hf)
  have h2 : Algebra.FiniteType P (A ⧸ I.map (algebraMap P A)) := h1.equiv (e1.trans e2).symm
  exact finiteType_of_finiteType_quotient_map_nilpotent I hn

theorem locallyOfFinitePresentation_specMap_of_isPullback_nilpotent {P R₁ A : CommRingCat.{0}}
    (f₁ : P ⟶ R₁) (hs : Function.Surjective f₁) (hn : IsNilpotent (RingHom.ker f₁.hom))
    [IsNoetherianRing P] (φ : P ⟶ A) {W : Scheme.{0}} (fst : W ⟶ Spec A) (snd : W ⟶ Spec R₁)
    (hsq : IsPullback fst snd (Spec.map φ) (Spec.map f₁)) (hsnd : LocallyOfFinitePresentation snd) :
    LocallyOfFinitePresentation (Spec.map φ) := by
  have h1 : LocallyOfFinitePresentation (pullback.snd (Spec.map φ) (Spec.map f₁)) := by
    have e : pullback.snd (Spec.map φ) (Spec.map f₁) = hsq.isoPullback.inv ≫ snd := by
      rw [Iso.eq_inv_comp, hsq.isoPullback_hom_snd]
    rw [e]
    exact MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hsnd
  letI := φ.hom.toAlgebra
  letI := f₁.hom.toAlgebra
  have hT : LocallyOfFinitePresentation ((pullbackSpecIso P A R₁).inv ≫ pullback.snd _ _) :=
    MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) h1
  rw [pullbackSpecIso_inv_snd, LocallyOfFinitePresentation.SpecMap_iff] at hT
  rw [LocallyOfFinitePresentation.SpecMap_iff, ← RingHom.FinitePresentation.of_finiteType]
  exact finiteType_of_finiteType_tensor_nilpotent (A := A) hs hn (RingHom.FiniteType.of_finitePresentation hT)

theorem locallyOfFinitePresentation_of_nilpotent_thickening :
    ∀ (P R₁ : CommRingCat.{0}) (f₁ : P ⟶ R₁), Function.Surjective f₁ → IsNilpotent (RingHom.ker f₁.hom) → IsNoetherianRing P → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (j₁ : Y₁.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → LocallyOfFinitePresentation Y₁.hom → LocallyOfFinitePresentation Y.hom := by
  intro P R₁ f₁ hs hn hP Y Y₁ j₁ hpb hY₁
  haveI : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation.{0})
    Y.left.affineOpenCover.openCover]
  intro i
  haveI : IsOpenImmersion (Y.left.affineOpenCover.f i) :=
    inferInstanceAs (IsOpenImmersion (Y.left.affineOpenCover.openCover.f i))
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.left.affineOpenCover.f i ≫ Y.hom)
  have hsq : IsPullback (pullback.fst (Y.left.affineOpenCover.f i) j₁)
      (pullback.snd (Y.left.affineOpenCover.f i) j₁ ≫ Y₁.hom) (Spec.map φ) (Spec.map f₁) := by
    rw [hφ]; exact (IsPullback.of_hasPullback (Y.left.affineOpenCover.f i) j₁).paste_vert hpb
  have hfin := GlobalTheory.locallyOfFinitePresentation_specMap_of_isPullback_nilpotent f₁ hs hn φ _ _ hsq
    (MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hY₁)
  rw [hφ] at hfin
  exact hfin

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TranslQuotientPow

theorem isMonHom_id_pow {Y : Scheme.{0}} (G : Over Y) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom ((𝟙 G) ^ n : G ⟶ G) := by
  induction n with
  | zero => rw [pow_zero]; infer_instance
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 G) ^ n) (𝟙 G) ≫ μ[G]))

theorem comp_id_pow {Y : Scheme.{0}} {G W : Over Y} [GrpObj G] (x : W ⟶ G) (n : ℕ) :
    x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, comp_one]
  | succ n ih => rw [pow_succ, pow_succ, comp_mul, ih, Category.comp_id]

theorem pow_comp_hom {Y : Scheme.{0}} {G A W : Over Y} [GrpObj G] [GrpObj A] (q : G ⟶ A) [IsMonHom q]
    (x : W ⟶ G) (n : ℕ) : (x ^ n) ≫ q = (x ≫ q) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_comp]
  | succ n ih => rw [pow_succ, pow_succ, mul_comp, ih]

end GlobalTheory.TranslQuotientPow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.SiegFactor

theorem comp_id_pow {S : Scheme.{0}} {T A : Over S} [GrpObj A] (x : T ⟶ A) (k : ℕ) :
    x ≫ (𝟙 A) ^ k = x ^ k := by
  rw [MonObj.comp_pow, Category.comp_id]

theorem id_pow_comp {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (χ : A ⟶ B) [IsMonHom χ]
    (k : ℕ) : ((𝟙 A) ^ k) ≫ χ = χ ≫ (𝟙 B) ^ k := by
  rw [MonObj.pow_comp, Category.id_comp, comp_id_pow]

theorem isMonHom_epi_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {k : ℕ}
    (hk : 0 < k) : IsMonHom ((𝟙 A) ^ k) ∧ Epi ((𝟙 A) ^ k) := by
  have := hA.comm
  have hm : IsMonHom ((𝟙 A) ^ k) := GlobalTheory.AbLaw.MulN.isMonHom_mulA A k
  obtain ⟨hfl, hsu, hqc⟩ := SiegUniqBase.flat_surjective_qc_pow S A hA k hk
  exact ⟨hm, (GlobalTheory.exists_monHom_factor_of_flat_surjective S A A A _ _ hm hm hfl hsu hqc
    fun _ _ h => h).2⟩

end GlobalTheory.UPel.HT.SiegFactor

namespace GlobalTheory.UPel.HT

end GlobalTheory.UPel.HT
end
