module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmall
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.squareZeroLiftSystem_filtration_inf_eq_and_full : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ S S' : Sys I π s₀, S.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) ∧ (S.Full hI → S'.Full hI) := by
  first | exact @GlobalTheory.LiftSys.K_inf_eq_and_full | exact GlobalTheory.LiftSys.K_inf_eq_and_full | (intros; apply GlobalTheory.LiftSys.K_inf_eq_and_full <;> assumption)
end

section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory.RatHomology

theorem finrank_rat_tensor (M : Type) [AddCommGroup M] [Module ℤ M] :
    Module.finrank ℚ (ℚ ⊗[ℤ] M) = Module.finrank ℤ M := by
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) le_rfl,
    ← IsFractionRing.finrank_right_eq ℤ ℚ]

theorem finrank_rat_homology (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (_ : Module.Finite ℤ (C.homology n)) :
    Module.finrank ℚ ((((ModuleCat.extendScalars (Int.castRingHom ℚ)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj C).homology n) = Module.finrank ℤ (C.homology n) := by
  obtain ⟨e⟩ := GlobalTheory.FieldChangeInter.nonempty_homology_equiv ℚ C n
  have h := e.finrank_eq
  have hφ : algebraMap ℤ ℚ = Int.castRingHom ℚ := rfl
  rw [hφ] at h
  rw [h]
  exact finrank_rat_tensor (C.homology n)

end GlobalTheory.RatHomology
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PinchLift

theorem exists_gen_away_of_closed : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X'), L'.IsLB → ∀ x : X, (∀ z : Z, i z ≠ x) → ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ), x ∈ W ∧ i ⁻¹ᵁ W = ⊥ ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' := by
  intro X X' Z Z' p i i' p' _ hp hi hG L' hL x hx
  let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hxU : x ∈ U := by rintro ⟨z, rfl⟩; exact hx z rfl
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  have hiV : ∀ {O : X.Opens}, O ≤ V → i ⁻¹ᵁ O = ⊥ := fun {O} hO =>
    eq_bot_iff.2 fun z hz => (hVU (hO hz) ⟨z, rfl⟩).elim
  have hbot : i ⁻¹ᵁ V = ⊥ := hiV le_rfl
  have hsZ : Subsingleton Γ(Z, i ⁻¹ᵁ V) := by rw [hbot]; infer_instance
  have hbot' : i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V) = ⊥ :=
    eq_bot_iff.2 fun z hz => (hVU (show i (p' z) ∈ V from hz.2) ⟨p' z, rfl⟩).elim
  have hsZ' : Subsingleton Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) := by rw [hbot']; infer_instance
  have hbij : Function.Bijective (p.app V).hom := by
    constructor
    · intro s t hst
      have h1 := hG V ((p.app V).hom s) ((i.app V).hom s) (Subsingleton.elim _ _)
      exact h1.unique ⟨rfl, rfl⟩ ⟨hst.symm, Subsingleton.elim _ _⟩
    · intro a
      obtain ⟨s, hs, -⟩ := hG V a 0 (Subsingleton.elim _ _)
      exact ⟨s, hs.1⟩
  haveI : IsIso (p.app V) := (ConcreteCategory.isIso_iff_bijective (p.app V)).2 hbij
  haveI : IsIso (p ∣_ V) := (isIso_morphismRestrict_iff_isIso_app p hV).2 inferInstance
  have hg : ∀ y, (p ∣_ V ≫ V.ι) y = p ((p ⁻¹ᵁ V).ι y) := fun y => by rw [morphismRestrict_ι]; rfl
  obtain ⟨y, hy⟩ : ∃ y, (p ∣_ V ≫ V.ι) y = x := by
    obtain ⟨v, hv⟩ := (p ∣_ V).surjective ⟨x, hxV⟩
    exact ⟨v, by show V.ι ((p ∣_ V) v) = x; rw [hv]; rfl⟩
  obtain ⟨k₀, hk₀⟩ := exists_chart hL ((p ⁻¹ᵁ V).ι y)
  let W : X.Opens := (p ∣_ V ≫ V.ι) ''ᵁ ((p ⁻¹ᵁ V).ι ⁻¹ᵁ L'.U k₀)
  have hmemW : ∀ z, z ∈ W ↔ ∃ w, (p ⁻¹ᵁ V).ι w ∈ L'.U k₀ ∧ (p ∣_ V ≫ V.ι) w = z := fun z => Iff.rfl
  have hxW : x ∈ W := (hmemW x).2 ⟨y, hk₀, hy⟩
  have hWV : W ≤ V := by
    intro z hz
    obtain ⟨w, -, rfl⟩ := (hmemW z).1 hz
    rw [hg]; exact w.2
  have hWk : p ⁻¹ᵁ W ≤ L'.U k₀ := by
    intro x'' hx''
    obtain ⟨w, hw, hwe⟩ := (hmemW _).1 hx''
    have hv : x'' ∈ p ⁻¹ᵁ V := hWV hx''
    have : (⟨x'', hv⟩ : (p ⁻¹ᵁ V).toScheme) = w :=
      (p ∣_ V ≫ V.ι).isOpenEmbedding.injective (by rw [hwe]; exact hg _)
    rw [← this] at hw; exact hw
  refine ⟨W, fun k => res (le_inf inf_le_left (inf_le_right.trans hWk)) (L'.g k k₀), hxW, hiV hWV, ?_⟩
  intro k l z hk hl hz
  have hz0 : z ∈ L'.U k₀ := hWk hz
  rw [gm_res (𝟙 X') z _ (show z ∈ L'.U k ⊓ p ⁻¹ᵁ W from ⟨hk, hz⟩),
    gm_res (𝟙 X') z _ (show z ∈ L'.U l ⊓ p ⁻¹ᵁ W from ⟨hl, hz⟩)]
  exact (gm_cocycle hL (𝟙 X') z hk hl hz0).symm

end GlobalTheory.PinchLift
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PinchLift.FlatBC

theorem isPushout_appLE_of_isPullback {X Y S T : Scheme.{0}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S}
    {iY : Y ⟶ T} (H : IsPullback g iY iX f) {US : S.Opens} {UT : T.Opens} {UX : X.Opens} {UY : Y.Opens}
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsAffineOpen UX)
    (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US) (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
    (h₁ : UY ≤ g ⁻¹ᵁ UX) (h₂ : UY ≤ iY ⁻¹ᵁ UT) :
    IsPushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) (g.appLE UX UY h₁) (iY.appLE UT UY h₂) :=
  (isIso_pushoutSection_iff H hUST hUSX hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hUS hUT hUX)

theorem appLE_congr_of_eq {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) (U : B.Opens) (V : A.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst h; rfl

end GlobalTheory.PinchLift.FlatBC

namespace GlobalTheory.PinchLift.FlatBC

theorem glues_affine_of_flat_baseChange : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → ∀ (V : X.left.Opens) (W : (E ⊗ X).left.Opens), IsAffineOpen V → IsAffineOpen W → W ≤ (snd E X).left ⁻¹ᵁ V → ∀ (a : Γ((E ⊗ X').left, (E ◁ p).left ⁻¹ᵁ W)) (b : Γ((E ⊗ Z).left, (E ◁ i).left ⁻¹ᵁ W)), ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_left).hom a = ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ((E ⊗ X).left, W), ((E ◁ p).left.app W).hom s = a ∧ ((E ◁ i).left.app W).hom s = b := by
  intro S E X X' Z Z' p i i' p' hE hc hpb hp hi hglue V W hV hW hWV a b hab
  have hcl : i'.left ≫ p.left = p'.left ≫ i.left := by
    rw [← Over.comp_left, ← Over.comp_left, hc]
  have hcE : (E ◁ i').left ≫ (E ◁ p).left = (E ◁ p').left ≫ (E ◁ i).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, hc]
  have nat : ∀ {Y Y' : Over S} (j : Y' ⟶ Y),
      (E ◁ j).left ≫ (snd E Y).left = (snd E Y').left ≫ j.left := by
    intro Y Y' j
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  haveI : IsAffineHom i.left := inferInstance
  haveI : IsClosedImmersion i'.left := MorphismProperty.of_isPullback hpb.flip ‹_›
  haveI : IsAffineHom p'.left := MorphismProperty.of_isPullback hpb ‹_›
  haveI : Flat (snd E X).left := by
    change Flat (pullback.snd E.hom X.hom); infer_instance
  have eV : p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V) = i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hcl]
  have eW : (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) = (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hcE]
  have hDV : i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V) = (i'.left ≫ p.left) ⁻¹ᵁ V := by
    rw [eV, inf_idem]; rfl
  have hDW : (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) =
      ((E ◁ i').left ≫ (E ◁ p).left) ⁻¹ᵁ W := by
    rw [eW, inf_idem]; rfl
  have hDVa : IsAffineOpen (i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V)) := by
    rw [hDV]; exact hV.preimage _
  have H1 := isPullback_whiskerLeft_snd_left E p
  have H2 := isPullback_whiskerLeft_snd_left E i
  have H3 : IsPullback ((E ◁ i').left ≫ (E ◁ p).left) (snd E Z').left (snd E X).left
      (i'.left ≫ p.left) := by
    have := isPullback_whiskerLeft_snd_left E (i' ≫ p)
    rwa [MonoidalCategory.whiskerLeft_comp, Over.comp_left, Over.comp_left] at this
  have hU1 : (E ◁ p).left ⁻¹ᵁ W = (E ◁ p).left ⁻¹ᵁ W ⊓ (snd E X').left ⁻¹ᵁ (p.left ⁻¹ᵁ V) := by
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← nat p, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ hWV
  have hU2 : (E ◁ i).left ⁻¹ᵁ W = (E ◁ i).left ⁻¹ᵁ W ⊓ (snd E Z).left ⁻¹ᵁ (i.left ⁻¹ᵁ V) := by
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← nat i, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ hWV
  have nat3 : ((E ◁ i').left ≫ (E ◁ p).left) ≫ (snd E X).left =
      (snd E Z').left ≫ (i'.left ≫ p.left) := by
    rw [Category.assoc, nat p, ← Category.assoc, nat i', Category.assoc]
  have hU3 : (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) =
      ((E ◁ i').left ≫ (E ◁ p).left) ⁻¹ᵁ W ⊓
        (snd E Z').left ⁻¹ᵁ (i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V)) := by
    rw [hDW, hDV]
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage (snd E Z').left (i'.left ≫ p.left) V, ← nat3,
      Scheme.Hom.comp_preimage _ (snd E X).left V]
    exact Scheme.Hom.preimage_mono _ hWV
  have P1 := isPushout_appLE_of_isPullback H1 hV (hV.preimage p.left) hW le_rfl hWV hU1 le_rfl
    (hU1.le.trans inf_le_right)
  have P2 := isPushout_appLE_of_isPullback H2 hV (hV.preimage i.left) hW le_rfl hWV hU2 le_rfl
    (hU2.le.trans inf_le_right)
  have P3 := isPushout_appLE_of_isPullback H3 hV hDVa hW hDV.le hWV hU3 (hU3.le.trans inf_le_left)
    (hU3.le.trans inf_le_right)
  have key := GlobalTheory.T.existsUnique_preimage_pair_of_pushout_of_compat (p.left.appLE V (p.left ⁻¹ᵁ V) le_rfl) (i.left.appLE V (i.left ⁻¹ᵁ V) le_rfl)
    (i'.left.appLE (p.left ⁻¹ᵁ V) _ inf_le_left) (p'.left.appLE (i.left ⁻¹ᵁ V) _ inf_le_right)
    ((snd E X).left.appLE V W hWV)
    ((snd E X').left.appLE (p.left ⁻¹ᵁ V) ((E ◁ p).left ⁻¹ᵁ W) (hU1.le.trans inf_le_right))
    ((snd E Z).left.appLE (i.left ⁻¹ᵁ V) ((E ◁ i).left ⁻¹ᵁ W) (hU2.le.trans inf_le_right))
    ((snd E Z').left.appLE _ _ (hU3.le.trans inf_le_right))
    ((E ◁ p).left.appLE W _ le_rfl) ((E ◁ i).left.appLE W _ le_rfl)
    ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) _ inf_le_left)
    ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) _ inf_le_right)
    ((snd E X).left.flat_appLE hV hW hWV) P1 P2
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]; exact P3)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq (nat i') _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq (nat p') _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq hcE _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq hcl _ _ _ _)
    (fun b c h => by
      have := hglue V b c h
      rwa [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE] at this) a b hab
  rwa [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]

end GlobalTheory.PinchLift.FlatBC
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unit_of_pinchingSquare_glued_units : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (a : Γ(X', p ⁻¹ᵁ V)ˣ) (b : Γ(Z, i ⁻¹ᵁ V)ˣ), (∀ z : Z', p (i' z) ∈ V → gm i' z (p ⁻¹ᵁ V) a = gm p' z (i ⁻¹ᵁ V) b) → ∃ u : Γ(X, V)ˣ, (∀ x' : X', p x' ∈ V → gm p x' V u = gm (𝟙 X') x' (p ⁻¹ᵁ V) a) ∧ (∀ z : Z, i z ∈ V → gm i z V u = gm (𝟙 Z) z (i ⁻¹ᵁ V) b) := by
  first | exact @GlobalTheory.PinchLift.exists_unit_of_glues | exact GlobalTheory.PinchLift.exists_unit_of_glues | (intros; apply GlobalTheory.PinchLift.exists_unit_of_glues <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unit_eq_of_germs_pinching_square : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (u v : Γ(X, V)ˣ), (∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) → (∀ z : Z, i z ∈ V → gm i z V u = gm i z V v) → u = v := by
  first | exact @GlobalTheory.PinchLift.unit_eq_of_germs_glues | exact GlobalTheory.PinchLift.unit_eq_of_germs_glues | (intros; apply GlobalTheory.PinchLift.unit_eq_of_germs_glues <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV

theorem _root_.GlobalTheory.T.columnNormParameters_eq_natStepGap : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) → GlobalTheory.ColumnNormCompare.numDatumOfParameters D L = ofRecord D L Del h0 := by
  first | exact @GlobalTheory.ColumnNormCompare.numRec_eq_ofRecord | exact GlobalTheory.ColumnNormCompare.numRec_eq_ofRecord | (intros; apply GlobalTheory.ColumnNormCompare.numRec_eq_ofRecord <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ColNorms.LastDatum

open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions
  _root_.Formalism.L2.DIV _root_.Formalism.L2.Col _root_.Formalism.L2.Ker
  GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
open GlobalTheory.TopStep

section

variable {X : Fields}

theorem norm_psi {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {cst : LocCst X SB} (hc : cst.Ok) (P : SB) {a : X.E}
    (ha : IntAt P.1 ((_root_.Formalism.L2.Col.qOf P.1 : X.E) * a)) (σ : X.K →+* ℂ) : ‖σ (cst.psi P a)‖ = 1 := by
  have hD : ∀ k : ℕ, IntAt P.1 ((_root_.Formalism.L2.Col.qOf P.1 : X.E) ^ cst.D P * ((k : X.E) * a)) := fun k => by
    obtain ⟨D, hD⟩ : ∃ D, cst.D P = D + 1 := ⟨cst.D P - 1, by have := hc.D_pos P; omega⟩
    have := ((intAt_pow (intAt_nat (P := P.1) (_root_.Formalism.L2.Col.qOf P.1)) D).mul (intAt_nat k)).mul ha
    convert this using 1
    rw [hD]
    ring
  have hk : ∀ k : ℕ, cst.psi P ((k : X.E) * a) = cst.psi P a ^ k := fun k => by
    induction k with
    | zero => simpa using hc.psi_int P 0 (by simpa using intAt_nat (P := P.1) 0)
    | succ k ih =>
      have h1 := hc.psi_add P _ _ (hD k) (hD 1)
      rw [Nat.cast_one, one_mul] at h1
      rw [Nat.cast_succ, add_mul, one_mul, h1, ih, pow_succ]
  have h1 := hk (_root_.Formalism.L2.Col.qOf P.1)
  rw [hc.psi_int P _ ha] at h1
  have hq : _root_.Formalism.L2.Col.qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have h2 : ‖σ (cst.psi P a)‖ ^ _root_.Formalism.L2.Col.qOf P.1 = 1 := by rw [← norm_pow, ← map_pow, ← h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq).1 h2

variable {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem locSmall_locTop (hm : R.m = m2 + 2) (hc : cst.Ok) (hs : cst.sharp = true) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs)
    {y' : Sp X.E (R.N (m2 + 1))} (hy' : ∀ i, IntAt P.1 ((_root_.Formalism.L2.Col.qOf P.1 : X.E) * y' i)) :
    LocSmall (_root_.Formalism.L2.Col.qOf P.1) (stdAt X.E (R.N (m2 + 1)) P.1) (stdAt X.E (R.N R.m) P.1)
      (fun y => locTop Ch sel mu cst m2 P y y') 1 := by
  have hq := qOf_ne_zero (P := P.1)
  have hsingle : ∀ s : Fin (R.N (m2 + 1)), (Pi.single s 1 : Sp X.E (R.N (m2 + 1))) ∈ stdAt X.E (R.N (m2 + 1)) P.1 := fun s =>
    mem_stdAt.2 fun i => by
      rw [Pi.single_apply]
      split_ifs
      · simpa using intAt_nat (P := P.1) 1
      · simpa using intAt_nat (P := P.1) 0
  refine ⟨fun x hx y hy => mem_stdAt.2 fun l => ?_, fun x z hz => ?_, fun σ x => ?_⟩
  · rw [apply_eq_sum]
    exact intAt_sum _ fun j _ => (mem_stdAt.1 hy j).mul (mem_stdAt.1 (locTop_supp hm hP hx j) l)
  · have hz' : ∀ s l, IntAt P.1 (z (Pi.single s 1) l) := fun s l => mem_stdAt.1 (hz _ (hsingle s)) l
    have e : ∀ s l, (x + (_root_.Formalism.L2.Col.qOf P.1 : X.E) • z) (Pi.single s 1) l =
        x (Pi.single s 1) l + (_root_.Formalism.L2.Col.qOf P.1 : X.E) * z (Pi.single s 1) l := fun s l => rfl
    have hi : ∀ s l, IntAt P.1 ((x + (_root_.Formalism.L2.Col.qOf P.1 : X.E) • z) (Pi.single s 1) l) ↔ IntAt P.1 (x (Pi.single s 1) l) :=
      fun s l => by rw [e, GlobalTheory.SymLevelDatum.intAt_add_iff P.1 ((intAt_nat _).mul (hz' s l))]
    by_cases hx : ∀ s l, IntAt P.1 (x (Pi.single s 1) l)
    · refine locTop_congr hm hc hP hy' fun s l => ⟨(hi s l).2 (hx s l), hx s l, ?_⟩
      rw [e, add_sub_cancel_left, mul_div_cancel_left₀ _ hq]
      exact hz' s l
    · have h1 : locTop Ch sel mu cst m2 P x y' = 0 := by
        by_contra h
        exact hx fun s l => mem_stdAt.1 (locTop_supp hm hP h s) l
      have h2 : locTop Ch sel mu cst m2 P (x + (_root_.Formalism.L2.Col.qOf P.1 : X.E) • z) y' = 0 := by
        by_contra h
        exact hx fun s l => (hi s l).1 (mem_stdAt.1 (locTop_supp hm hP h s) l)
      exact h2.trans h1.symm
  · show ‖σ (locTop Ch sel mu cst m2 P x y')‖ ≤ 1
    unfold locTop
    rw [map_mul, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · unfold PhiTop
      rw [if_pos hP, hs, if_pos rfl]
      have hq0 : _root_.Formalism.L2.Col.qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
      have hN : ∀ j, R.N j = R.k + j * R.t + j := fun j => by unfold Ranks.N; ring
      have h0 : _root_.Formalism.L2.Col.cOf R (m2 + 1) = 0 := by unfold _root_.Formalism.L2.Col.cOf; omega
      refine (GlobalTheory.SymLevelDatum.locSmall_phiGS X.E X.K P.1 _ _ _ _ _ _ _ R.m _ _ 0 _ hq0 (Ideal.absNorm_mem _)
        ?_ ?_ ?_ ?_ ?_).2.2 σ _
      · simp only [h0, rank_add_mul_eq_penultimate_rank hm, add_zero]
      · rw [h0, hN, hN, hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1) 1]; omega
      · rw [hN]; omega
      · rw [hN]; omega
      · unfold Ranks.r; omega
    · unfold ftY
      rw [if_pos hP]
      split_ifs with h
      · refine (norm_psi hc P ?_ σ).le
        have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
        have h' : ∀ j, IntAt P.1 (x (Pi.single j 1) (Br.iL (N_m_succ R))) := fun j => by
          have := h j
          rwa [LinearMap.comp_apply, atNL_last] at this
        have := he.mul (intAt_sum Finset.univ fun j _ => (hy' j).mul (h' j))
        convert this using 1
        rw [LinearMap.comp_apply, atNL_last, apply_eq_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · simp

end

end GlobalTheory.ColNorms.LastDatum
end
end

section

open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions
  _root_.Formalism.L2.DIV _root_.Formalism.L2.Col _root_.Formalism.L2.Ker
  GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.presentation_closed_under_bounded_combination : ∀ (D : D7) (T : TaylorLogMetric.Tor D) (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (F₀ : TaylorLogMetric.VC D a b → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → TaylorLogMetric.VC D a b → ℂ) (n β : ℝ), 0 ≤ β → (∀ x ∈ R, Pres D T L L' F₀ (F x) n) → (∀ x ∈ R, c x ∈ TaylorLogMetric.Qbar ∧ ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (c x)‖ ≤ β) → Pres D T L L' F₀ (fun z => ∑ x ∈ R, c x * F x z) (R.card * β * n) := by
  first | exact @GlobalTheory.PresSum.pres_sum | exact GlobalTheory.PresSum.pres_sum | (intros; apply GlobalTheory.PresSum.pres_sum <;> assumption)
end

section

open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions
  _root_.Formalism.L2.DIV _root_.Formalism.L2.Col _root_.Formalism.L2.Ker
  GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.symmetricLevel_typePrime_datum_locally_small : ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k rS r t j c' n' c n : ℕ), q ≠ 0 → (q : 𝓞 E) ∈ P.asIdeal → n' + c' = r + (j - 1) * t → n' + c' ≤ n + c → k ≤ n' → k ≤ n → k ≤ r → LocSmall q (LocE.lamY P q n' c' fun i => i + 1) (LocE.lamY P q n c fun i => i + 1) (LocE.PhiGS q ψ χ k rS r t j c' n' c n) 1 := by
  first | exact @GlobalTheory.SymLevelDatum.locSmall_phiGS | exact GlobalTheory.SymLevelDatum.locSmall_phiGS | (intros; apply GlobalTheory.SymLevelDatum.locSmall_phiGS <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ColNorms.SumBound

open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions
  _root_.Formalism.L2.DIV _root_.Formalism.L2.Col _root_.Formalism.L2.Ker
  GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem mat_opOf_apply {F F' : GFam K} (M : GFam.Mat F F') (hF : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) (b' : F'.β)
    (d' : F'.D b') :
    ((M.opOf hF s φ b' : (F'.mem b').EqFun) : F'.D b' → F'.V) d' =
      ∑ b, (M b b').appOf (hF b) (s b) (φ b : (F.mem b).D → F.V) d' := by
  simp only [GFam.Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem step_le (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (i : ℕ) (v : InfinitePlace K) (t h h' : ℝ)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hh' : 0 ≤ h') (hp : ∀ b, PosAt ((Q.F i).mem b) v) (hp' : ∀ b, PosAt ((Q.F (i + 1)).mem b) v)
    (hc : ∀ b, (Nat.card ((Q.F i).mem b).Cl : ℝ) ≤ h) (hc' : ∀ b, (Nat.card ((Q.F (i + 1)).mem b).Cl : ℝ) ≤ h')
    (hk : ∀ b b' d d', OpLe ((Q.F i).mem b) ((Q.F (i + 1)).mem b') v ((Q.kk i b b').k d d') t) (φ : (Q.F i).Forms) :
    (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re ≤
      (Fintype.card (Q.F i).β : ℝ) * (Fintype.card (Q.F (i + 1)).β : ℝ) * h * h' * t *
        (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
  have hN : (famIpAt (Q.F i) (Q.hF i) v φ φ).re =
      ∑ b, (((Q.F i).mem b).ipAt (Q.hF i b) v (φ b : ((Q.F i).mem b).D → (Q.F i).V) (φ b : ((Q.F i).mem b).D → (Q.F i).V)).re := by
    unfold famIpAt
    rw [Complex.re_sum]
  have hN0 : 0 ≤ (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
    rw [hN]
    exact Finset.sum_nonneg fun b _ => ipAt_self_nonneg _ v _ (hp b) _
  have hB : ∀ b' d', (((Q.F (i + 1)).mem b').pairAt v ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d')
      ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d')).re ≤
      (Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re)) := by
    intro b' d'
    have e := mat_opOf_apply (Q.kk i) (Q.hF i) (fun b => ((Q.F i).mem b).outSec) φ b' d'
    change ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d') = _ at e
    rw [e]
    refine (pairAt_sum_le ((Q.F (i + 1)).mem b') v (hp' b') _ _).trans ?_
    rw [Finset.card_univ, hN, Finset.mul_sum _ _ t, Finset.mul_sum _ _ h]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (by positivity)
    refine (appOf_le v (Q.kk i b b') (Q.hF i b) (hp b) (hp' b') t ht _ d' fun d => hk b b' d d').trans ?_
    exact mul_le_mul_of_nonneg_right (hc b) (mul_nonneg ht (ipAt_self_nonneg _ v _ (hp b) _))
  have hB0 : 0 ≤ (Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re)) := by positivity
  calc (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re
      ≤ ∑ _b' : (Q.F (i + 1)).β, h' * ((Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re))) := by
        rw [famIpAt, Complex.re_sum]
        refine Finset.sum_le_sum fun b' _ => ?_
        exact (ipAt_self_le _ v _ (hp' b') _ _ (hB b')).trans (mul_le_mul_of_nonneg_right (hc' b') hB0)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end GlobalTheory.ColNorms.SumBound
end
end
