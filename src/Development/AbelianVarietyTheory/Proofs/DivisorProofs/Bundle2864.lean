module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibClosed

open GlobalTheory.SplitTorus (torusMap bcMap bcIso)

section General

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left} {X : Type} [AddCommGroup X]

theorem pullTorus_left_comp_iso (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) :
    (pullTorus h i).left ≫ h.1.isoPullback.hom = (bcIso f X).hom.left ≫ ((Over.pullback f).map i).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullTorus_left, Category.assoc]
    have : ((Over.pullback f).map i).left ≫ pullback.fst G.hom f = pullback.fst (splitTorus S X).hom f ≫ i.left := by
      simp
    rw [this, ← Category.assoc, GlobalTheory.SplitTorus.bcIso_hom_fst]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc]
    have : ((Over.pullback f).map i).left ≫ pullback.snd G.hom f = pullback.snd (splitTorus S X).hom f := by
      simp
    rw [this, Over.w (pullTorus h i)]
    exact (Over.w (bcIso f X).hom).symm

theorem mono_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    (hc : IsClosedImmersion ((Over.pullback f).map i).left) : Mono (pullTorus h i) := by
  have k := pullTorus_left_comp_iso h i
  have : Mono ((bcIso f X).hom.left ≫ ((Over.pullback f).map i).left) := inferInstance
  rw [← k] at this
  have : Mono (pullTorus h i).left := mono_of_mono _ h.1.isoPullback.hom
  exact (Over.forget _).mono_of_mono_map this

theorem closedImm_of_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    (hc : IsClosedImmersion (pullTorus h i).left) : IsClosedImmersion ((Over.pullback f).map i).left := by
  have k := pullTorus_left_comp_iso h i
  have e : ((Over.pullback f).map i).left = (bcIso f X).inv.left ≫ (pullTorus h i).left ≫ h.1.isoPullback.hom := by
    rw [k, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
  haveI : IsIso (bcIso f X).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (bcIso f X).inv))
  rw [e]
  infer_instance

theorem isClosedImmersion_of_isTorPart {tι : splitTorus S X ⟶ G} (h : IsTorPart tι) : IsClosedImmersion tι.left := by
  obtain ⟨-, B, _, q, hB, -, hk⟩ := h
  have h₁ : IsClosedImmersion (η[B].left ≫ B.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[B].left := IsClosedImmersion.of_comp _ B.hom
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hk.map (Over.forget S)).flip h₂

theorem isIso_torusMap (T : Scheme.{0}) {Y : Type} [AddCommGroup Y] (e : X ≃+ Y) :
    IsIso (torusMap T e.toAddMonoidHom) :=
  ⟨torusMap T e.symm.toAddMonoidHom, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp⟩

end General

theorem spMap_fractionRing_closedPoint (V : Type) [CommRing V] [IsDomain V] :
    (spMap (algebraMap V (FractionRing V))) (closedPoint (FractionRing V)) = genericPoint (Sp V) := by
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap V (FractionRing V)) (maximalIdeal (FractionRing V)) = ⊥
  rw [maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V _)

theorem bijective_of_mono_torusMap {κ : Type} [Field κ] {X₀ X₁ : Type} [AddCommGroup X₀] [AddCommGroup X₁]
    [Module.Free ℤ X₀] [Module.Finite ℤ X₀] [Module.Free ℤ X₁] [Module.Finite ℤ X₁]
    (hr : Module.finrank ℤ X₀ = Module.finrank ℤ X₁) (ρ : X₀ →+ X₁) [Mono (torusMap (Sp κ) ρ)] :
    Function.Bijective ρ := by
  have hs : Function.Surjective ρ := by
    let l : X₁ →+ X₁ ⧸ ρ.range := QuotientAddGroup.mk' ρ.range
    have e : torusMap (Sp κ) l ≫ torusMap (Sp κ) ρ =
        torusMap (Sp κ) (0 : X₁ →+ X₁ ⧸ ρ.range) ≫ torusMap (Sp κ) ρ := by
      rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp]
      congr 1
      ext x
      simp [l]
    have e2 := GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 e)
    intro y
    have hy : QuotientAddGroup.mk' ρ.range y = 0 := DFunLike.congr_fun e2 y
    obtain ⟨x, hx⟩ := (QuotientAddGroup.eq_zero_iff y).1 hy
    exact ⟨x, hx⟩
  let e₀ : X₁ ≃ₗ[ℤ] X₀ := LinearEquiv.ofFinrankEq X₁ X₀ hr.symm
  have hinj := OrzechProperty.injective_of_surjective_endomorphism (e₀.toLinearMap ∘ₗ ρ.toIntLinearMap)
    (e₀.surjective.comp hs)
  exact ⟨fun a b hab => hinj (by simp [hab]), hs⟩

end GlobalTheory.Poinc.FibClosed

namespace GlobalTheory.Poinc.FibClosed

open GlobalTheory.SplitTorus (torusMap bcMap bcIso)

theorem isTorPart_pullTorus_closed : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (X₁ : Type) [AddCommGroup X₁] [Module.Free ℤ X₁] [Module.Finite ℤ X₁] (j : splitTorus (Sp V) X₁ ⟶ G₁), IsMonHom j → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (t₀ : splitTorus (Sp κ) X₀ ⟶ G₀), IsTorPart t₀ → Module.finrank ℤ X₀ = Module.finrank ℤ X₁ → IsTorPart (pullTorus hψ₀ j) := by
  intro V _ _ _ G₁ _ _ hG X₁ _ _ _ j hj GK _ ψ hψ hgen κ _ b hb G₀ _ ψ₀ hψ₀ X₀ _ _ _ t₀ ht₀ hr
  haveI := hj
  let e : X₁ ≃+ (Fin (Module.finrank ℤ X₁) → ℤ) := (Module.finBasis ℤ X₁).equivFun.toAddEquiv
  let u : splitTorus (Sp V) (Fin (Module.finrank ℤ X₁) → ℤ) ⟶ G₁ := torusMap (Sp V) e.toAddMonoidHom ≫ j
  have hu : IsMonHom u := inferInstance
  have hgenU : ∀ (k : Type) [Field k] (g : Sp k ⟶ Sp V), g (closedPoint k) = genericPoint (Sp V) →
      IsClosedImmersion ((Over.pullback g).map u).left := by
    intro k _ g hg
    rw [GlobalTheory.TorusFibreImm.closedImm_iff_residue u k g, hg, ← spMap_fractionRing_closedPoint V,
      ← GlobalTheory.TorusFibreImm.closedImm_iff_residue u (FractionRing V) _]
    refine closedImm_of_pullTorus hψ u ?_
    rw [pullTorus_torusMap_comp, Over.comp_left]
    haveI := isClosedImmersion_of_isTorPart hgen
    haveI := isIso_torusMap (Sp (FractionRing V)) e
    haveI : IsIso (torusMap (Sp (FractionRing V)) e.toAddMonoidHom).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (torusMap (Sp (FractionRing V)) e.toAddMonoidHom)))
    infer_instance
  have hsp := GlobalTheory.TorusFibre.isClosedImmersion_special_of_local V (FractionRing V) G₁ hG _ u hu
    (by
      haveI := hgenU (FractionRing V) _ (spMap_fractionRing_closedPoint V)
      exact (Over.forget _).mono_of_mono_map
        (inferInstanceAs (Mono ((Over.pullback (spMap (algebraMap V (FractionRing V)))).map u).left)))
  have hfib : IsClosedImmersion ((Over.pullback (spMap b)).map u).left := by
    have h2 := (GlobalTheory.TorusFibreImm.closedImm_iff_residue u (ResidueField V) _).1 hsp
    have h3 : (Spec.map (CommRingCat.ofHom (algebraMap V (ResidueField V)))) (closedPoint (ResidueField V)) =
        (spMap b) (closedPoint κ) :=
      (IsLocalRing.comap_closedPoint (residue V)).trans (IsLocalRing.comap_closedPoint b).symm
    rw [GlobalTheory.TorusFibreImm.closedImm_iff_residue, ← h3]
    exact h2
  have hmono : Mono (pullTorus hψ₀ u) := mono_pullTorus hψ₀ u hfib
  have hmono' : Mono (pullTorus hψ₀ j) := by
    have k : pullTorus hψ₀ j = torusMap _ e.symm.toAddMonoidHom ≫ pullTorus hψ₀ u := by
      rw [pullTorus_torusMap_comp, ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp,
        show e.symm.toAddMonoidHom.comp e.toAddMonoidHom = AddMonoidHom.id X₁ from by ext x; simp,
        GlobalTheory.SplitTorus.torusMap_id, Category.id_comp]
    haveI := isIso_torusMap (Sp κ) e.symm
    rw [k]
    infer_instance
  obtain ⟨ρ, hρ⟩ := ht₀.factor (pullTorus hψ₀ j) inferInstance
  haveI : Mono (torusMap (Sp κ) ρ) := by
    rw [hρ] at hmono'
    exact mono_of_mono _ t₀
  have hbij := bijective_of_mono_torusMap (κ := κ) hr ρ
  have h := ht₀.equiv (AddEquiv.ofBijective ρ hbij)
  rw [hρ]
  exact h

end GlobalTheory.Poinc.FibClosed
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_basicOpen_between_finset_and_open : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (V : X.Opens), V ≤ W → ∀ s : Finset X, (∀ x ∈ s, x ∈ V) → ∃ f : Γ(X, W), X.basicOpen f ≤ V ∧ ∀ x ∈ s, x ∈ X.basicOpen f := by
  classical
  intro X W hW V hVW s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · refine ⟨0, ?_, fun x hx => absurd hx (Finset.notMem_empty x)⟩
    rw [Scheme.basicOpen_zero]
    exact bot_le
  set Z : Set (PrimeSpectrum Γ(X, W)) := {p | hW.fromSpec p ∉ V} with hZ
  have hZc : IsClosed Z := by
    have h := (hW.fromSpec ⁻¹ᵁ V).isOpen.isClosed_compl
    exact h
  let P : X → Ideal Γ(X, W) := fun x => if h : x ∈ W then (hW.primeIdealOf ⟨x, h⟩).asIdeal else ⊤
  have hPx : ∀ x (h : x ∈ W), P x = (hW.primeIdealOf ⟨x, h⟩).asIdeal := fun x h => by
    simp only [P, dif_pos h]
  have hP : ∀ i ∈ s, i ≠ x₀ → i ≠ x₀ → (P i).IsPrime := by
    intro x hx _ _
    rw [hPx x (hVW (hs x hx))]
    exact (hW.primeIdealOf _).isPrime
  have key : ¬ ((PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W)) ⊆
      ⋃ i ∈ (↑s : Set X), (P i : Set Γ(X, W))) := by
    rw [Ideal.subset_union_prime x₀ x₀ hP]
    rintro ⟨x, hx, hle⟩
    have hxW : x ∈ W := hVW (hs x hx)
    rw [hPx x hxW] at hle
    have hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈
        PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W)) :=
      (PrimeSpectrum.mem_zeroLocus _ _).2 hle
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq] at hmem
    apply hmem
    show hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ V
    rw [hW.fromSpec_primeIdealOf]
    exact hs x hx
  obtain ⟨f, hfI, hfP⟩ := Set.not_subset.mp key
  refine ⟨f, ?_, ?_⟩
  · intro y hy
    have hyW : y ∈ W := X.basicOpen_le f hy
    obtain ⟨p, rfl⟩ : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
    have hp : p ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f := hy
    rw [hW.fromSpec_preimage_basicOpen] at hp
    by_contra hnot
    have hpZ : p ∈ Z := hnot
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hp
      ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hfI p hpZ)
  · intro x hx
    have hxW : x ∈ W := hVW (hs x hx)
    have hf : f ∉ (hW.primeIdealOf ⟨x, hxW⟩).asIdeal := by
      intro h
      apply hfP
      rw [Set.mem_iUnion₂]
      exact ⟨x, hx, by rw [hPx x hxW]; exact h⟩
    have hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hW.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen _ _).2 hf
    have h2 : hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ X.basicOpen f := hmem
    rwa [hW.fromSpec_primeIdealOf] at h2

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FibOpen

theorem universallyOpen_of {X Y : Scheme.{0}} (f : X ⟶ Y) [UniversallyClosed f] [UniversallyInjective f]
    [Surjective f] : UniversallyOpen f := by
  constructor
  intro X' Y' i₁ i₂ f' hf
  have h1 : UniversallyClosed f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have h2 : UniversallyInjective f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have h3 : Surjective f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have hb : Function.Bijective f' := ⟨f'.injective, f'.surjective⟩
  show IsOpenMap f'
  intro U hU
  have e : f' '' U = (f' '' Uᶜ)ᶜ := by rw [Set.image_compl_eq hb, compl_compl]
  rw [e]
  exact (f'.isClosedMap _ hU.isClosed_compl).isOpen_compl

theorem fiber_hom_ext {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) {u v : T ⟶ f.fiber y}
    (h₁ : u ≫ f.fiberι y = v ≫ f.fiberι y)
    (h₂ : u ≫ f.fiberToSpecResidueField y = v ≫ f.fiberToSpecResidueField y) : u = v :=
  pullback.hom_ext h₁ h₂

@[reassoc]
theorem fiber_condition {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y) :
    f.fiberι y ≫ f = f.fiberToSpecResidueField y ≫ Y.fromSpecResidueField y :=
  pullback.condition

def fiberLift {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : T ⟶ f.fiber y :=
  pullback.lift u v h

@[reassoc (attr := simp)]
theorem fiberLift_ι {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : fiberLift f y u v h ≫ f.fiberι y = u :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fiberLift_snd {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : fiberLift f y u v h ≫ f.fiberToSpecResidueField y = v :=
  pullback.lift_snd _ _ _

theorem range_comp_fromSpecResidueField {X T : Scheme.{0}} [Nonempty T] (x : X) (t : T ⟶ Spec (X.residueField x)) :
    Set.range (t ≫ X.fromSpecResidueField x) = {x} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    rfl
  · rintro rfl
    obtain ⟨z⟩ := ‹Nonempty T›
    exact ⟨z, by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩

theorem comp_fromSpecResidueField_apply {Y T : Scheme.{0}} (y : Y) (t : T ⟶ Spec (Y.residueField y)) (z : T) :
    (t ≫ Y.fromSpecResidueField y) z = y := by
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

end GlobalTheory.FibOpen
end


set_option backward.isDefEq.respectTransparency.types false in
theorem GlobalTheory.FibOpen.fibre_universallyOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ φ : a.fiber x ⟶ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiber (τ x), φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) = a.fiberι x ≫ c → φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x) = a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x) → UniversallyOpen φ := by
  intro R _ _ _ _ S X π U a b g τ c hπp hπs hΓ hlft hsep hap haO hτ hc₁ hc₂ het x hxc hxcl hinj hsurj φ hφ₁ hφ₂
  let ψ : a.fiber x ⟶ pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) :=
    pullback.lift φ (a.fiberToSpecResidueField x) hφ₂
  have hψ₁ : ψ ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd _ _ = a.fiberToSpecResidueField x := pullback.lift_snd _ _ _
  have hSx : pullback.fst ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x) =
      pullback.snd _ _ ≫ (Spec.map (τ.residueFieldMap x)) := pullback.condition
  have hres : U.left.fromSpecResidueField x ≫ τ = (Spec.map (τ.residueFieldMap x)) ≫ 𝔸(Fin g; Sp R).fromSpecResidueField (τ x) :=
    (τ.SpecMap_residueFieldMap_fromSpecResidueField x).symm
  have hFc : (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) π ≫ π := pullback.condition
  have hb : a.fiberι x ≫ b = φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) ≫ pullback.snd _ _ := by
    rw [← hc₂, ← Category.assoc, ← hφ₁, Category.assoc]
  suffices h : UniversallyOpen ψ by
    rw [← hψ₁]; infer_instance
  haveI : IsProper a := hap
  haveI : IsProper π := hπp
  haveI : IsProper (a.fiberToSpecResidueField x) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ hap
  haveI : IsSeparated (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) := MorphismProperty.pullback_fst (P := @IsSeparated) _ _ inferInstance
  haveI : IsSeparated ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : IsProper (ψ ≫ pullback.snd _ _) := by rw [hψ₂]; infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ (pullback.snd ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)))
  haveI : UniversallyInjective ψ := by
    refine ((tfae_universallyInjective ψ).out 1 2).mpr ?_
    intro K _ q q' hq
    simp only at hq
    have e₂ : q ≫ a.fiberToSpecResidueField x = q' ≫ a.fiberToSpecResidueField x := by
      rw [← hψ₂, ← Category.assoc, hq, Category.assoc]
    have e₃ : q ≫ φ = q' ≫ φ := by rw [← hψ₁, ← Category.assoc, hq, Category.assoc]
    have ea : ∀ q : Spec (.of K) ⟶ a.fiber x, (q ≫ a.fiberι x) ≫ a =
        (q ≫ a.fiberToSpecResidueField x) ≫ U.left.fromSpecResidueField x := fun q => by
      rw [Category.assoc, Category.assoc, GlobalTheory.FibOpen.fiber_condition]
    have key := hinj K (q ≫ a.fiberι x) (q' ≫ a.fiberι x)
      (by rw [ea]; exact GlobalTheory.FibOpen.range_comp_fromSpecResidueField x _) (by rw [ea, ea, e₂])
      (by rw [Category.assoc, Category.assoc, hb, ← Category.assoc q, e₃, Category.assoc])
    exact GlobalTheory.FibOpen.fiber_hom_ext a x key e₂
  haveI : Surjective ψ := by
    constructor
    intro y
    let Ω := AlgebraicClosure ((pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).residueField y)
    let t : Sp Ω ⟶ pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) :=
      Spec.map (CommRingCat.ofHom (algebraMap ((pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).residueField y) Ω)) ≫
        (pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).fromSpecResidueField y
    let ξ := (t ≫ pullback.snd _ _) ≫ U.left.fromSpecResidueField x
    let s := t ≫ pullback.fst _ _ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) ≫ pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) π
    have hξ : ξ ≫ U.hom = s ≫ π := by
      simp only [ξ, s, Category.assoc]
      rw [← hτ, ← hFc, reassoc_of% hres, GlobalTheory.FibOpen.fiber_condition_assoc, reassoc_of% hSx]
    obtain ⟨p, hp₁, hp₂⟩ := hsurj Ω ξ s (GlobalTheory.FibOpen.range_comp_fromSpecResidueField x _) hξ
    let q : Sp Ω ⟶ a.fiber x := GlobalTheory.FibOpen.fiberLift a x p (t ≫ pullback.snd _ _) (by rw [hp₁])
    have hqt : q ≫ ψ = t := by
      apply pullback.hom_ext
      · rw [Category.assoc, hψ₁]
        apply GlobalTheory.FibOpen.fiber_hom_ext
        · rw [Category.assoc, hφ₁, GlobalTheory.FibOpen.fiberLift_ι_assoc]
          apply pullback.hom_ext
          · simp only [Category.assoc]
            rw [hc₁, reassoc_of% hp₁]
            simp only [ξ, Category.assoc]
            rw [hres, GlobalTheory.FibOpen.fiber_condition, reassoc_of% hSx]
          · simp only [Category.assoc]
            rw [hc₂, hp₂]
        · rw [Category.assoc, hφ₂, GlobalTheory.FibOpen.fiberLift_snd_assoc]
          simp only [Category.assoc]
          rw [hSx]
      · rw [Category.assoc, hψ₂, GlobalTheory.FibOpen.fiberLift_snd]
    obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
    refine ⟨q z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hqt]
    exact GlobalTheory.FibOpen.comp_fromSpecResidueField_apply y _ z
  exact GlobalTheory.FibOpen.universallyOpen_of ψ
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.lineBundleIso_of_compatible_rational_local_units : ∀ (S : Scheme.{0}) [IsIntegral S] (A B : LB S) (f : B.ι × A.ι → S.presheaf.stalk (genericPoint S)),
    (∀ p, ∀ x ∈ B.U p.1 ⊓ A.U p.2, ∃ (V : S.Opens) (_ : V ≤ B.U p.1 ⊓ A.U p.2) (_ : x ∈ V) (u : Γ(S, V)ˣ),
      ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f p) →
    (∀ p q (h1 : genericPoint S ∈ B.U p.1 ⊓ B.U q.1) (h2 : genericPoint S ∈ A.U p.2 ⊓ A.U q.2),
      f p * S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2)) =
        S.presheaf.germ _ (genericPoint S) h1 (B.g p.1 q.1 : Γ(S, B.U p.1 ⊓ B.U q.1)) * f q) →
    LBIso A B := by
  first | exact @GlobalTheory.GlueRat.lbIso_of_rat | exact GlobalTheory.GlueRat.lbIso_of_rat | (intros; apply GlobalTheory.GlueRat.lbIso_of_rat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem lb_extends_over_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (H : Over (Sp R)) [Smooth H.hom] [QuasiCompact H.hom] [IsSeparated H.hom] [GeometricallyIntegral H.hom] (L : LB ((Over.pullback (jK R)).obj H).left), L.IsLB → ∃ L' : LB H.left, L'.IsLB ∧ LBIso L (L'.pull (pullback.fst H.hom (jK R))) := by
  intro R _ _ _ H _ _ _ _ L hL
  obtain ⟨M, hM, hML⟩ := GlobalTheory.LBExtDVR.exists_lineBundle_extension_genericFibre R (FractionRing R)
    H.left ((Over.pullback (jK R)).obj H).left H.hom (pullback.snd H.hom (jK R))
    (pullback.fst H.hom (jK R)) inferInstance inferInstance (IsPullback.of_hasPullback H.hom (jK R)) L hL
  exact ⟨M, hM, LBIso.symm hML⟩

end GlobalTheory.Mum
end
