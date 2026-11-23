module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle250
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.LocalToGlobal.Divisibility.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagBundle

theorem exists_spMap_fromSpecResidueField {Z : Scheme.{0}} (y : Z) {K : Type} [Field K] (p : Sp K ⟶ Z)
    (hp : p (IsLocalRing.closedPoint K) = y) :
    ∃ σ : Z.residueField y →+* K, spMap σ ≫ Z.fromSpecResidueField y = p := by
  subst hp
  exact ⟨(Z.descResidueField (Scheme.stalkClosedPointTo p)).hom,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z p⟩

theorem coBear_swap {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X Y₁ Y₂ : Var F} {Eb : Fr (ratOf X) m 0}
    {S₁ : Fr (ratOf Y₁) m m} {φ₁ : X.Fn →ₐ[F] Y₁.Fn} {S₂ : Fr (ratOf Y₂) m m} {φ₂ : X.Fn →ₐ[F] Y₂.Fn}
    {K : Type} [Field K] {x x' : Sp K ⟶ X.X} {p₁ : Sp K ⟶ Y₁.X} {p₂ : Sp K ⟶ Y₂.X}
    (h : CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂) (hx : x = x') : CoBear Eb S₂ φ₂ S₁ φ₁ x' p₂ p₁ := by
  subst hx
  obtain ⟨A, hA, g, hg, h₁, h₂⟩ := h
  exact ⟨A, hA, g, hg, h₂, h₁⟩

end GlobalTheory.FlagBundle

theorem GlobalTheory.FlagBundle.conclusion : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ r : Sp Y₂.Fn ⟶ Y₁.X, r ≫ f₁ = (ratOf Y₂).pt ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (r ≫ f₁) r (ratOf Y₂).pt → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = r (IsLocalRing.closedPoint Y₂.Fn) → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ r hr hrc K _ p p' hp hpp' hc
  set y₁ := r (IsLocalRing.closedPoint Y₂.Fn)
  let c : Sp (Y₁.X.residueField y₁) ⟶ Y₁.X := Y₁.X.fromSpecResidueField y₁
  obtain ⟨τ, hτ⟩ := exists_spMap_fromSpecResidueField y₁ r rfl
  obtain ⟨σ, hσ⟩ := exists_spMap_fromSpecResidueField y₁ p hp
  obtain ⟨A, hA, g, hg, hb₁⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₁ Eb S₁ φ₁ f₁ hR₁ _ c
  obtain ⟨s, ⟨hs, hb₂⟩, -⟩ := hR₂.2.2 _ (c ≫ f₁) A hA g hg
  have hcs : CoBear Eb S₁ φ₁ S₂ φ₂ (c ≫ f₁) c s := ⟨A, hA, g, hg, hb₁, hb₂⟩
  have hτc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ _ _ τ _ _ _ hcs
  have hσc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ _ _ σ _ _ _ hcs
  have hτ' : spMap τ ≫ c = r := hτ
  have hσ' : spMap σ ≫ c = p := hσ
  rw [hτ'] at hτc
  rw [hσ'] at hσc
  have e₁ : (spMap τ ≫ s) ≫ f₂ = r ≫ f₁ := by rw [Category.assoc, hs, ← Category.assoc, hτ']
  have e₂ : (spMap σ ≫ s) ≫ f₂ = p ≫ f₁ := by rw [Category.assoc, hs, ← Category.assoc, hσ']
  have k₁ : spMap τ ≫ s = (ratOf Y₂).pt :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ _ _ _ r e₁ hr.symm
      (coBear_swap hτc (by rw [Category.assoc, hs])) (coBear_swap hrc hr)
  have k₂ : p' = spMap σ ≫ s :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ _ _ _ p hpp'.symm e₂
      (coBear_swap hc hpp') (coBear_swap hσc (by rw [Category.assoc, hs]))
  have hgen : s (IsLocalRing.closedPoint _) = genericPoint Y₂.X := by
    have e : (spMap τ ≫ s) (IsLocalRing.closedPoint Y₂.Fn) = s (IsLocalRing.closedPoint _) := by
      exact (Scheme.Hom.comp_apply _ _ _).trans
        (congrArg s (Subsingleton.elim (α := PrimeSpectrum (Y₁.X.residueField y₁)) _ _))
    rw [← e, k₁]
    exact Scheme.fromSpecStalk_closedPoint
  rw [k₂, ← hgen]
  exact (Scheme.Hom.comp_apply _ _ _).trans
    (congrArg s (Subsingleton.elim (α := PrimeSpectrum (Y₁.X.residueField y₁)) _ _))
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle

theorem coBear_comp_of_isHom : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ g : Y₁.X ⟶ Y₂.X, (ratOf Y₂).IsHom (ratOf Y₁) ψ g → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ ψ hψ hgen g hg K _ p
  have hgf : g ≫ f₂ = f₁ := by
    have := h₂.1.comp hg
    rw [hψ] at this
    exact this.unique h₁.1

  let y : Y₁.X := p (IsLocalRing.closedPoint K)
  let R := Y₁.X.presheaf.stalk y
  let v₁ : Sp R ⟶ Y₁.X := Y₁.X.fromSpecStalk y
  have hpt : spMap (algebraMap R Y₁.Fn) ≫ v₁ = (ratOf Y₁).pt :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  have hinc := GlobalTheory.T.fullFlag_common_closedPoint_of_generic F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ R Y₁.Fn v₁ (v₁ ≫ g)
    (by rw [Category.assoc, hgf]) (by
      have e1 : spMap (algebraMap R Y₁.Fn) ≫ v₁ ≫ f₁ = (ratOf Y₁).pt ≫ f₁ := by
        rw [← Category.assoc]; exact congrArg (· ≫ f₁) hpt
      have e2 : spMap (algebraMap R Y₁.Fn) ≫ v₁ ≫ g = spMap ψ.toRingHom ≫ (ratOf Y₂).pt := by
        rw [← Category.assoc, hpt]; exact hg
      rw [e1, hpt, e2]; exact hgen)

  let c := Scheme.stalkClosedPointTo (R := .of K) p
  let σ : IsLocalRing.ResidueField R →+* K := IsLocalRing.ResidueField.lift c.hom
  have hσ : σ.comp (IsLocalRing.residue R) = c.hom := IsLocalRing.ResidueField.lift_comp_residue c.hom
  have hp : spMap σ ≫ spMap (IsLocalRing.residue R) ≫ v₁ = p := by
    rw [← Category.assoc, ← spMap_comp, hσ]
    exact spMap_stalkClosedPointTo p
  have hbc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ (IsLocalRing.ResidueField R) K σ _ _ _ hinc
  rw [← hp]
  simpa only [Category.assoc] using hbc

end GlobalTheory.FlagBundle
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle.Dom

theorem mem_O_of_forall_dvr {F : Type} [Field F] (Y : Var F) (y : (ratOf Y).Z) (x : Y.Fn)
    (hx : ∀ V : ValuationSubring Y.Fn, IsDiscreteValuationRing V →
      LocalSubring.range (algebraMap ((ratOf Y).O y) Y.Fn) ≤ V.toLocalSubring → x ∈ V) :
    x ∈ (ratOf Y).O y := by
  haveI := (ratOf Y).lft
  haveI : IsLocallyNoetherian (ratOf Y).Z := LocallyOfFiniteType.isLocallyNoetherian (ratOf Y).s
  haveI : IsNoetherianRing ((ratOf Y).O y) :=
    isNoetherianRing_of_ringEquiv _ ((ratOf Y).stalkEquiv y)
  haveI : Algebra.EssFiniteType ((ratOf Y).O y) Y.Fn :=
    Algebra.EssFiniteType.of_isLocalization Y.Fn (nonZeroDivisors ((ratOf Y).O y))
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (ratOf Y).Z := fun z =>
    ⟨(Y.isNormalScheme).isDomain_stalk z, (Y.isNormalScheme).isIntegrallyClosed_stalk z⟩
  haveI := RatModel.isIntegrallyClosed_O hN y
  by_contra hn
  have hi : ¬ IsIntegral ((ratOf Y).O y) x := fun h => by
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    exact hn a.2
  obtain ⟨V, h1, h2, h3⟩ := GlobalTheory.exists_discreteValuationSubring_dominating_notMem hi
  exact h3 (hx V h1 h2)

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle.Dom

theorem exists_pt_of_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z)
    (V : ValuationSubring Ω) (hV : LocalSubring.range (algebraMap (M.O z) Ω) ≤ V.toLocalSubring) :
    ∃ v : Sp V ⟶ M.Z, v (IsLocalRing.closedPoint V) = z ∧ spMap (algebraMap V Ω) ≫ v = M.pt ∧
      ∃ σ : IsLocalRing.ResidueField (M.Z.presheaf.stalk z) →+* IsLocalRing.ResidueField V,
        spMap (IsLocalRing.residue V) ≫ v = spMap σ ≫ spMap (IsLocalRing.residue _) ≫ M.Z.fromSpecStalk z := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.localSubring_range_le_valuationSubring_iff _ V).1 hV
  let ι : M.O z →+* V := (algebraMap (M.O z) Ω).codRestrict V h1
  haveI hι : IsLocalHom ι := ⟨fun r hr => by
    by_contra hn
    obtain ⟨_, hm⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).1 (h2 r hn)
    exact hm hr⟩
  let g : M.Z.presheaf.stalk z →+* V := ι.comp (M.stalkEquiv z).toRingHom
  haveI : IsLocalHom g := ⟨fun a ha =>
    (isUnit_map_iff (M.stalkEquiv z) a).1 (IsLocalHom.map_nonunit (f := ι) _ ha)⟩
  refine ⟨spMap g ≫ M.Z.fromSpecStalk z, ?_, ?_, IsLocalRing.ResidueField.map g, ?_⟩
  · show M.Z.fromSpecStalk z (spMap g (IsLocalRing.closedPoint V)) = z
    rw [show spMap g (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint _ from IsLocalRing.comap_closedPoint g]
    exact Scheme.fromSpecStalk_closedPoint
  · have e : (algebraMap V Ω).comp g = M.stalkHom z := rfl
    have e2 : spMap (M.stalkHom z) = spMap (Scheme.stalkClosedPointTo (R := .of Ω) M.pt).hom ≫
        Spec.map (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) z)) := by
      rw [RatModel.stalkHom]
      show Spec.map _ = _
      rw [CommRingCat.ofHom_hom, Spec.map_comp]
      rfl
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    change spMap (M.stalkHom z) ≫ _ = _
    rw [e2, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo M.pt
  · rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.map_comp_residue]

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle.Dom

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X Y₁ Y₂ : Var F} {Eb : Fr (ratOf X) m 0}
  {S₁ : Fr (ratOf Y₁) m m} {φ₁ : X.Fn →ₐ[F] Y₁.Fn} {S₂ : Fr (ratOf Y₂) m m} {φ₂ : X.Fn →ₐ[F] Y₂.Fn}

theorem coBear_swap {K : Type} [Field K] {x x' : Sp K ⟶ X.X} {p₁ p₁' : Sp K ⟶ Y₁.X}
    {p₂ p₂' : Sp K ⟶ Y₂.X} (hx : x = x') (hp₁ : p₁ = p₁') (hp₂ : p₂ = p₂')
    (h : CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂) : CoBear Eb S₂ φ₂ S₁ φ₁ x' p₂' p₁' := by
  subst hx hp₁ hp₂
  obtain ⟨A, hA, g, hg, b₁, b₂⟩ := h
  exact ⟨A, hA, g, hg, b₂, b₁⟩

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle


open GlobalTheory.FlagBundle.Dom in
theorem dominates_O (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F)
    (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X) (h₁ : Reps Eb S₁ φ₁ f₁)
    (h₂ : Reps Eb S₂ φ₂ f₂) (ψ : Y₂.Fn →ₐ[F] Y₁.Fn) (hψ : ψ.comp φ₂ = φ₁)
    (hg : CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt))
    (y : Y₁.X) : ∃ y' : Y₂.X, ∀ a ∈ (ratOf Y₂).O y', ψ a ∈ (ratOf Y₁).O y := by
  let κ := IsLocalRing.ResidueField (Y₁.X.presheaf.stalk y)
  let py : Sp κ ⟶ Y₁.X := spMap (IsLocalRing.residue _) ≫ Y₁.X.fromSpecStalk y
  obtain ⟨A, hA, h, hh, hb⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₁ Eb S₁ φ₁ f₁ h₁ κ py
  obtain ⟨s, ⟨hs, hsb⟩, -⟩ := h₂.2.2 κ (py ≫ f₁) A hA h hh
  refine ⟨s (IsLocalRing.closedPoint κ), fun a ha => ?_⟩
  refine mem_O_of_forall_dvr Y₁ y (ψ a) fun V _ hV => ?_
  obtain ⟨v, -, hv1, σ, hv2⟩ := exists_pt_of_le (ratOf Y₁) y V hV
  haveI : IsProper (f₂ ≫ X.str) := by
    rw [show f₂ ≫ X.str = Y₂.str from h₂.1.inducedModelMorphism_comp_structureMap]
    infer_instance
  haveI : IsProper f₂ := IsProper.of_comp f₂ X.str
  have hψ' : spMap ψ.toRingHom ≫ spMap φ₂.toRingHom = spMap φ₁.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hψ]
    rfl
  have hq : (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) ≫ f₂ = spMap (algebraMap V Y₁.Fn) ≫ (v ≫ f₁) := by
    have e1 : (ratOf Y₂).pt ≫ f₂ = spMap φ₂.toRingHom ≫ (ratOf X).pt := h₂.1
    have e2 : (ratOf Y₁).pt ≫ f₁ = spMap φ₁.toRingHom ≫ (ratOf X).pt := h₁.1
    erw [Category.assoc, e1, ← Category.assoc, hψ', ← e2, ← Category.assoc, hv1]
  obtain ⟨ℓ, ⟨hℓ1, hℓ2⟩, -⟩ :=
    GlobalTheory.ModelPoints.existsUnique_extension f₂ (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) (v ≫ f₁) hq
  have hinc := GlobalTheory.T.fullFlag_common_closedPoint_of_generic F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ V Y₁.Fn v ℓ hℓ1.symm
    (by erw [hℓ2, ← Category.assoc, hv1]; exact hg)
  have hbc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ κ (IsLocalRing.ResidueField V) σ
    (py ≫ f₁) py s ⟨A, hA, h, hh, hb, hsb⟩
  have hpv : spMap (IsLocalRing.residue V) ≫ v = spMap σ ≫ py := hv2
  have E1 : (spMap (IsLocalRing.residue V) ≫ ℓ) ≫ f₂ = (spMap σ ≫ py) ≫ f₁ :=
    (Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue V) ≫ ·) hℓ1).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f₁) hpv)))
  have E2 : (spMap σ ≫ s) ≫ f₂ = (spMap σ ≫ py) ≫ f₁ :=
    (Category.assoc _ _ _).trans ((congrArg (spMap σ ≫ ·) hs).trans (Category.assoc _ _ _).symm)
  have E3 : spMap (IsLocalRing.residue V) ≫ v ≫ f₁ = (spMap (IsLocalRing.residue V) ≫ ℓ) ≫ f₂ :=
    (congrArg (spMap (IsLocalRing.residue V) ≫ ·) hℓ1.symm).trans (Category.assoc _ _ _).symm
  have E4 : spMap σ ≫ py ≫ f₁ = (spMap σ ≫ s) ≫ f₂ :=
    (congrArg (spMap σ ≫ ·) hs.symm).trans (Category.assoc _ _ _).symm
  have e : spMap (IsLocalRing.residue V) ≫ ℓ = spMap σ ≫ s :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ h₂ h₁ _ (spMap (IsLocalRing.residue V) ≫ ℓ)
      (spMap σ ≫ s) (spMap σ ≫ py) E1 E2 (_root_.GlobalTheory.FlagBundle.Dom.coBear_swap E3 hpv rfl hinc) (_root_.GlobalTheory.FlagBundle.Dom.coBear_swap E4 rfl rfl hbc)
  have hℓc : ℓ (IsLocalRing.closedPoint V) = s (IsLocalRing.closedPoint κ) := by
    have h3 : ℓ (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) =
        s (spMap σ (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) :=
      congrArg (fun t : Sp (IsLocalRing.ResidueField V) ⟶ Y₂.X =>
        t (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) e
    have h4 : spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
        IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
    have h5 : spMap σ (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint κ :=
      Subsingleton.elim (α := PrimeSpectrum κ) _ _
    rw [h4, h5] at h3
    exact h3
  have hsp : ℓ (IsLocalRing.closedPoint V) ⤳ s (IsLocalRing.closedPoint κ) := hℓc ▸ specializes_rfl
  have k1 := RatModel.val_spMap_comp (M := ratOf Y₂) (algebraMap V Y₁.Fn) ℓ hsp ⟨a, ha⟩
  have k2 := RatModel.val_spMap_comp (M := ratOf Y₂) ψ.toRingHom (ratOf Y₂).pt
    ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, ha⟩
  have k4 := (RatModel.valLoc_eq_val (M := ratOf Y₂) (ratOf Y₂).pt
    ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) (s (IsLocalRing.closedPoint κ))) ⟨a, ha⟩).trans
    (RatModel.val_pt (M := ratOf Y₂) a)
  have k3 : ψ a = algebraMap V Y₁.Fn (RatModel.valLoc ℓ _ hsp ⟨a, ha⟩) := by
    calc ψ a = ψ.toRingHom (RatModel.valLoc (ratOf Y₂).pt _
          ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) (s (IsLocalRing.closedPoint κ))) ⟨a, ha⟩) :=
          (congrArg ψ.toRingHom k4).symm
      _ = (ratOf Y₂).val (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) a := k2.symm
      _ = (ratOf Y₂).val (spMap (algebraMap V Y₁.Fn) ≫ ℓ) a :=
          congrArg (fun t : Sp Y₁.Fn ⟶ Y₂.X => (ratOf Y₂).val t a) hℓ2.symm
      _ = _ := k1
  rw [k3]
  exact (RatModel.valLoc ℓ _ hsp ⟨a, ha⟩).2

end GlobalTheory.FlagBundle
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Mem

theorem cnorm_mulVec_eq_of_gram {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (M : Matrix ι μ ℂ) (N : Matrix κ μ ℂ) (h : Mᴴ * M = Nᴴ * N) (u : μ → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (M.mulVec u) = Formalism.HermitianLatticesTheory.cnorm (N.mulVec u) := by
  have key : ∀ {ι : Type} [Fintype ι] (M : Matrix ι μ ℂ),
      ((∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ (Mᴴ * M).mulVec u := by
    intro ι _ M
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    push_cast
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
  have h2 : (∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) = ∑ i, ‖N.mulVec u i‖ ^ 2 := by
    have := key M
    rw [h, ← key N] at this
    exact_mod_cast this
  unfold Formalism.HermitianLatticesTheory.cnorm
  rw [h2]

theorem exists_restricted_frames : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A : HLat K)
    (U : Submodule K A.V) (L : Submodule (𝓞 K) U), (∀ v, IsUnit (A.X v).det) →
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K U) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
      (∀ v, IsUnit (X v).det) ∧
        ∀ v (x : U), Formalism.HermitianLatticesTheory.normAt b X v x = Formalism.HermitianLatticesTheory.normAt A.b A.X v (x : A.V) := by
  intro K _ _ _ A U _ hX
  have : Module.Finite K A.V := Module.Finite.of_basis A.b
  let n := Module.finrank K U
  let b : Module.Basis (Fin n) K U := Module.finBasis K U
  let E : Matrix A.ι (Fin n) K := LinearMap.toMatrix b A.b U.subtype
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  have hLE : LinearMap.toMatrix A.b b g * E = 1 := by
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  let M : InfinitePlace K → Matrix A.ι (Fin n) ℂ := fun v => (A.X v)⁻¹ * E.map v.embedding
  have hM : ∀ v, Function.Injective (M v).mulVec := by
    intro v x y hxy
    have h1 : ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v) * M v = 1 := by
      simp only [M]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.X v), Matrix.mul_nonsing_inv _ (hX v),
        Matrix.one_mul, ← Matrix.map_mul, hLE, Formalism.L2.DIV.map_one']
    have := congrArg ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v).mulVec hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.one_mulVec] at this
  have hP : ∀ v, ((M v)ᴴ * M v).PosDef := fun v => Matrix.PosDef.conjTranspose_mul_self _ (hM v)
  refine ⟨n, b, fun v => Formalism.L2.DIV.frameOf ((M v)ᴴ * M v),
    fun v => (Formalism.L2.DIV.frameOfSpec n _ (hP v)).1, fun v x => ?_⟩
  have h2 := (Formalism.L2.DIV.frameOfSpec n _ (hP v)).2
  have h3 : Formalism.HermitianLatticesTheory.vecAt A.b v (x : A.V) = (E.map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    have h4 := LinearMap.toMatrix_mulVec_repr b A.b U.subtype x
    funext i
    have h5 := congrFun h4 i
    simp only [Submodule.subtype_apply] at h5
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← h5]
    simp [Matrix.mulVec, dotProduct, E, Formalism.HermitianLatticesTheory.vecAt]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  rw [h3, Matrix.mulVec_mulVec]
  exact cnorm_mulVec_eq_of_gram _ _ h2 _

end GlobalTheory.Mem

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

theorem hasSignature_diagonal_sgn (N : ℕ) (neg : Fin N → Bool) :
    Formalism.UG.HasSignature (Matrix.diagonal fun i : Fin N => (Examples₂.sgn (neg i) : ℂ))
      (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card := by
  classical
  let e1 : {i // neg i = false} ≃ Fin (Finset.univ.filter fun i => neg i = false).card :=
    Fintype.equivFinOfCardEq (Fintype.card_subtype _)
  let e2 : {i // ¬ neg i = false} ≃ Fin (Finset.univ.filter fun i => neg i = true).card :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simp)
  let f : Fin (Finset.univ.filter fun i => neg i = false).card ⊕
      Fin (Finset.univ.filter fun i => neg i = true).card ≃ Fin N :=
    (Equiv.sumCongr e1.symm e2.symm).trans (Equiv.sumCompl fun i => neg i = false)
  have h1 : ∀ i, neg (f (Sum.inl i)) = false := fun i => (e1.symm i).2
  have h2 : ∀ i, neg (f (Sum.inr i)) = true := fun i => by
    have h : ¬ neg (f (Sum.inr i)) = false := (e2.symm i).2
    simpa using h
  refine ⟨f.symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h1, h2, Examples₂.sgn]
  split_ifs <;> simp

theorem stdSpace_sigOK_count (E : Type) [Field E] [NumberField E] [StarRing E]
    (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) (neg : Fin N → Bool) :
    (Formalism.BasicNotions.Examples₂.stdSpace hstar N neg (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card).SigOK := by
  intro τ
  have hg : (Formalism.BasicNotions.Examples₂.stdSpace hstar N neg (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card).gram.map τ =
      Matrix.diagonal fun i : Fin N => (Examples₂.sgn (neg i) : ℂ) := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (Examples₂.stdSpace_gram_apply hstar N neg _ _ i j)).trans ?_
    change τ (if i = j then (Examples₂.sgn (neg i) : E) else 0) =
      if i = j then (Examples₂.sgn (neg i) : ℂ) else 0
    by_cases h : i = j <;> simp [h, Examples₂.map_sgn]
  rw [hg]
  exact hasSignature_diagonal_sgn N neg

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_comparison_data_independent_of_algebraic_forms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), ∃ O' : OMDat T.toCore (updFW R nW FW) i Tp tup, O'.c' = O.c' ∧ O'.lev = O.lev ∧ (O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) → O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀)) ∧ ∀ (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (ph : ℂ), O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph → O'.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := by
  first | exact @GlobalTheory.RealGeo.omDat_updFW | exact GlobalTheory.RealGeo.omDat_updFW | (intros; apply GlobalTheory.RealGeo.omDat_updFW <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.BaseChars

theorem eq_of_pow_eq {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {om : (ZMod p)ˣ →* Kˣ} (hom : Function.Injective om)
    {a b : ℕ} (ha : a < p - 1) (hb : b < p - 1) (h : ∀ x, om x ^ a = om x ^ b) : a = b := by
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have h1 := h g
  rw [← map_pow, ← map_pow] at h1
  exact pow_injOn_Iio_orderOf (x := g) (by rwa [Set.mem_Iio, hog]) (by rwa [Set.mem_Iio, hog]) (hom h1)

theorem nonempty_equiv_zmod {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hw : Ideal.absNorm w.asIdeal = p) : Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod p) := by
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  exact ⟨(ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])).symm⟩

end GlobalTheory.BaseChars
end
