module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle633
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle144
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicIntegralReadingOfTrivialisations
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem isLocalHom_of_map_maximalIdeal {W κ : Type} [CommRing W] [IsLocalRing W] [Field κ] (c : W →+* κ)
    (hc : ∀ x ∈ maximalIdeal W, c x = 0) : IsLocalHom c :=
  ⟨fun a ha => by
    by_contra h
    have hm : a ∈ maximalIdeal W := (IsLocalRing.mem_maximalIdeal a).2 h
    rw [hc a hm] at ha
    exact not_isUnit_zero ha⟩

theorem exists_common_residue {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] [CommRing V]
    [IsLocalRing V] (ψ : R →+* W) [IsLocalHom ψ] (g : R →+* V) [IsLocalHom g] :
    ∃ (κ : Type) (_ : Field κ) (c : W →+* κ) (b : V →+* κ), (∀ x ∈ maximalIdeal W, c x = 0) ∧
      (∀ x ∈ maximalIdeal V, b x = 0) ∧ c.comp ψ = b.comp g := by
  letI : Algebra (ResidueField R) (ResidueField W) := (ResidueField.map ψ).toAlgebra
  letI : Algebra (ResidueField R) (ResidueField V) := (ResidueField.map g).toAlgebra
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (ResidueField W ⊗[ResidueField R] ResidueField V)
  letI := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  refine ⟨_ ⧸ M, inferInstance, q.comp ((Algebra.TensorProduct.includeLeftRingHom).comp (residue W)),
    q.comp ((Algebra.TensorProduct.includeRight.toRingHom).comp (residue V)), fun x hx => ?_, fun x hx => ?_,
    RingHom.ext fun r => ?_⟩
  · simp [(IsLocalRing.residue_eq_zero_iff x).2 hx]
  · simp [(IsLocalRing.residue_eq_zero_iff x).2 hx]
  · simp only [RingHom.comp_apply]
    congr 1
    rw [← ResidueField.map_residue ψ r, ← ResidueField.map_residue g r]
    change Algebra.TensorProduct.includeLeftRingHom (algebraMap (ResidueField R) (ResidueField W) (residue R r)) =
      Algebra.TensorProduct.includeRight (algebraMap (ResidueField R) (ResidueField V) (residue R r))
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem spread₂_of_trait {B : Scheme.{0}} (H : Over B) [GrpObj H]
    {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {D₁ : DegData V₁ (maximalIdeal V₁)}
    {A₁ : PolAV (Sp (FractionRing V₁))} {G₁ : Over (Sp V₁)} [GrpObj G₁] [IsCommMonObj G₁]
    {V₂ : Type} [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] {D₂ : DegData V₂ (maximalIdeal V₂)}
    {A₂ : PolAV (Sp (FractionRing V₂))} {G₂ : Over (Sp V₂)} [GrpObj G₂] [IsCommMonObj G₂]
    (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left)
    (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left)
    {R : Type} [CommRing R] [IsLocalRing R] (ιB : Sp R ⟶ B) (HR : Over (Sp R)) [GrpObj HR] [IsCommMonObj HR]
    (φR : HR.left ⟶ H.left) (hR : IsGrpPullback HR H ιB φR)
    (g₁ : R →+* V₁) (β₁' : G₁.left ⟶ HR.left) (eβ₁ : β₁' ≫ φR = β₁) (hξ₁ : spMap g₁ ≫ ιB = ξ₁)
    (g₂ : R →+* V₂) (hg₂ : IsLocalHom g₂) (β₂' : G₂.left ⟶ HR.left) (hβ₂ : IsGrpPullback G₂ HR (spMap g₂) β₂')
    (eβ₂ : β₂' ≫ φR = β₂) (hξ₂ : spMap g₂ ≫ ιB = ξ₂)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ψ₀ : R →+* W) (hψ : IsLocalHom ψ₀)
    (Ω : Type) [Field Ω] (α : W →+* Ω) (hα : Function.Injective α) (b₁ : V₁ →+* Ω)
    (hb₁ : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0) (eα : α.comp ψ₀ = b₁.comp g₁)
    (GΩ : Over (Sp Ω)) [GrpObj GΩ] (n : GΩ.left ⟶ ((Over.pullback (spMap ψ₀)).obj HR).left)
    (hn : IsGrpPullback GΩ ((Over.pullback (spMap ψ₀)).obj HR) (spMap α) n)
    (n₁ : GΩ.left ⟶ G₁.left) (hn₁ : IsGrpPullback GΩ G₁ (spMap b₁) n₁)
    (hnn : n ≫ pullback.fst HR.hom (spMap ψ₀) = n₁ ≫ β₁')
    (j : splitTorus (Sp W) D₁.toPre.X ⟶ (Over.pullback (spMap ψ₀)).obj HR) (hj : IsMonHom j)
    (ej : GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb₁ hn₁) :
    ∃ ρ, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  haveI := hψ
  haveI := hg₂
  haveI := hj
  obtain ⟨κ, _, c, b₂, hc0, hb0, ec⟩ := exists_common_residue ψ₀ g₂
  have hcl : IsLocalHom c := isLocalHom_of_map_maximalIdeal c hc0
  have hb₂ := GlobalTheory.TorusPart.map_pow_one_eq_zero hb0
  have hW := isGrpPullback_pullback HR (spMap ψ₀)
  have hm := isGrpPullback_pullback ((Over.pullback (spMap ψ₀)).obj HR) (spMap c)
  obtain ⟨m₂, hm₂, em₂⟩ := GlobalTheory.SpreadTrait.pull_cancel hβ₂ (spMap b₂)
    ((hm.comp hW).congr ((GlobalTheory.SpreadTrait.spMap_comp' ψ₀ c).trans
      ((congrArg spMap ec).trans (GlobalTheory.SpreadTrait.spMap_comp' g₂ b₂).symm)) rfl)
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₂.gt 0) hb₂ hm₂).2 _
    (GlobalTheory.TorusPart.pullTorus hm j) inferInstance
  refine ⟨ρ, W, inferInstance, inferInstance, inferInstance, spMap ψ₀ ≫ ιB, (Over.pullback (spMap ψ₀)).obj HR,
    inferInstance, inferInstance, pullback.fst HR.hom (spMap ψ₀) ≫ φR, j, Ω, inferInstance, α, b₁, hb₁, GΩ,
    inferInstance, n, hn, n₁, hn₁, κ, inferInstance, c, b₂, hb₂, _, inferInstance, _, hm, m₂, hm₂, hW.comp hR, hj, hα,
    hcl, ?_, ?_, ?_, ?_, ej, hρ⟩
  · rw [← hξ₁, ← Category.assoc, ← Category.assoc, GlobalTheory.SpreadTrait.spMap_comp', GlobalTheory.SpreadTrait.spMap_comp', eα]
  · rw [← hξ₂, ← Category.assoc, ← Category.assoc, GlobalTheory.SpreadTrait.spMap_comp', GlobalTheory.SpreadTrait.spMap_comp', ec]
  · rw [← Category.assoc, hnn, Category.assoc, eβ₁]
  · rw [← eβ₂, ← Category.assoc m₂, em₂, Category.assoc]

theorem exists_spread₂ : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → IsIntegral B → IsLocallyNoetherian B → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → ∃ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ hBi hBn hsp
  haveI := hBi
  haveI := hBn
  let R : Type := B.presheaf.stalk (ξ₂ (closedPoint V₂))
  let ιB : Sp R ⟶ B := B.fromSpecStalk (ξ₂ (closedPoint V₂))
  let HR := (Over.pullback ιB).obj H
  have hHR : IsSemiAbelian HR := IsSemiAbelian.pullback ιB H hH
  haveI : IsCommMonObj HR := hHR.comm
  have hR := isGrpPullback_pullback H ιB
  let g₁ : R →+* V₁ := (B.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ₁).hom
  let g₂ : R →+* V₂ := (Scheme.stalkClosedPointTo ξ₂).hom
  have hg₂ : IsLocalHom g₂ := Scheme.isLocalHom_stalkClosedPointTo' ξ₂
  have hξ₁ : spMap g₁ ≫ ιB = ξ₁ := by
    have e : spMap g₁ = Spec.map (Scheme.stalkClosedPointTo ξ₁) ≫ Spec.map (B.presheaf.stalkSpecializes hsp) := by
      rw [← Spec.map_comp]; rfl
    rw [e, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hξ₂ : spMap g₂ ≫ ιB = ξ₂ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₂
  obtain ⟨β₁', hβ₁', eβ₁⟩ := GlobalTheory.SpreadTrait.pull_cancel hR (spMap g₁) (hβ₁.congr hξ₁.symm rfl)
  obtain ⟨β₂', hβ₂', eβ₂⟩ := GlobalTheory.SpreadTrait.pull_cancel hR (spMap g₂) (hβ₂.congr hξ₂.symm rfl)
  by_cases hl : IsLocalHom g₁
  · haveI := hl
    let κ₁ := ResidueField V₁
    have hC : IsLocalHom (PowerSeries.C (R := κ₁)) :=
      ⟨fun a ha => by simpa using ha.map (PowerSeries.constantCoeff (R := κ₁))⟩
    let c₁ : V₁ →+* PowerSeries κ₁ := (PowerSeries.C (R := κ₁)).comp (residue V₁)
    have hcl : IsLocalHom c₁ := RingHom.isLocalHom_comp _ _
    let ψ₀ : R →+* PowerSeries κ₁ := c₁.comp g₁
    have hψ : IsLocalHom ψ₀ := RingHom.isLocalHom_comp _ _
    let α := algebraMap (PowerSeries κ₁) (FractionRing (PowerSeries κ₁))
    have hα : Function.Injective α := IsFractionRing.injective _ _
    let b₁ : V₁ →+* FractionRing (PowerSeries κ₁) := α.comp c₁
    have hc0 : ∀ x ∈ maximalIdeal V₁, c₁ x = 0 := fun x hx => by
      simp [c₁, (IsLocalRing.residue_eq_zero_iff x).2 hx]
    have hc : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), c₁ x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hc0
    have hb : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0 := fun x hx => by
      simp [b₁, hc x hx]
    have hm₁ := isGrpPullback_pullback HR (spMap ψ₀)
    obtain ⟨mc, hmc, hmcβ⟩ := GlobalTheory.SpreadTrait.pull_cancel hβ₁' (spMap c₁)
      (hm₁.congr (GlobalTheory.SpreadTrait.spMap_comp' g₁ c₁).symm rfl)
    have hn := isGrpPullback_pullback ((Over.pullback (spMap ψ₀)).obj HR) (spMap α)
    have hn' : IsGrpPullback _ G₁ (spMap b₁) _ := (hn.comp hmc).congr (GlobalTheory.SpreadTrait.spMap_comp' c₁ α) rfl
    have hnn : pullback.fst ((Over.pullback (spMap ψ₀)).obj HR).hom (spMap α) ≫ pullback.fst HR.hom (spMap ψ₀) =
        (pullback.fst ((Over.pullback (spMap ψ₀)).obj HR).hom (spMap α) ≫ mc) ≫ β₁' := by
      rw [Category.assoc, hmcβ]
    exact spread₂_of_trait H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ιB HR _ hR g₁ β₁' eβ₁ hξ₁ g₂ hg₂ β₂' hβ₂' eβ₂ hξ₂
      (PowerSeries κ₁) ψ₀ hψ _ α hα b₁ hb rfl _ _ hn _ hn' hnn
      (GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hc hmc) inferInstance
      (GlobalTheory.TorusPart.pullTorus_gtTorus (U₁.gt 0) hc hb hmc hn' hn rfl rfl)
  · obtain ⟨W, _, _, _, ψ₀, Ω, _, αK, b₁, hψ, hb, eα, hT⟩ := GlobalTheory.T.exists_trait_nonlocal_torusExtension' R HR hHR V₁ g₁ hl
    haveI := hψ
    let alg := algebraMap W (FractionRing W)
    have hα : Function.Injective (αK.comp alg) :=
      αK.injective.comp (IsFractionRing.injective W (FractionRing W))
    have hm₁ := isGrpPullback_pullback HR (spMap ψ₀)
    have hG₁' : IsSemiAbelian ((Over.pullback (spMap ψ₀)).obj HR) := IsSemiAbelian.pullback _ HR hHR
    obtain ⟨φ₁, hφ₁, -⟩ := GlobalTheory.SpreadTrait.pull_cancel hm₁ (spMap alg)
      ((isGrpPullback_pullback HR (spMap (alg.comp ψ₀))).congr (GlobalTheory.SpreadTrait.spMap_comp' ψ₀ alg).symm rfl)
    have hn' := isGrpPullback_pullback G₁ (spMap b₁)
    obtain ⟨n, hn, hnm⟩ := GlobalTheory.SpreadTrait.pull_cancel hm₁ (spMap (αK.comp alg))
      ((hn'.comp hβ₁').congr ((GlobalTheory.SpreadTrait.spMap_comp' g₁ b₁).trans ((congrArg spMap eα.symm).trans
        (GlobalTheory.SpreadTrait.spMap_comp' ψ₀ (αK.comp alg)).symm)) rfl)
    have hb' : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hb
    obtain ⟨j, hj, ej⟩ := GlobalTheory.T.extend_splitTorus_hom_over_dvr W ((Over.pullback (spMap ψ₀)).obj HR) hG₁' _ φ₁ hφ₁ hT Ω αK _ n hn _
      (GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb' hn') inferInstance
    exact spread₂_of_trait H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ιB HR _ hR g₁ β₁' eβ₁ hξ₁ g₂ hg₂ β₂' hβ₂' eβ₂ hξ₂
      W ψ₀ hψ Ω (αK.comp alg) hα b₁ hb' eα _ n hn _ hn' hnm j hj ej

end GlobalTheory.Poinc.Sep.Spz
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem pullback_map_eq_of_pullTorus_eq {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {p : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G p φ) {X : Type} [AddCommGroup X]
    (f g : splitTorus S X ⟶ G) (e : GlobalTheory.TorusPart.pullTorus h f = GlobalTheory.TorusPart.pullTorus h g) :
    (Over.pullback p).map f = (Over.pullback p).map g := by
  have k : GlobalTheory.SplitTorus.bcMap p X ≫ f.left = GlobalTheory.SplitTorus.bcMap p X ≫ g.left := by
    rw [← GlobalTheory.TorusPart.pullTorus_left h f, ← GlobalTheory.TorusPart.pullTorus_left h g, e]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k]
  · simp only [Over.pullback_map_left, pullback.lift_snd]

theorem spread₂_surjective : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → Function.Surjective ρ := by
  intro B H _ _ hH V₁ _ _ _ _ G₁ _ _ _ D₁ A₁ U₁ ξ₁ β₁ _ V₂ _ _ _ _ G₂ _ _ _ D₂ A₂ U₂ ξ₂ β₂ _ ρ hS
  obtain ⟨W, _, _, _, ψ, GW, _, _, φW, j, Ω, _, α, b₁, hb₁, GΩ, _, n, hn, n₁, hn₁, κ, _, c, b₂, hb₂, Gκ, _, m, hm,
    m₂, hm₂, hGW, hj, -, hc, -, -, -, -, hΩj, hκj⟩ := hS
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := GlobalTheory.TorusOnto.exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  haveI := hj
  let f : splitTorus (Sp W) F ⟶ GW := GlobalTheory.SplitTorus.torusMap (Sp W) l ≫ j
  have e0 : (1 : splitTorus (Sp W) F ⟶ GW) = GlobalTheory.SplitTorus.torusMap (Sp W) (0 : D₁.toPre.X →+ F) ≫ j := by
    rw [GlobalTheory.SplitTorus.torusMap_zero, MonObj.one_comp]

  have hκ : GlobalTheory.TorusPart.pullTorus hm f = GlobalTheory.TorusPart.pullTorus hm 1 := by
    rw [e0, GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hκj, ← Category.assoc,
      ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, hlρ,
      AddMonoidHom.zero_comp]
  letI : Algebra W κ := c.toAlgebra
  letI : Algebra (ResidueField W) κ := (ResidueField.lift c).toAlgebra
  haveI : IsScalarTower W (ResidueField W) κ :=
    IsScalarTower.of_algebraMap_eq' (ResidueField.lift_comp_residue c).symm
  have hbc : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange W κ).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange W κ).map 1 :=
    pullback_map_eq_of_pullTorus_eq hm f 1 hκ

  have hk := GlobalTheory.T.overSpecBaseChange_map_eq_of_fieldExtension W (ResidueField W) κ _ _ f 1 hbc
  have hsep : IsSeparated GW.hom :=
    (GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ ψ H GW φW hGW hH).separated
  have hf1 : f = 1 := GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow W F GW hsep f 1 (GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one W F GW f inferInstance hk)

  have hf0 : GlobalTheory.SplitTorus.torusMap (Sp W) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp W) 0 ≫ j := hf1.trans e0
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus hn) hf0
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩj] at e2
  haveI := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₁.gt 0) hb₁ hn₁).1
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.Poinc.Sep.Spz
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.SpreadTorSection

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  show Spec.map (𝟙 _) = _
  exact Spec.map_id _

theorem spMap_injective' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have := congrArg (fun u => (Spec.preimage u).hom) h
  simpa [spMap, Spec.preimage_map] using this

theorem range_sub {W κ : Type} [CommRing W] [IsLocalRing W] [Field κ] {B : Scheme.{0}} (ψ : Sp W ⟶ B)
    (Wo : B.Opens) (c : W →+* κ) [IsLocalHom c] (y : Sp κ ⟶ Wo.toScheme) (e : spMap c ≫ ψ = y ≫ Wo.ι) :
    Set.range ψ ⊆ Set.range Wo.ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨p, hp⟩ : ∃ p : Sp κ, (spMap c p : PrimeSpectrum W) = closedPoint W :=
    ⟨closedPoint κ, comap_closedPoint c⟩
  have hx : x ⤳ spMap c p := by
    have := specializes_closedPoint (R := W) x
    rw [← hp] at this
    exact this
  refine (hx.map ψ.continuous).mem_open Wo.isOpen ?_
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  have := Set.mem_range_self (f := Wo.ι) (y p)
  rwa [Scheme.Opens.range_ι] at this

def powChar {A X : Type} [CommRing A] [AddCommGroup X] (u : Aˣ) (c : X →+ ℤ) : Multiplicative X →* Aˣ :=
  (zpowersHom Aˣ u).comp (AddMonoidHom.toMultiplicative c)

theorem powChar_apply {A X : Type} [CommRing A] [AddCommGroup X] (u : Aˣ) (c : X →+ ℤ) (χ : Multiplicative X) :
    powChar u c χ = u ^ c (Multiplicative.toAdd χ) := rfl

theorem powChar_map {o A A' X : Type} [CommRing o] [CommRing A] [CommRing A'] [AddCommGroup X] (g : o →+* A)
    (f : A →+* A') (u : oˣ) (c : X →+ ℤ) (χ : Multiplicative X) :
    ((powChar (Units.map (f.comp g).toMonoidHom u) c χ : A'ˣ) : A') = f (powChar (Units.map g.toMonoidHom u) c χ) := by
  rw [powChar_apply, powChar_apply,
    show Units.map (f.comp g).toMonoidHom u = Units.map f.toMonoidHom (Units.map g.toMonoidHom u) from rfl,
    ← map_zpow]
  rfl

theorem powChar_val {o K X : Type} [CommRing o] [Field K] [AddCommGroup X] (g : o →+* K) (u : oˣ)
    (c : X →+ ℤ) (χ : Multiplicative X) :
    ((powChar (Units.map g.toMonoidHom u) c χ : Kˣ) : K) = g u ^ c (Multiplicative.toAdd χ) := by
  rw [powChar_apply, Units.val_zpow_eq_zpow_val]; rfl

theorem bc_point {W L X : Type} [CommRing W] [CommRing L] [AddCommGroup X] (f : W →+* L)
    {GW : Over (Sp W)} [GrpObj GW] {GLf : Over (Sp L)} [GrpObj GLf] {n : GLf.left ⟶ GW.left}
    (hn : IsGrpPullback GLf GW (spMap f) n) (j : splitTorus (Sp W) X ⟶ GW)
    (τW : Multiplicative X →* Wˣ) (τL : Multiplicative X →* Lˣ) (hτ : ∀ χ, (τL χ : L) = f (τW χ : W))
    (zW : Over.mk (spMap (RingHom.id W)) ⟶ splitTorus (Sp W) X)
    (hzW : ∀ χ, GlobalTheory.UU.chV zW χ = unitOn (τW (Multiplicative.ofAdd χ)))
    (zL : Over.mk (spMap (RingHom.id L)) ⟶ splitTorus (Sp L) X)
    (hzL : ∀ χ, GlobalTheory.UU.chV zL χ = unitOn (τL (Multiplicative.ofAdd χ))) :
    spMap f ≫ (zW ≫ j).left = (zL ≫ GlobalTheory.TorusPart.pullTorus hn j).left ≫ n := by
  have key : zL.left ≫ GlobalTheory.SplitTorus.bcMap (spMap f) X = spMap f ≫ zW.left := by
    refine GlobalTheory.UU.splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w zL, Category.assoc, Over.w zW]
      change spMap (RingHom.id L) ≫ spMap f = spMap f ≫ spMap (RingHom.id W)
      rw [spMap_id', spMap_id', Category.id_comp, Category.comp_id]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, GlobalTheory.UU.bcMap_charUnit,
        Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      have e1 := (GlobalTheory.UU.chV_val zL χ).symm.trans (congrArg Units.val (hzL χ))
      have e2 := (GlobalTheory.UU.chV_val zW χ).symm.trans (congrArg Units.val (hzW χ))
      exact e1.trans ((GlobalTheory.ToricOverField.unitOn_val_map f _ _ (hτ _)).trans (congrArg _ e2.symm))
  rw [Over.comp_left, Over.comp_left, Category.assoc, GlobalTheory.TorusPart.pullTorus_left,
    ← Category.assoc zL.left, key, Category.assoc]

theorem trait_section : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁] (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂] (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left) (ρ : D₂.toPre.X →+ D₁.toPre.X), Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (o : Type) [CommRing o] (s : B ⟶ Sp o) (o₁ : o →+* V₁) (o₂ : o →+* V₂), ξ₁ ≫ s = spMap o₁ → ξ₂ ≫ s = spMap o₂ → ∀ (k : ℕ) (ζ : o), 1 ≤ k → ζ ^ k = 1 → ∀ (Wo : B.Opens) (h : Wo.toScheme ⟶ H.left) (ξ₁' : Sp V₁ ⟶ Wo.toScheme) (ξ₂' : Sp V₂ ⟶ Wo.toScheme), h ≫ H.hom = Wo.ι → ξ₁' ≫ Wo.ι = ξ₁ → ξ₂' ≫ Wo.ι = ξ₂ → ∀ (c : D₁.toPre.X →+ ℤ), (∀ (κ : Type) [Field κ] (b : V₁ →+* κ) (hb : ∀ y ∈ maximalIdeal V₁ ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G₁.left) (hm : IsGrpPullback Gκ G₁ (spMap b) m) (τ : Multiplicative D₁.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b (o₁ ζ) ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D₁.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ ξ₁' ≫ h = (z ≫ GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb hm).left ≫ m ≫ β₁) → ∃ (κ : Type) (_ : Field κ) (b : V₂ →+* κ) (hb : ∀ y ∈ maximalIdeal V₂ ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) (_ : GrpObj Gκ) (m : Gκ.left ⟶ G₂.left) (hm : IsGrpPullback Gκ G₂ (spMap b) m) (τ : Multiplicative D₂.toPre.X →* κˣ) (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D₂.toPre.X), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b (o₂ ζ) ^ (c.comp ρ) χ) ∧ (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) ∧ spMap b ≫ ξ₂' ≫ h = (z ≫ GlobalTheory.TorusPart.gtTorus (U₂.gt 0) hb hm).left ≫ m ≫ β₂ := by
  intro B H _ _ hH V₁ _ _ _ G₁ _ _ D₁ A₁ U₁ ξ₁ β₁ V₂ _ _ _ G₂ _ _ D₂ A₂ U₂ ξ₂ β₂ ρ hS o _ s o₁ o₂ hs₁ hs₂ k ζ hk hζ
    Wo h ξ₁' ξ₂' hh hξ₁ hξ₂ c hyp
  obtain ⟨W, _, _, _, ψ, GW, _, _, φW, j, Ω, _, α, b₁, hb₁, GΩ, _, n, hn, n₁, hn₁, κ, _, c', b₂, hb₂, Gκ, _, m, hm,
    m₂, hm₂, hψ, _, hα, hc', hαψ, hc'ψ, hnφ, hmφ, hjn, hjm⟩ := hS
  haveI := hc'

  have hrange : Set.range ψ ⊆ Set.range Wo.ι :=
    range_sub ψ Wo c' (spMap b₂ ≫ ξ₂') (by rw [hc'ψ, Category.assoc, hξ₂])
  let ψ' := IsOpenImmersion.lift Wo.ι ψ hrange
  have hψ' : ψ' ≫ Wo.ι = ψ := IsOpenImmersion.lift_fac _ _ _
  have e₁ : spMap α ≫ ψ' = spMap b₁ ≫ ξ₁' := by
    rw [← cancel_mono Wo.ι, Category.assoc, hψ', hαψ, Category.assoc, hξ₁]
  have e₂ : spMap c' ≫ ψ' = spMap b₂ ≫ ξ₂' := by
    rw [← cancel_mono Wo.ι, Category.assoc, hψ', hc'ψ, Category.assoc, hξ₂]

  let oW : o →+* W := (Spec.preimage (ψ ≫ s)).hom
  have hoW : spMap oW = ψ ≫ s := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage (ψ ≫ s)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have ho₁ : α.comp oW = b₁.comp o₁ := spMap_injective' (by
    rw [spMap_comp', spMap_comp', hoW, ← Category.assoc, hαψ, Category.assoc, hs₁])
  have ho₂ : c'.comp oW = b₂.comp o₂ := spMap_injective' (by
    rw [spMap_comp', spMap_comp', hoW, ← Category.assoc, hc'ψ, Category.assoc, hs₂])

  have hζu : IsUnit ζ := IsUnit.of_pow_eq_one hζ (by omega)
  let u := hζu.unit
  have hu : (u : o) = ζ := hζu.unit_spec
  let τW := powChar (Units.map oW.toMonoidHom u) c
  obtain ⟨zW, hzW⟩ := GlobalTheory.ToricOverField.exists_point (RingHom.id W) τW
  let τΩ := powChar (Units.map (α.comp oW).toMonoidHom u) c
  obtain ⟨zΩ, hzΩ⟩ := GlobalTheory.ToricOverField.exists_point (RingHom.id Ω) τΩ
  have hτΩ : ∀ χ, (τΩ (Multiplicative.ofAdd χ) : Ω) = b₁ (o₁ ζ) ^ c χ := fun χ => by
    rw [powChar_val, ho₁, hu]; rfl
  have hyp₁ := hyp Ω b₁ hb₁ GΩ n₁ hn₁ τΩ hτΩ zΩ hzΩ
  have hbcΩ := bc_point α hn j τW τΩ (fun χ => powChar_map oW α u c χ) zW hzW zΩ hzΩ

  haveI : IsSeparated H.hom := hH.separated
  haveI : IsDominant (spMap α) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical α).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hα]; exact bot_le)⟩
  have hd : ψ' ≫ h = (zW ≫ j).left ≫ φW := by
    refine ext_of_isDominant_of_isSeparated H.hom ?_ (spMap α) ?_
    · simp only [Category.assoc]
      rw [hh, hψ', hψ.1.w, ← Category.assoc, Over.w (zW ≫ j)]
      change ψ = spMap (RingHom.id W) ≫ ψ
      rw [spMap_id', Category.id_comp]
    · rw [← Category.assoc, e₁, Category.assoc, hyp₁, ← hjn, ← hnφ, ← Category.assoc (spMap α), hbcΩ,
        Category.assoc]

  let τ₁ := powChar (Units.map (c'.comp oW).toMonoidHom u) c
  obtain ⟨zκ, hzκ⟩ := GlobalTheory.ToricOverField.exists_point (RingHom.id κ) τ₁
  have hbcκ := bc_point c' hm j τW τ₁ (fun χ => powChar_map oW c' u c χ) zW hzW zκ hzκ
  let τ₂ : Multiplicative D₂.toPre.X →* κˣ := powChar (Units.map (c'.comp oW).toMonoidHom u) (c.comp ρ)
  refine ⟨κ, inferInstance, b₂, hb₂, Gκ, inferInstance, m₂, hm₂, τ₂, zκ ≫ GlobalTheory.SplitTorus.torusMap _ ρ,
    fun χ => ?_, fun χ => ?_, ?_⟩
  · rw [powChar_val, ho₂, hu]; rfl
  · apply Units.ext
    rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
      GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
      ← GlobalTheory.UU.chV_val, hzκ]
    rfl
  · rw [← Category.assoc (spMap b₂), ← e₂, Category.assoc, hd, ← Category.assoc (spMap c'), hbcκ,
      Category.assoc zκ, ← hjm, ← hmφ]
    simp only [Category.assoc]

end GlobalTheory.SpreadTorSection
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisedGroup_endomorphism_unique_of_thickening_action : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre b h g → ActsAs U.toUnifPre b h g' → g = g' := by
  first | exact @GlobalTheory.Mum.actsAs_unique | exact GlobalTheory.Mum.actsAs_unique | (intros; apply GlobalTheory.Mum.actsAs_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_even_cubic_integral_reading_of_trivialisations : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ κ : D.toPre.X → (FractionRing R)ˣ, GlobalTheory.ThFam.Reads D.toPre κ ∧ (∀ a, ∃ u : Rˣ, ((κ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ a : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a a' b, ∃ u : Rˣ, ((κ (a + a' + b) * κ a * κ a' * κ b : (FractionRing R)ˣ) : FractionRing R) = ((κ (a + a') * κ (a + b) * κ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R (FractionRing R) s) ∧ ∀ n : ℕ, {a | ¬ ∃ s ∈ maximalIdeal R ^ n, (κ a : FractionRing R) = algebraMap R (FractionRing R) s}.Finite := by
  first | exact @GlobalTheory.ThFamRead.exists_reading | exact GlobalTheory.ThFamRead.exists_reading | (intros; apply GlobalTheory.ThFamRead.exists_reading <;> assumption)
end
