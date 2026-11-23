module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle676
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle500
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle553
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle141
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle175
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle202
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle154
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle062
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle097
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle100
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle068
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle750
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.PUnit
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullUnif

theorem coordMap_of_isPullDeg {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V]
    [IsLocalRing V] {g : R →+* V} {D : DegPre R} {D' : DegPre V} (hD : IsPullDeg g D D') :
    CoordMap D D' g hD.xe.symm.toAddMonoidHom := by
  intro y r r' hr hr'
  have hr2 : PsiCoord D (hD.xe (hD.xe.symm y)) r := by rwa [AddEquiv.apply_symm_apply]
  obtain ⟨u, hu⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD (hD.xe.symm y) r hr2
  have h1 : Associated (u * g r) r' := GlobalTheory.TorRef.psiCoord_associated hu hr'
  exact Associated.trans ⟨u, mul_comm _ _⟩ h1



theorem gtTorus_pull {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
    {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']
    {U : Unif (maximalIdeal R) D A G} {U' : Unif (maximalIdeal V) D' A' G'} {g : R →+* V}
    {bc : G' ≅ (Over.pullback (specOf g)).obj G} {hD : IsPullDeg g D.toPre D'.toPre}
    (H : IsPullUnif g hD bc U U')
    {κ : Type} [Field κ] {b : V →+* κ} (hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0)
    (hb' : ∀ x ∈ maximalIdeal R ^ (0 + 1), (b.comp g) x = 0)
    {G₀ : Over (Sp κ)} [GrpObj G₀] {φ' : G₀.left ⟶ G'.left}
    (hp' : IsGrpPullback G₀ G' (spMap b) φ')
    (hp : IsGrpPullback G₀ G (spMap (b.comp g)) (φ' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g))) :
    GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hp' =
      GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb' hp := by
  obtain ⟨wL, -, he, -, Hs⟩ := (isPullUnif_iff_stalks R V _ _ g D D' hD A A' G G' bc U U').1 H
  obtain ⟨h, hf, ⟨hpG, hψ⟩, -⟩ := Hs 0
  obtain ⟨s, τ, hτ⟩ := GlobalTheory.PullLinear.exists_point (U.gt 0) (U'.gt 0) hpG (hψ 0).1 (𝟙 _)
  have : IsClosedImmersion (thick R (maximalIdeal R) 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have C1 : GlobalTheory.TorusPart.thickLift hb' hp = GlobalTheory.TorusPart.thickLift hb hp' ≫ h := by
    rw [← cancel_mono (pullback.fst G.hom (thick R (maximalIdeal R) 0)), GlobalTheory.TorusPart.thickLift_fst,
      Category.assoc]
    erw [hf]
    erw [← Category.assoc (GlobalTheory.TorusPart.thickLift hb hp'), GlobalTheory.TorusPart.thickLift_fst hb hp']
  have hτ' : (U'.gt 0).i.left ≫ h = τ.left ≫ (U.gt 0).i.left := by
    rw [← Over.comp_left, hτ, Category.id_comp]
  have key : GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb) D'.toPre.X ≫ τ.left =
      (GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom).left ≫
        GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb') D.toPre.X := by
    have wA : (GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb) D'.toPre.X ≫ τ.left) ≫
        (splitTorus (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) D.toPre.X).hom =
        (splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb' := by
      rw [Category.assoc, ← Over.w (U.gt 0).i, ← Category.assoc τ.left, ← hτ', Category.assoc,
        ← Category.assoc _ (U'.gt 0).i.left]
      erw [← GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb hp') (U'.gt 0).i]
      rw [Category.assoc, ← Category.assoc _ h, ← C1, (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp).1.w,
        ← Category.assoc, Over.w]
    have wB : ((GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom).left ≫
        GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb') D.toPre.X) ≫
        (splitTorus (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) D.toPre.X).hom =
        (splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb' := by
      rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w]
    have hchar : ∀ x' : D'.toPre.X, τ.left.appTop.hom (Rosenlicht.chi D.toPre.X (hD.xe x')) =
        Rosenlicht.chi D'.toPre.X x' := by
      intro x'
      apply TopCat.Presheaf.section_ext (splitTorus _ D'.toPre.X).left.sheaf ⊤
      intro z hz
      have e := congrArg Units.val
        (GlobalTheory.PullLinear.char_eq (U.gt 0) (U'.gt 0) hD.w (hψ x').1 (hψ x').2 (𝟙 _) τ hτ z)
      rw [gm_val τ.left z ⊤ trivial, gm_val (Over.Hom.left (𝟙 (WeightPf.Te D'.toPre (maximalIdeal V) 0))) z ⊤ trivial, GlobalTheory.SplitTorus.charUnit_val,
        GlobalTheory.SplitTorus.charUnit_val] at e
      exact e
    have e := GlobalTheory.SplitTorus.hom_ext (T := Over.mk ((splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb'))
      (g := Over.homMk _ wA) (g' := Over.homMk _ wB) (fun a => by
        rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq]
        simp only [Over.homMk_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
        rw [GlobalTheory.SplitTorus.bcMap_appTop_chi, GlobalTheory.SplitTorus.torusMap_appTop_chi,
          ← AddEquiv.apply_symm_apply hD.xe a, hchar, GlobalTheory.SplitTorus.bcMap_appTop_chi,
          AddEquiv.apply_symm_apply]
        rfl)
    exact congrArg (·.left) e
  apply GlobalTheory.TorusPart.hom_ext_of_pullback (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp)
  rw [Over.comp_left, Category.assoc]
  erw [GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp) (U.gt 0).i]
  rw [C1, ← Category.assoc]
  erw [GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb hp') (U'.gt 0).i]
  rw [Category.assoc, hτ', ← Category.assoc, key, Category.assoc]



theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsLocalHom g → ∀ (bc : G' ≅ (Over.pullback (specOf g)).obj G), IsMonHom bc.hom → β = bc.hom.left ≫ pullback.fst G.hom (specOf g) → ∀ hD : IsPullDeg g D.toPre D'.toPre, IsPullUnif g hD bc U U' → LBIso U'.LG.L (U.LG.L.pull β) ∧ CoordMap D.toPre D'.toPre g hD.xe.symm.toAddMonoidHom ∧ EquivMap U U' β hD.xe.symm.toAddMonoidHom := by
  intro R _ _ _ _ G _ _ _ D A U V _ _ _ _ G' _ _ _ D' A' U' g β hloc bc hbc hβ hD H
  subst hβ
  refine ⟨?_, coordMap_of_isPullDeg hD, ?_⟩
  · obtain ⟨wL, hwL, -⟩ := H.lg
    exact ⟨wL, hwL⟩
  intro f f' _ _ hcomm m m' hm hm' y
  have hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), residue V x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hb' : ∀ x ∈ maximalIdeal R ^ (0 + 1), ((residue V).comp g) x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 ((map_mem_nonunits_iff g x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx))
  have hp' := isGrpPullback_pullback G' (spMap (residue V))
  have hβ : IsGrpPullback G' G (spMap g) (bc.hom.left ≫ pullback.fst G.hom (specOf g)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf g))).congr (Category.id_comp _) rfl
  have hp : IsGrpPullback ((Over.pullback (spMap (residue V))).obj G') G (spMap ((residue V).comp g))
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) :=
    (hp'.comp hβ).congr (Spec.map_comp (CommRingCat.ofHom g) (CommRingCat.ofHom (residue V))).symm rfl
  have e' : ((Over.pullback (spMap (residue V))).map f').left ≫ pullback.fst G'.hom (spMap (residue V)) =
      pullback.fst G'.hom (spMap (residue V)) ≫ f'.left := pullback.lift_fst _ _ _
  have e : ((Over.pullback (spMap (residue V))).map f').left ≫
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) =
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) ≫ f.left := by
    rw [← Category.assoc, e', Category.assoc, hcomm]
    simp only [Category.assoc]
  have k' := hm' _ _ hb _ _ hp' _ e'
  have k := hm _ _ hb' _ _ hp _ e
  have K := gtTorus_pull H hb hb' hp' hp
  have hmono := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hb' hp).1
  have k2 := (Category.assoc _ _ _).trans ((congrArg (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V))
    hD.xe.symm.toAddMonoidHom ≫ ·) k.symm).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (Over.pullback (spMap (residue V))).map f') K.symm).trans (k'.trans
    ((congrArg (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V)) m' ≫ ·) K).trans (Category.assoc _ _ _).symm)))))
  have k3 := (cancel_mono _).1 k2
  rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp] at k3
  exact congrArg (fun φ : D.toPre.X →+ D'.toPre.X => φ y) (GlobalTheory.SplitTorus.torusMap_injective k3)

end GlobalTheory.Poinc.Eq8.PullUnif
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnifProperOpen

theorem isProper_of_polGeneric_of_abLocus : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.UU.CDVR V →
    ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ φ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) φ → (∀ x, x ∈ abLocus G) → IsProper G.hom := by
  intro V _ _ _ hV A G _ _ hG φ hφ hab
  haveI := hV.1
  haveI := hV.2.2
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hφ
  obtain ⟨L, hL⟩ := GlobalTheory.UU.polarisation_extends l₁ V A G hG e he
  obtain ⟨P, rfl⟩ := GlobalTheory.CubicalPackage.exists_package l₁ V hV A G hG e he L hL
  obtain ⟨w, hw⟩ := hL
  have hmax : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (V ⧸ maximalIdeal V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (V ⧸ maximalIdeal V ^ (0 + 1)))
  have h0 : IsAbelianScheme (thickObj V (maximalIdeal V) 0 G) := by
    have h₂ := IsSemiAbelian.pullback (thick V (maximalIdeal V) 0) G hG
    letI := hF.toField
    exact ⟨h₂.comm, h₂.smooth, GlobalTheory.ArcNotAbelian.isProper_fibre G hG _ _ p (hab _), h₂.geomConnected⟩
  obtain ⟨P₀, h₀⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal V) 0 P
  let s : GlobalTheory.UU.HidaSetting V A G := ⟨hV, hG, e, he, P, w, hw, PUnit, GlobalTheory.UU.TQ.abelian _ h0 PUnit, P₀, h₀,
    GlobalTheory.UU.SettingConsistentExample.ab_even h0 PUnit P₀⟩
  obtain ⟨D, U, -, -, -⟩ := GlobalTheory.uniformisation_dvr_unconditional V A G s
  let g := U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mem_abLocus G hG _ hF (thick V (maximalIdeal V) 0) p (hab _)
    D.toPre.X g.i g.i_hom
  exact (GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ V hV.2.1 D A G hG U hs).proper

theorem exists_polGeneric_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
    (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V),
    Function.Injective φ → ∃ (A' : PolAV (Sp (FractionRing V))) (ψ : A'.A.left ⟶ ((Over.pullback (spMap φ)).obj G).left),
    IsGrpPullback A'.A ((Over.pullback (spMap φ)).obj G) (jK V) ψ := by
  intro R _ _ A G _ gen hgen V _ _ φ hφ
  have hinj' : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V (FractionRing V)).comp hφ
  let ψ : FractionRing R →+* FractionRing V := IsFractionRing.lift hinj'
  have hg : spMap ψ ≫ jK R = jK V ≫ spMap φ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [ψ, IsFractionRing.lift_algebraMap]
  obtain ⟨A', eA, heA, -⟩ := GlobalTheory.GoodReductionUnif.exists_baseChange GlobalTheory.polBaseChange_holds (spMap ψ) A
  have h₁ := GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (spMap ψ) A.A eA heA
  have h₂ := GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK R) G gen hgen
  have h₃ := h₁.comp h₂
  refine ⟨A', pullback.lift ((eA.inv.left ≫ pullback.fst A.A.hom (spMap ψ)) ≫ gen.inv.left ≫
    pullback.fst G.hom (jK R)) (A'.A.hom ≫ jK V) (by rw [h₃.1.w, hg, Category.assoc]), ?_⟩
  exact (isGrpPullback_pullback G (spMap φ)).cancel (h₃.congr hg (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)

theorem range_spMap_away (R : Type) [CommRing R] (f : R) :
    Set.range (spMap (algebraMap R (Localization.Away f))) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  have e : ⇑(spMap (algebraMap R (Localization.Away f))) = PrimeSpectrum.comap (algebraMap R (Localization.Away f)) := by
    ext x : 1
    simp [spMap, Spec.map_base]
    rfl
  rw [e]
  exact PrimeSpectrum.localization_away_comap_range _ f

theorem isProper_away (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R]
    (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (gen : (Over.pullback (jK R)).obj G ≅ A.A) (hgen : IsMonHom gen.hom) (f : R) (hf : f ≠ 0)
    (hab : ∀ z ∈ Set.range (spMap (algebraMap R (Localization.Away f))), z ∈ abLocus G) :
    IsProper (pullback.snd G.hom (spMap (algebraMap R (Localization.Away f)))) := by
  haveI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  haveI : IsNoetherianRing (Localization.Away f) := IsLocalization.isNoetherianRing (Submonoid.powers f) _ inferInstance
  set j := spMap (algebraMap R (Localization.Away f)) with hj
  let Gf := (Over.pullback j).obj G
  haveI hGf : IsSemiAbelian Gf := IsSemiAbelian.pullback j G hG
  haveI := hGf.separated
  haveI := hGf.quasiCompact
  haveI := hGf.smooth
  haveI : IsIntegral Gf.left := GlobalTheory.isIntegral_left_of_isSemiAbelian Gf
  change IsProper Gf.hom
  refine GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint (Localization.Away f) Gf.left Gf.hom ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  obtain ⟨φ, hφ⟩ : ∃ φ : R →+* V, spMap φ = y ≫ j := ⟨(Spec.preimage (y ≫ j)).hom, by simp [spMap]⟩
  let p₀ : Sp K := (⊥ : PrimeSpectrum K)
  have h₁ : x p₀ = genericPoint Gf.left := hx ⟨p₀, rfl⟩
  have h₂ : (x ≫ Gf.hom ≫ j) p₀ = (⊥ : PrimeSpectrum R) := by
    rw [Scheme.Hom.comp_apply, h₁, GlobalTheory.ProperOfAbelianFibres.apply_genericPoint_of_flat]
    exact genericPoint_eq_bot_of_affine (CommRingCat.of R)
  rw [← Category.assoc, hxy, Category.assoc, ← hφ] at h₂
  have h₃ : Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) = ⊥ := congrArg PrimeSpectrum.asIdeal h₂
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) := by simp [ha]
    rw [h₃] at this
    simpa using this
  haveI : CharZero V := charZero_of_injective_ringHom hinj
  let GV := (Over.pullback (spMap φ)).obj G
  have hGV : IsSemiAbelian GV := IsSemiAbelian.pullback (spMap φ) G hG
  have habV : ∀ z, z ∈ abLocus GV := fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom (spMap φ)) z).1
      (hab _ ⟨y z, by rw [hφ, Scheme.Hom.comp_apply]⟩)
  obtain ⟨A', ψ, hψ⟩ := exists_polGeneric_pullback R A G gen hgen V φ hinj
  have hpV : IsProper GV.hom := isProper_of_polGeneric_of_abLocus V ⟨inferInstance, inferInstance, inferInstance⟩ A' GV hGV ψ hψ habV
  let xV : Sp K ⟶ GV.left := pullback.lift (x ≫ pullback.fst G.hom j) (spMap (algebraMap V K)) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [hxy]
    rw [Category.assoc, hφ])
  have hE : ValuativeCriterion.Existence GV.hom := by
    have h : UniversallyClosed GV.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq GV.hom :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨(pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  have e₁ : spMap (algebraMap V K) ≫ l.l = xV := l.fac_left
  have e₂ : l.l ≫ GV.hom = 𝟙 _ := l.fac_right
  refine ⟨pullback.lift (l.l ≫ pullback.fst G.hom (spMap φ)) y ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [e₂]
    rw [Category.id_comp, hφ]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, e₁]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, pullback.lift_snd]
      exact hxy.symm

theorem isProper_restrict : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (W : Set (Sp R)) ⊆ abLocus G →
    IsProper (G.hom ∣_ W) := by
  intro R _ _ _ hR D A G _ _ hG U W hW
  obtain ⟨⟨hN, -, -, -⟩, hc⟩ := hR
  haveI := hN
  haveI := hc
  let I := {f : R // f ≠ 0 ∧ ∀ z ∈ Set.range (spMap (algebraMap R (Localization.Away f))), z ∈ W}
  refine GlobalTheory.AbLocusLocal.isProper_restrict_of_cover G.hom (I := I)
    (fun i => spMap (algebraMap R (Localization.Away i.1))) (fun i => pullback.snd G.hom _)
    (fun i => pullback.fst G.hom _) (fun i => IsPullback.of_hasPullback _ _) (fun _ => ⊤) (fun i => ?_) W
    (fun i => ?_) (fun z hz => ?_)
  · exact IsZariskiLocalAtTarget.restrict
      (isProper_away R A G hG U.gen U.gen_hom i.1 i.2.1 fun z hz => hW (i.2.2 z hz)) ⊤
  · rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact i.2.2 _ ⟨_, rfl⟩
  · obtain ⟨_, ⟨f, rfl⟩, hzf, hfW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz W.isOpen
    have hr := range_spMap_away R f
    have hzf' : z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := hzf
    have hfW' : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ (W : Set (Sp R)) := hfW
    have hf : f ≠ 0 := by
      rintro rfl
      exact hzf' (zero_mem _)
    refine ⟨⟨f, hf, fun z' hz' => hfW' (by rw [hr] at hz'; exact hz')⟩, ?_⟩
    obtain ⟨a, ha⟩ : z ∈ Set.range (spMap (algebraMap R (Localization.Away f))) := by rw [hr]; exact hzf'
    exact ⟨⟨a, trivial⟩, ha⟩

end GlobalTheory.UnifProperOpen
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitSetting

open GlobalTheory.UU GlobalTheory.LN



theorem exists_setting_of_evenOn (laws : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G) (hE : EvenOn P)
    (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (φ : R →+* V) (hφ : Function.Injective φ)
    (hI : maximalIdeal R ≤ (maximalIdeal V).comap φ) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap φ)).obj G)) (w : _),
      IsCPMap s.P P (spMap φ) (pullback.fst G.hom (spMap φ)) pullback.condition w := by
  obtain ⟨X, _, _, _, Q₀, P₀, hlev, hev⟩ := hE
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback _ G hS
  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  rw [← hP'] at hA'
  obtain ⟨P₀', w₀, H₀⟩ := exists_isLevelCP (maximalIdeal V) 0 P'
  have le : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal V ^ (0 + 1)).comap φ := by
    rw [zero_add, pow_one, pow_one]; exact hI
  let b : R ⧸ maximalIdeal R ^ (0 + 1) →+* V ⧸ maximalIdeal V ^ (0 + 1) := Ideal.quotientMap _ φ le
  have sq : spMap b ≫ thick R (maximalIdeal R) 0 = thick V (maximalIdeal V) 0 ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  obtain ⟨wl, hl⟩ := hlev
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G)
    (H := thickObj R (maximalIdeal R) 0 G)
    (H' := thickObj V (maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := P₀) (N' := P₀') sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R (maximalIdeal R) 0))
    (isGrpPullback_pullback _ (thick V (maximalIdeal V) 0)) H hl H₀
  have := hS.smooth
  have := hS.geomConnected
  have : Smooth (thickObj R (maximalIdeal R) 0 G).hom := by
    show Smooth (pullback.snd _ _); infer_instance
  have : GeometricallyConnected (thickObj R (maximalIdeal R) 0 G).hom := by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ hev
  obtain ⟨Q₀', D₀', -, -, -⟩ := ClosedPol.exists_desc_pull pF Q₀ D₀ k₃
  have ev := UniformizationSetting.exists_even_of_desc D₀'
  obtain ⟨wA, hwA⟩ := hA'
  exact ⟨A', ⟨hV, hG', gen', hgen', P', wA, hwA, _, Q₀', P₀', ⟨w₀, H₀⟩, ev⟩, wP, H⟩

end GlobalTheory.Mum.TraitSetting
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem genericEnd_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ f : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom f → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = f := by
  intro R _ _ _ hR G _ _ hG f hf
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hR
  haveI := hN
  haveI := hIC
  haveI := hf
  obtain ⟨g, ⟨hg, hg'⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds R
    (FractionRing R) G G hG hG f
  exact ⟨g, hg, hg'⟩

end GlobalTheory.Mum
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_modif_graph : ∀ (R : Type) [CommRing R] [IsDomain R] (o : Type) [CommRing o] (b : o →+* R) (Z : Scheme.{0}) (s : Z ⟶ Sp o), IsProper s → ∀ y : Sp (FractionRing R) ⟶ Z, y ≫ s = jK R ≫ spMap b → ∃ (M : Modif R) (h : M.S ⟶ Z), M.gp ≫ h = y ∧ h ≫ s = M.π ≫ spMap b := by
  intro R _ _ o _ b Z s hs y hy
  let ℓ : Sp (FractionRing R) ⟶ pullback s (spMap b) := pullback.lift y (jK R) hy
  have : QuasiCompact ℓ := inferInstance
  have : IsProper (pullback.snd s (spMap b)) := inferInstance
  refine ⟨{ S := ℓ.image
            π := ℓ.imageι ≫ pullback.snd s (spMap b)
            proper := inferInstance
            integral := isIntegral_image_of_field ℓ
            gp := ℓ.toImage
            gp_π := by rw [ℓ.toImage_imageι_assoc, pullback.lift_snd]
            dominant := inferInstance }, ℓ.imageι ≫ pullback.fst s (spMap b), ?_, ?_⟩
  · show ℓ.toImage ≫ ℓ.imageι ≫ pullback.fst s (spMap b) = y
    rw [ℓ.toImage_imageι_assoc, pullback.lift_fst]
  · show (ℓ.imageι ≫ pullback.fst s (spMap b)) ≫ s = (ℓ.imageι ≫ pullback.snd s (spMap b)) ≫ spMap b
    rw [Category.assoc, Category.assoc, pullback.condition]

end GlobalTheory.Mum
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_modification_closure_of_graph : ∀ (R : Type) [CommRing R] [IsDomain R] (o : Type) [CommRing o] (b : o →+* R) (Z : Scheme.{0}) (s : Z ⟶ Sp o), IsProper s → ∀ y : Sp (FractionRing R) ⟶ Z, y ≫ s = jK R ≫ spMap b → ∃ (M : Modif R) (h : M.S ⟶ Z), M.gp ≫ h = y ∧ h ≫ s = M.π ≫ spMap b := by
  first | exact @GlobalTheory.Mum.exists_modif_graph | exact GlobalTheory.Mum.exists_modif_graph | (intros; apply GlobalTheory.Mum.exists_modif_graph <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isProper_uniformisedSemiAbelian_over_open_in_abLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (W : Set (Sp R)) ⊆ abLocus G → IsProper (G.hom ∣_ W) := by
  first | exact @GlobalTheory.UnifProperOpen.isProper_restrict | exact GlobalTheory.UnifProperOpen.isProper_restrict | (intros; apply GlobalTheory.UnifProperOpen.isProper_restrict <;> assumption)

end
end
