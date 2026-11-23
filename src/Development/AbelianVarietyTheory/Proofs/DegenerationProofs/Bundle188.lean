module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HenselianIUnionCompleteOfIntegralOverCompleteDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle187
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.Isog

open IsLocalRing

theorem spMap_comp {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := GlobalTheory.ModelDescent.spMap_comp_eq rfl

theorem isModel_pullback {K W L W' L' : Type} [Field K] [CommRing W] [Field L] [CommRing W'] [Field L']
    [Algebra K L] [Algebra W L] [Algebra K L'] [Algebra W' L'] (c : W →+* W') (b : L →+* L')
    (e : (algebraMap W' L').comp c = b.comp (algebraMap W L)) (e' : b.comp (algebraMap K L) = algebraMap K L')
    (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (h : IsModel (L := L) A G) :
    IsModel (L := L') A ((Over.pullback (spMap c)).obj G) := by
  obtain ⟨e₀, he₀⟩ := h
  have hW : spMap (algebraMap W' L') ≫ spMap c = spMap b ≫ spMap (algebraMap W L) := by
    rw [spMap_comp, spMap_comp, e]
  have hK : spMap (algebraMap K L') = spMap b ≫ spMap (algebraMap K L) := by
    rw [spMap_comp, e']
  have key : ∀ (φ : Sp L' ⟶ Sp W) (ψ : Sp L' ⟶ Sp K), φ = spMap b ≫ spMap (algebraMap W L) →
      ψ = spMap b ≫ spMap (algebraMap K L) →
      ∃ f : (Over.pullback φ).obj G ≅ (Over.pullback ψ).obj A, IsMonHom f.hom := by
    rintro φ ψ rfl rfl
    refine ⟨pullCompIso _ _ G ≪≫ (Over.pullback (spMap b)).mapIso e₀ ≪≫ (pullCompIso _ _ A).symm, ?_⟩
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    infer_instance
  obtain ⟨f, hf⟩ := key _ _ hW hK
  show ∃ e : _ ≅ _, IsMonHom e.hom
  refine ⟨(pullCompIso _ _ G).symm ≪≫ f, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

theorem pullback_map_id_pow {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B] (m : ℕ) :
    (Over.pullback f).map (𝟙 B ^ m) = 𝟙 ((Over.pullback f).obj B) ^ m := by
  simpa using map_pow ((Over.pullback f).homMonoidHom) (𝟙 B) m

theorem exists_model_of_isogeny (K R K' : Type) [Field K] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K']
    [Algebra R K'] [Algebra K K'] (hSH : SH R K') (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g m : ℕ)
    (hA : IsAbelianScheme A) (hP : GlobalTheory.AbLaw.IsProjBy A.hom) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (i : A ⟶ B) (r : B ⟶ A) [IsMonHom i] [IsMonHom r] (hm : 1 ≤ m)
    (hri : r ≫ i = 𝟙 _ ^ m) (G' : Over (Sp R)) [GrpObj G'] (hG' : IsSemiAbelian G') (hmod : IsModel (L := K') B G') :
    ∃ (G : Over (Sp R)) (_ : GrpObj G), SmConn G ∧ IsModel (L := K') A G ∧
      Nonempty (TorusExtension (spFibre G)) := by
  obtain ⟨e, he⟩ := hmod
  haveI := he
  have hbc : ∀ (X : Over (Sp K)), SmoothOfRelativeDimension g X.hom →
      SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj X).hom := fun X hX =>
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback X.hom (spMap (algebraMap K K'))) hX
  have hA' : IsAbelianScheme ((Over.pullback (spMap (algebraMap K K'))).obj A) := by
    obtain ⟨h1, h2, h3, h4⟩ := hA
    exact ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd A.hom (spMap (algebraMap K K')))),
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))) h3,
      inferInstanceAs (GeometricallyConnected (pullback.snd A.hom (spMap (algebraMap K K'))))⟩
  have hP' : GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K K'))).obj A).hom :=
    GlobalTheory.AbLaw.isProjBy_baseChange K K' (algebraMap K K') A.left _ A.hom _ _
      (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))) hP
  have hgA' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj A).hom := hbc A hgA
  haveI hgB' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj B).hom := hbc B hgB
  have hgG : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K'))).obj G').hom := by
    haveI : IsIso e.hom.left := ⟨e.inv.left, by simp [← Over.comp_left], by simp [← Over.comp_left]⟩
    have h : SmoothOfRelativeDimension (0 + g) (e.hom.left ≫ ((Over.pullback (spMap (algebraMap K K'))).obj B).hom) := inferInstance
    rw [zero_add, Over.w e.hom] at h
    exact h
  have hri' : (e.hom ≫ (Over.pullback (spMap (algebraMap K K'))).map r) ≫ ((Over.pullback (spMap (algebraMap K K'))).map i ≫ e.inv) = 𝟙 _ ^ m := by
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hri, pullback_map_id_pow, MonObj.pow_comp, MonObj.comp_pow]
    simp
  obtain ⟨G, _, e₂, hsc, he₂, ht⟩ := GlobalTheory.T.semiAbelian_reduction_along_isogeny_strict_henselian R K' hSH ((Over.pullback (spMap (algebraMap K K'))).obj A) G' g m hA' hP' hG' hgA' hgG
    ((Over.pullback (spMap (algebraMap K K'))).map i ≫ e.inv) (e.hom ≫ (Over.pullback (spMap (algebraMap K K'))).map r) inferInstance inferInstance hm hri'
  exact ⟨G, inferInstance, hsc, show ∃ _, _ from ⟨e₂, he₂⟩, ht⟩

end GlobalTheory.SS.Isog

namespace GlobalTheory.SS


open Isog IsLocalRing in
theorem potModel_semiAbelian_of_isogeny : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g m : ℕ), IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (i : A ⟶ B) (r : B ⟶ A), IsMonHom i → IsMonHom r → 1 ≤ m → r ≫ i = 𝟙 _ ^ m → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ A B _ _ g m hA hP hgA hgB i r hi hr hm hri hB
  haveI := hi
  haveI := hr
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hc, hfin, hloc, hcomp, G, _, hmod, hG⟩ := hB
  have hG' : IsSemiAbelian G := hG
  haveI : IsAdicComplete (maximalIdeal W) W := hcomp
  haveI : CharZero L := (RingHom.charZero_iff (algebraMap K L).injective).1 inferInstance
  haveI : CharZero W := (RingHom.charZero_iff (IsFractionRing.injective W L)).2 inferInstance
  haveI : CharZero V := (RingHom.charZero_iff (IsFractionRing.injective V K)).2 inferInstance
  obtain ⟨R, _, _, _, _, hinj, hint, hac⟩ := GlobalTheory.T.exists_integral_ext_isAlgClosed_residueField' W
  obtain ⟨-, hhen, -⟩ := GlobalTheory.T.henselian_iUnion_complete_of_integral_over_complete_dvr W R hinj hint
  have hWK : Function.Injective ((algebraMap R (FractionRing R)).comp (algebraMap W R)) :=
    (IsFractionRing.injective R (FractionRing R)).comp hinj
  obtain ⟨b, hbW⟩ : ∃ b : L →+* FractionRing R,
      (algebraMap R (FractionRing R)).comp (algebraMap W R) = b.comp (algebraMap W L) :=
    ⟨IsFractionRing.lift hWK, RingHom.ext fun x => (IsFractionRing.lift_algebraMap (K := L) hWK x).symm⟩
  letI : Algebra K (FractionRing R) := (b.comp (algebraMap K L)).toAlgebra
  have hSH : SH R (FractionRing R) := by
    show _ ∧ _ ∧ _ ∧ _
    exact ⟨inferInstance, hhen, hac, inferInstance⟩
  have hmodR : IsModel (L := FractionRing R) B ((Over.pullback (spMap (algebraMap W R))).obj G) :=
    isModel_pullback (algebraMap W R) b hbW rfl B G hmod
  have hsemiR : IsSemiAbelian ((Over.pullback (spMap (algebraMap W R))).obj G) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (spMap (algebraMap W R)) G hG'
  obtain ⟨GR, _, hsc, hmodA, ht⟩ := exists_model_of_isogeny K R (FractionRing R) hSH A B g m hA hP hgA hgB
    i r hm hri _ hsemiR hmodR
  letI : Algebra V R := ((algebraMap W R).comp (algebraMap V W)).toAlgebra
  have hVR : (algebraMap R (FractionRing R)).comp (algebraMap V R) =
      (algebraMap K (FractionRing R)).comp (algebraMap V K) := by
    change (algebraMap R (FractionRing R)).comp ((algebraMap W R).comp (algebraMap V W)) =
      (b.comp (algebraMap K L)).comp (algebraMap V K)
    rw [← RingHom.comp_assoc, hbW, RingHom.comp_assoc, hc, RingHom.comp_assoc]
  obtain ⟨s, hs⟩ := GlobalTheory.smConn_model_descends V K R (FractionRing R) hVR A hA GR hsc hmodA
  have hVW : Function.Injective (algebraMap V W) := by
    have h2 : Function.Injective ((algebraMap K L).comp (algebraMap V K)) :=
      (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    rw [← hc, RingHom.coe_comp] at h2
    exact h2.of_comp
  haveI : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have hVRi : (algebraMap V R).IsIntegral :=
    RingHom.IsIntegral.trans (f := algebraMap V W) (g := algebraMap W R)
      (fun x => Algebra.IsIntegral.isIntegral (R := V) x) (fun x => hint.isIntegral x)
  have hVRinj : Function.Injective (algebraMap V R) := hinj.comp hVW
  obtain ⟨hlocVR, -, hdescV⟩ := GlobalTheory.T.henselian_iUnion_complete_of_integral_over_complete_dvr V R hVRinj ⟨fun x => hVRi x⟩
  obtain ⟨W', hDVRW, hsW, hcW, hfW, hlW⟩ := hdescV s
  haveI : IsDiscreteValuationRing W' := hDVRW
  haveI : IsLocalRing W' := hDVRW.toIsLocalRing
  obtain ⟨GW, _, _, ε, hscW, hε, hcompW, hmodW⟩ := hs W' inferInstance hsW hlW
  haveI := hε
  have hlVW : IsLocalHom (algebraMap V W') := by
    refine ⟨fun x hx => ?_⟩
    have h1 : IsUnit (W'.val.toRingHom (algebraMap V W' x)) := hx.map _
    exact IsLocalHom.map_nonunit (f := algebraMap V R) x h1
  let ρ : W' →+* ResidueField R := (residue R).comp W'.val.toRingHom
  have hker : RingHom.ker ρ = IsLocalRing.maximalIdeal W' := by
    rw [← RingHom.comap_ker, IsLocalRing.ker_residue, IsLocalRing.maximalIdeal_comap]
  have hρi : ρ.IsIntegral :=
    RingHom.IsIntegral.trans (f := W'.val.toRingHom) (g := residue R)
      (RingHom.IsIntegral.tower_top (f := algebraMap V W') (g := W'.val.toRingHom) hVRi)
      (RingHom.isIntegral_of_surjective _ residue_surjective)
  have htor : Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj GW)) := by
    obtain ⟨T⟩ := ht
    have hρ : spMap ρ = spMap (residue R) ≫ spMap W'.val.toRingHom := (Isog.spMap_comp _ _).symm
    rw [hρ]
    let Z := pullCompIso (spMap (residue R)) (spMap W'.val.toRingHom) GW ≪≫ (Over.pullback _).mapIso ε
    haveI : IsMonHom Z.symm.hom := by
      dsimp only [Z, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv]
      infer_instance
    exact ⟨torusExtOfIso Z.symm T⟩
  have hprop : IsProper ((Over.pullback (spMap (algebraMap W' (FractionRing W')))).obj GW).hom := by
    obtain ⟨e, -⟩ := hmodW
    haveI : IsProper A.hom := hA.proper
    haveI : IsProper ((Over.pullback (spMap (algebraMap K (FractionRing W')))).obj A).hom :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap K (FractionRing W')))) (inferInstanceAs (IsProper A.hom))
    haveI : IsIso e.hom.left := ⟨e.inv.left, by simp [← Over.comp_left], by simp [← Over.comp_left]⟩
    rw [← Over.w e.hom]
    infer_instance
  have hsemiW : IsSemiAbelian GW :=
    isSemiAbelian_of_proper_generic_of_torusExtension W' (FractionRing W') GW hscW hprop
      (ResidueField R) ρ hker hρi htor
  unfold PotModel
  exact ⟨W', FractionRing W', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcompW, hfW, hlVW, hcW, GW, inferInstance, hmodW, hsemiW⟩

end GlobalTheory.SS
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_hom_algebraisation_of_reductionTower : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ Z : Over (Spec (CommRingCat.of R)), IsProjBy Z.hom → ∀ c : ∀ e, (Y e).left ⟶ Z.left, (∀ e, c e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ c (e + 1) = c e) → ∃ g : B ⟶ Z, ∀ e, b e ≫ g.left = c e := by
  first | exact @GlobalTheory.MorAlgTower.exists_hom_of_tower | exact GlobalTheory.MorAlgTower.exists_hom_of_tower | (intros; apply GlobalTheory.MorAlgTower.exists_hom_of_tower <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem psiUnitOn_abLocus_pel : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso → IsOpen (abLocus t.G) → ∀ y, PsiUnitOn P.D.toPre y (abLocus t.G) :=
  fun h1 h2 h3 h4 h5 _ _ _ _ _ R _ _ _ I hA t P _ ho y =>
    GlobalTheory.T.psiUnitOn_abelian_locus_uniformisation h1 h2 h3 h4 h5 R I hA P.D P.A t.G t.semi P.U ho y

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

theorem _root_.GlobalTheory.T.exists_normal_model_theta_tuple_maximal_minors : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω), S.HasTests → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω → ∃ (n a : ℕ) (GG : Fin n → S.J → Ω) (X Z : RatModel o Ω) (U₀ : Z.Z.Opens) (EE : Z.Lat S.J) (f : Z.Z ⟶ X.Z) (Xab : X.Z.Opens), X.IsNm S.th ∧ IsProjOver X.s ∧ Z.IsNm (fun q : S.Gam × (S.J → Fin n) => S.th q.1 * Matrix.det (Matrix.of fun i j => GG (q.2 i) j)) ∧ S.Over₀ Z U₀ ∧ S.IsEE Z U₀ EE ∧ X.IsHom Z (AlgHom.id o Ω) f ∧ (Xab : Set X.Z) = {x | S.TT X x = ⊥} ∧ IsIso (f ∣_ Xab) ∧ (∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z, ∀ w : S.J → Ω, w ∈ Submodule.span (Z.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ Z.O z) ∧ ∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z, (∀ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) / S.th x₀ ^ (a * Fintype.card S.J) ∈ Z.O z) ∧ (S.TT Z z = ⊥ ↔ ∃ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) ≠ 0 ∧ S.th x₀ ^ (a * Fintype.card S.J) / Matrix.det (Matrix.of fun i j => GG (k i) j) ∈ Z.O z) := by
  first | exact @GlobalTheory.ZH.exists_minor_model | exact GlobalTheory.ZH.exists_minor_model | (intros; apply GlobalTheory.ZH.exists_minor_model <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.CoreTests

theorem image_iff {T H B G B' F P : Scheme.{0}} (h : H ⟶ B) (s : T ⟶ B) (g : G ⟶ B') (s' : T ⟶ B')
    (r : F ⟶ G) (q : F ⟶ T) (cart : IsPullback r q g s') (u : H ⟶ P) (v : G ⟶ P)
    (e : pullback h s ≅ F) (e₁ : e.hom ≫ q = pullback.snd _ _) (e₂ : e.hom ≫ r ≫ v = pullback.fst _ _ ≫ u)
    (x : T ⟶ P) :
    (∃ c : T ⟶ H, c ≫ h = s ∧ c ≫ u = x) ↔ ∃ c' : T ⟶ G, c' ≫ g = s' ∧ c' ≫ v = x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨pullback.lift c (𝟙 T) (by simpa using hc) ≫ e.hom ≫ r, ?_, ?_⟩
    · simp only [Category.assoc]
      rw [cart.w, reassoc_of% e₁, pullback.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc]
      rw [e₂, pullback.lift_fst_assoc]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨cart.lift c (𝟙 T) (by simpa using hc) ≫ e.inv ≫ pullback.fst _ _, ?_, ?_⟩
    · simp only [Category.assoc]
      rw [pullback.condition, ← reassoc_of% e₁, e.inv_hom_id_assoc, cart.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc]
      rw [← e₂, e.inv_hom_id_assoc, cart.lift_fst_assoc]

theorem exists_test (hL : GlobalTheory.UT.LL) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J)
    (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (hS : S.Big) (hG : ρ.HasGeo)
    (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (hy : ex.core.Cl y) :
    ∃ τ : ex.core.Test y, ∀ x : Sp (GlobalTheory.ZJ.kb p) ⟶ Q.P.left, x ≫ Q.P.hom = GlobalTheory.ZJ.rPt p ≫ y →
      ((∃ c : Sp (GlobalTheory.ZJ.kb p) ⟶ τ.H.left, c ≫ τ.H.hom = GlobalTheory.ZJ.rPt p ≫ spMap τ.j ∧ c ≫ τ.f ≫ Q.G.ι = x) ↔
        (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := (GlobalTheory.T.exists_geometricTest_map_classicalPoint hL o Ω S ρ M U₀ EE hB Q hS hG).1 p y hy
  obtain ⟨τ, e, e₁, e₂⟩ := GlobalTheory.T.exists_uniformisationTest_of_geometricTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hS
  refine ⟨τ, fun x hx => ?_⟩
  exact (image_iff _ _ _ _ _ _ t.mod.cart.1 _ _ e e₁ e₂ x).trans
    (GlobalTheory.T.specialFibre_image_test_independent hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS x hx)

end GlobalTheory.ZH.CoreTests

theorem GlobalTheory.ZH.Clos.Ext.hasTests_and_indep : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.HasTests ∧ ex.core.Indep := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG
  have key := GlobalTheory.ZH.CoreTests.exists_test hL o Ω S ρ M U₀ EE hB Q ex hS hG
  have hT : ex.core.HasTests := fun p _ y hy => ⟨(key p y hy).choose⟩
  refine ⟨hT, GlobalTheory.T.indep_of_nested_special_fibre_images _ hT fun p _ y y' hy hy' hr => ?_⟩
  obtain ⟨τ, hτ⟩ := key p y hy
  obtain ⟨τ', hτ'⟩ := key p y' hy'
  refine ⟨τ, τ', fun c hc => ?_⟩
  have hx : (c ≫ τ.f ≫ Q.G.ι) ≫ Q.P.hom = GlobalTheory.ZJ.rPt p ≫ y := by
    have h : c ≫ τ.f ≫ ex.core.GG.hom = GlobalTheory.ZJ.rPt p ≫ y := by
      rw [τ.f_over, reassoc_of% hc, τ.fac]
    simp only [Category.assoc]
    exact h
  obtain ⟨c', hc', hf⟩ := (hτ' _ (hx.trans hr)).2 ((hτ _ hx).1 ⟨c, hc, rfl⟩)
  refine ⟨c', hc', ?_⟩
  have : Mono ex.core.G.ι := inferInstance
  rw [← cancel_mono ex.core.G.ι, Category.assoc, Category.assoc]
  exact hf
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PerpTorus
open GlobalTheory.ZH.TorusPerp GlobalTheory.TorusExt

theorem exists_form {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) {X : Type} [AddCommGroup X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy)
    (a : S.Gam) (ha : a ∈ S.perp yy.ker) :
    ∃ m : X →+ ZMod (S.r * S.N), ∀ b α, yy b = QuotientAddGroup.mk α → m α = eStd S.g _ a b := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ b b' : S.Gam, yy b = yy b' → eStd S.g _ a b = eStd S.g _ a b' := by
    intro b b' e
    have h0 : eStd S.g _ a (b - b') = 0 := ha _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  refine ⟨AddMonoidHom.mk' (fun α => eStd S.g _ a (σ α)) fun α β => ?_, fun b α e => ind _ _ ((hσ α).trans e.symm)⟩
  rw [← eStd_add_right]
  exact ind _ _ (by rw [map_add (f := _), hσ, hσ, hσ, QuotientAddGroup.mk_add])


attribute [local instance] gtGroup in
theorem exists_torus_point : LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (g : u.Geom) (a : S.Gam) (ha : a ∈ S.perp l.yy.ker), ∃ (q : QkPt u.D.toPre (PadicAlgCl p) S.N) (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q (g.pt (S.r • a)) ∧ ∀ χ, (τ (Multiplicative.ofAdd χ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζN ^ (l.wt χ ⟨a, ha⟩).val)) := by
  intro hL hT o Ω _ _ _ hA S ρ p _ y₀ u l g a ha
  have hG := hL.1.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hadm : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos

  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let ω : (PadicAlgCl p)ˣ := Units.map (y₀.comp (algebraMap o S.R)).toMonoidHom (hζ.isUnit hn.ne).unit
  have hωv : (ω : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N))) := rfl
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact (hζ.isRoot_cyclotomic hn.pos).map (y₀.comp (algebraMap o S.R))

  let pt : Multiplicative S.Gam →* (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
    MonoidHom.mk' (fun a => g.pt a.toAdd) fun _ _ => g.pt_add _ _
  have pt_nsmul : ∀ (n : ℕ) b, g.pt (n • b) = g.pt b ^ n := fun n b => map_pow pt (Multiplicative.ofAdd b) n
  have onto : ∀ b, ∃ q, f q = g.pt b := fun b => f₂ _ (by
    rw [← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul]
    exact map_one pt)
  obtain ⟨m, hm⟩ := exists_form S l.yy l.yy_onto a ha
  let τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ :=
    (AddChar.zmodChar (S.r * S.N) hω.pow_eq_one).toMonoidHom.comp m.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (m α).val := fun _ => rfl
  have hτ1 : τ ^ (S.r * S.N) = 1 := MonoidHom.ext fun α => by
    show (ω ^ (m α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow]
  obtain ⟨q, hq, hqτ⟩ := exists_qkPt_tor (F := PadicAlgCl p) hB τ hτ1
  obtain ⟨q₁, hq₁, hq₁τ⟩ := exists_qkPt_tor (F := PadicAlgCl p) (k := S.N) hB (τ ^ S.r) (by rw [← pow_mul, hτ1])
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := u.U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a', ha', -⟩ := g.pt_bij (f q) hq1
  have haa : a' = a := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eStd _ _ _ fun b => ?_
    obtain ⟨q', hq'⟩ := onto b
    have w₁ := (f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)
    rw [← ha', hq'] at w₁
    have w₂ := g.weil a' b (ω ^ (eStd S.g _ a' b).val) (by
      rw [Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul])
    have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB w₂ w₁)
    rw [hτ] at e₁
    have e₂ := ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)
    rw [hm b _ (l.yy_eq b q' _ ((f₁ _ _).2 hq'.symm) (g.pt_over b))] at e₂
    have e₃ := eStd_add_left S.g _ (a' - a) a b
    rw [sub_add_cancel, e₂] at e₃
    exact left_eq_add.1 (e₃.trans (add_comm _ _))
  subst haa
  refine ⟨q₁, τ ^ S.r, hq₁, hq₁τ, ?_, fun χ => ?_⟩
  · rw [pt_nsmul]
    refine (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N S.r (S.r * S.N) (by omega) hr
      (mul_comm _ _) q₁ q _).2 (hq₁.trans hq.symm) ((isNsmul_iff_eq _ _ _).2 ?_) ((f₁ _ _).2 ha')
    rw [(isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 hq₁τ), (isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 hqτ),
      ofMul_pow, map_nsmul]
  · obtain ⟨b, hb⟩ := l.yy_onto (QuotientAddGroup.mk χ)
    have z : S.ζN ^ S.N = 1 := by
      rw [ThetaSys.ζN, ← pow_mul, ← S.prim.pow_eq_one]
      congr 1
      ring
    have z' : S.ζN = (S.ζ ^ (S.r * S.N)) ^ S.r := by
      rw [ThetaSys.ζN, ← pow_mul]
      congr 1
      ring
    rw [l.wt_eq b χ hb, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ z,
      MonoidHom.pow_apply, hτ, hm b χ hb, z', pow_right_comm, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hωv,
      ← map_pow, ← map_pow, ← map_pow, ← map_pow]

end GlobalTheory.ZH.PerpTorus
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.twistedLabels_all_levels_of_four_le : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → (∀ k, 4 ≤ k → Labels A u r M ν' J k) → ∀ k, 0 < k → Labels A u r M ν' J k := by
  first | exact @GlobalTheory.Ex.LabelsAllLevels.labels_of_four_le | exact GlobalTheory.Ex.LabelsAllLevels.labels_of_four_le | (intros; apply GlobalTheory.Ex.LabelsAllLevels.labels_of_four_le <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.extendedArc_uAdicUniformisation_of_arcData : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → PushInvertible Y.t.G Y.t.PP.L → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → Y.HasArcData a (Ideal.span {(PowerSeries.X : PowerSeries O')}) (PowerSeries.C (R := O')) PowerSeries.X χ := by
  first | exact @GlobalTheory.ArcData.hasArcData_of_traitData | exact GlobalTheory.ArcData.hasArcData_of_traitData | (intros; apply GlobalTheory.ArcData.hasArcData_of_traitData <;> assumption)
end
