module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle671
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle533
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullO1SectionCoordinatesPower
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.NormBlowupField

theorem exists_normBl : ∀ (K : Type) [Field K] [CharZero K] (Z : Scheme.{0}) (z : Z ⟶ Sp K),
    IsProjOver z → GlobalTheory.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens),
    Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z)
    (BD : EffCartierData S), GlobalTheory.Poinc.IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ IsProper π ∧
    BD.idealSheaf = J.comap π ∧ IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  intro K _ _ Z z hz hZ J W hWd hWJ
  obtain ⟨X', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  haveI : LocallyOfFiniteType (b ≫ z) := by
    obtain ⟨m, i, hi, e⟩ := hbs
    have := isProper_str K m
    rw [← e]; infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (b ≫ z)
  let V : X'.Opens := b ⁻¹ᵁ W
  haveI hbW : IsIso (b ∣_ W) := hiso W fun x hx hJ => hWJ x hJ hx
  haveI hoi : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI hN : GlobalTheory.IsNormalScheme V.toScheme := .of_isOpenImmersion (V.ι ≫ b)
  haveI : IsReduced V.toScheme := by
    exact inferInstance
  haveI hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_of_genericPoints (o := CommRingCat.of K) V.ι (b ≫ z)
      (fun x _ => charZero_of_injective_ringHom (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (V.ι ≫ b ≫ z).appTop ≫ V.toScheme.presheaf.germ ⊤ x trivial ≫ V.toScheme.residue x).hom)
        (RingHom.injective _))
      fun x _ => (LocallyOfFiniteType.stalkMap V.ι x).residueFieldMap
  let ν := V.ι.fromNormalization
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.ι.normalization := IsNormalScheme.pred _
  have hν : IsIso (ν ∣_ V) := by
    have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  have hd : Dense ((ν ⁻¹ᵁ V : V.ι.normalization.Opens) : Set V.ι.normalization) := by
    refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2
  have hVd : Dense (V : Set X') := GlobalTheory.NormBlowupInt.dense_preimage_of_blowup J b hb hiso W hWd
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hK : D.KeepsRegular ν := by
    refine D.keepsRegular_of_dense ν (fun y => (hS y).1) (hd.mono fun t ht => ?_)
    show ν t ∉ D.idealSheaf.support
    rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
    exact fun h => hWJ _ h ht
  have hproj : IsProjOver ((ν ≫ b) ≫ z) := by
    rw [Category.assoc]; exact isProjOver_comp_of_isFinite ν hbs
  have hprop : IsProper (ν ≫ b) := by
    haveI : IsProper z := by
      obtain ⟨m, i, hi, e⟩ := hz
      have := isProper_str K m
      rw [← e]; infer_instance
    haveI : IsProper ((ν ≫ b) ≫ z) := by
      obtain ⟨m, i, hi, e⟩ := hproj
      have := isProper_str K m
      rw [← e]; infer_instance
    exact IsProper.of_comp (ν ≫ b) z
  refine ⟨V.ι.normalization, ν ≫ b, D.pull ν hK,
    ⟨inferInstance, X', b, ν, V, hb, rfl, hfin, hVd, hd, hν⟩, hproj, hprop, ?_, ?_, ?_⟩
  · rw [EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]
  · rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbW
  · convert hd using 1
    ext t
    simp [V]

end GlobalTheory.NormBlowupField
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TorEnd

theorem exists_lift_valuationSubring {F : Type} [Field F] (O : ValuationSubring F) {M : Type} [CommGroup M]
    (τ : M →* Fˣ) {k : ℕ} (hk : k ≠ 0) (hτ : τ ^ k = 1) :
    ∃ σ : M →* Oˣ, σ ^ k = 1 ∧ ∀ x, ((σ x : O) : F) = τ x := by
  have hp : ∀ x, (τ x : F) ^ k = 1 := fun x => by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hτ, MonoidHom.one_apply, Units.val_one]
  have hm : ∀ x, (τ x : F) ∈ O := fun x => by
    rw [← O.valuation_le_one_iff]
    have := congrArg O.valuation (hp x)
    rw [map_pow, map_one] at this
    exact ((pow_eq_one_iff_of_nonneg zero_le hk).1 this).le
  let σ₀ : M →* O :=
    { toFun := fun x => ⟨τ x, hm x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  refine ⟨σ₀.toHomUnits, MonoidHom.ext fun x => Units.ext (Subtype.ext ?_), fun x => rfl⟩
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  exact hp x

theorem chV_comp_torusMap {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z : Over S}
    (z : Z ⟶ splitTorus S X) (m : Y →+ X) (χ : Y) :
    GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap S m) χ = GlobalTheory.UU.chV z (m χ) := by
  refine Units.ext ?_
  rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val,
    ← GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_comp_torusMap]

theorem torMatch_of_endChar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G), IsMonHom f → ∀ m, EndChar U f m → TorMatch U U (RingHom.id R) f.left m := by
  intro R _ _ _ hR G _ _ hG D A U f hf m hm F _ _ i₁ i₂ hi k hk τ τ' q q' x x' hτ' hτ hq hqt hq' hqt' hx hx'
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  obtain ⟨s, s₁, s₂, s₃, s₄⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k (Nat.one_le_iff_ne_zero.2 hk0)
  let a : R →+* F := (@algebraMap (FractionRing R) F _ _ i₁).comp (algebraMap R (FractionRing R))
  have ha₂ : a = (@algebraMap (FractionRing R) F _ _ i₂).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun r => hi r
  let ν : Multiplicative D.toPre.X →* Multiplicative D.toPre.X := AddMonoidHom.toMultiplicative m
  have pw : ∀ {B : Type} [CommRing B] (σ : Multiplicative D.toPre.X →* Bˣ), σ ^ k = 1 → σ.comp ν ^ k = 1 :=
    fun σ h => MonoidHom.ext fun χ => DFunLike.congr_fun h (ν χ)
  obtain rfl : τ = τ'.comp ν := MonoidHom.ext fun χ => hτ χ.toAdd
  have e₁ := @s₄ F _ _ i₁ a _ (pw τ' hτ') q x rfl hq hqt hx
  have e₂ := @s₄ F _ _ i₂ a _ hτ' q' x' ha₂ hq' hqt' hx'
  rw [e₁, reassoc_of% e₂]
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing a
  let c : R →+* O := a.codRestrict O.toSubring hO
  have hc : IsLocalHom c := hloc
  obtain ⟨σ, hσ, hστ⟩ := exists_lift_valuationSubring O τ' hk0 hτ'
  have n₁ := s₂ O F c a O.subtype _ (pw σ hσ) _ (pw τ' hτ') rfl fun χ => (hστ (ν χ)).symm
  have n₂ := s₂ O F c a O.subtype _ hσ _ hτ' rfl fun χ => (hστ χ).symm
  suffices key : s O c _ (pw σ hσ) = s O c σ hσ ≫ f by
    rw [n₁, n₂, key, Over.comp_left, Category.assoc]
  have hkO : IsUnit (k : O) := by simpa using hk.map c
  refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap c) k hkO _ _ ?_
    (ResidueField O) (residue O) inferInstance ?_
  · rw [s₁, ← MonObj.pow_comp, s₁, MonObj.one_comp]
  let a₀ : R →+* ResidueField O := (residue O).comp c
  have ha₀ : ∀ r ∈ maximalIdeal R ^ (0 + 1), a₀ r = 0 := fun r hr => by
    rw [zero_add, pow_one] at hr
    exact (residue_eq_zero_iff _).2 (map_nonunit c r hr)
  let σ₀ : Multiplicative D.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp σ
  have hσ₀ : σ₀ ^ k = 1 := MonoidHom.ext fun χ => by
    have := DFunLike.congr_fun hσ χ
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this ⊢
    simp only [σ₀, MonoidHom.comp_apply, ← map_pow, this, map_one]
  have r₁ := s₂ O _ c a₀ (residue O) _ (pw σ hσ) _ (pw σ₀ hσ₀) rfl fun χ => rfl
  have r₂ := s₂ O _ c a₀ (residue O) _ hσ _ hσ₀ rfl fun χ => rfl
  have h₀ := isGrpPullback_pullback G (spMap a₀)
  let z : Over.mk (spMap (RingHom.id (ResidueField O))) ⟶ splitTorus (Sp (ResidueField O)) D.toPre.X :=
    (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
      ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp σ₀)
  have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (σ₀ (Multiplicative.ofAdd χ)) := fun χ => by
    simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]
    rfl
  have t₁ := s₃ _ _ a₀ ha₀ a₀ (RingHom.id _) _ _ h₀ _ (pw σ₀ hσ₀) (z ≫ GlobalTheory.SplitTorus.torusMap _ m) rfl
    fun χ => (chV_comp_torusMap z m χ).trans (hz _)
  have t₂ := s₃ _ _ a₀ ha₀ a₀ (RingHom.id _) _ _ h₀ _ hσ₀ z rfl hz
  have hf₀ : ((Over.pullback (spMap a₀)).map f).left ≫ pullback.fst G.hom (spMap a₀) =
      pullback.fst G.hom (spMap a₀) ≫ f.left := pullback.lift_fst _ _ _
  have hE := hm _ a₀ ha₀ _ _ h₀ _ hf₀
  rw [Over.comp_left, ← r₁, ← reassoc_of% r₂, t₁, t₂, Category.assoc z, ← hE, Category.assoc, ← hf₀]
  simp only [Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.TorEnd

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
open GlobalTheory.Poinc.Eq8

theorem _root_.GlobalTheory.T.uniformisation_endomorphism_closedFibreTorus_characterMap : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (E : EndU U.toUnifPre), EndChar U E.aG E.h := by
  first | exact @GlobalTheory.Poinc.Eq8.endChar_endU | exact GlobalTheory.Poinc.Eq8.endChar_endU | (intros; apply GlobalTheory.Poinc.Eq8.endChar_endU <;> assumption)
end

section

open IsLocalRing GlobalTheory.Poinc.Eq8
open scoped TensorProduct

namespace GlobalTheory.TraitLift

theorem exists_lift_adicCompletion (A V : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra A V] :
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : V →+* V')
      (g : AdicCompletion (maximalIdeal A) A →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      g.comp (algebraMap A _) = h.comp (algebraMap A V) ∧ ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ) := by
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  let R := AdicCompletion (maximalIdeal A) A
  haveI : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  let C := V ⊗[A] R
  let e : (C ⧸ (maximalIdeal V).map (algebraMap V C)) ≃+* R ⊗[A] (V ⧸ maximalIdeal V) :=
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor C (maximalIdeal V)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange A V V (V ⧸ maximalIdeal V) R).toRingEquiv).trans
      (Algebra.TensorProduct.comm A _ _).toRingEquiv
  haveI := formalFibre_isReduced_of_field A (V ⧸ maximalIdeal V)
  haveI : Nontrivial (R ⊗[A] (V ⧸ maximalIdeal V)) := inferInstance
  obtain ⟨V', i1, i2, i3, h₀, hc, hirr⟩ := GlobalTheory.ReducedFibre.exists_cdvr_of_flat_of_isReduced V C
    e.toEquiv.nontrivial (isReduced_of_injective e e.injective)
  refine ⟨V', i1, i2, i3, h₀.comp (algebraMap V C),
    h₀.comp (Algebra.TensorProduct.includeRight (R := A) (A := V) (B := R)).toRingHom, hc, ?_, hirr⟩
  ext a
  simp only [RingHom.comp_apply]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight (R := A) (A := V) (B := R)).commutes a

theorem isLocalHom_and_injective {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing V'] [IsDomain V'] (h : V →+* V') (hh : ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ)) :
    Function.Injective h ∧ IsLocalHom h := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine ⟨(injective_iff_map_eq_zero h).mpr fun x hx => ?_, ⟨fun x hx => ?_⟩⟩
  · by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [map_mul, map_pow] at hx
    exact mul_ne_zero (u.isUnit.map h).ne_zero (pow_ne_zero n (hh ϖ hϖ).ne_zero) hx
  · by_contra hu
    have hm : x ∈ maximalIdeal V := hu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    exact (hh ϖ hϖ).not_isUnit (isUnit_of_dvd_unit (map_dvd h hm) hx)

theorem exists_lift_of_isCpl : ∀ (A R V : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing R] (j : A →+* R), IsCpl j → ∀ [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (f : A →+* V), ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : V →+* V') (g : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective h ∧ IsLocalHom h ∧ g.comp j = h.comp f ∧ ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ) := by
  intro A R V _ _ _ _ j hj _ _ _ f
  obtain ⟨e, he⟩ := hj
  letI : Algebra A V := f.toAlgebra
  obtain ⟨V', i1, i2, i3, h, g, hc, hcomp, hirr⟩ := exists_lift_adicCompletion A V
  obtain ⟨hinj, hloc⟩ := isLocalHom_and_injective h hirr
  refine ⟨V', i1, i2, i3, h, g.comp e.symm.toRingHom, hc, hinj, hloc, ?_, hirr⟩
  ext a
  have := RingHom.congr_fun hcomp a
  simp only [RingHom.comp_apply] at this ⊢
  rw [← he a]
  simpa [RingHom.algebraMap_toAlgebra] using this

end GlobalTheory.TraitLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.elementaryMatrixEndomorphism_groupPullback_transport : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (a b : Fin 8) (f₁ : B ⟶ B) (f₁' : B' ⟶ B'), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ w, (pr' w).left ≫ χ = φB ≫ (pr w).left) → f₁'.left ≫ φB = φB ≫ f₁.left → MatEnd pr a b f₁ → MatEnd pr' a b f₁' := by
  first | exact @GlobalTheory.MatEndPull.matEnd_pull | exact GlobalTheory.MatEndPull.matEnd_pull | (intros; apply GlobalTheory.MatEndPull.matEnd_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_open_finite_onto_of_levelCover : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (β : cycAway n →+* o) (S : ThetaSys o Ω) (u : Sp S.R ⟶ F.X) (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X)
    (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → X.IsHom M (AlgHom.id o Ω) f →
    IsIso (f ∣_ Xab) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → Set.range d ⊆ Xab →
    ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ f ⁻¹' Xab := by
  first | exact @GlobalTheory.SiegTh.exists_openAt_of_levAt | exact GlobalTheory.SiegTh.exists_openAt_of_levAt | (intros; apply GlobalTheory.SiegTh.exists_openAt_of_levAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.closedPoint_completion_positive_residueChar : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsLocalHom j ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ maximalIdeal R := by
  first | exact @GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar | exact GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar | (intros; apply GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_normalisation_projective_quasiFinite : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra.FiniteType ℤ o] (N : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp o) (f : X ⟶ PSpace o N), IsIntegral X → Geo.Tor.IsNormalScheme X → LocallyOfFiniteType s → QuasiCompact s → IsSeparated s → f ≫ PSpace.str o N = s → QFin f → ∃ (Z : Scheme.{0}) (p : Z ⟶ PSpace o N) (i : X ⟶ Z), IsFinite p ∧ IsOpenImmersion i ∧ i ≫ p = f ∧ Geo.Tor.IsNormalScheme Z ∧ IsIntegral Z ∧ Dense (Set.range i) := by
  first | exact @GlobalTheory.SiegMin.exists_finite_openImmersion_of_qFin | exact GlobalTheory.SiegMin.exists_finite_openImmersion_of_qFin | (intros; apply GlobalTheory.SiegMin.exists_finite_openImmersion_of_qFin <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitLocal

theorem comap_maximalIdeal_of_irreducible {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : V →+* V') (ϖ : V) (hϖ : Irreducible (h ϖ)) :
    Ideal.comap h (maximalIdeal V') = maximalIdeal V := by
  have hne : Ideal.comap h (maximalIdeal V') ≠ ⊥ := by
    intro h0
    have : ϖ ∈ Ideal.comap h (maximalIdeal V') := hϖ.not_isUnit
    rw [h0, Ideal.mem_bot] at this
    exact hϖ.ne_zero (by rw [this, map_zero])
  haveI : (Ideal.comap h (maximalIdeal V')).IsPrime := Ideal.comap_isPrime _ _
  exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)

theorem maximalIdeal_le_map {O R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R]
    [IsLocalRing R] (j : O →+* R) (hj : IsCpl j) : maximalIdeal R ≤ Ideal.map j (maximalIdeal O) := by
  obtain ⟨e, he⟩ := hj
  have fg : (maximalIdeal O).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal O) O) := AdicCompletion.isLocalRing_of_fg fg
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  intro r hr
  have h1 : e.symm r ∈ maximalIdeal (AdicCompletion (maximalIdeal O) O) := by
    intro hu
    have := hu.map e
    rw [RingEquiv.apply_symm_apply] at this
    exact hr this
  rw [hm] at h1
  have h2 := Ideal.mem_map_of_mem (e : AdicCompletion (maximalIdeal O) O →+* R) h1
  rw [Ideal.map_map] at h2
  have h3 : (e : AdicCompletion (maximalIdeal O) O →+* R).comp (algebraMap O _) = j := by
    first | exact he | exact RingHom.ext he | exact he.symm
  rw [h3] at h2
  simpa using h2

end GlobalTheory.Poinc.TraitLocal

theorem GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : V →+* V') (g' : R →+* V') (ξ : Sp V ⟶ M.Z), Irreducible (h ϖ) → ξ (IsLocalRing.closedPoint V) = x → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → IsLocalHom g' := by
  intro o' Ω _ _ _ hA M x R _ _ j hj V _ _ _ ϖ V' _ _ _ h g' ξ hϖ hξ hsq
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have h1 : spMap h (closedPoint V') = closedPoint V :=
    PrimeSpectrum.ext (GlobalTheory.Poinc.TraitLocal.comap_maximalIdeal_of_irreducible h ϖ hϖ)
  have h2 : (spMap h ≫ ξ) (closedPoint V') = x :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg ξ h1).trans hξ)
  rw [← hsq] at h2
  have h3 : M.Z.fromSpecStalk x (spMap j (spMap g' (closedPoint V'))) =
      M.Z.fromSpecStalk x (closedPoint (M.Z.presheaf.stalk x)) :=
    h2.trans Scheme.fromSpecStalk_closedPoint.symm
  have h4 := (M.Z.fromSpecStalk x).isEmbedding.injective h3
  have h5 : Ideal.comap j (Ideal.comap g' (maximalIdeal V')) = maximalIdeal (M.Z.presheaf.stalk x) :=
    congrArg PrimeSpectrum.asIdeal h4
  have h6 : maximalIdeal R ≤ Ideal.comap g' (maximalIdeal V') :=
    (GlobalTheory.Poinc.TraitLocal.maximalIdeal_le_map j hj).trans (Ideal.map_le_iff_le_comap.2 h5.ge)
  refine ⟨fun r hr => ?_⟩
  by_contra hn
  exact h6 (show r ∈ maximalIdeal R from hn) hr
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pull_O1_section_coordinates_power : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (I : Type) [Finite I] (th : I → Ω) (δ : LB M.Z) (t : I → δ.Sec) (N D : ℕ) (e : Fin (N + 1) → Ω) (h : M.Z ⟶ PSpace o N), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → SecCoord δ t M.pt th → PCrd (M.pt ≫ h) e → SameScale M th e D → LBIso ((GlobalTheory.ProjSpace.O1 o N).pull h) (lbPow δ D) := by
  first | exact @GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow | exact GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow | (intros; apply GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_normal_projective_toric_minor_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω → ∃ (X M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE), MinorAt S X M U₀ EE f Xab ∧ IsOpen (abLocus Zh.G) ∧ (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
  first | exact @GlobalTheory.SiegJoin.minor_model | exact GlobalTheory.SiegJoin.minor_model | (intros; apply GlobalTheory.SiegJoin.minor_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.range_subset_abelianLocus_of_levelTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (o Ω : Type) [CommRing o] [Field Ω]
    [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X),
    SysAt F W β S ρ u → ∀ (Y M : RatModel o Ω) (q : Y.Z ⟶ F.X) (U₀ : M.Z.Opens) (EE : M.Lat S.J)
    (Zh : ZHOut ρ M U₀ EE), LevAt F β u Y q → S.Over₀ M U₀ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ξ : Sp V ⟶ M.Z) (τ : Sp V ⟶ Y.Z)
      (κ : Ω →+* FractionRing V), spMap (algebraMap V (FractionRing V)) ≫ ξ = spMap κ ≫ M.pt →
      spMap (algebraMap V (FractionRing V)) ≫ τ = spMap κ ≫ Y.pt → Set.range ξ ⊆ abLocus Zh.G := by
  first | exact @GlobalTheory.SiegTh.range_subset_abLocus_of_levelTrait | exact GlobalTheory.SiegTh.range_subset_abLocus_of_levelTrait | (intros; apply GlobalTheory.SiegTh.range_subset_abLocus_of_levelTrait <;> assumption)
end
