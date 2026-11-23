module

public import Development.EtaleCohomology.EtaleSheaves.Bundle026
public import Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing.SecondBlockUnimodularLocusInclusionMono
public import Development.EtaleCohomology.EtaleSheaves.Bundle012
public import Development.EtaleCohomology.EtaleSheaves.Bundle069
public import Development.EtaleCohomology.EtaleSheaves.Bundle085
public import Development.EtaleCohomology.EtaleSheaves.Bundle034
public import Development.EtaleCohomology.EtaleSheaves.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle831
import Development.EtaleCohomology.EtaleSheaves.Bundle040
import Development.EtaleCohomology.EtaleSheaves.Bundle024
public import Development.EtaleCohomology.EtaleSheaves.Bundle084
public import Development.EtaleCohomology.EtaleSheaves.Bundle020
public import Development.EtaleCohomology.EtaleSheaves.LeafActSheafPf
import Development.EtaleCohomology.EtaleSheaves.Bundle023
import Development.EtaleCohomology.EtaleSheaves.Bundle041
import Development.EtaleCohomology.EtaleSheaves.Bundle025
public import Development.EtaleCohomology.EtaleSheaves.Bundle038
import Development.EtaleCohomology.EtaleSheaves.Bundle064
import Development.EtaleCohomology.EtaleSheaves.Bundle079
import Development.EtaleCohomology.EtaleSheaves.Bundle014
public import Development.EtaleCohomology.EtaleSheaves.Bundle076
import Development.EtaleCohomology.EtaleSheaves.Bundle027
import Development.EtaleCohomology.EtaleSheaves.Bundle075
import Development.EtaleCohomology.EtaleSheaves.Bundle060
import Development.EtaleCohomology.EtaleSheaves.Bundle087
import Development.EtaleCohomology.EtaleSheaves.Bundle090
import Development.EtaleCohomology.EtaleSheaves.Bundle028
import Development.EtaleCohomology.EtaleSheaves.Bundle011
import Development.EtaleCohomology.EtaleSheaves.Bundle078
import Development.EtaleCohomology.EtaleSheaves.Bundle083
import Development.EtaleCohomology.EtaleSheaves.Bundle074
import Development.EtaleCohomology.EtaleSheaves.UnimodularBlockEqToHomValEqOne
import Development.EtaleCohomology.EtaleSheaves.UnitExistence.CocycleOfSec
import Development.EtaleCohomology.EtaleSheaves.Bundle054
public import Development.EtaleCohomology.EtaleSheaves.WeightBoundsExistence
public import Development.EtaleCohomology.EtaleSheaves.Bundle093
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.Fix.EtaleChapterDTwo

theorem awSpec : LateralTheory.E.LeafA6suppPf.LeafAWSpec := by
  intro q _ E n m i j α β
  have hS := LateralTheory.Fix.CupProductTensor.cupSpec (ZMod q) (twPair q i j) E (rfl : n + m = n + m)
  obtain ⟨γ, hγ⟩ := hS.1 α β
  exact ⟨γ, hγ, hS.2 α β γ hγ⟩

theorem s0 : LateralTheory.E.D2.LeafA6nat := @_root_.LateralTheory.E.LeafA6nat_xy7V2Cut.goal_of
theorem s1 : LateralTheory.E.CupProductRingLaws.LeafCupSpec := @_root_.LateralTheory.Fix.CupProductTensor.cupSpec
theorem s2 : LateralTheory.E.CupProductRingLaws.LeafTwPairExists := @_root_.LateralTheory.Fix.CupProductTensor.twPairExists
theorem s3 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists_of
theorem s4 : LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor_of
theorem s5 : LateralTheory.E.ZModFlatnessFromBaerCriterion.TensTwRes := @_root_.GlobalTheory.EtC.isTwRes_tensor
theorem s6 : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj := @_root_.LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj_of
theorem s7 : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod := @_root_.LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod_of
theorem s8 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes_of s5 s6 s7
theorem s9 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy_of
theorem s10 : LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy := @_root_.LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy_of s3 s4 s8 s9
theorem s11 : LateralTheory.E.LeafTwPairUniquePf.LeafHtpyAW := @_root_.LateralTheory.E.FreeSheafGeneratorLifts.LeafHtpyAW_proved
theorem s12 : LateralTheory.E.CupProductRingLaws.LeafTwPairUnique := @_root_.LateralTheory.E.CupProductRingLaws.LeafTwPairUnique_of s1 s10 s11
theorem s13 : LateralTheory.E.LeafOneExistsPf.LeafUnitSec := @_root_.LateralTheory.E.UnitSections.LeafUnitSec_of
theorem s14 : LateralTheory.E.LeafOneSpecPf.LeafOneExists := @_root_.LateralTheory.E.LeafOneExistsPf.CocycleOfSec.LeafOneExists_of_unit s13
theorem s15 : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := @_root_.LateralTheory.E.LeafPrimCoverPf.leafPrimCover_pf
theorem s16 : LateralTheory.E.CupProductRingLaws.LeafOneSpec := @_root_.LateralTheory.E.LeafOneSpecPf.LeafOneSpec_of s14 s15
theorem s17 : LateralTheory.E.LeafUnitActPf.LeafActSheaf := @_root_.LateralTheory.E.LeafActSheafPf.LeafActSheaf_of
theorem s18 : LateralTheory.E.LeafUnitPairGPf.LeafUnitAct := @_root_.LateralTheory.E.LeafUnitActPf.LeafUnitAct_of s17
theorem s19 : LateralTheory.E.LeafPairExtPf2.LeafTensUP := @_root_.LateralTheory.E.LeafTensUPPf.etale_tensor_pairing_universal_property_holds
theorem s20 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen := @_root_.LateralTheory.E.LeafTw0LocGenPf.LeafTw0LocGen_of
theorem s21 : LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0TwFree := @_root_.LateralTheory.E.LeafTw0TwFreePf.LeafTw0TwFree_of
theorem s22 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0GenFree := @_root_.LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0GenFree_of s21
theorem s23 : LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit := @_root_.LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocSplit_of s20 s22
theorem s24 : LateralTheory.E.LeafTensMonoPf.LeafPreTensLocInj := @_root_.LateralTheory.E.LeafPreTensLocInjPf.LeafPreTensLocInj_of s23
theorem s25 : LateralTheory.E.LeafExtTensPf.LeafTensMono := @_root_.LateralTheory.E.LeafTensMonoPf.LeafTensMono_of s24
theorem s26 : LateralTheory.E.LeafTensQIsoPf.LeafTensQIsoGen := @_root_.LateralTheory.E.LeafTensQIsoGenPf.LeafTensQIsoGen_of
theorem s27 : LateralTheory.E.LeafTensQIsoPf.LeafSecInj := @_root_.LateralTheory.E.LeafSecInjPf.LeafSecInj_of
theorem s28 : LateralTheory.E.LeafTensQIsoPf.LeafZModInjFlat := @_root_.LateralTheory.E.LeafZModInjFlatPf.LeafZModInjFlat_of
theorem s29 : LateralTheory.E.LeafExtTensPf.LeafTensQIso := @_root_.LateralTheory.E.LeafTensQIsoPf.LeafTensQIso_of s26 s27 s28
theorem s30 : LateralTheory.E.LeafPairExtPf2.LeafExtTens := @_root_.LateralTheory.E.LeafExtTensPf.LeafExtTens_of s25 s29
theorem s31 : LateralTheory.E.LeafPairExtPf.LeafExtAlongAug := @_root_.LateralTheory.E.LeafPairExtPf2.LeafExtAlongAug_of s19 s30
theorem s32 : LateralTheory.E.LeafUnitPairGPf.LeafPairExt := @_root_.LateralTheory.E.LeafPairExtPf.LeafPairExt_of' s31
theorem s33 : LateralTheory.E.LeafUnitPairPf.LeafUnitPairG := @_root_.LateralTheory.E.LeafUnitPairGPf.LeafUnitPairG_of s18 s32
theorem s34 : LateralTheory.E.LeafRingUnitPf.LeafUnitPair := @_root_.LateralTheory.E.LeafUnitPairPf.LeafUnitPair_of s33
theorem s35 : LateralTheory.E.LeafOneLocPf.LeafPrimLoc := @_root_.LateralTheory.E.PrimitiveRootLocalization.LeafPrimLoc_of
theorem s36 : LateralTheory.E.LeafRingUnitPf.LeafOneLoc := @_root_.LateralTheory.E.LeafOneLocPf.LeafOneLoc_of s35
theorem s37 : LateralTheory.E.LeafRingUnitPf.LeafUnitAW := @_root_.LateralTheory.E.LeafUnitAWPf.LeafUnitAW_of
theorem s38 : LateralTheory.E.CupProductRingLaws.LeafRingUnit := @_root_.LateralTheory.E.LeafRingUnitPf.LeafRingUnit_of s1 s2 s12 s16 s34 s36 s37
theorem s39 : LateralTheory.E.CupProductRingLaws.LeafRingAssoc := @_root_.LateralTheory.Fix.CupProductTensor.ringAssoc
theorem s40 : LateralTheory.E.CupProductRingLaws.LeafRingComm := @_root_.LateralTheory.E.RingCommutativity.goal_of
theorem s41 : LateralTheory.E.D2.LeafA6ring := @_root_.LateralTheory.E.LeafA6ringCut.goal_of s38 s39 s40
theorem s42 : LateralTheory.E.D2.LeafRing := @_root_.LateralTheory.E.D2.LeafRing_of s0 s41
theorem s43 : LateralTheory.E.D2.LeafChern := @_root_.LateralTheory.E.D2.LeafChern_of
theorem s44 : LateralTheory.E.D2.LeafNat := @_root_.LateralTheory.E.D2.LeafNat_of s0
theorem s45 : LateralTheory.E.LeafGeomPf.LeafHalf1 := @_root_.LateralTheory.E.LeafHalf1Pf.LeafHalf1_of
theorem s46 : LateralTheory.E.HalfDegreeVanishing.LeafMapW := @_root_.LateralTheory.E.LeafMapWPf.LeafMapW_of
theorem s47 : LateralTheory.E.LeafGeomPf.LeafHalf2 := @_root_.LateralTheory.E.HalfDegreeVanishing.LeafHalf2_of s46
theorem s48 : LateralTheory.E.D2.LeafGeom := @_root_.LateralTheory.E.LeafGeomPfLoc.LeafGeom_of s45 s47
theorem s49 : LateralTheory.E.D2.LeafCover2 := @_root_.LateralTheory.E.LeafCover2Pf.LeafCover2_of
theorem s50 : LateralTheory.E.LeafA6suppPf.LeafAWSpec := awSpec
theorem s51 : LateralTheory.E.LeafA6suppPf.LeafRepVanish := @_root_.LateralTheory.E.LeafRepVanishPf.LeafRepVanish_of
theorem s52 : LateralTheory.E.LeafA6suppPf.LeafCochainVanish := @_root_.LateralTheory.E.LeafA6suppPf.LeafCochainVanish_of
theorem s53 : LateralTheory.E.D2.LeafA6supp := @_root_.LateralTheory.E.LeafA6suppPf.LeafA6supp_of s50 s51 s52
theorem s54 : LateralTheory.E.D2.LeafWhitney := @_root_.LateralTheory.E.D2.LeafWhitney_of s48 s49 s53 s0
theorem s55 : LateralTheory.E.D2.LeafLine := @_root_.LateralTheory.E.D2.LeafLine_of s0
theorem s56 : LateralTheory.E.D2.LeafNewton := @_root_.LateralTheory.E.LeafNewtonPf.LeafNewton_of
theorem s57 : LateralTheory.E.EtaleChapterDTwo := @_root_.LateralTheory.E.D2.goal_of s42 s43 s44 s54 s55 s56

end LateralTheory.Fix.EtaleChapterDTwo
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf LateralTheory.E.StrictHenselianNeighbourhood

namespace LateralTheory.E.EtaleNeighbourhoodSystem

section
variable {S : Scheme.{0}} {Ω : Type} [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)

abbrev Fb : S.Etale ⥤ Type := Scheme.Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))

lemma exists_affine (i : (Fb s).Elements) :
    ∃ j : (Fb s).Elements, IsAffine j.1.left ∧ Nonempty (j ⟶ i) := by
  rcases i with ⟨x⟩
  rename_i X
  cases X with | _ Y f
  obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
  dsimp at y hy
  obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec R ⟶ Y)
      (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
    obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (x := y.base default) (U := ⊤) (by simp)
    refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  refine ⟨Functor.elementsMk (Fb s) ((Scheme.AffineEtale.Spec S).obj (Scheme.AffineEtale.mk (j ≫ f))) (Over.homMk y'), ?_,
    ⟨⟨MorphismProperty.Over.homMk j rfl trivial, by cat_disch⟩⟩⟩
  change IsAffine (Spec R)
  infer_instance

lemma exists_small : ∃ (Q : Set (Fb s).Elements), Small.{0} Q ∧ (∀ j ∈ Q, IsAffine j.1.left) ∧
    ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i) := by
  haveI : InitiallySmall.{0} (Fb s).Elements := (Scheme.pointSmallEtale s).initiallySmall
  obtain ⟨Q0, hQ0, h0⟩ := InitiallySmall.exists_small_weakly_initial_set.{0} (Fb s).Elements
  choose g hg hg' using exists_affine s
  refine ⟨g '' Q0, ?_, ?_, ?_⟩
  · haveI := hQ0; infer_instance
  · rintro _ ⟨i, -, rfl⟩; exact hg i
  · intro i
    obtain ⟨k, hk, ⟨f⟩⟩ := h0 i
    exact ⟨g k, ⟨k, hk, rfl⟩, ⟨(hg' k).some ≫ f⟩⟩

variable (Q : Set (Fb s).Elements) [Small.{0} Q]

def ι : Shrink.{0} Q → (Fb s).Elements := fun q => ((equivShrink Q).symm q).1
lemma ι_mem (q : Shrink.{0} Q) : ι s Q q ∈ Q := ((equivShrink Q).symm q).2

abbrev Jc := InducedCategory (Fb s).Elements (ι s Q)

lemma exists_of_wi (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) (d : (Fb s).Elements) :
    ∃ c : Jc s Q, Nonempty ((ι s Q c) ⟶ d) := by
  obtain ⟨j, hj, ⟨f⟩⟩ := hwi d
  exact ⟨equivShrink Q ⟨j, hj⟩, ⟨eqToHom (by simp [ι]) ≫ f⟩⟩

lemma cof (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) : IsCofiltered (Jc s Q) := by
  have h := exists_of_wi s Q hwi
  obtain ⟨d⟩ := IsCofiltered.nonempty (C := (Fb s).Elements)
  exact
  { cone_objs := fun a b => by
      obtain ⟨c, ⟨hc⟩⟩ := h (IsCofiltered.min (ι s Q a) (ι s Q b))
      exact ⟨c, InducedCategory.homMk (hc ≫ IsCofiltered.minToLeft _ _),
        InducedCategory.homMk (hc ≫ IsCofiltered.minToRight _ _), trivial⟩
    cone_maps := fun a b f g => by
      obtain ⟨c, ⟨hc⟩⟩ := h (IsCofiltered.eq f.hom g.hom)
      refine ⟨c, InducedCategory.homMk (hc ≫ IsCofiltered.eqHom f.hom g.hom), ?_⟩
      apply InducedCategory.hom_ext
      show (hc ≫ IsCofiltered.eqHom f.hom g.hom) ≫ f.hom = (hc ≫ IsCofiltered.eqHom f.hom g.hom) ≫ g.hom
      rw [Category.assoc, Category.assoc, IsCofiltered.eq_condition]
    nonempty := ⟨(h d).choose⟩ }

def G : Jc s Q ⥤ Scheme.{0} :=
  inducedFunctor (ι s Q) ⋙ CategoryOfElements.π (Fb s) ⋙ Scheme.Etale.forget S ⋙ Over.forget S

def D : (Jc s Q)ᵒᵖ ⥤ CommRingCat.{0} := (G s Q).op ⋙ Scheme.Γ

end

section Sys
variable {B : Scheme.{0}} {U : B.Etale} {Ω : Type} [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) (Q : Set (Fb s).Elements) [Small.{0} Q]

def pt (j : Jc s Q) : Spec (CommRingCat.of Ω) ⟶ (G s Q).obj j := (ι s Q j).2.left

lemma pt_w (j : Jc s Q) : pt s Q j ≫ (ι s Q j).1.hom = s := Over.w (ι s Q j).2

lemma G_w {j k : Jc s Q} (m : k ⟶ j) : (G s Q).map m ≫ (ι s Q j).1.hom = (ι s Q k).1.hom :=
  MorphismProperty.Over.w m.hom.1

lemma pt_map {j k : Jc s Q} (m : k ⟶ j) : pt s Q k ≫ (G s Q).map m = pt s Q j :=
  congrArg CommaMorphism.left m.hom.2

def V (j : (Jc s Q)ᵒᵖ) : B.Etale :=
  MorphismProperty.Over.mk ⊤ ((ι s Q j.unop).1.hom ≫ U.hom)
    (by have := (ι s Q j.unop).1.prop; have := U.prop; exact Etale.etale_comp _ _)

def a (j : (Jc s Q)ᵒᵖ) : V s Q j ⟶ U :=
  MorphismProperty.Over.homMk (ι s Q j.unop).1.hom rfl trivial

variable (haff : ∀ j ∈ Q, IsAffine j.1.left)
include haff

lemma aff (j : Jc s Q) : IsAffine ((G s Q).obj j) := haff _ (ι_mem s Q j)

def e (j : (Jc s Q)ᵒᵖ) : Sp ((D s Q).obj j) ⟶ (G s Q).obj j.unop :=
  haveI := aff s Q haff j.unop; ((G s Q).obj j.unop).isoSpec.inv

lemma e_iso (j : (Jc s Q)ᵒᵖ) : IsIso (e s Q haff j) := by unfold e; exact Iso.isIso_inv _

def l (j : (Jc s Q)ᵒᵖ) : Spec (CommRingCat.of Ω) ⟶ Sp ((D s Q).obj j) :=
  haveI := aff s Q haff j.unop; pt s Q j.unop ≫ ((G s Q).obj j.unop).isoSpec.hom

lemma l_e (j : (Jc s Q)ᵒᵖ) : l s Q haff j ≫ e s Q haff j = pt s Q j.unop := by
  unfold l e
  exact (Category.assoc _ _ _).trans ((congrArg (pt s Q j.unop ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _))

lemma nat {j k : (Jc s Q)ᵒᵖ} (f : j ⟶ k) :
    Spec.map ((D s Q).map f) ≫ e s Q haff j = e s Q haff k ≫ (G s Q).map f.unop := by
  haveI := aff s Q haff j.unop; haveI := aff s Q haff k.unop
  exact Scheme.isoSpec_inv_naturality ((G s Q).map f.unop)

def t (j0 : (Jc s Q)ᵒᵖ) : Sp (colimit.cocone (D s Q)).pt ⟶ U.left :=
  Spec.map ((colimit.cocone (D s Q)).ι.app j0) ≫ e s Q haff j0 ≫ (ι s Q j0.unop).1.hom

lemma main (x : U.left) (hx : s default = x) (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (_ : IsColimit c) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t := by
  haveI := cof s Q hwi
  obtain ⟨j0⟩ := IsFiltered.nonempty (C := (Jc s Q)ᵒᵖ)
  have hcomp0 : ∀ (j k : (Jc s Q)ᵒᵖ) (f : j ⟶ k),
      Spec.map ((D s Q).map f) ≫ e s Q haff j ≫ (a s Q j).left = e s Q haff k ≫ (a s Q k).left := by
    intro j k f
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (a s Q j).left) (nat s Q haff f)).trans
      ((Category.assoc _ _ _).trans (congrArg (e s Q haff k ≫ ·) (G_w s Q f.unop))))
  have key : ∀ (j k : (Jc s Q)ᵒᵖ) (f : j ⟶ k),
      Spec.map ((colimit.cocone (D s Q)).ι.app j) ≫ e s Q haff j ≫ (a s Q j).left =
        Spec.map ((colimit.cocone (D s Q)).ι.app k) ≫ e s Q haff k ≫ (a s Q k).left := by
    intro j k f
    rw [← (colimit.cocone (D s Q)).w f, Spec.map_comp, Category.assoc, hcomp0 j k f]
  refine ⟨(Jc s Q)ᵒᵖ, inferInstance, inferInstance, D s Q, colimit.cocone _, colimit.isColimit _,
    V s Q, a s Q, l s Q haff, e s Q haff, t s Q haff j0, hx, e_iso s Q haff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    erw [reassoc_of% (l_e s Q haff j)]
    exact pt_w s Q j.unop
  · intro j k f
    have := hcomp0 j k f
    simp only [CommRingCat.ofHom_hom]
    exact this
  · intro j
    simp only [CommRingCat.ofHom_hom]
    obtain ⟨k, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs j j0
    erw [key j k f, ← key j0 k g]
    rfl
  · intro j k f
    haveI := e_iso s Q haff j
    rw [← cancel_mono (e s Q haff j)]
    simp only [CommRingCat.ofHom_hom, Category.assoc]
    rw [nat, reassoc_of% (l_e s Q haff k), l_e, pt_map]
  · intro U' b l' hl'
    let X' : U.left.Etale := MorphismProperty.Over.mk ⊤ b.left inferInstance
    obtain ⟨c, ⟨hc⟩⟩ := exists_of_wi s Q hwi (Functor.elementsMk (Fb s) X' (Over.homMk l' hl'))
    refine ⟨op c, hc.1.left, MorphismProperty.Over.w hc.1, ?_⟩
    erw [reassoc_of% (l_e s Q haff (op c))]
    exact congrArg CommaMorphism.left hc.2
  · intro U' b j g g' hg hg' heq
    erw [reassoc_of% (l_e s Q haff j), reassoc_of% (l_e s Q haff j)] at heq
    let X' : U.left.Etale := MorphismProperty.Over.mk ⊤ b.left inferInstance
    have hy : (pt s Q j.unop ≫ g) ≫ b.left = s := by
      exact (Category.assoc _ _ _).trans ((congrArg (pt s Q j.unop ≫ ·) hg).trans (pt_w s Q j.unop))
    let y : (Fb s).Elements := Functor.elementsMk (Fb s) X' (Over.homMk (pt s Q j.unop ≫ g) hy)
    let u : ι s Q j.unop ⟶ y := ⟨MorphismProperty.Over.homMk (B := X') g hg trivial,
      by apply Over.OverMorphism.ext; rfl⟩
    let u' : ι s Q j.unop ⟶ y := ⟨MorphismProperty.Over.homMk (B := X') g' hg' trivial,
      by apply Over.OverMorphism.ext; exact heq.symm⟩
    obtain ⟨c, ⟨hc⟩⟩ := exists_of_wi s Q hwi (IsCofiltered.eq u u')
    let m : c ⟶ j.unop := InducedCategory.homMk (hc ≫ IsCofiltered.eqHom u u')
    refine ⟨op c, m.op, ?_⟩
    have h0 : (hc ≫ IsCofiltered.eqHom u u') ≫ u = (hc ≫ IsCofiltered.eqHom u u') ≫ u' := by
      rw [Category.assoc, Category.assoc, IsCofiltered.eq_condition]
    have h1 := congrArg (fun z => z.1.left) h0
    simp only [CommRingCat.ofHom_hom]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) (nat s Q haff m.op)).trans ((Category.assoc _ _ _).trans
      ((congrArg (e s Q haff (op c) ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g') (nat s Q haff m.op)).symm.trans (Category.assoc _ _ _))))))

end Sys

theorem LeafSHNbSys_of : LeafSHNbSys := by
  intro B U x
  let Ω := SeparableClosure (U.left.residueField x)
  let s : Spec (CommRingCat.of Ω) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)) ≫ U.left.fromSpecResidueField x
  have hx : s default = x := by
    first | exact Scheme.fromSpecResidueField_apply x _ | (simp [s]; exact Scheme.fromSpecResidueField_apply x _)
  obtain ⟨Q, hQs, haff, hwi⟩ := exists_small s
  haveI := hQs
  exact ⟨Ω, inferInstance, inferInstance, s, main s Q haff x hx hwi⟩

end LateralTheory.E.EtaleNeighbourhoodSystem
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf

namespace LateralTheory.E.StrictHenselianLocalization
open LateralTheory.E.StrictHenselianNeighbourhood

lemma isUnit_of_forall_prime {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (y : R)
    (h : ∀ p : PrimeSpectrum S, ψ y ∉ p.asIdeal) : IsUnit (ψ y) := by
  by_contra hu
  obtain ⟨M, hM, hyM⟩ := exists_max_ideal_of_mem_nonunits hu
  exact h ⟨M, hM.isPrime⟩ hyM

theorem key {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left) (hP : IsPtNb U x Ω s D c V a l e t)
    (j : J) (y : D.obj j) (hy : (Spec.preimage (l j)).hom y ≠ 0) :
    ∃ (n : J) (f : j ⟶ n), IsUnit (D.map f y) := by
  obtain ⟨-, he, hl, hcomp, -, hlc, hcof, heq⟩ := hP
  have _ : ∀ j, IsIso (e j) := he
  let O : (Sp (D.obj j)).Opens := PrimeSpectrum.basicOpen y
  have hrange : Set.range (l j).base ⊆ Set.range O.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [← Spec.map_preimage (l j)]
    show y ∉ Ideal.comap (Spec.preimage (l j)).hom q.asIdeal
    rw [hq, Ideal.mem_comap, Ideal.mem_bot]
    exact hy
  have : Etale (V j).hom := (V j).prop
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ e j ≫ (V j).hom) (by
    show Etale (O.ι ≫ e j ≫ (V j).hom); infer_instance)
  let b : U' ⟶ U := MorphismProperty.Over.homMk (O.ι ≫ e j ≫ (a j).left) (by
    have hw : (a j).left ≫ U.hom = (V j).hom := MorphismProperty.Over.w (a j)
    show _ = O.ι ≫ e j ≫ (V j).hom
    exact (Category.assoc _ _ _).trans (congrArg (O.ι ≫ ·) ((Category.assoc _ _ _).trans (congrArg (e j ≫ ·) hw)))) trivial
  have hOI : IsOpenImmersion O.ι := inferInstance
  let l' := IsOpenImmersion.lift O.ι (l j) hrange
  have hl' : l' ≫ O.ι = l j := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨k, g, hg', hlg'⟩ : ∃ (k : J) (g : (V k).left ⟶ (O : Scheme)),
      g ≫ O.ι ≫ e j ≫ (a j).left = (a k).left ∧ l k ≫ e k ≫ g = l' := by
    obtain ⟨k, g, hg, hlg⟩ := hcof U' b l' (by
      show l' ≫ (O.ι ≫ e j ≫ (a j).left) = s
      rw [← Category.assoc, hl', hl j])
    exact ⟨k, g, hg, hlg⟩
  clear_value b U' l'
  let m := IsFiltered.max j k
  let f1 : j ⟶ m := IsFiltered.leftToMax j k
  let f2 : k ⟶ m := IsFiltered.rightToMax j k
  have h1 := hlc j m f1
  have h2 := hlc k m f2
  obtain ⟨n, f3, h3⟩ := heq (V j) (a j) m
    (inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom) ≫ e j)
    (inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map f2).hom) ≫ e k ≫ g ≫ O.ι ≫ e j)
    (by simp only [Category.assoc]; rw [hcomp j m f1, IsIso.inv_hom_id_assoc])
    (by simp only [Category.assoc]; rw [hg', hcomp k m f2, IsIso.inv_hom_id_assoc])
    (by
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% hlg', reassoc_of% hl'])
  simp only [IsIso.hom_inv_id_assoc] at h3
  have hfac : Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom) =
      (Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f2).hom) ≫ e k ≫ g) ≫ O.ι := by
    rw [← cancel_mono (e j)]
    simpa only [Category.assoc] using h3
  refine ⟨n, f1 ≫ f3, ?_⟩
  rw [D.map_comp, CommRingCat.comp_apply]
  apply isUnit_of_forall_prime (D.map f3).hom
  intro p
  have hp : (Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom)).base p ∈
      Set.range O.ι.base := by
    rw [hfac]; exact ⟨_, rfl⟩
  rw [Scheme.Opens.range_ι] at hp
  exact hp

theorem LeafSHLoc_of : LeafSHLoc := by
  intro B U x Ω _ _ s J _ _ D c hc V a l e t hP
  have hunit : ∀ (j : J) (y : D.obj j), (Spec.preimage (l j)).hom y ≠ 0 → IsUnit (c.ι.app j y) := by
    intro j y hy
    obtain ⟨n, f, hf⟩ := key U x Ω s D c V a l e t hP j y hy
    have h : c.ι.app j y = c.ι.app n (D.map f y) := by
      rw [← c.w f]; rfl
    rw [h]; exact hf.map _
  have hrep : ∀ z : c.pt, ∃ (j : J) (y : D.obj j), c.ι.app j y = z := fun z =>
    Concrete.isColimit_exists_rep D hc z
  have : Nontrivial c.pt := by
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' : c.ι.app j 0 = c.ι.app j 1 := by rw [map_zero, map_one]; exact h
    obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc _ _ h'
    have := congrArg (Spec.preimage (l k)).hom hfg
    rw [map_zero, map_one, map_zero, map_one] at this
    exact zero_ne_one this
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨j, y, rfl⟩ := hrep z
  by_cases hy : (Spec.preimage (l j)).hom y = 0
  · right
    have h1 : (Spec.preimage (l j)).hom (1 - y) ≠ 0 := by
      rw [map_sub, map_one, hy, sub_zero]; exact one_ne_zero
    have := hunit j (1 - y) h1
    rwa [map_sub, map_one] at this
  · left; exact hunit j y hy

end LateralTheory.E.StrictHenselianLocalization
end
