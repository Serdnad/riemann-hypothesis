module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle047
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
import Mathlib.Algebra.AffineMonoid.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.PUnit
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.IsoOverField

theorem eSec_pullback_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec ((Over.pullback p).obj G) ≫ pullback.fst G.hom p = p ≫ eSec G := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq]
  erw [ExtUnique.pullback_map_left_fst, ← Category.assoc, ← pullback.condition]
  simp

theorem isAbelianScheme_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) :=
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

variable {U' U S : Scheme.{0}} (k : U' ⟶ U) (j : U ⟶ S)

noncomputable def toBase (A : Over S) : (Over.mk (k ≫ j) ⊗ A).left ⟶ pullback A.hom j :=
  pullback.lift (snd (Over.mk (k ≫ j)) A).left ((fst (Over.mk (k ≫ j)) A).left ≫ k)
    (by rw [Over.w, Category.assoc]; exact (Over.w (fst (Over.mk (k ≫ j)) A)).symm)

theorem toBase_fst (A : Over S) : toBase k j A ≫ pullback.fst A.hom j = (snd (Over.mk (k ≫ j)) A).left :=
  pullback.lift_fst _ _ _

theorem toBase_snd (A : Over S) : toBase k j A ≫ pullback.snd A.hom j = (fst (Over.mk (k ≫ j)) A).left ≫ k :=
  pullback.lift_snd _ _ _

theorem isPullback_snd (T A : Over S) : IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
  (IsPullback.of_hasPullback T.hom A.hom).flip

theorem isPullback_toBase (A : Over S) :
    IsPullback (toBase k j A) (fst (Over.mk (k ≫ j)) A).left (pullback.snd A.hom j) k := by
  refine IsPullback.of_right ?_ (toBase_snd k j A) (IsPullback.of_hasPullback A.hom j)
  rw [toBase_fst]
  exact isPullback_snd (Over.mk (k ≫ j)) A

theorem exists_iso_over [Flat k] [Surjective k] [QuasiCompact k] [Mono j] (A B : Over S) [GrpObj A] [GrpObj B]
    (φ : Over.mk (k ≫ j) ⊗ A ≅ Over.mk (k ≫ j) ⊗ B) (hφ : φ.hom ≫ fst _ _ = fst _ _)
    (h₁ : lift (𝟙 (Over.mk (k ≫ j))) (1 : Over.mk (k ≫ j) ⟶ A) ≫ φ.hom ≫ snd _ _ = 1)
    (κ : Over.mk (k ≫ j) ⟶ Over.mk j) (g : Over.mk j ⊗ A ⟶ B) (hg : κ ▷ A ≫ g = φ.hom ≫ snd _ _) :
    ∃ f : (Over.pullback j).obj A ≅ (Over.pullback j).obj B,
      η[(Over.pullback j).obj A] ≫ f.hom = η[(Over.pullback j).obj B] ∧
      toBase k j A ≫ f.hom.left ≫ pullback.fst B.hom j = (φ.hom ≫ snd _ _).left := by
  have hκ : κ.left = k := (cancel_mono j).1 (Over.w κ)
  let s : pullback A.hom j ⟶ (Over.mk j ⊗ A).left := (pullbackSymmetry A.hom j).hom
  have s₁ : s ≫ (fst (Over.mk j) A).left = pullback.snd A.hom j := pullbackSymmetry_hom_comp_fst _ _
  have s₂ : s ≫ (snd (Over.mk j) A).left = pullback.fst A.hom j := pullbackSymmetry_hom_comp_snd _ _
  have hs : toBase k j A ≫ s = (κ ▷ A).left := by
    refine (isPullback_snd (Over.mk j) A).hom_ext ?_ ?_
    · rw [Category.assoc, s₂, toBase_fst, ← Over.comp_left, whiskerRight_snd]
    · rw [Category.assoc, s₁, toBase_snd, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hκ]
  have hw : (s ≫ g.left) ≫ B.hom = pullback.snd A.hom j ≫ j := by
    rw [Category.assoc, Over.w, ← s₁, Category.assoc]
    exact congrArg (s ≫ ·) (Over.w (fst (Over.mk j) A)).symm
  let f : (Over.pullback j).obj A ⟶ (Over.pullback j).obj B :=
    Over.homMk (pullback.lift (s ≫ g.left) (pullback.snd A.hom j) hw) (pullback.lift_snd _ _ _)
  have f₁ : f.left ≫ pullback.fst B.hom j = s ≫ g.left := pullback.lift_fst _ _ _
  have f₂ : f.left ≫ pullback.snd B.hom j = pullback.snd A.hom j := pullback.lift_snd _ _ _
  have key : toBase k j A ≫ f.left ≫ pullback.fst B.hom j = (φ.hom ≫ snd _ _).left := by
    rw [f₁, ← Category.assoc, hs, ← Over.comp_left, hg]
  have hφ' : φ.hom.left ≫ (fst (Over.mk (k ≫ j)) B).left = (fst (Over.mk (k ≫ j)) A).left := by
    rw [← Over.comp_left, hφ]
  have sq : toBase k j A ≫ f.left = φ.hom.left ≫ toBase k j B := by
    apply pullback.hom_ext
    · rw [Category.assoc, key, Category.assoc, toBase_fst, Over.comp_left]
    · rw [Category.assoc, f₂, Category.assoc, toBase_snd, toBase_snd, ← Category.assoc, hφ']
  have pb : IsPullback (toBase k j A) φ.hom.left f.left (toBase k j B) := by
    refine IsPullback.of_bot ?_ sq (isPullback_toBase k j B)
    rw [hφ', f₂]
    exact isPullback_toBase k j A
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (toBase k j B) :=
    MorphismProperty.of_isPullback (isPullback_toBase k j B).flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hi : IsIso f.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0}) pb.flip hQ
      (inferInstanceAs (IsIso ((Over.forget S).map φ.hom)))
  have : IsIso ((Over.forget U).map f) := hi
  have : IsIso f := isIso_of_reflects_iso f (Over.forget U)
  refine ⟨asIso f, ?_, key⟩
  have : Epi k := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have one : ∀ (G : Over S) [GrpObj G], (1 : Over.mk (k ≫ j) ⟶ G).left = (k ≫ j) ≫ eSec G := fun G _ => by
      rw [Hom.one_def, Over.comp_left]
      congr 1
    have e : (lift (𝟙 (Over.mk (k ≫ j))) (1 : Over.mk (k ≫ j) ⟶ A)).left ≫ toBase k j A =
        k ≫ eSec ((Over.pullback j).obj A) := by
      apply pullback.hom_ext
      · rw [Category.assoc, toBase_fst, ← Over.comp_left, lift_snd, one, Category.assoc, Category.assoc]
        exact congrArg (k ≫ ·) (eSec_pullback_fst j A).symm
      · rw [Category.assoc, toBase_snd, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc]
        exact (Category.id_comp _).trans ((Category.comp_id k).symm.trans
          (congrArg (k ≫ ·) (Over.w η[(Over.pullback j).obj A]).symm))
    refine (cancel_epi k).1 ?_
    change k ≫ (eSec ((Over.pullback j).obj A) ≫ f.left) ≫ pullback.fst B.hom j =
      k ≫ eSec ((Over.pullback j).obj B) ≫ pullback.fst B.hom j
    rw [eSec_pullback_fst, Category.assoc, ← Category.assoc k, ← e, Category.assoc, key, ← Over.comp_left, h₁,
      one, Category.assoc]
  · exact (Over.w _).trans (Over.w _).symm

theorem exists_iso_over_dvr : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (P P' : PolAV (Sp V)) (C : Type) [Field C] [Algebra (FractionRing V) C] (φ : TF (R := V) C ⊗ P.A ≅ TF (R := V) C ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (TF (R := V) C)) (1 : TF (R := V) C ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (TF (R := V) C) P.A).left) (P'.L.pull (φ.hom ≫ snd (TF (R := V) C) P'.A).left) → ∀ (κ : TF (R := V) C ⟶ TK V) (g : TK V ⊗ P.A ⟶ P'.A), κ ▷ P.A ≫ g = φ.hom ≫ snd _ _ → ∃ Ψ : P.A ≅ P'.A, IsMonHom Ψ.hom ∧ φ.hom ≫ snd _ _ = snd _ _ ≫ Ψ.hom ∧ LBIso P.L (P'.L.pull Ψ.hom.left) := by
  intro hl _ V _ _ _ P P' C _ _ φ hφ h₁ hL κ g hg
  have : Flat (jFK (R := V) C) := FieldBaseChange.flat_spMap (algebraMap (FractionRing V) C)
  have : Surjective (jFK (R := V) C) := FieldBaseChange.surjective_spMap (algebraMap (FractionRing V) C)
  have : QuasiCompact (jFK (R := V) C) := by
    have : IsAffine (TK V).left := inferInstanceAs (IsAffine (Spec _))
    infer_instance
  have : Mono (jK V) := by
    have : IsPreimmersion (jK V) := IsPreimmersion.of_isLocalization (nonZeroDivisors V)
    infer_instance
  obtain ⟨f, hf₁, hf⟩ := exists_iso_over (jFK (R := V) C) (jK V) P.A P'.A φ hφ h₁ κ g hg
  have hm : IsMonHom f.hom := hl.rigidity _ _ _ (isAbelianScheme_pullback _ _ P.isAb)
    (isAbelianScheme_pullback _ _ P'.isAb) f.hom hf₁
  have hm' : IsMonHom f.inv := inferInstance
  have semi_of_ab {S : Scheme.{0}} (B : Over S) [GrpObj B] (h : IsAbelianScheme B) : IsSemiAbelian B := by
    have := h.proper
    refine ⟨h.comm, h.smooth, inferInstance, inferInstance, h.geomConnected, ?_⟩
    intro Ω _ _ p
    have hab := isAbelianScheme_pullback p B h
    refine ⟨{ X := PUnit, B := _, isAbelian := hab, q := 𝟙 _, q_hom := inferInstance
              q_flat := ?_, q_surjective := ?_, q_quasiCompact := ?_
              i := toUnit _ ≫ η, i_hom := ?_, isKernel := ?_ }⟩
    · rw [Over.id_left]; infer_instance
    · rw [Over.id_left]; infer_instance
    · rw [Over.id_left]; infer_instance
    · have := hab.comm; infer_instance
    · have hident : 𝟙 (splitTorus (Spec (CommRingCat.of Ω)) PUnit) = 1 := by
        rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
        congr 1
      have : IsIso (toUnit (splitTorus (Spec (CommRingCat.of Ω)) PUnit)) := ⟨η, hident.symm, toUnit_unique _ _⟩
      exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  have hs := semi_of_ab P.A P.isAb
  have hs' := semi_of_ab P'.A P'.isAb
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := homExtension_semiAbelian_dvr_unconditional V (FractionRing V) P.A P'.A hs hs' f.hom hm
  obtain ⟨G, ⟨-, eG⟩, -⟩ := homExtension_semiAbelian_dvr_unconditional V (FractionRing V) P'.A P.A hs' hs f.inv hm'
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing V (FractionRing V)
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P'.isAb.smooth
  have := P'.isAb.proper
  have : IsIso F := ExtUnique.isIso_of_pullback (jK V) f F G eF eG
  have e : φ.hom ≫ snd _ _ = snd _ _ ≫ F := by
    apply Over.OverMorphism.ext
    rw [← hf, ← eF, Over.comp_left, ← toBase_fst (jFK (R := V) C) (jK V) P.A, Category.assoc]
    exact congrArg (_ ≫ ·) (ExtUnique.pullback_map_left_fst (jK V) F)
  refine ⟨asIso F, hF, e, ?_⟩
  have pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL F
  have hN := pull_isLB P'.isLB F.left
  have hβ : jFK (R := V) C ≫ jK V =
      spMap ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V))) := (Spec.map_comp _ _).symm
  refine IsoDescent.lbIso_of_field V C ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V)))
    ((algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))) P.A P.isAb _
    (snd (TF (R := V) C) P.A).left (fst (TF (R := V) C) P.A).left (hβ ▸ isPullback_snd (TF (R := V) C) P.A)
    P.L (P'.L.pull F.left) P.isLB hN ?_ ?_
  all_goals
    obtain ⟨Pic, groups, cl, pl, iso_iff, gen_iff, -, comp, linComb, -⟩ := CechPicMul.exists_picardGroup
    let _ := groups
    have pull_class {S T : Scheme.{0}} (f : T ⟶ S) {L : LB S} (hL : L.IsLB) :
        (L.pull f).IsLB ∧ cl (L.pull f) = pl f (cl L) := by
      simpa only [Fintype.prod_unique, zpow_one] using
        linComb S T L hL PUnit (fun _ => f) (fun _ => 1)
  · have eF' : eSec P.A ≫ F.left = eSec P'.A := congrArg (·.left) (IsMonHom.one_hom F)
    apply (iso_iff _ _ _ (pull_isLB P.isLB _) (pull_isLB hN _)).1
    rw [(gen_iff _ _ (pull_isLB P.isLB _)).2 P.rigid,
      (pull_class _ hN).2, (pull_class _ P'.isLB).2, ← comp, eF',
      ← (pull_class _ P'.isLB).2, (gen_iff _ _ (pull_isLB P'.isLB _)).2 P'.rigid]
  · apply (iso_iff _ _ _ (pull_isLB P.isLB _) (pull_isLB hN _)).1
    have hL' := (iso_iff _ _ _ (pull_isLB P.isLB _) (pull_isLB P'.isLB _)).2 hL
    rw [(pull_class _ P'.isLB).2, e] at hL'
    rw [hL', (pull_class _ hN).2, (pull_class _ P'.isLB).2, ← comp, Over.comp_left]

end GlobalTheory.IsoOverField
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace SemiAbTorsionCount

theorem card_pow_eq_one_of_extension {T G B : Type} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hi : Function.Injective i) (hk : ∀ x, q x = 1 ↔ ∃ t, i t = x)
    (hq : Function.Surjective q) (n : ℕ) (hT : ∀ t : T, ∃ s : T, s ^ n = t) :
    Nat.card {x : G // x ^ n = 1} =
      Nat.card {b : B // b ^ n = 1} * Nat.card {t : T // t ^ n = 1} := by
  let K : Subgroup G := (powMonoidHom n : G →* G).ker
  let f : K →* B := q.comp K.subtype
  have h0 : Nat.card {x : G // x ^ n = 1} = Nat.card K := rfl
  have h1 : Nat.card {b : B // b ^ n = 1} = Nat.card f.range := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ⟨fun hb => ?_, ?_⟩)
    · obtain ⟨x, rfl⟩ := hq b
      obtain ⟨t, ht⟩ := (hk (x ^ n)).1 (by rw [map_pow, hb])
      obtain ⟨s, rfl⟩ := hT t
      refine ⟨⟨x / i s, ?_⟩, ?_⟩
      · change (x / i s) ^ n = 1
        rw [div_pow, ← map_pow, ht, div_self']
      · change q (x / i s) = q x
        rw [map_div, (hk _).2 ⟨s, rfl⟩, div_one]
    · rintro ⟨x, rfl⟩
      have hx : x.1 ^ n = 1 := x.2
      change q x.1 ^ n = 1
      rw [← map_pow, hx, map_one]
  have h2 : Nat.card {t : T // t ^ n = 1} = Nat.card f.ker := by
    refine Nat.card_eq_of_bijective (fun t => ⟨⟨i t.1, ?_⟩, (hk _).2 ⟨t.1, rfl⟩⟩) ⟨?_, ?_⟩
    · change i t.1 ^ n = 1
      rw [← map_pow, t.2, map_one]
    · intro a b h
      exact Subtype.ext (hi (congrArg (fun z : f.ker => z.1.1) h))
    · rintro ⟨⟨x, hx⟩, hx'⟩
      obtain ⟨t, rfl⟩ := (hk x).1 hx'
      have hx₁ : i t ^ n = 1 := hx
      exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩
  rw [h0, h1, h2, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem nonempty_hom_mulEquiv_pi (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (M : Type) [CommGroup M] :
    Nonempty ((Multiplicative X →* M) ≃* (Fin (Module.finrank ℤ X) → M)) := by
  let b := Module.finBasis ℤ X
  let ev : (Multiplicative X →* M) →* (Fin (Module.finrank ℤ X) → M) :=
    { toFun := fun t j => t (Multiplicative.ofAdd (b j))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨MulEquiv.ofBijective ev ⟨fun s t h => ?_, fun v => ?_⟩⟩
  · have : (MonoidHom.toAdditiveRight s).toIntLinearMap = (MonoidHom.toAdditiveRight t).toIntLinearMap :=
      b.ext fun j => congrArg Additive.ofMul (congrFun h j)
    ext x
    exact congrArg Additive.toMul (DFunLike.congr_fun this x)
  · refine ⟨AddMonoidHom.toMultiplicativeLeft
      (b.constr ℤ (fun j => Additive.ofMul (v j))).toAddMonoidHom, funext fun j => ?_⟩
    exact congrArg Additive.toMul (b.constr_basis ℤ (fun j => Additive.ofMul (v j)) j)

theorem nonempty_torus_points_mulEquiv (k : Type) [Field k] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] :
    Nonempty ((𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) ≃* (Fin (Module.finrank ℤ X) → kˣ)) := by
  obtain ⟨e₂⟩ := nonempty_hom_mulEquiv_pi X Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ
  let e₃ : Γ((𝟙_ (Over (Sp k))).left, ⊤) ≃+* k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  exact ⟨((splitTorusPointsEquiv (Sp k) X (𝟙_ (Over (Sp k)))).trans e₂).trans
    (MulEquiv.piCongrRight fun _ => Units.mapEquiv e₃.toMulEquiv)⟩

theorem divisible_and_card {k : Type} [Field k] [IsAlgClosed k] {T : Type} [Group T] {t : ℕ}
    (e : T ≃* (Fin t → kˣ)) (N : ℕ) (hN : (N : k) ≠ 0) :
    (∀ x : T, ∃ s : T, s ^ N = x) ∧ Nat.card {x : T // x ^ N = 1} = N ^ t := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  haveI : NeZero N := ⟨hN0⟩
  haveI : NeZero (N : k) := ⟨hN⟩
  constructor
  · intro x
    have : ∀ u : kˣ, ∃ s : kˣ, s ^ N = u := fun u => by
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : k) (Nat.pos_of_ne_zero hN0)
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [zero_pow hN0] at hz
        exact u.ne_zero hz.symm
      exact ⟨Units.mk0 z hz0, Units.ext hz⟩
    choose r hr using this
    refine ⟨e.symm fun j => r (e x j), e.injective ?_⟩
    rw [map_pow, e.apply_symm_apply]
    exact funext fun j => hr _
  · have h1 : Nat.card {x : T // x ^ N = 1} = Nat.card (Fin t → rootsOfUnity N k) := by
      refine Nat.card_congr ((e.toEquiv.subtypeEquiv (q := fun v => ∀ j, v j ∈ rootsOfUnity N k)
        fun x => ?_).trans Equiv.subtypePiEquivPi)
      rw [← e.map_eq_one_iff, map_pow, funext_iff]
      rfl
    rw [h1, Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_eq_fintype_card,
      Fintype.card_fin]

theorem dim_eq {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g g' : ℕ)
    (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' E.B.hom) :
    g = g' + @Module.finrank ℤ E.X _ E.addCommGroup.toAddCommMonoid _ := by
  letI := E.addCommGroup
  letI := E.grpB
  have := E.free
  have := E.finite
  obtain ⟨y⟩ : Nonempty ↥(Sp k) := inferInstance
  have := E.i_hom
  have := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim E.q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ E.X :=
    H1.dim_base (E.isKernel.map (Over.forget _)) d₁ (H1.torus_dim (Sp k) E.X) (eSec _ y)
      ((congrArg (fun f => f.left y ∈ W) (IsMonHom.one_hom E.i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w E.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

end SemiAbTorsionCount

open SemiAbTorsionCount

theorem card_torsion_mul_card_toric_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (T : TorusExtension G) (g N : ℕ), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1} * Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ T.i} = N ^ (2 * g) := by
  intro k _ _ G _ E g N hG dG hN
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := hG.comm
  haveI := E.q_surjective
  haveI := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1
  have hk := E.isKernel
  obtain ⟨g', dB⟩ := GlobalTheory.AbelianDim.exists_relDim k E.B E.isAbelian
  have hg := dim_eq G E g g' dG dB
  obtain ⟨e⟩ := nonempty_torus_points_mulEquiv k E.X
  obtain ⟨hdiv, hcard⟩ := divisible_and_card e N hN
  have hB := GlobalTheory.T.card_torsion_eq_pow_two_mul_dim k E.B g' N E.isAbelian dB hN
  let i := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  have h1 := card_pow_eq_one_of_extension i (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))) hi
    (fun x => ⟨fun hx => ?_, ?_⟩) (fun x => ?_) N hdiv
  · have h2 : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ E.i} =
        N ^ Module.finrank ℤ E.X := by
      rw [← hcard]
      refine (Nat.card_eq_of_bijective
        (fun t => ⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩) ⟨?_, ?_⟩).symm
      · intro a b h
        exact Subtype.ext (hi (congrArg Subtype.val h))
      · rintro ⟨x, hx, t, rfl⟩
        have hx₁ : i t ^ N = 1 := hx
        exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩
    rw [h2, h1, hB, hcard, hg]
    ring
  · have hx' : x ≫ E.q = 1 := hx
    exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
  · rintro ⟨t, rfl⟩
    change (t ≫ E.i) ≫ E.q = 1
    rw [Category.assoc, hk.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  · obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := k) E.q.left x.left
    refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp.symm⟩
    rw [← Over.w E.q, ← Category.assoc, ← hp]
    exact Over.w x

end GlobalTheory
end
