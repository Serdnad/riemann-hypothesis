module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle098
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.FormBundleKer


open GlobalTheory.CechPic in
theorem eq_one_of_slice_trivial : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.KTriv G L → ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro W S G A _ _ _ _ pr L P hpr huniv hL hP hsym hbi hLP hK T x hx
  let p : ∀ {T' : Over S}, (T' ⟶ A) → (T' ⟶ A) → Pic T'.left := fun a b => pull (lift a b).left (cls P hP)
  have padd : ∀ {T' : Over S} (a a' b : T' ⟶ A), p (a * a') b = p a b + p a' b := fun {T'} a a' b => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi T' a a' b).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [p]
    abel
  have psym : ∀ {T' : Over S} (a b : T' ⟶ A), p a b = p b a := fun {T'} a b => by
    have e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
      (cls_eq_iff hP (pull_isLB hP _)).2 hsym
    have k : (lift b a).left ≫ (lift (snd A A) (fst A A)).left = (lift a b).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    show pull (lift a b).left (cls P hP) = pull (lift b a).left (cls P hP)
    rw [← k, pull_comp, ← e]
  have pone : ∀ {T' : Over S} (b : T' ⟶ A), p 1 b = 0 := fun b => by
    have := padd 1 1 b
    rw [_root_.mul_one] at this
    exact left_eq_add.1 this
  have px : ∀ {T' : Over S} (τ : T' ⟶ T) (y : T' ⟶ A), p (τ ≫ x) y = 0 := fun τ y => by
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 hx
    rw [cls_pull hP] at e
    have k : (lift y τ).left ≫ (lift (snd A T ≫ x) (fst A T)).left = (lift (τ ≫ x) y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
    show pull (lift (τ ≫ x) y).left (cls P hP) = 0
    rw [← k, pull_comp, e, map_zero]
  have hl : ∀ {T' : Over S} (z : T' ⟶ G), pull z.left (cls L hL) =
      ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • p (z ≫ pr uv.1) (z ≫ pr uv.2) := fun z => by
    have e := (cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hLP
    rw [cls_linComb hP] at e

    rw [e, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift]
  obtain ⟨x', hx', -⟩ := huniv T fun v => if v = 0 then x else 1
  have pz : ∀ u (y : T ⊗ G ⟶ A), p ((fst T G ≫ x') ≫ pr u) y = 0 := fun u y => by
    rw [Category.assoc, hx']
    split_ifs
    · exact px _ _
    · rw [MonObj.comp_one]; exact pone _
  have key : pull (Out.translPt G x').left (cls L hL) = pull (snd T G).left (cls L hL) := by
    have e : Out.translPt G x' = (fst T G ≫ x') * snd T G := rfl
    rw [hl, hl, e]
    refine Finset.sum_congr rfl fun uv _ => ?_
    have := hpr uv.1
    have := hpr uv.2
    rw [MonObj.mul_comp, MonObj.mul_comp, padd, pz, zero_add, psym, padd, pz, zero_add, psym]
  have H : KerPow.HasGen L (K := Fin 2) ![(Out.translPt G x').left, (snd T G).left] ![1, -1] := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, key, one_smul, neg_smul, add_neg_cancel]
  have h1 : x' = 1 := KerPow.eq_one_of_locGen hK x' fun _ => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩
  have h0 := hx' 0
  have := hpr 0
  rw [h1, MonObj.one_comp, if_pos rfl] at h0
  exact h0.symm

end GlobalTheory.FormBundleKer
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.RigidifyTwist

open CechPic

theorem pull_cls_eq_zero {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (r : Z ⟶ X) (i : L.ι)
    (hi : ∀ z, r z ∈ L.U i) : CechPic.pull r (cls L hL) = 0 := by
  rw [← cls_pull hL r (pull_isLB hL r), cls_eq_zero_iff]
  refine (iso_triv_iff _).1 (iso_of_chart (pull_isLB hL r) ⟨fun _ _ => i, fun _ y _ => mem_pull.2 (hi y), ?_⟩)
  intro y p q hp hq
  rw [gm_pull_g L r (𝟙 Z) y (fun _ => i) (fun _ => i) (mem_pull.2 (hi y)) (mem_pull.2 (hi y))]
  have hy : (𝟙 Z ≫ r) y ∈ L.U i := by
    simpa using hi y
  rw [gm_self hL _ y hy]
  exact map_one _

theorem eSec_hom {S : Scheme.{0}} (A : Over S) [GrpObj A] : eSec A ≫ A.hom = 𝟙 S := by
  unfold eSec
  exact (Over.w _).trans rfl

private theorem cls_pull_tens_dual_eq_sub {S Y : Scheme.{0}} (A : Over S) (M : LB A.left) (hM : M.IsLB) (N : LB S)
    (hN : N.IsLB) (f : Y ⟶ A.left) (h : ((tens M (dual (N.pull A.hom))).pull f).IsLB) :
    cls _ h = pull f (cls M hM) - pull (f ≫ A.hom) (cls N hN) := by
  have hP := pull_isLB hN A.hom
  rw [cls_pull (isLB_tens hM (isLB_dual hP)) f h, cls_tens hM (isLB_dual hP), cls_dual hP,
    cls_pull hN A.hom, map_add, map_neg, pull_comp, sub_eq_add_neg]

private theorem pGen_of_isGen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) : PGen w := by
  intro Y f y j1 j2 k1 k2 h1 h2 h3 h4
  unfold gw
  have m1 : f y ∈ (L.pull F).U (fun _ => j1) := mem_pull.2 h1
  have m2 : f y ∈ (L.pull F).U (fun _ => j2) := mem_pull.2 h2
  have hV : f y ∈ ((L.pull F).div L').U (fun _ => j1, k1) ⊓ ((L.pull F).div L').U (fun _ => j2, k2) :=
    ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
  have e := congrArg (gm f y _) (hw (fun _ => j1, k1) (fun _ => j2, k2))
  rw [map_mul, gm_res f y _ hV, gm_res f y _ hV, gm_div' (L.pull F) L' f y _ _ ⟨m1, h3⟩ ⟨m2, h4⟩,
    gm_pull_g L F f y _ _ m1 m2] at e
  exact e

private theorem lbIso_tens_dual_pull_eSec_restrict {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : LB A.left) (hM : M.IsLB)
    (U : S.Opens) (j : (M.pull (eSec A)).ι) (hU : U ≤ (M.pull (eSec A)).U j) :
    LBIso ((tens M (dual ((M.pull (eSec A)).pull A.hom))).pull (A.hom ⁻¹ᵁ U).ι) (M.pull (A.hom ⁻¹ᵁ U).ι) := by
  have hN : (M.pull (eSec A)).IsLB := pull_isLB hM _
  have hT := isLB_tens hM (isLB_dual (pull_isLB hN A.hom))
  have hz : ∀ z : U.toScheme, U.ι z ∈ (M.pull (eSec A)).U j := fun z => by
    exact hU z.2
  refine (cls_eq_iff (pull_isLB hT _) (pull_isLB hM _)).1 ?_
  rw [cls_pull_tens_dual_eq_sub A M hM _ hN, ← morphismRestrict_ι, pull_comp, pull_cls_eq_zero hN U.ι j hz, map_zero,
    sub_zero, cls_pull hM]

theorem exists_rigidified_twist : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (M : LB A.left), M.IsLB → ∃ M' : LB A.left, M'.IsLB ∧ Out.Rigidified A M' ∧ (∀ p : S, ∃ U : S.Opens, p ∈ U ∧ LBIso (M'.pull (A.hom ⁻¹ᵁ U).ι) (M.pull (A.hom ⁻¹ᵁ U).ι)) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (X : Scheme.{0}) (φ : X ⟶ A.left) (π : X ⟶ Sp K), φ ≫ A.hom = π ≫ x → LBIso (M'.pull φ) (M.pull φ)) ∧ (IsProper A.hom → Out.RelAmple A M → Out.RelAmple A M') := by
  intro S A _ M hM
  have hN : (M.pull (eSec A)).IsLB := pull_isLB hM _
  have hP : ((M.pull (eSec A)).pull A.hom).IsLB := pull_isLB hN _
  have hT : (tens M (dual ((M.pull (eSec A)).pull A.hom))).IsLB := isLB_tens hM (isLB_dual hP)
  refine ⟨tens M (dual ((M.pull (eSec A)).pull A.hom)), hT, ?_, ?_, ?_, ?_⟩
  · unfold Out.Rigidified
    refine (cls_eq_zero_iff (pull_isLB hT _)).1 ?_
    rw [cls_pull_tens_dual_eq_sub A M hM _ hN, eSec_hom A, pull_id, cls_pull hM (eSec A) hN, sub_self]
  · intro p
    obtain ⟨j, hj⟩ := exists_chart hN p
    exact ⟨_, hj, lbIso_tens_dual_pull_eSec_restrict A M hM _ j le_rfl⟩
  · intro K _ x X φ π hφ
    obtain ⟨j, hj⟩ := exists_chart hN (x (Classical.arbitrary (Sp K)))
    have hx : ∀ z, x z ∈ (M.pull (eSec A)).U j := fun z => by
      rw [Subsingleton.elim z (Classical.arbitrary _)]
      exact hj
    refine (cls_eq_iff (pull_isLB hT _) (pull_isLB hM _)).1 ?_
    rw [cls_pull_tens_dual_eq_sub A M hM _ hN, hφ, pull_comp, pull_cls_eq_zero hN x j hx, map_zero, sub_zero, cls_pull hM]
  · intro hpr hamp
    have := hpr
    refine AmpleLocal.relAmple_of_locally S A _ hT inferInstance inferInstance fun s => ?_
    obtain ⟨j, hj⟩ := exists_chart hN s
    obtain ⟨V, hV, hsV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hj
    obtain ⟨w, hw⟩ := lbIso_tens_dual_pull_eSec_restrict A M hM V j hVle
    have hpw : PGen w := pGen_of_isGen w hw
    exact ⟨V, hsV, relAmple_pull (A' := Over.mk (A.hom ∣_ V)) (isPullback_morphismRestrict A.hom V).flip hM
      (pull_isLB hT _) (w := w) hpw V hV (fun y => y.2) hamp⟩

end GlobalTheory.RigidifyTwist
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.RigidLocal

open GlobalTheory.CechPic

private theorem surjective_app_of_eq_of_surjective_comp_injective {X S : Scheme.{0}} (f : X ⟶ S) {W V : S.Opens} (e : W = V)
    {R : CommRingCat} (g : Γ(X, f ⁻¹ᵁ W) ⟶ R)
    (h : Function.Surjective (f.app W ≫ g).hom) (hg : Function.Injective g.hom) :
    Function.Surjective (f.app V).hom := by
  subst e
  rw [CommRingCat.hom_comp, RingHom.coe_comp] at h
  exact h.of_comp_left hg

theorem surjective_app_of_pullback_snd {X S : Scheme.{0}} (f : X ⟶ S) (V : S.Opens)
    (h : Function.Surjective (pullback.snd f V.ι).appTop.hom) : Function.Surjective (f.app V).hom := by
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.coe_comp] at h
  have hi : IsIso (pullbackRestrictIsoRestrict f V).hom.appTop :=
    inferInstanceAs (IsIso ((pullbackRestrictIsoRestrict f V).hom.app ⊤))
  have h2 : Function.Surjective (f ∣_ V).appTop.hom :=
    h.of_comp_left (ConcreteCategory.bijective_of_isIso (pullbackRestrictIsoRestrict f V).hom.appTop).1
  rw [morphismRestrict_appTop] at h2
  refine surjective_app_of_eq_of_surjective_comp_injective f V.ι_image_top _ h2 ?_
  exact (ConcreteCategory.bijective_of_isIso
    (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f V ⊤)).op).hom).1

theorem eSec_comp {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] {φ : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (𝟙 S) φ) : eSec A ≫ φ = eSec A' :=
  (GlobalTheory.PolBaseChange.eSec_comm h).trans (Category.id_comp _)

theorem lbIso_of_local : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (φ : A.left ⟶ A'.left), IsAbelianScheme A → L.IsLB → L'.IsLB → Out.Rigidified A L → Out.Rigidified A' L' → IsGrpPullback A A' (𝟙 S) φ → (∀ p : S, ∃ (V B : Scheme.{0}) (x : V ⟶ S) (q : B ⟶ V) (a : B ⟶ A.left), IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsPullback a q A.hom x ∧ LBIso (L.pull a) (L'.pull (a ≫ φ))) → LBIso L (L'.pull φ) := by
  intro hG S A A' _ _ L L' φ hA hL hL' hR hR' hφ hloc
  have hM : (L'.pull φ).IsLB := LB.isLB_pull hL' φ
  have hN : (LB.div L (L'.pull φ)).IsLB := LB.isLB_div hL hM

  have key : ∀ {Y : Scheme.{0}} (g : Y ⟶ A.left),
      (∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull g), t.IsGen) ↔
        GlobalTheory.CechPic.pull g (GlobalTheory.CechPic.cls L hL) = GlobalTheory.CechPic.pull g (GlobalTheory.CechPic.cls _ hM) := by
    intro Y g
    rw [← cls_eq_zero_iff (LB.isLB_pull hN g), cls_pull hN g (LB.isLB_pull hN g), cls_div hL hM hN,
      map_sub, sub_eq_zero]

  have hsec : ∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull (eSec A)), t.IsGen := by
    rw [key]
    have h1 : GlobalTheory.CechPic.pull (eSec A) (GlobalTheory.CechPic.cls L hL) = 0 := by
      rw [← cls_pull hL (eSec A) (LB.isLB_pull hL _)]
      exact (cls_eq_zero_iff _).2 hR
    have h2 : GlobalTheory.CechPic.pull (eSec A') (GlobalTheory.CechPic.cls L' hL') = 0 := by
      rw [← cls_pull hL' (eSec A') (LB.isLB_pull hL' _)]
      exact (cls_eq_zero_iff _).2 hR'
    rw [h1, cls_pull hL' φ hM, ← pull_comp, eSec_comp hφ, h2]

  have hloc' : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull (A.hom ⁻¹ᵁ U).ι), t.IsGen := by
    intro s
    obtain ⟨V, B, x, q, a, hx, hs, hpb, hiso⟩ := hloc s
    refine ⟨x.opensRange, hs, ?_⟩
    rw [key]
    have w : (A.hom ⁻¹ᵁ x.opensRange).ι ≫ A.hom = ((A.hom ∣_ x.opensRange) ≫ x.isoOpensRange.inv) ≫ x := by
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
    obtain ⟨e, he⟩ : ∃ e, e ≫ a = (A.hom ⁻¹ᵁ x.opensRange).ι := ⟨hpb.lift _ _ w, hpb.lift_fst _ _ w⟩
    have ha : GlobalTheory.CechPic.pull a (GlobalTheory.CechPic.cls L hL) = GlobalTheory.CechPic.pull a (GlobalTheory.CechPic.cls _ hM) := by
      have h := (cls_eq_iff (LB.isLB_pull hL a) (LB.isLB_pull hL' (a ≫ φ))).2 hiso
      rw [cls_pull hL a, cls_pull hL' (a ≫ φ), pull_comp] at h
      rw [h, cls_pull hL' φ hM]
    rw [← he, pull_comp, pull_comp, ha]
  have hσ : eSec A ≫ A.hom = 𝟙 S := by
    unfold eSec
    exact (Over.w _).trans rfl
  have hsurj : ∀ U : S.Opens, Function.Surjective (A.hom.app U).hom := fun U =>
    surjective_app_of_pullback_snd A.hom U (surj_snd hG hA (Over.mk U.ι))
  obtain ⟨t, ht⟩ := exists_gen_of_local_of_section A.left S A.hom (eSec A) _ hN hσ hsurj hloc' hsec
  exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 ((cls_div hL hM hN).symm.trans ((cls_eq_zero_iff hN).2 ⟨t, ht⟩)))

end GlobalTheory.RigidLocal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem kTriv_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.KTriv (G i) (M i)) → Out.KTriv A L := by
  intro S I U A _ G _ ψ hU hG L M hL hM hLM hA hGA hK
  rw [GlobalTheory.UU.kTriv_iff_forall]
  intro T x hx
  apply over_ext hU
  intro i T' r
  obtain ⟨y, hy⟩ := exists_lift (hG i).1 (r ≫ x)
  have hpush : pushPt (hG i).1.w y = r ≫ x := by
    ext1
    exact hy.symm
  have hyK : GlobalTheory.UU.InK (G i) (M i) y :=
    GlobalTheory.UU.inK_of_push (hG i) hL (hM i) (hLM i) y (hpush ▸ hx.comp r)
  have hy1 : y = 1 := (GlobalTheory.UU.kTriv_iff_forall.1 (hK i)) T' y hyK
  have hsq : (r ≫ x) * (r ≫ x) = r ≫ x := by
    ext1
    rw [((hG i).2 T' y y (r ≫ x) (r ≫ x) hy hy), hy, hy1, _root_.mul_one]
  have h1 : r ≫ x = 1 := by simpa using hsq
  rw [h1]
  simp

end GlobalTheory.CoverGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.cubicalStructure_and_symmetric_of_cube_gen : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsSemiAbelian G → (IsReduced X ∧ genericPoints X ⊆ abLocus G) → ((∃ t : (Theta G L.L).Gen, t.IsGen) → Nonempty (CubicalStr G L)) ∧ (LBIso L.L (L.L.pull (GrpObj.inv (X := G)).left) → L.IsSymmetric) := by
  first | exact @GlobalTheory.CubeGen.cubical_and_symmetric | exact GlobalTheory.CubeGen.cubical_and_symmetric | (intros; apply GlobalTheory.CubeGen.cubical_and_symmetric <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TransitionUnique

open GlobalTheory.ModelCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isReduced_XF (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).1

theorem map_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} [IsReduced S]
    {t : SAB H S} {r r' : S ⟶ Xo.XF c} (ν : SABMap t Y.oF.t r) (ν' : SABMap t Y.oF.t r')
    (hr : r ≫ pullback.snd _ _ = r' ≫ pullback.snd _ _)
    (hM : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left)
    (hA : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.etaA a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left) : r = r' := open GlobalTheory.ObjPull in by
  let o : Obj D l _ (r ≫ _) :=
    have hL : LBIso t.PP.L (Y.oF.t.PP.L.pull ν.cm.F) := by
      obtain ⟨w, hw, -⟩ := ν.lin
      exact ⟨w, hw⟩
    have hpr := Y.oF.proper
    have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
      (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.PP.L t.PP.L Y.oF.t.PP.isLB t.PP.isLB
      (AbelianSchemeGerms.isAbelianScheme_of_proper Y.oF.t.G Y.oF.t.semi) ν.cart hL
    { t := t
      proper := MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 hpr
      ample := hp.2.1 Y.oF.ample
      ktriv := hp.2.2 Y.oF.ktriv
      eta := fun a => secPull ν.cart (Y.oF.eta a)
      eta_add := fun a c => by rw [Y.oF.eta_add, map_mul]
      eta_ker := fun a ha => by rw [Y.oF.eta_ker a ha, map_one]
      etaA := fun a => secPull ν.cart (Y.oF.etaA a)
      etaA_add := fun a c => by rw [Y.oF.etaA_add, map_mul]
      etaA_ker := fun a => by rw [Y.oF.etaA_ker a, map_one]
      geom := fun k _ _ x β hx => by
        obtain ⟨hdet, I, hI, hA, hM⟩ := Y.oF.geom k (x ≫ r) β (by rw [Category.assoc, hx])
        refine ⟨fun τ => ?_, tateMove (pushEquiv ν.cart (Over.mk x)) (fun c g => ?_) (fun n g g' u hc => ?_) I,
          hI, fun a => ?_, fun a ha => ?_⟩
        · rw [GlobalTheory.LiePull.lieMult_pull _ (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.act t.act ν.cart ν.act k x τ,
            GlobalTheory.LiePull.lieMult_pull _ (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.act t.act ν.cart ν.act k x τ]
          exact hdet τ
        · apply Over.OverMorphism.ext
          show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
          rw [Category.assoc, ν.act, Category.assoc]
        · exact (GlobalTheory.weilIs_grpPullback_of_comm (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.PP.L t.PP.L Y.oF.t.PP.isLB t.PP.isLB
            ν.cart hL (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
        · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull ν.cart _ _).trans (hA a))
        · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull ν.cart _ _).trans (hM a ha)) }
  let n : ObjMap o Y.oF r := ⟨ν, fun _ => secPull_left ν.cart _, fun _ => secPull_left ν.cart _⟩
  have sec_eq {e : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G} {e' : 𝟙_ (Over S) ⟶ t.G}
      (h : e'.left ≫ ν.φ = r ≫ e.left) : e' = secPull ν.cart e := by
    apply Over.OverMorphism.ext
    apply ν.cart.1.hom_ext
    · exact h.trans (secPull_left ν.cart _).symm
    · rw [Over.w, Over.w]
  let n' : ObjMap o Y.oF r' := ⟨ν', fun a => by
      obtain ⟨x, h, h'⟩ := hM a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq h)).symm.trans h', fun a => by
      obtain ⟨x, h, h'⟩ := hA a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq h)).symm.trans h'⟩
  obtain ⟨k, -⟩ := ObjComp.objMap_comp Y.m0 n
  obtain ⟨k', -⟩ := ObjComp.objMap_comp Y.m0 n'
  refine pullback.hom_ext ((Xo.rep S _ ‹_› o).unique ⟨Category.assoc _ _ _, ⟨k⟩⟩ ⟨?_, ⟨k'⟩⟩) hr
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hr, Category.assoc]

end GlobalTheory.TransitionUnique
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_nonzeroLocus_le_open_polarisation_complex : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (O : P₀.A.left.Opens) (y : P₀.A.left), y ∈ O → ∃ (n : ℕ) (σ : (lbPow P₀.L n).Sec), y ∈ Out.nonzeroLocus σ ∧ Out.nonzeroLocus σ ≤ O := by
  first | exact @GlobalTheory.exists_nonzeroLocus_le | exact GlobalTheory.exists_nonzeroLocus_le | (intros; apply GlobalTheory.exists_nonzeroLocus_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.detCond_of_diagonal_action : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → (∀ (a : 𝓞 E) z, u.ex (fun i => ty i (a : E) * z i) = u.ex z ≫ act.act a) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : ℂ →+* K), DetCond D act (spMap β) (β H.rt0) := by
  intro _ _ _ unif E _ _ _ H D P u _ _ act ty _ hty hact K _ _ β
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.AnyUnif.tangent_and_unimodular unif P u
  have hs : Smooth P.A.hom := P.isAb.smooth
  obtain ⟨v, hv, heig⟩ := GlobalTheory.exists_lieBasis_of_holUnif P.A P.L P.g u hs h₁ h₂
  have key : ∀ τ₀ : E →+* ℂ, LieMult act (𝟙 (Sp ℂ)) (τ₀.comp (algebraMap (𝓞 E) E))
      (Nat.card {i // ty i = τ₀}) := fun τ₀ => by
    have h := GlobalTheory.lieMult_of_eigenbasis ℂ (𝓞 E) P.A act P.g v (fun i => (ty i).comp (algebraMap (𝓞 E) E)) hs hv
      (fun i a => heig _ _ (act.hom a) (hact a) i) (τ₀.comp (algebraMap (𝓞 E) E))
    convert h using 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
      ⟨fun e => by rw [e], fun e => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e⟩)
  have hd : DetCond D act (𝟙 (Sp ℂ)) H.rt0 := fun τ => by
    obtain ⟨τ₀, rfl⟩ := GlobalTheory.PeriodPoint.exists_embedding (RingHom.id ℂ) τ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← (hty τ₀).1 h]; exact key τ₀
    · rw [← (hty τ₀).2 h]; exact key τ₀
  have := (GlobalTheory.detCond_iff_of_field_extension E H D _ P.A ℂ K β (𝟙 _) act H.rt0 hs).2 hd
  rwa [Category.comp_id] at this
end
