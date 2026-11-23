module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle025
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem zmod_pow_exists_eq_nsmul_of_nsmul_eq_zero (n J : ℕ) (hn : n ≠ 0) (hJ : 2 ≤ J)
    (t : ZMod (n ^ J)) (ht : n • t = 0) : ∃ s : ZMod (n ^ J), t = n • s := by
  have : NeZero (n ^ J) := ⟨pow_ne_zero _ hn⟩
  have hv : n ^ J ∣ n * t.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]
    exact ht
  obtain ⟨k, hk⟩ := hv
  have h1 : t.val = n * (n ^ (J - 2) * k) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
    rw [hk, show n ^ J = n * (n * n ^ (J - 2)) by
      rw [← pow_succ', ← pow_succ']; congr 1; omega]
    ring
  refine ⟨((n ^ (J - 2) * k : ℕ) : ZMod (n ^ J)), ?_⟩
  rw [nsmul_eq_mul, ← Nat.cast_mul, ← h1, ZMod.natCast_zmod_val]

theorem closure_eq_ker_of_meets_torsion_cosets :
    ∀ (I X : Type) [AddCommGroup X] [Module.Free ℤ X] (n J M : ℕ), n ≠ 0 → 2 ≤ J → M = n ^ J → ∀ (yy : (I → ZMod M) →+ X ⧸ (nsmulAddMonoidHom M : X →+ X).range), Function.Surjective yy → ∀ Z : Set (I → ZMod M), Z ⊆ yy.ker → (∀ a ∈ yy.ker, ∃ b, n • b = 0 ∧ a + b ∈ Z) → AddSubgroup.closure Z = yy.ker := by
  intro I X _ _ n J M hn hJ hM yy hyy Z hZ hcov
  subst hM
  have key : ∀ b : I → ZMod (n ^ J), n • b = 0 → b ∈ yy.ker → ∃ k ∈ yy.ker, n • k = b := by
    intro b hb hbk
    have hc : ∀ i, ∃ s, b i = n • s := fun i =>
      zmod_pow_exists_eq_nsmul_of_nsmul_eq_zero n J hn hJ (b i) (by
        simpa using congrFun hb i)
    choose c hc using hc
    have hbc : b = n • c := funext fun i => by simpa using hc i
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (yy c)
    have hnx : n • x ∈ (nsmulAddMonoidHom (n ^ J) : X →+ X).range := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, hx, ← map_nsmul, ← hbc]
      exact hbk
    obtain ⟨x', hx'⟩ := hnx
    have hx'' : (n ^ J) • x' = n • x := hx'
    have hxx : x = n ^ (J - 1) • x' := by
      have h2 : (n : ℤ) • x = (n : ℤ) • (n ^ (J - 1) • x') := by
        rw [natCast_zsmul, natCast_zsmul, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega]
        exact hx''.symm
      exact smul_right_injective X (by exact_mod_cast hn) h2
    obtain ⟨c', hc'⟩ := hyy (QuotientAddGroup.mk x')
    refine ⟨c - n ^ (J - 1) • c', ?_, ?_⟩
    · rw [AddMonoidHom.mem_ker, map_sub, map_nsmul, hc', ← QuotientAddGroup.mk_nsmul, ← hxx, hx,
        sub_self]
    · have h0 : (n ^ J) • c' = 0 := funext fun i => by
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rw [smul_sub, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega, ← hbc, h0, sub_zero]
  apply le_antisymm
  · exact (AddSubgroup.closure_le _).2 hZ
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    have hbk : b ∈ yy.ker := by
      have h3 : yy (a + b) = 0 := hZ hab
      rw [AddMonoidHom.mem_ker] at ha ⊢
      rwa [map_add, ha, zero_add] at h3
    obtain ⟨k, hk, hkb⟩ := key b hb hbk
    obtain ⟨b', hb', hkb'⟩ := hcov k hk
    have h4 : a = (a + b) - n • (k + b') := by
      rw [smul_add, hb', add_zero, hkb, add_sub_cancel_right]
    rw [h4]
    exact sub_mem (AddSubgroup.subset_closure hab) (nsmul_mem (AddSubgroup.subset_closure hkb') n)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DegenerateTest

section Pull

variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G'] [GrpObj G'']
  {L : LB G.left} {L' : LB G'.left} {L'' : LB G''.left}

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}


open IsLocalRing in
theorem exists_padic_embedding (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (h : Finite (ResidueField V)) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (c : FractionRing V →+* PadicAlgCl p),
      ∀ x, ‖c x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  obtain ⟨p, _, K₀, e, e₀, -, he⟩ := completeDVR_eq_integralClosure_padicInt.1 V (FractionRing V) h
  refine ⟨p, inferInstance, (algebraMap K₀ (PadicAlgCl p)).comp e.toRingHom, fun x => ?_⟩
  refine (mem_integralClosure_padicInt_iff K₀ (e x)).symm.trans ⟨fun hx => ⟨e₀.symm ⟨e x, hx⟩, ?_⟩, ?_⟩
  · apply e.injective
    rw [he, e₀.apply_symm_apply]
  · rintro ⟨v, rfl⟩
    rw [he]
    exact (e₀ v).2

end GlobalTheory.DegenerateTest

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

noncomputable section
namespace GlobalTheory.SS.TorOpen
open GlobalTheory.SplitTorus ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

theorem isIso_univPt_left (k : Type) [CommRing k] (X : Type) [AddCommGroup X] :
    IsIso (univPt (A := CommRingCat.of k) X (𝟙 (Sp k))).left := by
  have h1 := GlobalTheory.Diag.isPullback_groupRing k X
  have h2 := GlobalTheory.Diag.isPullback_torusFst (Sp k) X
  have e : (univPt (A := CommRingCat.of k) X (𝟙 (Sp k))).left = (h1.isoIsPullback _ _ h2).hom := by
    apply h2.hom_ext
    · refine Eq.trans ?_ (IsPullback.isoIsPullback_hom_fst _ _ h1 h2).symm
      refine (pullback.lift_fst _ _ _).trans ?_
      rw [Spec.map_comp]
      exact toSpecΓ_SpecMap_ΓSpecIso_inv_assoc (torusRing (CommRingCat.of k) X) _
    · refine Eq.trans ?_ (IsPullback.isoIsPullback_hom_snd _ _ h1 h2).symm
      exact (Over.w _).trans (Category.comp_id _)
  rw [e]; infer_instance

theorem exists_ringHom (k : Type) [Field k] (q : Polynomial k) :
    ∃ ψ : AddMonoidAlgebra k (ULift.{0} ℤ) →+* Localization.Away (Polynomial.X * q),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ)) ∧
      ψ.comp (algebraMap k _) = algebraMap k _ ∧
      ψ (AddMonoidAlgebra.single (ULift.up 1) 1) = algebraMap (Polynomial k) _ Polynomial.X := by
  let L := Localization.Away (Polynomial.X * q)
  have hu : IsUnit (algebraMap (Polynomial k) L Polynomial.X) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := L) (Polynomial.X * q)
    rw [map_mul] at this
    exact isUnit_of_mul_isUnit_left this
  let ψ' : LaurentPolynomial k →+* L := IsLocalization.Away.lift (Polynomial.X : Polynomial k) hu
  have hψ : ψ'.comp (algebraMap (Polynomial k) _) = algebraMap _ _ :=
    IsLocalization.Away.lift_comp _ hu
  let e : AddMonoidAlgebra k (ULift.{0} ℤ) ≃ₐ[k] LaurentPolynomial k :=
    AddMonoidAlgebra.domCongr k k AddEquiv.ulift
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ')) := by
    have a1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k)))) :=
      IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial k)
    have a2 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ') ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k)))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
      exact IsOpenImmersion.of_isLocalization (Polynomial.X * q)
    exact IsOpenImmersion.of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k))))
  refine ⟨ψ'.comp e.toRingEquiv.toRingHom, ?_, ?_, ?_⟩
  · rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) := e.toRingEquiv.toCommRingCatIso.isIso_hom
    infer_instance
  · ext c
    have : e (algebraMap k _ c) = algebraMap (Polynomial k) _ (algebraMap k _ c) := by
      rw [e.commutes]; simp
    change ψ' (e (algebraMap k _ c)) = _
    rw [this, ← RingHom.comp_apply, hψ, ← IsScalarTower.algebraMap_apply]
  · have : e (AddMonoidAlgebra.single (ULift.up 1) 1) = algebraMap (Polynomial k) _ Polynomial.X := by
      simp [e]; rfl
    change ψ' (e _) = _
    rw [this, ← RingHom.comp_apply, hψ]

theorem exists_of_ringHom (k L : Type) [CommRing k] [CommRing L] [Algebra k L]
    (ψ : AddMonoidAlgebra k (ULift.{0} ℤ) →+* L)
    (h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ))) (h2 : ψ.comp (algebraMap k _) = algebraMap k _)
    (t : L) (h3 : ψ (AddMonoidAlgebra.single (ULift.up 1) 1) = t) :
    ∃ jj : algOver k L ⟶ Gm (Sp k), IsOpenImmersion jj.left ∧ ∀ x y z : L →ₐ[k] k,
      (algOverHom x ≫ jj) * (algOverHom y ≫ jj) = algOverHom z ≫ jj → x t * y t = z t := by
  have hs : Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap k _))) ≫ 𝟙 (Sp k) =
      spMap (algebraMap k L) := by
    rw [h2]; exact Category.comp_id _
  let jj : algOver k L ⟶ Gm (Sp k) :=
    ptOf (A := CommRingCat.of k) (B := CommRingCat.of L) (𝟙 (Sp k)) ψ hs
  refine ⟨jj, ?_, fun x y z h => ?_⟩
  · have := isIso_univPt_left k (ULift.{0} ℤ)
    exact IsOpenImmersion.comp (Spec.map (CommRingCat.ofHom ψ))
      (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left
  · have key : ∀ w : L →ₐ[k] k,
        pull (B := CommRingCat.of k) (s := spMap (algebraMap k k)) (algOverHom w ≫ jj)
          (chi _ (ULift.up 1)) = w t := by
      intro w
      have hs' : Spec.map (CommRingCat.ofHom (((w : L →+* k).comp ψ).comp (algebraMap k _))) ≫ 𝟙 (Sp k) =
          spMap (algebraMap k k) := by
        rw [RingHom.comp_assoc, h2, w.comp_algebraMap]; exact Category.comp_id _
      have e : algOverHom w ≫ jj = ptOf (A := CommRingCat.of k) (B := CommRingCat.of k) (𝟙 (Sp k))
          ((w : L →+* k).comp ψ) hs' := by
        ext1
        change Spec.map (CommRingCat.ofHom (w : L →+* k)) ≫ Spec.map (CommRingCat.ofHom ψ) ≫
            (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left =
          Spec.map (CommRingCat.ofHom ((w : L →+* k).comp ψ)) ≫
            (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left
        rw [← Category.assoc, ← Spec.map_comp]
        rfl
      rw [e, pull_ptOf, ev_chi]
      exact congrArg w h3
    rw [← key, ← key, ← key, ← h]
    exact (pull_mul_chi (B := CommRingCat.of k) (s := spMap (algebraMap k k)) _ _ _).symm

theorem exists_open_part : ∀ (k : Type) [Field k] (q : Polynomial k), ∃ jj : algOver k (Localization.Away (Polynomial.X * q)) ⟶ Gm (Sp k), IsOpenImmersion jj.left ∧ ∀ x y z : Localization.Away (Polynomial.X * q) →ₐ[k] k, (algOverHom x ≫ jj) * (algOverHom y ≫ jj) = algOverHom z ≫ jj → x (algebraMap (Polynomial k) _ Polynomial.X) * y (algebraMap (Polynomial k) _ Polynomial.X) = z (algebraMap (Polynomial k) _ Polynomial.X) := by
  intro k _ q
  obtain ⟨ψ, h1, h2, h3⟩ := exists_ringHom k q
  exact exists_of_ringHom k _ ψ h1 h2 _ h3

end GlobalTheory.SS.TorOpen
end
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.PointDescent

theorem exists_lift {X I G H : Type*} [AddGroup X] [Group G] [Group H] (b : I → X)
    (hb : AddSubgroup.closure (Set.range b) = ⊤) (a : X → G) (ha : ∀ y z, a (y + z) = a y * a z) (β : H →* G)
    (hβ : Function.Injective β) (x₀ : I → H) (hx : ∀ k, a (b k) = β (x₀ k)) :
    ∃ c₀ : X → H, (∀ y z, c₀ (y + z) = c₀ y * c₀ z) ∧ ∀ y, a y = β (c₀ y) := by
  have h0 : a 0 = 1 := by
    have := ha 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have key : ∀ y, ∃ x, a y = β x := fun y => by
    have hy : y ∈ AddSubgroup.closure (Set.range b) := hb ▸ AddSubgroup.mem_top y
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact ⟨_, hx k⟩
    | zero => exact ⟨1, by rw [h0, map_one]⟩
    | add y z _ _ hy hz =>
      obtain ⟨u, hu⟩ := hy
      obtain ⟨v, hv⟩ := hz
      exact ⟨u * v, by rw [ha, hu, hv, map_mul]⟩
    | neg y _ hy =>
      obtain ⟨u, hu⟩ := hy
      refine ⟨u⁻¹, ?_⟩
      rw [map_inv, ← hu, eq_inv_iff_mul_eq_one, ← ha, neg_add_cancel, h0]
  choose c₀ hc using key
  exact ⟨c₀, fun y z => hβ (by rw [map_mul, ← hc, ← hc, ← hc, ha]), hc⟩

theorem exists_descent {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} [Epi f]
    {Φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f Φ) {X I : Type*} [AddGroup X] (b : I → X)
    (hb : AddSubgroup.closure (Set.range b) = ⊤) (c : X → (𝟙_ (Over S') ⟶ G')) (hc : ∀ y z, c (y + z) = c y * c z)
    (x₀ : I → (𝟙_ (Over S) ⟶ G)) (hx : ∀ k, (c (b k)).left ≫ Φ = f ≫ (x₀ k).left) :
    ∃ c₀ : X → (𝟙_ (Over S) ⟶ G), (∀ y z, c₀ (y + z) = c₀ y * c₀ z) ∧ ∀ y, (c y).left ≫ Φ = f ≫ (c₀ y).left := by
  let ρ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) :=
    Over.homMk f ((Category.comp_id f).trans (Category.id_comp f).symm)
  obtain ⟨c₀, h₁, h₂⟩ := exists_lift b hb (fun y => pushHom h (𝟙_ (Over S')) (c y))
    (fun y z => by rw [hc, map_mul]) (preHom (G := G) ρ)
    (fun u v huv => Over.OverMorphism.ext ((cancel_epi f).1 (congrArg (fun q => q.left) huv))) x₀
    (fun k => Over.OverMorphism.ext (hx k))
  exact ⟨c₀, h₁, fun y => congrArg (fun q => q.left) (h₂ y)⟩

theorem additive_points_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → ∀ (X : Type) [AddCommGroup X] (I : Type) (b : I → X), AddSubgroup.closure (Set.range b) = ⊤ → ∀ c : X → (𝟙_ (Over (Sp K)) ⟶ P.A), (∀ y z, c (y + z) = padd P.A (c y) (c z)) → ∀ x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ k, (c (b k)).left ≫ Φ = spMap i ≫ (x₀ k).left) → ∃ c₀ : X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) ∧ ∀ y, (c y).left ≫ Φ = spMap i ≫ (c₀ y).left := by
  intro K₀ K _ _ i P₀ P Φ h X _ I b hb c hc x₀ hx
  have := FieldBaseChange.flat_spMap i
  have := FieldBaseChange.surjective_spMap i
  have : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  exact exists_descent h b hb c hc x₀ hx

end GlobalTheory.PointDescent
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrimScale

open TopologicalSpace GlobalTheory.HolHom

theorem chart_one_le {X : Scheme.{0}} (L : LB X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun _ hy => Set.mem_iInter.1 hy 0

theorem exists_section_firstPower_restrict {X : Scheme.{0}} {L : LB X} (s : L.Sec) : ∃ t : H0 L 1, ∀ j,
    t.f j = (X.presheaf.map (homOfLE (chart_one_le L j)).op).hom (s.f (j 0)) := by
  have le := chart_one_le L
  refine ⟨⟨fun j => (X.presheaf.map (homOfLE (le j)).op).hom (s.f (j 0)),
    fun (i j : Fin 1 → L.ι) => fn_ext fun y hy => ?_⟩, fun _ => rfl⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.1 _)).trans
    ((SecPullIso.gs_sec_trans s (𝟙 X) y (le i hy.1) (le j hy.2)).trans (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val ?_))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.2 _))))))
  refine (gm_linComb L _ _ (𝟙 X) y i j hy.1 hy.2).trans ?_
  simp

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valR x U (a * b) = valR x U a * valR x U b := by
  simp only [valR_eq _ _ h, map_mul]

theorem valR_const {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (p : X ⟶ Sp A) (h : x ≫ p = 𝟙 _) (a : A) :
    valR x ⊤ (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = a := by
  refine (valR_comp x p ⊤ _).symm.trans ?_
  rw [h, valR, dite_eq_left (show ⊤ ≤ 𝟙 (Sp A) ⁻¹ᵁ ⊤ from le_top)]
  have : Scheme.Hom.appLE (𝟙 (Sp A)) ⊤ ⊤ le_top = 𝟙 _ := (Category.id_comp _).trans ((Sp A).presheaf.map_id _)
  rw [this]
  exact Iso.inv_hom_id_apply _ _

theorem exists_primitive_scaling : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G → ∀ (M : LB G.left), M.IsLB → ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (ψ : pullback G.hom (jK V) ⟶ Y) (w : LB.Iso (M.pull (pullback.fst G.hom (jK V))) (L.pull ψ)), w.IsGen → ∀ θ : LB.Sec L, (∃ z, ψ z ∈ nonzeroLocus θ) → ∃ (ϑ : H0 M 1) (c : FractionRing V), c ≠ 0 ∧ (∃ z ∈ nonzeroLocus ϑ, G.hom z = IsLocalRing.closedPoint V) ∧ ∀ x : Sp (FractionRing V) ⟶ pullback G.hom (jK V), x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → ∀ (i : M.ι) (k : L.ι), ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ M.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U k → valR x _ (w.s (fun _ => k, fun _ => i)).val * valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) = c * valR (x ≫ ψ) _ (θ.f k) := by
  intro V _ _ _ G _ hG M hM Y L hL ψ w hw θ hθ
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hK := IsPullback.of_hasPullback G.hom (jK V)
  have hs := IsPullback.of_hasPullback G.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  obtain ⟨r, hr⟩ := SecPullIso.exists_pull ψ L (M.pull (pullback.fst G.hom (jK V))) w hL (LB.isLB_linComb hM _ _) hw θ
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ hM r (by
    obtain ⟨x, hx⟩ := hθ
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx
    obtain ⟨a, ha⟩ := exists_chart (L := M.pull (pullback.fst G.hom (jK V))) (LB.isLB_linComb hM _ _) x
    have hk' := Y.basicOpen_le _ hk
    have u := (SecPullIso.isUnit_gs_iff ψ x hk' _).2 hk
    rw [hr x k a hk' ha] at u
    have u' := (SecPullIso.isUnit_gs_iff (𝟙 _) x ha _).1 (isUnit_of_mul_isUnit_right u)
    exact ⟨a, fun h => by rw [h, Scheme.basicOpen_zero] at u'; exact u'⟩)
  have h0 : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hϖ.ne_zero)
  obtain ⟨ϑ, hϑ⟩ := exists_section_firstPower_restrict σ
  refine ⟨ϑ, _, h0, ⟨x₀, Opens.mem_iSup.2 ⟨fun _ => b, ?_⟩, hx₀⟩, fun x hx i k hi hk => ?_⟩
  · refine (congrArg G.left.basicOpen (hϑ fun _ => b)).ge ?_
    exact (Scheme.basicOpen_res _ _ _).ge ⟨Set.mem_iInter.2 fun _ => G.left.basicOpen_le _ hb, hb⟩
  · have hi₁ : ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ LB.wchart M (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) :=
      fun z hz => Set.mem_iInter.2 fun _ => hi hz
    have hi₂ : ⊤ ≤ x ⁻¹ᵁ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i) := fun z hz => mem_pull.2 (hi hz)
    have hW : ⊤ ≤ x ⁻¹ᵁ ((L.pull ψ).U (fun _ => k) ⊓ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i)) :=
      fun z hz => ⟨mem_pull.2 (hk hz), hi₂ hz⟩
    have l₁ : (L.pull ψ).U (fun _ => k) ⊓ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i) ≤ ψ ⁻¹ᵁ L.U k :=
      fun y hy => mem_pull.1 hy.1
    have e₁ : valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) =
        algebraMap V (FractionRing V) ϖ ^ n * valR x _ (r.f fun _ => i) := by
      refine (congrArg (valR _ _) (hϑ fun _ => i)).trans ?_
      refine (valR_res _ _ _ hi₁).trans ((valR_appLE x _ _ _ _ _ hi₂).symm.trans
        ((congrArg (valR x _) (hσ fun _ => i)).trans ((valR_mul' x _ hi₂ _ _).trans (congrArg (· * _) ?_))))
      exact (valR_res x le_top _ hi₂).trans (valR_const x _ hx _)
    have e₂ : (ψ.appLE _ _ l₁).hom (θ.f k) = (show Γ(pullback G.hom (jK V), (L.pull ψ).U (fun _ => k) ⊓
        (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i))ˣ from w.s (fun _ => k, fun _ => i)).val *
          ((pullback G.hom (jK V)).presheaf.map (homOfLE inf_le_right).op).hom (r.f fun _ => i) :=
      fn_ext fun y hy => by
        refine (gs_appLE _ _ _ _ (𝟙 _) y hy _).trans ?_
        rw [Category.id_comp, hr y k _ (l₁ hy) hy.2]
        exact ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _)
          (gs_res (𝟙 _) y _ hy _))).symm
    have e₃ := (valR_appLE x ψ _ _ l₁ _ hW).symm.trans ((congrArg (valR x _) e₂).trans
      ((valR_mul' x _ hW _ _).trans (congrArg (_ * ·) (valR_res x _ _ hW))))
    rw [e₁, e₃]
    exact mul_left_comm _ _ _

end GlobalTheory.PrimScale
end
