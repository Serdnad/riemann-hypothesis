module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle977
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTPull

open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem push_comp (h : IsGrpPullback A' A f φ) {α : A' ⟶ A'} {β : A ⟶ A} (hab : α.left ≫ φ = φ ≫ β.left)
    (T : Over S') (x : T ⟶ A') : pushHom h T (x ≫ α) = pushHom h T x ≫ β :=
  Over.OverMorphism.ext (by
    show (x.left ≫ α.left) ≫ φ = (x.left ≫ φ) ≫ β.left
    rw [Category.assoc, hab, Category.assoc])

theorem isTanScal_iff (h : IsGrpPullback A' A f φ) {O : Type} [Ring O] (a : OActN O A) (a' : OActN O A')
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S')
    (e : (epsPtR x ⟶ A') ≃* (epsPtR (x ≫ f) ⟶ A)) (he : ∀ v, (e v).left = v.left ≫ φ) (b : O) (c : R')
    (v : epsPtR x ⟶ A') : IsTanScal a' x b c v ↔ IsTanScal a (x ≫ f) b c (e v) := by
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (u w : epsPtR x ⟶ A'), u.left = spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ w.left ↔
      (e u).left = spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ (e w).left := fun u w => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ ·) (Over.w w)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)
  refine and_congr ?_ ?_
  · rw [one, he]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · have E : e (v ≫ a'.act b) = e v ≫ a.act b := Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
    have H := hR (v ≫ a'.act b) v
    rw [E] at H
    exact H

end GlobalTheory.HTPull

namespace GlobalTheory.HTPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem kernel_pullback (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left}
    {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) (e : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x ^ e = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine GlobalTheory.SiegelPull.push_injective h T ((map_pow _ _ _).trans ((hn _ (pushHom h T x) ?_).trans (map_one _).symm))
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

end GlobalTheory.HTPull

namespace GlobalTheory.HTPull

open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

theorem exists_objMap_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : Obj b N s), ∃ o' : Obj b N (f ≫ s), Nonempty (ObjMap o' o f) := by
  intro p _ D R _ b N S S' s f o
  let A' := (Over.pullback f).obj o.A
  let φ := PullbackComparison.pφ f o.A
  let φ₂ := PullbackComparison.pφ₂ f o.A
  have pb : IsGrpPullback A' o.A f φ := PullbackComparison.isGrpPullback f o.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare f o.A
  have hab : IsAbelianScheme A' :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := ActPull.exists_act_pull S S' f o.A A' φ pb D.Oᵐᵒᵖ
    (fun a => o.act.act a.unop) (fun a => o.act.hom _) (by simpa using o.act.one)
    (fun a b => by simpa using o.act.mul b.unop a.unop) (fun a b => by simpa using o.act.add a.unop b.unop)
  let actN : OActN D.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ φ = φ ≫ (o.act.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := o.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB o.isLB φ₂
  have iso : LBIso P' (o.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 o.A ⟶ o.A), x'.left ≫ φ = φ₂ ≫ x.left → y'.left ≫ φ = φ₂ ≫ y.left →
      (lift x' y').left ≫ φ₂ = φ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (G2 o.A).hom)) (T' := G2 A') (𝟙 _) x' y'
      (Z := G2 o.A) φ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  obtain ⟨eK, heK, hK⟩ := o.kerP
  let o' : Obj b N (f ≫ s) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P _ _ rfl)
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap f o.A)) o.symm
      ample := (pol_pull S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab pb dg).2.1 o.ample
      kerP := ⟨eK, heK, fun T x hx => kernel_pullback pb sq o.isLB hP' iso eK hK T x hx⟩
      rosati := fun c => LBIso.chartPull
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.1, Category.assoc])
          (by rw [sq.2])))
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by rw [sq.1]) (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.2, Category.assoc])))
        (o.rosati c)
      lie := fun R' _ β x hx v hv => by
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc, hx]) (e v)
          ((isTanScal_iff pb o.act actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (isTanScal_iff pb o.act actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' o.A A' f φ (o.act.toF D) (actN.toF D) pb
        (fun c => hact _) k x (β.comp (b.t i)) D.m).2 (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hx]) i)
      eta := fun y => SiegelPull.secPull pb (o.eta y)
      eta_add := fun y z => SiegelPull.push_injective pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', o.eta_add, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pb _ (by
        rw [push_comp pb (hact c), push_secPull', push_secPull', o.eta_lin, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pb _ (by
        rw [push_secPull', o.eta_ker, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ o.A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
          ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ o.act.act c := fun c g => push_comp pb (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ φ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _)
                    (pull_isLB hP' _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pb (o.eta y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pb (o.eta y) (Over.mk x)).symm }
  exact ⟨o', ⟨{ φ := φ, φ₂ := φ₂, cart := pb, sq := sq, act := hact, pol := iso, eta := fun y => SiegelPull.secPull_left pb _ }⟩⟩

end GlobalTheory.HTPull
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObsUniq

theorem obAt_eq_of_iso : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (C : Type) [Category.{0} C] (G : C ⥤ AffOp X₀) (d d' : GlobalTheory.CatCoh.H2 (ext R₁ (G ⋙ OAff s₀))), L.IsLB → L'.IsLB → LBIso L L' → ObAt S α L G d → ObAt S α L' G d' → d = d' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L L' C _ G d d' hL hL' e hd hd'
  obtain ⟨u, hu, hobs⟩ := hd
  obtain ⟨u', hu', hobs'⟩ := hd'
  obtain ⟨t, ht⟩ := GlobalTheory.FrameCob.frames_cohomologous X₀ C (opOf G) (opOf_le G) L L' u u' hL hL' e hu hu'
  refine GlobalTheory.T.lineBundleLiftObstruction_eq_of_cohomologous R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) u u' t d d'
    ((ofSys_isFun S).restrict G) (fun T T' a ↦ ?_) hobs hobs'
  have := congrArg (fun w : Γ(X₀, opOf G T')ˣ ↦ (w : Γ(X₀, opOf G T'))) (ht T T' a)
  rw [Units.val_mul, Units.val_mul] at this
  exact this

end GlobalTheory.LBObsUniq
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isObL_tens : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), IsObL S α L c → IsObL S α L' c' → IsObL S α (tens L L') (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L L' c c' hL hL'
  obtain ⟨C, _, _, G, hG, hLG⟩ := hL
  obtain ⟨C', _, _, G', hG', hLG'⟩ := hL'
  obtain ⟨D, _, _, K, H, H', ⟨θ⟩, ⟨θ'⟩, hK⟩ := GlobalTheory.LBObs.common_refinement X₀ C C' G G' hG hG'
  have h₁ := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L c C D G K H θ hLG
  have h₂ := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L' c' C' D G' K H' θ' hLG'
  obtain ⟨u, hu, hU⟩ := h₁
  obtain ⟨u', hu', hU'⟩ := h₂
  refine ⟨D, inferInstance, inferInstance, K, hK, fun T T' a ↦ u T T' a * u' T T' a,
    GlobalTheory.T.isLineBundleFrameOnBasis_lineBundleCechTensor X₀ D (opOf K) (opOf_le K) L L' u u' hu hu', ?_⟩
  rw [map_add (f := _)]
  exact GlobalTheory.LBObs.isObU_mul R R₀ I hI π hπ hk R₁ α D (K ⋙ OAff s₀) ((ofSys S).restrict K) u u' _ _ hU hU'

end GlobalTheory.LBObs
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.Base

variable {p : ℕ} [Fact p.Prime] {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop}
  (B : GlobalTheory.Dieu.Base p P)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_id' {G : PDivGroup p k} (hG : P k G) : B.map hG hG (𝟙 G) = LinearMap.id :=
  LinearMap.ext fun m => B.smap_id G hG m

theorem map_comp' {G H K : PDivGroup p k} (hG : P k G) (hH : P k H) (hK : P k K) (f : G ⟶ H) (g : H ⟶ K) :
    B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g :=
  LinearMap.ext fun m => B.smap_comp hG hH hK (SemiHom.ofHom g) (SemiHom.ofHom f) (SemiHom.ofHom (f ≫ g))
    (fun _ _ => rfl) m

theorem map_add' {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f g : G ⟶ H) :
    B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g :=
  LinearMap.ext fun m => B.smap_add hG hH f g m

def mapAdd {G H : PDivGroup p k} (hG : P k G) (hH : P k H) :
    (G ⟶ H) →+ (B.M H hH →ₗ[WittVector p k] B.M G hG) :=
  AddMonoidHom.mk' (B.map hG hH) (B.map_add' hG hH)

theorem map_zero' {G H : PDivGroup p k} (hG : P k G) (hH : P k H) : B.map hG hH (0 : G ⟶ H) = 0 :=
  map_zero (B.mapAdd hG hH)

theorem map_pow_smul {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (n : ℕ) (f : G ⟶ H) (m : B.M H hH) :
    B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m := by
  have e : (p : ℤ_[p]) ^ n • f = (p ^ n) • f := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have e2 : B.map hG hH ((p ^ n) • f) = (p ^ n) • B.map hG hH f := map_nsmul (B.mapAdd hG hH) _ _
  rw [e, e2, LinearMap.smul_apply]

theorem red_map {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) (m : B.M H hH) :
    B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m) := by
  have := B.red_smap hG hH (SemiHom.ofHom f) m
  rw [SemiHom.ofHom_rig] at this
  exact this

theorem map_F {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) (m : B.M H hH) :
    B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m) := by
  let u := (SemiHom.ofHom f).comp (absFrob (p_eq_zero p k) H)
  have e1 : B.smap hG hH u m = B.map hG hH f (B.F H hH m) :=
    B.smap_comp hG hH hH (absFrob (p_eq_zero p k) H) (SemiHom.ofHom f) u (fun _ _ => rfl) m
  have e2 : B.smap hG hH u m = B.F G hG (B.map hG hH f m) :=
    B.smap_comp hG hG hH (SemiHom.ofHom f) (absFrob (p_eq_zero p k) G) u
      (fun n a => by simp only [u, SemiHom.comp_app, SemiHom.ofHom_app, absFrob_app, map_pow]) m
  exact e1.symm.trans e2

theorem finrank_M (G : PDivGroup p k) (hG : P k G) :
    Module.finrank (WittVector p k) (B.M G hG) = G.height := by
  haveI := B.free G hG
  haveI := B.finite G hG
  obtain ⟨_, h5⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p)
    (p_eq_zero p k) (B.red G hG) (B.red_surjective G hG) fun m => (B.red_eq_zero G hG m).1
  exact h5.symm.trans (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p k (p_eq_zero p k) G).2.2.1

theorem eq_zero_of_pow_smul {G : PDivGroup p k} (hG : P k G) (n : ℕ) (m : B.M G hG) (h : p ^ n • m = 0) :
    m = 0 := by
  haveI := B.free G hG
  rw [← Nat.cast_smul_eq_nsmul (WittVector p k)] at h
  refine (smul_eq_zero.1 h).resolve_left ?_
  rw [Nat.cast_pow]
  exact pow_ne_zero _ (WittVector.p_ne_zero p k)

end GlobalTheory.Dieu.Base

namespace GlobalTheory.Dieu

theorem base_functor_props : ∀ (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) (B : Base p P) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H K : PDivGroup p k) (hG : P k G) (hH : P k H) (hK : P k K), B.map hG hG (𝟙 G) = LinearMap.id ∧ (∀ (f : G ⟶ H) (g : H ⟶ K), B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g) ∧ (∀ f g : G ⟶ H, B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g) ∧ B.map hG hH (0 : G ⟶ H) = 0 ∧ (∀ (n : ℕ) (f : G ⟶ H) (m : B.M H hH), B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m)) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m)) ∧ Module.finrank (WittVector p k) (B.M G hG) = G.height ∧ ∀ (n : ℕ) (m : B.M G hG), p ^ n • m = 0 → m = 0 := by
  intro p _ P B k _ _ _ G H K hG hH hK
  exact ⟨B.map_id' hG, fun f g => B.map_comp' hG hH hK f g, B.map_add' hG hH, B.map_zero' hG hH,
    B.map_pow_smul hG hH, B.red_map hG hH, B.map_F hG hH, B.finrank_M G hG, B.eq_zero_of_pow_smul hG⟩

end GlobalTheory.Dieu
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.Base



theorem exists_mem_span_red_eq (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop)
    (B : Base p P) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (hG : P k G) (hG' : P k' (G.baseChange k'))
    (ι : Type) (b : Module.Basis ι (WittVector p k) (B.M G hG)) (z : (G.baseChange k').RigExt) :
    ∃ n ∈ Submodule.span (WittVector p k') (Set.range fun i => B.smap hG' hG (G.toBase k') (b i)),
      B.red _ hG' n = z := by
  obtain ⟨x, rfl⟩ := G.liftSemi_rig_bijective k' (CharP.cast_eq_zero k p) (.inl inferInstance) |>.2 z
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨n, hn, h1⟩ := hx
    obtain ⟨n', hn', h2⟩ := hy
    refine ⟨n + n', add_mem hn hn', ?_⟩
    rw [LinearMap.map_add (B.red _ hG') n n', h1, h2, LinearMap.map_add (f := _)]
  | tmul r y =>
    obtain ⟨m, rfl⟩ := B.red_surjective G hG y
    obtain ⟨R, rfl⟩ := (WittVector.constantCoeff_surjective p : Function.Surjective
      (WittVector.constantCoeff : WittVector p k' →+* k')) r
    refine ⟨R • B.smap hG' hG (G.toBase k') m, Submodule.smul_mem _ _ ?_, ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.linearCombination_repr m, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        rw [B.smap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · set_option backward.isDefEq.respectTransparency false in
      rw [liftSemi_tmul, LinearMap.map_smulₛₗ (B.red _ hG') R, B.red_smap]

set_option synthInstance.maxHeartbeats 200000 in
theorem smap_toBase_basis (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop)
    (B : Base p P) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (hG : P k G) (hG' : P k' (G.baseChange k'))
    (ι : Type) [Fintype ι] (b : Module.Basis ι (WittVector p k) (B.M G hG)) :
    ∃ b' : Module.Basis ι (WittVector p k') (B.M (G.baseChange k') hG'),
      ∀ i, b' i = B.smap hG' hG (G.toBase k') (b i) := by
  have := B.free G hG
  have := B.finite G hG
  have := B.free _ hG'
  have := B.finite _ hG'
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have hp' : (p : k') = 0 := CharP.cast_eq_zero k' p
  obtain ⟨-, hr⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p) hp
    (B.red G hG) (B.red_surjective G hG) fun m h => (B.red_eq_zero G hG m).1 h
  obtain ⟨-, hr'⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p) hp'
    (B.red _ hG') (B.red_surjective _ hG') fun m h => (B.red_eq_zero _ hG' m).1 h
  change Module.finrank k G.RigExt = _ at hr
  change Module.finrank k' (G.baseChange k').RigExt = _ at hr'
  have hrank : Module.finrank k' (G.baseChange k').RigExt = Module.finrank k G.RigExt := by
    rw [← (LinearEquiv.ofBijective _ (G.liftSemi_rig_bijective k' hp (.inl inferInstance))).finrank_eq,
      Module.finrank_baseChange]
  have hmax : (p : WittVector p k') ∈ IsLocalRing.maximalIdeal (WittVector p k') := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map (WittVector.constantCoeff : WittVector p k' →+* k')
    rw [map_natCast, hp'] at this
    exact not_isUnit_zero this
  have hjac : Ideal.span {(p : WittVector p k')} ≤ Ring.jacobson (WittVector p k') := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Ideal.span_le.2 (Set.singleton_subset_iff.2 hmax)
  have hspan : ⊤ ≤ Submodule.span (WittVector p k')
      (Set.range fun i => B.smap hG' hG (G.toBase k') (b i)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson Module.Finite.fg_top hjac fun m _ => ?_
    obtain ⟨n, hn, h1⟩ := exists_mem_span_red_eq p P B k k' G hG hG' ι b (B.red _ hG' m)
    obtain ⟨q, hq⟩ := (B.red_eq_zero _ hG' (m - n)).1 (by
      rw [LinearMap.map_sub (B.red _ hG') m n, h1, sub_self])
    have hm : m = n + (p : WittVector p k') • q := by
      rw [← Nat.cast_smul_eq_nsmul (WittVector p k')] at hq
      rw [← hq, add_sub_cancel]
    rw [hm]
    exact Submodule.add_mem_sup hn (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _)
      Submodule.mem_top)
  have hcard : Fintype.card ι = Module.finrank (WittVector p k') (B.M (G.baseChange k') hG') := by
    rw [← hr', hrank, hr, Module.finrank_eq_card_basis b]
  exact ⟨Module.Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard) hspan,
    fun i => Module.Basis.mk_apply _ _ i⟩

end GlobalTheory.Dieu.Base
end
end
