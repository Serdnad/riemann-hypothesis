module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreAV

section

variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) (A : Over S) [GrpObj A]

theorem pull_map_left_fst {B : Over S} (f : A ⟶ B) :
    ((Over.pullback x).map f).left ≫ pullback.fst B.hom x = pullback.fst A.hom x ≫ f.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

theorem push_comp_map {T : Over (Sp k)} {g : T.left ⟶ S} (f : A ⟶ A)
    (e : (T ⟶ (Over.pullback x).obj A) → (Over.mk g ⟶ A)) (he : ∀ z, (e z).left = z.left ≫ pullback.fst A.hom x)
    (z : T ⟶ (Over.pullback x).obj A) : e (z ≫ (Over.pullback x).map f) = e z ≫ f := by
  apply Over.OverMorphism.ext
  rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, pull_map_left_fst, Category.assoc]

end

open GlobalTheory.AV.AbVar in
theorem fibre_av : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ (B : AbVar k) (e : (Over.mk x ⟶ A) ≃* B.Pt) (ψ : 𝓞 F →+* End B), (∀ (c : 𝓞 F) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ Hom.hom (ψ c).asHom) ∧ ∀ c : 𝓞 F, (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → ∀ w : epsPtR (𝟙 (Sp k)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp k)) ⟶ B.X).left → w ≫ Hom.hom (ψ c).asHom = 1 → w = 1 := by
  intro S A _ _ hA F _ _ act k _ _ x
  letI : (Over.pullback x).Monoidal := (Over.instBraidedPullback (f := x)).toMonoidal
  letI : GrpObj ((Over.pullback x).obj A) := Functor.grpObjObj (F := Over.pullback x)
  have h : IsGrpPullback ((Over.pullback x).obj A) A x (pullback.fst A.hom x) := isGrpPullback_pullback A x
  have hab : IsAbelianScheme ((Over.pullback x).obj A) := GlobalTheory.isAbelianScheme_pullback_obj x A hA
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k _ hab
  let B : AbVar k := { X := (Over.pullback x).obj A, ab := hab, dim := g, smooth := hg }
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (𝟙_ (Over (Sp k))) x (by simp)
  have i : ptOver k (AlgebraicClosure k) ≅ 𝟙_ (Over (Sp k)) := by
    let σ : k ≃+* AlgebraicClosure k :=
      RingEquiv.ofBijective (algebraMap k (AlgebraicClosure k))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    have : IsIso (spMap (algebraMap k (AlgebraicClosure k))) := by
      change IsIso (Spec.map σ.toCommRingCatIso.hom)
      infer_instance
    exact Over.isoMk (asIso (spMap (algebraMap k (AlgebraicClosure k)))) (by
      change spMap _ ≫ 𝟙 _ = spMap _
      exact Category.comp_id _)
  let ptEquiv : (𝟙_ (Over (Sp k)) ⟶ B.X) ≃* B.Pt :=
    { toFun := fun t => i.hom ≫ t
      invFun := fun t => i.inv ≫ t
      left_inv := fun t => by simp
      right_inv := fun t => by simp
      map_mul' := fun t u => MonObj.comp_mul _ t u }
  let e : (Over.mk x ⟶ A) ≃* B.Pt := e₀.symm.trans ptEquiv
  have hm : ∀ c, IsMonHom ((Over.pullback x).map (act.act c)) := fun c => by
    have := act.hom c; infer_instance
  let ψf : 𝓞 F → (B ⟶ B) := fun c => Hom.mk (A := B) (B := B)
    ((Over.pullback x).map (act.act c)) (h := hm c)
  have hψ : ∀ c, Hom.hom (ψf c) = (Over.pullback x).map (act.act c) := fun c => rfl
  have hom_ext {f g : B ⟶ B} (hfg : Hom.hom f = Hom.hom g) : f = g := Subtype.ext hfg
  have act0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  let ψ : 𝓞 F →+* End B :=
    { toFun := fun c => End.of (ψf c)
      map_one' := by
        apply End.ext
        change ψf 1 = 𝟙 B
        apply hom_ext
        rw [hψ, act.one, CategoryTheory.Functor.map_id, id_hom]
      map_mul' := fun a b => by
        apply End.ext
        change ψf (a * b) = ψf b ≫ ψf a
        apply hom_ext
        rw [comp_hom, hψ, hψ, hψ, mul_comm, act.mul, CategoryTheory.Functor.map_comp]
      map_zero' := by
        apply End.ext
        change ψf 0 = 0
        apply hom_ext
        rw [hψ, act0, zero_hom]
        exact CategoryTheory.Functor.map_one _
      map_add' := fun a b => by
        apply End.ext
        change ψf (a + b) = ψf a + ψf b
        apply hom_ext
        rw [add_hom, hψ, hψ, hψ, act.add]
        exact CategoryTheory.Functor.map_mul _ _ _ }
  refine ⟨B, e, ψ, fun c z => ?_, fun c H w hw1 hw2 => ?_⟩
  · show ptEquiv (e₀.symm (z ≫ act.act c)) =
      ptEquiv (e₀.symm z) ≫ (Over.pullback x).map (act.act c)
    have : e₀.symm (z ≫ act.act c) = e₀.symm z ≫ (Over.pullback x).map (act.act c) := by
      apply e₀.injective
      rw [MulEquiv.apply_symm_apply, push_comp_map x A (act.act c) e₀ he₀, MulEquiv.apply_symm_apply]
    rw [this]
    rfl
  · obtain ⟨e₁, he₁⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR (𝟙 (Sp k)))
      (spMap (algebraMap k (DualNumber k)) ≫ x) (by simp)
    obtain ⟨e₂, he₂⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (𝟙 (Sp k))) x (by simp)
    have one : (1 : Over.mk x ⟶ A).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ (Over.pullback x).obj A).left ≫
        pullback.fst A.hom x := by
      rw [← he₂, map_one]
    have r1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (e₁ w).left = (1 : Over.mk x ⟶ A).left := by
      rw [he₁, one, ← Category.assoc, hw1]
    have r2 : e₁ w ≫ act.act c = 1 := by
      rw [← push_comp_map x A (act.act c) e₁ he₁]
      have hw2' : w ≫ Hom.hom (ψf c) = 1 := hw2
      change e₁ (w ≫ Hom.hom (ψf c)) = 1
      rw [hw2', map_one]
    exact e₁.injective ((H (e₁ w) r1 r2).trans (map_one e₁).symm)

end GlobalTheory.FibreAV
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

theorem diffVanish_chiPic_structureModule {K : Type} [Field K] (A : AbVar K) :
    letI := A.algΓ
    DiffVanish (A.dim + 1) (chiPic K (QCoh.structureModule A.X.left)) := by
  letI := A.algΓ
  refine diffVanish_chiPic_of_isProjOver (f := A.X.hom) (fun r => rfl) _
    (GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A).2 ?_
  refine (QCoh.suppDim_le _).trans ?_
  rw [GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A]

theorem inter_update_add {K : Type} [Field K] (A : AbVar K) {J : Type} [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = A.dim) (c : J → Pic A.X.left) (i : J) (a b : Pic A.X.left) :
    inter A (Function.update c i (a + b)) = inter A (Function.update c i a) + inter A (Function.update c i b) := by
  letI := A.algΓ
  exact congrFun ((diffVanish_chiPic_structureModule A).multiDiff_update_add_of_le_card hJ.ge c i a b) 0

def interAdd {K : Type} [Field K] (A : AbVar K) {J : Type} [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = A.dim) (c : J → Pic A.X.left) (i : J) : Pic A.X.left →+ ℤ :=
  AddMonoidHom.mk' (fun a => inter A (Function.update c i a)) (inter_update_add A hJ c i)

theorem inter_comp_equiv {K : Type} [Field K] (A : AbVar K) {J J' : Type} [Fintype J] [Fintype J']
    (e : J' ≃ J) (c : J → Pic A.X.left) : inter A (c ∘ e) = inter A c := by
  letI := A.algΓ
  exact congrFun (multiDiff_comp_equiv e c _) 0

theorem inter_multilinear_and_symm :
    ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J], Fintype.card J = A.dim →
      (∃ M : (J → Pic A.X.left) →ₘₗ[ℤ] ℤ, ∀ c, M c = inter A c) ∧
      ∀ (J' : Type) [Fintype J'] (e : J' ≃ J) (c : J → Pic A.X.left), inter A (c ∘ e) = inter A c := by
  intro K _ A J _ hJ
  classical
  refine ⟨⟨MultilinearMap.mk' (fun c => inter A c) (fun c i a b => inter_update_add A hJ c i a b)
    (fun c i n a => map_zsmul (interAdd A hJ c i) n a), fun c => rfl⟩, fun J' _ e c => inter_comp_equiv A e c⟩

end GlobalTheory.AV.AbVar
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_intersection_eq_lineBundleIntersection : ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J] (L : J → LB A.X.left) (hL : ∀ j, (L j).IsLB), inter A (fun j => cls (L j) (hL j)) = (letI := A.algΓ; interNum K (structureModule A.X.left) L) := by
  first | exact @GlobalTheory.AV.AbVar.inter_cls_eq_interNum | exact GlobalTheory.AV.AbVar.inter_cls_eq_interNum | (intros; apply GlobalTheory.AV.AbVar.inter_cls_eq_interNum <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive : ∀ (K : Type) [Field K] (A B : AbVar K) (c c' : Pic A.X.left) (d : Pic B.X.left) (f : A ⟶ B) (Y Z : Over (Sp K)) (u : Z ⟶ Y) (x y : Y ⟶ A.X), AbVar.lam c x y = AbVar.lam c y x ∧ CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) ∧ AbVar.lam d (x ≫ f.hom) (y ≫ f.hom) = AbVar.lam (CechPic.pull f.hom.left d) x y ∧ AbVar.lam (c + c') x y = AbVar.lam c x y + AbVar.lam c' x y := by
  first | (exact @GlobalTheory.AV.lam_symm_nat_add) | (exact GlobalTheory.AV.lam_symm_nat_add) | (intros; apply GlobalTheory.AV.lam_symm_nat_add  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom : ∀ (K : Type) [Field K] (A A' T : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P) (β : Pic (A.X ⊗ T.X).left), (∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ T.X), CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β) → CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ T.X)).left β = 0 → ∃! ψ : T ⟶ A', β = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ ψ.hom) := by
  first | (exact @GlobalTheory.AV.FamHom.main) | (exact GlobalTheory.AV.FamHom.main) | (intros; apply GlobalTheory.AV.FamHom.main  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_ampleSections_vanishing_origin_separating : ∀ (K : Type) [Field K] (B : AbVar K) (L : LB B.X.left), L.IsLB → Out.RelAmple B.X L → ∃ N : ℕ, 1 ≤ N ∧ ∃ (M : ℕ) (t : Fin M → LB.Sec (Out.powOver B.X L ⊤ N)), (∀ j y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y ∉ Out.nonzeroLocus (t j)) ∧ ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y ≠ B.origin → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  first | (exact @GlobalTheory.RelAmpleSep.exists_sec_sep_origin) | (exact GlobalTheory.RelAmpleSep.exists_sec_sep_origin) | (intros; apply GlobalTheory.RelAmpleSep.exists_sec_sep_origin  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_finiteHom_kernel_killed_by_nat : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsFinite f.hom.left → ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 := by
  first | exact @GlobalTheory.AV.KerKill.kernel_killed | exact GlobalTheory.AV.KerKill.kernel_killed | (intros; apply GlobalTheory.AV.KerKill.kernel_killed <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.comp_eq_one_of_kills_geometric_torsionPoints : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ), (n : K) ≠ 0 → (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1) → ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ^ n = 1 → x ≫ f.hom = 1 := by
  first | exact @GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts | exact GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts | (intros; apply GlobalTheory.AV.AbVar.comp_hom_eq_one_of_torsion_pts <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isFinite_of_surjective_of_dim_eq' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → Surjective f.hom.left → IsFinite f.hom.left := by
  first | exact @GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq | exact GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq | (intros; apply GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_exists_ampleClass : ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c := by
  first | exact @GlobalTheory.AV.exists_isAmpleCls | exact GlobalTheory.AV.exists_isAmpleCls | (intros; apply GlobalTheory.AV.exists_isAmpleCls <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem lam_swap_of_comm {K : Type} [Field K] {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    AbVar.lam c x y = AbVar.lam c y x := by
  rw [AbVar.lam, AbVar.lam, mul_comm x y]
  abel

noncomputable section

def lamLeftMonoidHom {K : Type} [Field K] (A : AbVar K) (c : Pic A.X.left) {Y : Over (Sp K)} (y : Y ⟶ A.X) :
    (Y ⟶ A.X) →* Multiplicative (Pic Y.left) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (AbVar.lam c x y)) (fun x x' => by
    rw [← ofAdd_add, lam_mul_left_of_cube])

theorem lam_bilinear : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K)) (x y y' : Y ⟶ A.X) (n : ℤ), AbVar.lam c x (y * y') = AbVar.lam c x y + AbVar.lam c x y' ∧ AbVar.lam c 1 y = 0 ∧ AbVar.lam c x 1 = 0 ∧ AbVar.lam c (x ^ n) y = n • AbVar.lam c x y ∧ AbVar.lam c x (y ^ n) = n • AbVar.lam c x y := by
  intro K _ A c Y x y y' n
  have hL : ∀ x z : Y ⟶ A.X, ∀ m : ℤ, AbVar.lam c (x ^ m) z = m • AbVar.lam c x z := fun x z m => by
    have := map_zpow (lamLeftMonoidHom A c z) x m
    simpa [lamLeftMonoidHom] using congrArg Multiplicative.toAdd this
  have h1 : ∀ z : Y ⟶ A.X, AbVar.lam c 1 z = 0 := fun z => by
    simpa using hL 1 z 0
  refine ⟨?_, h1 y, ?_, hL x y n, ?_⟩
  · rw [lam_swap_of_comm c x, lam_swap_of_comm c x, lam_swap_of_comm c x, lam_mul_left_of_cube]
  · rw [lam_swap_of_comm]; exact h1 x
  · rw [lam_swap_of_comm, hL, lam_swap_of_comm]

end

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVarietyMumfordClass_mul_left : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K)) (x x' y : Y ⟶ A.X), AbVar.lam c (x * x') y = AbVar.lam c x y + AbVar.lam c x' y := by
  first | exact @GlobalTheory.AV.AbVar.lam_mul_left_of_cube | exact GlobalTheory.AV.AbVar.lam_mul_left_of_cube | (intros; apply GlobalTheory.AV.AbVar.lam_mul_left_of_cube <;> assumption)
end
