module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V]
  (φ : Sp V ⟶ T.left)

theorem upa_mul {Y : Over (Sp V)} (x y : Y ⟶ bc A φ) : upa φ (x * y) = upa φ x * upa φ y := by
  have h := (isGrpPullback_pullback A (φ ≫ T.hom)).2 Y x y (upa φ x) (upa φ y) rfl rfl
  exact Over.OverMorphism.ext h.symm

theorem upa_one {Y : Over (Sp V)} : upa φ (1 : Y ⟶ bc A φ) = 1 := by
  have e := upa_mul φ (1 : Y ⟶ bc A φ) 1
  rw [_root_.mul_one] at e
  exact left_eq_mul.1 e

theorem pull_cls_twist {N : LB (A ⊗ T).left} (hN : N.IsLB) (h : (twist A φ N).IsLB) {Y : Over (Sp V)}
    (x : Y ⟶ bc A φ) : CechPic.pull x.left (cls _ h) = evc hN (upa φ x) (upt φ Y) := by
  let u : up φ Y ⟶ bcR A φ := Over.homMk x.left (by
    show x.left ≫ (bc A φ).hom ≫ φ ≫ T.hom = Y.hom ≫ φ ≫ T.hom
    rw [← Category.assoc, Over.w x])
  have ha : u ≫ pa A φ = upa φ x := Over.OverMorphism.ext rfl
  have ht : u ≫ pt A φ = upt φ Y := Over.OverMorphism.ext (by
    show x.left ≫ (bc A φ).hom ≫ φ = Y.hom ≫ φ
    rw [← Category.assoc, Over.w x])
  have e := pull_evc hN u (pa A φ) (pt A φ)
  rw [ha, ht] at e
  exact e


variable (A) in
theorem triv_lam_twist (N : LB (A ⊗ T).left) (hF : Fam A N) : Triv (abelian₂ (bc A φ) (twist A φ N)) := by
  have hO : (twist A φ N).IsLB := pull_isLB hF.isLB _
  have hP : (abelian₂ (bc A φ) (twist A φ N)).IsLB := LB.isLB_linComb hO _ _
  refine (cls_eq_zero_iff hP).1 ?_
  have e : cls _ hP = lam (G := bc A φ) (cls (X := (bc A φ).left) _ hO) (fst (bc A φ) (bc A φ)) (snd (bc A φ) (bc A φ)) := cls_cube_two (G := bc A φ) (L := twist A φ N) hO _ _ hP
  rw [e, lam, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO,
    pull_cls_twist φ hF.isLB hO, upa_mul, upa_one, (isAdditive_iff hF.isLB).1 hF.add, hF.add.evc_one hF.isLB]
  simp only [add_sub_cancel_left, sub_self, add_zero]

end GlobalTheory.TwistFlat
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.PolyColim

variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0})

def polyDiag : J ⥤ CommRingCat.{0} where
  obj j := CommRingCat.of (Polynomial (D.obj j))
  map f := CommRingCat.ofHom (Polynomial.mapRingHom (D.map f).hom)
  map_id j := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    simp
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    simp [Polynomial.map_map]

def polyCocone (c : Cocone D) : Cocone (polyDiag D) where
  pt := CommRingCat.of (Polynomial c.pt)
  ι :=
    { app := fun j => CommRingCat.ofHom (Polynomial.mapRingHom (c.ι.app j).hom)
      naturality := fun i j f => by
        refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
        exact (Polynomial.map_map (D.map f).hom (c.ι.app j).hom (show Polynomial (D.obj i) from p)).trans
          (congrArg (fun g => Polynomial.map g (show Polynomial (D.obj i) from p))
            (by rw [← CommRingCat.hom_comp, c.w f])) }

variable {D} [IsFiltered J]

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
private lemma exists_map_eq_zero_of_isColimit_lemma {c : Cocone D} (hc : IsColimit c) {j : J}
    (x : D.obj j) (h : (c.ι.app j).hom x = 0) : ∃ (k : J) (f : j ⟶ k), (D.map f).hom x = 0 := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc x 0 (by simpa using h)
  exact ⟨k, f, by simpa using hfg⟩

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
theorem _root_.GlobalTheory.EtC.PolyColim.poly_exists_map_eq_zero {c : Cocone D} (hc : IsColimit c) {j : J}
    (p : Polynomial (D.obj j))
    (h : p.map (c.ι.app j).hom = 0) : ∃ (k : J) (f : j ⟶ k), p.map (D.map f).hom = 0 := by
  have key : ∀ s : Finset ℕ, ∃ (k : J) (f : j ⟶ k), ∀ n ∈ s, (D.map f).hom (p.coeff n) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨j, 𝟙 j, by simp⟩
    | insert a s _ ih =>
      obtain ⟨k, f, hf⟩ := ih
      have ha : (c.ι.app k).hom ((D.map f).hom (p.coeff a)) = 0 := by
        rw [← CommRingCat.comp_apply, c.w f, ← Polynomial.coeff_map, h, Polynomial.coeff_zero]
      obtain ⟨k', f', hf'⟩ := exists_map_eq_zero_of_isColimit_lemma hc _ ha
      refine ⟨k', f ≫ f', fun n hn => ?_⟩
      rw [D.map_comp, CommRingCat.comp_apply]
      rcases Finset.mem_insert.mp hn with rfl | hn
      · exact hf'
      · rw [hf n hn, map_zero]
  obtain ⟨k, f, hf⟩ := key p.support
  refine ⟨k, f, Polynomial.ext fun n => ?_⟩
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  by_cases hn : n ∈ p.support
  · exact hf n hn
  · rw [Polynomial.notMem_support_iff.mp hn, map_zero]

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
private lemma exists_rep_of_isColimit_lemma_2 {c : Cocone D} (hc : IsColimit c) (x : c.pt) :
    ∃ (j : J) (y : D.obj j), (c.ι.app j).hom y = x := by
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep D hc x
  exact ⟨j, y, hy⟩

open CategoryTheory Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) in
variable {D} [IsFiltered J] in
theorem _root_.GlobalTheory.EtC.PolyColim.poly_exists_rep {c : Cocone D} (hc : IsColimit c)
    (p : Polynomial c.pt) :
    ∃ (j : J) (y : Polynomial (D.obj j)), y.map (c.ι.app j).hom = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨i, y, hy⟩ := hp
    obtain ⟨j, z, hz⟩ := hq
    refine ⟨IsFiltered.max i j, y.map (D.map (IsFiltered.leftToMax i j)).hom +
      z.map (D.map (IsFiltered.rightToMax i j)).hom, ?_⟩
    rw [Polynomial.map_add (f := _), Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, c.w, c.w, hy, hz]
  | monomial n a =>
    obtain ⟨j, y, hy⟩ := exists_rep_of_isColimit_lemma_2 hc a
    exact ⟨j, Polynomial.monomial n y, by rw [Polynomial.map_monomial, hy]⟩

def polyCoconeIsColimit {c : Cocone D} (hc : IsColimit c) : IsColimit (polyCocone D c) := by
  haveI : ReflectsColimitsOfShape J (forget CommRingCat.{0}) := reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (polyCocone D c)) ?_ ?_)
  · intro x
    obtain ⟨j, y, hy⟩ := poly_exists_rep hc (show Polynomial c.pt from x)
    exact ⟨j, y, hy.symm⟩
  · intro i j xi xj h
    change Polynomial.map (c.ι.app i).hom xi = Polynomial.map (c.ι.app j).hom xj at h
    obtain ⟨k, f, hf⟩ := poly_exists_map_eq_zero hc (j := IsFiltered.max i j)
      ((show Polynomial (D.obj i) from xi).map (D.map (IsFiltered.leftToMax i j)).hom -
        (show Polynomial (D.obj j) from xj).map (D.map (IsFiltered.rightToMax i j)).hom) (by
        rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
          ← CommRingCat.hom_comp, c.w, c.w, h, sub_self])
    refine ⟨k, IsFiltered.leftToMax i j ≫ f, IsFiltered.rightToMax i j ≫ f, ?_⟩
    change Polynomial.map (D.map (IsFiltered.leftToMax i j ≫ f)).hom xi =
      Polynomial.map (D.map (IsFiltered.rightToMax i j ≫ f)).hom xj
    rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp, sub_eq_zero] at hf
    exact hf

end GlobalTheory.EtC.PolyColim

namespace GlobalTheory.EtC

theorem pull_spMap_comp (R : Type) [CommRing R] {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (F : Shv R) (n : ℤ) (x : H R (sp A) F n) :
    pull R (spMap (g.comp f)) F n x = pull R (spMap g) F n (pull R (spMap f) F n x) := by
  show pull R (sch.map _) F n x = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp, pull_comp]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show sch.map _ = sch.map _ ≫ sch.map _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem hInv_of_filtered_colimit : ∀ (q : ℕ) [NeZero q] (J : Type) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ j, IsUnit (q : D.obj j)) →
    (∀ j, HInv q (D.obj j)) → HInv q c.pt := by
  intro q _ J _ _ D c hc hq hH i n
  have hB : B1 := pairingProperties
  let D' := PolyColim.polyDiag D
  let c' := PolyColim.polyCocone D c
  have hc' : IsColimit c' := PolyColim.polyCoconeIsColimit hc
  obtain ⟨j0⟩ : Nonempty J := IsFiltered.nonempty
  have hqc : IsUnit (q : c.pt) := by
    have := (hq j0).map (c.ι.app j0).hom
    rwa [map_natCast] at this
  have hqP : ∀ j, IsUnit (q : D'.obj j) := fun j => by
    have := (hq j).map (Polynomial.C : D.obj j →+* Polynomial (D.obj j))
    rwa [map_natCast] at this
  have hqc' : IsUnit (q : c'.pt) := by
    have := hqc.map (Polynomial.C : c.pt →+* Polynomial c.pt)
    rwa [map_natCast] at this
  have sq : ∀ j, (c'.ι.app j).hom.comp (Polynomial.C : D.obj j →+* Polynomial (D.obj j)) =
      (Polynomial.C : c.pt →+* Polynomial c.pt).comp (c.ι.app j).hom := fun j =>
    RingHom.ext fun a => by
      change Polynomial.map (c.ι.app j).hom (Polynomial.C a) = Polynomial.C ((c.ι.app j).hom a)
      exact Polynomial.map_C _
  have sqD : ∀ {j k : J} (f : j ⟶ k), (D'.map f).hom.comp (Polynomial.C : D.obj j →+* Polynomial (D.obj j)) =
      (Polynomial.C : D.obj k →+* Polynomial (D.obj k)).comp (D.map f).hom := @fun j k f =>
    RingHom.ext fun a => by
      change Polynomial.map (D.map f).hom (Polynomial.C a) = Polynomial.C ((D.map f).hom a)
      exact Polynomial.map_C _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, rfl⟩ := (hB q D c hc n i).1 x hqc
    have e1 : pull _ (spMap (c'.ι.app j).hom) _ _ (pull _ (spMap (Polynomial.C : D.obj j →+* Polynomial (D.obj j))) _ _ y) = 0 :=
      (pull_spMap_comp (ZMod q) Polynomial.C (c'.ι.app j).hom (tw q i) n y).symm.trans
        ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y) (sq j)).trans
          ((pull_spMap_comp (ZMod q) (c.ι.app j).hom Polynomial.C (tw q i) n y).trans hx))
    obtain ⟨k, f, hf⟩ := (hB q D' c' hc' n i).2 j _ (hqP j) e1
    have e2 : pull _ (spMap (Polynomial.C : D.obj k →+* Polynomial (D.obj k))) _ _ (pull _ (spMap (D.map f).hom) _ _ y) = 0 :=
      (pull_spMap_comp (ZMod q) (D.map f).hom Polynomial.C (tw q i) n y).symm.trans
        ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y) (sqD f).symm).trans
          ((pull_spMap_comp (ZMod q) Polynomial.C (D'.map f).hom (tw q i) n y).trans hf))
    have e3 := (hH k i n).1 (e2.trans (map_zero _).symm)
    rw [← c.w f, CommRingCat.hom_comp, spMap_comp', pull_comp, e3, map_zero]
  · intro x
    obtain ⟨j, y, rfl⟩ := (hB q D' c' hc' n i).1 x hqc'
    obtain ⟨y', rfl⟩ := (hH j i n).2 y
    refine ⟨pull _ (spMap (c.ι.app j).hom) _ _ y', ?_⟩
    exact (pull_spMap_comp (ZMod q) (c.ι.app j).hom Polynomial.C (tw q i) n y').symm.trans
      ((congrArg (fun g => pull (ZMod q) (spMap g) (tw q i) n y') (sq j).symm).trans
        (pull_spMap_comp (ZMod q) Polynomial.C (c'.ι.app j).hom (tw q i) n y'))

end GlobalTheory.EtC

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ProjField
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjField

open GlobalTheory.AbelianProjective

section BaseChange

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

abbrev bcProj (X : Over S) : ((Over.pullback f).obj X).left ⟶ X.left := pullback.fst X.hom f

theorem map_left_bcProj {X Y : Over S} (g : X ⟶ Y) :
    ((Over.pullback f).map g).left ≫ bcProj f Y = bcProj f X ≫ g.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem isPullback_bcProj {X Y : Over S} (g : X ⟶ Y) :
    IsPullback (bcProj f X) ((Over.pullback f).map g).left g.left (bcProj f Y) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) (h₃₁ := f) ?_ (map_left_bcProj f g).symm
    (IsPullback.of_hasPullback Y.hom f)
  have e : ((Over.pullback f).map g).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_snd _ _ _
  rw [e, Over.w]
  exact IsPullback.of_hasPullback X.hom f

def bcProd (X Y : Over S) : ((Over.pullback f).obj X ⊗ (Over.pullback f).obj Y).left ⟶ (X ⊗ Y).left :=
  (Functor.LaxMonoidal.μ (Over.pullback f) X Y).left ≫ bcProj f (X ⊗ Y)

theorem bcProd_fst (X Y : Over S) :
    bcProd f X Y ≫ (fst X Y).left = (fst ((Over.pullback f).obj X) ((Over.pullback f).obj Y)).left ≫ bcProj f X := by
  rw [bcProd, Category.assoc, ← map_left_bcProj, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_fst]

theorem bcProd_snd (X Y : Over S) :
    bcProd f X Y ≫ (snd X Y).left = (snd ((Over.pullback f).obj X) ((Over.pullback f).obj Y)).left ≫ bcProj f Y := by
  rw [bcProd, Category.assoc, ← map_left_bcProj, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_snd]

theorem bcProd_whiskerRight {W V : Over S} (π : W ⟶ V) (X : Over S) :
    ((Over.pullback f).map π ▷ (Over.pullback f).obj X).left ≫ bcProd f V X = bcProd f W X ≫ (π ▷ X).left := by
  rw [bcProd, bcProd, ← Category.assoc, ← Over.comp_left, Functor.LaxMonoidal.μ_natural_left, Over.comp_left,
    Category.assoc, map_left_bcProj, Category.assoc]

end BaseChange

section Group

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem bcSum_eq {W X : Over S} [GrpObj X] (a : W ⟶ X) :
    (fst ((Over.pullback f).obj W) ((Over.pullback f).obj X) ≫ (Over.pullback f).map a) *
        snd ((Over.pullback f).obj W) ((Over.pullback f).obj X) =
      Functor.LaxMonoidal.μ (Over.pullback f) W X ≫ (Over.pullback f).map ((fst W X ≫ a) * snd W X) := by
  rw [Hom.mul_def, Hom.mul_def, Functor.map_comp, Functor.obj.μ_def, ← Functor.Monoidal.lift_μ]
  simp only [← Category.assoc]
  congr 2
  rw [comp_lift, Functor.map_comp, Functor.Monoidal.μ_fst_assoc, Functor.Monoidal.μ_snd]

theorem bcSum_left {W X : Over S} [GrpObj X] (a : W ⟶ X) :
    ((fst ((Over.pullback f).obj W) ((Over.pullback f).obj X) ≫ (Over.pullback f).map a) *
        snd ((Over.pullback f).obj W) ((Over.pullback f).obj X)).left ≫ bcProj f X =
      bcProd f W X ≫ ((fst W X ≫ a) * snd W X).left := by
  rw [bcSum_eq, Over.comp_left, Category.assoc, map_left_bcProj, bcProd, Category.assoc]

end Group

theorem surjective_spMap (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] : Surjective (spMap (algebraMap K Ω)) := by
  refine ⟨fun x => ?_⟩
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Sp Ω) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  exact ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩

theorem normChart_baseChange : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A],
    IsAbelianScheme A → ∀ N₀ : LB A.left, N₀.IsLB → NormChart A N₀ →
      NormChart ((Over.pullback (spMap (algebraMap K Ω))).obj A)
        (N₀.pull (pullback.fst A.hom (spMap (algebraMap K Ω)))) := by
  intro K Ω _ _ _ A _ _ N₀ hN₀ ⟨W, V, π, a, U, N, n, hπ, ha, hW, hWt, hU, hUne, hN, H, hloc⟩
  have hf := surjective_spMap K Ω
  set f := spMap (algebraMap K Ω)
  have hsurj : ∀ X : Over (Sp K), Function.Surjective (bcProj f X) := fun X =>
    (MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback X.hom f).flip hf).surj
  have sq := bcProd_whiskerRight f π A
  have pb : IsPullback (bcProd f W A) ((Over.pullback f).map π ▷ (Over.pullback f).obj A).left (π ▷ A).left
      (bcProd f V A) := by
    refine IsPullback.of_right (h₁₂ := (fst W A).left) (v₁₃ := π.left) (h₂₂ := (fst V A).left) ?_ sq.symm
      (isPullback_whiskerRight π A)
    rw [bcProd_fst, bcProd_fst]
    exact (isPullback_whiskerRight _ _).paste_horiz (isPullback_bcProj f π)
  refine ⟨(Over.pullback f).obj W, (Over.pullback f).obj V, (Over.pullback f).map π, (Over.pullback f).map a,
    bcProj f A ⁻¹ᵁ U, N.pull (bcProd f V A), GlobalTheory.Cartier.secPull n (bcProd f V A),
    MorphismProperty.of_isPullback (isPullback_bcProj f π) hπ,
    MorphismProperty.of_isPullback (isPullback_bcProj f a) ha, ?_, ?_, ?_, ?_, LB.isLB_pull hN _, ?_, ?_⟩
  · obtain ⟨w⟩ := hW
    obtain ⟨w', -⟩ := hsurj W w
    exact ⟨w'⟩
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback W.hom f) hWt
  · have : IsAffineHom (bcProj f A) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback A.hom f).flip inferInstance
    exact hU.preimage _
  · obtain ⟨u, hu⟩ := hUne
    obtain ⟨u', rfl⟩ := hsurj A u
    exact ⟨u', hu⟩
  · let r := bcProd f V A
    let b := (snd V A).left
    let d := bcProj f A
    let c := (snd ((Over.pullback f).obj V) ((Over.pullback f).obj A)).left
    change LBIso (N.pull r) ((N₀.pull d).pull c)
    refine LBIso.trans (LB.isLB_pull hN r) (LB.isLB_pull (LB.isLB_pull hN₀ b) r)
      (LB.isLB_pull (LB.isLB_pull hN₀ d) c) ?_ ?_
    · obtain ⟨w, hw⟩ := H
      exact ⟨GlobalTheory.lbIsoPull w r, ReciprocityTheory.ChartRestriction.G.DVR.linCombIso_isGen w hw _ _⟩
    · exact GlobalTheory.FiniteAmple.lbIso_pull_pull b hN₀ (bcProd_snd f V A)
  · intro x'
    rw [GlobalTheory.Cartier.nonzeroLocus_secPull]
    change bcProd f V A x' ∈ Out.nonzeroLocus n ↔ _
    rw [hloc]
    constructor
    · intro h z' hz'
      change bcProj f A (((fst _ _ ≫ (Over.pullback f).map a) * snd _ _).left z') ∈ U
      rw [← Scheme.Hom.comp_apply, bcSum_left, Scheme.Hom.comp_apply]
      refine h _ ?_
      rw [← Scheme.Hom.comp_apply, ← sq, Scheme.Hom.comp_apply, hz']
    · intro h z hz
      obtain ⟨z', rfl, hz'⟩ := Scheme.exists_preimage_of_isPullback pb z x' hz
      have h' := h z' hz'
      change bcProj f A (((fst _ _ ≫ (Over.pullback f).map a) * snd _ _).left z') ∈ U at h'
      rw [← Scheme.Hom.comp_apply, bcSum_left, Scheme.Hom.comp_apply] at h'
      exact h'

end GlobalTheory.ProjField
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.grpHom_of_proportional_generating_combinations : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (T : Scheme.{0}) (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Ψ : A'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(T, ⊤)), Hyps L M k bA bB eA eB → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → Ψ ≫ GlobalTheory.HomFixUniv.fA B = A'.hom ≫ t → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom Ψ c → GlobalTheory.HomFixUniv.Normal t c αA βB → ∃ Φ : A' ⟶ B', IsMonHom Φ ∧ Φ.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B = Ψ := by
  first | (exact @GlobalTheory.HomFixUniv.hom_of_proport) | (exact GlobalTheory.HomFixUniv.hom_of_proport) | (intros; apply GlobalTheory.HomFixUniv.hom_of_proport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.germ_form_pulledBack_combinations_expand_monomials : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg (mA * mB) → ∀ (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q : N.ι), φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ g ≫ affπ Rg (mA * mB)) z) (comb a φ p (matOf g) z q) F = ∑ ν ∈ (GlobalTheory.FormsLocus.expand mA mB F).support, gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g ((GlobalTheory.FormsLocus.expand mA mB F).coeff ν)) * gs φ z (N.U q) ((GlobalTheory.FormsLocus.monSec a d ν).f q) := by
  first | (exact @GlobalTheory.FormsLocus.germ_eval_comb) | (exact GlobalTheory.FormsLocus.germ_eval_comb) | (intros; apply GlobalTheory.FormsLocus.germ_eval_comb  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_lagrangian_lift_lie_squareZero_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (φ : LinearMap.BilinForm C H), (∀ x y, φ x y = -φ y x) → Function.Bijective φ → (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ E : Submodule C H, (∃ M : Submodule C H, IsCompl E M) ∧ E ⊔ I • ⊤ = F ∧ (∀ (c : D.O), ∀ x ∈ E, ρ c x ∈ E) ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ ∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ E → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E := by
  first | exact @GlobalTheory.HTSummand.exists_lagrangian_lift_lie | exact GlobalTheory.HTSummand.exists_lagrangian_lift_lie | (intros; apply GlobalTheory.HTSummand.exists_lagrangian_lift_lie <;> assumption)
end
