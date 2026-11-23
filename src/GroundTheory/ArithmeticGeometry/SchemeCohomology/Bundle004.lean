module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle001
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}}

noncomputable def sectionValue [IsIntegral X] (V : X.Opens) (y : V) :
    Γ(X, V) →+* X.functionField :=
  (algebraMap (X.presheaf.stalk y) X.functionField).comp (X.presheaf.germ V y y.2).hom

lemma sectionValue_eq [IsIntegral X] (V : X.Opens) (y : V) (r : Γ(X, V)) :
    sectionValue V y r = (haveI : Nonempty V := ⟨y⟩; X.germToFunctionField V r) := by
  have : Nonempty V := ⟨y⟩
  exact Scheme.algebraMap_germ_eq_germToFunctionField X y.2 r

lemma sectionValue_res [IsIntegral X] {V W : X.Opens} (h : W ≤ V) (y : W) (r : Γ(X, V)) :
    sectionValue W y (X.presheaf.map (homOfLE h).op r) = sectionValue V ⟨y.1, h y.2⟩ r := by
  simp only [sectionValue, RingHom.comp_apply]
  congr 1
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

lemma sectionValue_const [IsIntegral X] (V : X.Opens) (y z : V) (r : Γ(X, V)) :
    sectionValue V y r = sectionValue V z r := by
  rw [sectionValue_eq, sectionValue_eq]

def PrimeDivisor.ofPoint (y : X) (hy : ringKrullDim (X.presheaf.stalk y) = 1) : PrimeDivisor X :=
  ⟨y, hy⟩

section

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

def divisorPredicate (D : WeilDivisor X) :
    TopCat.LocalPredicate (X := X.carrier) (fun _ => X.functionField) where
  pred {V} f := (∀ y : V, ∃ W : X.Opens, y.1 ∈ W ∧ ∀ z : V, z.1 ∈ W → f z = f y) ∧
    ∀ (y : V) (hy : ringKrullDim (X.presheaf.stalk y.1) = 1),
      (PrimeDivisor.ofPoint y.1 hy).valuation (f y) ≤ WithZero.exp (D (PrimeDivisor.ofPoint y.1 hy))
  res {V W} i f h := by
    refine ⟨fun y => ?_, fun y hy => h.2 (i y) hy⟩
    obtain ⟨W', hyW', hW'⟩ := h.1 (i y)
    exact ⟨W', hyW', fun z hz => hW' (i z) hz⟩
  locality {V} f w := by
    refine ⟨fun y => ?_, fun y hy => ?_⟩
    · obtain ⟨W, hyW, i, hW⟩ := w y
      obtain ⟨W', hyW', hW'⟩ := hW.1 ⟨y.1, hyW⟩
      refine ⟨W ⊓ W', ⟨hyW, hyW'⟩, fun z hz => ?_⟩
      exact hW' ⟨z.1, hz.1⟩ hz.2
    · obtain ⟨W, hyW, i, hW⟩ := w y
      exact hW.2 ⟨y.1, hyW⟩ hy

lemma PrimeDivisor.valuation_algebraMap_le_one (Z : PrimeDivisor X)
    (a : X.presheaf.stalk Z.point) : Z.valuation (algebraMap _ X.functionField a) ≤ 1 := by
  have := Z.isDedekindDomain_stalk
  simp only [PrimeDivisor.valuation]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _

def divisorSections (D : WeilDivisor X) (V : X.Opens) : AddSubgroup (V → X.functionField) where
  carrier := {f | (divisorPredicate D).pred f}
  zero_mem' := ⟨fun _ => ⟨⊤, trivial, fun _ _ => rfl⟩, fun y hy => by simp⟩
  add_mem' {f g} hf hg := by
    refine ⟨fun y => ?_, fun y hy => ?_⟩
    · obtain ⟨W₁, hy₁, h₁⟩ := hf.1 y
      obtain ⟨W₂, hy₂, h₂⟩ := hg.1 y
      exact ⟨W₁ ⊓ W₂, ⟨hy₁, hy₂⟩, fun z hz => by
        simp only [Pi.add_apply, h₁ z hz.1, h₂ z hz.2]⟩
    · exact (Valuation.map_add _ _ _).trans (max_le (hf.2 y hy) (hg.2 y hy))
  neg_mem' {f} hf := by
    refine ⟨fun y => ?_, fun y hy => ?_⟩
    · obtain ⟨W, hyW, h⟩ := hf.1 y
      exact ⟨W, hyW, fun z hz => by simp only [Pi.neg_apply, h z hz]⟩
    · simp only [Pi.neg_apply, Valuation.map_neg]
      exact hf.2 y hy

lemma smul_mem_divisorSections (D : WeilDivisor X) (V : X.Opens) (r : Γ(X, V))
    {f : V → X.functionField} (hf : f ∈ divisorSections D V) :
    (fun y => sectionValue V y r * f y) ∈ divisorSections D V := by
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨W, hyW, h⟩ := hf.1 y
    exact ⟨W, hyW, fun z hz => by simp only [h z hz, sectionValue_const V z y r]⟩
  · simp only [map_mul]
    calc _ ≤ 1 * WithZero.exp (D (PrimeDivisor.ofPoint y.1 hy)) :=
          mul_le_mul' ((PrimeDivisor.ofPoint y.1 hy).valuation_algebraMap_le_one
            (X.presheaf.germ V y.1 y.2 r)) (hf.2 y hy)
      _ = _ := one_mul _

noncomputable instance (D : WeilDivisor X) (V : X.Opens) :
    Module Γ(X, V) (divisorSections D V) where
  smul r f := ⟨fun y => sectionValue V y r * f.1 y, smul_mem_divisorSections D V r f.2⟩
  one_smul f := Subtype.ext (funext fun y => by
    change sectionValue V y 1 * f.1 y = f.1 y
    rw [map_one, one_mul])
  mul_smul r s f := Subtype.ext (funext fun y => by
    change sectionValue V y (r * s) * f.1 y = sectionValue V y r * (sectionValue V y s * f.1 y)
    rw [map_mul, mul_assoc])
  smul_zero r := Subtype.ext (funext fun y => by
    change sectionValue V y r * 0 = 0
    rw [mul_zero])
  smul_add r f g := Subtype.ext (funext fun y => by
    change sectionValue V y r * (f.1 y + g.1 y) = sectionValue V y r * f.1 y +
      sectionValue V y r * g.1 y
    rw [mul_add])
  add_smul r s f := Subtype.ext (funext fun y => by
    change sectionValue V y (r + s) * f.1 y = sectionValue V y r * f.1 y +
      sectionValue V y s * f.1 y
    rw [map_add (f := _), add_mul])
  zero_smul f := Subtype.ext (funext fun y => by
    change sectionValue V y 0 * f.1 y = 0
    rw [map_zero, zero_mul])

def divisorSectionsRes (D : WeilDivisor X) {V W : X.Opens} (h : W ≤ V) :
    divisorSections D V →+ divisorSections D W where
  toFun f := ⟨fun y => f.1 ⟨y.1, h y.2⟩, (divisorPredicate D).res (homOfLE h) f.1 f.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def divisorPresheaf (D : WeilDivisor X) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (divisorSections D V.unop)
  map i := AddCommGrpCat.ofHom (divisorSectionsRes D i.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable instance (D : WeilDivisor X) (V : (Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj V) ((divisorPresheaf D).obj V) :=
  inferInstanceAs (Module Γ(X, V.unop) (divisorSections D V.unop))

noncomputable def divisorPresheafOfModules (D : WeilDivisor X) :
    PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (divisorPresheaf D) (fun {V W} i r f => by
    apply Subtype.ext
    funext y
    exact congrArg (· * f.1 ⟨y.1, i.unop.le y.2⟩)
      (sectionValue_res i.unop.le y (show Γ(X, V.unop) from r)).symm)

theorem divisorPresheaf_isSheaf (D : WeilDivisor X) :
    TopCat.Presheaf.IsSheaf (X := X.carrier) (divisorPresheaf D) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]
  refine TopCat.Presheaf.isSheaf_of_iso ?_
    (TopCat.subpresheafToTypes.isSheaf (divisorPredicate D))
  refine NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f.1, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) ?_
  intro V W i
  rfl

noncomputable def divisorSheaf (D : WeilDivisor X) : X.Modules :=
  SheafOfModules.mk (divisorPresheafOfModules D) (divisorPresheaf_isSheaf D)

lemma PrimeDivisor.valuation_le_exp_iff (Z : PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0)
    (n : ℤ) : Z.valuation f ≤ WithZero.exp n ↔ -n ≤ Z.ord f := by
  have hv0 : Z.valuation f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  rw [← WithZero.log_le_iff_le_exp hv0, PrimeDivisor.ord]
  omega

end

section Basis

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

end Basis

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry MvPolynomial HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable (A : Type u) [CommRing A] {n : ℕ} (i : Fin (n + 1))

abbrev Chart := Away (grading A n) (X i : MvPolynomial (Fin (n + 1)) A)

abbrev ChartLoc := Localization.Away (X i : MvPolynomial (Fin (n + 1)) A)

def dehom : MvPolynomial (Fin (n + 1)) A →+* MvPolynomial {j // j ≠ i} A :=
  eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)

lemma dehom_X_self : dehom A i (X i) = 1 := by simp [dehom]

lemma dehom_X_of_ne (j : Fin (n + 1)) (h : j ≠ i) : dehom A i (X j) = X ⟨j, h⟩ := by
  simp [dehom, h]

lemma dehom_C (a : A) : dehom A i (C a) = C a := by simp [dehom]

def chartToPoly : Chart A i →+* MvPolynomial {j // j ≠ i} A :=
  (Localization.awayLift (dehom A i) (X i) (by rw [dehom_X_self]; exact isUnit_one)).comp
    (algebraMap (Chart A i) (ChartLoc A i))

def coordinate (j : {j // j ≠ i}) : Chart A i :=
  Away.mk (grading A n) (X_mem i) 1 (X j.1) (by simpa using X_mem (A := A) j.1)

def polyToChart : MvPolynomial {j // j ≠ i} A →+* Chart A i :=
  eval₂Hom ((fromZeroRingHom (grading A n) _).comp (algebraMap A (grading A n 0)))
    (coordinate A i)

def scaleMap : MvPolynomial (Fin (n + 1)) A →+* ChartLoc A i :=
  eval₂Hom ((algebraMap (MvPolynomial (Fin (n + 1)) A) (ChartLoc A i)).comp C)
    (fun j => algebraMap (MvPolynomial (Fin (n + 1)) A) (ChartLoc A i) (X j) *
      IsLocalization.Away.invSelf (S := ChartLoc A i) (X i : MvPolynomial (Fin (n + 1)) A))

end ProjSpace

namespace ProjSpace

variable (A : Type u) [CommRing A] {n : ℕ} (i : Fin (n + 1))

local notation "Pn" => MvPolynomial (Fin (n + 1)) A
local notation "xinv" => IsLocalization.Away.invSelf (S := ChartLoc A i)
  (X i : MvPolynomial (Fin (n + 1)) A)

lemma algebraMap_X_mul_invSelf :
    algebraMap (MvPolynomial (Fin (n + 1)) A) (ChartLoc A i) (X i) * xinv = 1 :=
  IsLocalization.Away.mul_invSelf _

lemma val_coordinate (j : {j // j ≠ i}) :
    (coordinate A i j).val = algebraMap Pn (ChartLoc A i) (X j.1) * xinv := by
  rw [coordinate, Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one,
    IsLocalization.Away.invSelf]
  congr 2
  exact Subtype.ext (pow_one _)

lemma val_polyToChart_C (a : A) :
    (polyToChart A i (C a)).val = algebraMap Pn (ChartLoc A i) (C a) := by
  simp [polyToChart, fromZeroRingHom]
  rfl

lemma scaleMap_eq :
    (algebraMap (Chart A i) (ChartLoc A i)).comp ((polyToChart A i).comp (dehom A i)) =
      scaleMap A i := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, dehom_C, HomogeneousLocalization.algebraMap_apply]
    rw [val_polyToChart_C]
    simp [scaleMap]
  · intro j
    simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
    by_cases h : j = i
    · subst h
      rw [dehom_X_self, map_one, val_one]
      simp only [scaleMap, coe_eval₂Hom, eval₂_X]
      exact (algebraMap_X_mul_invSelf A j).symm
    · rw [dehom_X_of_ne A i j h]
      simp only [polyToChart, coe_eval₂Hom, eval₂_X, scaleMap]
      exact val_coordinate A i ⟨j, h⟩

lemma scaleMap_monomial (e : Fin (n + 1) →₀ ℕ) (c : A) :
    scaleMap A i (monomial e c) * algebraMap Pn (ChartLoc A i) (X i ^ e.degree) =
      algebraMap Pn (ChartLoc A i) (monomial e c) := by
  have hdeg : e.degree = ∑ j ∈ e.support, e j := rfl
  have hinv : (e.prod fun _ k => xinv ^ k) * algebraMap Pn (ChartLoc A i) (X i ^ e.degree) = 1 := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, map_pow, ← hdeg, ← mul_pow, mul_comm,
      algebraMap_X_mul_invSelf, one_pow]
  simp only [scaleMap, coe_eval₂Hom, eval₂_monomial, RingHom.comp_apply]
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul, mul_assoc, mul_assoc, hinv, mul_one, monomial_eq, map_mul, map_finsuppProd]
  simp only [map_pow]

lemma scaleMap_homog {m : ℕ} {a : Pn} (ha : a ∈ grading A n m) :
    scaleMap A i a * algebraMap Pn (ChartLoc A i) (X i ^ m) = algebraMap Pn (ChartLoc A i) a := by
  have hh : a.IsHomogeneous m := (mem_homogeneousSubmodule m a).1 ha
  conv_lhs => rw [a.as_sum]
  conv_rhs => rw [a.as_sum]

  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hdeg : e.degree = m := by
    have := hh (mem_support_iff.mp he)
    rwa [Finsupp.degree_eq_weight_one]
  rw [← hdeg]
  exact scaleMap_monomial A i e _

lemma chartToPoly_mk (m : ℕ) (a : Pn) (ha : a ∈ grading A n (m • 1)) :
    chartToPoly A i (Away.mk (grading A n) (X_mem i) m a ha) = dehom A i a := by
  have := Localization.awayLift_mk (dehom A i) (X i) a 1 (by rw [dehom_X_self, one_mul]) m
  simp only [chartToPoly, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  refine this.trans ?_
  rw [one_pow, mul_one]

lemma chartToPoly_algebraMap (a : Pn) (h) :
    Localization.awayLift (dehom A i) (X i) h (algebraMap Pn (ChartLoc A i) a) = dehom A i a :=
  IsLocalization.Away.lift_eq _ _ a

lemma chartToPoly_polyToChart : (chartToPoly A i).comp (polyToChart A i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, RingHom.id_apply, chartToPoly,
      HomogeneousLocalization.algebraMap_apply]
    rw [val_polyToChart_C, chartToPoly_algebraMap, dehom_C]
  · intro j
    simp only [RingHom.comp_apply, RingHom.id_apply, polyToChart, coe_eval₂Hom, eval₂_X,
      coordinate]
    rw [chartToPoly_mk, dehom_X_of_ne A i j.1 j.2]

lemma polyToChart_chartToPoly : (polyToChart A i).comp (chartToPoly A i) = RingHom.id _ := by
  ext z : 1
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective (grading A n) (X_mem i) z
  rw [RingHom.comp_apply, chartToPoly_mk, RingHom.id_apply]
  apply HomogeneousLocalization.val_injective
  have h1 := congrArg (fun φ => φ a) (scaleMap_eq A i)
  simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply] at h1
  rw [h1, Away.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  have := scaleMap_homog A i (m := m) (a := a) (by simpa using ha)
  exact this

def chartEquiv : Chart A i ≃+* MvPolynomial {j // j ≠ i} A :=
  RingEquiv.ofRingHom (chartToPoly A i) (polyToChart A i) (chartToPoly_polyToChart A i)
    (polyToChart_chartToPoly A i)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end
