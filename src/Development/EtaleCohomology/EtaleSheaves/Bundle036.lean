module

public import Development.EtaleCohomology.EtaleSheaves.Bundle020
public import Development.EtaleCohomology.EtaleSheaves.Bundle021
public import Development.EtaleCohomology.EtaleSheaves.Bundle022
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
public import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.shiftPf

theorem conj_iff {α β γ δ : Type*} (F : α → β) (G : γ → δ) (e1 : α ≃ γ) (e2 : β ≃ δ)
    (h : ∀ x, G (e1 x) = e2 (F x)) :
    (Function.Bijective F ↔ Function.Bijective G) ∧ (Function.Injective F ↔ Function.Injective G) := by
  have hG : G = e2 ∘ F ∘ e1.symm := funext fun y => by simpa using h (e1.symm y)
  have hF : F = e2.symm ∘ G ∘ e1 := funext fun x => by simp [h]
  refine ⟨⟨fun hb => ?_, fun hb => ?_⟩, ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · rw [hG]; exact e2.bijective.comp (hb.comp e1.symm.bijective)
  · rw [hF]; exact e2.symm.bijective.comp (hb.comp e1.bijective)
  · rw [hG]; exact e2.injective.comp (hb.comp e1.symm.injective)
  · rw [hF]; exact e2.symm.injective.comp (hb.comp e1.injective)

section Cat
variable {C : Type*} [Category C]

abbrev pre {X X' : C} (u : X ⟶ X') (Y : C) : (X' ⟶ Y) → (X ⟶ Y) := fun h => u ≫ h

theorem pre_conj {W W' X X' : C} (u' : W ⟶ W') (u : X ⟶ X') (a : W ≅ X) (b : W' ≅ X')
    (h : u' ≫ b.hom = a.hom ≫ u) (Y : C) :
    (Function.Bijective (pre u Y) ↔ Function.Bijective (pre u' Y)) ∧
      (Function.Injective (pre u Y) ↔ Function.Injective (pre u' Y)) :=
  conj_iff _ _ ((Iso.homCongr b.symm (Iso.refl Y))) ((Iso.homCongr a.symm (Iso.refl Y))) (fun x => by
    simp only [pre, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, h, Category.assoc])

theorem pre_target {X X' Y Y' : C} (u : X ⟶ X') (e : Y ≅ Y') :
    (Function.Bijective (pre u Y) ↔ Function.Bijective (pre u Y')) ∧
      (Function.Injective (pre u Y) ↔ Function.Injective (pre u Y')) :=
  conj_iff _ _ (Iso.homCongr (Iso.refl X') e) (Iso.homCongr (Iso.refl X) e) (fun x => by
    simp [pre, Iso.homCongr_apply])

theorem pre_shift [HasShift C ℤ] {X X' : C} (u : X ⟶ X') (p : ℤ) (Y : C) :
    (Function.Bijective (pre (u⟦p⟧') Y) ↔ Function.Bijective (pre u (Y⟦-p⟧))) ∧
      (Function.Injective (pre (u⟦p⟧') Y) ↔ Function.Injective (pre u (Y⟦-p⟧))) :=
  conj_iff _ _ ((shiftEquiv C p).toAdjunction.homEquiv X' Y) ((shiftEquiv C p).toAdjunction.homEquiv X Y) (fun x => by
    simp only [pre]
    exact ((shiftEquiv C p).toAdjunction.homEquiv_naturality_left u x).symm)

end Cat

variable {R : Type} [CommRing R]

abbrev Qt (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

theorem toHom_cpull {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    CohomologyClass.toHom (cpull f I n x) = (Qt R).map f ≫ CohomologyClass.toHom x := by
  obtain ⟨b, rfl⟩ := x.mk_surjective
  rw [cpull, cpre_mk, CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, ← Functor.map_comp,
    ← Cocycle.equivHomShift_symm_precomp]
  congr 2

theorem cpull_iff {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) :
    (Function.Bijective (cpull f I n) ↔ Function.Bijective (pre ((Qt R).map f) ((Qt R).obj (I⟦n⟧)))) ∧
      (Function.Injective (cpull f I n) ↔ Function.Injective (pre ((Qt R).map f) ((Qt R).obj (I⟦n⟧)))) :=
  conj_iff _ _ (CohomologyClass.homAddEquiv (K := L) (L := I) (n := n)).toEquiv
    (CohomologyClass.homAddEquiv (K := K) (L := I) (n := n)).toEquiv (fun x => by
      simp [toHom_cpull])

theorem main_iff (I : Cx R) {A B : Shv R} (φ : A ⟶ B) (P j : ℤ) :
    (Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - P)) ↔
      Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) (-P)).map φ) I j)) ∧
    (Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - P)) ↔
      Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) (-P)).map φ) I j)) := by
  let s0 := (CochainComplex.singleFunctor (Shv R) 0).map φ
  let sp := (CochainComplex.singleFunctor (Shv R) (-P)).map φ
  let E := (CochainComplex.singleFunctors (Shv R)).shiftIso P (-P) 0 (by omega)
  obtain ⟨b1, i1⟩ := cpull_iff sp I j
  obtain ⟨b2, i2⟩ := pre_conj ((Qt R).map sp) ((Qt R).map (s0⟦P⟧'))
    ((Qt R).mapIso (E.symm.app A)) ((Qt R).mapIso (E.symm.app B)) (by
      simp only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, ← Functor.map_comp]
      congr 1
      exact E.inv.naturality φ) ((Qt R).obj (I⟦j⟧))
  obtain ⟨b3, i3⟩ := pre_conj ((Qt R).map (s0⟦P⟧')) (((Qt R).map s0)⟦P⟧')
    (((Qt R).commShiftIso P).app _) (((Qt R).commShiftIso P).app _)
    (((Qt R).commShiftIso P).hom.naturality s0) ((Qt R).obj (I⟦j⟧))
  obtain ⟨b4, i4⟩ := pre_shift ((Qt R).map s0) P ((Qt R).obj (I⟦j⟧))
  obtain ⟨b5, i5⟩ := pre_target ((Qt R).map s0)
    ((((Qt R).commShiftIso (-P)).symm.app (I⟦j⟧)) ≪≫
      (Qt R).mapIso ((shiftFunctorAdd' (Cx R) j (-P) (j - P) (by omega)).symm.app I))
  obtain ⟨b6, i6⟩ := cpull_iff s0 I (j - P)
  exact ⟨b6.trans (b5.symm.trans (b4.symm.trans (b3.trans (b2.trans b1.symm)))),
    i6.trans (i5.symm.trans (i4.symm.trans (i3.trans (i2.trans i1.symm))))⟩

theorem shift_of : LateralTheory.E.CxDescPf.shift := by
  intro R _ I A B φ p j
  obtain ⟨hb, hi⟩ := main_iff I φ (p : ℤ) j
  exact ⟨hb.1, hi.1⟩

end LateralTheory.E.shiftPf
end
end

section

noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.LocAtPf

structure DivIdx {A : Type} [CommRing A] (S : Submonoid A) : Type where
  val : S

variable {A : Type} [CommRing A] (S : Submonoid A)

instance : Preorder (DivIdx S) where
  le a b := ∃ c : A, (b.val : A) = (a.val : A) * c
  le_refl a := ⟨1, (mul_one _).symm⟩
  le_trans a b c := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, by rw [hy, hx, mul_assoc]⟩

instance : IsDirected (DivIdx S) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.val * b.val⟩, ⟨(b.val : A), by simp⟩, ⟨(a.val : A), by simp [mul_comm]⟩⟩⟩

instance : Nonempty (DivIdx S) := ⟨⟨1⟩⟩

lemma one_le (a : DivIdx S) : (⟨1⟩ : DivIdx S) ≤ a := ⟨(a.val : A), by simp⟩

lemma unit_of_le {a b : DivIdx S} (h : a ≤ b) :
    IsUnit (algebraMap A (Localization.Away (b.val : A)) (a.val : A)) := by
  obtain ⟨c, hc⟩ := h
  have hb := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (b.val : A)) (b.val : A)
  have e : algebraMap A (Localization.Away (b.val : A)) (b.val : A) =
      algebraMap A (Localization.Away (b.val : A)) (a.val : A) * algebraMap A (Localization.Away (b.val : A)) c := by
    rw [← map_mul, ← hc]
  rw [e] at hb
  exact isUnit_of_mul_isUnit_left hb

def tr {a b : DivIdx S} (h : a ≤ b) :
    Localization.Away (a.val : A) →+* Localization.Away (b.val : A) :=
  IsLocalization.Away.lift (a.val : A) (unit_of_le S h)

lemma tr_alg {a b : DivIdx S} (h : a ≤ b) (x : A) :
    tr S h (algebraMap A _ x) = algebraMap A _ x :=
  IsLocalization.Away.lift_eq _ _ x

def Dg : DivIdx S ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away (a.val : A))
  map {a b} f := CommRingCat.ofHom (tr S f.le)
  map_id a := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (a.val : A))
    ext x; simp [tr_alg]
  map_comp {a b c} f g := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (a.val : A))
    ext x; simp [tr_alg]

def tN : (Functor.const (DivIdx S)).obj (CommRingCat.of A) ⟶ Dg S where
  app a := CommRingCat.ofHom (algebraMap A (Localization.Away (a.val : A)))
  naturality a b f := by
    apply CommRingCat.hom_ext; ext x
    exact (tr_alg S f.le x).symm

lemma away_ext (a : DivIdx S) {R : CommRingCat.{0}} {f g : (Dg S).obj a ⟶ R}
    (h : ∀ x : A, f ((tN S).app a x) = g ((tN S).app a x)) : f = g := by
  apply CommRingCat.hom_ext
  exact IsLocalization.ringHom_ext (M := Submonoid.powers (a.val : A))
    (S := Localization.Away (a.val : A)) (RingHom.ext h)

variable (B : Type) [CommRing B] [Algebra A B] [IsLocalization S B]

def sApp (a : DivIdx S) : CommRingCat.of (Localization.Away (a.val : A)) ⟶ CommRingCat.of B :=
  CommRingCat.ofHom (IsLocalization.Away.lift (a.val : A) (IsLocalization.map_units B a.val))

lemma sApp_tN (a : DivIdx S) (x : A) : sApp S B a ((tN S).app a x) = algebraMap A B x :=
  IsLocalization.Away.lift_eq _ (IsLocalization.map_units B a.val) x

def sN : Dg S ⟶ (Functor.const (DivIdx S)).obj (CommRingCat.of B) where
  app a := sApp S B a
  naturality a b f := by
    apply CommRingCat.hom_ext
    refine IsLocalization.ringHom_ext (M := Submonoid.powers (a.val : A))
      (S := Localization.Away (a.val : A)) (RingHom.ext fun x => ?_)
    change IsLocalization.Away.lift (b.val : A) (IsLocalization.map_units B b.val) (tr S f.le (algebraMap A _ x)) =
      IsLocalization.Away.lift (a.val : A) (IsLocalization.map_units B a.val) (algebraMap A _ x)
    rw [tr_alg, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]

lemma cocone_alg (c : Cocone (Dg S)) (a : DivIdx S) :
    (tN S).app a ≫ c.ι.app a = (tN S).app ⟨1⟩ ≫ c.ι.app ⟨1⟩ := by
  rw [← c.w (homOfLE (one_le S a)), ← Category.assoc, ← (tN S).naturality]
  simp

def g0 (c : Cocone (Dg S)) : A →+* c.pt := ((tN S).app ⟨1⟩ ≫ c.ι.app ⟨1⟩).hom

lemma awayDivisibilityCocone_baseHom_submonoid_isUnit (c : Cocone (Dg S)) (s : S) : IsUnit (g0 S c (s : A)) := by
  have e : g0 S c (s : A) = c.ι.app ⟨s⟩ ((tN S).app ⟨s⟩ (s : A)) := by
    rw [← CategoryTheory.comp_apply, cocone_alg]; rfl
  rw [e]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (s : A)) (s : A)).map
    (c.ι.app ⟨s⟩).hom

def isColim : IsColimit (Cocone.mk (CommRingCat.of B) (sN S B)) where
  desc c := CommRingCat.ofHom (IsLocalization.lift (M := S) (S := B) (g := g0 S c) (awayDivisibilityCocone_baseHom_submonoid_isUnit S c))
  fac c a := by
    apply away_ext S a
    intro x
    rw [CategoryTheory.comp_apply]
    change CommRingCat.Hom.hom _ (sApp S B a ((tN S).app a x)) = _
    rw [sApp_tN]
    change IsLocalization.lift _ (algebraMap A B x) = _
    rw [IsLocalization.lift_eq, ← CategoryTheory.comp_apply, cocone_alg]
    rfl
  uniq c m hm := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext S
    ext x
    change m.hom (algebraMap A B x) = IsLocalization.lift _ (algebraMap A B x)
    rw [IsLocalization.lift_eq, ← sApp_tN S B ⟨1⟩ x]
    have := congrArg (fun f => f ((tN S).app ⟨1⟩ x)) (hm ⟨1⟩)
    simp only [CategoryTheory.comp_apply] at this
    exact this

theorem locIE (S : Submonoid A) (B : Type) [CommRing B] [Algebra A B] [IsLocalization S B] :
    IE (CommRingCat.ofHom (algebraMap A B)) := by
  refine ⟨DivIdx S, inferInstance, inferInstance, Dg S, tN S, sN S B, isColim S B, fun a => ⟨?_, ?_⟩⟩
  · show RingHom.Etale (CommRingCat.Hom.hom (CommRingCat.ofHom (algebraMap A (Localization.Away (a.val : A)))))
    rw [CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
    infer_instance
  · apply CommRingCat.hom_ext; ext x
    exact sApp_tN S B a x

theorem LocAt_of : LateralTheory.E.SHExistsPf.LocAt := by
  intro A r _
  exact locIE r.primeCompl (Localization.AtPrime r)

end LateralTheory.E.LocAtPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut Polynomial

namespace LateralTheory.E.SHLocPf

def EtClosed {O Ω : Type} [CommRing O] [Field Ω] (ψ : O →+* Ω) : Prop :=
  ∀ (C : Type) [CommRing C] [Algebra O C] [Algebra.Etale O C] (χ : C →+* Ω),
    χ.comp (algebraMap O C) = ψ → ∃ s : C →ₐ[O] O, ψ.comp s.toRingHom = χ

def Build : Prop := ∀ (A : CommRingCat.{0}) [IsLocalRing A],
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (ψ : O →+* Ω),
    IE f ∧ Function.Surjective ψ ∧ (∀ a : A, a ∈ IsLocalRing.maximalIdeal A → ψ (f.hom a) = 0) ∧ EtClosed ψ

def Lift : Prop := ∀ (O Ω : Type) [CommRing O] [Field Ω] (ψ : O →+* Ω), EtClosed ψ →
  ∀ p : O[X], p.Monic → ∀ a₀ : O, ψ (p.eval a₀) = 0 → ψ (p.derivative.eval a₀) ≠ 0 →
    ∃ a : O, p.IsRoot a ∧ ψ a = ψ a₀

def Colim : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (ψ : O →+* Ω), IE f ∧ ψ.comp f.hom = ι ∧ EtClosed ψ

theorem unit_of_etClosed {O Ω : Type} [CommRing O] [Field Ω] (ψ : O →+* Ω) (h : EtClosed ψ)
    (x : O) (hx : ψ x ≠ 0) : IsUnit x := by
  have hu : IsUnit (ψ x) := isUnit_iff_ne_zero.mpr hx
  let χ : Localization.Away x →+* Ω := IsLocalization.Away.lift x hu
  have hχ : χ.comp (algebraMap O (Localization.Away x)) = ψ := IsLocalization.Away.lift_comp x hu
  obtain ⟨s, -⟩ := h (Localization.Away x) χ hχ
  refine IsUnit.of_mul_eq_one (b :=  s (IsLocalization.Away.invSelf x)) ?_
  have e := congrArg s (IsLocalization.Away.mul_invSelf (S := Localization.Away x) x)
  rw [map_mul, map_one, AlgHom.commutes] at e
  simpa using e

theorem etaleClosed_point_lifts_simple_roots_monic : Lift := by
  intro O Ω _ _ ψ hE p hp a₀ h₁ h₂
  letI : Algebra O Ω := ψ.toAlgebra
  let P : StandardEtalePair O := ⟨p, hp, p.derivative, ⟨1, 0, 1, by ring⟩⟩
  have hev : ∀ q : O[X], aeval (ψ a₀) q = ψ (q.eval a₀) := by
    intro q
    rw [Polynomial.aeval_def]; exact Polynomial.eval₂_at_apply (p := q) ψ a₀
  have hM : P.HasMap (ψ a₀) := ⟨by rw [hev]; exact h₁, by rw [hev]; exact isUnit_iff_ne_zero.mpr h₂⟩
  let χ : P.Ring →+* Ω := (P.lift (ψ a₀) hM).toRingHom
  have hχ : χ.comp (algebraMap O P.Ring) = ψ := (P.lift (ψ a₀) hM).comp_algebraMap
  obtain ⟨s, hs⟩ := hE P.Ring χ hχ
  refine ⟨s P.X, ?_, ?_⟩
  · have h0 : aeval P.X P.f = 0 := P.hasMap_X.1
    have h1 := congrArg s h0
    rw [map_zero, ← Polynomial.aeval_algHom_apply] at h1
    rw [Polynomial.IsRoot.def, ← Polynomial.coe_aeval_eq_eval]
    exact h1
  · have := congrArg (fun g => g P.X) hs
    simp only [RingHom.comp_apply] at this
    rw [show ψ (s P.X) = χ P.X from this]
    exact P.lift_X (ψ a₀) hM

theorem build_of (hC : Colim) : Build := by
  intro A _
  let k := IsLocalRing.ResidueField A
  let ι : A →+* SeparableClosure k := (algebraMap k (SeparableClosure k)).comp (IsLocalRing.residue A)
  obtain ⟨O, f, ψ, hIE, hcomp, hE⟩ := hC A (SeparableClosure k) ι
  refine ⟨O, f, SeparableClosure k, inferInstance, inferInstance, ψ, hIE, ?_, ?_, hE⟩
  · intro ω
    have hsep : (minpoly k ω).Separable := Algebra.IsSeparable.isSeparable k ω
    have hmon : (minpoly k ω).Monic := minpoly.monic (Algebra.IsSeparable.isIntegral k ω)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      ((Polynomial.lifts_iff_coeff_lifts _).2 (fun n => IsLocalRing.residue_surjective _)) hmon
    letI : Algebra O (SeparableClosure k) := ψ.toAlgebra
    let P : StandardEtalePair O :=
      ⟨q.map f.hom, hqm.map _, (q.map f.hom).derivative, ⟨1, 0, 1, by ring⟩⟩
    have hev : ∀ r : A[X], aeval ω (r.map f.hom) = aeval ω (r.map (IsLocalRing.residue A)) := by
      intro r
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_map]
      congr 1
    have hM : P.HasMap ω := by
      refine ⟨?_, ?_⟩
      · change aeval ω (q.map f.hom) = 0
        rw [hev, hq]; exact minpoly.aeval k ω
      · change IsUnit (aeval ω (q.map f.hom).derivative)
        rw [Polynomial.derivative_map, hev, ← Polynomial.derivative_map, hq]
        exact isUnit_iff_ne_zero.mpr (hsep.aeval_derivative_ne_zero (minpoly.aeval k ω))
    let χ : P.Ring →+* SeparableClosure k := (P.lift ω hM).toRingHom
    have hχ : χ.comp (algebraMap O P.Ring) = ψ := (P.lift ω hM).comp_algebraMap
    obtain ⟨s, hs⟩ := hE P.Ring χ hχ
    refine ⟨s P.X, ?_⟩
    have := congrArg (fun g => g P.X) hs
    simp only [RingHom.comp_apply] at this
    rw [show ψ (s P.X) = χ P.X from this]
    exact P.lift_X ω hM
  · intro a ha
    have e : ψ (f.hom a) = ι a := congrArg (fun g => g a) hcomp
    rw [e]
    simp [ι, (IsLocalRing.residue_eq_zero_iff a).2 ha]

theorem SHLoc_of (hB : Build) (hL : Lift) : LateralTheory.E.SHExistsPf.SHLoc := by
  intro A _
  obtain ⟨O, f, Ω, _, _, ψ, hIE, hs, hm, hE⟩ := hB A
  have hU : ∀ x : O, ψ x ≠ 0 → IsUnit x := unit_of_etClosed ψ hE
  have hZ : ∀ x : O, IsUnit x → ψ x ≠ 0 := fun x hx => (hx.map ψ).ne_zero
  have : Nontrivial O := ⟨⟨1, 0, fun h => by simpa using congrArg ψ h⟩⟩
  have : IsLocalRing O := IsLocalRing.of_nonunits_add (by
    intro a b ha hb hab
    have ha' : ψ a = 0 := by by_contra h; exact ha (hU a h)
    have hb' : ψ b = 0 := by by_contra h; exact hb (hU b h)
    exact hZ _ hab (by rw [map_add (f := _), ha', hb', add_zero]))
  have hmem : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O ↔ ψ x = 0 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h => by by_contra h'; exact h (hU x h'), fun h hx => hZ x hx h⟩
  have hker : IsLocalRing.maximalIdeal O = RingHom.ker ψ := by
    ext x; rw [hmem, RingHom.mem_ker]
  let e : IsLocalRing.ResidueField O ≃+* Ω :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hs)
  have hSC : IsSepClosed (IsLocalRing.ResidueField O) := by
    refine IsSepClosed.of_exists_root _ (fun p _ hirr hsep => ?_)
    have hd : (p.map (e : IsLocalRing.ResidueField O →+* Ω)).degree ≠ 0 := by
      rw [Polynomial.degree_map]; exact (Polynomial.degree_pos_of_irreducible hirr).ne'
    obtain ⟨y, hy⟩ := IsSepClosed.exists_root _ hd (hsep.map)
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    rw [map_zero, ← hy]
    have h := Polynomial.eval₂_at_apply (p := p) (e : IsLocalRing.ResidueField O →+* Ω) (e.symm y)
    rw [Polynomial.eval_map]
    simpa using h.symm
  have hH : HenselianLocalRing O := {
    is_henselian := by
      intro p hp a₀ h₁ h₂
      obtain ⟨a, ha, ha'⟩ := hL O Ω ψ hE p hp a₀ ((hmem _).1 h₁) (hZ _ h₂)
      exact ⟨a, ha, (hmem _).2 (by rw [map_sub, ha', sub_self])⟩ }
  refine ⟨O, f, hIE, ⟨hH, hSC⟩, ⟨fun a ha => ?_⟩⟩
  by_contra hna
  exact hZ _ ha (hm a ((IsLocalRing.mem_maximalIdeal _).2 hna))

end LateralTheory.E.SHLocPf
end
end

section

open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.E.EtAlgPf

theorem key (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime]
    (c : B) : ∃ p : Polynomial A, (∃ n, algebraMap A B (p.coeff n) ∉ Q) ∧ p.eval₂ (algebraMap A B) c ∈ Q := by
  let P := Q.comap (algebraMap A B)
  have : Q.LiesOver P := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  have : Algebra.IsUnramifiedAt A Q := inferInstance
  have : Module.Finite P.ResidueField Q.ResidueField := inferInstance
  have : IsScalarTower A P.ResidueField Q.ResidueField := inferInstance
  set x := algebraMap B Q.ResidueField c
  have hx : IsIntegral P.ResidueField x := Algebra.IsIntegral.isIntegral x
  let p := minpoly P.ResidueField x
  have hp0 : p ≠ 0 := minpoly.ne_zero hx
  let M := nonZeroDivisors (A ⧸ P)
  let q := IsLocalization.integerNormalization M p
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_spec M p
  have hq0 : q ≠ 0 := by
    intro h; exact hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h)
  have hqm : q.map (algebraMap (A ⧸ P) P.ResidueField) = Polynomial.C (algebraMap (A ⧸ P) P.ResidueField b) * p := by
    rw [hb.2, ← Polynomial.smul_eq_C_mul, algebraMap_smul]
  obtain ⟨r, hr⟩ := Polynomial.map_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective q
  obtain ⟨n, hn⟩ : ∃ n, q.coeff n ≠ 0 := by
    by_contra h; push_neg at h; exact hq0 (Polynomial.ext h)
  refine ⟨r, ⟨n, ?_⟩, ?_⟩
  · intro hm; apply hn
    rw [← hr, Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]; exact hm
  · rw [← Ideal.algebraMap_residueField_eq_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq]
    have e1 : algebraMap A Q.ResidueField = (algebraMap P.ResidueField Q.ResidueField).comp
        ((algebraMap (A ⧸ P) P.ResidueField).comp (Ideal.Quotient.mk P)) := by
      ext a
      rw [RingHom.comp_apply, RingHom.comp_apply, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply A (A ⧸ P) P.ResidueField,
        ← IsScalarTower.algebraMap_apply A P.ResidueField Q.ResidueField]
    rw [e1, ← Polynomial.eval₂_map, ← Polynomial.map_map, hr, hqm, ← Polynomial.aeval_def, map_mul,
      minpoly.aeval, mul_zero]

theorem EtAlg_of : LateralTheory.E.AlgResPropsPf.EtAlg := by
  intro A B f hf
  let _ := f.hom.toAlgebra
  have : Algebra.Etale A B := hf
  intro Q hQ c
  exact key A B Q c

end LateralTheory.E.EtAlgPf
end
