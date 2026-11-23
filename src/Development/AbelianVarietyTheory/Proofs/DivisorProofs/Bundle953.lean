module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle932
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle927
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle929
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001

@[expose] public section

section

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem lbIso_pullPull {P X Y : Scheme.{0}} {M : LB P} (hM : M.IsLB) (b : X ⟶ P) (c : Y ⟶ X) :
    LBIso ((M.pull b).pull c) (M.pull (c ≫ b)) :=
  LBIso.chartPull (chartPullLinComb M b (fun _ : PUnit => c) (fun _ => c ≫ b) (fun _ => 1) (𝟙 _)
      fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hM _))

theorem lbIso_pullAlong {X Y : Scheme.{0}} {P Q : LB X} (H : LBIso P Q) (h : Y ⟶ X) :
    LBIso (P.pull h) (Q.pull h) :=
  LBIso.chartPull (chartPullPull P h h rfl) (chartPullPull Q h h rfl) H

theorem Pt.f_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z : Scheme.{0}} {x x' : Pt A B L M Z} (h : x = x') (e : x.t = x'.t) :
    pullback.lift (pullback.fst A.hom x'.t) (pullback.snd A.hom x'.t) (by rw [pullback.condition, e]) ≫ x.f = x'.f := by
  subst h
  rw [pullback.lift_fst_snd, Category.id_comp]

section
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
  {V : Scheme.{0}} {j : V ⟶ S} {A' B' : Over V} [GrpObj A'] [GrpObj B'] {φA : A'.left ⟶ A.left}
  {φB : B'.left ⟶ B.left}

theorem univ_iso (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)) :
    LBIso (L.pull (R.φA ≫ φA)) ((M.pull (R.φB ≫ φB)).pull R.Φ.left) :=
  LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _)
    (lbIso_pullPull hL φA R.φA).symm
    (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
      (pull_isLB (pull_isLB hM _) _) R.iso (lbIso_pullAlong (lbIso_pullPull hM φB R.φB) R.Φ.left))

def univPt (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB))
    (hA : IsGrpPullback A' A j φA) (hB : IsGrpPullback B' B j φB) : Pt A B L M R.H :=
  Pt.ofData (R.π ≫ j) R.AH R.BH (R.φA ≫ φA) (R.φB ≫ φB) R.Φ (R.pbA.comp hA) (R.pbB.comp hB) R.hom
    (univ_iso hL hM R)

theorem univPt_key (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB))
    (hA : IsGrpPullback A' A j φA) (hB : IsGrpPullback B' B j φB) {Z P : Scheme.{0}} (c : Z ⟶ R.H) (t : Z ⟶ V)
    (e : P ⟶ pullback A.hom (t ≫ j)) (ψ : P ⟶ R.AH.left)
    (h1 : ψ ≫ R.φA ≫ φA = e ≫ pullback.fst _ _) (h2 : ψ ≫ R.AH.hom = e ≫ pullback.snd _ _ ≫ c)
    (w : pullback.fst A.hom (t ≫ j) ≫ A.hom = pullback.snd A.hom (t ≫ j) ≫ c ≫ R.π ≫ j) :
    e ≫ pullback.lift (pullback.fst _ _) (pullback.snd _ _) w ≫ pmap A (R.π ≫ j) c ≫ (univPt hL hM R hA hB).f =
      ψ ≫ R.Φ.left ≫ R.φB ≫ φB := by
  have hk : e ≫ pullback.lift (pullback.fst _ _) (pullback.snd _ _) w ≫ pmap A (R.π ≫ j) c =
      ψ ≫ (R.pbA.comp hA).1.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [pmap, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst]
      exact h1.symm
    · simp only [pmap, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_snd]
      exact h2.symm
  have e0 : (univPt hL hM R hA hB).f = (R.pbA.comp hA).1.isoPullback.inv ≫ R.Φ.left ≫ R.φB ≫ φB := rfl
  have := congrArg (· ≫ ((R.pbA.comp hA).1.isoPullback.inv ≫ R.Φ.left ≫ R.φB ≫ φB)) hk
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at this
  rw [e0]
  exact this

end
end GlobalTheory.EndLoc.HomGlue

namespace GlobalTheory.EndLoc.HomGlue

theorem localRep_universal : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)
    (hL : L.IsLB) (hM : M.IsLB) (V : Scheme.{0}) (j : V ⟶ S) [IsOpenImmersion j] (A' B' : Over V) [GrpObj A']
    [GrpObj B'] (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)),
    IsGrpPullback A' A j φA → IsGrpPullback B' B j φB → ∃ y : HomGlue.Pt A B L M R.H, y.t = R.π ≫ j ∧
      ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V), x.t = b ≫ j → ∃! c : Z ⟶ R.H, y.map hL hM c = x := by
  intro S A B _ _ L M hL hM V j _ A' B' _ _ φA φB R hA hB
  refine ⟨univPt hL hM R hA hB, rfl, ?_⟩
  rintro Z ⟨t, f, w⟩ b hx
  dsimp only at hx
  subst hx
  have w₀ := w
  obtain ⟨A'', B'', _, _, φ'', ψ'', Φ'', hA'', hB'', hΦ'', hI'', e, e1, e2, e3⟩ := w₀
  let φ'A : A''.left ⟶ A'.left := hA.1.lift φ'' (A''.hom ≫ b) (by rw [hA''.1.w, Category.assoc])
  have fA : φ'A ≫ φA = φ'' := hA.1.lift_fst _ _ _
  have sA : φ'A ≫ A'.hom = A''.hom ≫ b := hA.1.lift_snd _ _ _
  have pA : IsGrpPullback A'' A' b φ'A := hA.cancel (hA''.congr rfl fA.symm) sA
  let φ'B : B''.left ⟶ B'.left := hB.1.lift ψ'' (B''.hom ≫ b) (by rw [hB''.1.w, Category.assoc])
  have fB : φ'B ≫ φB = ψ'' := hB.1.lift_fst _ _ _
  have sB : φ'B ≫ B'.hom = B''.hom ≫ b := hB.1.lift_snd _ _ _
  have pB : IsGrpPullback B'' B' b φ'B := hB.cancel (hB''.congr rfl fB.symm) sB
  have iso' : LBIso ((L.pull φA).pull φ'A) (((M.pull φB).pull φ'B).pull Φ''.left) := by
    have h1 := lbIso_pullPull hL φA φ'A
    rw [fA] at h1
    have h2 := (lbIso_pullAlong (lbIso_pullPull hM φB φ'B) Φ''.left).symm
    rw [fB] at h2
    exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _) h1
      (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _) hI'' h2)
  obtain ⟨h, ⟨hh, ψA, ψB, qA, qB, gA, gB, qΦ⟩, huniq⟩ := R.rep Z b A'' B'' φ'A φ'B Φ'' pA pB hΦ'' iso'
  have he : e = hA''.1.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [e1, IsPullback.isoPullback_hom_fst]
    · rw [e2, IsPullback.isoPullback_hom_snd]
  have hΦw : Φ''.left ≫ B''.hom = A''.hom := Over.w Φ''
  refine ⟨h, ?_, ?_⟩
  · refine Pt.ext' (show h ≫ R.π ≫ j = b ≫ j by rw [← Category.assoc, hh]) ?_
    have : IsIso e := by rw [he]; infer_instance
    rw [← cancel_epi e, e3]
    refine (univPt_key hL hM R hA hB h b e ψA (by rw [← Category.assoc, gA, fA, e1])
      (by rw [qA.1.w, ← Category.assoc, e2]) _).trans ?_
    rw [← Category.assoc ψA, ← qΦ, Category.assoc, ← Category.assoc ψB, gB, fB]
  · intro c hc
    have ht : c ≫ R.π ≫ j = b ≫ j := congrArg Pt.t hc
    have hcb : c ≫ R.π = b := (cancel_mono j).1 (by rw [Category.assoc]; exact ht)
    have hf := Pt.f_eq hc ht
    let ψA' : A''.left ⟶ R.AH.left := R.pbA.1.lift φ'A (A''.hom ≫ c) (by rw [sA, ← hcb, Category.assoc])
    have kA : ψA' ≫ R.φA = φ'A := R.pbA.1.lift_fst _ _ _
    have kA2 : ψA' ≫ R.AH.hom = A''.hom ≫ c := R.pbA.1.lift_snd _ _ _
    let ψB' : B''.left ⟶ R.BH.left := R.pbB.1.lift φ'B (B''.hom ≫ c) (by rw [sB, ← hcb, Category.assoc])
    have kB : ψB' ≫ R.φB = φ'B := R.pbB.1.lift_fst _ _ _
    have kB2 : ψB' ≫ R.BH.hom = B''.hom ≫ c := R.pbB.1.lift_snd _ _ _
    have key := univPt_key hL hM R hA hB c b e ψA' (by rw [← Category.assoc, kA, fA, e1])
      (by rw [kA2, ← Category.assoc, e2]) (by rw [pullback.condition, ← ht])
    have hΦA : R.Φ.left ≫ R.BH.hom = R.AH.hom := Over.w R.Φ
    apply huniq
    refine ⟨hcb, ψA', ψB', R.pbA.cancel (pA.congr hcb.symm kA.symm) kA2,
      R.pbB.cancel (pB.congr hcb.symm kB.symm) kB2, kA, kB, ?_⟩
    apply R.pbB.1.hom_ext
    · rw [Category.assoc, kB]
      apply hB.1.hom_ext
      · rw [Category.assoc, fB, ← e3, Category.assoc, Category.assoc, ← key]
        exact congrArg (e ≫ ·) hf.symm
      · rw [Category.assoc, sB, ← Category.assoc, hΦw, Category.assoc, Category.assoc, R.pbB.1.w,
          ← Category.assoc R.Φ.left, hΦA, ← Category.assoc, kA2, Category.assoc, hcb]
    · rw [Category.assoc, kB2, ← Category.assoc, hΦw, Category.assoc, hΦA, kA2]

end GlobalTheory.EndLoc.HomGlue
end
end

section

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem Pt.f_congr {Z W : Scheme.{0}} {x y : Pt A B L M Z} (h : x = y) (k : W ⟶ pullback A.hom x.t)
    (k' : W ⟶ pullback A.hom y.t) (h1 : k ≫ pullback.fst _ _ = k' ≫ pullback.fst _ _)
    (h2 : k ≫ pullback.snd _ _ = k' ≫ pullback.snd _ _) : k ≫ x.f = k' ≫ y.f := by
  subst h
  have : k = k' := pullback.hom_ext h1 h2
  subst this
  rfl

theorem homFixRep_of_universal (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left)
    (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (X : Scheme.{0}) (u : HomGlue.Pt A B L M X) :
    (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x) →
      ∃ (R : HomFixRep A B L M) (e : R.H ≅ X), e.hom ≫ u.t = R.π := by
  intro hu
  obtain ⟨A', B', iA, iB, φA, φB, Φ, hA, hB, hΦ, hI, e, e1, e2, e3⟩ := u.wit
  refine ⟨@HomFixRep.mk S A B _ _ L M X u.t A' iA B' iB φA φB hA hB Φ hΦ hI ?_, Iso.refl X, Category.id_comp _⟩
  intro T t A'' B'' _ _ φA' φB' Φ' hA' hB' hΦ' hI'
  let x : Pt A B L M T := Pt.ofData t A'' B'' φA' φB' Φ' hA' hB' hΦ' hI'
  have hxf : x.f = hA'.1.isoPullback.inv ≫ Φ'.left ≫ φB' := rfl

  have key : ∀ (h : T ⟶ X) (ψA : A''.left ⟶ A'.left), h ≫ u.t = t → ψA ≫ φA = φA' →
      ψA ≫ A'.hom = A''.hom ≫ h → Φ'.left ≫ φB' = ψA ≫ Φ.left ≫ φB → u.map hL hM h = x := by
    intro h ψA ht hψ1 hψ2 hf
    refine Pt.ext' ht ?_
    show pullback.lift (pullback.fst A.hom t) (pullback.snd A.hom t) (by rw [pullback.condition, ht])
      ≫ pmap A u.t h ≫ u.f = (hA'.1.isoPullback.inv ≫ Φ'.left ≫ φB' : pullback A.hom t ⟶ B.left)
    rw [← cancel_epi hA'.1.isoPullback.hom, Iso.hom_inv_id_assoc]
    have hk : hA'.1.isoPullback.hom ≫ pullback.lift (pullback.fst A.hom t) (pullback.snd _ _)
        (by rw [pullback.condition, ht] : _ = _ ≫ h ≫ u.t) ≫ pmap A u.t h = ψA ≫ e := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst, e1, hψ1]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, e2, hψ2]
        rw [← Category.assoc, IsPullback.isoPullback_hom_snd]
    rw [← Category.assoc, ← Category.assoc, Category.assoc _ _ (pmap A u.t h), hk, Category.assoc, e3, hf]
  obtain ⟨c, hc, hcu⟩ := hu T x
  have hct : c ≫ u.t = t := congrArg Pt.t hc
  have wA : φA' ≫ A.hom = (A''.hom ≫ c) ≫ u.t := by rw [hA'.1.w, Category.assoc, hct]
  have wB : φB' ≫ B.hom = (B''.hom ≫ c) ≫ u.t := by rw [hB'.1.w, Category.assoc, hct]
  let ψA := hA.1.lift φA' (A''.hom ≫ c) wA
  let ψB := hB.1.lift φB' (B''.hom ≫ c) wB
  have hψA1 : ψA ≫ φA = φA' := hA.1.lift_fst _ _ _
  have hψA2 : ψA ≫ A'.hom = A''.hom ≫ c := hA.1.lift_snd _ _ _
  have hψB1 : ψB ≫ φB = φB' := hB.1.lift_fst _ _ _
  have hψB2 : ψB ≫ B'.hom = B''.hom ≫ c := hB.1.lift_snd _ _ _
  have gA : IsGrpPullback A'' A' c ψA := IsGrpPullback.cancel hA (hA'.congr hct.symm hψA1.symm) hψA2
  have gB : IsGrpPullback B'' B' c ψB := IsGrpPullback.cancel hB (hB'.congr hct.symm hψB1.symm) hψB2

  have hfc : Φ'.left ≫ φB' = ψA ≫ e ≫ u.f := by
    have h0 := Pt.f_congr hc
      (pullback.lift φA' A''.hom (by rw [hA'.1.w, hct]) : A''.left ⟶ pullback A.hom (c ≫ u.t))
      (hA'.1.isoPullback.hom : A''.left ⟶ pullback A.hom t)
      ((pullback.lift_fst _ _ _).trans hA'.1.isoPullback_hom_fst.symm)
      ((pullback.lift_snd _ _ _).trans hA'.1.isoPullback_hom_snd.symm)
    have hk : pullback.lift φA' A''.hom (by rw [hA'.1.w, hct]) ≫ pmap A u.t c = ψA ≫ e := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, e1, hψA1]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, e2, hψA2]
    change _ ≫ pmap A u.t c ≫ u.f = (hA'.1.isoPullback.hom : A''.left ⟶ pullback A.hom t) ≫
      (hA'.1.isoPullback.inv ≫ Φ'.left ≫ φB' : pullback A.hom t ⟶ B.left) at h0
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hk, Category.assoc] at h0
    exact h0.symm
  have hcomm : Φ'.left ≫ ψB = ψA ≫ Φ.left := by
    apply hB.1.hom_ext
    · rw [Category.assoc, hψB1, Category.assoc, hfc, e3]
    · rw [Category.assoc, hψB2, ← Category.assoc, Over.w Φ', Category.assoc, Over.w Φ, hψA2]
  refine ⟨c, ⟨hct, ψA, ψB, gA, gB, hψA1, hψB1, hcomm⟩, ?_⟩
  rintro h ⟨ht, χA, χB, kA, kB, kA1, kB1, kcomm⟩
  have hx : u.map hL hM h = x := key h χA ht kA1 kA.1.w (by
    rw [← kB1, ← Category.assoc, kcomm, Category.assoc])
  exact (hcu h hx)

end GlobalTheory.EndLoc.HomGlue
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare.Shift

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

theorem natW_top (lam : DomWeight (n + 1)) (a : Fin (n + 1)) :
    (lam.natW a : ℤ) = lam.w a - lam.w (Fin.last n) := by
  have h1 : lam.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dite_eq_left (Nat.succ_pos n)]
    rfl
  have h2 := lam.anti (Fin.le_last a)
  unfold DomWeight.natW
  rw [h1]
  omega

theorem lamZ_lamN (lam : DomWeight (n + 1)) (a : Fin (n + 1)) :
    lamZ (lamN lam) a = lam.w a - lam.w (Fin.last n) := by
  unfold lamZ
  split_ifs with h
  · exact natW_top lam a
  · have : a = Fin.last n := Fin.ext (by have := a.2; simp; omega)
    simp [this]

theorem lamN_cast (lam : DomWeight (n + 1)) (i : Fin n) :
    (lamN lam i : ℤ) = lam.w i.castSucc - lam.w (Fin.last n) := natW_top lam _

theorem nuNext_cast (lam : DomWeight (n + 1)) (i : Fin n) :
    (nuNext (lamN lam) i : ℤ) = lam.w i.succ - lam.w (Fin.last n) := by
  rw [← lamZ_lamN]
  unfold nuNext lamZ
  simp only [Fin.val_succ]
  split_ifs <;> rfl

theorem natW_low (hE : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg) (i : Fin n) :
    (sg.natW i : ℤ) = sg.w i - lam.w (Fin.last n) := by
  have hi := i.2
  have h0 : 0 < n := by omega
  have h1 : sg.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dite_eq_left h0]
    exact hE _ (by simp only; omega)
  have h2 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i := sg.anti (by rw [Fin.le_def]; simp only; omega)
  rw [hE ⟨n - 1, by omega⟩ (by simp only; omega)] at h2
  unfold DomWeight.natW
  rw [h1]
  omega

theorem d0_eq (hE : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg) :
    Formalism.BranchingDeterminantCap.d0 (lamZ (lamN lam)) (fun i => (sg.natW i : ℤ)) = GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.dZero lam sg := by
  unfold Formalism.BranchingDeterminantCap.d0 GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.dZero
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [lamZ_lamN, natW_low hE]
  ring

theorem rename_initMinor (K : Type) [Field K] {s : ℕ} (I : Fin s → Fin (n + 1)) (hs : s ≤ n) :
    incl K n (initMinor K I hs) = initMinor K I (hs.trans (Nat.le_succ n)) := by
  unfold initMinor incl
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp

end GlobalTheory.BrCompare.Shift


open GlobalTheory.BrCompare.Shift in
theorem GlobalTheory.BrCompare.shifted_branching_list_character : ∀ (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → Formalism.BranchingDeterminantCap.Interlace (lamZ (lamN lam)) (fun i => (sg.natW i : ℤ)) ∧ (∀ u ∈ bmList (lamN lam) sg.natW, u ∈ zList lam sg) ∧ ((zList lam sg).map (bmChi (lamN lam) fun s => ((lamN lam s - sg.natW s : ℕ) : ℤ))).prod = Formalism.L2.Col.Br.cBr rfl lam sg ∧ (∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s) ∧ ∀ (K : Type) [Field K], Formalism.L2.Col.Br.xiBr K rfl lam sg = incl K n (xiB K (lamN lam) sg.natW) := by
  intro n lam sg hI hE
  have hb : ∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s := by
    intro s
    have h1 := lamN_cast lam s
    have h2 := natW_low hE s
    have h3 : Formalism.L2.Col.Br.bBr rfl lam sg s = lam.w s.castSucc - sg.w s := rfl
    rw [h3]
    omega
  have ha : ∀ s, (Formalism.L2.Col.Br.aBr rfl lam sg s).toNat = sg.natW s - nuNext (lamN lam) s := by
    intro s
    have h1 := nuNext_cast lam s
    have h2 := natW_low hE s
    have h3 : Formalism.L2.Col.Br.aBr rfl lam sg s = sg.w s - lam.w s.succ := rfl
    rw [h3]
    omega
  refine ⟨?_, ?_, ?_, hb, ?_⟩
  · intro i
    have := hI i
    simp only [lamZ_lamN, natW_low hE]
    omega
  · intro u hu
    simp only [bmList, List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_erase, rset, d0_eq hE,
      Finset.mem_Icc] at hu
    simp only [lamZ_lamN, natW_low hE] at hu
    obtain ⟨i, -, v, ⟨h1, h2, h3⟩, rfl⟩ := hu
    simp only [zList, List.mem_flatten, List.mem_ofFn]
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_erase, GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.rangeSet, Finset.mem_Icc]
    exact ⟨v + lam.w (Fin.last n), ⟨by omega, by omega, by omega⟩, by ring⟩
  · unfold zList Formalism.L2.Col.Br.cBr
    rw [List.map_flatten, List.prod_flatten, List.map_map, List.map_ofFn, List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_def, List.map_map, Finset.prod_map_toList]
    refine Finset.prod_congr rfl fun v _ => ?_
    unfold bmChi
    refine Finset.prod_congr rfl fun j _ => ?_
    have h1 := lamN_cast lam j
    have h2 := natW_low hE j
    have h3 := hI j
    simp only
    omega
  · intro K _
    unfold Formalism.L2.Col.Br.xiBr xiB
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_pow, rename_initMinor, rename_initMinor, ha, hb]
    congr 2
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.generic_fibre_base_change_injective : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA) P₁ := by
  first | (exact @GlobalTheory.AbhHeightOne.closureEtaleAt_of_root_of_uniformiser) | (exact GlobalTheory.AbhHeightOne.closureEtaleAt_of_root_of_uniformiser) | (intros; apply GlobalTheory.AbhHeightOne.closureEtaleAt_of_root_of_uniformiser  <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

def Eff {X : Scheme.{0}} (c : Pic X) : Prop :=
  ∃ (N : LB X) (hN : N.IsLB), cls N hN = c ∧ ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0

theorem eff_of_sec {X : Scheme.{0}} (N : LB X) (hN : N.IsLB) (σ : LB.Sec N) (j : N.ι) (h : σ.f j ≠ 0) :
    Eff (cls N hN) :=
  ⟨N, hN, rfl, σ, j, h⟩

theorem cls_pw {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (t : ℤ) :
    cls (pw H t) (isLB_pw hH t) = t • cls H hH := by
  have hL := LB.isLB_linComb hH (fun _ : PUnit => 𝟙 X) (fun _ => t)
  have e : LBIso (LB.LinComb H (fun _ : PUnit => 𝟙 X) (fun _ => t)) (pw H t) :=
    iso_of_chart (isLB_pw hH t)
      { idx := fun j => j PUnit.unit
        le := fun j y hy => Set.mem_iInter.1 hy PUnit.unit
        g := fun y j j' hj hj' => by
          refine (gm_linComb H (fun _ : PUnit => 𝟙 X) (fun _ => t) (𝟙 X) y j j' hj hj').trans ?_
          rw [Fintype.prod_unique]
          change _ = gm (𝟙 X) y _ (H.g (j PUnit.unit) (j' PUnit.unit) ^ t)
          rw [map_zpow, Category.comp_id] }
  rw [← (cls_eq_iff hL (isLB_pw hH t)).2 e, cls_linComb hH, Fintype.sum_unique, pull_id]

end GlobalTheory.EffBound
end
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z * g z) = GlobalTheory.PeriodFamily.taylor N t f * GlobalTheory.PeriodFamily.taylor N t g := by
  first | exact @GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero | exact GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero | (intros; apply GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero <;> assumption)
end

section

set_option autoImplicit false

namespace GlobalTheory.Published

theorem grothendieckDeformation_of_lifting (P : AbelianDeRham) (L : AbelianLifting) :
    GrothendieckDeformation :=
  fun R _ I κ hκ R₀ _ π hπ hI ↦
    ⟨GrothendieckMessing.canonical_of_abelianDeRham P hκ hπ hI, L R I κ hκ R₀ π hπ hI⟩

end GlobalTheory.Published
end
