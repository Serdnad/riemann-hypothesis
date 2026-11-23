module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UPel.HT.Gen.Unique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

theorem gObjMap_id {b : GBase G R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj b N s) :
    Nonempty (GObjMap o o (𝟙 S)) :=
  ⟨{ φ := 𝟙 _
     φ₂ := 𝟙 _
     cart := GlobalTheory.SiegLower.isGrpPullback_id o.A
     sq := ⟨by simp, by simp⟩
     act := fun c => by simp
     pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB
     eta := fun y => by simp }⟩

private theorem lbIso_pull_comp_of_lbIso {X Y Z : Scheme.{0}} {M : LB X} {P : LB Y} {Q : LB Z} {a : X ⟶ Y} {c : Y ⟶ Z}
    (H₁ : LBIso M (P.pull a)) (H₂ : LBIso P (Q.pull c)) (hM : M.IsLB) (hP : P.IsLB) (hQ : Q.IsLB) :
    LBIso M (Q.pull (a ≫ c)) := by
  have E : LBIso (P.pull a) ((Q.pull c).pull a) := SiegelDescent.lbIso_square hP hQ H₂ rfl
  have F : LBIso ((Q.pull c).pull a) ((Q.pull (a ≫ c)).pull (𝟙 X)) :=
    GlobalTheory.FiniteAmple.lbIso_pull_pull c hQ (g := a) (g' := 𝟙 X) (f' := a ≫ c) (by rw [Category.id_comp])
  have hPa := pull_isLB hP a
  have hQc := pull_isLB hQ (a ≫ c)
  exact LBIso.trans hM hPa hQc H₁ (LBIso.trans hPa (pull_isLB (pull_isLB hQ c) a) hQc E
    (LBIso.trans (pull_isLB (pull_isLB hQ c) a) (pull_isLB hQc (𝟙 X)) hQc F (GlobalTheory.SiegLower.lbIso_pull_id hQc).symm))

theorem gObjMap_comp {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) : Nonempty (GObjMap o₁ o₃ (f ≫ g)) :=
  ⟨{ φ := h₁.φ ≫ h₂.φ
     φ₂ := h₁.φ₂ ≫ h₂.φ₂
     cart := IsGrpPullback.comp h₁.cart h₂.cart
     sq := ⟨by rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc],
       by rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]⟩
     act := fun c => by rw [← Category.assoc, h₁.act c, Category.assoc, h₂.act c, ← Category.assoc]
     pol := lbIso_pull_comp_of_lbIso h₁.pol h₂.pol o₁.isLB o₂.isLB o₃.isLB
     eta := fun y => by rw [← Category.assoc, h₁.eta y, Category.assoc, h₂.eta y, ← Category.assoc] }⟩

end GlobalTheory.UPel.HT.Gen.Unique
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelObjectPullbackLevelPower_calculus : ∀ (h n n' n'' : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h n ζ s) (c' : SiegPre h n' ζ' s') (c'' : SiegPre h n'' ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (d d' d'' : ℕ), SRel c' c d' d f → (SRel c'' c' d'' d' f' ↔ SRel c'' c d'' d (f' ≫ f)) ∧ (c.Principal → c'.Principal) ∧ ∀ e, SRel c' c (d' * e) (d * e) f := by
  first | exact @GlobalTheory.SiegLevCalc.sRel_calculus | exact GlobalTheory.SiegLevCalc.sRel_calculus | (intros; apply GlobalTheory.SiegLevCalc.sRel_calculus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegCover

open GlobalTheory.SiegelPull GlobalTheory.SiegelPullComp GlobalTheory.SiegLevCalc

section Sec

variable {S V : Scheme.{0}} {A : Over S} {A' : Over V} [GrpObj A] [GrpObj A'] {π : V ⟶ S} {φ : A'.left ⟶ A.left}

def secOf (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) : 𝟙_ (Over V) ⟶ A' :=
  Over.homMk (hp.1.lift x.left (𝟙 V) ((Over.w x).trans (Category.id_comp π).symm)) (hp.1.lift_snd _ _ _)

theorem secOf_left (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) : (secOf hp x).left ≫ φ = x.left :=
  hp.1.lift_fst _ _ _

theorem push_secOf (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) (T : Over V) :
    pushHom hp T (toUnit T ≫ secOf hp x) = (Over.homMk T.hom rfl : Over.mk (T.hom ≫ π) ⟶ Over.mk π) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (secOf hp x).left) ≫ φ = T.hom ≫ x.left
  rw [Category.assoc, secOf_left, Over.toUnit_left]

theorem push_secOf' (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) :
    pushHom hp _ (secOf hp x) =
      (Over.homMk (𝟙_ (Over V)).hom rfl : Over.mk ((𝟙_ (Over V)).hom ≫ π) ⟶ Over.mk π) ≫ x := by
  have e := push_secOf hp x (𝟙_ (Over V))
  rwa [toUnit_unit, Category.id_comp] at e

theorem secOf_mul (hp : IsGrpPullback A' A π φ) (x y : Over.mk π ⟶ A) :
    secOf hp (x * y) = secOf hp x * secOf hp y :=
  push_injective hp _ (by rw [map_mul, push_secOf', push_secOf', push_secOf', MonObj.comp_mul])

theorem secOf_pow (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) (k : ℕ) :
    secOf hp (x ^ k) = secOf hp x ^ k :=
  push_injective hp _ (by rw [map_pow, push_secOf', push_secOf', MonObj.comp_pow])

theorem secOf_one (hp : IsGrpPullback A' A π φ) : secOf hp (1 : Over.mk π ⟶ A) = 1 :=
  push_injective hp _ (by rw [map_one, push_secOf', MonObj.comp_one])

end Sec

section Rel

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem comp_with {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hφ : IsGrpPullback c'.A c.A f φ)
    (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) {ψ : c''.A.left ⟶ c'.A.left}
    {ψ₂ : (G2 c''.A).left ⟶ (G2 c'.A).left} (hψ : IsGrpPullback c''.A c'.A f' ψ) (hs' : IsSquare ψ ψ₂)
    (hw' : LBIso c''.P (c'.P.pull ψ₂)) :
    IsGrpPullback c''.A c.A (f' ≫ f) (ψ ≫ φ) ∧
      ∃ χ₂ : (G2 c''.A).left ⟶ (G2 c.A).left, IsSquare (ψ ≫ φ) χ₂ ∧ LBIso c''.P (c.P.pull χ₂) := by
  refine ⟨hψ.comp hφ, ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)

theorem cancel_with {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hφ : IsGrpPullback c'.A c.A f φ)
    (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) {χ : c''.A.left ⟶ c.A.left}
    {χ₂ : (G2 c''.A).left ⟶ (G2 c.A).left} (hχ : IsGrpPullback c''.A c.A (f' ≫ f) χ) (hs' : IsSquare χ χ₂)
    (hw' : LBIso c''.P (c.P.pull χ₂)) (hl : ∀ a, (c''.lev a).left ≫ χ = f' ≫ (c'.lev a).left ≫ φ) :
    SiegPB c'' c' f' := by
  have hp := hφ.1
  let F : c''.A.left ⟶ c'.A.left := hp.lift χ (c''.A.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ c'.A.hom = c''.A.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A ⊗ c'.A :=
    lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))
  let F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left := U.left
  have h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, F₂, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨h₁, h₂⟩, ?_, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · rw [Category.assoc, hF, hl a, Category.assoc]
    · have a₁ : (c''.lev a).left ≫ c''.A.hom = 𝟙 S'' := Over.w (c''.lev a)
      have a₂ : (c'.lev a).left ≫ c'.A.hom = 𝟙 S' := Over.w (c'.lev a)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

end Rel

section Cover

variable {h n N : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {S V : Scheme.{0}} {s : S ⟶ Sp B}

def pair (c : SiegPre h n ζ s) (π : V ⟶ S) : ReciprocityTheory.ChartRestriction.G.Pdiv.SiegPairPB c π :=
  Classical.choice (siegPairPB_nonempty c π)

def cover (c : SiegPre h n ζ s) (sV : V ⟶ Sp B') (ζ' : B') (π : V ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A))
    (hadd : ∀ a a', e (a + a') = e a * e a') (htor : ∀ a, e a ^ N = 1)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) :
    SiegPre h N ζ' sV where
  A := (pair c π).A
  ab := (pair c π).ab
  P := (pair c π).P
  isLB := (pair c π).isLB
  rig₁ := (pair c π).rig₁
  rig₂ := (pair c π).rig₂
  symm := (pair c π).symm
  lev a := secOf (pair c π).pb (e a)
  lev_add a b := by rw [hadd, secOf_mul]
  lev_tors a := by rw [← secOf_pow, htor, secOf_one]
  geom k _ _ x β z hx hz := by
    obtain ⟨g₁, g₂, g₃⟩ := hgeom k x β z hx hz
    refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
    · rw [← (push_injective (pair c π).pb (Over.mk x)).eq_iff, push_secOf, map_one]
      try rfl
    · obtain ⟨a, ha⟩ := g₂ (pushHom (pair c π).pb (Over.mk x) g) (by
        have := congrArg (pushHom (pair c π).pb (Over.mk x)) hg
        rw [map_pow, map_one] at this
        exact this)
      exact ⟨a, push_injective (pair c π).pb _ ((push_secOf _ _ _).trans ha)⟩
    · exact (weilIs_grpPullback_of_comm S V c.A (pair c π).A π (pair c π).φ _ _ (pull_isLB c.isLB _)
        (pull_isLB (pair c π).isLB _) (pair c π).pb (diag_iso (pair c π).sq (pair c π).iso) (Over.mk x) N _ _ _ _ _
        (congrArg (fun q => q.left) (push_secOf (pair c π).pb (e a) (Over.mk x)).symm)
        (congrArg (fun q => q.left) (push_secOf (pair c π).pb (e b) (Over.mk x)).symm)).2 (g₃ a b)

end Cover

end GlobalTheory.SiegCover

namespace GlobalTheory

open SiegCover SiegLevCalc

theorem siegCover_build : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S V : Scheme.{0}) (s : S ⟶ Sp B) (sV : V ⟶ Sp B') (π : V ⟶ S) (c : SiegPre h n ζ s) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A)), (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a, e a ^ d = toUnit (Over.mk π) ≫ c.lev a) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) → ∃ (C : SiegPre h N ζ' sV) (φ : C.A.left ⟶ c.A.left), SRelBy C c d 1 π φ ∧ (∀ a, (C.lev a).left ≫ φ = (e a).left) ∧ ∀ (T : Scheme.{0}) (t : T ⟶ V) (B'' : Type) [CommRing B''] (ζ'' : B'') (sT : T ⟶ Sp B'') (C' : SiegPre h N ζ'' sT), SiegPB C' C t ↔ ∃ φ' : C'.A.left ⟶ c.A.left, SRelBy C' c d 1 (t ≫ π) φ' ∧ ∀ a, (C'.lev a).left ≫ φ' = t ≫ (e a).left := by
  intro h n N d B B' _ _ ζ ζ' S V s sV π c e hadd htor hd hgeom
  have levd : ∀ a, ((cover c sV ζ' π e hadd htor hgeom).lev a ^ d).left ≫ (pair c π).φ = π ≫ (c.lev a ^ 1).left := by
    intro a
    show (secOf (pair c π).pb (e a) ^ d).left ≫ _ = _
    rw [← secOf_pow, secOf_left, hd a, pow_one, Over.comp_left, Over.toUnit_left]
    try rfl
  refine ⟨cover c sV ζ' π e hadd htor hgeom, (pair c π).φ,
    ⟨(pair c π).pb, ⟨(pair c π).φ₂, (pair c π).sq, (pair c π).iso⟩, levd⟩, fun a => secOf_left (pair c π).pb (e a), ?_⟩
  intro T t B'' _ ζ'' sT C'
  constructor
  · rintro ⟨ψ, ψ₂, hψ, hs', hw', hl'⟩
    obtain ⟨hc, χ₂, hsq, hiso⟩ := comp_with (c' := cover c sV ζ' π e hadd htor hgeom) (pair c π).pb (pair c π).sq
      (pair c π).iso hψ hs' hw'
    refine ⟨ψ ≫ (pair c π).φ, ⟨hc, ⟨χ₂, hsq, hiso⟩, fun a => ?_⟩, fun a => ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (pair c π).φ) (pow_section hψ _ _ (hl' a) d)).trans
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (levd a)).trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (pair c π).φ) (hl' a)).trans
        ((Category.assoc _ _ _).trans (congrArg (t ≫ ·) (secOf_left (pair c π).pb (e a)))))
  · rintro ⟨φ', ⟨hχ, ⟨χ₂, hs', hw'⟩, -⟩, hl'⟩
    exact cancel_with (c' := cover c sV ζ' π e hadd htor hgeom) (pair c π).pb (pair c π).sq (pair c π).iso hχ hs' hw'
      fun a => (hl' a).trans (congrArg (t ≫ ·) (secOf_left (pair c π).pb (e a))).symm

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES.KerDet

variable {S : Scheme.{0}}

theorem comp_pow_id {A B : Over S} [GrpObj B] (f : A ⟶ B) (n : ℕ) : f ≫ (𝟙 B) ^ n = f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

theorem pow_id_comp {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    ((𝟙 A) ^ n) ≫ f = f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih, Category.id_comp]

theorem epi_pow_id (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (c : ℕ) (hc : 0 < c) :
    Epi ((𝟙 A) ^ c : A ⟶ A) := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA c hc
  exact GlobalTheory.FlatQuotient.epi_of_flat_surjective _

theorem exists_factor {A A₁ A₂ : Over S} [GrpObj A] [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂]
    (hA : IsAbelianScheme A) (hA₁ : IsAbelianScheme A₁) (c : ℕ) (hc : 0 < c)
    (ψ₁ : A ⟶ A₁) (ψ₂ : A ⟶ A₂) (ψ' : A₁ ⟶ A) [IsMonHom ψ₁] [IsMonHom ψ₂] [IsMonHom ψ']
    (h₁ : ψ₁ ≫ ψ' = (𝟙 A) ^ c) (h₂ : ψ' ≫ ψ₁ = (𝟙 A₁) ^ c)
    (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ ψ₁ = 1 → x ≫ ψ₂ = 1) :
    ∃ β : A₁ ⟶ A₂, IsMonHom β ∧ ψ₁ ≫ β = ψ₂ := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A₁ hA₁ c hc
  rw [← h₂] at h1 h2 h3
  have hpb := IsPullback.of_hasPullback (ψ' ≫ ψ₁) (η[A₁])
  have ht : pullback.snd (ψ' ≫ ψ₁) (η[A₁]) = toUnit _ := toUnit_unique _ _
  rw [ht] at hpb
  obtain ⟨β, hβ, e⟩ := GlobalTheory.FlatQuotient.exists_desc (ψ' ≫ ψ₁) _ (ψ' ≫ ψ₂) hpb (by
    rw [← Category.assoc, ← Hom.one_def]
    refine hk _ _ ?_
    rw [Category.assoc, hpb.w, Hom.one_def])
  refine ⟨β, hβ, ?_⟩
  have := epi_pow_id A hA c hc
  rw [← cancel_epi ((𝟙 A) ^ c), ← Category.assoc, pow_id_comp, ← comp_pow_id, ← h₂, Category.assoc, e,
    ← Category.assoc, h₁]


open GlobalTheory.CechPic GlobalTheory.BirigUniq in
theorem pic_eq_zero_of_pull {X B : Over S} [GrpObj X] [GrpObj B] (hX : IsAbelianScheme X)
    (hB : IsAbelianScheme B) (k : ℕ) (hk : 0 < k) (χ : X ⟶ B) (χ' : B ⟶ X) [IsMonHom χ]
    (hc : χ' ≫ χ = (𝟙 B) ^ k) (d : Pic (B ⊗ B).left)
    (d₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left d = 0) (d₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left d = 0)
    (dχ : pull (χ ⊗ₘ χ).left d = 0) : d = 0 := by
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S B hB k hk
  have hD : pull (χ ⊗ₘ 𝟙 B).left d = 0 := by
    refine pic_eq_zero_of_fpqc X B B hX ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : B ⟶ X) (𝟙 B) ≫ (χ ⊗ₘ 𝟙 B) = lift (1 : B ⟶ B) (𝟙 B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, d₁]
    · rw [← pull_comp_left]
      have : lift (fst X B) (snd X B ≫ (𝟙 B) ^ k) ≫ (χ ⊗ₘ 𝟙 B) =
          lift (fst X B) (snd X B ≫ χ') ≫ (χ ⊗ₘ χ) := by
        rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, pull_comp_left, dχ, map_zero]
  have hQ : pull (lift (snd B B) (fst B B)).left d = 0 := by
    refine pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : B ⟶ B) (𝟙 B) ≫ lift (snd B B) (fst B B) = lift (𝟙 B) (1 : B ⟶ B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, d₂]
    · rw [← pull_comp_left]
      have : lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (snd B B) (fst B B) =
          lift (snd B B ≫ χ') (fst B B) ≫ (χ ⊗ₘ 𝟙 B) := by
        rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, pull_comp_left, hD, map_zero]
  have hsw : lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B) = 𝟙 (B ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have H : pull (lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B)).left d = d := by
    rw [hsw, Over.id_left, pull_id]
  rw [pull_comp_left, hQ, map_zero] at H
  exact H.symm

theorem grpSchemeSquareProductMap_eq_tensorHom {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ = (ψ ⊗ₘ ψ).left := by
  have : lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ⊗ₘ ψ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  exact congrArg (fun f : A ⊗ A ⟶ A' ⊗ A' => f.left) this


open GlobalTheory.CechPic GlobalTheory.BirigUniq in
theorem exists_objMap_of_ker_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o o₁ o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog c o o₁ ψ₁ → IsPIsog c o o₂ ψ₂ → (∀ (T : Over S) (x : T ⟶ o.A), x ≫ ψ₁ = 1 ↔ x ≫ ψ₂ = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 S), ψ₁.left ≫ m.φ = ψ₂.left := by
  intro p _ D R _ b N _ _ c S _ s o o₁ o₂ ψ₁ ψ₂ H₁ H₂ hk
  have hc := H₁.pos
  obtain ⟨-, m₁, a₁, l₁, ⟨P₁⟩, ψ₁', m₁', u₁, v₁⟩ := H₁
  obtain ⟨-, m₂, a₂, l₂, ⟨P₂⟩, ψ₂', m₂', u₂, v₂⟩ := H₂
  obtain ⟨β, hβ, e⟩ := exists_factor o.ab o₁.ab c hc ψ₁ ψ₂ ψ₁' u₁ v₁ fun T x => (hk T x).1
  obtain ⟨β', -, e'⟩ := exists_factor o.ab o₂.ab c hc ψ₂ ψ₁ ψ₂' u₂ v₂ fun T x => (hk T x).2
  have E₁ : Epi ψ₁ := by
    have := epi_pow_id o₁.A o₁.ab c hc
    exact epi_of_epi_fac v₁
  have E₂ : Epi ψ₂ := by
    have := epi_pow_id o₂.A o₂.ab c hc
    exact epi_of_epi_fac v₂
  let i : o₁.A ≅ o₂.A := ⟨β, β', by rw [← cancel_epi ψ₁, ← Category.assoc, e, e', Category.comp_id],
    by rw [← cancel_epi ψ₂, ← Category.assoc, e', e, Category.comp_id]⟩
  have hpol : LBIso o₁.P (o₂.P.pull (β ⊗ₘ β).left) := by
    have hN : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    rw [grpSchemeSquareProductMap_eq_tensorHom] at P₁ P₂
    let p₁ := cls o₁.P o₁.isLB
    let p₂ := cls o₂.P o₂.isLB
    have n₁ : pull (ψ₁ ⊗ₘ ψ₁).left p₁ = cls _ hN := ((cls_eq_iff hN (pull_isLB o₁.isLB _)).2 P₁).symm
    have n₂ : pull (ψ₂ ⊗ₘ ψ₂).left p₂ = cls _ hN := ((cls_eq_iff hN (pull_isLB o₂.isLB _)).2 P₂).symm
    have r₁₁ : pull (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left p₁ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₁.isLB _)).2 o₁.rig₁
    have r₁₂ : pull (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left p₁ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₁.isLB _)).2 o₁.rig₂
    have r₂₁ : pull (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left p₂ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₂.isLB _)).2 o₂.rig₁
    have r₂₂ : pull (lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A)).left p₂ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₂.isLB _)).2 o₂.rig₂
    have e₁ : lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A) ≫ (β ⊗ₘ β) = β ≫ lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have e₂ : lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A) ≫ (β ⊗ₘ β) = β ≫ lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have hd : pull (β ⊗ₘ β).left p₂ - p₁ = 0 := by
      refine pic_eq_zero_of_pull o.ab o₁.ab c hc ψ₁ ψ₁' v₁ _ ?_ ?_ ?_
      · rw [map_sub, r₁₁, sub_zero, ← pull_comp_left, e₁, pull_comp_left, r₂₁, map_zero]
      · rw [map_sub, r₁₂, sub_zero, ← pull_comp_left, e₂, pull_comp_left, r₂₂, map_zero]
      · rw [map_sub, n₁, ← pull_comp_left, tensorHom_comp_tensorHom, e, n₂, sub_self]
    exact (cls_eq_iff o₁.isLB (pull_isLB o₂.isLB _)).1 (sub_eq_zero.1 hd).symm
  refine ⟨{ φ := β.left, φ₂ := (β ⊗ₘ β).left
            cart := (GlobalTheory.TQCompare.isGrpPullback_id_iff _).2 ⟨i, hβ, rfl⟩
            sq := ⟨?_, ?_⟩, act := fun a => ?_, pol := hpol, eta := fun y => ?_ }, ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_snd]
  · rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [← cancel_epi ψ₁, ← Category.assoc, ← a₁, Category.assoc, e, a₂, ← Category.assoc, e]
  · rw [← Over.comp_left, l₁, l₂, Category.assoc, e]
    exact (Category.id_comp _).symm
  · show ψ₁.left ≫ β.left = _
    rw [← Over.comp_left, e]

end GlobalTheory.UPel.HT.ES.KerDet
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.norm_localEquation_eq_uniformiser_pow_classicalPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (D : GlobalTheory.EffCartierData M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ϖ : V) (a : ℕ) (ξ : Sp V ⟶ M.Z) (p : ℕ) [Fact p.Prime] (ι : FractionRing V →+* PadicAlgCl p) (j : V →+* OO p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ v, (j v : PadicAlgCl p) = ι (algebraMap V (FractionRing V) v)) → idlAlong D.idealSheaf ξ = Ideal.span {ϖ ^ a} → ∀ f, EqAt M D (ξ (closedPoint V)) f → ‖M.val (gPt p ≫ spMap j ≫ ξ) f‖ = ‖ι (algebraMap V (FractionRing V) ϖ)‖ ^ a := by
  first | exact @GlobalTheory.Poinc.EqNormAt.norm_val_eqAt | exact GlobalTheory.Poinc.EqNormAt.norm_val_eqAt | (intros; apply GlobalTheory.Poinc.EqNormAt.norm_val_eqAt <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.levelCover_complexModels_components_isometries_degree : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∃ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E) (N : ℕ), 0 < N ∧ (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0) ∧ (∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N) ∧ ∃ t : (U₂ σ₂).Comp → ℂ, (∀ k₂, ‖t k₂‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → ∀ k₂ (x : Frame ((U₂ σ₂).X k₂).Ψ D.R.r) (x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ D.R.r), x ∈ ((U₂ σ₂).X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ) (h₁ : τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ), mat x' ⟨τ, h₁⟩ = (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → Even n → rdU (U₂ σ₂) g k₂ x = t k₂ ^ n * rdU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂) x' := by
  first | exact @GlobalTheory.LevModel.levCover_model | exact GlobalTheory.LevModel.levCover_model | (intros; apply GlobalTheory.LevModel.levCover_model <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sum_mul_hodgeFil_eq_zero_of_deRham_coboundary : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ y ∈ Fil B, ∀ (D : Type) [CommRing D] [Algebra R D] (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (hβ : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B), (∃ k, IsCob (whole _) (sumMul d fun i ↦ fv (β i)) k) → ∑ i, d i * algebraMap R D (y ⟨_, hβ i⟩) = 0 := by
  first | exact @GlobalTheory.PtExt.sum_mul_eq_zero_of_isCob | exact GlobalTheory.PtExt.sum_mul_eq_zero_of_isCob | (intros; apply GlobalTheory.PtExt.sum_mul_eq_zero_of_isCob <;> assumption)
end
