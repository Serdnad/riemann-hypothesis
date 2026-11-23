module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle183
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2971
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
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem uIsLab_onto_and_ker : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → Function.Surjective yy ∧ yy.ker = X.S.HH X.M z := by
  intro E _ _ _ H Dw _ l Xo cf C X p _ z ct yy hl
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, hR', G, _, α, β, -, -, -, y₀, hy₀, u, lb, j, -, hyy, -⟩ := hl
  refine ⟨?_, ?_⟩
  · intro m
    obtain ⟨χ', rfl⟩ := QuotientAddGroup.mk_surjective m
    obtain ⟨a, ha⟩ := lb.yy_onto (QuotientAddGroup.mk (j.symm χ'))
    exact ⟨a, by rw [hyy a _ ha, j.apply_symm_apply]⟩
  have hker : yy.ker = lb.yy.ker := by
    ext a
    simp only [AddMonoidHom.mem_ker]
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (lb.yy a)
    rw [hyy a χ hχ.symm, ← hχ, QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨j.symm v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv, j.symm_apply_apply]
    · rintro ⟨v, hv⟩
      refine ⟨j v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv]
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one ct.cen ((X.M.O z).algebraMap_mem a)
  have hcl := GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u lb hint
  rw [hker, ← hcl.2]
  obtain ⟨x₀, hx₀⟩ := X.hasDiv z
  set val := X.M.val (gPt p ≫ ct.y) with hval
  have hsp : ∀ w, (gPt p ≫ ct.y) w ⤳ (gPt p ≫ ct.y) (IsLocalRing.closedPoint (PadicAlgCl p)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : (gPt p ≫ ct.y) (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ z :=
    RatModel.gPt_specializes ct.cen _
  have hy : ∀ x, y₀ ⟨c₀ * X.S.th x, hth x⟩ = val (c₀ * X.S.th x) := fun x => hy₀ _
  have hmul : ∀ x, ‖val (c₀ * X.S.th x)‖ = ‖val (X.S.th x / X.S.th x₀)‖ * ‖val (c₀ * X.S.th x₀)‖ := by
    intro x
    rw [← norm_mul, hval, ← RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hx₀.2 x)) (hR' (hth x₀))]
    congr 2
    have := hx₀.1
    field_simp
  have hδ : ‖val (c₀ * X.S.th x₀)‖ = (X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    apply le_antisymm
    · rw [← hy]
      exact le_ciSup (f := fun x => ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖) (Set.finite_range _).bddAbove x₀
    · obtain ⟨x₁, hx₁⟩ := exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖)
      change ⨆ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ ≤ _
      rw [← hx₁, hy, hmul x₁]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one ct.cen (hx₀.2 x₁))
  have key : ∀ x, x ∈ X.S.supI X.M z ↔
      ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ = (X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    intro x
    change X.M.Div X.S.th x z ↔ _
    rw [hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff ct.cen (hx₀.2 x), hy, hmul x, hδ]
    exact (mul_eq_right₀ hcl.1.ne').symm
  rw [ThetaSys.HH]
  congr 1
  ext x
  exact (key x).symm

end GlobalTheory.UPoinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

abbrev prU (N : Near π G) : (Desc.UT N).left ⟶ N.U.left := pullback.fst _ _

def liftU (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : Y ⟶ (Desc.UT N).left :=
  pullback.lift x t h

theorem liftU_prU (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : liftU N x t h ≫ prU N = x :=
  pullback.lift_fst _ _ _

theorem liftU_hom (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : liftU N x t h ≫ (Desc.UT N).hom = t :=
  pullback.lift_snd _ _ _

theorem UT_ext (N : Near π G) {Y : Scheme.{0}} (f g : Y ⟶ (Desc.UT N).left) (h1 : f ≫ prU N = g ≫ prU N)
    (h2 : f ≫ (Desc.UT N).hom = g ≫ (Desc.UT N).hom) : f = g :=
  pullback.hom_ext h1 h2

theorem pairU_fst (N : Near π G) :
    pairU N ≫ (fst N.U N.U).left = (fst (Desc.UT N) (Desc.UT N)).left ≫ prU N :=
  congrArg Over.Hom.left (lift_fst (fstU N) (sndU N))

theorem pairU_snd (N : Near π G) :
    pairU N ≫ (snd N.U N.U).left = (snd (Desc.UT N) (Desc.UT N)).left ≫ prU N :=
  congrArg Over.Hom.left (lift_snd (fstU N) (sndU N))

theorem pairU_isPullback (N : Near π G) :
    IsPullback (pairU N) (Desc.UT N ⊗ Desc.UT N).hom (N.U ⊗ N.U).hom (pullback.fst π π ≫ π) := by
  have hUU : (N.U ⊗ N.U).hom = (fst N.U N.U).left ≫ N.U.hom := rfl
  have cUU : (fst N.U N.U).left ≫ N.U.hom = (snd N.U N.U).left ≫ N.U.hom := pullback.condition
  have hTT : (Desc.UT N ⊗ Desc.UT N).hom = (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom := rfl
  have cTT : (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom := pullback.condition
  have extUU : ∀ {Y : Scheme.{0}} (f g : Y ⟶ (N.U ⊗ N.U).left), f ≫ (fst N.U N.U).left = g ≫ (fst N.U N.U).left →
      f ≫ (snd N.U N.U).left = g ≫ (snd N.U N.U).left → f = g := fun f g h1 h2 => pullback.hom_ext h1 h2
  have extTT : ∀ {Y : Scheme.{0}} (f g : Y ⟶ (Desc.UT N ⊗ Desc.UT N).left),
      f ≫ (fst (Desc.UT N) (Desc.UT N)).left = g ≫ (fst (Desc.UT N) (Desc.UT N)).left →
      f ≫ (snd (Desc.UT N) (Desc.UT N)).left = g ≫ (snd (Desc.UT N) (Desc.UT N)).left → f = g :=
    fun f g h1 h2 => pullback.hom_ext h1 h2
  have liftTT : ∀ {Y : Scheme.{0}} (a b : Y ⟶ (Desc.UT N).left), a ≫ (Desc.UT N).hom = b ≫ (Desc.UT N).hom →
      ∃ f : Y ⟶ (Desc.UT N ⊗ Desc.UT N).left,
        f ≫ (fst (Desc.UT N) (Desc.UT N)).left = a ∧ f ≫ (snd (Desc.UT N) (Desc.UT N)).left = b :=
    fun a b h => ⟨pullback.lift a b h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have ha : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      (s.fst ≫ (fst N.U N.U).left) ≫ N.U.hom = s.snd ≫ pullback.fst π π ≫ π := fun s => by
    rw [Category.assoc, ← hUU]; exact s.condition
  have hb : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      (s.fst ≫ (snd N.U N.U).left) ≫ N.U.hom = s.snd ≫ pullback.fst π π ≫ π := fun s => by
    rw [Category.assoc, ← cUU, ← hUU]; exact s.condition
  have hab : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      liftU N _ _ (ha s) ≫ (Desc.UT N).hom = liftU N _ _ (hb s) ≫ (Desc.UT N).hom := fun s => by
    rw [liftU_hom, liftU_hom]
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ (pairU_over N)) ?_
  refine PullbackCone.IsLimit.mk (pairU_over N) (fun s => (liftTT _ _ (hab s)).choose) ?_ ?_ ?_
  · intro s
    obtain ⟨h1, h2⟩ := (liftTT _ _ (hab s)).choose_spec
    apply extUU
    · rw [Category.assoc, pairU_fst, ← Category.assoc, h1, liftU_prU]
    · rw [Category.assoc, pairU_snd, ← Category.assoc, h2, liftU_prU]
  · intro s
    obtain ⟨h1, _⟩ := (liftTT _ _ (hab s)).choose_spec
    show _ ≫ (Desc.UT N ⊗ Desc.UT N).hom = _
    rw [hTT, ← Category.assoc, h1, liftU_hom]
  · intro s m m1 m2
    obtain ⟨h1, h2⟩ := (liftTT _ _ (hab s)).choose_spec
    have m2' : m ≫ (Desc.UT N ⊗ Desc.UT N).hom = s.snd := m2
    rw [hTT] at m2'
    apply extTT
    · rw [h1]
      apply UT_ext
      · rw [liftU_prU, Category.assoc, ← pairU_fst, ← Category.assoc, m1]
      · rw [liftU_hom, Category.assoc, m2']
    · rw [h2]
      apply UT_ext
      · rw [liftU_prU, Category.assoc, ← pairU_snd, ← Category.assoc, m1]
      · rw [liftU_hom, Category.assoc, ← cTT, m2']

end GlobalTheory.Mum.DescKP
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Desc.toS N p hp ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

theorem toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Desc.toS N p hp ≫ pullback.snd _ _ = pullback.snd _ _ ≫ p := pullback.lift_snd _ _ _

theorem embL_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.emb N p hp).left ≫ pullback.fst G.hom p = Desc.toS N p hp ≫ N.u := pullback.lift_fst _ _ _

theorem embL_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.emb N p hp).left ≫ pullback.snd G.hom p = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem pairU_fst' (N : Near π G) :
    pairU N ≫ (fst N.U N.U).left = (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ := by
  show (lift (fstU N) (sndU N) ≫ fst _ _).left = _
  rw [lift_fst]; rfl

theorem pairU_snd' (N : Near π G) :
    pairU N ≫ (snd N.U N.U).left = (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ := by
  show (lift (fstU N) (sndU N) ≫ snd _ _).left = _
  rw [lift_snd]; rfl

theorem fst_hom' (N : Near π G) :
    (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.snd N.U.hom (pullback.fst π π ≫ π) = (Desc.UT N ⊗ Desc.UT N).hom :=
  Over.w (fst (Desc.UT N) (Desc.UT N))

theorem snd_hom' (N : Near π G) :
    (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.snd N.U.hom (pullback.fst π π ≫ π) = (Desc.UT N ⊗ Desc.UT N).hom :=
  Over.w (snd (Desc.UT N) (Desc.UT N))

theorem mT_fst' (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) : mT N V m hm ≫ pullback.fst _ _ = (pairU N ∣_ V) ≫ m :=
  pullback.lift_fst _ _ _

theorem mT_snd' (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) :
    mT N V m hm ≫ pullback.snd _ _ = (VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.DescKP

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem fst_toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.fst _ _ =
      (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ :=
  (Category.assoc _ _ _).trans (congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_fst' N p hp))

theorem snd_toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.fst _ _ =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ :=
  (Category.assoc _ _ _).trans (congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_fst' N p hp))

theorem fst_toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.snd _ _ = (Desc.UT N ⊗ Desc.UT N).hom ≫ p :=
  (Category.assoc _ _ _).trans ((congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_snd' N p hp)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (fst_hom' N))))

theorem snd_toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.snd _ _ = (Desc.UT N ⊗ Desc.UT N).hom ≫ p :=
  (Category.assoc _ _ _).trans ((congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_snd' N p hp)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (snd_hom' N))))

theorem fst_toS_u' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ N.u =
      (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.emb N p hp).left ≫ pullback.fst G.hom p :=
  (Category.assoc _ _ _).trans (congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (embL_fst' N p hp).symm)

theorem snd_toS_u' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ N.u =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ (Desc.emb N p hp).left ≫ pullback.fst G.hom p :=
  (Category.assoc _ _ _).trans (congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (embL_fst' N p hp).symm)

end GlobalTheory.Mum.DescKP

namespace GlobalTheory.Mum.DescKP

theorem sum_eq_mT_emb : ∀ {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G] (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left) (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom), (∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left → N.Pt s (v ≫ m) (x * y).left) → ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π), (DescKP.VT N V).ι ≫ (Desc.sum N p hp).left = DescKP.mT N V m hm ≫ (Desc.emb N p hp).left := by
  intro R _ _ S π G _ N V m hm law p hp
  let T0 : Over (pullback π π) := Over.mk ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)
  let ι0 : T0 ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk (VT N V).ι rfl
  let a : T0 ⟶ (Over.pullback p).obj G := ι0 ≫ fst _ _ ≫ Desc.emb N p hp
  let b : T0 ⟶ (Over.pullback p).obj G := ι0 ≫ snd _ _ ≫ Desc.emb N p hp
  have hab : ι0 ≫ Desc.sum N p hp = a * b := by rw [Desc.sum, comp_mul]
  have wpt : ∀ c : T0 ⟶ (Over.pullback p).obj G, (c.left ≫ pullback.fst G.hom p) ≫ G.hom = T0.hom ≫ p := by
    intro c
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ p) (Over.w c)
  let x : Over.mk (T0.hom ≫ p) ⟶ G := Over.homMk (a.left ≫ pullback.fst G.hom p) (wpt a)
  let y : Over.mk (T0.hom ≫ p) ⟶ G := Over.homMk (b.left ≫ pullback.fst G.hom p) (wpt b)
  have hxy : (x * y).left = (a * b).left ≫ pullback.fst G.hom p :=
    (isGrpPullback_pullback G p).2 T0 a b x y rfl rfl
  have e : (pairU N ∣_ V) ≫ V.ι = (VT N V).ι ≫ pairU N := morphismRestrict_ι _ _
  have e' : ∀ {Z : Scheme.{0}} (h : (N.U ⊗ N.U).left ⟶ Z), (pairU N ∣_ V) ≫ V.ι ≫ h = (VT N V).ι ≫ pairU N ≫ h :=
    fun h => by rw [← Category.assoc, e, Category.assoc]
  have ptx : N.Pt (T0.hom ≫ p) ((pairU N ∣_ V) ≫ V.ι ≫ (fst N.U N.U).left) x.left := by
    refine ⟨(VT N V).ι ≫ (fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) ((fst_toS_fst' N p hp).trans (pairU_fst' N).symm)).trans (e' _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (fst_toS_snd' N p hp)).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (fst_toS_u' N p hp)).trans (Category.assoc _ _ _).symm)
  have pty : N.Pt (T0.hom ≫ p) ((pairU N ∣_ V) ≫ V.ι ≫ (snd N.U N.U).left) y.left := by
    refine ⟨(VT N V).ι ≫ (snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) ((snd_toS_fst' N p hp).trans (pairU_snd' N).symm)).trans (e' _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (snd_toS_snd' N p hp)).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (snd_toS_u' N p hp)).trans (Category.assoc _ _ _).symm)
  obtain ⟨x₀, h₁, h₂, h₃⟩ := law (VT N V).toScheme (pairU N ∣_ V) (T0.hom ≫ p) x y ptx pty
  have hx₀ : x₀ = mT N V m hm ≫ Desc.toS N p hp := by
    apply pullback.hom_ext
    · exact h₁.trans (((Category.assoc _ _ _).trans ((congrArg (mT N V m hm ≫ ·) (toS_fst' N p hp)).trans (mT_fst' N V m hm))).symm)
    · exact h₂.trans (((Category.assoc _ _ _).trans ((congrArg (mT N V m hm ≫ ·) (toS_snd' N p hp)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (mT_snd' N V m hm))))).symm)
  apply pullback.hom_ext
  · rw [Category.assoc (mT N V m hm), embL_fst']
    refine (?_ : _ = (mT N V m hm ≫ Desc.toS N p hp) ≫ N.u).trans (Category.assoc _ _ _)
    rw [← hx₀, h₃, hxy, ← hab]
    rfl
  · have w : (Desc.sum N p hp).left ≫ pullback.snd G.hom p = (Desc.UT N ⊗ Desc.UT N).hom := Over.w _
    rw [Category.assoc, w, Category.assoc, embL_snd', mT_snd']

end GlobalTheory.Mum.DescKP
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

def postHom {S : Scheme.{0}} (T : Over S) {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    (T ⟶ A) →* (T ⟶ B) where
  toFun x := x ≫ f
  map_one' := by simp
  map_mul' x y := by simp [MonObj.mul_comp]

def preHom {S : Scheme.{0}} {T A : Over S} (x : T ⟶ A) (B : Over S) [GrpObj B] :
    (A ⟶ B) →* (T ⟶ B) where
  toFun y := x ≫ y
  map_one' := by simp
  map_mul' y z := by simp [MonObj.comp_mul]

theorem zpow_finset_sum {G J : Type} [CommGroup G] (g : G) (s : Finset J) (e : J → ℤ) :
    g ^ (∑ i ∈ s, e i) = ∏ i ∈ s, g ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

theorem prod_prod_zpow {G C J : Type} [CommGroup G] [Fintype C] [Fintype J] (b : C → G) (x : J → C → ℤ) (k : J → ℤ) :
    ∏ i, (∏ c, b c ^ x i c) ^ k i = ∏ c, b c ^ (∑ i, k i * x i c) := by
  simp only [← Finset.prod_zpow, ← zpow_mul, zpow_finset_sum]
  rw [Finset.prod_comm]
  simp only [mul_comm]

theorem pow_val_intCast {G : Type} [Group G] {N : ℕ} (hN : 0 < N) {g : G} (hg : g ^ N = 1) (k : ℤ) :
    g ^ ((k : ZMod N)).val = g ^ k := by
  haveI : NeZero N := ⟨hN.ne'⟩
  rw [← zpow_natCast, ZMod.val_intCast]
  exact (zpow_eq_zpow_emod' k hg).symm

theorem prod_zpow_pow_eq_one {G C : Type} [CommGroup G] [Fintype C] {N : ℕ} {b : C → G} (hb : ∀ c, b c ^ N = 1)
    (x : C → ℤ) : (∏ c, b c ^ x c) ^ N = 1 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun c _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

theorem sum_labMat_mul (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) (a : Fin 2)
    (i : Fin (2 * (8 * h))) (u : Fin 8) (c : Fin h ⊕ Fin h) :
    ∑ i', labMat W hW h a i' i * sharpBasis W hW h (Pi.single i' 1) u c =
      ∑ v, actMat W a u v * sharpBasis W hW h (Pi.single i 1) v c := by
  have key : ∀ y : Fin (2 * (8 * h)) → ℤ,
      ∑ i', y i' * sharpBasis W hW h (Pi.single i' 1) u c = sharpBasis W hW h y u c := by
    intro y
    conv_rhs => rw [pi_eq_sum_univ' y]

    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact (key _).trans (congrFun (congrFun ((sharpBasis W hW h).apply_symm_apply _) u) c)

theorem ptOf_torsion_and_act : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (gQ : ℕ) {S : Scheme.{0}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (hP : E8Fibration.IsProd pr) (N : ℕ) {T : Over S}
  (b : Fin gQ ⊕ Fin gQ → (T ⟶ B)), (∀ c, b c ^ N = 1) → 0 < N →
  (∀ i, E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ^ N = 1) ∧
  ∀ (act : Fin 2 → (A ⟶ A)), (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) → ∀ (a : Fin 2) (i : Fin (2 * (8 * gQ))),
    E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a =
      Out.linComb (fun i' => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1)))
        (fun i' => ((E8Fibration.Lab.labMat W hW.2 gQ a i' i : ZMod N)).val) := by
  intro W hW gQ S A B _ _ _ _ pr hP N T b hb hN
  have ext : ∀ x y : T ⟶ A, (∀ u, x ≫ pr u = y ≫ pr u) → x = y := fun x y h =>
    (hP.2 T fun u => y ≫ pr u).unique h fun _ => rfl
  refine ⟨fun i => ext _ _ fun u => ?_, fun act hact a i => ext _ _ fun u => ?_⟩
  · haveI := hP.1 u
    have := map_pow (postHom T (pr u)) (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1))) N
    refine this.trans ?_
    change (ptOf hP b _ ≫ pr u) ^ N = _
    rw [ptOf_pr, prod_zpow_pow_eq_one hb]
    exact (map_one (postHom T (pr u))).symm
  · haveI := hP.1 u
    have h1 : (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a) ≫ pr u =
        ∏ c, b c ^ (∑ v, actMat W a u v * sharpBasis W hW.2 gQ (Pi.single i 1) v c) := by
      rw [Category.assoc, hact a u, ← prod_prod_zpow]
      refine (map_prod (preHom (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1))) B) _ _).trans ?_
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_zpow, ← ptOf_pr hP]
      rfl
    rw [h1, Out.linComb, List.prod_ofFn]
    refine Eq.trans ?_ (map_prod (postHom T (pr u)) _ _).symm
    simp only [← sum_labMat_mul W hW.2 gQ a i u]
    rw [← prod_prod_zpow]
    refine Finset.prod_congr rfl fun i' _ => ?_
    rw [map_pow, ← pow_val_intCast hN (prod_zpow_pow_eq_one hb _), ← ptOf_pr hP]
    rfl

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem symLift_thTw : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (x x' : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))), SymLift A.A A.L N N x θ → x'.left = spMap τ.toRingHom ≫ x.left → SymLift A.A A.L N N x' (thTw A N τ θ) := by
  intro R _ _ A N τ x x' θ h hx
  have ex : x' = twK τ ≫ x := Over.OverMorphism.ext (by rw [hx, Over.comp_left, twK_left])
  subst ex
  have eM : mTw A τ = twK τ ▷ A.A := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [mTw_fst, whiskerRight_fst]
    · rw [mTw_snd, whiskerRight_snd]
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.symLift_pull A.isLB (twK τ) h _ (thTw A N τ θ).isGen fun r z J hJ => by
    show val (genCast _ _) r z J = _
    rw [val_genCast]
    exact (val_pull hJ _ _ r).trans (by rw [eM])

end GlobalTheory.Mum.Conj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_rigidified_translatedBundle_iso_psi_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A), IsMonHom β → ∀ w₀ : LB.Iso D₂.toPre.P.L (D.toPre.P.L.pull (padd D.toPre.P.A β (toUnit D₂.toPre.P.A ≫ g.b)).left), w₀.IsGen → ∃ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε), w.IsGen ∧ ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left)) := by
  first | exact @GlobalTheory.MumCmp.Norm.exists_rigidified | exact GlobalTheory.MumCmp.Norm.exists_rigidified | (intros; apply GlobalTheory.MumCmp.Norm.exists_rigidified <;> assumption)
end
