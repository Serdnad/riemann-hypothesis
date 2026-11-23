module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSectionOfAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle010
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedTwistedFactorValueAtLatticePoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DiagPic

open GlobalTheory.CechPic

theorem pull_inv {K : Type} [Field K] (A : PolAV (Sp K)) :
    pull (GrpObj.inv : A.A ⟶ A.A).left (cls A.L A.isLB) = cls A.L A.isLB := by
  obtain ⟨U, hU, ht⟩ := A.sym (default : PrimeSpectrum K)
  have h := (cls_eq_zero_iff (LB.isLB_linComb A.isLB _ _)).2 ht
  rw [cls_linComb A.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, add_neg_eq_zero] at h
  have hr : Set.range (𝟙 A.A.left : A.A.left ⟶ A.A.left) ⊆ Set.range (A.A.hom ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    intro x _
    have e : A.A.hom x = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    show A.A.hom x ∈ U
    rw [e]
    exact hU
  have h' := congrArg (pull (IsOpenImmersion.lift (A.A.hom ⁻¹ᵁ U).ι (𝟙 _) hr)) h
  rwa [← pull_comp, ← pull_comp, IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac, Category.id_comp,
    pull_id] at h'

theorem pull_one {S : Scheme.{0}} (A : PolAV S) {T : Over S} :
    pull (1 : T ⟶ A.A).left (cls A.L A.isLB) = 0 := by
  have h := (cls_eq_zero_iff (pull_isLB A.isLB _)).2 A.rigid
  rw [cls_pull A.isLB] at h
  rw [Hom.one_def, Over.comp_left, pull_comp]
  exact (congrArg _ h).trans (map_zero _)

theorem lam_self {K : Type} [Field K] (A : PolAV (Sp K)) :
    lam (cls A.L A.isLB) (𝟙 A.A) (𝟙 A.A) = 2 • cls A.L A.isLB := by
  have h := lam_mul_left A.isLB (GlobalTheory.Moduli.cube_of_isLB _ A A.L A.isLB) (𝟙 A.A) (𝟙 A.A)⁻¹ (𝟙 A.A)
  rw [mul_inv_cancel, lam_one_left] at h
  have e : lam (cls A.L A.isLB) (𝟙 A.A)⁻¹ (𝟙 A.A) = -(2 • cls A.L A.isLB) := by
    rw [lam, inv_mul_cancel, pull_one, Hom.inv_def, Category.id_comp, pull_inv, Over.id_left, pull_id]
    abel
  rw [e] at h
  exact (add_neg_eq_zero.1 h.symm)

theorem pull_sq {K : Type} [Field K] (A : PolAV (Sp K)) :
    pull ((𝟙 A.A) ^ 2 : A.A ⟶ A.A).left (cls A.L A.isLB) = 4 • cls A.L A.isLB := by
  have h := lam_self A
  rw [lam, pull_one, Over.id_left, pull_id, add_zero, sub_sub, sub_eq_iff_eq_add] at h
  rw [pow_two, h]
  abel

end GlobalTheory.Mum.DiagPic

namespace GlobalTheory.Mum

open GlobalTheory.CechPic

theorem two_smul_cls_eq_pull_diag_and_pull_sq : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (c : GlobalTheory.CechPic.Pic (pullback G.hom (jK R))) (d : GlobalTheory.CechPic.Pic G.left) (hL : (A.L.pull gen.hom.left).IsLB) (hP : (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left).IsLB), c = GlobalTheory.CechPic.cls (A.L.pull gen.hom.left) hL → d = GlobalTheory.CechPic.cls (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left) hP → 2 • c = GlobalTheory.CechPic.pull (pullback.fst G.hom (jK R)) d ∧ ∃ φ : pullback G.hom (jK R) ⟶ pullback G.hom (jK R), φ ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ ((𝟙 G) ^ 2 : G ⟶ G).left ∧ GlobalTheory.CechPic.pull φ c = 4 • c := by
  intro R _ _ G _ _ A gen hgen PP hExt c d hL hP hc hd
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have hc' : c = pull gen.hom.left (cls A.L A.isLB) := hc
  refine ⟨?_, ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left, ?_, ?_⟩
  · obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _
      (isGrpPullback_pullback G (jK R))
    have h₁ := (cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hExt.1 g₂)).2 (hExt.2 g₂ hg₂)
    have h₂ := (cls_cube_two hL (fst _ _) (snd _ _) (LB.isLB_linComb hL _ _)).symm.trans h₁
    have h₃ := congrArg (pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left) h₂
    have e : (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left ≫ g₂ =
        pullback.fst G.hom (jK R) ≫ (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left := by
      apply pullback.hom_ext
      · show (_ ≫ g₂) ≫ (fst G G).left = (_ ≫ _) ≫ (fst G G).left
        rw [Category.assoc, hg₂.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
          lift_fst, Over.id_left, Over.id_left]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      · show (_ ≫ g₂) ≫ (snd G G).left = (_ ≫ _) ≫ (snd G G).left
        rw [Category.assoc, hg₂.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
          lift_snd, Over.id_left, Over.id_left]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    rw [pull_lam, lift_fst, lift_snd, cls_pull hExt.1, ← pull_comp, e, pull_comp, cls_pull A.isLB, lam_pull,
      Category.id_comp] at h₃
    have h₄ := pull_lam gen.hom (cls A.L A.isLB) (𝟙 _) (𝟙 _)
    rw [Category.comp_id, DiagPic.lam_self, map_nsmul] at h₄
    rw [hc', hd]
    exact h₄.trans h₃
  · have e : ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G) = (Over.pullback (jK R)).map ((𝟙 G) ^ 2) := by
      letI : (Over.pullback (jK R)).Monoidal := (Over.instBraidedPullback (f := jK R)).toMonoidal
      rw [pow_two, pow_two, Functor.map_mul, CategoryTheory.Functor.map_id]
    rw [e]
    exact pullback.lift_fst _ _ _
  · have e : ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G) ≫ gen.hom = gen.hom ≫ (𝟙 A.A) ^ 2 := by
      rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
    have h := congrArg (pull gen.hom.left) (DiagPic.pull_sq A)
    rw [← pull_comp, ← Over.comp_left, ← e, Over.comp_left, pull_comp, map_nsmul] at h
    rw [hc']
    exact h

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Rigid

open GlobalTheory.CechPic

theorem pull_cls_P {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}
    (m : ObjMap o' o f) : pull m.φ₂ (cls o.P o.isLB) = cls o'.P o'.isLB := by
  rw [← cls_pull o.isLB m.φ₂ (pull_isLB o.isLB m.φ₂)]
  exact ((cls_eq_iff o'.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol).symm

theorem objMap_phi_unique : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (f f' : S' ⟶ S) (m₁ : ObjMap o' o f) (m₂ : ObjMap o' o f'), f = f' → m₁.φ = m₂.φ := by
  intro p _ D R _ b N hN hNp S S' s s' o o' f f' m₁ m₂ hf
  subst hf
  let α : o'.A.left ⟶ o'.A.left := m₂.cart.1.lift m₁.φ o'.A.hom m₁.cart.1.w
  have e₁ : α ≫ m₂.φ = m₁.φ := m₂.cart.1.lift_fst _ _ _
  have e₂ : α ≫ o'.A.hom = o'.A.hom := m₂.cart.1.lift_snd _ _ _
  have hα : IsGrpPullback o'.A o'.A (𝟙 _) α :=
    IsGrpPullback.cancel m₂.cart (by rw [Category.id_comp, e₁]; exact m₁.cart) (by rw [e₂, Category.comp_id])
  let α' : o'.A ⟶ o'.A := Over.homMk α e₂
  let φ₂ : (G2 o'.A).left ⟶ (G2 o'.A).left := (lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α')).left
  have sq : IsSquare α φ₂ := by
    constructor
    · show (lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α') ≫ fst o'.A o'.A).left = _
      rw [lift_fst]; rfl
    · show (lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α') ≫ snd o'.A o'.A).left = _
      rw [lift_snd]; rfl
  have e₃ : φ₂ ≫ m₂.φ₂ = m₁.φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst o.A o.A).left = _ ≫ (fst o.A o.A).left
      rw [Category.assoc, m₂.sq.1, ← Category.assoc, sq.1, Category.assoc, e₁, m₁.sq.1]
    · show (_ ≫ _) ≫ (snd o.A o.A).left = _ ≫ (snd o.A o.A).left
      rw [Category.assoc, m₂.sq.2, ← Category.assoc, sq.2, Category.assoc, e₁, m₁.sq.2]
  have act : ∀ c, (o'.act.act c).left ≫ α = α ≫ (o'.act.act c).left := fun c => by
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, e₁, m₂.act, ← Category.assoc, e₁, m₁.act]
    · simp only [Category.assoc, e₂, Over.w]
  have eta : ∀ y, (o'.eta y).left ≫ α = 𝟙 S' ≫ (o'.eta y).left := fun y => by
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, e₁, m₁.eta, Category.id_comp, m₂.eta]
    · rw [Category.assoc, e₂, Category.id_comp]
  have pol : LBIso o'.P (o'.P.pull φ₂) := by
    refine (cls_eq_iff o'.isLB (pull_isLB o'.isLB φ₂)).1 ?_
    rw [cls_pull o'.isLB φ₂]
    conv_lhs => rw [← pull_cls_P m₁]
    rw [← e₃, pull_comp, pull_cls_P m₂]
  let m : ObjMap o' o' (𝟙 S') := ⟨α, φ₂, hα, sq, act, pol, eta⟩
  have h := eq_id p D R b N hN hNp S' s' o' m
  change α = 𝟙 _ at h
  rw [← e₁, h, Category.id_comp]

end GlobalTheory.UPel.HT.Rigid
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

theorem _root_.GlobalTheory.T.exists_symplecticLevel_principalSiegel_algClosed : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N), Odd N → 3 ≤ N → c.Principal → SmoothOfRelativeDimension g c.A.hom → ∃ C : SiegPre g N (b.ζ : K) (𝟙 (Sp K)), SRel C c 0 0 (𝟙 _) := by
  first | exact @GlobalTheory.SiegLift.exists_level_of_forget | exact GlobalTheory.SiegLift.exists_level_of_forget | (intros; apply GlobalTheory.SiegLift.exists_level_of_forget <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

theorem _root_.GlobalTheory.T.eighthPower_E8Bundle_iso_of_principalSiegelIso : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N) (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (t : TObj (8 * g) N J b (𝟙 (Sp K))) (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ Q.A, ∀ u, x ≫ pr u = y u) → LBIso Q.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → SRel C c 0 0 (𝟙 _) → IsSharp W a bas t C → ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
  first | exact @GlobalTheory.SharpIso.iso_of_sRel | exact GlobalTheory.SharpIso.iso_of_sRel | (intros; apply GlobalTheory.SharpIso.iso_of_sRel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

theorem _root_.GlobalTheory.T.compatible_roots_evaluation_injective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → (∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z))))) → ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  first | (exact @GlobalTheory.UPel.HT.GTateGlue.glue) | (exact GlobalTheory.UPel.HT.GTateGlue.glue) | (intros; apply GlobalTheory.UPel.HT.GTateGlue.glue  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open Filter Topology

namespace GlobalTheory.PELU.LocLiftU

theorem comp_pow_one {X : Scheme.{0}} {G : Over X} [GrpObj G] {T U : Over X} (f : T ⟶ U) (x : U ⟶ G) {n : ℕ}
    (h : x ^ n = 1) : (f ≫ x) ^ n = 1 := by
  have : ∀ k : ℕ, (f ≫ x) ^ k = f ≫ x ^ k := fun k => by
    induction k with
    | zero => simp only [pow_zero, MonObj.comp_one]
    | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  rw [this, h, MonObj.comp_one]

end GlobalTheory.PELU.LocLiftU

namespace GlobalTheory.PELU

open LocLiftU



theorem holomorphic_map_lifts_to_periods : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)) (b₀ : Fin m → ℂ) P₀ e₀, 0 < N → (∀ a, F.eta a ^ N = 1) → LocallyOfFiniteType F.s → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ F.s = spMap (RingHom.id ℂ)) → IsHolTo B y → UnifAt F (RingHom.id ℂ) ρ N D' t P₀ (y b₀) e₀ → ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ρ B' P ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', UnifAt F (RingHom.id ℂ) ρ N D' t (P b) (y b) (e b) := by
  intro O _ bar g ρ Λ F N D' t m B y b₀ P₀ e₀ hN heta hlft hB hb₀ hyσ hy hU
  obtain ⟨-, hper₀, hexp₀, hker₀, hact₀, hweil₀, heta₀⟩ := hU
  have hab : IsAbelianScheme F.A := F.ab
  haveI := hab.proper
  obtain ⟨B₁, e, r, hB₁, hb₁, hB₁B, rfl, hr, hol, he, hl⟩ :=
    GlobalTheory.RelExp.exists_relative_exp ℂ (RingHom.id ℂ) F.X F.s F.A g m B y b₀ e₀ hlft hab F.dim hB hb₀ hyσ hy hexp₀
  change GlobalTheory.LocLift.HasLifts B₁ y e at hl
  change ∀ b ∈ B₁, GlobalTheory.LocLift.IsExp (y b) (e b) ∧ _ at he
  have hy₁ := GlobalTheory.LocLift.isHolTo_mono hy hB₁ hB₁B
  obtain ⟨P, hP₀, hP⟩ := GlobalTheory.LocLift.exists_periods GlobalTheory.latContinuation hB₁ hb₁ hy₁ hr hol he hl P₀ hper₀.2.1
    hper₀.2.2.2.1 hker₀
  choose L hL1 hL2 using fun a : O =>
    haveI := F.hom a; GlobalTheory.LocLift.exists_hol_linear_lift hB₁ hr hol he hl (F.act a)
  have hL0 : ∀ a, L a b₀ = Matrix.toLin' (ρ a) := fun a =>
    GlobalTheory.LocLift.linear_lift_unique (he b₀ hb₁).1.1 hr (he b₀ hb₁).2 fun z => by
      rw [hL1 a b₀ hb₁, Matrix.toLin'_apply, hact₀]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and (hB₁.mem_nhds hb₁))
  set C := Metric.ball b₀ ε
  have hCo : IsOpen C := Metric.isOpen_ball
  have hCc : IsPreconnected C := (convex_ball b₀ ε).isPreconnected
  have hC₀ : b₀ ∈ C := Metric.mem_ball_self hε
  have hC₁ : C ⊆ B₁ := fun b hb => (hball b hb).2
  have hPd : ∀ x, DifferentiableOn ℂ (fun b => P b x) C := fun x b hb =>
    ((hball b hb).1.1 x).differentiableWithinAt
  have hmv : ∀ {M : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
      {W : Set V} {β : V → (Fin m → ℂ)} {v : V → (Fin g → ℂ)}, (∀ i j, DifferentiableOn ℂ (fun w => M (β w) i j) W) →
      DifferentiableOn ℂ v W → DifferentiableOn ℂ (fun w => (M (β w)) *ᵥ (v w)) W := fun hM hv =>
    differentiableOn_pi.2 fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact DifferentiableOn.fun_sum fun j _ => (hM i j).fun_mul (differentiableOn_pi.1 hv j)
  have hLm : ∀ a i j, DifferentiableOn ℂ (fun b => LinearMap.toMatrix' (L a b) i j) B₁ := fun a i j => by
    simp only [LinearMap.toMatrix'_apply]
    exact differentiableOn_pi.1 (hL2 a (Pi.single j 1)) i
  have hk1 : ∀ b ∈ C, ∀ x, e b (P b x) = 1 := fun b hb x => ((hball b hb).1.2.1 _).2 ⟨x, rfl⟩
  have hlin : ∀ (a : O) x, ∀ b ∈ C, P b (a • x) - L a b (P b x) = 0 := fun a x => by
    haveI := F.hom a
    have hd : ContinuousOn (fun b => P b (a • x) - L a b (P b x)) C := by
      refine ((hPd _).sub ((hmv (M := fun b => LinearMap.toMatrix' (L a b)) (β := id)
        (fun i j => (hLm a i j).mono hC₁) (hPd x)).congr fun b _ => ?_)).continuousOn
      exact (LinearMap.toMatrix'_mulVec (L a b) (P b x)).symm
    refine GlobalTheory.LocLift.eq_zero_of_small hCc hd hr (fun b hb hn => (he b (hC₁ hb)).2 _ hn ?_) hC₀ ?_
    · exact (GlobalTheory.LocLift.hom_sub_eq_one (he b (hC₁ hb)).1.1).2
        (by rw [hL1 a b (hC₁ hb), hk1 b hb, hk1 b hb, MonObj.one_comp])
    · simp only [hP₀, hL0, Matrix.toLin'_apply, hper₀.1, sub_self]
  have htor : ∀ (k : ℕ) x, IsHolTo C (fun b => (e b ((k : ℂ)⁻¹ • P b x)).left) := fun k x =>
    GlobalTheory.LocLift.isHolTo_comp (β := fun b => (b, (k : ℂ)⁻¹ • P b x)) hol hCo
      (differentiableOn_id.prodMk ((hPd x).fun_const_smul _)) fun b hb => ⟨hC₁ hb, trivial⟩
  have hpow : ∀ (k : ℕ), 0 < k → ∀ x, ∀ b ∈ C, e b ((k : ℂ)⁻¹ • P b x) ^ k = 1 := fun k hk x b hb => by
    rw [← GlobalTheory.LocLift.hom_nsmul (he b (hC₁ hb)).1.1, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne'), hk1 b hb]
  have hyC : ∀ b ∈ C, y b ≫ F.s = spMap (RingHom.id ℂ) := fun b hb => hyσ b (hB₁B (hC₁ hb))
  have hwe : ∀ b ∈ C, ∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
      Out.WeilIs F.A F.L k (e b ((k : ℂ)⁻¹ • P b a)) (e b ((k : ℂ)⁻¹ • P b a₂)) (unitOn c) :=
    fun b hb k a a₂ c hk hc => (GlobalTheory.T.torsion_commutatorPairing_const_holomorphicFamily_anyLineBundle F.X F.s F.A F.L hlft hab F.isLB m k C y
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) (fun b => e b ((k : ℂ)⁻¹ • P b a₂)) c b₀ hk hCo hCc hC₀ hyC
      (htor k a) (htor k a₂) fun b hb => ⟨hpow k hk a b hb, hpow k hk a₂ b hb⟩).2
      (by simp only [hP₀]; exact hweil₀ k a a₂ c hk hc) b hb
  have heC : ∀ a, ∀ b ∈ C, toUnit _ ≫ F.eta a = e b ((N : ℂ)⁻¹ • P b (t a)) := fun a =>
    (GlobalTheory.T.torsion_commutatorPairing_const_holomorphicFamily_anyLineBundle F.X F.s F.A F.L hlft hab F.isLB m N C y (fun b => toUnit _ ≫ F.eta a)
      (fun b => e b ((N : ℂ)⁻¹ • P b (t a))) 1 b₀ hN hCo hCc hC₀ hyC
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.LocLift.isHolTo_comp_hom (GlobalTheory.LocLift.isHolTo_mono hy₁ hCo hC₁)
        (F.eta a).left) fun b _ => by rw [Over.comp_left, Over.toUnit_left]; rfl) (htor N (t a))
      fun b hb => ⟨comp_pow_one _ _ (heta a), hpow N hN (t a) b hb⟩).1 (by rw [hP₀]; exact heta₀ a)
  obtain ⟨B₂, h, hB₂, hb₂, hB₂C, hh₀, hhd, hh⟩ := GlobalTheory.T.holomorphic_lattice_family_retype_periodType O bar g ρ D' m C b₀ P hCo hC₀ hPd
    (by rw [hP₀]; exact hper₀) fun b hb => ⟨(hball b hb).1.2.2.2.1, fun a => ⟨LinearMap.toMatrix' (L a b), fun x => by
      rw [LinearMap.toMatrix'_mulVec]; exact sub_eq_zero.1 (hlin a x b hb)⟩⟩
  have hdet : ∀ b ∈ B₂, IsUnit (h b).det := fun b hb => (Matrix.isUnit_iff_isUnit_det _).1 (hh b hb).1
  obtain ⟨P', hP'⟩ := GlobalTheory.LocLift.exists_mulVec_comp h P
  have hinv : ∀ b ∈ B₂, ∀ z, (h b)⁻¹ *ᵥ (h b *ᵥ z) = z := fun b hb z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hdet b hb), Matrix.one_mulVec]
  have hinv' : ∀ b ∈ B₂, ∀ z, h b *ᵥ ((h b)⁻¹ *ᵥ z) = z := fun b hb z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet b hb), Matrix.one_mulVec]
  have key : ∀ b ∈ B₂, UnifAt F (RingHom.id ℂ) ρ N D' t (P' b) (y b) (fun z => e b ((h b)⁻¹ *ᵥ z)) := by
    intro b hb
    have hbC := hB₂C hb
    have hb1 := hC₁ hbC
    obtain ⟨j, hj⟩ := GlobalTheory.LocLift.exists_equiv_mulVec (hdet b hb)
    have hjs : ∀ z, (h b)⁻¹ *ᵥ z = j.symm z := fun z => by
      conv_lhs => rw [← j.apply_symm_apply z, ← hj]
      exact hinv b hb _
    have hPj : ∀ x, P' b x = j (P b x) := fun x => by rw [hP', hj]
    have hsm : ∀ (s : ℂ) x, (h b)⁻¹ *ᵥ (s • P' b x) = s • P b x := fun s x => by
      rw [Matrix.mulVec_smul, hP', hinv b hb]
    have hex : IsExp (y b) (fun z => e b ((h b)⁻¹ *ᵥ z)) := by
      have e1 : (fun z => e b ((h b)⁻¹ *ᵥ z)) = fun z => e b (j.symm z) := funext fun z => by rw [hjs]
      rw [e1]
      exact GlobalTheory.LocLift.IsExp.comp (he b hb1).1 j.symm
    have hPinj : Function.Injective (P' b) := fun x x' hx =>
      (hball b hbC).1.2.2.1 (j.injective (by rw [← hPj, ← hPj, hx]))
    have hker : ∀ z, e b ((h b)⁻¹ *ᵥ z) = 1 ↔ z ∈ (P' b).range := fun z => by
      rw [hjs, (hball b hbC).1.2.1]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [hPj, hx, j.apply_symm_apply]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [← hx, hPj, j.symm_apply_apply]⟩
    have hweil' : ∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
        Out.WeilIs F.A F.L k (e b ((h b)⁻¹ *ᵥ ((k : ℂ)⁻¹ • P' b a))) (e b ((h b)⁻¹ *ᵥ ((k : ℂ)⁻¹ • P' b a₂)))
          (unitOn c) := fun k a a₂ c hk hc => by
      rw [hsm, hsm]
      exact hwe b hbC k a a₂ c hk hc
    obtain ⟨Hm, EF', h1, h2, h3, h4⟩ :=
      GlobalTheory.T.exists_positiveRiemannForm_of_relAmple_exponential F.X F.A g hab F.dim F.L F.isLB F.ample (y b) _ D'.La (P' b) hex hPinj hker
    have hEF : ∀ x x', EF' x x' = D'.EF x x' := fun x x' => GlobalTheory.LocLift.int_eq_of_exp fun k hk => by
      have := congrArg Units.val (GlobalTheory.T.weilPairing_complex_value_unique F.X F.A g hab F.dim F.L F.isLB (y b) k _ _
        (Units.mk0 _ (Complex.exp_ne_zero _)) (Units.mk0 _ (Complex.exp_ne_zero _)) (h4 k x x' _ hk rfl)
        (hweil' k x x' _ hk rfl))
      exact this
    obtain ⟨sp, dc⟩ := GlobalTheory.LocLift.lattice_comp j.symm (P := P b) (P' := P' b)
      (fun x => by rw [hPj, j.symm_apply_apply]) (hball b hbC).1.2.2.2.1 (hball b hbC).1.2.2.2.2
    have hclaim : ∀ (a : O) w, (h b)⁻¹ *ᵥ (ρ a *ᵥ (h b *ᵥ w)) = L a b w := fun a w => by
      have hfg : ((Matrix.toLin' (h b)⁻¹ ∘ₗ Matrix.toLin' (ρ a) ∘ₗ Matrix.toLin' (h b)).restrictScalars ℝ) =
          (L a b).restrictScalars ℝ := LinearMap.ext_on (hball b hbC).1.2.2.2.1 (by
        rintro _ ⟨x, rfl⟩
        simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply]
        rw [← (hh b hb).2 a x, hinv b hb]
        exact sub_eq_zero.1 (hlin a x b hbC))
      have := LinearMap.congr_fun hfg w
      simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply] at this
      exact this
    refine ⟨hyσ b (hB₁B hb1), ⟨fun a x => ?_, hPinj, dc, sp, Hm, h1, h2, fun x x' => by rw [h3, hEF]⟩,
      hex, hker, fun a z => ?_, hweil', fun a => ?_⟩
    · simp only [hP']
      exact (hh b hb).2 a x
    · haveI := F.hom a
      have := hL1 a b hb1 ((h b)⁻¹ *ᵥ z)
      rw [← hclaim, hinv' b hb] at this
      exact this
    · beta_reduce
      rw [hsm]
      exact heC a b hbC
  refine ⟨B₂, P', fun b z => e b ((h b)⁻¹ *ᵥ z), hB₂, hb₂, hB₂C.trans (hC₁.trans hB₁B), ?_,
    ⟨fun b hb => (key b hb).2.1, fun x => ?_⟩, ?_, key⟩
  · ext1 x
    rw [hP', hh₀, Matrix.one_mulVec, hP₀]
  · exact (hmv (M := h) (β := id) hhd ((hPd x).mono hB₂C)).congr fun b _ => hP' b x
  · have hid : ∀ i j, DifferentiableOn ℂ (fun b => (h b)⁻¹ i j) B₂ :=
      GlobalTheory.RiemannRel.differentiableOn_left_inverse h (fun b => (h b)⁻¹) hhd fun b hb =>
        Matrix.nonsing_inv_mul _ (hdet b hb)
    exact GlobalTheory.LocLift.isHolTo_comp (β := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (bz.1, (h bz.1)⁻¹ *ᵥ bz.2)) hol
      (hB₂.prod isOpen_univ) (differentiableOn_fst.prodMk (hmv (M := fun b => (h b)⁻¹) (β := Prod.fst)
        (fun i j => (hid i j).comp differentiableOn_fst fun _ hw => hw.1) differentiableOn_snd))
      fun _ hw => ⟨hC₁ (hB₂C hw.1), trivial⟩

end GlobalTheory.PELU
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N c : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N s) (o₁ o₁' : Obj b N s') (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := by
  first | (exact @GlobalTheory.UPel.HT.ESPull.isPIsog_pull) | (exact GlobalTheory.UPel.HT.ESPull.isPIsog_pull) | (intros; apply GlobalTheory.UPel.HT.ESPull.isPIsog_pull  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.formalEndomorphism_pulls_torusCoordinate_normalisedGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))), IsIota u → ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J), Good D.toPre.P.L z J → val ((U.gt e).t α) (x ≫ (b e).left) z J = val ((U.gt e).t (h' α)) x z J * val u (x ≫ (U.gt e).pG.left) z J := by
  first | exact @GlobalTheory.TwFam.coord_of_formalEnd | exact GlobalTheory.TwFam.coord_of_formalEnd | (intros; apply GlobalTheory.TwFam.coord_of_formalEnd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_normalisedTwistedIotaGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ α : D.toPre.X, ∃ u : LB.Gen (IotaLB D.toPre a α (h' α)), IsIota u := by
  first | exact @GlobalTheory.TwFam.exists_iota | exact GlobalTheory.TwFam.exists_iota | (intros; apply GlobalTheory.TwFam.exists_iota <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.normalisedTwistedFactor_value_at_latticePoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ : D.toPre.X), β₁ = β₀ + shift h h' n j ν → ∀ (u₁ : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a ν β₀ β₁) (dε n j))), IsFac D.toPre a h n j ν β₀ β₁ u₁ → ∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val u₁ ((DegPre.zF D.toPre (FractionRing R)).left ≫ (DegPre.trF D.toPre (FractionRing R) mu).left) z J = (val (D.toPre.psi (ν + mu)) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h (ν + mu))) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau (ν + mu) β₀) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)) * (val (D.toPre.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau mu β₁) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j))⁻¹ := by
  first | exact @GlobalTheory.TwFacVal.val_fac_at_point | exact GlobalTheory.TwFacVal.val_fac_at_point | (intros; apply GlobalTheory.TwFacVal.val_fac_at_point <;> assumption)
end
