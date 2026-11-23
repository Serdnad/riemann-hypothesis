module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle122
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle138
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

theorem _root_.GlobalTheory.T.exists_product_iso_of_fibre_iso_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ → ∃ (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) (w : BunIso φ), HomF φ ∧ w.IsGen ∧ ∀ (a : TF (R := R) F ⟶ D.P.A) (a' : TF (R := R) F ⟶ D'.P.A), (∀ x : baseOver (Sp F) ⟶ Q.A, a.left = x.left ≫ Φ → a'.left = (x ≫ σ.hom).left ≫ Φ') → lift (𝟙 _) a ≫ φ.hom = lift (𝟙 _) a' := by
  first | exact @GlobalTheory.Ex.AbPartIso.exists_iso_of_isFib | exact GlobalTheory.Ex.AbPartIso.exists_iso_of_isFib | (intros; apply GlobalTheory.Ex.AbPartIso.exists_iso_of_isFib <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.exists_expansionTerm_unit_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → FibNZ (𝟙_ _ ⊗ G).hom σ → ∃ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (α : D.X), Good D.P.L z J ∧ T.hom z = IsLocalRing.closedPoint R ∧ (∀ b ∈ I, Geo.Tor.cst T.hom z b = 0) ∧ IsUnit (sval (f α) (lift (toUnit T) y).left z J) := by
  first | exact @GlobalTheory.PsiRing.exists_unit_term | exact GlobalTheory.PsiRing.exists_unit_term | (intros; apply GlobalTheory.PsiRing.exists_unit_term <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.exists_twistedSection_thetaTranslate_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th : SecBT D (𝟙_ _) 1 0), (∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b) → ∀ (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ g : SecBT D (𝟙_ _) 1 χ, ∃ b : R, Coef D χ u th g b := by
  first | exact @GlobalTheory.PsiCoef.exists_coef | exact GlobalTheory.PsiCoef.exists_coef | (intros; apply GlobalTheory.PsiCoef.exists_coef <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.exists_isPullDeg_of_comparison : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D.TauBimult → ∃ hD : IsPullDeg φ D D', hD.e.hom.left ≫ pullback.fst _ _ = β ∧ HEq hD.w v ∧ hD.xe = xe := by
  first | exact @GlobalTheory.PsiRing.exists_isPullDeg_of_cmp | exact GlobalTheory.PsiRing.exists_isPullDeg_of_cmp | (intros; apply GlobalTheory.PsiRing.exists_isPullDeg_of_cmp <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.expansionCoef_mem_adic_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), U.ExpT (𝟙_ _) 1 σ f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ e : ℕ, ∃ s : Finset D.X, ∀ χ ∉ s, ∀ (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (b : R), Coef D χ u th (f χ) b → b ∈ I ^ (e + 1) := by
  first | exact @GlobalTheory.PsiRing.coef_mem_pow | exact GlobalTheory.PsiRing.coef_mem_pow | (intros; apply GlobalTheory.PsiRing.coef_mem_pow <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.psiScalar_eq_expansionCoef_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), PsiScal D ga a → PsiRel D (𝟙_ _) f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ (χ : D.X) (q p : R), Mult D th (f 0) q → Coef D χ (ga χ) th (f χ) p → algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p := by
  first | exact @GlobalTheory.psiScal_eq_ratio | exact GlobalTheory.psiScal_eq_ratio | (intros; apply GlobalTheory.psiScal_eq_ratio <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → ∀ (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), PsiScal D ga a → ∀ (x : D'.X) (J' : Ideal V), D'.PsiIn x J' → ∀ p q : R, algebraMap R (FractionRing R) q * (a (xe x)).val = algebraMap R (FractionRing R) p → ∃ m ∈ J', φ p = φ q * m := by
  first | exact @GlobalTheory.PsiRing.scalar_mem_of_psiIn | exact GlobalTheory.PsiRing.scalar_mem_of_psiIn | (intros; apply GlobalTheory.PsiRing.scalar_mem_of_psiIn <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.psiEven_descend_baseChange : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.PsiEven → D.PsiEven := by
  first | exact @GlobalTheory.PsiRing.psiEven_descend | exact GlobalTheory.PsiRing.psiEven_descend | (intros; apply GlobalTheory.PsiRing.psiEven_descend <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.tauBimult_of_baseChange' : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.TauBimult → D.TauBimult := by
  first | exact @GlobalTheory.tauBimult_of_baseChange | exact GlobalTheory.tauBimult_of_baseChange | (intros; apply GlobalTheory.tauBimult_of_baseChange <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.TorsionField

open GlobalTheory.Ex.UnifModel

theorem exists_descend_algClosed (hM : MulNSt) {K F C : Type} [Field K] [Field F] [IsAlgClosed F] [Field C]
    [IsAlgClosed C] [CharZero C] (P : PolAV (Sp K)) (a : K →+* F) (i : F →+* C) (c : K →+* C)
    (h : ∀ x, i (a x) = c x) {n : ℕ} (hn : 1 ≤ n) (x : Over.mk (spMap c) ⟶ P.A) (hx : x ^ n = 1) :
    ∃ y : Over.mk (spMap a) ⟶ P.A, y ^ n = 1 ∧ spMap i ≫ y.left = x.left := by
  have hC : (n : C) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hF : (n : F) ≠ 0 := fun e => hC (by rw [← map_natCast i, e, map_zero])
  have c₁ := (hM _ P n hn).2.2.2.2 C (spMap c) hC
  have c₂ := (hM _ P n hn).2.2.2.2 F (spMap a) hF
  have := Nat.finite_of_card_ne_zero (c₁ ▸ pow_ne_zero _ (by omega) : _ ≠ 0)
  let u : Over.mk (spMap c) ⟶ Over.mk (spMap a) := Over.homMk (spMap i) (spMap_comp h)
  let Φ : {y : Over.mk (spMap a) ⟶ P.A // y ^ n = 1} → {y : Over.mk (spMap c) ⟶ P.A // y ^ n = 1} :=
    fun y => ⟨u ≫ y.1, by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]⟩
  have := epi_spMap i
  have hΦ : Function.Injective Φ := fun y y' e =>
    Subtype.ext (Over.OverMorphism.ext ((cancel_epi (spMap i)).1 congr(($e).1.left)))
  obtain ⟨y, hy⟩ := (hΦ.bijective_of_nat_card_le (c₁.trans c₂.symm).le).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congr(($hy).1.left)⟩

theorem exists_finset (hM : MulNSt) {K F : Type} [Field K] [Field F] [IsAlgClosed F] [CharZero F] [Algebra K F]
    [Algebra.IsAlgebraic K F] (P : PolAV (Sp K)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset F, ∀ (k : Type) [Field k] (β : k →+* F), (∀ c, algebraMap K F c ∈ β.fieldRange) →
      (∀ c ∈ s, c ∈ β.fieldRange) → ∀ x : Over.mk (spMap (algebraMap K F)) ⟶ P.A, x ^ n = 1 →
        ∃ y : Sp k ⟶ P.A.left, spMap β ≫ y = x.left := by
  classical
  have c₂ := (hM _ P n hn).2.2.2.2 F (spMap (algebraMap K F)) (Nat.cast_ne_zero.2 (by omega))
  have := Nat.finite_of_card_ne_zero (c₂ ▸ pow_ne_zero _ (by omega) : _ ≠ 0)
  have := Fintype.ofFinite {y : Over.mk (spMap (algebraMap K F)) ⟶ P.A // y ^ n = 1}
  have hpr := P.isAb.proper
  have key : ∀ x : {y : Over.mk (spMap (algebraMap K F)) ⟶ P.A // y ^ n = 1}, ∃ s : Finset F,
      ∀ (k : Type) [Field k] (β : k →+* F), (∀ c, algebraMap K F c ∈ β.fieldRange) →
        (∀ c ∈ s, c ∈ β.fieldRange) → ∃ y : Sp k ⟶ P.A.left, spMap β ≫ y = x.1.left := by
    intro x
    obtain ⟨E, -, h2, h3⟩ := GlobalTheory.SS.exists_fieldOfValues P.A.left F x.1.left
    obtain ⟨L, hL, rfl⟩ := h3 K P.A.hom inferInstance (Over.w x.1) inferInstance
    obtain ⟨s, hs⟩ := (Submodule.fg_top L.toSubalgebra.toSubmodule).1 hL.fg_top
    refine ⟨s, fun k _ β h₁ h₂ => (h2 k β).1 fun c hc => ?_⟩
    have hc' : c ∈ Submodule.span K (s : Set F) := hs ▸ hc
    clear hc
    induction hc' using Submodule.span_induction with
    | mem c hc => exact h₂ c hc
    | zero => exact zero_mem _
    | add _ _ _ _ ha hb => exact add_mem ha hb
    | smul r c _ hc => rw [Algebra.smul_def]; exact mul_mem (h₁ r) hc
  choose s hs using key
  exact ⟨Finset.univ.biUnion s, fun k _ β h₁ h₂ x hx => hs ⟨x, hx⟩ k β h₁ fun c hc =>
    h₂ c (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hc⟩)⟩

theorem exists_finset_ratTors (hL : Laws) {K F C : Type} [Field K] [Field F] [IsAlgClosed F] [Algebra K F]
    [Algebra.IsAlgebraic K F] [Field C] [IsAlgClosed C] [CharZero C] (i : F →+* C) {S : Scheme.{0}} (t : Sp K ⟶ S)
    (B₁ : PolAV S) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset F, ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) C] (β : FractionRing R →+* F),
      (∀ c, i (β c) = algebraMap _ C c) → (∀ c, algebraMap K F c ∈ β.fieldRange) → (∀ c ∈ s, c ∈ β.fieldRange) →
      ∀ r : Sp R ⟶ S, spMap β ≫ jK R ≫ r = spMap (algebraMap K F) ≫ t →
      ∀ (B : PolAV (Sp R)) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A r ψ → RatTors B C n := by
  have : CharZero F := i.charZero
  obtain ⟨P, φ, hφ₀, -, hm, -⟩ := hL.polBaseChange S (Sp K) t B₁
  have hφ : IsGrpPullback P.A B₁.A t φ := ⟨hφ₀, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ₀.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ₀.w y), ← hm]
    rfl⟩
  obtain ⟨s, hs⟩ := exists_finset (F := F) hL.mulN P hn
  refine ⟨s, fun R _ _ _ β hβ h₁ h₂ r hr B ψ hψ x hx => ?_⟩
  have e₁ : spMap i ≫ spMap β = jFK (R := R) C := spMap_comp hβ
  have e₂ : spMap i ≫ spMap (algebraMap K F) = spMap (i.comp (algebraMap K F)) := spMap_comp fun _ => rfl
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hψ (jFK (R := R) C ≫ jK R) _ rfl
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isGrpPullback hφ (spMap (i.comp (algebraMap K F)))
    ((jFK (R := R) C ≫ jK R) ≫ r) (by rw [← e₁, ← e₂, Category.assoc, Category.assoc, hr, Category.assoc])
  obtain ⟨y, hy, hy'⟩ := exists_descend_algClosed hL.mulN P (algebraMap K F) i _ (fun _ => rfl) hn
    (e'.symm (e x)) (by rw [← map_pow, ← map_pow, hx, map_one, map_one])
  obtain ⟨z, hz⟩ := hs _ β h₁ h₂ y hy
  have := epi_spMap β
  have w : (z ≫ φ) ≫ B₁.A.hom = jK R ≫ r := by
    rw [← cancel_epi (spMap β), hr, Category.assoc, hφ₀.w, reassoc_of% hz]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) (Over.w y))
  refine ⟨Over.homMk (hψ.1.lift _ _ w) (hψ.1.lift_snd _ _ _), hψ.1.hom_ext ?_ ?_⟩
  · refine (he x).symm.trans ?_
    rw [← e'.apply_symm_apply (e x), he', ← hy', ← hz, ← e₁]
    simp only [Category.assoc]
    exact congrArg (fun q => spMap i ≫ spMap β ≫ q) (hψ.1.lift_fst _ _ w).symm
  · refine (Over.w x).trans ?_
    exact (congrArg (fun q => jFK (R := R) C ≫ q) (hψ.1.lift_snd _ _ w).symm).trans (Category.assoc _ _ _).symm

theorem exists_cDvr_ratTors : Laws → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing W) C], CExt W (IsLocalRing.maximalIdeal W) C → ∀ n : ℕ, 1 ≤ n → ∀ (S₁ S₂ : Scheme.{0}) (s₁ : Sp W ⟶ S₁) (s₂ : Sp W ⟶ S₂) (B₁ : PolAV S₁) (B₂ : PolAV S₂), ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (_ : Algebra (FractionRing W') C) (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ Along io C ∧ CExt W' (IsLocalRing.maximalIdeal W') C ∧ (∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A (spMap io ≫ s₁) ψ → RatTors B C n) ∧ ∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₂.A.left), IsGrpPullback B.A B₂.A (spMap io ≫ s₂) ψ → RatTors B C n := by
  intro hL W _ _ _ ⟨d, hc, h0⟩ C _ _ _ _ hext n hn S₁ S₂ s₁ s₂ B₁ B₂
  classical
  let F := algebraicClosure (FractionRing W) C
  have : IsAlgClosed F := (algebraicClosure.isAlgClosure (FractionRing W) C).isAlgClosed
  let : Algebra W F := ((algebraMap (FractionRing W) F).comp (algebraMap W _)).toAlgebra
  have : IsScalarTower W (FractionRing W) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have iW : Function.Injective (algebraMap W F) :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  have : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective W F).2 iW
  have : Algebra.IsAlgebraic W F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := W) (K := FractionRing W) (C := F)).2 inferInstance
  have : CharZero (FractionRing W) := IsFractionRing.charZero_of_isFractionRing W
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap (FractionRing W) C).injective
  obtain ⟨t₁, ht₁⟩ := exists_finset_ratTors hL (algebraMap F C) (jK W ≫ s₁) B₁ hn
  obtain ⟨t₂, ht₂⟩ := exists_finset_ratTors hL (algebraMap F C) (jK W ≫ s₂) B₂ hn
  obtain ⟨V, dV, cV, -, fV, -, lV, hV, -⟩ := exists_complete_dvr_finite_subalgebra W F (t₁ ∪ t₂)
  have i₁ : Function.Injective (algebraMap V F) := Subtype.val_injective
  let β : FractionRing V →+* F := IsFractionRing.lift i₁
  have hβ : ∀ x, β (algebraMap V _ x) = algebraMap V F x := IsFractionRing.lift_algebraMap i₁
  let : Algebra (FractionRing V) C := ((algebraMap F C).comp β).toAlgebra
  have hA : Along (algebraMap W V) C := fun x => congrArg (algebraMap F C) (hβ _)
  have h₁ : ∀ c, algebraMap (FractionRing W) F c ∈ β.fieldRange := fun c => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) c
    rw [map_div₀]
    exact div_mem ⟨_, hβ (algebraMap W V a)⟩ ⟨_, hβ (algebraMap W V b)⟩
  have h₂ : ∀ c ∈ t₁ ∪ t₂, c ∈ β.fieldRange := fun x hx => by
    obtain ⟨u, hu, v, hv, h0, e⟩ := hV x hx
    refine ⟨algebraMap V _ ⟨u, hu⟩ / algebraMap V _ ⟨v, hv⟩, ?_⟩
    rw [map_div₀, hβ, hβ]
    exact (div_eq_iff h0).2 e.symm
  have e : spMap β ≫ jK V ≫ spMap (algebraMap W V) = spMap (algebraMap (FractionRing W) F) ≫ jK W := by
    rw [← Category.assoc, spMap_comp hβ, spMap_comp (d := algebraMap W F) fun _ => rfl]
    exact (spMap_comp fun _ => rfl).symm
  have : CharZero V := (algebraMap V F).charZero
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, algebraMap W V, ⟨dV, cV, inferInstance⟩,
    fun a b h => iW (congrArg Subtype.val h), RingHom.finite_algebraMap.2 fV, lV, hA, cExt_of_integral hext hA,
    ht₁ V β (fun _ => rfl) h₁ (fun c hc => h₂ c (Finset.mem_union_left _ hc)) _ ?_,
    ht₂ V β (fun _ => rfl) h₁ (fun c hc => h₂ c (Finset.mem_union_right _ hc)) _ ?_⟩
  · rw [reassoc_of% e]
  · rw [reassoc_of% e]

end GlobalTheory.Ex.TorsionField
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
noncomputable section
namespace GlobalTheory.Ex.ActPt

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem equiv_parts {k : ℕ} {p p' : QkPt D F k} (h : QkPt.Equiv D F p p') :
    ∃ z : D.X, p'.y = p.y + k • z ∧ p'.g.b = p.g.b * DegPre.cF D F z := by
  obtain ⟨z, h₁, g, h₂, h₃⟩ := h
  exact ⟨z, h₁, by rw [h₃.1, h₂.1]; rfl⟩

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O)

theorem mul_cF_act (x : O) (b : TF (R := R) F ⟶ D.P.A) (z : D.X) :
    (b * DegPre.cF D F z) ≫ oa.onB.act x = (b ≫ oa.onB.act x) * DegPre.cF D F (x • z) := by
  have := oa.onB.hom x
  rw [MonObj.mul_comp, DegPre.cF, DegPre.cF, oa.c_lin, Category.assoc]

theorem act_parts {k : ℕ} {x : O} {p p' : QkPt D F k} (h : QkAct oa x p p') :
    ∃ z : D.X, p'.y = x • p.y + k • z ∧ p'.g.b = (p.g.b ≫ oa.onB.act x) * DegPre.cF D F z := by
  obtain ⟨q, h₁, h₂, h₃⟩ := h
  obtain ⟨z, e₁, e₂⟩ := equiv_parts h₃
  exact ⟨z, by rw [e₁, h₁], by rw [e₂, h₂.1]⟩
end

theorem exists_image {C : Type} [CommRing C] {N N' : NumD C} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  obtain ⟨h₁, h₂, h₃, -⟩ := NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)
  obtain ⟨g, hg, -⟩ := h₁ p.1.2
  have hp : ∀ n : ℕ, (TateInh.homOfIso J).Rel (p.1.2 ^ n) (g ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact J.rel_one
    | succ n ih => rw [pow_succ, pow_succ]; exact h₂ _ _ _ _ ih hg
  have e := hp k
  rw [N.mem_QT.1 p.2] at e
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), (h₁ _).unique e (h₃ _)⟩, rfl, hg⟩

theorem main : GlobalTheory.UT.LL → BrGtSt → AllS fun {E} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → ∀ k : ℕ, 0 < k → Labels A u r M ν' J k → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) → ∀ (x : 𝓞 E) (y y' : A.N.A), y ^ k = 1 → (letI := H.starRing; A.ν.eA y' = A.ν.eA y ≫ a.oa.onB.act x → ν'.eA (J.φ y') = ν'.eA (J.φ y) ≫ M.P.oD.onB.act x) := by
  intro hL hB E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hT k hk hlab hlin x y y' hy hy'
  letI := H.starRing
  obtain ⟨-, -, -, -, B⟩ := hB O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨-, -, -, -, B'⟩ := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨t, t₁, -, t₃, -, t₅, -⟩ := hT C k hk
  have im : ∀ w : D.La, ∃ p' : QkPt M.P.D.toPre C k, (t p').left = (o.I.ev k w).left ≫ M.φ ∧
      p'.y = ν'.eX (J.e (A.q k w).1.1.toAdd) ∧ p'.g.b = ν'.eA (J.φ (A.q k w).1.2.b) := fun w => by
    obtain ⟨p, hp, -⟩ := existsUnique_twRel A.be u (r k) (hr.pow hk) (A.q k w)
    obtain ⟨q, q₁, q₂⟩ := exists_image J p
    obtain ⟨p', hp'⟩ := (B' k).2.1 q
    let z : TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev k w).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)
    have hz := (t₁ _ _).1 (hlab w p q p' z hp q₁ q₂ hp' rfl)
    refine ⟨p', by rw [← hz]; rfl, ?_, ?_⟩
    · rw [← hp'.1, q₁, hp.1]; rfl
    · rw [← hp'.2.1, q₂.1]; exact congrArg (fun s => ν'.eA (J.φ s)) hp.2.1
  obtain ⟨gm, hγ, hγ'⟩ := QStr.root_over A.N hk.ne' 1 y hy
  obtain ⟨p₀, hp₀⟩ := (B k).2.1 ⟨(1, gm), hγ'.trans A.N.io_zero.symm⟩
  obtain ⟨v, hv⟩ := A.I.onto k hk p₀
  obtain ⟨z₀, -, e₀⟩ := equiv_parts hv
  obtain ⟨z₁, d₁, e₁⟩ := act_parts a.oa (A.I.lin k hk x v)
  obtain ⟨p₁, a₁, b₁, c₁⟩ := im v
  obtain ⟨p₂, a₂, b₂, c₂⟩ := im (x • v)
  obtain ⟨p₃, h₃⟩ := qkAct_exists hL.1.globalFns M.P.D.tau_bimult M.P.oD x p₁
  have e₃ : t p₃ = t p₂ := by
    rw [t₅ _ _ _ h₃]
    ext1
    rw [a₂, o.I.lin, Over.comp_left, Over.comp_left, a₁, Category.assoc, Category.assoc, M.act]
  have h₂ : QkAct M.P.oD x p₁ p₂ :=
    (TorusExt.qkAct_iff_of_equiv M.P.D.tau_bimult hL.1.globalFns M.P.oD
      (qk_equiv_refl M.P.D.tau_bimult p₁) h₃).2
      ((t₃ _ _).1 e₃)
  obtain ⟨z₂, d₂, e₂⟩ := act_parts M.P.oD h₂
  obtain ⟨w₀, rfl⟩ := A.ν.eX.surjective z₀
  obtain ⟨w₁, rfl⟩ := A.ν.eX.surjective z₁
  rw [← (A.hq k v).1, ← (A.hq k (x • v)).1] at d₁
  rw [← (A.hq k v).2.1, ← (A.hq k (x • v)).2.1] at e₁
  rw [← (A.hq k v).2.1, ← hp₀.2.1] at e₀
  rw [b₁, b₂] at d₂
  rw [c₁, c₂] at e₂
  generalize (A.q k v).1.1.toAdd = s₁ at d₁ d₂
  generalize (A.q k (x • v)).1.1.toAdd = s₂ at d₁ d₂
  generalize (A.q k v).1.2.b = β₁ at e₀ e₁ e₂
  generalize (A.q k (x • v)).1.2.b = β₂ at e₁ e₂
  let e : A.N.X ≃+ N'.X := J.e
  let φ : A.N.A ≃* N'.A := J.φ
  have hc : ∀ χ, N'.c (e χ) = φ (A.N.c χ) := J.c_eq
  let act : A.N.X → A.N.X := fun s => A.ν.eX.symm (x • A.ν.eX s)
  have hl : ∀ s, ν'.eX (e (act s)) = x • ν'.eX (e s) := hlin x
  have ha : ∀ s, A.ν.eX (act s) = x • A.ν.eX s := fun s => A.ν.eX.apply_symm_apply _
  change ν'.eX (e s₂) = x • ν'.eX (e s₁) + k • z₂ at d₂
  change ν'.eA (φ β₂) = ν'.eA (φ β₁) ≫ _ * _ at e₂
  change ν'.eA (φ y') = ν'.eA (φ y) ≫ _
  have g₁ : s₂ = act s₁ + k • w₁ := A.ν.eX.injective (by rw [d₁, map_add (f := _), map_nsmul, ha])
  have g₂ : z₂ = ν'.eX (e w₁) := by
    rw [g₁, map_add (f := _), map_add (f := _), map_nsmul, map_nsmul, hl, add_right_inj, ← natCast_zsmul, ← natCast_zsmul] at d₂
    exact (smul_right_injective _ (Int.natCast_ne_zero.2 hk.ne') d₂).symm
  have g₀ : y = β₁ * A.N.c w₀ := A.ν.eA.injective (by rw [map_mul, A.ν.c_eq, ← e₀, hγ])
  have g₃ : y' * A.N.c w₁ = β₂ * A.N.c (act w₀) := A.ν.eA.injective (by
    rw [map_mul, map_mul, hy', g₀, map_mul, A.ν.c_eq, A.ν.c_eq, A.ν.c_eq, mul_cF_act, e₁, ha, mul_right_comm])
  have g₄ := congrArg (fun s => ν'.eA (φ s)) g₃
  simp only [map_mul, ← hc, ν'.c_eq, hl, e₂, ← g₂] at g₄
  rw [mul_right_comm, mul_left_inj] at g₄
  rw [g₄, g₀, map_mul, map_mul, ← hc, ν'.c_eq, mul_cF_act]

end GlobalTheory.Ex.ActPt
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

theorem reframe : ThetaUnifAV → ReframeSt := by
  intro hT Q L₀ g u₀ _ _ _
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, ht₁, ht₂, -, -, hEf, -⟩ := hT Q rig hrig
  obtain ⟨F, hF₀, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb L₀ Q.L g Q.g u₀ u ht₁ ht₂
    (𝟙 _) inferInstance
  have hF : ∀ z, u.ex (F z) = u₀.ex z := fun z => (hF₀ z).trans (Category.comp_id _)
  have hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ u₀.Λ := fun z => by rw [← u.ker, hF, u₀.ker]
  have cΛ : (u.Λ : Set (Fin Q.g → ℂ)).Countable := by
    have := u.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u.Λ)
  have cΛ₀ : (u₀.Λ : Set (Fin g → ℂ)).Countable := by
    have := u₀.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u₀.Λ)
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz =>
    FibreUnif.eq_zero_of_smul_mem_countable cΛ₀ fun t =>
      (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)
  have Fsurj : Function.Surjective F := FibreUnif.surjective_of_countable F cΛ fun v => by
    obtain ⟨z, hz⟩ := u₀.ex_onto (u.ex v)
    refine ⟨z, (u.ker _).1 ?_⟩
    have := u.ex_add (v - F z) (F z)
    rw [sub_add_cancel, hF, hz] at this
    exact right_eq_mul.1 this
  exact ⟨u, Hm, χ, Ef, LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩, hAH, hEf, hF⟩

end GlobalTheory.Ex.Arch
end
