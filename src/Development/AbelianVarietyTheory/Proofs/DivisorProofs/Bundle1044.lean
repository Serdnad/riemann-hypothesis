module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeRelationOfPullbackIsoThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle955
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle878
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_cocycle_correction_square_zero_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R) (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), PrimI I n₀ n₁ n₂ → ∀ (u : C1 F) (v : C0 F'), (∀ t t' a, IsUnit (u t t' a)) → In2 I F (mdef F u) → (∀ t, IsUnit (v t)) → MulRel I n₀ n₁ n₂ u v → ∃ u' : C1 F, In1 I F (u' - u) ∧ mdef F u' = 0 := by
  first | exact @GlobalTheory.LBLift.cocycle_of_sqZero | exact GlobalTheory.LBLift.cocycle_of_sqZero | (intros; apply GlobalTheory.LBLift.cocycle_of_sqZero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundle_lift_of_strict_cocycle : ∀ (R : Type) [CommRing R] (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsBasis (smallG i L) → IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) → mdef _ u = 0 → ∃ c : Pic X, GlobalTheory.CechPic.pull i c = cls L hL := by
  first | exact @GlobalTheory.LBLift.exists_pic_of_strict_lift | exact GlobalTheory.LBLift.exists_pic_of_strict_lift | (intros; apply GlobalTheory.LBLift.exists_pic_of_strict_lift <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.small_affine_basis_and_transition_units_lift : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀), IsThick I s i → L.IsLB → IsBasis (smallG i L) ∧ (∃ u, IsLift s i L u) ∧ ∀ u, IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) ∧ In2 I _ (mdef _ u) ∧ ∀ u', In1 I _ (u' - u) → IsLift s i L u' := by
  first | exact @GlobalTheory.LBLift.small_basis_lift | exact GlobalTheory.LBLift.small_basis_lift | (intros; apply GlobalTheory.LBLift.small_basis_lift <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isIdealThickeningImmersion_of_isPullback_square_zero_quotient : ∀ (R C : Type) [CommRing R] [CommRing C] (σ : R →+* C) (J : Ideal R), J ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp C) (s₀ : X₀ ⟶ Sp (R ⧸ J)) (i : X₀ ⟶ X), IsPullback i s₀ (s ≫ spMap σ) (spMap (Ideal.Quotient.mk J)) → IsThick (J.map σ) s i := by
  first | exact @GlobalTheory.LBLift.isThick_of_isPullback_quotient | exact GlobalTheory.LBLift.isThick_of_isPullback_quotient | (intros; apply GlobalTheory.LBLift.isThick_of_isPullback_quotient <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.multiplicative_relation_of_pullback_iso_thickening : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ Y Y₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : Y ⟶ Sp R) (i : X₀ ⟶ X) (i' : Y₀ ⟶ Y) (φ₀ φ₁ φ₂ : Y ⟶ X) (w₀ : φ₀ ≫ s = s' ≫ spMap (RingHom.id R)) (w₁ : φ₁ ≫ s = s' ≫ spMap (RingHom.id R)) (w₂ : φ₂ ≫ s = s' ≫ spMap (RingHom.id R)) (ψ₀ ψ₁ ψ₂ : Y₀ ⟶ X₀) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsThick I s' i' → IsBasis (smallG i L) → IsLift s i L u → ψ₀ ≫ i = i' ≫ φ₀ → ψ₁ ≫ i = i' ≫ φ₁ → ψ₂ ≫ i = i' ≫ φ₂ → GlobalTheory.CechPic.pull ψ₀ (cls L hL) = GlobalTheory.CechPic.pull ψ₁ (cls L hL) + GlobalTheory.CechPic.pull ψ₂ (cls L hL) → ∃ (T : Type) (_ : Category.{0} T) (_ : Quiver.IsThin T) (H : T ⥤ AffOp Y) (K₀ K₁ K₂ : T ⥤ (Small i L)ᵒᵖ) (le₀ : ∀ t, (H.obj t).unop.1 ≤ φ₀ ⁻¹ᵁ ((smallG i L).obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ φ₁ ⁻¹ᵁ ((smallG i L).obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ φ₂ ⁻¹ᵁ ((smallG i L).obj (K₂.obj t)).unop.1) (v : C0 (H ⋙ OAff s')), IsBasis H ∧ (∀ t, IsUnit (v t)) ∧ MulRel I (pullMap w₀ _ H K₀ le₀) (pullMap w₁ _ H K₁ le₁) (pullMap w₂ _ H K₂ le₂) u v := by
  first | exact @GlobalTheory.LBLift.IsoRel.mulRel_of_iso | exact GlobalTheory.LBLift.IsoRel.mulRel_of_iso | (intros; apply GlobalTheory.LBLift.IsoRel.mulRel_of_iso <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbDatum

open GlobalTheory.ConjSeq

theorem frobDR_primPull (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (c : primDR B) :
    frobDR p R hR A (primPull (dp0 R) (𝟙 _) f c) = primPull (dp0 R) (𝟙 _) f (frobDR p R hR B c) := by
  have k := (frobMor p R hR B (cast_left p R hR B)).comp (homMor (dp0 R) (𝟙 _) f)
  exact (GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) f) (frobMor p R hR A (cast_left p R hR A)) k (fun _ ↦ rfl)
    (GlobalTheory.VB.frob_naturality p _ f.left _) c).trans
    (GrpMor.pull_pull (frobMor p R hR B (cast_left p R hR B)) (homMor (dp0 R) (𝟙 _) f) k (fun _ ↦ rfl) rfl c).symm

end GlobalTheory.AbDatum
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechDR.FrobKill

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

theorem exists_closed_pow_local : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (X : Scheme.{0}) (s : X ⟶ Sp R) (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX)) (f : Z1 (O (dp0 R) s)), h.pull1 (GlobalTheory.CatCoh.H1.mk _ f) = 0 → ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1, (∀ U, KaehlerDifferential.D R (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧ ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V), (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p = u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) := by
  apply GlobalTheory.CechDR.FrobKill.exists_closed_pow <;> assumption


end GlobalTheory.CechDR.FrobKill

namespace GlobalTheory.ConjSeq

theorem sec_exists_pow_of_D_eq_zero_local : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (U : X.affineOpens) (u : GlobalTheory.CechDR.Sec s U.1), KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.1) u = 0 → ∃ h : GlobalTheory.CechDR.Sec s U.1, h ^ p = u := by
  intro p _ k _ _ hk X _ s _ U u hu
  haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s U.1) := by
    haveI : IsOpenImmersion (GlobalTheory.CechDR.affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
    have h : Smooth (GlobalTheory.CechDR.affPt s U ≫ s) := inferInstance
    rw [GlobalTheory.CechDR.affPt_w] at h
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h)
  by_cases hU : Nonempty U.1
  · haveI : IsDomain (GlobalTheory.CechDR.Sec s U.1) := IsIntegral.component_integral (X := X) U.1
    exact GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero_of_smooth_domain p k hk _ u hu
  · have e : U.1 = ⊥ := by
      ext x
      exact ⟨fun hx ↦ hU ⟨⟨x, hx⟩⟩, fun hx ↦ hx.elim⟩
    have hs : Subsingleton Γ(X, U.1) := by rw [e]; infer_instance
    haveI : Subsingleton (GlobalTheory.CechDR.Sec s U.1) := hs
    exact ⟨u, Subsingleton.elim _ _⟩


theorem eq_sub_of_pow_eq_sub (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsReduced B]
    (hB : (p : B) = 0) {c x y : B} (h : c ^ p = x ^ p - y ^ p) : c = x - y := by
  have e : (c - (x - y)) ^ p = 0 := by
    rw [← frobR_apply p B hB, map_sub, map_sub, frobR_apply, frobR_apply, frobR_apply, h, sub_self]
  exact sub_eq_zero.1 (IsReduced.eq_zero _ ⟨p, e⟩)

theorem mem_hodgeFiltrationOne_of_absoluteFrobenius_pull_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 k) s (dp0 k) s (frobR p k hk) (GlobalTheory.VB.frob X p hX)) (c : FirstDeRham s), h.pull1 c = 0 → c ∈ F1 s := by
  intro p _ k _ _ hk X _ s _ hX h c hc
  obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ c
  have hex : ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1,
      (∀ U, KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧
      ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V),
        (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p =
          u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) :=
    GlobalTheory.CechDR.FrobKill.exists_closed_pow_local p k hk X s hX h f hc
  obtain ⟨u, hu, hf⟩ := hex
  choose w hw using fun U : GlobalTheory.CechDR.AffOp X ↦ sec_exists_pow_of_D_eq_zero_local p k hk X s U.unop (u U) (hu U)
  refine LinearMap.mem_ker.2 (GlobalTheory.CechDR.cmpO_injective k X s ?_)
  rw [map_zero, ← GlobalTheory.CechDR.structureSheaf_comparison_comm, GlobalTheory.CechDR.comparison_mk]
  refine GlobalTheory.CatCoh.H1.mk_eq_zero.2 ⟨w, funext fun U ↦ funext fun V ↦ funext fun a ↦ ?_⟩
  have : IsReduced (GlobalTheory.CechDR.Sec s V.unop.1) :=
    inferInstanceAs (_root_.IsReduced Γ(X, V.unop.1))
  have hp : (p : GlobalTheory.CechDR.Sec s V.unop.1) = 0 := by
    rw [← map_natCast (algebraMap k (GlobalTheory.CechDR.Sec s V.unop.1)), hk, map_zero]
  have e := hf U V a
  rw [← hw V, ← hw U, map_pow] at e
  exact (eq_sub_of_pow_eq_sub p hp e).symm

end GlobalTheory.ConjSeq
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CosocleOfContra

open ProjLine

section General

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V}

theorem isIrreducible_quot {S : Subrepresentation π} (hS : IsCoatom S) : (quot S).IsIrreducible := by
  have h1 : S.toSubmodule ≠ ⊤ := fun e => hS.1 (Subrepresentation.toSubmodule_injective e)
  have := Submodule.Quotient.nontrivial_iff.2 h1
  have : Nontrivial (Subrepresentation (quot S)) := ⟨⊥, ⊤, fun e =>
    bot_ne_top (α := Submodule ℂ (V ⧸ S.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation π := ⟨T.toSubmodule.comap S.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  have hle : S ≤ T' := fun v hv => by
    show S.toSubmodule.mkQ v ∈ T.toSubmodule
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hv]
    exact T.toSubmodule.zero_mem
  rcases hS.le_iff.1 hle with e | e
  · right
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    have : v ∈ T' := e ▸ trivial
    exact this
  · left
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    have : v ∈ T' := hy
    rw [e] at this
    exact (Submodule.Quotient.mk_eq_zero _).2 this

end General

section GeneralLinearIntegers

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}

theorem isSmooth_quot (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth (quot S) :=
  (IsSubquotient.of_surjective (quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ

end GeneralLinearIntegers

end GlobalTheory.CosocleOfContra
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SmallGlue

theorem exists_units_of_pull_eq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (q : Y ⟶ X)
    (h : GlobalTheory.CechPic.pull q (cls L hL) = 0) :
    ∃ a : ∀ j, Γ(Y, q ⁻¹ᵁ L.U j)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i j : L.ι),
      q (f z) ∈ L.U i → q (f z) ∈ L.U j →
      gm f z (q ⁻¹ᵁ L.U i) (a i) = gm (f ≫ q) z (L.U i ⊓ L.U j) (L.g i j) * gm f z (q ⁻¹ᵁ L.U j) (a j) := by
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hL q)).1 h
  have le : ∀ j, q ⁻¹ᵁ L.U j ≤ (L.pull q).U (fun _ => j) := fun j y hy => mem_pull.2 hy
  refine ⟨fun j => res (le j) (t.s (fun _ => j)), fun Z f z i j hi hj => ?_⟩
  have hm : f z ∈ (L.pull q).U (fun _ => i) ⊓ (L.pull q).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
  have := congrArg (gm f z _) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, gm_res _ z _ hm, gm_res _ z _ hm] at this
  rw [gm_res f z (le i) hi, gm_res f z (le j) hj]
  exact this.trans (congrArg (· * _) (gm_pull_g L q f z (fun _ => i) (fun _ => j) hm.1 hm.2))

theorem pullU_isGen_of_germ {X Y : Scheme.{0}} {L : LB X} (q : Y ⟶ X) (d : ∀ j, Γ(X, L.U j)ˣ) (i j : L.ι)
    (h : ∀ y : Y, q y ∈ L.U i → q y ∈ L.U j →
      gm (𝟙 Y) y (q ⁻¹ᵁ L.U i) (pullU q _ (d i)) =
        gm (𝟙 Y ≫ q) y (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Y) y (q ⁻¹ᵁ L.U j) (pullU q _ (d j))) :
    pullU q (L.U i ⊓ L.U j) (res inf_le_left (d i)) =
      pullU q (L.U i ⊓ L.U j) (L.g i j * res inf_le_right (d j)) := by
  refine unit_ext fun y hy => ?_
  have hm : q ((𝟙 Y : Y ⟶ Y) y) ∈ L.U i ⊓ L.U j := hy
  have e := h y hm.1 hm.2
  rw [gm_pull (𝟙 Y) q y _ hm.1, gm_pull (𝟙 Y) q y _ hm.2] at e
  rw [gm_pull (𝟙 Y) q y _ hm, gm_pull (𝟙 Y) q y _ hm, map_mul, gm_res (𝟙 Y ≫ q) y _ hm,
    gm_res (𝟙 Y ≫ q) y _ hm]
  exact e

theorem cech_patching : ∀ {X X₁ X₂ X₀ : Scheme.{0}} (ι₁ : X₁ ⟶ X) (ι₂ : X₂ ⟶ X) (ρ₁ : X₀ ⟶ X₁) (ρ₂ : X₀ ⟶ X₂), ρ₁ ≫ ι₁ = ρ₂ ≫ ι₂ →
    (∀ u : Γ(X₀, ⊤)ˣ, ∃ v : Γ(X₁, ⊤)ˣ, ∀ x : X₀, gm ρ₁ x ⊤ v = gm (𝟙 X₀) x ⊤ u) →
    (∀ (U : X.Opens) (a₁ : Γ(X₁, ι₁ ⁻¹ᵁ U)ˣ) (a₂ : Γ(X₂, ι₂ ⁻¹ᵁ U)ˣ),
      (∀ x : X₀, ρ₁ x ∈ ι₁ ⁻¹ᵁ U → gm ρ₁ x (ι₁ ⁻¹ᵁ U) a₁ = gm ρ₂ x (ι₂ ⁻¹ᵁ U) a₂) →
      ∃ d : Γ(X, U)ˣ, pullU ι₁ U d = a₁ ∧ pullU ι₂ U d = a₂) →
    (∀ (U : X.Opens) (d d' : Γ(X, U)ˣ), pullU ι₁ U d = pullU ι₁ U d' → pullU ι₂ U d = pullU ι₂ U d' → d = d') →
    ∀ c : Pic X, GlobalTheory.CechPic.pull ι₁ c = 0 → GlobalTheory.CechPic.pull ι₂ c = 0 → c = 0 := by
  intro X X₁ X₂ X₀ ι₁ ι₂ ρ₁ ρ₂ hsq hlift hpatch huniq c h₁ h₂
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨α, hα⟩ := exists_units_of_pull_eq_zero hL ι₁ h₁
  obtain ⟨β, hβ⟩ := exists_units_of_pull_eq_zero hL ι₂ h₂
  have pt : ∀ x : X₀, ι₂ (ρ₂ x) = ι₁ (ρ₁ x) := fun x => congrArg (fun g => g x) hsq.symm
  have le : ∀ j, ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j) ≤ ρ₂ ⁻¹ᵁ (ι₂ ⁻¹ᵁ L.U j) := fun j x hx => by
    show ι₂ (ρ₂ x) ∈ L.U j
    rw [pt]; exact hx
  have hu : ∀ j (x : X₀), ι₁ (ρ₁ x) ∈ L.U j →
      gm (𝟙 X₀) x (ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j)) (pullU ρ₁ _ (α j) * (res (le j) (pullU ρ₂ _ (β j)))⁻¹) =
        gm ρ₁ x _ (α j) * (gm ρ₂ x _ (β j))⁻¹ := fun j x hx => by
    rw [map_mul, map_inv, gm_res (𝟙 X₀) x (le j) hx, gm_pull (𝟙 X₀) ρ₁ x _ hx,
      gm_pull (𝟙 X₀) ρ₂ x _ (le j hx), Category.id_comp, Category.id_comp]
  obtain ⟨w, hw⟩ := glue_unit (⊤ : X₀.Opens) (fun j => ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j)) (fun _ => le_top)
    (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (ι₁ (ρ₁ x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩)
    (fun j => pullU ρ₁ _ (α j) * (res (le j) (pullU ρ₂ _ (β j)))⁻¹)
    (fun i j x hx => by
      refine (hu i x hx.1).trans (Eq.trans ?_ (hu j x hx.2).symm)
      rw [hα _ ρ₁ x i j hx.1 hx.2, hβ _ ρ₂ x i j (le i hx.1) (le j hx.2), hsq, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  obtain ⟨v, hv⟩ := hlift w
  have hd : ∀ j, ∃ d : Γ(X, L.U j)ˣ, pullU ι₁ _ d = α j * (res le_top v)⁻¹ ∧ pullU ι₂ _ d = β j := fun j =>
    hpatch _ _ _ fun x hx => by
      have e : gm (𝟙 X₀) x ⊤ w = gm ρ₁ x _ (α j) * (gm ρ₂ x _ (β j))⁻¹ :=
        (gm_res (𝟙 X₀) x (le_top : ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j) ≤ ⊤) hx w).symm.trans
          ((congrArg _ (hw j)).trans (hu j x hx))
      rw [map_mul, map_inv, gm_res ρ₁ x _ hx, hv, e, mul_inv, inv_inv, mul_inv_cancel_left]
  choose d hd₁ hd₂ using hd
  refine (cls_eq_zero_iff hL).2 ⟨⟨d⟩, fun i j => huniq _ _ _ ?_ ?_⟩
  · refine pullU_isGen_of_germ ι₁ d i j fun y hi hj => ?_
    rw [hd₁, hd₁, map_mul, map_mul, map_inv, map_inv, gm_res (𝟙 X₁) y _ hi, gm_res (𝟙 X₁) y _ hj,
      hα _ (𝟙 X₁) y i j hi hj, _root_.mul_assoc]
  · refine pullU_isGen_of_germ ι₂ d i j fun y hi hj => ?_
    rw [hd₂, hd₂]
    exact hβ _ (𝟙 X₂) y i j hi hj

end GlobalTheory.SmallGlue
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PicDisj

open TopologicalSpace

theorem map_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) = gm f y U a := by
  refine Units.ext ?_
  rw [gm, gm, dite_eq_left h, dite_eq_left (show (𝟙 X : X ⟶ X) (f y) ∈ U from h)]
  exact Scheme.Hom.germ_stalkMap_apply f U y h a.val

theorem gm_image {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) (V : Y.Opens) (h : y ∈ V) (a : Γ(Y, V)ˣ) :
    gm f y (f ''ᵁ V) (Units.map (f.appIso V).inv.hom.toMonoidHom a) = gm (𝟙 Y) y V a := by
  refine Units.ext ?_
  have h' : f y ∈ f ''ᵁ V := ⟨y, h, rfl⟩
  rw [gm, gm, dite_eq_left h', dite_eq_left (show (𝟙 Y : Y ⟶ Y) y ∈ V from h)]
  change (Y.presheaf.germ (f ⁻¹ᵁ (f ''ᵁ V)) y h').hom (((f.appIso V).inv ≫ f.app (f ''ᵁ V)).hom a.val) =
    (Y.presheaf.germ V y h).hom a.val
  rw [Scheme.Hom.appIso_inv_app]
  exact Y.presheaf.germ_res_apply _ y _ _

theorem exists_gen_of_rel {Y : Scheme.{0}} {N : LB Y} (hN : N.IsLB) (P : N.ι → ∀ y : Y, (Y.presheaf.stalk y)ˣ → Prop)
    (loc : ∀ p, ∀ y ∈ N.U p, ∃ W : Y.Opens, W ≤ N.U p ∧ y ∈ W ∧ ∃ s : Γ(Y, W)ˣ, ∀ y' ∈ W, P p y' (gm (𝟙 Y) y' W s))
    (cmp : ∀ p q y u u', y ∈ N.U p → y ∈ N.U q → P p y u → P q y u' → u = gm (𝟙 Y) y _ (N.g p q) * u') :
    ∃ t : N.Gen, t.IsGen := by
  have uniq : ∀ p y u u', y ∈ N.U p → P p y u → P p y u' → u = u' := fun p y u u' hy h h' => by
    have e := gm_cocycle hN (𝟙 Y) y hy hy hy
    rw [cmp p p y u u' hy hy h h', mul_eq_left.1 e, _root_.one_mul]
  have key : ∀ p, ∃ a : Γ(Y, N.U p)ˣ, ∀ y ∈ N.U p, P p y (gm (𝟙 Y) y _ a) := fun p => by
    choose W hW hy s hs using fun y : (N.U p : Set Y) => loc p y.1 y.2
    have cp : ∀ k l, res (inf_le_left : W k ⊓ W l ≤ W k) (s k) = res inf_le_right (s l) := fun k l =>
      unit_ext fun y h => by
        rw [gm_res _ y _ h, gm_res _ y _ h]
        exact uniq p y _ _ (hW k h.1) (hs k y h.1) (hs l y h.2)
    have hc : N.U p ≤ iSup W := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy _⟩
    obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' W (N.U p) (fun k => homOfLE (hW k)) hc (fun k => (s k).val)
      fun k l => congrArg Units.val (cp k l)
    have hu : IsUnit (M := Γ(Y, N.U p)) b := Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
      have := (s ⟨x, hx⟩).isUnit.map (Y.presheaf.germ _ x (hy ⟨x, hx⟩)).hom
      rw [← hb] at this
      exact (Y.presheaf.germ_res_apply (homOfLE (hW ⟨x, hx⟩)) x (hy ⟨x, hx⟩) b) ▸ this
    refine ⟨hu.unit, fun y h => ?_⟩
    have e : res (hW ⟨y, h⟩) hu.unit = s ⟨y, h⟩ := Units.ext (hb _)
    rw [← gm_res _ y (hW ⟨y, h⟩) (hy ⟨y, h⟩), e]
    exact hs _ y (hy _)
  choose a ha using key
  exact ⟨⟨a⟩, (isGen_iff_germ _).2 fun y i j hi hj => cmp i j y _ _ hi hj (ha i y hi) (ha j y hj)⟩

theorem eq_zero_of_pull_eq_zero : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ d : Pic Y, (∀ i, GlobalTheory.CechPic.pull (f i) d = 0) → d = 0 := by
  intro Y κ _ Z f _ hcov hdis d hd
  obtain ⟨L, hL, rfl⟩ := cls_surj d
  choose t ht using fun i => (cls_eq_zero_iff (pull_isLB hL (f i))).1 (hd i)
  have surj : ∀ y : Y, ∃ i z, f i z = y := fun y => by
    have : y ∈ ⨆ i, (f i).opensRange := by rw [hcov]; trivial
    obtain ⟨i, z, hz⟩ := Opens.mem_iSup.1 this
    exact ⟨i, z, hz⟩
  refine (cls_eq_zero_iff hL).2 (exists_gen_of_rel hL (fun p y u => ∀ i (z : Z i) (u' : (Y.presheaf.stalk (f i z))ˣ),
    f i z = y → HEq u' u → Units.map ((f i).stalkMap z).hom.toMonoidHom u' =
      gm (𝟙 _) z ((L.pull (f i)).U fun _ => p) ((t i).s fun _ => p)) ?_ ?_)
  · intro p y hy
    obtain ⟨i, z, rfl⟩ := surj y
    refine ⟨f i ''ᵁ ((L.pull (f i)).U fun _ => p), ?_, ⟨z, mem_pull.2 hy, rfl⟩,
      Units.map ((f i).appIso _).inv.hom.toMonoidHom ((t i).s fun _ => p), ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact mem_pull.1 hw
    · rintro y' ⟨w, hw, hy'⟩ j z' u' rfl hu
      obtain rfl : i = j := by
        by_contra hne
        have hm : f j z' ∈ (f i).opensRange ⊓ (f j).opensRange := ⟨⟨w, hy'⟩, ⟨z', rfl⟩⟩
        rw [(hdis hne).eq_bot] at hm
        exact hm
      obtain rfl : w = z' := (f i).isOpenEmbedding.injective hy'
      rw [eq_of_heq hu, map_gm (f i) w _ (show f i w ∈ f i ''ᵁ ((L.pull (f i)).U fun _ => p) from ⟨w, hw, rfl⟩), gm_image _ _ _ hw]
  · intro p q y u u' hp hq h h'
    obtain ⟨i, z, rfl⟩ := surj y
    apply Units.map_injective (f := ((f i).stalkMap z).hom.toMonoidHom)
      (ConcreteCategory.bijective_of_isIso ((f i).stalkMap z)).1
    rw [map_mul, h i z u rfl HEq.rfl, h' i z u' rfl HEq.rfl, map_gm (f i) z (L.U p ⊓ L.U q) ⟨hp, hq⟩,
      (isGen_iff_germ _).1 (ht i) z (fun _ => p) (fun _ => q) (mem_pull.2 hp) (mem_pull.2 hq),
      gm_pull_g L (f i) (𝟙 _) z _ _ (mem_pull.2 hp) (mem_pull.2 hq), Category.id_comp]

end GlobalTheory.PicDisj
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechPicard_eq_zero_of_twoOpen_cover_units_split : ∀ (Z : Scheme.{0}) (O O' : Z.Opens), O ⊔ O' = ⊤ → (∀ F : Γ(Z, O ⊓ O')ˣ, ∃ (u : Γ(Z, O)ˣ) (u' : Γ(Z, O')ˣ), F = res (inf_le_left : O ⊓ O' ≤ O) u * res (inf_le_right : O ⊓ O' ≤ O') u') → ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull O'.ι c = 0 → c = 0 := by
  first | exact @GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split | exact GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split | (intros; apply GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_cechPicard_glue_finite_disjoint_cover : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ c : ∀ i, Pic (Z i), ∃ d : Pic Y, ∀ i, GlobalTheory.CechPic.pull (f i) d = c i := by
  first | exact @GlobalTheory.CechPic.Glue.exists_pic_glue | exact GlobalTheory.CechPic.Glue.exists_pic_glue | (intros; apply GlobalTheory.CechPic.Glue.exists_pic_glue <;> assumption)
end
