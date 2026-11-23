module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle784
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle786
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle785
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicDivisibleDedekindFiniteTypeAlgClosed
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardFilterLowerHeckeRepsEqRelIndexPow

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem closedSubscheme_iInter_exists :
    ∀ (H : Scheme.{0}) (Idx : Type) [Finite Idx] (Z : Idx → Scheme.{0}) (i : ∀ k, Z k ⟶ H),
      (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧
        ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h := by
  intro H Idx _ Z i hi
  revert Z i hi
  refine Finite.induction_empty_option
    (P := fun (α : Type) => ∀ (Z : α → Scheme.{0}) (i : ∀ k, Z k ⟶ H),
      (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧
        ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h)
    ?_ ?_ ?_ Idx
  · intro α β e ih Z i hi
    obtain ⟨Z₀, i₀, h₀, hp⟩ := ih (fun a => Z (e a)) (fun a => i (e a)) (fun a => hi (e a))
    refine ⟨Z₀, i₀, h₀, fun T h => (hp T h).trans ?_⟩
    exact e.forall_congr_right (q := fun k => ∃ z, z ≫ i k = h)
  · intro Z i _
    refine ⟨H, 𝟙 H, inferInstance, fun T h => ⟨fun _ k => k.elim, fun _ => ⟨h, Category.comp_id h⟩⟩⟩
  · intro α _ ih Z i hi
    obtain ⟨Z₀, i₀, h₀, hp⟩ := ih (fun a => Z (some a)) (fun a => i (some a)) (fun a => hi (some a))
    haveI := h₀
    haveI := hi none
    refine ⟨Limits.pullback i₀ (i none), Limits.pullback.fst i₀ (i none) ≫ i₀, inferInstance, ?_⟩
    intro T h
    rw [Option.forall, ← hp T h]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨⟨z ≫ Limits.pullback.snd _ _, ?_⟩, ⟨z ≫ Limits.pullback.fst _ _, ?_⟩⟩
      · rw [Category.assoc, ← Limits.pullback.condition]
      · rfl
    · rintro ⟨⟨z₂, h₂⟩, ⟨z₁, h₁⟩⟩
      exact ⟨Limits.pullback.lift z₁ z₂ (h₁.trans h₂.symm), by rw [Limits.pullback.lift_fst_assoc, h₁]⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem closedSubscheme_inter_exists : ∀ (H Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ H) (i₂ : Z₂ ⟶ H),
    IsClosedImmersion i₁ → IsClosedImmersion i₂ → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H),
      IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H),
        (∃ z, z ≫ i₀ = h) ↔ (∃ z, z ≫ i₁ = h) ∧ ∃ z, z ≫ i₂ = h := by
  intro H Z₁ Z₂ i₁ i₂ h₁ h₂
  refine ⟨pullback i₁ i₂, pullback.snd i₁ i₂ ≫ i₂, inferInstance, ?_⟩
  intro T h
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z ≫ pullback.fst i₁ i₂, ?_⟩, ⟨z ≫ pullback.snd i₁ i₂, ?_⟩⟩
    · rw [Category.assoc, pullback.condition]
    · rw [Category.assoc]
  · rintro ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩
    exact ⟨pullback.lift z₁ z₂ (hz₁.trans hz₂.symm), by rw [← Category.assoc, pullback.lift_snd, hz₂]⟩

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base : ∀ {S S' U U' X Y Y' YU Y'' : Scheme.{0}} (f : S' ⟶ S) (j : U ⟶ S) (f' : U' ⟶ U) (j' : U' ⟶ S') [Flat f] [Surjective f] [QuasiCompact f] [QuasiCompact j] [IsSchemeTheoreticallyDominant j], IsPullback j' f' f j → ∀ (x : X ⟶ S) [IsSeparated x] (y : Y ⟶ S) [Flat y] (y' : Y' ⟶ S') (π : Y' ⟶ Y), IsPullback π y' y f → ∀ (yU : YU ⟶ U) (ιY : YU ⟶ Y), IsPullback ιY yU y j → ∀ (y'' : Y'' ⟶ U') (c : Y'' ⟶ Y') (cU : Y'' ⟶ YU), IsPullback c y'' y' j' → IsPullback cU y'' yU f' → cU ≫ ιY = c ≫ π → ∀ (h' : Y' ⟶ X) (hU : YU ⟶ X), h' ≫ x = y' ≫ f → c ≫ h' = cU ≫ hU → ∃ h : Y ⟶ X, π ≫ h = h' ∧ ιY ≫ h = hU ∧ h ≫ x = y := by
  first | exact @GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant | exact GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant | (intros; apply GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback : ∀ (X S X' S' : Scheme.{0}) (f : X ⟶ S) (f' : X' ⟶ S') (p : S' ⟶ S) (q : X' ⟶ X) (e : S ⟶ X) (e' : S' ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} = {x : X' | x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (e' (f' x))} := by
  first | exact @GlobalTheory.sectionComponents_preimage_of_isPullback | exact GlobalTheory.sectionComponents_preimage_of_isPullback | (intros; apply GlobalTheory.sectionComponents_preimage_of_isPullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_mem_rightTranslate_mem_identityComponent : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), (η[G]).left (IsLocalRing.closedPoint k) ∈ U → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → ∃ z : G.left, z ∈ U ∧ (𝟙 G * (toUnit G ≫ y) : G ⟶ G).left z ∈ U := by
  first | exact @GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent | exact GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent | (intros; apply GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.Serre

theorem isMonHom_of_components : ∀ (T : Scheme.{0}) (A' B' C : Over T) [GrpObj A'] [GrpObj B'] [GrpObj C] (r : ℕ) (pr' : Fin r → (B' ⟶ A')), (∀ u, IsMonHom (pr' u)) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ Φ : C ⟶ B', (∀ u, IsMonHom (Φ ≫ pr' u)) → IsMonHom Φ := by
  intro T A' B' C _ _ _ r pr' hpr huniv Φ hΦ
  have hcomp : ∀ u, IsMonHom (pr' u) := hpr
  have hΦu : ∀ u, IsMonHom (Φ ≫ pr' u) := hΦ
  refine ⟨?_, ?_⟩
  · obtain ⟨x, -, hx⟩ := huniv (𝟙_ (Over T)) (fun u => η[C] ≫ Φ ≫ pr' u)
    have h1 : η[C] ≫ Φ = x := hx _ (fun u => by simp)
    have h2 : (η[B'] : 𝟙_ (Over T) ⟶ B') = x := hx _ (fun u => by
      haveI := hcomp u; haveI := hΦu u
      rw [IsMonHom.one_hom, IsMonHom.one_hom (Φ ≫ pr' u)])
    rw [h1, h2]
  · obtain ⟨x, -, hx⟩ := huniv (C ⊗ C) (fun u => μ[C] ≫ Φ ≫ pr' u)
    have h1 : μ[C] ≫ Φ = x := hx _ (fun u => by simp)
    have h2 : (Φ ⊗ₘ Φ) ≫ μ[B'] = x := hx _ (fun u => by
      haveI := hcomp u; haveI := hΦu u
      rw [Category.assoc, IsMonHom.mul_hom (Φ ≫ pr' u), IsMonHom.mul_hom (pr' u),
        ← Category.assoc, tensorHom_comp_tensorHom])
    rw [h1, h2]

end GlobalTheory.Serre
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_unramified_field_of_inertia_property : ∀ (N : IntermediateField ℚ ℂ) [NumberField N] [IsGalois ℚ N] (q : ℕ), q.Prime → ∀ Good : (ℂ ≃+* ℂ) → Prop, (∀ τ τ', Good τ → Good τ' → Good (τ.trans τ')) → (∀ (τ : ℂ ≃+* ℂ) (𝔮 : Ideal (𝓞 N)), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → Good τ) → ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ F', τ x = x) → Good τ := by
  first | exact @GlobalTheory.InertiaGood.exists_unramified_field_good | exact GlobalTheory.InertiaGood.exists_unramified_field_good | (intros; apply GlobalTheory.InertiaGood.exists_unramified_field_good <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActFin

theorem prod_zpow_transport : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A t φ → ∀ (r : ℕ) (g : Fin r → (A' ⟶ A')) (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ), (∀ k, (g k).left ≫ φ = φ ≫ (f k).left) → (∏ k, g k ^ c k).left ≫ φ = φ ≫ (∏ k, f k ^ c k).left := by
  intro S S' t A _ _ A' _ _ φ h r g f c hc
  let U : Over.mk (A'.hom ≫ t) ⟶ A := pushPt h.1.w (𝟙 A')
  have hk : ∀ k, pushHom h A' (g k) = preHom U (f k) := fun k => by
    ext
    show (g k).left ≫ φ = (𝟙 A' : A' ⟶ A').left ≫ φ ≫ (f k).left
    rw [hc k, Over.id_left, Category.id_comp]
  have e : pushHom h A' (∏ k, g k ^ c k) = preHom U (∏ k, f k ^ c k) := by
    rw [map_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [map_zpow, map_zpow, hk k]
  have e' := congrArg (fun z => z.left) e
  change (∏ k, g k ^ c k).left ≫ φ = ((𝟙 A' : A' ⟶ A').left ≫ φ) ≫ (∏ k, f k ^ c k).left at e'
  rwa [Over.id_left, Category.id_comp] at e'

end GlobalTheory.ActFin
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Pow8

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev G8 : Over S := powObj G 8

abbrev pr8 (i : Fin 8) : G8 G ⟶ G := powPr G i

def mk8 {T : Over S} (x : Fin 8 → (T ⟶ G)) : T ⟶ G8 G := (powIsLimit G 8).lift (Fan.mk T x)

theorem eighthPowerLift_comp_projection {T : Over S} (x : Fin 8 → (T ⟶ G)) (i : Fin 8) : mk8 G x ≫ pr8 G i = x i :=
  (powIsLimit G 8).fac (Fan.mk T x) ⟨i⟩

theorem eighthPowerGroupObj_hom_ext {T : Over S} {x y : T ⟶ G8 G} (h : ∀ i, x ≫ pr8 G i = y ≫ pr8 G i) : x = y :=
  (powIsLimit G 8).hom_ext fun ⟨i⟩ => h i

def matAct (a : Matrix (Fin 8) (Fin 8) ℤ) : G8 G ⟶ G8 G := mk8 G fun i => ∏ j, pr8 G j ^ a i j

theorem matAct_pr (a : Matrix (Fin 8) (Fin 8) ℤ) (i : Fin 8) : matAct G a ≫ pr8 G i = ∏ j, pr8 G j ^ a i j :=
  eighthPowerLift_comp_projection G _ i

theorem matAct_hom (a : Matrix (Fin 8) (Fin 8) ℤ) : IsMonHom (matAct G a) :=
  Serre.isMonHom_of_mul_comp _ fun T x y => eighthPowerGroupObj_hom_ext G fun k => by
    have hc : IsMonHom (∏ j, pr8 G j ^ a k j) :=
      PowQuotient.isMonHom_prod _ fun j => Serre.isMonHom_zpow _ _
    rw [MonObj.mul_comp _ _ (pr8 G k), Category.assoc, Category.assoc, Category.assoc, matAct_pr,
      MonObj.mul_comp _ _ (∏ j, pr8 G j ^ a k j)]

theorem matAct_one : matAct G 1 = 𝟙 (G8 G) := eighthPowerGroupObj_hom_ext G fun i => by
  rw [matAct_pr, Category.id_comp, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Matrix.one_apply_ne' hj]
  · simp

end GlobalTheory.Mum.Pow8
end
end

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isAbelianScheme_of_charts_surjective_image : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) [GrpObj A] [GrpObj G] (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) [∀ j, GrpObj (B j)] (ψ : ∀ j, (B j).left ⟶ G.left),
    IsAbelianScheme A → IsCommMonObj G → Surjective Q.left → (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) →
    (∀ j, IsAbelianScheme (B j)) → IsAbelianScheme G := by
  first | exact @GlobalTheory.QuotAbelian.isAbelianScheme_of_charts_of_surjective | exact GlobalTheory.QuotAbelian.isAbelianScheme_of_charts_of_surjective | (intros; apply GlobalTheory.QuotAbelian.isAbelianScheme_of_charts_of_surjective <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ c : CommRing.Pic B, ∃ d, d ^ q = c := by
  first | (exact @GlobalTheory.PicDiv.pic_divisible) | (exact GlobalTheory.PicDiv.pic_divisible) | (intros; apply GlobalTheory.PicDiv.pic_divisible  <;> assumption)
end

section

open NumberField

namespace GlobalTheory.SumIndex

theorem relIndex_pi_pi_of {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  apply _root_.GlobalTheory.LowerHeckeCount.relIndex_pi_univ <;> assumption

theorem eq_zero_of_sum_eq_zero {ι R V : Type} [Fintype ι] [DecidableEq ι] [Ring R] [AddCommGroup V]
    [Module R V] (S : ι → Submodule R V) (hS : iSupIndep S) (y : ι → V) (hy : ∀ a, y a ∈ S a)
    (h0 : ∑ a, y a = 0) (b : ι) : y b = 0 := by
  have hb : y b = -∑ a ∈ Finset.univ.erase b, y a := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hmem : y b ∈ ⨆ (a) (_ : a ≠ b), S a := by
    rw [hb]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun a ha => ?_)
    exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase ha) (hy a))
  exact (Submodule.disjoint_def.1 (hS b)) _ (hy b) hmem

theorem relIndex_iSup_map_eq_pow : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : ℕ)
  (M : Fin p → (W →ₗ[K] V)) (ℓ N : Submodule (𝓞 K) W), N ≤ ℓ → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
    (N.toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
  intro K _ _ W V _ _ _ _ _ _ _ _ p M ℓ N hNℓ hinj hind
  classical
  let Φ : (Fin p → W) →ₗ[𝓞 K] V := ∑ a, ((M a).restrictScalars (𝓞 K)).comp (LinearMap.proj a)
  have hΦ : ∀ x, Φ x = ∑ a, M a (x a) := by intro x; simp [Φ]
  have himg : ∀ S : Submodule (𝓞 K) W, (Submodule.pi Set.univ (fun _ : Fin p => S)).map Φ =
      ⨆ a, S.map ((M a).restrictScalars (𝓞 K)) := by
    intro S
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hΦ]
      exact Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ⟨x a, hx a (Set.mem_univ a), rfl⟩
    · refine iSup_le fun a => ?_
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨Pi.single a w, ?_, ?_⟩
      · intro b _
        by_cases h : b = a
        · subst h; simpa using hw
        · simp [Pi.single_apply, h]
      · rw [hΦ, Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
        simp
  let Lp : Submodule (𝓞 K) (Fin p → W) := Submodule.pi Set.univ (fun _ => ℓ)
  let Np : Submodule (𝓞 K) (Fin p → W) := Submodule.pi Set.univ (fun _ => N)
  have hNL : Np ≤ Lp := fun x hx a ha => hNℓ (hx a ha)
  let g : Lp.toAddSubgroup →+ V := Φ.toAddMonoidHom.comp Lp.toAddSubgroup.subtype
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun z hz => ?_
    have h0 : ∑ a, M a (z.1 a) = 0 := by rw [← hΦ]; exact hz
    have hy := eq_zero_of_sum_eq_zero _ hind (fun a => M a (z.1 a))
      (fun a => Submodule.subset_span ⟨z.1 a, z.2 a (Set.mem_univ a), rfl⟩) h0
    exact Subtype.ext (funext fun a => by simpa using hinj a (by simpa using hy a))
  have hL' : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup = (⊤ : AddSubgroup Lp.toAddSubgroup).map g := by
    rw [← himg]
    ext v
    simp [g, Lp]
  have hN' : (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
      (Np.toAddSubgroup.addSubgroupOf Lp.toAddSubgroup).map g := by
    rw [← himg]
    ext v
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map,
      AddSubgroup.mem_addSubgroupOf, Subtype.exists]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hNL hx, hx, rfl⟩
    · rintro ⟨x, _, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hL', hN', AddSubgroup.relIndex_map_map_of_injective _ _ hg, AddSubgroup.relIndex_top_right]
  change Np.toAddSubgroup.relIndex Lp.toAddSubgroup = _
  have e1 : Np.toAddSubgroup = AddSubgroup.pi Set.univ (fun _ : Fin p => N.toAddSubgroup) := by
    ext x; simp [Np, AddSubgroup.mem_pi, Submodule.mem_pi]
  have e2 : Lp.toAddSubgroup = AddSubgroup.pi Set.univ (fun _ : Fin p => ℓ.toAddSubgroup) := by
    ext x; simp [Lp, AddSubgroup.mem_pi, Submodule.mem_pi]
  rw [e1, e2, relIndex_pi_pi_of, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.SumIndex
end
