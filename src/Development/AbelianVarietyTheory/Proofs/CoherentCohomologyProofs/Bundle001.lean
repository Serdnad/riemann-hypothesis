module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
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
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.OrderOfVanishing.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Topology.Constructions
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory.PeirceDecompositionCut

variable {R : Type*} [CommRing R] (A : Type*) [Ring A] [Algebra R A]

def peirceCut (e : R) (he : IsIdempotentElem e) : A →* A where
  toFun x := e • x + (1 - e) • (1 : A)
  map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
  map_mul' x y := by
    have h1 : e * e = e := he
    have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
    have h3 : (1 - e) * e = 0 := by rw [mul_comm, h2]
    have h4 : (1 - e) * (1 - e) = 1 - e := he.one_sub
    simp only [add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, h4, zero_smul, add_zero,
      zero_add, mul_one]

variable {A}

end GlobalTheory.PeirceDecompositionCut
end

section

open Polynomial

namespace GlobalTheory.ReesAlgebraMembership

variable {K A : Type*} [CommSemiring K] [Semiring A] [Algebra K A]

def reesAlg (M : ℕ → Submodule K A) [SetLike.GradedMonoid M] : Subalgebra K A[X] where
  carrier := {f | ∀ n, f.coeff n ∈ M n}
  add_mem' := fun {f g} hf hg n => by
    rw [coeff_add]
    exact (M n).add_mem (hf n) (hg n)
  mul_mem' := fun {f g} hf hg n => by
    rw [coeff_mul]
    refine (M n).sum_mem fun c hc => ?_
    have hn : c.1 + c.2 = n := by simpa using hc
    rw [← hn]
    exact SetLike.mul_mem_graded (hf c.1) (hg c.2)
  algebraMap_mem' := fun r n => by
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      rw [Algebra.algebraMap_eq_smul_one]
      exact (M 0).smul_mem r (SetLike.one_mem_graded M)
    · exact (M n).zero_mem

variable (M : ℕ → Submodule K A) [SetLike.GradedMonoid M]

end GlobalTheory.ReesAlgebraMembership
end

section

namespace GlobalTheory.AddEquivOfSurjectiveKernel

universe u_1 u_2 u_3

theorem exists_addEquiv_of_surjective_of_ker_iff {A : Type u_1} {B : Type u_2} {C : Type u_3}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : A →+ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a : A, f a = 0 ↔ g a = 0) :
    ∃ e : B ≃+ C, ∀ a : A, e (f a) = g a := by
  have key : ∀ a b : A, f a = f b ↔ g a = g b := by
    intro a b
    rw [← sub_eq_zero, ← map_sub, h, map_sub, sub_eq_zero]
  choose s hs using hf
  choose t ht using hg
  have h1 : ∀ a, g (s (f a)) = g a := fun a => (key _ _).1 (hs _)
  have h2 : ∀ a, f (t (g a)) = f a := fun a => (key _ _).2 (ht _)
  refine ⟨{ toFun := fun b => g (s b)
            invFun := fun c => f (t c)
            left_inv := fun b => by
              show f (t (g (s b))) = b
              rw [h2, hs]
            right_inv := fun c => by
              show g (s (f (t c))) = c
              rw [h1, ht]
            map_add' := fun x y => by
              show g (s (x + y)) = g (s x) + g (s y)
              rw [← map_add (f := _), ← key, map_add (f := _), hs, hs, hs] }, fun a => h1 a⟩

end GlobalTheory.AddEquivOfSurjectiveKernel
end

section

namespace GlobalTheory.ConjugationEquiv

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjEquiv (N : Subgroup G) (b : G) (hb : ∀ u : G, u ∈ N ↔ b * u * b⁻¹ ∈ N) : N ≃ₜ* N where
  toFun u := ⟨b * (u : G) * b⁻¹, (hb u).1 u.2⟩
  invFun u := ⟨b⁻¹ * (u : G) * b, (hb _).2 (by
    have h : b * (b⁻¹ * (u : G) * b) * b⁻¹ = u := by group
    rw [h]; exact u.2)⟩
  left_inv u := Subtype.ext (by
    show b⁻¹ * (b * (u : G) * b⁻¹) * b = u
    group)
  right_inv u := Subtype.ext (by
    show b * (b⁻¹ * (u : G) * b) * b⁻¹ = u
    group)
  map_mul' u v := Subtype.ext (by
    show b * ((u : G) * v) * b⁻¹ = (b * u * b⁻¹) * (b * v * b⁻¹)
    group)
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

end GlobalTheory.ConjugationEquiv
end

section

namespace GlobalTheory.TwistedInverseSubgroups

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]

def leftInvRightTwisted (H : Subgroup G) (γ : G) (T : E →ₗ[ℂ] E) : Submodule ℂ (G → E) where
  carrier := {f | (∀ h ∈ H, ∀ g, f (h * g) = f g) ∧ ∀ g, f (g * γ) = T (f g)}
  add_mem' := by
    rintro f₁ f₂ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    exact ⟨fun h hh g => by simp [a₁ h hh g, a₂ h hh g], fun g => by simp [b₁ g, b₂ g]⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨a, b⟩
    exact ⟨fun h hh g => by simp [a h hh g], fun g => by simp [b g]⟩

variable {H : Subgroup G} {γ : G} {T : E →ₗ[ℂ] E} {f : G → E}

end GlobalTheory.TwistedInverseSubgroups
end

section

namespace GlobalTheory.SubmoduleSaturation

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

def saturation (g : A) (K : Submodule A M) : Submodule A M where
  carrier := {m | ∃ k : ℕ, g ^ k • m ∈ K}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    rw [smul_add]
    refine K.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact K.smul_mem _ hk
    · rw [pow_add, mul_smul]
      exact K.smul_mem _ hl
  smul_mem' := by
    rintro c a ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [smul_comm]
    exact K.smul_mem _ hk

end GlobalTheory.SubmoduleSaturation
end

section

open IsDedekindDomain Function

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R]

theorem isFiniteLength_of_isTorsion [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {X : Type*} [AddCommGroup X] [Module R X] [Module.Finite R X] (hX : Module.IsTorsion R X) :
    IsFiniteLength R X := by
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hX
  have hr' : Module.IsTorsionBySet R X (Ideal.span {r}) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    exact fun x ↦ Submodule.mem_annihilator.mp hr x trivial
  letI := hr'.module
  haveI : Module.Finite (R ⧸ Ideal.span {r}) X := Module.Finite.of_restrictScalars_finite R _ _
  haveI : IsArtinian R (R ⧸ Ideal.span {r}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_span_singleton R hr0)).2
  haveI : IsArtinianRing (R ⧸ Ideal.span {r}) := isArtinian_of_tower R inferInstance
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance,
    isArtinian_of_surjective_algebraMap (R := R ⧸ Ideal.span {r}) Ideal.Quotient.mk_surjective⟩

section Submodules

variable (T : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S]

variable {V : Type*} [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

end Submodules

end General

section Dedekind

variable {O : Type*} [CommRing O] [IsDedekindDomain O]

section Torsion

variable {X : Type*} [AddCommGroup X] [Module O X] [Module.Finite O X]

variable [Ring.HasFiniteQuotients O]

variable [Module.Free ℤ O]

end Torsion

section Lattices

variable [Ring.HasFiniteQuotients O] [Module.Free ℤ O]

end Lattices

end Dedekind

end GlobalTheory
end

section

namespace GlobalTheory

open Finset

theorem setOf_degree_eq_coe_finsuppAntidiag (σ : Type*) [Fintype σ] [DecidableEq σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a} = ↑(finsuppAntidiag (univ : Finset σ) a) := by
  ext α
  simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]

theorem ncard_degree_eq (σ : Type*) [Fintype σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a}.ncard = (a + Fintype.card σ - 1).choose a := by
  classical
  rw [setOf_degree_eq_coe_finsuppAntidiag, Set.ncard_coe_finset,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Nat.add_comm]

theorem natCard_degree_eq (σ : Type*) [Fintype σ] (a : ℕ) :
    Nat.card {α : σ →₀ ℕ // α.degree = a} = (a + Fintype.card σ - 1).choose a := by
  have h := ncard_degree_eq σ a
  rw [← Nat.card_coe_set_eq] at h
  exact h

end GlobalTheory
end

section

namespace GlobalTheory.SquareZeroLeibnizPoint

open TrivSqZeroExt

section PointsOfDual

variable {O C : Type*} [CommRing O] [CommRing C] {ι : Type*} [Fintype ι]

end PointsOfDual

section Leibniz

variable {A O M : Type*} [CommRing A] [CommRing O] [AddCommGroup M] [Module O M]

theorem leibniz_map_one (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : d 1 = 0 := by
  have h := hd 1 1
  simpa using h

variable [Module Oᵐᵒᵖ M] [IsCentralScalar O M]

def sqzOfLeibniz (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : A →+* TrivSqZeroExt O M where
  toFun f := (ε f, d f)
  map_one' := TrivSqZeroExt.ext (map_one ε) (leibniz_map_one ε d hd)
  map_zero' := TrivSqZeroExt.ext (map_zero ε) (map_zero d)
  map_add' f f' := TrivSqZeroExt.ext (map_add ε f f') (map_add d f f')
  map_mul' f f' := TrivSqZeroExt.ext (map_mul ε f f') (by
    change d (f * f') = ε f • d f' + MulOpposite.op (ε f') • d f
    rw [op_smul_eq_smul]
    exact hd f f')

end Leibniz

end GlobalTheory.SquareZeroLeibnizPoint
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.QCoh.Qcqs

section Base

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

def baseRingHom (p : X ⟶ Spec R) (U : X.Opens) : R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso R).inv ≫ p.appLE ⊤ U le_top

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_res (p : X ⟶ Spec R) {U V : X.Opens} (h : V ≤ U) (r : R) :
    X.presheaf.map (homOfLE h).op (baseRingHom p U r) = baseRingHom p V r := by
  rw [← ConcreteCategory.comp_apply, baseRingHom, Category.assoc, Scheme.Hom.appLE_map]
  rfl

theorem baseRingHom_top (p : X ⟶ Spec R) :
    baseRingHom p ⊤ = (Scheme.ΓSpecIso R).inv ≫ p.appTop := by
  rw [baseRingHom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_comp_app (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) :
    baseRingHom p U ≫ g.app U = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) := by
  rw [baseRingHom, baseRingHom, Category.assoc, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]

theorem app_baseRingHom (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) (r : R) :
    g.app U (baseRingHom p U r) = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) r := by
  rw [← baseRingHom_comp_app]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_comp_SpecMap {L : CommRingCat.{u}} (q : Y ⟶ Spec L) (ι : R ⟶ L)
    (V : Y.Opens) : baseRingHom (q ≫ Spec.map ι) V = ι ≫ baseRingHom q V := by
  rw [baseRingHom, baseRingHom, Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  exact congrArg _ (Scheme.Hom.appLE_comp_appLE q (Spec.map ι) ⊤ ⊤ V le_top le_top).symm

end Base

section Localization

variable {R L : CommRingCat.{u}} [Algebra R L] (S : Submonoid R) [IsLocalization S L]
  {X Y : Scheme.{u}} {p : X ⟶ Spec R} {q : Y ⟶ Spec L} {g : Y ⟶ X}
  (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R L))))

include H

omit S in
theorem baseRingHom_algebraMap (V : Y.Opens) (r : R) :
    baseRingHom q V (algebraMap R L r) = baseRingHom (g ≫ p) V r := by
  rw [H.w, baseRingHom_comp_SpecMap]; rfl


theorem isLocalization_app {V : X.Opens} (hV : IsAffineOpen V) :
    @IsLocalization Γ(X, V) _ (S.map (baseRingHom p V).hom) Γ(Y, g ⁻¹ᵁ V) _
      (g.app V).hom.toAlgebra := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := g ⁻¹ᵁ V) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  have po' : IsPushout (baseRingHom p V) (CommRingCat.ofHom (algebraMap R L)) (g.app V)
      (baseRingHom q (g ⁻¹ᵁ V)) := by
    refine po.of_iso (Scheme.ΓSpecIso R) (Iso.refl _) (Scheme.ΓSpecIso L) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [baseRingHom]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [baseRingHom]
  let := (g.app V).hom.toAlgebra
  let := (baseRingHom p V).hom.toAlgebra
  let := (baseRingHom q (g ⁻¹ᵁ V)).hom.toAlgebra
  let := (baseRingHom (g ≫ p) (g ⁻¹ᵁ V)).hom.toAlgebra
  have : IsScalarTower R Γ(X, V) Γ(Y, g ⁻¹ᵁ V) :=
    .of_algebraMap_eq fun r ↦ (app_baseRingHom g p V r).symm
  have : IsScalarTower R L Γ(Y, g ⁻¹ᵁ V) :=
    .of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap H _ r).symm
  exact (Algebra.isLocalization_iff_isPushout S L).mpr
    (CommRingCat.isPushout_iff_isPushout.mp po')

end Localization

end GlobalTheory.QCoh.Qcqs
end
end

section

open Matrix

namespace GlobalTheory.UnitaryLieAlgebra

variable {n : Type*} [Fintype n]

def unitaryLie (J : Matrix n n ℂ) : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | Xᴴ * J + J * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' := by
    intro r X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX,
      smul_zero]

end GlobalTheory.UnitaryLieAlgebra
end
