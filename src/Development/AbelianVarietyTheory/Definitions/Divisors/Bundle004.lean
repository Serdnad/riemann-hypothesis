module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.LinearAlgebra.BilinearMap
public import ReciprocityTheory.SemistableReduction.Bundle001
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import GroundTheory.FunctionField.PlaceDefs
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTan

variable {R : Type} [CommRing R]

def Lifts {X : Scheme.{0}} (s : X ⟶ Sp R) {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X) : Prop :=
  z ≫ s = spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) ∧
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = P

def unitPt (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] : Sp B ⟶ A.left :=
  spMap (algebraMap R B) ≫ (show Sp R ⟶ A.left from η[A].left)

def IsSum {B M B' M' : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [CommRing B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M']
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M') (α : B → B') (f : M → M') : Prop :=
  (∀ b, β (TrivSqZeroExt.inl b) = TrivSqZeroExt.inl (α b)) ∧ ∀ m, β (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (f m)

structure TanRep (A : Over (Sp R)) [GrpObj A] (W : Type) [AddCommGroup W] [Module R W] where

  Φ : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] (_ : Sp (TrivSqZeroExt B M) ⟶ A.left), W →ₗ[R] M

  bij : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] (l : W →ₗ[R] M),
    ∃! z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z ∧ Φ z = l

  nat : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M']
    [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M'] (α : B →ₐ[R] B') (f : M →ₗ[R] M')
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f →
    ∀ z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z → Φ (spMap β ≫ z) = f ∘ₗ Φ z

end GlobalTheory.AbTan

namespace GlobalTheory.AbTan.MultGroup

open LaurentPolynomial

variable (R : Type) [CommRing R]

local instance hopfLaurent : HopfAlgebra (CommRingCat.of R) (CommRingCat.of R[T;T⁻¹]) :=
  inferInstanceAs (HopfAlgebra R R[T;T⁻¹])

abbrev G : Over (Sp R) := (Spec (CommRingCat.of R[T;T⁻¹])).asOver (Spec (CommRingCat.of R))

theorem G_hom : (G R).hom = spMap (algebraMap R R[T;T⁻¹]) := rfl

theorem unit_eq (B : Type) [CommRing B] [Algebra R B] :
    unitPt (G R) B = spMap (algebraMap R B) ≫ spMap (Bialgebra.counitAlgHom R R[T;T⁻¹]).toRingHom := rfl

theorem comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem inj' {A B : Type} [CommRing A] [CommRing B] {p q : A →+* B} (h : spMap p = spMap q) : p = q := by
  have h' := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'

variable {R}

def pre {C : Type} [CommRing C] (z : Sp C ⟶ (G R).left) : R[T;T⁻¹] →+* C :=
  (Spec.preimage (R := CommRingCat.of R[T;T⁻¹]) (S := CommRingCat.of C) z).hom

theorem spMap_pre {C : Type} [CommRing C] (z : Sp C ⟶ (G R).left) : spMap (pre z) = z := by
  simp only [spMap, pre, CommRingCat.ofHom_hom]
  exact Spec.map_preimage z

theorem pre_spMap {C : Type} [CommRing C] (φ : R[T;T⁻¹] →+* C) : pre (R := R) (spMap φ) = φ := by
  simp only [pre, spMap, Spec.preimage_map, CommRingCat.hom_ofHom]

theorem hom_ext' {C : Type} [CommRing C] {φ ψ : R[T;T⁻¹] →+* C}
    (h0 : φ.comp (algebraMap R _) = ψ.comp (algebraMap R _)) (h1 : φ (T 1) = ψ (T 1)) : φ = ψ := by
  have hC : ∀ a : R, φ (LaurentPolynomial.C a) = ψ (LaurentPolynomial.C a) := fun a => by
    rw [LaurentPolynomial.C_eq_algebraMap]
    exact congrArg (fun f : R →+* C => f a) h0
  have hinv : φ (T (-1)) = ψ (T (-1)) := by
    have e : (T (-1) : R[T;T⁻¹]) * T 1 = 1 := by rw [← T_add]; simp
    have eφ : φ (T (-1)) * φ (T 1) = 1 := by rw [← map_mul, e, map_one]
    have eψ : ψ (T 1) * ψ (T (-1)) = 1 := by rw [← map_mul, mul_comm, e, map_one]
    calc φ (T (-1)) = φ (T (-1)) * (ψ (T 1) * ψ (T (-1))) := by rw [eψ, _root_.mul_one]
      _ = (φ (T (-1)) * φ (T 1)) * ψ (T (-1)) := by rw [h1, _root_.mul_assoc]
      _ = ψ (T (-1)) := by rw [eφ, _root_.one_mul]
  have hT : ∀ n : ℤ, φ (T n) = ψ (T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [T_add, map_mul, map_mul, ih, h1]
    | pred k ih => rw [sub_eq_add_neg, T_add, map_mul, map_mul, ih, hinv]
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  | C_mul_T n a => rw [map_mul, map_mul, hC, hT]

theorem lifts_iff {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (φ : R[T;T⁻¹] →+* TrivSqZeroExt B M) :
    Lifts (G R).hom (unitPt (G R) B) (spMap φ) ↔
      φ.comp (algebraMap R _) = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B) ∧ (φ (T 1)).fst = 1 := by
  have hε : Bialgebra.counitAlgHom R R[T;T⁻¹] (T 1) = 1 := by
    rw [Bialgebra.counitAlgHom_apply]
    exact AddMonoidAlgebra.counit_single (1 : ℤ) (1 : R)
  have hεC : ∀ r : R, Bialgebra.counitAlgHom R R[T;T⁻¹] (algebraMap R _ r) = r := fun r =>
    (Bialgebra.counitAlgHom R R[T;T⁻¹]).commutes r
  have e1 : spMap φ ≫ (G R).hom = spMap (φ.comp (algebraMap R _)) := by
    rw [G_hom]; exact comp' _ _
  have e2 : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap φ =
      spMap ((TrivSqZeroExt.fstHom B B M).toRingHom.comp φ) := comp' _ _
  have e3 : unitPt (G R) B =
      spMap ((algebraMap R B).comp (Bialgebra.counitAlgHom R R[T;T⁻¹]).toRingHom) := by
    rw [unit_eq]; exact comp' _ _
  unfold Lifts
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := inj' (e1.symm.trans h1)
    have h2' := inj' (e2.symm.trans (h2.trans e3))
    refine ⟨h1', ?_⟩
    have := congrArg (fun f : R[T;T⁻¹] →+* B => f (T 1)) h2'
    simpa [hε] using this
  · rintro ⟨h1, h2⟩
    refine ⟨e1.trans (congrArg spMap h1), e2.trans ((congrArg spMap ?_).trans e3.symm)⟩
    apply hom_ext'
    · ext r
      have := congrArg (fun f : R →+* TrivSqZeroExt B M => (f r).fst) h1
      simpa [hεC] using this
    · simpa [hε] using h2

def tanRep : TanRep (G R) R where
  Φ z := LinearMap.toSpanSingleton R _ (pre z (T 1)).snd
  bij := by
    intro B M _ _ _ _ _ _ _ _ l
    let u : (TrivSqZeroExt B M)ˣ :=
      ⟨TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l 1), TrivSqZeroExt.inl 1 - TrivSqZeroExt.inr (l 1),
        by ext <;> simp, by ext <;> simp⟩
    let φ := LaurentPolynomial.eval₂ ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) u
    have hT : φ (T 1) = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l 1) := by
      simp [φ, u, LaurentPolynomial.eval₂_T]
    have hC : φ.comp (algebraMap R _) = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B) := by
      refine RingHom.ext fun r => ?_
      simp [φ, ← LaurentPolynomial.C_eq_algebraMap]
    refine ⟨spMap φ, ⟨(lifts_iff φ).2 ⟨hC, by simp [hT]⟩, ?_⟩, ?_⟩
    · ext; simp [pre_spMap, hT]
    · rintro z ⟨hz, hl⟩
      rw [← spMap_pre z] at hz ⊢
      obtain ⟨h1, h2⟩ := (lifts_iff _).1 hz
      refine congrArg _ (hom_ext' (h1.trans hC.symm) ?_)
      have h3 : (pre z (T 1)).snd = l 1 := by rw [← hl]; simp
      rw [hT]; ext
      · simp [h2]
      · simp [h3]
  nat := by
    intro B M _ _ _ _ _ _ _ _ B' M' _ _ _ _ _ _ _ _ α f β hβ z _
    have : pre (spMap β ≫ z) = β.comp (pre z) := by
      apply inj'
      rw [spMap_pre, ← comp']
      erw [spMap_pre]
      rfl
    ext
    simp only [this, LinearMap.toSpanSingleton_apply, one_smul, LinearMap.comp_apply, RingHom.comp_apply]
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (pre z (T 1)), map_add (f := _), hβ.1, hβ.2]
    simp

end GlobalTheory.AbTan.MultGroup
end
end

section

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.Block5c

def TypeCusp : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (J : Subgroup (GL ι K)), IsOpen (J : Set (GL ι K)) → IsCompact (J : Set (GL ι K)) →
  ∀ χ : J →* ℂˣ, IsOpen (χ.ker : Set J) →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ h : GL ι K, ∃ X, ∃ hX : h⁻¹ * u X * h ∈ J, χ ⟨_, hX⟩ ≠ 1) →
  ∀ f : GL ι K → ℂ, (∀ g (hg : g ∈ J), f g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ)) → (∀ g, g ∉ J → f g = 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  (∀ x ∈ (χ.ker.map J.subtype), ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0)

end GlobalTheory.Block5c
end
end

section

set_option autoImplicit false

noncomputable section

open scoped IntermediateField Polynomial

namespace GlobalTheory.Nef

def IsFF (k F : Type) [Field k] [Field F] [Algebra k F] : Prop :=
  ∃ t : F, Transcendental k t ∧ FiniteDimensional k⟮t⟯ F

def Place (k F : Type) [Field k] [Field F] [Algebra k F] : Type :=
  {v : Valuation F (WithZero (Multiplicative ℤ)) //
    Function.Surjective v ∧ ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1}

variable {k F : Type} [Field k] [Field F] [Algebra k F]

abbrev Place.O (v : Place k F) : ValuationSubring F := v.1.valuationSubring

def ord (v : Place k F) (x : F) : ℤ := -WithZero.log (v.1 x)

def nrm {n : ℕ} (v : Place k F) (x : Fin n → F) : WithZero (Multiplicative ℤ) :=
  Finset.univ.sup fun i => v.1 (x i)

def ordVec {n : ℕ} (v : Place k F) (x : Fin n → F) : ℤ := -WithZero.log (nrm v x)

def Unimod {n : ℕ} (v : Place k F) (g : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ i j, v.1 (g i j) ≤ 1) ∧ v.1 g.det = 1

def admitted {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ v, (g v).det ≠ 0) ∧ {v | ¬ Unimod v (g v)}.Finite

def deg [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : ℤ := ∑ᶠ v, ord v (g v).det

def degLine [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (w : Fin n → F) : ℤ :=
  ∑ᶠ v, ordVec v ((g v).mulVec w)

def IsRes {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) : Prop :=
  ∀ p x, p.1 (algebraMap F E x) ≤ 1 ↔ (ρ p).1 x ≤ 1

def pullAd {n : ℕ} {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F)
    (g : Place k F → Matrix (Fin n) (Fin n) F) : Place k E → Matrix (Fin n) (Fin n) E :=
  fun p => (g (ρ p)).map (algebraMap F E)

def LinesLE [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (b : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E]
    (ρ : Place k E → Place k F), IsRes ρ → ∀ w : Fin n → E, w ≠ 0 →
      (degLine (pullAd ρ g) w : ℝ) ≤ b * Module.finrank F E

def IsRat (φ : PowerSeries F) : Prop :=
  ∃ p q : F[X], q ≠ 0 ∧ (q : PowerSeries F) * φ = (p : PowerSeries F)

def hankel (c : ℕ → F) (n : ℕ) : F := (Matrix.of fun i j : Fin (n + 1) => c (i + j)).det

def sc (v : Place k F) (u : F) : PowerSeries v.O →+* PowerSeries F :=
  (PowerSeries.rescale u).comp (PowerSeries.map v.O.subtype)

namespace Lib

open scoped WithZero
open IsDedekindDomain GroundTheory.FunctionField


section Line

variable (k)


variable {k}

end Line

section Product

end Product

end Lib

end GlobalTheory.Nef
end
end

section

noncomputable section

namespace GlobalTheory.UPel.Sm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

section KS

variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]

def IsKS (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H)
    (f : H →ₗ[k] H) : Prop :=
  (∀ a, ∀ x ∈ Fil, f (ρ a x) - ρ a (f x) ∈ Fil) ∧ (∀ x ∈ Z, f x ∈ Fil) ∧
    ∀ x ∈ Fil, ∀ y ∈ Fil, φ (f x) y + φ x (f y) = 0

def KSDim (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) (d : ℕ) :
    Prop :=
  ∃ f : Fin d → (H →ₗ[k] H), (∀ i, IsKS ρ φ Fil Z (f i)) ∧
    ∀ g, IsKS ρ φ Fil Z g → ∃! c : Fin d → k, ∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil

end KS

end GlobalTheory.UPel.Sm
end
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField

namespace GlobalTheory.ChowHt

structure IsChowForm {k : Type} [Field k] {N : ℕ} (I : Ideal (MvPolynomial (Fin N) k)) (D δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) k) : Prop where

  homog : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) f

  irred : Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f)

  zero_iff : ∀ u : Fin (D + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f = 0 ↔
    ∃ y : Fin N → AlgebraicClosure k, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
      ∀ i, ∑ j, u (i, j) * y j = 0

def linSubst {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (f : MvPolynomial (Fin B × Fin N) R) : MvPolynomial (Fin B × Fin n) R :=
  MvPolynomial.aeval (fun p : Fin B × Fin N => ∑ k, C (M p.2 k) * X (p.1, k)) f

def frameNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖(A⁻¹.mulVec x) i‖ ^ 2)

def formHeight {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ : ℕ)
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin B × Fin N) F) : ℝ :=
  ((∑ᶠ v : FinitePlace F, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linSubst w f))) +
    ∑ σ : F →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) +
      (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2)) / (Module.finrank ℚ F : ℝ)

def pointHeight {F : Type} [Field F] [NumberField F] {N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    {K : Type} [Field K] [NumberField K] [Algebra F K] (y : Fin N → K) : ℝ :=
  ((∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (∑ j, algebraMap F K (w j k) * y j))) +
    ∑ τ : K →+* ℂ, Real.log (Real.sqrt
      (∑ i, ‖∑ j, A (τ.comp (algebraMap F K)) j i * τ (y j)‖ ^ 2))) / (Module.finrank ℚ K : ℝ)

def ConjCompat {F : Type} [Field F] {N : ℕ} (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ (σ : F →+* ℂ) (x : Fin N → ℂ),
    frameNorm (A ((starRingEnd ℂ).comp σ)) (fun j => (starRingEnd ℂ) (x j)) = frameNorm (A σ) x

end GlobalTheory.ChowHt
end
end
