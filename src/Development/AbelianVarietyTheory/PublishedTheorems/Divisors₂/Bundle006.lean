module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.WittVector.Frobenius
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

def IsPeriodMap (ε : ℤˣ) {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (P : u.Λ →+ HdR A) : Prop :=
  Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g ∧
    (∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) ∧
    (∀ (α : A ⟶ A) [IsMonHom α] (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ w, u.ex (M w) = u.ex w ≫ α) →
      ∀ x x' : u.Λ, (x' : Fin g → ℂ) = M x → push (dp0 ℂ) (𝟙 _) α (P x) = P x') ∧
    ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (ψ : LinearMap.BilinForm ℂ (HdR A)), u.IsAH H χ →
      IsPolForm (dp0 ℂ) (𝟙 _) A L ψ → ∀ x x' : u.Λ,
        ψ (P x) (P x') = ((ε : ℤ) : ℂ) * (2 * Real.pi * Complex.I) *
          (((x : Fin g → ℂ) ⬝ᵥ H.mulVec (star (x' : Fin g → ℂ))).im : ℂ)

def taylor {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (f : (I → ℂ) → ℂ) : D :=
  ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I,
    ((k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k f 0 fun a ↦ Pi.single (s a) 1) • ∏ a, t (s a)

end GlobalTheory.PeriodFamily

namespace GlobalTheory.Published

open GlobalTheory.PeriodFamily

def GaussManinPeriods : Prop :=
  ∃ ε : ℤˣ, ∀ (B : Type) [CommRing B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (𝒜 : Over (Sp B)) [GrpObj 𝒜] (g : ℕ),
    IsAbelianScheme 𝒜 → SmoothOfRelativeDimension g 𝒜.hom →
    ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (y : (I → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen U → 0 ∈ U →
      (∀ b, DifferentiableOn ℂ (fun z ↦ y z b) U) →
    ∀ (A : (I → ℂ) → Over (Sp ℂ)) [∀ z, GrpObj (A z)] (φ : ∀ z, (A z).left ⟶ 𝒜.left),
      (∀ z, IsGrpPullback (A z) 𝒜 (spMap (y z : B →+* ℂ)) (φ z)) →
    ∀ (m : ∀ z, GrpMor (dp0 B) (𝟙 _) 𝒜 (dp0 ℂ) (𝟙 _) (A z) (y z : B →+* ℂ) (spMap (y z : B →+* ℂ)) (φ z))
      (L : ∀ z, LB (A z).left), (∀ z, (L z).IsLB) →
    ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (φ₀ : A₀.left ⟶ 𝒜.left), IsGrpPullback A₀ 𝒜 (spMap (y 0 : B →+* ℂ)) φ₀ →
    ∀ (L₀ : LB A₀.left), L₀.IsLB → ∀ u₀ : HolUnif A₀ L₀ g,
    ∃ (V : Set (I → ℂ)) (u : ∀ z, HolUnif (A z) (L z) g) (τ : ∀ z, u₀.Λ ≃+ (u z).Λ) (P : ∀ z, (u z).Λ →+ HdR (A z))
      (P₀ : u₀.Λ →+ HdR A₀), IsOpen V ∧ 0 ∈ V ∧ V ⊆ U ∧
      IsPeriodMap ε u₀ P₀ ∧ (∀ z ∈ V, IsPeriodMap ε (u z) (P z)) ∧
      (∀ w, ((u 0).ex w).left ≫ φ 0 = (u₀.ex w).left ≫ φ₀) ∧ (∀ x, (τ 0 x : Fin g → ℂ) = x) ∧
      (∀ x, DifferentiableOn ℂ (fun z ↦ (τ z x : Fin g → ℂ)) V) ∧
      (∀ (α : 𝒜 ⟶ 𝒜) [IsMonHom α] (M₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
        (∀ w, (u₀.ex (M₀ w)).left ≫ φ₀ = (u₀.ex w).left ≫ φ₀ ≫ α.left) →
        ∀ z ∈ V, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ w, ((u z).ex (M w)).left ≫ φ z = ((u z).ex w).left ≫ φ z ≫ α.left) ∧
          ∀ x x' : u₀.Λ, (x' : Fin g → ℂ) = M₀ x → (τ z x' : Fin g → ℂ) = M (τ z x)) ∧
      (∀ x (c : primDR 𝒜), DifferentiableOn ℂ (fun z ↦ P z (τ z x) ((m z).pull c)) V) ∧
      ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ →
        (∀ a : ℂ, π (algebraMap ℂ D a) = a) →
        ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
        ∀ (j : B →ₐ[ℂ] D), (∀ b, j b = taylor N t fun z ↦ y z b) →
        ∀ (A' : Over (Sp D)) [GrpObj A'] (φ' : A'.left ⟶ 𝒜.left), IsGrpPullback A' 𝒜 (spMap (j : B →+* D)) φ' →
        ∀ (m' : GrpMor (dp0 B) (𝟙 _) 𝒜 (dp0 D) (𝟙 _) A' (j : B →+* D) (spMap (j : B →+* D)) φ')
          (i : A₀.left ⟶ A'.left) (h : IsGrpPullback A₀ A' (spMap π) i), i ≫ φ' = φ₀ →
        ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀)))
          (x : u₀.Λ) (d : Crys κ (spMap π) A₀), k.Corr (P₀ x) d → ∀ c : primDR 𝒜,
          crysToDR κ h d (m'.pull c) = taylor N t fun z ↦ P z (τ z x) ((m z).pull c)

end GlobalTheory.Published
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def PeriodComparison : Prop :=
  ∃ ε : ℤˣ, ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left), L.IsLB → ∀ u : HolUnif A L g, ∃ P : u.Λ →+ HdR A,
      Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g ∧
      (∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) ∧
      (∀ (α : A ⟶ A) [IsMonHom α] (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ w, u.ex (M w) = u.ex w ≫ α) →
        ∀ x x' : u.Λ, (x' : Fin g → ℂ) = M x → push (dp0 ℂ) (𝟙 _) α (P x) = P x') ∧
      ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (ψ : LinearMap.BilinForm ℂ (HdR A)), u.IsAH H χ →
        IsPolForm (dp0 ℂ) (𝟙 _) A L ψ → ∀ x x' : u.Λ,
          ψ (P x) (P x') = ((ε : ℤ) : ℂ) * (2 * Real.pi * Complex.I) *
            (((x : Fin g → ℂ) ⬝ᵥ H.mulVec (star (x' : Fin g → ℂ))).im : ℂ)

end GlobalTheory.Published
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace AbelianDeRham

theorem bcMor {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A : Over (Sp R)} [GrpObj A]
    {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) :
    GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' (algebraMap R R') (spMap (algebraMap R R')) φ :=
  GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) h

def Free : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    AllPrim (dp0 R) (𝟙 _) A ∧
    Module.Finite R (FirstDeRham (A.hom ≫ 𝟙 _)) ∧ Module.Projective R (FirstDeRham (A.hom ≫ 𝟙 _)) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (FirstDeRham (A.hom ≫ 𝟙 _)) p = 2 * g) ∧
    ∃ e : ⋀[R]^2 (FirstDeRham (A.hom ≫ 𝟙 _)) ≃ₗ[R] SecondDeRham (A.hom ≫ 𝟙 _),
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup _ a b

def Hodge : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    LieExact A ∧ (∃ N : Submodule R (primDR A), IsCompl (PrimitiveSubmodule A) N) ∧
    Module.Finite R (PrimitiveSubmodule A) ∧ Module.Projective R (PrimitiveSubmodule A) ∧
    ∀ p : PrimeSpectrum R, Module.rankAtStalk (PrimitiveSubmodule A) p = g

def BaseChange : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (A' : Over (Sp R')) [GrpObj A']
      (φ : A'.left ⟶ A.left) (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ),
      (bcMor h).IsBC ∧ PrimitiveSubmodule A' = Submodule.span R' ((bcMor h).pull '' (PrimitiveSubmodule A))

def Rigid : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (i : A₀.left ⟶ A.left) (h : IsGrpPullback A₀ A (spMap π) i),
      Function.Bijective (liftMor κ h).pull

def Duality : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm R (HdR A),
      IsPolForm (dp0 R) (𝟙 _) A L ψ →
      (∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0) ∧
      (ReciprocityTheory.ChartRestriction.G.Out.KTriv A L → LinearMap.IsPerfPair ψ)

end AbelianDeRham

def AbelianDeRham : Prop :=
  AbelianDeRham.Free ∧ AbelianDeRham.Hodge ∧ AbelianDeRham.BaseChange ∧ AbelianDeRham.Rigid ∧
    AbelianDeRham.Duality

namespace AbelianDeRham

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem Free.prim (H : Free) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Module.Finite R (primDR A) ∧ Module.Projective R (primDR A) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (primDR A) p = 2 * g := by
  obtain ⟨h0, h1, h2, h3, -⟩ := H R A g hA hg
  let e : primDR A ≃ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) := LinearEquiv.ofTop _ h0
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm,
    fun p ↦ by rw [Module.rankAtStalk_eq_of_equiv e, h3]⟩

theorem Rigid.crysToDR_bijective (H : Rigid) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {I : Ideal R} {κ : DividedPowers I} (hκ : IsNilDP κ)
    {R₀ : Type} [CommRing R₀] {π : R →+* R₀} (hπ : Function.Surjective π) (hI : RingHom.ker π = I)
    {A₀ : Over (Sp R₀)} [GrpObj A₀] {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap π) i) :
    Function.Bijective (crysToDR κ h) :=
  (LinearEquiv.ofBijective _ (H R A g hA hg I κ hκ R₀ π hπ hI A₀ i h)).dualMap.bijective

end AbelianDeRham

end GlobalTheory.Published
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianDieudonne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p],
    ∃ (M : ∀ (A : Over (Sp k)) [GrpObj A], ModuleCat.{0} (WittVector p k))
      (map : ∀ {A B : Over (Sp k)} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f],
        M A →ₗ[WittVector p k] M B)
      (F : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] M A)
      (V : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] M A)
      (red : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] HdR A),
      (∀ (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
        SmoothOfRelativeDimension g A.hom →
        Module.Free (WittVector p k) (M A) ∧ Module.Finite (WittVector p k) (M A) ∧
        Module.finrank (WittVector p k) (M A) = 2 * g ∧
        (∀ m, F A (V A m) = p • m) ∧ (∀ m, V A (F A m) = p • m) ∧
        Function.Surjective (red A) ∧ (∀ m, red A m = 0 ↔ ∃ n, m = p • n) ∧
        (∀ h, h ∈ Fil A ↔ ∃ m, h = red A (V A m)) ∧
        map (𝟙 A) = LinearMap.id) ∧
      (∀ (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B →
        (∀ (f : A ⟶ B) [IsMonHom f] (m : M A),
          map f (F A m) = F B (map f m) ∧ map f (V A m) = V B (map f m) ∧
          red B (map f m) = push (dp0 k) (𝟙 _) f (red A m)) ∧
        ∀ (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)],
          map (f * g) = map f + map g) ∧
      ∀ (A B C : Over (Sp k)) [GrpObj A] [GrpObj B] [GrpObj C], IsAbelianScheme A →
        IsAbelianScheme B → IsAbelianScheme C →
        ∀ (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g], map (f ≫ g) = map g ∘ₗ map f

namespace AbelianDieudonne

end AbelianDieudonne

end GlobalTheory.Published
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogDR

section Nabla

variable {R : Type} [CommRing R]

def derHom (D : Derivation ℤ R R) : R →+* DualNumber R where
  toFun r := TrivSqZeroExt.inl r + TrivSqZeroExt.inr (D r)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem derHom_apply (D : Derivation ℤ R R) (r : R) :
    derHom D r = TrivSqZeroExt.inl r + TrivSqZeroExt.inr (D r) := rfl

variable (A : Over (Sp R)) [GrpObj A]

theorem derMor (D : Derivation ℤ R R) :
    GrpMor (dp0 R) (𝟙 _) A (epsDP R) (epsRed R) A (derHom D) (𝟙 _) (Over.Hom.left (𝟙 A)) :=
  GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _)
    (by
      rw [← Cris.spMap_comp, show (TrivSqZeroExt.fstHom R R R).toRingHom.comp (derHom D) = RingHom.id R from
        RingHom.ext fun r ↦ by simp [derHom_apply]]
      exact (Cris.spMap_id R).symm) (𝟙 A)

variable {A}

def IsNabla (D : Derivation ℤ R R) (h k : HdR A) : Prop :=
  ∃ d : Crys (epsDP R) (epsRed R) A, (derMor A D).Corr h d ∧
    ∀ c : primDR A, d ((constMor A).pull c) = TrivSqZeroExt.inl (h c) + TrivSqZeroExt.inr (k c)

variable {D : Derivation ℤ R R}

end Nabla

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

structure Chart (t : SAB H X) (V : X.Opens) where

  U : X.affineOpens

  S : Type
  [ring : CommRing S]
  [alg : Algebra Γ(X, U.1) S]
  isOpenImmersion : IsOpenImmersion (spMap (algebraMap Γ(X, U.1) S) ≫ chart U)
  range : Set.range (spMap (algebraMap Γ(X, U.1) S) ≫ chart U :) = (U.1 ⊓ V : X.Opens)

  A : Over (Sp S)
  [grp : GrpObj A]

  φ : A.left ⟶ t.G.left
  cart : IsGrpPullback A t.G (spMap (algebraMap Γ(X, U.1) S) ≫ chart U) φ

attribute [instance] Chart.ring Chart.alg Chart.grp

variable {t : SAB H X} {V : X.Opens}

theorem exists_chart (t : SAB H X) (U : X.affineOpens) (h : IsAffineOpen (U.1 ⊓ V)) :
    ∃ c : Chart t V, c.U = U := by
  let _ : Algebra Γ(X, U.1) Γ(X, U.1 ⊓ V) := (resG X inf_le_left).toAlgebra
  have e : spMap (algebraMap Γ(X, U.1) Γ(X, U.1 ⊓ V)) ≫ chart U = h.fromSpec :=
    U.2.map_fromSpec h (homOfLE inf_le_left).op
  refine ⟨{ U := U, S := Γ(X, U.1 ⊓ V), isOpenImmersion := ?_, range := ?_
            A := (Over.pullback _).obj t.G, φ := _, cart := isGrpPullback_pullback t.G _ }, rfl⟩
  · rw [e]; infer_instance
  · rw [e]; exact h.range_fromSpec

namespace Chart

variable (c : Chart t V)

def HasImage (h : HdR c.A) (v : Sp (DualNumber Γ(X, c.U.1)) ⟶ t.G.left) : Prop :=
  ∃ w : epsR c.S ⟶ c.A,
    w.left ≫ c.φ = spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap Γ(X, c.U.1) c.S)) ≫ v ∧
    IsLieImage h w


def coLie (ψ : LinearMap.BilinForm c.S (HdR c.A)) : Submodule Γ(X, c.U.1) (HdR c.A) where
  carrier := {f | f ∈ Fil c.A ∧ ∀ h v, IsTanAtG t (chart c.U) v → c.HasImage h v →
    ψ f h ∈ Set.range (algebraMap Γ(X, c.U.1) c.S)}
  zero_mem' := ⟨zero_mem _, fun h v _ _ ↦ ⟨0, by simp⟩⟩
  add_mem' := fun {f g} hf hg ↦ ⟨add_mem hf.1 hg.1, fun h v a b ↦ by
    obtain ⟨r, hr⟩ := hf.2 h v a b
    obtain ⟨s, hs⟩ := hg.2 h v a b
    exact ⟨r + s, by simp [hr, hs]⟩⟩
  smul_mem' := fun r f hf ↦ by
    rw [← algebraMap_smul c.S r f]
    refine ⟨Submodule.smul_mem _ _ hf.1, fun h v a b ↦ ?_⟩
    obtain ⟨s, hs⟩ := hf.2 h v a b
    exact ⟨r * s, by rw [map_smul, LinearMap.smul_apply, map_mul, hs, smul_eq_mul]⟩

end Chart

def IsCanLattice {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : Chart t V) (L : Submodule Γ(X, c.U.1) (HdR c.A)) : Prop :=
  Module.Finite Γ(X, c.U.1) L ∧ Module.Projective Γ(X, c.U.1) L ∧ Submodule.span c.S (L : Set (HdR c.A)) = ⊤ ∧
  (∃ ψ : LinearMap.BilinForm c.S (HdR c.A), IsPolForm (dp0 c.S) (𝟙 _) c.A (t.PP.L.pull c.φ) ψ ∧
    (∀ x, x ∈ L ↔ ∀ y ∈ L, ψ x y ∈ Set.range (algebraMap Γ(X, c.U.1) c.S)) ∧
    (∀ x, x ∈ c.coLie ψ ↔ x ∈ L ∧ x ∈ Fil c.A) ∧ ∀ x ∈ c.coLie ψ, ∀ y ∈ c.coLie ψ, ψ x y = 0) ∧
  (∀ h ∈ L, ∃ v, IsTanAtG t (chart c.U) v ∧ c.HasImage h v) ∧
  (∀ v, IsTanAtG t (chart c.U) v → ∃ h ∈ L, c.HasImage h v) ∧
  (∀ D ∈ logDer s (Scheme.IdealSheafData.vanishingIdeal V.compl) c.U, ∃ D' : Derivation ℤ c.S c.S,
    (∀ r, D' (algebraMap Γ(X, c.U.1) c.S r) = algebraMap Γ(X, c.U.1) c.S (D r)) ∧
      ∀ h ∈ L, ∃ k ∈ L, IsNabla D' h k) ∧
  ∀ (a : 𝓞 E) (f : c.A ⟶ c.A) [IsMonHom f], f.left ≫ c.φ = c.φ ≫ (t.act.act a).left →
    ∀ h ∈ L, push (dp0 c.S) (𝟙 _) f h ∈ L

def IsCanExt {K : Type} [CommRing K] (s : X ⟶ Sp K)
    (L : ∀ c : Chart t V, Submodule Γ(X, c.U.1) (HdR c.A)) : Prop :=
  (∀ c, IsCanLattice s c (L c)) ∧
    ∀ c c' : Chart t V, c'.U.1 ≤ c.U.1 → ∀ (σ : c.S →+* c'.S) (q : c'.A.left ⟶ c.A.left)
      (m : GrpMor (dp0 c.S) (𝟙 _) c.A (dp0 c'.S) (𝟙 _) c'.A σ (spMap σ) q), q ≫ c.φ = c'.φ →
      L c' = Submodule.span Γ(X, c'.U.1) {h' | ∃ h ∈ L c, m.Corr h h'}

end GlobalTheory.LogDR

namespace GlobalTheory.Published

open GlobalTheory.LogDR

def DeRhamCanonicalExtension : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
      ∃ Y : Model Xo c (RingHom.id c.F),
        SmoothOfRelativeDimension Dw.dim Y.s ∧ ReciprocityTheory.AnForm.R.FinalTheorems.Snc (boundary Y) ∧
          HasLogKS Y.t Y.s (interior Y) ∧
          ∃ L : ∀ ch : Chart Y.t (interior Y), Submodule Γ(Y.X, ch.U.1) (HdR ch.A), IsCanExt Y.s L

end GlobalTheory.Published
end
end
