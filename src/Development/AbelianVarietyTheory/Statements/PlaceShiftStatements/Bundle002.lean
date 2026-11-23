module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.LocalToGlobal.CyclotomicLocalNorms.NormSubToZModPowVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions.Loc

namespace GlobalTheory.HTLink

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

abbrev EtV {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) : Type 1 :=
  GlobalTheory.EtC.HQ l (GlobalTheory.EtC.sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) q)) n 0

def etAct {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (σ : ↥(GK K)) : EtV q n →ₗ[ℚ_[l]] EtV q n :=
  GlobalTheory.EtC.galHQ l (PadicAlgCl l) q n 0 (IntermediateField.fixingSubgroupEquiv K.1 σ)

def etPull {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {f : X' ⟶ X} (hf : f ≫ q = q') (n : ℕ) :
    EtV q n →ₗ[ℚ_[l]] EtV q' n :=
  GlobalTheory.EtC.pullHQ l (GlobalTheory.EtC.sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) q' f hf)) n 0

abbrev HodgeV {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (a : Fin (n + 1)) : Type :=
  GlobalTheory.HodgeCoh.hodgeH q a (n - a)

def toC (K : FinExt l) : ↥K.1 →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp (algebraMap ↥K.1 (PadicAlgCl l))

def chiPow (σ : GQ l) (i : ℤ) : ℂ_[l] := (algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l])) ^ i

structure Frame {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) : Type 1 where

  d : ℕ

  b : Module.Basis (Fin d) ℚ_[l] (EtV q n)

  e : Fin (n + 1) → ℕ

  c : ∀ a, Module.Basis (Fin (e a)) ↥K.1 (HodgeV q n a)

namespace Frame

variable {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {n : ℕ}

abbrev Col (F : Frame q n) : Type := Σ a : Fin (n + 1), Fin (F.e a)

def rho (F : Frame q n) (σ : ↥(GK K)) : Matrix (Fin F.d) (Fin F.d) ℂ_[l] :=
  (LinearMap.toMatrix F.b F.b (etAct q n σ)).map (algebraMap ℚ_[l] ℂ_[l])

def etMat (F : Frame q n) (F' : Frame q' n) {f : X' ⟶ X} (hf : f ≫ q = q') : Matrix (Fin F'.d) (Fin F.d) ℂ_[l] :=
  (LinearMap.toMatrix F.b F'.b (etPull hf n)).map (algebraMap ℚ_[l] ℂ_[l])

def hodgeMat (F : Frame q n) (F' : Frame q' n) {f : X' ⟶ X} (hf : f ≫ q = q') : Matrix F'.Col F.Col ℂ_[l] :=
  (Matrix.blockDiagonal' fun a : Fin (n + 1) =>
    LinearMap.toMatrix (F.c a) (F'.c a) (GlobalTheory.HodgeCoh.hodgePull hf a (n - a))).map (toC K)

def IsHT (F : Frame q n) (Φ : Matrix (Fin F.d) F.Col ℂ_[l]) : Prop :=
  (∃ Ψ : Matrix F.Col (Fin F.d) ℂ_[l], Φ * Ψ = 1 ∧ Ψ * Φ = 1) ∧
    ∀ σ : ↥(GK K), F.rho σ * Φ.map (Formalism.Per.σC (σ : GQ l)) =
      Φ * Matrix.diagonal fun j : F.Col => chiPow (σ : GQ l) (-((j.1 : ℕ) : ℤ))

end Frame

universe u

structure HodgeFam (K : FinExt l) : Type (max 1 (u + 1)) where

  H : ∀ {X : Scheme.{0}}, (X ⟶ Sp ↥K.1) → ∀ n : ℕ, Fin (n + 1) → Type u

  [add : ∀ {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (a : Fin (n + 1)), AddCommGroup (H q n a)]

  [mod : ∀ {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (n : ℕ) (a : Fin (n + 1)), Module ↥K.1 (H q n a)]

  pull : ∀ {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {f : X' ⟶ X}, f ≫ q = q' →
    ∀ (n : ℕ) (a : Fin (n + 1)), H q n a →ₗ[↥K.1] H q' n a

attribute [instance] HodgeFam.add HodgeFam.mod

end GlobalTheory.HTLink

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

def FamUnif : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra ℂ B] [Algebra.FiniteType ℂ B] (𝒜 : Over (Sp B)) [GrpObj 𝒜] (g : ℕ),
    IsAbelianScheme 𝒜 → SmoothOfRelativeDimension g 𝒜.hom →
    ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (y : (I → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen U → 0 ∈ U →
      (∀ b, DifferentiableOn ℂ (fun z ↦ y z b) U) →
    ∀ (A : (I → ℂ) → Over (Sp ℂ)) [∀ z, GrpObj (A z)] (φ : ∀ z, (A z).left ⟶ 𝒜.left),
      (∀ z, IsGrpPullback (A z) 𝒜 (spMap (y z : B →+* ℂ)) (φ z)) →
    ∀ (L : ∀ z, LB (A z).left), (∀ z, (L z).IsLB) →
    ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (φ₀ : A₀.left ⟶ 𝒜.left), IsGrpPullback A₀ 𝒜 (spMap (y 0 : B →+* ℂ)) φ₀ →
    ∀ (L₀ : LB A₀.left) (u₀ : HolUnif A₀ L₀ g),
    ∃ (r : ℝ) (u : ∀ z, HolUnif (A z) (L z) g) (τ : ∀ z, u₀.Λ ≃+ (u z).Λ), 0 < r ∧ Metric.ball 0 r ⊆ U ∧
      IsHolTo (Metric.ball (0 : I → ℂ) r ×ˢ (Set.univ : Set (Fin g → ℂ)))
        (fun q ↦ (show Sp ℂ ⟶ (A q.1).left from ((u q.1).ex q.2).left) ≫ φ q.1) ∧
      (∃ W : 𝒜.left.Opens, IsAffineOpen W ∧ ∀ z ∈ Metric.ball (0 : I → ℂ) r,
        ⊤ ≤ ((show Sp ℂ ⟶ (A z).left from ((u z).ex 0).left) ≫ φ z) ⁻¹ᵁ W) ∧
      (∀ w, ((u 0).ex w).left ≫ φ 0 = (u₀.ex w).left ≫ φ₀) ∧ (∀ x, (τ 0 x : Fin g → ℂ) = x) ∧
      (∀ x, DifferentiableOn ℂ (fun z ↦ (τ z x : Fin g → ℂ)) (Metric.ball 0 r)) ∧
      ∀ (α : 𝒜 ⟶ 𝒜) [IsMonHom α] (M₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
        (∀ w, (u₀.ex (M₀ w)).left ≫ φ₀ = (u₀.ex w).left ≫ φ₀ ≫ α.left) →
        ∀ z ∈ Metric.ball (0 : I → ℂ) r, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
          (∀ w, ((u z).ex (M w)).left ≫ φ z = ((u z).ex w).left ≫ φ z ≫ α.left) ∧
          ∀ x x' : u₀.Λ, (x' : Fin g → ℂ) = M₀ x → (τ z x' : Fin g → ℂ) = M (τ z x)

end GlobalTheory.PeriodFamily
end
end
