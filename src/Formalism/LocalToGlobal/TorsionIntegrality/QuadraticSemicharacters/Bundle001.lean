module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Objects

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def psiT (H : Sesq V) (α : V → ℂ) (z y : V) : ℂ :=
  α z * α y * α (z + y) * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ))


open Classical in
def tripleSum (H : Sesq V) (α : V → ℂ) (Λ₁ : AddSubgroup V) (S₂ S₃ : Finset V) : ℂ :=
  by classical exact ∑ z ∈ S₃, ∑ y ∈ S₂, if z + y ∈ Λ₁ then psiT H α z y else 0

def tripleMu (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V) (S₂ S₃ : Finset V) : ℂ :=
  ((Real.sqrt (relIdx Λ₁ Λ₃) / (Real.sqrt (relIdx Λ₁ Λ₂) * Real.sqrt (relIdx Λ₂ Λ₃)) : ℝ) : ℂ)
    * tripleSum H α Λ₁ S₂ S₃

structure TripleData (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V) : Prop where
  herm : IsHerm H
  sd₁ : IsSelfDual H Λ₁
  sd₂ : IsSelfDual H Λ₂
  sd₃ : IsSelfDual H Λ₃
  sc₁ : IsSemiChar H Λ₁ α
  sc₂ : IsSemiChar H Λ₂ α
  sc₃ : IsSemiChar H Λ₃ α
  i₁₂ : relIdx Λ₁ Λ₂ ≠ 0
  i₂₁ : relIdx Λ₂ Λ₁ ≠ 0
  i₁₃ : relIdx Λ₁ Λ₃ ≠ 0
  i₃₁ : relIdx Λ₃ Λ₁ ≠ 0
  i₂₃ : relIdx Λ₂ Λ₃ ≠ 0
  i₃₂ : relIdx Λ₃ Λ₂ ≠ 0

end Objects

def TripleFormula : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → ∀ S₂ S₃ : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ →
    ∀ F ∈ fixedBy H α Λ₁, ∀ v,
      inter H α Λ₂ Λ₃ (inter H α Λ₁ Λ₂ F) v = tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃ * inter H α Λ₁ Λ₃ F v

def PsiQuadratic : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ →
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ z' ∈ Λ₃, ∀ y' ∈ Λ₂, z' + y' ∈ Λ₁ →
      psiT H α (z + z') (y + y') = psiT H α z y * psiT H α z' y'
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H y z' : ℂ))) ∧
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ k : ℕ, psiT H α (k • z) (k • y) = psiT H α z y ^ (k ^ 2)) ∧
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ‖psiT H α z y‖ = 1) ∧
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ u' ∈ Λ₁ ⊓ Λ₃, ∀ u ∈ Λ₁ ⊓ Λ₂, ∀ t ∈ Λ₂ ⊓ Λ₃,
      psiT H α (z + u' + t) (y + u - t) = psiT H α z y)

structure IsQuadFn0 {M : Type*} [AddCommGroup M] (φ : M → ℂ) (b : M → M → ℂ) : Prop where
  add : ∀ x y, φ (x + y) = φ x * φ y * b x y
  left : ∀ x y z, b (x + y) z = b x z * b y z
  sq : ∀ (k : ℕ) (x : M), φ (k • x) = φ x ^ (k ^ 2)
  ne : ∀ x, φ x ≠ 0

def GaussDegenerate : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (φ : M → ℂ) (b : M → M → ℂ), IsQuadFn0 φ b →
    ∑ x, φ x ≠ 0 → ∃ r : ℝ, 0 < r ∧ (∑ x, φ x) ^ 8 = (r : ℂ)

def TripleSumEighth : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → ∀ S₂ S₃ : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ →
    tripleSum H α Λ₁ S₂ S₃ ≠ 0 → ∃ r : ℝ, 0 < r ∧ tripleSum H α Λ₁ S₂ S₃ ^ 8 = (r : ℂ)

def TripleConj : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → ∀ S₂ S₃ S₂' S₃' : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ →
    IsReps Λ₁ Λ₃ S₃' → IsReps Λ₃ Λ₂ S₂' →
    tripleMu H α Λ₁ Λ₃ Λ₂ S₃' S₂' = conj (tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃)

def TripleEighth : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → (∃ F ∈ fixedBy H α Λ₁, F ≠ 0) →
    ∀ S₂ S₃ : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ → tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃ ^ 8 = 1

end Formalism.L2.Th1.H
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Objects

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def cayC (Ae : V ≃ₗ[ℂ] V) (x : V) : V := Ae.symm x - (1 / 2 : ℂ) • x

def phiC (H : Sesq V) (α : V → ℂ) (Ae : V ≃ₗ[ℂ] V) (x : V) : ℂ :=
  α x * Complex.exp (-(Real.pi : ℂ) * H (cayC Ae x) x)

def bC (H : Sesq V) (Ae : V ≃ₗ[ℂ] V) (x x' : V) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H (Ae.symm x) x' : ℂ))

def latA (Λ : AddSubgroup V) (δ Ae : V ≃ₗ[ℂ] V) : AddSubgroup V :=
  imgLat (Ae : V →ₗ[ℂ] V) (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ)

structure UnitaryData (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V) : Prop where
  herm : IsHerm H
  pos : IsPosDef H
  selfDual : IsSelfDual H Λ
  semi : IsSemiChar H Λ α
  isom : IsIsom H H (δ : V →ₗ[ℂ] V)
  semi' : IsSemiChar H (imgLat (δ : V →ₗ[ℂ] V) Λ) α
  inv : ∀ x ∈ Λ, α (δ x) = α x
  idx₁ : relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ ≠ 0
  idx₂ : relIdx Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) ≠ 0
  cay : ∀ x, Ae x = x - δ.symm x

def gaussC (H : Sesq V) (α : V → ℂ) (Ae : V ≃ₗ[ℂ] V) (S : Finset V) : ℂ :=
  ((Real.sqrt S.card : ℝ) : ℂ)⁻¹ * ∑ x ∈ S, phiC H α Ae x

def AtMostLine {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Sesq V) (α : V → ℂ)
    (Λ : AddSubgroup V) : Prop :=
  ∀ θ ∈ Th H α Λ, θ ≠ 0 → ∀ F ∈ Th H α Λ, ∃ c : ℂ, F = c • θ

end Objects

def UnitaryIndex : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (Λ : AddSubgroup V) (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V), IsLat Λ → UnitaryData H Λ α δ Ae →
    latA Λ δ Ae ≤ Λ ∧
    (relIdx (latA Λ δ Ae) Λ : ℝ)
      = (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) * ‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ ^ 2

def PhiBasic : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ)
    (δ Ae : V ≃ₗ[ℂ] V), UnitaryData H Λ α δ Ae →
    (∀ x y, H (cayC Ae x) y = -H x (cayC Ae y)) ∧ (∀ x, (H (cayC Ae x) x).re = 0) ∧
    (∀ x ∈ Λ, ‖phiC H α Ae x‖ = 1) ∧
    ∀ x ∈ Λ, ∀ y ∈ latA Λ δ Ae, phiC H α Ae (x + y) = phiC H α Ae x

structure IsQuadFn {M : Type*} [AddCommGroup M] (φ : M → ℂ) (b : M → M → ℂ) : Prop where
  add : ∀ x y, φ (x + y) = φ x * φ y * b x y
  left : ∀ x y z, b (x + y) z = b x z * b y z
  sq : ∀ (k : ℕ) (x : M), φ (k • x) = φ x ^ (k ^ 2)
  ne : ∀ x, φ x ≠ 0
  nondeg : ∀ x, (∀ y, b x y = 1) → x = 0

def GaussEighth : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (φ : M → ℂ) (b : M → M → ℂ), IsQuadFn φ b →
    (∑ x, φ x) ^ 8 = (Fintype.card M : ℂ) ^ 4

def UnitaryGauss : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ)
    (δ Ae : V ≃ₗ[ℂ] V), UnitaryData H Λ α δ Ae → ∀ S : Finset V, IsReps (latA Λ δ Ae) Λ S →
    gaussC H α Ae S ^ 8 = 1

def DetCayley : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsHerm H → IsPosDef H →
    ∀ δ Ae : V ≃ₗ[ℂ] V, IsIsom H H (δ : V →ₗ[ℂ] V) → (∀ x, Ae x = x - δ.symm x) →
    conj (LinearMap.det (Ae : V →ₗ[ℂ] V))
      = (-1) ^ Module.finrank ℂ V * LinearMap.det (δ : V →ₗ[ℂ] V) * LinearMap.det (Ae : V →ₗ[ℂ] V)

def UnitaryConstant : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (Λ : AddSubgroup V) (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V), IsLat Λ → UnitaryData H Λ α δ Ae →
    AtMostLine H α Λ → ∀ S : Finset V, IsReps (latA Λ δ Ae) Λ S → ∀ θ ∈ Th H α Λ,
      pullInv δ θ = ((‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V)
        * gaussC H α Ae S) • inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ

def UnitaryEighth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (Λ : AddSubgroup V) (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V), IsLat Λ → UnitaryData H Λ α δ Ae →
    AtMostLine H α Λ → ∀ θ ∈ Th H α Λ, θ ≠ 0 → ∀ c : ℂ,
      pullInv δ θ = c • inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ →
      c ^ 8 = LinearMap.det (δ : V →ₗ[ℂ] V) ^ 4

end Formalism.L2.Th1.H
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

def InterClass : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ₂ α → ∀ F ∈ fixedBy H α Λ₁, ∀ x ∈ Λ₂, ∀ y ∈ Λ₂, y ∈ Λ₁ → ∀ z,
      α (x + y) * opU H (x + y) F z = α x * opU H x F z

def RepsExist : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Λ₁ Λ₂ : AddSubgroup V), relIdx Λ₁ Λ₂ ≠ 0 →
    (∃ S : Finset V, IsReps Λ₁ Λ₂ S) ∧ ∀ S : Finset V, IsReps Λ₁ Λ₂ S → S.card = relIdx Λ₁ Λ₂

def InterReps : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ₂ α → ∀ F ∈ fixedBy H α Λ₁, ∀ S : Finset V, IsReps Λ₁ Λ₂ S → ∀ z,
      inter H α Λ₁ Λ₂ F z = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * sumU H α S F z

def InterFixed : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ₂ α → relIdx Λ₁ Λ₂ ≠ 0 → ∀ F ∈ fixedBy H α Λ₁, inter H α Λ₁ Λ₂ F ∈ fixedBy H α Λ₂

def InterTh : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsHerm H →
    ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ), IsSemiChar H Λ₂ α → relIdx Λ₁ Λ₂ ≠ 0 →
      ∀ F ∈ Th H α Λ₁, inter H α Λ₁ Λ₂ F ∈ Th H α Λ₂

def IndexEq : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → relIdx Λ₁ Λ₂ = relIdx Λ₂ Λ₁

def CharSum : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → ∀ S : Finset V, IsReps Λ₂ Λ₁ S → ∀ y ∈ Λ₂,
      ∑ x ∈ S, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ))
        = by classical exact if y ∈ Λ₁ then (S.card : ℂ) else 0

def InterInv : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → IsSemiChar H Λ₁ α → IsSemiChar H Λ₂ α →
    relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → ∀ F ∈ fixedBy H α Λ₁, ∀ z,
      inter H α Λ₂ Λ₁ (inter H α Λ₁ Λ₂ F) z = F z

def LineTransport : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsHerm H →
    ∀ (Λ₁ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsSelfDual H Λ₁ → IsSelfDual H Λ₂ → IsSemiChar H Λ₁ α → IsSemiChar H Λ₂ α →
    relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → ∀ θ₁ ∈ Th H α Λ₁, θ₁ ≠ 0 → (∀ F ∈ Th H α Λ₁, ∃ c : ℂ, F = c • θ₁) →
      inter H α Λ₁ Λ₂ θ₁ ≠ 0 ∧ ∀ F ∈ Th H α Λ₂, ∃ c : ℂ, F = c • inter H α Λ₁ Λ₂ θ₁

def ThIsom : Prop :=
  ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] [FiniteDimensional ℂ W] (H : Sesq V) (H' : Sesq W) (g : V ≃ₗ[ℂ] W),
    IsIsom H H' (g : V →ₗ[ℂ] W) → ∀ (Λ : AddSubgroup V) (α' : W → ℂ) (G : W → ℂ),
      G ∈ Th H' α' (imgLat (g : V →ₗ[ℂ] W) Λ) ↔ (fun v => G (g v)) ∈ Th H (fun v => α' (g v)) Λ

end Formalism.L2.Th1.H
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

def OpUMul : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (x y : V) (F : V → ℂ) (z : V),
    opU H x (opU H y F) z
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) * opU H (x + y) F z

def OpUComm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (F : V → ℂ) (z : V),
    opU H 0 F z = F z ∧ ∀ x y : V,
    opU H x (opU H y F) z
      = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ)) * opU H y (opU H x F) z

def OpUIsom : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W)
    (g : V →ₗ[ℂ] W), IsIsom H H' g → ∀ (x : V) (G : W → ℂ) (z : V),
    opU H x (fun v => G (g v)) z = opU H' (g x) G (g z)

def PullOpU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (δ : V ≃ₗ[ℂ] V), IsIsom H H (δ : V →ₗ[ℂ] V) →
    ∀ (x : V) (F : V → ℂ) (z : V), pullInv δ (opU H x F) z = opU H (δ x) (pullInv δ F) z

def SemiCharBasic : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ α → α 0 = 1 ∧ (∀ x ∈ Λ, α (-x) = α x) ∧ Λ ≤ dualLat H Λ

def SemiHom : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ α → ∀ x ∈ Λ, ∀ y ∈ Λ, ∀ (F : V → ℂ) (z : V),
      α x * opU H x (fun v => α y * opU H y F v) z = α (x + y) * opU H (x + y) F z

def OpUAnalytic : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V) (x : V)
    (F : V → ℂ), AnalyticOnNhd ℂ F Set.univ → AnalyticOnNhd ℂ (opU H x F) Set.univ

def MatHBasic : Prop :=
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ),
    (∀ z w : n → ℂ, matH h z w = ∑ i, ∑ j, z i * h i j * conj (w j)) ∧ (h.IsHermitian → IsHerm (matH h))

def StdHBasic : Prop :=
  ∀ (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n],
    (∀ z w : n → ℂ, stdH L n z w = ∑ i, Formalism.L2.Th1.F.herm L (z i) (w i)) ∧ IsHerm (stdH L n) ∧
      IsPosDef (stdH L n)

def OpUStd : Prop :=
  ∀ (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] (x : n → ℂ) (f : n → ℂ → ℂ) (z : n → ℂ),
    opU (stdH L n) x (prodFn f) z = ∏ i, Formalism.L2.Th1.F.opU L (x i) (f i) (z i)

def OpUBlk4 : Prop :=
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ),
    (∀ z w : Fin 4 × n → ℂ, matH (blk4 h) z w = ∑ a, matH h (slice a z) (slice a w)) ∧
    ∀ (x : Fin 4 × n → ℂ) (θ : Fin 4 → (n → ℂ) → ℂ) (z : Fin 4 × n → ℂ),
      opU (matH (blk4 h)) x (fun v => ∏ a, θ a (slice a v)) z = ∏ a, opU (matH h) (slice a x) (θ a) (slice a z)

end Formalism.L2.Th1.H
end
end
