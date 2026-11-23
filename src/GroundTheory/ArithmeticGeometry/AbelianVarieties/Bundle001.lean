module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.Nat.Prime.Defs
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
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

section

namespace GroundTheory.Arith.Abelian

noncomputable section

open IsLocalRing

section Congr

variable {F : Type*} [Field F] [DecidableEq F]

def pointCongr {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

theorem pointCongr_some {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) {x y : F}
    (hxy : W₁.toAffine.Nonsingular x y) :
    pointCongr h (.some x y hxy) = .some x y (h ▸ hxy) := by
  subst h
  rfl

end Congr

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

variable [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [(W.map (algebraMap 𝒪 K)).IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

section Good

end Good

end

end GroundTheory.Arith.Abelian
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

section Line

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

theorem exists_line_of_add_eq_zero {x₁ y₁ x₂ y₂ x₃ y₃ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (h₃ : W.toAffine.Nonsingular x₃ y₃)
    (hs : Point.some _ _ h₁ + Point.some _ _ h₂ + Point.some _ _ h₃ = 0) :
    ∃ ℓ ν : F, y₁ = ℓ * x₁ + ν ∧ y₂ = ℓ * x₂ + ν ∧ y₃ = ℓ * x₃ + ν ∧
      x₁ + x₂ + x₃ = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * ℓ * ν - W.a₁ * ν - W.a₃ * ℓ ∧
      x₁ * x₂ * x₃ = ν ^ 2 + W.a₃ * ν - W.a₆ := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := by
    intro hxy
    rw [Point.add_of_Y_eq hxy.1 hxy.2, zero_add] at hs
    exact Point.some_ne_zero _ hs
  set ℓ := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  rw [Point.add_some hxy, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq] at hs
  obtain ⟨hx3, hy3⟩ := hs
  rw [← hℓ] at hx3 hy3
  refine ⟨ℓ, y₁ - ℓ * x₁, by ring, ?_, ?_, ?_⟩
  · by_cases hx : x₁ = x₂
    · subst hx
      have hy := Y_eq_of_Y_ne h₁.1 h₂.1 rfl (fun h => hxy ⟨rfl, h⟩)
      rw [← hy]; ring
    · rw [hℓ, slope_of_X_ne hx]
      have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
      field_simp
      ring
  · rw [← W.toAffine.negY_negY x₃ y₃, ← hy3, ← hx3]
    simp only [addY, negY_negY, negAddY]
    ring
  have e := W.toAffine.addPolynomial_slope h₁.1 h₂.1 hxy
  rw [addPolynomial_eq, Cubic.prod_X_sub_C_eq, neg_inj, Cubic.toPoly_injective,
    Cubic.mk.injEq, hx3] at e
  obtain ⟨-, e2, e3, e4⟩ := e
  rw [← hℓ] at e2 e3 e4
  refine ⟨by linear_combination e2, by linear_combination -e3, by linear_combination e4⟩

end Line

section Counting

variable {G : Type*} [AddCommGroup G] (H : AddSubgroup G)

end Counting

section DVR

open IsLocalRing

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)


section Origin

variable {π : 𝒪} (hπ : Irreducible π)
include hπ





end Origin



end DVR

end

end GroundTheory.Arith.Abelian
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open AddSubgroup

section Def

variable (ℓ : ℕ) (A : Type*) [AddCommGroup A]

variable {ℓ A}

end Def

section Module

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

instance neZero_pow_prime (k : ℕ) : NeZero (ℓ ^ k) := ⟨pow_ne_zero k hℓ.out.ne_zero⟩

end Module

section Lift

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

variable (hcard : ∀ k, Nat.card {P : A // ℓ ^ k • P = 0} = (ℓ ^ k) ^ 2)
include hcard

end Lift

section Basis

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

end Basis

section Curve

variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

end Curve

section Topology

variable {ℓ : ℕ} {A : Type*} [AddCommGroup A]

end Topology

section Action

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

end Action

section Galois

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

end Galois

end GroundTheory.Arith.Abelian
end
