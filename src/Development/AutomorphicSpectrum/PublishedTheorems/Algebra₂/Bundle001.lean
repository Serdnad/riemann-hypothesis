module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
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
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.Bundle002

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open TensorProduct GlobalTheory.PDivGroup

def FarguesExact : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [Algebra ℤ_[p] O], v.Integers O → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : O)}) O → ∀ G : PDivGroup p O,
    ∀ (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n), ζ 1 ≠ 1 →
      ∀ B : O ⊗[ℤ_[p]] G.Tate →ₗ[O] O ⊗[ℤ_[p]] G.dual.Tate →ₗ[O] O,
        (∀ (x : G.Tate) (χ : G.dual.Tate), ∃ a : ℤ_[p], pairing G O x χ = a • muTate O ζ h0 h ∧
          B (1 ⊗ₜ x) (1 ⊗ₜ χ) = algebraMap ℤ_[p] O a) →
        ∀ x, hodgeTateLinear G x = 0 ↔ ∀ y, dlogLinear G y = 0 → B x y = 0

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

def QuotientByFiniteFlatStatement : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left),
    IsAbelianScheme A → L.IsLB → Out.RelAmple A L →
    ∀ (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A), IsFinFlatSub A B h →
    ∃ (A' : Over (Spec (CommRingCat.of R))) (_ : GrpObj A') (L' : LB A'.left) (q : A ⟶ A'),
      IsAbelianScheme A' ∧ L'.IsLB ∧ Out.RelAmple A' L' ∧ IsMonHom q ∧
      IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
        z ≫ q = 1 ↔ ∃ φ : B →ₐ[R] S, spMap φ ≫ h = z

end GlobalTheory.CompanionTheory.Ar.GR
end
end
