module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.RingTheory.FormalGroup.Basic
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

universe u

namespace Formalism.ELL

def quadDiff {M T : Type u} [AddCommGroup M] [AddCommGroup T] (φ : M → T) (a b : M) : T :=
  φ (a + b) - φ a - φ b

def QuadHyp {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T) : Prop :=
  (∀ a a' b : M, quadDiff φ (a + a') b - quadDiff φ a b - quadDiff φ a' b ∈ N) ∧
  φ 0 ∈ N ∧
  (∀ (α : O) (t : M), φ (α • t) - nrm α • φ t ∈ N) ∧
  (∀ (α : O) (a b : M), quadDiff φ (α • a) b - quadDiff φ a (bar α • b) ∈ N)

def IsoExpand : Prop :=
  ∀ (O S M T : Type u) [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T), QuadHyp N bar nrm φ →
    ∀ (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M),
      (∑ i, φ (∑ e, y e i • t e))
        - ((∑ e, (∑ i, nrm (y e i)) • φ (t e))
            + (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
                quadDiff φ (t e) ((∑ i, bar (y e i) * y e' i) • t e'))) ∈ N

def IsoVanish : Prop :=
  ∀ (O S M T : Type u) [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T), QuadHyp N bar nrm φ →
    ∀ (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M),
      (∀ e e', ∑ i, bar (y e i) * y e' i = 0) → (∀ e, ∑ i, nrm (y e i) = 0) →
        (∑ i, φ (∑ e, y e i • t e)) ∈ N

end Formalism.ELL
end

section

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

def WFixed {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R) : Prop :=
  constantCoeff w = 0 ∧
  w = X ^ 3 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * X * w ^ 2
      + C W.a₆ * w ^ 3

def WSeriesUnique : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R), ∃! w : PowerSeries R, WFixed W w

def WSeriesLead : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R), WFixed W w →
    coeff 0 w = 0 ∧ coeff 1 w = 0 ∧ coeff 2 w = 0 ∧ coeff 3 w = 1

section Points

variable {K : Type u} [Field K] {σ : Type}

def xOf (w : PowerSeries K) (s : MvPowerSeries σ K) : FractionRing (MvPowerSeries σ K) :=
  algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s /
    algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)

def yOf (w : PowerSeries K) (s : MvPowerSeries σ K) : FractionRing (MvPowerSeries σ K) :=
  -1 / algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)

end Points

def WPoint : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∀ (σ : Type) [Finite σ] (s : MvPowerSeries σ K), MvPowerSeries.constantCoeff s = 0 → s ≠ 0 →
      (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
        (xOf w s) (yOf w s)

def WFormalGroup : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∃ F : FormalGroup K,
      (∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F.toPowerSeries ∈
        Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) ∧
      let z₁ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0
      let z₂ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1
      let W' := (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine
      let ℓ := (yOf w z₁ - yOf w z₂) / (xOf w z₁ - xOf w z₂)
      xOf w F.toPowerSeries = W'.addX (xOf w z₁) (xOf w z₂) ℓ ∧
      yOf w F.toPowerSeries = W'.addY (xOf w z₁) (xOf w z₂) (yOf w z₁) ℓ

end Formalism.ELL
end
end
