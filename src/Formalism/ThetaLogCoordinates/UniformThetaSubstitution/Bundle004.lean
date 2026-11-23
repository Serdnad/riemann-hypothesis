module

public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle003
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementJ
public import Formalism.GaussJetBounds.Bundle003
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle002
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle001
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

theorem thetaLogIsSubst : ThetaLogIsSubst := by
  intro K _ ν r0 r1 _ om oms ϖ μ Tht hμ

  have hz0 : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (zLin om oms x) = 0 := by
    intro x
    unfold zLin

    rw [map_sum]
    apply Finset.sum_eq_zero
    intro s _
    split_ifs <;> simp
  have hz : ∀ x : Bool × EV ν r0 r1, PowerSeries.HasSubst (zLin om oms x) := fun x =>
    PowerSeries.HasSubst.of_constantCoeff_zero (hz0 x)

  have hs : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (sSub om oms μ x) = 0 := by
    intro x
    unfold sSub
    rw [PowerSeries.constantCoeff_subst (hz x)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases d with _ | d
    · simp [hμ]
    · simp [map_pow, hz0 x]
  have ha : MvPowerSeries.HasSubst (fun x : Bool × EV ν r0 r1 => MvPowerSeries.C ϖ * sSub om oms μ x) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp [hs x])
  have hb : MvPowerSeries.HasSubst (fun y : ZV ν r0 r1 =>
      MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun y => by simp)
  exact MvPowerSeries.subst_comp_subst_apply ha hb Tht

end Formalism.InvariantFactorPaths.G7.Top
end

section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

def GenericExistsK : Prop :=
  ∀ (F σ : Type) [NormedField F] [IsUltrametricDist F] [CharZero F] [Finite σ],
    ∃ (K : Type) (_ : NormedField K), IsUltrametricDist K ∧ CharZero K ∧
      ∃ (φ : F →+* K) (Y : σ → K), (∀ z, ‖φ z‖ = ‖z‖) ∧
        ∀ P : MvPolynomial σ F,
          ‖MvPolynomial.eval₂ φ Y P‖ = ⨆ n : σ →₀ ℕ, ‖AddMonoidAlgebra.coeff P n‖

def GaussBoundNoOperatorGeneric : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K)
    (F : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → (∀ s, ‖u s‖ ≤ 1) → InClass (p : K) (hhS p u) F →
    ∀ n, ‖AddMonoidAlgebra.coeff (frameJet colN hts hp I F) n‖ ≤
      (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
          (fun s => (capG TT colN hts s : ℝ))
          (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) +
        rhoP p * ∑ s, ((alG TT colN hts s : ℝ) + lsG TT colN hts s)))

def GaussBoundArbitraryGeneric : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K)
    (F : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → (∀ s, ‖u s‖ ≤ 1) → InClass (p : K) (hhS p u) F →
    ∀ n, ‖AddMonoidAlgebra.coeff (frameJet colN hts hp I F) n‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
          (fun s => (capG TT colN hts s : ℝ))
          (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
        ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ) +
        rhoP p * ∑ s, ((alG TT colN hts s : ℝ) + lsG TT colN hts s)))

def GaussBK : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 i : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K)
    (F : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → 1 ≤ i → (∀ s, ‖u s‖ ≤ 1) → InClass (p : K) (hhS p u) F →
    ∀ n, ‖(p : K) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
          (if s.val % 2 = 0 then
            min (hts s c) i - ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
          else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
        AddMonoidAlgebra.coeff (frameJet colN hts hp I F) n‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
          (fun s => (capG TT colN hts s : ℝ))
          (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) +
        rhoP p * ∑ s, ((alG TT colN hts s : ℝ) + lsG TT colN hts s)))

def KernelValuationBoundUltrametric : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K) (ϖ : K)
    (Th : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) → (∀ s, ‖u s‖ ≤ 1) →
    InClass (p : K) (hhS p u) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) K)) Th) →
    ∀ n, ‖AddMonoidAlgebra.coeff (frameJet colN hts hp I Th) n‖ ≤
      (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))

def KernelBoundArbitrarySizes : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K) (ϖ : K)
    (Th : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) → (∀ s, ‖u s‖ ≤ 1) →
    InClass (p : K) (hhS p u) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) K)) Th) →
    ∀ n, ‖AddMonoidAlgebra.coeff (frameJet colN hts hp I Th) n‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
        ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ)))

def KernelBK : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (ν r0 r1 i : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K) (ϖ : K)
    (Th : MvPowerSeries (ZV ν r0 r1) K) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → ‖(p : K)‖ = (p : ℝ)⁻¹ → 1 ≤ i → ϖ ^ (p ^ 2 - 1) = (p : K) → (∀ s, ‖u s‖ ≤ 1) →
    InClass (p : K) (hhS p u) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) K)) Th) →
    ∀ n, ‖(p : K) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
          (if s.val % 2 = 0 then
            min (hts s c) i - ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
          else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
        AddMonoidAlgebra.coeff (frameJet colN hts hp I Th) n‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))

def KernelBoundsGeneric : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0]
    [CompleteSpace K0] (σ : K0 →+* K0), UnrOK K0 p σ → (∃ ζ : K0, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K0, BetaHyp p F be →
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (j : K0 →+* K) (ν r0 r1 : ℕ)
      [NeZero ν], (∀ a, ‖j a‖ = ‖a‖) →
    ∀ (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K) (μ : PowerSeries K)
      (U0 Φ : MvPowerSeries (Bool × EV ν r0 r1) K),
      ϖ ^ (p ^ 2 - 1) = (p : K) → OmOK p ν om oms →
      PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X → Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 →
      Simeq Φ (∑ e : EV ν r0 r1, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) K)) (MvPowerSeries.map j be)) →
    ∀ (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1) n,
      ‖AddMonoidAlgebra.coeff (frameJet colN hts hp I (thetaLog om oms ϖ μ (mvExp (-Φ) * U0))) n‖ ≤
          (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)))) ∧
      ‖AddMonoidAlgebra.coeff (frameJet colN hts hp I (thetaLog om oms ϖ μ (mvExp (-Φ) * U0))) n‖ ≤
          (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
            ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ))) ∧
      ∀ i : ℕ, 1 ≤ i →
        ‖(p : K) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
            (if s.val % 2 = 0 then
              min (hts s c) i -
                ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
            else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
          AddMonoidAlgebra.coeff (frameJet colN hts hp I (thetaLog om oms ϖ μ (mvExp (-Φ) * U0)))
            n‖ ≤
          (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))

end Formalism.InvariantFactorPaths.G7
end
end
