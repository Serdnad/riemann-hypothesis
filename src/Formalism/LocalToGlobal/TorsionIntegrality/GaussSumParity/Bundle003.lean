module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle002
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle001
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementJ
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

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog Simeq)

def ChainNonVacuous : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 2 < l → ∀ (ν r0 r1 : ℕ) [NeZero ν],
    ∃ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin ν → MaximalUnramifiedExtension l)
      (U0 Φ : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) ℂ_[l]) (ph : PowerSeries (MaximalUnramifiedExtension l)),
      UnrOK (MaximalUnramifiedExtension l) l σ ∧ CompleteSpace (MaximalUnramifiedExtension l) ∧ (∀ a, ‖(MaximalUnramifiedExtension l).subtype a‖ = ‖a‖) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1)) ∧
      (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ (2 * ν) - 1)) ∧ 2 ≤ 2 * ν ∧ Even (2 * ν) ∧
      (∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l])) ∧
      OwOK (2 * ν) σ om oms ∧ TrDual (2 * ν) σ om oms ∧ IsLawOfLog l F ∧ F1 F be ∧ F2 l σ be ∧
      ¬ Simeq be 0 ∧ Integral U0 ∧ MvPowerSeries.constantCoeff Φ = 0 ∧
      Simeq Φ (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be)) ∧
      Simeq (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l))) be)

end Formalism.L2.Th1.D
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)

def TilInvariantL : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ u : K, u ^ (l ^ d - 1) = 1 →
    ∀ (τ : Type) [Finite τ] (L : ZMod d → MvPowerSeries τ K), ShiftType l σ L →
      Simeq (MvPowerSeries.subst L (MvPowerSeries.subst (torus l u) (beTil (d := d) l σ be0 om oms)))
        (MvPowerSeries.subst L (beTil (d := d) l σ be0 om oms))

def MeanSimeqL : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ (τ : Type) [Finite τ] (L : ZMod d → MvPowerSeries τ K), ShiftType l σ L →
      Simeq (MvPowerSeries.subst L (beMean (d := d) l σ be0 om oms ζ))
        (MvPowerSeries.subst L (beTil (d := d) l σ be0 om oms))

def BiextensionPointsIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
      ∃ Xt : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K,
        (∀ x, MvPowerSeries.constantCoeff (Xt x) = 0 ∧ Integral (Xt x)) ∧
        (∀ x, PowerSeries.subst (Xt x) (lgF K l) =
          if x.1 = false then
            linEL σ (oms x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))
          else linOL σ (om x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))) ∧
        Simeq (∑ ab : Fin N0 × Fin N1, MvPowerSeries.subst
            (fun s => entLog (K := K) l (s, ab.1, ab.2)) (beMean (d := d) l σ be0 om oms ζ))
          (MvPowerSeries.subst Xt (sumE be0))

end Formalism.L2.Th1.D
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def RingAFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    (∀ x ∈ ringA l, ‖x‖ ≤ 1) ∧
    (∀ x ∈ ringA l, ∃ f : ℕ, 0 < f ∧ ∃ y ∈ ringA l, x ^ (l ^ f) - x = (l : ℂ_[l]) * y)

def FrobA : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    ∃ σ0 : ringA l →+* ringA l,
      (∀ ζ : ringA l, (ζ : ℂ_[l]) ∈ muPrime l → σ0 ζ = ζ ^ l) ∧
      ∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y

def FrobAIsom : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (σ0 : ringA l →+* ringA l),
    (∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y) →
    ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖

end Formalism.L2.Th1.D
end
end

section

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog OmOK lamF thetaLog EV alG capG lsG deLoss dSet oddT
  InClass hhS uS sSub)

def ThetaInZIsThetaLog : Prop :=
  ∀ (K0 K : Type) [Field K0] [Field K] (l ν r0 r1 : ℕ) [NeZero ν] (σ : K0 →+* K0) (j : K0 →+* K)
    (om oms : Fin ν → K0) (ϖ : K) (μ : PowerSeries K), 2 ≤ l → ϖ ≠ 0 →
    PowerSeries.constantCoeff μ = 0 →
    (PowerSeries.subst μ (lamF l ϖ) : PowerSeries K) = PowerSeries.X →
    ∀ Tht : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) K,
      thetaInZ (d := 2 * ν) l j σ om oms Tht = thetaLog (conjJ j σ om) (conjJ j σ oms) ϖ μ Tht

def KernelOfF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0]
    [CompleteSpace K0] (σ : K0 →+* K0), UnrOK K0 p σ → (∃ ζ : K0, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K0, F1 F be → F2 p σ be →
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (j : K0 →+* K) (ν r0 r1 : ℕ)
      [NeZero ν], (∀ a, ‖j a‖ = ‖a‖) → (∃ ϖ : K, ϖ ^ (p ^ 2 - 1) = (p : K)) →
    ∀ (om oms : Fin ν → K0), OwOK (2 * ν) σ om oms → TrDual (2 * ν) σ om oms →
    ∀ (U0 Φ : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) K), Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 → Simeq Φ (sumE (MvPowerSeries.map j be)) →
    ∀ (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1) n,
      ‖AddMonoidAlgebra.coeff (frameJet colN hts hp I (thetaInZ (d := 2 * ν) p j σ om oms (mvExp (-Φ) * U0))) n‖ ≤
          (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)))) ∧
      ‖AddMonoidAlgebra.coeff (frameJet colN hts hp I (thetaInZ (d := 2 * ν) p j σ om oms (mvExp (-Φ) * U0))) n‖ ≤
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
          AddMonoidAlgebra.coeff (frameJet colN hts hp I (thetaInZ (d := 2 * ν) p j σ om oms (mvExp (-Φ) * U0)))
            n‖ ≤
          (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))

end Formalism.L2.Th1.D
end
end
