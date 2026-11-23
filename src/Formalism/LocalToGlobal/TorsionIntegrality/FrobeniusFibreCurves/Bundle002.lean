module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle001
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

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)

def WronskLemma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A Bs : MvPowerSeries (Fin 3) K),
    A * pd 2 Bs = Bs * pd 2 A → ev3 A = ev3 Bs → ev3 Bs ≠ 0 → A = Bs

def ShearLemma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A Bs : MvPowerSeries (Fin 3) K),
    A * (pd 1 Bs - pd 2 Bs) = Bs * (pd 1 A - pd 2 A) → ev3 A = ev3 Bs → ev3 Bs ≠ 0 → A = Bs

def TauRule : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (pd 0 (wpDiff P) - pd 1 (wpDiff P)) =
      wpDiff P * (2 + 2 * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
        (atD (dz (sigS P)) - at1 0 (dz (sigS P)) + at1 1 (dz (sigS P))))

def DetRule : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    2 * wp3 P 0 1 * wp3 P 0 2 * wp3 P 1 2 * (pd 1 (det3 P) - pd 2 (det3 P)) =
      det3 P *
        (-(pd 0 (wp3 P 0 1) - pd 1 (wp3 P 0 1)) * wp3 P 0 2 * wp3 P 1 2 +
          (pd 0 (wp3 P 0 2) - pd 2 (wp3 P 0 2)) * wp3 P 0 1 * wp3 P 1 2 +
          2 * (pd 1 (wp3 P 1 2) - pd 2 (wp3 P 1 2)) * wp3 P 0 1 * wp3 P 0 2)

def FrobStickLog : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    det3 P = -2 * vand3 K * fExp (fsE (sigS P))

def FrobStick : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    (at1 0 (sigma P) * at1 1 (sigma P) * at1 2 (sigma P)) ^ 3 * det3 P =
      -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
        (evalSumThree (sigma P) * evalDiffThree 0 1 (sigma P) * evalDiffThree 0 2 (sigma P) * evalDiffThree 1 2 (sigma P))

def FrobStickStar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 s2 : K) (P : PowerSeries K), IsWp g2 g3 P →
    (at1 0 (sgStar s2 P) * at1 1 (sgStar s2 P) * at1 2 (sgStar s2 P)) ^ 3 * det3 P =
      -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
        (evalSumThree (sgStar s2 P) * evalDiffThree 0 1 (sgStar s2 P) * evalDiffThree 0 2 (sgStar s2 P) *
          evalDiffThree 1 2 (sgStar s2 P))

def FIUnit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l i : PowerSeries K), LawLog F l → IsInv l i →
    ∃ n : MvPowerSeries (Fin 2) K, Integral n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      FI F i = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n

def ParThree : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 a1 a3 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    Simeq (par3 F i (phO s2 P l)) 0

def CubeFromPars : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l i f : PowerSeries K), LawLog F l → IsInv l i →
    Simeq (par F i f) 0 → Simeq (par3 F i f) 0 → Simeq (d1 F (cob F f)) 0

def LogSigmaPullbackCocycleJets : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 a1 a3 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    DivAB (cob F (phO s2 P l)) ∧ swap2 (cob F (phO s2 P l)) = cob F (phO s2 P l) ∧
      Simeq (d1 F (cob F (phO s2 P l))) 0 ∧ Simeq (d1 F (swap2 (cob F (phO s2 P l)))) 0 ∧
      ∀ n : ℕ, 3 ≤ n → ‖PowerSeries.constantCoeff ((Dinv l)^[n] (phO s2 P l))‖ ≤ 1

end Formalism.L2.Th1.B
end
end

section

noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)

def SRules : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A kap : K) (w : PowerSeries K), IsW A kap w →
    sW w ^ 2 = w ∧ PowerSeries.constantCoeff (sW w) = 0 ∧ PowerSeries.coeff 1 (sW w) = 1 ∧
      2 * sW w * dz (sW w) = dz w ∧
      dz (sW w) ^ 2 = 1 + PowerSeries.C A * w + PowerSeries.C kap * w ^ 2 ∧
      dz (dz (sW w)) = (PowerSeries.C A + 2 * PowerSeries.C kap * w) * sW w

def ShearTwo : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (h : MvPowerSeries (Fin 2) K),
    pd 0 h = pd 1 h → h = atS (ev0 h)

def SAdd : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A kap : K) (w : PowerSeries K), IsW A kap w →
    atS (sW w) * (1 - MvPowerSeries.C kap * at1 0 w * at1 1 w) =
      at1 0 (sW w) * at1 1 (dz (sW w)) + at1 1 (sW w) * at1 0 (dz (sW w))

def WAdd : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A kap : K) (w : PowerSeries K), IsW A kap w →
    4 * at1 0 w * at1 1 w * (1 - MvPowerSeries.C kap * at1 0 w * at1 1 w) ^ 2 * atS w =
      (at1 0 w * at1 1 (dz w) + at1 1 w * at1 0 (dz w)) ^ 2

def WPrimeU : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 c0 a1 a3 xT yT : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    2 * yT + a1 * xT + a3 = 0 →
    PowerSeries.X * PowerSeries.subst l (dz (wOf (xT + c0) P)) =
      PowerSeries.subst l (wOf (xT + c0) P) *
        (2 * thT ep xT yT - PowerSeries.C a1 * PowerSeries.X)

def GCob : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 c0 a1 a3 xT yT : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    2 * yT + a1 * xT + a3 = 0 → 4 * (xT + c0) ^ 3 - g2 * (xT + c0) - g3 = 0 →
    PowerSeries.subst F (gT ep xT) * LT ep xT yT a1 ^ 2 =
      at1 0 (gT ep xT) * at1 1 (gT ep xT) * F ^ 2 *
        (1 - MvPowerSeries.C (3 * (xT + c0) ^ 2 - g2 / 4) *
          at1 0 (PowerSeries.subst l (wOf (xT + c0) P)) *
          at1 1 (PowerSeries.subst l (wOf (xT + c0) P))) ^ 2

def LDiv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 c0 a1 a3 xT yT : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    TwoHyp g2 g3 c0 a1 a3 xT yT →
    ∃ nu : MvPowerSeries (Fin 2) K, Integral nu ∧ MvPowerSeries.constantCoeff nu = 1 ∧
      LT ep xT yT a1 = F * nu

def BeESim : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 a1 a3 xT yT : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    TwoHyp g2 g3 c0 a1 a3 xT yT →
    Simeq (cob F (phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l))
      (cob F (phO s2 P l))

def CocycleDiffExpEquiv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F H H' : MvPowerSeries (Fin 2) K),
    MvPowerSeries.constantCoeff F = 0 → Integral F → Simeq H H' → Simeq (d1 F H) (d1 F H')

def CubeE : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 a1 a3 xT yT : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → CurveHyp3 F l P ep a1 a3 →
    TwoHyp g2 g3 c0 a1 a3 xT yT →
    let ph' := phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l
    DivAB (cob F ph') ∧ swap2 (cob F ph') = cob F ph' ∧ Simeq (d1 F (cob F ph')) 0 ∧
      Simeq (d1 F (swap2 (cob F ph'))) 0

end Formalism.L2.Th1.B
end
end
