module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle001
public import Formalism.FormalGroupLog.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.Bundle001
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle001

@[expose] public section

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.L2.Th1.F (MulStable)
open Formalism.L2.Th1.E (Unif ptW inW px IntCurve OneUnit GaussOne)

def QuadTwoAdic : Prop :=
  ∀ T N : ℤ, Odd T → Even N →
    ∃ b b' : ℤ_[2], b + b' = (T : ℤ_[2]) ∧ b * b' = (N : ℤ_[2]) ∧ ‖b‖ = 1 ∧ ‖b'‖ < 1

def RootsTwoAdic : Prop :=
  ∀ (ι : ℂ ≃+* ℂ_[2]) (α : ℂ) (T N : ℤ), α + conj α = (T : ℂ) → α * conj α = (N : ℂ) → Odd T →
    Even N → ∃ b b' : ℤ_[2], ‖b‖ = 1 ∧ ‖b'‖ < 1 ∧
      ((ι α = ((b : ℚ_[2]) : ℂ_[2]) ∧ ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2])) ∨
        (ι α = ((b' : ℚ_[2]) : ℂ_[2]) ∧ ι (conj α) = ((b : ℚ_[2]) : ℂ_[2])))

def ThetaZeroTwoTrace : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α ω₀ : ℂ) (T N : ℤ), MulStable L α → α + conj α = (T : ℂ) →
    α * conj α = (N : ℂ) → Odd T → Even N →
    ω₀ ∈ L.lattice → α * (ω₀ / 2) ∉ L.lattice → conj α * (ω₀ / 2) ∉ L.lattice →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) ∧
      ∀ (s : ℂ) (M : ℕ), 0 < M → ¬ 2 ∣ M → (M : ℂ) * s ∈ L.lattice →
        GaussOne (inW 2 ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

def ThetaZeroTwoCM : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → Formalism.L2.Th1.CM.HasCMBy d L →
    ∀ (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W → ‖W.a₁‖ = 1 →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → Formalism.L2.Th1.CM.omegaK d * (ω₀ / 2) ∉ L.lattice →
    conj (Formalism.L2.Th1.CM.omegaK d) * (ω₀ / 2) ∉ L.lattice →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) ∧
      ∀ (s : ℂ) (M : ℕ), 0 < M → ¬ 2 ∣ M → (M : ℂ) * s ∈ L.lattice →
        GaussOne (inW 2 ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

end Formalism.L2.Th1.B
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr IsLogPair mulBy EndInt PhNormAt IsBinomScalar)
open Formalism.L2.Th1.A (fgl iSer logSer expSer wpReg g₂ g₃ IntModel)

def Th0Isogeny : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 s2 c0 xT al S : K) (P : PowerSeries K)
    (ι : Type) [Fintype ι] (c : ι → K) (wp wm : ι → PowerSeries K),
    IsWp g2 g3 P → 4 * (xT + c0) ^ 3 - g2 * (xT + c0) - g3 = 0 →
    IsFibreZ P (PowerSeries.C (xT + c0) +
      PowerSeries.C (3 * (xT + c0) ^ 2 - g2 / 4) * wOf (xT + c0) P) c wp wm al S →
    (al ^ 2 - 2 * (Fintype.card ι : K)) * s2 = S →
    PowerSeries.rescale al (thTw g2 s2 c0 xT P) * wpShift P (xT + c0) ^ Fintype.card ι =
      thTw g2 s2 c0 xT P ^ (2 * Fintype.card ι) * ∏ Q, wpShift P (c Q)

def PhENorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 xT al albar S : K)
    (P l linv i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K)
    (ι : Type) [Fintype ι] (xQ : ι → K) (wp wm : ι → PowerSeries K),
    IsWp g2 g3 P → 4 * (xT + c0) ^ 3 - g2 * (xT + c0) - g3 = 0 → IsLogPair l linv →
    CurveHyp F i l P ep c0 → ‖xT‖ ≤ 1 → (∀ Q, ‖xQ Q‖ ≤ 1) →
    IsFibreZ P (PowerSeries.C (xT + c0) +
      PowerSeries.C (3 * (xT + c0) ^ 2 - g2 / 4) * wOf (xT + c0) P)
      (fun Q => xQ Q + c0) wp wm al S →
    al * albar = 2 * (Fintype.card ι : K) → al * (al - albar) * s2 = S →
    PhNormAt (unitBall K) l linv (phTw g2 s2 c0 xT P l) al albar

def ThetaZeroVanishing : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (g2 g3 s2 c0 a1 a3 xT yT al albar S : K)
    (P l linv i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K)
    (ι : Type) [Fintype ι] (xQ : ι → K) (wp wm : ι → PowerSeries K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → IsLogPair l linv → CurveHyp F i l P ep c0 →
    CurveHyp3 F l P ep a1 a3 → TwoHyp g2 g3 c0 a1 a3 xT yT → (∀ Q, ‖xQ Q‖ ≤ 1) →
    IsFibreZ P (PowerSeries.C (xT + c0) +
      PowerSeries.C (3 * (xT + c0) ^ 2 - g2 / 4) * wOf (xT + c0) P)
      (fun Q => xQ Q + c0) wp wm al S →
    al * albar = 2 * (Fintype.card ι : K) → al * (al - albar) * s2 = S →
    EndInt (unitBall K) l linv al → al ∈ closure (Set.range (fun n : ℤ => (n : K))) →
    al ≠ 0 → al ≠ albar → albar ≠ 1 →
    IsBinomScalar (unitBall K) (al * (al - albar))⁻¹ →
    IsBinomScalar (unitBall K) (al * (1 - albar))⁻¹ →
    Simeq (ι := Unit) (phTw g2 s2 c0 xT P l) 0 ∧
      PowerSeries.constantCoeff (PowerSeries.subst l (thTw g2 s2 c0 xT P)) = 1 ∧
      Integral (ι := Unit) (PowerSeries.subst l (thTw g2 s2 c0 xT P))

def TwoAdicScalars : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [NormedAlgebra ℚ_[2] K]
    (F : MvPowerSeries (Fin 2) K) (l linv : PowerSeries K) (b b' : ℤ_[2]),
    LawLog F l → IsLogPair l linv → ‖b‖ = 1 → ‖b'‖ < 1 →
    let al : K := algebraMap ℚ_[2] K (b : ℚ_[2])
    let albar : K := algebraMap ℚ_[2] K (b' : ℚ_[2])
    EndInt (unitBall K) l linv al ∧ al ∈ closure (Set.range (fun n : ℤ => (n : K))) ∧
      al ≠ 0 ∧ al ≠ albar ∧ albar ≠ 1 ∧
      IsBinomScalar (unitBall K) (al * (al - albar))⁻¹ ∧
      IsBinomScalar (unitBall K) (al * (1 - albar))⁻¹

end Formalism.L2.Th1.B
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)
open Formalism.L2.Th1.E (Unif ptW inW px py IntCurve OneUnit)

def IsHalfFibre (L : PeriodPair) (α t : ℂ) (Sq : Finset ℂ) : Prop :=
  (∀ Q ∈ Sq, α * Q - t ∈ L.lattice ∧ 2 * Q ∉ L.lattice) ∧
  (∀ Q ∈ Sq, ∀ Q' ∈ Sq, (Q - Q' ∈ L.lattice ∨ Q + Q' ∈ L.lattice) → Q = Q') ∧
  (∀ z, α * z - t ∈ L.lattice → ∃ Q ∈ Sq, z - Q ∈ L.lattice ∨ z + Q ∈ L.lattice)

def HalfFibreExists : Prop :=
  ∀ (L : PeriodPair) (α ω₀ : ℂ), α ≠ 0 → MulStable L α → ω₀ ∈ L.lattice →
    (∀ z, α * z - ω₀ / 2 ∈ L.lattice → 2 * z ∉ L.lattice) →
    ∃ Sq : Finset ℂ, IsHalfFibre L α (ω₀ / 2) Sq

def FibreZInstance : Prop :=
  ∀ (L : PeriodPair) (α ω₀ : ℂ) (S Sq : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice → IsHalfFibre L α (ω₀ / 2) Sq →
    2 * Sq.card = S.card + 1 ∧
    IsFibreZ (pSeries L) (taylor0 fun z => L.weierstrassP (z + ω₀ / 2))
      (fun Q : Sq => L.weierstrassP (Q : ℂ))
      (fun Q : Sq => taylor0 fun z => L.weierstrassP (z + (Q : ℂ)))
      (fun Q : Sq => taylor0 fun z => L.weierstrassP (z - (Q : ℂ)))
      α (∑ P ∈ S, L.weierstrassP P)

def HalfShiftSeries : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    (taylor0 fun z => L.weierstrassP (z + ω₀ / 2)) =
      PowerSeries.C (L.weierstrassP (ω₀ / 2)) +
        PowerSeries.C (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) *
          wOf (L.weierstrassP (ω₀ / 2)) (pSeries L)

def FibreMap : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
    (P tr : PowerSeries K) (ι : Type) [Fintype ι] (c : ι → K) (wp wm : ι → PowerSeries K) (al S : K),
    IsFibreZ P tr c wp wm al S →
    IsFibreZ (PowerSeries.map j P) (PowerSeries.map j tr) (fun Q => j (c Q))
      (fun Q => PowerSeries.map j (wp Q)) (fun Q => PowerSeries.map j (wm Q)) (j al) (j S)

def ThetaZeroTwoAnalytic : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W →
    Formalism.L2.Th1.A.IntModel W → ∀ (α ω₀ : ℂ) (b b' : ℤ_[2]), α ≠ 0 → MulStable L α →
    ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 → ‖b'‖ < 1 →
    (∀ z, α * z - ω₀ / 2 ∈ L.lattice → 2 * z ∉ L.lattice) →
    ‖px W (ptW 2 L ι W (ω₀ / 2))‖ ≤ 1 →
    (∀ z, α * z - ω₀ / 2 ∈ L.lattice → ‖px W (ptW 2 L ι W z)‖ ≤ 1) →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2)))

end Formalism.L2.Th1.B
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)
open Formalism.L2.Th1.E (Unif ptW inW px py IntCurve OneUnit GaussOne)


open Classical in
def TwoTorsionKernelUnique : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K), IntCurve W →
    ‖(2 : K)‖ = 2⁻¹ → ‖W.a₁‖ = 1 →
    ∀ P Q : W.toAffine.Point, P ≠ 0 → P + P = 0 → InFormalGroupPoints P →
      ‖px W P‖ = 4 ∧ (Q ≠ 0 → Q + Q = 0 → InFormalGroupPoints Q → P = Q)



open Classical in
def TorsBound : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K), IntCurve W →
    ‖(2 : K)‖ = 2⁻¹ → ∀ (P : W.toAffine.Point) (k : ℕ), (2 ^ k) • P = 0 → P + P ≠ 0 →
      ‖px W P‖ < 4

def KapNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.A.IntModel W → ‖(2 : K)‖ = 2⁻¹ → ∀ x : K,
      (‖x‖ = 4 → ‖3 * (x + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4‖ = 16) ∧
      (‖x‖ < 4 → ‖3 * (x + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4‖ < 16)

def KappaSum : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ∑ P ∈ S, (3 * L.weierstrassP P ^ 2 - L.g₂ / 4) = (α ^ 4 - 1) * L.g₂ / 20

def KernelIntegral : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α : ℂ) (b : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 →
    ∀ t, α * t ∈ L.lattice → t ∉ L.lattice → ¬ InFormalGroupPoints (ptW 2 L ι W t)

def KernelStableUnderMultiplier : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α : ℂ) (b : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 →
    ∀ t, InFormalGroupPoints (ptW 2 L ι W t) → InFormalGroupPoints (ptW 2 L ι W (α * t))

def PointsTwoFinal : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α ω₀ : ℂ) (b b' : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 → ‖b'‖ < 1 →
    ω₀ ∈ L.lattice → conj α * (ω₀ / 2) ∉ L.lattice →
    ¬ InFormalGroupPoints (ptW 2 L ι W (ω₀ / 2)) ∧
      (∀ Q, α * Q - ω₀ / 2 ∈ L.lattice → ¬ InFormalGroupPoints (ptW 2 L ι W Q)) ∧
      (∀ z, α * z - ω₀ / 2 ∈ L.lattice → 2 * z ∉ L.lattice)

def ThetaZeroAtTwo : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α ω₀ : ℂ) (b b' : ℤ_[2]), α ≠ 0 → MulStable L α →
    ι α = ((b : ℚ_[2]) : ℂ_[2]) → ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2]) → ‖b‖ = 1 → ‖b'‖ < 1 →
    ω₀ ∈ L.lattice → conj α * (ω₀ / 2) ∉ L.lattice →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) ∧
      ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ 2 ∣ N → (N : ℂ) * s ∈ L.lattice →
        GaussOne (inW 2 ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

end Formalism.L2.Th1.B
end
end
