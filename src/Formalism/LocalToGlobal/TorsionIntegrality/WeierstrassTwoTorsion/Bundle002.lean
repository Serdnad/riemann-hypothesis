module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle001
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

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

def WpPrimeInU : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    X ^ 3 * (-2 + logSer W ^ 3 * (derivative (wpReg W)).subst (logSer W)) =
      logSer W ^ 3 * (-2 * xS W + C W.a₁ * X * xS W + C W.a₃ * X ^ 3)

def BridgeCurve3 : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.CurveHyp3 (fgl W) (logSer W) (wpReg W) (xS W) W.a₁ W.a₃

end Formalism.L2.Th1.A
end
end

section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def WpCleared : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    constantCoeff (wpReg W) = 0 ∧ (∀ n : ℕ, Odd n → coeff n (wpReg W) = 0) ∧
    (-2 + X ^ 3 * derivative (wpReg W)) ^ 2 =
      4 * (1 + X ^ 2 * wpReg W) ^ 3 - C (g₂ W) * X ^ 4 * (1 + X ^ 2 * wpReg W) - C (g₃ W) * X ^ 6

def WpInU : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    X ^ 2 * (1 + logSer W ^ 2 * (wpReg W).subst (logSer W)) =
      logSer W ^ 2 * (xS W + C (W.b₂ / 12) * X ^ 2)

def TInZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP : K),
    (tS W xP).subst (expSer W) * (1 + X ^ 2 * wpReg W - C (xP + W.b₂ / 12) * X ^ 2) = X ^ 2

def CubeTwoR : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    ∃ c : MvPowerSeries (Fin 2) R, MvPowerSeries.constantCoeff c = -1 ∧
      U₂ ^ 2 * (xS W).subst (U₁ : MvPowerSeries (Fin 2) R)
        - U₁ ^ 2 * (xS W).subst (U₂ : MvPowerSeries (Fin 2) R)
        = c * fgl W * MvPowerSeries.subst
            (![U₁, (iSer W).subst (U₂ : MvPowerSeries (Fin 2) R)] :
              Fin 2 → MvPowerSeries (Fin 2) R) (fgl W)

def CubeThreeR : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    let t : Fin 3 → MvPowerSeries (Fin 3) R := fun i => MvPowerSeries.X i
    let row : Fin 3 → Fin 3 → MvPowerSeries (Fin 3) R := fun i =>
      ![t i ^ 3, t i * (xS W).subst (t i), (yS W).subst (t i)]
    ∃ e : MvPowerSeries (Fin 3) R, MvPowerSeries.constantCoeff e = -1 ∧
      (Matrix.of row).det
        = e * MvPowerSeries.subst
              (![MvPowerSeries.subst (![t 0, t 1] : Fin 2 → MvPowerSeries (Fin 3) R) (fgl W), t 2] :
                Fin 2 → MvPowerSeries (Fin 3) R) (fgl W)
            * (t 0 - t 1) * (t 0 - t 2) * (t 1 - t 2)

def CoeffMem : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (S : Subring R),
    W.a₁ ∈ S → W.a₂ ∈ S → W.a₃ ∈ S → W.a₄ ∈ S → W.a₆ ∈ S →
    (∀ n, coeff n (wSer W) ∈ S) ∧ (∀ n, coeff n (xS W) ∈ S) ∧ (∀ n, coeff n (yS W) ∈ S) ∧
    (∀ n, coeff n (fw W) ∈ S) ∧ (∀ n, coeff n (om W) ∈ S) ∧ (∀ n, coeff n (iSer W) ∈ S) ∧
    (∀ d, MvPowerSeries.coeff d (fgl W) ∈ S) ∧ (∀ (k : ℤ) n, coeff n (zSer W k) ∈ S) ∧
    ((∃ h ∈ S, 2 * h = 1) → ∀ n, coeff n (halfSer W) ∈ S) ∧
    (∀ xP ∈ S, ∀ n, coeff n (tS W xP) ∈ S) ∧
    (∀ xP ∈ S, ∀ yP ∈ S, ∀ n, coeff n (xPlus W xP yP) ∈ S ∧ coeff n (yPlus W xP yP) ∈ S)

end Formalism.L2.Th1.A
end
end

section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def TSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP : R),
    constantCoeff (tDen W xP) = 1 ∧ tDen W xP * invOfUnit (tDen W xP) 1 = 1 ∧
    toL (tS W xP) * (xL W - HahnSeries.C xP) = 1 ∧
    coeff 2 (tS W xP) = 1 ∧ X ^ 2 ∣ tS W xP ∧
    (tS W xP).subst (iSer W) = tS W xP

def PlusChord : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    toL (xPlus W xP yP) = (curveL W).toAffine.addX (xL W) (HahnSeries.C xP) (slopeL W xP yP) ∧
    toL (yPlus W xP yP)
      = (curveL W).toAffine.addY (xL W) (HahnSeries.C xP) (yL W) (slopeL W xP yP)

def PlusFlow : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    IsFlow (curveS W) (D W) (xPlus W xP yP) (yPlus W xP yP) ∧
    constantCoeff (xPlus W xP yP) = xP ∧ constantCoeff (yPlus W xP yP) = yP

def PlusLogDeriv : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    DL W (toL (tS W xP) * DL W (xL W))
      = 2 * xL W - toL (xPlus W xP yP) - toL (xPlus W xP (W.toAffine.negY xP yP))

def PlusMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)
    (xP yP : R),
    PowerSeries.map φ (tS W xP) = tS (W.map φ) (φ xP) ∧
    PowerSeries.map φ (xPlus W xP yP) = xPlus (W.map φ) (φ xP) (φ yP) ∧
    PowerSeries.map φ (yPlus W xP yP) = yPlus (W.map φ) (φ xP) (φ yP)

def TwoTorsionU : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xT yT : R), W.toAffine.Equation xT yT →
    2 * yT + W.a₁ * xT + W.a₃ = 0 →
    xPlus W xT yT = C xT + C (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * tS W xT ∧
    D W (tS W xT) ^ 2 = 4 * tS W xT + C (12 * xT + W.b₂) * tS W xT ^ 2
      + 4 * C (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * tS W xT ^ 3 ∧
    D W (D W (tS W xT)) = 2 + C (12 * xT + W.b₂) * tS W xT
      + 6 * C (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * tS W xT ^ 2

def TwoTorsionZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xT yT : K),
    W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    let e₁ : K := xT + W.b₂ / 12
    let kap : K := 3 * e₁ ^ 2 - g₂ W / 4
    let w₁ : K⟦X⟧ := (tS W xT).subst (expSer W)
    4 * e₁ ^ 3 - g₂ W * e₁ - g₃ W = 0 ∧
    (4 * Polynomial.X ^ 3 - Polynomial.C (g₂ W) * Polynomial.X - Polynomial.C (g₃ W) : Polynomial K)
      = 4 * (Polynomial.X - Polynomial.C e₁) *
        (Polynomial.X ^ 2 + Polynomial.C e₁ * Polynomial.X + Polynomial.C (e₁ ^ 2 - g₂ W / 4)) ∧
    kap = 3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT ∧
    toL w₁ * (wpL W - HahnSeries.C e₁) = 1 ∧
    X ^ 2 ∣ w₁ ∧ coeff 2 w₁ = 1 ∧ w₁.subst (-X : K⟦X⟧) = w₁ ∧
    derivative w₁ ^ 2 = 4 * w₁ * (1 + 3 * C e₁ * w₁ + C kap * w₁ ^ 2) ∧
    derivative (derivative w₁) = 2 + 12 * C e₁ * w₁ + 6 * C kap * w₁ ^ 2 ∧
    (xPlus W xT yT).subst (expSer W) + C (W.b₂ / 12) = C e₁ + C kap * w₁ ∧
    ∀ e₂ e₃ : K, (4 * Polynomial.X ^ 3 - Polynomial.C (g₂ W) * Polynomial.X
        - Polynomial.C (g₃ W) : Polynomial K)
        = 4 * (Polynomial.X - Polynomial.C e₁) * (Polynomial.X - Polynomial.C e₂)
          * (Polynomial.X - Polynomial.C e₃) →
      kap = (e₁ - e₂) * (e₁ - e₃) ∧
      derivative w₁ ^ 2 = 4 * w₁ * (1 + C (e₁ - e₂) * w₁) * (1 + C (e₁ - e₃) * w₁)

def PlusZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    IsFlow (curveS W) (derivative (R := K)) ((xPlus W xP yP).subst (expSer W))
      ((yPlus W xP yP).subst (expSer W)) ∧
    toL ((tS W xP).subst (expSer W)) * (xZ W - HahnSeries.C xP) = 1 ∧
    dL (toL ((tS W xP).subst (expSer W)) * dL (wpL W))
      = 2 * xZ W - toL ((xPlus W xP yP).subst (expSer W))
        - toL ((xPlus W xP (W.toAffine.negY xP yP)).subst (expSer W))

end Formalism.L2.Th1.A
end
end

section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def CubeMem : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (S : Subring R),
    W.a₁ ∈ S → W.a₂ ∈ S → W.a₃ ∈ S → W.a₄ ∈ S → W.a₆ ∈ S →
    (∃ c : MvPowerSeries (Fin 2) R, (∀ d, MvPowerSeries.coeff d c ∈ S) ∧
      MvPowerSeries.constantCoeff c = -1 ∧
      U₂ ^ 2 * (xS W).subst (U₁ : MvPowerSeries (Fin 2) R)
        - U₁ ^ 2 * (xS W).subst (U₂ : MvPowerSeries (Fin 2) R)
        = c * fgl W * MvPowerSeries.subst
            (![U₁, (iSer W).subst (U₂ : MvPowerSeries (Fin 2) R)] :
              Fin 2 → MvPowerSeries (Fin 2) R) (fgl W)) ∧
    (∃ e : MvPowerSeries (Fin 3) R, (∀ d, MvPowerSeries.coeff d e ∈ S) ∧
      MvPowerSeries.constantCoeff e = -1 ∧
      (Matrix.of fun i : Fin 3 => ![(MvPowerSeries.X i : MvPowerSeries (Fin 3) R) ^ 3,
          MvPowerSeries.X i * (xS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) R),
          (yS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) R)]).det
        = e * MvPowerSeries.subst
              (![MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
                  Fin 2 → MvPowerSeries (Fin 3) R) (fgl W), MvPowerSeries.X 2] :
                Fin 2 → MvPowerSeries (Fin 3) R) (fgl W)
            * (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2)
            * (MvPowerSeries.X 1 - MvPowerSeries.X 2)) ∧
    (∃ n₁ n₂ : MvPowerSeries (Fin 2) R, (∀ d, MvPowerSeries.coeff d n₁ ∈ S) ∧
      (∀ d, MvPowerSeries.coeff d n₂ ∈ S) ∧ MvPowerSeries.constantCoeff n₁ = 1 ∧
      MvPowerSeries.constantCoeff n₂ = 1 ∧
      MvPowerSeries.subst (![U₁, (iSer W).subst (U₂ : MvPowerSeries (Fin 2) R)] :
        Fin 2 → MvPowerSeries (Fin 2) R) (fgl W) = (U₁ - U₂) * n₁ ∧
      fgl W = (U₂ - (iSer W).subst (U₁ : MvPowerSeries (Fin 2) R)) * n₂) ∧
    ∀ n : ℤ, (∃ h ∈ S, (n : R) * h = 1) → ∀ k, coeff k (divSer W n) ∈ S

def BridgeTwoMore : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K)
    (xT yT : K), W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    4 * (xT + W.b₂ / 12) ^ 3 - g₂ W * (xT + W.b₂ / 12) - g₃ W = 0 ∧
    (∀ n, Odd n → coeff n ((tS W xT).subst (expSer W)) = 0) ∧
    (IntModel W → ‖xT‖ ≤ 1 → ‖yT‖ ≤ 1 ∧ ‖W.b₂ / 12 - (xT + W.b₂ / 12)‖ ≤ 1 ∧
      ‖3 * (xT + W.b₂ / 12) ^ 2 - g₂ W / 4‖ ≤ 1)

def FlowUniqueZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (x y x' y' : K⟦X⟧),
    IsFlow (curveS W) (derivative (R := K)) x y →
    IsFlow (curveS W) (derivative (R := K)) x' y' →
    constantCoeff x = constantCoeff x' → constantCoeff y = constantCoeff y' → x = x' ∧ y = y'

end Formalism.L2.Th1.A
end
end

section

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

def LogSpec : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    constantCoeff (logSer W) = 0 ∧ coeff 1 (logSer W) = 1 ∧ derivative (logSer W) = om W ∧
    D W (logSer W) = 1

def ExpSpec : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    constantCoeff (expSer W) = 0 ∧ coeff 1 (expSer W) = 1 ∧
    (logSer W).subst (expSer W) = X ∧ (expSer W).subst (logSer W) = X ∧
    derivative (expSer W) = (fw W).subst (expSer W)

def ChainZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (f : K⟦X⟧),
    derivative (f.subst (expSer W)) = (D W f).subst (expSer W)

def LogNeg : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    (logSer W).subst (iSer W) = -logSer W ∧
    (expSer W).subst (-X : K⟦X⟧) = (iSer W).subst (expSer W)

def FlowZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    IsFlow (curveL W) dL (xZ W) (yZ W) ∧ toL (expSer W) * yZ W = -xZ W

def WpODE : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    dL (wpL W) = 2 * yZ W + HahnSeries.C W.a₁ * xZ W + HahnSeries.C W.a₃ ∧
    dL (wpL W) ^ 2 = 4 * wpL W ^ 3 - HahnSeries.C (g₂ W) * wpL W - HahnSeries.C (g₃ W) ∧
    dL (dL (wpL W)) = 6 * wpL W ^ 2 - HahnSeries.C (g₂ W / 2)

def WpShape : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    wpL W = uPow (-2) + toL (wpReg W) ∧ coeff 0 (wpReg W) = 0 ∧
    (∀ n : ℕ, Odd n → coeff n (wpReg W) = 0) ∧
    coeff 2 (wpReg W) = g₂ W / 20 ∧ coeff 4 (wpReg W) = g₃ W / 28

def WpRecursion : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (k : ℕ), 3 ≤ k →
    ((k : K) - 2) * (2 * (k : K) + 3) * coeff (2 * k) (wpReg W) =
      3 * ∑ i ∈ Finset.Icc 1 (k - 2), coeff (2 * i) (wpReg W) * coeff (2 * (k - 1 - i)) (wpReg W)

end Formalism.L2.Th1.A
end
end
