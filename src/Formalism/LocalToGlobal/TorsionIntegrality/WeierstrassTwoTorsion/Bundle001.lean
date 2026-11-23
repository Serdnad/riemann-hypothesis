module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementF
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

noncomputable section

namespace Formalism.L2.Th1.A

def shortW {K : Type} [Field K] (g2 g3 : K) : WeierstrassCurve K :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -g2 / 4, a₆ := -g3 / 4 }

def ShortInv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    (shortW g2 g3).b₂ = 0 ∧ g₂ (shortW g2 g3) = g2 ∧ g₃ (shortW g2 g3) = g3 ∧
    (shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2

def WpNumEq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.CM.wpNum (g₂ W) (g₃ W) = 1 + X ^ 2 * wpReg W ∧
    Formalism.L2.Th1.CM.wpDen (g₂ W) (g₃ W) = 1 - C (1 / 2 : K) * X ^ 3 * derivative (wpReg W)

def USerEq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    Formalism.L2.Th1.CM.uSer g2 g3 = expSer (shortW g2 g3)

end Formalism.L2.Th1.A
end
end

section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.A

def IntModel {K : Type} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1

def BridgeWp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.B.IsWp (g₂ W) (g₃ W) (wpReg W)

def BridgeLaw : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.LawLog (fgl W) (logSer W) ∧ Formalism.L2.Th1.B.IsInv (logSer W) (iSer W) ∧
    (‖(2 : K)‖ = 1 → Formalism.L2.Th1.B.IsHalf (logSer W) (halfSer W))

def BridgeCurve : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.CurveHyp (fgl W) (iSer W) (logSer W) (wpReg W) (xS W) (W.b₂ / 12)

end Formalism.L2.Th1.A
end
end

section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

abbrev U₁ {R : Type u} [CommRing R] : MvPowerSeries (Fin 2) R := MvPowerSeries.X 0

abbrev U₂ {R : Type u} [CommRing R] : MvPowerSeries (Fin 2) R := MvPowerSeries.X 1

def FglMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    MvPowerSeries.map φ (fgl W) = fgl (W.map φ)

def FglChord : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    lam W * (U₂ - U₁) = (wSer W).subst (U₂ : MvPowerSeries (Fin 2) R) - (wSer W).subst (U₁ : MvPowerSeries (Fin 2) R) ∧
    MvPowerSeries.constantCoeff (uThird W) = 0 ∧
    wThird W = (wSer W).subst (uThird W) ∧
    fgl W = (iSer W).subst (uThird W) ∧
    MvPowerSeries.constantCoeff (fgl W) = 0 ∧
    MvPowerSeries.coeff (Finsupp.single 0 1) (fgl W) = 1 ∧
    MvPowerSeries.coeff (Finsupp.single 1 1) (fgl W) = 1

def FglSum : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K),
    Formalism.ELL.ChordAt W (wSer W) U₁ U₂ (fgl W)

def FglGroup : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    ∃ F : FormalGroup R, F.toPowerSeries = fgl W ∧ F.IsComm

def FglLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    (logSer W).subst (fgl W) = (logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K) ∧
    fgl W = (expSer W).subst ((logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K))

def FglInv : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    MvPowerSeries.subst (![X, iSer W] : Fin 2 → R⟦X⟧) (fgl W) = 0

def ZSerSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    (∀ n : ℤ, constantCoeff (zSer W n) = 0 ∧ coeff 1 (zSer W n) = (n : R)) ∧
    zSer W 0 = 0 ∧ zSer W 1 = X ∧ zSer W (-1) = iSer W ∧
    (∀ n : ℕ, zSer W (n : ℤ) = nSer W n) ∧
    (∀ m n : ℤ, MvPowerSeries.subst (![zSer W m, zSer W n] : Fin 2 → R⟦X⟧) (fgl W)
      = zSer W (m + n)) ∧
    (∀ m n : ℤ, (zSer W m).subst (zSer W n) = zSer W (m * n))

def ZSerMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)
    (n : ℤ), PowerSeries.map φ (zSer W n) = zSer (W.map φ) n

def ZSerLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (n : ℤ),
    (logSer W).subst (zSer W n) = C (n : K) * logSer W

def HalfSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R), IsUnit (2 : R) →
    constantCoeff (halfSer W) = 0 ∧ 2 * coeff 1 (halfSer W) = 1 ∧
    (nSer W 2).subst (halfSer W) = X ∧ (halfSer W).subst (nSer W 2) = X ∧
    MvPowerSeries.subst (![halfSer W, halfSer W] : Fin 2 → R⟦X⟧) (fgl W) = X

def HalfLog : Prop :=
  (∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    2 * (logSer W).subst (halfSer W) = logSer W) ∧
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    IsUnit (2 : R) → PowerSeries.map φ (halfSer W) = halfSer (W.map φ)

end Formalism.L2.Th1.A
end
end

section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def ZMap : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [CharZero K] [Field L] [CharZero L] (φ : K →+* L)
    (W : WeierstrassCurve K),
    PowerSeries.map φ (logSer W) = logSer (W.map φ) ∧
    PowerSeries.map φ (expSer W) = expSer (W.map φ) ∧
    PowerSeries.map φ (wpReg W) = wpReg (W.map φ) ∧
    φ (g₂ W) = g₂ (W.map φ) ∧ φ (g₃ W) = g₃ (W.map φ)

def ConstOfD : Prop :=
  ∀ (R : Type u) [CommRing R] [IsAddTorsionFree R] (W : WeierstrassCurve R),
    (∀ f : R⟦X⟧, D W f = 0 → f = C (constantCoeff f)) ∧
    (∀ f : LaurentSeries R, dL f = 0 → f = HahnSeries.C (f.coeff 0)) ∧
    (∀ f : LaurentSeries R, DL W f = 0 → f = HahnSeries.C (f.coeff 0))

def JetZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (f : K⟦X⟧) (n : ℕ),
    (n.factorial : K) * coeff n (f.subst (expSer W)) = constantCoeff ((D W)^[n] f)

def JetMem : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (S : Subring K),
    W.a₁ ∈ S → W.a₂ ∈ S → W.a₃ ∈ S → W.a₄ ∈ S → W.a₆ ∈ S →
    (∀ f : K⟦X⟧, (∀ n, coeff n f ∈ S) → ∀ n, coeff n (D W f) ∈ S) ∧
    (∀ f : K⟦X⟧, (∀ n, coeff n f ∈ S) → ∀ n : ℕ,
      (n.factorial : K) * coeff n (f.subst (expSer W)) ∈ S) ∧
    ∀ n : ℕ, (n.factorial : K) * coeff n (expSer W) ∈ S

def WpPrimeShape : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    dL (wpL W) = -2 * uPow (-3) + toL (derivative (wpReg W)) ∧
    toL ((wSer W).subst (expSer W)) * yZ W = -1

end Formalism.L2.Th1.A
end
end

section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def PlusZCleared : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    derivative (derivative (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))))
        * (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12)))
      - derivative (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))) ^ 2
      = (2 * wpReg W - ((xPlus W xP yP).subst (expSer W) + C (W.b₂ / 12))
          - ((xPlus W xP (W.toAffine.negY xP yP)).subst (expSer W) + C (W.b₂ / 12)))
        * (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))) ^ 2

end Formalism.L2.Th1.A
end
end

section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def divSer {R : Type u} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) : R⟦X⟧ := compInv (zSer W n)

def DivSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (n : ℤ), IsUnit (n : R) →
    constantCoeff (divSer W n) = 0 ∧ (n : R) * coeff 1 (divSer W n) = 1 ∧
    (zSer W n).subst (divSer W n) = X ∧ (divSer W n).subst (zSer W n) = X ∧
    (∀ (S : Type v) [CommRing S] (φ : R →+* S),
      PowerSeries.map φ (divSer W n) = divSer (W.map φ) n) ∧
    (n = 2 → divSer W n = halfSer W)

end Formalism.L2.Th1.A
end
end

section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def CompInvSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (s : R⟦X⟧), constantCoeff s = 0 → IsUnit (coeff 1 s) →
    constantCoeff (compInv s) = 0 ∧ s.subst (compInv s) = X ∧ (compInv s).subst s = X ∧
    coeff 1 (compInv s) * coeff 1 s = 1 ∧
    (∀ t : R⟦X⟧, constantCoeff t = 0 → s.subst t = X → t = compInv s) ∧
    (∀ t : R⟦X⟧, constantCoeff t = 0 → t.subst s = X → t = compInv s)

def CompInvMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (s : R⟦X⟧),
    constantCoeff s = 0 → IsUnit (coeff 1 s) →
    PowerSeries.map φ (compInv s) = compInv (PowerSeries.map φ s)

def IntegSpec : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (f : K⟦X⟧),
    constantCoeff (integ f) = 0 ∧ derivative (integ f) = f ∧
    ∀ g : K⟦X⟧, constantCoeff g = 0 → derivative g = f → g = integ f

end Formalism.L2.Th1.A
end
end

section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

abbrev curveS {R : Type u} [CommRing R] (W : WeierstrassCurve R) : WeierstrassCurve R⟦X⟧ :=
  W.map (C : R →+* R⟦X⟧)

abbrev curveL {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    WeierstrassCurve (LaurentSeries R) :=
  W.map (HahnSeries.C : R →+* LaurentSeries R)

def WSerSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    Formalism.ELL.WFixed W (wSer W) ∧ ∀ w : R⟦X⟧, Formalism.ELL.WFixed W w → w = wSer W

def WSerFactor : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    wSer W = X ^ 3 * wU W ∧ constantCoeff (wU W) = 1 ∧ wU W * xS W = 1 ∧
    constantCoeff (xS W) = 1 ∧ constantCoeff (yS W) = -1

def UnitSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    constantCoeff (fw W) = 1 ∧ fw W * om W = 1 ∧ constantCoeff (om W) = 1 ∧
    coeff 1 (om W) = W.a₁ ∧ coeff 2 (om W) = W.a₁ ^ 2 + W.a₂ ∧
    constantCoeff (iDen W) = -1 ∧ iDen W * invOfUnit (iDen W) (-1) = 1

def SeriesMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    PowerSeries.map φ (wSer W) = wSer (W.map φ) ∧ PowerSeries.map φ (wU W) = wU (W.map φ) ∧
    PowerSeries.map φ (xS W) = xS (W.map φ) ∧ PowerSeries.map φ (yS W) = yS (W.map φ) ∧
    PowerSeries.map φ (fw W) = fw (W.map φ) ∧ PowerSeries.map φ (fu W) = fu (W.map φ) ∧
    PowerSeries.map φ (om W) = om (W.map φ) ∧ PowerSeries.map φ (iSer W) = iSer (W.map φ)

def FlowU : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    IsDer (D W) ∧ ConstCurve (D W) (curveS W) ∧ IsFlowUW (curveS W) (D W) X (wSer W) ∧
    fwAt (curveS W) X (wSer W) = fw W ∧ fuAt (curveS W) X (wSer W) = fu W ∧
    ∀ f : R⟦X⟧, om W * D W f = derivative f

def DLSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    IsDer (DL W) ∧ ConstCurve (DL W) (curveL W) ∧ (∀ r : R, DL W (HahnSeries.C r) = 0) ∧
    ∀ f : R⟦X⟧, DL W (toL f) = toL (D W f)

def FlowL : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    IsFlow (curveL W) (DL W) (xL W) (yL W) ∧
    toL X * yL W = -xL W ∧ toL (wSer W) * yL W = -1 ∧ toL (wSer W) * xL W = toL X

def ISerSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    constantCoeff (iSer W) = 0 ∧ coeff 1 (iSer W) = -1 ∧ (iSer W).subst (iSer W) = X ∧
    (wSer W).subst (iSer W) = wSer W * invOfUnit (iDen W) (-1) ∧
    (xS W).subst (iSer W) = invOfUnit (iDen W) (-1) ^ 2 * xS W ∧
    (yS W).subst (iSer W) = invOfUnit (iDen W) (-1) ^ 3 *
      (-yS W - C W.a₁ * X * xS W - C W.a₃ * X ^ 3) ∧
    D W (iSer W) = -(fw W).subst (iSer W) ∧
    (om W).subst (iSer W) * derivative (iSer W) = -om W

end Formalism.L2.Th1.A
end
end
