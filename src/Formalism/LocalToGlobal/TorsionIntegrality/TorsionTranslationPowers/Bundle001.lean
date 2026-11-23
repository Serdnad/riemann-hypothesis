module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import Mathlib.NumberTheory.Padics.Complex
public import Formalism.GaussJetBounds.Bundle002
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

namespace Formalism.L2.Th1.E

section Gen

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l])

def Unif : Prop := Formalism.L2.Th1.A.g₂ W = ι L.g₂ ∧ Formalism.L2.Th1.A.g₃ W = ι L.g₃


open Classical in
def ptW (t : ℂ) : W.toAffine.Point :=
  if h : t ∉ L.lattice ∧ W.toAffine.Nonsingular (ι (L.weierstrassP t) - W.b₂ / 12)
      ((ι (L.derivWeierstrassP t) - W.a₁ * (ι (L.weierstrassP t) - W.b₂ / 12) - W.a₃) / 2)
  then .some _ _ h.2 else 0

def inW (f : ℂ → ℂ) : PowerSeries ℂ_[l] :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 f)).subst (Formalism.L2.Th1.A.logSer W)

def phW : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.phO (ι (Formalism.L2.Th1.F.s2 L)) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L))
    (Formalism.L2.Th1.A.logSer W)

def gW (t : ℂ) : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.fExp (phW l L ι W) * inW l ι W (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L))

end Gen


open Classical in
def PtWAdd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ s t : ℂ, ptW l L ι W (s + t) = ptW l L ι W s + ptW l L ι W t

def PtWZero : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ t : ℂ, ptW l L ι W t = 0 ↔ t ∈ L.lattice


open Classical in
def AnalyticSysW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ (π : ℂ →+ W.toAffine.Point), (∀ t, π t = ptW l L ι W t) → IsTransSys W π (gW l L ι W)

def AnalyticTransW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    IntCurve W →
    ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      ‖ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0)‖ = 1 ∧
      OneUnit (C (ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0))⁻¹ * gW l L ι W t)

def ShiftAnalyticW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    IntCurve W → ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ‖px W (ptW l L ι W (ω₀ / 2))‖ ≤ 1 → OneUnit (inW l ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      GaussOne (inW l ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

end Formalism.L2.Th1.E
end
end

section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

section An

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

def curveL : WeierstrassCurve ℂ_[l] := Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃)


open Classical in
def ptOf (t : ℂ) : (curveL l L ι).toAffine.Point :=
  if h : t ∉ L.lattice ∧
      (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2)
  then .some _ _ h.2 else 0

def phL : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.phO (ι (Formalism.L2.Th1.F.s2 L)) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L))
    (Formalism.L2.Th1.A.logSer (curveL l L ι))

def inU (f : ℂ → ℂ) : PowerSeries ℂ_[l] :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 f)).subst (Formalism.L2.Th1.A.logSer (curveL l L ι))

def gT (t : ℂ) : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.fExp (phL l L ι) * inU l L ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L))

def phPrime (t₀ : ℂ) : PowerSeries ℂ_[l] :=
  -Formalism.L2.Th1.B.fLog (inU l L ι (Formalism.L2.Th1.F.th0 L t₀))

end An


open Classical in
def PtOfAdd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (s t : ℂ),
    ptOf l L ι (s + t) = ptOf l L ι s + ptOf l L ι t

def PtOfZero : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (t : ℂ), ptOf l L ι t = 0 ↔ t ∈ L.lattice

def TorsionIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K), IntCurve W →
    ∀ (P : W.toAffine.Point) (N : ℕ), ‖(N : K)‖ = 1 → N • P = 0 → P ≠ 0 → ‖px W P‖ ≤ 1 ∧ ‖py W P‖ ≤ 1

def WpBridge : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]),
    Formalism.L2.Th1.A.wpReg (curveL l L ι) = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L)

def TransWpBridge : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (t : ℂ), t ∉ L.lattice →
    inU l L ι (fun z => L.weierstrassP (z + t)) = xT (curveL l L ι) (ptOf l L ι t)


open Classical in
def AnalyticSys : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (π : ℂ →+ (curveL l L ι).toAffine.Point), (∀ t, π t = ptOf l L ι t) →
    IsTransSys (curveL l L ι) π (gT l L ι)

def AnalyticTrans : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), IntCurve (curveL l L ι) →
    ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      ‖ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0)‖ = 1 ∧
      OneUnit (C (ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0))⁻¹ * gT l L ι t)

def OpUTh0Root : Prop :=
  ∀ (L : PeriodPair) (t t₀ : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ L.lattice → (N : ℂ) * t₀ ∈ L.lattice →
    t₀ ∉ L.lattice → ∃ (ζ : ℂ) (m : ℕ), 0 < m ∧ ζ ^ m = 1 ∧
      Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.th0 L t₀) =
        fun z => ζ * (Formalism.L2.Th1.F.opU L t₀ (Formalism.L2.Th1.F.sgStar L) 0)⁻¹ *
          Formalism.L2.Th1.F.opU L (t + t₀) (Formalism.L2.Th1.F.sgStar L) z

def ThetaZeroAnalytic : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), l ≠ 2 → IntCurve (curveL l L ι) →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
      Formalism.InvariantFactorPaths.G7.Simeq (ι := Unit) (phL l L ι) (phPrime l L ι (ω₀ / 2)) ∧
      ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice →
        GaussOne (Formalism.L2.Th1.B.fExp (phL l L ι) *
          inU l L ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

def PtOfInt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), IntCurve (curveL l L ι) →
    ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      ‖px (curveL l L ι) (ptOf l L ι t)‖ ≤ 1 ∧ ‖py (curveL l L ι) (ptOf l L ι t)‖ ≤ 1

def KernelPtInt : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]), IntCurve (curveL l L ι) →
    ∀ (a b : ℤ) (t : ℂ), ((a : ℂ) + (b : ℂ) * Formalism.L2.Th1.CM.omegaK d) * t ∈ L.lattice →
      ¬ (l : ℤ) ∣ a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4) → t ∉ L.lattice →
      ‖px (curveL l L ι) (ptOf l L ι t)‖ ≤ 1 ∧ ‖py (curveL l L ι) (ptOf l L ι t)‖ ≤ 1

end Formalism.L2.Th1.E
end
end

section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq cob IsLawOfLog lgF UnrOK)

section Prod

variable {K : Type} [Field K]

def phSum {n : Type} [Fintype n] (ph : PowerSeries K) : MvPowerSeries n K := ∑ i, at1 i ph

def thetaProd {κ n : Type} [Fintype κ] [Fintype n] (r : κ → K) (H : κ → n → PowerSeries K) :
    MvPowerSeries n K :=
  ∑ k, MvPowerSeries.C (r k) * ∏ i, at1 i (H k i)

def hypCoord {O ι n : Type} [Semiring O] [Fintype ι] (l linv : PowerSeries K) (τ : O →+* K) (f f' : ι → n → O) (i : n) :
    MvPowerSeries (Bool × ι) K :=
  Formalism.L2.Th1.C.flin l linv (Sum.elim (fun e => τ (f e i)) (fun e => τ (f' e i)))
    (Sum.elim (fun e => (MvPowerSeries.X (false, e) : MvPowerSeries (Bool × ι) K))
      (fun e => MvPowerSeries.X (true, e)))

def beSum {ι : Type} [Fintype ι] (l linv ph : PowerSeries K) : MvPowerSeries (Bool × ι) K :=
  ∑ e, Formalism.L2.Th1.C.be0 l linv ph (MvPowerSeries.X (false, e)) (MvPowerSeries.X (true, e))

end Prod

def ProdInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (κ n : Type) [Fintype κ] [Fintype n]
    (ph : PowerSeries K) (r : κ → K) (V : κ → n → PowerSeries K),
    constantCoeff ph = 0 → (∀ k, ‖r k‖ ≤ 1) → (∀ k i, IntS (V k i)) →
      thetaProd r (fun k i => (mvExp (-ph) : PowerSeries K) * V k i) =
          mvExp (-(phSum ph : MvPowerSeries n K)) * thetaProd r V ∧
        Integral (thetaProd r V)

def SubstExpInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (n m : Type) [Fintype n]
    (φ : n → MvPowerSeries m K), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → (∀ i, Integral (φ i)) →
    ∀ Φ U : MvPowerSeries n K, MvPowerSeries.constantCoeff Φ = 0 → Integral U →
      MvPowerSeries.subst φ (mvExp (-Φ) * U) =
          mvExp (-(MvPowerSeries.subst φ Φ)) * MvPowerSeries.subst φ U ∧
        Integral (MvPowerSeries.subst φ U) ∧ MvPowerSeries.constantCoeff (MvPowerSeries.subst φ Φ) = 0

def CongIffSimeq : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (R : Subring K),
    (∀ a, a ∈ R ↔ ‖a‖ ≤ 1) → ∀ (σ : Type) (f g : MvPowerSeries σ K),
      Formalism.L2.Th1.C.Cong R f g ↔ Simeq f g

def SumEBridge : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l linv : PowerSeries K), Formalism.L2.Th1.C.IsLogPair l linv →
    ∀ F : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F = 0 → cob F l = 0 →
    ∀ (ph : PowerSeries K) (ι : Type) [Fintype ι] (N0 N1 : ℕ),
      (Formalism.L2.Th1.D.sumE (cob F ph) : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K) =
        beSum l linv ph

def MapCob : Prop :=
  ∀ (K0 K : Type) [Field K0] [Field K] (j : K0 →+* K) (F : MvPowerSeries (Fin 2) K0) (f : PowerSeries K0),
    MvPowerSeries.constantCoeff F = 0 →
      MvPowerSeries.map j (cob F f) = cob (MvPowerSeries.map j F) (PowerSeries.map j f)

end Formalism.L2.Th1.E
end
end

section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

def IsShiftSys {K : Type} [NormedField K] [DecidableEq K] (W : WeierstrassCurve K)
    (A : AddSubgroup W.toAffine.Point) (S : W.toAffine.Point) (H : W.toAffine.Point → K⟦X⟧)
    (c : W.toAffine.Point → K) : Prop :=
  OneUnit (H 0) ∧ (∀ Q ∈ A, Q ≠ 0 → c Q ≠ 0) ∧
  ∀ P ∈ A, ∀ Q ∈ A, Q ≠ 0 → ∃ ρ : K, ‖ρ‖ = 1 ∧
    H (P + Q) * H (P - Q) = C (ρ * c Q ^ 2) * (C (px W Q) - xT W (P + S)) * H P ^ 2

def ShiftUnit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ (A : AddSubgroup W.toAffine.Point) [Finite A], ‖(Nat.card A : K)‖ = 1 →
    ∀ (S : W.toAffine.Point), S ∉ A →
    (∀ Q ∈ A, Q ≠ 0 → ‖px W Q‖ ≤ 1 ∧ ‖py W Q‖ ≤ 1) →
    (∀ P ∈ A, ‖px W (P + S)‖ ≤ 1 ∧ ‖py W (P + S)‖ ≤ 1) →
    ∀ (H : W.toAffine.Point → K⟦X⟧) (c : W.toAffine.Point → K), IsShiftSys W A S H c →
      (∀ Q ∈ A, Q ≠ 0 → ‖c Q‖ = 1) ∧
      ∀ P ∈ A, ‖constantCoeff (H P)‖ = 1 ∧ OneUnit (C (constantCoeff (H P))⁻¹ * H P)

def ShiftPtsInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ (A : AddSubgroup W.toAffine.Point) [Finite A], ‖(Nat.card A : K)‖ = 1 →
    ∀ (S : W.toAffine.Point), S ∉ A → S + S = 0 → ‖px W S‖ ≤ 1 → ‖py W S‖ ≤ 1 →
      (∀ Q ∈ A, Q ≠ 0 → ‖px W Q‖ ≤ 1 ∧ ‖py W Q‖ ≤ 1) ∧
      (∀ P ∈ A, ‖px W (P + S)‖ ≤ 1 ∧ ‖py W (P + S)‖ ≤ 1)

end Formalism.L2.Th1.E
end
end

section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

def XTShape : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ P : W.toAffine.Point, P ≠ 0 → ‖px W P‖ ≤ 1 → ‖py W P‖ ≤ 1 →
      IntS (xT W P) ∧ coeff 0 (xT W P) = px W P ∧ coeff 1 (xT W P) = psi2 W P ∧
      (psi2 W P = 0 → coeff 2 (xT W P) = kapP W P)

def FacShape : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ P Q : W.toAffine.Point, P ≠ 0 → Q ≠ 0 →
      ‖px W P‖ ≤ 1 → ‖py W P‖ ≤ 1 → ‖px W Q‖ ≤ 1 → ‖py W Q‖ ≤ 1 →
      (P + Q ≠ 0 → ‖px W (P + Q)‖ ≤ 1) → (P - Q ≠ 0 → ‖px W (P - Q)‖ ≤ 1) →
      (P + Q ≠ 0 → P - Q ≠ 0 → UnitAt 0 (C (px W Q) - xT W P)) ∧
      ((P + Q = 0 ∨ P - Q = 0) → Q + Q ≠ 0 → UnitAt 1 (C (px W Q) - xT W P)) ∧
      (P - Q = 0 → Q + Q = 0 → UnitAt 2 (C (px W Q) - xT W P))

def TransPower : Prop :=
  ∀ (K : Type) [NormedField K] [DecidableEq K] (W : WeierstrassCurve K)
    (T : Type) [AddCommGroup T] (π : T →+ W.toAffine.Point) (G : T → K⟦X⟧), IsTransSys W π G →
    ∀ ε : K, G 0 = C ε * X →
    ∀ (t : T) (k : ℕ), (∀ j : ℕ, 1 ≤ j → j ≤ k → π (j • t) ≠ 0) →
      C (ε ^ k) * G ((k + 1) • t) * X ^ k = G t ^ (k + 1) *
        ∏ j ∈ Finset.range k,
          (C (constantCoeff (G t) ^ 2) * (C (px W (π t)) - xT W (π ((j + 1) • t)))) ^ (k - j)

def TransUnit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W →
    ∀ (T : Type) [AddCommGroup T] (π : T →+ W.toAffine.Point) (G : T → K⟦X⟧), IntPts W π →
    IsTransSys W π G →
    ∀ (t : T) (N : ℕ), ‖(N : K)‖ = 1 → N • π t = 0 → π t ≠ 0 →
      ‖constantCoeff (G t)‖ = 1 ∧ OneUnit (C (constantCoeff (G t))⁻¹ * G t)

def TransGauss : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W →
    ∀ (T : Type) [AddCommGroup T] (π : T →+ W.toAffine.Point) (G : T → K⟦X⟧), IntPts W π →
    IsTransSys W π G →
    ∀ (t : T) (N : ℕ), ‖(N : K)‖ = 1 → N • π t = 0 → GaussOne (G t)

def ParSum : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (M : A → ℝ),
    (∀ P Q : A, Q ≠ 0 → M (P + Q) + M (P - Q) - 2 * M P = 2 * M Q) → ∀ Q : A, Q ≠ 0 → M Q = 0

def ParSumTwo : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (M₀ m : A → ℝ),
    (∀ P Q : A, Q ≠ 0 → M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P = 2 * m Q) →
    (∀ Q : A, Q ≠ 0 → m Q = 0) ∧ ∀ P : A, M₀ P = M₀ 0

end Formalism.L2.Th1.E
end
end

section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

def NonsingNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K), IntCurve W →
    ∀ x y : K, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → W.toAffine.Equation x y →
      ‖2 * y + W.a₁ * x + W.a₃‖ = 1 ∨ ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ = 1

def UnitKap : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ P : W.toAffine.Point, P ≠ 0 → P + P = 0 → ‖px W P‖ ≤ 1 → ‖py W P‖ ≤ 1 →
      psi2 W P = 0 ∧ ‖kapP W P‖ = 1

def UnitPsi2 : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ P : W.toAffine.Point, P ≠ 0 → P + P ≠ 0 → ‖px W P‖ ≤ 1 → ‖py W P‖ ≤ 1 →
      ‖px W (P + P)‖ ≤ 1 → ‖psi2 W P‖ = 1

def UnitDiff : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ P Q : W.toAffine.Point, P ≠ 0 → Q ≠ 0 → P + Q ≠ 0 → P - Q ≠ 0 →
      ‖px W P‖ ≤ 1 → ‖py W P‖ ≤ 1 → ‖px W Q‖ ≤ 1 → ‖py W Q‖ ≤ 1 →
      ‖px W (P + Q)‖ ≤ 1 → ‖px W (P - Q)‖ ≤ 1 → ‖px W P - px W Q‖ = 1

def IntRules : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K],
    (∀ a : K, ‖a‖ ≤ 1 → IntS (C a)) ∧ IntS (X : K⟦X⟧) ∧
    (∀ f g : K⟦X⟧, IntS f → IntS g → IntS (f + g)) ∧ (∀ f : K⟦X⟧, IntS f → IntS (-f)) ∧
    (∀ f g : K⟦X⟧, IntS f → IntS g → IntS (f * g)) ∧ (∀ (f : K⟦X⟧) (n : ℕ), IntS f → IntS (f ^ n)) ∧
    (∀ f g : K⟦X⟧, OneUnit f → OneUnit g → OneUnit (f * g)) ∧
    (∀ (f : K⟦X⟧) (n : ℕ), OneUnit f → OneUnit (f ^ n)) ∧
    (∀ f g : K⟦X⟧, OneUnit f → f * g = 1 → OneUnit g) ∧
    (∀ f : K⟦X⟧, IntS f ↔ Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) f)

def UnitAtRules : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K],
    (∀ (j k : ℕ) (f g : K⟦X⟧), UnitAt j f → UnitAt k g → UnitAt (j + k) (f * g)) ∧
    (∀ (k n : ℕ) (f : K⟦X⟧), UnitAt k f → UnitAt (k * n) (f ^ n)) ∧
    (∀ (k : ℕ) (f : K⟦X⟧), IntS f → (∀ i, i < k → coeff i f = 0) → ‖coeff k f‖ = 1 → UnitAt k f) ∧
    (∀ (k : ℕ) (f : K⟦X⟧), UnitAt k f → GaussOne f) ∧
    (∀ (k : ℕ) (f : K⟦X⟧) (a : K), ‖a‖ = 1 → UnitAt k f → UnitAt k (C a * f))

def RootInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (N : ℕ) (g : K⟦X⟧), ‖(N : K)‖ = 1 →
    constantCoeff g = 1 → IntS (g ^ N) → IntS g

def GaussMul : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (f g : K⟦X⟧),
    GaussOne f → GaussOne g → GaussOne (f * g)

end Formalism.L2.Th1.E
end
end

section

noncomputable section

namespace Formalism.L2.Th1.E

def CMIntegrality : Prop :=
  ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
    ‖lam ^ 4 * ι L.g₂‖ ≤ 1 → ‖lam ^ 6 * ι L.g₃‖ ≤ 1 →
    ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1 →
    ∀ (z : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      ‖lam ^ 2 * ι (L.weierstrassP z)‖ ≤ 1 ∧ ‖lam ^ 3 * ι (L.derivWeierstrassP z)‖ ≤ 1


open Classical in
def ScaledTorsionPointNonsingular : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
    ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      ∃ h : (Formalism.L2.Th1.A.shortW (lam ^ 4 * ι L.g₂) (lam ^ 6 * ι L.g₃)).toAffine.Nonsingular
          (lam ^ 2 * ι (L.weierstrassP z)) (lam ^ 3 * ι (L.derivWeierstrassP z) / 2),
        N • WeierstrassCurve.Affine.Point.some _ _ h = 0

end Formalism.L2.Th1.E
end
end
