module

public import Formalism.FormalGroupLog.Statement
public import Formalism.GaussJetBounds.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle001
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
public import Formalism.GaussJetBounds.StatementS
public import Formalism.GaussJetBounds.Bundle004

@[expose] public section

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram NoLowBidegree letterLog entLog de1 de2)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)

section Defs

variable {K : Type} [NormedField K] {τ : Type}

def IP (l : ℕ) (σ : K →+* K) (g : MvPowerSeries τ K) : Prop :=
  MvPowerSeries.constantCoeff g = 0 ∧
  Integral (g - MvPowerSeries.C ((l : K)⁻¹) * frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) g))

def ShiftType {d : ℕ} (l : ℕ) (σ : K →+* K) (L : ZMod d → MvPowerSeries τ K) : Prop :=
  ∀ s, MvPowerSeries.constantCoeff (L s) = 0 ∧
    Integral (L s - MvPowerSeries.C ((l : K)⁻¹) *
      frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) (L (s - 2))))

def linEL {d : ℕ} [NeZero d] (σ : K →+* K) (c : K) (L : ZMod d → MvPowerSeries τ K) :
    MvPowerSeries τ K :=
  ∑ s : ZMod d, if s.val % 2 = 0 then MvPowerSeries.C (σ^[s.val] c) * L s else 0

def linOL {d : ℕ} [NeZero d] (σ : K →+* K) (c : K) (L : ZMod d → MvPowerSeries τ K) :
    MvPowerSeries τ K :=
  ∑ s : ZMod d, if s.val % 2 = 0 then 0 else MvPowerSeries.C (σ^[s.val] c) * L s

end Defs

def FrobSq : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → Formalism.G.FunctionalEquationSetting K l (l ^ 2) (σ.comp σ) ∧ ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1

def IPLemma : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (τ : Type) [Finite τ] (g : MvPowerSeries τ K), IP l σ g →
      ∃ h : MvPowerSeries τ K, MvPowerSeries.constantCoeff h = 0 ∧ Integral h ∧
        PowerSeries.subst h (lgF K l) = g

def IPClosure : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K)
    (τ : Type) [Finite τ],
    IP l σ (0 : MvPowerSeries τ K) ∧
    (∀ g g' : MvPowerSeries τ K, IP l σ g → IP l σ g' → IP l σ (g + g')) ∧
    (∀ (c : K) (g : MvPowerSeries τ K), ‖c‖ ≤ 1 → σ (σ c) = c → IP l σ g →
      IP l σ (MvPowerSeries.C c * g))

def ShiftIP : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → Even d → ∀ (τ : Type) [Finite τ] (L : ZMod d → MvPowerSeries τ K),
    ShiftType l σ L → ∀ c : K, ‖c‖ ≤ 1 → σ^[d] c = c →
      IP l σ (linEL σ c L) ∧ IP l σ (linOL σ c L)

def LetterShift : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), l.Prime →
    (∀ b : Bool, ShiftType l σ (fun s : ZMod d => letterLog (K := K) l (b, s))) ∧
    ShiftType l σ (fun s : ZMod d => letLog (K := K) l s) ∧
    ∀ (N0 N1 : ℕ) (a : Fin N0) (b : Fin N1),
      ShiftType l σ (fun s : ZMod d => entLog (K := K) (N0 := N0) (N1 := N1) l (s, a, b))

def PairRules : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 → ∀ (τ : Type) [Finite τ],
    (∀ G G' H : MvPowerSeries τ K, IP l σ G → IP l σ G' → IP l σ H →
      Simeq (MvPowerSeries.subst ![G + G', H] (addC l be0))
        (MvPowerSeries.subst ![G, H] (addC l be0) + MvPowerSeries.subst ![G', H] (addC l be0))) ∧
    (∀ G H H' : MvPowerSeries τ K, IP l σ G → IP l σ H → IP l σ H' →
      Simeq (MvPowerSeries.subst ![G, H + H'] (addC l be0))
        (MvPowerSeries.subst ![G, H] (addC l be0) + MvPowerSeries.subst ![G, H'] (addC l be0))) ∧
    (F2 l σ be0 → ∀ (c : K) (G H : MvPowerSeries τ K), ‖c‖ ≤ 1 → σ (σ c) = c → IP l σ G →
      IP l σ H →
      Simeq (MvPowerSeries.subst ![MvPowerSeries.C c * G, H] (addC l be0))
        (MvPowerSeries.subst ![G, MvPowerSeries.C (σ c) * H] (addC l be0)))

def SubstTil : Prop :=
  ∀ (K : Type) [NormedField K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l →
    ∀ (be0 : MvPowerSeries (Fin 2) K) (ι : Type) [Fintype ι] (om oms : ι → K) (τ : Type) [Finite τ]
      (L : ZMod d → MvPowerSeries τ K), (∀ s, MvPowerSeries.constantCoeff (L s) = 0) →
      MvPowerSeries.subst L (beTil l σ be0 om oms) =
        ∑ r, MvPowerSeries.subst ![linEL σ (oms r) L, linOL σ (om r) L] (addC l be0)

def TorusTil : Prop :=
  ∀ (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l →
    ∀ (be0 : MvPowerSeries (Fin 2) K) (ι : Type) [Fintype ι] (om oms : ι → K) (u : K), u ≠ 0 →
      σ u = u ^ l →
      MvPowerSeries.subst (torus l u) (beTil (d := d) l σ be0 om oms) =
        beTil l σ be0 (fun r => u⁻¹ * om r) (fun r => u * oms r)

def TorusCoeff : Prop :=
  ∀ (K : Type) [Field K] (l d : ℕ) [NeZero d] (u : K) (f : MvPowerSeries (ZMod d) K)
    (n : ZMod d →₀ ℕ),
    MvPowerSeries.coeff n (MvPowerSeries.subst (torus l u) f) =
      (∏ s : ZMod d, (u ^ Formalism.DworkPowerSeriesWeights.lw l s) ^ n s) * MvPowerSeries.coeff n f

def DualExpand : Prop :=
  ∀ (K : Type) [Field K] (d : ℕ) [NeZero d] (σ : K →+* K), Even d →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K),
      (∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) → TrDual d σ om oms →
    ∀ x : K, σ^[d] x = x →
      (∀ r r', σ (σ (∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (x * oms r * om r') else 0)) =
        ∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (x * oms r * om r') else 0) ∧
      (∀ r, x * oms r = ∑ r', (∑ s : ZMod d,
        if s.val % 2 = 0 then σ^[s.val] (x * oms r * om r') else 0) * oms r') ∧
      (∀ r', x * om r' = ∑ r, (∑ s : ZMod d,
        if s.val % 2 = 0 then σ^[s.val] (x * oms r * om r') else 0) * om r)

end Formalism.L2.Th1.D
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram entLog oneLog thetaZ thetaOne frameJet frameJetOne
  nablaO)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp OmOK)

section Defs

variable {K0 K : Type} [Field K0] [Field K] {ι : Type} {d N0 N1 : ℕ} [NeZero d]

def xOfZ (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0)
    (x : Bool × ι × Fin N0 × Fin N1) : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K :=
  PowerSeries.subst
    (if x.1 = false then
      ∑ s : ZMod d, if s.val % 2 = 0 then
        MvPowerSeries.C (j (σ^[s.val] (oms x.2.1))) *
          (MvPowerSeries.X (s, x.2.2.1, x.2.2.2) : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K) else 0
    else
      ∑ s : ZMod d, if s.val % 2 = 0 then 0 else
        MvPowerSeries.C (j (σ^[s.val] (om x.2.1))) *
          (MvPowerSeries.X (s, x.2.2.1, x.2.2.2) : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K))
    (expF K l)

def thetaInZ (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0)
    (Tht : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K) :
    MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K :=
  MvPowerSeries.subst (xOfZ l j σ om oms) Tht

def sumE [Fintype ι] (be : MvPowerSeries (Fin 2) K) :
    MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K :=
  ∑ e : ι × Fin N0 × Fin N1, MvPowerSeries.subst
    (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
      MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K)) be

def conjJ {ν : ℕ} (j : K0 →+* K) (σ : K0 →+* K0) (c : Fin ν → K0) : Fin ν → ZMod (2 * ν) → K :=
  fun r s => j (σ^[s.val] (c r))

end Defs

def B0 : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d] (σ : K0 →+* K0) (j : K0 →+* K),
    UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K0), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K0, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ U0 Φ : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K, Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 → Simeq Φ (sumE (MvPowerSeries.map j be0)) →
      ∃ U : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K, Integral U ∧
        ∀ g : Formalism.DworkPowerSeriesWeights.ZV d N0 N1 → MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K,
          (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
          (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
          thetaInZ l j σ om oms (mvExp (-Φ) * U0) =
            thetaZ g U (-1) (MvPowerSeries.map j (beMean l σ be0 om oms ζ))

def OneLetterHalf : Prop :=
  ∀ (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] (l : ℕ) (σ : K0 →+* K0),
    UnrOK K0 l σ →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 → ∀ ζ : K0, IsPrimitiveRoot ζ (l ^ 2 - 1) →
    ∀ ph : PowerSeries K0,
      Simeq (MvPowerSeries.C (2 : K0) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K0)) be0) →
      Simeq (ph : MvPowerSeries Unit K0) (MvPowerSeries.C ((2 : K0)⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => lgF K0 l)
          (beMean (d := 2) l σ be0 (fun _ : Unit => (1 : K0)) (fun _ => 1) ζ))

def OmOKOf : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    (l ν : ℕ) [NeZero ν] (σ : K0 →+* K0) (j : K0 →+* K), UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) →
    ∀ om oms : Fin ν → K0, OwOK (2 * ν) σ om oms → TrDual (2 * ν) σ om oms →
      OmOK l ν (conjJ j σ om) (conjJ j σ oms)

def ThetaInZIsSSub : Prop :=
  ∀ (K0 K : Type) [Field K0] [Field K] (l ν r0 r1 : ℕ) [NeZero ν] (σ : K0 →+* K0) (j : K0 →+* K)
    (om oms : Fin ν → K0) (Tht : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) K),
    thetaInZ (d := 2 * ν) l j σ om oms Tht =
      MvPowerSeries.subst (Formalism.InvariantFactorPaths.G7.sSub (conjJ j σ om) (conjJ j σ oms) (expF K l)) Tht

end Formalism.L2.Th1.D
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def muPrime (l : ℕ) [Fact l.Prime] : Set ℂ_[l] := {ζ | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}

def ringA (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] := Subring.closure (muPrime l)

def ringB (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] := (ringA l).topologicalClosure

def KurUnram : Prop := ∀ (l : ℕ) [Fact l.Prime], Unram l (MaximalUnramifiedExtension l)

def KurIntegers : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    (∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) ∧
    (∀ x ∈ ringB l, ‖x‖ < 1 → ∃ y ∈ ringB l, x = (l : ℂ_[l]) * y) ∧
    (∀ x ∈ ringB l, ‖x‖ = 1 → x⁻¹ ∈ ringB l)

def KurRoots : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ¬ l ∣ n → ∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ n

def KurComplete : Prop := ∀ (l : ℕ) [Fact l.Prime], CompleteSpace (MaximalUnramifiedExtension l)

def KurFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 2 < l →
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ ∧
      ∀ ζ : MaximalUnramifiedExtension l, (ζ : ℂ_[l]) ∈ muPrime l → σ ζ = ζ ^ l

def TrDualExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → Even d → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∃ om oms : Fin (d / 2) → K, OwOK d σ om oms ∧ TrDual d σ om oms

end Formalism.L2.Th1.D
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram NoLowBidegree letterLog de1 de2)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp)

def ExpSpec : Prop :=
  ∀ (K : Type) [Field K] (l : ℕ), 2 ≤ l →
    PowerSeries.constantCoeff (expF K l) = 0 ∧
    PowerSeries.subst (expF K l) (lgF K l) = (PowerSeries.X : PowerSeries K) ∧
    PowerSeries.subst (lgF K l) (expF K l) = (PowerSeries.X : PowerSeries K) ∧
    ∀ ex : PowerSeries K, PowerSeries.constantCoeff ex = 0 →
      PowerSeries.subst ex (lgF K l) = (PowerSeries.X : PowerSeries K) → ex = expF K l

def MulSpec : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ c : K,
    (∃ e : PowerSeries K, IsMul l c e) ∧
    (∀ e e' : PowerSeries K, IsMul l c e → IsMul l c e' → e = e') ∧
    (‖c‖ ≤ 1 → σ (σ c) = c → ∀ e : PowerSeries K, IsMul l c e → ∀ n, ‖PowerSeries.coeff n e‖ ≤ 1)

def TeichSigma : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) (σ : K →+* K),
    UnrOK K l σ → 1 ≤ d → ∀ ζ : K, ζ ^ (l ^ d - 1) = 1 → σ ζ = ζ ^ l

def BeTilXY : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l → Even d →
    ∀ (be0 : MvPowerSeries (Fin 2) K) (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K),
      (∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) → TrDual d σ om oms →
      MvPowerSeries.subst (zXY l σ om oms) (beTil (d := d) l σ be0 om oms) = beXY be0

def BMinus1 : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms →
      ∃ (T : ZMod d → MvPowerSeries (Bool × ι) K) (Xi : Bool × ι → MvPowerSeries (ZMod d) K),
        (∀ s, MvPowerSeries.constantCoeff (T s) = 0 ∧ Integral (T s)) ∧
        (∀ x, MvPowerSeries.constantCoeff (Xi x) = 0 ∧ Integral (Xi x)) ∧
        (∀ s, MvPowerSeries.subst T (letLog (K := K) l s) = zXY l σ om oms s) ∧
        (∀ s x, MvPowerSeries.coeff (Finsupp.single x 1) (T s) = mXY σ om oms s x) ∧
        (∀ s, MvPowerSeries.subst Xi (T s) = MvPowerSeries.X s) ∧
        (∀ x, MvPowerSeries.subst T (Xi x) = MvPowerSeries.X x) ∧
        (∀ s n, MvPowerSeries.coeff n (T s) ≠ 0 → ∀ x, n x ≠ 0 → (x.1 = false ↔ s.val % 2 = 0))

def MeanTorusInvariant : Prop :=
  ∀ (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K)
    (ι : Type) [Fintype ι] (om oms : ι → K) (ζ : K), ζ ^ (l ^ d - 1) = 1 →
    MvPowerSeries.subst (torus l ζ) (beMean (d := d) l σ be0 om oms ζ) = beMean l σ be0 om oms ζ

def MeanNoLowBidegreeTerms : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l → 2 ≤ d → Even d →
    ∀ (be0 : MvPowerSeries (Fin 2) K), DivAB be0 →
    ∀ (ι : Type) [Fintype ι] (om oms : ι → K) (ζ : K), IsPrimitiveRoot ζ (l ^ d - 1) →
      NoLowBidegree (beMean (d := d) l σ be0 om oms ζ)

def TorusSumCoboundaryCondition : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    ∀ (ι : Type) [Fintype ι] (om oms : ι → K), OwOK d σ om oms →
      Simeq (MvPowerSeries.subst (letterLog (K := K) l) (de1 (beTil (d := d) l σ be0 om oms))) 0 ∧
      Simeq (MvPowerSeries.subst (letterLog (K := K) l) (de2 (beTil (d := d) l σ be0 om oms))) 0

def MeanBiextensionHypothesesOfCocycle : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    ∀ (ι : Type) [Fintype ι] (om oms : ι → K), OwOK d σ om oms →
    ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
      BHyp l d ⊤ ζ (beMean l σ be0 om oms ζ)

def MeanSimeq : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
      Simeq (MvPowerSeries.subst (letLog (K := K) l) (beMean (d := d) l σ be0 om oms ζ))
        (MvPowerSeries.subst (letLog (K := K) l) (beTil (d := d) l σ be0 om oms)) ∧
      Simeq (MvPowerSeries.subst (zXY l σ om oms) (beMean (d := d) l σ be0 om oms ζ)) (beXY be0)

def BetaHypOfF : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ F be0 : MvPowerSeries (Fin 2) K, F1 F be0 → F2 l σ be0 → BetaHyp l F be0

end Formalism.L2.Th1.D
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 cob UnrOK IsLawOfLog)

section Defs

variable {K : Type} [Field K]

def IsHom (F FE : MvPowerSeries (Fin 2) K) (θ : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff θ = 0 ∧
  PowerSeries.subst F θ = MvPowerSeries.subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] FE

def mulS (K : Type) [Field K] (l : ℕ) (c : K) : PowerSeries K :=
  PowerSeries.subst (PowerSeries.C c * lgF K l) (expF K l)

end Defs

def NormRel {K : Type} [NormedField K] [CharZero K] (l : ℕ) (σ : K →+* K) (ph : PowerSeries K)
    (α : K) : Prop :=
  Simeq (PowerSeries.subst (mulS K l α) ph : MvPowerSeries Unit K)
    (MvPowerSeries.C (α * σ α) * ph)

def SigmaIsom : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ a : K, ‖σ a‖ = ‖a‖

def FixedIsLimit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ x : K, ‖x‖ ≤ 1 → σ x = x → ∀ k : ℕ, ∃ n : ℕ, ‖x - n‖ ≤ ((l : ℝ) ^ k)⁻¹

def SimeqClosed : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (τ : Type) [Finite τ] (f : ℕ → MvPowerSeries τ K) (g : MvPowerSeries τ K),
    (∀ n, Filter.Tendsto (fun k => MvPowerSeries.coeff n (f k)) Filter.atTop
      (nhds (MvPowerSeries.coeff n g))) →
    (∀ k, Simeq (f k) 0) → Simeq g 0

def SimeqFixed : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (τ : Type) [Finite τ] (f : MvPowerSeries τ K) (c : K), ‖c‖ ≤ 1 → σ c = c →
    Simeq f 0 → Simeq (MvPowerSeries.C c * f) 0

def CoboundaryCocycleTransportAlongHom : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ = (l : ℝ)⁻¹ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ (FE : MvPowerSeries (Fin 2) K) (θ phE ph : PowerSeries K),
      MvPowerSeries.constantCoeff FE = 0 → (∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) → IsHom F FE θ →
      F1 FE (cob FE phE) → Simeq (ph : MvPowerSeries Unit K) (PowerSeries.subst θ phE) →
      F1 F (cob F ph)

def TransportNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (θ phE ph eE : PowerSeries K) (α : K),
      PowerSeries.constantCoeff θ = 0 → (∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) →
      PowerSeries.constantCoeff eE = 0 →
      ‖α‖ ≤ 1 → σ (σ α) = α →
      PowerSeries.subst (mulS K l α) θ = PowerSeries.subst θ eE →
      Simeq (PowerSeries.subst eE phE : MvPowerSeries Unit K) (MvPowerSeries.C (α * σ α) * phE) →
      Simeq (ph : MvPowerSeries Unit K) (PowerSeries.subst θ phE) →
      NormRel l σ ph α

def NormUnits : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (ph : PowerSeries K), PowerSeries.constantCoeff ph = 0 →
    ∀ S : Set K, (∀ α ∈ S, NormRel l σ ph α) →
      ∀ α : K, (∀ ε : ℝ, 0 < ε → ∃ a ∈ S, ‖a - α‖ < ε) → NormRel l σ ph α

def SecondLevelOfNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ ph : PowerSeries K, PowerSeries.constantCoeff ph = 0 → F1 F (cob F ph) →
    (∀ α : K, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ ph α) →
      F2 l σ (cob F ph) ∧
      (∀ α : K, ‖α‖ ≤ 1 → σ (σ α) = α → NormRel l σ ph α) ∧
      Simeq (MvPowerSeries.C (2 : K) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K)) (cob F ph))

def FOfBetaHyp : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → (∃ ζ : K, IsPrimitiveRoot ζ (l ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ be0 : MvPowerSeries (Fin 2) K, Formalism.InvariantFactorPaths.G7.BetaHyp l F be0 → F1 F be0 ∧ F2 l σ be0

end Formalism.L2.Th1.D
end
end
