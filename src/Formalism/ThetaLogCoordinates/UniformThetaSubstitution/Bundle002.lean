module

public import Formalism.GrowthSums.Bundle001
public import Formalism.GaussJetBounds.Bundle004
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (jetPair)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

def linS {K ι : Type} [Field K] [Fintype ι] (b : ι → K) : MvPowerSeries ι K :=
  ∑ x, MvPowerSeries.C (b x) * MvPowerSeries.X x

def shiftPoly {K ι κ : Type} [Field K] [Fintype κ] (b : κ → ι → K) (Q : MvPolynomial ι K) :
    MvPolynomial κ (MvPolynomial ι K) :=
  MvPolynomial.aeval (fun x : ι => (MvPolynomial.C (MvPolynomial.X x) +
    ∑ k, MvPolynomial.C (MvPolynomial.C (b k x)) * MvPolynomial.X k :
      MvPolynomial κ (MvPolynomial ι K))) Q

def hasseDir {K ι κ : Type} [Field K] [Fintype κ] (b : κ → ι → K) (β : κ →₀ ℕ)
    (Q : MvPolynomial ι K) : MvPolynomial ι K :=
  AddMonoidAlgebra.coeff (shiftPoly b Q) β

def JetPairingHasseIdentity : Prop :=
  ∀ (K ι κ : Type) [Field K] [Fintype ι] [Fintype κ] (b : κ → ι → K) (β : κ →₀ ℕ)
    (Q : MvPolynomial ι K) (G : MvPowerSeries ι K),
    jetPair Q ((∏ k, linS (b k) ^ β k) * G) =
      ((∏ k, (β k).factorial : ℕ) : K) * jetPair (hasseDir b β Q) G

def HasseDerivIntegralHomogeneous : Prop :=
  ∀ (K ι κ : Type) [NormedField K] [IsUltrametricDist K] [Fintype κ] (b : κ → ι → K)
    (β : κ →₀ ℕ) (Q : MvPolynomial ι K),
    ((∀ n, ‖AddMonoidAlgebra.coeff Q n‖ ≤ 1) → (∀ k x, ‖b k x‖ ≤ 1) →
      ∀ n, ‖AddMonoidAlgebra.coeff (hasseDir b β Q) n‖ ≤ 1) ∧
    (∀ d, Q.IsHomogeneous d → (hasseDir b β Q).IsHomogeneous (d - ∑ k, β k)) ∧
    (∀ d, Q.IsHomogeneous d → d < ∑ k, β k → hasseDir b β Q = 0)

def HasseDerivProdVanish : Prop :=
  ∀ (K ι κ : Type) [Field K] [Fintype κ] (b : κ → ι → K) (C : ℕ)
    (f : Fin C → MvPolynomial ι K) (m : Fin C → ℕ) (S : Finset κ),
    (∀ c (β' : κ →₀ ℕ), m c < ∑ k ∈ S, β' k → hasseDir b β' (f c) = 0) →
    ∀ β : κ →₀ ℕ, ∑ c, m c < ∑ k ∈ S, β k → hasseDir b β (∏ c, f c) = 0

def colDir {K σ : Type} [Field K] [DecidableEq σ] {r0 r1 : ℕ} (s : σ) (ξ : Fin r0 → K) (b : Fin r1) :
    σ × Fin r0 × Fin r1 → K :=
  fun x => if x.1 = s ∧ x.2.2 = b then ξ x.2.1 else 0

def minorAt {K σ : Type} [Field K] {r0 r1 l : ℕ} (s : σ) (T : Fin l → Fin r0 → K)
    (I : Fin l → Fin r1) : MvPolynomial (σ × Fin r0 × Fin r1) K :=
  (Matrix.of fun (i c : Fin l) =>
    (∑ a, MvPolynomial.C (T i a) * MvPolynomial.X (s, a, I c) :
      MvPolynomial (σ × Fin r0 × Fin r1) K)).det

def MinorHits : Prop :=
  ∀ (K σ κ : Type) [Field K] [DecidableEq σ] [Fintype κ] (r0 r1 l : ℕ) (s : σ)
    (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) (pos : κ → σ) (ξ : κ → Fin r0 → K)
    (col : κ → Fin r1) (β : κ →₀ ℕ),
    ((∃ k, 2 ≤ β k) ∨
      (∃ k k', k ≠ k' ∧ 1 ≤ β k ∧ 1 ≤ β k' ∧ pos k = pos k' ∧ (ξ k = ξ k' ∨ col k = col k')) ∨
      (∃ k, 1 ≤ β k ∧ (pos k ≠ s ∨ col k ∉ Set.range I))) →
    hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (minorAt s T I) = 0

def lgN (p x : ℕ) : ℕ := if x = 0 then 0 else Nat.log p x + 1

def FactorialLg : Prop :=
  ∀ (p m : ℕ), p.Prime → (m : ℝ) / ((p : ℝ) - 1) - lgN p m ≤ (padicValNat p m.factorial : ℝ)

def deLoss {S : Type} [Fintype S] (p r0 r1 : ℕ) (TT : Finset S) (al ls : S → ℕ) : ℝ :=
  ∑ s, ((r1 : ℝ) * lgN p (al s) + (r0 : ℝ) * r1 * lgN p (ls s)) + ∑ s ∈ TT, ((lgN p (al s) : ℝ)) ^ 2

def StarArith : Prop :=
  ∀ (S : Type) [Fintype S] (p r0 r1 : ℕ) (TT : Finset S) (al ls : S → ℕ)
    (e : S → Fin r1 → ℕ) (a : S → Fin r0 × Fin r1 → ℕ) (i : S → ℕ → ℕ) (E : Finset ℕ) (i0 i2 : ℕ),
    p.Prime → (∀ s, s ∉ TT → al s = 0) → (∀ s, ∑ b, e s b = al s) →
    (∀ s, ∑ x, a s x ≤ ls s) → (∀ s e', e' ∉ E → i s e' = 0) → (∀ s, s ∉ TT → ∀ e', i s e' = 0) →
    (∀ s e', p ^ (2 * e' + 1) * i s e' ≤ al s) →
    (∑ s, ∑ x, a s x + ∑ s, ∑ e' ∈ E, i s e' = ∑ s, ls s) → p * i2 ≤ ∑ s, ls s →
    gamP p * ∑ s ∈ TT, (al s : ℝ) - i0 - ∑ s ∈ TT, ∑ e' ∈ E, (i s e' : ℝ) - deLoss p r0 r1 TT al ls ≤
      (∑ s, ∑ b, (padicValNat p (e s b).factorial : ℝ)) +
        (∑ s, ∑ e' ∈ E, (padicValNat p (i s e').factorial : ℝ)) +
        (∑ s, ∑ x, (padicValNat p (a s x).factorial : ℝ)) -
        rhoP p * (∑ s, ((al s : ℝ) + ls s)) - (i0 + ∑ s, ∑ e' ∈ E, (i s e' : ℝ) + i2)

def ChargeLemma : Prop :=
  ∀ (n : ℕ) (s s' : ZMod n) (a a' d : ℕ), a' < a → s + (a : ZMod n) = s' + (a' : ZMod n) →
    IsLeast {e : ℕ | 1 ≤ e ∧ s + (e : ZMod n) = s'} d → d ≤ a

def ExcessGainBound : Prop :=
  ∀ (n : ℕ) (p : ℝ) (TT : Finset (ZMod n)) (D : ZMod n → Finset ℕ) (al cap : ZMod n → ℝ)
    (de v : ℝ) (i ch : ZMod n → ℕ → ℝ) (E : Finset ℕ),
    1 < p → (∀ s, 0 ≤ al s) → (∀ s, 0 ≤ cap s) → (∀ s e, 0 ≤ i s e) → (∀ s e, 0 ≤ ch s e) →
    (∀ s e, e ∉ E → i s e = 0 ∧ ch s e = 0) → (∀ s e, 2 * e + 1 ∉ D s → ch s e = 0) →
    gamP p * ∑ s ∈ TT, al s - ∑ s ∈ TT, ∑ e ∈ E, ch s e - ∑ s ∈ TT, ∑ e ∈ E, i s e - de ≤ v →
    (∀ s ∈ TT, ∀ e, 2 * e + 1 ∈ D s → ch s e + i s e ≤ al s / p ^ (2 * e + 1)) →
    (∀ s ∈ TT, ∀ e, 2 * e + 1 ∉ D s →
      i s e ≤ min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))) →
    excessGain p TT D al cap de ≤ v

def BCore : Prop :=
  ∀ (n : ℕ) (p : ℝ) (TT TTodd : Finset (ZMod n)) (al cap : ZMod n → ℝ) (de v paid : ℝ)
    (i : ZMod n → ℕ → ℝ) (E : Finset ℕ),
    1 < p → TTodd ⊆ TT → (∀ s, 0 ≤ al s) → (∀ s, 0 ≤ cap s) → (∀ s e, 0 ≤ i s e) →
    (∀ s e, e ∉ E → i s e = 0) →
    gamP p * ∑ s ∈ TT, al s - ∑ s ∈ TT, ∑ e ∈ E, i s e - de + paid ≤ v →
    ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e ≤ paid →
    (∀ s ∈ TTodd, ∀ e,
      i s e ≤ min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))) →
    gainG p TT TTodd al cap de ≤ v

end Formalism.InvariantFactorPaths.G7
end
end

section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

def UnrOK (K : Type) [NormedField K] (p : ℕ) (σ : K →+* K) : Prop :=
  p.Prime ∧ 2 < p ∧ ‖(p : K)‖ = (p : ℝ)⁻¹ ∧ (∀ a : K, a ≠ 0 → ∃ k : ℤ, ‖a‖ = (p : ℝ) ^ k) ∧
    ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹

section Defs

variable {K : Type} [Field K]

def cob (F : MvPowerSeries (Fin 2) K) (f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst F f - at1 0 f - at1 1 f

def swap2 (H : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] H

def in3 (f : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] f

def d1 (F H : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![in3 F, MvPowerSeries.X 2] H -
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] H -
    MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] H

def DivAB (H : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, n 0 = 0 ∨ n 1 = 0 → MvPowerSeries.coeff n H = 0

end Defs

def IsLawOfLog {K : Type} [NormedField K] (p : ℕ) (F : MvPowerSeries (Fin 2) K) : Prop :=
  MvPowerSeries.constantCoeff F = 0 ∧ Integral F ∧ cob F (lgF K p) = 0

def LawExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ →
    (∃ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F) ∧
    ∀ F F' : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F = 0 →
      MvPowerSeries.constantCoeff F' = 0 → cob F (lgF K p) = 0 → cob F' (lgF K p) = 0 → F = F'

def DivDeriv : Prop :=
  ∀ (K ι κ : Type) [Finite ι] [DecidableEq ι] [NormedField K] [IsUltrametricDist K] [CharZero K]
    (p : ℕ), p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ →
    ∀ (x : ι) (Φ : MvPowerSeries ι K) (φ : ι → MvPowerSeries κ K) (Y : MvPowerSeries κ K),
      Integral (MvPowerSeries.pderiv (R := K) x Φ) →
      (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → (∀ i, Integral (φ i)) →
      MvPowerSeries.constantCoeff Y = 0 → Integral Y →
      ∀ n, ‖MvPowerSeries.coeff n
        (MvPowerSeries.subst (Function.update φ x (φ x + MvPowerSeries.C (p : K) * Y)) Φ -
          MvPowerSeries.subst φ Φ)‖ ≤ (p : ℝ)⁻¹

def DeIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) (σ : K →+* K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → (∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F → Integral (cob F (g0F K p))

def DerivA : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ →
    Integral (MvPowerSeries.pderiv (R := K) 0 (Aser K p) -
      at1 0 (PowerSeries.derivative (R := K) (lgF K p)) * at1 1 (g0F K p)) ∧
    Integral (MvPowerSeries.pderiv (R := K) 0 (Aser' K p))

def LemmaOne : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ f : PowerSeries K, PowerSeries.constantCoeff f = 0 → Integral (cob F f) →
      ∃ (α β : K) (R : PowerSeries K), ‖α‖ ≤ 1 ∧ (∀ n, ‖PowerSeries.coeff n R‖ ≤ 1) ∧
        f = PowerSeries.C α * g0F K p + PowerSeries.C β * lgF K p + R

def LemmaTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ H : MvPowerSeries (Fin 2) K, DivAB H → Integral (d1 F H) → Integral (d1 F (swap2 H)) →
      ∃ (β : K) (R : MvPowerSeries (Fin 2) K), Integral R ∧
        H = MvPowerSeries.C β * (at1 0 (lgF K p) * at1 1 (lgF K p)) + R

def BetaHyp {K : Type} [NormedField K] [CharZero K] (p : ℕ) (F be : MvPowerSeries (Fin 2) K) :
    Prop :=
  DivAB be ∧ Simeq (d1 F be) 0 ∧ Simeq (d1 F (swap2 be)) 0 ∧
    ∀ ζ : K, ζ ^ (p ^ 2 - 1) = 1 →
      Simeq (MvPowerSeries.subst ![MvPowerSeries.C ζ * (MvPowerSeries.X 0 :
          MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] be)
        (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
          MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1] be)

def BetaIsG : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ → (∃ ζ : K, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K, BetaHyp p F be →
      ∃ c : K, ‖c‖ ≤ 1 ∧ σ (σ c) = c ∧ Simeq be (Gser p c (σ c))

end Formalism.InvariantFactorPaths.G7
end
end
