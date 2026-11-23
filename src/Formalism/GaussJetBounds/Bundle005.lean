module

public import Formalism.GaussJetBounds.Bundle003
public import Formalism.GaussJetBounds.Bundle004
public import Mathlib.NumberTheory.Padics.Complex
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

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def TransferB : Prop :=
  ∀ (F K : Type) [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K),
    (∀ z, ‖φ z‖ = ‖z‖) →
    ∀ (l d N0 N1 : ℕ) [NeZero d] (K0 : Subfield F) (ζ : F) (be : MvPowerSeries (ZMod d) F),
      (Unram l K0 → Unram l (K0.map φ)) ∧
      (BHyp l d K0 ζ be → BHyp l d (K0.map φ) (φ ζ) (MvPowerSeries.map φ be)) ∧
      (∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) F,
        (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
        (∀ y, MvPowerSeries.subst g (entLog (K := F) l y) = MvPowerSeries.X y) →
        (∀ y, MvPowerSeries.constantCoeff (MvPowerSeries.map φ (g y)) = 0) ∧
        ∀ y, MvPowerSeries.subst (fun y' => MvPowerSeries.map φ (g y')) (entLog (K := K) l y) =
          MvPowerSeries.X y) ∧
      (∀ U : MvPowerSeries (ZV d N0 N1) F, Integral U → Integral (MvPowerSeries.map φ U))

def FrameJetEval : Prop :=
  ∀ (F K : Type) [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
    (d N0 N1 : ℕ) [NeZero d] (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) F)
    (U : MvPowerSeries (ZV d N0 N1) F) (ε : F) (be : MvPowerSeries (ZMod d) F),
    (∀ y, MvPowerSeries.constantCoeff (g y) = 0) → MvPowerSeries.constantCoeff be = 0 →
    ∀ (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0)
      (I : ∀ s c, Fin (p s c) → Fin N1) (x : ZMod d × Fin N0 × Fin N0 → K),
      MvPolynomial.eval₂ φ x (frameJet colN p hp I (thetaZ g U ε be)) =
        jetPair (∏ s : ZMod d, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K))
            (p s) (hp s) (I s))
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) x))
              (MvPowerSeries.subst (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U)) *
            mvExp (φ ε • bSum (frameM (N1 := N1) x) (MvPowerSeries.map φ be)))

def LabelsExist : Prop :=
  ∀ (l d N0 : ℕ) [NeZero d], 2 ≤ l → ∀ (TT : Finset (ZMod d)) (nu1 size : ZMod d → ℕ) (a : ℕ),
    1 ≤ a → (∀ s, nu1 s ≤ a) → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∃ (J : ZMod d → ℕ) (lab : ∀ s, Fin (J s) → ZMod d × ℤ) (m : ℕ),
      (∀ s, Function.Injective (lab s)) ∧
      (∀ (s s0 : ZMod d) (j : ℤ), (∃ i, lab s i = (s0, j)) ↔
        (s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
          (j < 0 → l ^ (-j).toNat ≤ size s))) ∧
      (∀ s, J s + (if s ∈ TT then 1 else 0) ≤ N0) ∧ (∀ s i, (-(lab s i).2).toNat ≤ m)

def GaussPow : Prop :=
  ∀ (F K : Type) [NormedField F] [NormedField K] (φ : F →+* K) (σ : Type) (Y : σ → K),
    (∀ P : MvPolynomial σ F, ‖MvPolynomial.eval₂ φ Y P‖ = ⨆ n : σ →₀ ℕ, ‖AddMonoidAlgebra.coeff P n‖) →
    ∀ (k : σ → ℕ), (∀ y, k y ≠ 0) → ∀ (P : MvPolynomial σ F) (n : σ →₀ ℕ),
      ‖AddMonoidAlgebra.coeff P n‖ ≤ ‖MvPolynomial.eval₂ φ (fun y => Y y ^ k y) P‖

end Formalism.DworkPowerSeriesWeights
end
end

section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

def IntOp : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type) (Th : MvPowerSeries ι K),
    JetsIntegral Th → ∀ P : MvPolynomial ι K, (∀ n, ‖AddMonoidAlgebra.coeff P n‖ ≤ 1) →
      ‖jetPair P Th‖ ≤ 1

end Formalism.DworkPowerSeriesWeights
end
end

section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def JetPairLin : Prop :=
  ∀ (K : Type u) [Field K] (ι ι' : Type) [Fintype ι] [Fintype ι'] (A : ι → ι' → K)
    (P : MvPolynomial ι K) (F : MvPowerSeries ι' K),
    jetPair P (MvPowerSeries.subst
        (fun j : ι' => (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K)) F) =
      jetPair (MvPolynomial.aeval
        (fun i : ι => (∑ j : ι', MvPolynomial.C (A i j) * MvPolynomial.X j : MvPolynomial ι' K)) P) F

def effMat {K : Type u} [Field K] {d N0 : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (i k : Fin N0) : K :=
  if s ∈ TT ∧ i.val = 0 then (if k = i then 1 else 0)
  else if s ∈ TT ∧ k.val = 0 then 0 else T s i k

def ThmAGen : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → 3 ≤ l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0),
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ x : ZMod d × Fin N0 × Fin N0 → K, (∀ y, ‖x y‖ ≤ 1) →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U → ∀ (ε : K), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1)
      (T : ZMod d → Fin N0 → Fin N0 → K), (∀ s i k, ‖T s i k‖ ≤ 1) →
    ∀ xg : ZMod d × Fin N0 × Fin N0 → K,
      (∀ s i a, xg (s, i, a) = ∑ k : Fin N0, effMat TT T s i k * x (s, k, a)) →
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) →
    ∀ (spec : ZMod d × Fin N0 → Option (ZMod d × ℤ)),
      (∀ (s : ZMod d) (k : Fin N0) (s0 : ZMod d) (j : ℤ), spec (s, k) = some (s0, j) →
        s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ ¬ (s ∈ TT ∧ k.val = 0) ∧
        (0 < j → l ^ j.toNat ≤ nu1 s0) ∧ (j < 0 → l ^ (-j).toNat ≤ size s)) →
      (∀ r r' : ZMod d × Fin N0, spec r ≠ none → spec r = spec r' → r = r') →
      (∀ s0 ∈ TT, ∀ (s : ZMod d) (k : Fin N0) (j : ℤ), ¬ (s ∈ TT ∧ k.val = 0) → Odd j →
        s = s0 + (j : ZMod d) → (0 < j → l ^ j.toNat ≤ nu1 s0) → (j < 0 → l ^ (-j).toNat ≤ size s) →
        spec (s, k) ≠ some (s0, j) →
        (if 0 ≤ j then ‖∑ a : Fin N0, x (s0, ⟨0, h0⟩, a) ^ (l ^ j.toNat) * x (s, k, a)‖
          else ‖∑ a : Fin N0, x (s0, ⟨0, h0⟩, a) * x (s, k, a) ^ (l ^ (-j).toNat)‖) ≤ ‖(l : K)‖) →
      ‖jetPair (∏ s : ZMod d, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K))
            (p s) (hp s) (I s))
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) xg)) (MvPowerSeries.subst g U) *
            mvExp (ε • bSum (frameM (N1 := N1) xg) be))‖ ≤
        ‖(l : K)‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))

end Formalism.DworkPowerSeriesWeights
end
end

section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def ThmAFrame : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → 3 ≤ l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0),
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U → ∀ (ε : K), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ xg : ZMod d × Fin N0 × Fin N0 → K, (∀ y, ‖xg y‖ ≤ 1) →
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) →
    ∀ (J : ZMod d → ℕ) (lab : ∀ s, Fin (J s) → ZMod d × ℤ), (∀ s, Function.Injective (lab s)) →
      (∀ (s s0 : ZMod d) (j : ℤ), (∃ i, lab s i = (s0, j)) ↔
        (s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
          (j < 0 → l ^ (-j).toNat ≤ size s))) →
    ∀ (lam : ∀ s, Fin (J s) → Fin N0 → K), (∀ s i a, ‖lam s i a‖ ≤ 1) →
      (∀ s i a, 0 < (lab s i).2 →
        lam s i a = xg ((lab s i).1, ⟨0, h0⟩, a) ^ (l ^ (lab s i).2.toNat)) →
      (∀ s i a, (lab s i).2 < 0 →
        lam s i a ^ (l ^ (-(lab s i).2).toNat) = xg ((lab s i).1, ⟨0, h0⟩, a)) →
    ∀ (e : ∀ s, Fin (J s) → Fin N0), (∀ s, Function.Injective (e s)) →
      (∀ s i, ¬ (s ∈ TT ∧ (e s i).val = 0)) →
      (∀ s, ‖(Matrix.of fun (i i' : Fin (J s)) => ∑ a, lam s i a * xg (s, e s i', a)).det‖ = 1) →
      ‖jetPair (∏ s : ZMod d, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K))
            (p s) (hp s) (I s))
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) xg)) (MvPowerSeries.subst g U) *
            mvExp (ε • bSum (frameM (N1 := N1) xg) be))‖ ≤
        ‖(l : K)‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))

end Formalism.DworkPowerSeriesWeights
end
end

section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def IsGeneric {K : Type u} [NormedField K] {σ : Type} (l : ℕ) (Y : σ → K) : Prop :=
  ∀ P : MvPolynomial σ ℤ, MvPolynomial.map (Int.castRingHom (ZMod l)) P ≠ 0 →
    ‖MvPolynomial.aeval Y P‖ = 1

def genFrame {K : Type u} [Field K] {d N0 : ℕ} (TT : Finset (ZMod d)) (l m : ℕ)
    (Y : ZMod d × Fin N0 × Fin N0 → K) : ZMod d × Fin N0 × Fin N0 → K :=
  fun y => if y.1 ∈ TT ∧ y.2.1.val = 0 then Y y ^ (l ^ m) else Y y

def ThmAGeneric : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → 3 ≤ l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 → 0 < N0 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U → ∀ (ε : K), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ Y : ZMod d × Fin N0 × Fin N0 → K, IsGeneric l Y →
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) →
    ∀ (J : ZMod d → ℕ) (lab : ∀ s, Fin (J s) → ZMod d × ℤ), (∀ s, Function.Injective (lab s)) →
      (∀ (s s0 : ZMod d) (j : ℤ), (∃ i, lab s i = (s0, j)) ↔
        (s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
          (j < 0 → l ^ (-j).toNat ≤ size s))) →
      (∀ s, J s + (if s ∈ TT then 1 else 0) ≤ N0) →
    ∀ m : ℕ, (∀ s i, (-(lab s i).2).toNat ≤ m) →
      ‖jetPair (∏ s : ZMod d, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K))
            (p s) (hp s) (I s))
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) (genFrame TT l m Y)))
              (MvPowerSeries.subst g U) *
            mvExp (ε • bSum (frameM (N1 := N1) (genFrame TT l m Y)) be))‖ ≤
        ‖(l : K)‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))

def GenericExists : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (σ : Type) [Finite σ],
    ∃ (K : Type) (_ : NormedField K), IsUltrametricDist K ∧ CharZero K ∧
      ∃ (φ : ℂ_[l] →+* K) (Y : σ → K), (∀ z, ‖φ z‖ = ‖z‖) ∧
        (∀ P : MvPolynomial σ ℂ_[l],
          ‖MvPolynomial.eval₂ φ Y P‖ = ⨆ n : σ →₀ ℕ, ‖AddMonoidAlgebra.coeff P n‖) ∧
        IsGeneric l Y

end Formalism.DworkPowerSeriesWeights
end
end
