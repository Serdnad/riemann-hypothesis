module

public import Formalism.GaussJetBounds.Bundle002
public import Formalism.GaussJetBounds.Bundle001
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

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def genLog {K : Type u} [Field K] {τ : Type v} [DecidableEq τ] (l : ℕ) (p : τ → τ) (x : τ) :
    MvPowerSeries τ K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0

def WtGeLe {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (κ : ι →₀ ℕ)
    (f : MvPowerSeries ι K) : Prop :=
  ∀ n : ι →₀ ℕ, n ≤ κ → MonoWtGe pi r w n (MvPowerSeries.coeff n f)

def GenLogWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (τ : Type v) [Finite τ] [DecidableEq τ] (p : τ → τ)
    (g : τ → MvPowerSeries τ K), (∀ x, MvPowerSeries.constantCoeff (g x) = 0) →
      (∀ x, MvPowerSeries.subst g (genLog (K := K) l p x) = MvPowerSeries.X x) →
      ∀ x, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (g x)

def LogBridges : Prop :=
  ∀ (K : Type u) [Field K] (l d N0 N1 : ℕ),
    (∀ x : V2 d, letterLog (K := K) l x = genLog l (fun y : V2 d => (y.1, y.2 - 2)) x) ∧
    (∀ x : ZV d N0 N1, entLog (K := K) l x =
      genLog l (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2)) x) ∧
    (∀ x : Fin N0 × Fin N1, oneLog (K := K) l x = genLog l id x)

def GenLogInverse : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (l : ℕ), l.Prime → ∀ (τ : Type v) [Finite τ]
    [DecidableEq τ] (p : τ → τ),
    ∃ g : τ → MvPowerSeries τ K, (∀ x, MvPowerSeries.constantCoeff (g x) = 0) ∧
      (∀ x, MvPowerSeries.subst g (genLog (K := K) l p x) = MvPowerSeries.X x) ∧
      (∀ x, MvPowerSeries.subst (genLog (K := K) l p) (g x) = MvPowerSeries.X x)

def SubstWt : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (pi : ℝ), 0 < pi → pi < 1 →
    ∀ (σ : Type v) (τ : Type w) [Finite σ] (a : σ → MvPowerSeries τ K) (r : σ → ℝ) (r' : τ → ℝ)
      (wt : ℝ) (f : MvPowerSeries σ K),
      (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, WtGe pi r' (r i) (a i)) →
      WtGe pi r wt f → WtGe pi r' wt (MvPowerSeries.subst a f)

def RadMono : Prop :=
  ∀ (K : Type u) [NormedField K] (pi : ℝ), 0 < pi → pi < 1 → ∀ (ι : Type v) (r r' : ι → ℝ)
    (wt : ℝ), (∀ i, r i ≤ r' i) →
    (∀ f : MvPowerSeries ι K, WtGe pi r wt f → WtGe pi r' wt f) ∧
    (∀ (κ : ι →₀ ℕ) (f : MvPowerSeries ι K), WtGeLe pi r wt κ f → WtGeLe pi r' wt κ f)

def MulWtLe : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (pi : ℝ), 0 < pi →
    ∀ (ι : Type v) (r : ι → ℝ) (w1 w2 : ℝ) (κ : ι →₀ ℕ) (f g : MvPowerSeries ι K),
      WtGeLe pi r w1 κ f → WtGeLe pi r w2 κ g → WtGeLe pi r (w1 + w2) κ (f * g)

def ExpWtLe : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) (r : ι → ℝ) (κ : ι →₀ ℕ) (B : MvPowerSeries ι K),
      MvPowerSeries.constantCoeff B = 0 →
      WtGeLe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) κ B → WtGeLe ‖(l : K)‖ r 0 κ (mvExp B)

def FactVal : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) [Fintype ι] (κ : ι →₀ ℕ),
      ‖((mfact κ : ℕ) : K)‖ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
        (Fintype.card ι : ℝ) * (Real.logb l (κ.degree : ℝ) + 1))

def PureCross : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → ‖(l : K)‖ < 1 →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ZV d N0 N1 → ι → K), (∀ x i, ‖M x i‖ ≤ 1) →
    ∀ be : MvPowerSeries (ZMod d) K, MvPowerSeries.constantCoeff be = 0 →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) be →
      (∀ n, ¬ IsBiPower l n →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n (MvPowerSeries.coeff n be)) →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) (bSum M be) ∧
      ∀ n : ι →₀ ℕ, (¬ ∃ (i j : ι) (α β : ℕ), n = pureMon l i j α β) →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n
          (MvPowerSeries.coeff n (bSum M be))

def LogStep : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) (r : ι → ℝ) (D : MvPowerSeries ι K),
      MvPowerSeries.constantCoeff D = 0 →
      WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) (mvExp D - 1) → WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) D

def ExpDeInv : Prop :=
  ∀ (K : Type u) [NormedField K] [CharZero K] (l d : ℕ) [NeZero d], l.Prime → 2 ≤ d → Even d →
    ∀ (K0 : Subfield K) (ζ : K), IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, (∀ n, MvPowerSeries.coeff n be ∈ K0) →
      MvPowerSeries.subst (torus l ζ) be = be → MvPowerSeries.constantCoeff be = 0 →
      ∀ D ∈ ({de1 be, de2 be} : Set (MvPowerSeries (V2 d) K)),
        (∀ n, MvPowerSeries.coeff n (mvExp D) ∈ K0) ∧
        ∀ n : V2 d →₀ ℕ, MvPowerSeries.coeff n (mvExp D) ≠ 0 →
          ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2

def Quant : Prop :=
  ∀ (K : Type u) [NormedField K] (l d : ℕ) [NeZero d], l.Prime → 2 ≤ d → Even d →
    ‖(l : K)‖ < 1 → 0 < ‖(l : K)‖ → ∀ (K0 : Subfield K), Unram l K0 →
    ∀ (c : K), c ∈ K0 → ∀ n : V2 d →₀ ℕ,
      ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2 →
      MonoWtGe ‖(l : K)‖ (fun _ => rho l) (rho l) n c →
      MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n c

def BinomExtract : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d],
    l.Prime → Odd l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 →
    ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) → ∀ be : MvPowerSeries (ZMod d) K,
      MvPowerSeries.subst (torus l ζ) be = be → NoLowBidegree be →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (de1 be) →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (de2 be) →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) be ∧
      ∀ n, ¬ IsBiPower l n →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n (MvPowerSeries.coeff n be)

end Formalism.DworkPowerSeriesWeights
end
end

section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def frameM {K : Type u} [Field K] {d N0 N1 : ℕ} (x : ZMod d × Fin N0 × Fin N0 → K) :
    ZV d N0 N1 → ZV d N0 N1 → K :=
  fun z y => if y.1 = z.1 ∧ y.2.2 = z.2.2 then x (z.1, y.2.1, z.2.1) else 0

def FramePure : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0) (x : ZMod d × Fin N0 × Fin N0 → K), (∀ y, ‖x y‖ ≤ 1) →
    ∀ be : MvPowerSeries (ZMod d) K,
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) be →
    ∀ (s s' : ZMod d), s ≠ s' → ∀ (k : Fin N0) (b b' : Fin N1) (α β : ℕ),
      (b ≠ b' → MvPowerSeries.coeff (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b') α β)
          (bSum (frameM (N1 := N1) x) be) = 0) ∧
      ((if β ≤ α then ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ (α - β)) * x (s', k, a)‖
          else ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) * x (s', k, a) ^ (l ^ (β - α))‖) ≤ ‖(l : K)‖ →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1))
          (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b) α β)
          (MvPowerSeries.coeff (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b) α β)
            (bSum (frameM (N1 := N1) x) be)))

end Formalism.DworkPowerSeriesWeights
end
end

section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def frameTop {d N0 N1 : ℕ} (TT : Finset (ZMod d)) (y : ZV d N0 N1) : Bool :=
  decide (y.1 ∈ TT ∧ y.2.1.val = 0)

end Formalism.DworkPowerSeriesWeights
end
end

section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

def JetsIntegral {K : Type u} [NormedField K] {ι : Type} (sg : MvPowerSeries ι K) : Prop :=
  ∀ κ : ι →₀ ℕ, ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ sg‖ ≤ 1

end Formalism.DworkPowerSeriesWeights
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def idM {K : Type} [Field K] {d N0 N1 : ℕ} : ZV d N0 N1 → ZV d N0 N1 → K :=
  fun x y => if x = y then 1 else 0

def thetaZ {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]
    (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K) (U : MvPowerSeries (ZV d N0 N1) K) (ε : K)
    (be : MvPowerSeries (ZMod d) K) : MvPowerSeries (ZV d N0 N1) K :=
  MvPowerSeries.subst (linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K)) (MvPowerSeries.subst g U) *
    mvExp (ε • bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) be)

def jetPairPoly {K : Type} [Field K] {σ ι : Type} (P : MvPolynomial ι (MvPolynomial σ K))
    (Th : MvPowerSeries ι K) : MvPolynomial σ K :=
  ∑ κ ∈ P.support, AddMonoidAlgebra.coeff P κ *
    MvPolynomial.C (((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th)

def frameJet {K : Type} [Field K] {d N0 N1 : ℕ} [NeZero d] (colN : ZMod d → ℕ)
    (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) (I : ∀ s c, Fin (p s c) → Fin N1)
    (Th : MvPowerSeries (ZV d N0 N1) K) : MvPolynomial (ZMod d × Fin N0 × Fin N0) K :=
  jetPairPoly (∏ s : ZMod d, minorProd
    (fun (i : Fin N0) (b : Fin N1) =>
      (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (s, i, a)) * MvPolynomial.X (s, a, b) :
        MvPolynomial (ZV d N0 N1) (MvPolynomial (ZMod d × Fin N0 × Fin N0) K)))
    (p s) (hp s) (I s)) Th

def ThmAGauss : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d N0 N1 : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (K0 : Subfield ℂ_[l]), Unram l K0 → ∀ ζ : ℂ_[l], IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) ℂ_[l], BHyp l d K0 ζ be →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l],
      (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[l]) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) ℂ_[l], Integral U → ∀ (ε : ℂ_[l]), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∀ n : (ZMod d × Fin N0 × Fin N0) →₀ ℕ,
      ‖AddMonoidAlgebra.coeff (frameJet colN p hp I (thetaZ g U ε be)) n‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))

end Formalism.DworkPowerSeriesWeights
end
end
