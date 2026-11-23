module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
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
import Mathlib.Data.Nat.Choose.Multinomial
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
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def ZetaSummable : Prop :=
  ∀ (L : PeriodPair) (z : ℂ),
    Summable (fun l : L.lattice => 1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)

def ZetaHasDeriv : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → HasDerivAt (wZeta L) (-(L.weierstrassP z)) z

def ZetaOdd : Prop := ∀ (L : PeriodPair) (z : ℂ), wZeta L (-z) = -wZeta L z

def ZetaQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice → z ∉ L.lattice → wZeta L (z + ω) = wZeta L z + wEta L ω

def SigmaSummable : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), Summable (fun l : L.lattice => ‖wFactor (l : ℂ) z - 1‖)

def SigmaProdLU : Prop :=
  ∀ L : PeriodPair, HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z)
    (fun z => ∏' l : L.lattice, wFactor (l : ℂ) z) Set.univ

def SigmaEntire : Prop := ∀ L : PeriodPair, Differentiable ℂ (wSigma L)

def SigmaOdd : Prop := ∀ (L : PeriodPair) (z : ℂ), wSigma L (-z) = -wSigma L z

def SigmaZero : Prop := ∀ (L : PeriodPair) (z : ℂ), wSigma L z = 0 ↔ z ∈ L.lattice

def SigmaSimple : Prop :=
  ∀ L : PeriodPair, deriv (wSigma L) 0 = 1 ∧ ∀ z ∈ L.lattice, deriv (wSigma L) z ≠ 0

def SigmaLogDeriv : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → HasDerivAt (wSigma L) (wZeta L z * wSigma L z) z

def SigmaQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice →
    wSigma L (z + ω) = semiChar L ω * Complex.exp (wEta L ω * (z + ω / 2)) * wSigma L z

def EtaEisenstein : Prop :=
  ∀ L : PeriodPair,
    wEta L L.ω₁ = L.ω₁ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 ∧
    wEta L L.ω₂ = L.ω₂ * ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2

def Legendre : Prop :=
  ∀ L : PeriodPair,
    wEta L L.ω₁ * L.ω₂ - wEta L L.ω₂ * L.ω₁
      = (if 0 < (L.ω₂ / L.ω₁).im then 1 else -1) * (2 * (Real.pi : ℂ) * Complex.I)

end Formalism.L2.Th1.F
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def IsPeriodic (L : PeriodPair) (f : ℂ → ℂ) : Prop := ∀ ω ∈ L.lattice, ∀ z, f (z + ω) = f z

def EllipticEntire : Prop :=
  ∀ (L : PeriodPair) (f : ℂ → ℂ), Differentiable ℂ f → IsPeriodic L f → ∀ z, f z = f 0

def EllipticNoPole : Prop :=
  ∀ (L : PeriodPair) (f : ℂ → ℂ), (∀ z, MeromorphicAt f z) → IsPeriodic L f →
    (∀ z, 0 ≤ meromorphicOrderAt f z) → ∃ c : ℂ, ∀ z, ContinuousAt f z → f z = c

def EllipticOnePole : Prop :=
  ∀ (L : PeriodPair) (f : ℂ → ℂ) (p : ℂ), (∀ z, MeromorphicAt f z) → IsPeriodic L f →
    (∀ z, z - p ∉ L.lattice → 0 ≤ meromorphicOrderAt f z) → -1 ≤ meromorphicOrderAt f p →
    ∃ c : ℂ, ∀ z, ContinuousAt f z → f z = c

def SigmaOrder : Prop :=
  ∀ (L : PeriodPair) (a b z : ℂ), a ≠ 0 →
    meromorphicOrderAt (fun w => wSigma L (a * w + b)) z
      = (by classical exact if a * z + b ∈ L.lattice then 1 else 0)

def SigmaAdd : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice →
    wSigma L (z + w) * wSigma L (z - w)
      = -(wSigma L z ^ 2 * wSigma L w ^ 2 * (L.weierstrassP z - L.weierstrassP w))

def SgStarAdd : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice →
    sgStar L (z + w) * sgStar L (z - w)
      = -(sgStar L z ^ 2 * sgStar L w ^ 2 * (L.weierstrassP z - L.weierstrassP w))

def PInjective : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice →
    (L.weierstrassP z = L.weierstrassP w ↔ z - w ∈ L.lattice ∨ z + w ∈ L.lattice)

def PDerivZero : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → (L.derivWeierstrassP z = 0 ↔ 2 * z ∈ L.lattice)

def SigmaDouble : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice →
    wSigma L (2 * z) = -(L.derivWeierstrassP z) * wSigma L z ^ 4

def DiscNeZero : Prop := ∀ L : PeriodPair, L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0

def ZetaAdd : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice → z + w ∉ L.lattice → z - w ∉ L.lattice →
    wZeta L (z + w) = wZeta L z + wZeta L w
      + (L.derivWeierstrassP z - L.derivWeierstrassP w) / (2 * (L.weierstrassP z - L.weierstrassP w))

def SigmaThree : Prop :=
  ∀ (L : PeriodPair) (a b c : ℂ), a ∉ L.lattice → b ∉ L.lattice → c ∉ L.lattice →
    (Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                   1, L.weierstrassP b, L.derivWeierstrassP b;
                   1, L.weierstrassP c, L.derivWeierstrassP c])
        * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a)

def SgStarThree : Prop :=
  ∀ (L : PeriodPair) (a b c : ℂ), a ∉ L.lattice → b ∉ L.lattice → c ∉ L.lattice →
    (Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                   1, L.weierstrassP b, L.derivWeierstrassP b;
                   1, L.weierstrassP c, L.derivWeierstrassP c])
        * (sgStar L a * sgStar L b * sgStar L c) ^ 3
      = 2 * sgStar L (a + b + c) * sgStar L (a - b) * sgStar L (b - c) * sgStar L (c - a)

def ThetaLine : Prop :=
  ∀ (L : PeriodPair) (F : ℂ → ℂ), Differentiable ℂ F →
    (∀ ω ∈ L.lattice, ∀ z, semiChar L ω * opU L ω F z = F z) → ∃ c : ℂ, ∀ z, F z = c * sgStar L z

end Formalism.L2.Th1.F
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def altE (L : PeriodPair) (x y : ℂ) : ℝ := (herm L x y).im

def AreaPos : Prop := ∀ L : PeriodPair, 0 < area L

def EtaSplit : Prop :=
  ∀ (L : PeriodPair) (x : ℂ), wEta L x = s2 L * x + ((Real.pi : ℂ) / (area L : ℂ)) * conj x

def AltEInt : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ), x ∈ L.lattice → y ∈ L.lattice → ∃ k : ℤ, altE L x y = k

def AltEBasis : Prop :=
  ∀ L : PeriodPair, altE L L.ω₁ L.ω₂ = if 0 < (L.ω₂ / L.ω₁).im then -1 else 1

def SemiCharMul : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ), x ∈ L.lattice → y ∈ L.lattice →
    semiChar L (x + y)
      = semiChar L x * semiChar L y * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L x y : ℂ))

def SgStarQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice →
    sgStar L (z + ω) = semiChar L ω
      * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * sgStar L z

def SgStarFixed : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice → semiChar L ω * opU L ω (sgStar L) z = sgStar L z

def SgStarBasic : Prop :=
  ∀ L : PeriodPair, Differentiable ℂ (sgStar L) ∧ (∀ z, sgStar L (-z) = -sgStar L z) ∧
    (∀ z, sgStar L z = 0 ↔ z ∈ L.lattice) ∧
    deriv (sgStar L) 0 = 1 ∧ iteratedDeriv 3 (sgStar L) 0 = -3 * s2 L

def OpUMul : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ) (F : ℂ → ℂ) (z : ℂ),
    opU L x (opU L y F) z
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x y : ℂ)) * opU L (x + y) F z

def OpUComm : Prop :=
  ∀ (L : PeriodPair) (F : ℂ → ℂ) (z : ℂ), opU L 0 F z = F z ∧ ∀ x y : ℂ,
    opU L x (opU L y F) z
      = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE L x y : ℂ)) * opU L y (opU L x F) z

def ThetaZeroConstant : Prop :=
  ∀ (L : PeriodPair) (t : ℂ), opU L t (sgStar L) 0
      = sgStar L t * Complex.exp (-(Real.pi : ℂ) * herm L t t / 2) ∧
    (t ∉ L.lattice → opU L t (sgStar L) 0 ≠ 0)

def ThetaZeroBasic : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    Differentiable ℂ (th0 L (ω₀ / 2)) ∧ th0 L (ω₀ / 2) 0 = 1 ∧
    (∀ z, th0 L (ω₀ / 2) (-z) = th0 L (ω₀ / 2) z) ∧
    (∀ z, th0 L (ω₀ / 2) z = 0 ↔ z + ω₀ / 2 ∈ L.lattice) ∧
    ∀ ω ∈ L.lattice, ∀ z, th0 L (ω₀ / 2) (z + ω)
      = semiChar L ω * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω ω₀ : ℂ))
        * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * th0 L (ω₀ / 2) z

def ThetaZeroClass : Prop :=
  ∀ (L : PeriodPair) (t ω z : ℂ), ω ∈ L.lattice → t ∉ L.lattice → th0 L (t + ω) z = th0 L t z

def ThetaZeroLogDerivative : Prop :=
  ∀ (L : PeriodPair) (ω₀ z : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice → z + ω₀ / 2 ∉ L.lattice →
    HasDerivAt (th0 L (ω₀ / 2))
      ((wZeta L (z + ω₀ / 2) - wZeta L (ω₀ / 2) - s2 L * z) * th0 L (ω₀ / 2) z) z

end Formalism.L2.Th1.F
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have h := L.indep
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp this).resolve_left hc

def LatticeOnly : Prop :=
  ∀ L L' : PeriodPair, L.lattice = L'.lattice →
    wZeta L = wZeta L' ∧ wSigma L = wSigma L' ∧ wEta L = wEta L' ∧ area L = area L' ∧ s2 L = s2 L' ∧
    sgStar L = sgStar L' ∧ L.weierstrassP = L'.weierstrassP ∧ L.g₂ = L'.g₂ ∧ L.g₃ = L'.g₃

def Homogeneity : Prop :=
  ∀ (L : PeriodPair) (c : ℂ) (hc : c ≠ 0),
    (∀ z, z ∈ (scalePair L c hc).lattice ↔ c⁻¹ * z ∈ L.lattice) ∧
    (∀ z, wZeta (scalePair L c hc) (c * z) = c⁻¹ * wZeta L z) ∧
    (∀ z, wSigma (scalePair L c hc) (c * z) = c * wSigma L z) ∧
    (∀ z, (scalePair L c hc).weierstrassP (c * z) = (c ^ 2)⁻¹ * L.weierstrassP z) ∧
    (∀ z, wEta (scalePair L c hc) (c * z) = c⁻¹ * wEta L z) ∧
    area (scalePair L c hc) = ‖c‖ ^ 2 * area L ∧
    s2 (scalePair L c hc) = (c ^ 2)⁻¹ * s2 L ∧
    (∀ z, sgStar (scalePair L c hc) (c * z) = c * sgStar L z) ∧
    (∀ t z, th0 (scalePair L c hc) (c * t) (c * z) = th0 L t z) ∧
    (scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ ∧ (scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃

def MulStable (L : PeriodPair) (α : ℂ) : Prop := ∀ ω ∈ L.lattice, α * ω ∈ L.lattice

def IsKerReps (L : PeriodPair) (α : ℂ) (S : Finset ℂ) : Prop :=
  (∀ P ∈ S, α * P ∈ L.lattice ∧ P ∉ L.lattice) ∧
  (∀ P ∈ S, ∀ Q ∈ S, P - Q ∈ L.lattice → P = Q) ∧
  (∀ z, α * z ∈ L.lattice → z ∉ L.lattice → ∃ P ∈ S, z - P ∈ L.lattice)

def KerRepsExist : Prop :=
  ∀ (L : PeriodPair) (α : ℂ), α ≠ 0 → MulStable L α → ∃ S : Finset ℂ, IsKerReps L α S

def KerRepsCard : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ((S.card : ℝ) + 1) = Complex.normSq α

def MulStableIntegral : Prop :=
  ∀ (L : PeriodPair) (α : ℂ), MulStable L α →
    ∃ t n : ℤ, α + conj α = (t : ℂ) ∧ α * conj α = (n : ℂ) ∧ α ^ 2 - (t : ℂ) * α + (n : ℂ) = 0

def IsogenyP : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ∀ z, α * z ∉ L.lattice →
      α ^ 2 * L.weierstrassP (α * z)
        = L.weierstrassP z + ∑ P ∈ S, (L.weierstrassP (z + P) - L.weierstrassP P)

def IsogenySigma : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ∀ z, z ∉ L.lattice →
      sgStar L (α * z) ^ 2
        = α ^ 2 * sgStar L z ^ (2 * (S.card + 1)) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP P)

def QuasiPeriodConstIsogeny : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    (α ^ 2 - (Complex.normSq α : ℂ)) * s2 L = ∑ P ∈ S, L.weierstrassP P

def HalfShift : Prop :=
  ∀ (L : PeriodPair) (t z : ℂ), t ∉ L.lattice → 2 * t ∈ L.lattice → z ∉ L.lattice → z + t ∉ L.lattice →
    (L.weierstrassP (z + t) - L.weierstrassP t) * (L.weierstrassP z - L.weierstrassP t)
      = 3 * L.weierstrassP t ^ 2 - L.g₂ / 4

def PSecond : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice →
    HasDerivAt L.derivWeierstrassP (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z

def TranslateProduct : Prop :=
  ∀ (L : PeriodPair) (P Q z : ℂ), Q ∉ L.lattice → z + P ∉ L.lattice →
    opU L (P + Q) (sgStar L) z * opU L (P - Q) (sgStar L) z
      = opU L Q (sgStar L) 0 ^ 2 * (L.weierstrassP Q - L.weierstrassP (z + P))
        * opU L P (sgStar L) z ^ 2

end Formalism.L2.Th1.F
end
end
