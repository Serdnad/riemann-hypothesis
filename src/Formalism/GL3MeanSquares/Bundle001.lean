module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.Continuity
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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

namespace Formalism.HermitianLattices.LocalLatticeBases

open Finset Matrix

def LemmaB'_avg : Prop :=
  ∀ (k n : ℕ) (S : Finset (Fin k → ℕ)) (mult : (Fin k → ℕ) → ℕ),
    (∀ σ : Equiv.Perm (Fin k), ∀ w ∈ S, w ∘ σ ∈ S) →
    (∀ σ : Equiv.Perm (Fin k), ∀ w, mult (w ∘ σ) = mult w) →
    (∀ w ∈ S, ∑ i, w i = n) →
    ∀ j : Fin k, k * ∑ w ∈ S, mult w * w j = n * ∑ w ∈ S, mult w

end Formalism.HermitianLattices.LocalLatticeBases
end

section

open Finset ArithmeticFunction Classical

noncomputable section

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

def X1 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5))

def X2 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5) * Real.log x ^ 2)

def logDerivLAtOne {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1

def Gchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((y / n - 1 : ℝ) : ℂ)) + (y : ℂ) * logDerivLAtOne χ

def G1 (y : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * (y / n - 1)) - y * (Real.log y - 1 - Real.eulerMascheroniConstant)

def cN (x : ℝ) (n : ℕ) : ℝ := Λ n * min 1 (x / n)

def Sz {q : ℕ} (χ : DirichletCharacter ℂ q) (x z : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊z⌋₊, ((cN x n : ℝ) : ℂ) * χ (n : ZMod q)

def tailL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℝ) : ℂ :=
  - logDerivLAtOne χ - ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)

def qc (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ q :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)

def chi8 : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

instance neZeroMulPrime {t q : ℕ} [NeZero t] [Fact q.Prime] : NeZero (t * q) :=
  ⟨Nat.mul_ne_zero (NeZero.ne t) (Fact.out : q.Prime).ne_zero⟩

def tw {t : ℕ} (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ (t * q) :=
  DirichletCharacter.changeLevel (Dvd.intro q rfl) θ * DirichletCharacter.changeLevel (Dvd.intro_left t rfl) (qc q)

def ZeroFreeBox {N : ℕ} [NeZero N] (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction χ s ≠ 0

def GoodFor {N : ℕ} [NeZero N] (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ (N : ℝ) ≤ Q ∧ ZeroFreeBox Q χ

def PPset (m₀ a₀ : ℕ) (X : ℝ) : Finset ℕ :=
  (Icc 1 ⌊X⌋₊).filter (fun q => q.Prime ∧ q % m₀ = a₀ % m₀ ∧ X ^ (1 / 2 : ℝ) < (q : ℝ))

def oddM (y : ℝ) (q₁ : ℕ) : ℕ := q₁ * ∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p

def IsNormOne (d N p : ℕ) : Prop :=
  ∃ u v : ℤ, (N : ℤ) ∣ u - 1 ∧ (N : ℤ) ∣ v ∧ (p : ℤ) = u ^ 2 + u * v + (((d + 1) / 4 : ℕ) : ℤ) * v ^ 2

def normPrimes (d N : ℕ) (lo hi : ℝ) : Finset ℕ :=
  (Icc 1 ⌊hi⌋₊).filter (fun p => p.Prime ∧ lo < (p : ℝ) ∧ IsNormOne d N p)

def rho (c Cρ B X : ℝ) : ℝ :=
  Cρ * Real.exp (-c * Real.log X / Real.log B) + Cρ * Real.exp (-c * Real.log X ^ (1 / 2 : ℝ))

def BoxCountHyp (C : ℝ) : Prop :=
  ∀ (t : ℕ) [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (S : Finset ℕ), θ.IsPrimitive → θ ^ 2 = 1 →
    (∀ q ∈ S, ∃ _ : Fact q.Prime, q % 4 = 3 ∧ q.Coprime t ∧ ((t * q : ℕ) : ℝ) ≤ Q ∧ ¬ ZeroFreeBox Q (tw θ q)) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)

def BoxTailHyp (ε C x₀ : ℝ) : Prop :=
  ∀ (x Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), x₀ ≤ x → x ^ (ε / 6) ≤ Real.log Q →
    Real.log Q ≤ x ^ (ε / 4) → χ ≠ 1 → GoodFor Q χ →
    ‖(x : ℂ) * tailL χ (x ^ 400)‖ ≤ x ^ ε ∧ ‖logDerivLAtOne χ‖ ≤ C * Real.log x

def IntervalHyp (C₀ c Cρ c₃ : ℝ) : Prop :=
  ∀ (d N : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 1 ≤ N → (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ C₀ ≤ X →
    rho c Cρ (4 * (d : ℝ) * (N : ℝ) ^ 2) X ≤ h / 100 → 0 < h → h ≤ 1 →
    (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ 7 ≤ h * X ^ (1 / 3 : ℝ) →
    c₃ * h * (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ (-6 : ℝ) * X / Real.log X ≤ ((normPrimes d N X (X * (1 + h))).card : ℝ)

def GFiniteSplit : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x z : ℝ), 0 < x → x ≤ z →
    Gchi χ x = - Sz χ x z - (x : ℂ) * tailL χ z

def UnitModulusIncrementConditions : Prop :=
  ∀ ε C : ℝ, 0 < ε → ε ≤ 1 → 0 < C → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    x ^ 400 < X1 ε x ^ (1 / 2 : ℝ) ∧ 2 ≤ x ^ (ε / 5) ∧
    (1 / 4) * Real.log x ^ 2 * Real.log 8 ≤ Real.log (X1 ε x) ∧
    Real.log x ^ 2 * Real.log (8 * (x ^ 400) ^ 2) ≤ Real.log (X1 ε x) ∧
    x ^ (ε / 6) ≤ Real.log (X1 ε x) ∧
    x ^ (ε / 6) ≤ Real.log (8 * X1 ε x) ∧ Real.log (8 * X1 ε x) ≤ x ^ (ε / 4) ∧
    C * x * Real.log x / (x ^ (1 / 2 + ε) / 2) ^ 2 ≤ x ^ (-ε) ∧ x ^ (-ε) ≤ 1 / 8 ∧
    2 * (C * (8 * X1 ε x) ^ (1 / 4 : ℝ)) ≤ X1 ε x ^ (9 / 10 : ℝ) / 2

def TwEval : Prop :=
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime] (n : ℕ),
    tw θ q (n : ZMod (t * q)) = θ (n : ZMod t) * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)

def TwPrimitive : Prop :=
  (chi8.IsPrimitive ∧ chi8 ^ 2 = 1) ∧
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime], θ.IsPrimitive → q ≠ 2 → q.Coprime t →
    (tw θ q).IsPrimitive ∧ tw θ q ≠ 1 ∧ (θ ^ 2 = 1 → tw θ q ^ 2 = 1)

def SmoothingSizeBounds : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y lam : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y → 0 < lam →
    lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    x ^ (ε / 3) / 2 ≤ Real.log y ∧ x ^ (2 * ε / 15) / (4 * Real.log x ^ 2) ≤ Real.log y / lam ∧
    x ^ (ε / 6) / 2 ≤ Real.sqrt (Real.log y)

def ThinIntegral : Prop :=
  ∀ ε c : ℝ, 0 < ε → 0 < c → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ V lam : ℝ, x ^ (ε / 3) / 2 ≤ V → 1 ≤ lam →
    lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    MeasureTheory.IntegrableOn (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) ∧
    (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤ Real.exp (-c' * x ^ (ε / 8))

def TailIntegralBoundOfPsiBound : Prop :=
  ∀ ε c C : ℝ, 0 < ε → 0 < c → 0 < C → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ (y lam : ℝ) (psi0 : ℝ → ℂ),
    Real.exp (x ^ (ε / 3)) / 3 ≤ y → 1 ≤ lam → lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ u : ℝ, y ≤ u → ‖psi0 u‖ ≤
      C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) →
    ‖(y : ℂ) * ∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ y * Real.exp (-c' * x ^ (ε / 8))

end Formalism.HermitianLattices.ZeroFreeRegionGL2
end
end

section

noncomputable section

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset



def SeSign : Prop :=
  ∀ (A : Type) [CommRing A] (q : ℕ) (ε η : A), Odd q → ε ^ q = η * ε → η * η = 1 →
    ∀ (n : ℕ) (ζ : ZMod n → A) (e : ZMod n) (L : ℕ),
      ∑ l ∈ range L, (-η) ^ l * (ε * ζ (e - 2 * (l : ZMod n))) ^ (q ^ l) =
        ε * ∑ l ∈ range L, (-1) ^ l * ζ (e - 2 * (l : ZMod n)) ^ (q ^ l)


def PowerCongruenceIffEqual : Prop :=
  ∀ (l d s s' : ℕ), 2 ≤ l → s < d → s' < d →
    ((l ^ d - 1 : ℕ) : ℤ) ∣ (l : ℤ) ^ s - (l : ℤ) ^ s' → s = s'

def cob {M Q : Type} [AddCommGroup M] [AddCommGroup Q] (φ : M → Q) (a b : M) : Q :=
  φ (a + b) - φ a - φ b

def NormAllAlpha : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm tr : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) → (∀ α, algebraMap Z O (tr α) = star α + α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (z : Z) a b, cob φ a (algebraMap Z O z • b) = z • cob φ a b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ x : Q, x + x = 0 → x = 0) →
    ∀ (α α' : O) (u : M), φ ((2 : O) • u) = (4 : Z) • φ u →
      φ (α • u) = nm α • φ u → φ (α' • u) = nm α' • φ u →
      φ ((α + α') • u) = nm (α + α') • φ u

def UnitaryInvariance : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (δ : Matrix n n O), δ.conjTranspose * δ = 1 →
      ∀ u : n → M, ∑ i, φ (∑ j, δ i j • u j) = ∑ j, φ (u j)

def HyperbolicSplit : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n ι : Type) [Fintype n] [Fintype ι] [DecidableEq ι] (f f' : ι → n → O),
      (∀ e e', ∑ i, star (f e i) * f e' i = 0) → (∀ e e', ∑ i, star (f' e i) * f' e' i = 0) →
      (∀ e e', ∑ i, star (f e i) * f' e' i = if e = e' then 1 else 0) →
      ∀ t t' : ι → M,
        ∑ i, φ (∑ e, (f e i • t e + f' e i • t' e)) = ∑ e, cob φ (t e) (t' e)

def IntegerMeanLog : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : NumberField.RingOfIntegers K), x ≠ 0 →
    0 ≤ ∑ φ : K →+* ℂ, Real.log ‖φ (x : K)‖

def WeberRoot : Prop :=
  ∀ (x j : ℂ) (s : ℤ), (s = 16 ∨ s = -16) → IsIntegral ℤ j → (x - (s : ℂ)) ^ 3 = j * x →
    IsIntegral ℤ x ∧ x ≠ 0

end Formalism.HermitianLattices.IntegralLatticeDensity
end
end

section

namespace Formalism.HermitianLattices.RamifiedLatticeOperators

open Finset Matrix ComplexConjugate

def Fubini_orbits : Prop :=
  ∀ (Γ P Q V : Type) [Group Γ] [MulAction Γ P] [MulAction Γ Q] [AddCommGroup V] [Module ℚ V]
    (pr : P → Q) (fib : Q → Finset P) (Ψ : P → V) (RP : Finset P) (RQ : Finset Q),
    (∀ (γ : Γ) (p : P), pr (γ • p) = γ • pr p) → (∀ p y, p ∈ fib y ↔ pr p = y) →
    (∀ (γ : Γ) (p : P), Ψ (γ • p) = Ψ p) →
    (∀ y : Q, Finite (MulAction.stabilizer Γ y)) →
    (∀ p : P, ∃! r, r ∈ RP ∧ r ∈ MulAction.orbit Γ p) →
    (∀ y : Q, ∃! r, r ∈ RQ ∧ r ∈ MulAction.orbit Γ y) →
    ∑ p ∈ RP, ((Nat.card (MulAction.stabilizer Γ p) : ℚ))⁻¹ • Ψ p =
      ∑ y ∈ RQ, ((Nat.card (MulAction.stabilizer Γ y) : ℚ))⁻¹ • ∑ p ∈ fib y, Ψ p

def Count_orbits : Prop :=
  ∀ (Γ A B V : Type) [Group Γ] [MulAction Γ A] [MulAction Γ B] [AddCommGroup V] [Module ℚ V]
    (up : A → Finset B) (down : B → Finset A) (G : A → B → V) (RA : Finset A) (RB : Finset B),
    (∀ a b, b ∈ up a ↔ a ∈ down b) → (∀ (γ : Γ) a b, b ∈ up a → γ • b ∈ up (γ • a)) →
    (∀ (γ : Γ) a b, b ∈ up a → G (γ • a) (γ • b) = G a b) →
    (∀ a : A, Finite (MulAction.stabilizer Γ a)) → (∀ b : B, Finite (MulAction.stabilizer Γ b)) →
    (∀ a : A, ∃! r, r ∈ RA ∧ r ∈ MulAction.orbit Γ a) →
    (∀ b : B, ∃! r, r ∈ RB ∧ r ∈ MulAction.orbit Γ b) →
    ∑ a ∈ RA, ((Nat.card (MulAction.stabilizer Γ a) : ℚ))⁻¹ • ∑ b ∈ up a, G a b =
      ∑ b ∈ RB, ((Nat.card (MulAction.stabilizer Γ b) : ℚ))⁻¹ • ∑ a ∈ down b, G a b

def LemmaB'_length : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (ι : Type) [Fintype ι] (deg : ι → ℕ),
      Module.length R ((ι → R) ⧸
        (Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ deg i}) : Submodule R (ι → R))) =
        ((∑ i, deg i : ℕ) : ℕ∞)

end Formalism.HermitianLattices.RamifiedLatticeOperators
end
