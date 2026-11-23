module

public import Formalism.PieriBlockIdeals.PieriColumnMinors.RowGenDerivative
public import Formalism.GradedWeylDivisibility.StatementE
public import Mathlib.RingTheory.TensorProduct.Basic
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle670
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle672
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Formalism.LocalRingCardinality.DataTheta
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

def GlRel (N : ℕ) {A : Type} [Ring A] (e : ℕ → ℕ → A) : Prop :=
  ∀ a b c d : ℕ, a < N → b < N → c < N → d < N →
    e a b * e c d - e c d * e a b = (if b = c then e a d else 0) - (if d = a then e c b else 0)

def coef (j k : ℕ) : ℚ := (-1) ^ k * (j.factorial : ℚ) / ((k.factorial : ℚ) * ((k + j + 1).factorial : ℚ))

def proj {A : Type} [Ring A] [Algebra ℚ A] (K j : ℕ) (X Y : A) : A :=
  ∑ k ∈ Finset.range (K + 1), coef j k • (Y ^ k * X ^ k)

def rootP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K i j : ℕ) : A :=
  proj K (j - i - 1) (D i j) (D j i)

def rowP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K i s n : ℕ) : A :=
  ((List.range' s n).map (rootP D K i)).prod

def gridP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K a b t : ℕ) : A :=
  ((List.range t).reverse.map fun i => rowP D K i a b).prod

def adj {A : Type} [Ring A] [Algebra ℚ A] (x : A) : Module.End ℚ A :=
  LinearMap.mulLeft ℚ x - LinearMap.mulRight ℚ x

def IsWt (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) (μ : ℕ → ℤ) (x : V) : Prop :=
  ∀ c < N, e c c x = (μ c : ℚ) • x

def Bdd (N K : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) : Prop :=
  ∀ a < N, ∀ b < N, ∀ (n : ℤ) (x : V), e a a x - e b b x = (n : ℚ) • x → (K : ℤ) < n → x = 0

def Dom (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) : Prop :=
  ∀ (μ : ℕ → ℤ) (x : V), IsWt N e μ x → x ≠ 0 →
    (∀ k ≤ N, ∑ c ∈ Finset.range k, μ c ≤ ∑ c ∈ Finset.range k, lam c) ∧
      ∑ c ∈ Finset.range N, μ c = ∑ c ∈ Finset.range N, lam c

def WtSpan (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) : Prop :=
  Submodule.span ℚ {x : V | ∃ μ : ℕ → ℤ, IsWt N e μ x} = ⊤

def DivStable (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V)
    (L : Submodule ℤ V) : Prop :=
  ∀ i < N, ∀ j < N, i ≠ j → ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (e i j ^ k) x ∈ L

def RankOne : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (N K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel N D → Bdd N (2 * K) D →
    ∀ o q : ℕ, o < N → q < N → o ≠ q → ∀ T : W, D o o T = 0 → D q q T = 0 →
      D o q (proj K 0 (D o q) (D q o) T) = 0 ∧ (D o q T = 0 → D q o T = 0)

def RankTwo : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (N K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel N D → Bdd N (2 * K) D →
    ∀ o p q : ℕ, o < N → p < N → q < N → o ≠ p → o ≠ q → p ≠ q → ∀ (j : ℕ) (T : W),
      D o o T = 0 → D p p T = 0 → D q q T = 0 → D p q T = 0 →
      D p q (proj K j (D o p) (D p o) (proj K (j + 1) (D o q) (D q o) T)) = 0

def GridInv : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (a b K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel (a + b) D →
    Bdd (a + b) (2 * K) D → ∀ T : W, (∀ c < a + b, ∀ d < a + b, (c < a ↔ d < a) → D c d T = 0) →
      ∀ c < a + b, ∀ d < a + b, D c d (gridP D K a b a T) = 0

def AdjBdd : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (N K : ℕ) (e : ℕ → ℕ → Module.End ℚ V), GlRel N e → Bdd N K e →
    WtSpan N e → GlRel N (fun a b => adj (e a b)) ∧ Bdd N (2 * K) (fun a b => adj (e a b))

def StepScalar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (E F H T : Module.End ℚ V) (v : V) (φ : V →ₗ[ℚ] ℚ) (n K j : ℕ),
    E * F - F * E = H → H * F - F * H = -(F + F) → E v = 0 → H v = (n : ℚ) • v → n ≤ K → (∀ x, φ (F x) = 0) →
    (∀ k : ℕ, 0 < k → T ((F ^ k) v) = 0) →
      φ (proj K j (adj E) (adj F) T v) * ((n : ℚ) + j + 1) = φ (T v)

def GridScalar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (a b K : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) (v : V)
    (φ : V →ₗ[ℚ] ℚ) (T : Module.End ℚ V), GlRel (a + b) e → Dom (a + b) e lam → IsWt (a + b) e lam v →
    (∀ i j : ℕ, i < j → j < a + b → e i j v = 0 ∧ (∀ x, φ (e j i x) = 0) ∧ lam j ≤ lam i ∧ lam i ≤ lam j + K) →
    (∀ (μ : ℕ → ℤ) (x : V), IsWt (a + b) e μ x → ∑ c ∈ Finset.range a, μ c < ∑ c ∈ Finset.range a, lam c → T x = 0) →
      φ (gridP (fun c d => adj (e c d)) K a b a T v) *
        ((∏ i ∈ Finset.range a, ∏ j ∈ Finset.Ico a (a + b), (lam i - lam j + (j : ℤ) - (i : ℤ)) : ℤ) : ℚ) = φ (T v)

def GridInt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (a b K w Λ : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (L M : Submodule ℤ V),
    DivStable (a + b) e L → DivStable (a + b) e M → K + (a + b) ≤ w + 1 →
    (∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial)) →
    ∀ (c : ℕ) (T : Module.End ℚ V), (∀ x ∈ L, (c : ℤ) • T x ∈ M) →
      ∀ x ∈ L, ((c * Λ ^ (a * b) : ℕ) : ℤ) • gridP (fun c d => adj (e c d)) K a b a T x ∈ M

def BetaDen : Prop :=
  ∀ l w : ℕ, l.Prime → ∃ m : ℕ, ¬ l ∣ m ∧
    ∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ (m * l ^ Nat.log l w) * (j.factorial * k.factorial)

def eV (N : ℕ) (ν : Fin N → ℕ) (a b : ℕ) : Module.End ℚ (dualWeyl ℚ N N ν) :=
  if h : a < N ∧ b < N then
    LinearMap.restrict (Formalism.CohomologicalDescent.LR.der N N ⟨a, h.1⟩ ⟨b, h.2⟩ : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ))
      (fun f hf => Formalism.CohomologicalDescent.LR.der_mem ν _ _ f hf)
  else 0

def latV (N : ℕ) (ν : Fin N → ℕ) (M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ)) : Submodule ℤ (dualWeyl ℚ N N ν) :=
  (M.map (intQ N N)).comap ((dualWeyl ℚ N N ν).subtype.restrictScalars ℤ)

def wtZ {N : ℕ} (ν : Fin N → ℕ) (c : ℕ) : ℤ := if h : c < N then (ν ⟨c, h⟩ : ℤ) else 0

def resVarT (R : Type) [CommRing R] (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) :
    MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
      (fun s => X (a, s) ⊗ₜ[R] 1) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
      (fun _ => 0) (fun t => 1 ⊗ₜ[R] X (b, t)) v.2) v.1

def resT (R : Type) [CommRing R] (p q : ℕ) : MvPolynomial (Fin (p + q) × Fin (p + q)) R →ₐ[R]
    MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R :=
  aeval (resVarT R p q)

def NablaGl : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    GlRel N (eV N ν) ∧ WtSpan N (eV N ν) ∧ Dom N (eV N ν) (wtZ ν) ∧
      DivStable N (eV N ν) (latV N ν (dualWeyl ℤ N N ν)) ∧ DivStable N (eV N ν) (latV N ν (weyl ℤ N N le_rfl ν))

def NablaBdd : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ K : ℕ, (∀ i j, ν i ≤ ν j + K) → Bdd N K (eV N ν)

def NablaSchur : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (S : Module.End ℚ (dualWeyl ℚ N N ν)),
    (∀ c < N, ∀ d < N, eV N ν c d * S = S * eV N ν c d) →
    fockQ (hw ℚ le_rfl ν) (S ⟨hw ℚ le_rfl ν, hwMem ℚ N N le_rfl ν hν⟩ : dualWeyl ℚ N N ν) =
      fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) → S = 1

def SubstMem : Prop :=
  ∀ (R : Type) [CommRing R] (k N : ℕ) (τ : Fin k → Fin N), StrictMono τ →
    ∀ ψ : Fin N × Fin N → MvPolynomial (Fin k × Fin k) R,
      (∀ a s, ψ (τ a, τ s) = X (a, s)) → (∀ x s, x ∉ Set.range τ → ψ (x, τ s) = 0) →
      (∀ x y, y ∉ Set.range τ → ∃ c : R, ψ (x, y) = C c) →
      ∀ (ν : Fin N → ℕ), ∀ f ∈ dualWeyl R N N ν, aeval ψ f ∈ dualWeyl R k k (fun s => ν (τ s))

def ResLat : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ), ∀ f ∈ dualWeyl ℤ (p + q) (p + q) ν,
    resT ℚ p q (intQ (p + q) (p + q) f) ∈ Submodule.span ℤ
      {z | ∃ f₁ ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), ∃ f₂ ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
        z = intQ p p f₁ ⊗ₜ[ℚ] intQ q q f₂}

def ResHw : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ), Antitone ν →
    resT ℚ p q (hw ℚ le_rfl ν) =
      hw ℚ le_rfl (fun i => ν (Fin.castAdd q i)) ⊗ₜ[ℚ] hw ℚ le_rfl (fun j => ν (Fin.natAdd p j))

def ResDer : Prop :=
  ∀ (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ),
    (∀ c d : Fin p, resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q d) f) =
      LinearMap.rTensor _ (Formalism.CohomologicalDescent.LR.der p p c d : Module.End ℚ (MvPolynomial (Fin p × Fin p) ℚ)) (resT ℚ p q f)) ∧
    (∀ c d : Fin q, resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.natAdd p c) (Fin.natAdd p d) f) =
      LinearMap.lTensor _ (Formalism.CohomologicalDescent.LR.der q q c d : Module.End ℚ (MvPolynomial (Fin q × Fin q) ℚ)) (resT ℚ p q f)) ∧
    ∀ (ν : Fin (p + q) → ℕ) (t : ℚ), IsWeightedHomogeneous (colW (p + q) (p + q)) f ν →
      ∑ c : Fin p, Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q c) f = t • f →
      t ≠ ∑ c : Fin p, (ν (Fin.castAdd q c) : ℚ) → resT ℚ p q f = 0

def LeviProj : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ : ℕ),
    (∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i))) →
    (∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)), (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j))) →
    ∃ T : Module.End ℚ (dualWeyl ℚ (p + q) (p + q) ν),
      (∀ c < p + q, ∀ d < p + q, (c < p ↔ d < p) → eV (p + q) ν c d * T = T * eV (p + q) ν c d) ∧
      (∀ x ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν),
        ((c₁ * c₂ : ℕ) : ℤ) • T x ∈ latV (p + q) ν (weyl ℤ (p + q) (p + q) le_rfl ν)) ∧
      (∀ (μ : ℕ → ℤ) (x : dualWeyl ℚ (p + q) (p + q) ν), IsWt (p + q) (eV (p + q) ν) μ x →
        ∑ c ∈ Finset.range p, μ c < ∑ c ∈ Finset.range p, wtZ ν c → T x = 0) ∧
      fockQ (hw ℚ le_rfl ν) (T ⟨hw ℚ le_rfl ν, hwMem ℚ (p + q) (p + q) le_rfl ν hν⟩ : dualWeyl ℚ (p + q) (p + q) ν) =
        fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)

end GlobalTheory.LeviCut
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.UnitAboveOpen

theorem exists_extend (T H : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T]
    (hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T) (U : T.Opens) (hU : (U : Set T).Nonempty)
    (p : H ⟶ T) (e : T ⟶ H) (hs : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _)
    (F : Γ(H, p ⁻¹ᵁ U)ˣ) (hF : ∀ y : U.toScheme, gm (U.ι ≫ e) y (p ⁻¹ᵁ U) F = 1) :
    ∃ G : Γ(H, ⊤)ˣ, F = res (le_top : p ⁻¹ᵁ U ≤ ⊤) G := by
  have : Nonempty U.toScheme := ⟨⟨hU.some, hU.some_mem⟩⟩
  have : IsIntegral H := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  have hP : IsPullback (p ⁻¹ᵁ U).ι (p ∣_ U) p U.ι := (isPullback_morphismRestrict p U).flip
  let eU : U.toScheme ⟶ (p ⁻¹ᵁ U).toScheme := hP.lift (U.ι ≫ e) (𝟙 _) (by simp [he])
  have heU : eU ≫ (p ⁻¹ᵁ U).ι = U.ι ≫ e := hP.lift_fst _ _ _
  have : Nonempty (p ⁻¹ᵁ U).toScheme := ⟨eU (Nonempty.some inferInstance)⟩
  let L : LB H := ⟨PUnit, fun _ ↦ ⊤, fun _ _ ↦ 1⟩
  have hL : L.IsLB := ⟨by simp [L], fun _ ↦ map_one _, fun _ _ _ ↦ by simp [L]⟩
  let φ : PEmpty → (H ⟶ H) := PEmpty.elim
  let ε : PEmpty → ℤ := PEmpty.elim
  have hw {Y : Scheme.{0}} (ψ : PEmpty → (Y ⟶ H)) (a) (y : Y) : y ∈ LB.wchart L ψ a :=
    Set.mem_iInter.2 fun k ↦ k.elim
  have hm (y : (p ⁻¹ᵁ U).toScheme) : (p ⁻¹ᵁ U).ι y ∈ p ⁻¹ᵁ U := y.2
  let t : LB.Gen (LB.LinComb L (fun i ↦ (p ⁻¹ᵁ U).ι ≫ φ i) ε) :=
    ⟨fun a ↦ res (fun y _ ↦ hm y) (pullU (p ⁻¹ᵁ U).ι _ F)⟩
  have htg {Z : Scheme.{0}} (r : Z ⟶ (p ⁻¹ᵁ U).toScheme) (z : Z) (a) :
      gm r z (LB.wchart L (fun i ↦ (p ⁻¹ᵁ U).ι ≫ φ i) a) (t.s a) =
        gm (r ≫ (p ⁻¹ᵁ U).ι) z (p ⁻¹ᵁ U) F :=
    (gm_res r z _ (hw _ _ _) _).trans (gm_pull r _ z _ (hm _) F)
  let ρ : LB.Gen (LB.LinComb L (fun i ↦ e ≫ φ i) ε) := ⟨fun a ↦ 1⟩
  have ht : t.IsGen := fun a b ↦ by
    obtain rfl : a = b := funext fun k ↦ PEmpty.elim k
    simp [LB.LinComb]
  have hρ : ρ.IsGen := fun a b ↦ by
    obtain rfl : a = b := funext fun k ↦ PEmpty.elim k
    simp [LB.LinComb]
  have hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ U.ι) := by
    intro a b _ _ _
    refine unit_ext fun y hy ↦ ?_
    rw [gm_res _ y _ hy, gm_res _ y _ hy]
    refine Eq.trans (b := 1) ((gm_res _ y _ (hw _ _ _) _).trans
      ((gm_pull _ _ y _ (hw _ _ _) _).trans ((htg _ _ _).trans ?_))) ?_
    · rw [Category.id_comp, heU, hF]
    · refine Eq.symm ((gm_res _ y _ (hw _ _ _) _).trans ((gm_pull _ _ y _ (hw _ _ _) _).trans ?_))
      exact map_one _
  obtain ⟨c, ⟨-, hc'⟩, -⟩ := GlobalTheory.GenExtendNormal.existsUnique_gen_extend T hT U.toScheme H
    (p ⁻¹ᵁ U).toScheme H U.ι p e (p ⁻¹ᵁ U).ι (p ∣_ U) eU hs hg he hP heU L hL PEmpty φ ε t ρ
    ht hρ hc
  let a : PEmpty → L.ι := PEmpty.elim
  refine ⟨res (fun y _ ↦ hw φ a y : (⊤ : H.Opens) ≤ LB.wchart L φ a) (c.s a),
    GlobalTheory.GenExtendNormal.unit_ext_of_isOpenImmersion (p ⁻¹ᵁ U).ι fun y hy ↦ ?_⟩
  rw [gm_res _ y _ hy, gm_res (p ⁻¹ᵁ U).ι y (V := ⊤) _ trivial]
  have h₁ := htg (𝟙 _) y a
  rw [← hc', Category.id_comp] at h₁
  rw [← h₁]
  exact (gm_res _ y _ (hw _ _ _) _).trans ((gm_pull _ _ y _ (hw _ _ _) _).trans
    (by rw [Category.id_comp]))

theorem exists_eq_res_mul_pullU :
    ∀ (T H : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : H ⟶ T) (e : T ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ F : Γ(H, p ⁻¹ᵁ U)ˣ, ∃ (G : Γ(H, ⊤)ˣ) (w : Γ(T, U)ˣ), F = res (le_top : p ⁻¹ᵁ U ≤ ⊤) G * pullU p U w := by
  intro T H _ _ hT U hU p e hs hg he F
  have hle : U ≤ e ⁻¹ᵁ p ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, he]; rfl
  let w : Γ(T, U)ˣ := res hle (pullU e _ F)
  obtain ⟨G, hG⟩ := exists_extend T H hT U hU p e hs hg he (F * (pullU p U w)⁻¹) fun y ↦ by
    have hy : U.ι y ∈ U := y.2
    have hy' : p ((U.ι ≫ e) y) ∈ U := hle hy
    rw [map_mul, map_inv, gm_pull _ p y U hy', Category.assoc, he, Category.comp_id,
      gm_res _ y hle hy, gm_pull _ e y _ (hle hy), mul_inv_cancel]
  exact ⟨G, w, by rw [← hG, inv_mul_cancel_right]⟩

end GlobalTheory.UnitAboveOpen
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem map_comap_inf_sup_pow_eq : ∀ (W W' : Scheme.{0}) [IsAffine W] [IsLocallyNoetherian W] (π : W' ⟶ W)
    (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (K τ : W.IdealSheafData),
    (∀ x, x ∉ K.support → x ∈ U) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (τ.comap π).map π ⊓ (τ ⊔ K ^ k) = τ := by
  intro W W' _ _ π U hqc hiso K τ hK
  let T : W.affineOpens := ⟨⊤, isAffineOpen_top W⟩
  haveI : IsNoetherianRing Γ(W, T.1) := IsLocallyNoetherian.component_noetherian T
  have hle : τ ≤ (τ.comap π).map π := Scheme.IdealSheafData.le_map_comap τ π
  have htor : ∀ b ∈ ((τ.comap π).map π).ideal T, ∀ f ∈ K.ideal T, ∃ m : ℕ, f ^ m * b ∈ τ.ideal T := by
    intro b hb f hf
    have hV : (W.affineBasicOpen f).1 ≤ U := by
      intro x hx
      by_contra hxU
      have hxK : x ∈ K.support := by_contra fun h => hxU (hK x h)
      rw [Scheme.IdealSheafData.mem_support_iff] at hxK
      exact (Scheme.mem_zeroLocus_iff W _ x).1 (hxK T) f hf hx
    have heq := GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict W W' π U hqc hiso τ (W.affineBasicOpen f) hV
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, ← Scheme.IdealSheafData.map_ideal_basicOpen] at heq
    have hloc := T.2.isLocalization_basicOpen f
    have hb' := Ideal.mem_map_of_mem (W.presheaf.map (homOfLE (W.basicOpen_le f)).op).hom hb
    rw [heq] at hb'
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) Γ(W, W.basicOpen f)
        (τ.ideal T) b).1 hb'
    exact ⟨m, hm⟩
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.inf_sup_pow_eq_of_torsion_artinRees Γ(W, T.1) (K.ideal T) (τ.ideal T) (((τ.comap π).map π).ideal T)
    (hle T) htor
  refine ⟨k₀, fun k hk => Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  exact hk₀ k hk

end GlobalTheory.FormalAlg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.exists_immersed_closed_open_intersection : ∀ (Y : Scheme.{0}) [IsNoetherian Y] (Z₁ Z₂ : Scheme.{0}) (ι₁ : Z₁ ⟶ Y) (ι₂ : Z₂ ⟶ Y) (U : Y.Opens), IsClosedImmersion ι₁ → IsClosedImmersion ι₂ → ∃ (W : Scheme.{0}) (j : W ⟶ Y), IsImmersion j ∧ QuasiCompact j ∧ IsLocallyNoetherian W ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Y), ((∃ w : T ⟶ Z₁, w ≫ ι₁ = g) ∧ (∃ w : T ⟶ Z₂, w ≫ ι₂ = g) ∧ ∀ τ, g τ ∈ U) ↔ ∃ w : T ⟶ W, w ≫ j = g := by
  first | (exact @GlobalTheory.HomFixMat.exists_immersed_locus) | (exact GlobalTheory.HomFixMat.exists_immersed_locus) | (intros; apply GlobalTheory.HomFixMat.exists_immersed_locus  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isOpen_and_isIrreducible_sectionComponent_of_smooth_field
    (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    (e : Spec (CommRingCat.of k) ⟶ X) (hf : Smooth f) (he : e ≫ f = 𝟙 _) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧
      IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  have hsub : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  have hZ : {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}
      = connectedComponent (e p) := by
    ext x
    have h1 : (f ⁻¹' {f x} : Set X) = Set.univ :=
      Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    have h2 : f x = p := Subsingleton.elim _ _
    rw [Set.mem_setOf_eq, h1, h2, connectedComponentIn_univ]
  rw [hZ]
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hO : IsOpen (connectedComponent (e p)) := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' X hN (e p)
  refine ⟨hO, ?_⟩
  let U : X.Opens := ⟨connectedComponent (e p), hO⟩
  have hc : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := e p))
  have hi : IrreducibleSpace U.toScheme :=
    GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected k U.toScheme (U.ι ≫ f) inferInstance hc
  exact isIrreducible_iff_irreducibleSpace.mpr hi

end GlobalTheory
end

section

open scoped Matrix
open Formalism.BasicNotions.TH

namespace GlobalTheory

theorem cayley_two_injective :
    Function.Injective (fun x : ℝ => (1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)) := by
  have hne : ∀ x : ℝ, (1 - 2 * Complex.I * x) ≠ 0 := by
    intro x h
    have := congrArg Complex.re h
    simp at this
  intro x y hxy
  simp only at hxy
  rw [div_eq_div_iff (hne x) (hne y)] at hxy
  have h2 : ((x : ℂ) - y) * (4 * Complex.I) = 0 := by linear_combination hxy
  rcases mul_eq_zero.1 h2 with h | h
  · exact_mod_cast sub_eq_zero.1 h
  · exfalso; have := Complex.I_ne_zero; apply this; linear_combination h / 4

theorem zpow_cayley_two_eq_one_forall :
    ∀ m : ℤ, (∀ x : ℝ, ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)) ^ m = 1) → m = 0 := by
  intro m hm
  by_contra hm0
  set f : ℝ → ℂ := fun x => (1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x) with hf
  have hn : 0 < m.natAbs := Int.natAbs_pos.2 hm0
  have hpow : ∀ x : ℝ, f x ^ m.natAbs = 1 := by
    intro x
    have h := hm x
    rcases Int.natAbs_eq m with e | e
    · rw [e, zpow_natCast] at h; exact h
    · rw [e, zpow_neg, zpow_natCast, inv_eq_one] at h; exact h
  let S : Finset ℂ := (Polynomial.nthRoots m.natAbs (1 : ℂ)).toFinset
  have hS : ∀ x : ℝ, f x ∈ S := by
    intro x
    simp only [S, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots hn).2 (hpow x)
  have : Finite ℝ :=
    Finite.of_injective (fun x : ℝ => (⟨f x, hS x⟩ : S)) (by
      intro x y hxy
      exact cayley_two_injective (congrArg Subtype.val hxy))
  exact not_finite ℝ

end GlobalTheory
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.abhyankar_etale_integralClosure_root_uniformizer : ∀ (S S₁ K K₁ L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L)) := by
  first | (exact @GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer) | (exact GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer) | (intros; apply GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer  <;> assumption)
end
