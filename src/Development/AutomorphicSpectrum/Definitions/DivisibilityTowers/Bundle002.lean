module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Top

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def InWall (j : ℕ) (τ₀ : Ψ) (c₀ : ℝ) (lam : Wt Ψ N) : Prop :=
  ‖lam‖ ≤ 1 / 2 ∧ gap j lam τ₀ = 0 ∧ (∀ τ, τ ≠ τ₀ → c₀ ≤ gap j lam τ) ∧ CompactGapsGE j c₀ lam

def FrobShape (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) : Prop := ∀ p n τ τ', (frob p τ n).isLeft = (frob p τ' n).isLeft

def LabelInv (hh : RP Ψ N → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), hh (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = hh F

def restTerm (j p : ℕ) (fr : ℕ → Ψ ⊕ Ψ) (k : ℕ) (Q : RP Ψ N) : ℝ :=
  if 2 ≤ k then Real.log p * k * ∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * degFl (pLie j (k - 1) (fr n) * Q) else 0

def restSum (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N) : ℝ :=
  ∑' p : ℕ, if p.Prime ∧ B₀ < p ∧ p ∉ bad then restTerm j p (frob p τ) k Q else 0

def IsDecomp (F : RP Ψ N) (Q : Ψ → ℕ → RP Ψ N) : Prop :=
  (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (dimFl Ψ N + 1 - k)) ∧
    F = ∑ τ, ∑ k ∈ Finset.Icc 1 N, pk τ k * Q τ k

def muSmall (j : ℕ) : RP Ψ N :=
  if N - j ≤ j then ∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), X (τ, i) else -∑ τ, pkLow j τ 1

def fibClass (j : ℕ) : RP Ψ N :=
  ∏ τ, ∏ ab ∈ Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)),
    (X (τ, ab.2) - X (τ, ab.1))

def dimX (Ψ : Type) [Fintype Ψ] (N j : ℕ) : ℕ := Fintype.card Ψ * (j * (N - j))

def testPoly (j : ℕ) : RP Ψ N := muSmall j ^ (dimX Ψ N j + 1) * fibClass j

def testDeg (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) : ℝ :=
  degFl (muSmall j ^ dimX Ψ N j * fibClass j : RP Ψ N)

namespace RootTower

variable (T : RootTower Ψ N) (II : IntersectionSystem)

def ThmW : Prop :=
  ∀ c₀ > (0 : ℝ), ∃ C : ℝ, ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ τ₀ (lam : Wt Ψ N), InWall T.j τ₀ c₀ lam →
    |T.PB II B lam| ≤ C * Real.log B / B

def ThmB (hh : RP Ψ N → ℝ) : Prop :=
  ∃ C : ℝ, ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∃ α β : Ψ → ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 →
    |T.PPt II B (monomial m 1) - T.volT * (hh (monomial m 1) - ∑ τ, (α τ - β τ) * Sh T.j τ (monomial m 1) -
      ∑ τ, β τ * Tot τ (monomial m 1))| ≤ C * Real.log B / B

def ThmBA (hh : RP Ψ N → ℝ) : Prop :=
  ∃ C : ℝ, ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∃ α β : ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 →
    |T.PPt II B (monomial m 1) - T.volT * (hh (monomial m 1) - (α - β) * ∑ τ, Sh T.j τ (monomial m 1) -
      β * ∑ τ, Tot τ (monomial m 1))| ≤ C * Real.log B / B

def IdentAt (hh : RP Ψ N → ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (A₀ b₀ : ℝ) : Prop :=
  ∀ τ (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) →
    T.PPt II B₀ (pk τ k * Q) = T.volT * (hh (pk τ k * Q) - A₀ * ∑ σ, Sh T.j σ (pk τ k * Q) -
      b₀ * ∑ σ, Tot σ (pk τ k * Q) + restSum T.j T.bad frob B₀ τ k Q)

def SlopeLower (C rd Lval : ℝ) : Prop :=
  ∀ B : ℕ, 128 ≤ B → 4 * Fintype.card Ψ * N ^ 2 ≤ B → T.bad.card ≤ B →
    -(C * Fintype.card Ψ * (min T.j (N - T.j) : ℕ) * bigLam B rd Lval) *
        (((dimX Ψ N T.j : ℝ) + 1) * (T.volT * testDeg Ψ N T.j)) ≤ T.PPt II B (testPoly T.j)

def LowerBoundAtBase (hh : RP Ψ N → ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C rd Lval : ℝ) : Prop :=
  ∀ (B₀ : ℕ) (A₀ b₀ : ℝ), 128 ≤ B₀ → 4 * Fintype.card Ψ * N ^ 2 ≤ B₀ → T.bad.card ≤ B₀ →
    T.IdentAt II hh frob B₀ A₀ b₀ → -(C * bigLam B₀ rd Lval) ≤ A₀

def T1 : Prop :=
  ∀ (u : Wt Ψ N) (g : ℝ), WeightHyp T.j u g → ∀ B : ℕ, bigB0 u g < B + 1 → ∀ c,
    (∀ᶠ s in 𝓝[>] (0 : ℝ), (T.M B c).NefFib (T.lamS u s) s ∧ (T.M B c).Semipos (scale s) (T.lamS u s) s) ∧
    Tendsto (fun s => T.mbarTop II B c u s) (𝓝[>] 0) (𝓝 (T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)))) ∧
    Tendsto (fun s => T.mDeg B c u s) (𝓝[>] 0) (𝓝 (T.vol c * flagDeg u)) ∧ 0 < T.vol c * flagDeg u ∧
    Tendsto (fun s => T.mbarTop II B c u s / (((dimFl Ψ N : ℝ) + 1) * T.mDeg B c u s)) (𝓝[>] 0)
      (𝓝 (T.slope II B c u))

def bracket (rd Lval : ℝ) (B : ℕ) (u : Wt Ψ N) : ℝ :=
  bigLam B rd Lval * l1 u + (min T.j (N - T.j) : ℕ) * spread u

def T2 (C rd Lval : ℝ) : Prop :=
  ∀ (u : Wt Ψ N) (g : ℝ), WeightHyp T.j u g → ∀ B : ℕ, 128 ≤ B → bigB0 u g < B + 1 → T.bad.card ≤ B →
    -(C * ((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u) * T.bracket rd Lval B u) ≤ T.PB II B u

def MeanSlope (C rd Lval : ℝ) : Prop :=
  ∀ (u : Wt Ψ N) (g : ℝ), WeightHyp T.j u g → ∀ B : ℕ, 128 ≤ B → bigB0 u g < B + 1 → T.bad.card ≤ B →
    -(C * T.bracket rd Lval B u) ≤ (∑ c, T.slope II B c u) / (Fintype.card T.Comp : ℝ)

end RootTower

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsConjInvariantH IntersectionSystem)
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal divCycle cycEval intNumL)

noncomputable section

open scoped Classical in
open Classical in
def vertAt {K : Type} [DecidableEq K] {ι : K → Type} (p : Nat.Primes) (P : Ideal (MvPolynomial (Σ k, ι k) ℤ))
    (f : MvPolynomial (Σ k, ι k) ℤ) (l : List (K → ℤ)) : ℤ :=
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  cycEval (fun W => if (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W then
    intNumL (ZMod p) (extTo (ZMod p) W) l else 0) (divCycle P f)

def AtPlacesOver (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω] (p : ℕ)
    (Pr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω], Prop) : Prop :=
  ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O]
      [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], Pr O

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

structure SecondRoots (M : RootModel Ψ N) where

  xdeg : Ψ × Fin N → M.K → ℤ

  x : ℝ → Ψ × Fin N → HermLine M.ι
  x_deg : ∀ t r, (x t r).a = xdeg r
  x_smooth : ∀ t r, IsSmoothHerm (x t r)
  x_conj : ∀ t r, IsConjInvariantH (x t r)

  f : Ψ × Fin N → MvPolynomial (Σ k, M.ι k) ℤ

  g : Ψ × Fin N → MvPolynomial (Σ k, M.ι k) ℤ

variable {M : RootModel Ψ N}

def SecondRoots.model (R : SecondRoots M) : RootModel Ψ N :=
  { M with xdeg := R.xdeg, x := R.x, x_deg := R.x_deg, x_smooth := R.x_smooth, x_conj := R.x_conj }

def SecondRoots.pairs (R : SecondRoots M) : LocPair M.ι ℤ (Ψ × Fin N) := ⟨M.xdeg, R.xdeg, R.f, R.g⟩

open scoped Classical in
open Classical in
def SecondRoots.IsChange (R : SecondRoots M) (S : Finset Nat.Primes) : Prop :=
  R.pairs.IsVertOff M.P S ∧ ∀ t, 0 < t → R.pairs.IsIsometric M.P (M.x t) (R.x t)

open scoped Classical in
open Classical in
def SecondRoots.LocalAt [DecidableEq Ψ] (R : SecondRoots M) (j p : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (O : Type) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (P : Ideal (MvPolynomial (Σ k, M.ι k) O)) : Prop :=
  FlagChernComparison P (dimFl Ψ N) p j φ (R.pairs.map (Int.castRingHom O)) ∧
    ∀ τ, PowerSumsVanish P (dimFl Ψ N) fun i : Fin N => R.xdeg (τ, i)

def SecondRoots.LocalAtPlaces [DecidableEq Ψ] (R : SecondRoots M) (j : ℕ) (S : Finset Nat.Primes)
    (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)) : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : IsDedekindDomain A) (_ : Module.Finite ℤ A) (_ : Algebra A M.Ω),
    Function.Injective (algebraMap A M.Ω) ∧ HasConstants ℤ A M.y ∧
    ∀ p ∈ S, AtPlacesOver A M.Ω p fun O _ _ _ _ => R.LocalAt j p (φ p) O (pointIdeal O M.y)


open Classical in
def LinkedTower [DecidableEq Ψ] (T : RootTower Ψ N) (II : IntersectionSystem) (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)) : Prop :=
  ∀ B₀ B : ℕ, 2 ≤ B₀ → B₀ ≤ B → ∀ c, ∃ (M : RootModel Ψ N) (R : SecondRoots M) (S : Finset Nat.Primes),
    (∀ p : Nat.Primes, p ∈ S ↔ B₀ < (p : ℕ) ∧ (p : ℕ) ≤ B ∧ (p : ℕ) ∉ T.bad) ∧
    M.Converges II ∧ R.model.Converges II ∧
    (∀ F : RP Ψ N, M.PP II (toA F) = T.PPc II B₀ c F) ∧ (∀ F : RP Ψ N, R.model.PP II (toA F) = T.PPc II B c F) ∧
    (∀ F : RP Ψ N, M.geoFun (toA F) = (T.M B₀ c).geoFun (toA F)) ∧
    R.IsChange S ∧ R.LocalAtPlaces T.j S φ

end

end GlobalTheory.CompanionTheory.Ar.Num
end
