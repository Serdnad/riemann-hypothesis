module

public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.HermitianLattices.StatementLat
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module NumberField

noncomputable section

namespace Formalism.LFunctionChainParameters.LLcv

open Formalism.HN

section Defs

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

def lcvInf (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) {j : ℕ} (e : Fin j → V) : ℝ :=
  (1 / (nPl K : ℝ)) * ∑ v, Real.log (gramPl b X v e).det.re

def lcvFin {j : ℕ} (e : Fin j → V) (M : Submodule (𝓞 K) V) : ℝ :=
  2 * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
    (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) *
      (haveI := p.2.isPrime; (Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ))

def lcv (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) {j : ℕ} (e : Fin j → V)
    (M : Submodule (𝓞 K) V) : ℝ :=
  lcvInf b X e + lcvFin e M

end Defs

def LcvMu : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V) (M : Submodule (𝓞 K) V), LinearIndependent K e → M.FG → M ≠ ⊥ →
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e) →
      rkK M = j ∧ 0 < j ∧
      (∀ v, 0 < (gramPl b X v e).det.re ∧ (gramPl b X v e).det.im = 0) ∧
      (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M)).Finite ∧
      muDef b X M = -lcv b X e M / (rkK M : ℝ)

def LcvExists : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V),
    ∃ (j : ℕ) (e : Fin j → V), LinearIndependent K e ∧ (∀ a, e a ∈ M) ∧
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e)

def LcvFree : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V), LinearIndependent K e → 0 < j →
      lcvFin e (Submodule.span (𝓞 K) (Set.range e)) = 0 ∧
      muDef b X (Submodule.span (𝓞 K) (Set.range e)) = -lcvInf b X e / (j : ℝ)

def LcvIdeal : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (_b : Basis ι K V) (j : ℕ) (e : Fin j → V)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), LinearIndependent K e → 0 < j → I ≠ 0 →
      lcvFin e (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K)
        (Submodule.span (𝓞 K) (Set.range e))) =
        2 * (j : ℝ) * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)

def IndexLocLen : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V), B ≤ A → B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 →
      (∀ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (haveI := p.2.isPrime;
        Module.length (𝓞 K) ((Formalism.HermitianLatticesTheory.localization₂ p.1 A) ⧸
          (Formalism.HermitianLatticesTheory.localization₂ p.1 B).comap (Formalism.HermitianLatticesTheory.localization₂ p.1 A).subtype)) ≠ ⊤) ∧
      (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; Formalism.HermitianLatticesTheory.locLen p.1 A B)).Finite ∧
      Real.log (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
        ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, Real.log (Ideal.absNorm p.1 : ℝ) *
          (haveI := p.2.isPrime; (Formalism.HermitianLatticesTheory.locLen p.1 A B : ℝ))

end Formalism.LFunctionChainParameters.LLcv
end
end

section

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def psC : AddChar (E0 × H) ℂ where
  toFun g := if g.1.2 = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rcases a with ⟨⟨a1, a2⟩, ah⟩
    rcases b with ⟨⟨b1, b2⟩, bh⟩
    have key : ∀ x y : ZMod 2, (if x + y = 0 then (1 : ℂ) else -1)
        = (if x = 0 then 1 else -1) * (if y = 0 then 1 else -1) := by
      intro x y
      have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      rcases h2 x with rfl | rfl <;> rcases h2 y with rfl | rfl <;> simp [h11, h10]
    exact key a2 b2

def chpsC : AddChar (E0 × H) ℂ := chC * psC

def Gsig (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (y : ℝ) : ℂ :=
  GPsi D ell 0 y + GPsi D ell psC y - GPsi D ell chC y - GPsi D ell chpsC y

def fPl (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] : ℝ := ((PhiSet (H := H)).card : ℝ)

def delta2 (T2 : Finset H) : ℝ := (T2.card : ℝ) / (Fintype.card H : ℝ)

def ThickPartTranslateMean : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H) (t : H) (A b : ℝ), 0 < A → 0 < b →
    (1 / (Fintype.card H : ℂ)) * ∑ u0 : H, (1 / ((PhiSet (H := H)).card : ℂ)) *
        ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g ∧ IsThickAt T2 u0 (partner t g)),
          ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * (b : ℂ) * GPsi D ell ψ (A / b)
      = ((delta2 T2 * b / 2 : ℝ) : ℂ) * Gsig D ell (A / b)

def topExcess (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
    (ASK D N (a t) t (w u0 j) - (MAIN ell (a t) (w u0 j)).re)

def ThinScales (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (X' θ : ℝ) : Prop :=
  ∀ ψ : AddChar (E0 × H) ℂ, ∀ y : ℝ, X' / 3 ≤ y → ‖GPsi D ell ψ y‖ ≤ y * θ

def LipW (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) : Prop :=
  ∀ (ψ : AddChar (E0 × H) ℂ) (A w w' : ℝ), 0 < A → 0 < w → 0 < w' →
    ‖(w : ℂ) * GPsi D ell ψ (A / w) - (w' : ℂ) * GPsi D ell ψ (A / w')‖ ≤ 3 * A / min w w' * |w - w'|

def DerivInt (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (Cd : ℝ) : Prop :=
  (∀ ψ : AddChar (E0 × H) ℂ, ψ ≠ 0 → ∀ y z : ℝ, 1 ≤ y → 1 ≤ z →
      ‖GPsi D ell ψ y - GPsi D ell ψ z‖ ≤ |y - z| * (Real.log (max y z) + Cd + ‖ell ψ‖)) ∧
  (∀ y z : ℝ, 1 ≤ y → 1 ≤ z → |Gz y - Gz z| ≤ Cd * |y - z|)

def ValuesAtX (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (x ε CL : ℝ) : Prop :=
  ∀ ψ : AddChar (E0 × H) ℂ, (ψ = psC ∨ ψ = chC ∨ ψ = chpsC) →
    ‖GPsi D ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ ‖ell ψ‖ ≤ CL * Real.log x

def NodeSizes {m : ℕ} (T2 : Finset H) (b b' η : ℝ) (w : H → Fin m → E0 × H → ℝ) : Prop :=
  (∀ u0 j ρ, InPhi ρ → 0 < w u0 j ρ) ∧
  (∀ u0 j ρ, IsThickAt T2 u0 ρ → b ≤ w u0 j ρ ∧ w u0 j ρ ≤ b + η + 1) ∧
  (∀ u0 j ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → w u0 j ρ ≤ 2 * b')

def moveCost (x Cd CL : ℝ) : ℝ := Cd + 3 * (Real.log (x + 1) + Cd + CL * Real.log x)

def GrowthInequalityHypotheses (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) {m : ℕ} (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (x ε b b' η X' θ Cd CL Err : ℝ) : Prop :=
  3 ≤ x ∧ 0 < b ∧ 0 ≤ η ∧ 0 < X' ∧ 0 < b' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ ∧ 0 ≤ Cd ∧
  (∀ t ∈ TT, |a t / b - x| ≤ 1) ∧
  NodeSizes T2 b b' η w ∧
  (∀ u0 j t ρ, t ∈ TT → InPhi ρ → a t / w u0 j ρ ≤ N) ∧
  topExcess D N ell TT a w ≤ Err ∧
  ThinScales D ell X' θ ∧ LipW D ell ∧ DerivInt D ell Cd ∧ ValuesAtX D ell x ε CL

def GrowthInequalityExplicit : Prop :=
  AskMainBalance (H := H) → ∀ (D : ArithData H), HostFacts D →
  ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (x ε b b' η X' θ Cd CL Err : ℝ),
    GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err →
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL)
      ≤ Err + (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ)
        + (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1))

def SmallCosts (x ε f b η θ Cd CL : ℝ) : Prop :=
  moveCost x Cd CL ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ 2 * f * (x + 1) * θ ≤ 1 / x ∧ 6 * f * (x + 1) * (η + 1) ≤ b / x

def GrowthInequalityForm : Prop :=
  AskMainBalance (H := H) → ∀ (D : ArithData H), HostFacts D →
  ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (x ε b b' η X' θ Cd CL Err : ℝ),
    GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err → SmallCosts x ε (fPl H) b η θ Cd CL →
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ Err + 2 * (TT.card : ℝ) * m * b / x

end

def SizeWindows (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ) : Prop :=
  3 ≤ x ∧ 0 < ε ∧ 0 ≤ C ∧ 0 < n ∧ 0 < b ∧ 0 ≤ aE ∧ aE ≤ 2 * x * b ∧
  x ^ (-(ε / 8)) * n / 2 ≤ nT ∧
  x ^ (-ε) ≤ (nT2 : ℝ) / n ∧ nT2 ≤ n ∧
  x ^ ((1 : ℝ) / 2 - ε) ≤ m ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) ∧
  x * m ≤ k ∧ k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) ∧
  Err ≤ x ^ (C * ε) * ((nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
    + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))) ∧
  26 ≤ x ^ (3 * ε / 8)

def GrowthSizeBound : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err →
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x →
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε)

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

end

def LipWAll : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ),
    LipW D ell

def DerivIntAll : Prop :=
  ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H)
    (ell : AddChar (E0 × H) ℂ → ℂ), DerivInt D ell Cd

end Formalism.LFunctionChainParameters.ThickSetMeanBounds
end
end

section

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LHost

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData

def localUnits (N p : ℕ) : Subgroup (ZMod N)ˣ := (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker

def IsFrobUnit (N p : ℕ) (w : (ZMod N)ˣ) : Prop :=
  ((w : ZMod N).cast : ZMod (ordCompl[p] N)) = (p : ZMod (ordCompl[p] N)) ∧
    ((w : ZMod N).cast : ZMod (ordProj[p] N)) = 1

def frobUnit (N p : ℕ) : (ZMod N)ˣ := by
  classical
  exact if h : ∃ w, IsFrobUnit N p w then h.choose else 1

section
variable {N : ℕ} {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def cftData (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) : ArithData H where
  q1 := q1
  d := d
  inertia p := Subgroup.toAddSubgroup' ((localUnits N p).map r)
  frob p := Multiplicative.toAdd (r (frobUnit N p))

def dirChar (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) : DirichletCharacter ℂ N :=
  MulChar.ofUnitHom (ψ.toMonoidHom.comp r).toHomUnits

end

def sgn2 : ℤˣ →* Multiplicative (ZMod 2) where
  toFun s := Multiplicative.ofAdd (if s = 1 then 0 else 1)
  map_one' := by simp
  map_mul' := by decide

def FrobUnitSpec : Prop :=
  ∀ N p : ℕ, N ≠ 0 → p.Prime → IsFrobUnit N p (frobUnit N p) ∧ ∀ w, IsFrobUnit N p w → w = frobUnit N p

def UnramSpec : Prop :=
  ∀ N p : ℕ, N ≠ 0 → p.Prime → ¬ p ∣ N → localUnits N p = ⊥ ∧ ((frobUnit N p : (ZMod N)ˣ) : ZMod N) = (p : ZMod N)

section
variable (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H]

def DirCharSpec : Prop :=
  ∀ (N : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ),
    (∀ u : (ZMod N)ˣ, dirChar r ψ (u : ZMod N) = ψ (Multiplicative.toAdd (r u))) ∧
    ∀ x : ZMod N, ¬ IsUnit x → dirChar r ψ x = 0

def InertiaConductor : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (p : ℕ), N ≠ 0 → p.Prime →
    ((∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) ↔ ¬ p ∣ (dirChar r ψ).conductor)

def PrimValRamified : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (p i : ℕ), p.Prime → 1 ≤ i →
    ((∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) →
      primVal (cftData q1 d r) ψ (p ^ i) = ψ ((cftData q1 d r).frob p) ^ i) ∧
    ((¬ ∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) → primVal (cftData q1 d r) ψ (p ^ i) = 0)

def PrimValPrimitive : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (n : ℕ), N ≠ 0 → n ≠ 0 →
    primVal (cftData q1 d r) ψ n = (dirChar r ψ).primitiveCharacter (n : ZMod (dirChar r ψ).conductor)

end


end Formalism.LFunctionChainParameters.LHost
end
end
