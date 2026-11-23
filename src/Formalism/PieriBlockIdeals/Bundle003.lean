module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.RankGapBounds.Bundle001
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Formalism.PieriBlockIdeals.LemmaWFromLattice
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

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LA

open Formalism.GradedWeylDivisibility

def lamU (r n : ℕ) (ν : Fin n → ℕ) : Fin r → ℤ :=
  fun a => (rowNu (r := r) ν a : ℤ) + ((r : ℤ) - 1 - (a.val : ℤ))

def InclZ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l e : ℕ) : Prop :=
  ∃ m : ℕ, ¬ l ∣ m ∧ ∀ x ∈ dualWeyl ℤ r n ν, ((m * l ^ e : ℕ) : ℤ) • x ∈ weyl ℤ r n hn ν

def LemmaAZ : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l)

def exZ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l : ℕ) : ℕ := sInf {e : ℕ | InclZ r n hn ν l e}

def ExZSpec : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (exZ r n hn ν l)

def ExactExponentRankTwo : Prop :=
  ∀ (n : ℕ) (ν : Fin n → ℕ) (l : ℕ),
    Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 n ν) l =
      Formalism.RankGapBounds.JumpSetsAlt.maxVal l (rowNu (r := 2) ν 0 - rowNu (r := 2) ν 1)

def binForm (R : Type) [CommRing R] (d : ℕ) :
    (Fin (d + 1) → R) →ₗ[R] MvPolynomial (Fin 2 × Fin 1) R :=
  ∑ i : Fin (d + 1), (LinearMap.proj i : (Fin (d + 1) → R) →ₗ[R] R).smulRight
    ((X ((0 : Fin 2), (0 : Fin 1)) : MvPolynomial (Fin 2 × Fin 1) R) ^ (d - i.val) *
      X ((1 : Fin 2), (0 : Fin 1)) ^ i.val)

def LatticeInclusionTrivialWeight : Prop :=
  ∀ (r : ℕ) (hn : 0 ≤ r) (ν : Fin 0 → ℕ) (l : ℕ), l.Prime →
    InclZ r 0 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r 0 ν) l)

def LatticeInclusionRankOne : Prop :=
  ∀ (n : ℕ) (hn : n ≤ 1) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ 1 n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 1 n ν) l)

def LemmaAZ_r2n1 : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l : ℕ), l.Prime →
    InclZ 2 1 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 1 ν) l)

def LemmaAZ_r2n2 : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ 2 2 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 2 ν) l)

def LatticeInclusionRankLeTwo : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r), r ≤ 2 → ∀ ν : Fin n → ℕ, Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l)

def SharpInclusionRankTwoOneColumn : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l e : ℕ), l.Prime →
    (InclZ 2 1 hn ν l e ↔ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) ≤ e)

def SharpInclusionRankTwoTwoColumns : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l e : ℕ, l.Prime →
    (InclZ 2 2 hn ν l e ↔ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) ≤ e)

end Formalism.CohomologicalDescent.LA
end
end

section

open MvPolynomial

namespace Formalism.CohomologicalDescent.LD

open Formalism.GradedWeylDivisibility

def boxesOfContent {q : ℕ} (lam2 tau : Fin q → ℕ) (c : ℤ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).card

def colLen {q : ℕ} (lam2 tau : Fin q → ℕ) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => lam2 a ≤ j ∧ j < tau a).card

def shapes (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : Finset (Fin q → ℕ) :=
  (Fintype.piFinset fun a : Fin q => Finset.Icc (lam2 a) (lam2 a + i)).filter fun tau =>
    (∀ a b : Fin q, a ≤ b → tau b ≤ tau a) ∧ ∑ a, tau a = ∑ a, lam2 a + i ∧
      (∀ b : Fin q, ∀ j < tau b, colLen lam2 tau j ≤ p) ∧ boxesOfContent lam2 tau (w : ℤ) = 0

def mu (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) (c : ℤ) : ℕ :=
  (shapes p w i lam2).sup fun tau => boxesOfContent lam2 tau c

def Dn (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : ℤ :=
  ∏ k ∈ Finset.range (q + w + i), ((w : ℤ) - ((k : ℤ) - (q : ℤ))) ^ mu p w i lam2 ((k : ℤ) - (q : ℤ))

noncomputable def nablaWt (r : ℕ) (ν μ : Fin r → ℕ) : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ) :=
  dualWeyl ℤ r r ν ⊓ weightedHomogeneousSubmodule ℤ (rowW r r) μ

def KilledAt (l r : ℕ) (ν μ : Fin r → ℕ) (c : ℤ) : Prop :=
  ∀ x ∈ nablaWt r ν μ, ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ (m * c) • x ∈ weyl ℤ r r le_rfl ν

def ExpLe (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) : Prop := KilledAt l r ν μ ((l : ℤ) ^ e)

def blockWt (p q w : ℕ) (κ : Fin q → ℕ) : Fin (p + q) → ℕ := Fin.append (fun _ : Fin p => w) κ

def blockWtLast (p q w : ℕ) (κ : Fin q → ℕ) : Fin (q + p) → ℕ := Fin.append κ (fun _ : Fin p => w)

def IsDepth (p q w : ℕ) (μ : Fin (p + q) → ℕ) (i : ℕ) : Prop :=
  ∑ a : Fin p, μ (Fin.castAdd q a) + i = p * w

def IsDepthLast (p q w : ℕ) (μ : Fin (q + p) → ℕ) (i : ℕ) : Prop :=
  ∑ a : Fin p, μ (Fin.natAdd q a) = p * w + i

def depth2 {r : ℕ} (ξ : Fin r → ℤ) (lam μ : Fin r → ℕ) : ℤ := ∑ a, ξ a * ((lam a : ℤ) - (μ a : ℤ))

def LemmaDGradedAt (l p q w : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (p + q) → ℤ) : Prop :=
  ∀ (i' : ℤ) (eL : ℕ),
    (∀ μ2 : Fin q → ℕ, depth2 ξ (blockWt p q w lam2) (blockWt p q w μ2) ≤ i' → ExpLe l q lam2 μ2 eL) →
    ∀ (i : ℕ) (μ : Fin (p + q) → ℕ), IsDepth p q w μ i → depth2 ξ (blockWt p q w lam2) μ ≤ i' →
      ExpLe l (p + q) (blockWt p q w lam2) μ (eL + padicValInt l (Dn p w i lam2))

def LemmaDGraded : Prop :=
  ∀ (l p q w : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (p + q) → ℤ), l.Prime → Antitone lam2 → (∀ b, lam2 b ≤ w) →
    Antitone ξ → LemmaDGradedAt l p q w lam2 ξ

def LemmaDLast : Prop :=
  ∀ (l p q w M : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) →
    ∀ eL : ℕ, (∀ μ2 : Fin q → ℕ, ExpLe l q lam2 μ2 eL) →
      ∀ (i : ℕ) (μ : Fin (q + p) → ℕ), IsDepthLast p q w μ i →
        ExpLe l (q + p) (blockWtLast p q w lam2) μ
          (eL + padicValInt l (Dn p (M - w) i fun b : Fin q => M - lam2 (Fin.rev b)))

def DnNeZero : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ), Dn p w i lam2 ≠ 0

def MuSupport : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), (∀ b, lam2 b ≤ w) → mu p w i lam2 c ≠ 0 →
    -(q : ℤ) ≤ c ∧ c < (w : ℤ) + (i : ℤ)

def ExpLeMono : Prop :=
  ∀ (l r : ℕ) (ν μ : Fin r → ℕ) (e e' : ℕ), e ≤ e' → ExpLe l r ν μ e → ExpLe l r ν μ e'

def MuLe : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), mu p w i lam2 c ≤ p

def MuRange : Prop :=
  ∀ (p w i q m : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) → mu p w i lam2 c ≠ 0 →
    (m : ℤ) - (q : ℤ) < c ∧ c < (w : ℤ)

def DnDvd : Prop :=
  ∀ (p w i q m : ℕ) (lam2 : Fin q → ℕ), (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    Dn p w i lam2 ∣ (((w + q - m - 1).factorial ^ p : ℕ) : ℤ)

def DnVal : Prop :=
  ∀ (l p w i q m : ℕ) (lam2 : Fin q → ℕ), l.Prime → (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    (l - 1) * padicValInt l (Dn p w i lam2) ≤ p * (w + q - m - 1)

end Formalism.CohomologicalDescent.LD
end

section

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent.WorkedExample

open Formalism.CohomologicalDescent

def MwFlip : Prop :=
  ∀ (l : ℕ) (b h : ℤ) (t κ : ℕ) (U : Finset ℤ),
    mwCount l (h - (b + t - 1)) t κ (U.image fun u => h - u) = mwCount l b t κ U

def LinkageFlip : Prop :=
  ∀ (K : Type) [CommRing K] (N : ℕ) (U U' : Fin N → ℤ) (c c' h : ℤ),
    (∏ a, (Polynomial.X + Polynomial.C (((U a + c : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c : ℤ)) : K)) →
    (∏ a, (Polynomial.X + Polynomial.C (((h - U a + c' : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((h - U' a + c' : ℤ)) : K))

structure Labels (ι : Type) (N : ℕ) where
  cc : ι → ι
  Φ : Set ι
  U : ι → Fin N → ℤ
  U' : ι → Fin N → ℤ
  bot : ι → ℤ

namespace Labels

variable {ι : Type} {N : ℕ}

def Refl (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) : Prop :=
  (∀ i, D.cc (D.cc i) = i) ∧ (∀ i, σ (D.cc i) = D.cc (σ i)) ∧ (∀ i, i ∈ D.Φ ∨ D.cc i ∈ D.Φ) ∧
  (∀ i a, D.U (D.cc i) a = (h : ℤ) - D.U i (Fin.rev a)) ∧
  (∀ i a, D.U' (D.cc i) a = (h : ℤ) - D.U' i (Fin.rev a)) ∧
  (∀ i, D.bot (D.cc i) = (h : ℤ) - (D.bot i + (t : ℤ) - 1))

def Linked (D : Labels ι N) (F : Type) [Field F] (t : ℕ) (cst : ι → ℤ) : Prop :=
  ∀ i ∈ D.Φ, StrictAnti (D.U i) ∧ StrictAnti (D.U' i) ∧
    (∀ s : Fin t, ∃ a, D.U i a = D.bot i + ((s : ℕ) : ℤ)) ∧
    (∏ a, (Polynomial.X + Polynomial.C (((D.U i a + cst i : ℤ)) : F))) =
      ∏ a, (Polynomial.X + Polynomial.C (((D.U' i a + cst i : ℤ)) : F))

def Carried (D : Labels ι N) (ep : ι → ι) (J : ι → Fin N → ℤ) (botJ : ι → ℤ) : Prop :=
  (ep = id ∨ ep = D.cc) ∧ (∀ i, J (ep i) = D.U' i) ∧ (∀ i, botJ (ep i) = D.bot i)

def mw (D : Labels ι N) (l t κ : ℕ) (i : ι) : ℕ :=
  mwCount l (D.bot i) t κ (Finset.univ.image (D.U i))

end Labels

def ShapeAt {ι : Type} (k j t q : ℕ) (D : Labels ι (k + j + t + q)) (τ : ι) : Prop :=
  (∀ a, 0 ≤ D.U τ a) ∧ ∑ a, D.U τ a = ∑ a, D.U' τ a ∧
  ∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
    D.U τ a = D.bot τ + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)

def DepthBound {ι : Type} (k j t q l h : ℕ) (D : Labels ι (k + j + t + q)) (σ : Equiv.Perm ι)
    (τ : ι) : Prop :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j),
      (D.U τ a - D.U' τ a) ≤
    (q : ℤ) * h +
      ((l : ℤ) * (D.mw l t (h / (l - 1)) (σ τ) : ℤ) + (D.mw l t (h / (l - 1)) τ : ℤ)) *
        ((t : ℤ) + 2 * ((h / (l - 1) : ℕ) : ℤ))

def MwLetters : Prop :=
  ∀ (ι : Type) (N : ℕ) (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ), D.Refl σ h t →
    ∀ (l κ : ℕ) (i : ι), D.mw l t κ (D.cc i) = D.mw l t κ i

def LinkedAll : Prop :=
  ∀ (ι : Type) (N : ℕ) (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) (F : Type) [Field F]
    (cst : ι → ℤ), D.Refl σ h t → D.Linked F t cst →
    ∀ i, StrictAnti (D.U i) ∧ StrictAnti (D.U' i) ∧
      (∀ s : Fin t, ∃ a, D.U i a = D.bot i + ((s : ℕ) : ℤ)) ∧
      (∏ a, (Polynomial.X + Polynomial.C (((D.U i a + 0 : ℤ)) : F))) =
        ∏ a, (Polynomial.X + Polynomial.C (((D.U' i a + 0 : ℤ)) : F))

def WEOrientLattice : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) [Fact l.Prime] (O F L : Type)
    [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l] [Field L] (I : Ideal O)
    [IsAdicComplete I O] (W : FrobeniusPeriodChange.WLat ι t (k + j + t + q) O F) (u : ℤ_[l]ˣ) (c : ℤ_[l])
    (D : Labels ι (k + j + t + q)) (cst : ι → ℤ)
    (ep : ι → ι) (J : ι → Fin (k + j + t + q) → ℤ) (botJ : ι → ℤ) (kap : ι → Fin t → ℤ) (τ : ι)
    (ζ : O) (em : O →+* L) (jj : ℕ → PowerSeries O →+* PowerSeries L),
    l ≠ 2 → t + 2 * (h / (l - 1)) < l →
    D.Refl σ h t → D.Linked F t cst → D.Carried ep J botJ →
    FrobeniusPeriodChange.NInputs W σ l h u c J (fun i s => botJ i + ((s : ℕ) : ℤ)) kap I ζ em jj →
    ShapeAt k j t q D τ →
    DepthBound k j t q l h D σ τ

end Formalism.CohomologicalDescent.WorkedExample
end
end
