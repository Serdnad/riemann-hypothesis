module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Complex.Exponential
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

open scoped BigOperators

namespace Formalism.CountingSumsFrames

def weylDim (n : ℕ) (lam : Fin n → ℤ) : ℚ :=
  ∏ i : Fin n, ∏ j : Fin n,
    if i < j then (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))
    else 1

end Formalism.CountingSumsFrames
end
end

section

noncomputable section

open scoped BigOperators TensorProduct
open Finset MvPolynomial

namespace Formalism.CountingSumsFrames

def ShareProd : Prop :=
  ∀ (J : ℕ) (κ : Fin J → ℝ) (n d : Fin J → ℕ), (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) →
    (∀ j, (1 - κ j) * (d j : ℝ) ≤ n j) →
      (1 - ∑ j, κ j) * ((∏ j, d j : ℕ) : ℝ) ≤ ((∏ j, n j : ℕ) : ℝ)

def dd {K σ : Type} [Field K] (x : σ) (m : ℕ) (f : MvPolynomial σ K) : MvPolynomial σ K :=
  C ((m.factorial : K)⁻¹) * (⇑(pderiv x))^[m] f

end Formalism.CountingSumsFrames
end
end

section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.CountingSumsFrames

abbrev XY (k : ℕ) : Type := Fin k ⊕ Fin k

abbrev PolXY (K : Type) [Field K] (k : ℕ) : Type := MvPolynomial (XY k) K

def xDeg {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∑ i : Fin k, m (Sum.inl i)

def yDeg {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∑ i : Fin k, m (Sum.inr i)

def xFact {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∏ i : Fin k, (m (Sum.inl i)).factorial

def yFact {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∏ i : Fin k, (m (Sum.inr i)).factorial

variable (K : Type) [Field K] (k : ℕ)

def hXY : PolXY K k := ∑ i : Fin k, X (Sum.inl i) * X (Sum.inr i)

def ctrF : PolXY K k →ₗ[K] PolXY K k :=
  ∑ i : Fin k, (pderiv (R := K) (Sum.inl i : XY k)).toLinearMap ∘ₗ
    (pderiv (R := K) (Sum.inr i : XY k)).toLinearMap

def hDiv (l : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ((l.factorial : K)⁻¹) • LinearMap.mulLeft K (hXY K k ^ l)

def ctrDiv (l : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ((l.factorial : K)⁻¹) • (ctrF K k ^ l)

def PolAB (A B : ℕ) : Submodule K (PolXY K k) where
  carrier := {f | ∀ m ∈ f.support, xDeg m = A ∧ yDeg m = B}
  zero_mem' := by
    intro m hm
    simp at hm
  add_mem' := by
    intro f g hf hg m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hf m h
    · exact hg m h
  smul_mem' := by
    intro c f hf m hm
    exact hf m (MvPolynomial.support_smul hm)

def HarAB (A B : ℕ) : Submodule K (PolXY K k) := PolAB K k A B ⊓ LinearMap.ker (ctrF K k)

def harProj (A B : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ∑ l ∈ range (min A B + 1),
    ((-1 : K) ^ l / (((A + B + k - 2).choose l : ℕ) : K)) • (hDiv K k l ∘ₗ ctrDiv K k l)

def levelProj (A B j : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ((((A + B + k - 2 * j + j - 1).choose j : ℕ) : K)⁻¹) •
    (hDiv K k j ∘ₗ harProj K k (A - j) (B - j) ∘ₗ ctrDiv K k j)

variable {K k}

def glAct (g : GL (Fin k) K) : PolXY K k →ₐ[K] PolXY K k :=
  aeval (Sum.elim
    (fun i : Fin k => ∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j))
    (fun i : Fin k => ∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) * X (Sum.inr j)))

def GaussLat (R : Subring K) : Set (PolXY K k) := {f | ∀ m, AddMonoidAlgebra.coeff f m ∈ R}

def FockLat (R : Subring K) : Set (PolXY K k) := {f | ∀ m, (xFact m : K) * AddMonoidAlgebra.coeff f m ∈ R}

def DualLat (R : Subring K) : Set (PolXY K k) :=
  {f | ∀ m, ((xFact m : K) * (yFact m : K)) * AddMonoidAlgebra.coeff f m ∈ R}

def latOf (g : GL (Fin k) K) (S : Set (PolXY K k)) : Set (PolXY K k) := glAct g '' S

def PLocal (R : Subring K) (p : ℕ) : Prop := ∀ n : ℕ, ¬ p ∣ n → ((n : K))⁻¹ ∈ R

def SlTwo : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ) (f : PolXY K k), f ∈ PolAB K k A B →
    ctrF K k (hXY K k * f) - hXY K k * ctrF K k f = ((A + B + k : ℕ) : K) • f

def HarProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ), 1 ≤ k →
    (∀ f : PolXY K k, f ∈ PolAB K k A B →
      harProj K k A B f ∈ HarAB K k A B ∧
      ∃ g ∈ PolAB K k (A - 1) (B - 1), f - harProj K k A B f = hXY K k * g) ∧
    (∀ f : PolXY K k, f ∈ HarAB K k A B → harProj K k A B f = f) ∧
    (1 ≤ A → 1 ≤ B → ∀ g : PolXY K k, g ∈ PolAB K k (A - 1) (B - 1) →
      harProj K k A B (hXY K k * g) = 0)

def LevelProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ), 1 ≤ k →
    (∀ f : PolXY K k, f ∈ PolAB K k A B → ∀ j ≤ min A B,
      ∃ w ∈ HarAB K k (A - j) (B - j), levelProj K k A B j f = hXY K k ^ j * w) ∧
    (∀ f : PolXY K k, f ∈ PolAB K k A B → ∑ j ∈ range (min A B + 1), levelProj K k A B j f = f) ∧
    (∀ f : PolXY K k, f ∈ PolAB K k A B → ∀ i ≤ min A B, ∀ j ≤ min A B,
      levelProj K k A B i (levelProj K k A B j f) = if i = j then levelProj K k A B j f else 0) ∧
    (∀ i ≤ min A B, ∀ j ≤ min A B, ∀ w : PolXY K k, w ∈ HarAB K k (A - i) (B - i) →
      levelProj K k A B j (hXY K k ^ i * w) = if i = j then hXY K k ^ i * w else 0)

def FockProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (R : Subring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal R p → ∀ f : PolXY K k, f ∈ PolAB K k A B → f ∈ latOf g (FockLat R) →
      ((p : K) ^ Nat.log p (A + B + k)) • harProj K k A B f ∈ latOf g (FockLat R) ∧
      ∀ j ≤ min A B,
        ((p : K) ^ (2 * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ latOf g (FockLat R)

def FockGaussXY : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (R : Subring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal R p → ∀ f : PolXY K k, f ∈ PolAB K k A B →
      (f ∈ latOf g (FockLat R) → (A.factorial : K) • f ∈ latOf g (GaussLat R)) ∧
      (f ∈ latOf g (GaussLat R) →
        ((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f ∈ latOf g (FockLat R))

def GaussProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (R : Subring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal R p → ∀ f : PolXY K k, f ∈ PolAB K k A B →
      (f ∈ latOf g (GaussLat R) →
        ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • harProj K k A B f ∈ latOf g (GaussLat R) ∧
        ∀ j ≤ min A B,
          ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ latOf g (GaussLat R)) ∧
      (f ∈ latOf g (DualLat R) →
        ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • harProj K k A B f ∈ latOf g (DualLat R) ∧
        ∀ j ≤ min A B,
          ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ latOf g (DualLat R))

def GaussLemmaH : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K) (j : ℕ)
    (G : PolXY K k), 1 ≤ k →
      hXY K k ^ j * G ∈ latOf g (GaussLat O.toSubring) → G ∈ latOf g (GaussLat O.toSubring)

def LevelLattice : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k a b j : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K), 1 ≤ k →
    latOf g (GaussLat O.toSubring) ∩ {f | ∃ w ∈ HarAB K k a b, f = hXY K k ^ j * w} =
      (fun w => hXY K k ^ j * w) '' (latOf g (GaussLat O.toSubring) ∩ (HarAB K k a b : Set (PolXY K k)))

def HarQuot : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal O.toSubring p →
    (∀ w G : PolXY K k, w ∈ HarAB K k A B → w = hXY K k * G → w = 0) ∧
    (∀ f : PolXY K k, f ∈ PolAB K k A B → f ∈ latOf g (GaussLat O.toSubring) →
      ∃ w ∈ HarAB K k A B, ∃ G ∈ PolAB K k (A - 1) (B - 1),
        w ∈ latOf g (GaussLat O.toSubring) ∧ G ∈ latOf g (GaussLat O.toSubring) ∧
        ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • f = w + hXY K k * G)

end Formalism.CountingSumsFrames
end
end

section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

def lgSeg (p : ℕ) (a : ℝ) (r : ℕ) : ℝ := Real.logb p (8 * a + r) + 1

def kapSeg (p : ℕ) (a : ℝ) (r s : ℕ) : ℝ := 3 * ((s : ℝ) + 2) * (r : ℝ) ^ 2 * lgSeg p a r

def epsSeg (S Y' κ lg E : ℝ) : ℝ := 2 * S / Y' + (2 * κ + 2 * S * lg / Y') / E

def DetLeadDiag : Prop :=
  ∀ (K : Type) [Field K] (n J : ℕ) (A : Matrix (Fin n) (Fin n) (Polynomial K)) (d : Fin n → K),
    (∀ a b, (A a b).natDegree ≤ J) → (∀ a b, (A a b).coeff J = if a = b then d a else 0) →
    A.det.natDegree ≤ n * J ∧ A.det.coeff (n * J) = ∏ a, d a

end Formalism.CountingSumsFrames
end
end

section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

def dimPol (k' A : ℕ) : ℕ := (A + k').choose k'

def dimHar (k' al be : ℕ) : ℕ :=
  dimPol k' al * dimPol k' be - (if al = 0 ∨ be = 0 then 0 else dimPol k' (al - 1) * dimPol k' (be - 1))

def hwt (m : ℕ) (A B : ℕ) : Fin (m + 2) → ℤ := Fin.cons (A : ℤ) (Fin.snoc (fun _ : Fin m => (0 : ℤ)) (-(B : ℤ)))

def cwt (m : ℕ) (A c B : ℕ) (cl : Fin m → ℤ) : Fin (m + 2) → ℤ :=
  Fin.cons ((A : ℤ) + c) (Fin.snoc cl (-(B : ℤ)))

def LevelCount : Prop :=
  ∀ k' A B : ℕ, ∑ j ∈ range (min A B + 1), dimHar k' (A - j) (B - j) = dimPol k' A * dimPol k' B

def LevelTailExp : Prop :=
  ∀ (k' A B J : ℕ) (La b' : ℝ), 2 ≤ k' → 0 < b' → 0 ≤ La → La * b' / (k' + 1) ≤ J →
    (B : ℝ) + k' + 1 ≤ 2 * b' →
    ((∑ j ∈ Icc J (min A B), dimHar k' (A - j) (B - j) : ℕ) : ℝ) ≤
      Real.exp (-La / 3) * ((dimPol k' A * dimPol k' B : ℕ) : ℝ)

def BinomRatio : Prop :=
  ∀ k' al j : ℕ, 0 < al → 1 - (k' : ℝ) * j / al ≤ (dimPol k' al : ℝ) / dimPol k' (al + j)

def BinomTail : Prop :=
  ∀ (k' be J : ℕ) (La b' : ℝ), 5 ≤ k' → 0 < b' → 0 ≤ La → La * b' / (k' + 1) ≤ J →
    (be : ℝ) + J + k' + 1 ≤ 2 * b' →
    ∑' j : ℕ, (dimPol k' be : ℝ) / dimPol k' (be + J + j) ≤
      Real.exp (-La / 3) * (((be : ℝ) + k') / ((k' : ℝ) - 1))

def DensityLower : Prop :=
  ∀ (k' al be : ℕ) (La b' : ℝ), 5 ≤ k' → 0 < al → 0 < b' → 0 ≤ La →
    (be : ℝ) + (⌊La * b' / (k' + 1)⌋₊ + 1 : ℕ) + k' + 1 ≤ 2 * b' →
    (1 - (k' : ℝ) * (La * b' / (k' + 1)) / al) * (1 - Real.exp (-La / 3)) ≤
      ∑ j ∈ range (⌊La * b' / (k' + 1)⌋₊ + 1),
        (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j))

end Formalism.CountingSumsFrames
end
end

section

noncomputable section

namespace Formalism.CountingSumsFrames

open Real Finset

def lgII (p : ℕ) (a : ℝ) (k : ℕ) : ℝ := Real.logb p (2 * a + k) + 1

def omII (r N n' c₀ c'' : ℕ) : ℝ := (r : ℝ) * N * c₀ + 2 * r * n' * c''

def QII (p G' : ℕ) : ℝ := (p : ℝ) ^ G'

def cPrII (r N n' c₀ c'' cStar : ℕ) : ℝ := (cStar : ℝ) + omII r N n' c₀ c''

def mStarII (N₁ k : ℕ) (Q c' al : ℝ) : ℝ := ((N₁ : ℝ) + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c')

def slII (Y : ℝ) (k : ℕ) (B : ℝ) : ℝ := ((⌊B / (Y * (k : ℝ) ^ 2)⌋ : ℤ) : ℝ)

def errorTerm (CE : ℝ) (N₁ r k : ℕ) (Q c' : ℝ) : ℝ := CE * c' * ((N₁ : ℝ) + r * k) * Q ^ 2

def HypII (C : ℝ) (p r N N₁ Nₛ J k n' L₁ G' : ℕ) (Y a : ℝ) (c₀ c'' D cStar : ℕ) : Prop :=
  13 ≤ p ∧ 2 ≤ r ∧ r ≤ N₁ ∧ N₁ ^ 2 ≤ r * N ∧ (r : ℝ) ≤ Y ∧
  C * (N₁ : ℝ) ^ 2 * Real.log a ≤ k ∧ N₁ + 3 * r ≤ k ∧
  256 * (k : ℝ) ^ 2 * N * Y ^ 2 ≤ (p : ℝ) ^ (L₁ - 1) ∧
  C * (N : ℝ) * (k : ℝ) ^ 2 * Real.logb p a ≤ D ∧ 8 * (D + 1) ≤ cStar ∧
  C * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * (QII p G') ^ 5 * cPrII r N n' c₀ c'' cStar * Y ≤ a ∧
  1 ≤ L₁ ∧ L₁ ≤ G' ∧ Nₛ ≤ N₁ ∧ Nₛ ≤ 2 * N ∧ 1 ≤ J ∧ J * r ≤ N

def ParamsII0 : Prop :=
  ∀ CE C₂ : ℝ, 1 ≤ CE → 1 ≤ C₂ → ∃ C : ℝ, 1 ≤ C ∧
  ∀ (p r N N₁ Nₛ J k n' L₁ G' : ℕ) (Y a al : ℝ) (c₀ c'' D cStar : ℕ),
    HypII C p r N N₁ Nₛ J k n' L₁ G' Y a c₀ c'' D cStar →
    0 ≤ al → al ≤ 1 + r * k * QII p G' →
    32 * (p : ℝ) * Y * (k : ℝ) ^ 2 * Nₛ * (QII p G') ^ 2 *
        (errorTerm CE N₁ r k (QII p G') (cPrII r N n' c₀ c'' cStar) +
          mStarII N₁ k (QII p G') (cPrII r N n' c₀ c'' cStar) al + 1) ≤ a ∧
    (∀ B : ℝ, a / QII p G' ≤ B →
      100 * (r : ℝ) ^ 2 * cPrII r N n' c₀ c'' cStar + 24 * ((N₁ : ℝ) + r) * c₀ +
          mStarII N₁ k (QII p G') (cPrII r N n' c₀ c'' cStar) al ≤ slII Y k B ∧
        slII Y k B ≤ B / 100) ∧
    128 * (k : ℝ) ^ 2 * Nₛ * Y ^ 2 ≤ (p : ℝ) ^ (L₁ - 1) ∧
    C₂ * (Nₛ : ℝ) ^ 2 * Real.log a ≤ k ∧ 1 ≤ Y ∧ Nₛ + r ≤ k - r

def degreeLoss (p : ℕ) (a : ℝ) (k N r J : ℕ) : ℝ :=
  (N : ℝ) * (k : ℝ) ^ 2 * lgII p a k + 2 * N * ((r : ℝ) ^ 2 * lgII p a k) +
    (J : ℝ) * r * ((r : ℝ) ^ 2 * lgII p a k) + 2 * ((N : ℝ) * k * lgII p a k)

def kappaSecondRegime (p : ℕ) (a : ℝ) (k N : ℕ) : ℝ := (N : ℝ) * (k : ℝ) ^ 2 * lgII p a k

def ParamsII5 : Prop :=
  ∀ CE C₂ : ℝ, 1 ≤ CE → 1 ≤ C₂ → ∃ C : ℝ, 1 ≤ C ∧
  ∀ (p r N N₁ Nₛ J k n' L₁ G' : ℕ) (Y a : ℝ) (c₀ c'' D cStar : ℕ),
    HypII C p r N N₁ Nₛ J k n' L₁ G' Y a c₀ c'' D cStar →
    (∀ Q' B dw : ℝ, 1 ≤ Q' → Q' ≤ QII p G' → dw ≤ 3 * a / Q' → (p : ℝ) ^ L₁ * a / Q' ≤ B →
      dw ≤ 3 * (p : ℝ) ^ (-(L₁ : ℤ)) * B ∧ 3 * (p : ℝ) ^ (-(L₁ : ℤ)) * B ≤ slII Y k B / 8) ∧
    (∀ (Dd : ℕ) (Qj dj B : ℝ), (p : ℝ) ^ Dd ≤ QII p G' → 1 ≤ Qj → Qj ≤ QII p G' →
      dj ≤ 3 * a * (p : ℝ) ^ (-(Dd : ℤ) - L₁ - 1) → a / ((p : ℝ) ^ Dd * Qj) ≤ B →
      r * dj / Qj ≤ 3 * r * (p : ℝ) ^ (-(L₁ : ℤ) - 1) * B ∧
        3 * r * (p : ℝ) ^ (-(L₁ : ℤ) - 1) * B ≤ slII Y k B / 8) ∧
    2 * degreeLoss p a k N r J < cPrII r N n' c₀ c'' cStar ∧
    (∀ (B ms : ℝ), a / QII p G' ≤ B → ms ≤ ms + slII Y k B / 2 - 24 * cPrII r N n' c₀ c'' cStar) ∧
    (∀ B : ℝ, a / QII p G' ≤ B → 3 * ((N₁ : ℝ) + r) * c₀ ≤ slII Y k B / 8) ∧
    (D : ℝ) < cPrII r N n' c₀ c'' cStar / 2 ∧
    degreeLoss p a k N r J + kappaSecondRegime p a k N ≤ D

end Formalism.CountingSumsFrames
end
end
