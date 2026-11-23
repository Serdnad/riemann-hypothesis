module

public import Formalism.MahlerMeasure.Bundle001
public import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelAct
public import Formalism.MahlerMeasure.MahlerMeasureProofs.Bundle001
public import Formalism.MahlerMeasure.Bundle002
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

namespace Formalism.GM.Top
open Formalism.GM
theorem detBlockLead : DetBlockLead := determinant_block_leading_term
end Formalism.GM.Top
end

section

namespace Formalism.GM.Top
open Formalism.GM
theorem levelAct : LevelAct := levelAct_of alternatingChooseSum
end Formalism.GM.Top
end

section

namespace Formalism.GM.M

open MvPolynomial Finset

def Letters.snoc {N : ℕ} (LL : Letters N) (n : ℕ) : Letters (N + 1) where
  vec := Fin.lastCases false LL.vec
  deg := Fin.lastCases n LL.deg

def Letters.total {N : ℕ} (LL : Letters N) : ℕ := ∑ i, LL.deg i

noncomputable def freezeSub (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) :
    Fin N × Fin r → MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] :=
  fun ⟨i, c⟩ =>
    if LL.vec i then
      (if c = ρ then ∑ c', X (Fin.castSucc i, c') * X (Fin.last N, c')
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c))
    else
      (if c = ρ then X (Fin.last N, ρ) * X (Fin.castSucc i, ρ)
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c) - X (Fin.castSucc i, ρ) * X (Fin.last N, c))

noncomputable def freeze (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] :=
  X (Fin.last N, ρ) ^ (n - LL.total) * aeval (freezeSub p LL ρ) f

def IsFrozenInv (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (n : ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) : Prop :=
  ∀ c, c ≠ ρ → glAct p (LL.snoc n) (N + 1) c ρ F = 0

def FreezeInto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (n : ℕ), LL.total ≤ n →
    ∀ f ∈ Pol p r LL,
      freeze p LL ρ n f ∈ Pol p r (LL.snoc n) ∧ IsFrozenInv p LL ρ n (freeze p LL ρ n f) ∧
      (f ∈ IntPol p (Fin N × Fin r) → freeze p LL ρ n f ∈ IntPol p (Fin (N + 1) × Fin r))

def FreezeBij : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (n : ℕ), LL.total ≤ n →
    (∀ f ∈ Pol p r LL, ∀ g ∈ Pol p r LL, freeze p LL ρ n f = freeze p LL ρ n g → f = g) ∧
    (∀ F ∈ PolZ p r (LL.snoc n), IsFrozenInv p LL ρ n F → ∃ f ∈ PolZ p r LL, freeze p LL ρ n f = F)

def FreezeY : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Letters N) (ρ : Fin r) (n : ℕ) {q : ℕ}
    (J : Fin q → ℕ) (Mt : Fin q → WithTop ℤ), LL.total ≤ n → (∀ k, J k ≤ N) →
    ∀ f ∈ Pol p r LL, (f ∈ Y p LL J Mt ↔ freeze p LL ρ n f ∈ Y p (LL.snoc n) J Mt)

def FreezeStep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (n : ℕ), LL.total ≤ n →
    ∀ f : MvPolynomial (Fin N × Fin r) ℚ_[p],
      X (Fin.last N, ρ) * freeze p LL ρ n f = freeze p LL ρ (n + 1) f

end Formalism.GM.M
end

section

namespace Formalism.GM

open Finset Polynomial

open Classical in
def LieMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (t₀ : ℤ)
    (U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
    (∀ i j k, ‖c i j k‖ ≤ 1) → (∀ i j, ‖U i j‖ ≤ 1) → (∀ i j, ‖V i j‖ ≤ 1) →
    ‖U.det‖ = 1 → ‖V.det‖ = 1 → 0 ≤ E → del₀ ≤ p ^ h →
    (binMatK K del₀ c).map (Polynomial.eval (t₀ : K)) = U * Matrix.diagonal d * V →
    (gaussR (Real.toNNReal ((p : ℝ) ^ (-E)))
        (((binMatK K del₀ c).det).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))) : ℝ) ≤
      (p : ℝ) ^ (-(E * (univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card))

def LieRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (h β : ℕ) (E : ℝ) (D : K[X]) (lead : K) (roots : Multiset K) (t₀ : ℤ),
    0 ≤ E → lead ≠ 0 →
    D = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (gaussR (Real.toNNReal ((p : ℝ) ^ (-E)))
        (D.comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))) : ℝ) ≤ (p : ℝ) ^ (-(E * β)) →
    (β : ℝ) * E ≤
      (-Real.logb p ‖lead‖ + (roots.map (fun ζ => vmin p h ((t₀ : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)

end Formalism.GM
end

section

namespace Formalism.GM

open Finset Polynomial

def progr (t₀ d : ℤ) (j : ℕ) : ℤ := t₀ + d * (j : ℤ)

def WindowCountAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (ζ : K) (t₀ d : ℤ) (Y₀ h : ℕ), IsCoprime d (p : ℤ) →
    ∑ j ∈ range Y₀, vmin p h ((progr t₀ d j : K) - ζ) ≤ ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / (p : ℝ) ^ i + 1)

open Classical in
def DiscsDisjointAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (roots : Multiset K) (t₀ d : ℤ) (Y₀ h : ℕ), IsCoprime d (p : ℤ) → Y₀ ≤ p ^ h →
    ∑ j ∈ range Y₀, (roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card ≤
      roots.card

open Classical in
def WindowMeanAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (roots : Multiset K) (lam La₀ E : ℝ) (n₀ del₀ : ℕ) (t₀ d : ℤ) (Y₀ h : ℕ) (β : ℤ → ℕ),
    IsCoprime d (p : ℤ) → 0 < Y₀ → Y₀ ≤ p ^ h → 0 < E →
    roots.card ≤ del₀ * n₀ →
    lam + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n₀ : ℝ) * La₀ →
    (∀ j ∈ range Y₀,
      (β (progr t₀ d j) : ℝ) * E ≤ (lam + (roots.map (fun ζ => vmin p h ((progr t₀ d j : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) →
    (∑ j ∈ range Y₀, (β (progr t₀ d j) : ℝ)) / (Y₀ : ℝ) ≤
      (n₀ : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E)


open Classical in
def WindowFullAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (lead : K) (roots : Multiset K) (t₀ d : ℤ) (Y₀ : ℕ)
    (La₀ : ℝ) (U V : ℤ → Matrix (Fin n) (Fin n) K) (dg : ℤ → Fin n → K),
    IsCoprime d (p : ℤ) → 0 < Y₀ → Y₀ ≤ p ^ h → del₀ ≤ p ^ h → 0 < E → lead ≠ 0 → (∀ i j k, ‖c i j k‖ ≤ 1) →
    (binMatK K del₀ c).det = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (∀ j ∈ range Y₀, (∀ a b, ‖U (progr t₀ d j) a b‖ ≤ 1) ∧ (∀ a b, ‖V (progr t₀ d j) a b‖ ≤ 1) ∧
      ‖(U (progr t₀ d j)).det‖ = 1 ∧ ‖(V (progr t₀ d j)).det‖ = 1 ∧
      (binMatK K del₀ c).map (Polynomial.eval ((progr t₀ d j : ℤ) : K)) =
        U (progr t₀ d j) * Matrix.diagonal (dg (progr t₀ d j)) * V (progr t₀ d j)) →
    -Real.logb p ‖lead‖ + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * La₀ →
    (∑ j ∈ range Y₀, ((univ.filter (fun i => ‖dg (progr t₀ d j) i‖ ≤ (p : ℝ) ^ (-E))).card : ℝ)) / (Y₀ : ℝ) ≤
      (n : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E)

def QuotientUpperBoundsOfPowerBounds : Prop :=
  ∀ (p a Y k Ns Qn be : ℝ) (D₁ L₁ Rj Rn : ℤ),
    1 < p → 0 < a → 0 < Y → 0 < k → 0 < Ns → 0 < Qn →
    be ≤ 4 * a * p ^ (-D₁ - L₁ - Rj) →
    a / (8 * Y * k ^ 2 * Ns * p ^ D₁ * Qn) < p ^ (Rn + 1) →
    128 * k ^ 2 * Ns * Y ^ 2 ≤ p ^ (L₁ - 1) →
    be / (Qn * p ^ (Rn - Rj)) ≤ 32 * p * Y * k ^ 2 * Ns * p ^ (-L₁) ∧
      32 * p * Y * k ^ 2 * Ns * p ^ (-L₁) ≤ 1 / (4 * Y)

noncomputable def lgV2 (p a r : ℕ) : ℝ := Real.logb p (8 * a + r) + 1

end Formalism.GM
end

section

namespace Formalism.GM.M

open MvPolynomial Finset

abbrev BVar (N r t : ℕ) := (Fin (N + 1) × Fin r) ⊕ (Fin (t + 1) × Bool)

structure BlockData (N : ℕ) where
  LL : Letters N
  T : TieData
  uPos : Fin N
  B : ℕ
  zPlus : ℕ

variable {N r : ℕ}

def finPos (N : ℕ) (k : ℕ) : Fin (N + 1) := ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩

def BlockData.lettersAt (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) : Letters N where
  vec := D.LL.vec
  deg := fun a =>
    -- Unfold the sum over `Fin D.T.t` to avoid a missing compiler specialization.
    let tieDeg := (List.finRange D.T.t).map fun i =>
      if (a : ℕ) = D.T.pos i ∨ (a : ℕ) = D.T.pos i + 1 then j i else 0
    D.LL.deg a - tieDeg.sum - (if a = D.uPos then jp else 0)

def chainEmb (N r t : ℕ) : Fin N × Fin r → BVar N r t := fun x => Sum.inl (Fin.castSucc x.1, x.2)

def xiVar (N r t : ℕ) (c : Fin r) : BVar N r t := Sum.inl (Fin.last N, c)

def scalZ (N r t : ℕ) (i : Fin (t + 1)) : BVar N r t := Sum.inr (i, false)
def scalS (N r t : ℕ) (i : Fin (t + 1)) : BVar N r t := Sum.inr (i, true)

noncomputable def BlockData.Ehat (p : ℕ) [Fact p.Prime] (D : BlockData N) (i : Fin D.T.t) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
    ∑ c, X (Sum.inl (finPos N (D.T.pos i), c)) * X (Sum.inl (finPos N (D.T.pos i + 1), c))

noncomputable def BlockData.Eplus (p : ℕ) [Fact p.Prime] (D : BlockData N) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  X (scalZ N r D.T.t (Fin.last D.T.t)) * X (scalS N r D.T.t (Fin.last D.T.t)) +
    ∑ c, X (Sum.inl (Fin.castSucc D.uPos, c)) * X (xiVar N r D.T.t c)

noncomputable def XiPolZ (p : ℕ) [Fact p.Prime] (N r t b : ℕ) : Submodule ℤ_[p] (MvPolynomial (BVar N r t) ℚ_[p]) :=
  (MvPolynomial.restrictSupport ℚ_[p]
      {m | (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b}).restrictScalars ℤ_[p] ⊓
    IntPol p (BVar N r t)

def BlockData.LevelOK (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) : Prop :=
  (∀ i, j i ≤ D.LL.deg (⟨min (D.T.pos i) (N - 1), by
      rcases Nat.eq_zero_or_pos N with h | h
      · exact absurd D.uPos.2 (by omega)
      · omega⟩) ∧ j i ≤ D.LL.deg (⟨min (D.T.pos i + 1) (N - 1), by
      rcases Nat.eq_zero_or_pos N with h | h
      · exact absurd D.uPos.2 (by omega)
      · omega⟩)) ∧ jp ≤ min (D.LL.deg D.uPos) D.B

def BlockData.gens (p : ℕ) [Fact p.Prime] [NeZero r] (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    Set (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr, ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp),
    x = (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus *
      rename (chainEmb N r D.T.t) y * g}

noncomputable def BlockData.SSZ (p : ℕ) [Fact p.Prime] [NeZero r] (D : BlockData N) :
    Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens p (r := r) j jp)

noncomputable def BlockData.Pall (p : ℕ) [Fact p.Prime] (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  tieP (fun c => Sum.inl (Fin.castSucc D.uPos, c)) (fun c => xiVar N r D.T.t c)
    (scalZ N r D.T.t (Fin.last D.T.t)) (scalS N r D.T.t (Fin.last D.T.t))
    (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus
    ((List.finRange D.T.t).foldr (fun i acc =>
      tieP (fun c => Sum.inl (finPos N (D.T.pos i), c)) (fun c => Sum.inl (finPos N (D.T.pos i + 1), c))
        (scalZ N r D.T.t (Fin.castSucc i)) (scalS N r D.T.t (Fin.castSucc i))
        ((D.lettersAt j jp).deg (⟨min (D.T.pos i) (N - 1), by
            rcases Nat.eq_zero_or_pos N with h | h
            · exact absurd D.uPos.2 (by omega)
            · omega⟩))
        ((D.lettersAt j jp).deg (⟨min (D.T.pos i + 1) (N - 1), by
            rcases Nat.eq_zero_or_pos N with h | h
            · exact absurd D.uPos.2 (by omega)
            · omega⟩))
        (D.T.z i) acc) y)

noncomputable def BlockData.PSZ (p : ℕ) [Fact p.Prime] [NeZero r] (D : BlockData N) :
    Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp),
    {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr, ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp),
      x = (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
        D.Pall p (r := r) j jp (rename (chainEmb N r D.T.t) y * g)})

end Formalism.GM.M
end
