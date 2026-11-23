module

public import GroundTheory.HeightsAndTheta.Heights.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle003
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem numStandardTable_eq_frobDim (h1 : FrobeniusDimensionFormula.Statement) {m : ℕ}
    (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (numStandardTable lam : ℚ) = GroundTheory.Heights₂.Heights.frobDim lam := by
  rw [h1 m lam hlam, GroundTheory.Heights₂.Heights.frobDim]
  congr 2
  unfold vandermondeOf
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]

theorem LemmaC.proof (h1 : FrobeniusDimensionFormula.Statement) : LemmaC.Statement := by
  intro r a nu hnu
  have hsum : Antitone (fun i => a + nu i) := fun i j hij => Nat.add_le_add_left (hnu hij) a
  have hrect : Antitone (rectangle r a) := fun _ _ _ => le_rfl
  have hb := GroundTheory.Heights₂.Heights.FrobeniusRectangleBound.intersectionNumber_baseChange r a nu hnu
  rw [← numStandardTable_eq_frobDim h1 _ hsum, ← numStandardTable_eq_frobDim h1 nu hnu,
    show (fun _ : Fin r => a) = rectangle r a from rfl,
    ← numStandardTable_eq_frobDim h1 _ hrect] at hb
  exact_mod_cast hb

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv

noncomputable section

namespace Comb

def alternantPsum (m : ℕ) (ρ : List ℕ) : MvPolynomial (Fin m) ℚ :=
  vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) *
    (ρ.map fun q => psum (Fin m) ℚ q).prod

def IsStandard {m : ℕ} {lam : Fin m → ℕ} (T : youngCells lam ≃ Fin (youngCells lam).card) : Prop :=
  ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q

def rowWord {m : ℕ} {lam : Fin m → ℕ} (T : youngCells lam ≃ Fin (youngCells lam).card) :
    Fin (youngCells lam).card → Fin m :=
  fun t => (T.symm t).1.1

def cellOfWord {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) : Fin m × ℕ :=
  (w t, pcnt w t (w t))

end Comb

open Comb

def CombCardYoungCells.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), (youngCells lam).card = ∑ i, lam i

def CombYoungRowCard.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (i : Fin m),
    (univ.filter fun p : youngCells lam => p.1.1 = i).card = lam i

def CombTableauRowCount.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (T : youngCells lam ≃ Fin (youngCells lam).card) (t : ℕ)
    (i : Fin m),
    pcnt (rowWord T) t i = (univ.filter fun p : youngCells lam => p.1.1 = i ∧ (T p : ℕ) < t).card

def CombTableauRowPrefix.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
    ∀ t : Fin (youngCells lam).card,
      (univ.filter fun p : youngCells lam =>
        p.1.1 = (T.symm t).1.1 ∧ (T p : ℕ) < (t : ℕ)).card = (T.symm t).1.2

def CombTableauRowLattice.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
    ∀ (t : ℕ) (i j : Fin m), i ≤ j →
      (univ.filter fun p : youngCells lam => p.1.1 = j ∧ (T p : ℕ) < t).card ≤
        (univ.filter fun p : youngCells lam => p.1.1 = i ∧ (T p : ℕ) < t).card

def CombWordOfTableau.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
      rowWord T ∈ latticeWords (youngCells lam).card lam ∧
        ∀ t, cellOfWord (rowWord T) t = (T.symm t).1

def CombCellOfWordMem.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (w : Fin (youngCells lam).card → Fin m),
    w ∈ latticeWords (youngCells lam).card lam → ∀ t, cellOfWord w t ∈ youngCells lam

def CombCellOfWordInj.Statement : Prop :=
  ∀ (m n : ℕ) (w : Fin n → Fin m), Function.Injective (cellOfWord w)

def CombCellOfWordMono.Statement : Prop :=
  ∀ (m n : ℕ) (w : Fin n → Fin m), IsLattice w → ∀ s t : Fin n,
    (cellOfWord w s).1 ≤ (cellOfWord w t).1 → (cellOfWord w s).2 ≤ (cellOfWord w t).2 → s ≤ t

def CombTableauOfWord.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ w ∈ latticeWords (youngCells lam).card lam,
      ∃ T : youngCells lam ≃ Fin (youngCells lam).card, IsStandard T ∧ rowWord T = w

def CombTableEqWords.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    numStandardTable lam = (latticeWords (∑ i, lam i) lam).card

def CombCfUpdateZero.Statement : Prop :=
  ∀ (m : ℕ) (A : MvPolynomial (Fin m) ℚ), IsAlt A →
    ∀ (lam : Fin m → ℕ), Antitone lam → ∀ i : Fin m, 1 ≤ lam i + stair m i →
      (lam i = 0 ∨ ¬ Antitone (Function.update lam i (lam i - 1))) →
        cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - 1)) A = 0

def CombCfAtStair.Statement : Prop :=
  ∀ (m n : ℕ) (lam : Fin m → ℕ), Antitone lam →
    cf (fun i => lam i + stair m i) (alternantPsum m (List.replicate n 1)) =
      (latticeWords n lam).card

def CombCfMonomialPsumOne.Statement : Prop :=
  ∀ (m n : ℕ) (v l : Fin m → ℕ),
    cf l (monomial (ex v) (1 : ℚ) * psum (Fin m) ℚ 1 ^ n) =
      if (∀ i, v i ≤ l i) ∧ ∑ i, l i = ∑ i, v i + n then
        (n.factorial : ℚ) / ∏ i, ((l i - v i).factorial : ℚ)
      else 0

def CombDetDescFactorial.Statement : Prop :=
  ∀ (m : ℕ) (l : Fin m → ℕ),
    (Matrix.of fun i j : Fin m => ((l i).descFactorial (stair m j) : ℚ)).det =
      vandermondeOf (fun i => (l i : ℚ))

def CombCfVandermondePsumOne.Statement : Prop :=
  ∀ (m n : ℕ) (l : Fin m → ℕ), ∑ i, l i = ∑ i, stair m i + n →
    cf l (alternantPsum m (List.replicate n 1)) =
      (n.factorial : ℚ) * vandermondeOf (fun i => (l i : ℚ)) / ∏ i, ((l i).factorial : ℚ)

def CombSortLe.Statement : Prop :=
  ∀ (m : ℕ) (u l : Fin m → ℕ) (σ : Perm (Fin m)), Antitone l → (∀ i, u i ≤ l i) →
    Antitone (u ∘ σ) → ∀ k, u (σ k) ≤ l k

def CombSortShift.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam → ∀ (q : ℕ) (i : Fin m), q ≤ lam i + stair m i →
    Function.Injective (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q)) →
    ∃ (σ : Perm (Fin m)) (μ : Fin m → ℕ), Antitone μ ∧ (∀ k, μ k ≤ lam k) ∧
      ∀ k, Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) (σ k) =
        μ k + stair m k

def CombSortShiftDistinct.Statement : Prop :=
  ∀ (m : ℕ) (l : Fin m → ℕ), Function.Injective l → ∀ q : ℕ, 1 ≤ q →
    ∀ i j : Fin m, i ≠ j → q ≤ l i → q ≤ l j → ∀ σ τ : Perm (Fin m),
      Function.update l i (l i - q) ∘ σ ≠ Function.update l j (l j - q) ∘ τ

def CombPcntAppend.Statement : Prop :=
  ∀ (m n q : ℕ) (w : Fin n → Fin m) (s : Fin q → Fin m) (t : ℕ) (i : Fin m),
    pcnt (Fin.append w s) t i = pcnt w t i + pcnt s (t - n) i

def CombExtendWord.Statement : Prop :=
  ∀ (m n q : ℕ) (μ lam : Fin m → ℕ), Antitone μ → Antitone lam → (∀ i, μ i ≤ lam i) →
    ∑ i, lam i = ∑ i, μ i + q →
      ∃ s : Fin q → Fin m, ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam

def CombStripSum.Statement : Prop :=
  ∀ (m n q : ℕ) (lam : Fin m → ℕ), Antitone lam → 1 ≤ q →
    ∑ i : Fin m, (if q ≤ lam i + stair m i then
      |cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
        (alternantPsum m (List.replicate n 1))| else 0) ≤
      ((latticeWords (n + q) lam).card : ℚ)

def CombCfBound.Statement : Prop :=
  ∀ (m : ℕ) (ρ : List ℕ), (∀ q ∈ ρ, 1 ≤ q) → ∀ lam : Fin m → ℕ, Antitone lam →
    |cf (fun i => lam i + stair m i) (alternantPsum m ρ)| ≤ ((latticeWords ρ.sum lam).card : ℚ)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchurSignCoefficient.coeff_aeval_diagonal {N : ℕ} (c : Fin N → ℚ)
    (P : MvPolynomial (Fin N) ℚ) (e : Fin N →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun i : Fin N => C (c i) * X i) P) e = (∏ i, c i ^ e i) * AddMonoidAlgebra.coeff P e := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hmon : aeval (fun i : Fin N => C (c i) * X i) (monomial u a) =
        monomial u (a * ∏ i, c i ^ u i) := by
      rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
        Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, algebraMap_eq, C_mul, ← C_pow, ← map_prod]
      ring
    rw [hmon, coeff_monomial, coeff_monomial]
    split_ifs with hue
    · subst hue; ring
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem SchurSignCoefficient.aeval_smul_powerSumHom (N : ℕ) (s : ℚ)
    (S : MvPolynomial (Fin N) ℚ) :
    aeval (fun i : Fin N => C s * X i) (powerSumHom N S) =
      powerSumHom N (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S) := by
  have key : (aeval (fun i : Fin N => C s * X i)).comp (powerSumHom N) =
      (powerSumHom N).comp (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i)) := by
    apply MvPolynomial.algHom_ext
    intro i

    simp only [AlgHom.comp_apply, powerSumHom, aeval_X, map_mul, aeval_C, algebraMap_eq, psum,
    map_sum, map_pow, mul_pow, Finset.mul_sum]
  exact DFunLike.congr_fun key S

theorem SchurSignCoefficient.proof (h : SchurPowerSumCoefficient.Statement) :
    SchurSignCoefficient.Statement := by
  intro N r k hk1 hkN nu s _ hnu hsum
  obtain ⟨S₀, hS₀, hc₀⟩ := h N r k hk1 hkN nu hnu hsum
  refine ⟨aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S₀, ?_, ?_⟩
  · rw [← SchurSignCoefficient.aeval_smul_powerSumHom, hS₀]
  · rw [SchurSignCoefficient.coeff_aeval_diagonal, hc₀]
    congr 1
    rw [Finset.prod_eq_single (⟨k - 1, by omega⟩ : Fin N)]
    · rw [Finsupp.single_eq_same, pow_one]
      congr 1
      simp only
      omega
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg (Ne.symm hb), pow_zero]
    · intro hn
      exact absurd (Finset.mem_univ _) hn

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem exists_hookShape_of_isHook {r k : ℕ} (hk : 1 ≤ k) (nu : Fin r → ℕ) (hanti : Antitone nu)
    (hsum : ∑ i, nu i = k) (hhook : ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) :
    ∃ l, l < r ∧ l < k ∧ nu = hookShape r k l := by
  set g : ℕ → ℕ := fun j => if h : j < r then nu ⟨j, h⟩ else 0 with hg
  have hgnu : ∀ i : Fin r, g i = nu i := fun i => by simp [hg, i.isLt]
  have hsumg : ∑ j ∈ range r, g j = k := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [hgnu]
    exact hsum
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      simp at hsumg
      omega
    · exact h
  have hanti_g : ∀ i j, i ≤ j → g j ≤ g i := by
    intro i j hij
    by_cases hj : j < r
    · have hi : i < r := lt_of_le_of_lt hij hj
      simp only [hg, dif_pos hj, dif_pos hi]
      exact hanti (show (⟨i, hi⟩ : Fin r) ≤ ⟨j, hj⟩ from hij)
    · simp [hg, dif_neg hj]
  have hle1 : ∀ j, 1 ≤ j → g j ≤ 1 := by
    intro j hj
    by_cases h : j < r
    · simp only [hg, dif_pos h]
      exact hhook ⟨j, h⟩ (by simp only; omega)
    · simp [hg, dif_neg h]
  have hsplit : g 0 + ∑ j ∈ Ico 1 r, g j = k := by
    rw [← Finset.sum_eq_sum_Ico_succ_bot hr, ← Finset.range_eq_Ico]
    exact hsumg
  set t := ∑ j ∈ Ico 1 r, g j with ht
  have hrow : ∀ i, 1 ≤ i → i < r → g i = if i ≤ t then 1 else 0 := by
    intro i hi1 hir
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle1 i hi1) with h0 | h1
    · have hz : ∀ j ∈ Ico i r, g j = 0 := fun j hj => by
        have := hanti_g i j (mem_Ico.mp hj).1
        omega
      have hti : t ≤ i - 1 := by
        rw [ht, ← Finset.sum_Ico_consecutive g hi1 hir.le, Finset.sum_eq_zero hz, add_zero]
        calc ∑ j ∈ Ico 1 i, g j ≤ ∑ j ∈ Ico 1 i, 1 :=
              Finset.sum_le_sum fun j hj => hle1 j (mem_Ico.mp hj).1
          _ = i - 1 := by simp
      rw [h0, if_neg (by omega)]
    · have ho : ∀ j ∈ Ico 1 (i + 1), g j = 1 := fun j hj => by
        have h2 := hanti_g j i (by have := (mem_Ico.mp hj).2; omega)
        have h3 := hle1 j (mem_Ico.mp hj).1
        omega
      have hit : i ≤ t := by
        rw [ht, ← Finset.sum_Ico_consecutive g (show 1 ≤ i + 1 by omega)
          (show i + 1 ≤ r by omega), Finset.sum_congr rfl ho]
        simp
      rw [h1, if_pos hit]
  have htr : t < r := by
    have : t ≤ r - 1 := by
      calc t ≤ ∑ j ∈ Ico 1 r, 1 := Finset.sum_le_sum fun j hj => hle1 j (mem_Ico.mp hj).1
        _ = r - 1 := by simp
    omega
  have hg0 : 1 ≤ g 0 := by
    by_contra h
    have hz : ∀ j, g j = 0 := fun j => by
      have := hanti_g 0 j (Nat.zero_le j)
      omega
    simp [hz] at hsumg
    omega
  refine ⟨t, htr, by omega, ?_⟩
  funext i
  rw [← hgnu i]
  unfold hookShape
  by_cases hi0 : (i : ℕ) = 0
  · rw [if_pos hi0, hi0]
    omega
  · rw [if_neg hi0, hrow i (by omega) i.isLt]

theorem HookSumBound.proof (hC : LemmaC.Statement) (hH : HookTableauCount.Statement) :
    HookSumBound.Statement := by
  intro r a k b hk hb
  have hB0 : (0 : ℚ) ≤ (Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a) := by
    positivity
  have hterm : ∀ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
      |b nu| ≤ ((Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)) *
        (numStandardTable nu : ℚ) := by
    intro nu hnu
    have hmem := (Finset.mem_filter.mp hnu).1
    have h := Finset.mem_filter.mp hmem
    have hsum : ∑ i, nu i = k := Finset.Nat.mem_antidiagonalTuple.mp h.1
    have hc := hC r a nu (fun i j hij => h.2 i j hij)
    rw [hsum] at hc
    calc |b nu| ≤ numStandardTable (fun i => a + nu i) := hb nu hmem
      _ ≤ _ := by exact_mod_cast hc
  have himg : (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) ⊆
      (range (min r k)).image (hookShape r k) := by
    intro nu hnu
    obtain ⟨hmem, hhook⟩ := Finset.mem_filter.mp hnu
    have h := Finset.mem_filter.mp hmem
    obtain ⟨l, hlr, hlk, rfl⟩ := exists_hookShape_of_isHook hk nu (fun i j hij => h.2 i j hij)
      (Finset.Nat.mem_antidiagonalTuple.mp h.1) hhook
    exact Finset.mem_image.mpr ⟨l, Finset.mem_range.mpr (lt_min hlr hlk), rfl⟩
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hhooks : ∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
      (numStandardTable nu : ℚ) ≤ 2 ^ (k - 1) := by
    calc _ ≤ ∑ nu ∈ (range (min r k)).image (hookShape r k), (numStandardTable nu : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity
      _ ≤ ∑ l ∈ range (min r k), (numStandardTable (hookShape r k l) : ℚ) :=
          Finset.sum_image_le_of_nonneg fun _ _ => by positivity
      _ = ∑ l ∈ range (min r k), ((k - 1).choose l : ℚ) := by
          refine Finset.sum_congr rfl fun l hl => ?_
          have hl' := lt_min_iff.mp (Finset.mem_range.mp hl)
          rw [hH r k l hl'.2 hl'.1]
      _ ≤ ∑ l ∈ range k, ((k - 1).choose l : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_right _ _))
            fun _ _ _ => by positivity
      _ = 2 ^ (k - 1) := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          rw [Nat.add_sub_cancel]
          exact_mod_cast Nat.sum_range_choose n
  calc _ ≤ ((Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)) * 2 ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hhooks hB0
    _ = _ := by ring

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem numStandardTable_pos {m : ℕ} (lam : Fin m → ℕ) : 0 < numStandardTable lam := by
  classical
  let t : Finset (Fin m ×ₗ ℕ) := (youngCells lam).map (toLex : Fin m × ℕ ≃ _).toEmbedding
  have ht : t.card = (youngCells lam).card := Finset.card_map _
  let e : Fin (youngCells lam).card ≃o t := t.orderIsoOfFin ht
  let g : youngCells lam ≃ t :=
    Equiv.subtypeEquiv toLex fun p => by simp [t]
  let T : youngCells lam ≃ Fin (youngCells lam).card := g.trans e.symm.toEquiv
  have hT : ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q := by
    intro p q h1 h2
    apply e.symm.monotone
    show toLex p.1 ≤ toLex q.1
    exact Prod.Lex.toLex_mono ⟨h1, h2⟩
  have : Nonempty {T : youngCells lam ≃ Fin (youngCells lam).card //
      ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q} := ⟨⟨T, hT⟩⟩
  exact Nat.card_pos

theorem RectangleTablePos.intersectionNumber_baseChange : RectangleTablePos.Statement :=
  fun r a => numStandardTable_pos (rectangle r a)

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

theorem CoinvAboveTop.proof (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAboveTop.Statement := by
  intro K _ _ f n d H hH hd
  obtain ⟨v, hv, hJ⟩ := h1 K f n H
  obtain ⟨Q, hQ, hcomp⟩ := h2 K f n (H - v) hJ d
  refine ⟨Q, hQ, ?_⟩
  have h0 : homogeneousComponent d v = 0 := (h3 K f n v hv).1 d hd
  have hHd : homogeneousComponent d H = H := by
    rw [homogeneousComponent_of_mem (mem_homogeneousSubmodule d H |>.mpr hH), if_pos rfl]
  rw [← hcomp, map_sub, h0, sub_zero, hHd]

end GroundTheory.Heights₂.Heights.RestTerms
end
