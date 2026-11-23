module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem OtherFactorBound.add_le_mul_add_one {r a : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a) :
    r + a ≤ r * a + 1 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  nlinarith [Nat.zero_le (r' * a')]

theorem OtherFactorBound.coeff_bound (hS : SchurSignCoefficient.Statement)
    (hH : HookSumBound.Statement) (r a k : ℕ) (c : SmallBlock) (hk1 : 1 ≤ k) (hkN : k ≤ r + a)
    (S : MvPolynomial (Fin (r + a)) ℚ)
    (hSeq : powerSumHom (r + a) S =
      ∑ nu ∈ partitionsOf r k,
        C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
          aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu)) :
    |S.coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)| ≤
      (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) / k := by
  set e := Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1 with he
  have hs : c.sign = 1 ∨ c.sign = -1 := by cases c <;> simp [SmallBlock.sign]
  have hex : ∀ nu : Fin r → ℕ, ∃ T : MvPolynomial (Fin (r + a)) ℚ, nu ∈ partitionsOf r k →
      powerSumHom (r + a) T = aeval (fun i : Fin (r + a) => C c.sign * X i)
          (schur (Fin (r + a)) nu) ∧
        AddMonoidAlgebra.coeff T e = c.sign ^ k * if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card) / k
        else 0 := by
    intro nu
    by_cases hnu : nu ∈ partitionsOf r k
    · have hmem := hnu
      simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hmem
      obtain ⟨T, hT1, hT2⟩ := hS (r + a) r k hk1 hkN nu c.sign hs
        (fun i j hij => hmem.2 i j hij) hmem.1
      exact ⟨T, fun _ => ⟨hT1, hT2⟩⟩
    · exact ⟨0, fun h => absurd h hnu⟩
  choose T hT using hex
  have hSsum : S = ∑ nu ∈ partitionsOf r k,
      C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * T nu := by
    apply Flag.powerSumHom_injective

    rw [hSeq, map_sum]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [map_mul, (hT nu hnu).1]
    congr 1
    simp [powerSumHom]
  have hterm : ∀ nu ∈ partitionsOf r k,
      |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| =
        (if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) else 0) / k := by
    intro nu hnu
    rw [(hT nu hnu).2, abs_mul, abs_mul, abs_pow]
    have habs : |c.sign| = 1 := by rcases hs with h | h <;> simp [h]
    rw [habs, one_pow, one_mul, Nat.abs_cast]
    split_ifs
    · rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]; ring
    · simp
  calc |S.coeff e|
      = |∑ nu ∈ partitionsOf r k,
          ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| := by
        rw [hSsum, coeff_sum]
        simp only [coeff_C_mul]
    _ ≤ ∑ nu ∈ partitionsOf r k,
          |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = (∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
          |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ)|) / k := by
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_filter]
        simp only [Nat.abs_cast]
    _ ≤ (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) / k := by
        gcongr
        exact hH r a k (fun nu => ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ)) hk1
          (fun nu _ => by simp)

theorem OtherFactorBound.proof (hO : OtherFactorFormula.Statement)
    (hF : SameFactorFormula.Statement) (hS : SchurSignCoefficient.Statement)
    (hB : CharacterBound.Statement) (hH : HookSumBound.Statement)
    (hR : RectangleTablePos.Statement) (hD : RestPolynomialDecomposes.Statement) :
    OtherFactorBound.Statement := by
  intro f r a c hf hr ha
  have hP : (0 : ℚ) < numStandardTable (rectangle r a) := by exact_mod_cast hR r a
  have hkey := OtherFactorBound.add_le_mul_add_one hr ha
  refine ⟨?_, hD f r a c, ?_⟩
  · obtain ⟨C₀, hC₀, hJ, -⟩ := hF f r a c hf hr ha
    rw [hJ]
    have h1 : ((f * (r * a)).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((r * a).factorial : ℚ) ≠ 0 := by positivity
    have := hP.ne'
    simp_all
  intro Q hQ k hk2 hkN τ τ' hne
  have hk1 : k - 1 ≤ r * a := by omega
  refine ⟨fun h => absurd h (by omega), ?_⟩
  have hf2 : 2 ≤ f := by
    by_contra h
    have : f = 1 := by omega
    subst this
    exact hne (Subsingleton.elim _ _)
  obtain ⟨C₀, hC₀, hJ, hT⟩ := hO f r a c hf2 hr ha
  obtain ⟨S, hSeq, hTk⟩ := hT Q hQ k hk2 hkN τ τ' hne
  have hcoef := OtherFactorBound.coeff_bound hS hH r a k c (by omega) hkN S hSeq
  have hchi := hB r (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
    (fun _ _ _ => le_rfl) (by
      intro q hq
      simp only [List.mem_cons, List.mem_replicate] at hq
      omega)
  rw [hTk, hJ]
  set y := AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)
  set z := symmetricGroupCharacter (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
  set P : ℚ := (numStandardTable (rectangle r a) : ℚ) with hPdef
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  have hg : g + 2 - 2 = g := by omega
  rw [hg]

  set n1 := r * a with hn1
  set n := (g + 2) * n1 with hn
  have hD1 : ((n1 + k).factorial : ℚ) =
      (Nat.choose (n1 + k) k : ℚ) * (k.factorial : ℚ) * (n1.factorial : ℚ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial n1 k
    rw [← this]; push_cast; ring
  have hA : (n1.factorial : ℚ) =
      ((n1 - (k - 1)).factorial : ℚ) * (n1.descFactorial (k - 1) : ℚ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hk1).symm
  have hM : ((n + 1).factorial : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hchoose : (0 : ℚ) < Nat.choose (n1 + k) k := by
    exact_mod_cast Nat.choose_pos (by omega)

  have hstep : |C₀ * k * ((n + 1).factorial : ℚ) /
        (((n1 + k).factorial : ℚ) * ((n1 - (k - 1)).factorial : ℚ) *
          ((n1).factorial : ℚ) ^ g) * P ^ g * z * y| ≤
      ((n + 1 : ℕ) : ℚ) * |C₀ * (n.factorial : ℚ) / ((n1).factorial : ℚ) ^ (g + 2) * P ^ (g + 2)| *
        ((n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1)) / (k.factorial : ℚ) := by
    rw [hD1, hM]
    simp only [abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_pos hP]
    have hX1 : 0 ≤ |C₀| * (k : ℚ) * (((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ)) /
        ((Nat.choose (n1 + k) k : ℚ) * (k.factorial : ℚ) * (n1.factorial : ℚ) *
          ((n1 - (k - 1)).factorial : ℚ) * (n1.factorial : ℚ) ^ g) * P ^ g := by positivity
    refine (mul_le_mul (mul_le_mul_of_nonneg_left hchi hX1) hcoef (abs_nonneg _)
      (by positivity)).trans (le_of_eq ?_)
    field_simp
    rw [hA]
    ring
  refine hstep.trans ?_

  have hX : (n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1) ≤ restX r a ^ (k - 1) := by
    have h1 : (n1.descFactorial (k - 1) : ℚ) ≤ (n1 : ℚ) ^ (k - 1) := by
      exact_mod_cast Nat.descFactorial_le_pow n1 (k - 1)
    have h2 : (2 * (n1 : ℚ)) ≤ restX r a := by
      simp only [restX, hn1]; push_cast; nlinarith [(Nat.cast_nonneg (r + a : ℕ) : (0 : ℚ) ≤ _)]
    calc (n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1)
        ≤ (n1 : ℚ) ^ (k - 1) * 2 ^ (k - 1) := by gcongr
      _ = (2 * (n1 : ℚ)) ^ (k - 1) := by ring
      _ ≤ restX r a ^ (k - 1) := by gcongr
  gcongr

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem sameFactor_descFactorial_le (n₁ N : ℕ) :
    ∀ k : ℕ, 1 ≤ k → k ≤ N →
      (n₁ + k).descFactorial k * 2 ^ (k - 1) ≤ (n₁ + 1) * (2 * (n₁ + N)) ^ (k - 1)
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, _ => by simp [Nat.descFactorial]
  | k + 2, _, hN => by
    have ih : (n₁ + (k + 1)).descFactorial (k + 1) * 2 ^ k ≤ (n₁ + 1) * (2 * (n₁ + N)) ^ k := by
      simpa only [Nat.add_sub_cancel] using
        sameFactor_descFactorial_le n₁ N (k + 1) (by omega) (by omega)
    have hd : (n₁ + (k + 2)).descFactorial (k + 2) =
        (n₁ + (k + 1) + 1) * (n₁ + (k + 1)).descFactorial (k + 1) :=
      Nat.succ_descFactorial_succ (n₁ + (k + 1)) (k + 1)
    rw [show k + 2 - 1 = k + 1 by omega, pow_succ 2 k, pow_succ (2 * (n₁ + N)) k, hd]
    have hleft :
        (n₁ + (k + 1) + 1) * (n₁ + (k + 1)).descFactorial (k + 1) * (2 ^ k * 2) =
          ((n₁ + (k + 1)).descFactorial (k + 1) * 2 ^ k) * (2 * (n₁ + (k + 1) + 1)) := by
      ring
    rw [hleft, ← mul_assoc (n₁ + 1)]
    exact Nat.mul_le_mul ih (by omega)

theorem sameFactor_choose_le (r a k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ r + a) :
    (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ) ≤
      restX r a ^ (k - 1) / (k.factorial : ℚ) := by
  have h := sameFactor_descFactorial_le (r * a) (r + a) k hk1 hkN
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have hq : ((k.factorial * Nat.choose (r * a + k) k * 2 ^ (k - 1) : ℕ) : ℚ) ≤
      ((((r * a) + 1) * (2 * ((r * a) + (r + a))) ^ (k - 1) : ℕ) : ℚ) := by exact_mod_cast h
  have hX : restX r a = ((2 * ((r * a) + (r + a)) : ℕ) : ℚ) := by
    simp only [restX]; push_cast; ring
  rw [div_le_div_iff₀ (by positivity) (by positivity), hX]
  push_cast at hq ⊢
  linarith

theorem SameFactorBound.proof (hF : SameFactorFormula.Statement) (hS : SchurSignCoefficient.Statement)
    (hB : CharacterBound.Statement) (hH : HookSumBound.Statement)
    (hR : RectangleTablePos.Statement) (hD : RestPolynomialDecomposes.Statement) :
    SameFactorBound.Statement := by
  intro f r a c hf hr ha
  obtain ⟨C₀, hC₀, hJ, hT⟩ := hF f r a c hf hr ha
  have hfR : (0 : ℚ) < numStandardTable (rectangle r a) := by exact_mod_cast hR r a
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hJabs : |fibreDegree (f' + 1) r a c| =
      |C₀| * (((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1)) := by
    have hJp : (0 : ℚ) ≤ ((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1) := by positivity
    rw [hJ, ← abs_of_nonneg hJp, ← abs_mul]
    congr 1
    ring
  refine ⟨?_, hD (f' + 1) r a c, ?_⟩
  · rw [hJ]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero hC₀ (by positivity)) (by positivity))
      (pow_ne_zero _ hfR.ne')
  intro Q hQ k hk2 hkN τ
  obtain ⟨S, hSP, hTk⟩ := hT Q hQ k hk2 hkN τ
  have hk1 : 1 ≤ k := by omega
  set s : ℚ := c.sign with hs_def
  have hs : s = 1 ∨ s = -1 := by cases c <;> simp [hs_def, SmallBlock.sign]
  have hsk : |s ^ k| = 1 := by rcases hs with h | h <;> simp [h]
  have hmem : ∀ nu ∈ partitionsOf r k, Antitone nu ∧ ∑ i, nu i = k := by
    intro nu hnu
    simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hnu
    exact ⟨fun i j hij => hnu.2 i j hij, hnu.1⟩
  set chi : (Fin r → ℕ) → ℚ := fun nu =>
    symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1)
    with hchi
  have hex := fun nu (hnu : nu ∈ partitionsOf r k) =>
    hS (r + a) r k hk1 hkN nu s hs (hmem nu hnu).1 (hmem nu hnu).2
  choose! Sν hSν1 hSν2 using hex

  have hSeq : S = ∑ nu ∈ partitionsOf r k, C (chi nu) * Sν nu := by
    apply Flag.powerSumHom_injective

    rw [hSP, map_sum]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [map_mul, hSν1 nu hnu]
    congr 1
    simp [powerSumHom, hchi]
  set e : Fin (r + a) →₀ ℕ := Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1 with he
  have hcoef : |S.coeff e| ≤
      (∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
        |chi nu|) / k := by
    rw [hSeq, coeff_sum]
    simp only [coeff_C_mul]
    calc |∑ nu ∈ partitionsOf r k, chi nu * (Sν nu).coeff e|
        ≤ ∑ nu ∈ partitionsOf r k, |chi nu * (Sν nu).coeff e| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ nu ∈ partitionsOf r k,
            if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then |chi nu| / k else 0 := by
          refine Finset.sum_congr rfl fun nu hnu => ?_
          rw [hSν2 nu hnu]
          split_ifs
          · rw [abs_mul, abs_mul, hsk, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
            ring
          · simp
      _ = _ := by rw [Finset.sum_div, Finset.sum_filter]
  have hhook := hH r a k chi hk1 (fun nu hnu => hB r _ _
    (fun i j hij => Nat.add_le_add_left ((hmem nu hnu).1 hij) a)
    (fun q hq => by
      simp only [List.mem_cons, List.mem_replicate] at hq
      omega))

  set K : ℚ := k * ((f' + 1) * (r * a) + 1).factorial /
      (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f' + 1 - 1)) *
      (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1 - 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hTabs : |restTerm (f' + 1) (r + a) Q k τ (smallPowerSum (f' + 1) r a c (k - 1) τ)| =
      |C₀| * K * |S.coeff e| := by
    rw [hTk, show ∀ x : ℚ, C₀ * k * ((f' + 1) * (r * a) + 1).factorial /
        (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f' + 1 - 1)) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1 - 1) * x = C₀ * K * x from
        fun x => by rw [hK]; ring, abs_mul, abs_mul, abs_of_nonneg hK0]
  rw [hTabs, hJabs]
  set B : ℚ := (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) *
    numStandardTable (rectangle r a) with hBdef
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcoefB : |S.coeff e| ≤ B / k := le_trans hcoef (div_le_div_of_nonneg_right hhook hk0.le)
  have hKB : K * (B / k) = ((f' + 1) * (r * a) + 1 : ℕ) *
      ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) *
      ((Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ)) := by
    rw [hK, hBdef, Nat.add_sub_cancel, Nat.factorial_succ, Nat.factorial_succ (r * a)]
    have : ((r * a).factorial : ℚ) ≠ 0 := by positivity
    have : (((f' + 1) * (r * a)).factorial : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  have hP : (0 : ℚ) ≤ ((f' + 1) * (r * a) + 1 : ℕ) *
      ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) := by positivity
  calc |C₀| * K * |S.coeff e| ≤ |C₀| * K * (B / k) :=
        mul_le_mul_of_nonneg_left hcoefB (by positivity)
    _ = |C₀| * (((f' + 1) * (r * a) + 1 : ℕ) *
          ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
            (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) *
          ((Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ))) := by
        rw [mul_assoc, hKB]
    _ ≤ |C₀| * (((f' + 1) * (r * a) + 1 : ℕ) *
          ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
            (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) *
          (restX r a ^ (k - 1) / (k.factorial : ℚ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (sameFactor_choose_le r a k hk1 hkN) hP) (abs_nonneg _)
    _ = _ := by ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section


open Coinv in
theorem CoinvIdealRepresentation.proof : CoinvIdealRepresentation.Statement := by
  intro K _ f n J hJ
  induction hJ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m₀, b₀, h1, h2, rfl⟩ := hx
    refine ⟨fun m b => if m = m₀ ∧ b = b₀ then 1 else 0, ?_⟩
    have hm₀ : m₀ ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨h1, h2⟩
    symm
    rw [Finset.sum_eq_single m₀]
    · rw [Finset.sum_eq_single b₀]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ b₀) h
    · intro m _ hm
      apply Finset.sum_eq_zero
      intro b _
      simp [hm]
    · intro h
      exact absurd hm₀ h
  | zero =>
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := hy
    refine ⟨a + a', ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  | smul r x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨fun m b => r * a m b, ?_⟩
    simp only [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun b _ => ?_
    ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem Coinv.bps_isHomogeneous (K : Type) [Field K] (f n m : ℕ) (b : Fin f) :
    (bps K f n m b).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_X_pow _ _

theorem CoinvIdealComponent.proof (h1 : CoinvIdealRepresentation.Statement)
    (h2 : HomogeneousComponentMul.Statement) : CoinvIdealComponent.Statement := by
  intro K _ f n J hJ d
  obtain ⟨a, rfl⟩ := h1 K f n J hJ
  refine ⟨fun m b => if m ≤ d then homogeneousComponent (d - m) (a m b) else 0, ?_, ?_⟩
  · intro m b
    dsimp only
    split_ifs
    · exact homogeneousComponent_isHomogeneous _ _
    · exact isHomogeneous_zero _ _ _
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h2 (Fin f × Fin n) K (bps K f n m b) (a m b) m d (bps_isHomogeneous K f n m b)]
    by_cases hmd : m ≤ d <;> simp [hmd]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem RestBound.proof (h₁ : RestPrimeBound.Statement) (h₂ : RestBoundOfPrimeBound.Statement) :
    RestBound.Statement := by
  intro f r a c B₀ hf hr ha hB
  refine ⟨(h₁ f r a c B₀ hf hr ha hB).1, ?_⟩
  intro Q hQ s e he P
  exact h₂ f r a c B₀ hf hr ha hB Q s e
    (fun p hp hpB => (h₁ f r a c B₀ hf hr ha hB).2 Q hQ s e he p hp hpB) P

end RestTerms

end GroundTheory.Heights₂.Heights
end
