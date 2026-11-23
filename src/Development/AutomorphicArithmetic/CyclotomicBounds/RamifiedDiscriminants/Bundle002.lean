module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle002
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle006
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.RamEq
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle005
import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle008
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AutomorphicArithmetic.CMTraceForms.CmDatumDiscriminantDepthBounds
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OrdLeQS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open UpperTheory.HF
open NumberField Formalism.HC

theorem UpperTheory.KR.log_qd_le_rd :
    ∀ {φ : Frame} (H : HostAx φ), H.toHostRaw.PsQ → H.q ∈ H.ram ∧ Real.log H.q + Real.log H.d ≤ 2 * Real.log H.rd ∧ Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd ∧ 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd := by
  intro φ H hP
  have hq : H.q ∈ H.ram := (UpperTheory.HF.inert_q H).2.2.2.2 hP
  obtain ⟨hA, hB, -⟩ := UpperTheory.HF.ram_eq H
  have hd : H.d ∈ H.ram := (hA _).2 (Or.inr (Or.inr rfl))
  have h2 : 2 ∈ H.ram := (Finset.mem_inter.1 hB).2
  obtain ⟨hs, -, -, hrd⟩ := UpperTheory.HF.log_rd_sum H
  have vq : 1 / 2 ≤ H.vdH H.q := (UpperTheory.HF.mem_ram H H.q_prime).2.2.2.1 hq
  have vd : 1 / 2 ≤ H.vdH H.d := (UpperTheory.HF.mem_ram H H.d_prime).2.2.2.1 hd
  have v2 : 11 / 4 ≤ H.vdH 2 := (UpperTheory.HF.vd_two H).2.1
  have n2q : 2 ≠ H.q := fun h => H.q_notMem_small (h ▸ H.two_mem_small)
  have n2d : 2 ≠ H.d := fun h => H.d_notMem_small (h ▸ H.two_mem_small)
  have nqd : H.q ≠ H.d := H.q_ne_d
  have hsub : ({2, H.q, H.d} : Finset ℕ) ⊆ H.ram := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l : ℕ => H.vdH l * Real.log l) hsub
    (fun l _ _ => mul_nonneg (H.vdH_nonneg l) (Real.log_natCast_nonneg l))
  rw [← hs, Finset.sum_insert (by simp [n2q, n2d]), Finset.sum_pair nqd] at hle
  have lq := Real.log_natCast_nonneg H.q
  have ld := Real.log_natCast_nonneg H.d
  have l2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq0 : (0 : ℝ) < H.q := Nat.cast_pos.2 H.q_prime.pos
  have hd0 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  push_cast at hle
  have key : Real.log 2 + (Real.log H.q + Real.log H.d) / 2 ≤ Real.log H.rd := by
    nlinarith [mul_le_mul_of_nonneg_right vq lq, mul_le_mul_of_nonneg_right vd ld,
      mul_le_mul_of_nonneg_right v2 l2.le]
  have hsq : 0 < Real.sqrt ((H.q : ℝ) * H.d) := Real.sqrt_pos.2 (mul_pos hq0 hd0)
  have h4 : 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd := by
    rw [← Real.log_le_log_iff (by positivity) hrd, Real.log_mul two_ne_zero hsq.ne',
      Real.log_sqrt (mul_pos hq0 hd0).le, Real.log_mul hq0.ne' hd0.ne']
    exact key
  exact ⟨hq, by linarith, by linarith, h4⟩
end

section

open NumberField Formalism.HC

theorem UpperTheory.KR.small_vd_sum :
    ∀ {φ : Frame} (H : HostAx φ), (∑ p ∈ H.small, (1 + H.vdH p / 2) * Real.log p ≤ 3 / 2 * Real.logb 2 H.QS) ∧ 2 ∈ H.small ∧
      ∀ r : ℕ, r.Prime → r ∉ H.small → r ≠ H.q → r ≠ H.d → ¬ (r : ℤ) ∣ discr H.E := by
  intro φ H
  obtain ⟨hsm, -, -, -, -⟩ := UpperTheory.cmDatum_discriminantDepth_bounds H
  refine ⟨?_, H.two_mem_small, ?_⟩
  · have hQ0 : H.QS ≠ 0 := H.QS_ne_zero
    have hlogQ : Real.log (H.QS : ℝ) = ∑ p ∈ H.small, (padicValNat p H.QS : ℝ) * Real.log p := by
      show _ = ∑ p ∈ H.QS.primeFactors, (padicValNat p H.QS : ℝ) * Real.log p
      have hprod : (H.QS : ℝ) = ∏ p ∈ H.QS.primeFactors, (p : ℝ) ^ (H.QS.factorization p) := by
        conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hQ0]
        rw [Finsupp.prod, Nat.support_factorization]
        push_cast
        rfl
      rw [hprod, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Real.log_pow, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp),
          ← Nat.padicValNat_def]
      · intro p hp
        exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)
    have hlog2 : Real.log (H.QS : ℝ) ≤ Real.logb 2 H.QS := by
      rw [Real.logb]
      have hl0 : 0 ≤ Real.log (H.QS : ℝ) := Real.log_natCast_nonneg _
      have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h2' : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9
        linarith
      rw [le_div_iff₀ h2]
      nlinarith
    calc ∑ p ∈ H.small, (1 + H.vdH p / 2) * Real.log p
        ≤ ∑ p ∈ H.small, 3 / 2 * ((padicValNat p H.QS : ℝ) * Real.log p) := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpp, hpd⟩ := (H.mem_small_iff).mp hp
          haveI := Fact.mk hpp
          have hv1 : (1 : ℝ) ≤ padicValNat p H.QS := by
            exact_mod_cast (by simpa only [Nat.padicValNat_def] using one_le_padicValNat_of_dvd hQ0 hpd)
          have hvd := (hsm p hp).1
          have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 2 * padicValNat p H.QS - 1 - H.vdH p / 2) hlp]
      _ = 3 / 2 * Real.log H.QS := by rw [hlogQ, Finset.mul_sum]
      _ ≤ 3 / 2 * Real.logb 2 H.QS := by linarith
  · intro r hr hrs hrq hrd hdvd
    have h : r ∣ H.QS * H.q * H.d := (H.der.discr_primes).1 r hr hdvd
    rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
    · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
      · exact hrs ((H.mem_small_iff).mpr ⟨hr, h2⟩)
      · exact hrq ((Nat.prime_dvd_prime_iff_eq hr H.q_prime).mp h2)
    · exact hrd ((Nat.prime_dvd_prime_iff_eq hr H.d_prime).mp h1)
end

section

theorem UpperTheory.Ram.ord_le_totient_QS :
    ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostAx φ), φ.ord ≤ H.QS.totient ∧ 2 * φ.ord ≤ H.QS := by
  intro φ H
  obtain ⟨h1, h2, -⟩ := UpperTheory.KR.two_ord_le_QS H
  exact ⟨h1, h2⟩
end
