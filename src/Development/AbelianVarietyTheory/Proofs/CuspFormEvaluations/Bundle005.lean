module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.BasePointFree

theorem exists_ne_zero_pair (g : ℂ → ℂ) (hg : Differentiable ℂ g) (h1 : g 1 ≠ 0) (m : ℂ)
    (hm : m ≠ 0) : ∃ t : ℂ, g t ≠ 0 ∧ g (-(m * t)) ≠ 0 := by
  by_contra hne
  push Not at hne
  have hg' : Differentiable ℂ (fun t : ℂ => g (-(m * t))) := hg.comp (by fun_prop)
  have A : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have B : AnalyticOnNhd ℂ (fun t : ℂ => g (-(m * t))) Set.univ := fun z _ => hg'.analyticAt z
  have := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero A B (fun z _ => by
    by_cases h : g z = 0
    · simp [h]
    · simp [hne z h]) isPreconnected_univ
  rcases this with h | h
  · exact h1 (h 1 (Set.mem_univ _))
  · have := h (-m⁻¹) (Set.mem_univ _)
    apply h1
    simpa [hm] using this

theorem HC_add_smul_left {ι : Type} [Fintype ι] {n : ℕ} (w c γ : Fin n → EuclideanSpace ℂ ι)
    (a : ℂ) : HC (w + a • c) γ = HC w γ + a * HC c γ := by
  simp only [HC, Hf, Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem prod_translate_mem {E : Type} [Field E] [NumberField E] (X : PT E) {n : ℕ}
    (s : (Fin n → Vsp X.dim) → ℂ) (hs : s ∈ X.Sec 1 n) (m : ℕ) (c : Fin n → Vsp X.dim) :
    (fun w => s (w + (1 : ℂ) • c) ^ m * s (w + (-(m : ℂ)) • c)) ∈ X.Sec (m + 1) n := by
  obtain ⟨hd, hs⟩ := hs
  refine ⟨?_, fun γ hγ v => ?_⟩
  · exact ((hd.comp (by fun_prop)).pow m).mul (hd.comp (by fun_prop))
  · simp only
    rw [add_right_comm v γ, add_right_comm v γ, hs γ hγ, hs γ hγ, HC_add_smul_left,
      HC_add_smul_left, mul_pow, mul_pow, ← Complex.exp_nat_mul]
    have : ((m + 1 : ℕ) : ℂ) * Real.pi * HC v γ + ((m + 1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2 =
        (m : ℂ) * (((1 : ℕ) : ℂ) * Real.pi * (HC v γ + 1 * HC c γ) +
          ((1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2) +
        (((1 : ℕ) : ℂ) * Real.pi * (HC v γ + -(m : ℂ) * HC c γ) +
          ((1 : ℕ) : ℂ) * Real.pi * HC γ γ / 2) := by
      push_cast; ring
    rw [this, Complex.exp_add ((m : ℂ) * _)]
    ring

theorem exists_sec_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ), s ∈ X.Sec 1 1 → s ≠ 0 → ∀ q : ℕ, 2 ≤ q → ∀ v : Fin 1 → Vsp X.dim, ∃ F ∈ X.Sec q 1, F v ≠ 0 := by
  intro E _ _ _ X s hs hs0 q hq v
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hs0
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  obtain ⟨t, h1, h2⟩ := exists_ne_zero_pair (fun t : ℂ => s (v + t • (p - v)))
    (hs.1.comp (by fun_prop)) (by simpa using hp) m hm
  refine ⟨_, prod_translate_mem X s hs m (t • (p - v)), ?_⟩
  refine mul_ne_zero (pow_ne_zero _ (by simpa using h1)) ?_
  rwa [smul_smul, neg_mul]

end GlobalTheory.BasePointFree
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaRunParameters

theorem exists_large_nat (B c₁ c₂ d C : ℝ) (hB : 0 < B) (hd : 0 ≤ d) :
    ∃ q : ℕ, 1 ≤ q ∧ c₁ < q ∧ c₂ ≤ (q : ℝ) / 2 ∧ 1 ≤ (q : ℝ) / B ∧
      4 * (7 + Real.log q) + d + 1 ≤ q * ((q : ℝ) / B) ∧ C ≤ q * ((q : ℝ) / B) := by
  obtain ⟨q, hq⟩ := exists_nat_gt (1 + |c₁| + 2 * |c₂| + B * (33 + d + |C|))
  have h1 := abs_nonneg c₁
  have h2 := abs_nonneg c₂
  have h3 := abs_nonneg C
  have h1' := le_abs_self c₁
  have h2' := le_abs_self c₂
  have h3' := le_abs_self C
  have h4 : 0 ≤ B * (33 + d + |C|) := by positivity
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hK : 33 + d + |C| ≤ (q : ℝ) / B := by
    rw [le_div_iff₀ hB]; linarith
  have hlog : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hm : (q : ℝ) * (33 + d + |C|) ≤ q * ((q : ℝ) / B) :=
    mul_le_mul_of_nonneg_left hK (by linarith)
  have hqd : d ≤ q * d := le_mul_of_one_le_left hd hq1
  have hqC : |C| ≤ q * |C| := le_mul_of_one_le_left h3 hq1
  refine ⟨q, by exact_mod_cast hq1, by linarith, by linarith, by linarith, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem exists_par : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ),
    2 ≤ PT.f E * r → 1 ≤ m → m ^ 4 ≤ PT.f E → (PT.f E : ℝ) ≤ PT.rd E →
    (PT.f E : ℝ) ^ 2 ≤ PT.rd E → 16 ≤ PT.rd E →
    ∃ (q : ℕ) (R0 : ℝ), 0 < th (E := E) q R0 ∧ ∀ X : PT E, X.r = r → (∃ τ, X.dim τ ≤ m) →
      ∃ P : Par X 1, P.q = q ∧ P.R0 = R0 ∧ P.m = m := by
  intro E _ _ _ r m hfr hm1 hmf hfrd hf2 hrd
  have hf : 0 < PT.f E := by
    rcases Nat.eq_zero_or_pos (PT.f E) with h | h
    · rw [h] at hfr; omega
    · exact h
  have hfR : (0 : ℝ) < PT.f E := by exact_mod_cast hf
  have hrd0 : 0 < PT.rd E := by linarith
  have hRR : 0 < RR (E := E) := by unfold RR; positivity
  set S : ℝ := 270 + 90 * (((PT.f E * r : ℕ) : ℝ) + 1) with hS
  have hS0 : 0 < S := by positivity
  have hsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0.le
  have hB : 0 < Real.sqrt S ^ 2 * RR (E := E) ^ 4 := by rw [hsq]; positivity
  have hA : 0 < PT.f E * Real.sqrt S ^ 2 * RR (E := E) ^ 3 := by rw [hsq]; positivity
  obtain ⟨q, hq1, hc1, hc2, hb, h5, h6⟩ := exists_large_nat (Real.sqrt S ^ 2 * RR (E := E) ^ 4)
    ((dstar (E := E) m : ℝ) ^ 2 * omStar (E := E) * (PT.f E * Real.sqrt S ^ 2 * RR (E := E) ^ 3))
    (M1 (E := E) m) (dstar (E := E) m)
    (((PT.f E * r : ℕ) : ℝ) * Real.log 2 + 2 * dstar (E := E) m + 3 +
      (1 + 1) * (r * Real.log r + 3 * r + 3)) hB (Nat.cast_nonneg _)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  refine ⟨q, Real.sqrt S, Real.sqrt_pos.mpr (div_pos hA hq0), ?_⟩
  intro X hX hdim
  subst hX
  refine ⟨⟨q, Real.sqrt S, m, hq1, le_rfl, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, hb, hc2,
    hq1, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rw [hsq, hS]
    unfold PT.gA
    have : (0 : ℝ) ≤ ((PT.f E * X.r : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor
    · linarith
    · rw [Nat.cast_one]; linarith
  · unfold th
    rw [Real.sq_sqrt (div_pos hA hq0).le, ← mul_div_assoc, div_lt_one hq0]
    exact hc1
  · unfold t0 b0
    rw [Nat.cast_one, mul_one, mul_one]
    exact h5
  · unfold t0 b0 PT.gA
    rw [Nat.cast_one]
    exact h6

end GlobalTheory.ThetaRunParameters
end
