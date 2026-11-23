module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle166
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle164
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe

@[expose] public section

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem hilbert90_locallyConstant_cocycle :
    ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : (Ω ≃ₐ[K] Ω) → Ωˣ),
      IsLocallyConstant w → (∀ g h, ((w (g * h) : Ωˣ) : Ω) = w g * g (w h)) →
        ∃ t : Ωˣ, ∀ g, ((w g : Ωˣ) : Ω) = g t / t := by
  intro K Ω _ _ _ _ _ w hw hc
  have h1 : w 1 = 1 := by
    apply Units.ext
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    have h' : ((w 1 : Ωˣ) : Ω) * 1 = (w 1 : Ω) * (w 1 : Ω) := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ (w 1).ne_zero h').symm
  have hopen : IsOpen (w ⁻¹' {1}) := hw _
  obtain ⟨E, hfin, hE⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 (hopen.mem_nhds (by simp [h1]))
  haveI := hfin
  obtain ⟨β, hβ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_units_of_cocycle (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) (fun h => w h.1) E
    (fun h hh => hE hh) (fun g h => Units.ext (by simp [hc]))
  refine ⟨β, fun g => ?_⟩
  have := congrArg Units.val (hβ ⟨g, Subgroup.mem_top g⟩)
  simpa [div_eq_mul_inv] using this

end GlobalTheory
end

section

open Complex Filter Topology

namespace GlobalTheory.DivConvSum

theorem norm_divisorSum_le (k n : ℕ) (ψ θ : ℕ → ℂ) (h : ∀ n, ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) :
    ‖∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ k * θ p.2‖
      ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ k := by
  have hc : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  refine (norm_sum_le _ _).trans ?_
  rw [← hc, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
  have hle : p.1 ≤ n := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
  have hle' : (p.1 : ℝ) ^ k ≤ (n : ℝ) ^ k :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) k
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  have h1 := (h p.1).1
  have h2 := (h p.2).2
  have h0 : (0 : ℝ) ≤ (p.1 : ℝ) ^ k := by positivity
  calc ‖ψ p.1‖ * (p.1 : ℝ) ^ k * ‖θ p.2‖ ≤ 1 * (p.1 : ℝ) ^ k * 1 := by
        gcongr
    _ ≤ (n : ℝ) ^ k := by simpa using hle'

theorem lSeriesSummable_mul_divisorSum :
    ∀ (e : ℕ) (ψ θ g b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n : ℕ => g n * b n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  intro e ψ θ g b s he hs hψ hg hb
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have h1 := hg s hs
  have h2 := GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow s hs
  refine Summable.of_norm_bounded (h1.add h2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hbn : ‖b n‖ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ k := by
      rw [hb n hn, Nat.add_sub_cancel]
      exact norm_divisorSum_le k n ψ θ hψ
    have e1 : (n : ℝ) ^ (2 * ((k + 1 : ℕ) : ℝ) + s)
        = ((n : ℝ) ^ k * n) ^ 2 * (n : ℝ) ^ s := by
      rw [Real.rpow_add hN, show (2 * ((k + 1 : ℕ) : ℝ)) = ((2 * (k + 1) : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
      ring
    have e2 : (n : ℝ) ^ (((2 * (k + 1) + 1 : ℕ) : ℝ) + s)
        = ((n : ℝ) ^ k * n) ^ 2 * (n * (n : ℝ) ^ s) := by
      rw [Real.rpow_add hN, Real.rpow_natCast]
      ring
    have e3 : (n : ℝ) ^ (1 + s) = n * (n : ℝ) ^ s := by
      rw [Real.rpow_add hN, Real.rpow_one]
    rw [Complex.ofReal_re, norm_mul, e1, e2, e3]
    have hu : (0 : ℝ) < (n : ℝ) ^ s := Real.rpow_pos_of_pos hN s
    have hP : (0 : ℝ) < (n : ℝ) ^ k := by positivity
    generalize (n : ℝ) ^ s = u at *
    generalize (n : ℝ) ^ k = P at *
    generalize (n.divisors.card : ℝ) = d at *
    have hG : 0 ≤ ‖g n‖ := norm_nonneg _
    generalize ‖g n‖ = G at *
    generalize (n : ℝ) = N at *
    calc G * ‖b n‖ / ((P * N) ^ 2 * u) ≤ G * (d * P) / ((P * N) ^ 2 * u) := by gcongr
      _ = (G / (P * N) * d) / (N * u) := by field_simp
      _ ≤ ((G / (P * N)) ^ 2 + d ^ 2) / (N * u) := by
          gcongr
          nlinarith [sq_nonneg (G / (P * N) - d), sq_nonneg (G / (P * N)), sq_nonneg d]
      _ = G ^ 2 / ((P * N) ^ 2 * (N * u)) + d ^ 2 / (N * u) := by field_simp

end GlobalTheory.DivConvSum
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.j_invariant_equal_sl2_orbit : ∀ τ σ : ℍ, E₄ τ ^ 3 * E₆ σ ^ 2 = E₆ τ ^ 2 * E₄ σ ^ 3 → ∃ γ : SL(2, ℤ), τ = γ • σ := by
  first | exact @GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ | exact GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ | (intros; apply GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ <;> assumption)
end
