module

public import Formalism.QuotientMetricDivisors.Bundle004
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle002
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace DualLatticeDivisor

variable {K : Type} [Field K] [NumberField K]

theorem mem_range_of_vw_nonneg (a : K) (ha : a ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) :
    a ∈ Set.range (algebraMap (𝓞 K) K) := by
  classical
  set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact ha
  have key : ∃ J : Ideal (𝓞 K), (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (FractionalIdeal.count K v I) := by
    refine finprod_induction
      (fun X : FractionalIdeal (nonZeroDivisors (𝓞 K)) K =>
        ∃ J : Ideal (𝓞 K), (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = X)
      ⟨1, by simp⟩ ?_ ?_
    · rintro x y ⟨J1, h1⟩ ⟨J2, h2⟩
      exact ⟨J1 * J2, by rw [FractionalIdeal.coeIdeal_mul, h1, h2]⟩
    · intro v
      have hv : 0 ≤ FractionalIdeal.count K v I := h v
      refine ⟨v.asIdeal ^ (FractionalIdeal.count K v I).toNat, ?_⟩
      rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast, Int.toNat_of_nonneg hv]
  rw [FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI] at key
  obtain ⟨J, hJ⟩ := key
  have hmem : a ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [hJ, hIdef]
    exact FractionalIdeal.mem_spanSingleton_self _ a
  obtain ⟨y, -, hy⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
  exact ⟨y, hy⟩

end DualLatticeDivisor

theorem divisor_into_dual_lattice : DivIntoDual := by
  intro K _ _ _ D R B n M π ι P ζ hζ hvζ hP hM hloc x hx
  by_cases hBx : B x = 0
  · rw [hBx]; exact ⟨0, map_zero _⟩
  · apply DualLatticeDivisor.mem_range_of_vw_nonneg _ hBx
    intro w
    have hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R :=
      ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hx⟩
    rw [hloc w] at hxl
    rcases reduction_first_step K w (n w) D (M w) (π w) (ι w) B (P w) (ζ w) 0 (hζ w) (hvζ w) (hP w) (hM w) x
      hxl with h | h
    · exact absurd h hBx
    · exact h

end Formalism.DivisionValues
end
end

section

open Module NumberField IsDedekindDomain Finset

noncomputable section

namespace Formalism.DivisionValues

namespace PlaceSumConjugation

section Places

variable {K : Type} [Field K] [NumberField K]

theorem vw_nat_nonneg (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ vw w (g : K) := by
  unfold vw
  have h : (g : K) = algebraMap (𝓞 K) K (g : 𝓞 K) := by simp
  rw [h, ← FractionalIdeal.coeIdeal_span_singleton]
  apply FractionalIdeal.count_coe_nonneg

theorem lw_pos (w : HeightOneSpectrum (𝓞 K)) : 0 < lw w := by
  unfold lw
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
  have h2 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
    exact_mod_cast (by omega : 1 < Ideal.absNorm w.asIdeal)
  apply div_pos (Real.log_pos h2)
  exact_mod_cast Module.finrank_pos

theorem plOver_mem {g : ℕ} (hg : 0 < g) (w : HeightOneSpectrum (𝓞 K)) (h : PlOver g w) :
    (g : 𝓞 K) ∈ w.asIdeal := by
  classical
  have hc : ((g : 𝓞 K) : K) = (g : K) := by simp
  have hg0 : (g : 𝓞 K) ≠ 0 := by exact_mod_cast hg.ne'
  have hJ : (Ideal.span {(g : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold PlOver vw at h
  rw [← hc, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ hJ] at h
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors := by
    exact_mod_cast h
  have hm : Associates.mk (Ideal.span {(g : 𝓞 K)}) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h1
  exact h1

end Places

section Star

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_conj_nat (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) :
    vw (conjPl w) (g : K) = vw w (g : K) := by
  rw [← ValuationRepresentative.vw_star, star_natCast]

end Star

end PlaceSumConjugation

open PlaceSumConjugation

theorem places_over_coprime : PlOverCoprime := by
  unfold PlOverCoprime
  intro K _ _ g g' hcop w ⟨h1, h2⟩
  have hpos : ∀ n : ℕ, PlOver n w → 0 < n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      unfold PlOver vw at hn
      first | simp [FractionalIdeal.count_zero] at hn | (unfold FractionalIdeal.count at hn; simp at hn)
    · exact h0
  have m1 := plOver_mem (hpos g h1) w h1
  have m2 := plOver_mem (hpos g' h2) w h2
  have hab : (Nat.gcdA g g') * (g : ℤ) + (Nat.gcdB g g') * (g' : ℤ) = 1 := by
    have := Nat.gcd_eq_gcd_ab g g'
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    push_cast at this
    linarith
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : (1 : 𝓞 K) = ((Nat.gcdA g g' : ℤ) : 𝓞 K) * (g : 𝓞 K) + ((Nat.gcdB g g' : ℤ) : 𝓞 K) * (g' : 𝓞 K) := by
    exact_mod_cast hab.symm
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ m1) (Ideal.mul_mem_left _ _ m2)

end Formalism.DivisionValues
end
end
