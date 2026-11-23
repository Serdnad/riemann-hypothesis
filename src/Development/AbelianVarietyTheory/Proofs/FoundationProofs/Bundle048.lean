module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle019
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

section


theorem _root_.GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_charZero : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) (m : ℕ), 1 ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → A.valuation (ζ - 1) ^ Nat.totient (l ^ m) = A.valuation (l : Ω) := by
  first | exact @GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient | exact GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient | (intros; apply GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem valuation_eq_one_of_pow_eq_span :
    ∀ (E Ω R : Type) [Field E] [Field Ω] [Algebra E Ω] [CommRing R] [Algebra R E] (B : ValuationSubring Ω)
      (J : Submodule R E) (N : ℕ), 0 < N → (∀ x : R, algebraMap E Ω (algebraMap R E x) ∈ B) → ∀ w : E, w ≠ 0 →
      (J ^ N = Submodule.span R {w}) → ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / c ^ N)) = 1 := by
  intro E Ω R _ _ _ _ _ B J N hN hRB w hw hJ
  set v := B.valuation.comap (algebraMap E Ω) with hv
  have hva : ∀ x, v x = B.valuation (algebraMap E Ω x) := fun x => rfl
  have hR : ∀ r : R, v (algebraMap R E r) ≤ 1 := fun r => by
    rw [hva]; exact (B.valuation_le_one_iff _).mpr (hRB r)
  have hsm : ∀ (r : R) (z : E), v (r • z) ≤ v z := fun r z => by
    rw [Algebra.smul_def, v.map_mul]
    calc v (algebraMap R E r) * v z ≤ 1 * v z := mul_le_mul' (hR r) le_rfl
      _ = v z := one_mul _
  let S : ℕ → Submodule R E := fun n =>
    { carrier := {z | ∃ c ∈ J, v z ≤ v c ^ (n + 1)}
      zero_mem' := ⟨0, J.zero_mem, by simp⟩
      add_mem' := by
        rintro z₁ z₂ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
        rcases le_total (v c₁) (v c₂) with h | h
        · refine ⟨c₂, hc₂, (v.map_add z₁ z₂).trans (max_le ?_ h₂)⟩
          exact h₁.trans (pow_le_pow_left₀ zero_le' h _)
        · refine ⟨c₁, hc₁, (v.map_add z₁ z₂).trans (max_le h₁ ?_)⟩
          exact h₂.trans (pow_le_pow_left₀ zero_le' h _)
      smul_mem' := by
        rintro r z ⟨c, hc, h⟩
        exact ⟨c, hc, (hsm r z).trans h⟩ }
  have key : ∀ n : ℕ, J ^ (n + 1) ≤ S n := by
    intro n
    induction n with
    | zero =>
      intro z hz
      rw [pow_one] at hz
      exact ⟨z, hz, by simp⟩
    | succ n ih =>
      rw [pow_succ]
      refine Submodule.mul_le.mpr ?_
      intro y hy z' hz'
      obtain ⟨c, hc, h⟩ := ih hy
      show ∃ c ∈ J, v (y * z') ≤ v c ^ (n + 1 + 1)
      rw [v.map_mul]
      rcases le_total (v c) (v z') with h' | h'
      · refine ⟨z', hz', ?_⟩
        rw [pow_succ]
        exact mul_le_mul' (h.trans (pow_le_pow_left₀ zero_le' h' _)) le_rfl
      · refine ⟨c, hc, ?_⟩
        rw [pow_succ]
        exact mul_le_mul' h h'
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hwmem : w ∈ J ^ (n + 1) := by rw [hJ]; exact Submodule.mem_span_singleton_self w
  obtain ⟨c, hc, hle⟩ := key n hwmem
  have hcN : c ^ (n + 1) ∈ Submodule.span R {w} := hJ ▸ Submodule.pow_mem_pow J hc (n + 1)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hcN
  have hge : v (c ^ (n + 1)) ≤ v w := by
    rw [← hr]; exact hsm r w
  have heq : v (c ^ (n + 1)) = v w := le_antisymm hge (by rw [v.map_pow]; exact hle)
  have hw0 : v w ≠ 0 := by
    rw [hva]; exact (Valuation.ne_zero_iff _).mpr ((_root_.map_ne_zero _).mpr hw)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hw0
    rw [← heq]; simp
  refine ⟨c, hc0, ?_⟩
  have : v (w / c ^ (n + 1)) = 1 := by
    rw [map_div₀, heq, div_self hw0]
  simpa [hva] using this

end GlobalTheory
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem isIntegral_int_mem_every_valuationSubring {F : Type} [Field F] (V : ValuationSubring F)
    {y : F} (hy : IsIntegral ℤ y) : y ∈ V := by
  have hV : IsIntegral V y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hV
  rw [← hz]
  exact z.2

theorem valuationSubring_valuation_intCast_coprime_eq_one {F : Type} [Field F] (V : ValuationSubring F)
    {q : ℕ} (hq : ((q : ℕ) : F) ∈ V.nonunits) {n : ℤ} (hn : IsCoprime n (q : ℤ)) :
    V.valuation (n : F) = 1 := by
  obtain ⟨a, b, hab⟩ := hn
  have hint : ∀ m : ℤ, V.valuation (m : F) ≤ 1 := fun m =>
    (V.valuation_le_one_iff _).2 (by simp)
  have hq' : V.valuation ((q : ℕ) : F) < 1 := V.mem_nonunits_iff.1 hq
  refine le_antisymm (hint n) (not_lt.1 fun hlt => ?_)
  have hsum : ((a : F) * n + (b : F) * ((q : ℕ) : F)) = 1 := by
    have := congrArg (fun t : ℤ => (t : F)) hab
    simpa using this
  have h1 : V.valuation ((a : F) * n) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hlt
  have h2 : V.valuation ((b : F) * ((q : ℕ) : F)) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) hq'
  have h3 := Valuation.map_add_lt _ h1 h2
  rw [hsum, map_one] at h3
  exact lt_irrefl _ h3

theorem exists_finset_primes_forall_mem_valuationSubring :
    ∀ {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (s : Finset F),
      ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F,
        ((q : ℕ) : F) ∈ V.nonunits → ∀ x ∈ s, x ∈ V := by
  intro F _ _ _ s
  have : Algebra.IsAlgebraic ℤ F :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  obtain ⟨d, hd0, hd⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  refine ⟨d.natAbs.primeFactors, fun q hq hqS V hqV x hx => ?_⟩
  have hndvd : ¬ q ∣ d.natAbs := fun h =>
    hqS (Nat.mem_primeFactors.2 ⟨hq, h, Int.natAbs_ne_zero.2 hd0⟩)
  have hcop : IsCoprime d (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := (Nat.Prime.coprime_iff_not_dvd hq).2 hndvd
    simpa [Int.gcd, Nat.Coprime, Nat.gcd_comm] using this
  have hdx : (d : F) * x ∈ V := by
    have := isIntegral_int_mem_every_valuationSubring V (hd x hx)
    simpa [zsmul_eq_mul] using this
  have hv1 := valuationSubring_valuation_intCast_coprime_eq_one V hqV hcop
  rw [← V.valuation_le_one_iff]
  have := (V.valuation_le_one_iff _).2 hdx
  rwa [map_mul, hv1, one_mul] at this

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.coeff_mem_of_sum_mul_pow_mem_of_valuation_zpow : ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (N : ℕ) (π ℓ : Ω) (c : ℕ → Ω), 0 < N → ℓ ≠ 0 → A.valuation ℓ < 1 → A.valuation π ^ N = A.valuation ℓ → (∀ i < N, c i ≠ 0 → ∃ k : ℤ, A.valuation (c i) = A.valuation ℓ ^ k) → (∑ i ∈ Finset.range N, c i * π ^ i) ∈ A → ∀ i < N, c i ∈ A := by
  first | exact @GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow | exact GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow | (intros; apply GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow <;> assumption)
end
