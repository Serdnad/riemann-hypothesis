module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.AffineMonoid.Basic
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001

@[expose] public section

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.Segment

private theorem two_mul_triangle_add_mul_eq (d l₀ l₁ : ℕ) (h₀ : 1 ≤ l₀) (h₁ : 1 ≤ l₁) :
    2 * (d * (l₀ * l₁ + l₀ * (l₀ - 1) / 2)) * (l₀ + l₁) =
      2 * (d * ((l₀ + l₁) * (l₀ + l₁ - 1) / 2)) * l₀ + d * ((l₀ + l₁) * l₀ * l₁) := by
  obtain ⟨a, rfl⟩ : ∃ a, l₀ = a + 1 := ⟨l₀ - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, l₁ = b + 1 := ⟨l₁ - 1, by omega⟩
  rw [show a + 1 + (b + 1) = a + b + 1 + 1 by ring, Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hp : 2 * ((a + 1) * a / 2) = (a + 1) * a :=
    Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self a)
  have hq : 2 * ((a + b + 1 + 1) * (a + b + 1) / 2) = (a + b + 1 + 1) * (a + b + 1) :=
    Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self (a + b + 1))
  generalize (a + 1) * a / 2 = p at hp ⊢
  generalize (a + b + 1 + 1) * (a + b + 1) / 2 = q at hq ⊢
  zify at hp hq ⊢
  linear_combination ((d : ℤ) * (a + b + 1 + 1)) * hp - ((d : ℤ) * (a + 1)) * hq

theorem top_piece_exponent_lt_one : ∀ (α r : ℝ) (d l0 l1 : ℕ), 0 < α → α < 1 → 0 < r → 1 ≤ d → 1 ≤ l0 → 1 ≤ l1 →
    r ^ (l0 + l1) * α ^ (d * ((l0 + l1) * (l0 + l1 - 1) / 2)) = 1 →
    r ^ l0 * α ^ (d * (l0 * l1 + l0 * (l0 - 1) / 2)) < 1 := by
  intro α r d l0 l1 hα0 hα1 hr hd hl0 hl1 h
  have key := two_mul_triangle_add_mul_eq d l0 l1 hl0 hl1
  set T := (l0 + l1) * (l0 + l1 - 1) / 2
  set S := l0 * l1 + l0 * (l0 - 1) / 2
  have hpow : (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1)) = α ^ (d * ((l0 + l1) * l0 * l1)) := by
    calc (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1))
        = (r ^ (l0 + l1)) ^ (2 * l0) * α ^ (2 * (d * S) * (l0 + l1)) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 2 <;> ring
      _ = (r ^ (l0 + l1) * α ^ (d * T)) ^ (2 * l0) * α ^ (d * ((l0 + l1) * l0 * l1)) := by
          rw [key, pow_add α, mul_pow (r ^ (l0 + l1)), ← pow_mul α (d * T),
            show d * T * (2 * l0) = 2 * (d * T) * l0 by ring, ← mul_assoc ((r ^ (l0 + l1)) ^ (2 * l0))]
      _ = α ^ (d * ((l0 + l1) * l0 * l1)) := by rw [h, one_pow, one_mul]
  have hlt : α ^ (d * ((l0 + l1) * l0 * l1)) < 1 :=
    pow_lt_one₀ hα0.le hα1
      (Nat.mul_pos (by omega) (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))).ne'
  by_contra hc
  push_neg at hc
  have h1 : 1 ≤ (r ^ l0 * α ^ (d * S)) ^ (2 * (l0 + l1)) := one_le_pow₀ hc
  rw [hpow] at h1
  exact absurd hlt (not_lt.mpr h1)

end GlobalTheory.CompanionTheory.Segment
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.LocalFieldPow


open ValuativeRel in
theorem exists_unit_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∃ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) := by
  intro k _ _ _ _
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)
  have hr : r ≠ 0 := by simpa using hr0
  have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  refine ⟨Units.mk0 r hr, ?_⟩
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hr1 (Units.mk0 γ hγ)
  rw [Units.val_mk0] at hm
  filter_upwards [eventually_ge_atTop m] with n hn
  have h : ValuativeRel.valuation k ((Units.mk0 r hr : kˣ) : k) ^ n ≤ ValuativeRel.valuation k r ^ m := by
    simpa using pow_le_pow_of_le_one zero_le' hr1.le hn
  simpa using lt_of_le_of_lt h hm

end GlobalTheory.CompanionTheory.LocalFieldPow
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.Val

theorem valuation_lt_one_of_tendsto_pow_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      ∀ t : kˣ, Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) →
        ValuativeRel.valuation k (t : k) < 1 := by
  intro k _ _ _ _ t ht
  by_contra hge
  have hge' : 1 ≤ ValuativeRel.valuation k (t : k) := not_lt.mp hge
  have hU : {x : k | ValuativeRel.valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem one_ne_zero
  obtain ⟨n, hn⟩ := (ht.eventually hU).exists
  have hn' : ValuativeRel.valuation k ((t : k) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact absurd hn' (not_lt.mpr (one_le_pow₀ hge'))

end GlobalTheory.CompanionTheory.Val
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.DeligneRibet

theorem absNorm_not_dvd_of_sup_span_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ), l.Prime → ∀ 𝔟 : Ideal (𝓞 F),
      𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤ → ¬ l ∣ Ideal.absNorm 𝔟 := by
  intro F _ _ l hl 𝔟 h hdvd
  have h1 : (1 : 𝓞 F) ∈ 𝔟 ⊔ Ideal.span {(l : 𝓞 F)} := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  by_cases h𝔟 : 𝔟 = ⊥
  · subst h𝔟
    rw [bot_sup_eq] at h
    have hnorm := Ideal.absNorm_span_singleton (l : 𝓞 F)
    rw [h, Ideal.absNorm_top] at hnorm
    have hcast : (l : 𝓞 F) = algebraMap ℤ (𝓞 F) (l : ℤ) := by simp
    rw [hcast, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hnorm
    have hpos : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    rcases Nat.pow_eq_one.mp hnorm.symm with h' | h'
    · exact hl.one_lt.ne' h'
    · omega
  · haveI := Ideal.finiteQuotientOfFreeOfNeBot 𝔟 h𝔟
    haveI := Fact.mk hl
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hdvd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hdvd
    have hlx : (l : 𝓞 F ⧸ 𝔟) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have hunit : Ideal.Quotient.mk 𝔟 a * (l : 𝓞 F ⧸ 𝔟) = 1 := by
      have key := congrArg (Ideal.Quotient.mk 𝔟) hbc
      rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_add, map_mul, map_natCast,
        map_one] at key
      exact key
    have hx0 : x = 0 := by
      rw [← one_mul x, ← hunit, mul_assoc, hlx, mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hl.one_lt.ne hx

end GlobalTheory.CompanionTheory.DeligneRibet
end

section

open UpperHalfPlane CongruenceSubgroup Ad3

namespace GlobalTheory.CompanionTheory.HeckeSum

theorem sum_root (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ∑ b ∈ Finset.range p, Complex.exp (-(2 * Real.pi * Complex.I * n * b / p)) =
      if p ∣ n then (p : ℂ) else 0 := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / p)) p :=
    Complex.isPrimitiveRoot_exp p hp.ne_zero
  set ζ : ℂ := (Complex.exp (2 * Real.pi * Complex.I / p))⁻¹ ^ n with hζ
  have hterm : ∀ b ∈ Finset.range p,
      Complex.exp (-(2 * Real.pi * Complex.I * n * b / p)) = ζ ^ b := by
    intro b _
    rw [hζ, ← Complex.exp_neg, ← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  have hζp : ζ ^ p = 1 := by
    rw [hζ, ← pow_mul, mul_comm n p, pow_mul, hprim.inv.pow_eq_one, one_pow]
  split_ifs with h
  · have h1 : ζ = 1 := by
      rw [hζ]
      exact (hprim.inv.pow_eq_one_iff_dvd n).mpr h
    simp [h1]
  · have h1 : ζ ≠ 1 := by
      rw [hζ]
      intro h1
      exact h ((hprim.inv.pow_eq_one_iff_dvd n).mp h1)
    rw [geom_sum_eq h1, hζp, sub_self, zero_div]

theorem hecke_sum (k N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) (k : ℤ)) (a : ℕ → ℂ) (hf : IsForm k N χ f a)
    (he : IsEig k N χ a) (p : ℕ) (hp : p.Prime) (z : ℍ) (w : ℕ → ℍ)
    (hw : ∀ b : ℕ, (w b : ℂ) = ((z : ℂ) - b) / p) (w' : ℍ) (hw' : (w' : ℂ) = p * z) :
    ∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b) =
      p * (a p * f z - χ p * (p : ℂ) ^ (k - 1) * f w') := by
  have hterm : ∀ n : ℕ, ∑ b ∈ Finset.range p,
      a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((w b : ℍ) : ℂ)) =
      if p ∣ n then (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p))
      else 0 := by
    intro n
    have hsplit : ∀ b : ℕ,
        a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((w b : ℍ) : ℂ)) =
        a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p) *
          Complex.exp (-(2 * Real.pi * Complex.I * n * b / p)) := by
      intro b
      rw [hw b, mul_assoc (a n), ← Complex.exp_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl fun b _ => hsplit b, ← Finset.mul_sum, sum_root p hp n]
    split_ifs <;> ring
  have hL : HasSum (fun n : ℕ => if p ∣ n then
      (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p)) else 0)
      (∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b)) := by
    have h := hasSum_sum fun b (_ : b ∈ Finset.range p) => hf.exp (w b)
    convert h using 1
    funext n
    exact (hterm n).symm
  have hinj : Function.Injective (fun m : ℕ => p * m) := fun x y h =>
    Nat.eq_of_mul_eq_mul_left hp.pos h
  have hLm : HasSum (fun m : ℕ => (p : ℂ) *
      (a (p * m) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))))
      (∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b)) := by
    have h1 := (hinj.hasSum_iff (f := fun n : ℕ => if p ∣ n then
      (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p)) else 0)
      (a := ∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b)) ?_).mpr hL
    · convert h1 using 1
      funext m
      simp only [Function.comp_apply]
      rw [if_pos (dvd_mul_right p m)]
      congr 3
      rw [eq_div_iff (Nat.cast_ne_zero.mpr hp.ne_zero)]
      push_cast
      ring
    · intro x hx
      rw [if_neg]
      rintro ⟨m, rfl⟩
      exact hx ⟨m, rfl⟩
  have h2 : HasSum ((fun m : ℕ => if p ∣ m then
      a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0) ∘
      (fun n : ℕ => p * n)) ((f : ℍ → ℂ) w') := by
    convert hf.exp w' using 1
    funext n
    simp only [Function.comp_apply]
    rw [if_pos (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos, hw']
    congr 2
    push_cast
    ring
  have hw's : HasSum (fun m : ℕ => if p ∣ m then
      a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0)
      ((f : ℍ → ℂ) w') := by
    refine (hinj.hasSum_iff ?_).mp h2
    intro x hx
    rw [if_neg]
    rintro ⟨m, rfl⟩
    exact hx ⟨m, rfl⟩
  have hR := ((hf.exp z).mul_left (a p)).sub (hw's.mul_left (χ p * (p : ℂ) ^ (k - 1)))
  have key : ∀ m : ℕ, a p * (a m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) - χ p * (p : ℂ) ^ (k - 1) *
      (if p ∣ m then a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0) = a (p * m) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) := by
    intro m
    have h := he.2.2 p m hp
    by_cases hm : p ∣ m
    · rw [if_pos hm] at h ⊢
      linear_combination (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) * h
    · rw [if_neg hm] at h ⊢
      linear_combination (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) * h
  simp only [key] at hR
  exact hLm.unique (hR.mul_left (p : ℂ))

end GlobalTheory.CompanionTheory.HeckeSum
end
