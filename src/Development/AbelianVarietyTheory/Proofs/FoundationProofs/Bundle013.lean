module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.LSeries.Convolution
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

open scoped Matrix
open Polynomial

namespace GlobalTheory

theorem one_mem_of_mulClosed_of_det_ne_zero : ∀ {F K : Type} [Field F] [Field K] [Algebra F K]
    [Algebra.IsIntegral F K] {m : ℕ} (S : Submodule F (Matrix (Fin m) (Fin m) K)),
    (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) → ∀ T ∈ S, T.det ≠ 0 → (1 : Matrix (Fin m) (Fin m) K) ∈ S := by
  intro F K _ _ _ _ m S hS T hT hdet
  classical
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).2 (isUnit_iff_ne_zero.2 hdet)
  have hint : IsIntegral F T := by
    have hK : IsIntegral K T := Algebra.IsIntegral.isIntegral T
    exact isIntegral_trans T hK
  have hpow : ∀ n : ℕ, T ^ (n + 1) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hT
    | succ n ih => rw [pow_succ]; exact hS _ ih _ hT
  have hmul : ∀ q : F[X], T * aeval T q ∈ S := by
    intro q
    rw [aeval_eq_sum_range, Finset.mul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_smul_comm, ← pow_succ']
    exact S.smul_mem _ (hpow i)
  set p := minpoly F T with hpdef
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hkey : T * aeval T p.divX + algebraMap F _ (p.coeff 0) = 0 := by
    have h0 : aeval T p = 0 := minpoly.aeval F T
    have e : aeval T p = T * aeval T p.divX + algebraMap F _ (p.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add p, mul_comm p.divX X]
      simp only [map_add (f := _), map_mul, aeval_X, aeval_C]
    rw [← e, h0]
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    rw [hc, map_zero, add_zero] at hkey
    have hq : aeval T p.divX = 0 := by
      exact hTu.mul_right_eq_zero.1 hkey
    have hne : p.divX ≠ 0 := by
      intro h
      rw [divX_eq_zero_iff, hc, map_zero] at h
      exact hp0 h
    have hle := minpoly.degree_le_of_ne_zero F T hne hq
    exact absurd (degree_divX_lt hp0) (not_lt.2 hle)
  have hone : (1 : Matrix (Fin m) (Fin m) K) = (-(p.coeff 0)⁻¹) • (T * aeval T p.divX) := by
    rw [eq_neg_of_add_eq_zero_left hkey, smul_neg, neg_smul, neg_neg, Algebra.smul_def,
      ← map_mul, inv_mul_cancel₀ hc, map_one]
  rw [hone]
  exact S.smul_mem _ (hmul _)

end GlobalTheory
end

section

namespace GlobalTheory.DetZeroFactorization

theorem exists_mul_of_det_zero {K : Type*} [Field K] (a b c d : K) (h : a * d - b * c = 0)
    (hn : ¬ (a = 0 ∧ c = 0)) : ∃ u : K, b = a * u ∧ d = c * u := by
  by_cases ha : a = 0
  · have hc : c ≠ 0 := fun hc => hn ⟨ha, hc⟩
    subst ha
    have hb : b = 0 := by
      have hbc : b * c = 0 := by linear_combination -h
      exact (mul_eq_zero.mp hbc).resolve_right hc
    refine ⟨d / c, by simp [hb], ?_⟩
    field_simp
  · refine ⟨b / a, by field_simp, ?_⟩
    rw [eq_comm, mul_div_assoc', div_eq_iff ha]
    linear_combination -h

theorem main : (let d1 : (q : ℕ) → Option (Fin q) → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℤ := @(fun (q : ℕ) (x : Option (Fin q)) ↦ match x with | Option.none => !![(↑q : ℤ), (0 : ℤ); (0 : ℤ), (1 : ℤ)] | Option.some u => !![(1 : ℤ), (↑(↑u : ℕ) : ℤ); (0 : ℤ), (↑q : ℤ)]); ∀ {q : ℕ}, Nat.Prime q → ∀ (δ : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℤ), Matrix.det δ = (↑q : ℤ) → ∃ (γ : Matrix.SpecialLinearGroup (Fin (2 : ℕ)) ℤ) (y : Option (Fin q)), δ = (↑γ : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℤ) * d1 q y) := by
  intro d1 q hq δ hdet
  have : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hdet' : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = q := by rw [← hdet, Matrix.det_fin_two]
  by_cases hdiv : (q : ℤ) ∣ δ 0 0 ∧ (q : ℤ) ∣ δ 1 0
  ·
    obtain ⟨⟨a', ha'⟩, ⟨c', hc'⟩⟩ := hdiv
    have h1 : a' * δ 1 1 - δ 0 1 * c' = 1 := by
      apply mul_left_cancel₀ hq0
      linear_combination hdet' - δ 1 1 * ha' + δ 0 1 * hc'
    refine ⟨⟨!![a', δ 0 1; c', δ 1 1], by rw [Matrix.det_fin_two_of]; exact h1⟩, none, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d1, Matrix.mul_apply, Fin.sum_univ_two, ha', hc'] <;> ring
  ·
    have h0 : (δ 0 0 : ZMod q) * δ 1 1 - δ 0 1 * δ 1 0 = 0 := by
      have := congrArg (Int.cast : ℤ → ZMod q) hdet'
      push_cast at this
      rw [this, ZMod.natCast_self]
    have hn : ¬ ((δ 0 0 : ZMod q) = 0 ∧ (δ 1 0 : ZMod q) = 0) := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨u, hb, hd⟩ := exists_mul_of_det_zero (δ 0 0 : ZMod q) (δ 0 1) (δ 1 0) (δ 1 1) h0 hn
    obtain ⟨n, hnq, hnu⟩ : ∃ n : ℕ, n < q ∧ (n : ZMod q) = u :=
      ⟨u.val, ZMod.val_lt u, ZMod.natCast_zmod_val u⟩
    obtain ⟨b', hb'⟩ : (q : ℤ) ∣ δ 0 1 - δ 0 0 * (n : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hnu, hb, sub_self]
    obtain ⟨d', hd'⟩ : (q : ℤ) ∣ δ 1 1 - δ 1 0 * (n : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hnu, hd, sub_self]
    have h1 : δ 0 0 * d' - b' * δ 1 0 = 1 := by
      apply mul_left_cancel₀ hq0
      linear_combination hdet' - δ 0 0 * hd' + δ 1 0 * hb'
    refine ⟨⟨!![δ 0 0, b'; δ 1 0, d'], by rw [Matrix.det_fin_two_of]; exact h1⟩,
      some ⟨n, hnq⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d1, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

end GlobalTheory.DetZeroFactorization
end

section

open Complex Filter Topology

namespace GlobalTheory

theorem rankin_convolution_coeff_of_squareSupported (e : ℕ) (χ ψ θ g b z : ℕ → ℂ)
    (hψ : ∀ m n, ψ (m * n) = ψ m * ψ n) (hθ : ∀ m n, θ (m * n) = θ m * θ n)
    (hg : ∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2))
    (hb : ∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2)
    (hz : ∀ a, z a = if Nat.sqrt a * Nat.sqrt a = a then χ (Nat.sqrt a) * ψ (Nat.sqrt a) * θ (Nat.sqrt a) * (Nat.sqrt a : ℂ) ^ (3 * e - 1) else 0)
    (n : ℕ) (hn : n ≠ 0) :
    LSeries.convolution (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (fun n : ℕ => θ n * g n) n
      = LSeries.convolution z (fun n : ℕ => g n * b n) n := by
  simp only [LSeries.convolution_def]
  have hL : ∀ p ∈ n.divisorsAntidiagonal, (ψ p.1 * (p.1:ℂ)^(e-1) * g p.1) * (θ p.2 * g p.2)
      = ∑ δ ∈ (Nat.gcd p.1 p.2).divisors, χ δ * (δ:ℂ)^(2*e) * ψ p.1 * (p.1:ℂ)^(e-1) * θ p.2 * g (n / δ^2) := by
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have h1 : 0 < p.1 := Nat.pos_of_ne_zero (fun h => hn (by rw [← hp.1, h, zero_mul]))
    have h2 : 0 < p.2 := Nat.pos_of_ne_zero (fun h => hn (by rw [← hp.1, h, mul_zero]))
    rw [show (ψ p.1 * (p.1:ℂ)^(e-1) * g p.1) * (θ p.2 * g p.2) = ψ p.1 * (p.1:ℂ)^(e-1) * θ p.2 * (g p.1 * g p.2) by ring, hg _ _ h1 h2, Finset.mul_sum, hp.1]
    exact Finset.sum_congr rfl (fun δ _ => by ring)
  have hR : ∀ p ∈ n.divisorsAntidiagonal, z p.1 * (g p.2 * b p.2)
      = ∑ q ∈ p.2.divisorsAntidiagonal, z p.1 * g p.2 * (ψ q.1 * (q.1:ℂ)^(e-1) * θ q.2) := by
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have h2 : p.2 ≠ 0 := fun h => hn (by rw [← hp.1, h, mul_zero])
    rw [hb _ h2, ← mul_assoc, Finset.mul_sum]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_sigma', Finset.sum_sigma']
  have key : ∀ s x y : ℕ, 0 < s → s * s * (x * y) = n →
      z (s * s) * g (x * y) * (ψ x * (x:ℂ)^(e-1) * θ y)
        = χ s * (s:ℂ)^(2*e) * ψ (s * x) * ((s * x : ℕ):ℂ)^(e-1) * θ (s * y) * g (n / s^2) := by
    intro s x y hs hn'
    have hsq : Nat.sqrt (s * s) = s := Nat.sqrt_eq s
    have hdiv : n / s^2 = x * y := by
      rw [← hn', sq, Nat.mul_div_cancel_left _ (Nat.mul_pos hs hs)]
    have hpow : (s:ℂ)^(2*e) * (s:ℂ)^(e-1) = (s:ℂ)^(3*e-1) := by
      rw [← pow_add]; congr 1; omega
    rw [hz, hsq, if_pos rfl, hdiv, hψ, hθ, ← hpow]
    push_cast
    rw [mul_pow]
    ring
  have dec : ∀ a : (_ : ℕ × ℕ) × (ℕ × ℕ), a ∈ n.divisorsAntidiagonal.sigma (fun p => p.2.divisorsAntidiagonal) →
      z a.1.1 * g a.1.2 * (ψ a.2.1 * (a.2.1:ℂ)^(e-1) * θ a.2.2) ≠ 0 →
      ∃ s x y : ℕ, 0 < s ∧ s * s * (x * y) = n ∧ a = ⟨(s * s, x * y), (x, y)⟩ := by
    rintro ⟨⟨a, c⟩, ⟨x, y⟩⟩ hmem hne
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hmem
    obtain ⟨⟨hac, -⟩, hxy, -⟩ := hmem
    have h : Nat.sqrt a * Nat.sqrt a = a := by
      by_contra h
      apply hne
      simp only [hz, if_neg h, zero_mul]
    have ha : a ≠ 0 := fun h0 => hn (by rw [← hac, h0, zero_mul])
    refine ⟨Nat.sqrt a, x, y, Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero ha), by rw [h, hxy, hac], ?_⟩
    rw [h, hxy]
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => (⟨(Nat.sqrt a.1.1 * a.2.1, Nat.sqrt a.1.1 * a.2.2), Nat.sqrt a.1.1⟩ : (_ : ℕ × ℕ) × ℕ)) ?_ ?_ ?_ ?_
  · intro a ha hne
    obtain ⟨s, x, y, hs, hn', rfl⟩ := dec a ha hne
    have hx : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; apply hn; rw [← hn']; ring)
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_divisors, Nat.sqrt_eq]
    refine ⟨⟨by rw [← hn']; ring, hn⟩, Nat.dvd_gcd (dvd_mul_right s x) (dvd_mul_right s y),
      (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hs hx)).ne'⟩
  · intro a1 h11 h12 a2 h21 h22 heq
    obtain ⟨s, x, y, hs, hn', rfl⟩ := dec a1 h11 h12
    obtain ⟨t, u, v, ht, hn'', rfl⟩ := dec a2 h21 h22
    simp only [Nat.sqrt_eq, Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at heq
    obtain ⟨⟨h1, h2⟩, h3⟩ := heq
    subst h3
    obtain rfl := Nat.eq_of_mul_eq_mul_left hs h1
    obtain rfl := Nat.eq_of_mul_eq_mul_left hs h2
    rfl
  · rintro ⟨⟨x, y⟩, δ⟩ hb0 hne
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_divisors] at hb0
    obtain ⟨⟨hxy, -⟩, hδ, hg0⟩ := hb0
    have hδ0 : 0 < δ := Nat.pos_of_dvd_of_pos hδ (Nat.pos_of_ne_zero hg0)
    obtain ⟨x', rfl⟩ := dvd_trans hδ (Nat.gcd_dvd_left x y)
    obtain ⟨y', rfl⟩ := dvd_trans hδ (Nat.gcd_dvd_right (δ * x') y)
    have hn'' : δ * δ * (x' * y') = n := by rw [← hxy]; ring
    have hxy0 : x' * y' ≠ 0 := fun h0 => hn (by rw [← hn'', h0, mul_zero])
    refine ⟨⟨(δ * δ, x' * y'), (x', y')⟩, ?_, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal]
      exact ⟨⟨hn'', hn⟩, trivial, hxy0⟩
    · intro h0
      apply hne
      refine Eq.trans ?_ h0
      exact (key δ x' y' hδ0 hn'').symm
    · simp only [Nat.sqrt_eq]
  · intro a ha hne
    obtain ⟨s, x, y, hs, hn', rfl⟩ := dec a ha hne
    simp only [Nat.sqrt_eq]
    exact key s x y hs hn'

theorem rankin_convolution_coeff : ∀ (e : ℕ) (χ ψ θ g b : ℕ → ℂ), (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → ∀ n : ℕ, n ≠ 0 → LSeries.convolution (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (fun n : ℕ => θ n * g n) n = LSeries.convolution (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (fun n : ℕ => g n * b n) n := by
  intro e χ ψ θ g b hψ hθ hg hb n hn
  exact rankin_convolution_coeff_of_squareSupported e χ ψ θ g b _ hψ hθ hg hb (fun _ => rfl) n hn

end GlobalTheory
end

section

universe u_1 u_2

namespace GlobalTheory.IntegerScalarIntegral

open NumberField

theorem exists_int_smul_integral {K : Type u_1} [Field K] [NumberField K] (c : K) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (.of_finite ℚ c)
  exact hc.exists_integral_multiple

theorem exists_int_smul_mem {K : Type u_1} {V : Type u_2} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (y : V) :
    ∃ m : ℤ, m ≠ 0 ∧ m • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hbz a
  | smul c x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_int_smul_integral c
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    let r : 𝓞 K := ⟨d • c, hint⟩
    have hr : (algebraMap (𝓞 K) K r) = d • c := rfl
    have key : (d * m) • (c • x) = r • (m • x) := by
      rw [← algebraMap_smul K r (m • x), hr, smul_comm (d • c) m x, smul_assoc, mul_comm, mul_smul]
    rw [key]
    exact L.smul_mem r hmx

theorem main : ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    Submodule.span K (↑L : Set V) = ⊤ → ∀ (y : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • y ∈ L :=
  fun L hL y => exists_int_smul_mem L hL y

end GlobalTheory.IntegerScalarIntegral
end

section

open NumberField

namespace GlobalTheory.FiniteQuotientComap

theorem exists_int_mul_mem {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ b : 𝓞 E, (b : E) = (m : E) * a := by

  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (R := ℤ) (Rₘ := ℚ)
    (M := nonZeroDivisors ℤ) a (Algebra.IsIntegral.isIntegral a)
  refine ⟨(m : ℤ), nonZeroDivisors.coe_ne_zero m, (⟨m • a, hm⟩ : 𝓞 E), ?_⟩
  show m • a = _
  rw [Submonoid.smul_def, zsmul_eq_mul]

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨k, hk0, hk⟩ := hz
    refine ⟨m * k, mul_ne_zero hm0 hk0, ?_⟩
    have e1 : (m * k) • y = k • (m • y) := by rw [mul_comm, mul_smul]
    have e2 : (m * k) • z = m • (k • z) := mul_smul m k z
    rw [smul_add, e1, e2]
    exact add_mem (zsmul_mem hm k) (zsmul_mem hk m)
  | smul c y _ hy =>

    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨k, hk0, b, hb⟩ := exists_int_mul_mem c
    refine ⟨k * m, mul_ne_zero hk0 hm0, ?_⟩
    have e : (k * m) • (c • y) = b • (m • y) := by
      ext i
      simp [Algebra.smul_def, hb]
      ring
    rw [e]
    exact L.smul_mem b hm

theorem finite_quotient_comap {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L₀ L : Submodule (𝓞 E) (Fin n → E)) (h₀ : L₀.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := by

  have : Module.Finite (𝓞 E) L₀ := Module.Finite.iff_fg.mpr h₀
  have : Module.Finite ℤ L₀ := Module.Finite.trans (𝓞 E) L₀
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.comap L₀.subtype L) q
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem L (y : Fin n → E) (by rw [hL]; exact Submodule.mem_top)
  refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm0⟩, ?_⟩
  change (m : ℤ) • (Submodule.Quotient.mk y : L₀ ⧸ Submodule.comap L₀.subtype L) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  simpa using hm

end GlobalTheory.FiniteQuotientComap
end

section

namespace GlobalTheory.IdealComapPreimage

open IsDedekindDomain

theorem ideal_eq_comap {p : ℕ} (hp : Nat.Prime p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : (p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal) :
    v.asIdeal = Ideal.comap (Rat.ringOfIntegersEquiv : NumberField.RingOfIntegers ℚ →+* ℤ)
      (Ideal.span {(p : ℤ)}) := by
  set e := Rat.ringOfIntegersEquiv
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  haveI : (Ideal.comap (e : NumberField.RingOfIntegers ℚ →+* ℤ) (Ideal.span {(p : ℤ)})).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e.surjective
  symm
  refine Ideal.IsMaximal.eq_of_le this v.isPrime.ne_top ?_
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
  obtain ⟨k, hk⟩ := hx
  have : x = (p : NumberField.RingOfIntegers ℚ) * e.symm k := by
    apply e.injective
    simpa using hk
  rw [this]
  exact v.asIdeal.mul_mem_right _ hv

theorem main : ∀ {p : ℕ}, Nat.Prime p → ∀ {v v' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}, (↑p : NumberField.RingOfIntegers ℚ) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → (↑p : NumberField.RingOfIntegers ℚ) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v' → v = v' := by
  intro p hp v v' hv hv'
  apply HeightOneSpectrum.ext
  rw [ideal_eq_comap hp v hv, ideal_eq_comap hp v' hv']

end GlobalTheory.IdealComapPreimage
end

section

namespace GlobalTheory.PowerNearOneNorm

theorem exists_pow_sub_one_norm_lt_one {p : ℕ} [hp : Fact (Nat.Prime p)] (x : PadicAlgCl p)
    (hx : ‖x‖ = (1 : ℝ)) : ∃ n : ℕ, 0 < n ∧ ‖x ^ n - (1 : PadicAlgCl p)‖ < (1 : ℝ) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  let V : Submodule ℚ_[p] (PadicAlgCl p) := Subalgebra.toSubmodule (Algebra.adjoin ℚ_[p] {x})
  have : FiniteDimensional ℚ_[p] V := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  have : ProperSpace V := FiniteDimensional.proper ℚ_[p] V
  have hmem : ∀ n : ℕ, x ^ n ∈ V := fun n =>
    Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℚ_[p] x) n
  let s : ℕ → V := fun n => ⟨x ^ n, hmem n⟩
  have hs : ∀ n, s n ∈ Metric.closedBall (0 : V) 1 := by
    intro n
    simp [s, norm_pow, hx]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : V) 1).tendsto_subseq hs
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq 1 one_pos
  have h1 := hN (N + 1) (Nat.le_succ N)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (hφ (Nat.lt_succ_self N))
  refine ⟨d + 1, d.succ_pos, ?_⟩
  have e : x ^ φ (N + 1) - x ^ φ N = x ^ φ N * (x ^ (d + 1) - 1) := by
    rw [hd]
    ring
  have h1' : ‖x ^ φ (N + 1) - x ^ φ N‖ < 1 := by simpa [s, dist_eq_norm] using h1
  rwa [e, norm_mul, norm_pow, hx, one_pow, one_mul] at h1'

end GlobalTheory.PowerNearOneNorm
end

section

namespace GlobalTheory.AlgebraMapNormLeOne

open Polynomial

theorem norm_algebraMap_le_one (l : ℕ) [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  calc ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖
      = ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] a)‖ := by
        rw [← IsScalarTower.algebraMap_apply]
    _ = ‖algebraMap ℤ_[l] ℚ_[l] a‖ := PadicAlgCl.norm_extends l _
    _ ≤ 1 := PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral (l : ℕ) [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  let v : Valuation (PadicAlgCl l) NNReal := Valued.v
  have hle : ∀ y : PadicAlgCl l, v y ≤ 1 ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  let f : ℤ_[l] →+* v.integer := (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer
    fun a => (hle _).mpr (norm_algebraMap_le_one l a)
  let _ : Algebra ℤ_[l] v.integer := f.toAlgebra
  have : IsScalarTower ℤ_[l] v.integer (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxO : IsIntegral v.integer x := hx.tower_top
  exact (hle x).mp ((Valuation.Integers.isIntegral_iff_v_le_one (Valuation.integer.integers v)).mp hxO)

end GlobalTheory.AlgebraMapNormLeOne
end
