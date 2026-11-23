module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

section

open scoped TensorProduct Classical

namespace GlobalTheory.RatRed

def LUnit (ℓ : ℕ) (r : ℚ) : Prop :=
  ∃ N : ℕ, ¬ ℓ ∣ N ∧ (∃ m : ℤ, (N : ℚ) * r = m) ∧ ∃ m : ℤ, (N : ℚ) * r⁻¹ = m

theorem lunit_one (ℓ : ℕ) (hℓ : ℓ.Prime) : LUnit ℓ 1 :=
  ⟨1, hℓ.not_dvd_one, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

theorem lunit_mul {ℓ : ℕ} (hℓ : ℓ.Prime) {r s : ℚ} (hr : LUnit ℓ r) (hs : LUnit ℓ s) :
    LUnit ℓ (r * s) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  obtain ⟨M, hM, ⟨k₁, g₁⟩, ⟨k₂, g₂⟩⟩ := hs
  refine ⟨N * M, fun h => (hℓ.dvd_mul.1 h).elim hN hM, ⟨m₁ * k₁, ?_⟩, ⟨m₂ * k₂, ?_⟩⟩
  · push_cast; rw [← h₁, ← g₁]; ring
  · push_cast; rw [← h₂, ← g₂, mul_inv]; ring

theorem lunit_inv {ℓ : ℕ} {r : ℚ} (hr : LUnit ℓ r) : LUnit ℓ r⁻¹ := by
  obtain ⟨N, hN, h₁, h₂⟩ := hr
  exact ⟨N, hN, h₂, by simpa using h₁⟩

theorem lunit_neg {ℓ : ℕ} {r : ℚ} (hr : LUnit ℓ r) : LUnit ℓ (-r) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  refine ⟨N, hN, ⟨-m₁, ?_⟩, ⟨-m₂, ?_⟩⟩
  · push_cast; rw [← h₁]; ring
  · push_cast; rw [← h₂, inv_neg]; ring

theorem lunit_nat {ℓ : ℕ} {n : ℕ} (hn : ¬ ℓ ∣ n) : LUnit ℓ (n : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by
    rintro h; exact hn (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  refine ⟨n, hn, ⟨(n : ℤ) * n, by push_cast; ring⟩, ⟨1, by rw [mul_inv_cancel₀ hn0]; simp⟩⟩

theorem lunit_pow {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ} (hr : LUnit ℓ r) (k : ℕ) : LUnit ℓ (r ^ k) := by
  induction k with
  | zero => simpa using lunit_one ℓ hℓ
  | succ k ih => rw [pow_succ]; exact lunit_mul hℓ ih hr

theorem lunit_zpow {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ} (hr : LUnit ℓ r) (k : ℤ) : LUnit ℓ (r ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa using lunit_pow hℓ hr n
  · simpa [zpow_neg] using lunit_inv (lunit_pow hℓ hr n)

theorem lunit_prime {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hne : p ≠ ℓ) : LUnit ℓ (p : ℚ) :=
  lunit_nat (fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h).symm)

theorem lunit_decomp {ℓ : ℕ} (hℓ : ℓ.Prime) {c : ℚ} (hc : c ≠ 0) :
    ∃ k : ℤ, LUnit ℓ (c / (ℓ : ℚ) ^ k) := by
  have hnum : c.num.natAbs ≠ 0 := by simpa using Rat.num_ne_zero.2 hc
  obtain ⟨e₁, n, hn, hne⟩ := Nat.exists_eq_pow_mul_and_not_dvd hnum ℓ hℓ.ne_one
  obtain ⟨e₂, m, hm, hme⟩ := Nat.exists_eq_pow_mul_and_not_dvd c.den_nz ℓ hℓ.ne_one
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hm0 : (m : ℚ) ≠ 0 := by
    rintro h; exact hm (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  refine ⟨(e₁ : ℤ) - e₂, ?_⟩
  have hden : (c.den : ℚ) = (ℓ : ℚ) ^ e₂ * m := by rw [hme]; push_cast; ring
  have key : c * ((ℓ : ℚ) ^ e₂ * m) = (c.num : ℚ) := by rw [← hden]; exact Rat.mul_den_eq_num c
  rw [zpow_sub₀ hℓ0, zpow_natCast, zpow_natCast]
  rcases Int.natAbs_eq c.num with h | h
  · have hv : c / ((ℓ : ℚ) ^ e₁ / (ℓ : ℚ) ^ e₂) = (n : ℚ) * (m : ℚ)⁻¹ := by
      have : (c.num : ℚ) = (ℓ : ℚ) ^ e₁ * n := by rw [h, hne]; push_cast; ring
      rw [this] at key
      have hp : (ℓ : ℚ) ^ e₁ ≠ 0 := pow_ne_zero _ hℓ0
      field_simp at key ⊢
      linear_combination key
    rw [hv]; exact lunit_mul hℓ (lunit_nat hn) (lunit_inv (lunit_nat hm))
  · have hv : c / ((ℓ : ℚ) ^ e₁ / (ℓ : ℚ) ^ e₂) = -((n : ℚ) * (m : ℚ)⁻¹) := by
      have : (c.num : ℚ) = -((ℓ : ℚ) ^ e₁ * n) := by rw [h, hne]; push_cast; ring
      rw [this] at key
      have hp : (ℓ : ℚ) ^ e₁ ≠ 0 := pow_ne_zero _ hℓ0
      field_simp at key ⊢
      linear_combination key
    rw [hv]; exact lunit_neg (lunit_mul hℓ (lunit_nat hn) (lunit_inv (lunit_nat hm)))

theorem lunit_integral {E : Type} [CommRing E] [Algebra ℚ E] {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ}
    (hr : LUnit ℓ r) {d : ℕ} (hd : ¬ ℓ ∣ d) {x y : E} (hx : IsIntegral ℤ ((d : E) * x))
    (hy : IsIntegral ℤ ((d : E) * y)) :
    ∃ d' : ℕ, ¬ ℓ ∣ d' ∧ IsIntegral ℤ ((d' : E) * (algebraMap ℚ E r * x)) ∧
      IsIntegral ℤ ((d' : E) * (algebraMap ℚ E r⁻¹ * y)) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  refine ⟨d * N, fun h => (hℓ.dvd_mul.1 h).elim hd hN, ?_, ?_⟩
  · have e : ((d * N : ℕ) : E) * (algebraMap ℚ E r * x) = (m₁ : E) * ((d : E) * x) := by
      have : (m₁ : E) = algebraMap ℚ E ((N : ℚ) * r) := by rw [h₁]; simp
      rw [this, map_mul, map_natCast]; push_cast; ring
    rw [e]; exact (isIntegral_intCast m₁).mul hx
  · have e : ((d * N : ℕ) : E) * (algebraMap ℚ E r⁻¹ * y) = (m₂ : E) * ((d : E) * y) := by
      have : (m₂ : E) = algebraMap ℚ E ((N : ℚ) * r⁻¹) := by rw [h₂]; simp
      rw [this, map_mul, map_natCast]; push_cast; ring
    rw [e]; exact (isIntegral_intCast m₂).mul hy

theorem exists_nat_mul_integral {E : Type} [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (z : E) : ∃ D : ℕ, D ≠ 0 ∧ IsIntegral ℤ ((D : E) * z) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have := congrArg (Int.cast : ℤ → E) h
    rw [Int.cast_natCast] at this
    rwa [this] at hint
  · have := congrArg (Int.cast : ℤ → E) h
    rw [Int.cast_neg, Int.cast_natCast] at this
    rw [this, neg_mul] at hint
    simpa using hint.neg

theorem ratred : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E ≃ₐ[ℚ] E) (S : Finset ℕ) (A : Finset E),
    (∀ a : E, IsUnit a → τ a = a →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
        ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
      ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e) →
    ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  intro E _ _ _ τ S A hA a ha hτa hloc
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨D₁, hD₁, hi₁⟩ := exists_nat_mul_integral (u : E)
  obtain ⟨D₂, hD₂, hi₂⟩ := exists_nat_mul_integral ((u⁻¹ : Eˣ) : E)
  have hD0 : D₁ * D₂ ≠ 0 := mul_ne_zero hD₁ hD₂
  have hDu : IsIntegral ℤ (((D₁ * D₂ : ℕ) : E) * u) := by
    have e : (((D₁ * D₂ : ℕ) : E) * u) = (D₂ : E) * ((D₁ : E) * u) := by push_cast; ring
    rw [e]; exact (isIntegral_natCast D₂).mul hi₁
  have hDu' : IsIntegral ℤ (((D₁ * D₂ : ℕ) : E) * ((u⁻¹ : Eˣ) : E)) := by
    have e : (((D₁ * D₂ : ℕ) : E) * ((u⁻¹ : Eˣ) : E)) = (D₁ : E) * ((D₂ : E) * ((u⁻¹ : Eˣ) : E)) := by
      push_cast; ring
    rw [e]; exact (isIntegral_natCast D₁).mul hi₂
  choose! c b x y hc hb h₁ h₂ d hd hix hiy using hloc
  have hk : ∀ ℓ, ℓ.Prime → ℓ ∉ S → ∃ k : ℤ, LUnit ℓ (c ℓ / (ℓ : ℚ) ^ k) :=
    fun ℓ hℓ hS => lunit_decomp hℓ (hc ℓ hℓ hS)
  choose! k hk using hk
  let T : Finset ℕ := (D₁ * D₂).primeFactors.filter (· ∉ S)
  have hTmem : ∀ p, p ∈ T ↔ p.Prime ∧ p ∣ D₁ * D₂ ∧ p ∉ S := by
    intro p
    simp only [T, Finset.mem_filter, Nat.mem_primeFactors]
    tauto
  let q : ℚ := ∏ p ∈ T, (p : ℚ) ^ (k p)
  have hq0 : q ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun p hp => zpow_ne_zero _ ?_
    exact_mod_cast ((hTmem p).1 hp).1.ne_zero
  have hqU : ∀ ℓ, ℓ.Prime → ℓ ∉ T → LUnit ℓ q := by
    intro ℓ hℓ hT
    refine Finset.prod_induction _ (LUnit ℓ) (fun _ _ => lunit_mul hℓ) (lunit_one ℓ hℓ) ?_
    intro p hp
    exact lunit_zpow hℓ (lunit_prime hℓ ((hTmem p).1 hp).1 (fun h => hT (h ▸ hp))) _
  have hcqU : ∀ ℓ ∈ T, LUnit ℓ (c ℓ / q) := by
    intro ℓ hℓT
    obtain ⟨hℓ, -, hS⟩ := (hTmem ℓ).1 hℓT
    have e : c ℓ / q = c ℓ / (ℓ : ℚ) ^ (k ℓ) * (∏ p ∈ T.erase ℓ, (p : ℚ) ^ (k p))⁻¹ := by
      simp only [q]
      rw [← Finset.mul_prod_erase T (fun p => (p : ℚ) ^ (k p)) hℓT, div_mul_eq_div_div, div_eq_mul_inv]
    rw [e]
    refine lunit_mul hℓ (hk ℓ hℓ hS) (lunit_inv ?_)
    refine Finset.prod_induction _ (LUnit ℓ) (fun _ _ => lunit_mul hℓ) (lunit_one ℓ hℓ) ?_
    intro p hp
    obtain ⟨hpl, hpT⟩ := Finset.mem_erase.1 hp
    exact lunit_zpow hℓ (lunit_prime hℓ ((hTmem p).1 hpT).1 hpl) _
  have hq1 : algebraMap ℚ E q * algebraMap ℚ E q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
  have ha' : IsUnit (algebraMap ℚ E q⁻¹ * (u : E)) :=
    ((isUnit_iff_ne_zero.2 (inv_ne_zero hq0)).map (algebraMap ℚ E)).mul u.isUnit
  have hτ' : τ (algebraMap ℚ E q⁻¹ * (u : E)) = algebraMap ℚ E q⁻¹ * (u : E) := by
    rw [map_mul, AlgEquiv.commutes, hτa]
  obtain ⟨a₀, ha₀, e, he⟩ := hA _ ha' hτ' (by
    intro ℓ hℓ hS
    by_cases hT : ℓ ∈ T
    · obtain ⟨d', hd', hx', hy'⟩ :=
        lunit_integral hℓ (hcqU ℓ hT) (hd ℓ hℓ hS) (hix ℓ hℓ hS) (hiy ℓ hℓ hS)
      refine ⟨b ℓ, _, _, hb ℓ hℓ hS, ?_, ?_, d', hd', hx', hy'⟩
      · rw [div_eq_mul_inv, map_mul, h₁ ℓ hℓ hS]; ring
      · have hc1 : algebraMap ℚ E (c ℓ) * algebraMap ℚ E (c ℓ)⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel₀ (hc ℓ hℓ hS), map_one]
        rw [inv_div, div_eq_mul_inv, map_mul]
        linear_combination (-(b ℓ * τ (b ℓ))) * hc1 + algebraMap ℚ E (c ℓ)⁻¹ * h₂ ℓ hℓ hS -
          (algebraMap ℚ E (c ℓ)⁻¹ * y ℓ * (u : E)) * hq1
    · have hD : ¬ ℓ ∣ D₁ * D₂ := fun h => hT ((hTmem ℓ).2 ⟨hℓ, h, hS⟩)
      obtain ⟨d', hd', hx', hy'⟩ := lunit_integral hℓ (lunit_inv (hqU ℓ hℓ hT)) hD hDu hDu'
      refine ⟨1, _, _, isUnit_one, ?_, ?_, d', hd', hx', hy'⟩
      · simp
      · rw [inv_inv, map_one, mul_one]
        linear_combination (-((u : E) * ((u⁻¹ : Eˣ) : E))) * hq1 - u.mul_inv)
  refine ⟨a₀, ha₀, Units.mk0 q hq0, e, ?_⟩
  rw [← he, Units.val_mk0, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_mul]

end GlobalTheory.RatRed
end

section

open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerAlg

open MvPolynomial

variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

def rels (φ : (Π _ : Fin q, L) →ₘₗ[B] B) : Set (MvPolynomial L B) :=
  Set.range (fun p : L × L => X (p.1 + p.2) - X p.1 - X p.2) ∪
  Set.range (fun p : B × L => X (p.1 • p.2) - C p.1 * X p.2) ∪
  Set.range (fun ℓ : Fin q → L => ∏ i, X (ℓ i) - C (φ ℓ))

def ideal (φ : (Π _ : Fin q, L) →ₘₗ[B] B) : Ideal (MvPolynomial L B) :=
  Ideal.span (rels φ)

abbrev Alg (φ : (Π _ : Fin q, L) →ₘₗ[B] B) : Type :=
  MvPolynomial L B ⧸ ideal φ

variable (φ : (Π _ : Fin q, L) →ₘₗ[B] B)

theorem algebraMap_eq_mk (c : B) : algebraMap B (Alg φ) c = Ideal.Quotient.mk _ (C c) := rfl

theorem add_mem (a b : L) : X (a + b) - X a - X b ∈ ideal φ :=
  Ideal.subset_span (Or.inl (Or.inl ⟨(a, b), rfl⟩))

theorem smul_mem (c : B) (a : L) : X (c • a) - C c * X a ∈ ideal φ :=
  Ideal.subset_span (Or.inl (Or.inr ⟨(c, a), rfl⟩))

theorem prod_mem (ℓ : Fin q → L) : ∏ i, X (ℓ i) - C (φ ℓ) ∈ ideal φ :=
  Ideal.subset_span (Or.inr ⟨ℓ, rfl⟩)

def gen : L →ₗ[B] Alg φ where
  toFun ℓ := Ideal.Quotient.mk _ (X ℓ)
  map_add' a b := by
    rw [← sub_eq_zero, sub_add_eq_sub_sub, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact add_mem φ a b
  map_smul' c a := by
    rw [← sub_eq_zero, RingHom.id_apply, Algebra.smul_def, algebraMap_eq_mk,
      ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact smul_mem φ c a

theorem gen_apply (ℓ : L) : gen φ ℓ = Ideal.Quotient.mk _ (X ℓ) := rfl

theorem prod_gen (ℓ : Fin q → L) : ∏ i, gen φ (ℓ i) = algebraMap B (Alg φ) (φ ℓ) := by
  rw [← sub_eq_zero]
  simp only [gen_apply, ← map_prod, algebraMap_eq_mk]
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact prod_mem φ ℓ

def scalePoly (t : B) : MvPolynomial L B →ₐ[B] MvPolynomial L B := aeval fun ℓ => C t * X ℓ

theorem scalePoly_X (t : B) (ℓ : L) : scalePoly t (X ℓ) = C t * X ℓ := by simp [scalePoly]

theorem scalePoly_C (t c : B) : scalePoly (L := L) t (C c) = C c := by
  simp [scalePoly, aeval_C, MvPolynomial.algebraMap_eq]

theorem le_comap_scale (t : B) (ht : t ^ q = 1) : ideal φ ≤ (ideal φ).comap (scalePoly t) := by
  rw [ideal, Ideal.span_le]
  rintro r ((⟨⟨a, b⟩, rfl⟩ | ⟨⟨c, a⟩, rfl⟩) | ⟨ℓ, rfl⟩)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (X (a + b) - X a - X b) = C t * (X (a + b) - X a - X b) := by
      simp only [map_sub, scalePoly_X]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (add_mem φ a b)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (X (c • a) - C c * X a) = C t * (X (c • a) - C c * X a) := by
      simp only [map_sub, map_mul, scalePoly_X, scalePoly_C]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (smul_mem φ c a)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (∏ i, X (ℓ i) - C (φ ℓ)) = ∏ i, X (ℓ i) - C (φ ℓ) := by
      simp only [map_sub, map_prod, scalePoly_X, scalePoly_C, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← map_pow, ht, map_one, one_mul]
    rw [this]; exact prod_mem φ ℓ

def scale (t : B) (ht : t ^ q = 1) : Alg φ →ₐ[B] Alg φ :=
  Ideal.quotientMapₐ (ideal φ) (scalePoly t) (le_comap_scale φ t ht)

theorem scale_mk (t : B) (ht : t ^ q = 1) (p : MvPolynomial L B) :
    scale φ t ht (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (scalePoly t p) := rfl

theorem scale_gen (t : B) (ht : t ^ q = 1) (ℓ : L) : scale φ t ht (gen φ ℓ) = t • gen φ ℓ := by
  rw [gen_apply, scale_mk, scalePoly_X, map_mul, Algebra.smul_def, algebraMap_eq_mk]

theorem scale_ext {f g : Alg φ →ₐ[B] Alg φ} (h : ∀ ℓ, f (gen φ ℓ) = g (gen φ ℓ)) : f = g :=
  Ideal.Quotient.algHom_ext B (MvPolynomial.algHom_ext fun ℓ => h ℓ)

theorem scale_comp (s t : B) (hs : s ^ q = 1) (ht : t ^ q = 1) :
    (scale φ s hs).comp (scale φ t ht) = scale φ (s * t) (by rw [mul_pow, hs, ht, one_mul]) :=
  scale_ext φ fun ℓ => by
    rw [AlgHom.comp_apply, scale_gen, map_smul, scale_gen, scale_gen, smul_smul, mul_comm]

theorem scale_eq_id (t : B) (ht : t ^ q = 1) (h1 : t = 1) : scale φ t ht = AlgHom.id B (Alg φ) :=
  scale_ext φ fun ℓ => by rw [scale_gen, h1, one_smul, AlgHom.id_apply]

theorem scale_congr (s t : B) (hs : s ^ q = 1) (ht : t ^ q = 1) (h : s = t) :
    scale φ s hs = scale φ t ht := by subst h; rfl

def tw (ζ : B) (g : ZMod q) : B := ζ ^ g.val

theorem tw_add [NeZero q] {ζ : B} (hζ : ζ ^ q = 1) (g h : ZMod q) :
    tw ζ (g + h) = tw ζ g * tw ζ h := by
  rw [tw, tw, tw, ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (g.val + h.val) q, pow_add, pow_mul, hζ, one_pow, mul_one]

theorem tw_pow {ζ : B} (hζ : ζ ^ q = 1) (g : ZMod q) : tw ζ g ^ q = 1 := by
  rw [tw, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem tw_zero (ζ : B) : tw ζ (0 : ZMod q) = 1 := by simp [tw]

theorem tw_mul_tw_neg [NeZero q] {ζ : B} (hζ : ζ ^ q = 1) (g : ZMod q) :
    tw ζ g * tw ζ (-g) = 1 := by rw [← tw_add hζ, add_neg_cancel, tw_zero]

def act [NeZero q] (ζ : B) (hζ : ζ ^ q = 1) : Multiplicative (ZMod q) →* (Alg φ ≃ₐ[B] Alg φ) where
  toFun g := AlgEquiv.ofAlgHom (scale φ (tw ζ g.toAdd) (tw_pow hζ _))
    (scale φ (tw ζ (-g.toAdd)) (tw_pow hζ _))
    (by rw [scale_comp]; exact scale_eq_id φ _ _ (tw_mul_tw_neg hζ _))
    (by rw [scale_comp]; exact scale_eq_id φ _ _ (by rw [mul_comm]; exact tw_mul_tw_neg hζ _))
  map_one' := AlgEquiv.ext fun x => by
    change scale φ (tw ζ (0 : ZMod q)) (tw_pow hζ 0) x = x
    rw [scale_eq_id φ _ _ (tw_zero ζ)]; rfl
  map_mul' g h := AlgEquiv.ext fun x => by
    change scale φ (tw ζ (g.toAdd + h.toAdd)) (tw_pow hζ _) x =
      scale φ (tw ζ g.toAdd) (tw_pow hζ _) (scale φ (tw ζ h.toAdd) (tw_pow hζ _) x)
    rw [← AlgHom.comp_apply, scale_comp]
    exact DFunLike.congr_fun (scale_congr φ _ _ _ _ (tw_add hζ _ _)) x

theorem act_gen [NeZero q] (ζ : B) (hζ : ζ ^ q = 1) (g : ZMod q) (ℓ : L) :
    act φ ζ hζ (Multiplicative.ofAdd g) (gen φ ℓ) = ζ ^ g.val • gen φ ℓ :=
  scale_gen φ _ (tw_pow hζ _) ℓ

end GlobalTheory.KummerAlg
end
end

section

namespace GlobalTheory.GaloisEmbeddingExistence

theorem exists_galois_embedding (R R' : Type) [CommRing R] [IsDomain R] [CharZero R]
    [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R']
    (hinj : Function.Injective (algebraMap R R')) :
    ∃ (L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R))),
      FiniteDimensional (FractionRing R) L ∧ IsGalois (FractionRing R) L ∧
        ∃ (j : R' →ₐ[R] L), Function.Injective j := by
  classical
  set K := FractionRing R
  set Ω := AlgebraicClosure K
  haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').2 hinj
  have hΩ : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).2 hΩ
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  let φ : R' →ₐ[R] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hφ : Function.Injective φ := by
    have h1 : (RingHom.ker φ).comap (algebraMap R R') = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes] at hx
      exact hΩ (by simpa using hx)
    have h2 : RingHom.ker φ = ⊥ := Ideal.eq_bot_of_comap_eq_bot h1
    exact (RingHom.injective_iff_ker_eq_bot φ).2 h2
  obtain ⟨s, hs⟩ := (Module.finite_def.1 (inferInstance : Module.Finite R R'))
  let M : IntermediateField K Ω := IntermediateField.adjoin K (φ '' (s : Set R'))
  haveI : Finite (φ '' (s : Set R')) := (s.finite_toSet.image φ).to_subtype
  haveI : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  let L : IntermediateField K Ω := IntermediateField.normalClosure K M Ω
  have hML : M ≤ L := IntermediateField.le_normalClosure M
  have hmem : ∀ x : R', φ x ∈ L := by
    intro x
    have hx : x ∈ Submodule.span R (s : Set R') := by rw [hs]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact hML (IntermediateField.subset_adjoin K _ ⟨x, hx, rfl⟩)
    | zero => simpa using L.zero_mem
    | add x y _ _ hx hy => simpa using L.add_mem hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul, AlgHom.commutes, IsScalarTower.algebraMap_apply R K Ω]
      exact L.mul_mem (L.algebraMap_mem _) hx
  refine ⟨L, inferInstance, inferInstance, ?_⟩
  let j : R' →ₐ[R] L :=
    { toFun := fun x => ⟨φ x, hmem x⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun x y => Subtype.ext (map_mul φ x y)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun x y => Subtype.ext (map_add φ x y)
      commutes' := fun r => Subtype.ext (φ.commutes r) }
  exact ⟨j, fun x y h => hφ (congrArg Subtype.val h)⟩

end GlobalTheory.GaloisEmbeddingExistence
end

section

open Polynomial

namespace GlobalTheory

theorem ringHom_extend_of_isIntegral_isAlgClosed (A C K : Type) [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.IsIntegral A C] [Field K] [IsAlgClosed K] (h : A →+* K)
    (hk : RingHom.ker (algebraMap A C) ≤ RingHom.ker h) :
    ∃ ψ : C →+* K, ψ.comp (algebraMap A C) = h := by
  classical
  haveI hp : (RingHom.ker h).IsPrime := RingHom.ker_isPrime h
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker h) (⊥ : Ideal C)
    (by simpa [← RingHom.ker_eq_comap_bot] using hk)
  haveI : Q.LiesOver (RingHom.ker h) := (Ideal.liesOver_iff _ _).mpr hQc.symm
  letI : Algebra (A ⧸ RingHom.ker h) K := (RingHom.kerLift h).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker h) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective h)
  haveI : FaithfulSMul (A ⧸ RingHom.ker h) (C ⧸ Q) := inferInstance
  haveI : Nontrivial (A ⧸ RingHom.ker h) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker h) (C ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver (A := A) (p := RingHom.ker h) (P := Q)
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker h) (C ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) (C ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective h)
  let φ : (C ⧸ Q) →ₐ[A ⧸ RingHom.ker h] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have e1 : (Ideal.Quotient.mk Q) (algebraMap A C a) =
      algebraMap (A ⧸ RingHom.ker h) (C ⧸ Q) (Ideal.Quotient.mk _ a) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [e1, φ.commutes]
  rfl

end GlobalTheory
end
