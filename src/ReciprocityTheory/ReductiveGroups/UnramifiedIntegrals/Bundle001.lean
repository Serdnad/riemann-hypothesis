module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
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
public import Mathlib.NumberTheory.LSeries.PrimesInAP
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation

open Polynomial Finset

variable (l : ℕ) [Fact l.Prime]

theorem norm_eq_of_norm_sub_lt' {a b : ℂ_[l]} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - b) (y := b) h.ne
  rwa [sub_add_cancel, max_eq_right h.le] at this

theorem exists_root_near (P : ℂ_[l][X]) (hP : P.Monic) (x : ℂ_[l]) (h : ‖P.eval x‖ < 1) :
    ∃ a, P.IsRoot a ∧ ‖x - a‖ < 1 := by
  have hsplit : (P.roots.map fun a => X - C a).prod = P :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP IsAlgClosed.card_roots_eq_natDegree
  by_contra hcon
  push Not at hcon
  have key : ∀ s : Multiset ℂ_[l], (∀ a ∈ s, 1 ≤ ‖x - a‖) →
      1 ≤ ‖((s.map fun a => X - C a).prod).eval x‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul]
      simp only [eval_sub, eval_X, eval_C]
      exact one_le_mul_of_one_le_of_one_le (hs a (Multiset.mem_cons_self _ _))
        (ih fun b hb => hs b (Multiset.mem_cons_of_mem hb))
  have := key P.roots (fun a ha => hcon a ((mem_roots hP.ne_zero).1 ha))
  rw [hsplit] at this
  linarith

theorem norm_pow_sub_one_le {y : ℂ_[l]} (hy : ‖y‖ = 1) (k : ℕ) : ‖y ^ k - 1‖ ≤ ‖y - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : y ^ (k + 1) - 1 = y * (y ^ k - 1) + (y - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hy, one_mul]
    exact ih

theorem norm_geom_sum_sub_le {y : ℂ_[l]} (hy : ‖y‖ = 1) (k : ℕ) :
    ‖(∑ i ∈ range k, y ^ i) - k‖ ≤ ‖y - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (∑ i ∈ range (k + 1), y ^ i) - ((k + 1 : ℕ) : ℂ_[l]) =
        ((∑ i ∈ range k, y ^ i) - k) + (y ^ k - 1) := by
      rw [sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (norm_pow_sub_one_le l hy k))

theorem norm_geom_sum_eq_one {y : ℂ_[l]} (hy : ‖y - 1‖ < 1) {m : ℕ} (hm : ‖(m : ℂ_[l])‖ = 1) :
    ‖∑ i ∈ range m, y ^ i‖ = 1 := by
  have hy1 : ‖y‖ = 1 := by
    have := norm_eq_of_norm_sub_lt' l (a := y) (b := 1) (by rwa [norm_one])
    rwa [norm_one] at this
  have := norm_geom_sum_sub_le l hy1 m
  rw [← hm]
  exact norm_eq_of_norm_sub_lt' l (by rw [hm]; exact lt_of_le_of_lt this hy)

end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass

namespace ReciprocityTheory.ChartRestriction.L1

def DD (τ : ℍ) : ℂ := ModularForm.discriminant τ

def AA (τ : ℍ) : ℂ := E₄ τ ^ 3

def jT (τ : ℍ) : ℂ := AA τ / DD τ

def Tm (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (m.divisors.sigma fun a => Finset.range (m / a)).image fun x => (x.1, x.2, m / x.1)

def pt (a b e : ℕ) (τ : ℍ) : ℍ := UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / e)

def fac (t : ℕ × ℕ × ℕ) (τ : ℍ) : ℂ :=
  AA τ * DD (pt t.1 t.2.1 t.2.2 τ) - AA (pt t.1 t.2.1 t.2.2 τ) * DD τ

def Gm (m : ℕ) (τ : ℍ) : ℂ := ∏ t ∈ Tm m, fac t τ

def zetaC (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

def Rm (m : ℕ) : Subring ℂ := Subring.closure {zetaC m}

def CoeffIn (R : Subring ℂ) (f : PowerSeries ℂ) : Prop := ∀ n, PowerSeries.coeff n f ∈ R

def IsTauOf (L : PeriodPair) (c : ℂ) (τ : ℍ) : Prop :=
  c ≠ 0 ∧ ∀ x : ℂ, x ∈ L.lattice ↔ ∃ u v : ℤ, x = c * (u * (τ : ℂ) + v)

def Tmat (t : ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(t.1 : ℤ), (t.2.1 : ℤ); 0, (t.2.2 : ℤ)]

def IsMF (k : ℤ) (f : ℍ → ℂ) : Prop := ∃ g : ModularForm 𝒮ℒ k, ∀ τ, g τ = f τ

def e4Z : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ)

def e6Z : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ)

def aZ : PowerSeries ℤ := e4Z ^ 3

def dZ : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff n (e4Z ^ 3 - e6Z ^ 2) / 1728

def aC : PowerSeries ℂ := aZ.map (Int.castRingHom ℂ)

def dC : PowerSeries ℂ := dZ.map (Int.castRingHom ℂ)

def xp {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => if k ∣ n then PowerSeries.coeff (n / k) f else 0

def Conv (f : PowerSeries ℂ) : Prop :=
  ∀ x : ℂ, ‖x‖ < 1 → Summable fun n => ‖PowerSeries.coeff n f‖ * ‖x‖ ^ n

def ev (f : PowerSeries ℂ) (x : ℂ) : ℂ := ∑' n, PowerSeries.coeff n f * x ^ n

def sub1 (c : ℂ) (k : ℕ) (f : PowerSeries ℂ) : PowerSeries ℂ := xp k (PowerSeries.rescale c f)

def facSer (m : ℕ) (t : ℕ × ℕ × ℕ) : PowerSeries ℂ :=
  xp m aC * sub1 (zetaC t.2.2 ^ t.2.1) (t.1 ^ 2) dC - sub1 (zetaC t.2.2 ^ t.2.1) (t.1 ^ 2) aC * xp m dC

def prodSer (m : ℕ) : PowerSeries ℂ := ∏ t ∈ Tm m, facSer m t

def LowUnit (R : Subring ℂ) (f : PowerSeries ℂ) (n0 : ℕ) (u : ℂ) : Prop :=
  u ∈ R ∧ u⁻¹ ∈ R ∧ u ≠ 0 ∧ (∀ n < n0, PowerSeries.coeff n f = 0) ∧ PowerSeries.coeff n0 f = u

def qm (m : ℕ) (τ : ℍ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ / m)

end ReciprocityTheory.ChartRestriction.L1
end
end

section

namespace ReciprocityTheory.ChartRestriction.L1

open scoped NumberTheorySymbols

theorem prime_choice_class (d : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (h3 : 3 ∣ d) (hd3 : d ≠ 3) :
    ∃ a : ℕ, a % 3 = 2 ∧ J((a : ℤ) | d) = 1 := by
  obtain ⟨d', rfl⟩ := h3
  have hd'4 : d' % 4 = 1 := by omega
  have hd'1 : d' ≠ 1 := by
    rintro rfl
    exact hd3 rfl
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd'1
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hqd
    omega
  haveI := Fact.mk hq
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact hq2)
  obtain ⟨d'', rfl⟩ := hqd
  have hd''0 : d'' ≠ 0 := by
    rintro rfl
    simp at hd4
  haveI : NeZero d'' := ⟨hd''0⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hcop1 : Nat.Coprime q d'' := by
    refine (Nat.Prime.coprime_iff_not_dvd hq).mpr ?_
    rintro ⟨e, rfl⟩
    exact absurd (Nat.isUnit_iff.mp (hsq q ⟨3 * e, by ring⟩)) hq.one_lt.ne'
  have hcop2 : Nat.Coprime 3 (q * d'') := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_
    rintro ⟨e, he⟩
    exact absurd (Nat.isUnit_iff.mp (hsq 3 ⟨e, by rw [he]; ring⟩)) (by norm_num)

  obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcop1 c.val 1
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hcop2 2 b
  refine ⟨a, ?_, ?_⟩
  · unfold Nat.ModEq at ha1
    omega
  have hmq : a % q = c.val % q := (ha2.of_mul_right d'').trans hb1
  have hmd : a % d'' = 1 % d'' := (ha2.of_mul_left q).trans hb2
  have hm3 : a % 3 = 2 := by
    unfold Nat.ModEq at ha1
    omega
  have hJ3 : J((a : ℤ) | 3) = -1 := by
    rw [jacobiSym.mod_left]
    have : (a : ℤ) % ((3 : ℕ) : ℤ) = 2 := by omega
    rw [this]
    norm_num
  have hJq : J((a : ℤ) | q) = -1 := by
    have : (a : ℤ) % (q : ℤ) = (c.val : ℤ) % (q : ℤ) := by exact_mod_cast hmq
    rw [jacobiSym.mod_left, this, ← jacobiSym.mod_left, ← jacobiSym.legendreSym.to_jacobiSym,
      legendreSym.eq_neg_one_iff]
    simpa using hc
  have hJd : J((a : ℤ) | d'') = 1 := by
    have : (a : ℤ) % (d'' : ℤ) = ((1 : ℕ) : ℤ) % (d'' : ℤ) := by exact_mod_cast hmd
    rw [jacobiSym.mod_left, this, ← jacobiSym.mod_left, Nat.cast_one, jacobiSym.one_left]
  rw [jacobiSym.mul_right, jacobiSym.mul_right, hJ3, hJq, hJd]
  norm_num

theorem prime_choice_recip (d p : ℕ) (hd4 : d % 4 = 3) (hp : Odd p) :
    J(-(d : ℤ) | p) = J((p : ℤ) | d) := by
  have hd : Odd d := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hp]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hd]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hd4 h]
    ring

theorem prime_choice_lift (d p s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hd0 : 0 < d) (hdp : d < p)
    (hs : p ∣ s ^ 2 + d) : ∃ r : ℕ, Even r ∧ p ∣ r ^ 2 + d ∧ ¬ p ^ 2 ∣ r ^ 2 + d := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨r0, hr0e, hr0⟩ : ∃ r0 : ℕ, Even r0 ∧ p ∣ r0 ^ 2 + d := by
    rcases Nat.even_or_odd s with he | ho
    · exact ⟨s, he, hs⟩
    · refine ⟨s + p, ho.add_odd hpodd, ?_⟩
      have e : (s + p) ^ 2 + d = (s ^ 2 + d) + p * (2 * s + p) := by ring
      rw [e]
      exact dvd_add hs (dvd_mul_right _ _)
  have hndvd : ¬ p ∣ r0 := by
    intro h
    have h2 : p ∣ r0 ^ 2 := dvd_pow h two_ne_zero
    have hpd : p ∣ d := (Nat.dvd_add_right h2).mp hr0
    have := Nat.le_of_dvd hd0 hpd
    omega
  by_cases hsq : p ^ 2 ∣ r0 ^ 2 + d
  ·
    refine ⟨r0 + 2 * p, hr0e.add (even_two_mul p), ?_, ?_⟩
    · have e : (r0 + 2 * p) ^ 2 + d = (r0 ^ 2 + d) + p * (4 * r0 + 4 * p) := by ring
      rw [e]
      exact dvd_add hr0 (dvd_mul_right _ _)
    · intro h
      have e : (r0 + 2 * p) ^ 2 + d = (r0 ^ 2 + d) + p ^ 2 * 4 + p * (4 * r0) := by ring
      rw [e] at h
      have h1 : p ^ 2 ∣ p * (4 * r0) := (Nat.dvd_add_right (dvd_add hsq (dvd_mul_right _ _))).mp h
      rw [pow_two] at h1
      have h2 : p ∣ 4 * r0 := Nat.dvd_of_mul_dvd_mul_left hp.pos h1
      rcases (Nat.Prime.dvd_mul hp).mp h2 with h4 | h4
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)))
      · exact hndvd h4
  · exact ⟨r0, hr0e, hr0, hsq⟩

theorem prime_choice (d b : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (h3 : 3 ∣ d) (hd3 : d ≠ 3) :
    ∃ p r : ℕ, p.Prime ∧ b < p ∧ d < p ∧ p % 3 = 2 ∧ Even r ∧ p ∣ r ^ 2 + d ∧ ¬ p ^ 2 ∣ r ^ 2 + d := by
  obtain ⟨a, ha3, ha⟩ := prime_choice_class d hsq hd4 h3 hd3
  have hd0 : d ≠ 0 := by omega
  haveI : NeZero d := ⟨hd0⟩
  have hunit : IsUnit (a : ZMod d) := by
    rw [ZMod.isUnit_iff_coprime]
    by_contra hnc
    have h0 : J((a : ℤ) | d) = 0 := jacobiSym.eq_zero_iff.mpr ⟨hd0, by simpa [Int.gcd_natCast_natCast] using hnc⟩
    rw [ha] at h0
    exact one_ne_zero h0
  obtain ⟨p, hpgt, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (b + d)
  have hpd : p % d = a % d := (ZMod.natCast_eq_natCast_iff' p a d).mp hpa
  have hp3 : p % 3 = 2 := by
    rw [← Nat.mod_mod_of_dvd p h3, hpd, Nat.mod_mod_of_dvd a h3, ha3]
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hmod : (p : ℤ) % (d : ℤ) = (a : ℤ) % (d : ℤ) := by exact_mod_cast hpd
  have hJ : J(-(d : ℤ) | p) = 1 := by
    rw [prime_choice_recip d p hd4 hpodd, jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, ha]
  haveI := Fact.mk hp
  have hne : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have h1 : (d : ZMod p) = 0 := by
      push_cast at h0
      simpa using h0
    have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff d p).mp h1)
    omega
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hne] at hJ
  obtain ⟨x, hx⟩ := hJ
  have hs : p ∣ x.val ^ 2 + d := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast at hx ⊢
    rw [ZMod.natCast_zmod_val]
    linear_combination -hx
  obtain ⟨r, hr1, hr2, hr3⟩ := prime_choice_lift d p x.val hp (by omega) (by omega) (by omega) hs
  exact ⟨p, r, hp, by omega, by omega, hp3, hr1, hr2, hr3⟩

end ReciprocityTheory.ChartRestriction.L1
end
