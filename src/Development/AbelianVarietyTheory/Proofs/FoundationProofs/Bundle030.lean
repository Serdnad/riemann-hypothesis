module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.K5

namespace GlobalTheory.K5.Span

theorem sum_range_shift_one {A : Type*} [AddCommGroup A] {M : ℕ} (f : ℕ → A)
    (hf : ∀ i, f (i + M) = f i) :
    ∑ i ∈ Finset.range M, f (i + 1) = ∑ i ∈ Finset.range M, f i := by
  have h1 := Finset.sum_range_succ' f M
  have h2 := Finset.sum_range_succ f M
  have h3 : f M = f 0 := by simpa using hf 0
  rw [h3] at h2
  exact add_right_cancel (h1.symm.trans h2)

theorem sum_range_shift {A : Type*} [AddCommGroup A] {M : ℕ} (f : ℕ → A)
    (hf : ∀ i, f (i + M) = f i) (s : ℕ) :
    ∑ i ∈ Finset.range M, f (i + s) = ∑ i ∈ Finset.range M, f i := by
  induction s generalizing f with
  | zero => simp
  | succ s ih =>
    have := sum_range_shift_one (fun i => f (i + s)) (fun i => by
      show f (i + M + s) = f (i + s)
      rw [add_right_comm, hf])
    rw [← ih f hf, ← this]
    exact Finset.sum_congr rfl fun i _ => by congr 1; omega

theorem span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo (p := p) Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  intro p _ Ω _ _ hΩ T τ hτ hτq N z hz
  haveI : CharZero Ω := charZero_of_injective_algebraMap hΩ.inj
  have hprim : IsPrimitiveRoot (T.ζ N) (p ^ N) := T.prim N
  have hMpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have hq0 : T.qq N ≠ 0 := Basic.qq_ne_zero T N
  have hqpow : T.qq N ^ p ^ N = algebraMap (O0 p) Ω (qO p) := Basic.qq_pow T N
  have hτqN := hτq N
  set M := p ^ N with hMdef
  set ζ := T.ζ N with hζdef
  set q := T.qq N with hqdef
  have hM0 : (M : Ω) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hζ0 : ζ ≠ 0 := hprim.ne_zero hMpos.ne'

  have hζalg : IsAlgZp (p := p) ζ := by
    refine ⟨Polynomial.X ^ M - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero hMpos 1, ?_⟩
    simp [hprim.pow_eq_one]
  have hfixζ : ∀ g ∈ Ggeo (p := p) Ω, g ζ = ζ := fun g hg => hg ζ hζalg
  have hτpow : ∀ i : ℕ, (τ ^ i) q = ζ ^ i * q := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hfixζ τ hτ, hτqN, pow_succ']
      ring
  have hτG : ∀ i : ℕ, τ ^ i ∈ Ggeo (p := p) Ω := fun i => Subgroup.pow_mem _ hτ i
  have hconj : ∀ g ∈ Ggeo (p := p) Ω, g q = q → ∀ i : ℕ, g ((τ ^ i) z) = (τ ^ i) z := by
    intro g hg hgq i
    have hk : (τ ^ i)⁻¹ * g * τ ^ i ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) q := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hτG i)) hg)
        (hτG i), MulAction.mem_stabilizer_iff.2 ?_⟩
      show ((τ ^ i)⁻¹ * g * τ ^ i) q = q
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτpow, map_mul, map_pow, hfixζ g hg, hgq, ← hτpow,
        AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    have hkz := hz _ hk
    have e : τ ^ i * ((τ ^ i)⁻¹ * g * τ ^ i) = g * τ ^ i := by group
    calc g ((τ ^ i) z) = (g * τ ^ i) z := rfl
      _ = (τ ^ i * ((τ ^ i)⁻¹ * g * τ ^ i)) z := by rw [e]
      _ = (τ ^ i) (((τ ^ i)⁻¹ * g * τ ^ i) z) := rfl
      _ = (τ ^ i) z := by rw [hkz]
  have hdec : ∀ g ∈ Ggeo (p := p) Ω, ∃ s : ℕ, g q = ζ ^ s * q ∧ ∀ i : ℕ, g ((τ ^ i) z) = (τ ^ (s + i)) z := by
    intro g hg
    have h1 : (g q / q) ^ M = 1 := by
      rw [div_pow, ← map_pow, hqpow, AlgEquiv.commutes, ← hqpow, div_self (pow_ne_zero _ hq0)]
    obtain ⟨s, -, hse⟩ := hprim.eq_pow_of_pow_eq_one h1
    have hgq : g q = ζ ^ s * q := by rw [hse, div_mul_cancel₀ _ hq0]
    refine ⟨s, hgq, fun i => ?_⟩
    have hh : (τ ^ s)⁻¹ * g ∈ Ggeo (p := p) Ω := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hτG s)) hg
    have hhq : ((τ ^ s)⁻¹ * g) q = q := by
      rw [AlgEquiv.mul_apply, hgq, ← hτpow, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    have e : g = τ ^ s * ((τ ^ s)⁻¹ * g) := by group
    rw [e, AlgEquiv.mul_apply, hconj _ hh hhq i, ← AlgEquiv.mul_apply, ← pow_add]

  have hτMz : (τ ^ M) z = z := by
    refine hz _ (Subgroup.mem_inf.2 ⟨hτG M, MulAction.mem_stabilizer_iff.2 ?_⟩)
    show (τ ^ M) q = q
    rw [hτpow, hprim.pow_eq_one, one_mul]
  set η := ζ⁻¹ with hηdef
  have hηprim : IsPrimitiveRoot η M := hprim.inv
  have hfixη : ∀ g ∈ Ggeo (p := p) Ω, g η = η := by
    intro g hg; rw [hηdef, map_inv₀, hfixζ g hg]
  obtain ⟨P, hP⟩ : ∃ P : ℕ → Ω, ∀ j,
      P j = (M : Ω)⁻¹ * ∑ i ∈ Finset.range M, η ^ (i * j) * (τ ^ i) z := ⟨_, fun _ => rfl⟩
  have hgP : ∀ g ∈ Ggeo (p := p) Ω, ∀ s : ℕ, (∀ i : ℕ, g ((τ ^ i) z) = (τ ^ (s + i)) z) →
      ∀ j, g (P j) = ζ ^ (s * j) * P j := by
    intro g hg s hs j

    rw [hP, map_mul, map_inv₀, map_natCast, map_sum]
    have hper : ∀ i, (fun i => η ^ (i * j) * (τ ^ i) z) (i + M) = (fun i => η ^ (i * j) * (τ ^ i) z) i := by
      intro i
      show η ^ ((i + M) * j) * (τ ^ (i + M)) z = η ^ (i * j) * (τ ^ i) z
      rw [add_mul, pow_add, show η ^ (M * j) = 1 by rw [pow_mul, hηprim.pow_eq_one, one_pow],
        mul_one, pow_add, AlgEquiv.mul_apply, hτMz]
    have hsh := sum_range_shift (M := M) (fun i => η ^ (i * j) * (τ ^ i) z) hper s
    rw [← hsh, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hfixη g hg, hs, add_comm s i]
    have hζη : ζ ^ (s * j) * η ^ (s * j) = 1 := by
      rw [← mul_pow, hηdef, mul_inv_cancel₀ hζ0, one_pow]
    calc (M : Ω)⁻¹ * (η ^ (i * j) * (τ ^ (i + s)) z)
        = (M : Ω)⁻¹ * ((ζ ^ (s * j) * η ^ (s * j)) * η ^ (i * j) * (τ ^ (i + s)) z) := by
          rw [hζη, one_mul]
      _ = ζ ^ (s * j) * ((M : Ω)⁻¹ * (η ^ ((i + s) * j) * (τ ^ (i + s)) z)) := by
          rw [add_mul, pow_add]; ring
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Ω, ∀ j, c j = P j / q ^ j := ⟨_, fun _ => rfl⟩
  refine ⟨c, ?_, ?_⟩
  · intro j g hg
    obtain ⟨s, hgq, hs⟩ := hdec g hg
    rw [hc, map_div₀, map_pow, hgq, hgP g hg s hs j, mul_pow, ← pow_mul,
      mul_div_mul_left _ _ (pow_ne_zero _ hζ0)]
  · have hgeom : ∀ i ∈ Finset.range M,
        ∑ j ∈ Finset.range M, η ^ (i * j) = if i = 0 then (M : Ω) else 0 := by
      intro i hi
      split_ifs with h0
      · simp [h0]
      · have hne : η ^ i ≠ 1 :=
          hηprim.pow_ne_one_of_pos_of_lt h0 (Finset.mem_range.1 hi)
        simp_rw [pow_mul]
        rw [geom_sum_eq hne, pow_right_comm, hηprim.pow_eq_one, one_pow, sub_self, zero_div]
    have e1 : ∑ i ∈ Finset.range M, (∑ j ∈ Finset.range M, η ^ (i * j)) * (τ ^ i) z =
        ∑ i ∈ Finset.range M, (if i = 0 then (M : Ω) else 0) * (τ ^ i) z :=
      Finset.sum_congr rfl fun i hi => by rw [hgeom i hi]
    calc z = (M : Ω)⁻¹ * ∑ i ∈ Finset.range M, (∑ j ∈ Finset.range M, η ^ (i * j)) * (τ ^ i) z := by
          rw [e1, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hMpos) (fun b _ hb => by simp [hb])]
          simp [hM0]
      _ = ∑ j ∈ Finset.range M, P j := by
          simp only [hP]
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ = ∑ j ∈ Finset.range M, c j * q ^ j :=
          Finset.sum_congr rfl fun j _ => by rw [hc, div_mul_cancel₀ _ (pow_ne_zero j hq0)]

end GlobalTheory.K5.Span
end

section

open GlobalTheory.K5

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem charZero_of_tower (T : Tower p Ω) : CharZero Ω := by
  have hpp : p.Prime := Fact.out
  have hp : (p : Ω) ≠ 0 := by
    intro h0
    haveI : CharP Ω p := (CharP.charP_iff_prime_eq_zero hpp).mpr h0
    have hz := T.prim 1
    rw [pow_one] at hz
    have h1 : (T.ζ 1 - 1) ^ p = 0 := by rw [sub_pow_char, one_pow, hz.pow_eq_one, sub_self]
    have h2 : T.ζ 1 = 1 := sub_eq_zero.mp (pow_eq_zero_iff hpp.ne_zero |>.mp h1)
    rw [h2] at hz
    exact hpp.one_lt.ne' (hz.eq_orderOf.trans orderOf_one)
  let f : ℤ_[p] →+* Ω :=
    (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp (algebraMap ℤ_[p] (Lau p)))
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hpp.one_lt.ne'
  have hu : IsUnit (((m : ℤ) : ℤ_[p])) := by
    refine PadicInt.isUnit_iff.mpr (le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hm ?_))
    exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp h)
  have hmu : IsUnit (m : Ω) := by
    have := hu.map f
    simpa using this
  push_cast at hn
  rcases mul_eq_zero.mp hn with h | h
  · exact hp (pow_eq_zero_iff' |>.mp h).1
  · exact hmu.ne_zero h

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem qq_eq_pow (T : Tower p Ω) (i d : ℕ) : T.qq i = T.qq (i + d) ^ (p ^ d) := by
  induction d with
  | zero => simp
  | succ d ih => rw [ih, ← T.qpow (i + d), ← pow_mul, ← pow_succ', add_assoc]

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem sum_fixed (H : Subgroup (Gal p Ω)) (E : Finset (Gal p Ω)) (y₀ x : Ω)
    (hEH : ∀ g ∈ E, g ∈ H)
    (huniq : ∀ h ∈ H, ∃! g, g ∈ E ∧ h y₀ = g y₀ ∧ ∀ s ∈ ({x} : Finset Ω), h s = g s) :
    ∀ h ∈ H, h (∑ g ∈ E, g (y₀ * x)) = ∑ g ∈ E, g (y₀ * x) := by
  classical
  simp only [Finset.mem_singleton, forall_eq] at huniq
  let rep : Gal p Ω → Gal p Ω := fun a => if ha : a ∈ H then (huniq a ha).exists.choose else 1
  have hrep : ∀ a ∈ H, rep a ∈ E ∧ a y₀ = rep a y₀ ∧ a x = rep a x := by
    intro a ha
    simp only [rep, dif_pos ha]
    exact (huniq a ha).exists.choose_spec
  have hun : ∀ a ∈ H, ∀ g ∈ E, a y₀ = g y₀ → a x = g x → rep a = g := by
    intro a ha g hg h1 h2
    exact ((huniq a ha).unique (hrep a ha) ⟨hg, h1, h2⟩)
  intro h hh

  rw [map_sum]
  have hmem : ∀ g ∈ E, h * g ∈ H := fun g hg => H.mul_mem hh (hEH g hg)
  have hmem' : ∀ g ∈ E, h⁻¹ * g ∈ H := fun g hg => H.mul_mem (H.inv_mem hh) (hEH g hg)
  refine Finset.sum_bij' (fun g _ => rep (h * g)) (fun g _ => rep (h⁻¹ * g))
    (fun g hg => (hrep _ (hmem g hg)).1) (fun g hg => (hrep _ (hmem' g hg)).1) ?_ ?_ ?_
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem g hg)
    refine hun _ (hmem' _ (hrep _ (hmem g hg)).1) g hg ?_ ?_
    · rw [AlgEquiv.mul_apply, ← h1, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem' g hg)
    refine hun _ (hmem _ (hrep _ (hmem' g hg)).1) g hg ?_ ?_
    · rw [AlgEquiv.mul_apply, ← h1, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem g hg)
    show (h * g) (y₀ * x) = _
    rw [map_mul, map_mul (rep (h * g)), h1, h2]

end GlobalTheory.K5.FinLevel
end

section

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.DerAlg

open Polynomial

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

abbrev phiZ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] : ℤ_[p] →+* Ω :=
  (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))

theorem phiZ_injective [CharZero Ω] : Function.Injective (phiZ p Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hc
  have hu : IsUnit (phiZ p Ω (PadicInt.unitCoeff h0 : ℤ_[p])) :=
    (Units.isUnit _).map _
  have hp : ((p : Ω)) ^ c.valuation ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  exact mul_ne_zero hu.ne_zero hp hc

theorem der_eval₂ (E : Derivation ℤ Ω Ω)
    (hE : ∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0)
    (x : Ω) (Q : ℤ_[p][X]) :
    E (eval₂ (phiZ p Ω) x Q) = eval₂ (phiZ p Ω) x (derivative Q) * E x := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [eval₂_add, map_add (f := _), hP, hQ, derivative_add, eval₂_add, add_mul]
  | monomial n c =>
    have hc : E (phiZ p Ω c) = 0 := hE c
    rw [eval₂_monomial, Derivation.leibniz, Derivation.leibniz_pow, hc, smul_zero, add_zero,
      derivative_monomial, eval₂_monomial]
    simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring

theorem der_algZp : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ E : Derivation ℤ Ω Ω, (∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0) →
    ∀ x : Ω, IsAlgZp (p := p) x → E x = 0 := by
  intro p _ Ω _ _ hC E hE x hx
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hC
  obtain ⟨P, hP0, hPx⟩ := hx
  rw [aeval_def, eval₂_map] at hPx
  change eval₂ (phiZ p Ω) x P = 0 at hPx
  by_contra hEx
  have key : ∀ n, ∀ P : ℤ_[p][X], P.natDegree = n → P ≠ 0 → eval₂ (phiZ p Ω) x P ≠ 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P hn hP hzero
      by_cases hd : P.natDegree = 0
      · rw [eq_C_of_natDegree_eq_zero hd, eval₂_C] at hzero
        have := phiZ_injective (p := p) (Ω := Ω) (hzero.trans (map_zero _).symm)
        exact hP (by rw [eq_C_of_natDegree_eq_zero hd, this, C_0])
      · have hD : derivative P ≠ 0 := fun h => hd (natDegree_eq_zero_of_derivative_eq_zero h)
        have hlt := natDegree_derivative_lt hd
        refine ih _ (hn ▸ hlt) (derivative P) rfl hD ?_
        have h1 := der_eval₂ E hE x P
        rw [hzero, map_zero] at h1
        exact (mul_eq_zero.1 h1.symm).resolve_right hEx
  exact key _ P rfl hP0 hPx

end GlobalTheory.K5.DerAlg
end
end

section

noncomputable section

namespace GlobalTheory.K5.ReprSpan

open Polynomial

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isAlgZp_one : IsAlgZp (p := p) (1 : Ω) :=
  ⟨X - C 1, X_sub_C_ne_zero 1, by simp⟩

theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp (p := p) x) (hy : IsAlgZp (p := p) y) :
    IsAlgZp (p := p) (x * y) := by
  let : Algebra ℤ_[p] Ω := Algebra.compHom Ω (algebraMap ℤ_[p] (O0 p))
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ z : Ω, IsAlgZp (p := p) z ↔ IsAlgebraic ℤ_[p] z := fun z => by
    simp only [IsAlgZp, IsAlgebraic, aeval_map_algebraMap]
  rw [key] at hx hy ⊢
  exact hx.mul hy


variable (p Ω) in
def algZpMonoid : Submonoid Ω where
  carrier := {x | IsAlgZp (p := p) x}
  one_mem' := isAlgZp_one
  mul_mem' := isAlgZp_mul

theorem mem_adjoin_iff (z : Ω) :
    z ∈ Algebra.adjoin (O0 p) {x : Ω | IsAlgZp (p := p) x} ↔
      z ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x} := by
  rw [← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span]
  have hcl : (Submonoid.closure {x : Ω | IsAlgZp (p := p) x} : Set Ω) = {x | IsAlgZp (p := p) x} := by
    rw [show {x : Ω | IsAlgZp (p := p) x} = (algZpMonoid (p := p) (Ω := Ω) : Set Ω) from rfl,
      Submonoid.closure_eq]
  rw [hcl]

theorem exists_mul_mem_span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x}),
    ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x} := by
  intro p _ Ω _ _ h b hb
  set B := Algebra.adjoin (O0 p) {x : Ω | IsAlgZp (p := p) x} with hBdef
  let S : Subfield Ω :=
    { carrier := {b | ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ B}
      zero_mem' := ⟨1, one_ne_zero, by rw [mul_zero]; exact B.zero_mem⟩
      one_mem' := ⟨1, one_ne_zero, by rw [map_one, mul_one]; exact B.one_mem⟩
      add_mem' := by
        rintro a c ⟨g, hg, ha⟩ ⟨g', hg', hc⟩
        refine ⟨g * g', mul_ne_zero hg hg', ?_⟩
        have e : algebraMap (O0 p) Ω (g * g') * (a + c) =
            algebraMap (O0 p) Ω g' * (algebraMap (O0 p) Ω g * a) +
              algebraMap (O0 p) Ω g * (algebraMap (O0 p) Ω g' * c) := by
          rw [map_mul]; ring
        rw [e]
        exact B.add_mem (B.mul_mem (B.algebraMap_mem _) ha) (B.mul_mem (B.algebraMap_mem _) hc)
      mul_mem' := by
        rintro a c ⟨g, hg, ha⟩ ⟨g', hg', hc⟩
        refine ⟨g * g', mul_ne_zero hg hg', ?_⟩
        have e : algebraMap (O0 p) Ω (g * g') * (a * c) =
            (algebraMap (O0 p) Ω g * a) * (algebraMap (O0 p) Ω g' * c) := by
          rw [map_mul]; ring
        rw [e]
        exact B.mul_mem ha hc
      neg_mem' := by
        rintro a ⟨g, hg, ha⟩
        exact ⟨g, hg, by rw [mul_neg]; exact B.neg_mem ha⟩
      inv_mem' := by
        rintro a ⟨g, hg, ha⟩
        by_cases ha0 : a = 0
        · exact ⟨1, one_ne_zero, by rw [ha0, inv_zero, mul_zero]; exact B.zero_mem⟩
        have hg0 : algebraMap (O0 p) Ω g ≠ 0 := fun e => hg (h.inj (by rw [e, map_zero]))
        have hy0 : algebraMap (O0 p) Ω g * a ≠ 0 := mul_ne_zero hg0 ha0
        let y : B := ⟨algebraMap (O0 p) Ω g * a, ha⟩
        have halg : IsAlgebraic (O0 p) y :=
          (isAlgebraic_algHom_iff B.val Subtype.val_injective).1 (h.alg.isAlgebraic _)
        have hnz : y ∈ nonZeroDivisors B :=
          mem_nonZeroDivisors_of_ne_zero (fun e => hy0 (congrArg Subtype.val e))
        obtain ⟨r, hr, s, hs⟩ := halg.exists_ne_zero_dvd hnz
        have hs' : algebraMap (O0 p) Ω r = algebraMap (O0 p) Ω g * a * (s : Ω) := by
          have := congrArg Subtype.val hs
          simpa [y] using this
        refine ⟨r, hr, ?_⟩
        have e : algebraMap (O0 p) Ω r * a⁻¹ = algebraMap (O0 p) Ω g * (s : Ω) := by
          rw [hs']; field_simp
        show algebraMap (O0 p) Ω r * a⁻¹ ∈ B
        rw [e]
        exact B.mul_mem (B.algebraMap_mem g) s.2 }
  have hle : Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x}) ≤ S := by
    rw [Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · exact ⟨1, one_ne_zero, by rw [map_one, one_mul]; exact B.algebraMap_mem c⟩
    · exact ⟨1, one_ne_zero, by rw [map_one, one_mul]; exact Algebra.subset_adjoin hx⟩
  obtain ⟨g, hg, hgb⟩ := hle hb
  exact ⟨g, hg, (mem_adjoin_iff _).1 hgb⟩

end GlobalTheory.K5.ReprSpan
end
end

section

open GlobalTheory.K5 Polynomial

noncomputable section
namespace GlobalTheory.K5.DlogCoef

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

theorem smul_mk (J : Ideal (On p n)) (a b : On p n) :
    a • (Ideal.Quotient.mk J b) = Ideal.Quotient.mk J (a * b) := by
  first
  | rfl
  | exact (Submodule.Quotient.mk_smul _ _ _).symm
  | simp [Algebra.smul_def]

theorem deriv_pow (J : Ideal (On p n)) (D : Derivation (O0 p) (On p n) (On p n ⧸ J))
    (r c : On p n) (h : D r = Ideal.Quotient.mk J (c * r)) (i : ℕ) :
    D (r ^ i) = Ideal.Quotient.mk J ((i : On p n) * c * r ^ i) := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Derivation.leibniz, ih, h, smul_mk, smul_mk, ← (Ideal.Quotient.mk J).map_add]
    congr 1
    push_cast
    ring

end GlobalTheory.K5.DlogCoef
end
end
