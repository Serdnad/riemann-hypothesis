module

public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.Ar.LocalisedSmooth

def denomMonoid {R : Type} [CommRing R] (c : R) : Submonoid R where
  carrier := {x | ∃ n k : ℕ, n ≠ 0 ∧ x = (n : R) * c ^ k}
  one_mem' := ⟨1, 0, one_ne_zero, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, k, hn, rfl⟩ ⟨m, l, hm, rfl⟩
    exact ⟨n * m, k + l, mul_ne_zero hn hm, by push_cast; ring⟩

theorem map_denomMonoid {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (c : R) :
    (denomMonoid c).map f = denomMonoid (f c) := by
  ext x
  constructor
  · rintro ⟨_, ⟨n, k, hn, rfl⟩, rfl⟩
    exact ⟨n, k, hn, by simp⟩
  · rintro ⟨n, k, hn, rfl⟩
    exact ⟨_, ⟨n, k, hn, rfl⟩, by simp⟩

theorem exists_nat_mul_mem {Ω : Type} [Field Ω] [CharZero Ω] (A : Subalgebra ℤ Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (A : Set Ω)) : ∃ N : ℕ, N ≠ 0 ∧ (N : Ω) * x ∈ A := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_nz, ?_⟩
    have : (r.den : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [this]
    exact intCast_mem A _
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (x + y) = (m : Ω) * ((n : Ω) * x) + (n : Ω) * ((m : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem A _) hnx) (mul_mem (natCast_mem A _) hmy)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (x * y) = ((n : Ω) * x) * ((m : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact mul_mem hnx hmy

theorem isLocalization_adjoin {Ω : Type} [Field Ω] [CharZero Ω] (A : Subalgebra ℤ Ω)
    (S : Subalgebra ℚ Ω) [Algebra A S] (hι : ∀ a : A, ((algebraMap A S a : S) : Ω) = a)
    (c : A) (N : ℕ) (hN : N ≠ 0) (h : Ω) (h0 : h ≠ 0) (hc : (c : Ω) = N * h)
    (hS : S = Algebra.adjoin ℚ (insert h⁻¹ (A : Set Ω))) :
    IsLocalization (denomMonoid c) S := by
  have hNΩ : (N : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hinv : h⁻¹ ∈ S := hS ▸ Algebra.subset_adjoin (Set.mem_insert _ _)
  have hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (algebraMap A S (n : A)) := by
    intro n hn
    have hnΩ : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
    refine IsUnit.of_mul_eq_one (algebraMap ℚ S (n : ℚ)⁻¹) (Subtype.ext ?_)
    have h1 : ((algebraMap ℚ S (n : ℚ)⁻¹ : S) : Ω) = (n : Ω)⁻¹ := by
      change algebraMap ℚ Ω (n : ℚ)⁻¹ = _
      simp
    rw [Subalgebra.coe_mul, hι, h1]
    simp [hnΩ]
  have hcu : IsUnit (algebraMap A S c) := by
    refine IsUnit.of_mul_eq_one (algebraMap ℚ S (N : ℚ)⁻¹ * ⟨h⁻¹, hinv⟩) (Subtype.ext ?_)
    have h1 : ((algebraMap ℚ S (N : ℚ)⁻¹ : S) : Ω) = (N : Ω)⁻¹ := by
      change algebraMap ℚ Ω (N : ℚ)⁻¹ = _
      simp
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, hι, h1, hc]
    simp only [Subalgebra.coe_one]
    field_simp
  have hcmem : c ∈ denomMonoid c := ⟨1, 1, one_ne_zero, by simp⟩
  have hnmem : ∀ n : ℕ, n ≠ 0 → (n : A) ∈ denomMonoid c := fun n hn => ⟨n, 0, hn, by simp⟩
  have key : ∀ w ∈ Algebra.adjoin ℚ (insert h⁻¹ (A : Set Ω)),
      ∃ (a : A) (m : denomMonoid c), w * (((m : A)) : Ω) = a := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · refine ⟨(N : A), ⟨c, hcmem⟩, ?_⟩
        simp only [hc]
        push_cast
        field_simp
      · exact ⟨⟨x, hx⟩, 1, by simp⟩
    | algebraMap r =>
      refine ⟨(r.num : A), ⟨(r.den : A), hnmem _ r.den_nz⟩, ?_⟩
      have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
      push_cast
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    | add x y _ _ hx hy =>
      obtain ⟨a, m, hx⟩ := hx
      obtain ⟨b, l, hy⟩ := hy
      refine ⟨a * (l : A) + b * (m : A), m * l, ?_⟩
      push_cast
      rw [← hx, ← hy]
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨a, m, hx⟩ := hx
      obtain ⟨b, l, hy⟩ := hy
      refine ⟨a * b, m * l, ?_⟩
      push_cast
      rw [← hx, ← hy]
      ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, k, hn, rfl⟩
    simp only [map_mul, map_pow]
    exact (hnat n hn).mul (hcu.pow k)
  · intro z
    obtain ⟨a, m, hz⟩ := key z (hS ▸ z.2)
    refine ⟨(a, m), Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hι, hι]
    exact hz
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : Ω) = y := by rw [← hι, ← hι, hxy]
    rw [Subtype.ext this]

end GlobalTheory.CompanionTheory.Ar.LocalisedSmooth


open GlobalTheory.CompanionTheory.Ar.LocalisedSmooth in
theorem GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised
    (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    (A₀ : Subalgebra ℤ Ω₀) (A₁ : Subalgebra ℤ Ω) (φ : A₀ →+* A₁)
    (hφ : ∀ a, ((φ a : A₁) : Ω) = algebraMap Ω₀ Ω a) (hsm : φ.Smooth)
    (h : Ω₀) (hh : h ∈ Algebra.adjoin ℚ (A₀ : Set Ω₀)) (h0 : h ≠ 0)
    (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω)
    (hS : S = Algebra.adjoin ℚ (insert h⁻¹ (A₀ : Set Ω₀)))
    (hT : T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (A₁ : Set Ω))) :
    ∃ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) ∧ ψ.Smooth := by
  obtain ⟨N, hN, hNh⟩ := exists_nat_mul_mem A₀ hh
  let c₀ : A₀ := ⟨(N : Ω₀) * h, hNh⟩
  have hc₀ : (c₀ : Ω₀) = N * h := rfl
  have hc₁ : ((φ c₀ : A₁) : Ω) = N * algebraMap Ω₀ Ω h := by
    rw [hφ, hc₀, map_mul, map_natCast]
  have hAS : ∀ a : A₀, (a : Ω₀) ∈ S := fun a =>
    hS ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ a.2)
  have hAT : ∀ a : A₁, (a : Ω) ∈ T := fun a =>
    hT ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ a.2)
  let ι₀ : A₀ →+* S := (A₀.val : A₀ →+* Ω₀).codRestrict S.toSubsemiring hAS
  let ι₁ : A₁ →+* T := (A₁.val : A₁ →+* Ω).codRestrict T.toSubsemiring hAT
  letI : Algebra A₀ S := ι₀.toAlgebra
  letI : Algebra A₁ T := ι₁.toAlgebra
  haveI L₀ : IsLocalization (denomMonoid c₀) S :=
    isLocalization_adjoin A₀ S (fun _ => rfl) c₀ N hN h h0 hc₀ hS
  haveI L₁ : IsLocalization (denomMonoid (φ c₀)) T :=
    isLocalization_adjoin A₁ T (fun _ => rfl) (φ c₀) N hN (algebraMap Ω₀ Ω h)
      ((map_ne_zero _).2 h0) hc₁ hT
  have hle : denomMonoid c₀ ≤ (denomMonoid (φ c₀)).comap φ := by
    intro x hx
    rw [Submonoid.mem_comap, ← map_denomMonoid]
    exact ⟨x, hx, rfl⟩
  let ψ : S →+* T := IsLocalization.map T φ hle
  have hψ : ∀ a : A₀, ψ (algebraMap A₀ S a) = algebraMap A₁ T (φ a) := fun a =>
    IsLocalization.map_eq hle a
  refine ⟨ψ, ?_, ?_⟩
  · have : ((T.val : T →+* Ω).comp ψ) = (algebraMap Ω₀ Ω).comp (S.val : S →+* Ω₀) := by
      refine IsLocalization.ringHom_ext (denomMonoid c₀) (RingHom.ext fun a => ?_)
      change ((ψ (algebraMap A₀ S a) : T) : Ω) = algebraMap Ω₀ Ω (a : Ω₀)
      rw [hψ]
      exact hφ a
    exact fun s => RingHom.congr_fun this s
  · letI : Algebra S T := ψ.toAlgebra
    letI : Algebra A₀ A₁ := φ.toAlgebra
    letI : Algebra A₀ T := ((algebraMap A₁ T).comp φ).toAlgebra
    haveI : IsScalarTower A₀ A₁ T := .of_algebraMap_eq' rfl
    haveI : IsScalarTower A₀ S T := .of_algebraMap_eq fun a => (hψ a).symm
    have hsub : Algebra.algebraMapSubmonoid A₁ (denomMonoid c₀) = denomMonoid (φ c₀) :=
      map_denomMonoid φ c₀
    haveI : IsLocalization (Algebra.algebraMapSubmonoid A₁ (denomMonoid c₀)) T := by
      rw [hsub]; exact L₁
    haveI P : Algebra.IsPushout A₀ A₁ S T :=
      Algebra.isPushout_of_isLocalization (denomMonoid c₀) S A₁ T
    exact RingHom.Smooth.isStableUnderBaseChange A₀ A₁ S T hsm
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem ep_inert : ∀ (p N j : ℕ), 2 ≤ p → j ≤ N → HasSum (fun n : ℕ => (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1)) ((j : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ |((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)| ≤ N / ((p : ℝ) - 1) := by
  intro p N j hp hjN
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hjN' : (j : ℝ) ≤ N := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpsq : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp0' : (p : ℝ) ≠ 0 := hp0.ne'
  have hp1' : (p : ℝ) - 1 ≠ 0 := hp1.ne'
  have hpsq' : (p : ℝ) ^ 2 - 1 ≠ 0 := hpsq.ne'
  refine ⟨?_, ?_⟩
  · have hr1 : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    have hg := hasSum_geometric_of_lt_one (by positivity) hr1
    have hE : HasSum (fun k : ℕ => (if Even (2 * k + 1) then (j : ℝ) else (N : ℝ) - j) /
        (p : ℝ) ^ (2 * k + 1)) (((N : ℝ) - j) / p * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) := by
      have hf : (fun k : ℕ => (if Even (2 * k + 1) then (j : ℝ) else (N : ℝ) - j) /
          (p : ℝ) ^ (2 * k + 1)) = fun k => ((N : ℝ) - j) / p * ((p : ℝ) ^ 2)⁻¹ ^ k := by
        funext k
        rw [if_neg (Nat.not_even_two_mul_add_one k), inv_pow, ← pow_mul, pow_succ,
          ← div_eq_mul_inv, div_div, mul_comm ((p : ℝ) ^ (2 * k)) (p : ℝ)]
      rw [hf]
      exact hg.mul_left _
    have hO : HasSum (fun k : ℕ => (if Even (2 * k + 1 + 1) then (j : ℝ) else (N : ℝ) - j) /
        (p : ℝ) ^ (2 * k + 1 + 1)) ((j : ℝ) / (p : ℝ) ^ 2 * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) := by
      have hf : (fun k : ℕ => (if Even (2 * k + 1 + 1) then (j : ℝ) else (N : ℝ) - j) /
          (p : ℝ) ^ (2 * k + 1 + 1)) = fun k => (j : ℝ) / (p : ℝ) ^ 2 * ((p : ℝ) ^ 2)⁻¹ ^ k := by
        funext k
        rw [if_pos ⟨k + 1, by ring⟩, inv_pow, ← pow_mul, ← div_eq_mul_inv, div_div, ← pow_add,
          show 2 * k + 1 + 1 = 2 + 2 * k by ring]
      rw [hf]
      exact hg.mul_left _
    have h := HasSum.even_add_odd (f := fun n : ℕ =>
      (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1)) hE hO
    have hinv : (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ = (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) := by
      rw [show (1 : ℝ) - ((p : ℝ) ^ 2)⁻¹ = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 by
        rw [sub_div, div_self (pow_ne_zero 2 hp0'), one_div], inv_div]
    have hv : (j : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1) =
        ((N : ℝ) - j) / p * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ + (j : ℝ) / (p : ℝ) ^ 2 * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
      rw [hinv]
      field_simp
      ring
    rw [hv]
    exact h
  · have hA : |(N : ℝ) - 2 * j| ≤ N := abs_le.2 ⟨by linarith, by linarith⟩
    rw [abs_div, abs_mul, abs_of_pos hp0, abs_of_pos hpsq, div_le_div_iff₀ hpsq hp1]
    nlinarith [abs_nonneg ((N : ℝ) - 2 * j),
      mul_le_mul_of_nonneg_right hA (by nlinarith : (0 : ℝ) ≤ p * (p - 1)),
      mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hp1.le]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem ep_split : ∀ (p j : ℕ), 2 ≤ p →
    HasSum (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) ((j : ℝ) / ((p : ℝ) - 1)) := by
  intro p j hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (p : ℝ) ≠ 0 := by positivity
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hr : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left ((j : ℝ) / p)
  have hf : (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) =
      fun n : ℕ => (j : ℝ) / p * (1 / (p : ℝ)) ^ n := by
    funext n
    rw [one_div_pow, pow_succ]
    field_simp
  have hv : (j : ℝ) / ((p : ℝ) - 1) = (j : ℝ) / p * (1 - 1 / (p : ℝ))⁻¹ := by
    rw [one_sub_div h0, inv_div]
    field_simp
  rw [hf, hv]
  exact hs

end GlobalTheory.CompanionTheory.Ar.Flat
end
