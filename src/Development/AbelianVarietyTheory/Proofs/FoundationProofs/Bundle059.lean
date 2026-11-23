module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle027
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisFDistribution
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.InertKummer

theorem valuation_eq_one_of_mem {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {x : Ω} (hx : x ∈ B) (hx' : x⁻¹ ∈ B)
    (h0 : x ≠ 0) : B.valuation x = 1 := by
  have hu : IsUnit (⟨x, hx⟩ : B) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hx'⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  exact (B.valuation_eq_one_iff ⟨x, hx⟩).mp hu

theorem inert_fixes_adjoin_and_kum_eq : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ θ₀ : Ω, θ ≠ 0 → θ₀ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} → θ₀ ^ N ∈ Set.range (algebraMap K Ω) →
      ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
      ∀ g : Ω ≃ₐ[K] Ω, GlobalTheory.NeedB.Inert B g → ∀ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 →
        B.valuation (θ ^ N / (θ₀ ^ N * c ^ N)) = 1 →
        g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup ∧ GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum ζ θ₀ g := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ θ₀ hθ hθ₀ hθE hθ₀K B hB g hg c hcE hc0 hv
  haveI : NeZero N := ⟨hN.ne'⟩

  have hunit : ∀ x : K, x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 →
      B.valuation (algebraMap K Ω x) = 1 := by
    intro x hx hx' hx0
    refine valuation_eq_one_of_mem B (hB x hx) ?_ ((_root_.map_ne_zero _).mpr hx0)
    rw [← map_inv₀]; exact hB _ hx'

  have hNK0 : (N : K) ≠ 0 := by
    have : ((algebraMap k[X] K).comp Polynomial.C) (N : k) = (N : K) := map_natCast _ _
    rw [← this]; exact (_root_.map_ne_zero _).mpr (by exact_mod_cast hN.ne')
  have hNmem : (N : K) ∈ FunctionField.ringOfIntegers k K := Subalgebra.natCast_mem _ N
  have hNinv : (N : K)⁻¹ ∈ FunctionField.ringOfIntegers k K := by
    have : ((algebraMap k[X] K).comp Polynomial.C) ((N : k)⁻¹) = (N : K)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [← this]
    exact Subalgebra.algebraMap_mem _ _
  have hvN : B.valuation (N : Ω) = 1 := by
    have := hunit _ hNmem hNinv hNK0
    rwa [map_natCast] at this

  have hroot : ∀ (γ : Ω) (x : K), x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 →
      γ ^ N = algebraMap K Ω x → g γ = γ := by
    intro γ x hx hx' hx0 hγ
    refine GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N 1 γ hN hvN hg (map_one g) one_ne_zero ?_ ?_
    · rw [hγ]; exact g.commutes x
    · rw [one_pow, div_one, hγ]; exact hunit x hx hx' hx0
  have hgα : g α = α := hroot α a ha ha' ha0 hα
  have hgβ : g β = β := hroot β b hb hb' hb0 hβ
  have hfix : g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup := by
    have hz : Subgroup.zpowers g ≤ (IntermediateField.adjoin K {α, β}).fixingSubgroup := by
      rw [← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
      intro x hx
      have hgx : g x = x := by
        rcases hx with rfl | hx
        · exact hgα
        · rw [Set.mem_singleton_iff.mp hx]; exact hgβ
      have hs : g ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := hgx
      intro f
      have hf : (f : Ω ≃ₐ[K] Ω) ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := Subgroup.zpowers_le.mpr hs f.2
      exact hf
    exact hz (Subgroup.mem_zpowers g)
  have hfixE : ∀ x ∈ IntermediateField.adjoin K {α, β}, g x = x := fun x hx => hfix ⟨x, hx⟩
  refine ⟨hfix, ?_⟩

  have hgθN : g (θ ^ N) = θ ^ N := hfixE _ hθE
  have hgθ₀N : g (θ₀ ^ N) = θ₀ ^ N := by
    obtain ⟨y, hy⟩ := hθ₀K; rw [← hy]; exact g.commutes y
  have hq : g (θ / θ₀) = θ / θ₀ := by
    refine GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N c (θ / θ₀) hN hvN hg (hfixE c hcE) hc0 ?_ ?_
    · rw [div_pow, map_div₀, hgθN, hgθ₀N]
    · rw [div_pow, div_div]; exact hv
  have hq' : g θ₀ = g θ * θ₀ / θ := by
    rw [map_div₀] at hq
    have hgθ₀0 : g θ₀ ≠ 0 := (_root_.map_ne_zero g).mpr hθ₀
    rw [div_eq_div_iff hgθ₀0 hθ₀] at hq
    rw [eq_div_iff hθ, hq, mul_comm]

  have hξ : (g θ / θ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hgθN, div_self (pow_ne_zero _ hθ)]
  obtain ⟨i, hiN, hi⟩ := hζ.eq_pow_of_pow_eq_one hξ
  have hval : ((i : ZMod N)).val = i := ZMod.val_cast_of_lt hiN
  have h1 : g θ = ζ ^ ((i : ZMod N)).val * θ := by
    rw [hval, hi]; field_simp
  have h2 : g θ₀ = ζ ^ ((i : ZMod N)).val * θ₀ := by
    rw [hq', h1]; field_simp
  rw [kum_eq_of hζ hθ _ h1, kum_eq_of hζ hθ₀ _ h2]

end GlobalTheory.InertKummer
end

section

noncomputable section

open Finset GlobalTheory.KummerEisensteinGalois
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.RowFibre

theorem val_lift (p n : ℕ) [hp : Fact p.Prime] (x : ZMod (p ^ n)) (s : ℕ) (hs : s < p) :
    ((x.val + p ^ n * s : ℕ) : ZMod (p ^ (n + 1))).val = x.val + p ^ n * s := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  apply ZMod.val_cast_of_lt
  have hx := ZMod.val_lt x
  calc x.val + p ^ n * s < p ^ n + p ^ n * s := by omega
    _ = p ^ n * (s + 1) := by ring
    _ ≤ p ^ n * p := Nat.mul_le_mul_left _ hs
    _ = p ^ (n + 1) := by ring

theorem sum_lifts {α : Type*} [AddCommMonoid α] (p n : ℕ) [hp : Fact p.Prime] (x : ZMod (p ^ n))
    (f : ZMod (p ^ (n + 1)) → α) :
    ∑ y ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) =>
        ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x)), f y
      = ∑ s ∈ range p, f ((x.val + p ^ n * s : ℕ) : ZMod (p ^ (n + 1))) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hpos : 0 < p ^ n := pow_pos hp.out.pos n
  have hmem : ∀ y : ZMod (p ^ (n + 1)),
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x ↔ y.val % p ^ n = x.val := by
    intro y
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    constructor
    · rintro rfl; rw [ZMod.val_natCast]
    · intro h; rw [← ZMod.natCast_mod, h, ZMod.natCast_zmod_val]
  symm
  refine Finset.sum_nbij' (fun s => ((x.val + p ^ n * s : ℕ) : ZMod (p ^ (n + 1))))
    (fun y => y.val / p ^ n) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [mem_coe, mem_range, mem_filter, mem_univ, true_and] at hs ⊢
    rw [hmem, val_lift p n x s hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt x)]
  · intro y hy
    simp only [mem_coe, mem_range, mem_filter, mem_univ, true_and] at hy ⊢
    rw [Nat.div_lt_iff_lt_mul hpos]
    have := ZMod.val_lt y
    calc y.val < p ^ (n + 1) := this
      _ = p * p ^ n := by ring
  · intro s hs
    simp only [mem_coe, mem_range] at hs
    rw [val_lift p n x s hs, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (ZMod.val_lt x), zero_add]
  · intro y hy
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hy
    rw [hmem] at hy
    rw [← hy, Nat.mod_add_div, ZMod.natCast_zmod_val]
  · intro s _
    rfl

theorem sum_range_perm {α : Type*} [AddCommMonoid α] (p : ℕ) [hp : Fact p.Prime] (H : ℤ → α)
    (hH : ∀ t, H t = H (t % p)) (c e : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    ∑ s ∈ range p, H (c * ((s : ℤ) + e)) = ∑ k ∈ range p, H k := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set Hz : ZMod p → α := fun z => H (z.val : ℤ) with hHz
  have hHt : ∀ t : ℤ, H t = Hz (t : ZMod p) := by
    intro t; rw [hH t, hHz]; simp only [ZMod.val_intCast]
  have hr : ∀ f : ZMod p → α, ∑ s ∈ range p, f (s : ZMod p) = ∑ z, f z := by
    intro f
    refine Finset.sum_nbij' (fun s => (s : ZMod p)) (fun z => z.val) ?_ ?_ ?_ ?_ ?_
    · intros; simp
    · intro z _; simp [ZMod.val_lt]
    · intro s hs
      simp only [mem_coe, mem_range] at hs
      simp [ZMod.val_cast_of_lt hs]
    · intro z _; simp
    · intros; rfl
  have hcz : (c : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hbij : Function.Bijective (fun z : ZMod p => (c : ZMod p) * (z + e)) := by
    rw [← Finite.injective_iff_bijective]
    intro a b h
    simpa using mul_left_cancel₀ hcz h
  calc ∑ s ∈ range p, H (c * ((s : ℤ) + e))
        = ∑ s ∈ range p, Hz ((c : ZMod p) * ((s : ZMod p) + e)) := by
        refine sum_congr rfl fun s _ => ?_
        rw [hHt]; push_cast; rfl
    _ = ∑ z, Hz ((c : ZMod p) * (z + e)) := hr (fun z => Hz ((c : ZMod p) * (z + e)))
    _ = ∑ z, Hz z := Fintype.sum_bijective _ hbij _ _ (fun _ => rfl)
    _ = ∑ k ∈ range p, Hz (k : ZMod p) := (hr Hz).symm
    _ = ∑ k ∈ range p, H k := by
        refine sum_congr rfl fun k _ => ?_
        rw [hHt]; push_cast; rfl

theorem modEq_shift (p M : ℕ) (A t : ℤ) :
    A + (M : ℤ) * t ≡ A + (M : ℤ) * (t % p) [ZMOD ((p * M : ℕ) : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-(t / p), ?_⟩
  push_cast
  linear_combination (M : ℤ) * Int.emod_add_mul_ediv t p

theorem sum_perm2 {K : Type*} [Field K] [CharZero K] (p : ℕ) [hp : Fact p.Prime] (M j : ℕ) (hM : 0 < M)
    (ζ : K) (hζ : ζ ^ (p * M) = 1) (A₁ A₂ c e₁ e₂ : ℤ) (hc : ¬ (p : ℤ) ∣ c) (r : ℕ) :
    ∑ s₁ ∈ range p, ∑ s₂ ∈ range p,
        eisF j (p * M) ζ (A₁ + M * (c * ((s₁ : ℤ) + e₁))) (A₂ + M * (c * ((s₂ : ℤ) + e₂))) r
      = ∑ i₁ ∈ range p, ∑ i₂ ∈ range p, eisF j (p * M) ζ (A₁ + M * i₁) (A₂ + M * i₂) r := by
  have hL : 0 < p * M := Nat.mul_pos hp.out.pos hM
  have inner : ∀ a : ℤ, ∑ s₂ ∈ range p, eisF j (p * M) ζ a (A₂ + M * (c * ((s₂ : ℤ) + e₂))) r
      = ∑ i₂ ∈ range p, eisF j (p * M) ζ a (A₂ + M * i₂) r := by
    intro a
    exact sum_range_perm p (fun t => eisF j (p * M) ζ a (A₂ + M * t) r)
      (fun t => congrFun (GlobalTheory.KummerEisensteinGalois.Smoothing.eisF_congr_mod hL hζ (Int.ModEq.refl a)
        (modEq_shift p M A₂ t)) r) c e₂ hc
  simp only [inner]
  exact sum_range_perm p (fun t => ∑ i₂ ∈ range p, eisF j (p * M) ζ (A₁ + M * t) (A₂ + M * i₂) r)
    (fun t => sum_congr rfl fun i₂ _ => congrFun (GlobalTheory.KummerEisensteinGalois.Smoothing.eisF_congr_mod hL hζ
      (modEq_shift p M A₁ t) (Int.ModEq.refl _)) r) c e₁ hc

theorem not_dvd_num (p : ℕ) [hp : Fact p.Prime] (N n : ℕ) (hn : 1 ≤ n) (hpN : ¬ p ∣ N) (x : ℕ)
    (hx : ¬ p ∣ x) (w c : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    ¬ (((N * p ^ n : ℕ) : ℤ) ∣ c * ((N : ℤ) * x + (p : ℤ) ^ n * w)) := by
  intro h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpn : (p : ℤ) ∣ (p : ℤ) ^ n := dvd_pow_self _ (by omega)
  have h1 : (p : ℤ) ∣ ((N * p ^ n : ℕ) : ℤ) := by
    push_cast; exact Dvd.dvd.mul_left hpn _
  rcases hpz.dvd_or_dvd (h1.trans h) with h3 | h3
  · exact hc h3
  · have h4 : (p : ℤ) ∣ (N : ℤ) * x := (dvd_add_left (Dvd.dvd.mul_right hpn w)).mp h3
    rcases hpz.dvd_or_dvd h4 with h5 | h5
    · exact hpN (Int.natCast_dvd_natCast.mp h5)
    · exact hx (Int.natCast_dvd_natCast.mp h5)

theorem smF_sum_lifts : ∀ (p : ℕ) [Fact p.Prime] (N n j : ℕ) (K : Type) [Field K] [CharZero K] (ζ : K) (c : ℤ)
    (x₁ x₂ : ZMod (p ^ n)) (u₁ u₂ w₁ w₂ : ℤ), IsPrimitiveRoot ζ (N * p ^ (n + 1)) → 0 < N → ¬ p ∣ N → 1 ≤ n →
    1 ≤ j → ¬ (p : ℤ) ∣ c → ¬ p ∣ x₁.val → (p : ℤ) * u₁ ≡ w₁ [ZMOD N] → (p : ℤ) * u₂ ≡ w₂ [ZMOD N] →
    ∀ r : ℕ, ∑ y₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) =>
        ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x₁)),
      ∑ y₂ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) =>
        ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x₂)),
      smF c j (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁.val : ℤ) + (p : ℤ) ^ (n + 1) * u₁)
        ((N : ℤ) * (y₂.val : ℤ) + (p : ℤ) ^ (n + 1) * u₂) r =
      (p : K) ^ ((2 : ℤ) - (j : ℤ)) * vp p (smF c j (N * p ^ n) (ζ ^ p) ((N : ℤ) * (x₁.val : ℤ) + (p : ℤ) ^ n * w₁)
        ((N : ℤ) * (x₂.val : ℤ) + (p : ℤ) ^ n * w₂)) r := by
  intro p hp N n j K _ _ ζ c x₁ x₂ u₁ u₂ w₁ w₂ hζ hN hpN hn hj hc hx hu₁ hu₂ r
  have hpos : 0 < p := hp.out.pos
  have hM : 0 < N * p ^ n := Nat.mul_pos hN (pow_pos hpos n)
  have hL : N * p ^ (n + 1) = p * (N * p ^ n) := by ring
  have hζ' : IsPrimitiveRoot ζ (p * (N * p ^ n)) := hL ▸ hζ
  have hζ1 : ζ ^ (p * (N * p ^ n)) = 1 := hζ'.pow_eq_one
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨k₁, hk₁⟩ := hu₁.dvd
  obtain ⟨k₂, hk₂⟩ := hu₂.dvd
  set A₁ : ℤ := (N : ℤ) * (x₁.val : ℤ) + (p : ℤ) ^ n * w₁ with hA₁
  set A₂ : ℤ := (N : ℤ) * (x₂.val : ℤ) + (p : ℤ) ^ n * w₂ with hA₂
  rw [hL, sum_lifts p n x₁]
  simp_rw [sum_lifts p n x₂]
  have key : ∀ s₁ ∈ range p, ∀ s₂ ∈ range p,
      smF c j (p * (N * p ^ n)) ζ
        ((N : ℤ) * ((((x₁.val + p ^ n * s₁ : ℕ) : ZMod (p ^ (n + 1))).val : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₁)
        ((N : ℤ) * ((((x₂.val + p ^ n * s₂ : ℕ) : ZMod (p ^ (n + 1))).val : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₂) r
      = (c : K) ^ 2 * eisF j (p * (N * p ^ n)) ζ (A₁ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₁ : ℤ) + -k₁)))
            (A₂ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₂ : ℤ) + -k₂))) r
        - (c : K) ^ ((2 : ℤ) - j) * eisF j (p * (N * p ^ n)) ζ (c * A₁ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₁ : ℤ) + -k₁)))
            (c * A₂ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₂ : ℤ) + -k₂))) r := by
    intro s₁ hs₁ s₂ hs₂
    rw [mem_range] at hs₁ hs₂
    rw [val_lift p n x₁ s₁ hs₁, val_lift p n x₂ s₂ hs₂]
    have e₁ : (N : ℤ) * ((x₁.val + p ^ n * s₁ : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₁
        = A₁ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₁ : ℤ) + -k₁)) := by
      rw [hA₁]; push_cast; linear_combination (-(p : ℤ) ^ n) * hk₁
    have e₂ : (N : ℤ) * ((x₂.val + p ^ n * s₂ : ℕ) : ℤ) + (p : ℤ) ^ (n + 1) * u₂
        = A₂ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₂ : ℤ) + -k₂)) := by
      rw [hA₂]; push_cast; linear_combination (-(p : ℤ) ^ n) * hk₂
    have f₁ : c * (A₁ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₁ : ℤ) + -k₁)))
        = c * A₁ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₁ : ℤ) + -k₁)) := by ring
    have f₂ : c * (A₂ + ((N * p ^ n : ℕ) : ℤ) * (1 * ((s₂ : ℤ) + -k₂)))
        = c * A₂ + ((N * p ^ n : ℕ) : ℤ) * (c * ((s₂ : ℤ) + -k₂)) := by ring
    rw [e₁, e₂, smF, f₁, f₂]
  refine (sum_congr rfl fun s₁ hs₁ => sum_congr rfl fun s₂ hs₂ => key s₁ hs₁ s₂ hs₂).trans ?_
  simp only [sum_sub_distrib, ← mul_sum]
  have h1 : ¬ (p : ℤ) ∣ 1 := hpz.not_dvd_one
  have nd₁ : ¬ (((N * p ^ n : ℕ) : ℤ) ∣ A₁ ∧ ((N * p ^ n : ℕ) : ℤ) ∣ A₂) := fun h => by
    have := not_dvd_num p N n hn hpN x₁.val hx w₁ 1 h1
    rw [one_mul] at this
    exact this h.1
  have ndc : ¬ (((N * p ^ n : ℕ) : ℤ) ∣ c * A₁ ∧ ((N * p ^ n : ℕ) : ℤ) ∣ c * A₂) := fun h =>
    not_dvd_num p N n hn hpN x₁.val hx w₁ c hc h.1
  rw [sum_perm2 p (N * p ^ n) j hM ζ hζ1 A₁ A₂ 1 (-k₁) (-k₂) h1 r,
    sum_perm2 p (N * p ^ n) j hM ζ hζ1 (c * A₁) (c * A₂) c (-k₁) (-k₂) hc r,
    GlobalTheory.EisDist.eisF_distribution p (N * p ^ n) j K ζ hζ' hM hj A₁ A₂ nd₁ r,
    GlobalTheory.EisDist.eisF_distribution p (N * p ^ n) j K ζ hζ' hM hj (c * A₁) (c * A₂) ndc r]
  unfold vp smF
  split_ifs <;> ring

end GlobalTheory.KummerEisensteinGalois.RowFibre
end
end

section

open Polynomial

noncomputable section

namespace GlobalTheory.K4.Geo

open Topology GlobalTheory.NeedB

theorem mem_fixingSubgroup_adjoin_of {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (S : Set Ω)
    (g : Ω ≃ₐ[k] Ω) (hg : ∀ x ∈ S, g x = x) : g ∈ (IntermediateField.adjoin k S).fixingSubgroup := by
  have hle : IntermediateField.adjoin k S ≤ IntermediateField.fixedField (fixingSubgroup (Ω ≃ₐ[k] Ω) S) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    exact (mem_fixingSubgroup_iff _).1 hf x hx
  exact (IntermediateField.le_iff_le _ _).1 hle ((mem_fixingSubgroup_iff _).2 fun x hx => hg x hx)

theorem valuation_lt_one_iff' {Ω : Type} [Field Ω] (B : ValuationSubring Ω) (y : Ω) :
    B.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ B := by
  by_cases hy : y = 0
  · simp [hy]
  · have h0 : B.valuation y ≠ 0 := by simpa using hy
    rw [← B.valuation_le_one_iff, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h0)]
    simp [hy, not_le]

variable (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω]

def equiv : (Ω ≃ₐ[K] Ω) ≃* GlobalTheory.K4.geo F K Ω where
  toFun g := ⟨g.restrictScalars F, (GlobalTheory.K4.TopW.mem_geo (K := K) _).2 fun z => g.commutes z⟩
  invFun h := AlgEquiv.ofRingEquiv (f := (h : Ω ≃ₐ[F] Ω).toRingEquiv)
    (fun z => (GlobalTheory.K4.TopW.mem_geo (K := K) _).1 h.2 z)
  left_inv g := by ext x; rfl
  right_inv h := by ext x; rfl
  map_mul' g g' := by ext x; rfl

variable [Algebra.IsAlgebraic F Ω]

theorem continuous_restrict :
    Continuous (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[F] Ω)) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 hU
  obtain ⟨S, hS⟩ : E.FG := IntermediateField.fg_of_fg_toSubalgebra _
    (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hE))
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := F) K
  have hfd : FiniteDimensional K (IntermediateField.adjoin K (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsIntegral.isIntegral x)
  refine Filter.mem_of_superset ((IntermediateField.adjoin K (S : Set Ω)).fixingSubgroup_isOpen.mem_nhds
    (Subgroup.one_mem _)) ?_
  intro g hg
  apply hEU
  rw [← hS]
  apply mem_fixingSubgroup_adjoin_of
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (IntermediateField.subset_adjoin _ _ hx)

theorem continuous_symm : Continuous (equiv F K Ω).symm := by
  apply continuous_of_continuousAt_one (equiv F K Ω).symm
  rw [ContinuousAt, map_one]
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).1 hU
  obtain ⟨S, hS⟩ : E.FG := IntermediateField.fg_of_fg_toSubalgebra _
    (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hE))
  have hfd : FiniteDimensional F (IntermediateField.adjoin F (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsIntegral.isIntegral x)
  refine (mem_nhds_subtype _ _ _).2 ⟨_, (IntermediateField.adjoin F (S : Set Ω)).fixingSubgroup_isOpen.mem_nhds
    (Subgroup.one_mem _), ?_⟩
  intro h hh
  simp only [Set.mem_preimage] at hh ⊢
  apply hEU
  rw [← hS]
  apply mem_fixingSubgroup_adjoin_of
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x (IntermediateField.subset_adjoin _ _ hx)

theorem continuous_equiv : Continuous (equiv F K Ω) :=
  continuous_induced_rng.2 (continuous_restrict F K Ω)

end GlobalTheory.K4.Geo

theorem GlobalTheory.K4.geo_facts : ∀ (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [Algebra.IsAlgebraic F Ω],
 (∀ g : Ω ≃ₐ[F] Ω, g ∈ GlobalTheory.K4.geo F K Ω ↔ ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) ∧
 (∃ e : (Ω ≃ₐ[K] Ω) ≃* GlobalTheory.K4.geo F K Ω, (∀ g x, ((e g : GlobalTheory.K4.geo F K Ω) : Ω ≃ₐ[F] Ω) x = g x) ∧ Continuous e ∧ Continuous e.symm) ∧
 (Normal F K → (GlobalTheory.K4.geo F K Ω).Normal) ∧ (IsGalois K Ω → IsCompact (GlobalTheory.K4.geo F K Ω : Set (Ω ≃ₐ[F] Ω))) ∧
 (∀ (B : ValuationSubring Ω) (r g : Ω ≃ₐ[F] Ω), GlobalTheory.NeedB.Inert B r → GlobalTheory.NeedB.Inert (B.comap (g : Ω →+* Ω)) (g⁻¹ * r * g)) := by
  intro F K Ω _ _ _ _ _ _ _ _
  refine ⟨fun g => GlobalTheory.K4.TopW.mem_geo g, ⟨GlobalTheory.K4.Geo.equiv F K Ω, fun g x => rfl, GlobalTheory.K4.Geo.continuous_equiv F K Ω,
    GlobalTheory.K4.Geo.continuous_symm F K Ω⟩, fun _ => ⟨fun n hn g => GlobalTheory.K4.TopW.conj_mem_geo g hn⟩, fun _ => ?_, ?_⟩
  · have hr : (GlobalTheory.K4.geo F K Ω : Set (Ω ≃ₐ[F] Ω)) =
        Set.range (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[F] Ω)) := by
      ext h
      constructor
      · intro hh
        exact ⟨(GlobalTheory.K4.Geo.equiv F K Ω).symm ⟨h, hh⟩, AlgEquiv.ext fun _ => rfl⟩
      · rintro ⟨g, rfl⟩
        exact (GlobalTheory.K4.Geo.equiv F K Ω g).2
    rw [hr]
    exact isCompact_range (GlobalTheory.K4.Geo.continuous_restrict F K Ω)
  · intro B r g hr x hx
    rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap] at hx
    have h1 := hr _ ((B.valuation_le_one_iff _).2 hx)
    rw [GlobalTheory.K4.Geo.valuation_lt_one_iff'] at h1
    rw [GlobalTheory.K4.Geo.valuation_lt_one_iff']
    have key : (g : Ω →+* Ω) ((g⁻¹ * r * g) x - x) = r ((g : Ω →+* Ω) x) - (g : Ω →+* Ω) x := by
      simp [AlgEquiv.mul_apply]
    rcases h1 with h0 | h0
    · left
      apply g.injective
      have : g ((g⁻¹ * r * g) x - x) = 0 := by simpa using key.trans h0
      rw [this, map_zero]
    · right
      intro hm
      apply h0
      rw [ValuationSubring.mem_comap, map_inv₀, key] at hm
      exact hm
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem FN.germ_ringHom_and_restrict : (∃ A : (ℍ → ℂ) →+* Mero, ∀ f, A f = germ f) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔ DifferentiableOn ℂ (up f) Hs) ∧ (∀ a b : ℂ → ℂ, (∀ z ∈ Hs, a z = b z) → (a : Mero) = (b : Mero)) ∧ (∀ a : ℂ → ℂ, germ (fun τ : ℍ => a τ) = (a : Mero)) ∧ ∀ τ : ℍ, (τ : ℂ) ∈ Hs := by
  refine ⟨⟨(Filter.Germ.coeRingHom _).comp (Pi.ringHom fun z => Pi.evalRingHom (fun _ : ℍ => ℂ) (UpperHalfPlane.ofComplex z)), fun f => rfl⟩, fun f => ?_, ?_, ?_, fun τ => τ.2⟩
  · exact UpperHalfPlane.mdifferentiable_iff
  · intro a b h
    rw [Filter.Germ.coe_eq]
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz
  · intro a
    unfold germ up
    rw [Filter.Germ.coe_eq]
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

end GlobalTheory
end
