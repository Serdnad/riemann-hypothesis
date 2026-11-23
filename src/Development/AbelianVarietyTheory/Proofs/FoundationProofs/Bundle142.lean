module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle133
public import Formalism.GaloisCohomology.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_of_qexp : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) → (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs, HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) → ∃ f : T.K, T.an f = (a : Mero) := by
  intro Ω _ _ _ ε T a M hM _ hinv hexp
  have hHs : ∀ τ : ℍ, (τ : ℂ) ∈ Hs := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict.2.2.2.2
  have hmob : ∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties.2.2.2.1
  set f : ℍ → ℂ := fun τ => a τ with hf
  have hinvf : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ := by
    intro γ hγ τ
    simp only [hf]
    rw [← hmob γ τ]
    exact hinv γ hγ τ (hHs τ)
  have hw : ∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ ε.range) M fun τ => DD τ ^ w * f (γ • τ) := by
    intro γ
    obtain ⟨c, n0, hc0, hs⟩ := hexp γ
    refine (GlobalTheory.T.exists_deltaPow_qExpansion_iff_laurentSeries ε.range M (fun τ => f (γ • τ)) hM).2 ⟨fun n => ε (c n), n0, fun n => ⟨c n, rfl⟩, ?_, ?_⟩
    · intro n hn
      simp [hc0 n hn]
    · intro τ
      have := hs τ (hHs τ)
      simp only [hf]
      rw [← hmob γ τ]
      exact this
  obtain ⟨w, hLv⟩ := GlobalTheory.T.exists_Lv_of_invariant_Gamma_of_forall_QAll ε.range M f hM hinvf hw
  have hmem : f ∈ ring ε.range := mem_ring_of_inR ⟨M, w, hM, hLv⟩
  refine ⟨T.io ⟨f, hmem⟩, ?_⟩
  rw [T.an_io]
  exact GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict.2.2.2.1 a

end GlobalTheory.FN
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.TateInv

theorem sub_one_mul_sum {R : Type*} [CommRing R] (ω : R) (n : ℕ) :
    (ω - 1) * ∑ s ∈ Finset.range n, (s : R) * ω ^ s = n * ω ^ n - ω * ∑ s ∈ Finset.range n, ω ^ s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem sub_one_mul_sum_eq {Ω : Type*} [Field Ω] (ω : Ω) (p : ℕ) (h1 : ω ≠ 1) (hp : ω ^ p = 1) :
    (ω - 1) * ∑ s ∈ Finset.range p, (s : Ω) * ω ^ s = p := by
  rw [sub_one_mul_sum, hp, geom_sum_eq h1, hp, sub_self, zero_div, mul_zero, sub_zero, mul_one]

theorem pow_apply_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] (γ : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (a : ℕ) (hγ : γ ζ = ζ ^ a)
    (t i : ℕ) : (γ ^ t) (ζ ^ i) = ζ ^ (i * a ^ t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hγ, ← pow_mul, pow_succ]
    congr 1; ring

theorem pow_apply_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] (γ : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (a : ℕ) (hγ : γ ζ = ζ ^ a)
    (t : ℕ) {x : Ω} (hx : x ∈ Subring.closure {ζ}) : (γ ^ t) x ∈ Subring.closure {ζ} := by
  have h : Subring.closure {ζ} ≤ (Subring.closure {ζ}).comap ((γ ^ t : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω) := by
    rw [Subring.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy, SetLike.mem_coe, Subring.mem_comap]
    have := pow_apply_pow γ ζ a hγ t 1
    simp only [pow_one, one_mul] at this
    show (γ ^ t) ζ ∈ _
    rw [this]
    exact Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _
  exact h hx

theorem mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m)) (i : ℕ)
    (hi : ¬ p ^ (L - m) ∣ i) :
    ∃ H ∈ Subring.closure {ζ}, (p : Ω) * ζ ^ i = γ H - H := by
  have hp : p.Prime := hpf.out
  obtain ⟨hmL, K, d, u, hd, hu, he, -⟩ := GlobalTheory.K5.MonX.exists_pow_eq hp2 hm1 hi
  have hpL : p ^ L = p ^ (L - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hpm : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  set ω := ζ ^ (u * d * p ^ (L - 1)) with hω
  have hω1 : ω ≠ 1 := by
    rw [hω, Ne, hζ.pow_eq_one_iff_dvd, hpL]
    intro h
    have h' : p ^ (L - 1) * p ∣ p ^ (L - 1) * (u * d) := by rwa [mul_comm (p ^ (L - 1)) (u * d)]
    have := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h'
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact hu h
    · exact hd h
  have hωp : ω ^ p = 1 := by
    rw [hω, ← pow_mul, hζ.pow_eq_one_iff_dvd]
    exact ⟨u * d, by rw [hpL]; ring⟩
  have hγω : γ ω = ω := by
    rw [hω, map_pow, hγ, ← pow_mul]
    have e : (1 + p ^ m) * (u * d * p ^ (L - 1)) = u * d * p ^ (L - 1) + p ^ L * (u * d * p ^ (m - 1)) := by
      rw [hpL, hpm]; ring
    rw [e, pow_add, pow_mul ζ (p ^ L), hζ.pow_eq_one, one_pow, mul_one]
  have hγtω : ∀ t : ℕ, (γ ^ t) ω = ω := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hγω]
  set S : Ω := ∑ s ∈ Finset.range p, (s : Ω) * ω ^ s with hS
  have hγtS : ∀ t : ℕ, (γ ^ t) S = S := by
    intro t

    rw [hS, map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [map_mul, map_natCast, map_pow, hγtω]
  have hK : (γ ^ K) (ζ ^ i) = ω * ζ ^ i := by
    rw [pow_apply_pow γ ζ _ hγ, he, pow_add, hω, mul_comm]
  have hωmem : ω ∈ Subring.closure {ζ} := Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _
  have hSmem : S ∈ Subring.closure {ζ} :=
    Subring.sum_mem _ fun s _ => Subring.mul_mem _ (natCast_mem _ s) (Subring.pow_mem _ hωmem _)
  have hH0 : S * ζ ^ i ∈ Subring.closure {ζ} :=
    Subring.mul_mem _ hSmem (Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _)
  refine ⟨∑ t ∈ Finset.range K, (γ ^ t) (S * ζ ^ i),
    Subring.sum_mem _ fun t _ => pow_apply_mem γ ζ _ hγ t hH0, ?_⟩
  have hγH : γ (∑ t ∈ Finset.range K, (γ ^ t) (S * ζ ^ i)) = ∑ t ∈ Finset.range K, (γ ^ (t + 1)) (S * ζ ^ i) := by

    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [pow_succ', AlgEquiv.mul_apply]
  rw [hγH, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun t => (γ ^ t) (S * ζ ^ i)), pow_zero,
    AlgEquiv.one_apply, map_mul, hγtS, hK]
  have := sub_one_mul_sum_eq ω p hω1 hωp
  rw [← hS] at this
  linear_combination (-(ζ ^ i)) * this


open Classical in
theorem trace_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * (if p ^ (L - m) ∣ i then ζ ^ i else 0) := by
  have hp : p.Prime := hpf.out
  have hN : p ^ L = p ^ m * p ^ (L - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hs : ∀ a : (ZMod (p ^ L))ˣ, τ a (ζ ^ i) = ζ ^ ((a : ZMod (p ^ L)).val * i) := by
    intro a; rw [map_pow, hτ, ← pow_mul]
  have hr := GlobalTheory.NTr.sum_reindex p L m hm1 hm (fun v => ζ ^ (v * i))
  rw [Finset.sum_congr rfl (fun a _ => hs a), hr]
  have hw : IsPrimitiveRoot (ζ ^ p ^ m) (p ^ (L - m)) := hζ.pow (pow_pos hp.pos _) hN
  have hterm : ∀ k, ζ ^ ((1 + p ^ m * k) * i) = ζ ^ i * ((ζ ^ p ^ m) ^ i) ^ k := by
    intro k; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  simp only [hterm, ← Finset.mul_sum]
  split_ifs with hd
  · have h1 : (ζ ^ p ^ m) ^ i = 1 := by
      obtain ⟨j, hj⟩ := hd
      rw [hj, pow_mul, hw.pow_eq_one, one_pow]
    rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow]
    ring
  · have h1 : (ζ ^ p ^ m) ^ i ≠ 1 := fun h => hd ((hw.pow_eq_one_iff_dvd i).mp h)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm i, pow_mul, hw.pow_eq_one, one_pow, sub_self, zero_div, mul_zero, mul_zero]


open Classical in
theorem key_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m))
    (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω)) (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
    ∃ H ∈ Subring.closure {ζ}, ∃ z : Ω, (p : Ω) * (ζ ^ i - z) = γ H - H ∧
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * z := by
  rw [trace_mono p L m hm1 hm ζ hζ τ hτ i]
  split_ifs with hd
  · exact ⟨0, Subring.zero_mem _, ζ ^ i, by simp, rfl⟩
  · obtain ⟨H, hH, e⟩ := mono p hp2 L m hm1 ζ hζ γ hγ i hd
    exact ⟨H, hH, 0, by rw [sub_zero, e], rfl⟩


open Classical in
theorem key {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (L m : ℕ) (hm1 : 1 ≤ m)
    (hm : m ≤ L) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (γ : Ω ≃ₐ[ℚ] Ω) (hγ : γ ζ = ζ ^ (1 + p ^ m))
    (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω)) (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val)
    (y : Ω) (hy : y ∈ Subring.closure {ζ}) :
    ∃ H ∈ Subring.closure {ζ}, ∃ z : Ω, (p : Ω) * (y - z) = γ H - H ∧
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a y
        = (p : Ω) ^ (L - m) * z := by
  rw [Subring.mem_closure_iff, Submonoid.closure_singleton_eq] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact key_mono p hp2 L m hm1 hm ζ hζ γ hγ τ hτ (Multiplicative.toAdd i)
  | zero => exact ⟨0, Subring.zero_mem _, 0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨H1, h1, z1, e1, f1⟩ := hx
    obtain ⟨H2, h2, z2, e2, f2⟩ := hy
    exact ⟨H1 + H2, Subring.add_mem _ h1 h2, z1 + z2, by rw [map_add (f := _)]; linear_combination e1 + e2,
      by simp only [map_add (f := _), Finset.sum_add_distrib, f1, f2]; ring⟩
  | neg x _ hx =>
    obtain ⟨H1, h1, z1, e1, f1⟩ := hx
    exact ⟨-H1, Subring.neg_mem _ h1, -z1, by rw [map_neg]; linear_combination -e1,
      by simp only [map_neg, Finset.sum_neg_distrib, f1]; ring⟩

theorem tate_inv : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F F' : Ω, InZl ε p L F → IsNT ε p L m F F' →
  ∀ γ : Ω ≃ₐ[ℚ] Ω, γ (zt ε p L) = zt ε p L ^ (1 + p ^ m) → ∃ H : Ω, InZl ε p L H ∧ (p : Ω) ^ c * (F - F') = γ H - H := by
  intro p hpf hp2
  refine ⟨1, ?_⟩
  intro Ω _ _ _ ε L m hm1 hmL F F' hF hNT γ hγ
  have hp : p.Prime := hpf.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hζ := GlobalTheory.NTr.zt_prim ε p L hp.pos
  obtain ⟨D, hD, hDF⟩ := hF
  obtain ⟨τ, hτ, hT⟩ := hNT
  have hD0 : (D : Ω) ≠ 0 := by
    have : D ≠ 0 := by rintro rfl; exact hD (dvd_zero p)
    exact_mod_cast this
  have hpN : (p : Ω) ^ (L - m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  obtain ⟨H, hH, z, e1, e2⟩ := key p hp2 L m hm1 hmL (zt ε p L) hζ γ hγ τ hτ _ hDF
  have hz : z = D * F' := by
    apply mul_left_cancel₀ hpN
    rw [← e2]
    simp only [map_mul, map_natCast, ← Finset.mul_sum]
    rw [← hT]; ring
  refine ⟨H / D, ⟨D, hD, by rwa [mul_div_cancel₀ _ hD0]⟩, ?_⟩
  rw [map_div₀, map_natCast, pow_one, ← sub_div, ← e1, hz, eq_div_iff hD0]
  ring

end GlobalTheory.TateInv
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem isAlgZp_map_of_algebraic : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl] (j : Ω →+* Ωl) (x : Ω), IsAlgZp (p := p) (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ j x
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have hz : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 hx
  obtain ⟨P, hP, hPx⟩ := hz
  refine ⟨P.map (Int.castRingHom ℤ_[p]), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hP
  · rw [Polynomial.map_map, Polynomial.aeval_def, Polynomial.eval₂_map]
    have e1 : (algebraMap (O0 p) Ωl).comp ((algebraMap ℤ_[p] (O0 p)).comp (Int.castRingHom ℤ_[p])) = j.comp (algebraMap ℤ Ω) := RingHom.ext_int _ _
    rw [e1, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hPx, map_zero]

theorem zt_prim_and_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l n : ℕ), 0 < l → IsPrimitiveRoot (zt ε l n) (l ^ n) ∧ zt ε l (n + 1) ^ l = zt ε l n := by
  intro Ω _ _ _ ε l n hl
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hkey : ∀ m : ℕ, ε (zt ε l m) = Complex.exp (2 * Real.pi * Complex.I / ((l ^ m : ℕ) : ℂ)) := by
    intro m
    have hN : l ^ m ≠ 0 := pow_ne_zero _ hl.ne'
    have hw : Complex.exp (2 * Real.pi * Complex.I * (((1 / (l : ℚ) ^ m : ℚ)) : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I / ((l ^ m : ℕ) : ℂ)) := by
      congr 1; push_cast; ring
    haveI : NeZero ((l ^ m : ℕ) : Ω) := ⟨by exact_mod_cast hN⟩
    haveI : NeZero (l ^ m) := ⟨hN⟩
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hz' : IsPrimitiveRoot (ε z) (l ^ m) := hz.map_of_injective ε.injective
    have hp := Complex.isPrimitiveRoot_exp (l ^ m) hN
    obtain ⟨i, -, hi⟩ := hz'.eq_pow_of_pow_eq_one hp.pow_eq_one
    have hex : ∃ y, ε y = Complex.exp (2 * Real.pi * Complex.I * (((1 / (l : ℚ) ^ m : ℚ)) : ℂ)) :=
      ⟨z ^ i, by rw [map_pow, hi, hw]⟩
    show ε (Function.invFun ε _) = _
    rw [Function.invFun_eq hex, hw]
  refine ⟨?_, ?_⟩
  · rw [← IsPrimitiveRoot.map_iff_of_injective (f := ε) ε.injective, hkey]
    exact Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ hl.ne')
  · apply ε.injective
    rw [map_pow, hkey, hkey, ← Complex.exp_nat_mul]
    congr 1
    have : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    push_cast
    field_simp
    ring

theorem exists_cusp_embedding : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ∃ (Ωl : Type) (_ : Field Ωl) (_ : Algebra (O0 p) Ωl), IsClo p Ωl ∧ ∃ (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl), IsCusp ε A T j := by
  intro Ω _ _ _ ε X _ p _ _ A hA
  let Ωl := AlgebraicClosure (FractionRing (O0 p))
  have hcl : IsClo p Ωl := GlobalTheory.K5.Basic.isClo_algebraicClosure p
  haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hcl
  haveI : IsAlgClosed Ωl := hcl.clo
  let j0 : Ω →+* Ωl := (IsAlgClosed.lift : Ω →ₐ[ℚ] Ωl).toRingHom
  have hBexists : ∃ B : ValuationSubring Ω, (p : Ω) ∈ B.nonunits ∧
      ∀ x, x ∈ B ↔ IsInt (p := p) (j0 x) := by
    obtain ⟨v, hv, _, _, hp⟩ := GlobalTheory.K5.exists_valuation_isInt p Ωl hcl
    let w := v.comap j0
    refine ⟨w.valuationSubring, ?_, fun x => ?_⟩
    · rw [ValuationSubring.mem_nonunits_iff, ← map_one w.valuationSubring.valuation,
        ← w.isEquiv_valuation_valuationSubring.lt_iff_lt, map_one]
      change v (j0 (p : Ω)) < 1
      rw [map_natCast]
      exact hp
    · rw [Valuation.mem_valuationSubring_iff]
      exact hv (j0 x)
  obtain ⟨B, hBp, hB⟩ := hBexists
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_algEquiv_map_valuationSubring_over_prime p A B hA hBp
  let j : Ω →+* Ωl := j0.comp σ.toRingEquiv.toRingHom
  have hint : ∀ x, x ∈ A ↔ IsInt (p := p) (j x) := fun x => (hσ x).symm.trans (hB _)
  have hl : 0 < p := (Fact.out : p.Prime).pos
  let T0 := (GlobalTheory.K5.Basic.nonempty_tower hcl).some
  let T : GlobalTheory.K5.Tower p Ωl :=
    { ζ := fun n => j (zt ε p n), qq := T0.qq,
      prim := fun n => (zt_prim_and_pow ε p n hl).1.map_of_injective j.injective,
      ζpow := fun n => by simp only [← map_pow, (zt_prim_and_pow ε p n hl).2],
      q0 := T0.q0, qpow := T0.qpow }
  have hdown : ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x) := by
    exact GlobalTheory.CuspDown.exists_restrict p A Ωl hcl j hint
  refine ⟨Ωl, inferInstance, inferInstance, hcl, T, j, ?_⟩
  exact { int := hint, alg := isAlgZp_map_of_algebraic p Ωl j, root := fun n => rfl,
          dense := GlobalTheory.T.exists_algebraicNumber_congr_mod_prime_pow p A Ωl hcl j hint, down := hdown,
          up := fun n s hs => GlobalTheory.T.exists_local_aut_fixing_tower_param_of_stabilizes p A Ωl hcl j hint T n s hs }

end GlobalTheory.Glue
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

section

variable (l : ℕ) [Fact l.Prime]

private theorem qzTor_smul_mk (x : ℤ_[l]) (q : ℚ_[l]) :
    x • QZ.mk l q = QZ.mk l ((x : ℚ_[l]) * q) := rfl

private theorem qzTor_mk_eq_zero (q : ℚ_[l]) :
    QZ.mk l q = 0 ↔ ∃ z : ℤ_[l], (z : ℚ_[l]) = q :=
  Submodule.Quotient.mk_eq_zero (ZlSub l)

private theorem qzTor_mk_surj (a : QZ l) : ∃ q, QZ.mk l q = a :=
  Submodule.Quotient.mk_surjective (ZlSub l) a

private theorem qzTor_key (r : ℕ) (x : ℤ_[l]) :
    x • QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) = 0 ↔ PadicInt.toZModPow r x = 0 := by
  have hl : ((l : ℚ_[l]) ^ r) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  rw [qzTor_smul_mk, qzTor_mk_eq_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, Subtype.ext ?_⟩
    have : ((z * (l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) = (z : ℚ_[l]) * (l : ℚ_[l]) ^ r := by
      push_cast; rfl
    rw [this, hz]
    field_simp
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    push_cast
    field_simp

end

theorem qz_torsion_zmod_embedding (l : ℕ) [Fact l.Prime] :
    (∀ a : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) ∧
    ∀ r : ℕ, ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧
      (∀ a : QZ l, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) ∧
      ∀ (x : ℤ_[l]) (y : ZMod (l ^ r)), ι (PadicInt.toZModPow r x * y) = x • ι y := by
  have hp : l.Prime := Fact.out
  refine ⟨fun a => ?_, fun r => ?_⟩
  · obtain ⟨q, rfl⟩ := qzTor_mk_surj l a
    have hlt : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
    have hpos : (0 : ℝ) < (‖q‖ + 1)⁻¹ := by positivity
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hpos hlt
    refine ⟨r, ?_⟩
    rw [qzTor_smul_mk, qzTor_mk_eq_zero]
    have hle : ‖(l : ℚ_[l]) ^ r * q‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      calc ‖(l : ℚ_[l])‖ ^ r * ‖q‖ ≤ (‖q‖ + 1)⁻¹ * (‖q‖ + 1) :=
            mul_le_mul hr.le (by linarith) (norm_nonneg _) hpos.le
        _ = 1 := inv_mul_cancel₀ (by positivity)
    refine ⟨⟨_, hle⟩, ?_⟩
    push_cast
    rfl
  · have hl : ((l : ℚ_[l]) ^ r) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
    set e : QZ l := QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) with he
    have hs : Function.Surjective (PadicInt.toZModPow (p := l) r) := by
      haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
      exact ZMod.ringHom_surjective _
    have hwd : ∀ x x' : ℤ_[l], PadicInt.toZModPow r x = PadicInt.toZModPow r x' →
        x • e = x' • e := by
      intro x x' h
      rw [← sub_eq_zero, ← sub_smul, he, qzTor_key, map_sub, h, sub_self]
    have hinv := Function.surjInv_eq hs
    let ι : ZMod (l ^ r) →+ QZ l := AddMonoidHom.mk' (fun y => Function.surjInv hs y • e) (by
      intro y y'
      rw [← add_smul]
      apply hwd
      rw [map_add (f := _), hinv, hinv, hinv])
    have hι : ∀ x : ℤ_[l], ι (PadicInt.toZModPow r x) = x • e := fun x =>
      hwd _ _ (hinv _)
    refine ⟨ι, ?_, fun a => ⟨fun ha => ?_, ?_⟩, fun x y => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := hs y
      rw [hι, he, qzTor_key] at hy
      exact hy
    · obtain ⟨q, rfl⟩ := qzTor_mk_surj l a
      rw [qzTor_smul_mk, qzTor_mk_eq_zero] at ha
      obtain ⟨z, hz⟩ := ha
      refine ⟨PadicInt.toZModPow r z, ?_⟩
      rw [hι, he, qzTor_smul_mk, hz]
      congr 1
      push_cast
      field_simp
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hs y
      rw [hι, smul_smul, he, qzTor_key, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · obtain ⟨x', rfl⟩ := hs y
      rw [← map_mul, hι, hι, mul_smul]

end GlobalTheory
end
