module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

@[expose] public section

section
end

section

namespace GlobalTheory

theorem padicNorm_prime_mul_sq_ne_sq (p : ℕ) [hp : Fact p.Prime] (s t : ℚ) (ht : t ≠ 0) :
    padicNorm p (s ^ 2) ≠ padicNorm p ((p : ℚ) * t ^ 2) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hpt : (p : ℚ) * t ^ 2 ≠ 0 := mul_ne_zero hp0 (pow_ne_zero _ ht)
  by_cases hs : s = 0
  · subst hs
    intro h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, padicNorm.zero] at h
    exact padicNorm.nonzero hpt h.symm
  · intro h
    rw [padicNorm.eq_zpow_of_nonzero (pow_ne_zero _ hs), padicNorm.eq_zpow_of_nonzero hpt,
      padicValRat.mul hp0 (pow_ne_zero _ ht), padicValRat.pow s, padicValRat.pow t,
      padicValRat.self hp.out.one_lt] at h
    have := zpow_right_injective₀ (by linarith) hp1.ne' h
    push_cast at this
    omega

theorem padicNorm_of_sq_add_prime_mul_sq (p : ℕ) [hp : Fact p.Prime] (s t : ℚ)
    (h : padicNorm p (s ^ 2 + (p : ℚ) * t ^ 2) = 1) :
    padicNorm p s ≤ 1 ∧ padicNorm p ((p : ℚ) * t ^ 2) < 1 := by
  have key : padicNorm p (s ^ 2) ≤ 1 ∧ padicNorm p ((p : ℚ) * t ^ 2) < 1 := by
    by_cases ht : t = 0
    · subst ht
      simp at h ⊢
      exact h.le
    · rw [padicNorm.add_eq_max_of_ne (padicNorm_prime_mul_sq_ne_sq p s t ht)] at h
      have h1 := padicNorm_prime_mul_sq_ne_sq p 1 t ht
      rw [one_pow, padicNorm.one] at h1
      exact ⟨h ▸ le_max_left _ _, lt_of_le_of_ne (h ▸ le_max_right _ _) h1.symm⟩
  refine ⟨?_, key.2⟩
  have h1 := key.1
  rw [sq, padicNorm.mul] at h1
  have := padicNorm.nonneg (p := p) s
  nlinarith

theorem selfDual_lattice_exists_norm_one_mod :
    ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → (∀ u v : ℚ, padicNorm p u = 1 → padicNorm p v = 1 → ∃ a b : ℤ, padicNorm p (u * (a : ℚ) ^ 2 + v * (b : ℚ) ^ 2 - 1) < 1) → (∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ x ∈ W, x ≠ 0) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p u = 1) → ∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ e ∈ W, h e e = 1) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1 := by
  intro K V _ _ _ _ σ h p d θ O L hp hd hθ hσθ hK hσO hω hO hh hdef hL hLO hbig hab hun W hW
    ⟨e, heW, he⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  obtain ⟨y1, hy1L, hy1W, u1, hu1, hu1n⟩ := hun W hW ⟨e, heW, he0⟩
  have hu10 : u1 ≠ 0 := by
    rintro rfl
    simp at hu1n
  have hu10K : (u1 : K) ≠ 0 := by exact_mod_cast hu10
  have hinv : (u1 : K)⁻¹ ∈ O := by
    have : ((u1⁻¹ : ℚ) : K) ∈ O := by
      rw [hO, ← one_div, padicNorm.div, hu1n]
      simp
    simpa using this
  have hθO : θ ∈ O := by
    have h2 : θ = (1 + θ) / 2 + (1 + θ) / 2 - 1 := by ring
    rw [h2]
    exact O.sub_mem (O.add_mem hω hω) O.one_mem
  have hperp : ∀ y : V, h (y - (h y y1 * (u1 : K)⁻¹) • y1) y1 = 0 := by
    intro y
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu1]
    field_simp
    ring
  have hnorm : ∀ s t : ℚ, h (((s : K) + (t : K) * θ) • y1) (((s : K) + (t : K) * θ) • y1)
      = (((s ^ 2 + (d : ℚ) * t ^ 2) * u1 : ℚ) : K) := by
    intro s t
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hu1, map_add (f := _),
      map_mul, map_ratCast, hσθ]
    push_cast
    linear_combination (-(t : K) ^ 2 * (u1 : K)) * hθ
  set W' : Submodule K V := W ⊓ LinearMap.ker (h.flip y1) with hW'
  have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ h x y1 = 0 := by
    intro x
    simp [hW']
  by_cases hne : ∃ x ∈ W', x ≠ 0
  · have hsd : ∀ x ∈ W', (∀ y ∈ L, y ∈ W' → h x y ∈ O) → x ∈ L := by
      intro x hx hxO
      obtain ⟨hxW, hx1⟩ := (hmem x).1 hx
      refine hW x hxW fun y hyL hyW => ?_
      have := hxO (y - (h y y1 * (u1 : K)⁻¹) • y1)
        (L.sub_mem hyL (hL _ (O.mul_mem (hLO _ hyL _ hy1L) hinv) _ hy1L))
        ((hmem _).2 ⟨W.sub_mem hyW (W.smul_mem _ hy1W), hperp y⟩)
      simpa [map_sub, LinearMap.map_smulₛₗ, hx1] using this
    obtain ⟨y2, hy2L, hy2W', u2, hu2, hu2n⟩ := hun W' hsd hne
    obtain ⟨hy2W, h21⟩ := (hmem y2).1 hy2W'
    have h12 : h y1 y2 = 0 := by rw [hh, h21, map_zero]
    obtain ⟨a, b, hab'⟩ := hab u1 u2 hu1n hu2n
    refine ⟨(a : K) • y1 + (b : K) • y2,
      L.add_mem (hL _ (intCast_mem O a) _ hy1L) (hL _ (intCast_mem O b) _ hy2L),
      W.add_mem (W.smul_mem _ hy1W) (W.smul_mem _ hy2W), _, ?_, hab'⟩
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, hu1, hu2, h12, h21, map_intCast]
    push_cast
    ring
  · by_cases hpd : p = d
    · subst hpd
      have h0 : e - (h e y1 * (u1 : K)⁻¹) • y1 = 0 := by
        by_contra hc
        exact hne ⟨_, (hmem _).2 ⟨W.sub_mem heW (W.smul_mem _ hy1W), hperp e⟩, hc⟩
      obtain ⟨s, t, hst⟩ := hK (h e y1 * (u1 : K)⁻¹)
      rw [hst, sub_eq_zero] at h0
      have h1 := hnorm s t
      rw [← h0, he] at h1
      have h2 : (s ^ 2 + (p : ℚ) * t ^ 2) * u1 = 1 := by exact_mod_cast h1.symm
      have h3 : padicNorm p (s ^ 2 + (p : ℚ) * t ^ 2) = 1 := by
        have := congrArg (padicNorm p) h2
        rwa [padicNorm.mul, hu1n, mul_one, padicNorm.one] at this
      obtain ⟨hs, ht⟩ := padicNorm_of_sq_add_prime_mul_sq p s t h3
      have h4 := hnorm s 0
      refine ⟨_, hL _ ?_ _ hy1L, W.smul_mem _ hy1W, _, h4, ?_⟩
      · simpa using (hO s).2 hs
      · have : (s ^ 2 + (p : ℚ) * 0 ^ 2) * u1 - 1 = -((p : ℚ) * t ^ 2 * u1) := by
          linear_combination h2
        rw [this, padicNorm.neg, padicNorm.mul, hu1n, mul_one]
        exact ht
    · haveI : Fact d.Prime := ⟨hd⟩
      have hdn : padicNorm p (d : ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne hpd
      obtain ⟨a, b, hab'⟩ := hab u1 (u1 * d) hu1n (by rw [padicNorm.mul, hu1n, hdn, mul_one])
      have h4 := hnorm a b
      refine ⟨_, hL _ ?_ _ hy1L, W.smul_mem _ hy1W, _, h4, ?_⟩
      · push_cast
        exact O.add_mem (intCast_mem O a) (O.mul_mem (intCast_mem O b) hθO)
      · convert hab' using 2
        ring

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_lattice_norm_one_of_norm_one_mod (K V : Type) [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K)
    (O : Subring K) (L : AddSubgroup V) (hp : p.Prime) (_hd : d.Prime) (hθ : θ ^ 2 = -(d : K))
    (hσ : σ θ = -θ) (hK : ∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ)
    (hOσ : ∀ x ∈ O, σ x ∈ O) (hω : (1 + θ) / 2 ∈ O)
    (hO : ∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) (hh : ∀ x y : V, h y x = σ (h x y))
    (_hdef : ∀ x : V, h x x = 0 → x = 0) (hL : ∀ a ∈ O, ∀ x ∈ L, a • x ∈ L)
    (_hint : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) (hfull : ∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L)
    (W : Submodule K V) (he : ∃ e ∈ W, h e e = 1)
    (hy : ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1) :
    ∃ z ∈ L, z ∈ W ∧ h z z = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, heW, hee⟩ := he
  obtain ⟨y₀, hy₀L, hy₀W, u₀, hu₀, hr⟩ := hy
  have hσω : σ ((1 + θ) / 2) = (1 - θ) / 2 := by
    rw [map_div₀, map_add (f := _), map_one, hσ, map_ofNat, sub_eq_add_neg]
  have hn : padicNorm p ((1 + d) / 4) ≤ 1 := by
    rw [← hO]
    have := O.mul_mem hω (hOσ _ hω)
    rw [hσω] at this
    convert this using 1
    push_cast
    linear_combination (1 / 4 : K) * hθ

  have step : ∀ y ∈ L, y ∈ W → ∀ u : ℚ, h y y = (u : K) → padicNorm p (u - 1) ≤ 1 →
      ∃ y' ∈ L, y' ∈ W ∧ ∃ u' : ℚ, h y' y' = (u' : K) ∧
        padicNorm p (u' - 1) ≤ padicNorm p (u - 1) * padicNorm p (u - 1) := by
    intro y hyL hyW u hu hu1
    have hc : ((1 - u : ℚ) : K) ∈ O := by
      rw [hO, ← padicNorm.neg]; simpa using hu1
    have hu' : padicNorm p u ≤ 1 := by
      have := padicNorm.nonarchimedean (p := p) (q := u - 1) (r := 1)
      rw [sub_add_cancel, padicNorm.one] at this
      exact this.trans (max_le hu1 le_rfl)
    refine ⟨(1 + ((1 - u : ℚ) : K) * ((1 + θ) / 2)) • y,
      hL _ (O.add_mem O.one_mem (O.mul_mem hc hω)) y hyL, W.smul_mem _ hyW,
      1 + (u - 1) * (u - 1) * ((1 + d) / 4 * u - 1), ?_, ?_⟩
    · simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hu, map_add (f := _), map_mul,
        map_one, hσω, map_ratCast]
      push_cast
      linear_combination (-(1 - (u : K)) ^ 2 * u / 4) * hθ
    · rw [add_sub_cancel_left, padicNorm.mul, padicNorm.mul]
      have h1 : padicNorm p ((1 + d) / 4 * u - 1) ≤ 1 := by
        refine padicNorm.sub.trans (max_le ?_ (by rw [padicNorm.one]))
        rw [padicNorm.mul]
        exact mul_le_one₀ hn (padicNorm.nonneg _) hu'
      exact mul_le_of_le_one_right
        (mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)) h1
  have hr0 : 0 ≤ padicNorm p (u₀ - 1) := padicNorm.nonneg _
  have iter : ∀ k : ℕ, ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧
      padicNorm p (u - 1) ≤ padicNorm p (u₀ - 1) ^ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨y₀, hy₀L, hy₀W, u₀, hu₀, by simp⟩
    | succ k ih =>
      obtain ⟨y, hyL, hyW, u, hu, hk⟩ := ih
      have hk1 : padicNorm p (u - 1) ≤ padicNorm p (u₀ - 1) :=
        hk.trans (by
          rw [pow_succ]
          exact mul_le_of_le_one_left hr0 (pow_le_one₀ hr0 hr.le))
      obtain ⟨y', hy'L, hy'W, u', hu', hle⟩ := step y hyL hyW u hu (hk1.trans hr.le)
      refine ⟨y', hy'L, hy'W, u', hu', hle.trans ?_⟩
      rw [pow_succ _ (k + 1)]
      exact mul_le_mul hk hk1 (padicNorm.nonneg _) (pow_nonneg hr0 _)
  obtain ⟨m, hm⟩ := hfull e
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpos : ∀ q : ℚ, q ≠ 0 → 0 < padicNorm p q := fun q hq =>
    lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero hq).symm
  have hP0 : 0 < padicNorm p ((p : ℚ) ^ m) := hpos _ (pow_ne_zero _ hp0)
  have hP1 : padicNorm p ((p : ℚ) ^ m) ≤ 1 := by
    have := padicNorm.of_nat (p := p) (p ^ m)
    rwa [Nat.cast_pow] at this
  have h40 : 0 < padicNorm p 4 := hpos _ (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (mul_pos h40 hP0) hr
  obtain ⟨y, hyL, hyW, u, hu, hyk⟩ := iter k
  have hsmall : padicNorm p (u - 1) < padicNorm p 4 * padicNorm p ((p : ℚ) ^ m) := by
    refine lt_of_le_of_lt (hyk.trans ?_) hk
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hr0 _) hr.le

  have secant : ∀ y ∈ L, y ∈ W → h y y = (u : K) → ∀ T : ℚ, h e y + h y e = (T : K) →
      padicNorm p 4 ≤ padicNorm p (u + 1 - T) → ∃ z ∈ L, z ∈ W ∧ h z z = 1 := by
    intro y hyL hyW hu T hT hQ
    have hQpos : 0 < padicNorm p (u + 1 - T) := h40.trans_le hQ
    have hQ0 : u + 1 - T ≠ 0 := by
      intro h0; rw [h0, padicNorm.zero] at hQpos; exact lt_irrefl _ hQpos
    set t : ℚ := (1 - u) / ((u + 1 - T) * (p : ℚ) ^ m) with ht
    have htO : (t : K) ∈ O := by
      rw [hO, ht, padicNorm.div, padicNorm.mul, div_le_one (mul_pos hQpos hP0), ← padicNorm.neg,
        neg_sub]
      exact hsmall.le.trans (mul_le_mul_of_nonneg_right hQ hP0.le)
    have hpO : (p : K) ^ m ∈ O := O.pow_mem (natCast_mem O p) m
    have hs : t * (p : ℚ) ^ m * (u + 1 - T) = 1 - u := by
      rw [ht]; field_simp
    have hs' : (t : K) * (p : K) ^ m * (u + 1 - T) = 1 - u := by
      exact_mod_cast congrArg (fun q : ℚ => (q : K)) hs
    refine ⟨y + ((t : K) * (p : K) ^ m) • y - (t : K) • ((p : K) ^ m • e),
      L.sub_mem (L.add_mem hyL (hL _ (O.mul_mem htO hpO) y hyL)) (hL _ htO _ hm),
      W.sub_mem (W.add_mem hyW (W.smul_mem _ hyW)) (W.smul_mem _ (W.smul_mem _ heW)), ?_⟩
    simp only [map_smul, map_smulₛₗ, map_add (f := _), map_sub, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, smul_eq_mul, hu, hee, map_mul, map_pow, map_ratCast, map_natCast,
      RingHom.id_apply]
    linear_combination (1 + (t : K) * (p : K) ^ m) * hs' -
      ((t : K) * (p : K) ^ m) * (1 + (t : K) * (p : K) ^ m) * hT
  obtain ⟨T, hT⟩ : ∃ T : ℚ, h e y + h y e = (T : K) := by
    obtain ⟨a, b, hab⟩ := hK (h e y)
    refine ⟨2 * a, ?_⟩
    rw [hh e y, hab, map_add (f := _), map_mul, map_ratCast, map_ratCast, hσ]
    push_cast
    ring
  by_cases hQ : padicNorm p 4 ≤ padicNorm p (u + 1 - T)
  · exact secant y hyL hyW hu T hT hQ
  · refine secant (-y) (L.neg_mem hyL) (W.neg_mem hyW) (by simpa using hu) (-T)
      (by
        simp only [map_neg, LinearMap.neg_apply]
        push_cast
        linear_combination -hT) ?_
    by_contra hQ'
    push Not at hQ hQ'
    have h2 : padicNorm p (2 * (u - 1)) < padicNorm p 4 := by
      rw [padicNorm.mul]
      have h21 : padicNorm p 2 ≤ 1 := by simpa using padicNorm.of_nat (p := p) 2
      refine lt_of_le_of_lt (mul_le_of_le_one_left (padicNorm.nonneg _) h21) ?_
      exact hsmall.trans_le (mul_le_of_le_one_right h40.le hP1)
    have h3 : padicNorm p 4 < padicNorm p 4 := by
      calc padicNorm p 4
          = padicNorm p ((u + 1 - T) + (u + 1 - -T) - 2 * (u - 1)) := by congr 1; ring
        _ ≤ _ := padicNorm.sub
        _ < padicNorm p 4 :=
          max_lt (lt_of_le_of_lt padicNorm.nonarchimedean (max_lt hQ hQ')) h2
    exact lt_irrefl _ h3

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_unit_norm_of_selfDual_hermitian_lattice :
    ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → ∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ x ∈ W, x ≠ 0) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p u = 1 := by
  intro K V _ _ _ _ σ h p d θ O L hp hd hθ hσθ hK _ hω hO hherm hdef hL hLO hscale W hW hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    have : (d : K) = 0 := by simpa using hθ
    exact hd.ne_zero (by exact_mod_cast this)

  have hrat : ∀ x : V, ∃ u : ℚ, h x x = (u : K) := by
    intro x
    obtain ⟨a, b, hab⟩ := hK (h x x)
    have h1 := hherm x x
    rw [hab, map_add (f := _), map_mul, map_ratCast, map_ratCast, hσθ] at h1
    have h2 : (b : K) * θ = 0 := by
      have : (2 : K) * ((b : K) * θ) = 0 := by linear_combination h1
      simpa using this
    exact ⟨a, by rw [hab, h2, add_zero]⟩
  have hnp : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
  by_contra hcon
  push_neg at hcon
  have hdiv : ∀ y ∈ L, y ∈ W → h y y / p ∈ O := by
    intro y hy hyW
    obtain ⟨u, hu⟩ := hrat y
    have h1 : padicNorm p u ≤ 1 := (hO u).1 (hu ▸ hLO y hy y hy)
    have h2 := hcon y hy hyW u hu
    have h3 : ((u / p : ℚ) : K) ∈ O := by
      rw [hO, padicNorm.div, hnp]
      by_cases hu0 : u = 0
      · simp [hu0]
      obtain ⟨z, hz⟩ := padicNorm.values_discrete (p := p) hu0
      rw [hz] at h1 h2 ⊢
      have hz0 : -z < 0 := by
        have := lt_of_le_of_ne h1 h2
        exact (zpow_lt_one_iff_right₀ hp1).1 this
      rw [div_inv_eq_mul, ← zpow_add_one₀ hpQ]
      exact zpow_le_one_of_nonpos₀ hp1.le (by omega)
    rw [hu]
    simpa using h3
  have htr : ∀ x ∈ L, x ∈ W → ∀ y ∈ L, y ∈ W → (h x y + σ (h x y)) / p ∈ O := by
    intro x hx hxW y hy hyW
    have h1 := O.sub_mem (O.sub_mem (hdiv _ (L.add_mem hx hy) (W.add_mem hxW hyW)) (hdiv x hx hxW))
      (hdiv y hy hyW)
    convert h1 using 1
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [← hherm x y]
    ring
  have hstep : ∀ x ∈ L, x ∈ W → (θ / p) • x ∈ L := by
    intro x hx hxW
    refine hW _ (W.smul_mem _ hxW) ?_
    intro y hy hyW
    have r1 := htr x hx hxW y hy hyW
    have r2 := htr _ (hL _ hω x hx) (W.smul_mem _ hxW) y hy hyW
    have h1 := O.add_mem r2 (O.mul_mem (O.sub_mem hω O.one_mem) r1)
    convert h1 using 1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, map_div₀, map_add (f := _), map_one,
      hσθ, map_ofNat]
    field_simp
    ring
  obtain ⟨x, hxW, hx0⟩ := hne
  obtain ⟨m, hm⟩ := hscale x
  set x0 := (p : K) ^ m • x with hx0def
  have hx0W : x0 ∈ W := W.smul_mem _ hxW
  have hx00 : x0 ≠ 0 := smul_ne_zero (pow_ne_zero _ hpK) hx0
  have hiter : ∀ k : ℕ, (θ / p) ^ k • x0 ∈ L := by
    intro k
    induction k with
    | zero => simpa using hm
    | succ k ih =>
      rw [pow_succ', mul_smul]
      exact hstep _ ih (W.smul_mem _ hx0W)
  obtain ⟨u, hu⟩ := hrat x0
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hx00 (hdef _ (by simpa using hu))
  have hupos : 0 < padicNorm p u :=
    lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero hu0).symm
  have hnd : (p : ℚ)⁻¹ ≤ padicNorm p (d : ℚ) := by
    by_cases hpd : p = d
    · rw [← hpd, hnp]
    · haveI : Fact d.Prime := ⟨hd⟩
      rw [padicNorm.padicNorm_of_prime_of_ne hpd]
      exact inv_le_one_of_one_le₀ hp1.le
  have hc : (p : ℚ) ≤ padicNorm p ((d : ℚ) / (p * p)) := by
    rw [padicNorm.div, padicNorm.mul, hnp, le_div_iff₀ (by positivity)]
    calc (p : ℚ) * ((p : ℚ)⁻¹ * (p : ℚ)⁻¹) = (p : ℚ)⁻¹ := by field_simp
      _ ≤ _ := hnd
  have hpow : ∀ (q : ℚ) (k : ℕ), padicNorm p (q ^ k) = padicNorm p q ^ k := by
    intro q k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, padicNorm.mul, ih]
  have hbound : ∀ k : ℕ, (p : ℚ) ^ k * padicNorm p u ≤ 1 := by
    intro k
    have h1 := hLO _ (hiter k) _ (hiter k)
    have h2 : h ((θ / p) ^ k • x0) ((θ / p) ^ k • x0) = ((((d : ℚ) / (p * p)) ^ k * u : ℚ) : K) := by
      rw [h.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, hu, smul_eq_mul, smul_eq_mul,
        map_pow, map_div₀, hσθ, map_natCast, ← mul_assoc, ← mul_pow]
      push_cast
      congr 2
      field_simp
      linear_combination -hθ
    rw [h2, hO, padicNorm.mul, hpow] at h1
    refine le_trans ?_ h1
    gcongr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (padicNorm p u)⁻¹ hp1
  have := hbound k
  rw [inv_lt_iff_one_lt_mul₀ hupos] at hk
  linarith

end GlobalTheory
end

section

namespace GlobalTheory.ComplexValueBound

open Finset

theorem main : ∀ {ι κ M : Type} [inst : AddCommGroup M] [inst_1 : Module ℂ M] (T : κ → M →ₗ[ℂ] M) (l : ι → κ → ℂ), (∀ (i j : ι), i ≠ j → ∃ (k : κ), l i k ≠ l j k) → ∀ (s : Finset ι) (u : ι → M), (∀ (i : ι) (k : κ), (T k : M → M) (u i) = l i k • u i) → ∑ i ∈ s, u i = (0 : M) → ∀ i ∈ s, u i = (0 : M) := by
  intro ι κ M _ _ T l hl s
  classical
  induction s using Finset.induction_on with
  | empty => intro u _ _ i hi; simp at hi
  | insert a s ha ih =>
    intro u hu hsum
    rw [Finset.sum_insert ha] at hsum
    have hsa : ∑ i ∈ s, u i = -u a := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hsum
    have hs : ∀ j ∈ s, u j = 0 := by
      intro j hj
      have hne : a ≠ j := fun h => ha (h ▸ hj)
      obtain ⟨k, hk⟩ := hl a j hne
      have hvu : ∀ (i : ι) (k' : κ), (T k' : M → M) ((l i k - l a k) • u i)
          = l i k' • ((l i k - l a k) • u i) := by
        intro i k'
        rw [LinearMap.map_smul, hu, smul_comm]
      have hvsum : ∑ i ∈ s, (l i k - l a k) • u i = 0 := by
        have h1 : ∑ i ∈ s, (l i k - l a k) • u i
            = T k (∑ i ∈ s, u i) - l a k • ∑ i ∈ s, u i := by

          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hu, sub_smul]
        rw [h1, hsa, map_neg, hu, smul_neg, sub_neg_eq_add, neg_add_cancel]
      have h := ih (fun i => (l i k - l a k) • u i) hvu hvsum j hj
      exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm hk))
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have h0 : ∑ i ∈ s, u i = 0 := Finset.sum_eq_zero hs
      rw [h0, add_zero] at hsum; exact hsum
    · exact hs i hi

end GlobalTheory.ComplexValueBound
end
