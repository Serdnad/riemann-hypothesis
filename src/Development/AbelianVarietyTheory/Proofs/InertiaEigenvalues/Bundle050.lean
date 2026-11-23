module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Group.AddChar

@[expose] public section

section

open scoped PowerSeries Pointwise

namespace GlobalTheory.InertiaEigenvalues.PowerSeriesFree

theorem coeff_term {O : Type} [CommRing O] (l : ℕ) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0)
    (j m : ℕ) (g : O⟦X⟧) :
    PowerSeries.coeff m (PowerSeries.X ^ j * φ g) =
      if j ≤ m ∧ l ∣ (m - j) then PowerSeries.coeff ((m - j) / l) g else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases h : j ≤ m
  · simp only [h, true_and, if_true]
    exact hφ g (m - j)
  · simp [h]

theorem coeff_sum {O : Type} [CommRing O] (l : ℕ) (hl : 2 ≤ l) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0)
    (g : Fin l → O⟦X⟧) (m : ℕ) :
    PowerSeries.coeff m (∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j)) =
      PowerSeries.coeff (m / l) (g ⟨m % l, Nat.mod_lt _ (by omega)⟩) := by
  have hl0 : 0 < l := by omega

  rw [map_sum]
  rw [Finset.sum_eq_single (⟨m % l, Nat.mod_lt _ hl0⟩ : Fin l)]
  · rw [coeff_term l φ hφ]
    have h1 : m % l ≤ m := Nat.mod_le _ _
    have h2 : l ∣ m - m % l := by
      have := Nat.div_add_mod m l
      exact ⟨m / l, by omega⟩
    have h3 : (m - m % l) / l = m / l := by
      have := Nat.div_add_mod m l
      rw [show m - m % l = l * (m / l) by omega]
      exact Nat.mul_div_cancel_left _ hl0
    simp only [h1, h2, and_self, if_true, h3]
  · intro j _ hj
    rw [coeff_term l φ hφ]
    rw [if_neg]
    rintro ⟨hjm, k, hk⟩
    apply hj
    ext
    simp only
    have hjl := j.isLt
    have : m = l * k + j.val := by omega
    rw [this, Nat.mul_add_mod]
    exact (Nat.mod_eq_of_lt hjl).symm
  · intro h; exact absurd (Finset.mem_univ _) h

theorem main : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧, f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j) := by
  intro O _ l hl φ hφ f
  have hl0 : 0 < l := by omega
  refine ⟨fun j => PowerSeries.mk (fun n => PowerSeries.coeff (n * l + j.val) f), ?_, ?_⟩
  · ext m
    rw [coeff_sum l hl φ hφ, PowerSeries.coeff_mk]
    simp only
    rw [Nat.div_add_mod']
  · intro g hg
    funext j
    ext n
    rw [PowerSeries.coeff_mk, hg, coeff_sum l hl φ hφ]
    have hj := j.isLt
    have e1 : (n * l + j.val) / l = n := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hl0, Nat.div_eq_of_lt hj, Nat.zero_add]
    have e2 : (n * l + j.val) % l = j.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [e1, e2]

end GlobalTheory.InertiaEigenvalues.PowerSeriesFree
end

section

namespace GlobalTheory


open PowerSeries in
theorem powerSeries_eq_C_of_subst_eq_self (L : Type) [Field L] (y : PowerSeries L)
    (hy : PowerSeries.constantCoeff y = 0)
    (hu : ∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) (a : PowerSeries L)
    (ha : (PowerSeries.subst y a : PowerSeries L) = a) :
    a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  classical
  obtain ⟨z, rfl⟩ : X ∣ y := by rwa [PowerSeries.X_dvd_iff]
  have hs : HasSubst (X * z) := HasSubst.of_constantCoeff_zero' hy
  have hu1 : coeff 1 (X * z) = constantCoeff z := by
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [hu1] at hu

  have hc : ∀ n, coeff n (a.subst (X * z)) =
      ∑ d ∈ Finset.range (n + 1), coeff d a * coeff (n - d) (z ^ d) := by
    intro n
    rw [coeff_subst' hs, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [mul_pow, coeff_X_pow_mul', if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)),
        smul_eq_mul]
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

  have main : ∀ k, 0 < k → coeff k a = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have h1 := hc k
      rw [ha, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self,
        coeff_zero_eq_constantCoeff_apply, map_pow] at h1
      · have h2 : coeff k a * (1 - constantCoeff z ^ k) = 0 := by
          rw [mul_sub, mul_one, ← h1, sub_self]
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h).symm (hu k hk)
      · intro d hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp [coeff_one, hk.ne']
        · rw [ih d (Finset.mem_range.mp hd) hd0, zero_mul]
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_C, if_neg (Nat.succ_ne_zero n)]
    exact main (n + 1) (Nat.succ_pos n)

end GlobalTheory
end

section

namespace GlobalTheory

private lemma char_eq_of_same_coset {G M : Type} [Group G] [CommGroup M]
    (Ik H : Subgroup G) (ψ : ↥Ik →* M) (hψ : ∀ s : ↥Ik, (s : G) ∈ H → ψ s = 1)
    (g s t : G) (hs : s ∈ Ik) (ht : t ∈ Ik) (h1 : s⁻¹ * g ∈ H) (h2 : t⁻¹ * g ∈ H) :
    ψ ⟨s, hs⟩ = ψ ⟨t, ht⟩ := by
  have hmem : ((⟨s, hs⟩⁻¹ * ⟨t, ht⟩ : ↥Ik) : G) ∈ H := by
    have h3 : s⁻¹ * t = (s⁻¹ * g) * (t⁻¹ * g)⁻¹ := by group
    have h5 : s⁻¹ * t ∈ H := by
      rw [h3]
      exact H.mul_mem h1 (H.inv_mem h2)
    exact h5
  have h4 := hψ _ hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h4
  exact h4

theorem exists_extend_character_trivial_on_normal {G M : Type} [Group G] [CommGroup M]
    (I Ik H : Subgroup G) (hH : H.Normal) (hdec : ∀ g ∈ I, ∃ s ∈ Ik, s⁻¹ * g ∈ H)
    (ψ : ↥Ik →* M) (hψ : ∀ s : ↥Ik, (s : G) ∈ H → ψ s = 1) :
    ∃ χ : ↥I →* M, ∀ (g : ↥I) (s : G) (hs : s ∈ Ik), s⁻¹ * (g : G) ∈ H → χ g = ψ ⟨s, hs⟩ := by
  classical
  choose f hfIk hfH using hdec
  have key := char_eq_of_same_coset Ik H ψ hψ
  refine ⟨{ toFun := fun g => ψ ⟨f g g.2, hfIk g g.2⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · show ψ ⟨f _ _, _⟩ = 1
    rw [key _ _ 1 _ Ik.one_mem (hfH _ _) (by simp)]
    exact map_one ψ
  · intro a b
    show ψ ⟨f _ _, _⟩ = ψ ⟨f _ _, _⟩ * ψ ⟨f _ _, _⟩
    have hab : (f a a.2 * f b b.2)⁻¹ * ((a * b : ↥I) : G) ∈ H := by
      show (f a a.2 * f b b.2)⁻¹ * ((a : G) * b) ∈ H
      have hc := hH.conj_mem _ (hfH a a.2) (f b b.2)⁻¹
      have he : (f a a.2 * f b b.2)⁻¹ * ((a : G) * b)
          = ((f b b.2)⁻¹ * ((f a a.2)⁻¹ * a) * (f b b.2)⁻¹⁻¹) * ((f b b.2)⁻¹ * b) := by group
      rw [he]
      exact H.mul_mem hc (hfH b b.2)
    rw [key ((a * b : ↥I) : G) _ (f a a.2 * f b b.2) _ (Ik.mul_mem (hfIk a a.2) (hfIk b b.2))
      (hfH _ _) hab]
    exact map_mul ψ ⟨f a a.2, hfIk a a.2⟩ ⟨f b b.2, hfIk b b.2⟩
  · intro g s hs hsg
    exact key g _ s _ hs (hfH g g.2) hsg

theorem extend_characters_and_generator : ∀ {G F LL : Type} [Group G] [Field F] [Field LL] (I Ik H : Subgroup G), H.Normal → Ik ≤ I → (∀ g ∈ I, ∃ s ∈ Ik, s⁻¹ * g ∈ H) → ∀ (n : ℕ), 0 < n → ∀ (Ψ : ↥(rootsOfUnity n F) →* (↥Ik →* LLˣ)) (Y : Set F), (∀ y ∈ Y, ∃ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) = y) → (∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) ∈ Y → ∀ s : ↥Ik, (s : G) ∈ H → Ψ u s = 1) → ∃ ch : F → (↥I →* LLˣ), (∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) ∈ Y → ∀ (g : ↥I) (s : G) (hs : s ∈ Ik), s⁻¹ * (g : G) ∈ H → ch ((u : Fˣ) : F) g = Ψ u ⟨s, hs⟩) ∧ ∃ c : ↥I →* LLˣ, (∀ g, c g ^ n = 1) ∧ ∀ y ∈ Y, ∃ k : ℕ, ∀ g, ch y g = c g ^ k := by
  intro G F LL _ _ _ I Ik H hH _ hdec n hn Ψ Y hY hΨ
  classical
  have : NeZero n := ⟨hn.ne'⟩
  let K : Subgroup ↥(rootsOfUnity n F) :=
    { carrier := {u | ∀ s : ↥Ik, (s : G) ∈ H → Ψ u s = 1}
      mul_mem' := fun {a b} ha hb s hs => by
        simp only [Set.mem_ofPred_eq] at ha hb
        rw [map_mul, MonoidHom.mul_apply, ha s hs, hb s hs, mul_one]
      one_mem' := fun s _ => by rw [map_one, MonoidHom.one_apply]
      inv_mem' := fun {a} ha s hs => by
        simp only [Set.mem_ofPred_eq] at ha
        rw [map_inv, MonoidHom.inv_apply, ha s hs, inv_one] }
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := ↥K)
  obtain ⟨c, hc⟩ := exists_extend_character_trivial_on_normal I Ik H hH hdec
    (Ψ (ζ : ↥(rootsOfUnity n F))) (fun s hs => ζ.2 s hs)
  have hk : ∀ y ∈ Y, ∃ k : ℕ, ∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) = y →
      (ζ : ↥(rootsOfUnity n F)) ^ k = u := by
    intro y hy
    obtain ⟨u₀, hu₀⟩ := hY y hy
    have hK : u₀ ∈ K := hΨ u₀ (hu₀ ▸ hy)
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := ζ) (y := ⟨u₀, hK⟩)).mpr (hζ _)
    refine ⟨k, fun u hu => ?_⟩
    have hu' : u = u₀ := Subtype.ext (Units.ext (hu.trans hu₀.symm))
    rw [hu']
    have := congrArg (fun v : ↥K => (v : ↥(rootsOfUnity n F))) hk
    simpa using this
  choose! kk hkk using hk
  have hpow : (ζ : ↥(rootsOfUnity n F)) ^ n = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact (mem_rootsOfUnity n _).mp (ζ : ↥(rootsOfUnity n F)).2
  refine ⟨fun y => c ^ kk y, ?_, c, ?_, ?_⟩
  · intro u hu g s hs hsg
    show (c ^ kk ((u : Fˣ) : F)) g = Ψ u ⟨s, hs⟩
    rw [MonoidHom.pow_apply, hc g s hs hsg, ← MonoidHom.pow_apply, ← map_pow,
      hkk _ hu u rfl]
  · intro g
    obtain ⟨s, hs, hsg⟩ := hdec g g.2
    rw [hc g s hs hsg, ← MonoidHom.pow_apply, ← map_pow, hpow, map_one, MonoidHom.one_apply]
  · intro y _
    exact ⟨kk y, fun g => MonoidHom.pow_apply c (kk y) g⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem eq_of_root_congr_of_deriv_unit {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : Polynomial ℤ) (β β' : Ω)
    (hβ : A.valuation β ≤ 1) (hβ' : A.valuation β' ≤ 1) (h0 : Polynomial.aeval β f = 0) (h0' : Polynomial.aeval β' f = 0)
    (hd : ¬ A.valuation (Polynomial.aeval β (Polynomial.derivative f)) < 1) (hs : A.valuation (β - β') < 1) : β = β' := by
  by_contra hne
  have hb : β ∈ A := (A.valuation_le_one_iff β).mp hβ
  have hb' : β' ∈ A := (A.valuation_le_one_iff β').mp hβ'
  set b : A := ⟨β, hb⟩
  set b' : A := ⟨β', hb'⟩
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map (algebraMap ℤ A)) b (b' - b)
  rw [add_sub_cancel, derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap] at hk
  have hc := congrArg (fun x : A => (x : Ω)) hk
  have e : ∀ (p : ℤ[X]) (x : A), ((aeval x p : A) : Ω) = aeval (x : Ω) p := by
    intro p x
    exact (aeval_algebraMap_apply Ω x p).symm
  push_cast at hc
  rw [e, e, e] at hc
  have hβ0 : (b : Ω) = β := rfl
  have hβ1 : (b' : Ω) = β' := rfl
  rw [hβ0, hβ1, h0, h0'] at hc
  have hne' : β' - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hD : aeval β (derivative f) = -((k : Ω) * (β' - β)) := by
    have : (β' - β) * (aeval β (derivative f) + (k : Ω) * (β' - β)) = 0 := by linear_combination -hc
    have := (mul_eq_zero.mp this).resolve_left hne'
    linear_combination this
  apply hd
  rw [hD, Valuation.map_neg, Valuation.map_mul, Valuation.map_sub_swap]
  have hk1 : A.valuation (k : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr k.2
  calc A.valuation (k : Ω) * A.valuation (β - β') ≤ 1 * A.valuation (β - β') := by gcongr
    _ = A.valuation (β - β') := one_mul _
    _ < 1 := hs

end GlobalTheory
end

section

namespace GlobalTheory.RootValuationOne

open Finset

theorem sub_pow_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {x y : Ω}
    (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1) (hd : A.valuation (x - y) < 1) (i : ℕ) :
    A.valuation (x ^ i - y ^ i) < 1 := by
  rw [← geom_sum₂_mul, map_mul]
  have hs : A.valuation (∑ j ∈ range i, x ^ j * y ^ (i - 1 - j)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro j _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' hx _) (pow_le_one' hy _)
  calc _ ≤ 1 * A.valuation (x - y) := by gcongr
    _ < 1 := by rw [one_mul]; exact hd

theorem val_root_eq_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ} (hn0 : n ≠ 0)
    {x : Ω} (hx : x ^ n = 1) : A.valuation x = 1 := by
  have h : A.valuation x ^ n = 1 := by rw [← map_pow, hx, map_one]
  rcases lt_trichotomy (A.valuation x) 1 with h' | h' | h'
  · exact absurd h (pow_lt_one₀ zero_le' h' hn0).ne
  · exact h'
  · exact absurd h (one_lt_pow₀ h' hn0).ne'

theorem main : ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) (n : ℕ),
    ¬(ValuationSubring.valuation A : Ω → ValuationSubring.ValueGroup A) (↑n : Ω) < (1 : ValuationSubring.ValueGroup A) →
    ∀ {ξ ξ' : Ω}, ξ ^ n = (1 : Ω) → ξ' ^ n = (1 : Ω) →
    (ValuationSubring.valuation A : Ω → ValuationSubring.ValueGroup A) (ξ - ξ') < (1 : ValuationSubring.ValueGroup A) → ξ = ξ' := by
  intro Ω _ A n hn ξ ξ' h1 h2 hd
  have hn0 : n ≠ 0 := by rintro rfl; apply hn; simp
  have hv1 := val_root_eq_one A hn0 h1
  have hv2 := val_root_eq_one A hn0 h2
  by_contra hne
  have hs : ∑ i ∈ range n, ξ ^ i * ξ' ^ (n - 1 - i) = 0 := by
    have := geom_sum₂_mul ξ ξ' n
    rw [h1, h2, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hlt : A.valuation (∑ i ∈ range n, (ξ ^ i * ξ' ^ (n - 1 - i) - ξ' ^ (n - 1))) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro i hi
    have hi' : i + (n - 1 - i) = n - 1 := by
      have := mem_range.mp hi; omega
    have e : ξ ^ i * ξ' ^ (n - 1 - i) - ξ' ^ (n - 1) = (ξ ^ i - ξ' ^ i) * ξ' ^ (n - 1 - i) := by
      rw [sub_mul, ← pow_add, hi']
    rw [e, map_mul, map_pow, hv2, one_pow, mul_one]
    exact sub_pow_lt_one A hv1.le hv2.le hd i
  rw [sum_sub_distrib, hs, sum_const, card_range, zero_sub, Valuation.map_neg, nsmul_eq_mul,
    map_mul, map_pow, hv2, one_pow, mul_one] at hlt
  exact hn hlt

end GlobalTheory.RootValuationOne
end

section

open scoped NNReal

namespace GlobalTheory

theorem WittVector.ghostComponent_injective_of_noTorsion :
    ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
      ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  intro l _ A _ hA x y h
  have hpow : ∀ (k : ℕ) (a : A), ((l : ℕ) : A) ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      apply hA
      apply ih
      rw [← mul_assoc, ← pow_succ]
      exact ha
  apply _root_.WittVector.ext
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := h n
    rw [_root_.WittVector.ghostComponent_apply, _root_.WittVector.ghostComponent_apply,
      wittPolynomial_eq_sum_C_mul_X_pow] at hn

    simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    eq_intCast, Int.cast_natCast, map_natCast] at hn
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hn
    have hs : ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * x.coeff i ^ l ^ (n - i) =
        ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * y.coeff i ^ l ^ (n - i) :=
      Finset.sum_congr rfl (fun i hi => by rw [ih i (Finset.mem_range.1 hi)])
    rw [hs, add_left_cancel_iff, Nat.sub_self, pow_zero, pow_one, pow_one] at hn
    apply sub_eq_zero.1
    apply hpow n
    rw [mul_sub, hn, sub_self]

end GlobalTheory
end

section

open scoped NNReal
open Finset

namespace GlobalTheory.DworkGhost


open scoped Classical in
open Classical in
noncomputable def coeff {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) : ℕ → A
  | n => if h : ((l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i))
      then h.choose else 0
decreasing_by exact i.isLt

theorem coeff_spec {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) (n : ℕ)
    (h : (l : A) ^ n ∣ φ^[n] a - ∑ i ∈ range n, (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  have h' : (l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i) := by
    rwa [Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n]
  have e : coeff l φ a n = h'.choose := by
    rw [coeff, dite_eq_left h']
  have hc := h'.choose_spec
  rw [← e, Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n] at hc
  rw [sum_range_succ, Nat.sub_self, pow_zero, pow_one, ← hc]
  ring

theorem ghost_eq {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A)
    (hφ : ∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) (a : A) (n : ℕ) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  induction n with
  | zero => exact coeff_spec l φ a 0 (by simp)
  | succ n ih =>
    apply coeff_spec

    rw [Function.iterate_succ_apply', ih, map_sum, ← sum_sub_distrib]
    apply dvd_sum
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [map_mul, map_pow, map_pow, map_natCast, ← mul_sub]
    have e1 : n + 1 = i + (n - i + 1) := by omega
    have e2 : n + 1 - i = n - i + 1 := by omega
    have e3 : coeff l φ a i ^ l ^ (n - i + 1) = (coeff l φ a i ^ l) ^ l ^ (n - i) := by
      rw [pow_succ', pow_mul]
    rw [e2, e3, e1, pow_add]
    exact mul_dvd_mul_left _ (dvd_sub_pow_of_dvd_sub (hφ (coeff l φ a i)) (n - i))

theorem exists_witt_ghost_iterate : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A),
    (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A,
      ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  intro l _ A _ φ hφ a
  refine ⟨WittVector.mk l (coeff l φ a), fun n => ?_⟩
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial, ghost_eq l φ hφ a n]

end GlobalTheory.DworkGhost
end

section

namespace GlobalTheory

theorem natCard_addMonoidHom_zmod_le (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] [Finite A] :
    Nat.card (A →+ ZMod N) ≤ Nat.card A := by
  classical
  have : Fintype A := Fintype.ofFinite A

  have hinj : Function.Injective fun f : A →+ ZMod N ↦ (ZMod.stdAddChar (N := N)).compAddMonoidHom f :=
    AddChar.compAddMonoidHom_injective_right _ ZMod.injective_stdAddChar
  calc Nat.card (A →+ ZMod N) ≤ Nat.card (AddChar A ℂ) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card A := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

end GlobalTheory
end
