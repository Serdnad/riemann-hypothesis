module

public import Development.EtaleCohomology.EtaleSheaves.Bundle064
public import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.NormAICOf
import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.NoetherianChartOverlapFiniteComplement

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

theorem exists_pow_mul_mem (S : Subalgebra A K) (u : K) (hu : u ≠ 0) (hv : u⁻¹ ∈ S) {x : K}
    (hx : x ∈ Algebra.adjoin A ((S : Set K) ∪ {u})) : ∃ n : ℕ, u⁻¹ ^ n * x ∈ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hu]; exact S.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using S.algebraMap_mem r⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    have : u⁻¹ ^ (n + m) * (x + y) = u⁻¹ ^ m * (u⁻¹ ^ n * x) + u⁻¹ ^ n * (u⁻¹ ^ m * y) := by ring
    rw [this]
    exact S.add_mem (S.mul_mem (S.pow_mem hv _) hn) (S.mul_mem (S.pow_mem hv _) hm)
  | mul x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    have : u⁻¹ ^ (n + m) * (x * y) = (u⁻¹ ^ n * x) * (u⁻¹ ^ m * y) := by ring
    rw [this]; exact S.mul_mem hn hm

theorem pow_inv_mul_pow (t : K) (ht : t ≠ 0) (n j : ℕ) :
    (n ≤ j ∧ t⁻¹ ^ n * t ^ j = t ^ (j - n)) ∨ (j < n ∧ t⁻¹ ^ n * t ^ j = t⁻¹ ^ (n - j)) := by
  rcases le_or_gt n j with h | h
  · left
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    refine ⟨h, ?_⟩
    rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ht, one_pow, one_mul]
  · right
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    refine ⟨h, ?_⟩
    rw [Nat.add_sub_cancel_left, pow_add, mul_comm (t⁻¹ ^ j), mul_assoc, ← mul_pow, inv_mul_cancel₀ ht,
      one_pow, mul_one]

theorem noetherian_local_chart_overlap_finite_complement : LateralTheory.E.LZIdemSumNoetherian.NoetherianLocalChartOverlapFiniteComplement := by
  intro A _ _ _ K _ _ B C t hc hB _
  obtain ⟨S, hS⟩ := hB
  set R := Algebra.adjoin A ({t} : Set K)
  have hfg : (Algebra.adjoin R (S : Set K)).toSubmodule.FG :=
    fg_adjoin_of_finite S.finite_toSet (fun x hx => hc.intB x (hS ▸ Algebra.subset_adjoin hx))
  obtain ⟨G, hG⟩ := hfg
  have hRB : ∀ r : R, (r : K) ∈ B := by
    intro r
    have : R ≤ B := Algebra.adjoin_le (by simpa using hc.tB)
    exact this r.2
  have hAB : ∀ y ∈ Algebra.adjoin R (S : Set K), y ∈ B := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact hS ▸ Algebra.subset_adjoin hx
    | algebraMap r => exact hRB r
    | add x y _ _ hx hy => exact B.add_mem hx hy
    | mul x y _ _ hx hy => exact B.mul_mem hx hy
  have hGB : ∀ g ∈ G, g ∈ B := by
    intro g hg
    have : g ∈ (Algebra.adjoin R (S : Set K)).toSubmodule := hG ▸ Submodule.subset_span hg
    exact hAB g this
  have hBR : ∀ x ∈ B, x ∈ Submodule.span R (G : Set K) := by
    intro x hx
    rw [hG]
    rw [← hS] at hx
    show x ∈ Algebra.adjoin R (S : Set K)
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap a => exact ((Algebra.adjoin R (S : Set K)).restrictScalars A).algebraMap_mem a
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  have hLex : ∀ g ∈ G, ∃ n : ℕ, t⁻¹ ^ n * g ∈ C := by
    intro g hg
    have : g ∈ Algebra.adjoin A ((C : Set K) ∪ {t}) := by
      rw [← hc.glue]; exact Algebra.subset_adjoin (Or.inl (hGB g hg))
    exact exists_pow_mul_mem C t hc.ne hc.tC this
  classical
  let Lf : K → ℕ := fun g => if h : ∃ n : ℕ, t⁻¹ ^ n * g ∈ C then Classical.choose h else 0
  let L := G.sup Lf
  have hL : ∀ g ∈ G, t⁻¹ ^ L * g ∈ C := by
    intro g hg
    have h := hLex g hg
    have hle : Lf g ≤ L := Finset.le_sup hg
    have hspec : t⁻¹ ^ Lf g * g ∈ C := by
      simp only [Lf, dif_pos h]; exact Classical.choose_spec h
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, mul_comm (t⁻¹ ^ Lf g), mul_assoc]
    exact C.mul_mem (C.pow_mem hc.tC _) hspec
  let N : Submodule A K := Submodule.span A ↑((G ×ˢ Finset.range L).image (fun p => t⁻¹ ^ p.2 * p.1))
  refine ⟨N, ⟨_, rfl⟩, ?_⟩
  set T := Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C ⊔ N with hT
  have hCT : ∀ x ∈ C, x ∈ T := fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_right hx)
  have hBT : ∀ x ∈ B, x ∈ T := fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_left hx)
  have core : ∀ g ∈ G, ∀ m : ℕ, t⁻¹ ^ m * g ∈ T := by
    intro g hg m
    rcases lt_or_ge m L with h | h
    · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(g, m), Finset.mem_product.mpr ⟨hg, Finset.mem_range.mpr h⟩, rfl⟩)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      rw [hk, pow_add, mul_comm (t⁻¹ ^ L), mul_assoc]
      exact hCT _ (C.mul_mem (C.pow_mem hc.tC _) (hL g hg))
  have core2 : ∀ g ∈ G, ∀ n j : ℕ, t⁻¹ ^ n * t ^ j * g ∈ T := by
    intro g hg n j
    rcases pow_inv_mul_pow t hc.ne n j with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact hBT _ (B.mul_mem (B.pow_mem hc.tB _) (hGB g hg))
    · rw [h]; exact core g hg _
  have hspan : ∀ x ∈ Submodule.span R (G : Set K), ∀ n j : ℕ, t⁻¹ ^ n * t ^ j * x ∈ T := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g hg => exact core2 g hg
    | zero => intro n j; simp
    | add x y _ _ hx hy => intro n j; rw [mul_add]; exact T.add_mem (hx n j) (hy n j)
    | smul r x _ hx =>
      intro n j
      have hr : (r : K) ∈ (Polynomial.aeval (R := A) t).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval A t]; exact r.2
      obtain ⟨p, hp⟩ := hr
      have hp' : Polynomial.aeval t p = (r : K) := hp
      have this : r • x = (r : K) * x := rfl
      rw [this, ← hp']
      clear hp hp' this
      induction p using Polynomial.induction_on' with
      | add p q hp' hq' =>
        rw [map_add (f := _), add_mul, mul_add]
        exact T.add_mem hp' hq'
      | monomial i a =>
        rw [Polynomial.aeval_monomial]
        have : t⁻¹ ^ n * t ^ j * (algebraMap A K a * t ^ i * x) = a • (t⁻¹ ^ n * t ^ (j + i) * x) := by
          rw [Algebra.smul_def, pow_add]; ring
        rw [this]; exact T.smul_mem a (hx n (j + i))
  intro x hx
  have hx' : x ∈ Algebra.adjoin A ((B : Set K) ∪ {t⁻¹}) := hx
  obtain ⟨n, hn⟩ := exists_pow_mul_mem B t⁻¹ (inv_ne_zero hc.ne) (by rw [inv_inv]; exact hc.tB) hx'
  rw [inv_inv] at hn
  have := hspan _ (hBR _ hn) n 0
  have e : t⁻¹ ^ n * t ^ 0 * (t ^ n * x) = x := by
    rw [pow_zero, mul_one, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc.ne, one_pow, one_mul]
  rwa [e] at this

end LateralTheory.E.NoetherianChartOverlapFiniteComplement
end
end

section

noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.LZIdemPowProof

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mul_left_mem (S : Subalgebra A K) (I : Ideal A) {s y : K} (hs : s ∈ S)
    (hy : y ∈ I • Subalgebra.toSubmodule S) : s * y ∈ I • Subalgebra.toSubmodule S := by
  refine Submodule.smul_induction_on hy (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr (S.mul_mem hs hn)
  · rw [mul_add]; exact add_mem hx hy

theorem mul_right_mem (S : Subalgebra A K) (I : Ideal A) {s y : K} (hs : s ∈ S)
    (hy : y ∈ I • Subalgebra.toSubmodule S) : y * s ∈ I • Subalgebra.toSubmodule S := by
  rw [mul_comm]; exact mul_left_mem S I hs hy

theorem mul_mem_mul (S : Subalgebra A K) (I J : Ideal A) {x y : K}
    (hx : x ∈ I • Subalgebra.toSubmodule S) (hy : y ∈ J • Subalgebra.toSubmodule S) :
    x * y ∈ (I * J) • Subalgebra.toSubmodule S := by
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun a b ha hb => ?_)
  · rw [smul_mul_assoc, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_left_mem S J hn hy)
  · rw [add_mul]; exact add_mem ha hb

theorem lift_pow (S : Subalgebra A K) (x : K) (hx : x ∈ S) (hp : x * x - x ∈ mS S) (n : ℕ) :
    ∃ y ∈ S, y - x ∈ mS S ∧
      y * y - y ∈ (IsLocalRing.maximalIdeal A ^ (2 ^ n)) • Subalgebra.toSubmodule S := by
  induction n with
  | zero => exact ⟨x, hx, by simp, by simpa [mS] using hp⟩
  | succ n ih =>
    obtain ⟨y, hy, hyx, hyy⟩ := ih
    have hle : IsLocalRing.maximalIdeal A ^ (2 ^ n) ≤ IsLocalRing.maximalIdeal A :=
      Ideal.pow_le_self (by positivity)
    have h2y : y + y - 1 ∈ S := S.sub_mem (S.add_mem hy hy) S.one_mem
    have hpS : y * y - y ∈ S := S.sub_mem (S.mul_mem hy hy) hy
    refine ⟨y - (y + y - 1) * (y * y - y), S.sub_mem hy (S.mul_mem h2y hpS), ?_, ?_⟩
    · rw [show y - (y + y - 1) * (y * y - y) - x = (y - x) - (y + y - 1) * (y * y - y) by ring]
      exact sub_mem hyx (Submodule.smul_mono_left hle (mul_left_mem S _ h2y hyy))
    · have h4 : (y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - 1 - 1 - 1 ∈ S :=
        S.sub_mem (S.sub_mem (S.sub_mem (S.add_mem (S.add_mem (S.add_mem hpS hpS) hpS) hpS)
          S.one_mem) S.one_mem) S.one_mem
      have hsq := mul_mem_mul S _ _ hyy hyy
      rw [← pow_add, ← two_mul, ← pow_succ'] at hsq
      have := mul_right_mem S _ h4 hsq
      convert this using 1
      ring

theorem LZIdemPow_of : LateralTheory.E.LZIdemSumNoetherian.LZIdemPow := by
  intro A _ _ K _ _ B C t hc e f hp k
  obtain ⟨he, hf, hee, hff, hef⟩ := hp
  obtain ⟨b, hb, hbe, hbb⟩ := lift_pow B e he hee (k + 1)
  obtain ⟨c, hcC, hcf, hcc⟩ := lift_pow C f hf hff (k + 1)
  have hBD : B ≤ AdjoinInv B t := fun x hx => Algebra.subset_adjoin (Or.inl hx)
  have hCD : C ≤ AdjoinInv B t := by
    intro x hx; rw [hc.glue]; exact Algebra.subset_adjoin (Or.inl hx)
  have hbD : b ∈ AdjoinInv B t := hBD hb
  have hcD : c ∈ AdjoinInv B t := hCD hcC
  have hmono : ∀ (I : Ideal A) (S : Subalgebra A K), S ≤ AdjoinInv B t → ∀ x,
      x ∈ I • Subalgebra.toSubmodule S → x ∈ I • Subalgebra.toSubmodule (AdjoinInv B t) :=
    fun I S h x hx => Submodule.smul_mono (le_refl I) (fun y hy => h hy) hx
  have hpow : IsLocalRing.maximalIdeal A ^ (2 ^ (k + 1)) ≤ IsLocalRing.maximalIdeal A ^ (k + 1) :=
    Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le
  have hp : b * b - b ∈ (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) :=
    Submodule.smul_mono_left hpow (hmono _ B hBD _ hbb)
  have hq : c * c - c ∈ (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) :=
    Submodule.smul_mono_left hpow (hmono _ C hCD _ hcc)
  have hd1 : b - c ∈ (IsLocalRing.maximalIdeal A ^ 1) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    rw [pow_one, show b - c = (b - e) + (e - f) - (c - f) by ring]
    exact sub_mem (add_mem (hmono _ B hBD _ hbe) hef) (hmono _ C hCD _ hcf)
  have hcube : (b - c) * (b - c) * (b - c) - (b - c) ∈
      (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    rw [show (b - c) * (b - c) * (b - c) - (b - c) = (b * b - b) - (c * c - c) - (c + c) * (b * b - b)
      + (b + b) * (c * c - c) + (b - c) * (b * b - b) + (b - c) * (c * c - c) by ring]
    have hbc : b - c ∈ AdjoinInv B t := (AdjoinInv B t).sub_mem hbD hcD
    refine add_mem (add_mem (add_mem (sub_mem (sub_mem hp hq) ?_) ?_) ?_) ?_
    · exact mul_left_mem _ _ ((AdjoinInv B t).add_mem hcD hcD) hp
    · exact mul_left_mem _ _ ((AdjoinInv B t).add_mem hbD hbD) hq
    · exact mul_left_mem _ _ hbc hp
    · exact mul_left_mem _ _ hbc hq
  have key : ∀ j, j + 1 ≤ k + 1 →
      b - c ∈ (IsLocalRing.maximalIdeal A ^ (j + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    intro j
    induction j with
    | zero => intro _; simpa using hd1
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h3 := mul_mem_mul _ _ _ (mul_mem_mul _ _ _ h1 h1) h1
      rw [← pow_add, ← pow_add] at h3
      have h3' := Submodule.smul_mono_left (Ideal.pow_le_pow_right (show j + 1 + 1 ≤ j + 1 + (j + 1) + (j + 1) by omega)) h3
      have hc' := Submodule.smul_mono_left (Ideal.pow_le_pow_right hj) hcube
      rw [show b - c = (b - c) * (b - c) * (b - c) - ((b - c) * (b - c) * (b - c) - (b - c)) by ring]
      exact sub_mem h3' hc'
  refine ⟨b, hb, c, hcC, ?_, hcf, ?_⟩
  · rw [← neg_sub]; exact neg_mem hbe
  · exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (key k le_rfl)

end LateralTheory.E.LZIdemPowProof
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut Polynomial

namespace LateralTheory.E.LocalIntegralClosureRoots

theorem root_mem (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] (h : GlobalTheory.EtC.AIC A) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → ∀ x : K, aeval x p = 0 →
      ∃ a : A, algebraMap A K a = x := by
  intro n
  induction n with
  | zero =>
    intro p hn hp x hx
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hp hn
    subst h1
    simp at hx
  | succ n ih =>
    intro p hn hp x hx
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hdvd : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hq : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hdvd]; exact hp)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hdvd, map_mul] at hx
    rcases mul_eq_zero.mp hx with h1 | h1
    · refine ⟨a, ?_⟩
      simp only [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
      exact h1.symm
    · exact ih _ hqd hq x h1

theorem isIntegrallyClosed_of_aic (A : Type) [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x ⟨p, hp, hx⟩
  exact root_mem A (FractionRing A) h _ p rfl hp x (by rw [aeval_def]; exact hx)

theorem LocAIC_of : NormPf.AICPf.LocAIC := by
  intro X _ hcov
  refine ⟨inferInstance, fun V hV hVne => ?_⟩
  have : Nonempty V := hVne.to_subtype
  have hst : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := by
    intro x
    obtain ⟨U, hxU, hU, hA⟩ := hcov x
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    have := isIntegrallyClosed_of_aic _ hA
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)
  have hR : IsIntegrallyClosed Γ(X, V) := by
    apply IsIntegrallyClosed.of_localization_maximal
    intro P _ hP
    let y : PrimeSpectrum Γ(X, V) := ⟨P, hP.isPrime⟩
    have hy : hV.fromSpec y ∈ V := by
      show hV.fromSpec y ∈ (V : Set X)
      rw [← hV.range_fromSpec]; exact ⟨y, rfl⟩
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hV.fromSpec y, hy⟩ : V)
    have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec y)) P := hV.isLocalization_stalk' y hy
    have := hst (hV.fromSpec y)
    exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv P.primeCompl
      (X.presheaf.stalk (hV.fromSpec y)) (Localization.AtPrime P)).toRingEquiv
  have hK : IsAlgClosed X.functionField := by
    obtain ⟨x⟩ := ‹Nonempty V›
    obtain ⟨U, hxU, hU, hA⟩ := hcov x.1
    have : Nonempty U := ⟨⟨x.1, hxU⟩⟩
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    exact NormPf.FFPf.algClosed_of_aic _ _ hA
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  intro p hp hd
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (algebraMap Γ(X, V) X.functionField))
    (by
      rw [degree_map_eq_of_injective (IsFractionRing.injective Γ(X, V) X.functionField),
        degree_eq_natDegree hp.ne_zero]
      exact_mod_cast hd.ne')
  have hint : IsIntegral Γ(X, V) z := ⟨p, hp, by rwa [IsRoot, Polynomial.eval_map] at hz⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, IsFractionRing.injective Γ(X, V) X.functionField ?_⟩
  have hz' : eval z (p.map (algebraMap Γ(X, V) X.functionField)) = 0 := hz
  rw [map_zero, ← hz', Polynomial.eval_map, ← ha, eval₂_at_apply]

end LateralTheory.E.LocalIntegralClosureRoots

end
end
