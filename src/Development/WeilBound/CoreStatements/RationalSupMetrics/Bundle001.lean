module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

private theorem isMultiHomog_mul_rational_sup_metrics {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {f g : MRing ι}
    {d e : K → ℕ} (hf : IsMultiHomog f d) (hg : IsMultiHomog g e) : IsMultiHomog (f * g) (d + e) := by
  classical
  intro m hm k
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf a ha k, hg b hb k]

theorem MultiProjectiveCoordinates.exists_form_with_valuation : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), Birational y → IsRelevant (mCoordIdeal y) → ∀ (a : K → ℤ) (s : Ω), ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜), aeval z h ≠ 0 → ∃ w, HasVal y a s z w := by
  intro K _ ι _ Ω _ y hbir hrel a s
  classical
  choose i hi using hrel
  have hev : ∀ f : MRing ι, eval (fun _ => (1 : Ω)) (mConeMap y f) = aeval y f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => simp [mConeMap]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]; simp [mConeMap]
  have hy : ∀ k, y ⟨k, i k⟩ ≠ 0 := by
    intro k hk
    apply hi k
    show _ ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, hk]
  let mon : (K → ℕ) → ((Σ k, ι k) →₀ ℕ) := fun e =>
    Finsupp.equivFunOnFinite.symm (fun p => if p = ⟨p.1, i p.1⟩ then e p.1 else 0)
  have hmon_homog : ∀ e, IsMultiHomog (monomial (mon e) (1 : ℤ) : MRing ι) e := by
    intro e m hm k
    have hm' := support_monomial_subset hm
    rw [Finset.mem_singleton] at hm'
    subst hm'
    simp [mon]
  have hmon_ne : ∀ e, aeval y (monomial (mon e) (1 : ℤ) : MRing ι) ≠ 0 := by
    intro e
    rw [aeval_monomial, map_one, one_mul, Finsupp.prod]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ ?_
    rw [Finsupp.mem_support_iff] at hp
    by_cases hpe : p = ⟨p.1, i p.1⟩
    · rw [hpe]
      exact hy _
    · exact absurd (by simp [mon, hpe]) hp
  obtain ⟨Mp, hMph, hMpn⟩ : ∃ M : MRing ι, IsMultiHomog M (fun k => (a k).toNat) ∧ aeval y M ≠ 0 :=
    ⟨monomial (mon fun k => (a k).toNat) 1, hmon_homog (fun k => (a k).toNat), hmon_ne (fun k => (a k).toNat)⟩
  obtain ⟨Mn, hMnh, hMnn⟩ : ∃ M : MRing ι, IsMultiHomog M (fun k => (-a k).toNat) ∧ aeval y M ≠ 0 :=
    ⟨monomial (mon fun k => (-a k).toNat) 1, hmon_homog (fun k => (-a k).toNat), hmon_ne (fun k => (-a k).toNat)⟩
  clear hmon_homog hmon_ne
  obtain ⟨d, g0, h0, hg0, hh0, hy0, hgy0⟩ := hbir (s * aeval y Mn / aeval y Mp)
  have hH : IsMultiHomog (h0 * Mn) (d + fun k => (-a k).toNat) := isMultiHomog_mul_rational_sup_metrics hh0 hMnh
  have hG : IsMultiHomog (g0 * Mp) (d + fun k => (a k).toNat) := isMultiHomog_mul_rational_sup_metrics hg0 hMph
  refine ⟨h0 * Mn, ⟨⟨_, hH⟩, ?_⟩, ?_⟩
  · intro hmem
    have hk : mConeMap y (h0 * Mn) = 0 := RingHom.mem_ker.mp hmem
    have hz := congrArg (eval fun _ => (1 : Ω)) hk
    rw [hev, map_zero, map_mul] at hz
    exact mul_ne_zero hy0 hMnn hz
  · intro 𝕜 _ z hz
    refine ⟨aeval z (g0 * Mp) / aeval z (h0 * Mn), _, _, g0 * Mp, h0 * Mn, hG, hH, ?_, ?_, hz, ?_⟩
    · intro k
      simp only [Pi.add_apply]
      push_cast
      omega
    · rw [map_mul, map_mul, hgy0]
      field_simp
    · rw [div_mul_cancel₀ _ hz]
end

section

set_option linter.unusedSectionVars false

namespace MultiProjectiveCoordinates.Val

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mh_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem mh_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mh_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem mh_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  exact mh_add hf (mh_neg hg)

theorem map_aeval_int {σ R S : Type*} [CommRing R] [Algebra ℤ R] [CommRing S] [Algebra ℤ S]
    (φ : R →+* S) (z : σ → R) (f : MvPolynomial σ ℤ) :
    φ (aeval z f) = aeval (fun p => φ (z p)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, aeval_C, eq_intCast (algebraMap ℤ R), eq_intCast (algebraMap ℤ S), map_intCast]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X]

theorem aeval_scale {R : Type*} [CommRing R] [Algebra ℤ R] (z : (Σ k, ι k) → R) (t : K → R)
    {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval (fun p : Σ k, ι k => z p * t p.1) g = aeval z g * ∏ k, t k ^ d k := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_assoc]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← hg m hm k, ← Finset.prod_pow_eq_pow_sum]

variable {Ω : Type} [Field Ω]

theorem mem_of_form (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  have h := aeval_scale (fun p => (C (y p) : MvPolynomial K Ω)) (fun k => X k) hg
  rw [← map_aeval_int (C : Ω →+* MvPolynomial K Ω) y g, h0, map_zero, zero_mul] at h
  exact h

theorem form_vanish (y : (Σ k, ι k) → Ω) {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}
    (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (h0 : aeval y g = 0) : aeval z g = 0 :=
  hz.2 g (mem_of_form y hg h0)

end MultiProjectiveCoordinates.Val
end
