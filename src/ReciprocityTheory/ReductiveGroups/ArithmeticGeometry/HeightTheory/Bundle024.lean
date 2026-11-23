module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle013
import Mathlib.Algebra.MvPolynomial.Nilpotent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem gen_ne_zero_of_mem_htOne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  obtain ⟨hpr, hh⟩ := hp
  haveI := hpr
  obtain ⟨g, hg, hpg⟩ := ValUFD.heightOne_principal p hh
  have hPr : p.IsPrincipal := ⟨⟨g, hpg⟩⟩
  unfold gen
  rw [dite_eq_left hPr]
  intro h0
  have hbot : p = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).2 h0
  rw [hbot] at hpg
  exact hg.ne_zero (Ideal.span_singleton_eq_bot.1 hpg.symm)

theorem finite_height_fraction_repr (hd : d.AxH 𝒜) (h : d.S1) :
    ∃ U V : KTp K d.D d.N, U ≠ 0 ∧ V ≠ 0 ∧ (∃ eU, IsMultiHomogeneous eU U) ∧
      (∃ eV, IsMultiHomogeneous eV V) ∧
      d.fDivE hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) V =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) U ∧
      d.h0f h d.wF hd.a4.choose = h0 U - h0 V := by
  classical
  have hspec : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hd.a4.choose_spec.1
  have hfin : ∀ c, {p | p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0}.Finite := fun c =>
    (d.good_primes_properties hd h c).2.2.1 d.wF (hd.a4.choose c) (hspec c).1 (hspec c).2
  obtain ⟨T, hmemT⟩ : ∃ T : ι → Finset (Ideal (KTp K d.D d.N)),
      ∀ c p, p ∈ T c ↔ p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0 :=
    ⟨fun c => (hfin c).toFinset, fun c p => by simp⟩
  have hmemS : ∀ x ∈ Finset.univ.sigma T,
      x.2 ∈ d.HtOne ∧ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2 ≠ 0 := by
    intro x hx
    rw [Finset.mem_sigma] at hx
    exact (hmemT _ _).1 hx.2
  have hne : ∀ x ∈ Finset.univ.sigma T, d.gen x.2 ≠ 0 := fun x hx => d.gen_ne_zero_of_mem_htOne (hmemS x hx).1
  have hmh : ∀ x ∈ Finset.univ.sigma T,
      IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen x.2)) (d.gen x.2) := by
    intro x hx
    obtain ⟨hp, hn⟩ := hmemS x hx
    refine (d.good_primes_properties hd h x.1).2.1 x.2 hp ?_
    by_contra hw
    push_neg at hw
    apply hn
    simp [nP, hw]
  have halg : ∀ x ∈ Finset.univ.sigma T,
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).2 (hne x hx)
  have key : ∀ (a : KTf K d.D d.N), a ≠ 0 → ∀ m : ℤ, a ^ m * a ^ (-m).toNat = a ^ m.toNat := by
    intro a ha m
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]
    congr 1
    omega
  refine ⟨∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat,
    ∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat,
    Finset.prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (hne x hx),
    Finset.prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (hne x hx),
    ⟨_, HeightMultiplicativity.multi_prod _ _ _ fun x hx => HeightMultiplicativity.multi_pow (hmh x hx) _⟩,
    ⟨_, HeightMultiplicativity.multi_prod _ _ _ fun x hx => HeightMultiplicativity.multi_pow (hmh x hx) _⟩, ?_, ?_⟩
  · have hfac : ∀ c, (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p) =
        ∏ p ∈ T c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
          d.nP h c d.wF (hd.a4.choose c) p := by
      intro c
      apply finprod_mem_eq_prod_of_subset
      · rintro p ⟨hp, hp1⟩
        rw [Function.mem_mulSupport] at hp1
        rw [Finset.mem_coe, hmemT]
        exact ⟨hp, fun h0' => hp1 (by rw [h0', zpow_zero])⟩
      · intro p hp
        exact ((hmemT c p).1 hp).1
    have hf : d.fDivE hd h = ∏ x ∈ Finset.univ.sigma T,
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ^ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2 := by
      rw [Finset.prod_sigma]
      unfold fDivE
      exact Finset.prod_congr rfl fun c _ => hfac c
    rw [hf, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [map_pow, map_pow]
    exact key _ (halg x hx) _
  · have hsum : ∀ c, (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p)) =
        ∑ p ∈ T c, (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p) := by
      intro c
      apply finsum_mem_eq_sum_of_subset
      · rintro p ⟨hp, hp1⟩
        rw [Function.mem_support] at hp1
        rw [Finset.mem_coe, hmemT]
        exact ⟨hp, fun h0' => hp1 (by rw [h0', Int.cast_zero, zero_mul])⟩
      · intro p hp
        exact ((hmemT c p).1 hp).1
    have hn0 : 0 < d.N + 1 := Nat.succ_pos _
    have hU : h0 (∏ x ∈ Finset.univ.sigma T,
        d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) =
        ∑ x ∈ Finset.univ.sigma T,
          ((d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2) :=
      HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T)
        (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh
    have hV : h0 (∏ x ∈ Finset.univ.sigma T,
        d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) =
        ∑ x ∈ Finset.univ.sigma T,
          ((-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2) :=
      HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T)
        (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh
    rw [hU, hV, ← Finset.sum_sub_distrib, Finset.sum_sigma]
    unfold h0f
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsum c]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← sub_mul]
    congr 1
    exact_mod_cast (Int.toNat_sub_toNat_neg _).symm

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem logNorm_nonneg (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 0 ≤ logNorm la := by
  unfold logNorm
  exact Real.log_natCast_nonneg _

theorem NlaG_nonneg (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    0 ≤ d.NlaG h (d.n1 • d.wde) d.et la :=
  Finset.sum_nonneg fun c _ => finsum_nonneg fun w => finsum_nonneg fun hw =>
    mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hd.ord_nonneg_et c _ (d.admissible_over_prime hd h la c w hw).1)

theorem Nla_le (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (f : ∀ c, A c)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    d.NlaG h d.wL f la ≤ d.NlaMM h f la + d.del * d.nu la +
      d.cc / d.i * d.NlaG h (d.n1 • d.wde) d.et la := by
  have hnn := d.NlaG_nonneg hd h la
  have hi : (0 : ℝ) ≤ d.cc / d.i := div_nonneg hd.cc_nonneg (Nat.cast_nonneg _)
  suffices key : d.NlaG h d.wL f la ≤ d.NlaMM h f la + d.del * d.nu la +
      d.cc / (2 * d.i) * d.NlaG h (d.n1 • d.wde) d.et la by
    have : d.cc / (2 * d.i) * d.NlaG h (d.n1 • d.wde) d.et la ≤ d.cc / d.i * d.NlaG h (d.n1 • d.wde) d.et la := by
      have : d.cc / (2 * d.i) = (d.cc / d.i) / 2 := by ring
      rw [this]; nlinarith
    linarith
  unfold NlaG NlaMM del
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  have hfin := (d.places_over_la hd h la c).1
  have hsum := (d.places_over_la hd h la c).2
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum ⊢
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsumR : (d.delc c : ℝ) = ∑ w ∈ hfin.toFinset, (d.fze h c w : ℝ) * (ramIdx (K := K) (d.Wres c w) la : ℝ) := by
    have e := congrArg (fun z : ℤ => (z : ℝ)) hsum
    push_cast at e
    linarith
  rw [hsumR, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  have hs := d.admissible_over_prime hd h la c w hw
  have h3 := hH1.2.2.2 c (d.Wres c w) la hs.1 hs.2.1
  have hf : (0 : ℝ) ≤ d.fze h c w := Nat.cast_nonneg _
  unfold ordMM
  push_cast
  have e : ((⨅ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c) : ℤ) : ℝ) =
    (d.Emin c (d.Wres c w) : ℝ) := rfl
  rw [e] at h3 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h3 hf]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
