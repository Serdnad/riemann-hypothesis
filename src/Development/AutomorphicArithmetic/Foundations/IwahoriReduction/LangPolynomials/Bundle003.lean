module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

variable {l : ℕ} [Fact l.Prime]

private theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c := c) ((u : c.O)).2
  have h2 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c := c) (((u⁻¹ : c.Oˣ) : c.O)).2
  have h3 : ((u : c.O) : PadicAlgCl l) * (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  have h4 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, h3, norm_one]
  nlinarith [norm_nonneg ((u : c.O) : PadicAlgCl l), norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)]

private theorem norm_pos_and_lt_one_of_irreducible (c : Coef l) (ϖ : c.O) (hϖ : Irreducible ϖ) :
    0 < ‖(ϖ : PadicAlgCl l)‖ ∧ ‖(ϖ : PadicAlgCl l)‖ < 1 := by
  haveI := c.dvr
  have hne : (ϖ : PadicAlgCl l) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  refine ⟨norm_pos_iff.2 hne, ?_⟩
  have hl : (l : c.O) ≠ 0 := by
    intro h
    apply (GlobalTheory.LambdaValuationPowers.natCast_ne_zero (l := l))
    have := congrArg (fun z : c.O => (z : PadicAlgCl l)) h
    simpa using this
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  have h1 : ‖((l : c.O) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ e := by
    rw [he]
    push_cast
    rw [norm_mul, norm_unit c u, one_mul, norm_pow]
  have h2 : ‖((l : c.O) : PadicAlgCl l)‖ < 1 := by
    have := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)
    simpa using this
  have h3 : ‖(ϖ : PadicAlgCl l)‖ ≤ 1 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem ϖ.2
  rcases h3.lt_or_eq with h | h
  · exact h
  · rw [h1, h, one_pow] at h2
    exact absurd h2 (lt_irrefl 1)

private theorem dvd_of_norm_le (c : Coef l) (x y : c.O) (hy : y ≠ 0)
    (h : ‖(x : PadicAlgCl l)‖ ≤ ‖(y : PadicAlgCl l)‖) : y ∣ x := by
  haveI := c.dvr
  by_cases hx : x = 0
  · rw [hx]
    exact dvd_zero y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨h0, h1⟩ := norm_pos_and_lt_one_of_irreducible c ϖ hϖ
  have hn : ∀ (k : ℕ) (w : c.Oˣ),
      ‖(((w : c.O) * ϖ ^ k : c.O) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ k := by
    intro k w
    push_cast
    rw [norm_mul, norm_unit c w, one_mul, norm_pow]
  obtain ⟨a, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  obtain ⟨b, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [hn, hn] at h
  have hba : b ≤ a := (pow_le_pow_iff_right_of_lt_one₀ h0 h1).1 h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hba
  refine ⟨((v⁻¹ : c.Oˣ) : c.O) * u * ϖ ^ k, ?_⟩
  calc (u : c.O) * ϖ ^ (b + k) = ((v : c.O) * ((v⁻¹ : c.Oˣ) : c.O)) * u * ϖ ^ (b + k) := by
        rw [Units.mul_inv, one_mul]
    _ = _ := by ring

private theorem div_pow_of_cg (c : Coef l) (n : ℕ) (x : c.O) (h : Cg n (x : PadicAlgCl l) 0) :
    ∃ y : c.O, x = (l : c.O) ^ n * y := by
  have hl0 : (l : c.O) ≠ 0 := fun h0 => GlobalTheory.LambdaValuationPowers.natCast_ne_zero (l := l) (by simpa using congrArg Subtype.val h0)
  refine dvd_of_norm_le c x _ (pow_ne_zero n hl0) ?_
  simpa [Cg] using h

theorem pBasEx : SBasEx := by
  intro l _ c
  haveI := c.fin
  haveI := c.dvr
  refine ⟨⟨⟨_, Module.finBasis ℤ_[l] c.O⟩⟩, fun β => ⟨fun i => GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (β.e i).2,
    ?_, fun n x h => div_pow_of_cg c n x h, ?_⟩⟩
  · intro n x h i
    have hzc : ((∑ j, x j • β.e j : c.O) : PadicAlgCl l)
        = ∑ j, β.val j * algebraMap ℤ_[l] (PadicAlgCl l) (x j) := by
      simp [Bas.val, Algebra.smul_def, mul_comm]
    obtain ⟨y, hy⟩ := div_pow_of_cg c n (∑ j, x j • β.e j) (by rw [hzc]; exact h)
    have hs : (∑ j, x j • β.e j : c.O) = ((l : ℤ_[l]) ^ n) • y := by
      rw [hy, Algebra.smul_def, map_pow, map_natCast]
    have hx : β.e.repr (∑ j, x j • β.e j) i = x i := by
      rw [β.e.repr_sum_self]
    refine ⟨β.e.repr y i, ?_⟩
    rw [← hx, hs, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · intro x hx h1
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at h1
    obtain ⟨z, hz⟩ := dvd_of_norm_le c 1 ⟨x, hx⟩
      (fun h0 => hx0 (by simpa using congrArg Subtype.val h0)) (by simp [h1])
    have hz' : (1 : PadicAlgCl l) = x * (z : PadicAlgCl l) := by
      have := congrArg Subtype.val hz
      simpa using this
    rw [← eq_inv_of_mul_eq_one_right hz'.symm]
    exact z.2

end UpperTheory.Kd.C7
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem term_le {R K : Type} [CommRing R] [NormedField K] (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1) (t : K)
    (h : PowerSeries R) (i : ℕ) : ‖f (h.coeff i) * t ^ i‖ ≤ ‖t‖ ^ i := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) (hf _)

private theorem summ {R K : Type} [CommRing R] [NormedField K] (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1) (t : K) (ht : ‖t‖ < 1)
    (h : PowerSeries R) : Summable fun i => ‖f (h.coeff i) * t ^ i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_le f hf t h)
    (summable_geometric_of_lt_one (norm_nonneg _) ht)

private theorem exE {R K : Type} [CommRing R] [NormedField K] [CompleteSpace K] (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1)
    (t : K) (ht : ‖t‖ < 1) : ∃ E : PowerSeries R →+* K, ∀ h, E h = ∑' i, f (h.coeff i) * t ^ i := by
  refine ⟨{ toFun := fun h => ∑' i, f (h.coeff i) * t ^ i
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun _ => rfl⟩
  · rw [tsum_eq_single 0]
    · simp
    · intro b hb; simp [PowerSeries.coeff_one, hb]
  · intro a b
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summ f hf t ht a) (summ f hf t ht b)]
    refine tsum_congr fun n => ?_

    rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_mul, pow_add]; ring
  · simp
  · intro a b
    rw [← Summable.tsum_add (summ f hf t ht a).of_norm (summ f hf t ht b).of_norm]
    refine tsum_congr fun n => ?_
    rw [map_add (f := _), map_add (f := _), add_mul]

private theorem tail {R K : Type} [CommRing R] [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1) (t : K) (ht : ‖t‖ < 1) (h : PowerSeries R) (N : ℕ) :
    ‖(∑' i, f (h.coeff i) * t ^ i) - ∑ i ∈ Finset.range N, f (h.coeff i) * t ^ i‖ ≤ ‖t‖ ^ N := by
  rw [← (summ f hf t ht h).of_norm.sum_add_tsum_nat_add N, add_sub_cancel_left]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_
  exact (term_le f hf t h _).trans (pow_le_pow_of_le_one (norm_nonneg _) ht.le (by omega))

private theorem rootb {K : Type} [NormedField K] [IsUltrametricDist K] (l m : ℕ) (hl : l.Prime) (h2 : l ≠ 2)
    (z : K) (hz : z ^ l ^ m = 1) : ‖z - 1‖ ^ l ^ m ≤ ‖(l : K)‖ :=
  _root_.UpperTheory.Reformulated.B.Qh18.rootb l m hl h2 z hz

theorem UpperTheory.Kd.C7.pEvHom :
    UpperTheory.Kd.C7.SEvHom := by
  intro l hl h2 Ω _ _ _ A _ j Φ m hm z hz
  have hb := rootb l m hl.out h2 z hz.pow_eq_one
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have ht : ‖z - 1‖ < 1 := by
    by_contra hc
    exact absurd (hb.trans_lt hl1) (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))
  obtain ⟨E, hE⟩ := exE Φ.jh Φ.jh_le (z - 1) ht
  have hC : ∀ x, E (PowerSeries.C x) = Φ.jh x := by
    intro x
    rw [hE, tsum_eq_single 0]
    · simp
    · intro b hb; simp [PowerSeries.coeff_C, hb]
  have hX : E (1 + PowerSeries.X) = z := by
    rw [map_add (f := _), map_one, hE, tsum_eq_single 1]
    · simp
    · intro b hb; simp [PowerSeries.coeff_X, hb]
  have hcyc : E (GlobalTheory.Col.cyc Φ.R l m) = 0 := by
    have : E.comp PowerSeries.C = Φ.jh := RingHom.ext hC
    rw [GlobalTheory.Col.cyc, Polynomial.hom_eval₂, this, hX, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hz.isRoot_cyclotomic (pow_pos hl.out.pos m)
  refine ⟨Ideal.Quotient.lift _ E (fun a ha => ?_), fun y => ?_, hC, hX, fun h => ?_⟩
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hcyc, mul_zero]
  · obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := tail Φ.jh Φ.jh_le (z - 1) ht h 0
    rw [Ideal.Quotient.lift_mk, hE]
    simpa using this
  · rw [Ideal.Quotient.lift_mk, hE]
    refine (tail Φ.jh Φ.jh_le (z - 1) ht h _).trans ?_
    have hle : l ^ m * m ≤ l ^ (3 * m) := by
      rw [show 3 * m = m + 2 * m by ring, pow_add]
      exact Nat.mul_le_mul_left _ (le_trans (by omega) (Nat.lt_pow_self hl.out.one_lt).le)
    refine (pow_le_pow_of_le_one (norm_nonneg _) ht.le hle).trans ?_
    rw [pow_mul, norm_pow]
    exact pow_le_pow_left₀ (by positivity) hb m
end
