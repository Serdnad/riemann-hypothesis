module

public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import ReciprocityTheory.DualLattices.Bundle001
public import ReciprocityTheory.DualLattices.Bundle008
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Mathlib.Algebra.Order.Ring.Pow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory

theorem exists_isPrime_ne_bot_lt_maximalIdeal_of_two_le_ringKrullDim (R : Type) [CommRing R]
    [IsLocalRing R] (h : 2 ≤ ringKrullDim R) :
    ∃ q : Ideal R, q.IsPrime ∧ q ≠ ⊥ ∧ q < maximalIdeal R := by
  obtain ⟨l, hl⟩ : ∃ l : LTSeries (PrimeSpectrum R), l.length = 2 :=
    Order.le_krullDim_iff.mp (by exact_mod_cast h)
  let i0 : Fin l.length := ⟨0, by omega⟩
  let i1 : Fin l.length := ⟨1, by omega⟩
  have h01 : l i0.succ = l i1.castSucc := congrArg l (Fin.ext rfl)
  have s0 := l.step i0
  have s1 := l.step i1
  rw [h01] at s0
  refine ⟨(l i1.castSucc).asIdeal, (l i1.castSucc).isPrime, ?_, ?_⟩
  · intro h0
    have : (l i0.castSucc).asIdeal < (l i1.castSucc).asIdeal := s0
    rw [h0] at this
    exact not_lt_bot this
  · exact lt_of_lt_of_le (show (l i1.castSucc).asIdeal < (l i1.succ).asIdeal from s1)
      (le_maximalIdeal (l i1.succ).isPrime.ne_top)

end GlobalTheory

namespace GlobalTheory

open Pointwise

theorem modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing :
    ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [IsDomain A]
      [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A],
      2 ≤ ringKrullDim R → ReciprocityTheory.CA.ModDepthGE R A 2 := by
  intro R A _ _ _ _ _ _ _ _ hdim
  obtain ⟨hRd, hRic⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R
  haveI : IsNoetherianRing A := isNoetherian_of_tower R inferInstance
  have hinj := FaithfulSMul.algebraMap_injective R A
  obtain ⟨q, hq, hq0, hqm⟩ := exists_isPrime_ne_bot_lt_maximalIdeal_of_two_le_ringKrullDim R hdim
  have hm0 : maximalIdeal R ≠ ⊥ := (bot_le.trans_lt hqm).ne'
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm0
  have hx' : algebraMap R A x ≠ 0 := (map_ne_zero_iff _ hinj).mpr hx0
  have hreg : IsSMulRegular A x := by
    intro a b hab
    simp only [Algebra.smul_def] at hab
    exact mul_left_cancel₀ hx' hab

  have hmemx : ∀ a : A, a ∈ x • (⊤ : Submodule R A) ↔ a ∈ Ideal.span {algebraMap R A x} := by
    intro a
    rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, by rw [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, Submodule.mem_top, by rw [Algebra.smul_def, mul_comm]⟩

  obtain ⟨y, hym, hyreg⟩ : ∃ y ∈ maximalIdeal R, IsSMulRegular (QuotSMulTop x A) y := by
    by_contra hno
    push_neg at hno
    have hfin := associatedPrimes.finite R (QuotSMulTop x A)
    have hsub : (maximalIdeal R : Set R) ⊆
        ⋃ p ∈ associatedPrimes R (QuotSMulTop x A), (p : Set R) := by
      intro y hy
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact hno y hy
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun p hp _ _ => (hfin.mem_toFinset.mp hp).isPrime)).mp (by simpa using hsub)
    rw [hfin.mem_toFinset] at hp
    have hpm : p = maximalIdeal R :=
      (le_antisymm (le_maximalIdeal (hp.isPrime.ne_top)) hmp)
    rw [hpm] at hp
    obtain ⟨-, w, hw⟩ := isAssociatedPrime_iff.mp hp
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hmz : ∀ a ∈ maximalIdeal R, algebraMap R A a * z ∈ Ideal.span {algebraMap R A x} := by
      intro a ha
      rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, hmemx] at ha
      simpa [Algebra.smul_def] using ha
    have hz : z ∉ Ideal.span {algebraMap R A x} := by
      intro hz
      apply (maximalIdeal.isMaximal R).ne_top
      rw [hw, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton, Submodule.mem_bot, one_smul,
        Submodule.Quotient.mk_eq_zero, hmemx]
      exact hz
    set I := Ideal.span {algebraMap R A x}
    have hzq : (Ideal.Quotient.mk I z : A ⧸ I) ≠ 0 := by
      rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hzq
    haveI hPp : P.IsPrime := hP.isPrime
    have hmP : maximalIdeal R ≤ P.comap (algebraMap R A) := by
      intro a ha
      apply hle
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hmz a ha
    have hPm : P.comap (algebraMap R A) = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_isPrime _ P).ne_top hmP).symm
    haveI : P.LiesOver (maximalIdeal R) := ⟨hPm.symm⟩
    obtain ⟨Q, hQP, hQp, hQq⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := A) P hqm
    have h1 : P.height = 1 := height_eq_one_of_mem_associatedPrimes hx' hP
    have hlt : Q.height < P.height := Ideal.height_strict_mono_of_isPrime hQP
    rw [h1, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at hlt
    apply hq0
    rw [hQq.over, hlt]
    exact Ideal.comap_bot_of_injective _ hinj
  refine ⟨[x, y], rfl, (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption), ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption),
    RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
  exact ⟨hreg, hyreg, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩

end GlobalTheory
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.ExpWeightTwoRadii

variable {C : Type} [Field C] {M : ℕ}

def WtBelow (v : AddValuation C (WithTop ℝ)) (ρ : Fin M → ℝ) (D : ℕ)
    (g : MvPowerSeries (Fin M) C) (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, Finsupp.degree α < D →
    (((r - ∑ m, ρ m * (α m : ℝ) : ℝ)) : WithTop ℝ) ≤ v (coeff α g)

theorem wt_add_index (ρ : Fin M → ℝ) (β γ : Fin M →₀ ℕ) :
    ∑ m, ρ m * ((β + γ) m : ℝ) = (∑ m, ρ m * (β m : ℝ)) + ∑ m, ρ m * (γ m : ℝ) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finsupp.add_apply, Nat.cast_add, mul_add]

theorem WtBelow.mul {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g h : MvPowerSeries (Fin M) C} {r s : ℝ} (hg0 : constantCoeff g = 0)
    (hh0 : constantCoeff h = 0) (hg : WtBelow v ρ D g r) (hh : WtBelow v ρ D h s) :
    WtBelow v ρ (D + 1) (g * h) (r + s) := by
  classical
  intro α hα
  rw [coeff_mul]
  refine v.map_le_sum fun q hq => ?_
  have hq' : q.1 + q.2 = α := by simpa using hq
  by_cases h1 : q.1 = 0
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, v.map_zero]; exact le_top
  by_cases h2 : q.2 = 0
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hh0, mul_zero, v.map_zero]; exact le_top
  have hd : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree α := by
    rw [← hq', map_add (f := _)]
  have d1 : Finsupp.degree q.1 ≠ 0 := fun e => h1 ((Finsupp.degree_eq_zero_iff _).1 e)
  have d2 : Finsupp.degree q.2 ≠ 0 := fun e => h2 ((Finsupp.degree_eq_zero_iff _).1 e)
  rw [v.map_mul]
  refine le_trans (le_of_eq ?_) (add_le_add (hg q.1 (by omega)) (hh q.2 (by omega)))
  rw [← WithTop.coe_add, ← hq', wt_add_index]
  congr 1
  ring

theorem WtBelow.pow_succ {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : WtBelow v ρ D g r) (k : ℕ) :
    WtBelow v ρ D (g ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * r) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have h := WtBelow.mul (by simp [hg0]) hg0 ih hg
    intro α hα
    have h' := h α (by omega)
    rw [_root_.pow_succ g (k + 1)]
    refine le_trans (le_of_eq ?_) h'
    congr 1
    push_cast
    ring

theorem WtBelow.pow {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : WtBelow v ρ D g r) {N : ℕ} (hN : 2 ≤ N) :
    WtBelow v ρ (D + 1) (g ^ N) ((N : ℝ) * r) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  have h := WtBelow.mul (by simp [hg0]) hg0 (hg.pow_succ hg0 k) hg
  rw [_root_.pow_succ g (k + 1)]
  convert h using 1
  push_cast
  ring

theorem ordGe_of_lgSum_radii (v : AddValuation C (WithTop ℝ)) (p : ℕ) (hp : p.Prime)
    {d : ℕ} (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C)
    (h0 : ∀ a, c a 0 = Pi.single a 1)
    (hc : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (hgood : ∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C) (r : Fin d → ℝ)
    (hr : ∀ b, r b = if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))
    (hz : ∀ b, OrdGe v ρ (z b) (r b)) (ht : ∀ b, constantCoeff (t b) = 0)
    (hlg : ∀ b, lgSum p c t b = z b) : ∀ b, OrdGe v ρ (t b) (r b) := by
  classical
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  set g' : ℝ := 2 / ((p : ℝ) - 1) with hg'
  have hg'1 : g' * ((p : ℝ) - 1) = 2 := by rw [hg']; field_simp
  have hg'0 : 0 < g' := by rw [hg']; apply div_pos <;> linarith
  have hgp : 2 / ((p : ℝ) * (p - 1)) * p = g' := by rw [hg']; field_simp
  have hγ0 : 0 ≤ 2 / ((p : ℝ) * (p - 1)) := by
    apply div_nonneg (by norm_num); apply mul_nonneg <;> linarith
  have hγg : 2 / ((p : ℝ) * (p - 1)) ≤ g' := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ p by linarith) hγ0
    linarith
  have hre : ∀ e, r e ≤ g' := by
    intro e; rw [hr e]; split_ifs <;> linarith

  have hnum : ∀ (a e : Fin d) (n : ℕ) (L : ℝ), (good a → -(n : ℝ) ≤ L) →
      (-((n : ℝ) + 1) ≤ L) → r e ≤ L + (p : ℝ) ^ (n + 1) * r a := by
    intro a e n L hLg hL
    have hb := one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) n
    have hb' := mul_le_mul_of_nonneg_left hb hg'0.le
    have hb1 := one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) (n + 1)
    have hb1' := mul_le_mul_of_nonneg_left hb1 hg'0.le
    have e1 : g' * (1 + (n : ℝ) * ((p : ℝ) - 1)) = g' + 2 * n := by
      linear_combination (n : ℝ) * hg'1
    have e2 : g' * (1 + ((n + 1 : ℕ) : ℝ) * ((p : ℝ) - 1)) = g' + 2 * ((n : ℝ) + 1) := by
      push_cast; linear_combination ((n : ℝ) + 1) * hg'1
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hre' := hre e
    rw [hr a]
    split_ifs with hga
    · have hL' := hLg hga
      have e3 : (p : ℝ) ^ (n + 1) * (2 / ((p : ℝ) * (p - 1))) = g' * (p : ℝ) ^ n := by
        rw [_root_.pow_succ, ← hgp]; ring
      rw [e3]; linarith
    · have e4 : (p : ℝ) ^ (n + 1) * g' = g' * (p : ℝ) ^ (n + 1) := by ring
      rw [e4]; linarith
  have step : ∀ D : ℕ, ∀ a, WtBelow v ρ D (t a) (r a) := by
    intro D
    induction D with
    | zero => intro a α hα; omega
    | succ D ih =>
      intro e α hα
      have h1 : coeff α (lgSum p c t e) = coeff α (z e) := by rw [hlg e]
      have h2 : coeff α (lgSum p c t e) =
          ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n e * coeff α (t a ^ (p ^ n)) :=
        rfl
      rw [h2, Finset.sum_range_succ'] at h1
      have h3 : ∑ a, c a 0 e * coeff α (t a ^ (p ^ 0)) = coeff α (t e) := by
        simp [h0, Pi.single_apply]
      rw [h3] at h1
      rw [eq_sub_of_add_eq' h1]
      refine v.map_le_sub (hz e α) ?_
      refine v.map_le_sum fun n _ => v.map_le_sum fun a _ => ?_
      have hN : 2 ≤ p ^ (n + 1) := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have h4 := (ih a).pow (ht a) hN α hα
      rw [v.map_mul]
      by_cases hga : good a
      · have hc1 := hgood a hga (n + 1) e (by omega)
        refine le_trans ?_ (add_le_add hc1 h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have := hnum a e n (1 - ((n + 1 : ℕ) : ℝ)) (fun _ => by push_cast; linarith)
          (by push_cast; linarith)
        push_cast at this ⊢
        linarith
      · have hc1 := hc a (n + 1) e
        refine le_trans ?_ (add_le_add hc1 h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have := hnum a e n (-((n + 1 : ℕ) : ℝ)) (fun h => absurd h hga) (by push_cast; linarith)
        push_cast at this ⊢
        linarith
  intro b α
  exact step (Finsupp.degree α + 1) b α (by omega)

theorem ordGe_of_lgSum_twoRadii :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d M : ℕ) (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C), (∀ a, c a 0 = Pi.single a 1) → (∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → (∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → ∀ (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C), (∀ b, OrdGe v ρ (z b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))) → (∀ b, constantCoeff (t b) = 0) → (∀ b, lgSum p c t b = z b) → ∀ b, OrdGe v ρ (t b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) := by
  intro C _ _ v p hp _ d M good _ c h0 hc hgood ρ z t hz ht hlg
  exact ordGe_of_lgSum_radii v p hp good c h0 hc hgood ρ z t
    (fun b => if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) (fun _ => rfl)
    hz ht hlg

end GlobalTheory.ExpWeightTwoRadii
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam


open ReciprocityTheory.PGsh in
theorem isMF_eq_sum_monomials :
    ∀ (w : ℕ) (F : ℍ → ℂ), IsMF w F → ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ),
      (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
        ∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  intro w F hF
  obtain ⟨g, hg⟩ := hF
  have hm := coe_mem_monoSpanF w g
  rw [monoSpanF, Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨(monoIdx w).image fun a => (a, monoB w a),
    fun p => if h : p.1 ∈ monoIdx w then c ⟨p.1, h⟩ else 0, ?_, fun τ => ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact monoIdx_wt ha
  · rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h), ← hg τ, ← hc,
      Finset.sum_apply, ← Finset.sum_coe_sort (monoIdx w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coe_monoW a.2]
    simp [a.2]

end GlobalTheory.QFam
end

section

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FubiniStudyHessian

open ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

variable {n : ℕ}

theorem differentiableAt_coord (i : Fin n) (x : V n) : DifferentiableAt ℂ (fun w : V n => w i) x :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt

theorem wd_coord (j i : Fin n) (x : V n) : wd n j (fun w : V n => w i) x = if j = i then 1 else 0 := by
  rw [wd_of_differentiableAt (differentiableAt_coord i x)]
  have h : fderiv ℂ (fun w : V n => w i) x = EuclideanSpace.proj (𝕜 := ℂ) i :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).fderiv
  rw [h]
  by_cases hji : j = i
  · subst hji; simp [bas]
  · simp [bas, hji, Ne.symm hji]

theorem normSq_eq_sum : (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) = fun w => ∑ i, w i * conj (w i) := by
  funext w
  rw [EuclideanSpace.norm_sq_eq]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem differentiableAt_normSq (x : V n) : DifferentiableAt ℝ (fun w : V n => ‖w‖ ^ 2) x :=
  ((contDiff_norm_sq ℂ (n := 1)).differentiable one_ne_zero) x

theorem wd_normSq (j : Fin n) (x : V n) :
    wd n j (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) x = conj (x j) := by
  have hd : ∀ i, DifferentiableAt ℝ (fun w : V n => w i) x := fun i =>
    (differentiableAt_coord i x).restrictScalars ℝ
  rw [normSq_eq_sum, wd_sum Finset.univ (f := fun i (w : V n) => w i * conj (w i))
    (fun i _ => (hd i).mul (differentiableAt_conj (hd i)))]
  have h : ∀ i, wd n j (fun w : V n => w i * conj (w i)) x = if j = i then conj (x i) else 0 := fun i => by
    rw [wd_mul (hd i) (differentiableAt_conj (hd i)), wd_conj (hd i),
      wdb_of_differentiableAt (differentiableAt_coord i x), wd_coord]
    simp
  simp [h]

theorem wdb_normSq (j : Fin n) (x : V n) :
    wdb n j (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) x = x j := by
  rw [wdb_ofReal (differentiableAt_normSq x), wd_normSq, Complex.conj_conj]

theorem wdb_log (l : Fin n) :
    wdb n l (fun w : V n => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) =
      fun w => (((1 + ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * w l := by
  funext x
  have hpos : (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hk : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + ‖x‖ ^ 2)) (‖x‖ ^ 2) :=
    ((hasDerivAt_id' (‖x‖ ^ 2)).const_add 1).log hpos
  rw [wdb_ofReal_comp (k := fun t : ℝ => Real.log (1 + t)) (v := fun w : V n => ‖w‖ ^ 2)
    hk.differentiableAt (differentiableAt_normSq x), hk.deriv, wdb_normSq, one_div]

theorem cHess_log_one_add_normSq : ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v = Matrix.of (fun j l => (if j = l then 1 else 0) / (1 + (‖v‖ : ℂ) ^ 2) - (starRingEnd ℂ (v j) * v l) / (1 + (‖v‖ : ℂ) ^ 2) ^ 2) := by
  intro n v
  ext j l
  have hpos : (1 + ‖v‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hk : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-1 / (1 + ‖v‖ ^ 2) ^ 2) (‖v‖ ^ 2) :=
    ((hasDerivAt_id' (‖v‖ ^ 2)).const_add 1).inv hpos
  have hd : DifferentiableAt ℝ (fun w : V n => (1 + ‖w‖ ^ 2)⁻¹) v :=
    ((differentiableAt_normSq v).const_add 1).inv hpos
  simp only [cHess, Matrix.of_apply]
  rw [wdb_log, wd_mul (differentiableAt_ofReal hd) ((differentiableAt_coord l v).restrictScalars ℝ),
    wd_ofReal_comp (k := fun t : ℝ => (1 + t)⁻¹) (v := fun w : V n => ‖w‖ ^ 2)
      hk.differentiableAt (differentiableAt_normSq v), hk.deriv, wd_normSq, wd_coord]
  push_cast
  ring

end GlobalTheory.FubiniStudyHessian
end
end

section

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.integral_exp_neg_hermitian_form_posDef : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.PosDef → Integrable (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) ∧ ∫ w : V n, Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re) = Real.pi ^ n / H.det.re := by
  first | exact @GlobalTheory.GaussHerm.integral_exp_neg_herm | exact GlobalTheory.GaussHerm.integral_exp_neg_herm | (intros; apply GlobalTheory.GaussHerm.integral_exp_neg_herm <;> assumption)
end

section

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.norm_sq_mul_integral_ball_le_of_circle_invariant' : ∀ (n : ℕ) (δ : ℝ) (U : Set (V n)) (f : V n → ℂ) (W : V n → ℝ), 0 < δ → IsOpen U → closedBall 0 δ ⊆ U → DifferentiableOn ℂ f U → ContinuousOn W (closedBall 0 δ) → (∀ w, 0 ≤ W w) → (∀ (θ : ℂ) (w : V n), ‖θ‖ = 1 → W (θ • w) = W w) → ‖f 0‖ ^ 2 * ∫ w in ball (0 : V n) δ, W w ≤ ∫ w in ball (0 : V n) δ, ‖f w‖ ^ 2 * W w := by
  first | exact @GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant | exact GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant | (intros; apply GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.topologicalKrullDim_eq_of_isIso_restrict' : ∀ (F : Type) [Field F] (W W' : Scheme.{0}) [IsIntegral W] [IsIntegral W'] (p : W ⟶ Sp F) (q : W' ⟶ Sp F) (h : W' ⟶ W), LocallyOfFiniteType p → LocallyOfFiniteType q → h ≫ p = q → ∀ U : W.Opens, (U : Set W).Nonempty → IsIso (h ∣_ U) → topologicalKrullDim W' = topologicalKrullDim W := by
  first | exact @GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict | exact GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict | (intros; apply GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict <;> assumption)
end
