module

public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle002
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Lemmata.GeneralBFactRightRest.Imports
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Normal.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

private theorem sum_le_of_unique {ι : Type} (s : Finset ι) (g : ι → ℕ) (r : ℕ)
    (hle : ∀ i ∈ s, g i ≤ r) (huniq : ∀ i ∈ s, ∀ j ∈ s, g i ≠ 0 → g j ≠ 0 → i = j) :
    ∑ i ∈ s, g i ≤ r := by
  classical
  by_cases h : ∃ i ∈ s, g i ≠ 0
  · obtain ⟨i, hi, hgi⟩ := h
    rw [← Finset.add_sum_erase s g hi]
    have h0 : ∑ j ∈ s.erase i, g j = 0 := Finset.sum_eq_zero fun j hj => by
      by_contra hne
      exact (Finset.ne_of_mem_erase hj) (huniq j (Finset.mem_of_mem_erase hj) i hi hne hgi)
    rw [h0, add_zero]
    exact hle i hi
  · push Not at h
    rw [Finset.sum_eq_zero h]
    exact Nat.zero_le _

theorem sumPadicValDifferencesLe : LagrangeBoundT := by
  intro l a A' r' Cc hl ha hA hlt hdiv c hc n hn
  have hfact : Fact l.Prime := ⟨hl⟩
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hnotL : ¬ (l : ℤ) ∣ (l : ℤ) ^ a - 1 := by
    intro h
    have h1 : (l : ℤ) ∣ (l : ℤ) ^ a := dvd_pow_self _ (by omega)
    have h2 : (l : ℤ) ∣ 1 := by
      have h3 := dvd_sub h1 h
      rwa [sub_sub_cancel] at h3
    exact hlZ.not_isUnit (isUnit_of_dvd_one h2)
  have hsep : ∀ x m1 m2 : ℤ, |m1 - m2| < l → (l : ℤ) ∣ x + m1 * ((l : ℤ) ^ a - 1) →
      (l : ℤ) ∣ x + m2 * ((l : ℤ) ^ a - 1) → m1 = m2 := by
    intro x m1 m2 hm h1 h2
    have h3 : (l : ℤ) ∣ (m1 - m2) * ((l : ℤ) ^ a - 1) := by
      have e : (m1 - m2) * ((l : ℤ) ^ a - 1) =
          (x + m1 * ((l : ℤ) ^ a - 1)) - (x + m2 * ((l : ℤ) ^ a - 1)) := by ring
      rw [e]
      exact dvd_sub h1 h2
    rcases hlZ.dvd_or_dvd h3 with h | h
    · have := Int.eq_zero_of_abs_lt_dvd h hm
      linarith
    · exact absurd h hnotL
  have hdv : ∀ z : ℤ, padicValInt l z ≠ 0 → (l : ℤ) ∣ z := by
    intro z hz
    have h := (padicValInt_dvd_iff (p := l) 1 z).mpr (Or.inr (Nat.one_le_iff_ne_zero.mpr hz))
    simpa using h
  have hneg : ∀ z : ℤ, padicValInt l (-z) = padicValInt l z := fun z => by simp [padicValInt]
  have hpow : ∀ k : ℕ, ((l ^ k - 1 : ℕ) : ℤ) = (l : ℤ) ^ k - 1 := fun k => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hl.pos)]
    push_cast
    ring
  have hper : ∀ c' ∈ Cc, (∑ n' ∈ Finset.range (2 * A'),
      if c' = c ∧ n' = n then 0
      else padicValInt l (((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)))) ≤
      if c' = c then 0 else r' := by
    intro c' hc'
    by_cases hcc : c' = c
    · subst hcc
      rw [if_pos rfl]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro n' hn'
      rw [Finset.mem_range] at hn'
      split_ifs with h
      · rfl
      · by_contra hne
        have h1 := hdv _ hne
        have hz : ((c' : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
            0 + ((n : ℤ) - n') * ((l : ℤ) ^ a - 1) := by ring
        rw [hz] at h1
        have h2 := hsep 0 ((n : ℤ) - n') 0 (by rw [sub_zero, abs_lt]; constructor <;> omega) h1 (by simp)
        exact h ⟨rfl, by omega⟩
    · rw [if_neg hcc]
      obtain ⟨ρ, hρ1, hρr, hρd⟩ := hdiv c hc c' hc' (Ne.symm hcc)
      apply sum_le_of_unique
      · intro n' hn'
        rw [Finset.mem_range] at hn'
        rw [if_neg (fun h => hcc h.1)]
        refine le_trans ?_ hρr
        rcases lt_or_gt_of_ne hcc with hlt' | hgt
        · have hdN : (l ^ a - 1) ∣ (c - c') * (l ^ ρ - 1) := by
            rw [← Int.natCast_dvd_natCast, Nat.cast_mul, hpow, hpow, Nat.cast_sub hlt'.le]
            exact hρd
          have hD := padicValIntShiftLe l a (c - c') ρ ((n : ℤ) - n') hl ha (by omega)
            (lt_of_le_of_lt (Nat.sub_le _ _) (hlt c hc)) hρ1 hdN
            (by rw [abs_lt]; constructor <;> omega)
          have hz : ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
              ((c - c' : ℕ) : ℤ) + ((n : ℤ) - n') * ((l : ℤ) ^ a - 1) := by
            rw [Nat.cast_sub hlt'.le]
            ring
          rw [hz]
          exact hD
        · have hdN : (l ^ a - 1) ∣ (c' - c) * (l ^ ρ - 1) := by
            rw [← Int.natCast_dvd_natCast, Nat.cast_mul, hpow, hpow, Nat.cast_sub hgt.le]
            have e : ((c' : ℤ) - c) * ((l : ℤ) ^ ρ - 1) = -(((c : ℤ) - c') * ((l : ℤ) ^ ρ - 1)) := by ring
            rw [e]
            exact dvd_neg.mpr hρd
          have hD := padicValIntShiftLe l a (c' - c) ρ ((n' : ℤ) - n) hl ha (by omega)
            (lt_of_le_of_lt (Nat.sub_le _ _) (hlt c' hc')) hρ1 hdN
            (by rw [abs_lt]; constructor <;> omega)
          have hz : ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
              -(((c' - c : ℕ) : ℤ) + ((n' : ℤ) - n) * ((l : ℤ) ^ a - 1)) := by
            rw [Nat.cast_sub hgt.le]
            ring
          rw [hz, hneg]
          exact hD
      · intro i hi j hj hgi hgj
        rw [Finset.mem_range] at hi hj
        rw [if_neg (fun h => hcc h.1)] at hgi hgj
        have h1 := hdv _ hgi
        have h2 := hdv _ hgj
        have ez : ∀ k : ℕ, ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + k * ((l : ℤ) ^ a - 1)) =
            ((c : ℤ) - c') + ((n : ℤ) - k) * ((l : ℤ) ^ a - 1) := fun k => by ring
        rw [ez] at h1 h2
        have := hsep _ _ _ (by rw [abs_lt]; constructor <;> omega) h1 h2
        omega
  calc (∑ c' ∈ Cc, ∑ n' ∈ Finset.range (2 * A'),
        if c' = c ∧ n' = n then 0
        else padicValInt l (((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1))))
      ≤ ∑ c' ∈ Cc, (if c' = c then 0 else r') := Finset.sum_le_sum hper
    _ = (Cc.card - 1) * r' := by
      rw [← Finset.add_sum_erase Cc _ hc, if_pos rfl, zero_add,
        Finset.sum_congr rfl (fun x hx => if_neg (Finset.ne_of_mem_erase hx)), Finset.sum_const,
        smul_eq_mul, Finset.card_erase_of_mem hc]

end Formalism.IrreducibleCountingLemmas.WindowSums
end

section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

variable {K : Type} [Field K] {N : ℕ}

theorem monicOf_degree_lt (c : Fin N → K) :
    (∑ i : Fin N, C (c i) * X ^ (i : ℕ)).degree < (N : WithBot ℕ) := degree_sum_fin_lt c

theorem monicOf_monic (c : Fin N → K) : (monicOf c).Monic := by
  rw [monicOf]
  exact monic_X_pow_add (monicOf_degree_lt c)

theorem monicOf_natDegree (c : Fin N → K) : (monicOf c).natDegree = N := by
  rw [monicOf, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact monicOf_degree_lt c

theorem monicOf_coeff (c : Fin N → K) (i : Fin N) : (monicOf c).coeff i = c i := by
  rw [monicOf, coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt), zero_add,
    Polynomial.finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h).symm
  · simp

theorem monicOf_injective : Function.Injective (monicOf : (Fin N → K) → K[X]) := by
  intro c d h
  funext i
  rw [← monicOf_coeff c i, ← monicOf_coeff d i, h]

theorem monicOf_coeffs {p : K[X]} (hp : p.Monic) (hN : p.natDegree = N) :
    monicOf (fun i : Fin N => p.coeff i) = p := by
  subst hN
  rw [monicOf, Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
  exact hp.as_sum.symm

theorem irreducible_count_upper : IrredCountUpper := by
  intro K _ _ d hd
  classical
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hd0 : d ≠ 0 := by omega
  have hdvd : ∀ f : K[X], Irreducible f → f.natDegree = d → f ∣ X ^ (Fintype.card K ^ d) - X := by
    intro f hf hfd
    haveI := Fact.mk hf
    haveI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
    haveI : Finite (AdjoinRoot f) := Module.finite_of_finite K
    letI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
    have hcard : Fintype.card (AdjoinRoot f) = Fintype.card K ^ d := by
      rw [Module.card_fintype (AdjoinRoot.powerBasis hf.ne_zero).basis, Fintype.card_fin,
        AdjoinRoot.powerBasis_dim, hfd]
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← hcard, FiniteField.pow_card,
      sub_self]
  have main : ∀ S : Finset (Fin d → K), (∀ c ∈ S, Irreducible (monicOf c)) →
      d * S.card ≤ Fintype.card K ^ d := by
    intro S hS
    have hcop : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → IsCoprime (monicOf c) (monicOf c') := by
      intro c hc c' hc' hne
      rw [(hS c hc).coprime_iff_not_dvd]
      intro hdv
      apply hne
      apply monicOf_injective
      exact eq_of_monic_of_associated (monicOf_monic c) (monicOf_monic c')
        ((hS c hc).associated_of_dvd (hS c' hc') hdv)
    have hprod : ∏ c ∈ S, monicOf c ∣ X ^ (Fintype.card K ^ d) - X :=
      Finset.prod_dvd_of_coprime (fun c hc c' hc' hne => hcop c hc c' hc' hne)
        (fun c hc => hdvd _ (hS c hc) (monicOf_natDegree c))
    have hdeg : (∏ c ∈ S, monicOf c).natDegree = d * S.card := by
      rw [natDegree_prod_of_monic _ _ (fun c _ => monicOf_monic c),
        Finset.sum_congr rfl (fun c _ => monicOf_natDegree c), Finset.sum_const, smul_eq_mul, mul_comm]
    have hle := natDegree_le_of_dvd hprod (FiniteField.X_pow_card_pow_sub_X_ne_zero K hd0 hq1)
    rw [hdeg, FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hd0 hq1] at hle
    exact hle
  exact main _ (fun c hc => (Finset.mem_filter.mp hc).2)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsOrbit)

theorem frobenius_orbit_irreducible : FrobOrbitIrred := by
  unfold FrobOrbitIrred IsOrbit
  intro K L _ _ _ _ _ f hm hirr
  classical
  have hf0 : f ≠ 0 := hm.ne_zero
  have hfL : f.map (algebraMap K L) ≠ 0 := Polynomial.map_ne_zero hf0
  have hmem : ∀ z : L, z ∈ (f.aroots L).toFinset ↔ aeval z f = 0 := by
    intro z
    rw [Multiset.mem_toFinset, mem_aroots]
    exact ⟨fun h => h.2, fun h => ⟨hf0, h⟩⟩
  have hfrob : ∀ z : L, aeval (z ^ Fintype.card K) f = (aeval z f) ^ Fintype.card K := by
    intro z
    rw [← expand_aeval, FiniteField.expand_card, map_pow]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rw [hmem] at hx ⊢
    show aeval (x ^ Fintype.card K) f = 0
    rw [hfrob, hx, zero_pow Fintype.card_ne_zero]
  · intro x hx y hy
    rw [hmem] at hx hy
    let E : IntermediateField K L := IntermediateField.adjoin K (f.rootSet L)
    have hxE : x ∈ E := IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hf0).2 hx)
    have hyE : y ∈ E := IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hf0).2 hy)
    haveI hSF : IsSplittingField K E f :=
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
    haveI : Normal K E := Normal.of_isSplittingField f
    haveI : FiniteDimensional K E := IsSplittingField.finiteDimensional E f
    haveI : Finite E := Module.finite_of_finite K
    haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    have hmx : minpoly K x = f := (minpoly.eq_of_irreducible_of_monic hirr hx hm).symm
    have hmy : minpoly K y = f := (minpoly.eq_of_irreducible_of_monic hirr hy hm).symm
    have hxy : minpoly K (⟨y, hyE⟩ : E) = minpoly K (⟨x, hxE⟩ : E) := by
      rw [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq]
      show minpoly K y = minpoly K x
      rw [hmx, hmy]
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit E).1 hxy
    obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K E).2 σ
    have key : ∀ (m : ℕ) (w : E), (((FiniteField.frobeniusAlgEquivOfAlgebraic K E ^ m) w : E) : L) =
        (fun z : L => z ^ Fintype.card K)^[m] (w : L) := by
      intro m
      induction m with
      | zero => intro w; rfl
      | succ m ih =>
        intro w
        rw [pow_succ, AlgEquiv.mul_apply, ih, Function.iterate_succ_apply]
        congr 1
        all_goals (try rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic])
        all_goals (try simp)
    simp only at hσ
    have h2 : ((σ ⟨x, hxE⟩ : E) : L) = y := by
      rw [← AlgEquiv.smul_def, hσ]
    simp only at hn
    rw [← hn, key] at h2
    exact ⟨_, h2⟩
  · have hsep : f.Separable := by
      first
      | exact PerfectField.separable_of_irreducible hirr
      | (haveI : PerfectField K := PerfectField.ofFinite
         exact PerfectField.separable_of_irreducible hirr)
    rw [Multiset.toFinset_card_of_nodup (nodup_roots (hsep.map (f := algebraMap K L)))]
    show Multiset.card (f.map (algebraMap K L)).roots = f.natDegree
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem cycleProbSum_of_cycleProbPrime : CycleProbPrime → CycleProbSum := by
  unfold CycleProbPrime CycleProbSum
  intro h N
  classical
  have hdisj : ∀ p ∈ (range (N + 1)).filter (fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N),
      ∀ q ∈ (range (N + 1)).filter (fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N), p ≠ q →
      Disjoint (univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.cycleType)
        (univ.filter fun σ : Equiv.Perm (Fin N) => q ∈ σ.cycleType) := by
    intro p hp q hq hpq
    simp only [mem_filter, mem_range] at hp hq
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    have hq' : q ∈ σ.cycleType.erase p := (Multiset.mem_erase_of_ne hpq.symm).2 h2
    have hsum : σ.cycleType.sum ≤ N := by
      rw [Equiv.Perm.sum_cycleType]
      exact (Finset.card_le_univ _).trans (by simp)
    have hsplit : σ.cycleType.sum = p + (σ.cycleType.erase p).sum := by
      conv_lhs => rw [← Multiset.cons_erase h1]
      rw [Multiset.sum_cons]
    have hle : q ≤ (σ.cycleType.erase p).sum := Multiset.le_sum_of_mem hq'
    omega
  have hset : (univ.filter fun σ : Equiv.Perm (Fin N) => ∃ p ∈ σ.cycleType, Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N) =
      ((range (N + 1)).filter fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N).biUnion
        (fun p => univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.cycleType) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
    constructor
    · rintro ⟨p, hp, hpr, h2, h3⟩
      exact ⟨p, ⟨by omega, hpr, h2, h3⟩, hp⟩
    · rintro ⟨p, ⟨-, hpr, h2, h3⟩, hp⟩
      exact ⟨p, hp, hpr, h2, h3⟩
  rw [hset, Finset.card_biUnion hdisj, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp only [mem_filter, mem_range] at hp
  obtain ⟨hpN, hpr, h2, h3⟩ := hp
  have hk := h N p hpr (by omega) h2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpr.ne_zero
  rw [eq_div_iff hp0, ← hk]
  push_cast
  ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem pow_eq_pow_of_modEq_orderOf {M : Type*} [Monoid M] (x : M) {a b : ℕ}
    (h : a ≡ b [MOD orderOf x]) : x ^ a = x ^ b := by
  rw [← pow_mod_orderOf x a, ← pow_mod_orderOf x b, show a % orderOf x = b % orderOf x from h]

theorem gcd_mul_pow_totient {q m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime q m) :
    Nat.gcd (q * m) (q ^ Nat.totient m) = q := by
  have ht : 0 < Nat.totient m := Nat.totient_pos.mpr hm
  obtain ⟨k, hk⟩ : ∃ k, Nat.totient m = k + 1 := ⟨Nat.totient m - 1, by omega⟩
  rw [hk, pow_succ', Nat.gcd_mul_left]
  have : Nat.gcd m (q ^ k) = 1 := (Nat.Coprime.pow_right k hcop.symm)
  rw [this, mul_one]

theorem prime_to_part_spec : PrimeToPartSpec := by
  unfold PrimeToPartSpec
  intro M _ l x hl hx
  set n := orderOf x with hn
  set q := l ^ n.factorization l with hq
  have hnpos : 0 < n := hx.orderOf_pos
  have hqd : q ∣ n := Nat.ordProj_dvd n l
  have hqpos : 0 < q := pow_pos hl.pos _
  have hmpos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hnpos hqd) hqpos
  have hcop : Nat.Coprime q (n / q) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hnpos.ne')
  have hnqm : n = q * (n / q) := (Nat.mul_div_cancel' hqd).symm
  unfold primeToPart
  refine ⟨?_, ?_⟩
  · have hg : Nat.gcd n (q ^ Nat.totient (n / q)) = q := by
      have h3 := gcd_mul_pow_totient hmpos hcop
      rwa [← hnqm] at h3
    rw [orderOf_pow' x (pow_pos hqpos _).ne', ← hn, hg]
  · refine ⟨n.factorization l, ?_⟩
    rw [← pow_mul]
    apply pow_eq_pow_of_modEq_orderOf
    rw [← hn]
    have h1 : q ^ Nat.totient (n / q) ≡ 1 [MOD n / q] := Nat.ModEq.pow_totient hcop
    have h2 : q * q ^ Nat.totient (n / q) ≡ q * 1 [MOD q * (n / q)] := Nat.ModEq.mul_left' q h1
    rw [← hnqm, mul_one, mul_comm] at h2
    exact h2.symm

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section

open Polynomial UniqueFactorizationMonoid

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsSubSum)

theorem exists_le_map_eq {α β : Type*} [DecidableEq β] (f : α → β) (t : Multiset α) :
    ∀ s : Multiset β, s ≤ t.map f → ∃ u ≤ t, u.map f = s := by
  first | exact Bl.general_b_fact_right_rest.goal1 .. | (apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_rest.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t s ‹_› | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t s | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f t | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› f | exact @Bl.general_b_fact_right_rest.goal1 α β ‹_› | exact @Bl.general_b_fact_right_rest.goal1 α β | exact @Bl.general_b_fact_right_rest.goal1 α

theorem divisor_degree_subsum : DivisorDegreeSubSum := by
  classical
  intro K _ f a hf
  have hdeg : ∀ t : Multiset K[X], t ≤ normalizedFactors f →
      t.prod.natDegree = (t.map natDegree).sum := by
    intro t ht
    apply natDegree_multiset_prod
    intro h0
    exact zero_notMem_normalizedFactors f (Multiset.mem_of_le ht h0)
  constructor
  · rintro ⟨h, hdvd, rfl⟩
    have hh : h ≠ 0 := fun h0 => hf (by rw [h0] at hdvd; exact zero_dvd_iff.mp hdvd)
    have hle : normalizedFactors h ≤ normalizedFactors f :=
      (dvd_iff_normalizedFactors_le_normalizedFactors hh hf).mp hdvd
    refine ⟨(normalizedFactors h).map natDegree, Multiset.map_le_map hle, ?_⟩
    rw [← hdeg _ hle]
    exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hh))
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨u, hu, rfl⟩ := exists_le_map_eq natDegree _ s hs
    refine ⟨u.prod, ?_, hdeg u hu⟩
    exact (Multiset.prod_dvd_prod_of_le hu).trans (prod_normalizedFactors hf).dvd

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
