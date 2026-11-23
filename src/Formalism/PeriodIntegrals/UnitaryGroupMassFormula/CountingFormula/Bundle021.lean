module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle020
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

@[expose] public section

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

theorem orbit_count_first_stage : Stage1 := stage1_of_unipotentIntegralIsGroup unipotent_integral_isGroup

theorem orbitReps_of_stage2 (h2 : Stage2) : OrbitReps :=
  orbitReps_of unipotent_integral_isGroup rank_gram good_places_integral orbit_count_first_stage h2 finite_level_index

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem row_class_holds : RowClass := rowClass_of_zunit row_unit_condition

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end

section

open NumberField Module Formalism.MainNotions.S

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

def SStable {K : Type} [Field K] [NumberField K] [StarRing K]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Prop :=
  ∀ a ∈ (I : Submodule (𝓞 K) K), star a ∈ (I : Submodule (𝓞 K) K)

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem sStable_one : SStable (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  intro a ha
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff] at ha ⊢
  obtain ⟨x, rfl⟩ := ha
  exact ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd K) x, rfl⟩

theorem sStable_mul {I J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (hJ : SStable J) :
    SStable (I * J) := by
  intro a ha
  rw [FractionalIdeal.coe_mul] at ha ⊢
  refine Submodule.mul_induction_on (C := fun a => star a ∈ (I : Submodule (𝓞 K) K) * J) ha ?_ ?_
  · intro x hx y hy
    rw [star_mul, mul_comm (star y)]
    exact Submodule.mul_mem_mul (hI x hx) (hJ y hy)
  · intro x y hx hy
    rw [star_add]
    exact add_mem hx hy

theorem sStable_pow {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (n : ℕ) :
    SStable (I ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact sStable_one
  | succ n ih => rw [pow_succ]; exact sStable_mul ih hI

theorem sStable_inv {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) : SStable I⁻¹ := by
  by_cases h0 : I = 0
  · subst h0
    intro a ha
    rw [FractionalIdeal.inv_zero', FractionalIdeal.coe_zero, Submodule.mem_bot] at ha ⊢
    rw [ha, star_zero]
  · intro a ha
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff h0] at ha ⊢
    intro y hy
    have h1 : a * star y ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
      ha _ (FractionalIdeal.mem_coe.mp (hI y (FractionalIdeal.mem_coe.mpr hy)))
    have h2 := sStable_one (K := K) _ (FractionalIdeal.mem_coe.mpr h1)
    rw [star_mul, star_star, mul_comm] at h2
    exact FractionalIdeal.mem_coe.mp h2

theorem sStable_zpow {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (n : ℤ) :
    SStable (I ^ n) := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_coe, zpow_natCast]; exact sStable_pow hI n
  | negSucc n => rw [zpow_negSucc]; exact sStable_inv (sStable_pow hI _)

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sStable_ddS (D : Formalism.BasicNotions.D7) : SStable (ddS D) := by
  intro a ha
  rw [FractionalIdeal.mem_coe] at ha ⊢
  unfold ddS at ha ⊢
  rw [FractionalIdeal.mem_coeIdeal] at ha ⊢
  obtain ⟨y, hy, rfl⟩ := ha

  have hc : (NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E)).comp
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) := by
    ext x
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  refine ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E) y, ?_, rfl⟩
  rw [← hc, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hy

theorem ddS_ne_zero' (D : Formalism.BasicNotions.D7) : ddS D ≠ 0 :=
  PI.ScalarPairDr.W.ddS_ne_zero D

theorem stable_differentIdealPowers (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) : SStable (differentIdealPowers D i) := by
  induction i using Fin.lastCases with
  | last => unfold differentIdealPowers; rw [Fin.snoc_last]; exact sStable_one
  | cast a => unfold differentIdealPowers; rw [Fin.snoc_castSucc]; exact sStable_zpow (sStable_ddS D) _

theorem differentIdealPowers_ne_zero (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) : differentIdealPowers D i ≠ 0 := by
  induction i using Fin.lastCases with
  | last => unfold differentIdealPowers; rw [Fin.snoc_last]; exact one_ne_zero
  | cast a => unfold differentIdealPowers; rw [Fin.snoc_castSucc]; exact zpow_ne_zero _ (ddS_ne_zero' D)

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

section

open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Counts

variable {K : Type} [Field K] [NumberField K]

theorem count_span_mul (P : HeightOneSpectrum (𝓞 K)) {y z : K} (hy : y ≠ 0) (hz : z ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (y * z)) =
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y) +
        FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) z) := by
  have hy' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hy
  have hz' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) z ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hz
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K P hy' hz']

theorem count_span_inv (P : HeightOneSpectrum (𝓞 K)) (y : K) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y⁻¹) =
      - FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y) := by
  by_cases hy : y = 0
  · simp [hy, FractionalIdeal.count_zero]
  have hy' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hy
  have hyi : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y⁻¹ ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hy
  have h := FractionalIdeal.count_mul K P hyi hy'
  rw [FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hy,
    FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one] at h
  omega

theorem count_span_prod {ι : Type} (P : HeightOneSpectrum (𝓞 K)) (s : Finset ι) (z : ι → K)
    (hz : ∀ i, z i ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (∏ i ∈ s, z i)) =
      ∑ i ∈ s, FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (z i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FractionalIdeal.count_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, count_span_mul P (hz a)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hz i), ih]

theorem count_le_of_integral {ι : Type} [Fintype ι] (P : HeightOneSpectrum (𝓞 K)) (c : K) (s : 𝓞 K)
    (z : ι → K) (hc : c ≠ 0) (hs : s ∉ P.asIdeal) (hz : ∀ i, z i ≠ 0)
    (hw : c⁻¹ * (s : K) * ∏ i, z i ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c) ≤
      ∑ i, FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (z i)) := by
  have hs0 : (s : K) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact P.asIdeal.zero_mem
  have hprod : ∏ i, z i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hz i
  have hw0 : c⁻¹ * (s : K) * ∏ i, z i ≠ 0 :=
    mul_ne_zero (mul_ne_zero (inv_ne_zero hc) hs0) hprod
  have h1 := count_le_of_mem (K := K) P hw hw0
  rw [FractionalIdeal.count_one, count_span_mul P (mul_ne_zero (inv_ne_zero hc) hs0) hprod,
    count_span_mul P (inv_ne_zero hc) hs0, count_span_inv, count_span_prod P _ _ hz] at h1
  have h2 : FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (s : K)) = 0 :=
    count_span_unit (K := K) P s hs
  rw [h2] at h1
  linarith

end Counts

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
