module

public import Formalism.PeriodIntegrals.Bundle011
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.PowerSeries.Exp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.Bundle001
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.FglPhSplit.Wk

open PI.FglPhSplit

variable {K : Type} [Field K]

def AllIn (W : Subring K) {σ : Type} (F : MvPowerSeries σ K) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ W

theorem allIn_mul {W : Subring K} {σ : Type} {F G : MvPowerSeries σ K} (hF : AllIn W F)
    (hG : AllIn W G) : AllIn W (F * G) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hF _) (hG _)

theorem expMv_eq_subst [CharZero K] {σ : Type} {F : MvPowerSeries σ K}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    expMv F = PowerSeries.subst F (PowerSeries.exp K) := by
  classical
  ext α
  have hs : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  rw [coeff_expMv, PowerSeries.coeff_subst hs,
    finsum_eq_sum_of_support_subset _ (s := Finset.range ((α.sum fun _ k => k) + 1)) ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul, map_div₀, map_one, map_natCast]
    ring
  · intro n hn
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hn ⊢
    by_contra hc
    apply hn
    have hdeg : (α.sum fun _ k => k) = Finsupp.degree α := rfl
    rw [MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1)
      (by rw [pow_one]; exact hF) (by omega), smul_zero]

section Rename₂

variable {ι ι' : Type} [Fintype ι]

variable (g : Dat K) (hex0 : PowerSeries.constantCoeff g.ex = 0)
  (hl0 : PowerSeries.constantCoeff g.l = 0)
include hex0 hl0


end Rename₂

end PI.FglPhSplit.Wk

end
end

section

noncomputable section

namespace PI.FglPhSplit.Wk

open PI.FglPhSplit

theorem compositionalInverseSymm : S1 := by
  intro K _ l ex hex hinv
  have hsub : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have hsplit : l = PowerSeries.C (PowerSeries.constantCoeff l) +
        (l - PowerSeries.C (PowerSeries.constantCoeff l)) := by ring
    have h0 : MvPowerSeries.constantCoeff
        (PowerSeries.subst ex (l - PowerSeries.C (PowerSeries.constantCoeff l))) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hex _ (by simp)
    have key : MvPowerSeries.constantCoeff (PowerSeries.subst ex l) = PowerSeries.constantCoeff l := by
      conv_lhs => rw [hsplit]
      rw [PowerSeries.subst_add hsub, map_add (f := _), h0, PowerSeries.subst_C]
      simp
    rw [hinv] at key
    rw [← key]
    exact PowerSeries.constantCoeff_X
  have hu : IsUnit (PowerSeries.coeff 1 ex) := by
    refine Ne.isUnit fun h1 => ?_
    have h2 : (2 : ℕ∞) ≤ ex.order := by
      refine PowerSeries.le_order ex 2 fun i hi => ?_
      have hi' : i < 2 := by exact_mod_cast hi
      interval_cases i
      · simpa using hex
      · exact h1
    have h3 := PowerSeries.le_order_subst_right' (φ := l) hex hl0
    rw [hinv, PowerSeries.order_X] at h3
    have := h2.trans h3
    norm_num at this
  have hQ := PowerSeries.HasSubst.substInvOfIsUnit ex hu
  have hexQ := PowerSeries.subst_substInvOfIsUnit_right ex hex hu
  have hlQ : l = PowerSeries.substInvOfIsUnit ex hu := by
    calc l = PowerSeries.subst (PowerSeries.X : PowerSeries K) l := (PowerSeries.X_subst l).symm
      _ = PowerSeries.subst (PowerSeries.subst (PowerSeries.substInvOfIsUnit ex hu) ex) l := by
          rw [hexQ]
      _ = PowerSeries.subst (PowerSeries.substInvOfIsUnit ex hu) (PowerSeries.subst ex l) :=
          (PowerSeries.subst_comp_subst_apply hsub hQ l).symm
      _ = PowerSeries.subst (PowerSeries.substInvOfIsUnit ex hu) (PowerSeries.X : PowerSeries K) := by
          rw [hinv]
      _ = PowerSeries.substInvOfIsUnit ex hu := PowerSeries.subst_X hQ
  refine ⟨hl0, ?_⟩
  rw [hlQ]
  exact hexQ

variable {K : Type} [Field K]

end PI.FglPhSplit.Wk

end
end
