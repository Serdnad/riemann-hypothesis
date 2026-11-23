module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.ValuativeRel
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.RingTheory.LaurentSeries

@[expose] public section

section

open scoped LaurentSeries

namespace GroundTheory.LocalField

open ValuativeRel Polynomial IsLocalRing Topology Filter WithZero HahnSeries

namespace EqualChar

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

def ballIdeal (γ : (ValueGroupWithZero K)ˣ) : Ideal 𝒪[K] where
  carrier := {x | valuation K (x : K) < γ}
  add_mem' {a b} ha hb := by
    change valuation K ((a : K) + (b : K)) < γ
    exact lt_of_le_of_lt ((valuation K).map_add _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c x hx := by
    change valuation K ((c : K) * (x : K)) < γ
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).mp c.2)) hx

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem mem_ballIdeal {γ : (ValueGroupWithZero K)ˣ} {x : 𝒪[K]} :
    x ∈ ballIdeal K γ ↔ valuation K (x : K) < γ := Iff.rfl

theorem hasBasis_nhds_zero_integer :
    (𝓝 (0 : 𝒪[K])).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero K)ˣ => ((ballIdeal K γ : Ideal 𝒪[K]) : Set 𝒪[K]) := by
  rw [nhds_subtype_eq_comap, ZeroMemClass.coe_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero K).comap Subtype.val).congr
    (fun _ => Iff.rfl) fun γ _ => ?_
  ext x
  simp [mem_ballIdeal]

instance : IsLinearTopology 𝒪[K] 𝒪[K] :=
  IsLinearTopology.mk_of_hasBasis' 𝒪[K] (hasBasis_nhds_zero_integer K)
    fun I r _ hx => I.mul_mem_left r hx

variable (p : ℕ) [Fact p.Prime] [CharP K p]

section Uniform

end Uniform


end EqualChar

end GroundTheory.LocalField
end

section

namespace GroundTheory.LocalField

open ValuativeRel WithZero

theorem isValuativeTopology_of_valued {R : Type*} [CommRing R] [ValuativeRel R]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀]
    [(Valued.v : Valuation R Γ₀).Compatible] : IsValuativeTopology R :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle (Valued.v : Valuation R Γ₀) fun {s} => by
    simpa using (Valued.hasBasis_nhds_zero R Γ₀).mem_iff (t := s)

namespace Padic

variable (p : ℕ) [hp : Fact p.Prime]

theorem mulValuation_le_iff_norm_le (x y : ℚ_[p]) :
    Padic.mulValuation x ≤ Padic.mulValuation y ↔ ‖x‖ ≤ ‖y‖ := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hx, hy]
  rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy,
    zpow_le_zpow_iff_right₀ (by exact_mod_cast hp.out.one_lt)]
  simp [hx, hy, -exp_neg]

instance isValuativeTopology : IsValuativeTopology ℚ_[p] :=
  letI : Valued ℚ_[p] NNReal := NormedField.toValued
  haveI : (Valued.v : Valuation ℚ_[p] NNReal).Compatible := ⟨fun x y => by
    rw [Valuation.Compatible.vle_iff_le (v := Padic.mulValuation) x y,
      mulValuation_le_iff_norm_le]
    rfl⟩
  isValuativeTopology_of_valued

instance isNonarchimedeanLocalField : IsNonarchimedeanLocalField ℚ_[p] where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

end Padic

namespace LaurentSeries

open _root_.LaurentSeries HahnSeries

variable (K : Type*) [Field K]

section Finite

variable {K}

variable (K) [Finite K]

end Finite

end LaurentSeries

end GroundTheory.LocalField
end
