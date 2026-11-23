module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle014
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle009
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Inertia
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Bundle001
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpenA
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpenB

@[expose] public section

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def redK : OK p K →+* resK p K :=
  (resMap p K).codRestrict (resK p K) fun x => (mem_resK_iff p K _).2 ⟨toObar p K x, (x : K).2, rfl⟩

theorem redK_surjective : Function.Surjective (redK p K) := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx, rfl⟩ := (mem_resK_iff p K c).1 hc
  exact ⟨⟨⟨x, hx⟩, x.2⟩, Subtype.ext rfl⟩

variable {K}

variable (K)

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Euler

open _root_.Neutral.B1 Function

noncomputable section

section aux

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

attribute [local instance] zpAlgOK

theorem card_OK_quot_natCast (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : n ≠ 0) :
    Nat.card (OK p K ⧸ Ideal.span {(n : OK p K)}) = (p ^ padicValNat p n) ^ Module.finrank ℚ_[p] K := by
  have := isScalarTower_zp_OK p K
  have : IsIntegralClosure (OK p K) ℤ_[p] K := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    rw [isIntegral_zp_K_iff, ← _root_.ReciprocityTheory.Neutral.Cmp.norm_le_one_iff_isIntegral,
      ← mem_OK_iff]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
  have := isTorsionFree_zp_K p K
  have : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _
  have : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  have hr := IsIntegralClosure.rank ℤ_[p] ℚ_[p] K (OK p K)
  have hn' : (n : OK p K) = algebraMap ℤ_[p] (OK p K) (n : ℕ) := (map_natCast _ _).symm
  rw [hn', ReciprocityTheory.Neutral.Cmp.card_quot_span_algebraMap (Module.finBasis ℤ_[p] (OK p K)),
    ReciprocityTheory.Neutral.Cmp.card_quot_natCast_padicInt p hn, Fintype.card_fin, hr]

end aux

attribute [local instance] zpAlgOK

variable (p : ℕ) [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Euler
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem normHom_mem (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (y : KbarMult p) (hy : y ∈ multOf p L) :
    normHom p K L y ∈ multOf p K := normHom_mem_multiplicative_group hL y hy

theorem normHom_eq_algebraNorm (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (y : KbarMult p)
    (hy : y ∈ multOf p L) :
    ((Additive.toMul (normHom p K L y) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ((Algebra.norm K (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ :
        IntermediateField.extendScalars h) : K) : PadicAlgCl p) :=
  normHom_eq_algebra_norm hL h y hy

theorem normHom_layer (h : K ≤ L) [(subG p K L).Normal] [Fintype (GalLK p K L)] (y : (layer p K L).V) :
    normHom p K L y.1 = (∑ g, (layer p K L).rho g y).1 := normHom_layer_eq_trace_sum y

theorem normHom_trans {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L') (h : K ≤ L) (h' : L ≤ L') (y : KbarMult p)
    (hy : y ∈ multOf p L') : normHom p K L (normHom p L L' y) = normHom p K L' y :=
  normHom_comp_normHom_of_le hL' h h' y hy

theorem normGrp_anti {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L') (h : K ≤ L) (h' : L ≤ L') :
    normGrp p K L' ≤ normGrp p K L := normGroup_antitone hL' h h'

theorem pow_degLK_mem_normGrp (h : K ≤ L) (x : Kˣ) : x ^ degLK p K L ∈ normGrp p K L :=
  pow_degree_mem_normGroup h x

theorem normGrp_self : normGrp p K K = ⊤ := normGroup_self_eq_top

theorem finiteIndex_range_pow (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex := finiteIndex_range_pow' hK hn

theorem isOpen_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    IsOpen (normGrp p K L : Set Kˣ) :=
  Subgroup.isOpen_mono (by rintro _ ⟨x, rfl⟩; exact pow_degLK_mem_normGrp h x)
    (isOpen_range_pow' hK (degLK_pos hL))

theorem finiteIndex_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    (normGrp p K L).FiniteIndex := by
  have := finiteIndex_range_pow' hK (degLK_pos (K := K) hL)
  exact Subgroup.finiteIndex_of_le (H := (powMonoidHom (degLK p K L) : Kˣ →* Kˣ).range)
    (by rintro _ ⟨x, rfl⟩; exact pow_degLK_mem_normGrp h x)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
