module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle010
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle008
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle009
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle011
import ReciprocityTheory.GroupCohomology.Bundle002
public import ReciprocityTheory.GroupCohomology.Bundle007
import ReciprocityTheory.GroupCohomology.Bundle006

@[expose] public section

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem norm_le_norm_iff_vK_of_pos (he : 0 < eK p K) (x y : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ ‖((y : K) : PadicAlgCl p)‖ ↔ vK p K y ≤ vK p K x := by
  have he' : (0 : ℝ) < eK p K := by positivity
  rw [← Real.logb_le_logb (one_lt_p_real p) (norm_units_pos x) (norm_units_pos y), ← Int.cast_le (R := ℝ),
    vK_spec, vK_spec, neg_le_neg_iff, mul_le_mul_iff_right₀ he']

theorem norm_le_one_iff_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ 1 ↔ 0 ≤ vK p K x := by
  have h := norm_le_norm_iff_vK_of_pos p K he x 1
  rw [vK_one] at h
  simpa using h

theorem norm_lt_one_iff_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ < 1 ↔ 1 ≤ vK p K x := by
  have h := norm_le_norm_iff_vK_of_pos p K he 1 x
  rw [vK_one] at h
  have h' : (1 : ℝ) ≤ ‖((x : K) : PadicAlgCl p)‖ ↔ vK p K x ≤ 0 := by simpa using h
  rw [← not_le, h']
  omega

theorem mem_UK_iff_of_pos (he : 0 < eK p K) (x : Kˣ) : x ∈ UK p K ↔ vK p K x = 0 := by
  show ‖((x : K) : PadicAlgCl p)‖ = 1 ↔ _
  have h1 := norm_le_one_iff_vK_of_pos p K he x
  have h2 := norm_lt_one_iff_vK_of_pos p K he x
  constructor
  · intro h
    have h3 := h1.1 h.le
    have h4 : ¬ (1 ≤ vK p K x) := fun h5 => (h2.2 h5).ne h
    omega
  · intro h
    have h3 := h1.2 (by omega)
    have h4 : ¬ ‖((x : K) : PadicAlgCl p)‖ < 1 := fun h5 => by have := h2.1 h5; omega
    exact le_antisymm h3 (not_lt.1 h4)

theorem mem_UK_iff (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) : x ∈ UK p K ↔ vK p K x = 0 :=
  mem_UK_iff_of_pos p K (eK_pos p K hK) x

theorem norm_le_one_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ 1 ↔ 0 ≤ vK p K x := norm_le_one_iff_vK_of_pos p K (eK_pos p K hK) x

theorem norm_lt_one_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ < 1 ↔ 1 ≤ vK p K x := norm_lt_one_iff_vK_of_pos p K (eK_pos p K hK) x

theorem norm_le_norm_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x y : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ ‖((y : K) : PadicAlgCl p)‖ ↔ vK p K y ≤ vK p K x :=
  norm_le_norm_iff_vK_of_pos p K (eK_pos p K hK) x y

theorem vK_p (x : Kˣ) (hx : ((x : K) : PadicAlgCl p) = (p : PadicAlgCl p)) : vK p K x = eK p K := by
  apply Int.cast_injective (α := ℝ)
  rw [vK_spec, hx, logb_norm_p]
  simp

def eLK : ℕ := eK p L / eK p K

def fLK : ℕ := fK p L / fK p K

variable {K L}

theorem multOf_mono (h : K ≤ L) : multOf p K ≤ multOf p L := fun _ hx => h hx

theorem valueGroup_mono (h : K ≤ L) : valueGroup p K ≤ valueGroup p L := AddSubgroup.map_mono (multOf_mono p h)

theorem eK_dvd_of_le (h : K ≤ L) : eK p K ∣ eK p L :=
  ⟨_, (AddSubgroup.relIndex_mul_relIndex (AddSubgroup.zmultiples (1 : ℝ)) (valueGroup p K) (valueGroup p L)
    (AddSubgroup.zmultiples_le_of_mem (one_mem_valueGroup p K)) (valueGroup_mono p h)).symm⟩

theorem eK_eq_mul_of_le (h : K ≤ L) : eK p L = eLK p K L * eK p K := (Nat.div_mul_cancel (eK_dvd_of_le p h)).symm

theorem eK_eq_mul (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) : eK p L = eLK p K L * eK p K := eK_eq_mul_of_le p h

theorem eK_eq_of_norm (h : K ≤ L) (hn : ∀ x ∈ L, ∃ y ∈ K, ‖x‖ = ‖y‖) : eK p L = eK p K := by
  have h1 : valueGroup p L = valueGroup p K := by
    refine le_antisymm ?_ (valueGroup_mono p h)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hn _ hx
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [norm_zero, norm_eq_zero] at hxy
      exact (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero hxy
    refine ⟨Additive.ofMul (Units.mk0 y hy0), hy, ?_⟩
    rw [vbar_apply p x, hxy]
    rfl
  unfold eK
  rw [h1]

theorem eK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : eK p (Kn p K n) = eK p K :=
  eK_eq_of_norm p (le_Kn p K n) fun _ hx => norm_Kn p K hK hn hx

theorem eLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : eLK p K (Kn p K n) = 1 := by
  rw [eLK, eK_Kn p hK hn, Nat.div_self (eK_pos p K hK)]

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem layer_inflation_h2_injective [(subG p K L).Normal] : Injective ((layerInf p K L).hom.H 2) :=
  multiplicative_inflation_h2_injective p K (subG p K L) (isClosed_subG p K L) _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)

theorem layerInf_layerInfl {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] (n : ℕ) (x : (layer p K L).H n) :
    (layerInf p K L').hom.H n ((layerInfl h).hom.H n x) = (layerInf p K L).hom.H n x := by
  induction x using Cx.H_ind with
  | h x hx => rfl

theorem BrLK_mono {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] : BrLK p K L ≤ BrLK p K L' := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(layerInfl h).hom.H 2 x, layerInf_layerInfl h 2 x⟩

theorem card_BrLK [(subG p K L).Normal] : Nat.card (BrLK p K L) = Nat.card ((layer p K L).H 2) :=
  (Nat.card_congr (LinearEquiv.ofInjective ((layerInf p K L).hom.H 2) layer_inflation_h2_injective).toEquiv).symm

theorem mem_BrKer_iff (h : K ≤ L) (x : Br p K) :
    x ∈ BrKer h ↔ (resP (kbarT p K) (subG p K L)).hom.H 2 x = 0 := by
  obtain ⟨e, he, hf⟩ := exists_resPair_factor h
  show (resPair h).hom.H 2 x = 0 ↔ _
  rw [hf 2 x]
  exact map_eq_zero_iff _ (he 2).1

theorem BrKer_eq_BrLK (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] :
    BrKer h = BrLK p K L := by
  ext x
  rw [mem_BrKer_iff]
  exact infRes2_exact (kbarT p K) (subG p K L) (isOpen_subG hL) _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)
    (restricted_multiplicative_h1_subsingleton p K _) x

theorem degLK_smul_eq_zero (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K) (hx : x ∈ BrKer h) :
    degLK p K L • x = 0 := by
  have := finiteIndex_subG (K := K) hL
  obtain ⟨cor, -, hcor⟩ := cor_holds ℤ (GK p K) (kbarT p K) (subG p K L) (isOpen_subG hL)
  have h2 := hcor 2 x
  rw [(mem_BrKer_iff h x).1 hx, map_zero] at h2
  exact h2.symm

theorem eq_zero_of_mem_BrKer_of_coprime (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K)
    (hx : x ∈ BrKer h) (k : ℕ) (hk : k • x = 0) (hc : Nat.Coprime k (degLK p K L)) : x = 0 := by
  have h1 := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hk)
    (addOrderOf_dvd_of_nsmul_eq_zero (degLK_smul_eq_zero hL h x hx))
  rw [Nat.Coprime.gcd_eq_one hc, Nat.dvd_one] at h1
  exact AddMonoid.addOrderOf_eq_one_iff.1 h1

theorem exists_mem_BrKer (hK : FiniteDimensional ℚ_[p] K) (x : Br p K) :
    ∃ (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ L), FiniteDimensional ℚ_[p] L ∧
      (subG p K L).Normal ∧ x ∈ BrKer h := by
  obtain ⟨N, hN, hNo, hx⟩ := FiniteLevelCohomology.exists_level (kbarT p K) 2 x
  obtain ⟨L, h, hL, rfl⟩ := exists_subG_eq_of_isOpen hK N hNo
  refine ⟨L, h, hL, hN, ?_⟩
  rw [BrKer_eq_BrLK hL h]
  exact hx _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
