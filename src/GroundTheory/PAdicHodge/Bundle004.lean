module

public import GroundTheory.PAdicHodge.Bundle002
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import GroundTheory.PowerSubgroups.CountableNeighbourhoods.Bundle001
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import GroundTheory.LocalFields.Bundle002
import Mathlib.Algebra.Lie.OfAssociative
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import GroundTheory.PAdicHodge.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open ValuativeRel

variable {p : ℕ} [Fact p.Prime]

section Subfield

variable {S : Type*} [SetLike S (PadicAlgCl p)] [SubfieldClass S (PadicAlgCl p)] (s : S)

instance subfield_isUltrametricDist : IsUltrametricDist s :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
    (PadicAlgCl.isNonarchimedean p) (x : PadicAlgCl p) y

instance subfield_valuativeRel : ValuativeRel s :=
  ValuativeRel.ofValuation (NormedField.valuation (K := s))

theorem subfield_norm_def (x : s) : ‖x‖ = ‖(x : PadicAlgCl p)‖ := rfl

theorem subfield_vle_iff_norm_le (x y : s) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  exact NNReal.coe_le_coe

instance subfield_compatible : (NormedField.valuation (K := s)).Compatible :=
  Valuation.Compatible.ofValuation _

instance subfield_isValuativeTopology : IsValuativeTopology s := by
  let : Valued s NNReal := NormedField.toValued
  have : (Valued.v : Valuation s NNReal).Compatible := subfield_compatible s
  exact GroundTheory.LocalField.isValuativeTopology_of_valued

theorem subfield_norm_natCast_prime : ‖((p : ℕ) : s)‖ = (p : ℝ)⁻¹ := by
  rw [subfield_norm_def]
  have h := PadicAlgCl.valuation_coe p (p : PadicAlgCl p)
  rw [PadicAlgCl.valuation_p] at h
  push_cast [map_natCast] at h ⊢
  rw [← h]
  simp

instance subfield_isNontrivial : IsNontrivial s := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine ⟨⟨valuation s (p : s), ?_, ?_⟩⟩
  · rw [ne_eq, Valuation.zero_iff]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  · intro h
    have h2 : (1 : s) ≤ᵥ ((p : ℕ) : s) := by
      rw [Valuation.vle_iff_le (valuation s), h, map_one]
    rw [subfield_vle_iff_norm_le, subfield_norm_natCast_prime, norm_one] at h2
    exact absurd h2 (not_le.2 (inv_lt_one_of_one_lt₀ hp))

theorem integer_eq_normInteger : 𝒪[s] = normInteger s := by
  ext x
  rw [Valuation.mem_integer_iff, mem_normInteger, ← map_one (valuation s),
    ← Valuation.vle_iff_le, subfield_vle_iff_norm_le, norm_one]

end Subfield

theorem locallyCompactSpace_of_finiteDimensional (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] : LocallyCompactSpace K := by
  let M := Subalgebra.toSubmodule K.toSubalgebra
  have : FiniteDimensional ℚ_[p] M := (inferInstance : FiniteDimensional ℚ_[p] K)
  have : ProperSpace M := FiniteDimensional.proper ℚ_[p] M
  exact (inferInstance : LocallyCompactSpace M)

theorem isNonarchimedeanLocalField_of_coe_eq {S : Type*} [SetLike S (PadicAlgCl p)]
    [SubfieldClass S (PadicAlgCl p)] (s : S) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (h : (s : Set (PadicAlgCl p)) = K) :
    IsNonarchimedeanLocalField s := by
  have : LocallyCompactSpace (K : Set (PadicAlgCl p)) := locallyCompactSpace_of_finiteDimensional K
  have : LocallyCompactSpace s := (Homeomorph.setCongr h).isClosedEmbedding.locallyCompactSpace
  exact {}

instance isNonarchimedeanLocalField_intermediateField (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] : IsNonarchimedeanLocalField K :=
  isNonarchimedeanLocalField_of_coe_eq K K rfl

instance finiteDimensional_tower (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (L : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K L] :
    FiniteDimensional ℚ_[p] L :=
  Module.Finite.trans K L

instance isNonarchimedeanLocalField_tower (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (L : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K L] :
    IsNonarchimedeanLocalField L :=
  have : FiniteDimensional ℚ_[p] (L.restrictScalars ℚ_[p]) :=
    (inferInstance : FiniteDimensional ℚ_[p] L)
  isNonarchimedeanLocalField_of_coe_eq L (L.restrictScalars ℚ_[p]) rfl

instance valuativeExtension_padic (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    ValuativeExtension ℚ_[p] K := by
  refine ⟨fun {a b} => ?_⟩
  rw [subfield_vle_iff_norm_le, subfield_norm_def, subfield_norm_def,
    IntermediateField.coe_algebraMap_apply, IntermediateField.coe_algebraMap_apply]
  have ha : ‖algebraMap ℚ_[p] (PadicAlgCl p) a‖ = ‖a‖ := PadicAlgCl.norm_extends p a
  have hb : ‖algebraMap ℚ_[p] (PadicAlgCl p) b‖ = ‖b‖ := PadicAlgCl.norm_extends p b
  rw [ha, hb, Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le]

instance valuativeExtension_intermediateField {F : Type*} [Field F] [Algebra F (PadicAlgCl p)]
    (E : IntermediateField F (PadicAlgCl p)) (L : IntermediateField E (PadicAlgCl p)) :
    ValuativeExtension E L :=
  ⟨fun {_ _} => by rw [subfield_vle_iff_norm_le, subfield_vle_iff_norm_le]; rfl⟩

section Unique

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

end Unique

section Inclusion

variable {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L)

theorem valuativeExtension_inclusion :
    (letI := (IntermediateField.inclusion h).toRingHom.toAlgebra; ValuativeExtension K L) := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact ⟨fun {_ _} => by rw [subfield_vle_iff_norm_le, subfield_vle_iff_norm_le]; rfl⟩

theorem isScalarTower_inclusion :
    (letI := (IntermediateField.inclusion h).toRingHom.toAlgebra; IsScalarTower ℚ_[p] K L) := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem finiteDimensional_inclusion [FiniteDimensional ℚ_[p] L] :
    (letI := (IntermediateField.inclusion h).toRingHom.toAlgebra; FiniteDimensional K L) := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have := isScalarTower_inclusion h
  exact Module.Finite.of_restrictScalars_finite ℚ_[p] K L

end Inclusion

section Galois

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (L : IntermediateField K (PadicAlgCl p))
  [Normal K L]

end Galois

section Examples

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
  (L : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K L]

end Examples

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent Module

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]


variable (K) in
def dvUnif : K := ((IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose : K)

theorem irreducible_dvUnif :
    Irreducible (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose :=
  (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose_spec

theorem norm_eq_one_of_isUnit {z : normInteger K} (hz : IsUnit z) : ‖(z : K)‖ = 1 := by
  have := (normInteger_integers (K := K)).isUnit_iff_valuation_eq_one.1 hz
  rw [NormedField.valuation_apply, ← NNReal.coe_eq_one] at this
  exact this

theorem exists_norm_eq_zpow {x : K} (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = ‖dvUnif K‖ ^ n := by
  have key : ∀ y : K, y ≠ 0 → ‖y‖ ≤ 1 → ∃ n : ℕ, ‖y‖ = ‖dvUnif K‖ ^ n := by
    intro y hy hy1
    let z : normInteger K := ⟨y, mem_normInteger.2 hy1⟩
    have hz : z ≠ 0 := fun h => hy (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz irreducible_dvUnif
    refine ⟨n, ?_⟩
    have h2 := congrArg (fun w : normInteger K => (w : K)) hu
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow] at h2
    rw [show y = (z : K) from rfl, h2, norm_mul, norm_pow, norm_eq_one_of_isUnit u.isUnit, one_mul]
    rfl
  rcases le_total ‖x‖ 1 with h | h
  · obtain ⟨n, hn⟩ := key x hx h
    exact ⟨n, by rw [hn, zpow_natCast]⟩
  · obtain ⟨n, hn⟩ := key x⁻¹ (inv_ne_zero hx) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h)
    refine ⟨-(n : ℤ), ?_⟩
    rw [norm_inv] at hn
    rw [zpow_neg, zpow_natCast, ← hn, inv_inv]

namespace Robba

end Robba

namespace Robba

end Robba

namespace PhiModule

open Matrix

end PhiModule

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Matrix Finset Equiv

abbrev KSubset (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

def KSubset.emb {n k : ℕ} (s : KSubset n k) : Fin k ↪o Fin n := s.1.orderEmbOfFin s.2

theorem KSubset.range_emb {n k : ℕ} (s : KSubset n k) : Set.range s.emb = (s.1 : Set (Fin n)) :=
  Finset.range_orderEmbOfFin _ _

variable {R : Type*} [CommRing R]

section CauchyBinet

variable {k n : ℕ}

private theorem det_mul_eq_sum_fun (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ p : Fin k → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id, sum_mul, prod_mul_distrib, mul_assoc]
  rw [Finset.sum_comm]

theorem det_mul_eq_sum_minors (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ s : KSubset n k, (A.submatrix id s.emb).det * (B.submatrix s.emb id).det := by
  classical
  set F : (Fin k → Fin n) → R := fun p => (A.submatrix id p).det * ∏ i, B (p i) i with hF
  have hzero : ∀ p, ¬ Function.Injective p → F p = 0 := by
    intro p hp
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hp
      obtain ⟨i, j, h, hne⟩ := hp
      exact ⟨i, j, h, hne⟩
    simp only [hF]
    rw [det_zero_of_column_eq hne (fun r => by simp [hij]), zero_mul]
  have hterm : ∀ (s : KSubset n k) (σ : Perm (Fin k)),
      F (s.emb ∘ σ) = (A.submatrix id s.emb).det * (Perm.sign σ * ∏ i, B (s.emb (σ i)) i) := by
    intro s σ
    simp only [hF]
    have : A.submatrix id (s.emb ∘ σ) = (A.submatrix id s.emb).submatrix id σ := rfl
    rw [this, det_permute']
    simp only [Function.comp_apply]
    ring
  have hs : ∀ s : KSubset n k, (A.submatrix id s.emb).det * (B.submatrix s.emb id).det =
      ∑ σ : Perm (Fin k), F (s.emb ∘ σ) := by
    intro s
    simp only [hterm, ← mul_sum]
    congr 1
    rw [det_apply']
    rfl
  have hprod := Fintype.sum_prod_type (fun x : KSubset n k × Perm (Fin k) => F (x.1.emb ∘ x.2))
  simp only at hprod
  rw [det_mul_eq_sum_fun, Finset.sum_congr rfl (fun s _ => hs s)]
  change ∑ p, F p = _
  rw [← hprod, ← Finset.sum_filter_of_ne (p := Function.Injective) (fun p _ h => by
      by_contra hp; exact h (hzero p hp))]
  symm
  refine Finset.sum_bij (fun x _ => x.1.emb ∘ x.2) ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.1.emb.injective.comp x.2.injective
  · rintro ⟨s, σ⟩ _ ⟨t, τ⟩ _ h
    simp only at h
    have hst : s = t := by
      apply Subtype.ext
      have h1 : Set.range (s.emb ∘ σ) = Set.range (t.emb ∘ τ) := by rw [h]
      rw [Set.range_comp, Set.range_comp, σ.range_eq_univ, τ.range_eq_univ, Set.image_univ,
        Set.image_univ, KSubset.range_emb, KSubset.range_emb] at h1
      exact_mod_cast h1
    subst hst
    have : σ = τ := by
      ext i
      have := congrFun h i
      simp only [Function.comp_apply] at this
      exact congrArg Fin.val (s.emb.injective this)
    rw [this]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hcard : (Finset.univ.image p).card = k := by
      rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_fin]
    let s : KSubset n k := ⟨Finset.univ.image p, hcard⟩
    have hex : ∀ i, ∃ j, s.emb j = p i := by
      intro i
      have : p i ∈ (s.1 : Set (Fin n)) := by simp [s]
      rw [← KSubset.range_emb] at this
      exact this
    choose f hf using hex
    have hfinj : Function.Injective f := by
      intro i j hij
      apply hp
      rw [← hf i, ← hf j, hij]
    let σ : Perm (Fin k) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
    refine ⟨(s, σ), Finset.mem_univ _, ?_⟩
    funext i
    exact hf i
  · intro x _
    rfl

end CauchyBinet

section Minors

variable {m n k : ℕ}

def maxMinor (B : Matrix (Fin n) (Fin k) R) (s : KSubset n k) : R :=
  (B.submatrix s.emb id).det

end Minors

section Independence

variable {n k : ℕ}

theorem linearIndependent_col_iff_mulVec_eq_zero (B : Matrix (Fin n) (Fin k) R) :
    LinearIndependent R B.col ↔ ∀ v, B *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  have key : ∀ v : Fin k → R, ∑ j, v j • B.col j = B *ᵥ v := by
    intro v; ext i; simp [mulVec, dotProduct, Finset.sum_apply, col, mul_comm]
  constructor
  · intro h v hv
    funext j
    exact h v (by rw [key, hv]) j
  · intro h g hg j
    have := h g (by rw [← key, hg])
    exact congrFun this j

theorem exists_maxMinor_ne_zero_of_linearIndependent [IsDomain R]
    (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 :=
  _root_.GroundTheory.Variant₂.N1.exists_maxMinor_ne_zero_of_linearIndependent_alt B hB

end Independence

end GroundTheory.PAdicHodge
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace CyclNorms

open GroundTheory.LocalField ValuativeRel

variable (p : ℕ) [Fact p.Prime]

scoped instance padicAlgCl_valuativeRel : ValuativeRel (PadicAlgCl p) :=
  ValuativeRel.ofValuation (NormedField.valuation (K := PadicAlgCl p))

variable {p}

theorem vle_iff_norm_le (x y : PadicAlgCl p) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  exact NNReal.coe_le_coe

scoped instance padicAlgCl_compatible : (NormedField.valuation (K := PadicAlgCl p)).Compatible :=
  Valuation.Compatible.ofValuation _

scoped instance padicAlgCl_isValuativeTopology : IsValuativeTopology (PadicAlgCl p) := by
  let : Valued (PadicAlgCl p) NNReal := NormedField.toValued
  have : (Valued.v : Valuation (PadicAlgCl p) NNReal).Compatible := padicAlgCl_compatible
  exact GroundTheory.LocalField.isValuativeTopology_of_valued

scoped instance padicAlgCl_valuativeExtension : ValuativeExtension ℚ_[p] (PadicAlgCl p) := by
  refine ⟨fun {a b} ↦ ?_⟩
  rw [vle_iff_norm_le, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le]

end CyclNorms

end GroundTheory.PAdicHodge
end
end
