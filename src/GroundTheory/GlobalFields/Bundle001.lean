module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped NumberField nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace SUnit

theorem forall_valuation_eq_one_iff (x : Kˣ) :
    (∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (x : K) = 1) ↔
      x ∈ (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).range := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := mem_integers_of_valuation_le_one (R := 𝓞 K) K (x : K) fun v => (h v).le
    obtain ⟨b, hb⟩ := mem_integers_of_valuation_le_one (R := 𝓞 K) K ((x⁻¹ : Kˣ) : K) fun v => by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, ha, hb, map_one, Units.mul_inv]
    have hba : b * a = 1 := by rw [mul_comm, hab]
    refine ⟨⟨a, b, hab, hba⟩, ?_⟩
    ext
    simp [ha]
  · rintro ⟨u, rfl⟩ v
    rw [← valuationOfNeZero_eq, valuation_of_unit_eq, WithZero.coe_one]

variable (S : Set (HeightOneSpectrum (𝓞 K)))

def ofUnits : (𝓞 K)ˣ →* S.unit K where
  toFun u := ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u, fun v _ =>
    (forall_valuation_eq_one_iff _).mpr ⟨u, rfl⟩ v⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]
theorem coe_ofUnits (u : (𝓞 K)ˣ) : ((ofUnits S u : Kˣ) : K) = algebraMap (𝓞 K) K u := rfl

theorem ofUnits_injective : Function.Injective (ofUnits S (K := K)) := by
  intro u u' h
  have : ((ofUnits S u : Kˣ) : K) = ((ofUnits S u' : Kˣ) : K) := by rw [h]
  simp only [coe_ofUnits] at this
  exact Units.ext (IsFractionRing.injective (𝓞 K) K this)

def valuationVector : Additive (S.unit K) →ₗ[ℤ] (S → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x v => Multiplicative.toAdd (v.1.valuationOfNeZero ((x.toMul : S.unit K) : Kˣ))
      map_zero' := by funext v; simp
      map_add' := fun x y => by funext v; simp }

theorem valuationVector_apply (x : S.unit K) (v : S) :
    valuationVector S (Additive.ofMul x) v = Multiplicative.toAdd (v.1.valuationOfNeZero (x : Kˣ)) :=
  rfl

theorem mem_ker_valuationVector_iff (x : S.unit K) :
    Additive.ofMul x ∈ LinearMap.ker (valuationVector S) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((x : Kˣ) : K) = 1 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h v
    by_cases hv : v ∈ S
    · have h1 := congrFun h ⟨v, hv⟩
      rw [valuationVector_apply, Pi.zero_apply, toAdd_eq_zero] at h1
      rw [← valuationOfNeZero_eq, h1, WithZero.coe_one]
    · exact x.2 v hv
  · intro h
    funext v
    rw [valuationVector_apply, Pi.zero_apply, toAdd_eq_zero, ← WithZero.coe_inj,
      valuationOfNeZero_eq, WithZero.coe_one]
    exact h v.1

theorem ker_valuationVector :
    LinearMap.ker (valuationVector S) =
      LinearMap.range (ofUnits S).toAdditive.toIntLinearMap := by
  ext x
  rw [← ofMul_toMul x, mem_ker_valuationVector_iff, LinearMap.mem_range]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (forall_valuation_eq_one_iff _).mp h
    exact ⟨Additive.ofMul u, by
      change Additive.ofMul (ofUnits S u) = _
      congr 1
      exact Subtype.ext hu⟩
  · rintro ⟨u, hu⟩
    have hx : ofUnits S u.toMul = x.toMul := congrArg Additive.toMul hu
    rw [← hx]
    exact (forall_valuation_eq_one_iff _).mpr ⟨u.toMul, rfl⟩

def unitsEquivKer : Additive (𝓞 K)ˣ ≃ₗ[ℤ] LinearMap.ker (valuationVector S) :=
  (LinearEquiv.ofInjective (ofUnits S).toAdditive.toIntLinearMap
    (ofUnits_injective S)).trans (LinearEquiv.ofEq _ _ (ker_valuationVector S).symm)

end SUnit

end

end GroundTheory.Global
end

section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace GroundTheory.Global

section Residue

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ r ∈ v.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one, algebraMap_adicCompletionIntegers_apply,
    valuedAdicCompletion_eq_valuation', valuation_eq_one_iff_notMem, not_not]

theorem exists_algebraMap_sub_mem_maximalIdeal (x : v.adicCompletionIntegers K) :
    ∃ r : R, x - algebraMap R (v.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by

  have hnhds : {y : v.adicCompletion K | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) :=
    Valued.mem_nhds.2 ⟨1, fun y hy ↦ by
      simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (K := K) v).mem_nhds hnhds
  have hk' : Valued.v ((x : v.adicCompletion K) - (k : v.adicCompletion K)) < 1 := by
    rw [Valuation.map_sub_swap]; exact hk

  have hk1 : v.valuation K k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    have : (k : v.adicCompletion K) = (x : v.adicCompletion K) -
        ((x : v.adicCompletion K) - (k : v.adicCompletion K)) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le x.2 hk'.le)
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer v hk1 1
  refine ⟨r, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]
  refine ne_of_lt ?_
  have hr' : Valued.v (algebraMap K (v.adicCompletion K) (k - algebraMap R K r)) < 1 := by
    rw [Valuation.map_sub_swap] at hr
    have := valuedAdicCompletion_eq_valuation' (R := R) v (k - algebraMap R K r)
    exact this.trans_lt (by simpa using hr)
  have : ((x - algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) :
      v.adicCompletion K) = ((x : v.adicCompletion K) - (k : v.adicCompletion K)) +
        algebraMap K (v.adicCompletion K) (k - algebraMap R K r) := by
    rw [map_sub]
    simp [algebraMap_adicCompletion]
  rw [this]
  exact Valuation.map_add_lt _ hk' hr'

noncomputable def toResidueFieldAdicCompletionIntegers :
    R →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (IsLocalRing.residue _).comp (algebraMap R (v.adicCompletionIntegers K))

theorem ker_toResidueFieldAdicCompletionIntegers :
    RingHom.ker (toResidueFieldAdicCompletionIntegers (K := K) v) = v.asIdeal := by
  ext r
  rw [RingHom.mem_ker, toResidueFieldAdicCompletionIntegers, RingHom.comp_apply,
    IsLocalRing.residue_eq_zero_iff, algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff]

theorem toResidueFieldAdicCompletionIntegers_surjective :
    Function.Surjective (toResidueFieldAdicCompletionIntegers (K := K) v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, hr⟩ := exists_algebraMap_sub_mem_maximalIdeal v x
  exact ⟨r, (Ideal.Quotient.eq.2 hr).symm⟩

noncomputable def residueFieldEquiv :
    (R ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (Ideal.quotEquivOfEq (ker_toResidueFieldAdicCompletionIntegers v).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toResidueFieldAdicCompletionIntegers_surjective v))

end Residue

section NumberField

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

instance : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  haveI := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  Finite.of_equiv _ (residueFieldEquiv v).toEquiv

theorem natCard_residueField_adicCompletionIntegers :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (residueFieldEquiv v).toEquiv).symm

end NumberField

section Topology

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isOpen_adicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

theorem isClosed_adicCompletionIntegers :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  (Valued.isClopen_integer (v.adicCompletion K)).isClosed

theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have : CompleteSpace (Valued.integer (v.adicCompletion K)) :=
    (isClosed_adicCompletionIntegers v).completeSpace_coe
  have : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  have : Finite (Valued.ResidueField (v.adicCompletion K)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  have h : CompactSpace (Valued.integer (v.adicCompletion K)) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact isCompact_iff_compactSpace.2 h

instance : CompactSpace (v.adicCompletionIntegers K) :=
  isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)

instance : LocallyCompactSpace (v.adicCompletion K) :=
  (isCompact_adicCompletionIntegers v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isOpen_adicCompletionIntegers v).mem_nhds (v.adicCompletionIntegers K).zero_mem)

end Topology

end GroundTheory.Global
end
