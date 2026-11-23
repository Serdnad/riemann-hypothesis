module

public import GroundTheory.LocalFields.Bundle007
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.GeneralBFactAlt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RamificationLowerIndex
public import GroundTheory.LocalFields.Bundle008
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import GroundTheory.LocalFields.LocalFourierHaar
public import GroundTheory.LocalFields.PrincipalUnitsModule
public import GroundTheory.LocalFields.ExamplesCharZero
public import GroundTheory.LocalFields.PadicLogHom
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial

theorem addVal_prod {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ι : Type*}
    (s : Finset ι) (f : ι → R) : addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) :=
  _root_.Bl.general_b_fact'''''''.goal1 s f

section Restrict

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L)

theorem restrictNormalHom_restrictScalars [Normal K M] (τ : L ≃ₐ[M] L) :
    AlgEquiv.restrictNormalHom M (τ.restrictScalars K) = 1 := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, ← range_restrictScalarsHom M]
  exact ⟨τ, rfl⟩

theorem exists_eq_mul_restrictScalars_of_restrictNormalHom_eq [Normal K M] {σ ρ : L ≃ₐ[K] L}
    (h : AlgEquiv.restrictNormalHom M ρ = AlgEquiv.restrictNormalHom M σ) :
    ∃ τ : L ≃ₐ[M] L, σ * τ.restrictScalars K = ρ := by
  have hker : σ⁻¹ * ρ ∈ (AlgEquiv.restrictNormalHom M).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [IntermediateField.restrictNormalHom_ker, ← range_restrictScalarsHom M] at hker
  obtain ⟨τ, hτ⟩ := hker
  refine ⟨τ, ?_⟩
  rw [← AlgEquiv.restrictScalarsHom_apply, hτ, mul_inv_cancel_left]

end Restrict

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section

variable (M : IntermediateField K L)

section

variable [IsGalois K L]

theorem ramificationIndex_mul_lowerIndex_restrictNormalHom [Normal K M] (σ : L ≃ₐ[K] L) :
    ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) : ℕ∞) * lowerIndex K M (AlgEquiv.restrictNormalHom M σ) =
      ∑ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) :=
  by apply _root_.UpperTheory.Reformulated.B.RamificationLowerIndex.ramificationIndex_mul_lowerIndex_restrictNormalHom <;> assumption


end

theorem exists_lowerIndex_mul_eq_min (σ : L ≃ₐ[K] L) :
    ∃ τ₀ : L ≃ₐ[M] L,
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) ≤
        lowerIndex K L (σ * τ₀.restrictScalars K)) ∧
      ∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ₀.restrictScalars K * τ.restrictScalars K) =
        min (lowerIndex M L τ) (lowerIndex K L (σ * τ₀.restrictScalars K)) := by
  obtain ⟨τ₀, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun τ : L ≃ₐ[M] L ↦ lowerIndex K L (σ * τ.restrictScalars K)) Finset.univ_nonempty
  refine ⟨τ₀, fun τ ↦ hmax τ (Finset.mem_univ _), fun τ ↦ ?_⟩
  set σ₀ := σ * τ₀.restrictScalars K with hσ₀
  rw [← lowerIndex_restrictScalars (K := K)]
  rcases lt_or_ge (lowerIndex K L (τ.restrictScalars K)) (lowerIndex K L σ₀) with h | h
  · rw [lowerIndex_mul_of_lt h, min_eq_left h.le]
  · rw [min_eq_right h]
    refine le_antisymm ?_ ((min_eq_left h).symm.le.trans (min_le_lowerIndex_mul _ _))
    have hm : (τ₀ * τ).restrictScalars K = τ₀.restrictScalars K * τ.restrictScalars K :=
      AlgEquiv.ext fun _ ↦ rfl
    have := hmax (τ₀ * τ) (Finset.mem_univ _)
    rwa [hm, ← mul_assoc] at this

end

end GroundTheory.LocalField
end
end

section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Topology Filter
open scoped WithZero Pointwise

section RatCircle

def ratAddCircleToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ : ℚ →+* ℝ).toAddMonoidHom
    (AddSubgroup.zmultiples_le_of_mem (by
      rw [AddSubgroup.mem_comap]
      simp))

theorem ratAddCircleToReal_coe (q : ℚ) :
    ratAddCircleToReal (q : AddCircle (1 : ℚ)) = ((q : ℝ) : AddCircle (1 : ℝ)) := rfl

theorem ratAddCircleToReal_injective : Function.Injective ratAddCircleToReal := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    rw [ratAddCircleToReal_coe, AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
    simpa using (Rat.cast_injective this)

def ratCircleChar : AddChar (AddCircle (1 : ℚ)) Circle :=
  (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom ratAddCircleToReal

theorem ratCircleChar_injective : Function.Injective ratCircleChar :=
  (AddCircle.injective_toCircle one_ne_zero).comp ratAddCircleToReal_injective

theorem ratCircleChar_eq_one_iff {x : AddCircle (1 : ℚ)} : ratCircleChar x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply ratCircleChar_injective
    rw [h, AddChar.map_zero_eq_one]
  · rintro rfl
    exact AddChar.map_zero_eq_one _

end RatCircle

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Existence

theorem exists_mem_valBall_neg_one_notMem_valBall_zero :
    ∃ x : K, x ∈ valBall K (-1) ∧ x ∉ valBall K 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hi : (ϖ : K)⁻¹ ≠ 0 := inv_ne_zero h0
  refine ⟨(ϖ : K)⁻¹, ?_, ?_⟩
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
    omega

theorem continuous_of_isTrivialOn {χ : AddChar K Circle} {n : ℤ} (h : IsTrivialOn χ n) :
    Continuous χ := by
  have hlc : IsLocallyConstant χ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{z | z - x ∈ valBall K n},
      (isOpen_valBall n).preimage (continuous_id.sub continuous_const), by simp, fun z hz => ?_⟩
    have e : x + (z - x) = z := by abel
    rw [← e, AddChar.map_add_eq_mul, h _ hz, mul_one]
  exact hlc.continuous

theorem exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one :
    ∃ ψ : AddChar K Circle, IsTrivialOn ψ 0 ∧ ¬ IsTrivialOn ψ (-1) := by
  obtain ⟨x, hx1, hx0⟩ := exists_mem_valBall_neg_one_notMem_valBall_zero (K := K)
  let π : K →+ K ⧸ valBall K 0 := QuotientAddGroup.mk' (valBall K 0)
  have hπx : π x ≠ 0 := by
    rwa [Ne, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hπx
  let ψ : AddChar K Circle :=
    ratCircleChar.compAddMonoidHom ((c : K ⧸ valBall K 0 →+ AddCircle (1 : ℚ)).comp π)
  have hψ : ∀ y, ψ y = ratCircleChar (c (π y)) := fun _ => rfl
  refine ⟨ψ, fun y hy => ?_, fun h => ?_⟩
  · have : π y = 0 := by
      rwa [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [hψ, this, map_zero, AddChar.map_zero_eq_one]
  · exact hc (ratCircleChar_eq_one_iff.mp ((hψ x).symm.trans (h x hx1)))

theorem exists_addChar_addCharConductor_eq_zero :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 ∧ addCharConductor ψ = 0 := by
  obtain ⟨ψ, h0, h1⟩ := exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one (K := K)
  have hc : Continuous ψ := continuous_of_isTrivialOn h0
  have hne : ψ ≠ 1 := by
    rintro rfl
    exact h1 fun _ _ => AddChar.one_apply _
  refine ⟨ψ, hc, hne, le_antisymm ((isTrivialOn_iff hc hne 0).mp h0) ?_⟩
  by_contra hlt
  exact h1 ((isTrivialOn_iff hc hne (-1)).mpr (by omega))

theorem exists_addChar_continuous_ne_one :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 := by
  obtain ⟨ψ, hc, hne, -⟩ := exists_addChar_addCharConductor_eq_zero (K := K)
  exact ⟨ψ, hc, hne⟩

end Existence

end GroundTheory.LocalField
end
end

section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem eq_zero_of_forall_mem_valBall {y : K} (h : ∀ N : ℤ, y ∈ valBall (K := K) N) : y = 0 := by
  by_contra hy
  have := h (ord y + 1)
  rw [mem_valBall, normalizedValuation_eq_exp_ord hy, WithZero.exp_le_exp] at this
  omega

theorem exists_mem_valBall (y : K) : ∃ M : ℤ, y ∈ valBall (K := K) M := by
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  · exact ⟨ord y, by rw [mem_valBall, normalizedValuation_eq_exp_ord hy]⟩

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem padicHom_padicInt_mem_valBall_zero (t : ℤ_[p]) :
    CharZero.padicHom K p (t : ℚ_[p]) ∈ valBall (K := K) 0 := by
  rw [mem_valBall, neg_zero, WithZero.exp_zero, ← map_one (normalizedValuation K),
    normalizedValuation_le_iff, map_one]
  exact CharZero.valuation_padicHom_padicInt_le_one K p t


include p in
include p in
theorem padicLog_mem_valBall_of_mem {k : ℕ} (hk : absRamificationIndex (K := K) ≤ k)
    {w : Additive (unitFiltrationUnits K 1)} (hw : w ∈ principalFiltration (K := K) k) :
    padicLog K w ∈ valBall (K := K) (k + 1) := by
  rw [mem_principalFiltration] at hw
  rw [padicLog_apply]
  refine logSeries_mem_valBall p hw ?_
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have : (absRamificationIndex (K := K) : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem padicLog_smul (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K (a • u) = CharZero.padicHom K p (a : ℚ_[p]) * padicLog K u := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_valBall fun N ↦ ?_
  set e := absRamificationIndex (K := K)
  have he := one_le_absRamificationIndex (K := K) p
  obtain ⟨M, hM⟩ := exists_mem_valBall (padicLog K u)
  set k : ℕ := N.toNat + M.natAbs + e + 1 with hk_def
  set c : ℤ := ((a.appr k : ℕ) : ℤ)
  have hac := dvd_sub_appr p k a
  obtain ⟨t, ht⟩ := hac
  have hw := smul_sub_intCast_smul_mem p (dvd_sub_appr p k a) u
  have h1 := padicLog_mem_valBall_of_mem p (by omega : e ≤ k) hw
  rw [map_sub, map_zsmul, zsmul_eq_mul] at h1
  have h2 : CharZero.padicHom K p (a : ℚ_[p]) - (c : K) =
      ((p ^ k : ℕ) : K) * CharZero.padicHom K p (t : ℚ_[p]) := by
    have := congrArg (fun z : ℤ_[p] ↦ CharZero.padicHom K p (z : ℚ_[p])) ht
    simp only [PadicInt.coe_sub, PadicInt.coe_intCast, map_sub, map_intCast, PadicInt.coe_mul,
      PadicInt.coe_pow, PadicInt.coe_natCast, map_mul, map_pow, map_natCast] at this
    rw [this]; push_cast; ring
  have h3 : (CharZero.padicHom K p (a : ℚ_[p]) - (c : K)) * padicLog K u ∈
      valBall (K := K) (e * k + 0 + M) := by
    rw [h2]
    exact mul_mem_valBall (mul_mem_valBall (natCast_prime_pow_mem_valBall p k)
      (padicHom_padicInt_mem_valBall_zero p t)) hM
  have heq : padicLog K (a • u) - CharZero.padicHom K p (a : ℚ_[p]) * padicLog K u =
      (padicLog K (a • u) - (c : K) * padicLog K u) -
        (CharZero.padicHom K p (a : ℚ_[p]) - (c : K)) * padicLog K u := by ring
  rw [heq]
  have hNt := Int.self_le_toNat N
  have hMa := neg_abs_le M
  have hMa' := abs_nonneg M
  have hN1 : N ≤ (k : ℤ) + 1 := by rw [hk_def]; push_cast; omega
  have hN2 : N ≤ (e : ℤ) * k + 0 + M := by
    have : (k : ℤ) ≤ e * k := by
      have : (1 : ℤ) ≤ e := by exact_mod_cast he
      nlinarith [(by positivity : (0 : ℤ) ≤ k)]
    rw [hk_def] at this ⊢; push_cast at this ⊢; omega
  exact sub_mem (valBall_antitone hN1 h1) (valBall_antitone hN2 h3)

end GroundTheory.LocalField
end
