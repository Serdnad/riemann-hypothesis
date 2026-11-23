module

public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle002
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.Statement
public import Mathlib.Data.Nat.Totient
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem relIndex_sup_normal {Γ : Type} [Group Γ] (K D H : Subgroup Γ) [K.Normal] (hD : D ≤ H) :
    H.relIndex (K ⊔ D) = H.relIndex K := by
  classical
  unfold Subgroup.relIndex Subgroup.index
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ D)) fun a b h => ?_) ⟨?_, ?_⟩)
  · rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h
  · refine Quotient.ind' fun a => Quotient.ind' fun b => ?_
    intro h
    simp only [Quotient.map'_mk''] at h
    rw [Quotient.eq''] at h ⊢
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h
  · refine Quotient.ind' fun y => ?_
    obtain ⟨k, hk, d, hd, hkd⟩ := Subgroup.mem_sup_of_normal_left.mp y.2
    refine ⟨Quotient.mk'' ⟨k, hk⟩, ?_⟩
    simp only [Quotient.map'_mk'']
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    have hy : (y : Γ) = k * d := hkd.symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hy, inv_mul_cancel_left]
    exact hD hd

theorem UpperTheory.V.Two.supIndex :
    ∀ (Γ : Type) [Group Γ] (K W D : Subgroup Γ) [K.Normal] [W.Normal], W.index ≠ 0 → (K ⊔ D).index ≠ 0 → ((W ⊓ K) ⊔ D).index ≠ 0 ∧ ((W ⊓ K) ⊔ D).index ≤ W.index * (K ⊔ D).index := by
  intro Γ _ K W D _ _ hW hKD
  have hLKD : (W ⊓ K) ⊔ D ≤ K ⊔ D := sup_le_sup_right inf_le_right D
  have hDL : D ≤ (W ⊓ K) ⊔ D := le_sup_right
  have hWKL : W ⊓ K ≤ (W ⊓ K) ⊔ D := le_sup_left
  have h1 : ((W ⊓ K) ⊔ D).index = ((W ⊓ K) ⊔ D).relIndex K * (K ⊔ D).index := by
    rw [← relIndex_sup_normal K D _ hDL, Subgroup.relIndex_mul_index hLKD]
  have h2 : ((W ⊓ K) ⊔ D).relIndex K ∣ W.index := by
    have h := Subgroup.relIndex_dvd_of_le_left K hWKL
    rw [Subgroup.inf_relIndex_right] at h
    exact h.trans (Subgroup.relIndex_dvd_index_of_normal W K)
  have h3 : ((W ⊓ K) ⊔ D).relIndex K ≠ 0 := fun h => hW (Nat.eq_zero_of_zero_dvd (h ▸ h2))
  have h4 : ((W ⊓ K) ⊔ D).relIndex K ≤ W.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hW) h2
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact mul_ne_zero h3 hKD
  · rw [h1]
    exact Nat.mul_le_mul_right _ h4
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem two_pow_dvd_intCast_padic_iff (k : ℤ) (n : ℕ) : (2 : ℤ_[2]) ^ n ∣ (k : ℤ_[2]) ↔ (2 : ℤ) ^ n ∣ k := by
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) (k : ℤ_[2]) n).symm.trans
    (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := k) (n := n))
  rw [Ideal.mem_span_singleton] at h
  exact_mod_cast h

private theorem index_closed_dyadic_subgroup (H : Subgroup ℤ_[2]ˣ) (u : ℤ_[2]ˣ) (p a : ℕ) (hH : IsClosed (H : Set ℤ_[2]ˣ))
    (hu : u ∈ H) (hp : (u : ℤ_[2]) = p) (ha : 2 ≤ a) (h1 : (2 : ℤ) ^ a ∣ (p : ℤ) ^ 2 - 1)
    (h2 : ¬ (2 : ℤ) ^ (a + 1) ∣ (p : ℤ) ^ 2 - 1) (h3 : ¬ (2 : ℤ) ^ a ∣ (p : ℤ) - 1) :
    H.index ≠ 0 ∧ 2 * H.index ≤ Nat.totient (2 ^ a) := by
  have hu2 : ((u ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1 = (((p : ℤ) ^ 2 - 1 : ℤ) : ℤ_[2]) := by
    push_cast [Units.val_pow_eq_pow_val, hp]
    ring
  have hem : emultiplicity ((2 : ℕ) : ℤ_[2]) (((u ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1) = (a : ℕ∞) := by
    rw [emultiplicity_eq_coe, hu2]
    simp only [Nat.cast_ofNat, two_pow_dvd_intCast_padic_iff]
    exact ⟨h1, h2⟩
  have hle : KStar.TotallyRealRoots.princ 2 a ≤ H :=
    KStar.TotallyRealRoots.princ_le_of_isClosed (by omega) (fun _ => ha) hH (H.pow_mem hu 2) hem
  have hnot : u ∉ KStar.TotallyRealRoots.princ 2 a := by
    rw [KStar.TotallyRealRoots.mem_princ, hp]
    intro h
    apply h3
    rw [← two_pow_dvd_intCast_padic_iff]
    exact_mod_cast h
  have hidx : (KStar.TotallyRealRoots.princ 2 a).index ≤ Nat.totient (2 ^ a) := by
    rw [KStar.TotallyRealRoots.princ, Subgroup.index_ker, ← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_le_card_group _
  have hpos : 0 < (KStar.TotallyRealRoots.princ 2 a).index := by
    rw [KStar.TotallyRealRoots.princ, Subgroup.index_ker]
    exact Nat.card_pos
  have hr := Subgroup.relIndex_mul_index hle
  have hr1 : (KStar.TotallyRealRoots.princ 2 a).relIndex H ≠ 1 := fun h => hnot (Subgroup.relIndex_eq_one.mp h hu)
  have hr0 : (KStar.TotallyRealRoots.princ 2 a).relIndex H ≠ 0 := by
    intro h
    rw [h, zero_mul] at hr
    omega
  refine ⟨?_, ?_⟩
  · intro h
    rw [h, mul_zero] at hr
    omega
  · calc 2 * H.index ≤ (KStar.TotallyRealRoots.princ 2 a).relIndex H * H.index :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (KStar.TotallyRealRoots.princ 2 a).index := hr
      _ ≤ Nat.totient (2 ^ a) := hidx

theorem UpperTheory.V.Two.idxAdic :
    ∀ (H : Subgroup ℤ_[2]ˣ) (u : ℤ_[2]ˣ) (p c : ℕ), IsClosed (H : Set ℤ_[2]ˣ) → u ∈ H → (u : ℤ_[2]) = p → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → H.index ≠ 0 ∧ H.index ≤ c := by
  intro H u p c hH hu hp hpc
  rcases hpc with ⟨hp8, rfl⟩ | ⟨hp16, rfl⟩
  · have hk : p = 8 * (p / 8) + 3 := by omega
    generalize p / 8 = k at hk
    subst hk
    have e : ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 = 16 * (4 * (k : ℤ) ^ 2 + 3 * k) + 8 := by
      push_cast
      ring
    have d1 : (2 : ℤ) ^ 3 ∣ ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 4 * (k : ℤ) ^ 2 + 3 * k = m
      exact ⟨2 * m + 1, by ring⟩
    have d2 : ¬ (2 : ℤ) ^ (3 + 1) ∣ ((8 * k + 3 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 4 * (k : ℤ) ^ 2 + 3 * k = m
      rintro ⟨t, ht⟩
      norm_num at ht
      omega
    have d3 : ¬ (2 : ℤ) ^ 3 ∣ ((8 * k + 3 : ℕ) : ℤ) - 1 := by
      rintro ⟨t, ht⟩
      push_cast at ht
      norm_num at ht
      omega
    obtain ⟨h0, h⟩ := index_closed_dyadic_subgroup H u (8 * k + 3) 3 hH hu hp (by norm_num) d1 d2 d3
    refine ⟨h0, ?_⟩
    have ht : Nat.totient (2 ^ 3) = 4 := by decide
    omega
  · have hk : p = 16 * (p / 16) + 7 := by omega
    generalize p / 16 = k at hk
    subst hk
    have e : ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 = 32 * (8 * (k : ℤ) ^ 2 + 7 * k + 1) + 16 := by
      push_cast
      ring
    have d1 : (2 : ℤ) ^ 4 ∣ ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 8 * (k : ℤ) ^ 2 + 7 * k + 1 = m
      exact ⟨2 * m + 1, by ring⟩
    have d2 : ¬ (2 : ℤ) ^ (4 + 1) ∣ ((16 * k + 7 : ℕ) : ℤ) ^ 2 - 1 := by
      rw [e]
      generalize 8 * (k : ℤ) ^ 2 + 7 * k + 1 = m
      rintro ⟨t, ht⟩
      norm_num at ht
      omega
    have d3 : ¬ (2 : ℤ) ^ 4 ∣ ((16 * k + 7 : ℕ) : ℤ) - 1 := by
      rintro ⟨t, ht⟩
      push_cast at ht
      norm_num at ht
      omega
    obtain ⟨h0, h⟩ := index_closed_dyadic_subgroup H u (16 * k + 7) 4 hH hu hp (by norm_num) d1 d2 d3
    refine ⟨h0, ?_⟩
    have ht : Nat.totient (2 ^ 4) = 8 := by decide
    omega
end
