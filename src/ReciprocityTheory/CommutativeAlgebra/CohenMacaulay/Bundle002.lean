module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle001
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Unmixed
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Mathlib.RingTheory.KrullDimension.Module

@[expose] public section

section

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence

variable {R : Type*} [CommRing R] [IsLocalRing R]

private theorem height_le_length_of_mem_minimalPrimes [IsNoetherianRing R] (rs : List R) {p : Ideal R}
    (hp : p ∈ (Ideal.ofList rs).minimalPrimes) : p.height ≤ (rs.length : ℕ∞) := by
  classical
  have h1 := Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ p hp
  have hcard : Cardinal.mk {x | x ∈ rs} ≤ rs.length := by
    have : {x | x ∈ rs} = (rs.toFinset : Set R) := by ext; simp
    rw [this]
    calc Cardinal.mk (rs.toFinset : Set R) = (rs.toFinset.card : Cardinal) := Cardinal.mk_coe_finset
      _ ≤ rs.length := by exact_mod_cast List.toFinset_card_le rs
  have h2 : (Ideal.ofList rs).spanRank ≤ rs.length := by
    unfold Ideal.ofList
    exact (Submodule.spanRank_span_le_card _).trans hcard
  refine h1.trans ?_
  simpa using OrderHomClass.mono Cardinal.toENat h2

theorem grade_step_exists (h : IsCM R) {I : Ideal R} (hI : I ≠ ⊤) {r : ℕ}
    (hr : (r : ℕ∞) ≤ I.height) (rs : List R) (hlen : rs.length < r) (hrsI : ∀ x ∈ rs, x ∈ I)
    (reg : IsRegular R rs) :
    ∃ x ∈ I, IsSMulRegular (R ⧸ (Ideal.ofList rs • ⊤ : Submodule R R)) x := by
  haveI : IsNoetherianRing R := h.1
  have hIm : I ≤ maximalIdeal R := le_maximalIdeal hI
  have hCM := (isCM_iff_isCMMod.mp h).quotient_ofList (fun x hx => hIm (hrsI x hx)) reg
  have hJ : (Ideal.ofList rs • (⊤ : Submodule R R) : Ideal R) = Ideal.ofList rs := Ideal.mul_top _
  have hass : associatedPrimes R (R ⧸ (Ideal.ofList rs • ⊤ : Submodule R R)) =
      (Ideal.ofList rs).minimalPrimes := by
    rw [hCM.associatedPrimes_eq_minimalPrimes, Ideal.annihilator_quotient, hJ]
  have hfin := associatedPrimes.finite R (R ⧸ (Ideal.ofList rs • ⊤ : Submodule R R))
  have hnot : ¬ ((I : Set R) ⊆ ⋃ p ∈ (hfin.toFinset : Set (Ideal R)), (p : Set R)) := by
    intro hsub
    obtain ⟨p, hp, hIp⟩ := (Ideal.subset_union_prime (f := id) ⊥ ⊥
      (fun i hi _ _ => by
        rw [Set.Finite.mem_toFinset] at hi
        exact (IsAssociatedPrime.isPrime hi))).mp hsub
    rw [Set.Finite.mem_toFinset, hass] at hp
    have h1 := height_le_length_of_mem_minimalPrimes rs hp
    have h2 : I.height ≤ p.height := Ideal.height_mono hIp
    have h3 : (rs.length : ℕ∞) < r := by exact_mod_cast hlen
    exact absurd (hr.trans (h2.trans h1)) (not_le.mpr h3)
  obtain ⟨x, hxI, hx⟩ := Set.not_subset.mp hnot
  refine ⟨x, hxI, ?_⟩
  have hx' : x ∉ ⋃ p ∈ associatedPrimes R (R ⧸ (Ideal.ofList rs • ⊤ : Submodule R R)), (p : Set R) := by
    simpa using hx
  rw [biUnion_associatedPrimes_eq_compl_regular] at hx'
  simpa using hx'

private theorem isRegular_of_isWeaklyRegular_of_mem_ne_top {I : Ideal R} (hI : I ≠ ⊤) (rs : List R)
    (hrsI : ∀ x ∈ rs, x ∈ I) (w : IsWeaklyRegular R rs) : IsRegular R rs := by
  refine ⟨w, ?_⟩
  intro heq
  apply hI
  rw [eq_top_iff]
  have h1 : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs := Ideal.mul_top _
  have h2 : Ideal.ofList rs ≤ I := Ideal.span_le.mpr (fun y hy => hrsI y hy)
  calc (⊤ : Ideal R) = (Ideal.ofList rs • (⊤ : Submodule R R)) := heq
    _ = Ideal.ofList rs := h1
    _ ≤ I := h2

theorem IsCM.exists_isRegular_of_le_height (h : IsCM R) {I : Ideal R} (hI : I ≠ ⊤) {r : ℕ}
    (hr : (r : ℕ∞) ≤ I.height) :
    ∃ rs : List R, rs.length = r ∧ (∀ x ∈ rs, x ∈ I) ∧ IsRegular R rs := by
  induction r with
  | zero =>
    exact ⟨[], rfl, by simp, isRegular_of_isWeaklyRegular_of_mem_ne_top hI [] (by simp) (by simp)⟩
  | succ n ih =>
    obtain ⟨rs, hlen, hrsI, reg⟩ := ih ((Nat.cast_le.mpr (Nat.le_succ n)).trans hr)
    obtain ⟨x, hxI, hx⟩ := grade_step_exists h hI hr rs (by omega) hrsI reg
    have hall : ∀ y ∈ rs ++ [x], y ∈ I := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hrsI y hy
      · rw [List.mem_singleton.mp hy]; exact hxI
    refine ⟨rs ++ [x], by simp [hlen], hall, isRegular_of_isWeaklyRegular_of_mem_ne_top hI _ hall ?_⟩
    exact (isWeaklyRegular_append_iff R rs [x]).mpr
      ⟨reg.1, (isWeaklyRegular_singleton_iff _ x).mpr hx⟩

end ReciprocityTheory.CA
end

section

namespace ReciprocityTheory.CA

theorem isCM_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsCM R :=
  GlobalTheory.isCM_of_isRegularLocalRing R

end ReciprocityTheory.CA
end

section

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence Pointwise

variable {R : Type*} [CommRing R] [IsLocalRing R]

private theorem smul_top_eq_self' (I : Ideal R) : (I • (⊤ : Submodule R R)) = I := by
  exact Ideal.mul_top I

private theorem span_singleton_eq_smul_top' (x : R) :
    (x • (⊤ : Submodule R R)) = Ideal.span {x} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_top_eq_self']

private theorem isSMulRegular_of_mem_nonZeroDivisors' {x : R} (reg : x ∈ nonZeroDivisors R) :
    IsSMulRegular R x := by
  intro a b hab
  have h0 : (a - b) * x = 0 := by
    simp only [smul_eq_mul] at hab
    rw [sub_mul, mul_comm a, mul_comm b, hab, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp reg).2 _ h0)

private noncomputable def quotSMulTopEquivQuot' (x : R) :
    QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
  Submodule.quotEquivOfEq _ _ (span_singleton_eq_smul_top' x)

theorem isCM_of_quotient_span_singleton [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (reg : x ∈ nonZeroDivisors R) [IsLocalRing (R ⧸ Ideal.span {x})]
    (h : IsCM (R ⧸ Ideal.span {x})) : IsCM R := by
  exact isCM_iff_isCMMod.mpr (IsCMMod.of_quotSMulTop hx (isSMulRegular_of_mem_nonZeroDivisors' reg)
    ((isCMMod_congr (quotSMulTopEquivQuot' x)).mpr ((isCM_quotient_iff _).mp h)))

theorem IsCM.quotient_ofList (h : IsCM R) {rs : List R} (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (reg : IsRegular R rs) [IsLocalRing (R ⧸ Ideal.ofList rs)] :
    IsCM (R ⧸ Ideal.ofList rs) := by
  haveI : IsNoetherianRing R := h.1
  have h1 := (isCM_iff_isCMMod.mp h).quotient_ofList hrs reg
  exact (isCM_quotient_iff _).mpr
    ((isCMMod_congr (Submodule.quotEquivOfEq _ _ (smul_top_eq_self' _))).mp h1)

theorem IsCM.isRegular_of_isArtinianRing_quotient (h : IsCM R) (xs : List R)
    (hxs : ∀ r ∈ xs, r ∈ maximalIdeal R) (hlen : (xs.length : WithBot ℕ∞) = ringKrullDim R)
    (hart : IsArtinianRing (R ⧸ Ideal.ofList xs)) : IsRegular R xs := by
  apply (isCM_iff_isCMMod.mp h).isRegular_of_supportDim_quotient_le_zero xs hxs
  · rw [Module.supportDim_self_eq_ringKrullDim]; exact hlen
  · rw [Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEq _ _ (smul_top_eq_self' _)),
      Module.supportDim_quotient_eq_ringKrullDim]
    exact Ring.krullDimLE_iff.mp inferInstance

end ReciprocityTheory.CA
end
