module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Field.IsField
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Trace.Defs
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
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

section

noncomputable section

open ValuativeRel IsLocalRing

namespace PI.LocDualGen.FpU

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]

theorem t2 : T2Space K := by
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed, ← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hv : valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨Units.mk0 _ hv, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ h0
  have hz' : valuation K z < valuation K x := hz
  have h0' : x + z = 0 := h0
  have : z = -x := by linear_combination h0'
  rw [this, Valuation.map_neg] at hz'
  exact lt_irrefl _ hz'

theorem isClosed_O : IsClosed ((𝒪[K] : Set K)) := by
  haveI : T2Space K := t2 (K := K)
  exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).isClosed

theorem iota_mem (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    algebraMap ℚ_[l] K (a : ℚ_[l]) ∈ 𝒪[K] := by
  have hcl : IsClosed {a : ℤ_[l] | algebraMap ℚ_[l] K (a : ℚ_[l]) ∈ 𝒪[K]} :=
    (isClosed_O (K := K)).preimage (hcont.comp continuous_subtype_val)
  refine PadicInt.denseRange_intCast.induction_on a hcl ?_
  intro n
  simp only [Set.mem_setOf_eq, PadicInt.coe_intCast, map_intCast]
  exact intCast_mem _ n

def iotaR (hcont : Continuous (algebraMap ℚ_[l] K)) : ℤ_[l] →+* 𝒪[K] :=
  ((algebraMap ℚ_[l] K).comp (PadicInt.Coe.ringHom (p := l))).codRestrict 𝒪[K]
    (fun a => iota_mem K l hcont a)

theorem iotaR_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    ((iotaR K l hcont a : 𝒪[K]) : K) = algebraMap ℚ_[l] K (a : ℚ_[l]) := rfl

theorem charP_res (huni : Irreducible ((l : ℕ) : 𝒪[K])) : CharP 𝓀[K] l := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime), ← map_natCast (residue 𝒪[K]) l,
    IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 huni.not_isUnit)

theorem repr_sum {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (c : ι → R) (i : ι) : b.repr (∑ j, c j • b j) i = c i := by
  exact congrFun (b.repr_sum_self c) i

section Res

variable [CharP 𝓀[K] l]

abbrev algRes : Algebra (ZMod l) 𝓀[K] := ZMod.algebra _ l

attribute [local instance] algRes

theorem res_iotaR (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    residue 𝒪[K] (iotaR K l hcont a) = algebraMap (ZMod l) 𝓀[K] (PadicInt.toZMod a) := by
  obtain ⟨-, h⟩ := PadicInt.zmodRepr_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  have ha : a = ((a.zmodRepr : ℕ) : ℤ_[l]) + b * (l : ℤ_[l]) := by rw [hb]; ring
  rw [ha]
  simp [map_natCast, CharP.cast_eq_zero]

abbrev fdim : ℕ := Module.finrank (ZMod l) 𝓀[K]

def bb : Module.Basis (Fin (fdim K l)) (ZMod l) 𝓀[K] := Module.finBasis (ZMod l) 𝓀[K]

def blift (i : Fin (fdim K l)) : 𝒪[K] := (residue_surjective (bb K l i)).choose

theorem res_blift (i : Fin (fdim K l)) : residue 𝒪[K] (blift K l i) = bb K l i := by
  exact (residue_surjective (bb K l i)).choose_spec

def Phi (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) : 𝒪[K] :=
  ∑ i, iotaR K l hcont (c i) * blift K l i

theorem Phi_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) :
    ((Phi K l hcont c : 𝒪[K]) : K) = ∑ i, algebraMap ℚ_[l] K (c i : ℚ_[l]) * (blift K l i : K) := by
  unfold Phi
  push_cast
  simp only [iotaR_coe]

theorem Phi_add (hcont : Continuous (algebraMap ℚ_[l] K)) (c c' : Fin (fdim K l) → ℤ_[l]) (s : ℤ_[l]) :
    Phi K l hcont (c + s • c') = Phi K l hcont c + iotaR K l hcont s * Phi K l hcont c' := by
  simp only [Phi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem res_Phi (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) :
    residue 𝒪[K] (Phi K l hcont c) = ∑ i, PadicInt.toZMod (c i) • bb K l i := by

  simp only [Phi, map_sum, map_mul, res_iotaR, res_blift, Algebra.smul_def]

theorem one_step (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ∃ c, ∃ y : 𝒪[K], x = Phi K l hcont c + (l : 𝒪[K]) * y := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  set r := (bb K l).repr (residue 𝒪[K] x) with hr
  refine ?_
  have hc : residue 𝒪[K] (Phi K l hcont (fun i => ((r i).val : ℤ_[l]))) = residue 𝒪[K] x := by
    rw [res_Phi]
    have h1 : ∀ i, PadicInt.toZMod (((r i).val : ℕ) : ℤ_[l]) = r i := fun i => by
      rw [map_natCast, ZMod.natCast_zmod_val]
    simp_rw [h1]
    exact (bb K l).sum_repr (residue 𝒪[K] x)
  have hm : x - Phi K l hcont (fun i => ((r i).val : ℤ_[l])) ∈ maximalIdeal 𝒪[K] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hc, sub_self]
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 huni,
    Ideal.mem_span_singleton'] at hm
  obtain ⟨y, hy⟩ := hm
  exact ⟨_, y, by rw [mul_comm, hy]; ring⟩

theorem n_step (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (j : ℕ) (x : 𝒪[K]) : ∃ c, ∃ y : 𝒪[K], x = Phi K l hcont c + (l : 𝒪[K]) ^ j * y := by
  induction j with
  | zero => exact ⟨0, x, by simp [Phi]⟩
  | succ j ih =>
    obtain ⟨c, y, hxy⟩ := ih
    obtain ⟨c', y', hy⟩ := one_step K l hcont huni y
    refine ⟨c + ((l : ℤ_[l]) ^ j) • c', y', ?_⟩
    rw [Phi_add, hxy, hy]
    simp only [map_pow, map_natCast]
    ring

theorem span (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ∃ c, x = Phi K l hcont c := by
  haveI : T2Space K := t2 (K := K)
  choose c y hxy using fun j => n_step K l hcont huni j x
  let F : (Fin (fdim K l) → ℤ_[l]) → K := fun c => ((Phi K l hcont c : 𝒪[K]) : K)
  have hF : Continuous F := by
    have : F = fun c => ∑ i, algebraMap ℚ_[l] K (c i : ℚ_[l]) * (blift K l i : K) := by
      funext c
      exact Phi_coe K l hcont c
    rw [this]
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (hcont.comp (continuous_subtype_val.comp (continuous_apply i))).mul continuous_const
  have hcl : IsClosed (Set.range F) := (isCompact_range hF).isClosed
  have h0 : Filter.Tendsto (fun j => (l : K) ^ j * (y j : K)) Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun j => (l : ℚ_[l]) ^ j) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    have hp' : Filter.Tendsto (fun j => (l : K) ^ j) Filter.atTop (nhds 0) := by
      have := (hcont.tendsto 0).comp hp
      simpa [Function.comp_def, map_pow, map_natCast] using this
    rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff] at hp' ⊢
    intro γ _
    filter_upwards [hp' γ trivial] with j hj
    have hj' : valuation K ((l : K) ^ j) < γ := hj
    show valuation K ((l : K) ^ j * (y j : K)) < γ
    rw [map_mul]
    have hy1 : valuation K (y j : K) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (y j).2
    calc valuation K ((l : K) ^ j) * valuation K (y j : K) ≤ valuation K ((l : K) ^ j) * 1 :=
          by gcongr
      _ = valuation K ((l : K) ^ j) := mul_one _
      _ < _ := hj'
  have heq : (fun j => F (c j)) = fun j => (x : K) - (l : K) ^ j * (y j : K) := by
    funext j
    have := congrArg (fun z : 𝒪[K] => (z : K)) (hxy j)
    push_cast at this
    simp only [F]
    rw [this]
    ring
  have hlim : Filter.Tendsto (fun j => F (c j)) Filter.atTop (nhds (x : K)) := by
    rw [heq]
    simpa using (tendsto_const_nhds (x := (x : K))).sub h0
  obtain ⟨c0, hc0⟩ := hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall fun j => ⟨c j, rfl⟩)
  exact ⟨c0, Subtype.ext hc0.symm⟩

end Res

end PI.LocDualGen.FpU
end
end

section

noncomputable section
open Module

namespace PI.LocDualGen.EpC

variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]

private theorem nontrivial_of_finrank_eq_two (hr : finrank K L = 2) : Nontrivial L := by
  rcases subsingleton_or_nontrivial L with h | h
  · rw [Module.finrank_zero_of_subsingleton] at hr
    exact absurd hr (by norm_num)
  · exact h

private theorem exists_not_mem_range_algebraMap_of_finrank_eq_two (hr : finrank K L = 2) :
    ∃ x : L, x ∉ Set.range (algebraMap K L) := by
  by_contra h
  push Not at h
  have hsurj : LinearMap.range (Algebra.linearMap K L) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨a, ha⟩ := h y
    exact ⟨a, ha⟩
  have h1 := LinearMap.finrank_range_le (Algebra.linearMap K L)
  rw [hsurj, finrank_top, Module.finrank_self, hr] at h1
  omega

private theorem exists_eq_add_mul_of_finrank_eq_two' (hr : finrank K L = 2) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) (y : L) :
    ∃ a c : K, algebraMap K L a + algebraMap K L c * x = y := by
  have := nontrivial_of_finrank_eq_two hr
  have hli : LinearIndependent K ![(1 : L), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      refine ⟨?_, rfl⟩
      have h0 : algebraMap K L s = 0 := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact hst
      exact (algebraMap K L).injective (by rw [h0, map_zero])
    · exfalso
      apply hx
      refine ⟨-(s / t), ?_⟩
      have h2 : t • x = -(s • (1 : L)) := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
        exact hst
      have h3 : x = t⁻¹ • (t • x) := by
        rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [Algebra.algebraMap_eq_smul_one, h3, h2, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hcard : Fintype.card (Fin 2) = finrank K L := by
    rw [hr, Fintype.card_fin]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = x := by simp [b]
  have hy := b.sum_repr y
  rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one] at hy
  exact ⟨b.repr y 0, b.repr y 1, hy⟩

theorem dichotomy (hr : finrank K L = 2) (hred : IsReduced L) :
    IsField L ∨ ∃ e : L, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  have := nontrivial_of_finrank_eq_two hr
  obtain ⟨x, hx⟩ := exists_not_mem_range_algebraMap_of_finrank_eq_two hr
  have hrep := exists_eq_add_mul_of_finrank_eq_two' hr hx
  obtain ⟨p, q, hpq0⟩ := hrep (x ^ 2)
  have hpq : x ^ 2 = algebraMap K L p + algebraMap K L q * x := hpq0.symm
  by_cases hroot : ∃ r : K, r ^ 2 = p + q * r
  · obtain ⟨r, hr2⟩ := hroot
    have hfac : (x - algebraMap K L r) * (x - algebraMap K L (q - r)) = 0 := by
      have h' : algebraMap K L (r ^ 2) = algebraMap K L (p + q * r) := by rw [hr2]
      simp only [map_add (f := _), map_mul, map_pow, map_sub] at h' ⊢
      linear_combination hpq - h'
    by_cases hrs : r = q - r
    · exfalso
      have hsq : (x - algebraMap K L r) ^ 2 = 0 := by
        have h' := hfac
        rw [← hrs] at h'
        rw [sq]
        exact h'
      have hz : x - algebraMap K L r = 0 := hred.eq_zero _ ⟨2, hsq⟩
      exact hx ⟨r, (sub_eq_zero.mp hz).symm⟩
    · right
      have hd : q - r - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
      have hsq : (x - algebraMap K L r) * (x - algebraMap K L r) =
          algebraMap K L (q - r - r) * (x - algebraMap K L r) := by
        have h' := hfac
        simp only [map_sub] at h' ⊢
        linear_combination h'
      have hu : algebraMap K L (q - r - r)⁻¹ * algebraMap K L (q - r - r) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hd, map_one]
      have hback : x - algebraMap K L r = algebraMap K L (q - r - r) *
          (algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r)) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd, map_one, one_mul]
      refine ⟨algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r), ?_, ?_, ?_⟩
      · show _ * _ = _
        linear_combination (algebraMap K L (q - r - r)⁻¹) ^ 2 * hsq +
          algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r) * hu
      · intro he
        rw [he, mul_zero, sub_eq_zero] at hback
        exact hx ⟨r, hback.symm⟩
      · intro he
        rw [he, mul_one] at hback
        apply hx
        refine ⟨q - r, ?_⟩
        simp only [map_sub] at hback ⊢
        linear_combination -hback
  · push Not at hroot
    left
    refine ⟨⟨0, 1, zero_ne_one⟩, fun a b => mul_comm a b, ?_⟩
    intro y hy
    obtain ⟨a, c, rfl⟩ := hrep y
    have hN : a * a + a * c * q - c ^ 2 * p ≠ 0 := by
      intro h0
      by_cases hc : c = 0
      · subst hc
        apply hy
        have ha : a = 0 := by simpa using h0
        simp [ha]
      · apply hroot (-a / c)
        have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
        linear_combination (c⁻¹) ^ 2 * h0 + (p * (1 + c * c⁻¹) - q * a * c⁻¹) * hci
    have hprod : (algebraMap K L a + algebraMap K L c * x) *
        (algebraMap K L (a + c * q) - algebraMap K L c * x) =
        algebraMap K L (a * a + a * c * q - c ^ 2 * p) := by
      simp only [map_add (f := _), map_mul, map_sub, map_pow]
      linear_combination (-(algebraMap K L c) ^ 2) * hpq
    refine ⟨algebraMap K L (a * a + a * c * q - c ^ 2 * p)⁻¹ *
      (algebraMap K L (a + c * q) - algebraMap K L c * x), ?_⟩
    rw [mul_left_comm, hprod, ← map_mul, inv_mul_cancel₀ hN, map_one]

end PI.LocDualGen.EpC
end
end

section

noncomputable section

open ValuativeRel

namespace PI.LocDualGen.W

def PsiKer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (t : ℚ_[l]) (a : ℚ), (∃ n : ℕ, a.den = l ^ n) → ‖t - (a : ℚ_[l])‖ ≤ 1 →
    (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 ↔ ‖t‖ ≤ 1)

def FpDual : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (l : ℕ) [Fact l.Prime]
    [Algebra ℚ_[l] K], IsNonarchimedeanLocalField K → CharZero K →
    Continuous (algebraMap ℚ_[l] K) → FiniteDimensional ℚ_[l] K →
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[K]

def FpDualUnram : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (l : ℕ) [Fact l.Prime]
    [Algebra ℚ_[l] K], IsNonarchimedeanLocalField K → CharZero K →
    Continuous (algebraMap ℚ_[l] K) → FiniteDimensional ℚ_[l] K →
    Irreducible ((l : ℕ) : 𝒪[K]) →
    ∀ a : K, (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K))‖ ≤ 1) ↔ a ∈ 𝒪[K]

def EpSelfDual : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] (L : Type) [CommRing L]
    [Algebra K L], IsNonarchimedeanLocalField K → CharZero K →
    Module.Free K L → Module.finrank K L = 2 → IsReduced L →
    ∀ O : Subring L, (∀ x : L, x ∈ O ↔ IsIntegral 𝒪[K] x) →
    (∀ ϖ : 𝒪[K], Irreducible ϖ → ∀ x ∈ O,
      x * x ∈ Submodule.span O {algebraMap K L (ϖ : K)} →
        x ∈ Submodule.span O {algebraMap K L (ϖ : K)}) →
    ∀ x : L, (∀ y ∈ O, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ O

end PI.LocDualGen.W
end
end
