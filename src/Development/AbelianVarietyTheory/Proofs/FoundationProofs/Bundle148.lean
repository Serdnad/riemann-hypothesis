module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle136
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle141
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle143
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle098
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.GaloisCohomology.StatementLoc

@[expose] public section

section

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

open Polynomial Classical in
private lemma exists_le_degType_sum_eq_of_hasDiv {g : ℕ} [Fact g.Prime] {N a : ℕ}
    {f : (ZMod g)[X]} (hf : f ∈ _root_.GlobalTheory.BadShare.sqSet g N) (hd : _root_.GlobalTheory.BadShare.HasDiv g a f) :
    ∃ ν ≤ _root_.GlobalTheory.BadShare.degType g f, ν.sum = a := by
  unfold _root_.GlobalTheory.BadShare.HasDiv at hd
  obtain ⟨h, hdvd, hdeg⟩ := hd
  obtain ⟨hmon, -, hsq, hc0⟩ := (_root_.GlobalTheory.BadShare.mem_sqSet).mp hf
  have hf0 : f ≠ 0 := hmon.ne_zero
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hf0 (zero_dvd_iff.mp hdvd)
  have hlc : h.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hh0
  obtain ⟨u, hu⟩ : ∃ u : (ZMod g)[X], u = h * C h.leadingCoeff⁻¹ := ⟨_, rfl⟩
  have hudvd : u ∣ f := by
    refine dvd_trans ⟨C h.leadingCoeff, ?_⟩ hdvd
    rw [hu, mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
  have humon : u.Monic := hu ▸ monic_mul_leadingCoeff_inv hh0
  have hudeg : u.natDegree = a := by rw [hu, natDegree_mul_C (inv_ne_zero hlc), hdeg]
  have husq : Squarefree u := hsq.squarefree_of_dvd hudvd
  have huc0 : u.coeff 0 ≠ 0 := by
    intro h0
    apply hc0
    obtain ⟨k, hk⟩ := hudvd
    rw [hk, mul_coeff_zero, h0, zero_mul]
  have hmem : u ∈ _root_.GlobalTheory.BadShare.sqSet g a :=
    (_root_.GlobalTheory.BadShare.mem_sqSet).mpr ⟨humon, hudeg, husq, huc0⟩
  obtain ⟨k, hk⟩ := hudvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact hf0 hk
  refine ⟨_root_.GlobalTheory.BadShare.degType g u, ?_,
    ((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).1 a u hmem).2.2.1⟩
  rw [hk, ((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).2.1 u k humon.ne_zero hk0).1]
  exact Multiset.le_add_right _ _

open Polynomial Classical in
private lemma exists_subset_map_eq_of_le_map {β γ : Type} (f : β → γ) (s : Finset β) :
    ∀ ν : Multiset γ, ν ≤ s.val.map f → ∃ t ⊆ s, t.val.map f = ν := by
  induction s using Finset.cons_induction with
  | empty =>
    intro ν h
    rw [Finset.empty_val, Multiset.map_zero, Multiset.le_zero] at h
    exact ⟨∅, Finset.empty_subset _, by rw [h]; rfl⟩
  | cons a s ha ih =>
    intro ν h
    rw [Finset.cons_val, Multiset.map_cons] at h
    by_cases hm : f a ∈ ν
    · obtain ⟨t, ht, htν⟩ := ih (ν.erase (f a))
        (by rw [← Multiset.cons_le_cons_iff (f a), Multiset.cons_erase hm]; exact h)
      refine ⟨Finset.cons a t (fun hat => ha (ht hat)), fun x hx => ?_, ?_⟩
      · rw [Finset.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (ht hx)
      · rw [Finset.cons_val, Multiset.map_cons, htν, Multiset.cons_erase hm]
    · obtain ⟨t, ht, htν⟩ := ih ν ((Multiset.le_cons_of_notMem hm).mp h)
      exact ⟨t, fun x hx => Finset.mem_cons.mpr (Or.inr (ht hx)), htν⟩

open Polynomial Classical in
private lemma exists_invariant_finset_card_of_le_cycleType {n : ℕ} (σ : Equiv.Perm (Fin n)) (ν : Multiset ℕ)
    (hν : ν ≤ σ.partition.parts) : ∃ S : Finset (Fin n), S.card = ν.sum ∧ S.map σ.toEmbedding = S := by
  rw [Equiv.Perm.parts_partition] at hν
  have h1 : ν.filter (2 ≤ ·) ≤ σ.cycleType := by
    refine (Multiset.filter_le_filter _ hν).trans (le_of_eq ?_)
    rw [Multiset.filter_add, Multiset.filter_eq_self.mpr (fun x hx => Equiv.Perm.two_le_of_mem_cycleType hx),
      Multiset.filter_eq_nil.mpr (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; norm_num), add_zero]
  have h2 : ν.filter (fun x => ¬ 2 ≤ x) ≤ Multiset.replicate (Fintype.card (Fin n) - σ.support.card) 1 := by
    refine (Multiset.filter_le_filter _ hν).trans (le_of_eq ?_)
    rw [Multiset.filter_add, Multiset.filter_eq_nil.mpr (fun x hx => not_not.mpr (Equiv.Perm.two_le_of_mem_cycleType hx)),
      Multiset.filter_eq_self.mpr (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; norm_num), zero_add]
  have hν2 : ν.filter (fun x => ¬ 2 ≤ x) = Multiset.replicate (Multiset.card (ν.filter (fun x => ¬ 2 ≤ x))) 1 :=
    Multiset.eq_replicate_of_mem fun b hb => Multiset.eq_of_mem_replicate (Multiset.mem_of_le h2 hb)
  have hk := Multiset.card_le_card h2
  rw [Multiset.card_replicate] at hk
  rw [Equiv.Perm.cycleType_def] at h1
  obtain ⟨C, hC, hCν⟩ := exists_subset_map_eq_of_le_map _ _ _ h1
  have hcompl : (σ.support)ᶜ.card = Fintype.card (Fin n) - σ.support.card := Finset.card_compl _
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (hcompl ▸ hk)
  have hCσ : ∀ c ∈ C, ∀ x ∈ c.support, σ x = c x := fun c hc x hx =>
    ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp (hC hc)).2 x hx).symm
  have hS1 : ∀ x ∈ C.biUnion (fun c => c.support), σ x ∈ C.biUnion (fun c => c.support) ∧ σ x ≠ x := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
    rw [hCσ c hc x hxc]
    exact ⟨Finset.mem_biUnion.mpr ⟨c, hc, Equiv.Perm.apply_mem_support.mpr hxc⟩, Equiv.Perm.mem_support.mp hxc⟩
  have hT' : ∀ x ∈ T, σ x = x := fun x hx => Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp (hT hx))
  have hdisj : Disjoint (C.biUnion (fun c => c.support)) T := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    exact (hS1 x hx).2 (hT' x hxT)
  have hcard1 : (C.biUnion (fun c => c.support)).card = (ν.filter (2 ≤ ·)).sum := by
    rw [Finset.card_biUnion, ← hCν, Finset.sum_eq_multiset_sum]
    · rfl
    · intro c hc e he hce
      exact (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ (hC hc) (hC he) hce).disjoint_support
  refine ⟨C.biUnion (fun c => c.support) ∪ T, ?_, ?_⟩
  · have hs2 : (ν.filter (fun x => ¬ 2 ≤ x)).sum = Multiset.card (ν.filter (fun x => ¬ 2 ≤ x)) := by
      conv_lhs => rw [hν2]
      rw [Multiset.sum_replicate, smul_eq_mul, mul_one]
    rw [Finset.card_union_of_disjoint hdisj, hcard1, hTc, ← hs2, ← Multiset.sum_add, Multiset.filter_add_not]
  · refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) (by rw [Finset.card_map])
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (hS1 x hx).1
    · simp only [Equiv.toEmbedding_apply]
      rw [hT' x hx]
      exact Finset.mem_union_right _ hx


open Polynomial Classical in
theorem _root_.GlobalTheory.BadShare.mass_hasDiv_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N a : ℕ, 0 < a → a < N →
    _root_.GlobalTheory.BadShare.mass g N (_root_.GlobalTheory.BadShare.HasDiv g a) ≤ 7 / 8 := by
  intro g _ N a ha haN
  have hmono := (_root_.GlobalTheory.BadShare.mass_union_bounds g N).1
  refine (hmono _ (fun f => (fun μ : Multiset ℕ => ∃ ν ≤ μ, ν.sum = a) (_root_.GlobalTheory.BadShare.degType g f))
    (fun f hf hd => exists_le_degType_sum_eq_of_hasDiv hf hd)).trans ?_
  refine (_root_.GlobalTheory.BadShare.mass_degType_le_cycleType g N (fun μ => ∃ ν ≤ μ, ν.sum = a)).trans ?_
  have h := _root_.GlobalTheory.StableSubset.card_exists_stable_subset_le N a ha haN
  have hc := Finset.card_le_card (s := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ ν ≤ σ.partition.parts, ν.sum = a)
    (t := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ A : Finset (Fin N), A.card = a ∧ A.map σ.toEmbedding = A)
    (fun σ hσ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      obtain ⟨ν, hν, rfl⟩ := hσ
      exact exists_invariant_finset_card_of_le_cycleType σ ν hν)
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [div_le_iff₀ hf]
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  have hc' := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at h' hc'
  linarith

end GlobalTheory.BadShare
end

section

open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.Square

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem stepRatio_vw_pow (w : Pl K) {x : K} (hx : x ≠ 0) (c : ℕ) : vw w (x ^ c) = c * vw w x := by
  induction c with
  | zero =>
    have h := Formalism.DivisionValues.ValuationRepresentative.vw_mul w (1 : K) 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    rw [pow_zero]
    push_cast
    omega
  | succ c ih =>
    rw [pow_succ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero c hx) hx, ih]
    push_cast
    ring

theorem stepRatio_vw_of_dvd (w : Pl K) {q c : ℕ} (hq : 0 < q) {g : 𝓞 K} (hg : g ∣ (q : 𝓞 K) ^ c) :
    (g : K) ≠ 0 ∧ 0 ≤ vw w (g : K) ∧ vw w (g : K) ≤ c * vw w (q : K) := by
  obtain ⟨b, hb⟩ := hg
  have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have h : (q : K) ^ c = (g : K) * (b : K) := by
    have := congrArg (fun x : 𝓞 K => (x : K)) hb
    simpa using this
  have hne : (g : K) * (b : K) ≠ 0 := h ▸ pow_ne_zero c hq0
  have hg0 := left_ne_zero_of_mul hne
  have hb0 := right_ne_zero_of_mul hne
  refine ⟨hg0, Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w g, ?_⟩
  rw [← stepRatio_vw_pow w hq0, h, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hg0 hb0]
  have := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w b
  omega

theorem stepRatio_abs_vw_prod (w : Pl K) {T : Type} (S : Finset T) (f : T → K) (r : T → ℝ)
    (h : ∀ v ∈ S, f v ≠ 0 ∧ |(vw w (f v) : ℝ)| ≤ r v) :
    |(vw w (∏ v ∈ S, f v) : ℝ)| ≤ ∑ v ∈ S, r v := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := stepRatio_vw_pow w (one_ne_zero : (1 : K) ≠ 0) 0
    rw [pow_zero, Nat.cast_zero, zero_mul] at this
    rw [Finset.prod_empty, Finset.sum_empty, this]
    simp
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self a S)
    have h2 := fun v hv => h v (Finset.mem_insert_of_mem hv)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h1.1 (Finset.prod_ne_zero_iff.2 fun v hv => (h2 v hv).1)]
    push_cast
    exact (abs_add_le _ _).trans (add_le_add h1.2 (ih h2))

theorem stepRatio_vw_bound : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (w : Pl K) (Qn : ℕ),
    (Qn : 𝓞 K) ∉ w.asIdeal → ∀ (T : Type) (S0 : Finset T) (cc qq : T → ℕ), (∀ v ∈ S0, 0 < qq v) → ∀ u1 u0 : ℂ,
    StepRatio σ₀ Qn S0 cc qq u1 u0 → ∃ t : K, t ≠ 0 ∧ u1 = σ₀ t * u0 ∧
      |(vw w t : ℝ)| ≤ 2 * ∑ v ∈ S0, (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by
  intro K _ _ _ σ₀ w Qn hQ T S0 cc qq hq u1 u0 h
  obtain ⟨b, g, g', hb, hg, hu⟩ := h
  have vz : ∀ {a : 𝓞 K}, a ∉ w.asIdeal → vw w (a : K) = 0 := by
    intro a ha
    classical
    have ha0 : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
      rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      rintro rfl
      exact ha w.asIdeal.zero_mem
    unfold vw
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ ha0]
    by_contra h
    have h' : (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {a})).factors ≠ 0 := by
      intro h0
      exact h (by rw [h0]; rfl)
    exact ha (Ideal.dvd_span_singleton.1 ((Associates.count_ne_zero_iff_dvd ha0 w.irreducible).1 h'))
  have ⟨hb0, hbv⟩ : b ≠ 0 ∧ vw w b = 0 := by
    obtain ⟨a, k, k', ⟨d, hd⟩, he⟩ := hb
    have hpow : ∀ j : ℕ, (Qn : 𝓞 K) ^ j ∉ w.asIdeal :=
      fun j hj => hQ (w.isPrime.mem_of_pow_mem j hj)
    have ha : a ∉ w.asIdeal := fun h => hpow k' (hd ▸ w.asIdeal.mul_mem_right d h)
    have ha0 : (a : K) ≠ 0 := by
      intro h
      have : a = 0 := by exact_mod_cast h
      exact ha (this ▸ w.asIdeal.zero_mem)
    have hb0 : b ≠ 0 := by rintro rfl; rw [zero_mul] at he; exact ha0 he.symm
    have hk0 : (Qn : K) ^ k ≠ 0 := by intro h; rw [h, mul_zero] at he; exact ha0 he.symm
    refine ⟨hb0, ?_⟩
    have h1 := Formalism.DivisionValues.ValuationRepresentative.vw_mul w b _ hb0 hk0
    have h2 := vz ha
    have h3 := vz (hpow k)
    have h4 : ((((Qn : 𝓞 K) ^ k : 𝓞 K)) : K) = (Qn : K) ^ k := by simp
    rw [h4] at h3
    rw [he, h2, h3] at h1
    omega
  have key : ∀ v ∈ S0, (g v : K) / (g' v : K) ≠ 0 ∧
      |(vw w ((g v : K) / (g' v : K)) : ℝ)| ≤ 2 * ((cc v : ℝ) * (vw w (qq v : K) : ℝ)) := by
    intro v hv
    obtain ⟨a0, a1, a2⟩ := stepRatio_vw_of_dvd w (hq v hv) (hg v hv).1
    obtain ⟨b0, b1, b2⟩ := stepRatio_vw_of_dvd w (hq v hv) (hg v hv).2
    refine ⟨div_ne_zero a0 b0, ?_⟩
    rw [div_eq_mul_inv, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ a0 (inv_ne_zero b0), Formalism.DivisionValues.ValuationRepresentative.vw_inv]
    have a1' : (0 : ℝ) ≤ (vw w (g v : K) : ℝ) := by exact_mod_cast a1
    have a2' : (vw w (g v : K) : ℝ) ≤ (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by exact_mod_cast a2
    have b1' : (0 : ℝ) ≤ (vw w (g' v : K) : ℝ) := by exact_mod_cast b1
    have b2' : (vw w (g' v : K) : ℝ) ≤ (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by exact_mod_cast b2
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have hp : ∏ v ∈ S0, (g v : K) / (g' v : K) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v hv => (key v hv).1
  refine ⟨_, mul_ne_zero hb0 hp, hu, ?_⟩
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hb0 hp, hbv, zero_add, Finset.mul_sum]
  exact stepRatio_abs_vw_prod w S0 _ _ key

end GlobalTheory.Square
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog Polynomial

noncomputable section
namespace GlobalTheory.LevDer

theorem int_div_of_mk {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω] [CharZero Ω]
    (m : ℕ) (a : integralClosure (O0 p) Ω)
    (ha : Ideal.Quotient.mk (Ideal.span {((p : integralClosure (O0 p) Ω)) ^ m}) a = 0) :
    IsInt (p := p) ((a : Ω) / (p : Ω) ^ m) := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, rfl⟩ := ha
  have hp : (p : Ω) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  refine int_congr c.2 ?_
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
  field_simp

theorem natCast_eq_pow {Ω : Type} [Field Ω] (N p k : ℕ) (h : N = p ^ (k + 1)) :
    (N : Ω) = (p : Ω) ^ (k + 1) := by
  subst h; push_cast; rfl


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem exists_levDer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m →
    ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq := by
  intro p _ Ω _ _ hC T m hm
  haveI : CharZero Ω := Basic.charZero_of_isClo hC
  obtain ⟨ι, hι⟩ := Basic.exists_isEmb T m
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hC T m hm ι hι
  have hιA : ∀ z, ι z ∈ integralClosure (O0 p) Ω := fun z =>
    Lev_int T m _ (hrange ▸ AlgHom.mem_range_self ι z)
  let ιA : On p m →ₐ[O0 p] integralClosure (O0 p) Ω := ι.codRestrict _ hιA
  have hιAv : ∀ z, ((ιA z : integralClosure (O0 p) Ω) : Ω) = ι z := fun z => rfl
  let I : Ideal (integralClosure (O0 p) Ω) := Ideal.span {((p : integralClosure (O0 p) Ω)) ^ m}
  letI : Algebra (On p m) (integralClosure (O0 p) Ω ⧸ I) :=
    ((Ideal.Quotient.mk I).comp ιA.toRingHom).toAlgebra
  have halg : ∀ z, algebraMap (On p m) (integralClosure (O0 p) Ω ⧸ I) z = Ideal.Quotient.mk I (ιA z) :=
    fun z => rfl
  haveI : IsScalarTower (O0 p) (On p m) (integralClosure (O0 p) Ω ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [halg, AlgHom.commutes, Ideal.Quotient.mk_algebraMap]

  let g : Ω → On p m := Function.invFun ι
  have hg : ∀ x ∈ Lev T m, ι (g x) = x := fun x hx =>
    Function.invFun_eq ((AlgHom.mem_range ι).1 (hrange.symm ▸ hx))
  have hgm : ∀ x ∈ Lev T m, ∀ z, ι z = x → g x = z := fun x hx z hz =>
    hinj ((hg x hx).trans hz.symm)
  let lift : (integralClosure (O0 p) Ω ⧸ I) → integralClosure (O0 p) Ω :=
    Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ s, Ideal.Quotient.mk I (lift s) = s := Function.surjInv_eq _
  have hdiv := fun a ha => GlobalTheory.LevDer.int_div_of_mk (p := p) (Ω := Ω) m a ha

  have hF : ∀ D : Derivation (O0 p) (On p m) (integralClosure (O0 p) Ω ⧸ I),
      IsDer (Lev T m) (fun x => ((lift (D (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ m) := by
    intro D
    refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
    · have e : g (x + y) = g x + g y :=
        hgm _ (add_mem hx hy) _ (by rw [map_add (f := _), hg x hx, hg y hy])
      refine int_congr (hdiv (lift (D (g (x + y))) - lift (D (g x)) - lift (D (g y))) ?_) ?_
      · rw [map_sub (Ideal.Quotient.mk I), map_sub (Ideal.Quotient.mk I), hlift, hlift, hlift, e, map_add (f := _)]; ring
      · push_cast; ring
    · have e : g (x * y) = g x * g y :=
        hgm _ (mul_mem hx hy) _ (by rw [map_mul, hg x hx, hg y hy])
      refine int_congr (hdiv (lift (D (g (x * y))) - ιA (g x) * lift (D (g y))
        - ιA (g y) * lift (D (g x))) ?_) ?_
      · rw [map_sub (Ideal.Quotient.mk I), map_sub (Ideal.Quotient.mk I), map_mul (Ideal.Quotient.mk I), map_mul (Ideal.Quotient.mk I), hlift, hlift, hlift, e, Derivation.leibniz,
          Algebra.smul_def, Algebra.smul_def, halg, halg]; ring
      · push_cast; rw [hιAv, hιAv, hg x hx, hg y hy]; ring
    · have e : g (algebraMap (O0 p) Ω c) = algebraMap (O0 p) (On p m) c :=
        hgm _ (Subalgebra.algebraMap_mem _ c) _ (ι.commutes c)
      refine hdiv _ ?_
      rw [hlift, e, Derivation.map_algebraMap]

  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hpd := GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T 1 1 le_rfl (Nat.totient_pos.2 (ppow_pos (p := p) 1))
  let u : integralClosure (O0 p) Ω := ⟨(p : Ω) / (T.ζ 1 - 1) ^ 1, hpd⟩
  have hz1 : T.ζ 1 - 1 ≠ 0 :=
    sub_ne_zero.2 ((T.prim 1).ne_one (by simpa using (Fact.out : p.Prime).one_lt))
  have hpow : T.ζ (k + 1) ^ p ^ k = T.ζ 1 := by
    have := zeta_pow T 1 k; rwa [add_comm] at this
  have hxn : Ideal.Quotient.mk (towerIdeal p (k + 1)) (C X) = xn p (k + 1) := rfl
  have hyn : Ideal.Quotient.mk (towerIdeal p (k + 1)) X = yn p (k + 1) := rfl
  have hd := congrArg ι (DlogUniq.derivative_cyclotomic_mul p k)
  simp only [map_mul, map_sub, map_pow, map_natCast, map_one, hι.1, hpow] at hd
  have hxz : algebraMap (On p (k + 1)) (integralClosure (O0 p) Ω ⧸ I)
      (aeval (xn p (k + 1)) (derivative (cyclotomic (p ^ (k + 1)) (O0 p)))) *
      algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * xn p (k + 1)) = 0 := by
    rw [← map_mul, halg, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨ιA (xn p (k + 1)) ^ (p ^ (k + 1) - 1) * u * ιA (xn p (k + 1)), Subtype.ext ?_⟩
    have hp' : (p : Ω) = (T.ζ 1 - 1) * ((p : Ω) / (T.ζ 1 - 1) ^ 1) := by field_simp
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, hιAv,
      map_mul, map_natCast, hι.1, u]
    linear_combination (-((p : Ω) / (T.ζ 1 - 1) ^ 1 * T.ζ (k + 1))) * hd -
      (ι (aeval (xn p (k + 1)) (derivative (cyclotomic (p ^ (k + 1)) (O0 p)))) * T.ζ (k + 1)) * hp'
  obtain ⟨Dz, hzx, hzy⟩ := DlogUniq.exists_derivation (cyclotomic (p ^ (k + 1)) (O0 p)) (p ^ (k + 1))
    (qO p) (towerIdeal p (k + 1)) rfl (integralClosure (O0 p) Ω ⧸ I)
    (algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * xn p (k + 1))) 0 hxz (mul_zero _)
  have hyq : ∀ N : ℕ, N = p ^ (k + 1) → (N : integralClosure (O0 p) Ω ⧸ I) *
      algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * yn p (k + 1)) = 0 := by
    intro N hN
    rw [← map_natCast (algebraMap (On p (k + 1)) (integralClosure (O0 p) Ω ⧸ I)) N, ← map_mul, halg,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨ιA ((p : On p (k + 1)) * yn p (k + 1)), Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, hιAv,
      map_mul, map_natCast]
    rw [natCast_eq_pow (Ω := Ω) N p k hN]
    ring
  obtain ⟨N, hN⟩ : ∃ N, N = p ^ (k + 1) := ⟨_, rfl⟩
  obtain ⟨Dq, hqx, hqy⟩ := DlogUniq.exists_derivation (cyclotomic (p ^ (k + 1)) (O0 p)) N
    (qO p) (towerIdeal p (k + 1)) (by rw [hN]; rfl) (integralClosure (O0 p) Ω ⧸ I)
    0 (algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * yn p (k + 1))) (mul_zero _)
    (hyq N hN)
  rw [hxn] at hzx hqx
  rw [hyn] at hzy hqy
  have hgz : g (T.ζ (k + 1)) = xn p (k + 1) := hgm _ (zeta_mem_Lev T _) _ hι.1
  have hgq : g (T.qq (k + 1)) = yn p (k + 1) := hgm _ (qq_mem_Lev T _) _ hι.2
  refine ⟨fun x => ((lift (Dz (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ (k + 1),
    fun x => ((lift (Dq (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ (k + 1),
    hF Dz, hF Dq, ?_, ?_, ?_, ?_⟩
  · refine int_congr (hdiv (lift (Dz (xn p (k + 1))) - ιA ((p : On p (k + 1)) * xn p (k + 1))) ?_) ?_
    · rw [map_sub (Ideal.Quotient.mk I), hlift, hzx, halg, sub_self]
    · simp only [hgz, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, SubringClass.coe_natCast, hιAv, map_mul, map_natCast, hι.1]
      ring
  · exact int_congr (hdiv (lift (Dz (yn p (k + 1)))) (by rw [hlift, hzy])) (by simp only [hgq])
  · exact int_congr (hdiv (lift (Dq (xn p (k + 1)))) (by rw [hlift, hqx])) (by simp only [hgz])
  · refine int_congr (hdiv (lift (Dq (yn p (k + 1))) - ιA ((p : On p (k + 1)) * yn p (k + 1))) ?_) ?_
    · rw [map_sub (Ideal.Quotient.mk I), hlift, hqy, halg, sub_self]
    · simp only [hgq, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, SubringClass.coe_natCast, hιAv, map_mul, map_natCast, hι.2]
      ring

end GlobalTheory.LevDer
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.nonempty_H1_H2_equiv_of_continuous_mulEquiv : ∀ (R : Type) [CommRing R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (ρ : Representation R Γ M) (ρ' : Representation R Γ' M), (∀ g m, ρ' g m = ρ (e g) m) → Nonempty (H1 ρ ≃ H1 ρ') ∧ Nonempty (H2 ρ ≃ H2 ρ') ∧ (Subsingleton (Hn ρ 3) → Subsingleton (Hn ρ' 3)) := by
  first | exact @GlobalTheory.contCohomology_transport_mulEquiv | exact GlobalTheory.contCohomology_transport_mulEquiv | (intros; apply GlobalTheory.contCohomology_transport_mulEquiv <;> assumption)
end
