module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle103
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle081
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem sum_graph_eq_sum_entN {A : Type} [AddCommMonoid A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A)
    (S : Finset ℕ) (f : ℕ → ℕ) :
    (∑ a : Fin N, ∑ b : Fin N, if (a : ℕ) ∈ S ∧ (b : ℕ) = f a then M a b else 0) =
      ∑ a ∈ S, entN M a (f a) := by
  have h1 : ∀ a : Fin N, (∑ b : Fin N, if (a : ℕ) ∈ S ∧ (b : ℕ) = f a then M a b else 0) =
      if (a : ℕ) ∈ S then entN M a (f a) else 0 := by
    intro a
    by_cases ha : (a : ℕ) ∈ S
    · rw [if_pos ha]
      by_cases hf : f a < N
      · rw [Finset.sum_eq_single ⟨f a, hf⟩]
        · split_ifs with hc
          · unfold entN
            rw [dite_eq_left ⟨a.isLt, hf⟩]
          · exact absurd ⟨ha, rfl⟩ hc
        · intro b _ hb
          rw [if_neg]
          intro h
          exact hb (Fin.ext h.2)
        · intro h
          exact absurd (Finset.mem_univ _) h
      · rw [Finset.sum_eq_zero]
        · unfold entN
          rw [dite_eq_right (fun hh => hf hh.2)]
        · intro b _
          rw [if_neg]
          intro h
          exact hf (h.2 ▸ b.isLt)
    · rw [if_neg ha]
      exact Finset.sum_eq_zero (fun b _ => if_neg (fun h => ha h.1))
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  rw [Fin.sum_univ_eq_sum_range (fun a => if a ∈ S then entN M a (f a) else 0) N]
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a haS hnot
    have hlt : ¬ a < N := fun hlt => hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, haS⟩)
    unfold entN
    rw [dite_eq_right (fun hh => hlt hh.1)]

theorem phI_last_iff {N : ℕ} (k s : ℕ) (a b : Fin N) :
    phI k s s a b ↔ (a : ℕ) < b ∧ ¬ (s ≤ (a : ℕ) ∧ (a : ℕ) < s + k ∧ (b : ℕ) = s + k) := by
  simp only [phI, IsW, Fin.lt_iff_val_lt_val]
  constructor <;> intro h <;> omega

variable {g : ℕ} [Fact g.Prime]

theorem inPat_phI_last_iff {N : ℕ} (k s : ℕ) (M : Mt g N) :
    InPat (phI k s s) M ↔ IsUniUp M ∧ ∀ a, s ≤ a → a < s + k → entN M a (s + k) = 0 := by
  unfold InPat IsUniUp
  constructor
  · intro h
    refine ⟨fun a b => ⟨fun hba => ?_, fun hab => ?_⟩, fun a h1 h2 => ?_⟩
    · have hv := Fin.lt_iff_val_lt_val.mp hba
      have hn : ¬ phI k s s a b := by
        rw [phI_last_iff]
        omega
      rw [h a b hn, Matrix.one_apply_ne]
      intro e
      rw [e] at hv
      omega
    · subst hab
      have hn : ¬ phI k s s a a := by
        rw [phI_last_iff]
        omega
      rw [h a a hn, Matrix.one_apply_eq]
    · unfold entN
      split_ifs with hh
      · have hn : ¬ phI k s s (⟨a, hh.1⟩ : Fin N) ⟨s + k, hh.2⟩ := by
          rw [phI_last_iff]
          exact fun h' => h'.2 ⟨h1, h2, rfl⟩
        rw [h _ _ hn, Matrix.one_apply_ne]
        intro e
        simp only [Fin.mk.injEq] at e
        omega
      · rfl
  · rintro ⟨hU, hz⟩ ⟨a, ha⟩ ⟨b, hb⟩ hn
    rw [phI_last_iff] at hn
    rcases lt_trichotomy a b with hab | hab | hab
    · have hw : s ≤ a ∧ a < s + k ∧ b = s + k := by
        by_contra hc
        exact hn ⟨hab, hc⟩
      obtain ⟨hw1, hw2, rfl⟩ := hw
      have h0 := hz a hw1 hw2
      unfold entN at h0
      rw [dite_eq_left ⟨ha, hb⟩] at h0
      rw [Matrix.one_apply_ne]
      · exact h0
      · intro e
        simp only [Fin.mk.injEq] at e
        omega
    · subst hab
      rw [(hU _ _).2 rfl, Matrix.one_apply_eq]
    · rw [(hU _ _).1 (Fin.mk_lt_mk.mpr hab), Matrix.one_apply_ne]
      intro e
      simp only [Fin.mk.injEq] at e
      omega

private theorem sum_sum_ite_eq_sum_entN_of_iff {A : Type} [AddCommMonoid A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A)
    (P : ℕ → ℕ → Prop) [∀ a b, Decidable (P a b)] (S : Finset ℕ) (f : ℕ → ℕ)
    (h : ∀ a b : ℕ, b < N → (P a b ↔ a ∈ S ∧ b = f a)) :
    (∑ a : Fin N, ∑ b : Fin N, if P (a : ℕ) (b : ℕ) then M a b else 0) = ∑ a ∈ S, entN M a (f a) := by
  rw [← sum_graph_eq_sum_entN]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases hp : P a b
  · rw [if_pos hp, if_pos ((h a b b.isLt).1 hp)]
  · rw [if_neg hp, if_neg (fun hq => hp ((h a b b.isLt).2 hq))]

theorem sumAt_eeI_eq_phiJ {N : ℕ} (k s : ℕ) (hN : N = k + 2 * s + 1) (M : Mt g N) :
    sumAt (eeI k s) M = phiJ k s M := by
  subst hN
  have hsplit : sumAt (eeI k s) M =
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (b : ℕ) = a + 1 ∧ (b : ℕ) < s then M a b else 0) +
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k then M a b else 0) +
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ) then M a b else 0) +
      (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
        if (b : ℕ) = a + 1 ∧ s ≤ (a : ℕ) ∧ (b : ℕ) < s + k then M a b else 0) := by
    unfold sumAt
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    have hb := b.isLt
    unfold eeI IsW
    split_ifs <;> first | omega | simp
  have h1 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (b : ℕ) = a + 1 ∧ (b : ℕ) < s then M a b else 0) =
      ∑ a ∈ Finset.range (s - 1), entN M a (a + 1) :=
    sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ b < s) _ (fun a => a + 1)
      (fun a b _ => by simp only [Finset.mem_range]; constructor <;> intro h <;> omega)
  have h2 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k then M a b else 0) =
      ∑ a ∈ (Finset.range s).filter (fun a => a + 1 = s), entN M a (s + k) :=
    sum_sum_ite_eq_sum_entN_of_iff M (fun a b => a + 1 = s ∧ b = s + k) _ (fun _ => s + k)
      (fun a b _ => by simp only [Finset.mem_filter, Finset.mem_range]; constructor <;> intro h <;> omega)
  have h3 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ) then M a b else 0) =
      ∑ i ∈ Finset.range s, entN M (s + k + i) (s + k + i + 1) := by
    rw [sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ s + k ≤ a) (Finset.Ico (s + k) (s + k + s)) (fun a => a + 1)
      (fun a b hb => by simp only [Finset.mem_Ico]; constructor <;> intro h <;> omega)]
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have h4 : (∑ a : Fin (k + 2 * s + 1), ∑ b : Fin (k + 2 * s + 1),
      if (b : ℕ) = a + 1 ∧ s ≤ (a : ℕ) ∧ (b : ℕ) < s + k then M a b else 0) =
      ∑ a ∈ Finset.range (k - 1), entN M (s + a) (s + a + 1) := by
    rw [sum_sum_ite_eq_sum_entN_of_iff M (fun a b => b = a + 1 ∧ s ≤ a ∧ b < s + k) (Finset.Ico s (s + (k - 1))) (fun a => a + 1)
      (fun a b _ => by simp only [Finset.mem_Ico]; constructor <;> intro h <;> omega)]
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have key : (∑ a ∈ (Finset.range s).filter (fun a => a + 1 = s), entN M a (s + k)) +
      (∑ i ∈ Finset.range s, entN M (s + k + i) (s + k + i + 1)) =
      (if 1 ≤ s then entN M (s - 1) (s + k) + entN M (s + k) (s + k + 1) else 0) +
      ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 2 + i) := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp
    · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have hB : (Finset.range (t + 1)).filter (fun a => a + 1 = t + 1) = {t} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        omega
      have hC : (∑ i ∈ Finset.range (t + 1), entN M (t + 1 + k + i) (t + 1 + k + i + 1)) =
          (∑ i ∈ Finset.range (t + 1 - 1), entN M (t + 1 + k + 1 + i) (t + 1 + k + 2 + i)) +
            entN M (t + 1 + k) (t + 1 + k + 1) := by
        rw [Finset.sum_range_succ', Nat.add_sub_cancel]
        simp only [add_zero]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by congr 1 <;> omega)
      rw [hB, Finset.sum_singleton, hC, if_pos (show 1 ≤ t + 1 by omega), Nat.add_sub_cancel]
      ring
  rw [hsplit, h1, h2, h3, h4]
  unfold phiJ
  linear_combination key

theorem ePat_last_eq_eJ : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N k s : ℕ), N = k + 2 * s + 1 →
    ePat g N (phI k s s) (eeI k s) ψ = eJ g N k s ψ := by
  intro g _ ψ N k s hN
  have hP : (InPat (phI k s s) : Mt g N → Prop) =
      fun M => IsUniUp M ∧ ∀ a, s ≤ a → a < s + k → entN M a (s + k) = 0 :=
    funext fun M => propext (inPat_phI_last_iff k s M)
  have hφ : (sumAt (eeI k s) : Mt g N → ZMod g) = phiJ k s := funext fun M => sumAt_eeI_eq_phiJ k s hN M
  unfold ePat eJ
  rw [hP, hφ]

end GlobalTheory.GLm
end
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.NearCount

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem line_cyclic (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ u ∈ line (I : Submodule (𝓞 K) K) v,
      line (I : Submodule (𝓞 K) K) v ≤ n • line (I : Submodule (𝓞 K) K) v ⊔ Submodule.span (𝓞 K) {u} := by
  obtain ⟨a, J, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  let φ : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V ((algebraMap (𝓞 K) K a)⁻¹ • v)
  have hφ : line (I : Submodule (𝓞 K) K) v = Submodule.map φ J := by
    ext x
    simp only [line, Submodule.mem_map, hI, FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul,
      FractionalIdeal.mem_coeIdeal, φ, LinearMap.toSpanSingleton_apply, LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨y, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
  rw [hφ]
  by_cases hJ : J = ⊥
  · exact ⟨0, zero_mem _, by simp [hJ]⟩
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_sup_span_eq (I := n * J) (J := J) Ideal.mul_le_right
    (mul_ne_zero hn hJ)
  have hbJ : b ∈ J := by
    rw [← hb]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
  refine ⟨φ b, Submodule.mem_map_of_mem hbJ, ?_⟩
  conv_lhs => rw [← hb]
  rw [Submodule.map_sup, ← Ideal.smul_eq_mul, Submodule.map_smul'']
  refine sup_le_sup_left ?_ _
  rw [← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton]


omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem count_between (P : Submodule (𝓞 K) V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) (e : ℕ) (v : Fin e → V)
    (hv : ∀ i, v i ∈ P) (hP : P ≤ n • P ⊔ Submodule.span (𝓞 K) (Set.range v)) :
    {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P}.encard ≤ ((Ideal.absNorm n ^ (e * e) : ℕ) : ℕ∞) := by
  let S : Submodule (𝓞 K) P := (n • P).comap P.subtype
  let w : Fin e → P ⧸ S := fun i => S.mkQ ⟨v i, hv i⟩
  have hS : ∀ a ∈ n, ∀ y : P ⧸ S, a • y = 0 := by
    intro a ha y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha x.2
  have hgen : ∀ y : P ⧸ S, ∃ c : Fin e → 𝓞 K, y = ∑ i, c i • w i := by
    intro y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hP x.2)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ht
    refine ⟨c, ?_⟩

    simp only [w, ← map_smul, ← map_sum]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show ((x - ∑ i, c i • (⟨v i, hv i⟩ : P) : P) : V) ∈ n • P
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, ← hst, add_sub_cancel_right]
    exact hs
  haveI : Finite (𝓞 K ⧸ n) := Ideal.finiteQuotientOfFreeOfNeBot n hn
  let f : (Fin e → 𝓞 K ⧸ n) → P ⧸ S := fun c => ∑ i, (c i).out • w i
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨c, rfl⟩ := hgen y
    refine ⟨fun i => Ideal.Quotient.mk n (c i), Finset.sum_congr rfl fun i _ => ?_⟩
    rw [← sub_eq_zero, ← sub_smul]
    apply hS
    rw [← Ideal.Quotient.eq]
    exact Quotient.out_eq _
  haveI : Finite (P ⧸ S) := Finite.of_surjective f hf
  have hcard : Nat.card (P ⧸ S) ≤ Ideal.absNorm n ^ e := by
    refine (Nat.card_le_card_of_surjective f hf).trans (le_of_eq ?_)
    rw [Nat.card_fun, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simp
  have hw : Submodule.span (𝓞 K) (Set.range w) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨c, rfl⟩ := hgen y
    exact (Submodule.mem_span_range_iff_exists_fun _).2 ⟨c, rfl⟩
  have hc := Formalism.SLP.P.card_submodules_le_of_dedekind (𝓞 K) (P ⧸ S) e w hw
  haveI : Finite (Submodule (𝓞 K) (P ⧸ S)) := Finite.of_injective _ SetLike.coe_injective
  have hinj : Set.InjOn (fun L : Submodule (𝓞 K) V => (L.comap P.subtype).map S.mkQ)
      {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P} := by
    have key : ∀ L : Submodule (𝓞 K) V, n • P ≤ L → L ≤ P →
        (((L.comap P.subtype).map S.mkQ).comap S.mkQ).map P.subtype = L := by
      intro L h1 h2
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 (Submodule.comap_mono h1),
        Submodule.map_comap_subtype, inf_eq_right.2 h2]
    intro L hL L' hL' h
    rw [← key L hL.1 hL.2, ← key L' hL'.1 hL'.2]
    simp only at h
    rw [h]
  refine (Set.encard_le_encard_of_injOn (t := Set.univ) (Set.mapsTo_univ _ _) hinj).trans ?_
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.cast_le, pow_mul]
  exact hc.trans (Nat.pow_le_pow_left hcard e)

theorem smul_injective (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Function.Injective fun P : Submodule (𝓞 K) V => m • P := by
  obtain ⟨a, ham, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨J, hJ⟩ : m ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ham)
  have key : ∀ P Q : Submodule (𝓞 K) V, m • P = m • Q → P ≤ Q := by
    intro P Q h x hx
    have h2 : Ideal.span {a} • P = Ideal.span {a} • Q := by
      rw [hJ, mul_comm, Submodule.mul_smul, Submodule.mul_smul, h]
    have h3 : a • x ∈ Ideal.span {a} • Q := h2 ▸ Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
    obtain ⟨y, hy, hxy⟩ := h3
    have ha' : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    rw [← algebraMap_smul K a y, ← algebraMap_smul K a x] at hxy
    rwa [← smul_right_injective V ha' hxy]
  intro P Q h
  exact le_antisymm (key P Q h) (key Q P h.symm)

theorem exists_gens [StarRing K] {H : HermSpace K V} {r : ℕ} (N : NF H r) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ v : Fin (2 * r + 1) → V, (∀ i, v i ∈ N.P0) ∧ N.P0 ≤ n • N.P0 ⊔ Submodule.span (𝓞 K) (Set.range v) := by
  choose u hu hu' using fun (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) => line_cyclic I v n hn
  let d : FractionalIdeal (𝓞 K)⁰ K := N.𝔡
  let I : Option (Fin r ⊕ Fin r) → FractionalIdeal (𝓞 K)⁰ K := fun o => o.elim 1
    (Sum.elim (fun a => d ^ (-((r : ℤ) - a.val)))
      fun a => if a.val < N.j then d ^ (-((r : ℤ) - a.val)) else d ^ ((r : ℤ) - a.val))
  let x : Option (Fin r ⊕ Fin r) → V := fun o => o.elim N.F.z
    (Sum.elim (fun a => N.F.e a.castSucc) fun a => if a.val < N.j then N.F'.e a.castSucc else N.ist a)
  have hP : N.P0 = ⨆ o, line (I o : Submodule (𝓞 K) K) (x o) := by
    apply le_antisymm
    · refine sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a h => ?_)) ?_) (iSup₂_le fun a h => ?_)
      · exact le_iSup_of_le (some (Sum.inl a)) le_rfl
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
        rfl
      · refine le_iSup_of_le none (le_of_eq ?_)
        simp only [I, x, Option.elim, FractionalIdeal.coe_one]
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_neg (not_lt.2 h)]
        rfl
    · refine iSup_le ?_
      rintro (_ | a | a)
      · simp only [I, x, Option.elim, FractionalIdeal.coe_one]
        exact le_sup_of_le_left le_sup_right
      · refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left ?_))
        exact le_iSup_of_le a le_rfl
      · by_cases h : a.val < N.j
        · simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
          refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right ?_))
          exact le_iSup₂_of_le a h le_rfl
        · simp only [I, x, Option.elim, Sum.elim_inr, if_neg h]
          refine le_sup_of_le_right ?_
          exact le_iSup₂_of_le a (not_lt.1 h) le_rfl
  have hle : ∀ o, line (I o : Submodule (𝓞 K) K) (x o) ≤ N.P0 := fun o => by
    rw [hP]; exact le_iSup (fun o => line (I o : Submodule (𝓞 K) K) (x o)) o
  let σ : Fin (2 * r + 1) ≃ Option (Fin r ⊕ Fin r) := Fintype.equivOfCardEq (by simp; ring)
  refine ⟨fun i => u (I (σ i)) (x (σ i)), fun i => hle _ (hu _ _), ?_⟩
  conv_lhs => rw [hP]
  refine iSup_le fun o => (hu' _ _).trans (sup_le_sup (Submodule.smul_mono le_rfl (hle o)) ?_)
  exact Submodule.span_mono (Set.singleton_subset_iff.2 ⟨σ.symm o, by simp⟩)

end GlobalTheory.DegCnt.NearCount

theorem GlobalTheory.DegCnt.NearCount.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ → ((({P : Submodule (𝓞 K) V | 𝔪 • N.P0 ≤ P ∧ 𝔪 • P ≤ N.P0}).encard : ℕ∞) : ℝ≥0∞) ≤ (Ideal.absNorm 𝔪 : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H _ r N m hm
  have hn : m * m ≠ ⊥ := mul_ne_zero hm hm
  obtain ⟨v, hv, hP⟩ := GlobalTheory.DegCnt.NearCount.exists_gens N (m * m) hn
  have h1 := GlobalTheory.DegCnt.NearCount.count_between N.P0 (m * m) hn _ v hv hP
  have h2 : ({P : Submodule (𝓞 K) V | m • N.P0 ≤ P ∧ m • P ≤ N.P0}).encard ≤
      {L : Submodule (𝓞 K) V | (m * m) • N.P0 ≤ L ∧ L ≤ N.P0}.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun P => m • P) ?_
      (GlobalTheory.DegCnt.NearCount.smul_injective m hm).injOn
    rintro P ⟨h, h'⟩
    exact ⟨by rw [Submodule.mul_smul]; exact Submodule.smul_mono le_rfl h, h'⟩
  refine (ENat.toENNReal_le.2 (h2.trans h1)).trans (le_of_eq ?_)
  rw [map_mul, ← sq, ← pow_mul, ← sq]
  simp
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory


open scoped Pointwise in
theorem covol_eq_measure_inter_fund : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) (μ : Measure G) (fund A : Set G), (Γ : Set G).Countable → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → MeasurableSet A → (∀ γ ∈ Γ, ∀ x ∈ A, γ * x ∈ A) → covol (Γ : Set G) μ A = μ (A ∩ fund) := by
  intro G _ _ _ Γ μ fund A hc hμ hf hcov hdis hA hinv
  have : Countable Γ := hc.to_subtype
  have : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  have : SMulInvariantMeasure Γ G μ := ⟨fun γ s hs => by
    have h := hμ γ γ.2
    conv_rhs => rw [← h]
    rw [Measure.map_apply (measurable_const_mul (γ : G)) hs]
    rfl⟩
  have hF : IsFundamentalDomain Γ fund μ := by
    refine IsFundamentalDomain.mk'' hf.nullMeasurableSet ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun y => ?_
      obtain ⟨γ, hγ, h⟩ := hcov y
      exact ⟨⟨γ, hγ⟩, h⟩
    · intro γ hγ
      exact hdis γ γ.2 (fun h => hγ (Subtype.ext h))
    · intro γ
      exact (measurePreserving_smul γ μ).quasiMeasurePreserving
  apply le_antisymm
  · unfold covol
    refine iInf_le_of_le (A ∩ fund) (iInf_le_of_le (hA.inter hf) (iInf_le_of_le ?_ le_rfl))
    intro x hx
    obtain ⟨γ, hγ, h⟩ := hcov x
    exact ⟨γ, hγ, hinv γ hγ x hx, h⟩
  · unfold covol
    refine le_iInf fun D => le_iInf fun _ => le_iInf fun hD => ?_
    rw [hF.measure_eq_tsum D]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    rintro x ⟨hx, hxf⟩
    obtain ⟨γ, hγ, h⟩ := hD x hx
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hxf⟩
    rw [Set.mem_inv_smul_set_iff]
    exact h

end GlobalTheory
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.amp_summand_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, ∀ h ∈ S.St, P (h • Λ) ↔ P Λ) → ∀ Λ, S.IsTerm d Λ → IsLat L Λ → ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o = Quotient.mk'' Λ → S.IsTerm d o.out ∧ (∃ h ∈ S.St, o.out = h • Λ) ∧ (if S.IsTerm d o.out ∧ P o.out then (S.mu o.out : ℂ) * S.om d o.out else 0) = (if P Λ then (S.mu Λ : ℂ) * S.om d Λ else 0) ∧ (if S.IsTerm d o.out ∧ P o.out then ENNReal.ofReal (S.mu o.out) else 0) = (if P Λ then ENNReal.ofReal (S.mu Λ) else 0) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d P hP Λ hT hL o ho
  have hrel : MulAction.orbitRel S.St (Submodule L.O S.V) o.out Λ := by
    have h1 : (Quotient.mk'' o.out : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)) = Quotient.mk'' Λ :=
      (Quotient.out_eq' o).trans ho
    exact Quotient.exact' h1
  obtain ⟨g, hg⟩ := hrel
  have hout : o.out = (g : S.GLV) • Λ := by rw [← hg]; rfl
  have hgm : (g : S.GLV) ∈ S.St := g.2
  obtain ⟨hT', hom, -⟩ := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hT _ hgm
  have hmu : S.mu ((g : S.GLV) • Λ) = S.mu Λ := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ hL |>.2.2 _ hgm
  have hPg : P ((g : S.GLV) • Λ) ↔ P Λ := hP Λ _ hgm
  refine ⟨hout ▸ hT', ⟨_, hgm, hout⟩, ?_, ?_⟩
  · rw [hout]; simp only [hT', true_and, hPg, hmu, hom]
  · rw [hout]; simp only [hT', true_and, hPg, hmu]
end
