module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.MemColRangeOfLeEntry
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle038
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AllowedLettersOfLateRows
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs3

variable {N r : ℕ}

theorem Icut_eq [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    Icut n0 ν c = if 1 ≤ c ∧ c ≤ be then Finset.univ \ riseA n0 ν c r else ∅ := by
  classical
  unfold Icut
  rw [Ican_eq H]
  split_ifs
  · rfl
  · exact Finset.empty_sdiff _

theorem pEnd_cut {n0 : ℕ} (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) : pEnd (cutPath n0 ν) = stg ν n0 := by
  rw [pEnd_eq, stg_cut n0 ν N le_rfl, min_eq_right hn]

theorem riseA_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : Fin r) :
    (riseA n0 ν c r).filter (· ≤ t) = riseA n0 ν c r \ riseA n0 ν c (r - 1 - t.val) := by
  classical
  ext m
  have hm := m.isLt
  have ht := t.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, fun h4 => ?_⟩
    have : m.val ≤ t.val := h3
    omega
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    by_contra h4
    have h5 : t.val < m.val := not_le.mp h4
    exact h3 (by omega) h2

theorem riseA_mono (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {s t : ℕ} (h : s ≤ t) :
    riseA n0 ν c s ⊆ riseA n0 ν c t := by
  classical
  intro m
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨h1, h2⟩
  exact ⟨by omega, h2⟩

theorem card_Icut_filter [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (c : ℤ) (hc : 1 ≤ c ∧ c ≤ be) (t : Fin r) :
    ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + r =
      t.val + 1 + colH (stg ν (n0 + (r - 1 - t.val))) c := by
  classical
  have ht := t.isLt
  have h1 : ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + ((riseA n0 ν c r).filter (· ≤ t)).card =
      t.val + 1 := by
    rw [← Finset.card_union_of_disjoint]
    · have : (Finset.univ \ riseA n0 ν c r).filter (· ≤ t) ∪ (riseA n0 ν c r).filter (· ≤ t) = Finset.Iic t := by
        ext m
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_Iic]
        tauto
      rw [this, Fin.card_Iic]
    · rw [Finset.disjoint_left]
      intro m hm hm'
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm hm'
      exact hm.1 hm'.1
  have h2 : ((riseA n0 ν c r).filter (· ≤ t)).card + (riseA n0 ν c (r - 1 - t.val)).card = (riseA n0 ν c r).card := by
    rw [riseA_filter, Finset.card_sdiff_add_card_eq_card (riseA_mono n0 ν c (by omega))]
  have h3 := card_riseA H c r le_rfl
  have h4 := card_riseA H c (r - 1 - t.val) (by omega)
  have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact hc.2
  rw [hN, hNr] at h3
  omega

theorem isSt_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    IsSt (cutPath n0 ν) (Icut n0 ν) := by
  classical
  have hcard : ∀ c, (Icut n0 ν c).card =
      if 1 ≤ c then colH (pEnd (cutPath n0 ν)) c else r - colH (pEnd (cutPath n0 ν)) c := by
    intro c
    rw [pEnd_cut (by omega), Icut_eq H]
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1]
      by_cases h2 : c ≤ be
      · rw [if_pos ⟨h1, h2⟩, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        have h3 := card_riseA H c r le_rfl
        have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact h2
        rw [hN, hNr] at h3
        omega
      · rw [if_neg fun h => h2 h.2, Finset.card_empty,
          colH_none fun m => lt_of_le_of_lt (H.rng n0 (by omega) m).2 (by omega)]
    · rw [if_neg h1, if_neg fun h => h1 h.1, Finset.card_empty,
        colH_all fun m => le_trans (by omega) (H.rng n0 (by omega) m).1]
      omega
  refine ⟨?_, hcard, ?_⟩
  · intro c hc
    by_cases h : 1 ≤ c ∧ c ≤ be
    · rw [← Finset.card_eq_zero, hcard c, if_pos h.1, pEnd_cut (by omega)]
      apply colH_none
      intro m
      by_contra hge
      apply hc
      refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨n0, by omega⟩ m (by omega) ?_
      have : cutPath n0 ν ⟨n0, by omega⟩ m = stg ν n0 m := by simp [cutPath]
      rw [this]; omega
    · rw [Icut_eq H, if_neg h]
  · intro c t
    unfold tabCol
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1, if_pos (by omega : (1 : ℤ) ≤ c + 1), Icut_eq H, Icut_eq H]
      by_cases h2 : c + 1 ≤ be
      · rw [if_pos ⟨by omega, h2⟩, if_pos ⟨h1, by omega⟩]
        have e1 := card_Icut_filter hN H (c + 1) ⟨by omega, h2⟩ t
        have e2 := card_Icut_filter hN H c ⟨h1, by omega⟩ t
        have e3 := colH_anti (stg ν (n0 + (r - 1 - t.val))) (by omega : c ≤ c + 1)
        omega
      · rw [if_neg fun h => h2 h.2]
        simp
    · rw [if_neg h1]
      have hc0 : Icut n0 ν c = ∅ := by rw [Icut_eq H, if_neg fun h => h1 h.1]
      rw [hc0, Finset.sdiff_empty]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

theorem le_iff_lt_colH {μ : Fin r → ℤ} (hμ : Antitone μ) (c : ℤ) (m : Fin r) : c ≤ μ m ↔ m.val < colH μ c := by
  first | exact UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH .. | (apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ c m | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ c | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r

theorem eq_of_colH {μ μ' : Fin r → ℤ} (hμ : Antitone μ) (hμ' : Antitone μ') (h : ∀ c, colH μ c = colH μ' c) :
    μ = μ' := by
  funext m
  apply le_antisymm
  · rw [le_iff_lt_colH hμ', ← h, ← le_iff_lt_colH hμ]
  · rw [le_iff_lt_colH hμ, h, ← le_iff_lt_colH hμ']

theorem riseA_eq_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {t : ℕ} (ht : t ≤ r) :
    riseA n0 ν c t = (riseA n0 ν c r).filter fun m => r - 1 - m.val < t := by
  classical
  ext m
  have := m.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩
  · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩

theorem path_eq_of_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν ν' : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (H' : PlHyp n0 be ν') (hd : ∀ i, Antitone (ν i)) (hd' : ∀ i, Antitone (ν' i))
    (hcut : cutPath n0 ν = cutPath n0 ν') (hI : Icut n0 ν = Icut n0 ν') : ν = ν' := by
  classical
  have hlow : ∀ i ≤ n0, stg ν i = stg ν' i := by
    intro i hi
    have h1 := stg_cut n0 ν i (by omega)
    have h2 := stg_cut n0 ν' i (by omega)
    rw [min_eq_left hi] at h1 h2
    rw [← h1, ← h2, hcut]
  have hrise : ∀ c, 1 ≤ c ∧ c ≤ be → riseA n0 ν c r = riseA n0 ν' c r := by
    intro c hc
    have h1 := congrFun hI c
    rw [Icut_eq H, Icut_eq H', if_pos hc, if_pos hc] at h1
    have := congrArg (fun s => Finset.univ \ s) h1
    simpa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using this
  funext i
  rw [stg_eq ν i.val i.isLt, stg_eq ν' i.val i.isLt]
  by_cases hi : i.val ≤ n0
  · exact hlow i.val hi
  · obtain ⟨t, ht⟩ : ∃ t, i.val = n0 + t := ⟨i.val - n0, by omega⟩
    have hi' := i.isLt
    have htr : t ≤ r := by omega
    apply eq_of_colH
    · rw [← stg_eq ν i.val i.isLt]; exact hd i
    · rw [← stg_eq ν' i.val i.isLt]; exact hd' i
    intro c
    rw [ht]
    by_cases hc : 1 ≤ c ∧ c ≤ be
    · rw [← card_riseA H c t htr, ← card_riseA H' c t htr, hlow n0 le_rfl, riseA_eq_filter n0 ν c htr,
        riseA_eq_filter n0 ν' c htr, hrise c hc]
    · by_cases h1 : 1 ≤ c
      · have h2 : be < c := by
          by_contra h; exact hc ⟨h1, by omega⟩
        rw [colH_none fun m => lt_of_le_of_lt (H.rng _ (by omega) m).2 h2,
          colH_none fun m => lt_of_le_of_lt (H'.rng _ (by omega) m).2 h2]
      · rw [colH_all fun m => le_trans (by omega) (H.rng _ (by omega) m).1,
          colH_all fun m => le_trans (by omega) (H'.rng _ (by omega) m).1]

end Abs3

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Img

variable {ι ι' : Type} {n : ℕ}

theorem multideg_imgMon [DecidableEq ι'] (ga : ι → ι') (ep : ι → ℕ) (m : ι × Fin n →₀ ℕ) (t : ι') :
    multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m) t =
      m.sum fun v k => (if ga v.1 = t then ep v.1 else 0) * k := by
  classical
  unfold multideg imgMon
  simp only [Finsupp.sum_apply]
  unfold Finsupp.sum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases h : ga v.1 = t
  · simp [h]
  · simp [h]

theorem sum_eq_multideg (h : ι → ℕ) (m : ι × Fin n →₀ ℕ) (T : Finset ι) (hT : ∀ v ∈ m.support, v.1 ∈ T) :
    (m.sum fun v k => h v.1 * k) = ∑ x ∈ T, h x * multideg m x := by
  classical
  have hsub : m.support ⊆ T ×ˢ (Finset.univ : Finset (Fin n)) := by
    intro v hv
    rw [Finset.mem_product]
    exact ⟨hT v hv, Finset.mem_univ _⟩
  rw [Finsupp.sum_of_support_subset m hsub _ (fun _ _ => mul_zero _), Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold multideg
  rw [Finset.mul_sum]

theorem multideg_imgMon_congr (ga : ι → ι') (ep : ι → ℕ) (m m' : ι × Fin n →₀ ℕ)
    (h : ∀ x, multideg m x = multideg m' x) (t : ι') :
    multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m) t =
      multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m') t := by
  classical
  rw [multideg_imgMon, multideg_imgMon]
  let T : Finset ι := m.support.image Prod.fst ∪ m'.support.image Prod.fst
  rw [sum_eq_multideg (fun x => if ga x = t then ep x else 0) m T
      (fun v hv => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)),
    sum_eq_multideg (fun x => if ga x = t then ep x else 0) m' T
      (fun v hv => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv))]
  exact Finset.sum_congr rfl fun x _ => by rw [h x]

theorem degAt_aeval {R : Type} [CommRing R] (ga : ι → ι') (ep : ι → ℕ) {β : ι → ℕ}
    {P Q : MvPolynomial (ι × Fin n) R} (hP : P ∈ Pol R n β) (hQ : Q ∈ Pol R n β) (hQ0 : Q ≠ 0) :
    ∃ δ : ι' → ℕ, (∀ t, DegAt t (δ t)
        (aeval (fun v : ι × Fin n => (X (ga v.1, v.2) : MvPolynomial (ι' × Fin n) R) ^ ep v.1) P)) ∧
      ∀ t, DegAt t (δ t)
        (aeval (fun v : ι × Fin n => (X (ga v.1, v.2) : MvPolynomial (ι' × Fin n) R) ^ ep v.1) Q) := by
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hQ0
  have hm0' : m0 ∈ Q.support := MvPolynomial.mem_support_iff.mpr hm0
  refine ⟨fun t => multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m0) t,
    fun t m' hm' => ?_, fun t m' hm' => ?_⟩
  · obtain ⟨m, hm, rfl⟩ := supp_aeval_pow (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) P hm'
    exact multideg_imgMon_congr ga ep m m0
      (fun x => (mem_Pol_iff.mp hP m hm x).trans (mem_Pol_iff.mp hQ m0 hm0' x).symm) t
  · obtain ⟨m, hm, rfl⟩ := supp_aeval_pow (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) Q hm'
    exact multideg_imgMon_congr ga ep m m0
      (fun x => (mem_Pol_iff.mp hQ m hm x).trans (mem_Pol_iff.mp hQ m0 hm0' x).symm) t

end Img

theorem degAt_monomial {R : Type} [CommRing R] {ι : Type} {n : ℕ} (l : ι × Fin n →₀ ℕ) (c : R) (t : ι) :
    DegAt t (multideg l t) (monomial l c : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

theorem mem_Pol_of_degAt {R : Type} [CommRing R] {ι : Type} {n : ℕ} {d : ι → ℕ} {P : MvPolynomial (ι × Fin n) R}
    (h : ∀ t, DegAt t (d t) P) : P ∈ Pol R n d := mem_Pol_iff.mpr fun m hm t => h t m hm

theorem segment_product_degree_determined : SegmentProductDegreeDetermined := by
  intro p n' r K _ F O _ x z β l0 d hx hz hdeg hne
  classical
  have hz0 : ∀ j ∈ Finset.range F.J, z (j : ℤ) ≠ 0 := by
    intro j hj h0
    apply hne
    rw [Finset.prod_eq_zero hj (by rw [h0, map_zero]), zero_mul]
  have key : ∀ j : ℕ, ∃ δ : Fin n' → ℕ, j ∈ Finset.range F.J →
      (∀ t, DegAt t (δ t) (phSeg O K p F (j : ℤ) (x j))) ∧ ∀ t, DegAt t (δ t) (phSeg O K p F (j : ℤ) (z j)) := by
    intro j
    by_cases hj : j ∈ Finset.range F.J
    · obtain ⟨δ, h1, h2⟩ := degAt_aeval (R := O) (n := r + K) (fun y : ℤ => posOf n' y)
        (fun y : ℤ => p ^ F.dist (j : ℤ) y) (hx j) (hz j) (hz0 j hj)
      exact ⟨δ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose δ hδ using key
  have hX : ∀ t, DegAt t (∑ j ∈ Finset.range F.J, δ j t + multideg l0 t)
      ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l0 1) := fun t =>
    degAt_mul (degAt_prod _ _ _ fun j hj => (hδ j hj).1 t) (degAt_monomial l0 1 t)
  have hZ : ∀ t, DegAt t (∑ j ∈ Finset.range F.J, δ j t + multideg l0 t)
      ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1) := fun t =>
    degAt_mul (degAt_prod _ _ _ fun j hj => (hδ j hj).2 t) (degAt_monomial l0 1 t)
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hm0' := MvPolynomial.mem_support_iff.mpr hm0
  rw [RRdeg_eq_Pol] at hdeg ⊢
  refine mem_Pol_of_degAt fun t => ?_
  have e : d t = ∑ j ∈ Finset.range F.J, δ j t + multideg l0 t :=
    (mem_Pol_iff.mp hdeg m0 hm0' t).symm.trans (hZ t m0 hm0')
  rw [e]
  exact hX t

theorem degAt_sum {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι} {d : ℕ} {κ : Type} (s : Finset κ)
    (f : κ → MvPolynomial (ι × Fin n) R) (h : ∀ i ∈ s, DegAt x d (f i)) : DegAt x d (∑ i ∈ s, f i) := by
  classical
  intro m hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp (support_sum hm)
  exact h i hi m hmi

theorem degAt_C_mul {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι} {d : ℕ} (c : R)
    {P : MvPolynomial (ι × Fin n) R} (h : DegAt x d P) : DegAt x d (C c * P) := by
  intro m hm
  refine h m ?_
  rw [mem_support_iff] at hm ⊢
  intro h0
  exact hm (by rw [coeff_C_mul, h0, mul_zero])

theorem degAt_detPl {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x t : ℤ) :
    DegAt t (∑ a : Fin r, if X.row j x a = t then 1 else 0) (X.detPl R j x) := by
  classical
  unfold Dat.detPl
  rw [Matrix.det_apply]
  refine degAt_sum _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin r) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) := by
    simp
  rw [h1]
  refine degAt_C_mul _ ?_
  have h2 := degAt_prod (R := R) (x := t) Finset.univ
    (fun i : Fin r => (Matrix.of fun a b : Fin r => (MvPolynomial.X (X.row j x a, b) : MvPolynomial (ℤ × Fin r) R)) (σ i) i)
    (fun i => if X.row j x (σ i) = t then 1 else 0) (fun i _ => degAt_X (x := t) (X.row j x (σ i), i))
  rw [Equiv.sum_comp σ (fun a => if X.row j x a = t then 1 else 0)] at h2
  exact h2

theorem segment_image_multihomogeneous : SegmentImageMultihomogeneous := by
  intro p n' r K _ _ _ X O _ j b y e hy
  classical
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0]; simp [Dat.zSeg]⟩
  have hexp : ∀ P : SegRing O r K, expand (p ^ X.Rj p K j) P =
      aeval (fun v : ℤ × Fin (r + K) => (MvPolynomial.X ((fun z : ℤ => z) v.1, v.2) : SegRing O r K) ^
        (fun _ : ℤ => p ^ X.Rj p K j) v.1) P := by
    intro P
    have : expand (p ^ X.Rj p K j) = aeval (fun v : ℤ × Fin (r + K) =>
        (MvPolynomial.X ((fun z : ℤ => z) v.1, v.2) : SegRing O r K) ^ (fun _ : ℤ => p ^ X.Rj p K j) v.1) := by
      apply MvPolynomial.algHom_ext
      intro v
      simp
    rw [this]
  obtain ⟨δ, h1, -⟩ := degAt_aeval (R := O) (n := r + K) (fun z : ℤ => z) (fun _ : ℤ => p ^ X.Rj p K j) hy hy hy0
  have hD : X.DlSeg p K O j ∈ Pol O r (fun t => ∑ x ∈ X.toLate j, X.sg p K j x *
      ∑ a : Fin r, if X.row j x a = t then 1 else 0) := by
    refine mem_Pol_of_degAt fun t => ?_
    unfold Dat.DlSeg
    exact degAt_prod _ _ _ fun x _ => degAt_pow (degAt_detPl X j x t) _
  have h := hom_Pol_mul O (hom_Pol_mul O (plEmb_Pol r K hD) (mem_Pol_of_degAt h1))
    (mem_Pol_of_degAt fun t => degAt_monomial e (1 : O) t)
  unfold Dat.zSeg
  rw [hexp]
  exact ⟨_, h⟩

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
