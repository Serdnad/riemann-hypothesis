module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle005
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

theorem Comb.stair_strictAnti (m : ℕ) : StrictAnti (stair m) := by
  intro a b hab
  have hb := b.isLt
  have hab' : (a : ℕ) < b := hab
  simp only [stair]
  omega

theorem CombCfAtStair.proof (h1 : CombCfUpdateZero.Statement) : CombCfAtStair.Statement := by
  intro m n
  induction n with
  | zero =>
    intro lam hlam
    have hs := Comb.stair_strictAnti m
    have hl : StrictAnti (fun i => lam i + stair m i) := by
      intro a b hab
      have h2 := hlam hab.le
      have h3 := hs hab
      simp only
      omega
    simp only [alternantPsum, List.replicate_zero, List.map_nil, List.prod_nil, mul_one,
      vandermondeOf_X_eq_alt]
    rw [cf_alt_of_strictAnti hl hs]
    by_cases h0 : lam = 0
    · subst h0
      have hu : latticeWords 0 (0 : Fin m → ℕ) = univ := by
        rw [Finset.eq_univ_iff_forall]
        intro w
        simp only [latticeWords, mem_filter, mem_univ, true_and]
        refine ⟨fun t ht i j _ => ?_, fun i => pcnt_zero w i⟩
        have ht0 : t = 0 := by omega
        subst ht0
        rw [pcnt_zero, pcnt_zero]
      rw [hu, Finset.card_univ]
      simp
    · have hne : (fun i => lam i + stair m i) ≠ stair m := by
        intro h
        apply h0
        funext i
        have := congrFun h i
        show lam i = 0
        omega
      rw [if_neg hne, latticeWords_eq_empty_of_sum_ne]
      · simp
      · intro hsum
        apply h0
        funext i
        have := (Finset.sum_eq_zero_iff.mp hsum) i (mem_univ i)
        simpa using this
  | succ n ih =>
    intro lam hlam
    have hsplit : alternantPsum m (List.replicate (n + 1) 1) =
        alternantPsum m (List.replicate n 1) * psum (Fin m) ℚ 1 := by
      simp only [alternantPsum, List.replicate_succ', List.map_append, List.prod_append,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rw [hsplit, cf_mul_psum, card_latticeWords_succ n lam hlam, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_ite, Nat.cast_zero]
    by_cases hgood : 1 ≤ lam i ∧ Antitone (Function.update lam i (lam i - 1))
    · rw [if_pos (by omega), if_pos hgood.1]
      have hup : Function.update (fun j => lam j + stair m j) i (lam i + stair m i - 1) =
          fun j => Function.update lam i (lam i - 1) j + stair m j := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [Function.update_self]
          omega
        · simp only [Function.update_of_ne hj]
      rw [hup]
      exact ih _ hgood.2
    · have hR : (if 1 ≤ lam i then
          (((latticeWords n (Function.update lam i (lam i - 1))).card : ℕ) : ℚ) else 0) = 0 := by
        split_ifs with hi
        · rw [latticeWords_eq_empty_of_not_antitone n _ (fun h => hgood ⟨hi, h⟩)]
          simp
        · rfl
      rw [hR]
      split_ifs with hL
      · refine h1 m _ (isAlt_vandermonde_mul_prod _) lam hlam i hL ?_
        by_cases hi : lam i = 0
        · exact Or.inl hi
        · exact Or.inr fun h => hgood ⟨by omega, h⟩
      · rfl

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

noncomputable section

open scoped Classical

namespace CombExtendWord

theorem snoc_mem {m n : ℕ} (lam : Fin m → ℕ) (hlam : Antitone lam) (k : Fin m) (hk : 1 ≤ lam k)
    (v : Fin n → Fin m) (hv : v ∈ latticeWords n (Function.update lam k (lam k - 1))) :
    (Fin.snoc v k : Fin (n + 1) → Fin m) ∈ latticeWords (n + 1) lam := by
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hv ⊢
  obtain ⟨hlat, hcont⟩ := hv
  refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
  · rcases Nat.lt_or_ge t (n + 1) with htn | htn
    · rw [pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]
      exact hlat t (by omega) i j hij
    · have ht' : t = n + 1 := by omega
      subst ht'
      rw [pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam k i hk,
        update_pred_sub lam k j hk]
      exact hlam hij
  · rw [pcnt_snoc_last, hcont, update_pred_sub lam k i hk]

theorem exists_word {m : ℕ} (h1 : CombPcntAppend.Statement) (μ : Fin m → ℕ) (hμ : Antitone μ) :
    ∀ (q : ℕ) (lam : Fin m → ℕ), Antitone lam → (∀ i, μ i ≤ lam i) →
      ∑ i, lam i = ∑ i, μ i + q →
        ∃ s : Fin q → Fin m, ∀ n, ∀ w ∈ latticeWords n μ,
          Fin.append w s ∈ latticeWords (n + q) lam := by
  intro q
  induction q with
  | zero =>
    intro lam _ hle hsum
    have heq : ∀ i, μ i = lam i := by
      have := (Finset.sum_eq_sum_iff_of_le (s := univ) (fun i _ => hle i)).mp (by simpa using hsum.symm)
      exact fun i => this i (mem_univ i)
    refine ⟨Fin.elim0, fun n w hw => ?_⟩
    simp only [latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
    have hp : ∀ t i, pcnt (Fin.append w (Fin.elim0 : Fin 0 → Fin m)) t i = pcnt w t i := by
      intro t i
      rw [h1]
      have : pcnt (Fin.elim0 : Fin 0 → Fin m) (t - n) i = 0 := by unfold pcnt; simp
      omega
    refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
    · rw [hp, hp]; exact hw.1 t ht i j hij
    · rw [hp, Nat.add_zero, hw.2 i, heq i]
  | succ q ih =>
    intro lam hlam hle hsum
    have hne : (univ.filter (fun i => μ i < lam i)).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      have : ∑ i, lam i ≤ ∑ i, μ i :=
        Finset.sum_le_sum fun i _ => not_lt.mp (hemp (mem_univ i))
      omega
    obtain ⟨k, hk, hkmax⟩ : ∃ k, μ k < lam k ∧ ∀ j, μ j < lam j → j ≤ k :=
      ⟨_, (mem_filter.mp (max'_mem _ hne)).2,
        fun j hj => le_max' _ j (mem_filter.mpr ⟨mem_univ j, hj⟩)⟩
    have hgt : ∀ j, k < j → lam j = μ j := by
      intro j hj
      by_contra hne'
      exact absurd (hkmax j (lt_of_le_of_ne (hle j) (Ne.symm hne'))) (not_le.mpr hj)
    have hanti : Antitone (Function.update lam k (lam k - 1)) := by
      intro i j hij
      by_cases hik : i = k <;> by_cases hjk : j = k
      · rw [hik, hjk]
      · rw [hik, Function.update_self, Function.update_of_ne hjk]
        have hkj : k < j := lt_of_le_of_ne (hik ▸ hij) (Ne.symm hjk)
        rw [hgt j hkj]
        have := hμ (hik ▸ hij)
        omega
      · rw [hjk, Function.update_self, Function.update_of_ne hik]
        have := hlam (hjk ▸ hij)
        omega
      · rw [Function.update_of_ne hik, Function.update_of_ne hjk]
        exact hlam hij
    have hle' : ∀ i, μ i ≤ Function.update lam k (lam k - 1) i := by
      intro i
      by_cases hik : i = k
      · rw [hik, Function.update_self]; omega
      · rw [Function.update_of_ne hik]; exact hle i
    have hsum' : ∑ i, Function.update lam k (lam k - 1) i = ∑ i, μ i + q := by
      have h2 : ∀ i, Function.update lam k (lam k - 1) i + (if k = i then 1 else 0) = lam i :=
        fun i => update_pred_sub lam k i (by omega)
      have : ∑ i, lam i = ∑ i, Function.update lam k (lam k - 1) i + 1 := by
        rw [← Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_add_distrib, Finset.sum_ite_eq]
        simp
      omega
    obtain ⟨s', hs'⟩ := ih _ hanti hle' hsum'
    refine ⟨Fin.snoc s' k, fun n w hw => ?_⟩
    rw [Fin.append_snoc]
    exact snoc_mem lam hlam k (by omega) _ (hs' n w hw)

theorem proof (h1 : CombPcntAppend.Statement) : CombExtendWord.Statement := by
  intro m n q μ lam hμ hlam hle hsum
  obtain ⟨s, hs⟩ := exists_word h1 μ hμ q lam hlam hle hsum
  exact ⟨s, hs n⟩

end CombExtendWord

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem Comb.pcnt_succ_self {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) :
    pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1 := by
  unfold pcnt
  have hins : (univ.filter (fun s : Fin n => (s : ℕ) < (t : ℕ) + 1 ∧ w s = w t)) =
      insert t (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = w t)) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl (Fin.ext h)
    · rintro (h | ⟨h1, h2⟩)
      · subst h; exact ⟨Nat.lt_succ_self _, rfl⟩
      · exact ⟨Nat.lt_succ_of_lt h1, h2⟩
  rw [hins, card_insert_of_notMem]
  simp

theorem CombCellOfWordMono.proof : CombCellOfWordMono.Statement := by
  intro m n w hw s t hrow hcol
  by_contra hst
  rw [not_le] at hst
  simp only [cellOfWord] at hrow hcol
  have h1 : pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1 := Comb.pcnt_succ_self w t
  have h2 : pcnt w ((t : ℕ) + 1) (w s) ≤ pcnt w s (w s) :=
    pcnt_le_of_le w (Nat.succ_le_of_lt hst) (w s)
  have h3 : pcnt w ((t : ℕ) + 1) (w t) ≤ pcnt w ((t : ℕ) + 1) (w s) :=
    hw _ (by have := s.isLt; have : (t : ℕ) < s := hst; omega) (w s) (w t) hrow
  omega

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

theorem CombWordOfTableau.proof (h1 : CombTableauRowCount.Statement)
    (h2 : CombTableauRowPrefix.Statement) (h3 : CombTableauRowLattice.Statement)
    (h4 : CombYoungRowCard.Statement) : CombWordOfTableau.Statement := by
  intro m lam hlam T hT
  refine ⟨?_, fun t => ?_⟩
  · simp only [latticeWords, mem_filter, mem_univ, true_and]
    refine ⟨fun t _ i j hij => ?_, fun i => ?_⟩
    · rw [h1 m lam T t j, h1 m lam T t i]
      exact h3 m lam hlam T hT t i j hij
    · rw [h1 m lam T _ i, ← h4 m lam i]
      congr 1
      exact Finset.filter_congr fun p _ => by simp [(T p).isLt]
  · unfold cellOfWord
    refine Prod.ext rfl ?_
    show pcnt (rowWord T) (t : ℕ) ((T.symm t).1.1) = (T.symm t).1.2
    rw [h1 m lam T t _]
    exact h2 m lam T hT t

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowLattice.proof : CombTableauRowLattice.Statement := by
  classical
  intro m lam hlam T hT t i j hij
  have hmem : ∀ p : youngCells lam, p.1.1 = j → (i, p.1.2) ∈ youngCells lam := by
    intro p hp
    have hp' := p.2
    simp only [youngCells, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_range] at hp' ⊢
    have h1 : p.1.2 < lam i := by
      rw [hp] at hp'
      exact lt_of_lt_of_le hp'.2 (hlam hij)
    refine ⟨lt_of_lt_of_le h1 ?_, h1⟩
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (lam k)) (Finset.mem_univ i)
  let f : youngCells lam → youngCells lam := fun p =>
    if h : p.1.1 = j then ⟨(i, p.1.2), hmem p h⟩ else p
  have hf : ∀ p : youngCells lam, ∀ h : p.1.1 = j, f p = ⟨(i, p.1.2), hmem p h⟩ := by
    intro p h
    simp only [f, dif_pos h]
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [hf p hp.1]
    refine ⟨rfl, lt_of_le_of_lt ?_ hp.2⟩
    have := hT ⟨(i, p.1.2), hmem p hp.1⟩ p (by simpa [hp.1] using hij) le_rfl
    exact_mod_cast this
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
    rw [hf p hp.1, hf q hq.1] at hpq
    have h2 : p.1.2 = q.1.2 := by
      have := congrArg (fun x : youngCells lam => x.1.2) hpq
      simpa using this
    apply Subtype.ext
    exact Prod.ext (hp.1.trans hq.1.symm) h2

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem CombTableauRowPrefix.proof : CombTableauRowPrefix.Statement := by
  intro m lam T hT t
  set c := T.symm t with hc
  have hTc : T c = t := by simp [hc]
  have key : ∀ p : youngCells lam, p.1.1 = c.1.1 →
      ((T p : ℕ) < (t : ℕ) ↔ p.1.2 < c.1.2) := by
    intro p hp
    constructor
    · intro hlt
      by_contra hle'
      have hle := not_lt.mp hle'
      have h := hT c p hp.symm.le hle
      rw [hTc] at h
      exact absurd hlt (not_lt.mpr (Fin.le_def.mp h))
    · intro hlt
      have hle : T p ≤ T c := hT p c hp.le hlt.le
      have hne : p ≠ c := by
        intro h
        rw [h] at hlt
        exact lt_irrefl _ hlt
      have hne' : T p ≠ T c := fun h => hne (T.injective h)
      rw [hTc] at hle hne'
      exact Fin.lt_def.mp (lt_of_le_of_ne hle hne')
  have hcmem : c.1 ∈ youngCells lam := c.2
  simp only [youngCells, mem_filter, mem_product, mem_univ, true_and, mem_range] at hcmem
  rw [show (univ.filter fun p : youngCells lam => p.1.1 = c.1.1 ∧ (T p : ℕ) < (t : ℕ)) =
      univ.filter fun p : youngCells lam => p.1.1 = c.1.1 ∧ p.1.2 < c.1.2 from
    filter_congr fun p _ => and_congr_right (key p)]
  refine Eq.trans ?_ (card_range c.1.2)
  refine card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    exact mem_range.mpr hp.2
  · intro p hp q hq hpq
    simp only [mem_filter, mem_univ, true_and] at hp hq
    exact Subtype.ext (Prod.ext (hp.1.trans hq.1.symm) hpq)
  · intro k hk
    rw [mem_range] at hk
    refine ⟨⟨(c.1.1, k), ?_⟩, ?_, rfl⟩
    · simp only [youngCells, mem_filter, mem_product, mem_univ, true_and, mem_range]
      exact ⟨by omega, by omega⟩
    · simp [hk]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

noncomputable section

theorem CombTableEqWords.proof (h1 : CombCardYoungCells.Statement)
    (h2 : CombWordOfTableau.Statement) (h3 : CombTableauOfWord.Statement) :
    CombTableEqWords.Statement := by
  intro m lam hlam
  classical
  let e : {T : youngCells lam ≃ Fin (youngCells lam).card // IsStandard T} ≃
      latticeWords (youngCells lam).card lam :=
    { toFun := fun T => ⟨rowWord T.1, (h2 m lam hlam T.1 T.2).1⟩
      invFun := fun w => ⟨Classical.choose (h3 m lam hlam w.1 w.2),
        (Classical.choose_spec (h3 m lam hlam w.1 w.2)).1⟩
      left_inv := by
        rintro ⟨T, hT⟩
        have hs := Classical.choose_spec (h3 m lam hlam (rowWord T) (h2 m lam hlam T hT).1)
        apply Subtype.ext
        have k1 := (h2 m lam hlam _ hs.1).2
        have k2 := (h2 m lam hlam T hT).2
        have hsymm : (Classical.choose
            (h3 m lam hlam (rowWord T) (h2 m lam hlam T hT).1)).symm = T.symm := by
          refine Equiv.ext fun t => Subtype.ext ?_
          rw [← k1 t, ← k2 t, hs.2]
        simpa using congrArg Equiv.symm hsymm
      right_inv := by
        rintro ⟨w, hw⟩
        exact Subtype.ext (Classical.choose_spec (h3 m lam hlam w hw)).2 }
  show Nat.card {T : youngCells lam ≃ Fin (youngCells lam).card // IsStandard T} = _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, h1 m lam]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

noncomputable section

theorem symmetricGroupCharacter_eq_cf {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) :
    symmetricGroupCharacter lam rho =
      cf (fun i => lam i + stair m i) (alternantPsum m rho) := rfl

theorem CharacterAtIdentity.proof (h1 : CombTableEqWords.Statement)
    (h2 : CombCfAtStair.Statement) : CharacterAtIdentity.Statement := by
  intro m lam hlam
  rw [symmetricGroupCharacter_eq_cf, h2 m (∑ i, lam i) lam hlam, h1 m lam hlam]

end

end GroundTheory.Heights₂.Heights.RestTerms
end
