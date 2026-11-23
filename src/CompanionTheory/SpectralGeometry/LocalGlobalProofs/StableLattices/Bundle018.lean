module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset
open CompanionTheory.D.DSIC

namespace GlobalTheory.CompanionTheory.GamDomProof

variable {n : ℕ}

theorem card_four (ε : Fin n → Bool) (a : Fin n) :
    ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) + (univ.filter fun b => b < a ∧ ε b = ε a).card
      + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card + 1 = n := by
  have h1 : (1 : ℝ) = ∑ b : Fin n, if b = a then (1 : ℝ) else 0 := by simp
  have h2 : (n : ℝ) = ∑ _b : Fin n, (1 : ℝ) := by simp
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [h2]
  nth_rewrite 5 [h1]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne', e]
  · simp [h]
  · by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne, e]

theorem card_fst (ε : Fin n → Bool) (a : Fin n) :
    ((A1 ε).filter fun i => i.1.1 = a).card =
      if ε a = true then (univ.filter fun b => b < a ∧ ε b ≠ ε a).card else 0 := by
  split_ifs with h
  · refine card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi hx hy ⊢
      obtain ⟨h1, rfl⟩ := hi
      exact ⟨h1, by simp [hx, hy]⟩
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi ⟨⟨x', y'⟩, hx', hy'⟩ hi' e
      simp only [A1, mem_filter, mem_univ, true_and] at hi hi' e
      apply Subtype.ext
      simp [hi.2, hi'.2, e]
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      refine ⟨⟨(a, b), h, by simpa [h] using hb.2⟩, ?_, rfl⟩
      simp [A1, hb.1]
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨⟨x, y⟩, hx, hy⟩ _ e
    simp only at e hx
    exact h (e ▸ hx)

theorem card_snd (ε : Fin n → Bool) (a : Fin n) :
    ((A1 ε).filter fun i => i.1.2 = a).card =
      if ε a = true then 0 else (univ.filter fun b => a < b ∧ ε b ≠ ε a).card := by
  split_ifs with h
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨⟨x, y⟩, hx, hy⟩ _ e
    simp only at e hy
    rw [e, h] at hy
    exact absurd hy (by simp)
  · have h' : ε a = false := by simpa using h
    refine card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi hx hy ⊢
      obtain ⟨h1, rfl⟩ := hi
      exact ⟨h1, by simp [hx, hy]⟩
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi ⟨⟨x', y'⟩, hx', hy'⟩ hi' e
      simp only [A1, mem_filter, mem_univ, true_and] at hi hi' e
      apply Subtype.ext
      simp [hi.2, hi'.2, e]
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      refine ⟨⟨(b, a), by simpa [h'] using hb.2, h'⟩, ?_, rfl⟩
      simp [A1, hb.1]

theorem card_other (ε : Fin n → Bool) (a : Fin n) (h : ε a = true) :
    (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
      = nb ε false := by
  simp only [nb, card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h' | h' | h'
  · cases e : ε b <;> simp [h, h', h'.not_gt]
  · simp [← h', h]
  · cases e : ε b <;> simp [h, h', h'.not_gt]

theorem gam_eq (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    gam ε lam a = lam a - ((n : ℝ) - 1) / 2 + (univ.filter fun b => b < a ∧ ε b = ε a).card
      + (if ε a = true then (nb ε false : ℝ) else 0) := by
  have h4 := card_four ε a
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, wtA, Pi.add_apply, Pi.sub_apply,
    card_fst, card_snd]
  split_ifs with h
  · rw [← card_other ε a h]
    push_cast
    linarith
  · push_cast
    linarith

theorem pos_le (ε : Fin n → Bool) (m : Fin n → ℤ) (hm : StrictAnti m) (c d : Fin n) (hcd : c < d)
    (e : ε c = ε d) :
    m d + (univ.filter fun b => b < d ∧ ε b = ε d).card ≤
      m c + (univ.filter fun b => b < c ∧ ε b = ε c).card := by
  have h1 : (univ.filter fun b => b < d ∧ ε b = ε d).card ≤
      (univ.filter fun b => b < c ∧ ε b = ε c).card + (Ico c d).card := by
    refine le_trans (card_le_card ?_) (card_union_le _ _)
    intro b hb
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_Ico] at hb ⊢
    rcases lt_or_ge b c with h | h
    · exact Or.inl ⟨h, hb.2.trans e.symm⟩
    · exact Or.inr ⟨h, hb.1⟩
  have h2 : (Ico c d).card ≤ (Ioc (m d) (m c)).card := by
    refine card_le_card_of_injOn m ?_ hm.injective.injOn
    intro b hb
    simp only [coe_Ico, coe_Ioc, Set.mem_Ico, Set.mem_Ioc] at hb ⊢
    exact ⟨hm hb.2, hm.antitone hb.1⟩
  rw [Int.card_Ioc] at h2
  have h3 := hm hcd
  omega

theorem gamDom : CompanionTheory.D.DSIC.GamDom := by
  intro n ε lam ⟨hanti, hint⟩
  choose m hm using hint
  have hm' : StrictAnti m := by
    intro a b hab
    have := hanti hab
    have h : (m b : ℝ) < m a := by rw [← hm, ← hm]; linarith
    exact_mod_cast h
  refine ⟨fun a => m a + (univ.filter fun b => b < a ∧ ε b = ε a).card
    + (if ε a = true then (nb ε false : ℤ) else 0), fun a => ?_, fun c d hcd e => ?_⟩
  · rw [gam_eq, hm]
    push_cast
    rfl
  · have := pos_le ε m hm' c d hcd e
    have h2 : (if ε d = true then (nb ε false : ℤ) else 0) = (if ε c = true then (nb ε false : ℤ) else 0) := by
      rw [e]
    simp only [h2]
    linarith

end GlobalTheory.CompanionTheory.GamDomProof
end

section

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.GopEntries

open CompanionTheory.D.DSIC

variable {n : ℕ} {ε : Fin n → Bool}

def sgR (i : NC ε) (A : Finset (NC ε)) : ℝ := (-1) ^ (A.filter fun j => key j < key i).card

def hh (i j : NC ε) (A B : Finset (NC ε)) : ℝ :=
  if i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j then sgR i (A.erase i) * sgR j (B.erase j) else 0

def coef (c d : Fin n) (i j : NC ε) : ℝ :=
  (if i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2 then 1 else 0) -
    (if i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1 then 1 else 0)

def gg (c d : Fin n) (A B : Finset (NC ε)) : ℝ := ∑ i : NC ε, ∑ j : NC ε, coef c d i j * hh i j A B

lemma sg_eq (i : NC ε) (A : Finset (NC ε)) : sg i A = (sgR i A : ℂ) := by
  simp [sg, sgR]

lemma sgR_erase (i : NC ε) (A : Finset (NC ε)) : sgR i (A.erase i) = sgR i A := by
  unfold sgR
  congr 2
  ext j
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨?_, h⟩, h'⟩
    rintro rfl
    exact lt_irrefl _ h'

lemma sgR_mul_self (i : NC ε) (A : Finset (NC ε)) : sgR i A * sgR i A = 1 := by
  unfold sgR
  rw [← mul_pow]; simp

lemma hh_symm (i j : NC ε) (A B : Finset (NC ε)) : hh i j A B = hh j i B A := by
  unfold hh
  by_cases h : i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, mul_comm]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩)]

lemma coef_symm (c d : Fin n) (i j : NC ε) : coef c d i j = coef d c j i := by
  unfold coef
  congr 1
  · exact if_congr ⟨fun h => ⟨h.2.1, h.1, h.2.2.symm⟩, fun h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩ rfl rfl
  · exact if_congr ⟨fun h => ⟨h.2.1, h.1, h.2.2.symm⟩, fun h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩ rfl rfl

lemma cre_ann_apply {V : Type} [AddCommGroup V] [Module ℂ V] (i j : NC ε) (x : Ch ε V)
    (A : Finset (NC ε)) :
    (cre i * ann j : Module.End ℂ (Ch ε V)) x A = ∑ B, (hh i j A B : ℂ) • x B := by
  change (if i ∈ A then sg i A • (if j ∈ A.erase i then 0 else
    sg j (A.erase i) • x (insert j (A.erase i))) else 0) = _
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    by_cases hj : j ∈ A.erase i
    · rw [if_pos hj, smul_zero]
      symm
      refine Finset.sum_eq_zero fun B _ => ?_
      have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := by
        rintro ⟨_, _, h⟩
        rw [h] at hj
        exact Finset.notMem_erase _ _ hj
      simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]
    · rw [if_neg hj, Finset.sum_eq_single (insert j (A.erase i))]
      · have : i ∈ A ∧ j ∈ insert j (A.erase i) ∧ A.erase i = (insert j (A.erase i)).erase j :=
          ⟨hi, mem_insert_self _ _, (Finset.erase_insert hj).symm⟩
        rw [hh, if_pos this, Finset.erase_insert hj, sgR_erase, smul_smul, sg_eq, sg_eq,
          Complex.ofReal_mul]
      · intro B _ hB
        have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := by
          rintro ⟨_, h1, h⟩
          apply hB
          rw [h, Finset.insert_erase h1]
        simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]
      · intro h; exact absurd (mem_univ _) h
  · rw [if_neg hi]
    symm
    refine Finset.sum_eq_zero fun B _ => ?_
    have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := fun h => hi h.1
    simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]

lemma Gop_apply {V : Type} [AddCommGroup V] [Module ℂ V] (c d : Fin n) (x : Ch ε V)
    (A : Finset (NC ε)) : Gop ε c d x A = ∑ B, (gg c d A B : ℂ) • x B := by
  have hc : ∀ i j : NC ε, ((if i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2 then 1 else 0) -
      (if i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1 then 1 else 0) : ℂ) = (coef c d i j : ℂ) := by
    intro i j
    unfold coef
    split_ifs <;> simp
  unfold Gop gg
  simp only [hc, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    cre_ann_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_smul, Finset.smul_sum,
    smul_smul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma wtA_erase (i : NC ε) (A : Finset (NC ε)) (hi : i ∈ A) :
    wtA A = wtA (A.erase i) + Pi.single i.1.1 1 - Pi.single i.1.2 1 := by
  funext c
  have key : ∀ (p : NC ε → Prop) [DecidablePred p],
      ((A.filter p).card : ℝ) = (((A.erase i).filter p).card : ℝ) + if p i then 1 else 0 := by
    intro p _
    conv_lhs => rw [← Finset.insert_erase hi, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]; simp
    · simp
  simp only [wtA, Pi.sub_apply, Pi.add_apply, Pi.single_apply]
  rw [key (fun i => i.1.1 = c), key (fun i => i.1.2 = c)]
  simp only [eq_comm (a := c)]
  ring

lemma exists_of_ne {c d : Fin n} {A B : Finset (NC ε)} (h : gg c d A B ≠ 0) :
    ∃ i j : NC ε, ((i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2) ∨ (i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1)) ∧
      i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j := by
  obtain ⟨i, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨j, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨i, j, ?_, ?_⟩
  · by_contra h'
    rw [not_or] at h'
    exact left_ne_zero_of_mul h (by rw [coef, if_neg h'.1, if_neg h'.2, sub_zero])
  · by_contra h'
    exact right_ne_zero_of_mul h (by rw [hh, if_neg h'])

lemma gg_diag (c : Fin n) (A B : Finset (NC ε)) : gg c c A B = if A = B then wtA A c else 0 := by
  have h1 : ∀ i : NC ε, ∑ j : NC ε, coef c c i j * hh i j A B = coef c c i i * hh i i A B := by
    intro i
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (mem_univ _) h)
    have e1 : ¬ (i.1.1 = c ∧ j.1.1 = c ∧ i.1.2 = j.1.2) := by
      rintro ⟨a, b, e⟩
      exact hj (Subtype.ext (Prod.ext (b.trans a.symm) e.symm))
    have e2 : ¬ (i.1.2 = c ∧ j.1.2 = c ∧ i.1.1 = j.1.1) := by
      rintro ⟨a, b, e⟩
      exact hj (Subtype.ext (Prod.ext e.symm (b.trans a.symm)))
    rw [coef, if_neg e1, if_neg e2, sub_zero, zero_mul]
  unfold gg
  simp only [h1]
  split_ifs with h
  · subst h
    have h2 : ∀ i : NC ε, hh i i A A = if i ∈ A then 1 else 0 := by
      intro i
      unfold hh
      by_cases hi : i ∈ A
      · simp [hi, sgR_mul_self]
      · simp [hi]
    simp only [h2, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp [coef, wtA, Finset.sum_sub_distrib]
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : ¬ (i ∈ A ∧ i ∈ B ∧ A.erase i = B.erase i) := by
      rintro ⟨a, b, e⟩
      apply h
      rw [← Finset.insert_erase a, e, Finset.insert_erase b]
    rw [hh, if_neg this, mul_zero]

theorem gFacts : GFacts := by
  intro n ε
  refine ⟨gg, fun V _ _ c d x A => Gop_apply c d x A, fun c d A B => ?_, fun c d A B h => ?_,
    gg_diag, fun c d A hdc => ?_⟩
  · unfold gg
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [coef_symm, hh_symm]
  · obtain ⟨i, j, hc, hi, hj, e⟩ := exists_of_ne h
    refine ⟨?_, ?_⟩
    · rw [← Finset.card_erase_add_one hi, e, Finset.card_erase_add_one hj]
    · rw [wtA_erase i A hi, wtA_erase j B hj, e]
      rcases hc with ⟨a, b, f⟩ | ⟨a, b, f⟩
      · rw [a, b, f]; abel
      · rw [a, b, f]; abel
  · by_contra h
    obtain ⟨i, j, hc, hi, hj, e⟩ := exists_of_ne h
    have hn : i ∉ (A1 ε).erase j := e ▸ Finset.notMem_erase i A
    apply hn
    simp only [A1, mem_filter, mem_univ, true_and, mem_erase] at hj ⊢
    rcases hc with ⟨a, b, f⟩ | ⟨a, b, f⟩
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact hdc.ne (b.symm.trans a)
      · rw [a, f]; rw [b] at hj; exact hj.trans hdc
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact hdc.ne (a.symm.trans b)
      · rw [a, f]; rw [b] at hj; exact hdc.trans hj

end GlobalTheory.CompanionTheory.GopEntries
end
end

section

open Formalism.REAL CompanionTheory.D.DSIC

noncomputable section

namespace GlobalTheory.CompanionTheory.DSCoreSub

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}

theorem ofFn_prod_intertwine (φ : V' →ₗ[ℂ] V) :
    ∀ {t : ℕ} (f' : Fin t → Module.End ℂ V') (f : Fin t → Module.End ℂ V),
      (∀ k x, φ (f' k x) = f k (φ x)) → ∀ x, φ ((List.ofFn f').prod x) = (List.ofFn f).prod (φ x)
  | 0, _, _, _, x => by simp
  | t + 1, f', f, h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h, ofFn_prod_intertwine φ _ (fun k => f k.succ) (fun k => h k.succ)]

theorem qdet_intertwine (φ : V' →ₗ[ℂ] V) (E' : Fin n → Fin n → Module.End ℂ V')
    (E : Fin n → Fin n → Module.End ℂ V) (h : ∀ a b x, φ (E' a b x) = E a b (φ x)) (u : ℂ) (x : V') :
    φ (qdet E' u x) = qdet E u (φ x) := by
  unfold qdet qminor

  simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply, Module.End.intCast_apply, map_zsmul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine ofFn_prod_intertwine φ _ _ (fun k y => ?_) x
  unfold Tm
  split_ifs <;> simp [h, Module.algebraMap_end_apply]

theorem algCoreSub_of_algCore : AlgCore → AlgCoreSub := by
  intro hA n ε lam V _ _ E V₀ v S hlam hgl hun hst hS hv hfd hK hvS hmin Y
  let E' : Fin n → Fin n → Module.End ℂ V₀ := fun a b => (E a b).restrict (hst a b)
  have hE : ∀ a b (x : V₀), ((E' a b x : V₀) : V) = E a b x := fun a b x => rfl
  have hhi : ∀ (μ : Fin n → ℝ) (x : V₀), KHighest ε E' μ x ↔ KHighest ε E μ (x : V) := by
    intro μ x
    unfold KHighest IsWeight
    simp only [Subtype.ext_iff, hE, Submodule.coe_smul, Submodule.coe_zero]
  have hgl' : GlRel E' := by
    intro a b c d
    ext x
    have := LinearMap.congr_fun (hgl a b c d) (x : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hE] at this ⊢
    rw [this]
    split_ifs <;> simp [hE]
  have hun' : IsUnitary ε E' := fun a b x y => hun a b x y
  haveI : FiniteDimensional ℂ (S.comap V₀.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hS).symm.finiteDimensional
  have key := hA n ε lam V₀ E' ⟨v, hS hvS⟩ (S.comap V₀.subtype) hlam hgl' hun' ((hhi _ _).2 hv) inferInstance
    (fun a b hab x hx => hK a b hab x hx) hvS
    (fun μ x hx hμ => hmin μ x x.2 (fun h0 => hx (Subtype.ext h0)) ((hhi μ x).1 hμ)) Y
  have h2 := qdet_intertwine V₀.subtype E' E hE (Y + ((n : ℂ) - 1) / 2) ⟨v, hS hvS⟩
  rw [key] at h2
  simpa using h2.symm

end GlobalTheory.CompanionTheory.DSCoreSub
end
end
