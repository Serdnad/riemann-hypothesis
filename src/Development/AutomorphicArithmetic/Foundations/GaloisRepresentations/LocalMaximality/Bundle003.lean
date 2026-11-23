module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
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
import Mathlib.Tactic.Lemma
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

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section SlopeTestRemainingChoices
variable {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]

private lemma wd_apply' (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]

private lemma mem_acxC {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E} {n : ℤ}
    {c : Finset σ → E} :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) := by
  simp [acx, Submodule.mem_pi]

private lemma wd_wOn_mem {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    (h : WOk A w) (P : Finset σ) {n : ℤ} {c : Finset σ → E} (hc : c ∈ (acx A w).C n) :
    wd (wOn P w) c ∈ (acx A w).C (n + 1) := by
  rw [mem_acxC] at hc ⊢
  intro s
  rw [wd_apply']
  by_cases hs : (s.card : ℤ) = n + 1
  · rw [if_pos hs]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_of_tower_mem _ _ ?_
    have hcard : ((s.erase i).card : ℤ) = n := by
      have := Finset.card_erase_add_one hi
      omega
    have hmem := hc (s.erase i)
    rw [if_pos hcard] at hmem
    unfold wOn
    split_ifs
    · have := h.2 (s.erase i) i (by simp) _ hmem
      rwa [Finset.insert_erase hi] at this
    · rw [LinearMap.zero_apply]
      exact Submodule.zero_mem _
  · rw [if_neg hs, Submodule.mem_bot]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : ¬ ((s.erase i).card : ℤ) = n := by
      have := Finset.card_erase_add_one hi
      omega
    have hmem := hc (s.erase i)
    rw [if_neg hcard, Submodule.mem_bot] at hmem
    rw [hmem, map_zero, smul_zero]

private lemma wd_compl_lev [Fintype σ] {Q : Finset σ} {w : σ → Module.End ℂ E} {m : ℤ}
    {c : Finset σ → E} (h : Lev Q (· = m) c) : Lev Q (· = m) (wd (wOn Qᶜ w) c) := by
  intro s hs
  rw [wd_apply']
  refine Finset.sum_eq_zero fun i hi => ?_
  unfold wOn
  split_ifs with hiQ
  · rw [Finset.mem_compl] at hiQ
    have hQ : (s.erase i) ∩ Q = s ∩ Q := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hx⟩, hxQ⟩
        exact ⟨hx, hxQ⟩
      · rintro ⟨hx, hxQ⟩
        exact ⟨⟨fun hxi => hiQ (by rw [← hxi]; exact hxQ), hx⟩, hxQ⟩
    rw [h (s.erase i) (by rw [hQ]; exact hs), map_zero, smul_zero]
  · rw [LinearMap.zero_apply, smul_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.productCup_of_system.filtrationCocycleLiftCriterion_of_wdBasic :
    WdBasic → FiltrationCocycleLiftCriterion := by
  rintro hB σ E _ _ _ _ A w Q d n hW hQE c0 hc0 hl0 hq0 ⟨y, hy, hly, hdy⟩
  have hcw : ∀ P P' : Finset σ, ∀ i j, Commute (wOn P w i) (wOn P' w j) := by
    intro P P' i j
    unfold wOn
    split_ifs
    all_goals first
      | exact hW.1 i j
      | exact Commute.zero_right _
      | exact Commute.zero_left _
  have hsplit : ∀ x, wd w x = wd (wOn Q w) x + wd (wOn Qᶜ w) x := by
    intro x
    have hw : w = wOn Q w + wOn Qᶜ w := by
      funext i
      by_cases hi : i ∈ Q <;> simp [wOn, hi]
    conv_lhs => rw [hw]
    rw [(hB σ E A (wOn Q w)).2.2.1 (wOn Qᶜ w), LinearMap.add_apply]
  have hRR : ∀ x, wd (wOn Qᶜ w) (wd (wOn Qᶜ w) x) = 0 := (hB σ E A (wOn Qᶜ w)).1 (hcw Qᶜ Qᶜ)
  have hQR : ∀ x, wd (wOn Q w) (wd (wOn Qᶜ w) x) + wd (wOn Qᶜ w) (wd (wOn Q w) x) = 0 :=
    (hB σ E A (wOn Q w)).2.2.2.1 (wOn Qᶜ w) (hcw Q Qᶜ) (fun i => by by_cases hi : i ∈ Q <;> simp [wOn, hi])
  have levZero : ∀ (m : ℤ) (x : Finset σ → E), m < 0 → Lev Q (· = m) x → x = 0 := by
    intro m x hm hx
    funext s
    exact hx s (fun h => by
      have h' : (((s ∩ Q).card : ℕ) : ℤ) = m := h
      omega)
  have key : ∀ j : ℕ, ∀ m : ℤ, m < j → m < d → ∀ ck yk : Finset σ → E,
      ck ∈ (acx A w).C n → Lev Q (· < d) (ck - c0) → yk ∈ (acx A w).C n → Lev Q (· = m) yk →
      wd w ck = -wd (wOn Qᶜ w) yk → wd (wOn Q w) (wd (wOn Qᶜ w) yk) = 0 →
      ∃ c ∈ (acx A w).Z n, Lev Q (· < d) (c - c0) := by
    intro j
    induction j with
    | zero =>
      intro m hm _ ck yk hck hlk _ hly hd _
      have hy0 := levZero m yk (by exact_mod_cast hm) hly
      refine ⟨ck, ?_, hlk⟩
      show ck ∈ (acx A w).C n ⊓ LinearMap.ker (acx A w).D
      refine Submodule.mem_inf.2 ⟨hck, LinearMap.mem_ker.2 ?_⟩
      show wd w ck = 0
      rw [hd, hy0, map_zero, neg_zero]
    | succ j ih =>
      intro m hm hmd ck yk hck hlk hyk hly hd hqr
      have hmem : -wd (wOn Qᶜ w) yk ∈ (acx A w).C (n + 1) :=
        Submodule.neg_mem _ (wd_wOn_mem hW Qᶜ hyk)
      have hlev : Lev Q (· = m) (-wd (wOn Qᶜ w) yk) := by
        intro s hs
        rw [Pi.neg_apply, wd_compl_lev hly s hs, neg_zero]
      have hdq : wd (wOn Q w) (-wd (wOn Qᶜ w) yk) = 0 := by rw [map_neg, hqr, neg_zero]
      obtain ⟨y', hy', hly', hdy'⟩ := hQE (n + 1) m hmd _ hmem hlev hdq
      rw [add_sub_cancel_right] at hy'
      refine ih (m - 1) (by push_cast at hm; omega) (by omega) (ck - y') y'
        (Submodule.sub_mem _ hck hy') ?_ hy' hly' ?_ ?_
      · intro s hs
        have h1 := hlk s hs
        have h2 := hly' s (fun h => hs (by
          have h' : (((s ∩ Q).card : ℕ) : ℤ) = m - 1 := h
          show (((s ∩ Q).card : ℕ) : ℤ) < d
          omega))
        simp only [Pi.sub_apply] at h1 ⊢
        rw [h2, sub_zero]
        exact h1
      · rw [map_sub, hd, hsplit y', hdy']
        abel
      · have := hQR y'
        rw [hdy', map_neg, hRR, neg_zero, add_zero] at this
        exact this
  refine key d.toNat (d - 1) (by have := Int.self_le_toNat d; omega) (by omega) (c0 - y) y
    (Submodule.sub_mem _ hc0 hy) ?_ hy hly ?_ ?_
  · intro s hs
    have h2 := hly s (fun h => hs (by
      have h' : (((s ∩ Q).card : ℕ) : ℤ) = d - 1 := h
      show (((s ∩ Q).card : ℕ) : ℤ) < d
      omega))
    simp only [Pi.sub_apply]
    rw [h2]
    abel
  · rw [map_sub, hsplit c0, hsplit y, hq0, hdy]
    abel
  · have := hQR y
    rw [hdy, hRR, add_zero] at this
    exact this
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)

private lemma card_uni {β κ : Type} [LinearOrder β] [LinearOrder κ] (I : Finset β) (J : Finset κ) :
    (uni I J).card = I.card + J.card := by
  simp [uni]

private lemma mem_uni {β κ : Type} [LinearOrder β] [LinearOrder κ] (I : Finset β) (J : Finset κ)
    (t : β ⊕ₗ κ) : t ∈ uni I J ↔ (∃ i ∈ I, t = toLex (Sum.inl i)) ∨ ∃ l ∈ J, t = toLex (Sum.inr l) := by
  simp only [uni, Finset.mem_map, Finset.mem_disjSum, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a, (⟨i, hi, rfl⟩ | ⟨l, hl, rfl⟩), rfl⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨l, hl, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact ⟨Sum.inl i, Or.inl ⟨i, hi, rfl⟩, rfl⟩
    · exact ⟨Sum.inr l, Or.inr ⟨l, hl, rfl⟩, rfl⟩

private lemma detC_eq {κ : Type} [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (s : Finset κ)
    (f : Fin p → κ) (hc : s.card = p) (hs : ∀ x, f x ∈ s) (hf : StrictMono f) :
    detC ρ s = (Matrix.of fun a b => ρ (f a) b).det := by
  unfold detC
  rw [dite_eq_left hc, Finset.orderEmbOfFin_unique hc hs hf]

private lemma rowMu_inr (l : Mi d) (m : Fin (d + 1)) : T.rowMu (toLex (Sum.inr l)) m =
    (if m = (ofLex l).1 then (T.X m * T.Y (ofLex l).2 : S) else 0) -
      if m = (ofLex l).2 then (T.X m * T.Y (ofLex l).1 : S) else 0 := rfl

private lemma rowMu_inl (i m : Fin (d + 1)) : T.rowMu (toLex (Sum.inl i)) m =
    (Pi.single i 1 : Fin (d + 1) → S) m := rfl

private lemma rowMu_sum (t : Fin (d + 1) ⊕ₗ Mi d) :
    ∑ b, T.rowMu t b * (1 : Fin (d + 1) → S) b = app (fun _ => (1 : S)) T.mu t := by
  obtain ⟨t, rfl⟩ := toLex.surjective t
  rcases t with i | l
  · simp [rowMu_inl, app]
  · simp only [rowMu_inr, Pi.one_apply, mul_one, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl

private lemma rowMu_null (l : Mi d) :
    ∑ m, T.rowMu (toLex (Sum.inr l)) m * ((T.Y m * (T.X m)⁻¹ : Sˣ) : S) = 0 := by
  simp only [rowMu_inr, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Units.val_mul]
  have h1 : ((T.X (ofLex l).1 : Sˣ) : S) * (((T.X (ofLex l).1)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  have h2 : ((T.X (ofLex l).2 : Sˣ) : S) * (((T.X (ofLex l).2)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  linear_combination ((T.Y (ofLex l).1 : S) * (T.Y (ofLex l).2 : S)) * (h1 - h2)

private lemma detC_left (L : Finset (Mi d)) : detC T.rowMu (uni ∅ L) = 0 := by
  unfold detC
  split_ifs with h
  · set A : Matrix (Fin (d + 1)) (Fin (d + 1)) S :=
      Matrix.of fun a b => T.rowMu ((uni ∅ L).orderEmbOfFin h a) b with hA
    have hAv : A.mulVec (fun m => ((T.Y m * (T.X m)⁻¹ : Sˣ) : S)) = 0 := by
      funext a
      have hmem : (uni ∅ L).orderEmbOfFin h a ∈ uni ∅ L := Finset.orderEmbOfFin_mem _ _ _
      rw [mem_uni] at hmem
      rcases hmem with ⟨i, hi, _⟩ | ⟨l, _, hl⟩
      · simp at hi
      · simp only [Matrix.mulVec, dotProduct, hA, Matrix.of_apply, hl, Pi.zero_apply]
        exact rowMu_null T l
    have h0 := congrArg A.adjugate.mulVec hAv
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h0
    have h1 := congrFun h0 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    exact (Units.mul_left_eq_zero (T.Y 0 * (T.X 0)⁻¹)).1 h1
  · rfl

private lemma detC_univ : detC T.rowMu (uni Finset.univ ∅) = 1 := by
  rw [detC_eq T.rowMu _ (fun a => toLex (Sum.inl a)) (by simp [card_uni])
    (fun x => (mem_uni _ _ _).2 (Or.inl ⟨x, Finset.mem_univ _, rfl⟩))
    (fun a b h => Sum.Lex.inl_strictMono h)]
  have : (Matrix.of fun a b => T.rowMu (toLex (Sum.inl a)) b) = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) S) := by
    ext a b
    simp [rowMu_inl, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_one]

private lemma detC_top : detC T.rowMu (uni {0} (img (dj 0))) =
    (∏ l : Fin d, (T.X l.succ : S)) * (T.Y 0 : S) ^ d := by
  let f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Mi d :=
    Fin.cons (toLex (Sum.inl 0)) fun l => toLex (Sum.inr (dj 0 l))
  have hf0 : f 0 = toLex (Sum.inl 0) := rfl
  have hfs : ∀ l : Fin d, f l.succ = toLex (Sum.inr (dj 0 l)) := fun _ => rfl
  have hmono : StrictMono f := by
    intro a b h
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact absurd h (lt_irrefl _)
      | succ b => rw [hf0, hfs]; exact Sum.Lex.inl_lt_inr _ _
    | succ a =>
      induction b using Fin.cases with
      | zero => exact absurd h (Fin.not_lt_zero _)
      | succ b =>
        rw [hfs, hfs]
        exact Sum.Lex.inr_strictMono ((dj 0).strictMono (Fin.succ_lt_succ_iff.1 h))
  have hmem : ∀ x, f x ∈ uni {0} (img (dj 0)) := by
    intro x
    induction x using Fin.cases with
    | zero => exact (mem_uni _ _ _).2 (Or.inl ⟨0, by simp, rfl⟩)
    | succ l => exact (mem_uni _ _ _).2 (Or.inr ⟨dj 0 l, by simp [img], rfl⟩)
  rw [detC_eq T.rowMu _ f (by simp [card_uni, img, add_comm]) hmem hmono]
  have hrow : ∀ (l : Fin d) (m : Fin (d + 1)), T.rowMu (f l.succ) m =
      (if m = l.succ then (T.X m * T.Y 0 : S) else 0) -
        if m = 0 then (T.X m * T.Y l.succ : S) else 0 := by
    intro l m
    have e1 : (ofLex (dj (0 : Fin (d + 1)) l)).1 = l.succ := by simp [dj]
    have e2 : (ofLex (dj (0 : Fin (d + 1)) l)).2 = 0 := rfl
    rw [hfs, rowMu_inr, e1, e2]
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp only [Matrix.of_apply, hf0, rowMu_inl, Pi.single_eq_same, one_mul, hrow]
    simp [Finset.prod_mul_distrib, Fin.succ_ne_zero]
  · intro i j hij
    have hij' : i < j := hij
    simp only [Matrix.of_apply]
    induction i using Fin.cases with
    | zero =>
      rw [hf0, rowMu_inl]
      simp [Pi.single_apply, (Fin.pos_iff_ne_zero.1 hij')]
    | succ l =>
      rw [hrow]
      have h1 : j ≠ l.succ := ne_of_gt hij'
      have h2 : j ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hij'
      simp [h1, h2]

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.thMu_of :
    Det → ThMu := by
  intro hDet d S E _ _ _ _ T
  refine ⟨?_, detC_left T, detC_univ T, detC_top T⟩
  have h := hDet S S (Algebra.lmul ℂ S) (Fin (d + 1) ⊕ₗ Mi d) (d + 1) T.rowMu 1 1
  simp only [rowMu_sum] at h
  have e : (fun s => (Algebra.lmul ℂ S) (detC T.rowMu s) (1 : S)) = detC T.rowMu := by
    funext s
    simp
  rwa [e] at h
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma exists_of_mem_sm_range {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) (x : E)
    (hx : x ∈ sm act M (Set.range f)) :
    ∃ m : Fin d → E, (∀ j, m j ∈ M) ∧ x = ∑ j, act (f j) (m j) := by
  classical
  let L : (Fin d → M) →ₗ[ℂ] E :=
    ∑ j, ((act (f j) : E →ₗ[ℂ] E) ∘ₗ M.subtype ∘ₗ (LinearMap.proj j : (Fin d → M) →ₗ[ℂ] M))
  have hL : ∀ v, L v = ∑ j, act (f j) (v j : E) := by
    intro v
    simp [L, LinearMap.sum_apply]
  have hle : sm act M (Set.range f) ≤ LinearMap.range L := by
    refine iSup₂_le ?_
    rintro _ ⟨j, rfl⟩ _ ⟨m, hm, rfl⟩
    refine ⟨Pi.single j ⟨m, hm⟩, ?_⟩
    rw [hL, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  obtain ⟨v, rfl⟩ := hle hx
  exact ⟨fun j => (v j : E), fun j => (v j).2, hL v⟩

theorem UpperTheory.Gal.productCup_of_system.koszulTwoInjective_of_gl1 :
    FiltrationBoundaryCriterion → SubQEx → KoszulBoundaryOfComponentMemIdeal := by
  intro gl1 subq S E _ _ _ _ act κ _ _ R M r d e hst hr hKE c hc hsm
  classical
  obtain ⟨m, hm, hcm⟩ := exists_of_mem_sm_range act M (fun j => r (e j)) _ hsm
  have hW : WOk (fun _ : Finset κ => M) (fun l => act (r l)) := by
    refine ⟨fun i j => ?_, fun s i _ x hx => hst _ (hr i) x hx⟩
    show act (r i) * act (r j) = act (r j) * act (r i)
    rw [← map_mul, ← map_mul, mul_comm]
  have hQ := subq S E act κ M r d e hKE
  have hQc : (img e).card = d := by simp [img]
  have hmem : ∀ j, e j ∈ img e := fun j => by simp [img]
  have hcz : ∀ s : Finset κ, (s.card : ℤ) ≠ d → c s = 0 := by
    intro s hs
    have h := hc.1 s (Set.mem_univ s)
    simpa [hs] using h
  have hcard : ∀ j, (((img e).erase (e j)).card : ℤ) = (d : ℤ) - 1 := by
    intro j
    have := j.pos
    rw [Finset.card_erase_of_mem (hmem j), hQc]
    omega
  have hinj : ∀ i j, (img e).erase (e i) = (img e).erase (e j) → i = j := by
    intro i j h
    by_contra hij
    have hne : e i ≠ e j := fun h' => hij (e.injective h')
    have h1 : e i ∈ (img e).erase (e j) := Finset.mem_erase.mpr ⟨hne, hmem i⟩
    rw [← h] at h1
    exact (Finset.notMem_erase _ _) h1
  let y : Finset κ → E := fun s =>
    ∑ j, if s = (img e).erase (e j) then GlobalTheory.cubeSign (img e) (e j) • m j else 0
  have hyv : ∀ j, y ((img e).erase (e j)) = GlobalTheory.cubeSign (img e) (e j) • m j := by
    intro j
    show (∑ i, if (img e).erase (e j) = (img e).erase (e i) then _ else _) = _
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg fun h => hb (hinj _ _ h).symm]
    · simp
  have hy0 : ∀ s, (∀ j, s ≠ (img e).erase (e j)) → y s = 0 := by
    intro s hs
    exact Finset.sum_eq_zero fun j _ => if_neg (hs j)
  have hycard : ∀ s : Finset κ, (s.card : ℤ) ≠ (d : ℤ) - 1 → y s = 0 := by
    intro s hs
    refine hy0 s fun j h => hs ?_
    rw [h, hcard]
  refine gl1 κ E (fun _ => M) (fun l => act (r l)) (img e) d d hW hQ c hc ?_ ?_
  · intro s hs
    exfalso
    apply hs
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := s) (s₂ := img e))
    rw [hQc] at this
    exact_mod_cast this
  · refine ⟨y, ?_, ?_, ?_⟩
    · intro s _
      show y s ∈ if (s.card : ℤ) = (d : ℤ) - 1 then M else ⊥
      split_ifs with h
      · refine Submodule.sum_mem _ fun j _ => ?_
        split_ifs
        · exact zsmul_mem (hm j) _
        · exact M.zero_mem
      · rw [hycard s h]
        exact Submodule.zero_mem _
    · intro s hs
      refine hy0 s fun j h => hs ?_
      subst h
      rw [Finset.inter_eq_left.mpr (Finset.erase_subset _ _), hcard]
    · intro s hs
      have hsub : img e ⊆ s := by
        have h1 : (s ∩ img e) = img e := by
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
          rw [hQc]
          exact_mod_cast hs.ge
        rw [← h1]
        exact Finset.inter_subset_left
      have hwd : ∀ t : Finset κ, wd (wOn (img e) fun l => act (r l)) y t =
          ∑ i ∈ t, GlobalTheory.cubeSign t i • (wOn (img e) (fun l => act (r l)) i) (y (t.erase i)) := by
        intro t
        simp [wd, LinearMap.sum_apply]
      rw [hwd]
      by_cases hsQ : s = img e
      · subst hsQ
        rw [hcm]
        have hsum : ∀ F : κ → E, ∑ i ∈ img e, F i = ∑ j, F (e j) := fun F =>
          Finset.sum_map _ _ _
        rw [hsum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hw : wOn (img e) (fun l => act (r l)) (e j) = act (r (e j)) := if_pos (hmem j)
        have hsq : GlobalTheory.cubeSign (img e) (e j) * GlobalTheory.cubeSign (img e) (e j) = 1 := by
          rw [GlobalTheory.cubeSign, ← mul_pow]
          simp
        rw [hw, hyv j, map_zsmul, smul_smul, hsq, one_smul]
      · have hlt : img e ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hsQ h.symm⟩
        have hgt : d < s.card := by
          have := Finset.card_lt_card hlt
          rwa [hQc] at this
        rw [hcz s (by omega)]
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [hycard (s.erase i) ?_]
        · simp
        · rw [Finset.card_erase_of_mem hi]
          omega
end
