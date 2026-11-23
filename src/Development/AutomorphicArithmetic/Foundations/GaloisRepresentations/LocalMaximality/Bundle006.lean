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

private def phiT {d : ℕ} : Fin (d + 1) ⊕ₗ Fin d → Fin (d + 1) := fun t => Sum.elim id Fin.succ (ofLex t)

private def cT {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E) :
    Fin (d + 1) ⊕ₗ Fin d → S :=
  app (fun _ => 1) (fun l : Fin d => (T.X l.succ : S))

private lemma rowT_eq {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (t : Fin (d + 1) ⊕ₗ Fin d) : T.rowT t = Pi.single (phiT t) (cT T t) := by
  rcases t with i | l <;> rfl

private lemma det_single {S : Type} [CommRing S] {n : ℕ} (g : Fin n → Fin n) (v : Fin n → S) :
    (Matrix.of fun a b => (Pi.single (g a) (v a) : Fin n → S) b).det = 0 ∨
      (Function.Bijective g ∧ ∃ ε : ℤˣ,
        (Matrix.of fun a b => (Pi.single (g a) (v a) : Fin n → S) b).det = ε • ∏ a, v a) := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply, Pi.single_apply]
  rw [Finset.sum_congr rfl fun σ _ => by rw [Fintype.prod_ite_zero]]
  by_cases hg : Function.Bijective g
  · right
    refine ⟨hg, Equiv.Perm.sign (Equiv.ofBijective g hg), ?_⟩
    rw [Finset.sum_eq_single (Equiv.ofBijective g hg)]
    · rw [if_pos (show ∀ i, (Equiv.ofBijective g hg) i = g i from fun i => rfl)]
    · intro σ _ hσ
      rw [if_neg, smul_zero]
      intro h
      exact hσ (Equiv.ext fun i => h i)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · left
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [if_neg, smul_zero]
    intro h
    have hgσ : g = σ := funext fun i => (h i).symm
    exact hg (hgσ ▸ σ.bijective)

private lemma detC_eq {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin d)) (h : s.card = d + 1) :
    detC T.rowT s = (Matrix.of fun a b => (Pi.single (phiT (s.orderEmbOfFin h a)) (cT T (s.orderEmbOfFin h a)) :
      Fin (d + 1) → S) b).det := by
  simp only [detC, dif_pos h, rowT_eq]

private lemma detC_id {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin d)) (h : s.card = d + 1) (f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Fin d)
    (hfs : ∀ a, f a ∈ s) (hf : StrictMono f) (hφ : ∀ a, phiT (f a) = a) :
    detC T.rowT s = ∏ a, cT T (f a) := by
  have hf' : ∀ a, s.orderEmbOfFin h a = f a := fun a =>
    (congrFun (Finset.orderEmbOfFin_unique h hfs hf) a).symm
  rw [detC_eq T s h]
  simp only [hf', hφ]
  rw [show (Matrix.of fun a b => (Pi.single a (cT T (f a)) : Fin (d + 1) → S) b) =
      Matrix.diagonal (fun a => cT T (f a)) from ?_]
  · exact Matrix.det_diagonal
  · ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Matrix.diagonal_apply_ne _ hab, Pi.single_apply, Ne.symm hab]

private lemma mem_uni_inl {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) (i : Fin (d + 1)) :
    toLex (Sum.inl i) ∈ uni I L ↔ i ∈ I := by
  simp [uni]

private lemma mem_uni_inr {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) (l : Fin d) :
    toLex (Sum.inr l) ∈ uni I L ↔ l ∈ L := by
  simp [uni]

private lemma card_uni' {d : ℕ} (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) :
    (uni I L).card = I.card + L.card := by
  simp [uni]

private lemma prod_uni' {d : ℕ} {S : Type} [CommMonoid S] (I : Finset (Fin (d + 1))) (L : Finset (Fin d))
    (c : Fin (d + 1) ⊕ₗ Fin d → S) :
    ∏ t ∈ uni I L, c t = (∏ i ∈ I, c (toLex (Sum.inl i))) * ∏ l ∈ L, c (toLex (Sum.inr l)) := by
  rw [uni, Finset.prod_map, Finset.prod_disjSum]
  rfl

private lemma prod_emb {α M : Type} [LinearOrder α] [CommMonoid M] (s : Finset α) {k : ℕ} (h : s.card = k) (c : α → M) :
    ∏ a, c (s.orderEmbOfFin h a) = ∏ t ∈ s, c t := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ s h]
  rw [Finset.prod_map]
  rfl

private theorem wd_lmul_app_detC_eq_zero_of_det (hD : Det) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E]
    [Module ℂ E] (T : Sys d S E) :
    (wd fun t => (Algebra.lmul ℂ S) (app (fun _ => (1 : S)) (fun l : Fin d => (T.X l.succ : S)) t))
      (detC T.rowT) = 0 := by
  have key := hD S S (Algebra.lmul ℂ S) (Fin (d + 1) ⊕ₗ Fin d) (d + 1) T.rowT (fun _ => 1) 1
  have h1 : (fun l => Algebra.lmul ℂ S (∑ b, T.rowT l b * 1)) =
      fun t => Algebra.lmul ℂ S (app (fun _ => (1 : S)) (fun l : Fin d => (T.X l.succ : S)) t) := by
    funext t
    rw [show (∑ b, T.rowT t b * 1) = cT T t by simp [rowT_eq]]
    rfl
  have h2 : (fun s => Algebra.lmul ℂ S (detC T.rowT s) 1) = detC T.rowT := by
    funext s
    simp
  rw [h1, h2] at key
  exact key

private theorem detC_uni_univ_empty {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) : detC T.rowT (uni Finset.univ ∅) = 1 := by
  rw [detC_id T (uni Finset.univ ∅) (by simp [card_uni']) (fun a => toLex (Sum.inl a))
    (fun a => (mem_uni_inl _ _ a).2 (Finset.mem_univ a)) Sum.Lex.inl_strictMono (fun a => rfl)]
  simp [cT, app]

private theorem detC_uni_singleton_zero_univ {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) : detC T.rowT (uni {0} Finset.univ) = ∏ l : Fin d, (T.X l.succ : S) := by
  let f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Fin d := fun a =>
    Fin.cases (motive := fun _ => Fin (d + 1) ⊕ₗ Fin d) (toLex (Sum.inl 0)) (fun l => toLex (Sum.inr l)) a
  have hfs : ∀ a, f a ∈ uni {0} Finset.univ := by
    intro a
    cases a using Fin.cases with
    | zero => exact (mem_uni_inl _ _ 0).2 (Finset.mem_singleton_self 0)
    | succ l => exact (mem_uni_inr _ _ l).2 (Finset.mem_univ l)
  have hf : StrictMono f := by
    intro a b hab
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact absurd hab (lt_irrefl _)
      | succ l => exact Sum.Lex.inl_lt_inr _ _
    | succ i =>
      cases b using Fin.cases with
      | zero => exact absurd hab (Fin.not_lt_zero _)
      | succ l => exact Sum.Lex.inr_strictMono (Fin.succ_lt_succ_iff.1 hab)
  have hφ : ∀ a, phiT (f a) = a := by
    intro a
    cases a using Fin.cases <;> rfl
  have hcard : (uni ({0} : Finset (Fin (d + 1))) (Finset.univ : Finset (Fin d))).card = d + 1 := by
    rw [card_uni', Finset.card_singleton, Finset.card_univ, Fintype.card_fin, add_comm]
  rw [detC_id T _ hcard f hfs hf hφ, Fin.prod_univ_succ]
  simp [f, cT, app]

private theorem detC_uni_eq_zero_or_eq_unit_smul_prod_compl {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) :
    detC T.rowT (uni I L) = 0 ∨
      0 ∈ I ∧ I.card + L.card = d + 1 ∧ ∃ ε : ℤˣ, detC T.rowT (uni I L) = ε • ∏ m ∈ Iᶜ, (T.X m : S) := by
  by_cases hc : (uni I L).card = d + 1
  swap
  · left
    simp only [detC, dif_neg hc]
  rcases det_single (fun a => phiT ((uni I L).orderEmbOfFin hc a))
      (fun a => cT T ((uni I L).orderEmbOfFin hc a)) with h0 | ⟨hbij, ε, hε⟩
  · left
    rw [detC_eq T _ hc]
    exact h0
  · right
    have hdet := (detC_eq T _ hc).trans hε
    have hmem : ∀ t, t ∈ uni I L ↔ ∃ a, (uni I L).orderEmbOfFin hc a = t := by
      intro t
      rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (uni I L) hc, Set.mem_range]
    have h0I : 0 ∈ I := by
      obtain ⟨a, ha⟩ := hbij.2 0
      replace ha : phiT ((uni I L).orderEmbOfFin hc a) = 0 := ha
      have hA : (uni I L).orderEmbOfFin hc a ∈ uni I L := Finset.orderEmbOfFin_mem _ hc a
      generalize (uni I L).orderEmbOfFin hc a = t at ha hA
      rcases t with i | l
      · change i = 0 at ha
        subst ha
        exact (mem_uni_inl I L _).1 hA
      · exact absurd ha (Fin.succ_ne_zero l)
    have hcard : I.card + L.card = d + 1 := by
      rw [← card_uni']
      exact hc
    have hcompl : Iᶜ = L.map (Fin.succEmb d) := by
      ext m
      simp only [Finset.mem_compl, Finset.mem_map, Fin.coe_succEmb]
      constructor
      · intro hm
        obtain ⟨a, ha⟩ := hbij.2 m
        replace ha : phiT ((uni I L).orderEmbOfFin hc a) = m := ha
        have hA : (uni I L).orderEmbOfFin hc a ∈ uni I L := Finset.orderEmbOfFin_mem _ hc a
        generalize (uni I L).orderEmbOfFin hc a = t at ha hA
        rcases t with i | l
        · change i = m at ha
          subst ha
          exact absurd ((mem_uni_inl I L _).1 hA) hm
        · exact ⟨l, (mem_uni_inr I L l).1 hA, ha⟩
      · rintro ⟨l, hl, rfl⟩ hI
        obtain ⟨a, ha⟩ := (hmem (toLex (Sum.inl l.succ))).1 ((mem_uni_inl I L _).2 hI)
        obtain ⟨b, hb⟩ := (hmem (toLex (Sum.inr l))).1 ((mem_uni_inr I L _).2 hl)
        have hab : a = b := hbij.1 (by
          show phiT ((uni I L).orderEmbOfFin hc a) = phiT ((uni I L).orderEmbOfFin hc b)
          rw [ha, hb]
          rfl)
        rw [hab, hb] at ha
        exact Sum.inl_ne_inr (toLex.injective ha.symm)
    refine ⟨h0I, hcard, ε, ?_⟩
    rw [hdet, prod_emb (uni I L) hc (cT T), prod_uni', hcompl, Finset.prod_map]
    simp [cT, app]

theorem UpperTheory.Gal.productCup_of_system.thT_of :
    Det → ThT := by
  intro hD d S E _ _ _ _ T
  exact ⟨wd_lmul_app_detC_eq_zero_of_det hD T, detC_uni_univ_empty T, detC_uni_singleton_zero_univ T, detC_uni_eq_zero_or_eq_unit_smul_prod_compl T⟩
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.WH

namespace UpperTheory.Gal.productCup_of_system

private theorem wd_single {σ E : Type} [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E]
    (w : σ → Module.End ℂ E) (T : Finset σ) (v : E) :
    wd w (Pi.single T v) =
      ∑ i ∈ Tᶜ, Pi.single (insert i T) (GlobalTheory.cubeSign (insert i T) i • w i v) := by
  funext t
  have hl : wd w (Pi.single T v) t =
      ∑ i ∈ t, GlobalTheory.cubeSign t i • w i ((Pi.single T v : Finset σ → E) (t.erase i)) := by
    simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]
  have L : ∑ i ∈ t, GlobalTheory.cubeSign t i • w i ((Pi.single T v : Finset σ → E) (t.erase i)) =
      ∑ i, if i ∈ t ∧ t.erase i = T then GlobalTheory.cubeSign t i • w i v else 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => by simp [hi])]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h : t.erase i = T
    · simp [hi, h]
    · simp [hi, h, Pi.single_eq_of_ne h]
  have Rr : (∑ i ∈ Tᶜ, (Pi.single (insert i T) (GlobalTheory.cubeSign (insert i T) i • w i v) :
      Finset σ → E)) t =
      ∑ i, if i ∉ T ∧ t = insert i T then GlobalTheory.cubeSign t i • w i v else 0 := by
    rw [Finset.sum_apply, ← Finset.sum_subset (Finset.subset_univ Tᶜ)
      (fun i _ hi => by simp at hi; simp [hi])]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ∉ T := by simpa using hi
    by_cases h : t = insert i T
    · subst h; simp [hi']
    · simp [hi', h, Pi.single_eq_of_ne h]
  rw [hl, L, Rr]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (i ∈ t ∧ t.erase i = T) ↔ (i ∉ T ∧ t = insert i T) := by
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨Finset.notMem_erase _ _, (Finset.insert_erase h1).symm⟩
    · rintro ⟨h1, rfl⟩
      exact ⟨Finset.mem_insert_self _ _, Finset.erase_insert h1⟩
  simp only [this]

private theorem sm_dec {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) {x : E}
    (hx : x ∈ sm act M (Set.range f)) :
    ∃ g : Fin d → E, (∀ j, g j ∈ M) ∧ x = ∑ j, act (f j) (g j) := by
  unfold sm at hx
  rw [iSup_range] at hx
  refine Submodule.iSup_induction _ (motive := fun x => ∃ g : Fin d → E, (∀ j, g j ∈ M) ∧
    x = ∑ j, act (f j) (g j)) hx ?_ ?_ ?_
  · intro j x hx
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨Pi.single j m, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using hm
      · simp [Pi.single_eq_of_ne h]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  · exact ⟨0, fun _ => M.zero_mem, by simp⟩
  · rintro x y ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
    exact ⟨g + g', fun j => M.add_mem (hg j) (hg' j), by
      simp [Finset.sum_add_distrib]⟩

private theorem single_mem {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (M : Submodule ℂ E) (w : σ → Module.End ℂ E) {T : Finset σ} {v : E} {d : ℕ}
    (hT : T.card = d) (hv : v ∈ M) :
    (Pi.single T v : Finset σ → E) ∈ (acx (fun _ => M) w).C d := by
  simp only [acx, Submodule.mem_pi]
  intro s _
  by_cases h : s = T
  · subst h; simp [hT, hv]
  · simp [Pi.single_eq_of_ne h]

theorem koszulTwoExact_of_gl2 : FiltrationCocycleLiftCriterion → SubQEx → KoszulCocycleExistsWithPrescribedComponent := by
  intro gl2 subq S E _ _ _ _ act κ _ _ R M r d e hst hr hke m hm hsm
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = img e := ⟨_, rfl⟩
  have hcard : Q.card = d := by simp [hQ, img]
  have hQmem : ∀ j, e j ∈ Q := fun j => by simp [hQ, img]
  have qex : QEx (fun _ => M) (fun l => act (r l)) Q d := hQ ▸ subq S E act κ M r d e hke
  have wok : WOk (fun _ : Finset κ => M) (fun l => act (r l)) :=
    ⟨fun i j => by
      show act (r i) * act (r j) = act (r j) * act (r i)
      rw [← map_mul, ← map_mul, mul_comm], fun s i _ x hx => hst _ (hr i) _ hx⟩
  choose g hgM hg using fun l => sm_dec act M (fun j => r (e j)) (hsm l)
  have hTcard : ∀ l, l ∉ Q → ∀ j, ((insert l Q).erase (e j)).card = d := fun l hl j => by
    rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem (hQmem j)), Finset.card_insert_of_notMem hl,
      hcard]
    rfl
  have hTQ : ∀ l, l ∉ Q → ∀ j, ((insert l Q).erase (e j)) ∩ Q = Q.erase (e j) := fun l hl j => by
    ext i
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, Or.inr h2⟩, h2⟩
  have hterm : ∀ l, l ∉ Q → ∀ j (v : E),
      wd (wOn Q fun l => act (r l)) (Pi.single ((insert l Q).erase (e j)) v) =
        Pi.single (insert l Q) (GlobalTheory.cubeSign (insert l Q) (e j) • act (r (e j)) v) := by
    intro l hl j v
    have hmem : e j ∈ insert l Q := Finset.mem_insert_of_mem (hQmem j)
    rw [wd_single, Finset.sum_eq_single (e j)]
    · rw [Finset.insert_erase hmem]
      simp [wOn, hQmem j]
    · intro i hi hne
      have hiQ : i ∉ Q := by
        intro h
        apply (Finset.mem_compl.1 hi)
        exact Finset.mem_erase.2 ⟨hne, Finset.mem_insert_of_mem h⟩
      simp [wOn, hiQ]
    · intro h
      exact absurd (Finset.mem_compl.2 (Finset.notMem_erase _ _)) h
  have hsum : ∀ (t : Finset κ) (f : Fin d → E),
      (Pi.single t (∑ j, f j) : Finset κ → E) = ∑ j, Pi.single t (f j) := fun t f =>
    map_sum (AddMonoidHom.single (fun _ : Finset κ => E) t) f Finset.univ
  have hy : ∃ y ∈ (acx (fun _ => M) (fun l => act (r l))).C d, Lev Q (· = (d : ℤ) - 1) y ∧
      wd (wOn Q fun l => act (r l)) y = wd (wOn Qᶜ fun l => act (r l)) (Pi.single Q m) := by
    refine ⟨∑ l ∈ Qᶜ, ∑ j, Pi.single ((insert l Q).erase (e j))
        ((GlobalTheory.cubeSign (insert l Q) l * GlobalTheory.cubeSign (insert l Q) (e j)) • g l j), ?_, ?_, ?_⟩
    · refine Submodule.sum_mem _ fun l hl => Submodule.sum_mem _ fun j _ => ?_
      have hl' : l ∉ Q := by simpa using hl
      exact single_mem M _ (hTcard l hl' j) (Submodule.smul_of_tower_mem _ _ (hgM l j))
    · intro s hs
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hl' : l ∉ Q := by simpa using hl
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : s ≠ (insert l Q).erase (e j) := by
        rintro rfl
        apply hs
        rw [hTQ l hl' j, Finset.card_erase_of_mem (hQmem j), hcard]
        have : 1 ≤ d := by
          rw [← hcard]
          exact Finset.card_pos.2 ⟨_, hQmem j⟩
        omega
      exact Pi.single_eq_of_ne this _

    · rw [wd_single, map_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' : l ∉ Q := by simpa using hl
      have hlc : l ∈ Qᶜ := hl

      rw [map_sum]
      simp only [hterm l hl']
      rw [← hsum]
      congr 1
      have hw : wOn Qᶜ (fun l => act (r l)) l m = ∑ j, act (r (e j)) (g l j) := by
        simpa [wOn, hl'] using hg l
      rw [hw, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, smul_smul, mul_comm, mul_assoc, GlobalTheory.cubeSign_mul_self, mul_one]
  obtain ⟨c, hc, hlev⟩ := gl2 κ E (fun _ => M) (fun l => act (r l)) Q d d wok qex
    (Pi.single Q m) (single_mem M _ hcard hm)
    (by
      intro s hs
      have : s ≠ Q := by
        rintro rfl
        simp [hcard] at hs
      exact Pi.single_eq_of_ne this _)
    (by
      rw [wd_single]
      refine Finset.sum_eq_zero fun i hi => ?_
      have : i ∉ Q := by simpa using hi
      simp [wOn, this])
    hy
  refine ⟨c, hc, ?_⟩
  have h := hlev Q (by simp [hcard])
  rw [hQ] at h
  have h' : c (img e) - (Pi.single (img e) m : Finset κ → E) (img e) = 0 := h
  simpa [sub_eq_zero] using h'

end UpperTheory.Gal.productCup_of_system

end
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.kSub_of :
    FiltrationBoundaryCriterion → SubQEx → KSub := by
  intro gl sub S E _ _ _ _ act κ _ _ R M r hst hr
  refine ⟨?_, ?_⟩
  · intro d e hK m hm c hc
    have hW : WOk (fun _ : Finset κ => M) (fun l => act (r l)) := by
      refine ⟨fun i j => ?_, fun s i _ x hx => hst _ (hr i) x hx⟩
      show act (r i) * act (r j) = act (r j) * act (r i)
      rw [← map_mul, ← map_mul, mul_comm]
    have hQ := sub S E act κ M r d e hK
    have hcard : (img e).card = d := by simp [img]
    refine gl κ E (fun _ => M) (fun l => act (r l)) (img e) d m hW hQ c hc ?_
      ⟨0, Submodule.zero_mem _, fun _ _ => rfl, ?_⟩
    · intro s hs
      exfalso
      apply hs
      have h1 : (s ∩ img e).card ≤ (img e).card := Finset.card_le_card Finset.inter_subset_right
      rw [hcard] at h1
      exact_mod_cast h1
    · intro s hs
      have h1 : (s ∩ img e).card ≤ s.card := Finset.card_le_card Finset.inter_subset_left
      have hne : (s.card : ℤ) ≠ m := by
        have : ((s ∩ img e).card : ℤ) ≤ s.card := by exact_mod_cast h1
        omega
      have h2 : c s ∈ (if (s.card : ℤ) = m then M else ⊥ : Submodule ℂ E) := hc.1 s (Set.mem_univ s)
      rw [if_neg hne, Submodule.mem_bot] at h2
      rw [h2, map_zero]
      rfl
  · intro n c hc L
    obtain ⟨y, hy, rfl⟩ := hc
    have hval : ∀ i ∈ L, y (L.erase i) ∈ M := by
      intro i _
      have h2 : y (L.erase i) ∈ (if ((L.erase i).card : ℤ) = n - 1 then M else ⊥ : Submodule ℂ E) :=
        hy (L.erase i) (Set.mem_univ _)
      split_ifs at h2 with h
      · exact h2
      · rw [Submodule.mem_bot] at h2
        rw [h2]
        exact M.zero_mem
    have hexp : (kos act M r).D y L
        = ∑ i ∈ L, (GlobalTheory.cubeSign L i : ℤ) • act (r i) (y (L.erase i)) := by
      simp [kos, acx, wd]
    rw [hexp]
    refine Submodule.sum_mem _ fun i hi => ?_
    refine Submodule.smul_of_tower_mem _ _ ?_
    have h3 : act (r i) (y (L.erase i)) ∈ M.map (act (r i)) := ⟨_, hval i hi, rfl⟩
    exact (le_iSup₂_of_le (r i) (Set.mem_range_self i) le_rfl : M.map (act (r i)) ≤ sm act M (Set.range r)) h3
end
