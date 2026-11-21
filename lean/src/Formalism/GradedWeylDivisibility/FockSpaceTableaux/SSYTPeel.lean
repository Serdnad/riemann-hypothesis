import Formalism.GradedWeylDivisibility.StatementC

/-! # Semistandard tableaux and their leading terms -/

section LCssytLemmas

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcssyt_card_initial {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ t t' : Fin n, t' ≤ t → P t → P t') (t : Fin n) :
    t.val < (univ.filter P).card ↔ P t := by
  constructor
  · intro h
    by_contra hPt
    have hsub : univ.filter P ⊆ Iio t := by
      intro t' ht'
      simp only [mem_filter, mem_univ, true_and] at ht'
      simp only [mem_Iio]
      by_contra hle
      exact hPt (hP t' t (not_lt.mp hle) ht')
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro hPt
    have hsub : Iic t ⊆ univ.filter P := by
      intro t' ht'
      simp only [mem_Iic] at ht'
      simp only [mem_filter, mem_univ, true_and]
      exact hP t t' ht' hPt
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

theorem lcssyt_colExp_apply_lt {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (a : Fin r) (t : Fin n)
    (ht : t.val < h) : colExp c hh (a, t) = if c ⟨t.val, ht⟩ = a then 1 else 0 := by
  unfold colExp
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single ⟨t.val, ht⟩]
  · rw [Finsupp.single_apply]
    congr 1
    apply propext
    constructor
    · intro he; exact (Prod.ext_iff.mp he).1
    · intro he; exact Prod.ext he (Fin.ext rfl)
  · intro p _ hp
    rw [Finsupp.single_apply, if_neg]
    intro he
    apply hp
    have := congrArg (fun x => x.2.val) he
    exact Fin.ext (by simpa using this)
  · simp

theorem lcssyt_colExp_apply_ge {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (a : Fin r) (t : Fin n)
    (ht : ¬ t.val < h) : colExp c hh (a, t) = 0 := by
  unfold colExp
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Finsupp.single_apply, if_neg]
  intro he
  apply ht
  have := congrArg (fun x => x.2.val) he
  simp only [Fin.coe_castLE] at this
  omega

theorem lcssyt_colExp_sum_lt {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (S : Finset (Fin r)) (t : Fin n)
    (ht : t.val < h) : ∑ b ∈ S, colExp c hh (b, t) = if c ⟨t.val, ht⟩ ∈ S then 1 else 0 := by
  simp only [lcssyt_colExp_apply_lt c hh _ t ht]
  exact Finset.sum_ite_eq S (c ⟨t.val, ht⟩) (fun _ => 1)

theorem lcssyt_colExp_sum_ge {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (S : Finset (Fin r)) (t : Fin n)
    (ht : ¬ t.val < h) : ∑ b ∈ S, colExp c hh (b, t) = 0 := by
  simp [lcssyt_colExp_apply_ge c hh _ t ht]

theorem lcssyt_shapeDeg_cons {n K : ℕ} (h : ℕ) (sz : Fin K → ℕ) (t : Fin n) :
    shapeDeg (Fin.cons h sz : Fin (K + 1) → ℕ) t = (if t.val < h then 1 else 0) + shapeDeg sz t := by
  unfold shapeDeg
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem lcssyt_consSz {n K h : ℕ} (hh : h ≤ n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) :
    ∀ k : Fin (K + 1), (Fin.cons h sz : Fin (K + 1) → ℕ) k ≤ n := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using hh
  · simpa using hsz i

def lcssyt_consI {r K h : ℕ} (sz : Fin K → ℕ) (c : Fin h → Fin r) (I : ∀ k, Fin (sz k) → Fin r) :
    ∀ k : Fin (K + 1), Fin ((Fin.cons h sz : Fin (K + 1) → ℕ) k) → Fin r :=
  fun k => Fin.cases (motive := fun k => Fin ((Fin.cons h sz : Fin (K + 1) → ℕ) k) → Fin r) c I k

theorem lcssyt_bidetExp_cons {r n K h : ℕ} (hh : h ≤ n) (c : Fin h → Fin r) (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    bidetExp (Fin.cons h sz : Fin (K + 1) → ℕ) (lcssyt_consSz hh sz hsz) (lcssyt_consI sz c I) =
      colExp c hh + bidetExp sz hsz I := by
  unfold bidetExp
  rw [Fin.sum_univ_succ]
  rfl

theorem lcssyt_consI_strictMono {r K h : ℕ} (sz : Fin K → ℕ) (c : Fin h → Fin r) (I : ∀ k, Fin (sz k) → Fin r)
    (hc : StrictMono c) (hI : ∀ k, StrictMono (I k)) : ∀ k, StrictMono (lcssyt_consI sz c I k) := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · exact hc
  · exact hI i

end Formalism.GradedWeylDivisibility

end

end LCssytLemmas

section SSYTExists

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem exists_tableau_of_sum_eq_lemma (hP : SSYTPeel) (r n : ℕ) :
    ∀ (N : ℕ) (ν : Fin n → ℕ) (m : Fin r × Fin n →₀ ℕ), ∑ t, ν t = N →
      (∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t) → Interlaced m →
      ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
        shapeDeg sz = ν ∧ (∀ k, StrictMono (I k)) ∧ bidetExp sz hsz I = m := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih ν m hN hcol hint_r
  by_cases hm : m = 0
  · subst hm
    have hν : ν = 0 := by
      funext t
      rw [← hcol t]
      simp
    subst hν
    refine ⟨0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, ?_, fun k => k.elim0, ?_⟩
    · funext t
      simp [shapeDeg]
    · simp [bidetExp]
  · obtain ⟨h, hh, c, hc, hν, hle, hint', hcol'⟩ := hP r n ν m hcol hint_r hm
    obtain ⟨⟨a0, t0⟩, hne⟩ : ∃ x, m x ≠ 0 := by
      by_contra H
      push_neg at H
      exact hm (Finsupp.ext H)
    have hpos : 0 < ν t0 := by
      rw [← hcol t0]
      exact lt_of_lt_of_le (Nat.pos_of_ne_zero hne)
        (Finset.single_le_sum (f := fun a => m (a, t0)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a0))
    have hlt : ∑ t, (ν t - if t.val < h then 1 else 0) < N := by
      rw [← hN]
      apply Finset.sum_lt_sum
      · intro t _
        exact Nat.sub_le _ _
      · refine ⟨t0, Finset.mem_univ _, ?_⟩
        rw [if_pos ((hν t0).2 hpos)]
        omega
    obtain ⟨K, sz, hsz, I, hshape, hI, hexp⟩ :=
      ih _ hlt (fun t => ν t - if t.val < h then 1 else 0) (m - colExp c hh) rfl hcol' hint'
    refine ⟨K + 1, Fin.cons h sz, lcssyt_consSz hh sz hsz, lcssyt_consI sz c I, ?_,
      lcssyt_consI_strictMono sz c I hc hI, ?_⟩
    · funext t
      rw [lcssyt_shapeDeg_cons, congrFun hshape t]
      by_cases ht : t.val < h
      · have h1 := (hν t).1 ht
        simp only [if_pos ht]
        omega
      · simp only [if_neg ht]
        omega
    · rw [lcssyt_bidetExp_cons hh c sz hsz I, hexp]
      exact add_tsub_cancel_of_le hle

theorem sSYTExists_of (hP : SSYTPeel) : SSYTExists :=
  fun r n ν m hcol hint_r => exists_tableau_of_sum_eq_lemma hP r n _ ν m rfl hcol hint_r

end Formalism.GradedWeylDivisibility

end

end SSYTExists

section SSYTPeel

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem exists_pos_of_sum_pos {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : 0 < ∑ i ∈ s, f i) : ∃ i ∈ s, 0 < f i := by
  by_contra hne
  push_neg at hne
  have hz : ∑ i ∈ s, f i = 0 := Finset.sum_eq_zero (fun i hi => by have := hne i hi; omega)
  omega

private theorem colExp_apply {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (a : Fin r)
    (t : Fin n) :
    colExp c hh (a, t) = if ht : t.val < h then (if c ⟨t.val, ht⟩ = a then 1 else 0) else 0 := by
  unfold colExp
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases ht : t.val < h
  · rw [dif_pos ht]
    rw [Finset.sum_eq_single ⟨t.val, ht⟩]
    · have e : Fin.castLE hh ⟨t.val, ht⟩ = t := Fin.ext rfl
      by_cases hca : c ⟨t.val, ht⟩ = a
      · rw [if_pos ⟨hca, e⟩, if_pos hca]
      · rw [if_neg (fun hh' => hca hh'.1), if_neg hca]
    · intro p _ hp
      rw [if_neg]
      rintro ⟨_, h2⟩
      have h3 : p.val = t.val := congrArg Fin.val h2
      exact hp (Fin.ext h3)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [dif_neg ht]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    rintro ⟨_, h2⟩
    have h3 : p.val = t.val := congrArg Fin.val h2
    have h4 := p.isLt
    apply ht
    omega

private theorem sum_colExp_apply_eq_ite_mem {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n)
    (S : Finset (Fin r)) (t : Fin n) :
    ∑ b ∈ S, colExp c hh (b, t) =
      if ht : t.val < h then (if c ⟨t.val, ht⟩ ∈ S then 1 else 0) else 0 := by
  simp only [colExp_apply]
  by_cases ht : t.val < h
  · simp only [dif_pos ht]
    exact Finset.sum_ite_eq S (c ⟨t.val, ht⟩) (fun _ => 1)
  · simp only [dif_neg ht]
    exact Finset.sum_const_zero

theorem semistandardPeel : SSYTPeel := by
  intro r n ν m hcol hint_r _hm
  have hstep : ∀ l j : Fin n, j.val = l.val + 1 → 0 < ν j → 0 < ν l := by
    intro l j hlj hj
    rw [← hcol j] at hj
    obtain ⟨a, -, ha⟩ := exists_pos_of_sum_pos _ _ hj
    have h1 : (∑ b : Fin r with b ≤ a, m (b, j)) ≤ 0 + ∑ b : Fin r with b < a, m (b, l) :=
      hint_r l j hlj a
    have h2 : m (a, j) ≤ ∑ b : Fin r with b ≤ a, m (b, j) :=
      Finset.single_le_sum (f := fun b => m (b, j)) (fun _ _ => Nat.zero_le _) (by simp)
    have h3 : (∑ b : Fin r with b < a, m (b, l)) ≤ ∑ b, m (b, l) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    rw [← hcol l]
    omega
  have hdown : ∀ (d : ℕ) (t t' : Fin n), t.val = t'.val + d → 0 < ν t → 0 < ν t' := by
    intro d
    induction d with
    | zero =>
      intro t t' htt ht
      have e : t = t' := Fin.ext (by omega)
      rw [← e]
      exact ht
    | succ d ih =>
      intro t t' htt ht
      have hs : t'.val + d < n := by have := t.isLt; omega
      exact ih ⟨t'.val + d, hs⟩ t' rfl
        (hstep ⟨t'.val + d, hs⟩ t (by show t.val = t'.val + d + 1; omega) ht)
  have hmono : ∀ t t' : Fin n, t' ≤ t → 0 < ν t → 0 < ν t' := by
    intro t t' hle ht
    have hle' : t'.val ≤ t.val := hle
    exact hdown (t.val - t'.val) t t' (by omega) ht
  obtain ⟨h, hh, hiff⟩ : ∃ h : ℕ, h ≤ n ∧ ∀ t : Fin n, t.val < h ↔ 0 < ν t := by
    refine ⟨(Finset.univ.filter (fun t : Fin n => 0 < ν t)).card, ?_, ?_⟩
    · exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_univ, Fintype.card_fin])
    · intro t
      constructor
      · intro ht
        by_contra hnt
        have hsub : Finset.univ.filter (fun t : Fin n => 0 < ν t) ⊆ Finset.Iio t := by
          intro s hs
          rw [Finset.mem_filter] at hs
          rw [Finset.mem_Iio]
          by_contra hst
          push_neg at hst
          exact hnt (hmono s t hst hs.2)
        have hc := Finset.card_le_card hsub
        rw [Fin.card_Iio] at hc
        omega
      · intro ht
        have hsub : Finset.Iic t ⊆ Finset.univ.filter (fun t : Fin n => 0 < ν t) := by
          intro s hs
          rw [Finset.mem_Iic] at hs
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hmono t s hs ht⟩
        have hc := Finset.card_le_card hsub
        rw [Fin.card_Iic] at hc
        omega
  have hex : ∀ p : Fin h, ∃ a : Fin r, 0 < m (a, Fin.castLE hh p) ∧
      ∀ b : Fin r, 0 < m (b, Fin.castLE hh p) → a ≤ b := by
    intro p
    have hp : 0 < ν (Fin.castLE hh p) := (hiff _).1 p.isLt
    rw [← hcol] at hp
    obtain ⟨a, -, ha⟩ := exists_pos_of_sum_pos _ _ hp
    have hS : (Finset.univ.filter (fun b : Fin r => 0 < m (b, Fin.castLE hh p))).Nonempty :=
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    refine ⟨(Finset.univ.filter (fun b : Fin r => 0 < m (b, Fin.castLE hh p))).min' hS, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
    · intro b hb
      exact Finset.min'_le _ b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
  choose c hc1 hc2 using hex
  have hc1' : ∀ (t : Fin n) (ht : t.val < h), 0 < m (c ⟨t.val, ht⟩, t) := by
    intro t ht
    have e : Fin.castLE hh ⟨t.val, ht⟩ = t := Fin.ext rfl
    have h1 := hc1 ⟨t.val, ht⟩
    rwa [e] at h1
  have hc2' : ∀ (t : Fin n) (ht : t.val < h) (b : Fin r), 0 < m (b, t) → c ⟨t.val, ht⟩ ≤ b := by
    intro t ht b hb
    have e : Fin.castLE hh ⟨t.val, ht⟩ = t := Fin.ext rfl
    apply hc2 ⟨t.val, ht⟩ b
    rw [e]
    exact hb
  have hcstep : ∀ (l j : Fin n) (hl : l.val < h) (hj : j.val < h), j.val = l.val + 1 →
      c ⟨l.val, hl⟩ < c ⟨j.val, hj⟩ := by
    intro l j hl hj hlj
    have h1 : (∑ b : Fin r with b ≤ c ⟨j.val, hj⟩, m (b, j)) ≤
        0 + ∑ b : Fin r with b < c ⟨j.val, hj⟩, m (b, l) := hint_r l j hlj (c ⟨j.val, hj⟩)
    have h2 : m (c ⟨j.val, hj⟩, j) ≤ ∑ b : Fin r with b ≤ c ⟨j.val, hj⟩, m (b, j) :=
      Finset.single_le_sum (f := fun b => m (b, j)) (fun _ _ => Nat.zero_le _) (by simp)
    have h3 := hc1' j hj
    have h4 : 0 < ∑ b : Fin r with b < c ⟨j.val, hj⟩, m (b, l) := by omega
    obtain ⟨b, hb, hbpos⟩ := exists_pos_of_sum_pos _ _ h4
    rw [Finset.mem_filter] at hb
    exact lt_of_le_of_lt (hc2' l hl b hbpos) hb.2
  have hcstep' : ∀ p q : Fin h, q.val = p.val + 1 → c p < c q := by
    intro p q hpq
    have := hcstep (Fin.castLE hh p) (Fin.castLE hh q) p.isLt q.isLt hpq
    exact this
  have hkey : ∀ (d : ℕ) (p q : Fin h), q.val = p.val + d + 1 → c p < c q := by
    intro d
    induction d with
    | zero =>
      intro p q hpq
      exact hcstep' p q (by omega)
    | succ d ih =>
      intro p q hpq
      have hs : p.val + d + 1 < h := by have := q.isLt; omega
      exact lt_trans (ih p ⟨p.val + d + 1, hs⟩ rfl)
        (hcstep' ⟨p.val + d + 1, hs⟩ q (by show q.val = p.val + d + 1 + 1; omega))
  have hcmono : StrictMono c := by
    intro p q hpq
    have hpq' : p.val < q.val := hpq
    exact hkey (q.val - p.val - 1) p q (by omega)
  have hle : ∀ (a : Fin r) (t : Fin n), colExp c hh (a, t) ≤ m (a, t) := by
    intro a t
    rw [colExp_apply]
    by_cases ht : t.val < h
    · rw [dif_pos ht]
      by_cases hca : c ⟨t.val, ht⟩ = a
      · rw [if_pos hca]
        have h1 := hc1' t ht
        rw [hca] at h1
        omega
      · rw [if_neg hca]
        exact Nat.zero_le _
    · rw [dif_neg ht]
      exact Nat.zero_le _
  have hsub : ∀ x, (m - colExp c hh) x = m x - colExp c hh x := by
    intro x
    first
      | exact Finsupp.tsub_apply _ _ _
      | simp
      | rfl
  have hpart : ∀ (S : Finset (Fin r)) (t : Fin n),
      ∑ b ∈ S, (m - colExp c hh) (b, t) =
        ∑ b ∈ S, m (b, t) - (if ht : t.val < h then (if c ⟨t.val, ht⟩ ∈ S then 1 else 0) else 0) := by
    intro S t
    have hadd : ∑ b ∈ S, (m - colExp c hh) (b, t) + ∑ b ∈ S, colExp c hh (b, t) =
        ∑ b ∈ S, m (b, t) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [hsub]
      exact Nat.sub_add_cancel (hle b t)
    rw [sum_colExp_apply_eq_ite_mem] at hadd
    omega
  have hzero : ∀ t : Fin n, ¬ t.val < h → ∀ S : Finset (Fin r), ∑ b ∈ S, m (b, t) = 0 := by
    intro t ht S
    have hν : ν t = 0 := by
      have := (hiff t).not.mp ht
      omega
    have h1 : ∑ b ∈ S, m (b, t) ≤ ∑ b, m (b, t) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [hcol t, hν] at h1
    omega
  refine ⟨h, hh, c, hcmono, hiff, ?_, ?_, ?_⟩
  · first
      | exact Finsupp.le_def.mpr (fun x => hle x.1 x.2)
      | exact fun x => hle x.1 x.2
      | (intro x; exact hle x.1 x.2)
  · intro l j hlj a
    show (∑ b : Fin r with b ≤ a, (m - colExp c hh) (b, j)) ≤
      0 + ∑ b : Fin r with b < a, (m - colExp c hh) (b, l)
    rw [hpart, hpart]
    have h1 : (∑ b : Fin r with b ≤ a, m (b, j)) ≤ 0 + ∑ b : Fin r with b < a, m (b, l) :=
      hint_r l j hlj a
    by_cases hl : l.val < h
    · by_cases hcl : c ⟨l.val, hl⟩ < a
      · have hmemL : c ⟨l.val, hl⟩ ∈ Finset.univ.filter (fun b : Fin r => b < a) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl⟩
        rw [dif_pos hl, if_pos hmemL]
        by_cases hj : j.val < h
        · by_cases hcj : c ⟨j.val, hj⟩ ≤ a
          · have hmemJ : c ⟨j.val, hj⟩ ∈ Finset.univ.filter (fun b : Fin r => b ≤ a) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩
            rw [dif_pos hj, if_pos hmemJ]
            omega
          · have hz : ∑ b : Fin r with b ≤ a, m (b, j) = 0 := by
              apply Finset.sum_eq_zero
              intro b hb
              rw [Finset.mem_filter] at hb
              by_contra hne
              exact hcj (le_trans (hc2' j hj b (Nat.pos_of_ne_zero hne)) hb.2)
            omega
        · have hz := hzero j hj (Finset.univ.filter (fun b : Fin r => b ≤ a))
          omega
      · have hz : ∑ b : Fin r with b < a, m (b, l) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          rw [Finset.mem_filter] at hb
          by_contra hne
          exact hcl (lt_of_le_of_lt (hc2' l hl b (Nat.pos_of_ne_zero hne)) hb.2)
        omega
    · have hz := hzero l hl (Finset.univ.filter (fun b : Fin r => b < a))
      omega
  · intro t
    rw [hpart, hcol t]
    by_cases ht : t.val < h
    · rw [dif_pos ht, if_pos (Finset.mem_univ _), if_pos ht]
    · rw [dif_neg ht, if_neg ht]

end Formalism.GradedWeylDivisibility

end

end SSYTPeel
