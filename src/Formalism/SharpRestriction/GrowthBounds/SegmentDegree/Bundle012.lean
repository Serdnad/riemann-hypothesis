module

import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CardFinRange
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AllowedLettersOfLateRows
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Rows

variable {n' r : ℕ} [NeZero n'] [NeZero r]


open Classical in
def evL (F : Frames n' r) (j x : ℤ) : List ℤ := ((F.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)

theorem row_eq (X : Dat n' r) (j x : ℤ) (i : Fin r) :
    X.row j x i = (evL X.F j x).getD ((evL X.F j x).length - r + i.val) 0 := rfl

theorem oldest_eq (F : Frames n' r) (j x : ℤ) : F.oldest j x = (evL F j x).getD ((evL F j x).length - r) 0 := rfl

theorem mem_evL (F : Frames n' r) (j x z : ℤ) : z ∈ evL F j x ↔ z ∈ F.letters j ∧ Even z ∧ z < x := by
  classical
  unfold evL
  rw [Finset.mem_sort, Finset.mem_filter]

theorem bk_fr_lt {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) :
    ∀ i', i < i' → i' < r → F.fr j i < F.fr j i' :=
  TE.fr_lt hV j i

theorem bk_fr_le {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i i' : ℕ) (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' :=
  TE.fr_le hV j i i' h h'

theorem r_le_length {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j x : ℤ) (hx : x ∈ F.letters j)
    (hW : ¬ F.IsW j x) : r ≤ (evL F j x).length := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hW' : F.fr (j - 1) (r - 1) < x := lt_of_not_ge hW
  have h4 : F.fr (j - 1) (r - 1) < F.fr j 0 := by
    have := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at this
  have hj0 : F.fr j 0 ≤ F.fr j (r - 1) := bk_fr_le hV j 0 (r - 1) (Nat.zero_le _) (by omega)
  have hsub : (Finset.range r).image (fun i => F.fr (j - 1) i) ⊆
      (F.letters j).filter (fun z => Even z ∧ z < x) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.mem_range] at hi
    have hle : F.fr (j - 1) i ≤ F.fr (j - 1) (r - 1) := bk_fr_le hV (j - 1) i (r - 1) (by omega) (by omega)
    have hge : F.fr (j - 1) 0 ≤ F.fr (j - 1) i := bk_fr_le hV (j - 1) 0 i (Nat.zero_le _) hi
    have h5 := hV.2.2.2.2.1 (j - 1) i hi
    rw [Finset.mem_filter]
    refine ⟨?_, h5.2, lt_of_le_of_lt hle hW'⟩
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hge, by linarith⟩, h5.1⟩
  have hinj : Set.InjOn (fun i => F.fr (j - 1) i) (Finset.range r : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · exact absurd hab (ne_of_lt (bk_fr_lt hV (j - 1) a b h1 hb))
    · exact absurd hab (ne_of_gt (bk_fr_lt hV (j - 1) b a h1 ha))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hc
  unfold evL
  rw [Finset.length_sort]
  exact hc

theorem evL_nodup (F : Frames n' r) (j x : ℤ) : (evL F j x).Nodup := by
  classical
  unfold evL
  exact Finset.sort_nodup _ _

theorem evL_mono (F : Frames n' r) (j x : ℤ) {a b : ℕ} (hab : a ≤ b) (hb : b < (evL F j x).length) :
    (evL F j x)[a]'(lt_of_le_of_lt hab hb) ≤ (evL F j x)[b]'hb := by
  have hp : (evL F j x).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  rcases Nat.lt_or_eq_of_le hab with h1 | h1
  · exact List.pairwise_iff_getElem.mp hp a b _ hb h1
  · subst h1
    exact le_refl _

end Rows

theorem late_row_injective : LateIndexInjective := by
  intro p n' r K _ _ _ X hX j x hx
  unfold Dat.toLate at hx
  simp only [Finset.mem_filter] at hx
  have hlen := r_le_length hX.valid j x hx.1 hx.2
  have hidx : ∀ i : Fin r, (evL X.F j x).length - r + i.val < (evL X.F j x).length := by
    intro i
    have := i.isLt
    omega
  have hrow : ∀ i : Fin r, X.row j x i = (evL X.F j x)[(evL X.F j x).length - r + i.val]'(hidx i) := by
    intro i
    rw [row_eq, List.getD_eq_getElem]
  refine ⟨?_, ?_⟩
  · intro a b h
    rw [hrow, hrow] at h
    have := (evL_nodup X.F j x).getElem_inj_iff.mp h
    exact Fin.ext (by omega)
  · intro i
    rw [hrow]
    exact (mem_evL X.F j x _).mp (List.getElem_mem _)

theorem oldest_letter_in_segment : OldestLetterInSegment := by
  intro p n' r K _ _ _ X hX j x hx
  unfold Dat.toLate at hx
  simp only [Finset.mem_filter] at hx
  have hV := hX.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hlen := r_le_length hV j x hx.1 hx.2
  have hk : (evL X.F j x).length - r < (evL X.F j x).length := by omega
  have hold : X.F.oldest j x = (evL X.F j x)[(evL X.F j x).length - r]'hk := by
    rw [oldest_eq, List.getD_eq_getElem]
  have hmem := (mem_evL X.F j x _).mp (List.getElem_mem hk)
  rw [hold]
  refine ⟨hmem.1, ?_⟩
  intro hnW
  have hlet := hmem.1
  unfold Frames.letters at hlet
  rw [Finset.mem_filter, Finset.mem_Icc] at hlet
  unfold Frames.LLset
  rw [Finset.mem_filter, Finset.mem_Ioo]
  refine ⟨⟨lt_of_not_ge hnW, ?_⟩, hlet.2⟩
  by_contra hge
  push_neg at hge
  have frame : ∀ y ∈ X.F.letters j, X.F.fr j 0 ≤ y → ∃ i < r, X.F.fr j i = y := by
    intro y hy hy0
    unfold Frames.letters at hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hy
    by_contra hne
    push_neg at hne
    have hall : ∀ i, i < r → X.F.fr j i < y := by
      intro i
      induction i with
      | zero => intro h0; exact lt_of_le_of_ne hy0 (hne 0 h0)
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        by_contra h2
        push_neg at h2
        rcases lt_or_eq_of_le h2 with h3 | h3
        · exact hV.2.2.2.2.2.1 j m y hm h1 h3 hy.2
        · exact hne (m + 1) hm h3.symm
    have := hall (r - 1) (by omega)
    linarith [hy.1.2]
  set l := evL X.F j x with hl
  set k := l.length - r with hkdef
  have hdl : (l.drop k).length = r := by
    rw [List.length_drop]
    omega
  have hnd : (l.drop k).Nodup := (evL_nodup X.F j x).sublist (List.drop_sublist _ _)
  have hxn : x ∉ (l.drop k).toFinset := by
    intro h
    rw [List.mem_toFinset] at h
    have := ((mem_evL X.F j x x).mp (List.mem_of_mem_drop h)).2.2
    exact lt_irrefl _ this
  have hsub : insert x (l.drop k).toFinset ⊆ (Finset.range r).image (fun i => X.F.fr j i) := by
    intro y hy
    rw [Finset.mem_image]
    rw [Finset.mem_insert, List.mem_toFinset] at hy
    rcases hy with rfl | hy
    · obtain ⟨i, hi, he⟩ := frame y hx.1 (le_trans hge (le_of_lt hmem.2.2))
      exact ⟨i, Finset.mem_range.mpr hi, he⟩
    · have hyl := (mem_evL X.F j x y).mp (List.mem_of_mem_drop hy)
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hy
      have hm' : k + m < l.length := by
        rw [hdl] at hm
        omega
      have hge2 : l[k]'hk ≤ (l.drop k)[m] := by
        rw [List.getElem_drop]
        exact evL_mono X.F j x (Nat.le_add_right k m) hm'
      obtain ⟨i, hi, he⟩ := frame _ hyl.1 (le_trans hge hge2)
      exact ⟨i, Finset.mem_range.mpr hi, he⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxn, List.toFinset_card_of_nodup hnd, hdl] at hc
  have hc2 := Finset.card_image_le (s := Finset.range r) (f := fun i => X.F.fr j i)
  rw [Finset.card_range] at hc2
  omega

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem ell_degree_le_power_bound : EllDegreeLePowerBound := by
  intro p n' r K _ _ _ X hX j e he
  classical
  unfold Dat.dS Dat.dV
  rw [← Finset.sum_add_distrib]
  have h1 : ∀ x ∈ X.toLate j, ((if Even x then 0 else ∑ c : Fin r, e (x, Fin.castAdd K c)) +
      (if Even x then ∑ c : Fin K, e (x, Fin.natAdd r c) else 0)) ≤ (r + K) * p ^ X.Rj p K j := by
    intro x _
    have a1 : ∑ c : Fin r, e (x, Fin.castAdd K c) ≤ r * p ^ X.Rj p K j := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin r => e (x, Fin.castAdd K c)) (p ^ X.Rj p K j)
        (fun c _ => (he.2 _).le)
      simpa using this
    have a2 : ∑ c : Fin K, e (x, Fin.natAdd r c) ≤ K * p ^ X.Rj p K j := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin K => e (x, Fin.natAdd r c)) (p ^ X.Rj p K j)
        (fun c _ => (he.2 _).le)
      simpa using this
    rw [add_mul]
    split_ifs <;> omega
  have h2 := Finset.sum_le_card_nsmul (X.toLate j) _ _ h1
  have h3 : (X.toLate j).card ≤ X.Ns := le_trans (by unfold Dat.toLate; exact Finset.card_filter_le _ _) (hX.card j)
  calc _ ≤ (X.toLate j).card • ((r + K) * p ^ X.Rj p K j) := h2
    _ = (X.toLate j).card * ((r + K) * p ^ X.Rj p K j) := smul_eq_mul _ _
    _ ≤ X.Ns * ((r + K) * p ^ X.Rj p K j) := Nat.mul_le_mul_right _ h3
    _ = (r + K) * X.Ns * p ^ X.Rj p K j := by ring

theorem degAt_ellP {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) (hx : x ∈ X.toLate j) :
    DegAt x (∑ c : Fin r, e (x, Fin.castAdd K c)) (X.ellP K R j e) := by
  classical
  have h := degAt_prod (R := R) (x := x) (X.toLate j)
    (fun x' => ∏ c : Fin r, (MvPolynomial.X (x', c) : MvPolynomial (ℤ × Fin r) R) ^ e (x', Fin.castAdd K c))
    (fun x' => ∑ c : Fin r, e (x', Fin.castAdd K c) * (if x' = x then 1 else 0))
    (fun x' _ => degAt_prod Finset.univ _ _ (fun c _ => degAt_pow (degAt_X (x := x) (x', c)) _))
  have hD : (∑ x' ∈ X.toLate j, ∑ c : Fin r, e (x', Fin.castAdd K c) * (if x' = x then 1 else 0)) =
      ∑ c : Fin r, e (x, Fin.castAdd K c) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact absurd hx h
  rw [hD] at h
  exact h

theorem degAt_ellN {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) (hx : x ∈ X.toLate j) :
    DegAt x (∑ c : Fin K, e (x, Fin.natAdd r c)) (X.ellN K R j e) := by
  classical
  have h := degAt_prod (R := R) (x := x) (X.toLate j)
    (fun x' => ∏ c : Fin K, (MvPolynomial.X (x', c) : MvPolynomial (ℤ × Fin K) R) ^ e (x', Fin.natAdd r c))
    (fun x' => ∑ c : Fin K, e (x', Fin.natAdd r c) * (if x' = x then 1 else 0))
    (fun x' _ => degAt_prod Finset.univ _ _ (fun c _ => degAt_pow (degAt_X (x := x) (x', c)) _))
  have hD : (∑ x' ∈ X.toLate j, ∑ c : Fin K, e (x', Fin.natAdd r c) * (if x' = x then 1 else 0)) =
      ∑ c : Fin K, e (x, Fin.natAdd r c) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact absurd hx h
  rw [hD] at h
  exact h

theorem word_order_bound_of_numeric_bound (D : Formalism.BasicNotions.D7) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ) (hRow : LateIndexInjective) (hN3 : OrderNumericBound C₀) :
    ProductOrdersBounded C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc mm hmm x hx hW
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  obtain ⟨nu, ka⟩ := q
  obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩ := hc.hq
  have hI' := hc.hI'
  have hI'' := hc.hI''
  simp only at h1 h2 hcond hI' hI'' hmm
  rw [← h1] at hI' hcond hmm
  rw [← h2] at hI'' hcond hmm
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).2) P1 I' hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).2) P2 I'' hI''
  obtain ⟨cE, cO, -⟩ := (hcond i).2 hW
  have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
  have hrows := hRow p n' r K X hc.hX j
  have n3 := hN3 p n' r K X hc.hX hc.hLa hc.hk j _ hxl
  have hQ0 : (0 : ℝ) ≤ ((p ^ X.Rj p K j : ℕ) : ℝ) := Nat.cast_nonneg _
  have dG : DegAt (segE X.F j i) (p ^ X.Rj p K j * b'' i + ∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c))
      (X.Gw p K (FF O) j e P2.mu I'') := by
    unfold Dat.Gw
    exact degAt_mul (degAt_pow (degAt_segRen X.F j u2.1 i) _) (degAt_ellN X K j e _ hxl)
  have dA : ¬ Even (segE X.F j i) →
      DegAt (segE X.F j i) (p ^ X.Rj p K j * b' i + ∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) + 0)
      (X.Aw p K (FF O) j e P1.mu I') := by
    intro he
    unfold Dat.Aw
    refine degAt_mul (degAt_mul (degAt_pow (degAt_segRen X.F j u1.1 i) _) (degAt_ellP X K j e _ hxl)) ?_
    refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (DlSeg_supported _ X p K j _
      fun x' hx' a _ => ((hrows x' hx').2 a).2.1) ?_
    intro v hv hvx
    exact he (hvx ▸ hv)
  have a1 : ∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) ≤ r * p ^ X.Rj p K j := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin r => e (segE X.F j i, Fin.castAdd K c))
      (p ^ X.Rj p K j) (fun c _ => (hc.he.2 _).le)
    simpa using this
  have a2 : ∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c) ≤ K * p ^ X.Rj p K j := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin K => e (segE X.F j i, Fin.natAdd r c))
      (p ^ X.Rj p K j) (fun c _ => (hc.he.2 _).le)
    simpa using this
  have a1r : ((∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) : ℕ) : ℝ) ≤ (r : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by
    exact_mod_cast a1
  have a2r : ((∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c) : ℕ) : ℝ) ≤ (K : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by
    exact_mod_cast a2
  have hkd : Dat.k (r := r) K = (r : ℝ) + K := by unfold Dat.k; push_cast; ring
  rw [hkd] at n3
  have hr0 : (0 : ℝ) ≤ (r : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by positivity
  have hK0 : (0 : ℝ) ≤ (K : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by positivity
  rw [ordDeg_prod dA (fun _ => dG) mm hmm]
  refine le_trans ?_ n3
  split_ifs with he
  · have hb := mul_le_mul_of_nonneg_left (cE he).2 hQ0
    rw [Nat.cast_add, Nat.cast_mul]
    linarith
  · have hb := mul_le_mul_of_nonneg_left (cO he).2 hQ0
    rw [add_zero, Nat.cast_add, Nat.cast_mul]
    linarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
