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

private lemma wd_apply' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private lemma wd_one_eq {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (c : Finset ι → E) : wd (fun _ => (1 : Module.End ℂ E)) c = deltaL ℂ ι E c := by
  funext t
  rw [wd_apply']
  simp [deltaL, GlobalTheory.DI.delta]

private lemma wd_tail {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (v : E) (L : Finset ι)
    (hL : L.Nonempty) :
    wd (fun _ => (1 : Module.End ℂ E)) (fun L' : Finset ι => if L' = ∅ then v else 0) L =
      if L.card = 1 then v else 0 := by
  rw [wd_apply']
  split_ifs with h
  · obtain ⟨l, rfl⟩ := Finset.card_eq_one.1 h
    simp [GlobalTheory.cubeSign, Finset.filter_singleton]
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : L.erase i ≠ ∅ := by
      intro h0
      apply h
      have := Finset.card_erase_of_mem hi
      rw [h0, Finset.card_empty] at this
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [this]

theorem UpperTheory.Gal.productCup_of_system.edgeInj_of :
    WdUni → EdgeInj := by
  intro hU ι E _ _ _ _ G d x hx hB
  obtain ⟨y, hyC, hy⟩ := hB
  have hxC := hx.1
  have hxd : deltaL ℂ ι E x = 0 := hx.2
  have hy' : wd (fun _ => (1 : Module.End ℂ E)) y = edge1 x := hy
  have hyC' : ∀ s, y s ∈ (if (s.card : ℤ) = ((d : ℤ) + 2 - 1) then
      mixF (fun I J => G (uni I J)) s else ⊥) := fun s => hyC s (Set.mem_univ s)
  have hxC' : ∀ I, x I ∈ (if I.Nonempty ∧ (I.card : ℤ) = (d : ℤ) + 1 then G (uni I ∅) else ⊥) :=
    fun I => hxC I (Set.mem_univ I)
  have hUn := hU ι ι E (fun _ => 1)
  have hl : ∀ (b L : Finset ι), lft (uni b L) = b := fun b L => (hUn y b L).2.1
  have hr : ∀ (b L : Finset ι), rgt (uni b L) = L := fun b L => (hUn y b L).2.2.1
  have hc : ∀ (b L : Finset ι), (uni b L).card = b.card + L.card := fun b L => (hUn y b L).2.2.2.1
  have hs : ∀ s : Finset (ι ⊕ₗ ι), uni (lft s) (rgt s) = s := (hUn y ∅ ∅).2.2.2.2
  have hx0 : ∀ I : Finset ι, (I.card : ℤ) ≠ (d : ℤ) + 1 → x I = 0 := by
    intro I hI
    have := hxC' I
    rw [if_neg (fun h => hI h.2)] at this
    simpa using this
  have hy0 : ∀ s, ¬ ((lft s).Nonempty ∧ (rgt s).Nonempty) → y s = 0 := by
    intro s h
    have := hyC' s
    split_ifs at this
    · simpa [mixF, h] using this
    · simpa using this
  let e : Finset (ι ⊕ₗ ι) → E := fun s => if rgt s = ∅ then x (lft s) else 0
  have he : ∀ b L, e (uni b L) = if L = ∅ then x b else 0 := by
    intro b L
    simp only [e, hl, hr]
  have hwe : ∀ s, wd (fun _ => (1 : Module.End ℂ E)) e s = (-((-1 : ℤ) ^ d)) • edge1 x s := by
    intro s
    rw [← hs s]
    generalize lft s = b
    generalize rgt s = L
    have h1 := (hU ι ι E (fun _ => 1) e b L).1
    simp only [he] at h1
    rw [h1]
    by_cases hL : L = ∅
    · subst hL
      have : edge1 (κ := ι) x (uni b ∅) = 0 := by simp [edge1, hr]
      rw [this, smul_zero]
      have hd : wd (fun _ => (1 : Module.End ℂ E)) x = 0 := by rw [wd_one_eq, hxd]
      have e1 : (fun b' : Finset ι => if (∅ : Finset ι) = ∅ then x b' else 0) = x := by
        funext b'
        simp
      rw [e1, hd]
      simp [wd_apply']
    · have hLn : L.Nonempty := Finset.nonempty_iff_ne_empty.2 hL
      simp only [hL, if_false]
      have h0 : wd (fun _ => (1 : Module.End ℂ E)) (fun _ : Finset ι => (0 : E)) b = 0 := by
        simp [wd_apply']
      have h2 := wd_tail (x b) L hLn
      rw [h0, h2, zero_add]
      simp only [edge1, hl, hr]
      split_ifs with h1c
      · by_cases hb : (b.card : ℤ) = (d : ℤ) + 1
        · have hb' : b.card = d + 1 := by exact_mod_cast hb
          rw [hb', pow_succ]
          simp
        · simp [hx0 b hb]
      · simp
  refine ⟨e + ((-1 : ℤ) ^ d) • y, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro s _
    change (e + ((-1 : ℤ) ^ d) • y) s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (d : ℤ) + 1 then G s else ⊥)
    by_cases hr0 : rgt s = ∅
    · have hys : y s = 0 := hy0 s (fun h => h.2.ne_empty hr0)
      have hs' : uni (lft s) ∅ = s := by
        have := hs s
        rwa [hr0] at this
      have hcard : s.card = (lft s).card := by
        have := hc (lft s) ∅
        rw [hs'] at this
        simpa using this
      have hval : (e + ((-1 : ℤ) ^ d) • y) s = x (lft s) := by
        simp [e, hr0, hys]
      rw [hval]
      split_ifs with h
      · have := hxC' (lft s)
        have hlc : ((lft s).card : ℤ) = (d : ℤ) + 1 := by rw [← hcard]; exact h.2
        have hne : (lft s).Nonempty := by
          apply Finset.card_pos.1
          omega
        rw [if_pos ⟨hne, hlc⟩, hs'] at this
        exact this
      · have : x (lft s) = 0 := by
          apply hx0
          intro hlc
          apply h
          have hsc : (s.card : ℤ) = (d : ℤ) + 1 := by rw [hcard]; exact hlc
          refine ⟨Finset.card_pos.1 ?_, hsc⟩
          omega
        simp [this]
    · have hval : (e + ((-1 : ℤ) ^ d) • y) s = ((-1 : ℤ) ^ d) • y s := by
        simp [e, hr0]
      rw [hval]
      by_cases hcs : (s.card : ℤ) = (d : ℤ) + 2 - 1
      · by_cases hlr : (lft s).Nonempty ∧ (rgt s).Nonempty
        · have := hyC' s
          rw [if_pos hcs] at this
          simp only [mixF, if_pos hlr, hs s] at this
          have hsc : (s.card : ℤ) = (d : ℤ) + 1 := by omega
          rw [if_pos ⟨Finset.card_pos.1 (by omega), hsc⟩]
          exact zsmul_mem this _
        · simp [hy0 s hlr]
      · have := hyC' s
        rw [if_neg hcs] at this
        have h0 : y s = 0 := by simpa using this
        simp [h0]
  · change deltaL ℂ (ι ⊕ₗ ι) E (e + ((-1 : ℤ) ^ d) • y) = 0
    rw [← wd_one_eq, map_add (f := _), map_zsmul, hy']
    funext s
    simp [hwe]
  · intro J
    have h1 : y (uni ∅ J) = 0 := hy0 _ (fun h => by
      have := h.1
      rw [hl] at this
      simp at this)
    have h2 : x ∅ = 0 := hx0 ∅ (by simp; omega)
    simp [he, h1, h2]
  · intro I
    have h1 : y (uni I ∅) = 0 := hy0 _ (fun h => by
      have := h.2
      rw [hr] at this
      simp at this)
    simp [he, h1]
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma det_form {S : Type} [CommRing S] [Algebra ℂ S] (R : Subalgebra ℂ S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (P I : Finset (Fin n)) (f : Fin n → Fin n) (D : Fin n → S) (w : S)
    (t : Fin n → Fin n → S)
    (hP : ∀ a ∈ P, ∀ m, A a m = if m = f a then 1 else 0)
    (hI : ∀ a ∈ P, f a ∈ I)
    (hI' : ∀ m ∈ I, ∃ a ∈ P, f a = m)
    (hA : ∀ a, a ∉ P → ∀ m, m ∉ I → A a m = D m * w * t a m)
    (ht : ∀ a m, t a m ∈ R) :
    ∃ s ∈ R, A.det = s * (∏ m ∈ Iᶜ, D m) * w ^ (Pᶜ).card := by
  refine ⟨∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : S) *
      ((∏ a ∈ P, A a (σ a)) * ∏ a ∈ Pᶜ, t a (σ a)), ?_, ?_⟩
  · refine Subalgebra.sum_mem _ (fun σ _ => Subalgebra.mul_mem _ (intCast_mem R _)
      (Subalgebra.mul_mem _ (Subalgebra.prod_mem _ (fun a ha => ?_)) (Subalgebra.prod_mem _ (fun a _ => ht _ _))))
    rw [hP a ha]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  · rw [← Matrix.det_transpose, Matrix.det_apply', Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [Matrix.transpose_apply]
    rw [← Finset.prod_mul_prod_compl P]
    by_cases hσ : ∀ a ∈ P, σ a = f a
    · have hout : ∀ a ∉ P, σ a ∉ I := by
        intro a ha hm
        obtain ⟨b, hb, hfb⟩ := hI' _ hm
        have hba : σ b = σ a := by rw [hσ b hb, hfb]
        apply ha
        rw [← σ.injective hba]
        exact hb
      have hD : ∏ a ∈ Pᶜ, D (σ a) = ∏ m ∈ Iᶜ, D m := by
        refine Finset.prod_nbij σ (fun a ha => Finset.mem_compl.2 (hout a (Finset.mem_compl.1 ha)))
          (fun a _ b _ hab => σ.injective hab) ?_ (fun a _ => rfl)
        intro m hm
        have hm' : m ∉ I := Finset.mem_compl.1 hm
        refine ⟨σ.symm m, Finset.mem_coe.2 (Finset.mem_compl.2 (fun hp => ?_)), σ.apply_symm_apply m⟩
        have h1 := hσ _ hp
        rw [σ.apply_symm_apply] at h1
        exact hm' (h1 ▸ hI _ hp)
      have hprod : ∏ a ∈ Pᶜ, A a (σ a) = (∏ m ∈ Iᶜ, D m) * w ^ Pᶜ.card * ∏ a ∈ Pᶜ, t a (σ a) := by
        rw [Finset.prod_congr rfl (fun a ha => hA a (Finset.mem_compl.1 ha) (σ a) (hout a (Finset.mem_compl.1 ha)))]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, hD]
      rw [hprod]
      ring
    · push_neg at hσ
      obtain ⟨a, ha, hne⟩ := hσ
      have h0 : ∏ a ∈ P, A a (σ a) = 0 := Finset.prod_eq_zero ha (by rw [hP a ha, if_neg hne])
      rw [h0]
      ring

theorem UpperTheory.Gal.productCup_of_system.thMuLat_of :
    ThMuLat := by
  unfold ThMuLat
  intro d S E _ _ _ _ T hT
  refine ⟨?_, ?_⟩
  · unfold Sys.admitted
    intro i j l
    have hx : ∀ a, ((T.X a * (T.X i)⁻¹ : Sˣ) : S) ∈ T.R {i} {j} := fun a =>
      hT.memX {i} {j} (Finset.singleton_nonempty j) i (Finset.mem_singleton_self i) a
    have hy : ∀ a, ((T.Y a * (T.Y j)⁻¹ : Sˣ) : S) ∈ T.R {i} {j} := fun a =>
      hT.memY {i} {j} (Finset.singleton_nonempty i) j (Finset.mem_singleton_self j) a
    have key := sub_mem (mul_mem (hx (ofLex l).1) (hy (ofLex l).2))
      (mul_mem (hx (ofLex l).2) (hy (ofLex l).1))
    simp only [Units.val_mul] at key
    convert key using 1
    simp only [Sys.r, Sys.u, Sys.mu, n11, pow_one, mul_inv, Units.val_mul]
    ring
  · intro I J L hI j hj
    unfold detC
    by_cases h : (uni I L).card = d + 1
    · classical
      rw [dite_eq_left h]
      set e := (uni I L).orderEmbOfFin h with he
      have mem_e : ∀ a, e a ∈ uni I L := fun a => Finset.orderEmbOfFin_mem _ h a
      have mem_l : ∀ i : Fin (d + 1), (toLex (Sum.inl i : Fin (d + 1) ⊕ Mi d) ∈ uni I L) ↔ i ∈ I := by
        intro i
        simp [uni]
      have inl_mem : ∀ a i, ofLex (e a) = Sum.inl i → i ∈ I := by
        intro a i hai
        have h2 : e a = toLex (Sum.inl i) := by rw [← hai]; rfl
        exact (mem_l i).1 (h2 ▸ mem_e a)
      obtain ⟨P, hPm⟩ : ∃ P : Finset (Fin (d + 1)), ∀ a, a ∈ P ↔ ∃ i, ofLex (e a) = Sum.inl i :=
        ⟨Finset.univ.filter fun a => ∃ i, ofLex (e a) = Sum.inl i, fun a => by simp⟩
      obtain ⟨f, hf⟩ : ∃ f : Fin (d + 1) → Fin (d + 1), ∀ a i, ofLex (e a) = Sum.inl i → f a = i :=
        ⟨fun a => Sum.elim id (fun _ => 0) (ofLex (e a)), fun a i hai => by simp [hai]⟩
      have hfI : ∀ a ∈ P, f a ∈ I := by
        intro a ha
        obtain ⟨i, hi⟩ := (hPm a).1 ha
        rw [hf a i hi]
        exact inl_mem a i hi
      have hIf : ∀ m ∈ I, ∃ a ∈ P, f a = m := by
        intro m hm
        have hr : toLex (Sum.inl m : Fin (d + 1) ⊕ Mi d) ∈ Set.range e := by
          rw [he, Finset.range_orderEmbOfFin]
          exact (mem_l m).2 hm
        obtain ⟨a, ha⟩ := hr
        have ha' : ofLex (e a) = Sum.inl m := by rw [ha]; rfl
        exact ⟨a, (hPm a).2 ⟨m, ha'⟩, hf a m ha'⟩
      have hPcard : P.card = I.card := by
        refine Finset.card_nbij f hfI ?_ (fun m hm => ?_)
        · intro a ha b hb hab
          obtain ⟨i, hi⟩ := (hPm a).1 ha
          obtain ⟨i', hi'⟩ := (hPm b).1 hb
          rw [hf a i hi, hf b i' hi'] at hab
          apply e.injective
          have h1 : e a = toLex (Sum.inl i) := by rw [← hi]; rfl
          have h2 : e b = toLex (Sum.inl i') := by rw [← hi']; rfl
          rw [h1, h2, hab]
        · obtain ⟨a, ha, hfa⟩ := hIf m hm
          exact ⟨a, ha, hfa⟩
      have hcard : Pᶜ.card = L.card := by
        have hu : (uni I L).card = I.card + L.card := by simp [uni]
        rw [Finset.card_compl, Fintype.card_fin, hPcard]
        omega
      have hu := Units.mul_inv (T.Y j)
      have hsplit : ∀ (c1 c2 : Prop) [Decidable c1] [Decidable c2] (x y1 y2 : S),
          ((if c1 then x * y1 else 0) - if c2 then x * y2 else 0) =
            x * ((if c1 then y1 else 0) - if c2 then y2 else 0) := by
        intros
        split_ifs <;> ring
      obtain ⟨s, hs, hdet⟩ := det_form (T.R I J) (Matrix.of fun a b => T.rowMu (e a) b) P I f
        (fun m => (T.X m : S)) (T.Y j : S)
        (fun a m => Sum.elim (fun _ => (0 : S)) (fun l => ((if m = (ofLex l).1 then (T.Y (ofLex l).2 : S) else 0) -
          if m = (ofLex l).2 then (T.Y (ofLex l).1 : S) else 0) * (((T.Y j)⁻¹ : Sˣ) : S)) (ofLex (e a)))
        (by
          intro a ha m
          obtain ⟨i, hi⟩ := (hPm a).1 ha
          simp only [Matrix.of_apply, Sys.rowMu, hi, Sum.elim_inl, Pi.single_apply, hf a i hi])
        hfI hIf
        (by
          intro a ha m hm
          rcases hx : ofLex (e a) with i | l
          · exact absurd ((hPm a).2 ⟨i, hx⟩) ha
          · simp only [Matrix.of_apply, Sys.rowMu, hx, Sum.elim_inr]
            rw [hsplit]
            linear_combination (-((T.X m : S) * ((if m = (ofLex l).1 then (T.Y (ofLex l).2 : S) else 0) -
              if m = (ofLex l).2 then (T.Y (ofLex l).1 : S) else 0))) * hu)
        (by
          intro a m
          rcases hx : ofLex (e a) with i | l
          · simp only [hx, Sum.elim_inl]
            exact zero_mem _
          · simp only [hx, Sum.elim_inr, sub_mul, ite_mul, zero_mul]
            rw [← Units.val_mul, ← Units.val_mul]
            refine sub_mem ?_ ?_
            · split_ifs
              · exact hT.memY I J hI j hj _
              · exact zero_mem _
            · split_ifs
              · exact hT.memY I J hI j hj _
              · exact zero_mem _)
      beta_reduce at hdet
      refine ⟨s, hs, ?_⟩
      rw [hdet, hcard]
    · rw [dite_eq_right h]
      exact ⟨0, zero_mem _, by ring⟩
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma muSpan_base {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (R : Subalgebra ℂ S) (i j a : Fin (d + 1)) :
    InSp R (fun t => T.r n11 T.mu i j (dj j t)) (T.r n11 T.mu i j (toLex (a, j))) := by
  by_cases h : a = j
  · subst h
    refine ⟨0, fun _ => zero_mem _, ?_⟩
    simp [Sys.r, Sys.mu, mul_comm]
  · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq h
    refine ⟨Pi.single t 1, fun l => ?_, ?_⟩
    · by_cases hl : l = t
      · subst hl
        simpa using R.one_mem
      · simpa [Pi.single_eq_of_ne hl] using R.zero_mem
    · rw [Finset.sum_eq_single t]
      · simp only [Pi.single_eq_same, one_mul]
        rfl
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · intro hb
        exact absurd (Finset.mem_univ t) hb

private lemma muSpan_rel {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (i j : Fin (d + 1)) (l : Mi d) :
    T.r n11 T.mu i j l =
      ((T.Y (ofLex l).2 * (T.Y j)⁻¹ : Sˣ) : S) * T.r n11 T.mu i j (toLex ((ofLex l).1, j)) -
      ((T.Y (ofLex l).1 * (T.Y j)⁻¹ : Sˣ) : S) * T.r n11 T.mu i j (toLex ((ofLex l).2, j)) := by
  have hv : (T.Y j : S) * ((T.Y j)⁻¹ : Sˣ) = 1 := Units.mul_inv _
  have hu : ∀ l' : Mi d, T.u n11 i j l' = T.X i * T.Y j := fun _ => by simp [Sys.u, n11]
  simp only [Sys.r, Sys.mu, ofLex_toLex, Units.val_mul, hu]
  linear_combination (-((T.X (ofLex l).1 : S) * T.Y (ofLex l).2 - T.X (ofLex l).2 * T.Y (ofLex l).1) *
    ((T.X i * T.Y j)⁻¹ : Sˣ)) * hv

theorem UpperTheory.Gal.productCup_of_system.muSpan_of :
    MuSpan := by
  intro d S E _ _ _ _ T hT I J i hi j hj l
  have hI : I.Nonempty := ⟨i, hi⟩
  obtain ⟨p, hp, hp'⟩ := muSpan_base T (T.R I J) i j (ofLex l).1
  obtain ⟨q, hq, hq'⟩ := muSpan_base T (T.R I J) i j (ofLex l).2
  have hb := hT.memY I J hI j hj (ofLex l).2
  have ha := hT.memY I J hI j hj (ofLex l).1
  refine ⟨fun t => ((T.Y (ofLex l).2 * (T.Y j)⁻¹ : Sˣ) : S) * p t -
    ((T.Y (ofLex l).1 * (T.Y j)⁻¹ : Sˣ) : S) * q t, fun t => ?_, ?_⟩
  · exact sub_mem (mul_mem hb (hp t)) (mul_mem ha (hq t))
  · rw [muSpan_rel T i j l, hp', hq', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma acx_eq_zero {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E)
    (hc : c ∈ (acx A w).C n) (s : Finset σ) (hs : A s = ⊥) : c s = 0 := by
  have h : c s ∈ (if (s.card : ℤ) = n then A s else ⊥) :=
    Submodule.mem_pi.1 (show c ∈ Submodule.pi Set.univ
      (fun s : Finset σ => if (s.card : ℤ) = n then A s else ⊥) from hc) s (Set.mem_univ _)
  rw [hs, ite_self, Submodule.mem_bot] at h
  exact h

theorem UpperTheory.Gal.productCup_of_system.coordinateSystem_degree_one_of_universalDerivation :
    L1 → SysOk → WdUni → CechKoszulSystemBoundaryCriterion := by
  intro hL hOk hU
  intro d S E _ _ _ _ T κ _ _ n z N hG hAdm hKE c hc hbig hcol
  obtain ⟨hW, -, -⟩ := hOk d S E T κ n z hG hAdm
  set A : Finset (Two d ⊕ₗ κ) → Submodule ℂ E := fun s => mixF (fun I J =>
    Submodule.map (T.act ↑(∏ l ∈ rgt s, T.u n (pk I) (pk J) l)) (T.M I J)) (lft s) with hA
  have hu := fun (b : Finset (Two d)) (L : Finset κ) => hU (Two d) κ E (T.wt z) (fun _ => 0) b L
  have hcolA : ∀ b : Finset (Two d), (lft b).Nonempty → (rgt b).Nonempty →
      colA A (T.wt z) b = T.colCx n z (lft b) (rgt b) := by
    intro b h1 h2
    simp only [colA, Sys.colCx, kosT]
    congr 1
    funext L
    simp only [hA, (hu b L).2.1, (hu b L).2.2.1, mixF, h1, h2, and_self, if_true]
  have hbot : ∀ b : Finset (Two d), ¬ ((lft b).Nonempty ∧ (rgt b).Nonempty) → ∀ L, A (uni b L) = ⊥ := by
    intro b h L
    simp only [hA, (hu b L).2.1, mixF, if_neg h]
  have hcC : c ∈ (acx A (T.wt z)).C N := hc.1
  refine hL (Two d) κ E A (T.wt z) (d : ℤ) N hW ?_ c hc ?_ ?_
  · intro b
    by_cases h : (lft b).Nonempty ∧ (rgt b).Nonempty
    · rw [hcolA b h.1 h.2]
      exact hKE _ _ h.1 h.2
    · intro m _ x hx
      have hx1 : x ∈ (colA A (T.wt z) b).C m := hx.1
      have hx0 : x = 0 := funext fun L =>
        acx_eq_zero (fun L => A (uni b L)) (fun l => T.wt z (inrE l)) m x hx1 L (hbot b h L)
      rw [hx0]
      exact Submodule.zero_mem _
  · intro b L hlt
    exact hbig b L (by exact_mod_cast hlt)
  · intro b hb
    by_cases h : (lft b).Nonempty ∧ (rgt b).Nonempty
    · rw [hcolA b h.1 h.2]
      have hU2 := hU (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 0) (fun _ => 0) (lft b) (rgt b)
      have hs : uni (lft b) (rgt b) = b := hU2.2.2.2.2 b
      have := hcol (lft b) (rgt b) h.1 h.2 (by rw [← hb, ← hU2.2.2.2.1, hs])
      rw [hs] at this
      exact this
    · have h0 : col c b = 0 := funext fun L => acx_eq_zero A (T.wt z) N c hcC (uni b L) (hbot b h L)
      rw [h0]
      exact Submodule.zero_mem _
end
