module

public import Formalism.PieriBlockIdeals.Bundle005
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem no_bad_tuple : NoTuple := by
  intro K V J _ _ _ T TT E hE v hv t0 ht0 hv0
  classical
  choose! tt htt1 htt2 using hE
  obtain ⟨f, t, htE, -, hsum⟩ := (Submodule.mem_span_iff_exists_finset_subset).1 hv
  clear hv
  induction t using Finset.induction_on generalizing f v with
  | empty => simpa using hsum.symm
  | insert e0 t' he0 ih =>
    have he0E : e0 ∈ E := htE (by simp)
    have hne : tt e0 ≠ t0 := fun h => ht0 (h ▸ htt1 e0 he0E)
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have h1 : (t0 j - tt e0 j) • v = ∑ a ∈ t', (f a * (tt a j - tt e0 j)) • a := by
      have h3 : T j v - tt e0 j • v = ∑ a ∈ insert e0 t', f a • (T j a - tt e0 j • a) := by
        rw [← hsum]

        simp only [map_sum, map_smul, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intros
        rw [smul_comm]
      rw [sub_smul, ← hv0 j, h3, Finset.sum_insert he0, htt2 e0 he0E j, sub_self, smul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro a ha
      rw [htt2 a (htE (by simp [ha])) j, ← sub_smul, smul_smul]
    have h2 := ih ((t0 j - tt e0 j) • v) (fun i => by rw [map_smul, hv0 i, smul_comm])
      (fun a => f a * (tt a j - tt e0 j)) (fun a ha => htE (by simp at ha ⊢; exact Or.inr ha)) h1.symm
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hj))

theorem measure_swap_invariant : MeasSwap := by
  intro n col j hj hlt
  set b : Fin n := ⟨j.val + 1, hj⟩ with hb
  have hjb : j ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [hb] at this
  have hsplit : ∀ F : Fin n → ℕ, ∑ l, F l = F j + (F b + ∑ l ∈ (Finset.univ.erase j).erase b, F l) := by
    intro F
    rw [Finset.add_sum_erase _ F (by simp [hjb.symm]), Finset.add_sum_erase _ F (by simp)]
  unfold meas
  rw [hsplit, hsplit (fun l => (n - l.val) * col l)]
  have hrest : ∑ l ∈ (Finset.univ.erase j).erase b, (n - l.val) * (col ∘ Equiv.swap j b) l =
      ∑ l ∈ (Finset.univ.erase j).erase b, (n - l.val) * col l := by
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hl
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne hl.2 hl.1]
  rw [hrest]
  simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]
  obtain ⟨w, hw⟩ : ∃ w, n - b.val = w := ⟨_, rfl⟩
  have hw' : n - j.val = w + 1 := by
    have : b.val = j.val + 1 := rfl
    omega
  rw [hw, hw']
  nlinarith

theorem ColumnsFromPieri_of (hSwap : SwapPath) (hSame : SameCol) (hMeas : MeasSwap) (hMono : MonoRun)
    (hWt : WtIff) (hGood : GoodSwap) (hAntiStep : AntiStep) (hAnti : Anti) : ColumnsFromPieri := by
  intro K P M q _ _ _ _ _ _ EM n lam2 hp tau ⟨b, j0, hj0, hcol⟩ z hz
  have key : ∀ N : ℕ, ∀ (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ →
      meas (colSeq κ ρ) = N → ∀ z : Tens (Fin q) P M n, IsWt K EM lam2 (cseq κ ρ) z → toSym K z = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro κ ρ hpath hN z hz
      by_cases hdesc : ∃ (j : Fin n) (hj : j.val + 1 < n), colSeq κ ρ ⟨j.val + 1, hj⟩ < colSeq κ ρ j
      · obtain ⟨j, hj, hlt⟩ := hdesc
        obtain ⟨h2, κ', hpath', hc', hcol'⟩ := hSwap q n lam2 tau κ ρ hpath j hj hlt
        refine hGood K P M q EM n lam2 (cseq κ ρ) j hj h2 ?_ z hz
        intro z' hz'
        rw [← hc'] at hz'
        refine ih _ ?_ κ' _ hpath' rfl z' hz'
        rw [hcol', ← hN]
        exact hMeas n _ j hj hlt
      · push Not at hdesc
        obtain ⟨i, hi, hrun⟩ := hMono q n lam2 tau κ ρ hpath hdesc (Fintype.card P) j0 hcol
        refine hAnti K (Fin q) P M n i hi z ?_
        intro j hj h1 h2
        have hc : colSeq κ ρ ⟨j.val + 1, hj⟩ = colSeq κ ρ j := by
          rw [hrun j h1 (by omega), hrun ⟨j.val + 1, hj⟩ (by simp only []; omega) (by simp only []; omega)]
        obtain ⟨ha, hb⟩ := hSame q n lam2 tau κ ρ hpath j hj hc
        exact hAntiStep K P M q EM n lam2 hp _ z j hj hz ha hb
  have hle : PathSpace K (P := P) EM n lam2 tau ≤ LinearMap.ker (toSym K) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨κ, ρ, hpath, hy⟩
    exact LinearMap.mem_ker.2 (key _ κ ρ hpath rfl y ((hWt K P M q EM n lam2 κ ρ hpath.start hpath.step y).1 hy))
  exact LinearMap.mem_ker.1 (hle hz)

end Formalism.CohomologicalDescent.LC
end

section

namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lca_content_lt {q : ℕ} (κ : Fin q → ℕ) (h : Antitone κ) {a b : Fin q} (hab : a < b) :
    (κ b : ℤ) - (b.val : ℤ) < (κ a : ℤ) - (a.val : ℤ) := by
  have h1 : κ b ≤ κ a := h hab.le
  have h2 : a.val < b.val := hab
  omega

theorem lca_content_inj {q : ℕ} (κ : Fin q → ℕ) (h : Antitone κ) {a b : Fin q}
    (e : (κ a : ℤ) - (a.val : ℤ) = (κ b : ℤ) - (b.val : ℤ)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have := lca_content_lt κ h hab; omega
  · exact hab
  · have := lca_content_lt κ h hab; omega

theorem path_eq_of_content_sequence {q n : ℕ} {lam2 tau tau' : Fin q → ℕ} {κ κ' : ℕ → Fin q → ℕ} {ρ ρ' : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (H' : IsPath n lam2 tau' κ' ρ') (m : ℕ) (hm : m ≤ n)
    (hc : ∀ j : Fin n, j.val < m → cseq κ ρ j = cseq κ' ρ' j) : ∀ l ≤ m, κ l = κ' l := by
  intro l
  induction l with
  | zero => intro _; rw [H.start, H'.start]
  | succ l ih =>
    intro hl
    have e := ih (by omega)
    have hln : l < n := by omega
    have h1 := hc ⟨l, hln⟩ (by show l < m; omega)
    have h2 := H.step ⟨l, hln⟩
    have h3 := H'.step ⟨l, hln⟩
    dsimp only [cseq] at h1 h2 h3
    rw [← e] at h1 h3
    have h4 : ρ ⟨l, hln⟩ = ρ' ⟨l, hln⟩ := lca_content_inj (κ l) (H.dom l (by omega)) h1
    rw [h2, h3, h4]

theorem lca_single_ne {q : ℕ} {r a : Fin q} (h : a ≠ r) (A : Fin q → ℕ) :
    (A + Pi.single r 1 : Fin q → ℕ) a = A a := by
  simp [Pi.single_apply, h]

theorem lca_single_eq {q : ℕ} (r : Fin q) (A : Fin q → ℕ) :
    (A + Pi.single r 1 : Fin q → ℕ) r = A r + 1 := by simp

theorem lca_rows_lt {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (hle : colSeq κ ρ j' ≤ colSeq κ ρ j) :
    ρ j < ρ j' ∧ colSeq κ ρ j' = κ j.val (ρ j') := by
  have hjn := j'.isLt
  have s1 := H.step j
  have d1 := H.dom (j.val + 1) (by omega)
  have hle' : κ (j.val + 1) (ρ j') ≤ κ j.val (ρ j) := by
    have := hle; unfold colSeq at this; rwa [hv] at this
  have hlt : ρ j < ρ j' := by
    by_contra hcon
    have hcon : ρ j' ≤ ρ j := not_lt.mp hcon
    have h3 := d1 hcon
    rw [s1] at h3 hle'
    rw [lca_single_eq] at h3
    omega
  refine ⟨hlt, ?_⟩
  unfold colSeq; rw [hv, s1, lca_single_ne hlt.ne']

theorem lca_swap {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (hlt : colSeq κ ρ j' < colSeq κ ρ j) :
    2 ≤ cseq κ ρ j - cseq κ ρ j' ∧
      ∃ κ' : ℕ → Fin q → ℕ, IsPath n lam2 tau κ' (ρ ∘ Equiv.swap j j') ∧
        cseq κ' (ρ ∘ Equiv.swap j j') = cseq κ ρ ∘ Equiv.swap j j' ∧
        colSeq κ' (ρ ∘ Equiv.swap j j') = colSeq κ ρ ∘ Equiv.swap j j' := by
  obtain ⟨hr, hc⟩ := lca_rows_lt H j j' hv hlt.le
  have hjn := j'.isLt
  have s1 := H.step j
  have s2 := H.step j'
  rw [hv] at s2
  have d0 := H.dom j.val (by omega)
  have d2 := H.dom (j.val + 1 + 1) (by omega)
  have hA : κ j.val (ρ j') < κ j.val (ρ j) := by rw [← hc]; exact hlt
  have hc' : cseq κ ρ j' = (κ j.val (ρ j') : ℤ) - ((ρ j').val : ℤ) := by
    have := hc; unfold colSeq at this; unfold cseq; rw [this]
  have hr' : (ρ j).val < (ρ j').val := hr
  refine ⟨by rw [hc']; unfold cseq; omega, ?_⟩
  obtain ⟨κ', hκ'⟩ : ∃ κ' : ℕ → Fin q → ℕ,
      ∀ l, κ' l = if l = j.val + 1 then κ j.val + Pi.single (ρ j') 1 else κ l := ⟨_, fun _ => rfl⟩
  have k1 : κ' (j.val + 1) = κ j.val + Pi.single (ρ j') 1 := by rw [hκ', if_pos rfl]
  have k2 : ∀ l, l ≠ j.val + 1 → κ' l = κ l := fun l h => by rw [hκ', if_neg h]
  have anti : Antitone (κ j.val + Pi.single (ρ j') 1) := by
    intro a b hab
    by_cases hb : b = ρ j'
    · by_cases ha : a = ρ j'
      · rw [ha, hb]
      · rw [hb, lca_single_eq, lca_single_ne ha]
        have hab' : a < ρ j' := lt_of_le_of_ne (hb ▸ hab) ha
        by_cases har : a ≤ ρ j
        · have := d0 har; omega
        · have har : ρ j < a := not_le.mp har
          have h5 := d2 hab'.le
          rw [s2, s1] at h5
          rw [lca_single_eq, lca_single_ne hr.ne', lca_single_ne ha, lca_single_ne har.ne'] at h5
          exact h5
    · rw [lca_single_ne hb]
      calc κ j.val b ≤ κ j.val a := d0 hab
        _ ≤ (κ j.val + Pi.single (ρ j') 1 : Fin q → ℕ) a := by simp [Pi.add_apply]
  have hcol : colSeq κ' (ρ ∘ Equiv.swap j j') = colSeq κ ρ ∘ Equiv.swap j j' := by
    funext l
    by_cases h1 : l = j
    · rw [h1]
      simp only [colSeq, Function.comp, Equiv.swap_apply_left]
      rw [k2 j.val (by omega), hv, s1, lca_single_ne hr.ne']
    · by_cases h2 : l = j'
      · rw [h2]
        simp only [colSeq, Function.comp, Equiv.swap_apply_right]
        rw [hv, k1, lca_single_ne hr.ne]
      · have h4 : l.val ≠ j.val + 1 := fun h => h2 (Fin.ext (h.trans hv.symm))
        simp only [colSeq, Function.comp]
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, k2 _ h4]
  refine ⟨κ', ⟨?_, ?_, ?_, ?_⟩, ?_, hcol⟩
  · rw [k2 0 (by omega), H.start]
  · intro l
    by_cases h1 : l = j
    · rw [h1]
      simp only [Function.comp, Equiv.swap_apply_left]
      rw [k1, k2 j.val (by omega)]
    · by_cases h2 : l = j'
      · rw [h2]
        simp only [Function.comp, Equiv.swap_apply_right]
        rw [hv, k1, k2 (j.val + 1 + 1) (by omega), s2, s1]
        exact add_right_comm _ _ _
      · have h3 : l.val ≠ j.val := fun h => h1 (Fin.ext h)
        have h4 : l.val ≠ j.val + 1 := fun h => h2 (Fin.ext (h.trans hv.symm))
        simp only [Function.comp]
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, k2 _ (by omega), k2 _ h4]
        exact H.step l
  · rw [k2 n (by omega), H.stop]
  · intro l hl
    by_cases h : l = j.val + 1
    · rw [h, k1]; exact anti
    · rw [k2 l h]; exact H.dom l hl
  · funext l
    have := congrFun hcol l
    simp only [colSeq, cseq, Function.comp] at this ⊢
    rw [this]

theorem swap_path_exists : SwapPath := by
  intro q n lam2 tau κ ρ H j hj hlt
  exact lca_swap H j ⟨j.val + 1, hj⟩ rfl hlt

theorem lca_same {q n : ℕ} {lam2 tau : Fin q → ℕ} {κ : ℕ → Fin q → ℕ} {ρ : Fin n → Fin q}
    (H : IsPath n lam2 tau κ ρ) (j j' : Fin n) (hv : j'.val = j.val + 1) (heq : colSeq κ ρ j' = colSeq κ ρ j) :
    cseq κ ρ j' = cseq κ ρ j - 1 ∧ ¬ IsContentSeq lam2 (cseq κ ρ ∘ Equiv.swap j j') := by
  obtain ⟨hr, hc⟩ := lca_rows_lt H j j' hv heq.le
  have hjn := j'.isLt
  have s1 := H.step j
  have s2 := H.step j'
  rw [hv] at s2
  have d0 := H.dom j.val (by omega)
  have d2 := H.dom (j.val + 1 + 1) (by omega)
  have hA : κ j.val (ρ j') = κ j.val (ρ j) := by rw [← hc]; exact heq
  have hc' : cseq κ ρ j' = (κ j.val (ρ j') : ℤ) - ((ρ j').val : ℤ) := by
    have := hc; unfold colSeq at this; unfold cseq; rw [this]
  have hr' : (ρ j).val < (ρ j').val := hr
  constructor
  · have hrow : (ρ j').val = (ρ j).val + 1 := by
      by_contra hcon
      have hq := (ρ j').isLt
      obtain ⟨a, ha⟩ : ∃ a : Fin q, a.val = (ρ j).val + 1 := ⟨⟨(ρ j).val + 1, by omega⟩, rfl⟩
      have ha1 : ρ j < a := by show (ρ j).val < a.val; omega
      have ha2 : a < ρ j' := by show a.val < (ρ j').val; omega
      have h5 := d2 ha2.le
      rw [s2, s1] at h5
      rw [lca_single_eq, lca_single_ne hr.ne', lca_single_ne ha2.ne, lca_single_ne ha1.ne'] at h5
      have h6 := d0 ha1.le
      omega
    rw [hc']; unfold cseq; omega
  · rintro ⟨tau', κ', ρ', H', hcs⟩
    have hpre : ∀ i : Fin n, i.val < j.val → cseq κ ρ i = cseq κ' ρ' i := by
      intro i hi
      have h := congrFun hcs i
      have h1 : i ≠ j := fun h => by rw [h] at hi; omega
      have h2 : i ≠ j' := fun h => by rw [h] at hi; omega
      simp only [Function.comp] at h
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at h
      exact h.symm
    have e : κ j.val = κ' j.val := path_eq_of_content_sequence H H' j.val (by omega) hpre j.val le_rfl
    have h1 := congrFun hcs j
    simp only [Function.comp, Equiv.swap_apply_left] at h1
    rw [hc'] at h1
    unfold cseq at h1
    rw [← e] at h1
    have h2 : ρ' j = ρ j' := lca_content_inj _ d0 h1
    have h3 := H'.dom (j.val + 1) (by omega) hr.le
    rw [H'.step j, ← e, h2, lca_single_eq, lca_single_ne hr.ne] at h3
    omega

theorem same_column : SameCol := by
  intro q n lam2 tau κ ρ H j hj heq
  exact lca_same H j ⟨j.val + 1, hj⟩ rfl heq

end Formalism.CohomologicalDescent.LC
end

section

namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

section

variable {K N : Type*} [CommRing K] [AddCommGroup N] [Module K N] {q : ℕ}

inductive LowW (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) : N → Prop
  | base (v : N) : IsHW T κ v → LowW T κ v
  | step (a b : Fin q) (x : N) : b < a → LowW T κ x → LowW T κ (T a b x)

def lowSpan (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) : Submodule K N :=
  Submodule.span K {x | LowW T κ x}

theorem lowSpan_low (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) (c d : Fin q) (h : d < c) :
    ∀ y ∈ lowSpan T κ, T c d y ∈ lowSpan T κ := by
  intro y hy
  have : (lowSpan T κ).map (T c d) ≤ lowSpan T κ := by
    unfold lowSpan
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span (LowW.step c d x h hx)
  exact this (Submodule.mem_map_of_mem hy)

theorem lowW_all (T : Fin q → Fin q → Module.End K N) (hT : GlRel T) (κ : Fin q → K) (x : N) (hx : LowW T κ x) :
    ∀ a b, T a b x ∈ lowSpan T κ := by
  induction hx with
  | base v hv =>
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hv.1 a b h]; exact Submodule.zero_mem _
    · subst h
      rw [hv.2 a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (LowW.base v hv))
    · exact Submodule.subset_span (LowW.step a b v h (LowW.base v hv))
  | step c d x hdc _ ih =>
    intro a b
    have h := LinearMap.congr_fun (hT a b c d) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    have e : T a b (T c d x) = T c d (T a b x) +
        (((if b = c then T a d else 0 : Module.End K N) x) - ((if d = a then T c b else 0 : Module.End K N) x)) := by
      rw [← h]; abel
    rw [e]
    refine Submodule.add_mem _ (lowSpan_low T κ c d hdc _ (ih a b)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih a d
      · simp
    · split_ifs
      · exact ih c b
      · simp

theorem lowSpan_stab (T : Fin q → Fin q → Module.End K N) (hT : GlRel T) (κ : Fin q → K) : Stab T (lowSpan T κ) := by
  intro a b y hy
  have : (lowSpan T κ).map (T a b) ≤ lowSpan T κ := by
    rw [lowSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact lowW_all T hT κ x hx a b
  exact this (Submodule.mem_map_of_mem hy)

end

theorem generatedHighestWeight_holds : GeneratedHW := by
  intro K N q _ _ _ _ _ T B hF κ hgen v μ hv hhw
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ κ a := by
    by_contra hcon
    exact hne (funext fun a => by_contra fun h => hcon ⟨a, h⟩)
  have htop : lowSpan T κ = ⊤ :=
    hgen _ (lowSpan_stab T hF.gl κ) (fun w hw => Submodule.subset_span (LowW.base w hw))
  have horth : ∀ x, LowW T κ x → B v x = 0 := by
    intro x hx
    cases hx with
    | base _ hw =>
      have h := hF.adj a a v x
      rw [hhw.2 a, hw.2 a, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h
      have h2 : (μ a - κ a) * B v x = 0 := by rw [sub_mul, h, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)
    | step c d y hdc _ =>
      rw [← hF.adj d c v y, hhw.1 d c hdc, map_zero, LinearMap.zero_apply]
  have hall : ∀ y ∈ lowSpan T κ, B v y = 0 := by
    intro y hy
    have : lowSpan T κ ≤ LinearMap.ker (B v) := by
      rw [lowSpan, Submodule.span_le]
      intro x hx
      exact LinearMap.mem_ker.2 (horth x hx)
    exact LinearMap.mem_ker.1 (this hy)
  have h0 : B v v = 0 := hall v (by rw [htop]; exact Submodule.mem_top)
  exact absurd (hF.pos v hv) (by rw [h0]; exact lt_irrefl _)

end Formalism.CohomologicalDescent.LP
end
