module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

theorem sq_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) : ∑ i ∈ s, m i ^ 2 ≤ (∑ i ∈ s, m i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    nlinarith [ih, Nat.zero_le (m a * ∑ i ∈ s, m i)]

theorem sq_sum_lt {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ s, 1 ≤ m i) (h : 1 < s.card) :
    ∑ i ∈ s, m i ^ 2 < (∑ i ∈ s, m i) ^ 2 := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  have hne : (s.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb⟩ := hne
  have hM : 1 ≤ ∑ i ∈ s.erase a, m i :=
    (hm b (Finset.mem_of_mem_erase hb)).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb)
  have ih := sq_sum_le (s.erase a) m
  rw [← Finset.add_sum_erase s _ ha, ← Finset.add_sum_erase s _ ha]
  have := hm a ha
  nlinarith

theorem num_fib {ι : Type*} [DecidableEq ι] (s : Finset ι) (m dE : ι → ℕ) (n dF : ℕ) (hdF : 0 < dF)
    (hm : ∀ i ∈ s, 1 ≤ m i) (hd : ∀ i ∈ s, dF ≤ dE i) (hsum : n * dF = ∑ i ∈ s, m i * dE i) :
    ∑ i ∈ s, m i ^ 2 ≤ n ^ 2 ∧ (∑ i ∈ s, m i ^ 2 = n ^ 2 → s.Nonempty → ∀ i ∈ s, s = {i} ∧ dE i ≤ dF) := by
  have hMn : ∑ i ∈ s, m i ≤ n := by
    have : (∑ i ∈ s, m i) * dF ≤ n * dF := by
      rw [hsum, Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (hd i hi)
    exact Nat.le_of_mul_le_mul_right this hdF
  have h1 := sq_sum_le s m
  have h2 : (∑ i ∈ s, m i) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hMn 2
  refine ⟨h1.trans h2, fun heq hne i hi => ?_⟩
  have hcard : s.card = 1 := by
    by_contra hc
    have := sq_sum_lt s m hm (by have := hne.card_pos; omega)
    omega
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.mem_singleton] at hi; subst hi
  refine ⟨rfl, ?_⟩
  simp only [Finset.sum_singleton] at heq hsum
  have hn : m i = n := by
    have := (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)) heq
    exact this
  rw [← hn] at hsum
  have := hm i (Finset.mem_singleton_self i)
  have : dF = dE i := Nat.eq_of_mul_eq_mul_left (by omega) hsum
  omega

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end

section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open Matrix

variable {k : Type} [Field k] {N : ℕ}

theorem rank_add_orth {a b : Matrix (Fin N) (Fin N) k} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : a * b = 0) (hba : b * a = 0) : (a + b).rank = a.rank + b.rank := by
  have hsup : LinearMap.range (a + b).mulVecLin = LinearMap.range a.mulVecLin ⊔ LinearMap.range b.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec]
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨v, rfl⟩
        refine ⟨a *ᵥ v, ?_⟩
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, ha.eq, hba, add_zero]
      · rintro _ ⟨v, rfl⟩
        refine ⟨b *ᵥ v, ?_⟩
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hb.eq, hab, zero_add]
  have hinf : LinearMap.range a.mulVecLin ⊓ LinearMap.range b.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    simp only [Matrix.mulVecLin_apply] at hv ⊢
    have h1 : a *ᵥ (a *ᵥ u) = a *ᵥ u := by rw [Matrix.mulVec_mulVec, ha.eq]
    have h2 : a *ᵥ (b *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec, hab, Matrix.zero_mulVec]
    rw [← hv, h2] at h1
    rw [Submodule.mem_bot, ← hv, ← h1]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range a.mulVecLin) (LinearMap.range b.mulVecLin)
  rw [hinf, finrank_bot, add_zero, ← hsup] at h
  simpa only [Matrix.finrank_range_mulVecLin] using h

theorem idem_sum_orth {ι : Type} (s : Finset ι) (e : ι → Matrix (Fin N) (Fin N) k)
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    IsIdempotentElem (∑ i ∈ s, e i) := by
  unfold IsIdempotentElem
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => ho i hi j hj (Ne.symm hji)) (fun h => absurd hi h)]
  exact hid i hi

theorem rank_sum_orth {ι : Type} (s : Finset ι) (e : ι → Matrix (Fin N) (Fin N) k)
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    (∑ i ∈ s, e i).rank = ∑ i ∈ s, (e i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hid' : ∀ j ∈ s, IsIdempotentElem (e j) := fun j hj => hid j (Finset.mem_insert_of_mem hj)
    have ho' : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → e j * e l = 0 := fun j hj l hl h =>
      ho j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl) h
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih hid' ho']
    refine rank_add_orth (hid i (Finset.mem_insert_self i s)) (idem_sum_orth s e hid' ho') ?_ ?_
    · rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => ho i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    · rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun j hj => ho j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i s)
        (fun h => hi (h ▸ hj))

theorem rank_pos_of_ne {e : Matrix (Fin N) (Fin N) k} (h : e ≠ 0) : 0 < e.rank := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  apply h
  rw [← Matrix.finrank_range_mulVecLin, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have : Matrix.toLin' e = 0 := h0
  simpa using congrArg LinearMap.toMatrix' this

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end

section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

variable {k : Type} [Field k] {N : ℕ}

abbrev Wd (e : Matrix (Fin N) (Fin N) k) : Submodule k (Fin N → k) := LinearMap.range e.mulVecLin

lemma mat_ext {b b' : Matrix (Fin N) (Fin N) k} (h : ∀ v, b *ᵥ v = b' *ᵥ v) : b = b' :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

lemma toMatrix'_mulVec' (f : (Fin N → k) →ₗ[k] (Fin N → k)) (v : Fin N → k) :
    LinearMap.toMatrix' f *ᵥ v = f v := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

lemma W_fix {e : Matrix (Fin N) (Fin N) k} (hid : IsIdempotentElem e) {w : Fin N → k} (hw : w ∈ Wd e) :
    e *ᵥ w = w := by
  obtain ⟨v, rfl⟩ := hw
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hid.eq]

lemma W_stable {e a : Matrix (Fin N) (Fin N) k} (hc : a * e = e * a) {w : Fin N → k} (hw : w ∈ Wd e) :
    a *ᵥ w ∈ Wd e := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨a *ᵥ v, by simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hc]⟩

variable {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}

def rho (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A) : A →ₐ[k] Module.End k (Wd e) where
  toFun a := (a.1.mulVecLin).restrict (fun w hw => W_stable (hA _ a.2 _ he) hw)
  map_one' := by ext w; simp
  map_mul' a b := by
    ext w : 1; apply Subtype.ext
    show (a.1 * b.1) *ᵥ (w : Fin N → k) = a.1 *ᵥ (b.1 *ᵥ (w : Fin N → k))
    rw [Matrix.mulVec_mulVec]
  map_zero' := by ext w; simp
  map_add' a b := by
    ext w : 1; apply Subtype.ext
    show (a.1 + b.1) *ᵥ (w : Fin N → k) = a.1 *ᵥ (w : Fin N → k) + b.1 *ᵥ (w : Fin N → k)
    rw [Matrix.add_mulVec]
  commutes' r := by ext w; simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]

lemma rho_apply (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A) (a : A) (w : Wd e) :
    ((rho hA he a w : Wd e) : Fin N → k) = a.1 *ᵥ (w : Fin N → k) := rfl

abbrev Pe (e : Matrix (Fin N) (Fin N) k) : (Fin N → k) →ₗ[k] Wd e := LinearMap.rangeRestrict e.mulVecLin

lemma Pe_surj (e : Matrix (Fin N) (Fin N) k) : Function.Surjective (Pe e) := LinearMap.surjective_rangeRestrict _

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end
