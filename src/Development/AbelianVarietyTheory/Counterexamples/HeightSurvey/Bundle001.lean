module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Matrix

namespace GlobalTheory.SignedParTest

theorem isEnum_unique {n : ℕ} {S : SPar} {l l' : Fin n → ℝ} {e e' : Fin n → Bool}
    (h : IsEnum S l e) (h' : IsEnum S l' e') : l = l' ∧ e = e' := by
  obtain ⟨ha, q, hq, hS⟩ := h
  obtain ⟨ha', q', hq', hS'⟩ := h'
  have key : ∀ a, ∃ b, q' b = q a ∧ e' b = e a := by
    intro a
    have : (q a, e a) ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hS'] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, congrArg Prod.fst hb, congrArg Prod.snd hb⟩
  have key' : ∀ a, ∃ b, q b = q' a := by
    intro a
    have : (q' a, e' a) ∈ S := by rw [hS']; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hS] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, congrArg Prod.fst hb⟩
  have hr : Set.range l = Set.range l' := by
    ext x; constructor
    · rintro ⟨a, rfl⟩; obtain ⟨b, hb, -⟩ := key a; exact ⟨b, by rw [hq, hq', hb]⟩
    · rintro ⟨a, rfl⟩; obtain ⟨b, hb⟩ := key' a; exact ⟨b, by rw [hq, hq', hb]⟩
  have hl : l = l' := (ha.range_inj ha').1 hr
  refine ⟨hl, funext fun a => ?_⟩
  obtain ⟨b, hb, he⟩ := key a
  have : l' b = l' a := by rw [hq' b, hb, ← hq a, hl]
  rw [ha'.injective this] at he
  exact he.symm

theorem blattner_add_rho2C {p q : ℕ} {lam : Ix p q → ℚ} (h : IsParam lam) (a : Ix p q) :
    blattner lam a + rhoOfIndex a = lam a +
      (((Finset.univ.filter fun b => lam b < lam a).card : ℚ) -
        ((Finset.univ.filter fun b => lam a < lam b).card : ℚ)) / 2 := by
  classical
  have pos : ∀ a b : Ix p q, posC a b ↔ sameBlock a b ∧ lam b < lam a := by
    intro a b
    refine ⟨fun hh => ⟨by cases a <;> cases b <;> simp_all [posC, sameBlock], h.2.1 a b hh⟩, fun ⟨h1, h2⟩ => ?_⟩
    by_contra hn
    rcases a with a | a <;> rcases b with b | b
    · rcases (not_lt.1 hn).lt_or_eq with e | e
      · exact lt_asymm h2 (h.2.1 (.inl b) (.inl a) e)
      · subst e; exact lt_irrefl _ h2
    · exact h1
    · exact h1
    · rcases (not_lt.1 hn).lt_or_eq with e | e
      · exact lt_asymm h2 (h.2.1 (.inr b) (.inr a) e)
      · subst e; exact lt_irrefl _ h2
  have sym : ∀ a b : Ix p q, sameBlock a b ↔ sameBlock b a := by
    intro a b; cases a <;> cases b <;> simp [sameBlock]
  simp only [blattner, rhoNC, rhoOfIndex, Finset.card_filter, pos, sym _ a]
  push_cast
  simp only [← Finset.sum_sub_distrib, Finset.sum_div, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : sameBlock a b <;> by_cases h2 : lam b < lam a <;> by_cases h3 : lam a < lam b <;>
    simp [h1, h2, h3] <;> norm_num

theorem blattner_inj {p q : ℕ} {l l' : Ix p q → ℚ} (h : IsParam l) (h' : IsParam l') (e : blattner l = blattner l') :
    l = l' := by
  classical
  have mono : ∀ {m : Ix p q → ℚ}, IsParam m → ∀ a b, m b < m a → blattner m b + rhoOfIndex b < blattner m a + rhoOfIndex a := by
    intro m hm a b hab
    rw [blattner_add_rho2C hm, blattner_add_rho2C hm]
    have h1 : ((Finset.univ.filter fun c => m c < m b).card : ℚ) ≤ (Finset.univ.filter fun c => m c < m a).card := by
      exact_mod_cast Finset.card_le_card fun c hc => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; linarith
    have h2 : ((Finset.univ.filter fun c => m a < m c).card : ℚ) ≤ (Finset.univ.filter fun c => m b < m c).card := by
      exact_mod_cast Finset.card_le_card fun c hc => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; linarith
    linarith
  have one : ∀ {m m' : Ix p q → ℚ}, IsParam m → IsParam m' → blattner m = blattner m' →
      ∀ a b, m b < m a → m' b < m' a := by
    intro m m' hm hm' e a b hab
    by_contra hn
    rcases (not_lt.1 hn).lt_or_eq with x | x
    · have := mono hm a b hab
      have := mono hm' b a x
      rw [e] at *; linarith
    · rw [hm'.1 x] at hab; exact lt_irrefl _ hab
  have ord : ∀ a b, l b < l a ↔ l' b < l' a := fun a b => ⟨one h h' e a b, one h' h e.symm a b⟩
  funext a
  have x := blattner_add_rho2C h a
  have y := blattner_add_rho2C h' a
  simp only [ord] at x
  rw [e] at x
  linarith

theorem hasParam_zero {T : GrpData 0 0} (R : DSRep T) (lam : Ix 0 0 → ℚ) : HasParam R lam := by
  refine ⟨?_, fun μ v _ => by simp [vogan]⟩
  haveI := R.nontriv
  obtain ⟨x, hx⟩ := exists_ne (0 : R.U.H)
  have hfin : Finite T.G := by
    have hinj : Function.Injective fun g : T.G => ((T.sq g : ℂˣ) : ℂ) := by
      intro g h e
      refine T.emb.injective (Prod.ext (Units.ext (Subsingleton.elim _ _)) (Units.ext e))
    have hsub : Set.range (fun g : T.G => ((T.sq g : ℂˣ) : ℂ)) ⊆ {1, -1} := by
      rintro _ ⟨g, rfl⟩
      have := T.sq_sq g
      rw [Matrix.det_isEmpty] at this
      simpa using this
    have := (Set.toFinite _).subset hsub
    exact Set.finite_univ_iff.1 (Set.Finite.of_finite_image (by rwa [Set.image_univ]) hinj.injOn)
  obtain ⟨v, hv⟩ := (R.ι_range x).2 (by
    unfold KFin
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _))
  refine ⟨v, fun h => hx (by rw [← hv, h, map_zero]), ?_⟩
  simp [hwSub, wtSub]

end GlobalTheory.SignedParTest
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.VolHeckeCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isWittLower_self (D : D7) (V : HSp D) : IsWittLower V V 0 := by
  refine ⟨rfl, LinearMap.id, fun _ _ => rfl, 0, ⟨linearIndependent_empty_type, ?_⟩, ?_⟩
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

end GlobalTheory.VolHeckeCheck

end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RunWeightTest

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

variable {D : D7} {j : ℕ}

set_option autoImplicit false in
variable {D : _root_.Formalism.BasicNotions.D7} {j : ℕ} in
private lemma ofGaps_eq_sub_mul {p : ℕ} (a b g : Fin p → ℕ) (T : ℕ)
    (hg : ∀ k : Fin p, (g k : ℤ) = if (k : ℕ) + 1 < p then _root_.Formalism.MainNotions.WeightAlgebra.gapZ a k - T * _root_.Formalism.MainNotions.WeightAlgebra.gapZ b k
      else (a k : ℤ) - T * b k) (i : Fin p) :
    (_root_.Formalism.MainNotions.DIV.Cons.ofGaps g i : ℤ) = a i - T * b i := by
  suffices h : ∀ n, ∀ i : Fin p, p - (i : ℕ) = n → (_root_.Formalism.MainNotions.DIV.Cons.ofGaps g i : ℤ) = a i - T * b i from
    h _ i rfl
  intro n
  induction n with
  | zero => intro i hi; have := i.isLt; omega
  | succ n ih =>
    intro i hi
    by_cases h : (i : ℕ) + 1 < p
    · rw [_root_.Formalism.MainNotions.DIV.Cons.ofGaps_succ g i h]
      push_cast
      rw [ih ⟨(i : ℕ) + 1, h⟩ (by simp only; omega), hg i, if_pos h]
      unfold _root_.Formalism.MainNotions.WeightAlgebra.gapZ
      rw [dite_eq_left h, dite_eq_left h]
      ring
    · rw [_root_.Formalism.MainNotions.DIV.Cons.ofGaps_last g i h, hg i, if_neg h]

set_option autoImplicit false in
variable {D : _root_.Formalism.BasicNotions.D7} {j : ℕ} in
private lemma mul_toNat_fdiv_add_two_le_of_add_two_le {T K : ℕ} (hK : T + 2 ≤ K) {d : ℤ} (hd : 0 ≤ d) :
    (T : ℤ) * ((d + 2).fdiv K).toNat ≤ d := by
  have hKpos : (0 : ℤ) < K := by omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hKpos.le]
  have hq : 0 ≤ (d + 2) / (K : ℤ) := Int.ediv_nonneg (by omega) hKpos.le
  rw [Int.toNat_of_nonneg hq]
  have hle := Int.ediv_mul_le (d + 2) hKpos.ne'
  have hK' : (T : ℤ) + 2 ≤ K := by exact_mod_cast hK
  rcases (show (d + 2) / (K : ℤ) = 0 ∨ 1 ≤ (d + 2) / (K : ℤ) by omega) with h0 | h1
  · rw [h0]; simp [hd]
  · nlinarith

set_option autoImplicit false in
variable {D : _root_.Formalism.BasicNotions.D7} {j : ℕ} in
private lemma gapZ_nonneg_of_antitone' {p : ℕ} (a : Fin p → ℕ) (ha : Antitone a) (k : Fin p) :
    0 ≤ _root_.Formalism.MainNotions.WeightAlgebra.gapZ a k := by
  unfold _root_.Formalism.MainNotions.WeightAlgebra.gapZ
  split_ifs with h
  · have hk : k ≤ ⟨(k : ℕ) + 1, h⟩ := by rw [Fin.le_iff_val_le_val]; simp
    have := ha hk
    omega
  · positivity

set_option autoImplicit false in
variable {D : _root_.Formalism.BasicNotions.D7} {j : ℕ} in
private lemma mul_toNat_fdiv_le_of_le_of_nonneg {T K : ℕ} (hK : T + 2 ≤ K) {y a : ℤ} (hy : y ≤ a)
    (ha : 0 ≤ a) : (T : ℤ) * (y.fdiv K).toNat ≤ a := by
  have hKpos : (0 : ℤ) < K := by omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hKpos.le]
  by_cases hq : 0 ≤ y / (K : ℤ)
  · rw [Int.toNat_of_nonneg hq]
    have hle := Int.ediv_mul_le y hKpos.ne'
    have hK' : (T : ℤ) + 2 ≤ K := by exact_mod_cast hK
    nlinarith
  · rw [Int.toNat_of_nonpos (by omega)]
    simpa using ha


set_option autoImplicit false in
variable {D : _root_.Formalism.BasicNotions.D7} {j : ℕ} in
theorem _root_.GlobalTheory.RunWeightTest.isF'_fWt (ka : _root_.Formalism.MainNotions.WeightFamilies.Wt D j) (T nW nP : ℕ) (hW : Even nW)
    (hP : Even nP) :
    _root_.Formalism.MainNotions.WeightAlgebra.IsF' ka (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW) (_root_.Formalism.MainNotions.DIV.Cons.fWt D ka (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW) T nP hP) T nP := by
  have hK : T + 2 ≤ _root_.Formalism.MainNotions.WeightAlgebra.Tp D j T := by unfold _root_.Formalism.MainNotions.WeightAlgebra.Tp; omega
  unfold _root_.Formalism.MainNotions.WeightAlgebra.IsF'
  refine ⟨rfl, fun τ i => ?_, fun τ i => ?_⟩
  · have hl : (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW).aP τ = _root_.Formalism.MainNotions.DIV.Cons.ofGaps (_root_.Formalism.MainNotions.DIV.Cons.lGapP D ka T nW τ) := rfl
    show (_root_.Formalism.MainNotions.DIV.Cons.ofGaps (_root_.Formalism.MainNotions.DIV.Cons.fGapP D ka (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW) T τ) i : ℤ) = _
    refine ofGaps_eq_sub_mul _ _ _ T (fun k => ?_) i
    unfold _root_.Formalism.MainNotions.DIV.Cons.fGapP
    split_ifs with h
    · refine Int.toNat_of_nonneg ?_
      rw [hl, _root_.Formalism.MainNotions.DIV.Cons.gapZ_ofGaps]
      unfold _root_.Formalism.MainNotions.DIV.Cons.lGapP
      rw [if_pos h]
      have := mul_toNat_fdiv_add_two_le_of_add_two_le hK (gapZ_nonneg_of_antitone' _ (ka.aPlus_antitone τ) k)
      linarith
    · refine Int.toNat_of_nonneg ?_
      rw [hl, _root_.Formalism.MainNotions.DIV.Cons.ofGaps_last _ k h]
      unfold _root_.Formalism.MainNotions.DIV.Cons.lGapP
      rw [if_neg h]
      refine sub_nonneg.mpr (mul_toNat_fdiv_le_of_le_of_nonneg hK ?_ (by positivity))
      refine (sub_le_self _ ?_).trans (sub_le_self _ ?_) <;> positivity
  · have hl : (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW).aM τ = _root_.Formalism.MainNotions.DIV.Cons.ofGaps (_root_.Formalism.MainNotions.DIV.Cons.lGapM D ka T τ) := rfl
    show (_root_.Formalism.MainNotions.DIV.Cons.ofGaps (_root_.Formalism.MainNotions.DIV.Cons.fGapM D ka (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW) T τ) i : ℤ) = _
    refine ofGaps_eq_sub_mul _ _ _ T (fun k => ?_) i
    unfold _root_.Formalism.MainNotions.DIV.Cons.fGapM
    split_ifs with h
    · refine Int.toNat_of_nonneg ?_
      rw [hl, _root_.Formalism.MainNotions.DIV.Cons.gapZ_ofGaps]
      unfold _root_.Formalism.MainNotions.DIV.Cons.lGapM
      rw [if_pos h]
      have := mul_toNat_fdiv_add_two_le_of_add_two_le hK (gapZ_nonneg_of_antitone' _ (ka.aM_anti τ) k)
      linarith
    · refine Int.toNat_of_nonneg ?_
      rw [hl, _root_.Formalism.MainNotions.DIV.Cons.ofGaps_last _ k h]
      unfold _root_.Formalism.MainNotions.DIV.Cons.lGapM
      rw [if_neg h]
      have := mul_toNat_fdiv_le_of_le_of_nonneg hK le_rfl (show (0 : ℤ) ≤ ka.aM τ k by positivity)
      linarith

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

end GlobalTheory.RunWeightTest
end
end
