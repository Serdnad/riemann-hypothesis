module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.RepOnAlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem valSuccAbove {n : ℕ} (p : Fin (n + 1)) (x : Fin n) :
    (p.succAbove x).val = if x.val < p.val then x.val else x.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

theorem skip1Eq {t : ℕ} (i : Fin (t + 1)) (j : Fin t) : skip1 i j = i.succAbove j := by
  apply Fin.ext
  rw [valSuccAbove]
  unfold skip1
  split_ifs <;> simp

theorem skip1Fun {t : ℕ} (i : Fin (t + 1)) : (skip1 i : Fin t → Fin (t + 1)) = i.succAbove :=
  funext (skip1Eq i)

theorem valSkip2 {t : ℕ} (i i' : Fin t) (j : Fin (t - 2)) :
    (skip2 i i' j).val =
      if j.val < i.val then j.val else if j.val + 1 < i'.val then j.val + 1 else j.val + 2 := by
  unfold skip2
  split_ifs <;> rfl

theorem skip2Lt {t : ℕ} (i' : Fin (t + 2)) (k : Fin (t + 1)) (h : (k : ℕ) < (i' : ℕ)) :
    (skip2 (i'.succAbove k) i' : Fin t → Fin (t + 2)) = i'.succAbove ∘ k.succAbove := by
  funext x
  apply Fin.ext
  have hx := x.isLt
  simp only [Function.comp, valSuccAbove, valSkip2]
  split_ifs <;> omega

theorem skip2Gt {t : ℕ} (i' : Fin (t + 2)) (k : Fin (t + 1)) (h : ¬ (k : ℕ) < (i' : ℕ)) :
    (skip2 i' (i'.succAbove k) : Fin t → Fin (t + 2)) = i'.succAbove ∘ k.succAbove := by
  funext x
  apply Fin.ext
  have hx := x.isLt
  simp only [Function.comp, valSuccAbove, valSkip2]
  split_ifs <;> omega

theorem pairSum {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (c d : Fin (t + 2) → A)
    (G : (Fin t → Fin (t + 2)) → A) :
    ∑ i : Fin (t + 2), ∑ i' : Fin (t + 2),
        (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • ((c i * d i' - c i' * d i) * G (skip2 i i')) else 0) =
      ∑ i' : Fin (t + 2), ∑ k : Fin (t + 1),
        ((-1 : ℂ) ^ ((i' : ℕ) + (k : ℕ))) • (c (i'.succAbove k) * d i' * G (i'.succAbove ∘ k.succAbove)) := by
  have hR : ∀ i' : Fin (t + 2), ∑ k : Fin (t + 1),
      ((-1 : ℂ) ^ ((i' : ℕ) + (k : ℕ))) • (c (i'.succAbove k) * d i' * G (i'.succAbove ∘ k.succAbove)) =
        ∑ j : Fin (t + 2),
          ((if j < i' then ((-1 : ℂ) ^ ((j : ℕ) + (i' : ℕ))) • (c j * d i' * G (skip2 j i')) else 0) -
            (if i' < j then ((-1 : ℂ) ^ ((i' : ℕ) + (j : ℕ))) • (c j * d i' * G (skip2 i' j)) else 0)) := by
    intro i'
    conv_rhs => rw [Fin.sum_univ_succAbove _ i']
    simp only [lt_irrefl, if_false, sub_zero, zero_add]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : (k : ℕ) < (i' : ℕ)
    · have hv : ((i'.succAbove k : Fin (t + 2)) : ℕ) = k := by rw [valSuccAbove, if_pos hk]
      have h1 : i'.succAbove k < i' := by rw [Fin.lt_def, hv]; exact hk
      have h2 : ¬ i' < i'.succAbove k := by rw [Fin.lt_def, hv]; omega
      rw [if_pos h1, if_neg h2, sub_zero, skip2Lt i' k hk, hv, add_comm (k : ℕ)]
    · have hv : ((i'.succAbove k : Fin (t + 2)) : ℕ) = k + 1 := by rw [valSuccAbove, if_neg hk]
      have h1 : ¬ i'.succAbove k < i' := by rw [Fin.lt_def, hv]; omega
      have h2 : i' < i'.succAbove k := by rw [Fin.lt_def, hv]; omega
      rw [if_pos h2, if_neg h1, zero_sub, skip2Gt i' k hk, hv, ← neg_smul]
      congr 1
      rw [← add_assoc, pow_succ]
      ring
  have hL : ∀ i i' : Fin (t + 2),
      (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • ((c i * d i' - c i' * d i) * G (skip2 i i')) else 0) =
        (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • (c i * d i' * G (skip2 i i')) else 0) -
          (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • (c i' * d i * G (skip2 i i')) else 0) := by
    intro i i'
    split_ifs <;> simp [sub_mul, smul_sub]
  simp only [hL, Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i' _ => hR i')]
  simp only [Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

theorem intCastMul {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (X : A) : (z : A) * X = (z : ℂ) • X := by
  rw [Algebra.smul_def, map_intCast]

theorem eSq (e : ℤˣ) : ((e : ℤ) : ℂ) * ((e : ℤ) : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem starE (e : ℤˣ) : star (((e : ℤ) : ℂ)) = ((e : ℤ) : ℂ) := star_intCast _

theorem prodSA {t : ℕ} (ε : Fin (t + 1) → ℤˣ) (i : Fin (t + 1)) :
    ∏ k, ε (i.succAbove k) = ε i * ∏ k, ε k := by
  rw [Fin.prod_univ_succAbove ε i, ← mul_assoc, Int.units_mul_self, one_mul]

theorem prodSA2 {t : ℕ} (ε : Fin (t + 2) → ℤˣ) (i : Fin (t + 2)) (k : Fin (t + 1)) :
    ∏ x, ε (i.succAbove (k.succAbove x)) = ε i * ε (i.succAbove k) * ∏ k, ε k := by
  have h := prodSA (fun y => ε (i.succAbove y)) k
  rw [h, prodSA ε i, ← mul_assoc, mul_comm (ε (i.succAbove k)) (ε i)]

theorem star1 (hSM : StarMinor) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {t : ℕ}
    (E : Fin (t + 1) → Fin (t + 1) → A) (ε : Fin (t + 1) → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (i j : Fin (t + 1)) (w : ℂ) :
    star (qminor E i.succAbove j.succAbove w) =
      (((ε i : ℤ) : ℂ) * ((ε j : ℤ) : ℂ)) • qminor E j.succAbove i.succAbove (star w) := by
  rw [hSM A (t + 1) t E ε hGl hE i.succAbove j.succAbove w, intCastMul, prodSA, prodSA,
    mul_mul_mul_comm, Int.units_mul_self, mul_one]
  push_cast
  rfl

theorem star2 (hSM : StarMinor) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {t : ℕ}
    (E : Fin (t + 2) → Fin (t + 2) → A) (ε : Fin (t + 2) → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (i : Fin (t + 2)) (k : Fin (t + 1))
    (j : Fin (t + 2)) (l : Fin (t + 1)) (w : ℂ) :
    star (qminor E (i.succAbove ∘ k.succAbove) (j.succAbove ∘ l.succAbove) w) =
      (((ε i : ℤ) : ℂ) * ((ε (i.succAbove k) : ℤ) : ℂ) * (((ε j : ℤ) : ℂ) * ((ε (j.succAbove l) : ℤ) : ℂ))) •
        qminor E (j.succAbove ∘ l.succAbove) (i.succAbove ∘ k.succAbove) (star w) := by
  rw [hSM A (t + 2) t E ε hGl hE _ _ w, intCastMul]
  simp only [Function.comp_apply]
  rw [prodSA2, prodSA2, mul_mul_mul_comm, Int.units_mul_self, mul_one]
  push_cast
  rfl

theorem mvC (hMV : MoveVec) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
    (hGl : GlRel E) (hL : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (hC : ∀ a b, y a * y b = y b * y a) (a : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (w : ℂ) :
    ∑ j : Fin (t + 1), ((-1 : ℂ) ^ (j : ℕ)) • (y (b j) * qminor E a (b ∘ j.succAbove) w) =
      ∑ j : Fin (t + 1), ((-1 : ℂ) ^ (j : ℕ)) • (qminor E a (b ∘ j.succAbove) (w - 1) * y (b j)) := by
  have h := hMV A n t E y hGl hL hC a b w
  simp only [intCastMul] at h
  push_cast at h
  exact h

theorem nested_minor_expansion_zero_one {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 1) → Fin (t + 1) → A)
    (Y Yb : Fin (t + 1) → A) (x xb : Fin (t + 1) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 0 1 = -∑ i : Fin (t + 1), ∑ j : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E i.succAbove j.succAbove (u - 1)) := by
  simp only [tA, skip1Fun]

theorem nested_minor_expansion_one_zero {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 1) → Fin (t + 1) → A)
    (Y Yb : Fin (t + 1) → A) (x xb : Fin (t + 1) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 0 = -∑ i : Fin (t + 1), ∑ j : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * xb i) • (Y j * qminor E i.succAbove j.succAbove u) := by
  simp only [tA, skip1Fun]

theorem star_transfer_diagonal_zero (hSM : StarMinor) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (ε : Fin m → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (u : ℂ) :
    star (tA E Y Yb x xb u 0 0) = tA E Y Yb x xb (star u) 0 0 := by
  show star (qminor E id id u) = qminor E id id (star u)
  rw [hSM A m m E ε hGl hE id id u, Int.units_mul_self]
  simp

theorem star_transfer_zero_one (hSM : StarMinor) (hMV : MoveVec) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (ε : Fin m → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a)
    (hLY : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0)
    (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (hxb : ∀ c, xb c = ((ε c : ℤ) : ℂ) * star (x c))
    (u : ℂ) :
    star (tA E Y Yb x xb u 0 1) = tA E Y Yb x xb (star u) 1 0 := by
  cases m with
  | zero => simp [tA]
  | succ t =>
    rw [nested_minor_expansion_zero_one, nested_minor_expansion_one_zero]
    have hterm : ∀ i j : Fin (t + 1),
        star (((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E i.succAbove j.succAbove (u - 1))) =
          ((-1 : ℂ) ^ ((j : ℕ) + (i : ℕ)) * xb j) •
            (qminor E j.succAbove i.succAbove (star u - 1) * Y i) := by
      intro i j
      rw [star_smul, star_mul (Yb i), star1 hSM E ε hGl hE, hYb i, star_smul, star_star, starE, hxb j, star_mul,
        star_pow, star_neg, star_one, star_sub, star_one]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      congr 1
      have h1 := eSq (ε i)
      linear_combination ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * star (x j) * ((ε j : ℤ) : ℂ)) * h1
    simp only [star_neg, star_sum, hterm]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hmv := mvC hMV E Y hGl hLY hYY a.succAbove id (star u)
    simp only [Function.id_comp, id] at hmv
    have e1 : ∀ i : Fin (t + 1), ((-1 : ℂ) ^ ((a : ℕ) + (i : ℕ)) * xb a) • (qminor E a.succAbove i.succAbove (star u - 1) * Y i)
        = ((-1 : ℂ) ^ (a : ℕ) * xb a) • (((-1 : ℂ) ^ (i : ℕ)) • (qminor E a.succAbove i.succAbove (star u - 1) * Y i)) := by
      intro i; rw [smul_smul, pow_add]; ring_nf
    have e2 : ∀ j : Fin (t + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ)) * xb a) • (Y j * qminor E a.succAbove j.succAbove (star u))
        = ((-1 : ℂ) ^ (a : ℕ) * xb a) • (((-1 : ℂ) ^ (j : ℕ)) • (Y j * qminor E a.succAbove j.succAbove (star u))) := by
      intro j; rw [smul_smul, pow_add]; ring_nf
    simp only [e1, e2, ← Finset.smul_sum, hmv]

end PI.QnHermHaar
end
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section test

variable {k r : ℕ} {i : Fin (r + 1)}

theorem smoothLev_zero : SmoothLev k r i Set.univ (0 : Mx k r → ℂ) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => (0 : ℂ), isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem smoothLev_add {f h : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) (hh : SmoothLev k r i Set.univ h) :
    SmoothLev k r i Set.univ (f + h) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨V, G, hV, hgV, hG, hhG⟩ := hh g₀ hg₀
  refine ⟨U ∩ V, fun x => F x + G x, hU.inter hV, ⟨hgU, hgV⟩,
    (hF.mono Set.inter_subset_left).add (hG.mono Set.inter_subset_right), fun g hg hgl => ?_⟩
  show f g + h g = F g + G g
  rw [hfF g hg.1 hgl, hhG g hg.2 hgl]

theorem smoothLev_smul (c : ℂ) {f : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) :
    SmoothLev k r i Set.univ (c • f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun x => c * F x, hU, hgU, contDiffOn_const.mul hF, fun g hg hgl => ?_⟩
  show c • f g = c * F g
  rw [hfF g hg hgl, smul_eq_mul]

theorem cptOn_zero : CptOn k r i (0 : Mx k r → ℂ) :=
  ⟨∅, isCompact_empty, fun _ _ _ => rfl⟩

theorem cptOn_add {f h : Mx k r → ℂ} (hf : CptOn k r i f) (hh : CptOn k r i h) : CptOn k r i (f + h) := by
  obtain ⟨K, hK, hfK⟩ := hf
  obtain ⟨L, hL, hhL⟩ := hh
  refine ⟨K ∪ L, hK.union hL, fun g hg hn => ?_⟩
  have h1 : g ∉ K := fun hk => hn (Or.inl hk)
  have h2 : g ∉ L := fun hl => hn (Or.inr hl)
  show f g + h g = 0
  rw [hfK g hg h1, hhL g hg h2, add_zero]

theorem cptOn_smul (c : ℂ) {f : Mx k r → ℂ} (hf : CptOn k r i f) : CptOn k r i (c • f) := by
  obtain ⟨K, hK, hfK⟩ := hf
  refine ⟨K, hK, fun g hg hn => ?_⟩
  show c • f g = 0
  rw [hfK g hg hn, smul_zero]

def testSub (k r : ℕ) (i : Fin (r + 1)) : Submodule ℂ (Mx k r → ℂ) where
  carrier := {f | TestF k r i f}
  zero_mem' := ⟨smoothLev_zero, cptOn_zero⟩
  add_mem' hf hh := ⟨smoothLev_add hf.1 hh.1, cptOn_add hf.2 hh.2⟩
  smul_mem' c _ hf := ⟨smoothLev_smul c hf.1, cptOn_smul c hf.2⟩

theorem mem_testSub {f : Mx k r → ℂ} : f ∈ testSub k r i ↔ TestF k r i f :=
  Iff.rfl

theorem posL_inj {a b : Fin (mdim k r i)} (h : posL k r i a = posL k r i b) : a = b := by
  have h' : a.val + i.val = b.val + i.val := congrArg Fin.val h
  exact Fin.ext (by omega)

end test

structure Hyp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (μ : Measure (Mt k r)) : Prop where
  hμ : Formalism.FourierDecayAlt.B.IsHaarOn (Glev k r i) μ
  hz : inWb k r z
  hz' : inWb k r z'
  ET : EabTest
  EA : EabAdj
  MT : MulTest
  TI : TestInt
  Yb : YbRel
  Xb : XbRel
  HF : HmFacts
  EP : EabPres
  Gl : EabGlLev
  YL : YLeibniz

section main

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}

abbrev ιo (k r : ℕ) : Mt k r → Mx k r := fun x => Matrix.of x

theorem hI (H : Hyp k r z z' i μ) : IntOn μ (ιo k r) (testSub k r i) :=
  fun f hf h hh => H.TI k r i μ H.hμ f h hf hh

theorem hG (H : Hyp k r z z' i μ) : ∀ᵐ x ∂μ, ιo k r x ∈ Glev k r i := by
  first
    | exact ae_iff.mpr H.hμ.conc
    | (rw [ae_iff]; exact H.hμ.conc)

def EOp (k r : ℕ) (i : Fin (r + 1)) (a b : Fin (mdim k r i)) : (Mx k r → ℂ) → Mx k r → ℂ :=
  EH k r (posL k r i a) (posL k r i b)

def EOp' (k r : ℕ) (i : Fin (r + 1)) (a b : Fin (mdim k r i)) : (Mx k r → ℂ) → Mx k r → ℂ :=
  fun f g => ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EH k r (posL k r i c) (posL k r i d) f g

def MOp {k r : ℕ} (φ : Mx k r → ℂ) : (Mx k r → ℂ) → Mx k r → ℂ := fun f g => φ g * f g

def MOp' {k r : ℕ} (φ : Mx k r → ℂ) : (Mx k r → ℂ) → Mx k r → ℂ := fun f g => star (φ g) * f g

theorem EOp'_eq (a b : Fin (mdim k r i)) (f : Mx k r → ℂ) :
    EOp' k r i a b f = ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EOp k r i c d f := by
  funext g
  simp only [EOp', EOp, Finset.sum_apply, Pi.smul_apply]

theorem adjOp_E (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) :
    AdjOp (μ := μ) (ι := ιo k r) (𝓕 := testSub k r i) (Glev k r i) (EOp k r i a b) (EOp' k r i a b) := by
  refine ⟨fun f hf => H.ET k r i a b f hf, ?_, ?_, ?_, fun f hf h hh => H.EA k r i μ H.hμ a b f h hf hh⟩
  · intro f hf
    rw [EOp'_eq]
    exact Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ =>
      Submodule.smul_mem _ _ (H.ET k r i c d f hf)
  · intro f hf h hh c g hg
    have := (H.EP ℂ k r z i Set.univ a b f h c isOpen_univ hf.1 hh.1).2.2 g ⟨hg, trivial⟩
    simpa only [EOp, smul_eq_mul] using this
  · intro f hf h hh c g hg
    simp only [EOp']
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c' _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    have := (H.EP ℂ k r z i Set.univ c' d f h c isOpen_univ hf.1 hh.1).2.2 g ⟨hg, trivial⟩
    simp only [smul_eq_mul] at this ⊢
    rw [this]
    ring

theorem adjOp_M (φ : Mx k r → ℂ)
    (hφ : ∀ f, TestF k r i f → TestF k r i (fun g => φ g * f g) ∧ TestF k r i (fun g => star (φ g) * f g)) :
    AdjOp (μ := μ) (ι := ιo k r) (𝓕 := testSub k r i) (Glev k r i) (MOp φ) (MOp' φ) := by
  refine ⟨fun f hf => (hφ f hf).1, fun f hf => (hφ f hf).2, ?_, ?_, ?_⟩
  · intro f _ h _ c g _
    simp only [MOp]
    ring
  · intro f _ h _ c g _
    simp only [MOp']
    ring
  · intro f _ h _
    unfold pr MOp MOp'
    congr 1
    funext x
    rw [star_star_mul]
    ring

theorem yTest (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) (f : Mx k r → ℂ) (hf : TestF k r i f) :
    TestF k r i (fun g => yv k r z i g c * f g) ∧ TestF k r i (fun g => star (yv k r z i g c) * f g) :=
  ⟨(H.MT k r z i c f hf).1, (H.MT k r z i c f hf).2.1⟩

theorem ybTest (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) (f : Mx k r → ℂ) (hf : TestF k r i f) :
    TestF k r i (fun g => ybv k r z i g c * f g) ∧ TestF k r i (fun g => star (ybv k r z i g c) * f g) :=
  ⟨(H.MT k r z i c f hf).2.2.1, (H.MT k r z i c f hf).2.2.2⟩

def EA (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : A (hI H) := toA (hI H) (hG H) (adjOp_E H a b)

def YA (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) : A (hI H) :=
  toA (hI H) (hG H) (adjOp_M (fun g => yv k r z i g c) (yTest H c))

def YbA (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) : A (hI H) :=
  toA (hI H) (hG H) (adjOp_M (fun g => ybv k r z i g c) (ybTest H c))

theorem repE (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : RepOn (hI H) (EA H a b) (EOp k r i a b) :=
  repOn_toA (hI H) (hG H) (adjOp_E H a b)

theorem repY (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) :
    RepOn (hI H) (YA H c) (MOp (fun g => yv k r z i g c)) :=
  repOn_toA (hI H) (hG H) (adjOp_M _ (yTest H c))

theorem repYb (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) :
    RepOn (hI H) (YbA H c) (MOp (fun g => ybv k r z i g c)) :=
  repOn_toA (hI H) (hG H) (adjOp_M _ (ybTest H c))

end main

end PI.QnHermHaar
end
end
