module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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

namespace PI.NRL

open Matrix

variable {R : Type*} [CommRing R] {r : ℕ}

def UniUp (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : Prop :=
  (∀ a b, b < a → ξ a b = 0) ∧ ∀ a, ξ a a = 1

def rowMat (a : Fin (r + 1)) (w : Fin (r + 1) → R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  fun d c => if d = a then w c else 0

theorem exists_mul_eq_one_add_smul_of_rows_ge (g : R) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R → Prop)
    (h1 : P 1) (hmul : ∀ M N, P M → P N → P (M * N))
    (hrow : ∀ a : Fin (r + 1), a.val < r → ∀ t : Fin (r + 1) → R, ∃ w : Fin (r + 1) → R,
      (∀ c, c ≤ a → w c = 0) ∧ (∀ c, a < c → ∃ q, w c = t c + g * q) ∧ P (1 + rowMat a w)) :
    ∀ k : ℕ, k ≤ r → ∀ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) R, UniUp ξ →
      (∀ d c : Fin (r + 1), k ≤ d.val → ξ d c = if d = c then 1 else 0) →
      ∃ M, P M ∧ ∃ Q, M * ξ = 1 + g • Q := by
  intro k
  induction k with
  | zero =>
    intro _ ξ _ hid
    refine ⟨1, h1, 0, ?_⟩
    rw [Matrix.one_mul, smul_zero, add_zero]
    ext d c
    rw [hid d c (Nat.zero_le _), Matrix.one_apply]
  | succ k ih =>
    intro hk ξ hξ hid
    let a : Fin (r + 1) := ⟨k, by omega⟩
    have hak : a.val < r := by show k < r; omega
    obtain ⟨w, hw0, hw1, hP⟩ := hrow a hak (fun c => -ξ a c)
    choose! q hq using hw1
    let ξ₀ : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
      fun d c => if d = a then (if d = c then 1 else 0) else ξ d c
    let Q₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
      fun d c => if d = a then (if a < c then q c else 0) else 0
    have hsum : ∀ c, ∑ e, w e * ξ e c = w c := by
      intro c
      have he' : ∀ e, w e * ξ e c = w e * (if e = c then 1 else 0) := by
        intro e
        by_cases he : e ≤ a
        · rw [hw0 e he, zero_mul, zero_mul]
        · rw [hid e c (Fin.lt_iff_val_lt_val.mp (not_le.mp he))]
      rw [Finset.sum_congr rfl (fun e _ => he' e)]
      simp
    have hE : (1 + rowMat a w) * ξ = ξ₀ + g • Q₁ := by
      ext d c
      have hrm : ∑ e, rowMat a w d e * ξ e c = if d = a then w c else 0 := by
        simp only [rowMat]
        split_ifs with hd
        · exact hsum c
        · simp
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply, hrm]
      show ξ d c + (if d = a then w c else 0) =
        (if d = a then (if d = c then 1 else 0) else ξ d c) + g * (if d = a then (if a < c then q c else 0) else 0)
      by_cases hd : d = a
      · rw [hd, if_pos rfl, if_pos rfl, if_pos rfl]
        rcases lt_trichotomy c a with hca | hca | hca
        · rw [hξ.1 a c hca, hw0 c hca.le, if_neg (ne_of_lt hca).symm, if_neg (not_lt.mpr hca.le)]
          simp
        · rw [hca, hξ.2 a, hw0 a le_rfl, if_pos rfl, if_neg (lt_irrefl a)]
          simp
        · rw [hq c hca, if_neg (ne_of_lt hca), if_pos hca]
          ring
      · rw [if_neg hd, if_neg hd, if_neg hd]
        simp
    have hξ₀ : UniUp ξ₀ := by
      refine ⟨fun d c hcd => ?_, fun d => ?_⟩
      · show (if d = a then (if d = c then 1 else 0) else ξ d c) = 0
        by_cases h1' : d = a
        · rw [if_pos h1', if_neg (ne_of_lt hcd).symm]
        · rw [if_neg h1']
          exact hξ.1 d c hcd
      · show (if d = a then (if d = d then 1 else 0) else ξ d d) = 1
        by_cases h1' : d = a
        · rw [if_pos h1', if_pos rfl]
        · rw [if_neg h1']
          exact hξ.2 d
    have hid₀ : ∀ d c : Fin (r + 1), k ≤ d.val → ξ₀ d c = if d = c then 1 else 0 := by
      intro d c hdk
      show (if d = a then (if d = c then 1 else 0) else ξ d c) = _
      by_cases h1' : d = a
      · rw [if_pos h1']
      · rw [if_neg h1']
        apply hid d c
        have hne : d.val ≠ k := fun h' => h1' (Fin.ext h')
        omega
    obtain ⟨M, hM, Q, hMQ⟩ := ih (by omega) ξ₀ hξ₀ hid₀
    refine ⟨M * (1 + rowMat a w), hmul _ _ hM hP, Q + M * Q₁, ?_⟩
    rw [Matrix.mul_assoc, hE, Matrix.mul_add, hMQ, Matrix.mul_smul, smul_add, add_assoc]

theorem row_elim (g : R) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R → Prop)
    (h1 : P 1) (hmul : ∀ M N, P M → P N → P (M * N))
    (hrow : ∀ a : Fin (r + 1), a.val < r → ∀ t : Fin (r + 1) → R, ∃ w : Fin (r + 1) → R,
      (∀ c, c ≤ a → w c = 0) ∧ (∀ c, a < c → ∃ q, w c = t c + g * q) ∧ P (1 + rowMat a w))
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (hξ : UniUp ξ) :
    ∃ M, P M ∧ ∃ Q, M * ξ = 1 + g • Q := by
  refine exists_mul_eq_one_add_smul_of_rows_ge g P h1 hmul hrow r le_rfl ξ hξ fun d c hd => ?_
  have hdl : d = Fin.last r := Fin.ext (by have := d.isLt; simp only [Fin.val_last]; omega)
  subst hdl
  split_ifs with hc
  · subst hc
    exact hξ.2 _
  · exact hξ.1 _ _ (lt_of_le_of_ne (Fin.le_last c) (fun h' => hc h'.symm))

end PI.NRL
end

section

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem star_int (x : 𝓞 E) : ∃ y : 𝓞 E, (y : E) = star (x : E) := by
  have h : IsIntegral ℤ (star (x : E)) := by
    have := (RingOfIntegers.isIntegral_coe x).map (starRingEnd E).toIntAlgHom
    exact this
  exact ⟨⟨star (x : E), h⟩, rfl⟩

def cj (x : 𝓞 E) : 𝓞 E := Classical.choose (star_int x)

@[simp] theorem coe_cj (x : 𝓞 E) : ((cj x : 𝓞 E) : E) = star (x : E) := Classical.choose_spec (star_int x)

theorem exists_beta (P : HeightOneSpectrum (𝓞 E)) :
    ∃ β : E, (∀ p ∈ P.asIdeal, ∃ o : 𝓞 E, β * (p : E) = (o : E)) ∧
      ∀ s : 𝓞 E, s ∉ P.asIdeal → ∀ o : 𝓞 E, (s : E) * β ≠ (o : E) := by
  have hP0 : (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot
  have hnot : ¬ ((P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ ≤ 1) := by
    intro hle
    have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ P.asIdeal := by
      calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
          = P.asIdeal * (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ :=
            (mul_inv_cancel₀ hP0).symm
        _ ≤ P.asIdeal * 1 := mul_le_mul_right hle _
        _ = P.asIdeal := mul_one _
    rw [← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal] at h1
    exact P.isPrime.ne_top (top_le_iff.mp h1)
  obtain ⟨β, hβ, hβ1⟩ := Set.not_subset.mp hnot
  have hmem := (FractionalIdeal.mem_inv_iff hP0).mp hβ
  have hPO : ∀ p ∈ P.asIdeal, ∃ o : 𝓞 E, β * (p : E) = (o : E) := by
    intro p hp
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).mp
      (hmem _ (FractionalIdeal.mem_coeIdeal_of_mem _ hp))
    exact ⟨o, ho.symm⟩
  refine ⟨β, hPO, fun s hs o ho => hβ1 ?_⟩
  obtain ⟨y, i, hi, hyi⟩ := P.isMaximal.exists_inv hs
  obtain ⟨o', ho'⟩ := hPO i hi
  refine (FractionalIdeal.mem_one_iff _).mpr ⟨y * o + o', ?_⟩
  have : β = (y : E) * ((s : E) * β) + β * (i : E) := by
    have h1 : ((y * s + i : 𝓞 E) : E) = 1 := by rw [hyi]; simp
    push_cast at h1
    linear_combination (-β) * h1
  rw [this, ho, ho']
  rw [map_add (f := _), map_mul]

end PI.NRL
end
end
