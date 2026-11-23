module

public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AAvCongr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle071
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle069
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle070
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem det_star {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.of fun a b => star (M a b)).det = star M.det := by
  have e : (Matrix.of fun a b => star (M a b)) = M.conjTranspose.transpose := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  rw [e, Matrix.det_transpose, Matrix.det_conjTranspose]

theorem keyS_sR (k r m : ℕ) (hm : m ≤ r) (l : Fin m) : keyS k r (sR k r m hm l) = l.val := by
  simp only [sR]
  rw [keyS_esI]
  rfl

theorem AAv_head {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 : ℕ) (hi0 : i0 ≤ r) (h : Matrix (Fin i0) (Fin i0) ℂ) (ell : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 → p ∉ Set.range (sR k r i0 hi0) → y a p = 0)
    (hh : ∀ a b : Fin i0, y (Fin.castLE hi0 a) (sR k r i0 hi0 b) = star (h a b)) :
    AAv k r E y i0 hi0 ell = star h.det • qminor E (sR k r i0 hi0) (sR k r i0 hi0) (ell + (i0 : ℂ) - 1) := by
  classical
  have he : StrictMono (fun l => keyS k r (sR k r i0 hi0 l)) := by
    intro a b hab
    simp only [keyS_sR]
    exact hab
  have hX : ∀ (a : Fin i0) (p : Fin (2 * r + k + 1)), p ∉ Set.range (sR k r i0 hi0) →
      y (Fin.castLE hi0 a) p = 0 := by
    intro a p hp
    exact hz _ p a.isLt hp
  have hu : ∀ c : Fin i0 → Fin (2 * r + k + 1), StrictMono (fun l => keyS k r (c l)) →
      (∀ l, c l ∈ Set.range (sR k r i0 hi0)) → c = sR k r i0 hi0 := by
    intro c hc hS
    exact uniq_key (keyS k r) (keyS_inj k r) (sR k r i0 hi0) c he hc hS
  have hs := sum_single (M := A) (fun B : Fin i0 → Fin (2 * r + k + 1) => StrictMono (fun l => keyS k r (B l)))
    (fun a p => y (Fin.castLE hi0 a) p) (Set.range (sR k r i0 hi0)) hX (sR k r i0 hi0) he hu
    (fun B => qminor E B (sR k r i0 hi0) (ell + (i0 : ℂ) - 1))
  have hdet : (Matrix.of fun a l : Fin i0 => y (Fin.castLE hi0 a) (sR k r i0 hi0 l)).det = star h.det := by
    rw [← det_star]
    congr 1
    ext a b
    exact hh a b
  unfold AAv
  rw [← hdet]
  convert hs using 1

theorem second_expansion_identity : ExpansionDualColumn := by
  intro A _ _ M _ _ k r z' E La y i0 s h t ell hs hj hG hR hh ht hy
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hm : i0 + s' ≤ r := by omega
  have hm' : i0 + s' + 1 ≤ r := by omega
  rw [AAv_congr k r E y (show i0 + (s' + 1) - 1 = i0 + s' by omega) _ hm]
  set e2 : Fin (i0 + s') → Fin (2 * r + k + 1) :=
    fun l => sR k r (i0 + s' + 1) hm' ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l) with he2def
  have he2v : ∀ l, (e2 l).val = 2 * r + k - ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val := by
    intro l; simp [e2, sR, esI]
  have he2k : ∀ l, keyS k r (e2 l) = ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val := by
    intro l; simp only [e2]; rw [keyS_sR]
  have he2 : StrictMono (fun l => keyS k r (e2 l)) := by
    intro a b hab
    simp only [he2k]; exact Fin.strictMono_succAbove _ hab
  have hAA : AAv k r E y (i0 + s') hm ell =
      star (h.det * t ^ s' * sgnW s') • qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1) := by
    unfold AAv
    rw [sum_single (fun B => StrictMono (fun l => keyS k r (B l))) (fun a p => y (Fin.castLE hm a) p)
      (Set.range e2) ?_ e2 he2 ?_]
    · congr 1
      have hp := minors_first_case i0 s' h t ⟨i0, by omega⟩
      rw [if_pos rfl] at hp
      rw [← hp, ← det_star]
      congr 1
      ext a l
      simp only [Matrix.of_apply]
      have hl := ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).isLt
      rw [hy _ _ (by simp; omega), if_pos (by rw [he2v]; omega), he2v]
      congr 2 <;> (try simp) <;> omega
    · intro a p hp
      rw [hy _ _ (by simp; omega)]
      split_ifs with h1
      · by_cases hpi : 2 * r + k - p.val = i0
        · rw [hpi, zb_col_zero i0 s' h t _ (by simp), star_zero]
        · exfalso; apply hp
          refine ⟨⟨if 2 * r + k - p.val < i0 then 2 * r + k - p.val else 2 * r + k - p.val - 1,
            by split_ifs <;> omega⟩, ?_⟩
          ext; rw [he2v, succAbove_val]; simp only; split_ifs <;> omega
      · rfl
    · intro c hc hS; exact uniq_key (keyS k r) (keyS_inj k r) _ _ he2 hc hS
  have hhead : AAv k r E y i0 (by omega) ell =
      star h.det • qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1) := by
    apply AAv_head
    · intro a p ha hp
      rw [hy _ _ (by omega)]
      split_ifs with hc
      · have hx : ¬ (2 * r + k - p.val < i0) := by
          intro hlt; apply hp
          exact ⟨⟨2 * r + k - p.val, hlt⟩, by ext; simp [sR, esI]; omega⟩
        unfold Zb; rw [dite_eq_left ha, dite_eq_right hx, star_zero]
      · rfl
    · intro a b
      have hb := b.isLt
      rw [hy _ _ (by simp; omega)]
      rw [if_pos (by simp [sR, esI]; omega)]
      have hsv : (sR k r i0 (by omega) b).val = 2 * r + k - b.val := by simp [sR, esI]
      have hav : (Fin.castLE (by omega : i0 ≤ r) a).val = a.val := by simp
      unfold Zb
      rw [hav, hsv]
      rw [dite_eq_left a.isLt, dite_eq_left (by omega)]
      congr 2
      apply Fin.ext; simp only [Fin.val_mk]; omega
  have hP := third_peeling_identity A k r z' E hG (i0 + s') hm' ⟨i0, by omega⟩ ell
  have hLa : La (qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1)) =
      La (qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1)) := la_congr hR hP
  rw [hAA, hhead, map_smul, map_smul, hLa, (derivative_leading_zb i0 (s' + 1) h t).1, (derivative_leading_zb i0 (s' + 1) h t).2,
    smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [star_mul', star_pow, star_sgnW, sgnW_succ, Nat.add_sub_cancel, star_neg, star_one]
  rw [scal_E (star h.det) (star t) (sgnW s') ((-1) ^ s') s' (star_ne_zero.mpr hh) (star_ne_zero.mpr ht)
    (sgnW_sq s') (neg_one_sq' s')]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem la_intmul {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (La : A →ₗ[ℂ] M) (z : ℤ) (x : A) :
    La ((z : A) * x) = (z : ℂ) • La x := by
  have hz : ((z : A) * x) = (z : ℂ) • x := by
    rw [Algebra.smul_def, map_intCast]
  rw [hz, map_smul]

theorem chain_first_identity : LastColumnChain := by
  intro A _ _ M _ _ k r z' c E La hG hc hR hL m hm u
  set a := xR k r (m + 2) hm with hadef
  have hav : ∀ l, (a l).val = l.val := by intro l; simp [a, xR, eI]
  have hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega) := by
    funext l; ext; simp [a, xR, eI]
  have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u

  rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]

  have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
    intro l
    rw [la_intmul]
    have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
    rw [tm_offdiag _ _ hne, hR _ _ _ (by simp only [InNp, hav]; simp; omega)]
    have : dpsiP k r z' (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))) = 0 := by
      unfold dpsiP; simp only [hav]; simp; split_ifs <;> first | rfl | omega
    rw [this, zero_smul, smul_zero]
  rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]

  have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) := by
    rw [la_intmul, Fin.succAbove_last, hcs]
    have h1 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [h1]
    have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
      simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
    rw [h2]; simp
  rw [hlast]

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (eI k r ⟨m + 1, by omega⟩) (xR k r m (by omega)) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [eI]
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [xR, eI]; omega
  have hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]

    rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      have hrs : rowsP ∘ Fin.succ = xR k r m (by omega) := by funext q; simp [rowsP]
      rw [hr0, hrs, Fin.succAbove_last, hcs]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.last m) := by
        intro h'; have := congrArg Fin.val h'; simp [eI, xR] at this
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.last m) = eI k r ⟨m, by omega⟩ := by ext; simp [xR, eI]
      rw [hx, hL _ ⟨m + 1, by omega⟩ ⟨m, by omega⟩ (by simp), if_pos rfl]
      have hcs2 : xR k r (m + 1) (by omega) ∘ Fin.castSucc = xR k r m (by omega) := by funext q; ext; simp [xR, eI]
      rw [hcs2, smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_last]
      push_cast
      rw [neg_one_sq', one_mul]
    · intro q _
      rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      rw [hr0, hcs]
      have hqv : (xR k r (m + 1) (by omega) (Fin.castSucc q)).val = q.val := by simp [xR, eI]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.castSucc q) := by
        intro h'; have := congrArg Fin.val h'; rw [hqv] at this; simp [eI] at this; omega
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.castSucc q) = eI k r ⟨q.val, by omega⟩ := by ext; simp [xR, eI]
      rw [hx, hL _ ⟨m + 1, by omega⟩ ⟨q.val, by omega⟩ (by simp <;> omega), if_neg (by simp <;> omega), zero_smul, smul_zero]
  have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
      Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
    rw [tm_offdiag _ _ hne, hR _ _ _ (by simp only [InNp, hav]; simp; omega)]
    have : dpsiP k r z' (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1))) = 1 := by
      unfold dpsiP; simp only [hav]; simp; split_ifs <;> first | rfl | omega
    rw [this, one_smul]
  rw [la_intmul, hmT, hQm]
  have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h3, neg_one_smul]; abel

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.BesselScaling

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem haar_smul {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) (c : ℝ≥0) (hc : 0 < c) :
    IsHaarOn U (c • μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, h.conc, smul_zero]
  · intro a ha
    have hcont : Continuous (lmulM a : Mt k r → Mt k r) := by
      unfold lmulM
      exact (continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))
    rw [Measure.map_smul c hcont.measurable.aemeasurable, h.left a ha]
  · intro a ha
    have hcont : Continuous (rmulF a) := by
      unfold rmulF
      exact (continuous_id (X := Mat k r)).matrix_mul continuous_const
    rw [Measure.map_smul c hcont.measurable.aemeasurable, h.right a ha]
  · intro K hK
    rw [smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK)
  · intro h0
    apply h.ne_zero
    have h1 : (c • μ) Set.univ = 0 := by rw [h0]; rfl
    rw [smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (by exact_mod_cast h2 : c = 0) hc.ne'
    · exact Measure.measure_univ_eq_zero.mp h2

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def scaleG (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) : RealPlaceData k r Wp Wq :=
  { D with μG := c • D.μG, haarG := haar_smul D.haarG c hc }

theorem iteratedDeriv_two_const_mul (c : ℂ) (f : ℝ → ℂ) :
    iteratedDeriv 2 (fun x => c * f x) = fun x => c * iteratedDeriv 2 f x := by
  have h2 : ∀ g : ℝ → ℂ, iteratedDeriv 2 g = deriv (deriv g) := by
    intro g
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, h2, deriv_const_mul_field', deriv_const_mul_field']

theorem oneMinusDD_const_mul (c : ℂ) (h : ℝ → ℝ → ℂ) (t₁ t₂ : ℝ) :
    oneMinusDD (fun a b => c * h a b) t₁ t₂ = c * oneMinusDD h t₁ t₂ := by
  simp only [oneMinusDD, iteratedDeriv_two_const_mul, ← mul_sub]

variable [FiniteDimensional ℂ Wq]

theorem ph_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) :
    Ph (scaleG D c hc) F F' p = ((c : ℝ) : ℂ) * Ph D F F' p := by
  have hμ : (scaleG D c hc).μG = c • D.μG := rfl
  unfold Ph
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  try rfl

theorem betaInf_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    betaInf (scaleG D c hc) F F' = ((c : ℝ) : ℂ) * betaInf D F F' := by
  have hreg : ∀ p, regBracket (scaleG D c hc) F F' p =
      fun a b => ((c : ℝ) : ℂ) * regBracket D F F' p a b := by
    intro p
    funext a b
    have hχ : (scaleG D c hc).χ = D.χ := rfl
    simp only [regBracket]
    rw [ph_scale, hχ]
    ring
  have hz : (scaleG D c hc).z = D.z := rfl
  have hz' : (scaleG D c hc).z' = D.z' := rfl
  have hS : (scaleG D c hc).μSS = D.μSS := rfl
  unfold betaInf betaInfTau
  simp only [hreg, hz, hz', hS, oneMinusDD_const_mul, mul_assoc, integral_const_mul]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring
end

theorem anyFromNorm : LemmaBNorm → IntNormB → LemmaBAny := by
  intro hN hB k r Wp Wq _ _ _ _ _ _ D A hA
  obtain ⟨c, ⟨hc, hF⟩, -⟩ := hB k r Wp Wq D
  have hF' : IntFormula (scaleG D c hc) := hF
  obtain ⟨h1, h2, h3, h4⟩ := hN k r Wp Wq (scaleG D c hc) A hA hF'
  refine ⟨c, hc, hF, h1, ?_, ?_, h4⟩
  · intro F F' hF1 hF2
    have hb : beta (scaleG D c hc) F F' = beta D F F' := rfl
    rw [← hb, h2 F F' hF1 hF2, betaInf_scale]
  · intro UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4 hIC
    exact h3 UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4
      (fun p hp T hT i j hij hj => (hIC p hp T hT i j hij hj).smul_measure_nnreal)

end Formalism.FourierDecayAlt.P.BesselScaling

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem lemma_b_from_xi_of_parts : Formalism.FourierDecayAlt.B2.LemmaBFromXiFromParts := by
  intro hC hJ hD hI hB hX
  have hN : LemmaBNorm := by
    intro k r Wp Wq _ _ _ _ _ _ D A hA hF
    exact hC hX k r Wp Wq D A hA hF (hJ k r Wp Wq D) (hD k r Wp Wq D) (hI k r Wp Wq D A hA)
  exact ⟨hN, Formalism.FourierDecayAlt.P.BesselScaling.anyFromNorm hN hB⟩

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.BesselScaling

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem lemmaBFromXi_of : ConjInvAll → DilJacAll → CCIntAll → IntNormB → LemmaBFromXi :=
  Formalism.FourierDecayAlt.P.lemma_b_from_xi_of_parts (fun hX => Formalism.FourierDecayAlt.P.bessel_lemma_closed_form hX Formalism.FourierDecayAlt.P.lemma_B_of_components
            Formalism.FourierDecayAlt.P.clause_of_regularized_limit Formalism.FourierDecayAlt.P.adjointness_polynomially_bounded)

end Formalism.FourierDecayAlt.P.BesselScaling
end
end
