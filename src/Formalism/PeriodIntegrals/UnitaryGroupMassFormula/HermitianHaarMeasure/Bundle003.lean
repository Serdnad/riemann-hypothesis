module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Development
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.GeneralSecondMinorExpansion
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.LowerRightNeZeroOfUpperRightZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem rel_posL_val (k r : ℕ) (i : Fin (r + 1)) (l : Fin (mdim k r i)) :
    (posL k r i l).val = l.val + i.val := rfl

theorem rel_posL_injective (k r : ℕ) (i : Fin (r + 1)) : Function.Injective (posL k r i) := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Fin.val h
  rw [rel_posL_val, rel_posL_val] at h'
  omega

theorem rel_posL_bound (k r : ℕ) (i : Fin (r + 1)) (l : Fin (mdim k r i)) :
    i.val ≤ (posL k r i l).val ∧ (posL k r i l).val + i.val ≤ 2 * r + k := by
  rw [rel_posL_val]
  have hl : l.val < 2 * (r - i.val) + k + 1 := l.isLt
  have hi := i.isLt
  omega

theorem rel_hpk_off_left (k r : ℕ) (p q : Fin (2 * r + k + 1)) (j : ℕ)
    (hp : j ≤ p.val ∧ p.val + j ≤ 2 * r + k) (hq : q.val < j ∨ 2 * r + k < q.val + j) :
    Hpk k r q p = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem rel_hpk_off_right (k r : ℕ) (p q : Fin (2 * r + k + 1)) (j : ℕ)
    (hp : j ≤ p.val ∧ p.val + j ≤ 2 * r + k) (hq : q.val < j ∨ 2 * r + k < q.val + j) :
    Hpk k r p q = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem rel_sum_posL (k r : ℕ) (i : Fin (r + 1)) (F : Fin (2 * r + k + 1) → ℂ)
    (hF : ∀ a : Fin (2 * r + k + 1), (a.val < i.val ∨ 2 * r + k < a.val + i.val) → F a = 0) :
    ∑ a, F a = ∑ l : Fin (mdim k r i), F (posL k r i l) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := posL k r i)
    (fun x _ y _ h => rel_posL_injective k r i h)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hF
  by_contra hc
  push_neg at hc
  apply ha
  have hi := i.isLt
  refine Finset.mem_image.2 ⟨⟨a.val - i.val, ?_⟩, Finset.mem_univ _, ?_⟩
  · show a.val - i.val < 2 * (r - i.val) + k + 1
    omega
  · apply Fin.ext
    show a.val - i.val + i.val = a.val
    omega

theorem rel_herm_unitary {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hU : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hU]

theorem rel_herm_bvec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (p : Fin n) (y : Fin n → ℂ) :
    herm H (bvec p) y = ∑ a, star (y a) * H a p := by
  unfold herm bvec
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

theorem conjugate_y_relation : YbRel := by
  intro k r z i _ g hg c
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  obtain ⟨_, hI, -⟩ := hpkFacts k r
  have hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc (Hpk k r * gᴴ), Matrix.mul_assoc (Hpk k r), ← Matrix.mul_assoc gᴴ, hU, hI]
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse hleft
  have hf : fvec k r z i = g *ᵥ (g⁻¹ *ᵥ fvec k r z i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have key : herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) =
      herm (Hpk k r) (bvec (posL k r i c)) (g⁻¹ *ᵥ fvec k r z i) := by
    conv_lhs => rw [hf]
    exact rel_herm_unitary _ _ hU _ _
  have hsum := rel_sum_posL k r i
    (fun a => star ((g⁻¹ *ᵥ fvec k r z i) a) * Hpk k r a (posL k r i c)) (by
      intro a ha
      show star ((g⁻¹ *ᵥ fvec k r z i) a) * Hpk k r a (posL k r i c) = 0
      rw [rel_hpk_off_left k r (posL k r i c) a i.val (rel_posL_bound k r i c) ha, mul_zero])
  show herm (Hpk k r) (g *ᵥ bvec (posL k r i c)) (fvec k r z i) =
    ∑ l, Hm k r i l c * star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l))
  rw [key, rel_herm_bvec]
  refine hsum.trans (Finset.sum_congr rfl fun l _ => ?_)
  show star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l)) * Hpk k r (posL k r i l) (posL k r i c) =
    Hm k r i l c * star ((g⁻¹ *ᵥ fvec k r z i) (posL k r i l))
  rw [mul_comm]
  rfl

theorem conjugate_x_relation : XbRel := by
  intro k r z' i _ c
  have hsum := rel_sum_posL k r i
    (fun a => star (fvec k r z' i a) * Hpk k r a (posL k r i c)) (by
      intro a ha
      show star (fvec k r z' i a) * Hpk k r a (posL k r i c) = 0
      rw [rel_hpk_off_left k r (posL k r i c) a i.val (rel_posL_bound k r i c) ha, mul_zero])
  show herm (Hpk k r) (bvec (posL k r i c)) (fvec k r z' i) =
    ∑ l, Hm k r i l c * star (fvec k r z' i (posL k r i l))
  rw [rel_herm_bvec]
  refine hsum.trans (Finset.sum_congr rfl fun l _ => ?_)
  show star (fvec k r z' i (posL k r i l)) * Hpk k r (posL k r i l) (posL k r i c) =
    Hm k r i l c * star (fvec k r z' i (posL k r i l))
  rw [mul_comm]
  rfl

theorem restricted_gram_hermitian_involution : HmFacts := by
  intro k r i
  obtain ⟨hH, hI, -⟩ := hpkFacts k r
  constructor
  · ext a b
    show star (Hpk k r (posL k r i b) (posL k r i a)) = Hpk k r (posL k r i a) (posL k r i b)
    rw [← Matrix.conjTranspose_apply (Hpk k r), hH]
  · ext a b
    have h1 : (Hm k r i * Hm k r i) a b = (Hpk k r * Hpk k r) (posL k r i a) (posL k r i b) := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      symm
      refine rel_sum_posL k r i
        (fun q => Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b)) ?_
      intro q hq
      show Hpk k r (posL k r i a) q * Hpk k r q (posL k r i b) = 0
      rw [rel_hpk_off_right k r (posL k r i a) q i.val (rel_posL_bound k r i a) hq, zero_mul]
    rw [h1, hI, Matrix.one_apply, Matrix.one_apply]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg h, if_neg (fun e => h (rel_posL_injective k r i e))]

end PI.QnHermHaar
end
end

section

open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem hermitian_algebra_generation : HermAlgFrom := by
  unfold HermAlgFrom HermAlg
  intro hSM hCC hMV hMC A _ _ _ _ m E Y Yb Hm x xb hGl hHm hHm2 hstarE hYY hYbYb hYYb hLY hLYb hYbH hxbH u p q

  obtain ⟨P, Q, ε, hQP, hPQ, hPs, hQs, hHmP, hQHm⟩ : ∃ (P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ),
      Q * P = 1 ∧ P * Q = 1 ∧ (∀ i j, star (P i j) = Q j i) ∧ (∀ i j, star (Q i j) = P j i) ∧
      (∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ)) ∧
      (∀ a l, ∑ i, Q a i * Hm i l = ((ε a : ℤ) : ℂ) * Q a l) := by
    have hH : Hm.IsHermitian := hHm
    set P : Matrix (Fin m) (Fin m) ℂ := (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hPdef
    have hQP : star P * P = 1 := by
      first
        | exact Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
        | exact unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
        | exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    have hPQ : P * star P = 1 := by
      first
        | exact Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
        | exact unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
        | exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
    set d : Fin m → ℂ := fun b => ((hH.eigenvalues b : ℝ) : ℂ) with hd
    have hspec : Hm = P * Matrix.diagonal d * star P := by
      first
        | exact hH.spectral_theorem
        | exact Matrix.IsHermitian.spectral_theorem hH
    have hHP : Hm * P = P * Matrix.diagonal d := by
      rw [hspec]
      simp only [Matrix.mul_assoc, hQP, Matrix.mul_one]
    have hQH : star P * Hm = Matrix.diagonal d * star P := by
      rw [hspec]
      simp only [← Matrix.mul_assoc, hQP, Matrix.one_mul]
    have hPHP : star P * Hm * P = Matrix.diagonal d := by
      rw [hQH, Matrix.mul_assoc, hQP, Matrix.mul_one]
    have hD2 : Matrix.diagonal d * Matrix.diagonal d = 1 := by
      rw [← hPHP]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P (star P), hPQ, Matrix.one_mul, ← Matrix.mul_assoc Hm Hm, hHm2, Matrix.one_mul, hQP]
    have hdd : ∀ b, hH.eigenvalues b * hH.eigenvalues b = 1 := fun b => by
      have h1 := congrFun (congrFun hD2 b) b
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
      have h2 : ((hH.eigenvalues b : ℝ) : ℂ) * ((hH.eigenvalues b : ℝ) : ℂ) = 1 := h1
      exact_mod_cast h2
    have hεd : ∀ b, (((if hH.eigenvalues b = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) : ℂ) = d b := fun b => by
      rcases mul_self_eq_one_iff.mp (hdd b) with h | h
      · simp [hd, h]
      · have hne : hH.eigenvalues b ≠ 1 := by rw [h]; norm_num
        rw [if_neg hne]
        simp [hd, h]
    refine ⟨P, star P, fun b => if hH.eigenvalues b = 1 then 1 else -1, hQP, hPQ,
      fun i j => by rw [Matrix.star_apply], fun i j => by rw [Matrix.star_apply, star_star], fun k b => ?_,
      fun a l => ?_⟩
    · have h1 := congrFun (congrFun hHP k) b
      rw [Matrix.mul_apply, Matrix.mul_diagonal] at h1
      rw [h1]
      congr 1
      exact (hεd b).symm
    · have h1 := congrFun (congrFun hQH a) l
      rw [Matrix.mul_apply, Matrix.diagonal_mul] at h1
      rw [h1]
      congr 1
      exact (hεd a).symm

  have hGl' := glConj E P Q hGl hQP
  have hE' := starConj E Hm P Q ε hstarE hPs hQs hHmP hQHm
  have hYY' := commVec Y Q hYY
  have hYbYb' := commCov Yb P hYbYb
  have hLY' := leibVec E Y P Q hQP hLY
  have hLYb' := leibCov E Yb P Q hQP hLYb
  have hYb' : ∀ c, covC P Yb c = ((ε c : ℤ) : ℂ) • star (vecC Q Y c) := by
    intro c
    simp only [covC, vecC, hYbH, star_sum, star_smul, hQs, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    calc ∑ l, P l c * Hm l' l = ∑ l, Hm l' l * P l c := Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = P l' c * ((ε c : ℤ) : ℂ) := hHmP l' c
      _ = ((ε c : ℤ) : ℂ) * P l' c := mul_comm _ _
  have hxb' : ∀ c, (xb ᵥ* P) c = ((ε c : ℤ) : ℂ) * star ((Q *ᵥ x) c) := by
    intro c
    show ∑ l, xb l * P l c = ((ε c : ℤ) : ℂ) * star (∑ k, Q c k * x k)
    simp only [hxbH, star_sum, star_mul', hQs, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    have e1 : ∑ l, Hm l' l * star (x l') * P l c = star (x l') * ∑ l, Hm l' l * P l c := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, hHmP l' c]
    ring
  rw [tATrans hCC E Y Yb x xb P Q hGl hQP hPQ u p q, tATrans hCC E Y Yb x xb P Q hGl hQP hPQ (star u) q p]
  fin_cases p <;> fin_cases q
  · exact star_transfer_diagonal_zero hSM _ _ _ _ _ ε hGl' hE' u
  · exact star_transfer_zero_one hSM hMV _ _ _ _ _ ε hGl' hE' hYY' hLY' hYb' hxb' u
  · have h := congrArg star (star_transfer_zero_one hSM hMV _ _ _ _ _ ε hGl' hE' hYY' hLY' hYb' hxb' (star u))
    rw [star_star, star_star] at h
    exact h.symm
  · exact lower_right_ne_zero_of_upper_right_zero hSM hMV hMC _ _ _ _ _ ε hGl' hE' hYY' hYbYb' hLY' hLYb' hYb' hxb' u

end PI.QnHermHaar
end
end
