module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
public import Formalism.HermitianCurvature.StatementWd
public import Mathlib.CategoryTheory.Category.Basic
public import Formalism.HermitianCurvature.Bundle003
public import Formalism.HermitianCurvature.StatementM
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle018

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.Wd1

open Matrix Formalism.FourierDecayAlt.Wd

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem cond_iff (a : S) (i j : Fin 2) (x y : Ix S) :
    (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (x a = i ∧ y = Function.update x a j) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    funext b
    by_cases hb : b = a
    · subst hb; simp [h2]
    · simp [Function.update_apply, hb, h3 b hb]
  · rintro ⟨h1, rfl⟩
    exact ⟨h1, by simp, fun b hb => by simp [Function.update_apply, hb]⟩

theorem eU_apply (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if x a = i ∧ y = Function.update x a j then 1 else 0 := by
  simp only [eU, Matrix.of_apply]
  exact if_congr (cond_iff a i j x y) rfl rfl

theorem eU_mul_apply (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((eU a i j : SlopeTestRemainingChoices S A) * B) x y = if x a = i then B (Function.update x a j) y else 0 := by
  simp only [Matrix.mul_apply, eU_apply, ite_mul, one_mul, zero_mul]
  by_cases hx : x a = i <;> simp [hx]

theorem eU_mul_eU (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x y
  rw [eU_mul_apply]
  by_cases hx : x a = i <;> by_cases hjk : j = k <;> simp [hx, hjk, eU_apply, Function.update_idem]

theorem sum_eU_diag (a : S) : ∑ i, (eU a i i : SlopeTestRemainingChoices S A) = 1 := by
  ext x y
  rw [Matrix.sum_apply, Finset.sum_eq_single (x a)]
  · rw [eU_apply, Matrix.one_apply, Function.update_eq_self]
    by_cases h : x = y
    · subst h; simp
    · have h' : ¬ y = x := fun e => h e.symm
      simp [h, h']
  · intro i _ hi
    rw [eU_apply, if_neg]
    rintro ⟨h, _⟩
    exact hi h.symm
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eU_comm_of_ne {a c : S} (hc : c ≠ a) (i j k l : Fin 2) :
    Commute (eU c i j : SlopeTestRemainingChoices S A) (eU a k l) := by
  show (eU c i j : SlopeTestRemainingChoices S A) * eU a k l = eU a k l * eU c i j
  ext x y
  rw [eU_mul_apply, eU_mul_apply, eU_apply, eU_apply]
  by_cases hxc : x c = i <;> by_cases hxa : x a = k <;>
    simp [Function.update_apply, hc, Ne.symm hc, hxc, hxa, Function.update_comm hc j l x]

theorem star_eU [StarRing A] (a : S) (i j : Fin 2) :
    star (eU a i j : SlopeTestRemainingChoices S A) = eU a j i := by
  ext x y
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  simp only [eU, Matrix.of_apply]
  rw [apply_ite star, star_one, star_zero]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun b hb => (h3 b hb).symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun b hb => (h3 b hb).symm⟩

theorem ins_mul (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 a M) :
    ins a (M * N) = ins a M * ins a N := by
  apply Formalism.FourierDecayAlt.P.Wd7.ins_mul <;> assumption

theorem ins_star [StarRing A] (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 a M) :
    star (ins a M) = ins a Mᴴ := by
  have key : ∀ i j : Fin 2, star ((eU a i j : SlopeTestRemainingChoices S A) * M i j) = eU a j i * star (M i j) := by
    intro i j
    have h := congrArg star (hM i j i j).eq
    rw [star_mul, star_mul, star_eU] at h
    rw [star_mul, star_eU]
    exact h
  simp only [ins, Fin.sum_univ_two, star_add, key, Matrix.conjTranspose_apply]
  abel

theorem ins_one (a : S) : ins a (1 : M2 (SlopeTestRemainingChoices S A)) = 1 := by
  simp only [ins, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  exact sum_eU_diag a

theorem insert_diagonal_extract (a : S) (b : SlopeTestRemainingChoices S A) : ins a (d0 b) = b := by
  simp only [ins, d0, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [← Finset.sum_mul, sum_eU_diag, one_mul]

theorem ins_free {a c : S} (hc : c ≠ a) (M : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 c M) :
    FreeOf c (ins a M) := by
  intro k l
  unfold ins
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  exact (eU_comm_of_ne hc k l i j).mul_right (hM i j k l)

theorem ins_comm (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (b : SlopeTestRemainingChoices S A) (hb : FreeOf a b)
    (hbM : ∀ i j, Commute b (M i j)) : Commute b (ins a M) := by
  unfold ins
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  exact (hb i j).symm.mul_right (hbM i j)

end Formalism.FourierDecayAlt.P.Wd1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.Wd

theorem position_insertion_mul_compat : Formalism.FourierDecayAlt.Wd.InsMul := by
  intro K A S _ _ _ _ _ _ _ _ a M N hM
  exact Wd1.ins_mul a M N hM

theorem position_insertion_star_compat : Formalism.FourierDecayAlt.Wd.InsStar := by
  intro K A S _ _ _ _ _ _ _ _ a M hM
  exact Wd1.ins_star a M hM

theorem position_insertion_diagonal_compat : Formalism.FourierDecayAlt.Wd.InsDiag := by
  intro K A S _ _ _ _ _ _ _ _ a b
  exact ⟨Wd1.ins_one a, Wd1.insert_diagonal_extract a b⟩

theorem position_insertion_free_compat : Formalism.FourierDecayAlt.Wd.InsFree := by
  intro K A S _ _ _ _ _ _ _ _ a M
  exact ⟨fun c hc hM => Wd1.ins_free hc M hM, fun b hb hbM => Wd1.ins_comm a M b hb hbM⟩

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.DualKernelLemmas

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

end Rep

theorem real_bound (u v c b : ℂ) (hc : c ≠ 0) (hu : u.im = 0) (hv : v.im = 0)
    (hb : ‖b‖ ^ 2 ≤ u.re * v.re) :
    (u * (c * v) / c).im = 0 ∧ ‖b‖ ^ 2 ≤ (u * (c * v) / c).re := by
  have h : u * (c * v) / c = u * v := by field_simp <;> ring
  rw [h]
  constructor
  · simp [Complex.mul_im, hu, hv]
  · simpa [Complex.mul_re, hu, hv] using hb

theorem qw_append_ne {S : Type} (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (hq : qw q w Y ≠ 0) :
    ∀ L : List (Letter ℂ S), (∀ l ∈ L, l.plus = true ∧ Y - l.pt ≠ 0 ∧ Y - l.pt + 1 ≠ 0) →
      qw q (L ++ w) Y ≠ 0 := by
  intro L hL
  induction L with
  | nil => simpa using hq
  | cons l L ih =>
    have hl := hL l (by simp)
    rw [List.cons_append]
    simp only [qw]
    rw [if_pos hl.1]
    exact mul_ne_zero (ih fun l' hl' => hL l' (by simp [hl'])) (div_ne_zero hl.2.2 hl.2.1)

theorem good_tail {S : Type} {l : Letter ℂ S} {w : List (Letter ℂ S)} (h : Good (l :: w)) : Good w := by
  unfold Good at *
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'), (List.pairwise_cons.1 h3).2⟩
  simp only [List.map_cons, List.nodup_cons] at h1
  exact h1.2

theorem dkDualOK : DKDualOK := by
  intro S _ _ q w L hD
  induction L with
  | nil => trivial
  | cons l L ih =>
    obtain ⟨hP, hG, hGd, hPw, hq⟩ := hD
    have hl : l.plus = true := hP l (by simp)
    have hG' : Good (L ++ w) := good_tail hG
    have hGd' : Good (L.map dl ++ w) := good_tail (by simpa using hGd)
    have hpw := List.pairwise_cons.mp hPw
    refine ⟨?_, ?_, ih ⟨fun l' h => hP l' (by simp [h]), hG', hGd', hpw.2,
      fun l' h => hq l' (by simp [h])⟩⟩
    ·
      intro l' hl'
      have hdl : dl l = ⟨false, l.intersection_update_fsHerm_neg_one, l.pt + 1⟩ := by simp [dl, hl]
      rw [hdl]
      rcases List.mem_append.mp hl' with h | h
      · have hpl : l'.plus = true := hP l' (by simp [h])
        have := (hpw.1 l' h).1
        simp only [RegL, hpl, if_true]
        intro h0; apply this; linear_combination h0
      · have hgd : Good (dl l :: (L.map dl ++ w)) := by simpa using hGd
        have := (List.pairwise_cons.mp hgd.2.2).1 l' (by simp [h])
        rw [hdl] at this
        exact this
    · simp only [ypt, hl, if_true]
      refine qw_append_ne q w l.pt (hq l (by simp)) L fun l' hl' => ⟨hP l' (by simp [hl']), ?_, ?_⟩
      · exact (hpw.1 l' hl').1
      · intro h0; exact (hpw.1 l' hl').2.2 (by linear_combination h0)

end Formalism.FourierDecayAlt.P.DualKernelLemmas
end

section

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P.Mx1

theorem star_sc (P : Par) (w : Pr P.r) : star (sc P w) = sc P (star w) := by
  unfold sc
  ext i j
  rw [Matrix.star_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

end Formalism.FourierDecayAlt.P.Mx1

namespace Formalism.FourierDecayAlt.P

open Mx1

theorem model_nontrivial : Formalism.FourierDecayAlt.M.ModelNontrivial := by
  intro P
  have key : ∀ w : Pr P.r, sc P w = 0 → w = 0 := by
    intro w h
    have := congrFun (congrFun h (fun _ => 0)) (fun _ => 0)
    simpa [sc] using this
  refine ⟨⟨⟨0, 1, fun h => ?_⟩⟩, fun f fb h => ?_⟩
  · have h1 : (1 : Pr P.r) = 0 := key 1 (by unfold sc; rw [map_one]; exact h.symm)
    have h2 : (1 : Op P.r) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simp at h2
  · have h1 := key _ h
    have h2 : (mulOp f) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simpa [mulOp] using h2

theorem star_generators : Formalism.FourierDecayAlt.M.StarGens := by
  intro P
  have hs : ∀ X Y : Op P.r, star (mk X Y) = mk Y X := fun X Y => rfl
  have hneg : ∀ X Y : Op P.r, -(mk X Y : Pr P.r) = mk (-X) (-Y) := fun X Y => rfl
  have mc : ∀ f g : Fn P.r, mulOp f * mulOp g = mulOp g * mulOp f := fun f g => by
    refine LinearMap.ext fun x => ?_
    simp only [mulOp, Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, mul_comm f g]
  refine ⟨fun l => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cA cbA; rw [star_sc]; rfl
  · unfold ciA cbiA; rw [star_sc]; rfl
  · unfold pA pbA
    rw [star_sc]
    unfold sc
    rw [← map_neg]
    congr 1
    unfold pP pbP
    rw [hs, hneg, neg_neg]
  · unfold zA zbA; rw [star_sc]; rfl
  · unfold ziA zbiA; rw [star_sc]; rfl
  · unfold ggA; rw [star_sc]; rfl
  · unfold ggiA; rw [star_sc]; rfl
  · have e1 : star (dzP : Pr P.r) = -dzbP := by
      unfold dzP dzbP
      rw [hs, hneg, neg_neg]
    have e2 : star (zbP : Pr P.r) = zP := rfl
    have e3 : star (ggiP P.TT : Pr P.r) = ggiP P.TT := rfl
    have e4 : (ggiP P.TT : Pr P.r) * zP = zP * ggiP P.TT := by
      unfold ggiP zP fnP M.mk
      refine Prod.ext (mc _ _) ?_
      show MulOpposite.op _ * MulOpposite.op _ = MulOpposite.op _ * MulOpposite.op _
      rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, mc]
    unfold nabA nabsA
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext π
    rw [Pi.star_apply, star_add, star_smul, star_mul, e1, e2, e3, e4, Complex.star_def, Complex.conj_ofReal]

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P

open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M

namespace Mx9

theorem eq_ofReal {z : ℂ} (h : z.im = 0) : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])

theorem star_eq {z : ℂ} (h : z.im = 0) : star z = z := by
  exact Complex.conj_eq_iff_im.mpr h

theorem far {z z' : ℂ} (h : 2 < |z.re - z'.re|) (n : ℤ) (hn : |n| ≤ 2) : z - z' ≠ (n : ℂ) := by
  intro heq
  have h1 := congrArg Complex.re heq
  simp only [Complex.sub_re, Complex.intCast_re] at h1
  rw [h1] at h
  have h2 : ((|n| : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hn
  rw [Int.cast_abs] at h2
  linarith

noncomputable def ty0 (P : Par) : Ty P := fun _ => 0

theorem xC_ne (hR : RealPoints) (P : Par) (π : Ty P) (n : ℕ) (Y : ℝ)
    (h : 0 < (-1 : ℝ) ^ n * I.xpoly P.k (rho P π) Y) : xC P π (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P π Y).1] at h0
  have h1 : I.xpoly P.k (rho P π) Y = 0 := by exact_mod_cast h0
  rw [h1, mul_zero] at h
  exact lt_irrefl _ h

theorem qC_ne (hR : RealPoints) (P : Par) (Y : ℝ)
    (h : 0 < I.qpoly P.k P.T P.T' P.u P.u' Y) : qC P (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P (ty0 P) Y).2] at h0
  have h1 : I.qpoly P.k P.T P.T' P.u P.u' Y = 0 := by exact_mod_cast h0
  rw [h1] at h
  exact lt_irrefl _ h

end Mx9

open Mx9

theorem cut_admissible : Formalism.FourierDecayAlt.M.CutAdm := by
  intro hIS hQP hQS hTy hR P hP l hl1 hlk S _ _ w hw
  obtain ⟨hnd, hpt, hpw⟩ := hw
  have key : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → ∀ e ∈ ({-1, 0, 1} : Finset ℝ),
      ((Y + e : ℝ) : ℂ) ∈ (startM P l).inv := by
    intro Y hY e he
    show ∀ π, xC P π _ ≠ 0
    intro π
    exact xC_ne hR P π (P.k - l) (Y + e) (hIS P.k P.u P.u' (rho P π) l Y hl1 hlk (hTy P hP π) hY e he)
  have qpos : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q (Y : ℂ) ≠ 0 := by
    intro Y hY
    exact qC_ne hR P Y (hQP P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
  have qsh : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q ((Y : ℂ) - 1) ≠ 0 := by
    intro Y hY
    have h := qC_ne hR P (Y - 1) (hQS P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
    push_cast at h
    exact h
  refine ⟨hnd, fun a ha => star_eq (hpt a ha).1, fun a ha => ?_, hpw.imp fun h n hn => far h n hn⟩
  obtain ⟨him, hcut⟩ := hpt a ha
  have hz : a.pt = ((a.pt.re : ℝ) : ℂ) := eq_ofReal him
  rw [hz]
  refine ⟨?_, ?_, ?_, qpos _ hcut, qsh _ hcut⟩
  · convert key _ hcut 0 (by norm_num) using 1 <;> push_cast <;> ring
  · convert key _ hcut 1 (by norm_num) using 1 <;> push_cast <;> ring
  · convert key _ hcut (-1) (by norm_num) using 1 <;> push_cast <;> ring

end Formalism.FourierDecayAlt.P
end
