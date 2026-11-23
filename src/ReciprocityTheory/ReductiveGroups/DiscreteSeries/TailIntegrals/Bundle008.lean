module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.OneLeGN
public import Formalism.HermitianCurvature.StatementB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.GoodRowsProjectorApplyEqSum
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

def sg (k r i : ℕ) : ℕ := if i < r ∨ r + k < i then 2 * r + k - i else i

theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = sg k r i.val then (if i.val = r + k then -1 else 1) else 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecA.hpk_apply <;> assumption

theorem hpk_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) : Hpk k r j i = Hpk k r i j := by
  rw [hpk_apply, hpk_apply]; unfold sg
  split_ifs <;> first | rfl | omega

theorem hpk_conjT (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, hpk_symm, hpk_apply]
  split_ifs <;> simp

theorem sg_lt {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i < 2 * r + k + 1 := by
  unfold sg; split_ifs <;> omega

theorem sg_sg {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r (sg k r i) = i := by
  unfold sg; split_ifs <;> omega

theorem sg_rk {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i = r + k ↔ i = r + k := by
  unfold sg; split_ifs <;> omega

theorem hpk_apply' (k r i : ℕ) (hi : i < 2 * r + k + 1) (j : Fin (2 * r + k + 1)) :
    Hpk k r ⟨i, hi⟩ j = if j.val = sg k r i then (if i = r + k then -1 else 1) else 0 :=
  hpk_apply k r ⟨i, hi⟩ j

theorem hpk_mul (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  apply ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecA.hpk_mul <;> assumption

theorem sum_mid {n N : ℕ} (h : N = n + 2) (f : Fin N → ℂ) (h0 : ∀ q : Fin N, q.val = 0 → f q = 0)
    (h1 : ∀ q : Fin N, q.val = n + 1 → f q = 0) : ∑ q, f q = ∑ q : Fin n, f ⟨q.val + 1, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, h0 0 rfl, h1 (Fin.last n).succ (by simp)]
  simp only [zero_add, add_zero]; rfl

theorem mv_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (q p : Fin n) : (M *ᵥ bvec q) p = M p q := by
  unfold bvec; simp [mulVec, dotProduct, Pi.single_apply]

theorem mat_ext_bvec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : ∀ q, A *ᵥ bvec q = B *ᵥ bvec q) : A = B := by
  ext i j; have := congrFun (h j) i; rwa [mv_bvec, mv_bvec] at this

section Lev
variable {k r' : ℕ}

def sh (q : Fin (2 * r' + k + 1)) : Fin (2 * (1 + r') + k + 1) := ⟨q.val + 1, by have := q.2; omega⟩

theorem sh_val (q : Fin (2 * r' + k + 1)) : (sh q).val = q.val + 1 := rfl

theorem exists_sh (p : Fin (2 * (1 + r') + k + 1)) (hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) :
    ∃ q : Fin (2 * r' + k + 1), p = sh q :=
  ⟨⟨p.val - 1, by omega⟩, Fin.ext (by simp [sh]; omega)⟩

theorem sum_sh (f : Fin (2 * (1 + r') + k + 1) → ℂ) (h0 : ∀ q : Fin _, q.val = 0 → f q = 0)
    (h1 : ∀ q : Fin _, q.val = 2 * (1 + r') + k → f q = 0) : ∑ q, f q = ∑ q : Fin (2 * r' + k + 1), f (sh q) :=
  sum_mid (n := 2 * r' + k + 1) (by omega) f h0 (fun q hq => h1 q (by omega))

theorem lv_in (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) : liftVec k 1 r' v (sh q) = v q := by
  unfold liftVec; rw [dite_eq_left (show 1 ≤ (sh q).val ∧ (sh q).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := q.2; simp [sh]; omega⟩)]
  congr 1

theorem lv_out (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : liftVec k 1 r' v p = 0 := by
  unfold liftVec; rw [dite_eq_right (by omega)]

theorem io_in (g : Mat k r') (p q : Fin (2 * r' + k + 1)) : ιLev k 1 r' g (sh p) (sh q) = g p q := by
  unfold ιLev
  rw [dite_eq_left (show 1 ≤ (sh p).val ∧ (sh p).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := p.2; simp [sh]; omega⟩),
    dite_eq_left (show 1 ≤ (sh q).val ∧ (sh q).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := q.2; simp [sh]; omega⟩)]
  congr 1

theorem io_out (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1))
    (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) : ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · rw [dite_eq_left hp, dite_eq_right (by omega), if_neg (fun h => by subst h; omega)]
  · rw [dite_eq_right hp]

theorem io_out' (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  unfold ιLev; rw [dite_eq_right (by omega)]

theorem io_lv (g : Mat k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' v = liftVec k 1 r' (g *ᵥ v) := by
  funext p
  simp only [mulVec, dotProduct]
  rw [sum_sh _ (fun q hq => by rw [lv_out v q (by omega), mul_zero]) (fun q hq => by rw [lv_out v q (by omega), mul_zero])]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · obtain ⟨p', rfl⟩ := exists_sh p hp
    rw [lv_in]; simp only [mulVec, dotProduct]
    exact Finset.sum_congr rfl fun q _ => by rw [io_in, lv_in]
  · rw [lv_out _ p (by omega)]
    exact Finset.sum_eq_zero fun q _ => by
      rw [io_out' g p _ (by omega), if_neg (fun h => by rw [h, sh_val] at hp; omega), zero_mul]

theorem io_bvec_out (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) :
    ιLev k 1 r' g *ᵥ bvec q = bvec q := by
  funext p; rw [mv_bvec, io_out g p q hq]; unfold bvec; simp only [Pi.single_apply]

theorem bvec_lv (q : Fin (2 * r' + k + 1)) : (bvec (sh q) : Fin (2 * (1 + r') + k + 1) → ℂ) = liftVec k 1 r' (bvec q) := by
  funext p
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · obtain ⟨p', rfl⟩ := exists_sh p hp
    rw [lv_in]; unfold bvec; simp only [Pi.single_apply, Fin.ext_iff, sh_val]; simp
  · rw [lv_out _ p (by omega)]; unfold bvec; rw [Pi.single_apply, if_neg (fun h => by rw [h, sh_val] at hp; omega)]

theorem io_bvec_sh (g : Mat k r') (q : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g *ᵥ bvec (sh q) = liftVec k 1 r' (g *ᵥ bvec q) := by
  rw [bvec_lv, io_lv]

theorem io_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  apply mat_ext_bvec; intro q
  rw [← Matrix.mulVec_mulVec]
  by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · obtain ⟨q', rfl⟩ := exists_sh q hq
    rw [io_bvec_sh, io_bvec_sh, io_lv, Matrix.mulVec_mulVec]
  · rw [io_bvec_out _ _ (by omega), io_bvec_out _ _ (by omega), io_bvec_out _ _ (by omega)]

theorem io_one : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply mat_ext_bvec; intro q
  rw [Matrix.one_mulVec]
  by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · obtain ⟨q', rfl⟩ := exists_sh q hq
    rw [io_bvec_sh, Matrix.one_mulVec, bvec_lv]
  · rw [io_bvec_out _ _ (by omega)]

theorem io_conjT (g : Mat k r') : ιLev k 1 r' gᴴ = (ιLev k 1 r' g)ᴴ := by
  ext p q
  rw [conjTranspose_apply]; unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 <;>
    by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · rw [dite_eq_left hp, dite_eq_left hq, dite_eq_left hq, dite_eq_left hp, conjTranspose_apply]
  · rw [dite_eq_left hp, dite_eq_right hq, dite_eq_right hq, if_neg (fun h => by subst h; exact hq hp), star_zero]
  · rw [dite_eq_right hp, dite_eq_left hq, dite_eq_right hp, if_neg (fun h => by subst h; exact hp hq), star_zero]
  · rw [dite_eq_right hp, dite_eq_right hq]; by_cases h : p = q
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]

end Lev

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section

noncomputable section

set_option linter.unusedSimpArgs false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section grp
variable (k r' : ℕ)

theorem mat_ext_lev {A B : Mat k (1 + r')} (h0 : A *ᵥ e0 k r' = B *ᵥ e0 k r')
    (h1 : A *ᵥ es0 k r' = B *ᵥ es0 k r') (h2 : ∀ v, A *ᵥ liftVec k 1 r' v = B *ᵥ liftVec k 1 r' v) : A = B := by
  have key : ∀ q : Fin (2 * (1 + r') + k + 1), A *ᵥ Pi.single q 1 = B *ᵥ Pi.single q 1 := by
    intro q
    by_cases hq0 : q.val = 0
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = e0 k r' := by
        have hq : q = eI k (1 + r') (a0 r') := Fin.ext (by simp [eI, a0, hq0])
        rw [hq]
        rfl
      rw [he, h0]
    by_cases hql : q.val = 2 * (1 + r') + k
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = es0 k r' := by
        have hq : q = esI k (1 + r') (a0 r') := Fin.ext (by simp [esI, a0, hql])
        rw [hq]
        rfl
      rw [he, h1]
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) =
          liftVec k 1 r' (Pi.single ⟨q.val - 1, by omega⟩ 1) := by
        funext p
        simp only [liftVec, Pi.single_apply, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [he, h2]
  ext p q
  have h := congrFun (key q) p
  simpa [Matrix.mulVec_single_one, Matrix.transpose_apply] using h

theorem lev_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift]

theorem lev_one : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply mat_ext_lev
  · simp only [levi_fixes_base_vector, Matrix.one_mulVec]
  · simp only [levi_fixes_last_basis, Matrix.one_mulVec]
  · intro v
    simp only [lev_lift, Matrix.one_mulVec]

theorem lev_conjT (g : Mat k r') : (ιLev k 1 r' g)ᴴ = ιLev k 1 r' gᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, ιLev]
  split_ifs <;> (try subst_vars) <;> simp_all [Matrix.conjTranspose_apply]

theorem lev_mem {g : Mat k r'} (hg : g ∈ GV k r') : ιLev k 1 r' g ∈ GV k (1 + r') := by
  have hg' : gᴴ * Hpk k r' * g = Hpk k r' := hg
  show (ιLev k 1 r' g)ᴴ * Hpk k (1 + r') * ιLev k 1 r' g = Hpk k (1 + r')
  rw [lev_conjT]
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, Hpk_mulVec_e0, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, hermMatrix_last_basis, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, Hpk_lift]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem rankOne_levi_comm (c : ℂ) (g : Mat k r') : w0 k r' c * ιLev k 1 r' g = ιLev k 1 r' g * w0 k r' c := by
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, long_weyl_sends_base_to_dual, Matrix.mulVec_smul, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, rankOneMatrix_last_basis, Matrix.mulVec_smul, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, rankOneMatrix_lift]

theorem lev_K {κ : Mat k r'} (hκ : κ ∈ Kset k r') : ιLev k 1 r' κ ∈ Kset k (1 + r') := by
  refine ⟨lev_mem k r' hκ.1, ?_⟩
  rw [lev_conjT, ← lev_mul, hκ.2, lev_one]

end grp

section gn
variable {n : ℕ}

theorem normSq_sum_eq_trace (Y : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (Y i j) : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

theorem gN_unitary (k r : ℕ) {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (κ * X) = gN X := by
  unfold gN
  congr 1
  have h1 := normSq_sum_eq_trace (κ * X)
  have h2 := normSq_sum_eq_trace X
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul] at h1
  exact_mod_cast h1.trans h2.symm

theorem gN_cont (k r : ℕ) : Continuous (fun g : Mat k r => gN g) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _
    fun j _ => Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))

end gn

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

section

noncomputable section

open Matrix InnerProductSpace
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS

variable {n m : ℕ}

theorem gram_det_zero (w : Fin m → EuclideanSpace ℂ (Fin n)) (hw : ¬ LinearIndependent ℂ w) :
    (GS.gram w).det = 0 := by
  rw [Fintype.not_linearIndependent_iff] at hw
  obtain ⟨g, hg, i, hi⟩ := hw
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨g, fun h => hi (congrFun h i), ?_⟩
  funext a
  simp only [mulVec, dotProduct, GS.gram, Matrix.of_apply, Pi.zero_apply]
  have hs : ∑ b, inner ℂ (w a) (w b) * g b = inner ℂ (w a) (∑ b, g b • w b) := by
    rw [inner_sum]
    congr 1
    funext b
    rw [inner_smul_right]
    ring
  rw [hs, hg, inner_zero_right]

theorem gram_re_det_le (v : Fin m → EuclideanSpace ℂ (Fin n)) (M : ℝ) (hM : ∀ j, ‖v j‖ ≤ M) :
    (GS.gram v).det.re ≤ (M ^ 2) ^ m := by
  by_cases hv : LinearIndependent ℂ v
  · obtain ⟨u, τ, hu, hτ, -, hwe, -⟩ := gs_fac v hv
    rw [det_gram_of v u τ hu hτ hwe, Complex.ofReal_re]
    have hτj : ∀ j, ‖τ j j‖ ≤ M := by
      intro j
      have h1 : inner ℂ (u j) (v j) = τ j j := by
        rw [hwe j]; exact hu.inner_right_fintype (fun b => τ b j) j
      rw [← h1]
      calc ‖inner ℂ (u j) (v j)‖ ≤ ‖u j‖ * ‖v j‖ := norm_inner_le_norm _ _
        _ = ‖v j‖ := by rw [hu.1 j, one_mul]
        _ ≤ M := hM j
    calc ∏ j, ‖τ j j‖ ^ 2 ≤ ∏ _j : Fin m, M ^ 2 :=
          Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hτj j) 2
      _ = (M ^ 2) ^ m := by simp
  · rw [gram_det_zero v hv, Complex.zero_re]
    by_cases hm : m = 0
    · subst hm; simp
    · exact pow_nonneg (sq_nonneg M) m

end ReciprocityTheory.ChartRestriction.DS.Xi.GSB

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS

def linA {k r : ℕ} (A : Mat k r) :
    EuclideanSpace ℂ (Fin (2 * r + k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
  (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.toLin' A ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap

theorem linA_apply {k r : ℕ} (A : Mat k r) (x : EuclideanSpace ℂ (Fin (2 * r + k + 1))) :
    linA A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

theorem gram_one {m n : ℕ} (u : Fin m → EuclideanSpace ℂ (Fin n)) (hu : Orthonormal ℂ u) : GS.gram u = 1 := by
  ext a b
  simp only [GS.gram, Matrix.of_apply, Matrix.one_apply]
  exact orthonormal_iff_ite.mp hu a b

theorem ga_mul_le (k r : ℕ) (A : Mat k r) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => A *ᵥ Y a) ≤ (gN A ^ 2) ^ (l.val + 1) * Ga k r l Y := by
  rw [ga_eq, ga_eq]
  set w : Fin (l.val + 1) → EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    fun a => WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) with hwdef
  have hAw : (fun a : Fin (l.val + 1) =>
      (WithLp.toLp 2 (A *ᵥ Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) =
      fun a => linA A (w a) := by
    funext a; rw [linA_apply]
  rw [hAw]
  by_cases hw : LinearIndependent ℂ w
  · obtain ⟨u, τ, hu, hτ, -, hwe, -⟩ := gs_fac w hw
    have h1 : (fun a => linA A (w a)) = fun a => ∑ b, τ b a • linA A (u b) := by
      funext a; rw [hwe a, map_sum]; simp only [map_smul]
    have hgw : (GS.gram w).det = (τᴴ).det * τ.det := by
      rw [show w = (fun a => ∑ b, τ b a • u b) from funext hwe, gram_comb, gram_one u hu, Matrix.mul_one, det_mul]
    have hv : ∀ b, ‖linA A (u b)‖ ≤ gN A := by
      intro b
      have := norm_mulVec_le A (WithLp.ofLp (u b))
      rw [WithLp.toLp_ofLp, hu.1 b, mul_one] at this
      rw [linA_apply]; exact this
    have hle := gram_re_det_le (fun b => linA A (u b)) (gN A) hv
    have hX := det_gram_of w u τ hu hτ hwe
    rw [h1, gram_comb, det_mul, det_mul]
    have e1 : (τᴴ).det * (GS.gram fun b => linA A (u b)).det * τ.det =
        (GS.gram w).det * (GS.gram fun b => linA A (u b)).det := by rw [hgw]; ring
    rw [e1, hX, Complex.re_ofReal_mul]
    have hnn : (0 : ℝ) ≤ ∏ j, ‖τ j j‖ ^ 2 := Finset.prod_nonneg fun j _ => by positivity
    rw [Complex.ofReal_re, mul_comm]
    exact mul_le_mul_of_nonneg_right hle hnn
  · have hw' : ¬ LinearIndependent ℂ (fun a => linA A (w a)) := fun h => hw (h.of_comp (linA A))
    rw [gram_det_zero _ hw', gram_det_zero _ hw, Complex.zero_re, mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Xi.GSB
end
end
