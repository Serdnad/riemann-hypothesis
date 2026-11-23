module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.Bundle001
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.Bundle001

@[expose] public section

section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section iso

variable {k r : ℕ}

lemma herm_X_gen {x w : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) (hw : ∀ i : Fin (2 * r + k + 1), r + k < i.val → w i = 0) :
    herm (Hpk k r) x w = 0 := by
  have hlo : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → x j = 0 := by
    intro j hj
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      have hne : j ≠ eI k r a := by
        intro h
        have := congrArg Fin.val h
        simp [eI] at this
        omega
      simp [bvec, Pi.single_apply, hne]
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : r ≤ j.val
  · rw [hlo j hj, mul_zero, mul_zero]
  · push_neg at hj
    by_cases hi : r + k < i.val
    · rw [hw i hi, star_zero, zero_mul]
    · push_neg at hi
      have hH : Hpk k r i j = 0 := by
        unfold Hpk
        simp only [Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [hH, zero_mul, mul_zero]

lemma herm_wb_X {x w : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) (hw : ∀ i : Fin (2 * r + k + 1), r + k < i.val → w i = 0) :
    herm (Hpk k r) w x = 0 := by
  have hlo : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → x j = 0 := by
    intro j hj
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      have hne : j ≠ eI k r a := by
        intro h
        have := congrArg Fin.val h
        simp [eI] at this
        omega
      simp [bvec, Pi.single_apply, hne]
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases hi : r ≤ i.val
  · rw [hlo i hi, star_zero, zero_mul]
  · push_neg at hi
    by_cases hj : r + k < j.val
    · rw [hw j hj, mul_zero, mul_zero]
    · push_neg at hj
      have hH : Hpk k r i j = 0 := by
        unfold Hpk
        simp only [Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [hH, zero_mul, mul_zero]

lemma X_hi {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) : ∀ i : Fin (2 * r + k + 1), r + k < i.val → x i = 0 := by
  intro i hi
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have hne : i ≠ eI k r a := by
      intro h
      have := congrArg Fin.val h
      simp [eI] at this
      omega
    simp [bvec, Pi.single_apply, hne]
  | zero => rfl
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

lemma wb_hi {x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) : ∀ i : Fin (2 * r + k + 1), r + k < i.val → x i = 0 := by
  intro i hi
  exact hx i (Or.inr hi)

end iso

end PI.UnitaryGroupMassFormula.GsFr
end
end

section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section lemmas

variable {k r : ℕ}

lemma mem_Xsp_iff (v : Fin (2 * r + k + 1) → ℂ) : v ∈ Xsp k r ↔ ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro i hi
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      intro h
      have ha := a.isLt
      rw [h] at hi
      simp only [eI] at hi
      omega
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul c x _ hx => intro i hi; simp [hx i hi]
  · intro hv
    have hsum : v = ∑ a : Fin r, v (eI k r a) • bvec (eI k r a) := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hi : i.val < r
      · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
        · have he : i = eI k r ⟨i.val, hi⟩ := by ext; rfl
          rw [if_pos he, ← he]
        · intro b _ hb
          rw [if_neg]
          intro h
          apply hb
          ext
          show b.val = i.val
          have h2 := congrArg Fin.val h
          simp only [eI] at h2
          omega
        · simp
      · rw [hv i (by omega)]
        refine (Finset.sum_eq_zero fun b _ => ?_).symm
        rw [if_neg]
        intro h
        have hb := b.isLt
        rw [h] at hi
        simp only [eI] at hi
        omega
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end lemmas

end PI.UnitaryGroupMassFormula.GsFr
end
end

section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

abbrev Sm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (s : Set E) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f s

lemma sv_iff {m : ℕ} {v : E → Fin m → ℂ} : Sm v s ↔ ∀ i, Sm (fun x => v x i) s := by
  exact contDiffOn_pi

lemma sm_iff {p q : ℕ} {M : E → Matrix (Fin p) (Fin q) ℂ} : Sm M s ↔ ∀ i j, Sm (fun x => M x i j) s := by
  unfold Sm
  exact contDiffOn_pi.trans (forall_congr' fun i => contDiffOn_pi)

lemma s_star {f : E → ℂ} (hf : Sm f s) : Sm (fun x => star (f x)) s := by
  exact Complex.conjCLE.contDiff.comp_contDiffOn hf

lemma s_re {f : E → ℂ} (hf : Sm f s) : Sm (fun x => (f x).re) s := by
  exact Complex.reCLM.contDiff.comp_contDiffOn hf

lemma s_mulVec {m : ℕ} {M : E → Matrix (Fin m) (Fin m) ℂ} {v : E → Fin m → ℂ} (hM : Sm M s) (hv : Sm v s) :
    Sm (fun x => M x *ᵥ v x) s := by
  rw [sv_iff]
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffOn.sum fun j _ => (sm_iff.1 hM i j).mul (sv_iff.1 hv j)

lemma s_herm {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) {v w : E → Fin m → ℂ} (hv : Sm v s) (hw : Sm w s) :
    Sm (fun x => herm H (v x) (w x)) s := by
  have hH : Sm (fun x => H *ᵥ v x) s := s_mulVec contDiffOn_const hv
  simp only [herm, dotProduct, Pi.star_apply]
  exact ContDiffOn.sum fun i _ => (s_star (sv_iff.1 hw i)).mul (sv_iff.1 hH i)

lemma s_smul {m : ℕ} {c : E → ℂ} {v : E → Fin m → ℂ} (hc : Sm c s) (hv : Sm v s) :
    Sm (fun x => c x • v x) s := by
  rw [sv_iff]
  intro i
  simp only [Pi.smul_apply, smul_eq_mul]
  exact hc.mul (sv_iff.1 hv i)

lemma s_mmul {m : ℕ} {A B : E → Matrix (Fin m) (Fin m) ℂ} (hA : Sm A s) (hB : Sm B s) :
    Sm (fun x => A x * B x) s := by
  rw [sm_iff]
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (sm_iff.1 hA i l).mul (sm_iff.1 hB l j)

lemma s_ct {m : ℕ} {A : E → Matrix (Fin m) (Fin m) ℂ} (hA : Sm A s) : Sm (fun x => (A x)ᴴ) s := by
  rw [sm_iff]
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact s_star (sm_iff.1 hA j i)

private lemma sm_finset_prod {ι : Type*} (u : Finset ι) {f : ι → E → ℂ} (h : ∀ i ∈ u, Sm (f i) s) :
    Sm (fun x => ∏ i ∈ u, f i x) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using contDiffOn_const
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma s_det {p : ℕ} {M : E → Matrix (Fin p) (Fin p) ℂ} (h : ∀ i j, Sm (fun x => M x i j) s) :
    Sm (fun x => (M x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (sm_finset_prod _ fun i _ => h (σ i) i)

lemma s_adj {p : ℕ} {M : E → Matrix (Fin p) (Fin p) ℂ} (h : ∀ i j, Sm (fun x => M x i j) s) (a b : Fin p) :
    Sm (fun x => (M x).adjugate a b) s := by
  simp only [Matrix.adjugate_apply]
  refine s_det fun i j => ?_
  simp only [Matrix.updateRow_apply]
  by_cases hi : i = b
  · simp only [hi, if_true]
    exact contDiffOn_const
  · simp only [hi, if_false]
    exact h i j

variable {k r : ℕ}

lemma s_wbPart {v : E → Fin (2 * r + k + 1) → ℂ} (hv : Sm v s) : Sm (fun x => wbPart k r (v x)) s := by
  rw [sv_iff]
  intro i
  simp only [wbPart]
  by_cases hc : r ≤ i.val ∧ i.val ≤ r + k
  · simp only [hc, and_self, if_true]
    exact sv_iff.1 hv i
  · simp only [hc, if_false]
    exact contDiffOn_const

lemma s_prW (z : Fin (2 * r + k + 1) → ℂ) {v : E → Fin (2 * r + k + 1) → ℂ} (hv : Sm v s) :
    Sm (fun x => prW k r z (v x)) s := by
  simp only [prW]
  exact (s_wbPart hv).add (s_smul ((s_herm _ (s_wbPart hv) contDiffOn_const).div_const _) contDiffOn_const)

lemma s_Zhat (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) (a b : Fin (r + 1)) :
    Sm (fun x => Zhat k r z z' (Y x) a b) s := by
  simp only [Zhat]
  exact s_herm _ (s_mulVec hY contDiffOn_const) contDiffOn_const

lemma s_xcofL (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) :
    Sm (fun x => xcofL k r z z' (Y x)) s := by
  simp only [xcofL]
  exact ContDiffOn.sum fun a _ =>
    s_smul (s_star (s_adj (fun i j => s_Zhat z z' hY i j) _ _)) contDiffOn_const

lemma s_xcof (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) :
    Sm (fun x => xcof k r z z' (Y x)) s := by
  simp only [xcof]
  exact ContDiffOn.sum fun b _ =>
    s_smul (s_adj (fun i j => s_Zhat z z' hY i j) _ _) (s_mulVec hY contDiffOn_const)

lemma s_omW (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) :
    Sm (fun x => omW k r z z' (Y x)) s := by
  simp only [omW]
  exact s_prW z (s_xcof z z' hY)

end smooth

end PI.UnitaryGroupMassFormula.GsFr
end
end
