module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Formalism.RealPlaceAnalysis.Bundle003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle006
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle021
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.kCurve :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E)), star Z = -Z →
      ∃ k : ℝ → Kinf E a, k 0 = 1 ∧ HasDerivAt (fun t => toL (k t).1) (toL Z) 0 := by
  intro E _ _ _ a Z hZ
  open scoped Matrix.Norms.Operator in
  have hs : ∀ t : ℝ, star (NormedSpace.exp (t • Z)) = NormedSpace.exp (-(t • Z)) := fun t => by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, ← Matrix.star_eq_conjTranspose, star_smul,
      star_trivial, hZ, smul_neg]
  have hm : ∀ t : ℝ, NormedSpace.exp (t • Z) ∈ unitary (Matrix (Fin a) (Fin a) (Cinf E)) := fun t => by
    rw [Unitary.mem_iff, hs, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
    simp
  refine ⟨fun t => ⟨NormedSpace.exp (t • Z), hm t⟩, Subtype.ext (by simp), ?_⟩
  open scoped Matrix.Norms.Operator in
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

namespace UpperTheory.V.AlgRepEndIrreducible.GLNegationOpposite

open Formalism.REAL Formalism.HermitianLatticeCounting.P MulOpposite

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}


omit [Algebra ℂ A] in
private theorem glRel_op {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) : Formalism.REAL.GlRel fun i j => op (X j i) := by
  intro a b c d
  have h1 := congrArg op (h d c b a)
  simp only [op_sub, op_mul, apply_ite op, op_zero] at h1
  rw [h1]
  simp only [eq_comm (a := c) (b := b), eq_comm (a := a) (b := d)]

private theorem qdet_op {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) (y : ℂ) :
    qdet (fun i j => op (X j i)) y = op (qdet X y) := by
  have hP : ∀ (arg : Fin n → ℂ) (σ τ : Equiv.Perm (Fin n)), orderedTermProduct (fun i j => op (X j i)) arg σ τ =
      op (orderedTermProduct X (arg ∘ Fin.revPerm) (τ * Fin.revPerm) (σ * Fin.revPerm)) := fun arg σ τ => by
    unfold orderedTermProduct
    rw [op_list_prod, List.map_ofFn]
    congr 1
    refine List.ext_getElem (by simp) fun k h1 h2 => ?_
    have hk : k < n := by simpa using h1
    have e : (⟨n - 1 - k, by omega⟩ : Fin n).rev = ⟨k, hk⟩ := Fin.ext (by rw [Fin.val_rev]; simp only; omega)
    simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, Function.comp_apply, Equiv.Perm.mul_apply,
      Fin.revPerm_apply, e, Tm, op_add, apply_ite op, op_zero, eq_comm (a := τ _)]
    rfl
  have hS : ∀ arg : Fin n → ℂ, doublyAntisymmetrizedProduct (fun i j => op (X j i)) arg = op (doublyAntisymmetrizedProduct X (arg ∘ Fin.revPerm)) := fun arg => by
    unfold doublyAntisymmetrizedProduct
    rw [Finset.sum_comm, Finset.op_sum]
    refine Fintype.sum_equiv (Equiv.mulRight Fin.revPerm) _ _ fun σ => ?_
    rw [Finset.op_sum]
    refine Fintype.sum_equiv (Equiv.mulRight Fin.revPerm) _ _ fun τ => ?_
    simp only [hP, ← zsmul_eq_mul, op_smul, smul_smul, Equiv.coe_mulRight, Equiv.Perm.sign_mul, Units.val_mul]
    congr 1
    linear_combination (-((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ))) *
      Int.units_coe_mul_self (Equiv.Perm.sign (Fin.revPerm (n := n)))
  have e := hS fun k => y - (k : ℂ)
  rw [antisymmetrizedProduct_perm_invariant, antisymmetrizedProduct_eq_factorial_smul_qdet _ h, antisymmetrizedProduct_eq_factorial_smul_qdet _ (glRel_op h), op_smul] at e
  exact (IsUnit.mk0 _ (by exact_mod_cast n.factorial_ne_zero)).smul_left_cancel.mp e

private theorem qdet_antipode {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) (x : ℂ) :
    qdet (fun i j => -op (X i j)) x = op ((-1 : ℂ) ^ n • qdet X ((n : ℂ) - 1 - x)) := by
  rw [quantumDet_neg_transpose _ (glRel_op h), qdet_op h, op_smul]

omit [Algebra ℂ A] in
private theorem glRel_negOp {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) :
    Formalism.REAL.GlRel fun i j => -op (X i j) := by
  intro a b c d
  have h1 := congrArg op (h c d a b)
  simp only [op_sub, op_mul, apply_ite op, op_zero] at h1
  simp only [neg_mul_neg]
  rw [h1]
  simp only [eq_comm (a := d) (b := a), eq_comm (a := b) (b := c)]
  split_ifs <;> abel

end UpperTheory.V.AlgRepEndIrreducible.GLNegationOpposite

theorem UpperTheory.V.AlgRepEndIrreducible.glNegOp :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X →
      Formalism.REAL.GlRel (fun i j => -MulOpposite.op (X i j)) ∧
      ∀ x : ℂ, Formalism.REAL.qdet (fun i j => -MulOpposite.op (X i j)) x =
        MulOpposite.op ((-1 : ℂ) ^ n • Formalism.REAL.qdet X ((n : ℂ) - 1 - x)) :=
  fun _ _ _ _ _ h => ⟨GLNegationOpposite.glRel_negOp h, fun x => GLNegationOpposite.qdet_antipode h x⟩
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.msetSep :
    ∀ m m' : Multiset ℂ, (∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) → m = m' :=
  _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.expSub :
    ∀ (d d' : ℕ) (S : Subalgebra ℂ (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ))
      (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d') (Fin d') ℂ), (A, B) ∈ S → (NormedSpace.exp A, NormedSpace.exp B) ∈ S := by
  intro d d' S A B h
  have hc : IsClosed (S : Set (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule S)
  have hA : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • A ^ n) (NormedSpace.exp A) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hB : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • B ^ n) (NormedSpace.exp B) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B
  refine hc.mem_of_tendsto (hA.prodMk hB) (Filter.Eventually.of_forall fun s => ?_)
  refine S.sum_mem fun n _ => ?_
  exact S.smul_mem (S.pow_mem h n) ((n.factorial : ℂ)⁻¹)
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem expSq {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (h : N * N = 0) :
    NormedSpace.exp N = 1 + N :=
  _root_.UpperTheory.Reformulated.B.Qf11.expSq N h

theorem UpperTheory.V.AlgRepEndIrreducible.expGenC :
    ∀ (n : ℕ) (H : Submonoid (Matrix (Fin n) (Fin n) ℂ)), (∀ X : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp X ∈ H) →
      ∀ g : Matrix (Fin n) (Fin n) ℂ, g.det ≠ 0 → g ∈ H := by
  intro n H hH g hg
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => M ∈ H) g hg ?_ ?_ ?_
  · intro D hD
    have hD' : ∀ i, D i ≠ 0 := by
      rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hD
      exact fun i => hD i (Finset.mem_univ i)
    have := hH (Matrix.diagonal fun i => Complex.log (D i))
    rw [Matrix.exp_diagonal] at this
    convert this using 2
    funext i
    rw [Pi.exp_def]
    simp only [← Complex.exp_eq_exp_ℂ]
    exact (Complex.exp_log (hD' i)).symm
  · intro t
    have := hH (Matrix.single t.i t.j t.c)
    rw [expSq _ (Matrix.single_mul_single_of_ne _ _ _ _ t.hij.symm _)] at this
    exact this
  · intro A B _ _ hA hB
    exact H.mul_mem hA hB
end
