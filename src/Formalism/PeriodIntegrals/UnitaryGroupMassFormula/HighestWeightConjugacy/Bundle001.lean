module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.LongestElementTranspose
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

open scoped Classical in
open Classical in
def repPt {L : Type} [Field L] [NumberField L] {n : ℕ} (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) :
    (L →+* ℂ) × Fin n × Fin n → ℂ := fun p =>
  if p.1 = (InfinitePlace.mk p.1).embedding then Y (InfinitePlace.mk p.1) p.2.1 p.2.2
  else (Y (InfinitePlace.mk p.1))⁻¹ p.2.2 p.2.1

def DensA : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ γ₀ ∈ GQ0 L n, MvPolynomial.eval (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) F = 0) →
    ∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ, (∀ w, (Y w)ᴴ * Y w = 1) → (∀ w, (1 + Y w).det ≠ 0) →
      MvPolynomial.eval (repPt Y) F = 0

def DensB : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ, (∀ w, (Y w)ᴴ * Y w = 1) → (∀ w, (1 + Y w).det ≠ 0) →
      MvPolynomial.eval (repPt Y) F = 0) →
    ∀ y, InV y → MvPolynomial.eval y F = 0

theorem densStep_of (ha : DensA) (hb : DensB) : DensStep :=
  fun L _ _ _ n F h => hb L n F (ha L n F h)

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

section

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

abbrev Vars (L : Type) [Field L] (n : ℕ) := (L →+* ℂ) × Fin n × Fin n

def vmul (y z : Vars L n → ℂ) : Vars L n → ℂ := fun p => ∑ k, y (p.1, p.2.1, k) * z (p.1, k, p.2.2)

theorem eval_aeval_eq {σ' : Type} (y : σ' → ℂ) (f : Vars L n → MvPolynomial σ' ℂ) (Q : MvPolynomial (Vars L n) ℂ) :
    MvPolynomial.eval y (MvPolynomial.aeval f Q) = MvPolynomial.eval (fun p => MvPolynomial.eval y (f p)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p i hp => rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, map_mul, MvPolynomial.eval_X]

def tInv (g : GL (Fin n) ℂ) : GL (Fin n) ℂ :=
  ⟨((g⁻¹).val)ᵀ, (g.val)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]⟩

theorem inV_evPt (τ : L →+* ℂ) (g : GL (Fin n) ℂ) : InV (evPt τ g) := by
  intro σ
  by_cases h1 : σ = τ
  · subst h1
    refine ⟨g, fun i j => ⟨?_, ?_⟩⟩
    · simp [evPt]
    · simp [evPt, conj_ne σ]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      refine ⟨tInv g, fun i j => ⟨?_, ?_⟩⟩
      · simp [evPt, conj_ne τ, tInv]
      · simp [evPt, conj_conj, tInv]
    · have h3 : ComplexEmbedding.conjugate σ ≠ τ := fun h => h2 (by rw [← h, conj_conj])
      have h4 : ComplexEmbedding.conjugate σ ≠ ComplexEmbedding.conjugate τ := fun h => h1 (by
        rw [← conj_conj σ, h, conj_conj])
      refine ⟨1, fun i j => ⟨?_, ?_⟩⟩
      · simp [evPt, h1, h2, Matrix.one_apply]
      · simp [evPt, h3, h4, Matrix.one_apply, eq_comm]

theorem unit_conj (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) (i j : Fin n) :
    (IsCMField.complexConj L : L →+* L) (γ₀.val i j) = (γ₀⁻¹).val j i := by
  have hg' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := hg
  rw [Units.inv_eq_of_mul_eq_one_right hg']
  rfl

theorem conj_ratPt (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) (σ : L →+* ℂ) (i j : Fin n) :
    (ComplexEmbedding.conjugate σ) (γ₀.val i j) = σ ((γ₀⁻¹).val j i) := by
  rw [← unit_conj γ₀ hg]
  exact (IsCMField.complexEmbedding_complexConj (K := L) σ _).symm

theorem inV_ratPt (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) : InV (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) := by
  intro σ
  refine ⟨Matrix.GeneralLinearGroup.map σ γ₀, fun i j => ⟨rfl, ?_⟩⟩
  rw [← map_inv]
  exact conj_ratPt γ₀ hg σ i j


open Classical in
def trivAt (τ : L →+* ℂ) (y : Vars L n → ℂ) : Vars L n → ℂ := fun p =>
  if p.1 = τ ∨ p.1 = ComplexEmbedding.conjugate τ then (if p.2.1 = p.2.2 then 1 else 0) else y p

theorem inV_trivAt (τ : L →+* ℂ) (y : Vars L n → ℂ) (hy : InV y) : InV (trivAt τ y) := by
  intro σ
  by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
  · have h' : ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ := by
      rcases h with h | h <;> subst h <;> simp [conj_conj]
    refine ⟨1, fun i j => ⟨?_, ?_⟩⟩
    · simp only [trivAt, if_pos h]; simp [Matrix.one_apply]
    · simp only [trivAt, if_pos h']; simp [Matrix.one_apply, eq_comm]
  · have h' : ¬ (ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ) := by
      rintro (h1 | h1)
      · exact h (Or.inr (by rw [← h1, conj_conj]))
      · exact h (Or.inl (by rw [← conj_conj σ, h1, conj_conj]))
    obtain ⟨B, hB⟩ := hy σ
    exact ⟨B, fun i j => by simp only [trivAt, h, h', if_false]; exact hB i j⟩

theorem trivAt_tau (τ : L →+* ℂ) (y : Vars L n → ℂ) (i j : Fin n) :
    trivAt τ y (τ, i, j) = if i = j then 1 else 0 := by simp [trivAt]

theorem trivAt_conj (τ : L →+* ℂ) (y : Vars L n → ℂ) (i j : Fin n) :
    trivAt τ y (ComplexEmbedding.conjugate τ, i, j) = if i = j then 1 else 0 := by simp [trivAt]

theorem ratPt_split (τ : L →+* ℂ) (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) :
    ratPt (γ₀ : Matrix (Fin n) (Fin n) L) =
      vmul (trivAt τ (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) (evPt τ (Matrix.GeneralLinearGroup.map τ γ₀)) := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  by_cases h1 : σ = τ
  · subst h1
    simp [vmul, trivAt, evPt, ratPt]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      have e1 : ∀ k, trivAt τ (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) (ComplexEmbedding.conjugate τ, i, k) =
          if i = k then 1 else 0 := fun k => trivAt_conj τ _ i k
      have e2 : ∀ k, evPt τ (Matrix.GeneralLinearGroup.map τ γ₀) (ComplexEmbedding.conjugate τ, k, j) =
          ((Matrix.GeneralLinearGroup.map τ γ₀)⁻¹).val j k := fun k => by
        simp only [evPt, conj_ne τ, if_false, if_true]
      simp only [vmul, e1, e2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      show (ComplexEmbedding.conjugate τ) (γ₀.val i j) = _
      rw [conj_ratPt γ₀ hg, ← map_inv]
      rfl
    · simp [vmul, trivAt, evPt, ratPt, h1, h2]

theorem vmul_comm_evPt (τ : L →+* ℂ) (y : Vars L n → ℂ)
    (hy : ∀ i j, y (τ, i, j) = (if i = j then 1 else 0) ∧ y (ComplexEmbedding.conjugate τ, i, j) = (if i = j then 1 else 0))
    (g : GL (Fin n) ℂ) : vmul y (evPt τ g) = vmul (evPt τ g) y := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  by_cases h1 : σ = τ
  · subst h1
    simp [vmul, evPt, (hy _ _).1]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp [vmul, evPt, (hy _ _).2, conj_ne τ]
    · simp [vmul, evPt, h1, h2]

theorem evPt_mul (τ : L →+* ℂ) (g h : GL (Fin n) ℂ) : evPt τ (g * h) = vmul (evPt τ g) (evPt τ h) := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  by_cases h1 : σ = τ
  · subst h1
    simp [vmul, evPt, Matrix.mul_apply]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp [vmul, evPt, conj_ne τ, Matrix.mul_apply, mul_comm]
    · simp [vmul, evPt, h1, h2]

end

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

section

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {n : ℕ}

theorem upper_inv (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) : (U⁻¹).val.BlockTriangular id := by
  letI : Invertible U.val := U.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hU

theorem inv_diag (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) (i : Fin n) :
    (U⁻¹).val i i * U.val i i = 1 := by
  have h1 := upper_inv U hU
  have key : ((U⁻¹).val * U.val) i i = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at key
  · exact key
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [h1 (show id k < id i from h), zero_mul]
    · rw [hU (show id i < id k from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

def swapB (U : GL (Fin n) ℂ) : GL (Fin n) ℂ :=
  ⟨((U⁻¹).val)ᵀ.submatrix Fin.rev Fin.rev, (U.val)ᵀ.submatrix Fin.rev Fin.rev,
    by
      rw [show ((U⁻¹).val)ᵀ.submatrix Fin.rev Fin.rev * (U.val)ᵀ.submatrix Fin.rev Fin.rev =
        (((U⁻¹).val)ᵀ * (U.val)ᵀ).submatrix Fin.rev Fin.rev from
          Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm _]
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
      exact Matrix.submatrix_one_equiv Fin.revPerm,
    by
      rw [show (U.val)ᵀ.submatrix Fin.rev Fin.rev * ((U⁻¹).val)ᵀ.submatrix Fin.rev Fin.rev =
        ((U.val)ᵀ * ((U⁻¹).val)ᵀ).submatrix Fin.rev Fin.rev from
          Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm _]
      rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
      exact Matrix.submatrix_one_equiv Fin.revPerm⟩

theorem swapB_val (U : GL (Fin n) ℂ) (i j : Fin n) : (swapB U).val i j = (U⁻¹).val (Fin.rev j) (Fin.rev i) := rfl

theorem swapB_inv_val (U : GL (Fin n) ℂ) (i j : Fin n) : ((swapB U)⁻¹).val i j = U.val (Fin.rev j) (Fin.rev i) := rfl

theorem swapB_upper (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) : (swapB U).val.BlockTriangular id := by
  intro i j hij
  rw [swapB_val]
  apply upper_inv U hU
  exact Fin.rev_lt_rev.mpr hij

theorem swapB_prod (U : GL (Fin n) ℂ) (hU : U.val.BlockTriangular id) (lam' : Fin n → ℤ) :
    ∏ i, (swapB U).val i i ^ lam' i = ∏ i, U.val i i ^ (-lam' (Fin.rev i)) := by
  have hd : ∀ i, (swapB U).val i i = (U.val (Fin.rev i) (Fin.rev i))⁻¹ := by
    intro i
    rw [swapB_val]
    exact eq_inv_of_mul_eq_one_left (inv_diag U hU (Fin.rev i))
  simp only [hd, _root_.inv_zpow']
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by simp)

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def ren : (L →+* ℂ) × Fin n × Fin n → (L →+* ℂ) × Fin n × Fin n := fun p => (p.1, Fin.rev p.2.1, Fin.rev p.2.2)

theorem evPt_swap (τ : L →+* ℂ) (U : GL (Fin n) ℂ) :
    evPt τ U ∘ ren = evPt (ComplexEmbedding.conjugate τ) (swapB U) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    (InfinitePlace.isComplex_mk_iff.mp (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      (ComplexEmbedding.isReal_iff.mpr h)
  have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := star_star τ
  funext p
  obtain ⟨σ, i, j⟩ := p
  simp only [evPt, ren, Function.comp_apply, swapB_val, swapB_inv_val, hcc, Fin.rev_inj]
  have hne' : ¬ τ = ComplexEmbedding.conjugate τ := fun h => hne h.symm
  split_ifs <;> first | rfl | (simp_all <;> rfl)

end

theorem conjugation_swap : ConjSwap := by
  intro L _ _ _ n a τ lam' h
  obtain ⟨ι, hι, hd, b, P, hP, v, hv0, hv⟩ := h
  let w : GQ L n := toGQ w0L longest_element_mem
  let e : a.W ≃ₗ[ℂ] a.W := LinearEquiv.ofLinear (a.ρ w) (a.ρ w⁻¹)
    (by ext x; rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by ext x; rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl)
  refine ⟨ι, hι, hd, b.map e, fun i j => MvPolynomial.rename ren (P i j), ?_, v, hv0, ?_⟩
  · intro γ γ₀ hγ
    let γ₀' : GL (Fin n) L := w0L⁻¹ * γ₀ * w0L
    have hγ' : ((((w⁻¹ * γ * w : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀' : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
      have e1 : (((w⁻¹ * γ * w : GQ L n) : GAf L n) : GL (Fin n) (AL L)) =
          Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) (w0L⁻¹) *
            ((γ : GAf L n) : GL (Fin n) (AL L)) *
            Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) w0L := by
        rw [map_inv]; rfl
      rw [e1, Units.val_mul, Units.val_mul, hγ]
      simp only [γ₀', Units.val_mul, Matrix.map_mul]
      rfl
    have hq := hP _ _ hγ'
    ext i j
    have hq' := congrFun (congrFun hq i) j
    rw [LinearMap.toMatrix_apply] at hq'
    rw [LinearMap.toMatrix_apply, Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply]
    have e2 : e.symm (a.ρ γ (e (b j))) = a.ρ (w⁻¹ * γ * w) (b j) := by
      rw [map_mul, map_mul]; rfl
    rw [e2, hq', MvPolynomial.eval_rename]
    refine congrArg (fun f => MvPolynomial.eval f (P i j)) ?_
    funext p
    simp only [Function.comp, ren, γ₀', Units.val_mul]
    have e3 : ((w0L⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = W0 L n := rfl
    have e4 : ((w0L : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = W0 L n := rfl
    rw [e3, e4, longest_element_conj]
    rfl
  · intro U hU
    have hB := hv (swapB U) (swapB_upper U hU)
    rw [swapB_prod U hU] at hB
    rw [← hB]
    congr 1
    ext i j
    simp only [Matrix.of_apply, MvPolynomial.eval_rename, evPt_swap]

end PI.UnitaryGroupMassFormula.HwConjInf
end
end
