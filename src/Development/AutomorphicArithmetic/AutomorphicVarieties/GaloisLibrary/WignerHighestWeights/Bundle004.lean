module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.multiHW :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V) [FiniteDimensional ℂ V] [Nontrivial V], IsMultiGl F →
      ∃ (ν : ι → Fin n → ℂ) (v : V), v ≠ 0 ∧ ∀ t, Formalism.REAL.IsHW (F t) (ν t) v ∧ Dom (ν t) := by
  intro ι V _ _ _ n F _ _ hM
  obtain ⟨hF, hcomm⟩ := hM
  classical
  have hc : ∀ t k i j, F t k k * F t i j - F t i j * F t k k =
      ((if k = i then (1 : ℂ) else 0) - (if j = k then 1 else 0)) • F t i j := by
    intro t k i j
    rw [hF t]
    by_cases h1 : k = i <;> by_cases h2 : j = k <;> simp_all
  let G : ι → Module.End ℂ V := fun s => ∑ k : Fin n, ((k : ℕ) : ℂ) • F s k k
  have hG : ∀ t i j, G t * F t i j - F t i j * G t = (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j := by
    intro t i j
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, hc, smul_smul, ← Finset.sum_smul]
    simp [mul_sub]
  have hG' : ∀ s t, s ≠ t → ∀ i j, G s * F t i j - F t i j * G s = 0 := by
    intro s t hst i j
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, hcomm s t hst, sub_self]
  let H : Module.End ℂ V := ∑ s, G s
  have hH : ∀ t i j, H * F t i j = F t i j * H + (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j := by
    intro t i j
    rw [← sub_eq_iff_eq_add', Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single t (fun s _ hs => hG' s t hs i j) (by simp), hG]
  obtain ⟨l, hl, hmin⟩ := Set.exists_min_image {c | H.HasEigenvalue c} Complex.re (Module.End.finite_hasEigenvalue H)
    (Module.End.exists_eigenvalue H)
  obtain ⟨v, hv, hv0, ν, hν⟩ := GlobalTheory.AlgInfChar.exists_joint_eigenvector (fun p : ι × Fin n => F p.1 p.2 p.2)
    (fun p q => by
      obtain ⟨s, i⟩ := p
      obtain ⟨t, j⟩ := q
      by_cases hst : s = t
      · subst hst
        rw [← sub_eq_zero, hc]
        by_cases h : i = j <;> simp [h, eq_comm]
      · exact hcomm s t hst _ _ _ _) (H.eigenspace l) hl
    (fun k v hv => by
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, hH]
      simp [hv])
  rw [Module.End.mem_eigenspace_iff] at hv
  have hup : ∀ t i j, i < j → F t i j v = 0 := by
    intro t i j hij
    by_contra h0
    have h1 : H (F t i j v) = (l + (((i : ℕ) : ℂ) - (j : ℕ))) • F t i j v := by
      rw [← Module.End.mul_apply, hH]
      simp [hv, add_smul]
    have h2 := hmin _ (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h1, h0⟩)
    simp at h2
    exact absurd hij (not_lt.2 h2)
  have hν' : ∀ t k, F t k k v = ν (t, k) • v := fun t k => hν (t, k)
  refine ⟨fun t k => ν (t, k), v, hv0, fun t => ⟨⟨hν' t, hup t⟩, fun i j hij =>
    GlobalTheory.AlgInfChar.exists_nat_of_primitive (F t i j) (F t j i) (F t i i - F t j j) ?_ ?_ v _ hv0
      (hup t i j hij) ?_⟩⟩
  · rw [hF t]; simp
  · have h1 := hc t i j i
    have h2 := hc t j j i
    simp only [hij.ne, if_false, if_true] at h1 h2
    rw [sub_mul, mul_sub]
    linear_combination (norm := module) h1 - h2
  · simp [hν', sub_smul]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private noncomputable def actAlg (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)) :=
  (Module.End.lTensorAlgHom ℂ (Fin d → ℂ) V).comp
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom

private noncomputable def actOp (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] (Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)))ᵐᵒᵖ where
  toFun N := MulOpposite.op (actAlg V d Nᵀ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.transpose_mul]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.transpose_add]
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

private theorem actOp_apply (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) (N : Matrix (Fin d) (Fin d) ℂ) :
    actOp V d N = MulOpposite.op (actAlg V d Nᵀ) := rfl

set_option synthInstance.maxHeartbeats 100000 in
theorem UpperTheory.V.AlgRepEndIrreducible.tensB :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), IsLieHom (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) ∧
      (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), tensorK π Ξ k * lieB π Ξ (toL X) = lieB π Ξ (toL (k.1 * X * star k.1)) * tensorK π Ξ k) ∧
      ∀ (τ : E →+* ℂ) (m : Multiset ℂ), GlobalTheory.WignerGL.HasDualInfChar Ξ τ m → ∀ u : ℂ,
        Formalism.REAL.qdet (fun i j => -MulOpposite.op (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) τ i j)) (u + ((a : ℂ) - 1) / 2) =
          MulOpposite.op ((m.map (u + ·)).prod • (1 : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)))) := by
  intro E _ _ _ a π Ξ
  have hB : ∀ X, lieB π Ξ X = actAlg π.V Ξ.d (Ξ.dmat X) := fun _ => rfl
  refine ⟨fun X Y => ?_, fun k X => ?_, fun τ m hm u => ?_⟩
  · rw [hB, hB, hB, ← GlobalTheory.AlgInfChar.dmat_bracket, map_sub, map_mul, map_mul]
  · refine TensorProduct.ext' fun φ v => ?_
    have h2 : Ξ.mat (Unitary.toUnits k) * Ξ.dmat (toL X) =
        Ξ.dmat (toL (k.1 * X * star k.1)) * Ξ.mat (Unitary.toUnits k) :=
      Ξ.mat_mul_dmat (Unitary.toUnits k) X
    simp only [mul_apply_eq_comp, tensorK, lieB_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
  · have h0 := map_qdet (A := Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (B := (Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)))ᵐᵒᵖ)
      (actOp π.V Ξ.d) (GlobalTheory.WignerGL.dualE Ξ τ) (u + ((a : ℂ) - 1) / 2)
    have h := h0.symm.trans (congrArg (actOp π.V Ξ.d) (hm.2 u))
    rw [map_smul, map_one] at h
    have e : ∀ i j, actOp π.V Ξ.d (GlobalTheory.WignerGL.dualE Ξ τ i j) =
        -MulOpposite.op (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) τ i j) := fun i j => by
      rw [dualE_eq, map_neg, actOp_apply, Matrix.transpose_transpose]
      simp only [eL, hB, map_smul, map_sub]
    simp only [e] at h
    rw [h, MulOpposite.op_smul, MulOpposite.op_one]
end
