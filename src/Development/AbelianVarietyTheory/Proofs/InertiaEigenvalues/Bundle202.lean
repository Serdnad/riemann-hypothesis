module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle149
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceFinExt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuCocycleCoboundaryLift
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TamePairing
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Formalism.CharacterColumnKernels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle105
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Data.FunLike.Fintype

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt.AdBridge

section Maps

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}

theorem Aof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Aof (M.map f) = (Aof M).map f := rfl
theorem Bof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Bof (M.map f) = (Bof M).map f := rfl
theorem Cof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Cof (M.map f) = (Cof M).map f := rfl
theorem Dof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Dof (M.map f) = (Dof M).map f := rfl

theorem inv_map_of_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (h : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one f (map_zero f) (map_one f)]

theorem Yof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Yof (M.map f) = (Yof M).map f := by
  rw [Yof, Yof, Matrix.map_mul, Dof_map, Cof_map, inv_map_of_isUnit f _ h]

theorem Xof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Xof (M.map f) = (Xof M).map f := by
  rw [Xof, Xof, Matrix.map_mul, Dof_map, Bof_map, inv_map_of_isUnit f _ h]

theorem Scof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Scof (M.map f) = (Scof M).map f := by
  rw [Scof, Scof, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, Aof_map, Dof_map, Bof_map, Cof_map,
    inv_map_of_isUnit f _ h]

theorem lowUni_map (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) :
    (lowUni Y).map f = lowUni (Y.map f) := by
  ext i j
  simp only [lowUni, unblk, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (eqv m r i) with a | a <;> rcases (eqv m r j) with b | b <;>
    simp [Matrix.one_apply, apply_ite f]

theorem conjLowUni_map (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (conjLowUni Y k).map f = conjLowUni (Y.map f) (k.map f) := by
  rw [conjLowUni, conjLowUni, Matrix.map_mul, Matrix.map_mul, lowUni_map, lowUni_map, Matrix.map_neg _ (map_neg f)]

end Maps

section Ones

variable {R : Type} [CommRing R] {m r : ℕ}

theorem blk_one : blk (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  simp [blk]

theorem Aof_one : Aof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Aof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]
theorem Bof_one : Bof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Bof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂]
theorem Cof_one : Cof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Cof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]
theorem Dof_one : Dof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Dof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]
theorem Yof_one : Yof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Yof, Cof_one, Matrix.mul_zero]
theorem Xof_one : Xof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Xof, Bof_one, Matrix.zero_mul]
theorem Scof_one : Scof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Scof, Aof_one, Bof_one, Cof_one]; simp

theorem unblk_mul (P Q : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    unblk P * unblk Q = unblk (P * Q) := Matrix.submatrix_mul_equiv _ _ _ _ _

theorem unblk_one : unblk (1 : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) = 1 := by
  simp [unblk]

theorem lowUni_mul_neg (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : lowUni Y * lowUni (-Y) = 1 := by
  rw [lowUni, lowUni, unblk_mul, Matrix.fromBlocks_multiply]
  simp [unblk_one]

theorem conjLowUni_one (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : conjLowUni Y 1 = 1 := by
  rw [conjLowUni, Matrix.mul_one, lowUni_mul_neg]

theorem det_lowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : (lowUni (m := m) Y).det = 1 := by
  rw [lowUni, unblk, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]; simp

theorem det_conjLowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (conjLowUni Y k).det = k.det := by
  rw [conjLowUni, Matrix.det_mul, Matrix.det_mul, det_lowUni, det_lowUni]; ring

theorem det_eq_det_Dof_mul (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    M.det = (Dof M).det * (Scof M).det := by
  letI := Matrix.invertibleOfIsUnitDet _ h
  have e : Matrix.fromBlocks (Aof M) (Bof M) (Cof M) (Dof M) = blk M := Matrix.fromBlocks_toBlocks _
  have h1 : M.det = (blk M).det := by rw [blk, Matrix.det_submatrix_equiv_self]
  rw [h1, ← e, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]; rfl

theorem isUnit_det_Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (hM : IsUnit M.det)
    (h : IsUnit (Dof M).det) : IsUnit (Scof M).det := by
  rw [det_eq_det_Dof_mul M h] at hM
  exact isUnit_of_mul_isUnit_right hM

end Ones

section Adeles

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem pInf_sFin_eq_zero (b : Af E) : pInf E (sFin E b) = 0 := map_zero (infEq E).symm

omit [_root_.NumberField.IsTotallyComplex E] in
theorem pFin_sFin_eq (b : Af E) : pFin E (sFin E b) = b := rfl

theorem isUnit_of_parts {x : Ad E} (h1 : IsUnit (pInf E x)) (h2 : IsUnit (pFin E x)) : IsUnit x := by
  refine Prod.isUnit_iff.2 ⟨?_, h2⟩
  have e : (infEq E) (pInf E x) = x.1 := (infEq E).apply_symm_apply x.1
  rw [← e]; exact h1.map _

theorem map_pInf_finGL {n : ℕ} (k : GL (Fin n) (Af E)) :
    (finGL E n k : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1 :=
  congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) (pInf_finGL k)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem map_pFin_finGL {n : ℕ} (k : GL (Fin n) (Af E)) :
    (finGL E n k : Matrix (Fin n) (Fin n) (Ad E)).map (pFin E) = (k : Matrix (Fin n) (Fin n) (Af E)) :=
  congrArg (fun g : GL (Fin n) (Af E) => (g : Matrix (Fin n) (Fin n) (Af E))) (pFin_finGL k)

theorem coe_finGL_mkGL {n : ℕ} (M : Matrix (Fin n) (Fin n) (Ad E)) (hi : M.map (pInf E) = 1) (hu : IsUnit M.det) :
    (finGL E n (mkGL (M.map (pFin E))) : Matrix (Fin n) (Fin n) (Ad E)) = M := by
  have hu' : IsUnit (M.map (pFin E)).det := by
    have h := hu.map (pFin E)
    rwa [RingHom.map_det] at h
  ext i j
  refine ad_ext ?_ ?_
  · exact congrFun (congrFun ((map_pInf_finGL _).trans hi.symm) i) j
  · exact congrFun (congrFun ((map_pFin_finGL _).trans (coe_mkGL hu')) i) j

end Adeles

theorem schur_data_mul_finGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := by
  intro E _ _ _ m r x k hD hD'
  rw [Units.val_mul]
  have hx : IsUnit (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  have hK : IsUnit (finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (finGL E (m + r + 1 + 1) k).isUnit
  have hKi := map_pInf_finGL (E := E) k
  have hKf := map_pFin_finGL (E := E) k
  generalize (finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = K at *
  generalize (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = g at *
  have hf : conjLowUni ((Yof g).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)) =
      (conjLowUni (Yof g) K).map (pFin E) := by rw [conjLowUni_map, hKf]
  have hi : (conjLowUni (Yof g) K).map (pInf E) = 1 := by rw [conjLowUni_map, hKi, conjLowUni_one]
  have hdet : IsUnit (conjLowUni (Yof g) K).det := by rwa [det_conjLowUni]
  rw [hf] at hD' ⊢
  have alg := GlobalTheory.T.lower_unipotent_conj_block_formulas (Ad E) m r g K hD
  generalize conjLowUni (Yof g) K = L at *
  have hDi : (Dof L).map (pInf E) = 1 := by rw [← Dof_map, hi, Dof_one]
  have hDL : IsUnit (Dof L).det := by
    refine isUnit_of_parts ?_ ?_
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, hDi, Matrix.det_one]; exact isUnit_one
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Dof_map]; exact hD'
  obtain ⟨a1, a2, a3, a4, a5⟩ := alg hDL
  have hS := isUnit_det_Scof g hx hD
  have hSL := isUnit_det_Scof L hdet hDL
  have hSi : (Scof L).map (pInf E) = 1 := by rw [← Scof_map _ _ hDL, hi, Scof_one]
  have hYi : (Yof L).map (pInf E) = 0 := by rw [← Yof_map _ _ hDL, hi, Yof_one]
  have hXi : (Xof L).map (pInf E) = 0 := by rw [← Xof_map _ _ hDL, hi, Xof_one]
  have hXi' : ∀ j l, pInf E (Xof L j l) = 0 := fun j l => congrFun (congrFun hXi j) l
  refine ⟨hS, a1, Units.ext ?_, Units.ext ?_, fun i j => ?_, fun i j => ?_, ?_⟩
  · rw [coe_mkGL a1, Units.val_mul, coe_mkGL hD, Dof_map, coe_finGL_mkGL _ hDi hDL, a2]
  · have hSgK : IsUnit (Scof (g * K)).det := by rw [a4, Matrix.det_mul]; exact hS.mul hSL
    rw [coe_mkGL hSgK, Units.val_mul, coe_mkGL hS, Scof_map _ _ hDL, coe_finGL_mkGL _ hSi hSL, a4]
  · have h0 : pInf E (Yof L i j) = 0 := congrFun (congrFun hYi i) j
    rw [a3, Matrix.add_apply, map_add (f := _), h0, add_zero]
  · rw [a3, Matrix.add_apply, map_add (f := _), Yof_map _ _ hDL, Matrix.map_apply]
  · rw [a5, Matrix.add_apply, Xof_map _ _ hDL]
    congr 1
    refine ad_ext ?_ ?_
    · rw [pInf_sFin_eq_zero]

      simp only [Matrix.mul_apply, map_sum, map_mul, hXi', mul_zero, Finset.sum_const_zero, zero_mul]
    · rw [pFin_sFin_eq, Finset.sum_comm]

      simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Matrix.map_apply]

end GlobalTheory.SchurExt.AdBridge
end
end

section

noncomputable section

namespace GlobalTheory.HWL.BanachEval

open PowerSeries Filter Finset GlobalTheory.HWL.Disc

variable {K : Type} [NormedField K] {N : Type} [NormedCommRing N]

def Small (ν : N) : Prop := ∃ C r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ‖ν ^ k‖ ≤ C * r ^ k

def Bdd (c : K →+* N) : Prop := ∃ C : ℝ, ∀ x, ‖c x‖ ≤ C * ‖x‖

def ev (c : K →+* N) (ν : N) (a : K⟦X⟧) : N := ∑' k : ℕ, c (coeff k a) * ν ^ k

variable {c : K →+* N} {ν : N}

theorem Bdd.continuous (hc : Bdd c) : Continuous c := by
  obtain ⟨C, h⟩ := hc
  exact AddMonoidHomClass.continuous_of_bound c C h

theorem exists_bound (hc : Bdd c) (hν : Small ν) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ (x : K) (k : ℕ), ‖c x * ν ^ k‖ ≤ C * (‖x‖ * r ^ k) := by
  obtain ⟨C, h⟩ := hc
  obtain ⟨D, r, h0, h1, h2⟩ := hν
  refine ⟨|C| * |D|, r, by positivity, h0, h1, fun x k => (norm_mul_le _ _).trans ?_⟩
  have e1 : ‖c x‖ ≤ |C| * ‖x‖ := (h x).trans (by gcongr; exact le_abs_self C)
  have e2 : ‖ν ^ k‖ ≤ |D| * r ^ k := (h2 k).trans (by gcongr; exact le_abs_self D)
  calc _ ≤ (|C| * ‖x‖) * (|D| * r ^ k) := by gcongr
    _ = _ := by ring

theorem summable_norm (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    Summable fun k : ℕ => ‖c (coeff k a) * ν ^ k‖ := by
  obtain ⟨C, r, -, h0, h1, h⟩ := exists_bound hc hν
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => h _ k) ((ha r h0 h1).mul_left C)

theorem Small.tendsto (hν : Small ν) : Tendsto (fun k : ℕ => ν ^ k) atTop (nhds 0) := by
  obtain ⟨D, r, h0, h1, h2⟩ := hν
  refine squeeze_zero_norm h2 ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul D

theorem ev_C_mul (hc : Bdd c) (hν : Small ν) [CompleteSpace N] (x : K) {a : K⟦X⟧} (ha : SC a) :
    ev c ν (x • a) = c x * ev c ν a := by
  rw [ev, ev, ← (summable_norm hc hν ha).of_norm.tsum_mul_left]
  simp [mul_assoc]

theorem sum_range_eq (a : K⟦X⟧) (m : ℕ) :
    ∑ k ∈ range m, c (coeff k a) * ν ^ k = Polynomial.eval₂ c ν (trunc m a) := by
  rw [eval₂_trunc_eq_sum_range]

variable [CompleteSpace N]

theorem hasSum_ev (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    HasSum (fun k : ℕ => c (coeff k a) * ν ^ k) (ev c ν a) :=
  (summable_norm hc hν ha).of_norm.hasSum

theorem tendsto_ev (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    Tendsto (fun m : ℕ => Polynomial.eval₂ c ν (trunc m a)) atTop (nhds (ev c ν a)) := by
  simpa only [sum_range_eq] using (hasSum_ev hc hν ha).tendsto_sum_nat

theorem ev_add (hc : Bdd c) (hν : Small ν) {a b : K⟦X⟧} (ha : SC a) (hb : SC b) :
    ev c ν (a + b) = ev c ν a + ev c ν b := by
  refine HasSum.tsum_eq ?_
  simpa only [map_add (f := _), add_mul] using (hasSum_ev hc hν ha).add (hasSum_ev hc hν hb)

theorem ev_mul (hc : Bdd c) (hν : Small ν) {a b : K⟦X⟧} (ha : SC a) (hb : SC b) :
    ev c ν (a * b) = ev c ν a * ev c ν b := by
  rw [ev, ev, ev, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm hc hν ha)
    (summable_norm hc hν hb)]
  refine tsum_congr fun k => ?_

  rw [coeff_mul, map_sum, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [← mem_antidiagonal.1 hp, map_mul, pow_add]
  ring

theorem ev_one : ev c ν 1 = 1 := by
  rw [ev, tsum_eq_single 0 fun k hk => by simp [coeff_one, hk]]
  simp

theorem sc_pow {a : K⟦X⟧} (ha : SC a) (k : ℕ) : SC (a ^ k) := by
  induction k with
  | zero => simpa using sc_coe (1 : Polynomial K)
  | succ k ih => rw [pow_succ]; exact ih.mul ha

theorem ev_pow (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) (k : ℕ) :
    ev c ν (a ^ k) = ev c ν a ^ k := by
  induction k with
  | zero => simpa using ev_one
  | succ k ih => rw [pow_succ, pow_succ, ev_mul hc hν (sc_pow ha k) ha, ih]

theorem hasSum_map (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) (f : N →+* N) (hf : Continuous f)
    (hfc : ∀ x, f (c x) = c x) : HasSum (fun k : ℕ => c (coeff k a) * f ν ^ k) (f (ev c ν a)) := by
  have := (hasSum_ev hc hν ha).map f hf
  simpa only [Function.comp_def, map_mul, map_pow, hfc] using this

theorem ev_map {O : Type} [CommRing O] (j : O →+* K) (hν : Small ν) (hc : Bdd c) (f : O⟦X⟧ →+* N)
    (hC : ∀ o, f (C o) = c (j o)) (hX : f X = ν) (hf : ∀ a, ‖f a‖ ≤ 1) (a : O⟦X⟧) (ha : SC (map j a)) :
    ev c ν (map j a) = f a := by
  refine tendsto_nhds_unique (hasSum_ev hc hν ha).tendsto_sum_nat ?_
  have key : ∀ m : ℕ, ∑ k ∈ range m, c (coeff k (map j a)) * ν ^ k =
      f a - ν ^ m * f (mk fun i => coeff (i + m) a) := by
    intro m
    have e0 := congrArg f (eq_X_pow_mul_shift_add_trunc m a)
    rw [e0, map_add (f := _), map_mul, map_pow, hX, add_sub_cancel_left, trunc_apply, Polynomial.coe_def]
    have e : (mk (∑ k ∈ Ico 0 m, Polynomial.monomial k (coeff k a)).coeff : O⟦X⟧) =
        ∑ k ∈ range m, C (coeff k a) * X ^ k := by
      ext n
      simp [coeff_X_pow, Polynomial.coeff_monomial, Polynomial.finsetSum_coeff, Finsupp.single_apply]

    rw [e, map_sum]
    simp only [map_mul, map_pow, hX, hC, coeff_map]
  simp only [key]
  conv => rhs; rw [← sub_zero (f a)]
  refine tendsto_const_nhds.sub (squeeze_zero_norm (a := fun m => ‖ν ^ m‖) (fun m => ?_) ?_)
  · exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hf _))
  · simpa using hν.tendsto.norm

theorem hasSum_subst [IsUltrametricDist K] (hc : Bdd c) (hν : Small ν) {y a : K⟦X⟧} (hy0 : constantCoeff y = 0)
    (hy : ∀ k, ‖coeff k y‖ ≤ 1) (ha : SC a) :
    HasSum (fun k : ℕ => c (coeff k a) * ev c ν y ^ k) (ev c ν (subst y a)) := by
  obtain ⟨C, r, hC, h0, h1, h⟩ := exists_bound hc hν
  have hy' : SC y := sc_of_le 0 fun k => by simpa using hy k
  have hp : ∀ k n, ‖coeff n (y ^ k)‖ ≤ 1 := fun k n => by
    simpa using norm_coeff_pow_le y n (r := 1) (R := 1) zero_le_one zero_le_one (fun i _ => by simpa using hy i) k n le_rfl
  have hz : ∀ k n, n < k → coeff n (y ^ k) = 0 := fun k n hn =>
    X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hy0) k) n hn
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ r = ρ * ρ :=
    ⟨√r, Real.sqrt_pos.2 h0, by rwa [Real.sqrt_lt' one_pos, one_pow], (Real.mul_self_sqrt h0.le).symm⟩
  let F : ℕ × ℕ → N := fun p => c (coeff p.1 a * coeff p.2 (y ^ p.1)) * ν ^ p.2
  have hF : Summable F := by
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ => (C * (‖coeff p.1 a‖ * ρ ^ p.1)) * ρ ^ p.2)
      (Summable.mul_of_nonneg ((ha ρ hρ0 hρ1).mul_left C) (summable_geometric_of_lt_one hρ0.le hρ1)
        (fun _ => by positivity) fun _ => by positivity) fun p => ?_
    by_cases hlt : p.2 < p.1
    · simp only [F, hz _ _ hlt, mul_zero, map_zero, zero_mul, norm_zero]
      positivity
    · refine (h _ _).trans ?_
      have e : ρ ^ p.2 ≤ ρ ^ p.1 := pow_le_pow_of_le_one hρ0.le hρ1.le (not_lt.1 hlt)
      rw [norm_mul, hρ, mul_pow]
      calc _ ≤ C * (‖coeff p.1 a‖ * 1 * (ρ ^ p.1 * ρ ^ p.2)) := by gcongr; exact hp _ _
        _ = _ := by ring
  have h2 : HasSum (fun n : ℕ => c (coeff n (subst y a)) * ν ^ n) (∑' p, F p) := by
    refine HasSum.prod_fiberwise ((Equiv.prodComm ℕ ℕ).hasSum_iff.2 hF.hasSum) fun n => ?_
    have e : coeff n (subst y a) = ∑ k ∈ range (n + 1), coeff k a * coeff n (y ^ k) := by
      rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hy0), finsum_eq_sum_of_support_subset (s := range (n + 1))]
      · simp
      · intro k hk
        by_contra hk'
        apply hk
        simp only [coe_range, Set.mem_Iio, not_lt] at hk'
        simp [hz k n hk']

    rw [e, map_sum, sum_mul]
    refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
    simp only [mem_range, not_lt] at hk
    simp [F, hz k n hk]
  rw [show ev c ν (subst y a) = _ from h2.tsum_eq]
  refine HasSum.prod_fiberwise hF.hasSum fun k => ?_
  rw [← ev_pow hc hν hy']
  simpa only [F, map_mul, mul_assoc] using (hasSum_ev hc hν (sc_pow hy' k)).mul_left (c (coeff k a))

end GlobalTheory.HWL.BanachEval
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.mu_cocycle_coboundary_lift : LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (n : ℕ) (w : Z2 (muLoc F l 1 A)) (a : Dec (F := F) A → ZMod (l ^ (n + 1))), Continuous a → (∀ g h : Dec (F := F) A, ((cycMod F Ω l (n + 1) g : (ZMod (l ^ (n + 1)))ˣ) : ZMod (l ^ (n + 1))) * a h - a (g * h) + a g = ((l ^ n * (w.1 (g, h)).val : ℕ) : ZMod (l ^ (n + 1)))) → (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 := by
  first | exact @GlobalTheory.MuTowerInj.mk_eq_zero_of_coboundary | exact GlobalTheory.MuTowerInj.mk_eq_zero_of_coboundary | (intros; apply GlobalTheory.MuTowerInj.mk_eq_zero_of_coboundary <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.tame_pairing_statement : TameLocal → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → normV v ≡ 1 [MOD l ^ 1] → (∀ g : Dec (F := F) A, cycMod F Ω l 1 g = 1) → ∀ e : H2 (muLoc F l 1 A) →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1), Function.Bijective e → ∀ (M : ℕ), 1 ≤ M → ∀ d : G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (G F Ω)) → ∀ γ φ : Dec (F := F) A, (γ : G F Ω) ∈ Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → IsFrob A (normV v) (φ : G F Ω) → ∃ u : (ZMod (l ^ 1))ˣ, ∀ z y : Dec (F := F) A → ZMod (l ^ 1), Continuous z → Continuous y → (∀ g h, z (g * h) = z g + z h) → (∀ g h, y (g * h) = y g + y h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → y g = 0) → ∀ w : Z2 (muLoc F l 1 A), (∀ g h, w.1 (g, h) = z g * y h) → e (Submodule.Quotient.mk w) = (u : ZMod (l ^ 1)) * (z γ * y φ) := by
  first | exact @GlobalTheory.TamePairing.tame_pairing | exact GlobalTheory.TamePairing.tame_pairing | (intros; apply GlobalTheory.TamePairing.tame_pairing <;> assumption)
end

section

open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

theorem finite_card_dual {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Finite V] :
    Finite (Module.Dual F V) ∧ Nat.card (Module.Dual F V) = Nat.card V := by
  haveI : Module.Finite F V := Module.Finite.of_finite
  haveI : Finite (Module.Dual F V) := DFunLike.finite (Module.Dual F V)
  refine ⟨inferInstance, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := F), Module.natCard_eq_pow_finrank (K := F) (V := V),
    Subspace.dual_finrank_eq]

theorem card_H2_level_rep_le :
    Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M)
    (h : ((p : O) ^ 1) ∈ Ideal.span {ϖ ^ 1}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ) →
    Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ)) ≤ Nat.card (IsLocalRing.ResidueField O) := by
  intro hT p _ K hK O _ _ _ _ ϖ hϖ M _ _ e ρ h
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
  intro hc
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.finite_card_torsionLevel_fractionRingQuot hϖ e 1
  haveI : Finite (Lev M (ϖ ^ 1)) := hfin
  haveI : Fact (p ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  obtain ⟨⟨eH⟩, -, -, -, hb⟩ := hT p K hK 1 (Lev M (ϖ ^ 1)) (levRepZ p 1 h ρ) one_pos hc
  set ρ' := levRepZ p 1 h ρ
  set χ := Formalism.GaloisCohomology.cycK p K 1

  let W := ↥(H0 ((twDual χ ρ').comp (MonoidHom.id _)))
  haveI : Finite (TDual (ZMod (p ^ 1)) (Lev M (ϖ ^ 1))) :=
    (finite_card_dual (F := ZMod (p ^ 1)) (V := Lev M (ϖ ^ 1))).1
  haveI : Finite W := Subtype.finite
  have hW : Nat.card W ≤ Nat.card (Lev M (ϖ ^ 1)) :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      (finite_card_dual (F := ZMod (p ^ 1)) (V := Lev M (ϖ ^ 1))).2.le
  obtain ⟨hfd, hcd⟩ := finite_card_dual (F := ZMod (p ^ 1)) (V := W)
  let E := LinearEquiv.congrRight (M := W) eH
  haveI : Finite (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) :=
    Finite.of_equiv _ E.symm.toEquiv
  have h1 : Nat.card (H2 ρ') ≤ Nat.card (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) :=
    Nat.card_le_card_of_injective _ hb.1
  have h2 : Nat.card (W →ₗ[ZMod (p ^ 1)] H2 ((charRep χ).comp (MonoidHom.id _))) = Nat.card W :=
    (Nat.card_congr E.toEquiv).trans hcd
  calc Nat.card (H2 ρ') ≤ Nat.card W := h1.trans h2.le
    _ ≤ Nat.card (Lev M (ϖ ^ 1)) := hW
    _ = Nat.card (IsLocalRing.ResidueField O) := hcard.trans (pow_one _)

end GlobalTheory.ShapeNeg
end
end
