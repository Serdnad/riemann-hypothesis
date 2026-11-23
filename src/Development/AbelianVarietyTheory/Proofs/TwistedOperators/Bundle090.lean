module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CommuteRowOpRightMixedOp
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ColumnDegreeLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle081
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularRowLatticeTriangularBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle082
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle083
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.isOpen_isCompact_twoBlockParahoricSubgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D],
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) ∧ IsCompact (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  first | exact @GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric | exact GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric | (intros; apply GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.mem_integralGL_of_inParahoricDatumSupport_mul_blockDiag : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (z : Matrix (A ⊕ E) (A ⊕ D) k) (x : GL A k) (y : GL D k),
    InSupp z → InSupp (z * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k)) → x ∈ KO k A := by
  first | exact @GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp | exact GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp | (intros; apply GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.parahoricDatum_eigenvector_twoBlockParahoric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ₀ : kˣ →* ℂˣ), IsTame ξ → IsUnram μ₀ →
    ∀ j ∈ parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    om (μ₀ * ξ) j (1 : GL (A ⊕ E) k) (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ) = fun x => (ξ d : ℂ) * datum ξ x := by
  first | exact @GlobalTheory.DatumEigen.om_datum | exact GlobalTheory.DatumEigen.om_datum | (intros; apply GlobalTheory.DatumEigen.om_datum <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ →
  ∀ j ∈ parahoric k A D, (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det ≠ 0 ∧
    ∀ d d' : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      (d' : k) = ((j⁻¹ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det → (ξ d : ℂ) * ξ d' = 1 := by
  first | exact @GlobalTheory.ParahoricLowerBlock.lower_block_tame | exact GlobalTheory.ParahoricLowerBlock.lower_block_tame | (intros; apply GlobalTheory.ParahoricLowerBlock.lower_block_tame <;> assumption)
end

section

open Formalism.REAL Finset Polynomial

namespace GlobalTheory.ScalarNewton

open Matrix

theorem sum_adjugate_eq {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (h : M.det ≠ 0) :
    ∑ a, ∑ b, M.adjugate a b = (M + Matrix.of fun _ _ => (1 : R)).det - M.det := by
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  have hinj : Function.Injective φ := IsFractionRing.injective R K
  apply hinj
  have hdet : φ M.det = (M.map φ).det := RingHom.map_det φ M
  have hd0 : (M.map φ).det ≠ 0 := by
    rw [← hdet]; exact (map_ne_zero_iff φ hinj).2 h
  have hd : IsUnit (M.map φ).det := hd0.isUnit
  have hJ : (M + Matrix.of fun _ _ => (1 : R)).map φ =
      M.map φ + replicateCol Unit (fun _ : ι => (1 : K)) * replicateRow Unit (fun _ : ι => (1 : K)) := by
    ext i j; simp [replicateCol, replicateRow, Matrix.mul_apply]
  have hadj : ∀ a b, φ (M.adjugate a b) = (M.map φ).adjugate a b := by
    intro a b
    have := congrFun (congrFun (RingHom.map_adjugate φ M) a) b
    simpa using this
  have key := det_add_replicateCol_mul_replicateRow (ι := Unit) hd (fun _ => (1 : K)) (fun _ => 1)

  rw [map_sub, RingHom.map_det φ, RingHom.map_det φ, map_sum]

  simp only [map_sum, hadj]
  change _ = ((M + Matrix.of fun _ _ => (1 : R)).map φ).det - (M.map φ).det
  rw [hJ, key, det_unique (n := Unit), Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply, replicateCol_apply,
    Matrix.smul_apply, smul_eq_mul, one_mul, mul_one, Finset.univ_unique, Finset.sum_singleton]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hd0]
  ring

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

variable (m : ℕ) (χ : Fin (m + 1) → ℂ)

noncomputable def amat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)

theorem gelfVal_eq (k : ℕ) : GlobalTheory.Dec.gelfVal χ k = ∑ a, ∑ b, (amat m χ ^ k) a b := rfl

noncomputable def pmat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X] :=
  (X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + (amat m χ - (m : ℂ) • 1).map C

theorem pmat_apply (a b : Fin (m + 1)) : pmat m χ a b =
    if a = b then X + C (χ a - (m : ℂ) / 2) else if a < b then -1 else 0 := by
  by_cases h1 : a = b
  · subst h1
    simp [pmat, amat, Formalism.REAL.Amat]
    rw [show ((m : ℂ[X])) = C (m : ℂ) from (map_natCast C m).symm, ← C_add, ← C_sub, ← C_sub]
    congr 1
    ring
  · by_cases h2 : a < b
    · simp [pmat, amat, Formalism.REAL.Amat, h1, h2, Matrix.one_apply]
    · simp [pmat, amat, Formalism.REAL.Amat, h1, h2, Matrix.one_apply]

theorem pmat_eq : pmat m χ = (X - C (m : ℂ)) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X]) + (amat m χ).map C := by
  refine Matrix.ext fun a b => ?_
  by_cases h1 : a = b
  · subst h1
    simp [pmat]
    ring
  · simp [pmat, h1, Matrix.one_apply]

theorem det_pmat : (pmat m χ).det = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_congr rfl fun s _ => by rw [pmat_apply]; simp
  · intro i j h
    have h' : j < i := h
    rw [pmat_apply, if_neg (ne_of_gt h'), if_neg (not_lt_of_gt h')]

theorem det_pmat_add : (pmat m χ + Matrix.of fun _ _ => (1 : ℂ[X])).det =
    ∏ s, (X + C (χ s - (m : ℂ) / 2 + 1)) := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_congr rfl fun s _ => by rw [Matrix.add_apply, pmat_apply]; simp; ring
  · intro i j h
    have h' : i < j := h
    rw [Matrix.add_apply, pmat_apply, if_neg (ne_of_lt h'), if_pos h']
    simp

theorem det_pmat_ne_zero : (pmat m χ).det ≠ 0 := by
  rw [det_pmat]
  exact Finset.prod_ne_zero_iff.2 fun s _ => X_add_C_ne_zero _

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

theorem sumEnt_smul {n : ℕ} (c : ℂ[X]) (W : Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (c • W) a b = c * ∑ a, ∑ b, W a b := by
  simp [Finset.mul_sum]

theorem sumEnt_sub {n : ℕ} (V W : Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (V - W) a b = ∑ a, ∑ b, V a b - ∑ a, ∑ b, W a b := by
  simp [Finset.sum_sub_distrib]

theorem sumEnt_sum {n : ℕ} (s : Finset ℕ) (W : ℕ → Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (∑ i ∈ s, W i : Matrix (Fin n) (Fin n) ℂ[X]) a b = ∑ i ∈ s, ∑ a, ∑ b, W i a b := by
  simp only [Matrix.sum_apply]
  calc _ = ∑ a, ∑ i ∈ s, ∑ b, W i a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem poly_identity (m N : ℕ) (χ : Fin (m + 1) → ℂ) :
    (X - C (m : ℂ)) ^ (N + 1) * ((pmat m χ + Matrix.of fun _ _ => (1 : ℂ[X])).det - (pmat m χ).det) -
      (pmat m χ).det * ∑ k ∈ range (N + 1), (-1) ^ k * (X - C (m : ℂ)) ^ (N - k) * C (GlobalTheory.Dec.gelfVal χ k) =
    (-1) ^ (N + 1) * ∑ a, ∑ b, ((pmat m χ).adjugate * ((amat m χ).map C) ^ (N + 1)) a b := by
  set x : ℂ[X] := X - C (m : ℂ)
  set Bm : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X] := (amat m χ).map C
  set Mx := pmat m χ
  have hnp : ∀ i : ℕ, (-Bm) ^ i = ((-1 : ℂ[X]) ^ i) • Bm ^ i := by
    intro i; rw [← neg_one_smul ℂ[X] Bm, _root_.smul_pow]
  have hxp : ∀ i : ℕ, (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) ^ i = x ^ i • 1 := by
    intro i; rw [_root_.smul_pow, one_pow]
  have hBp : ∀ i : ℕ, ∑ a, ∑ b, (Bm ^ i) a b = C (GlobalTheory.Dec.gelfVal χ i) := by
    intro i

    rw [gelfVal_eq, map_sum]

    simp only [map_sum]
    have : Bm ^ i = (amat m χ ^ i).map C := by
      rw [Matrix.map_pow]
    rw [this]
    simp
  have hcomm : Commute (-Bm) (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) :=
    (Commute.one_right _).smul_right x
  have hgeom := hcomm.mul_geom_sum₂ (N + 1)
  set P := ∑ i ∈ range (N + 1), (-Bm) ^ i * (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) ^ (N + 1 - 1 - i)
  have hMP : Mx * P = x ^ (N + 1) • 1 - (-1 : ℂ[X]) ^ (N + 1) • Bm ^ (N + 1) := by
    have : Mx = -(-Bm - x • 1) := by rw [show Mx = pmat m χ from rfl, pmat_eq]; abel
    rw [this, neg_mul, hgeom, hnp, hxp]
    abel
  have hSP : ∑ a, ∑ b, P a b = ∑ k ∈ range (N + 1), (-1) ^ k * x ^ (N - k) * C (GlobalTheory.Dec.gelfVal χ k) := by
    rw [sumEnt_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hnp, hxp, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, sumEnt_smul, hBp]
    simp only [Nat.add_sub_cancel]
  have hadj : Mx.adjugate * Mx = Mx.det • 1 := Matrix.adjugate_mul Mx
  have hdP : Mx.det • P = Mx.adjugate * (Mx * P) := by
    rw [← Matrix.mul_assoc, hadj, Matrix.smul_mul, Matrix.one_mul]
  have hS := congrArg (fun W => ∑ a, ∑ b, W a b) hdP
  rw [sumEnt_smul, hSP, hMP, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, sumEnt_sub,
    sumEnt_smul, sumEnt_smul, sum_adjugate_eq Mx (det_pmat_ne_zero m χ)] at hS
  rw [hS]
  ring

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

theorem natDegree_adjugate_pmat_le (m : ℕ) (χ : Fin (m + 1) → ℂ) (i j : Fin (m + 1)) :
    ((pmat m χ).adjugate i j).natDegree ≤ m := by
  rw [adjugate_fin_succ_eq_det_submatrix]
  have h1 : ((-1 : ℂ[X]) ^ ((j : ℕ) + i)) = C ((-1) ^ ((j : ℕ) + i)) := by simp
  rw [h1]
  refine (natDegree_C_mul_le _ _).trans ?_
  have e : (pmat m χ).submatrix j.succAbove i.succAbove =
      (X : ℂ[X]) • ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix j.succAbove i.succAbove).map C +
      ((amat m χ - (m : ℂ) • 1).submatrix j.succAbove i.succAbove).map C := rfl
  rw [e]
  simpa using natDegree_det_X_add_C_le
    ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix j.succAbove i.succAbove)
    ((amat m χ - (m : ℂ) • 1).submatrix j.succAbove i.succAbove)

theorem scalar_newton : ∀ (m N : ℕ) (χ : Fin (m + 1) → ℂ), ∃ r : ℂ[X], r.natDegree ≤ m ∧ ∀ u : ℂ,
    (u - m) ^ (N + 1) * (∏ s, (u + 1 - (m : ℂ) / 2 + χ s) - ∏ s, (u - (m : ℂ) / 2 + χ s)) -
      (∏ s, (u - (m : ℂ) / 2 + χ s)) * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * GlobalTheory.Dec.gelfVal χ k =
      r.eval u := by
  intro m N χ
  refine ⟨(-1) ^ (N + 1) * ∑ a, ∑ b, ((pmat m χ).adjugate * ((amat m χ).map C) ^ (N + 1)) a b, ?_, ?_⟩
  · have hc : ((-1 : ℂ[X]) ^ (N + 1)) = C ((-1) ^ (N + 1)) := by simp
    rw [hc]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_sum_le_of_forall_le _ _ fun a _ => natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
    rw [Matrix.mul_apply]
    refine natDegree_sum_le_of_forall_le _ _ fun c _ => ?_
    rw [← Matrix.map_pow, Matrix.map_apply]
    exact (natDegree_mul_C_le _ _).trans (natDegree_adjugate_pmat_le m χ a c)
  · intro u
    rw [← poly_identity, det_pmat, det_pmat_add]
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_prod, eval_add, Polynomial.eval_finsetSum, eval_neg,
      eval_one]
    have e1 : ∏ s, (u + (χ s - (m : ℂ) / 2 + 1)) = ∏ s, (u + 1 - (m : ℂ) / 2 + χ s) :=
      Finset.prod_congr rfl fun _ _ => by ring
    have e0 : ∏ s, (u + (χ s - (m : ℂ) / 2)) = ∏ s, (u - (m : ℂ) / 2 + χ s) :=
      Finset.prod_congr rfl fun _ _ => by ring
    rw [e1, e0]

end GlobalTheory.ScalarNewton
end

section

noncomputable section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.BlockWeights

def extZero {p : ℕ} (a : Fin p → ℕ) (i : ℕ) : ℕ := if h : i < p then a ⟨i, h⟩ else 0

theorem sum_range_extZero {p : ℕ} (a : Fin p → ℕ) (i : ℕ) :
    ∑ j ∈ Finset.range i, extZero a j =
      ∑ b ∈ Finset.univ.filter (fun b : Fin p => (b : ℕ) < i), a b := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : n < p
    · have hset : Finset.univ.filter (fun b : Fin p => (b : ℕ) < n + 1) =
          insert ⟨n, h⟩ (Finset.univ.filter (fun b : Fin p => (b : ℕ) < n)) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hset, Finset.sum_insert (by simp), add_comm]
      simp only [extZero, dif_pos h]
    · have hset : Finset.univ.filter (fun b : Fin p => (b : ℕ) < n + 1) =
          Finset.univ.filter (fun b : Fin p => (b : ℕ) < n) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hset]
      simp only [extZero, dif_neg h, add_zero]

theorem partial_sum_le {σ : Type} [DecidableEq σ] {p r : ℕ} (z : Fin p × Fin r → σ)
    (hz : Function.Injective z) (P : MvPolynomial σ ℂ) (a : Fin p → ℕ) (a' : Fin r → ℕ)
    (hP : P ≠ 0) (hrow : ∀ i j : Fin p, i < j → rowOp ℂ z i j P = 0)
    (ha : ∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) (ha' : ∀ i, colOp ℂ z i i P = (a' i : ℂ) • P)
    (i : ℕ) :
    ∑ j ∈ Finset.range i, extZero a' j ≤ ∑ j ∈ Finset.range i, extZero a j := by

  have hinv : ∀ b c : Fin p, b < c → ∀ t : ℂ,
      bind₁ (fun s => X s + ∑ k, if s = z (c, k) then C t * X (z (b, k)) else 0) P = P := by
    intro b c hbc t
    have hw : Function.Injective (fun k : Fin r => z (c, k)) :=
      fun k l h => congrArg Prod.snd (hz h)
    have huw : ∀ k l : Fin r, z (b, k) ≠ z (c, l) := by
      intro k l h
      exact (ne_of_lt hbc) (congrArg Prod.fst (hz h))
    have hT := GlobalTheory.rowAdd_invariant_iff (K := ℂ) (fun k : Fin r => z (b, k))
      (fun k : Fin r => z (c, k)) hw huw P
    have h0 : ∑ k, X (z (b, k)) * pderiv (z (c, k)) P = 0 := by
      rw [← GlobalTheory.Capelli.rowOp_apply]
      exact hrow b c hbc
    have h23 := hT.out 2 3
    exact h23.mpr h0 t

  have hrowdeg : ∀ b, ∀ m ∈ P.support, ∑ k, m (z (b, k)) = a b := by
    intro b m hm
    exact_mod_cast (GlobalTheory.JointHarm.rowOp_eq_smul_iff z b P _).mp (ha b) m hm
  have hcoldeg : ∀ k, ∀ m ∈ P.support, ∑ b, m (z (b, k)) = a' k := by
    intro k m hm
    exact_mod_cast (GlobalTheory.JointHarm.colOp_eq_smul_iff z k P _).mp (ha' k) m hm
  obtain ⟨m, hm⟩ : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hP
  have key := GlobalTheory.column_degree_le z hz P a hrowdeg hinv
    (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)) m hm
  have hcard : (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card ≤ i := by
    calc (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card
        = ((Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).map Fin.valEmbedding).card :=
          (Finset.card_map _).symm
      _ ≤ (Finset.range i).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.valEmbedding_apply] at hx
          obtain ⟨k, hk, hkx⟩ := hx
          rw [Finset.mem_range, ← hkx]
          exact hk
      _ = i := Finset.card_range i
  rw [sum_range_extZero, sum_range_extZero]
  calc ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), a' k
      = ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), ∑ b, m (z (b, k)) :=
        Finset.sum_congr rfl (fun k _ => (hcoldeg k m hm).symm)
    _ = ∑ b, ∑ k ∈ Finset.univ.filter (fun k : Fin r => (k : ℕ) < i), m (z (b, k)) :=
        Finset.sum_comm
    _ ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin p =>
          (b : ℕ) < (Finset.univ.filter (fun k : Fin r => (k : ℕ) < i)).card), a b := key
    _ ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin p => (b : ℕ) < i), a b := by
        apply Finset.sum_le_sum_of_subset
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        omega

theorem row_col_weights_agree : ∀ (σ : Type) [DecidableEq σ] (p r : ℕ) (z : Fin p × Fin r → σ), Function.Injective z → ∀ (P : MvPolynomial σ ℂ) (a : Fin p → ℕ) (a' : Fin r → ℕ), P ≠ 0 → Antitone a → (∀ i j : Fin p, i < j → rowOp ℂ z i j P = 0) → (∀ i j : Fin r, i < j → colOp ℂ z i j P = 0) → (∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) → (∀ i, colOp ℂ z i i P = (a' i : ℂ) • P) → ∃ α : ℕ → ℕ, Antitone α ∧ (∀ i, min p r ≤ i → α i = 0) ∧ (∀ i : Fin p, a i = α i) ∧ ∀ i : Fin r, a' i = α i := by
  intro σ _ p r z hz P a a' hP hanti hrow hcol ha ha'
  have h1 : ∀ i, ∑ j ∈ Finset.range i, extZero a' j ≤ ∑ j ∈ Finset.range i, extZero a j :=
    partial_sum_le z hz P a a' hP hrow ha ha'

  have h2 : ∀ i, ∑ j ∈ Finset.range i, extZero a j ≤ ∑ j ∈ Finset.range i, extZero a' j := by
    have hz' : Function.Injective (fun w : Fin r × Fin p => z w.swap) :=
      hz.comp Prod.swap_injective
    have e : ∀ k l : Fin r,
        rowOp ℂ (fun w : Fin r × Fin p => z w.swap) k l = colOp ℂ z k l :=
      fun k l => GlobalTheory.Capelli.rowOp_eq_colOp _ k l
    have e' : ∀ b c : Fin p,
        colOp ℂ (fun w : Fin r × Fin p => z w.swap) b c = rowOp ℂ z b c :=
      fun b c => (GlobalTheory.Capelli.rowOp_eq_colOp z b c).symm
    exact partial_sum_le (fun w : Fin r × Fin p => z w.swap) hz' P a' a hP
      (fun k l hkl => by rw [e]; exact hcol k l hkl) (fun k => by rw [e]; exact ha' k)
      (fun b => by rw [e']; exact ha b)
  have hsum : ∀ i, ∑ j ∈ Finset.range i, extZero a j = ∑ j ∈ Finset.range i, extZero a' j :=
    fun i => le_antisymm (h2 i) (h1 i)

  have heq : ∀ j, extZero a j = extZero a' j := by
    intro j
    have hj := hsum (j + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hsum j] at hj
    omega
  refine ⟨extZero a, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    unfold extZero
    by_cases hj : j < p
    · rw [dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]
      exact hanti (Fin.mk_le_mk.mpr hij)
    · rw [dif_neg hj]
      exact Nat.zero_le _
  · intro i hi
    by_cases hp : p ≤ i
    · simp [extZero, show ¬ i < p by omega]
    · rw [heq i]
      simp [extZero, show ¬ i < r by omega]
  · intro i
    simp [extZero]
  · intro i
    rw [heq]
    simp [extZero]

end GlobalTheory.JointHarm.BlockWeights
end
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.blockTriangular_row_lattice_triangular_basis : SpanEq := by
  first | exact @GlobalTheory.InertZeta.RowSpan.spanEq_holds | exact GlobalTheory.InertZeta.RowSpan.spanEq_holds | (intros; apply GlobalTheory.InertZeta.RowSpan.spanEq_holds <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.elementaryDivisors_exist_discretelyValued : Smith := by
  first | exact @GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued | exact GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued | (intros; apply GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.biInvariant_replace_same_double_coset_sums : DosetSwap := by
  first | exact @GlobalTheory.InertZeta.dosetSwap | exact GlobalTheory.InertZeta.dosetSwap | (intros; apply GlobalTheory.InertZeta.dosetSwap <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.unitary_heisenberg_radical_coordinates : Heis := by
  first | exact @GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ | exact GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ | (intros; apply GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.length_count_generating_series_formula : GenFun := by
  first | exact @GlobalTheory.InertZeta.genFun_holds | exact GlobalTheory.InertZeta.genFun_holds | (intros; apply GlobalTheory.InertZeta.genFun_holds <;> assumption)
end
