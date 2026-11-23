module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.BfENondeg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.MapCAMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

section

set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

def Gm (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) :
    Matrix (Fin m × Fin n × Fin 2) (Fin m × Fin n × Fin 2) F :=
  LinearMap.BilinForm.toMatrix (bs.matrix (Fin m) (Fin n)) (BfE σ J)

theorem Gm_det [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E)
    (hJ : J.det ≠ 0) (bs : Module.Basis (Fin 2) F E) : (Gm (n := n) σ J bs).det ≠ 0 :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).1 (BfE_nondeg σ hσ J hJ)

theorem Bf_Ek_Ek [FiniteDimensional F E] (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E)
    (k k' : Fin m × Fin n × Fin 2) : Bf σ J (Ek bs k) (Ek bs k') = algebraMap F (AF F) (Gm σ J bs k k') := by
  obtain ⟨i, j, l⟩ := k
  obtain ⟨i', j', l'⟩ := k'
  have hE : ∀ (a : Fin m) (b : Fin n) (c : Fin 2), Ek bs (a, b, c) = incM F (Matrix.single a b (bs c)) := by
    intro a b c
    ext x y
    by_cases hx : a = x <;> by_cases hy : b = y <;> simp [Ek, incM, Matrix.single_apply, inclR, hx, hy]
  have hc : ∀ M : Matrix (Fin m) (Fin n) E, (incM F M).map (cA σ) = incM F (M.map σ) := by
    intro M
    ext x y
    simp [incM, cA, inclR]
  have htr : ∀ M : Matrix (Fin m) (Fin n) E, (incM F M)ᵀ = incM F Mᵀ := by
    intro M
    ext x y
    rfl
  have ht : ∀ M : Matrix (Fin n) (Fin n) E, (incM F M).trace = inclR (F := F) (E := E) (AF F) M.trace := by
    intro M
    rw [incM, AddMonoidHom.map_trace]
  rw [Gm, LinearMap.BilinForm.toMatrix_apply, Module.Basis.matrix_apply, Module.Basis.matrix_apply, Bf, hE, hE, hc,
    htr, ← incM_mul, ← incM_mul, ht, trace_inclR']
  rfl

def bM (bs : Module.Basis (Fin 2) F E) : Module.Basis (Fin m × Fin n × Fin 2) (AF F) (Mx F E m n) :=
  (Algebra.TensorProduct.basis (AF F) bs).matrix (Fin m) (Fin n)

theorem bM_repr (bs : Module.Basis (Fin 2) F E) (X : Mx F E m n) (k : Fin m × Fin n × Fin 2) :
    (bM bs).repr X k = crdB bs X k := by
  obtain ⟨i, j, l⟩ := k
  simp [bM, Module.Basis.matrix, crdB, Pi.basis_repr]

theorem incM_one {ι : Type} [Fintype ι] [DecidableEq ι] : incM F (1 : Matrix ι ι E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

def eQ (b : GL (Fin n ⊕ Fin n) E) : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E) ≃ₗ[AF F] Mx F E m n × Mx F E m n :=
  LinearEquiv.ofLinear
    { toFun := fun w => ((w * (incM F (b⁻¹).1)ᵀ).toCols₁, (w * (incM F (b⁻¹).1)ᵀ).toCols₂)
      map_add' := fun w w' => by rw [Matrix.add_mul]; rfl
      map_smul' := fun c w => by rw [Matrix.smul_mul]; rfl }
    { toFun := fun p => p.1 * (incM F b.1.toCols₁)ᵀ + p.2 * (incM F b.1.toCols₂)ᵀ
      map_add' := fun p p' => by simp [Matrix.add_mul]; abel
      map_smul' := fun c p => by simp [Matrix.smul_mul, smul_add] }
    (by
      refine LinearMap.ext fun p => ?_
      obtain ⟨Z, X⟩ := p
      have h1 : (incM F b.1)ᵀ * (incM F (b⁻¹).1)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, ← incM_mul, Units.inv_mul, incM_one, Matrix.transpose_one]
      show (((Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) * (incM F (b⁻¹).1)ᵀ).toCols₁,
        ((Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) * (incM F (b⁻¹).1)ᵀ).toCols₂) = (Z, X)
      rw [show Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ = Matrix.fromCols Z X * (incM F b.1)ᵀ by
        rw [incM_b, Matrix.fromCols_mul_fromRows], Matrix.mul_assoc, h1, Matrix.mul_one]
      simp)
    (by
      refine LinearMap.ext fun w => ?_
      have h1 : (incM F (b⁻¹).1)ᵀ * (incM F b.1)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, ← incM_mul, Units.mul_inv, incM_one, Matrix.transpose_one]
      show (w * (incM F (b⁻¹).1)ᵀ).toCols₁ * (incM F b.1.toCols₁)ᵀ + (w * (incM F (b⁻¹).1)ᵀ).toCols₂ * (incM F b.1.toCols₂)ᵀ = w
      rw [← Matrix.fromCols_mul_fromRows, ← incM_b, Matrix.fromCols_toCols, Matrix.mul_assoc, h1, Matrix.mul_one])

theorem eQ_symm_apply (b : GL (Fin n ⊕ Fin n) E) (Z X : Mx F E m n) :
    (eQ b).symm (Z, X) = Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ := rfl

theorem eQ_frame (b : GL (Fin n ⊕ Fin n) E) (Z X : Mx F E m n) :
    eQ b (Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) = (Z, X) := by
  rw [← eQ_symm_apply, LinearEquiv.apply_symm_apply]

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end

section

set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

theorem trace_int_mul (u : ℤ) (t : AE F E) :
    Algebra.trace (AF F) (AE F E) ((u : AE F E) * t) = (u : AF F) * Algebra.trace (AF F) (AE F E) t := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem trace_map_cA {σ : E →ₐ[F] E} {ι : Type} [Fintype ι] (M : Matrix ι ι (AE F E)) :
    (M.map (cA σ)).trace = cA σ M.trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, map_sum]

theorem Bf_symm {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E) (u : ℤ)
    (hJ : ∀ i j, σ (J j i) = (u : E) * J i j) (X Z : Mx F E m n) :
    Bf σ J X Z = (u : AF F) * Bf σ J Z X := by
  have hJc : (incM F J).map (cA σ) = ((u : ℤ) : AE F E) • (incM F J)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    change cA σ (inclR (F := F) (AF F) (J i j)) = _ * inclR (F := F) (AF F) (J j i)
    rw [show cA σ (inclR (F := F) (AF F) (J i j)) = inclR (F := F) (AF F) (σ (J i j)) from rfl, hJ j i, map_mul, map_intCast]
  have hcc : (Z.map (cA σ)).map (cA σ) = Z := by ext i j; exact cA_cA hσ _
  unfold Bf
  rw [← trace_cA hσ, ← trace_map_cA, map_cA_mul, map_cA_mul, Matrix.transpose_map, hJc, hcc,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_int_mul]
  congr 2
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem mapS_mul {σ : E →ₐ[F] E} {a b c : Type} [Fintype b] (x : Matrix a b E) (y : Matrix b c E) :
    (x * y).map σ = x.map σ * y.map σ := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem congr_symm {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) {ι : Type} [Fintype ι] (D b : Matrix ι ι E) (u : ℤ)
    (hD : Dᵀ.map σ = (u : E) • D) : ((bᵀ * D * b.map σ).map σ)ᵀ = (u : E) • (bᵀ * D * b.map σ) := by
  have hbb : (b.map σ).map σ = b := by ext i j; simp [hσ]
  rw [mapS_mul, mapS_mul, hbb, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.transpose_map,
    ← Matrix.transpose_map, Matrix.transpose_transpose, hD, Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

theorem eps_eq {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (YJ : Matrix (Fin n) (Fin n) E) (u : ℤ)
    (hY : ∀ i j, σ (YJ j i) = (u : E) * YJ i j) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (hb : b.1ᵀ * dbl YJ * b.1.map σ = jeps n ε) (hn : 1 ≤ n) : (ε : ℤ) = u := by
  have hD : (dbl YJ)ᵀ.map σ = (u : E) • dbl YJ := by
    ext (i | i) (j | j) <;> simp [dbl, hY]
  have h := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => M (Sum.inl ⟨0, hn⟩) (Sum.inr ⟨0, hn⟩))
    (congr_symm hσ (dbl YJ) b.1 u hD)
  simp only [hb] at h
  simp [jeps] at h
  exact_mod_cast h

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end
