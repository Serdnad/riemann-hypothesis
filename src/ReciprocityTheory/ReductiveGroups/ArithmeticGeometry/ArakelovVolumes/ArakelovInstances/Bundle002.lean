module

public import ReciprocityTheory.AnalyticForms.LeviForms.HomDensA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.DetOfBlockDiag
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.LeviForms.HomDensB
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Polynomial Matrix ReciprocityTheory.AnForm.P

variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

def lin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ[X] := 1 + (X : ℂ[X]) • A.map C

theorem cf_lin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    cf k (lin A) = if k = 0 then 1 else if k = 1 then A else 0 := by
  ext i j
  rcases k with _ | _ | k <;> by_cases h : i = j <;>
    simp [cf, lin, Matrix.one_apply, h, Polynomial.coeff_one, Polynomial.coeff_C]

theorem coeffMatrix_zero_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 0 (lin A) = 1 := by
  simp [cf_lin]
theorem coeffMatrix_one_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 1 (lin A) = A := by
  simp [cf_lin]
theorem coeffMatrix_two_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 2 (lin A) = 0 := by
  simp [cf_lin]

theorem cf_submatrix {α β γ δ : Type*} (k : ℕ) (P : Matrix α β ℂ[X]) (f : γ → α) (g : δ → β) :
    cf k (P.submatrix f g) = (cf k P).submatrix f g := rfl

abbrev Dc : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => (D k : ℂ)

abbrev Ym : Matrix (Fin m) (Fin m) ℂ := Y.submatrix (Fin.castLE hm) (Fin.castLE hm)

abbrev Dm : Matrix (Fin m) (Fin m) ℂ := diagonal fun i => (D (Fin.castLE hm i) : ℂ)

theorem Dc_sub : (Dc D).submatrix (Fin.castLE hm) (Fin.castLE hm) = Dm hm D := by
  ext i j
  by_cases h : i = j <;> simp [Dc, Dm, Matrix.diagonal_apply, h]

def GP (t : ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  (lin ((starRingEnd ℂ t) • Yᴴ) * ((Dc D).map C * lin (t • Y))).submatrix (Fin.castLE hm) (Fin.castLE hm)

def GnP (t : ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  lin (-((starRingEnd ℂ t) • (Ym hm Y)ᴴ)) * (GP hm D Y t * lin (-(t • Ym hm Y)))

theorem coeffMatrix_zero_lineGramPoly (t : ℂ) : cf 0 (GP hm D Y t) = Dm hm D := by
  rw [GP, cf_submatrix, cf_mul_zero, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, one_mul, mul_one, Dc_sub]

theorem coeffMatrix_one_lineGramPoly (t : ℂ) : cf 1 (GP hm D Y t) =
    (starRingEnd ℂ t) • ((Ym hm Y)ᴴ * Dm hm D) + t • (Dm hm D * Ym hm Y) := by
  rw [GP, cf_submatrix, cf_mul_one, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly,
    one_mul, mul_one]
  ext i j
  simp [Dc, Dm, Ym, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  ring

theorem coeffMatrix_two_lineGramPoly (t : ℂ) : cf 2 (GP hm D Y t) =
    ((starRingEnd ℂ t) * t) • (Yᴴ * Dc D * Y).submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  rw [GP, cf_submatrix, cf_mul_two, cf_mapC_mul, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly,
    coeffMatrix_two_linearMatrixPoly, coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, one_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  rw [mul_comm t]
  rfl

theorem coeffMatrix_zero_correctedLineGramPoly (t : ℂ) : cf 0 (GnP hm D Y t) = Dm hm D := by
  rw [GnP, cf_mul_zero, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, one_mul, mul_one]

theorem coeffMatrix_one_correctedLineGramPoly (t : ℂ) : cf 1 (GnP hm D Y t) = 0 := by
  rw [GnP, cf_mul_one, cf_mul_one, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, coeffMatrix_one_lineGramPoly]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.add_mul]
  abel

theorem coeffMatrix_two_correctedLineGramPoly (t : ℂ) : cf 2 (GnP hm D Y t) =
    ((starRingEnd ℂ t) * t) • ((Yᴴ * Dc D * Y).submatrix (Fin.castLE hm) (Fin.castLE hm) -
      (Ym hm Y)ᴴ * Dm hm D * Ym hm Y) - t ^ 2 • (Dm hm D * Ym hm Y * Ym hm Y) -
      (starRingEnd ℂ t) ^ 2 • ((Ym hm Y)ᴴ * (Ym hm Y)ᴴ * Dm hm D) := by
  rw [GnP, cf_mul_two, cf_mul_two, cf_mul_one, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly,
    coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, coeffMatrix_one_lineGramPoly, coeffMatrix_two_lineGramPoly]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, smul_smul]
  module

def Gz (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ((1 + ζ • Y)ᴴ * Dc D * (1 + ζ • Y)).submatrix (Fin.castLE hm) (Fin.castLE hm)

def Gnz (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (1 - ζ • Ym hm Y)ᴴ * (Gz hm D Y ζ * (1 - ζ • Ym hm Y))

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def vecOf (z : V (nd X)) : Ent X → ℂ := fun e => z (Fintype.equivFin (Ent X) e)

def Lin (τ : X.Ψ) : V (nd X) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ where
  toFun z := Matrix.of (embF X (vecOf X z) τ)
  map_add' z w := by
    ext a c
    simp only [Matrix.of_apply, Matrix.add_apply, embF, vecOf]
    split_ifs
    · rfl
    · simp
  map_smul' t z := by
    ext a c
    simp only [Matrix.of_apply, Matrix.smul_apply, embF, vecOf, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rfl
    · simp

theorem nmat_eq (z : V (nd X)) (τ : X.Ψ) : mat (nmat X z) τ = 1 + Lin X τ z := by
  ext a c
  simp only [mat, nmat, Lin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.add_apply,
    Matrix.one_apply, embF, vecOf]
  split_ifs with h1 h2 <;> first
    | (subst h2; exact absurd h1 (lt_irrefl _))
    | simp_all
    | omega

theorem hasFDerivAt_nmat (τ : X.Ψ) (z : V (nd X)) :
    HasFDerivAt (fun z' => mat (nmat X z') τ) (LinearMap.toContinuousLinearMap (Lin X τ)) z := by
  have e : (fun z' => mat (nmat X z') τ) = fun z' => 1 + LinearMap.toContinuousLinearMap (Lin X τ) z' :=
    funext fun z' => by rw [nmat_eq]; rfl
  rw [e]
  exact (LinearMap.toContinuousLinearMap (Lin X τ)).hasFDerivAt.const_add 1

theorem isUnit_nmat (τ : X.Ψ) (z : V (nd X)) : IsUnit (mat (nmat X z) τ) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_lowerTriangular]
  · simp [mat, nmat]
  · intro a c hac
    have h' : a < c := OrderDual.toDual_lt_toDual.mp hac
    simp only [mat, nmat, Matrix.of_apply]
    rw [dite_eq_right (not_lt.mpr h'.le), if_neg h'.ne]

def entryL (a c : Fin r) : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] ℂ where
  toFun M := M a c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lower_deriv (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) ℂ) (U : Set (V (nd X))) (hU : IsOpen U)
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Matrix (Fin r) (Fin r) ℂ)
    (hrel : ∀ z ∈ U, mat (nmat X (Φ z)) τ * bf z = A * mat (nmat X z) τ)
    (hup : ∀ z ∈ U, ∀ a c : Fin r, c < a → bf z a c = 0)
    (z : V (nd X)) (hz : z ∈ U) (Φ' : V (nd X) →L[ℂ] V (nd X)) (hΦ : HasFDerivAt Φ Φ' z)
    (h : V (nd X)) (a c : Fin r) (hca : c < a) :
    (bf z * (Ring.inverse (mat (nmat X z) τ) * Lin X τ h) -
      (Ring.inverse (mat (nmat X (Φ z)) τ) * Lin X τ (Φ' h)) * bf z) a c = 0 := by
  obtain ⟨G, hG⟩ : ∃ G : V (nd X) → Matrix (Fin r) (Fin r) ℂ,
      G = fun w => Ring.inverse (mat (nmat X (Φ w)) τ) * A * mat (nmat X w) τ := ⟨_, rfl⟩
  have hbfG : ∀ w ∈ U, bf w = G w := by
    intro w hw
    rw [hG]
    dsimp only
    rw [mul_assoc, ← hrel w hw, ← mul_assoc,
      Ring.inverse_mul_cancel _ (isUnit_nmat X τ (Φ w)), one_mul]
  have hMd : HasFDerivAt (fun w => mat (nmat X (Φ w)) τ)
      ((LinearMap.toContinuousLinearMap (Lin X τ)).comp Φ') z :=
    (hasFDerivAt_nmat X τ (Φ z)).comp z hΦ
  have hinv : DifferentiableAt ℂ (fun w => Ring.inverse (mat (nmat X (Φ w)) τ)) z := by
    have hi := (differentiableAt_inverse (𝕜 := ℂ) (isUnit_nmat X τ (Φ z))).comp z hMd.differentiableAt
    exact hi
  have hGd : DifferentiableAt ℂ G z := by
    rw [hG]
    exact (hinv.mul (differentiableAt_const A)).mul (hasFDerivAt_nmat X τ z).differentiableAt
  have hGd' : HasFDerivAt G (fderiv ℂ G z) z := hGd.hasFDerivAt
  have hent : (fderiv ℂ G z h) a c = 0 := by
    have hE : HasFDerivAt (fun w => G w a c)
        ((LinearMap.toContinuousLinearMap (entryL a c)).comp (fderiv ℂ G z)) z :=
      (LinearMap.toContinuousLinearMap (entryL a c)).hasFDerivAt.comp z hGd'
    have heq : (fun w => G w a c) =ᶠ[𝓝 z] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => by
        show G w a c = 0
        rw [← hbfG w hw]
        exact hup w hw a c hca
    have h0 : HasFDerivAt (fun w => G w a c) (0 : V (nd X) →L[ℂ] ℂ) z :=
      (hasFDerivAt_const (0 : ℂ) z).congr_of_eventuallyEq heq
    have := congrArg (fun T => T h) (hE.unique h0)
    exact this
  have hLHS := hMd.mul' hGd'
  have hRHS : HasFDerivAt (fun w => A * mat (nmat X w) τ)
      (A • LinearMap.toContinuousLinearMap (Lin X τ)) z := (hasFDerivAt_nmat X τ z).const_mul A
  have heq2 : (fun w => A * mat (nmat X w) τ) =ᶠ[𝓝 z] fun w => mat (nmat X (Φ w)) τ * G w :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => by
      show A * mat (nmat X w) τ = mat (nmat X (Φ w)) τ * G w
      rw [← hbfG w hw]
      exact (hrel w hw).symm
  have hU2 := (hLHS.congr_of_eventuallyEq heq2).unique hRHS
  have I : mat (nmat X (Φ z)) τ * fderiv ℂ G z h + Lin X τ (Φ' h) * G z = A * Lin X τ h := by
    have := congrArg (fun T => T h) hU2
    exact this
  have e1 : Ring.inverse (mat (nmat X (Φ z)) τ) * mat (nmat X (Φ z)) τ = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_nmat X τ (Φ z))
  have e2 : mat (nmat X z) τ * Ring.inverse (mat (nmat X z) τ) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_nmat X τ z)
  have hGh : fderiv ℂ G z h =
      Ring.inverse (mat (nmat X (Φ z)) τ) * (A * Lin X τ h - Lin X τ (Φ' h) * G z) := by
    rw [← I, add_sub_cancel_right, ← mul_assoc, e1, one_mul]
  have hGz : G z * (Ring.inverse (mat (nmat X z) τ) * Lin X τ h) =
      Ring.inverse (mat (nmat X (Φ z)) τ) * A * Lin X τ h := by
    rw [hG]
    simp only
    rw [mul_assoc (Ring.inverse (mat (nmat X (Φ z)) τ) * A), ← mul_assoc (mat (nmat X z) τ), e2, one_mul]
  rw [hbfG z hz, hGz, ← hent, hGh, mul_sub]
  simp only [mul_assoc]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
end
end
