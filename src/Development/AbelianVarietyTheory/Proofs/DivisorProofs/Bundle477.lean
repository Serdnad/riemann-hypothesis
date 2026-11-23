module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle427
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle438
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle428
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

noncomputable section
namespace GlobalTheory.TorusFrame

theorem sum_angles {r : ℕ} (φ : Fin (r - 1) → ℝ) : ∑ a : Fin r, angles φ a = 0 := by
  cases r with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, angles φ (Fin.castSucc i) = φ ⟨i, by simpa using i.isLt⟩ := by
      intro i; unfold angles; rw [dite_eq_left (by simpa using i.isLt)]; rfl
    have h2 : angles φ (Fin.last n) = -∑ k, φ k := by
      unfold angles; rw [dite_eq_right (by simp)]
    rw [h2, Finset.sum_congr rfl (fun i _ => h1 i)]
    simp

theorem hermC_eq_dot {r : ℕ} {E : Type} [Field E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ fun b => (starRingEnd ℂ) (w b)) := by
  simp only [hermC, dotProduct, mulVec, map_apply, Finset.mul_sum, mul_assoc]

theorem conj_mulVec {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    (fun b => (starRingEnd ℂ) ((M *ᵥ w) b)) = M.map (starRingEnd ℂ) *ᵥ fun b => (starRingEnd ℂ) (w b) := by
  ext b; simp [mulVec, dotProduct, map_sum]

theorem hermC_mulVec {r : ℕ} {E : Type} [Field E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (u w : Fin r → ℂ) :
    hermC τ G (M *ᵥ u) (M *ᵥ w) = u ⬝ᵥ ((Mᵀ * G.map τ * M.map (starRingEnd ℂ)) *ᵥ fun b => (starRingEnd ℂ) (w b)) := by
  rw [hermC_eq_dot, conj_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem det_phase {r : ℕ} (φ : Fin (r - 1) → ℝ) :
    (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ)))).det = 1 := by
  rw [det_diagonal, ← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum, sum_angles]
  simp

theorem phase_gram {r : ℕ} (φ : Fin (r - 1) → ℝ) (s : Fin r → ℂ) :
    (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ))))ᵀ * diagonal s *
      (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ)))).map (starRingEnd ℂ) = diagonal s := by
  rw [diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext a
  rw [← Complex.exp_conj, mul_comm (Complex.exp _) (s a), mul_assoc, ← Complex.exp_add]
  simp [Complex.conj_ofReal]

theorem torusGL_mem_realSU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ), torusGL hx θ ∈ realSU X.Ψ X.Gm := by
  intro E _ _ _ r X x hx θ
  intro τ
  have hu := isUnit_det_of_isOrth hx τ
  rw [torusGL_val]
  refine ⟨?_, fun u w => ?_⟩
  · rw [det_mul, det_mul, det_phase, mul_one, det_nonsing_inv, Ring.mul_inverse_cancel _ hu]
  · rw [hermC_mulVec, hermC_eq_dot]
    congr 2
    have hG := hx τ
    rw [gram_eq] at hG
    have h1 : (mat x τ)⁻¹ᵀ * (mat x τ)ᵀ = 1 := by
      rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
    have h2 : (mat x τ).map (starRingEnd ℂ) * ((mat x τ)⁻¹).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    have hGτ : X.Gm.map τ.1 = (mat x τ)⁻¹ᵀ * ((mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ)) *
        ((mat x τ)⁻¹).map (starRingEnd ℂ) := by
      rw [Matrix.mul_assoc _ _ ((mat x τ)⁻¹.map _), Matrix.mul_assoc _ ((mat x τ).map _), h2, Matrix.mul_one,
        ← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [hG] at hGτ
    simp only [transpose_mul, Matrix.map_mul]
    rw [hGτ]
    have h1' : (mat x τ)ᵀ * (mat x τ)⁻¹ᵀ = 1 := by
      rw [← transpose_mul, nonsing_inv_mul _ hu, transpose_one]
    have h2' : ((mat x τ)⁻¹).map (starRingEnd ℂ) * (mat x τ).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    have key := fun (Q : Matrix (Fin r) (Fin r) ℂ) =>
      (show (diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ)))ᵀ *
          ((diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
          ((diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))).map (starRingEnd ℂ) * Q)) =
          (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * Q by
        simp only [← Matrix.mul_assoc, phase_gram])
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (mat x τ)ᵀ, h1', Matrix.one_mul, ← Matrix.mul_assoc ((mat x τ)⁻¹.map _), h2',
      Matrix.one_mul, key]

end GlobalTheory.TorusFrame
end
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusFrame

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem torusDer_sum_angles (φ : Fin (r - 1) → ℝ) : ∑ a : Fin r, angles φ a = 0 := by
  cases r with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, angles φ i.castSucc = φ ⟨i, by simp⟩ := by
      intro i; unfold angles; rw [dite_eq_left (by simp)]; rfl
    have h2 : angles φ (Fin.last n) = -∑ k, φ k := by
      unfold angles; rw [dite_eq_right (by simp)]
    rw [h2, Finset.sum_congr rfl fun i _ => h1 i]
    rw [add_neg_eq_zero]
    exact Fintype.sum_equiv (finCongr (by simp)) _ _ (fun i => rfl)

theorem torusDer_hermC_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ fun b => conj (w b)) := by
  simp [hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem torusDer_conj_mulVec (Y : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    (fun b => conj ((Y *ᵥ w) b)) = Y.map (starRingEnd ℂ) *ᵥ fun b => conj (w b) := by
  ext b; simp [mulVec, dotProduct, map_sum]

theorem torusDer_skew_of_mat (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Y : Matrix (Fin r) (Fin r) ℂ)
    (hK : Yᵀ * G.map τ + G.map τ * Y.map (starRingEnd ℂ) = 0) (u w : Fin r → ℂ) :
    hermC τ G (Y *ᵥ u) w + hermC τ G u (Y *ᵥ w) = 0 := by
  rw [torusDer_hermC_dot, torusDer_hermC_dot, torusDer_conj_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, ← dotProduct_add, ← add_mulVec, hK, zero_mulVec, dotProduct_zero]

end GlobalTheory.TorusFrame

namespace GlobalTheory.TorusFrame

open Complex
open scoped ComplexConjugate

theorem skewHermitian_of_diagonal_imaginary_frame {r : ℕ} (G M Y : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit M.det) (d s : Fin r → ℂ)
    (hd : ∀ a, conj (d a) = -d a) (hJ : Mᵀ * G * M.map (starRingEnd ℂ) = diagonal s)
    (hYM : Y * M = M * diagonal d) :
    Yᵀ * G + G * Y.map (starRingEnd ℂ) = 0 := by
  have e1 : Mᵀ * (Yᵀ * G) * M.map (starRingEnd ℂ) = diagonal d * diagonal s := by
    calc Mᵀ * (Yᵀ * G) * M.map (starRingEnd ℂ) = (Y * M)ᵀ * G * M.map (starRingEnd ℂ) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = diagonal d * diagonal s := by
          rw [hYM, transpose_mul, diagonal_transpose, ← hJ]; simp only [Matrix.mul_assoc]
  have e2 : Mᵀ * (G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) =
      diagonal s * (diagonal d).map (starRingEnd ℂ) := by
    calc Mᵀ * (G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) = Mᵀ * G * (Y * M).map (starRingEnd ℂ) := by
          rw [Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = diagonal s * (diagonal d).map (starRingEnd ℂ) := by
          rw [hYM, Matrix.map_mul, ← hJ]; simp only [Matrix.mul_assoc]
  have h2 : Mᵀ * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) = 0 := by
    rw [Matrix.mul_add, Matrix.add_mul, e1, e2]
    ext a b
    by_cases h : a = b
    · subst h; simp [diagonal_apply, hd]; ring
    · simp [diagonal_apply, h]
  have hL : (M⁻¹)ᵀ * Mᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
  have hR : M.map (starRingEnd ℂ) * (M⁻¹).map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  calc Yᵀ * G + G * Y.map (starRingEnd ℂ)
      = ((M⁻¹)ᵀ * Mᵀ) * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) *
          (M.map (starRingEnd ℂ) * (M⁻¹).map (starRingEnd ℂ)) := by rw [hL, hR, Matrix.one_mul, Matrix.mul_one]
    _ = (M⁻¹)ᵀ * (Mᵀ * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ)) *
          (M⁻¹).map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h2, Matrix.mul_zero, Matrix.zero_mul]

theorem torusDer_skew_diag {r : ℕ} (G M : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit M.det) (d s : Fin r → ℂ)
    (hd : ∀ a, conj (d a) = -d a) (hJ : Mᵀ * G * M.map (starRingEnd ℂ) = diagonal s) :
    (M * diagonal d * M⁻¹)ᵀ * G + G * (M * diagonal d * M⁻¹).map (starRingEnd ℂ) = 0 :=
  skewHermitian_of_diagonal_imaginary_frame G M _ hu d s hd hJ (by rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one])

theorem torusDer_mem_realLie_and_inFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r), IsOrth X x → ∀ θ : X.Ψ → Fin (r - 1) → ℝ, torusDer x θ ∈ realLie X.Ψ X.Gm ∧
      ∀ τ a b, inFrame x (torusDer x θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0 := by
  intro E _ _ _ r X x hx θ
  have key : ∀ τ : X.Ψ, Matrix.of (torusDer x θ τ) =
      mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹ := fun τ => rfl
  refine ⟨?_, fun τ a b => ?_⟩
  · intro τ
    have hu := isUnit_det_of_isOrth hx τ
    refine ⟨?_, fun u w => ?_⟩
    · rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul, trace_diagonal,
        ← Finset.mul_sum, ← ofReal_sum, torusDer_sum_angles, ofReal_zero, mul_zero]
    · rw [key]
      refine torusDer_skew_of_mat τ.1 X.Gm _ ?_ u w
      refine torusDer_skew_diag _ _ hu _ (fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (fun a => ?_) ?_
      · simp
      · rw [← gram_eq]; exact hx τ
  · have hu := isUnit_det_of_isOrth hx τ
    unfold inFrame
    rw [key, show (mat x τ)⁻¹ * (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) * mat x τ =
        ((mat x τ)⁻¹ * mat x τ) * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * ((mat x τ)⁻¹ * mat x τ) by
        simp only [Matrix.mul_assoc], nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one, diagonal_apply]

end GlobalTheory.TorusFrame
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

noncomputable section

namespace GlobalTheory.WhitBump.Shear

theorem det_eq_one_of_isNilpotent_sub_one {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : V →ₗ[ℝ] V) (hf : IsNilpotent (f - 1)) : LinearMap.det f = 1 := by
  let b := Module.finBasis ℝ V
  rw [← LinearMap.det_toMatrix b]
  set B := LinearMap.toMatrix b b f with hB
  have hBB : LinearMap.toMatrixAlgEquiv b f = B := by
    ext i j; simp [hB, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have h3 : IsNilpotent (B - 1) := by
    have : B - 1 = LinearMap.toMatrixAlgEquiv b (f - 1) := by
      rw [map_sub, map_one, hBB]
    rw [this]; exact hf.map _
  have h4 : IsNilpotent (1 - B) := by rw [← neg_sub]; exact h3.neg
  have h5 := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h4).map (Polynomial.evalRingHom (1 : ℝ))
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_sub, Matrix.eval_charpoly, Polynomial.eval_pow, Polynomial.eval_X,
    one_pow, map_one, sub_sub_cancel] at h5
  exact sub_eq_zero.1 h5.eq_zero

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def above (M : Matrix (Fin n) (Fin n) (Cinf E)) : Vp E n := fun p => M p.1.1 p.1.2

def sU (t : Vp E n) : Matrix (Fin n) (Fin n) (Cinf E) :=
  Matrix.of fun i j => if h : i < j then t ⟨(i, j), h⟩ else 0

theorem nu_eq (t : Vp E n) : nu t = 1 + sU t := by
  ext i j
  simp only [nu, sU, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  by_cases h : i < j
  · simp [h, ne_of_lt h]
  · by_cases h' : i = j
    · subst h'; simp
    · simp [h, h']

theorem nu_above {M : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → M i j = 0) (hd : ∀ i, M i i = 1) :
    nu (above M) = M := by
  ext i j
  simp only [nu, above, Matrix.of_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp [h]
  · subst h; simp [hd]
  · simp [not_lt_of_gt h, ne_of_gt h, hl i j h]

def lin (u : Matrix (Fin n) (Fin n) (Cinf E)) : Vp E n →ₗ[ℝ] Vp E n where
  toFun t := above (sU t * u)
  map_add' a b := by
    have : sU (a + b) = sU a + sU b := by
      ext i j; simp only [sU, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
    rw [this, Matrix.add_mul]; rfl
  map_smul' r a := by
    have : sU (r • a) = r • sU a := by
      ext i j; simp only [sU, Matrix.of_apply, Matrix.smul_apply]; split_ifs <;> simp
    rw [this, Matrix.smul_mul]; rfl

theorem lin_apply (u : Matrix (Fin n) (Fin n) (Cinf E)) (t : Vp E n) : lin u t = above (sU t * u) := rfl

theorem sub_one_vanish {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0) (hd : ∀ i, u i i = 1)
    (c : ℕ) (t : Vp E n) (ht : ∀ p : Idx n, p.1.2.val < c → t p = 0) :
    ∀ p : Idx n, p.1.2.val < c + 1 → ((lin u - 1) t) p = 0 := by
  intro p hp
  obtain ⟨⟨i, j⟩, hij⟩ := p
  simp only at hp hij
  rw [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, lin_apply, sub_eq_zero]
  simp only [above, Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp [sU, hij, hd]
  · intro k _ hkj
    rcases lt_or_gt_of_ne hkj with hk | hk
    · have : sU t i k = 0 := by
        simp only [sU, Matrix.of_apply]
        split_ifs with h
        · exact ht _ (by simp only; have := Fin.lt_def.1 hk; omega)
        · rfl
      rw [this, zero_mul]
    · rw [hl k j hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem isNilpotent_lin_sub_one {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) : IsNilpotent (lin u - 1) := by
  have key : ∀ m : ℕ, ∀ t : Vp E n, ∀ p : Idx n, p.1.2.val < m → (((lin u - 1) ^ m) t) p = 0 := by
    intro m
    induction m with
    | zero => intro t p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ m ih =>
      intro t p hp
      rw [pow_succ', Module.End.mul_apply]
      exact sub_one_vanish hl hd m _ (ih t) p hp
  exact ⟨n, LinearMap.ext fun t => funext fun p => key n t p p.1.2.isLt⟩

theorem det_lin {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) : LinearMap.det (lin u) = 1 :=
  det_eq_one_of_isNilpotent_sub_one _ (isNilpotent_lin_sub_one hl hd)

end GlobalTheory.WhitBump.Shear


open GlobalTheory.WhitBump.Shear in
theorem GlobalTheory.WhitBump.exists_shear_measurePreserving : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (u : GL (Fin n) (Cinf E)), u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) →
    ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧
      ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := by
  intro E _ _ n u hu
  obtain ⟨hl, hd⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Vp E n)) := Measure.pi.isAddHaarMeasure _
  set L := lin (u : Matrix (Fin n) (Fin n) (Cinf E)) with hLdef
  have hdet : LinearMap.det L = 1 := det_lin hl hd
  have hdet0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact one_ne_zero
  let e := (LinearMap.equivOfDetNeZero L hdet0).toContinuousLinearEquiv
  let h := e.toHomeomorph.trans (Homeomorph.addLeft (above (u : Matrix (Fin n) (Fin n) (Cinf E))))
  refine ⟨h.toMeasurableEquiv, ?_, ?_⟩
  · have hL : MeasurePreserving L volume volume :=
      ⟨L.continuous_of_finiteDimensional.measurable, by
        rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, hdet]; simp⟩
    have := (measurePreserving_add_left volume (above (u : Matrix (Fin n) (Fin n) (Cinf E)))).comp hL
    exact this
  · intro t
    have hmem : nuGL t * u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) := mul_mem (nuGL_mem t) hu
    obtain ⟨hl', hd'⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hmem
    simp only [Units.val_mul, nuGL_val] at hl' hd'
    have : h.toMeasurableEquiv t = above (nu t * (u : Matrix (Fin n) (Fin n) (Cinf E))) := by
      show above _ + L t = _
      rw [hLdef, lin_apply, nu_eq, Matrix.add_mul, Matrix.one_mul]
      rfl
    rw [this, nu_above hl' hd']
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem chartMatrixTopBlock_det_eq_one (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : (chartMatrixTopBlock X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (chartMatrixTopBlock X z τ) (by
    intro i j hij
    have hij' : i < j := hij
    show nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = 0
    have h1 : ¬ (Fin.castLE X.p0_le j < Fin.castLE X.p0_le i) := by
      rw [Fin.lt_iff_val_lt_val]; simp only [Fin.coe_castLE]; exact not_lt.mpr (le_of_lt hij')
    have h2 : Fin.castLE X.p0_le i ≠ Fin.castLE X.p0_le j := by
      intro h; apply ne_of_lt hij'; exact Fin.castLE_injective _ h
    simp only [nmat, dif_neg h1, if_neg h2])]
  apply Finset.prod_eq_one
  intro i _
  show nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le i) = 1
  simp [nmat]

theorem entry_eq (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (m : Fin r) (a : Fin X.p0) :
    nmat X z τ m (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) * chartMatrixTopBlock X z τ c a := by
  by_cases hm : (m : ℕ) < X.p0
  · have hrow : ∀ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) =
        if (⟨m, hm⟩ : Fin X.p0) = c then 1 else 0 := by
      intro c
      simp only [Data.lowBlock, Matrix.of_apply]
      rw [dif_neg (by omega)]
      simp only [add_zero]
      congr 1
      apply propext
      constructor
      · intro h
        have hv : (m : ℕ) = (c : ℕ) := by simpa using congrArg (fun t : Fin r => (t : ℕ)) h
        exact Fin.ext hv
      · intro h; ext; rw [← h]; rfl
    simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  · have hm' : X.p0 ≤ (m : ℕ) := not_lt.mp hm
    have hrow : ∀ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) =
        graphCoord X z τ ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩ c := by
      intro c
      simp only [Data.lowBlock, Matrix.of_apply]
      have hne : m ≠ Fin.castLE X.p0_le c := by
        intro h; have := congrArg Fin.val h; simp at this; have := c.isLt; omega
      rw [if_neg hne, dite_eq_left ⟨hm', c.isLt⟩, zero_add]
      rfl
    simp only [hrow]
    have hdet : IsUnit (chartMatrixTopBlock X z τ).det := by rw [chartMatrixTopBlock_det_eq_one]; exact isUnit_one
    have key : chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹ * chartMatrixTopBlock X z τ = chartBottomLeftBlock X z τ := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
    have := congrFun (congrFun key ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩) a
    rw [Matrix.mul_apply] at this
    have h2 : chartBottomLeftBlock X z τ ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩ a = nmat X z τ m (Fin.castLE X.p0_le a) := by
      show nmat X z τ ⟨X.p0 + ((m : ℕ) - X.p0), _⟩ (Fin.castLE X.p0_le a) = _
      congr 1
      ext; simp only; omega
    exact (this.trans h2).symm

theorem cols_graph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r)
    (z : V (nd X)) (τ : X.Ψ), (chartMatrixTopBlock X z τ).det = 1 ∧ ∀ a : Fin X.p0,
    col (mat (cpt X x z) τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a • col (mat (X.xZ x (graphCoord X z)) τ) (Fin.castLE X.p0_le c) := by
  intro E _ _ _ r X x z τ
  refine ⟨chartMatrixTopBlock_det_eq_one X z τ, fun a => ?_⟩
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  show (mat x τ * mat (nmat X z) τ) k (Fin.castLE X.p0_le a) =
    ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a * (mat x τ * X.lowBlock (graphCoord X z) τ) k (Fin.castLE X.p0_le c)
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  show mat x τ k m * nmat X z τ m (Fin.castLE X.p0_le a) = _
  rw [entry_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.ChartGraph
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound : ∀ (n : ℕ) (f : Sch (Fin n)), ∃ G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n), Continuous G ∧
    (∀ w, ⇑(G w) = rhoFun w ⇑f) ∧
    ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N := by
  first | exact @GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun | exact GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun | (intros; apply GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun <;> assumption)
end

section

open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil

theorem _root_.GlobalTheory.T.continuous_rho_apply : ∀ (l : Type) [Fintype l] (v : L2 l), Continuous fun w : l ⊕ l → ℝ => rho w v := by
  first | exact @GlobalTheory.RealWeil.continuous_rho | exact GlobalTheory.RealWeil.continuous_rho | (intros; apply GlobalTheory.RealWeil.continuous_rho <;> assumption)
end
