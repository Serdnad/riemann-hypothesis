module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

@[expose] public section

section

open NumberField Polynomial

namespace GlobalTheory

theorem isIntegral_pow_mul_esymm (s : Multiset ℂ) (c : ℂ) (m : ℕ)
    (h : ∀ w ∈ s, IsIntegral ℤ (c * w)) : IsIntegral ℤ (c ^ m * s.esymm m) := by
  rw [Multiset.esymm, ← Multiset.sum_map_mul_left]
  refine (integralClosure ℤ ℂ).multiset_sum_mem ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  rw [Multiset.mem_powersetCard] at ht
  have : c ^ m * t.prod = (t.map (fun w => c * w)).prod := by
    rw [Multiset.prod_map_mul (f := fun _ => c) (g := fun w => w), Multiset.map_const', Multiset.prod_replicate,
      Multiset.map_id', ht.2]
  rw [this]
  refine (integralClosure ℤ ℂ).multiset_prod_mem ?_
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
  exact h w (Multiset.mem_of_le ht.1 hw)

theorem finite_monic_roots_bdd_mul_isIntegral :
    ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ) (B : ℝ), 0 < N →
    {P : Polynomial F | P.Monic ∧ P.natDegree = n ∧ ∀ φ : F →+* ℂ, ∀ w ∈ (P.map φ).roots,
      ‖w‖ ≤ B ∧ IsIntegral ℤ ((N : ℂ) * w)}.Finite := by
  intro F _ _ n N B hN
  let φ₀ : F →+* ℂ := (Classical.arbitrary (InfinitePlace F)).embedding
  let B₁ : ℝ := max |B| 1
  let C : ℝ := (N : ℝ) ^ n * (B₁ ^ n * 2 ^ n)
  have hT := Embeddings.finite_of_norm_le F ℂ C
  let f : F[X] → Fin (n + 1) → F := fun P k => (N : F) ^ n * P.coeff k
  refine Set.Finite.of_finite_image (f := f) ((Set.Finite.pi (fun _ => hT)).subset ?_) ?_
  · rintro _ ⟨P, ⟨hm, hd, hr⟩, rfl⟩ k -
    have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
    refine ⟨?_, fun φ => ?_⟩
    · have hcard : Multiset.card (P.map φ₀).roots = (P.map φ₀).natDegree :=
        IsAlgClosed.card_roots_eq_natDegree
      have hdeg : (P.map φ₀).natDegree = n := by rw [hm.natDegree_map, hd]
      have hc := coeff_eq_esymm_roots_of_card hcard (k := k) (by omega)
      rw [(hm.map φ₀).leadingCoeff, hdeg, one_mul, coeff_map] at hc
      rw [← isIntegral_algHom_iff φ₀.toIntAlgHom φ₀.injective]
      show IsIntegral ℤ (φ₀ ((N : F) ^ n * P.coeff k))
      rw [map_mul, map_pow, map_natCast, hc]
      have hsplit : (N : ℂ) ^ n * ((-1) ^ (n - k) * (P.map φ₀).roots.esymm (n - k)) =
          ((N : ℂ) ^ (k : ℕ) * (-1) ^ (n - k)) *
            ((N : ℂ) ^ (n - k) * (P.map φ₀).roots.esymm (n - k)) := by
        have : (N : ℂ) ^ n = (N : ℂ) ^ (k : ℕ) * (N : ℂ) ^ (n - k) := by
          rw [← pow_add, Nat.add_sub_cancel' hk]
        rw [this]; ring
      rw [hsplit]
      refine IsIntegral.mul (IsIntegral.mul ((isIntegral_natCast N).pow _)
        ((isIntegral_one.neg).pow _)) ?_
      exact GlobalTheory.isIntegral_pow_mul_esymm _ _ _ (fun w hw => (hr φ₀ w hw).2)
    · show ‖φ ((N : F) ^ n * P.coeff k)‖ ≤ C
      rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
      have hb := coeff_le_of_roots_le (p := P) (f := φ) (B := B₁) k hm (IsAlgClosed.splits _)
        (fun z hz => (hr φ z hz).1.trans ((le_abs_self B).trans (le_max_left _ _)))
      rw [coeff_map, hd] at hb
      have hB₁ : (1 : ℝ) ≤ B₁ := le_max_right _ _
      have h2 : B₁ ^ (n - k) * (n.choose k : ℝ) ≤ B₁ ^ n * 2 ^ n :=
        mul_le_mul (pow_le_pow_right₀ hB₁ (Nat.sub_le _ _))
          (by exact_mod_cast Nat.choose_le_two_pow n k) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (hb.trans h2) (by positivity)
  · rintro P ⟨-, hdP, -⟩ Q ⟨-, hdQ, -⟩ hPQ
    ext i
    by_cases hi : i ≤ n
    · have h := congrFun hPQ ⟨i, by omega⟩
      exact mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')) h
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

end GlobalTheory
end

section

namespace GlobalTheory.ElementarySymmetricNormBound

open Polynomial

theorem sum_esymm_eq_zero (s : Multiset ℂ) (x : ℂ) (hx : x ∈ s) :
    ∑ j ∈ Finset.range (Multiset.card s + 1),
      (-1) ^ j * (s.esymm j * x ^ (Multiset.card s - j)) = 0 := by
  have h := congrArg (Polynomial.eval x) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum] at h
  simp only [Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_one] at h
  rw [← h]
  exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨x, hx, sub_self x⟩)

theorem norm_le_of_esymm (s : Multiset ℂ) (M : ℝ) (hM : 1 ≤ M)
    (h : ∀ j, 1 ≤ j → j ≤ Multiset.card s → ‖s.esymm j‖ ≤ M) (x : ℂ) (hx : x ∈ s) :
    ‖x‖ ≤ (Multiset.card s : ℝ) * M := by
  have hn1 : 1 ≤ Multiset.card s := Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx⟩
  by_cases hx1 : ‖x‖ ≤ 1
  · calc ‖x‖ ≤ 1 := hx1
      _ ≤ M := hM
      _ ≤ (Multiset.card s : ℝ) * M :=
          le_mul_of_one_le_left (by linarith) (by exact_mod_cast hn1)
  push_neg at hx1
  have h0 := sum_esymm_eq_zero s x hx
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm]
  rw [Finset.sum_range_succ'] at h0
  simp only [pow_zero, he0, one_mul, Nat.sub_zero] at h0
  have hxn : x ^ Multiset.card s = -∑ i ∈ Finset.range (Multiset.card s),
      (-1) ^ (i + 1) * (s.esymm (i + 1) * x ^ (Multiset.card s - (i + 1))) :=
    eq_neg_of_add_eq_zero_right h0
  have hbound : ‖x‖ ^ Multiset.card s ≤
      (Multiset.card s : ℝ) * M * ‖x‖ ^ (Multiset.card s - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    calc _ ≤ ∑ i ∈ Finset.range (Multiset.card s),
          ‖(-1 : ℂ) ^ (i + 1) * (s.esymm (i + 1) * x ^ (Multiset.card s - (i + 1)))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (Multiset.card s), M * ‖x‖ ^ (Multiset.card s - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_range.mp hi
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact mul_le_mul (h (i + 1) (by omega) (by omega)) (pow_le_pow_right₀ hx1.le (by omega))
            (pow_nonneg (norm_nonneg _) _) (by linarith)
      _ = (Multiset.card s : ℝ) * M * ‖x‖ ^ (Multiset.card s - 1) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hpos : 0 < ‖x‖ ^ (Multiset.card s - 1) := pow_pos (by linarith) _
  have hsplit : ‖x‖ ^ Multiset.card s = ‖x‖ * ‖x‖ ^ (Multiset.card s - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit] at hbound
  exact le_of_mul_le_mul_right hbound hpos

theorem norm_unit_le_of_esymm :
    ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), Multiset.card B = n → (1 : ℝ) ≤ M →
      (∀ (j : ℕ), (1 : ℕ) ≤ j → j ≤ n →
        ‖Multiset.esymm (Multiset.map (fun (b : ℂˣ) ↦ (↑b : ℂ)) B) j‖ ≤ M) →
      ∀ b ∈ B, ‖(↑b : ℂ)‖ ≤ (↑n : ℝ) * M := by
  intro n B M hcard hM h b hb
  have hb' := norm_le_of_esymm (B.map (fun b : ℂˣ => (b : ℂ))) M hM
    (fun j hj1 hj2 => by
      rw [Multiset.card_map, hcard] at hj2
      exact h j hj1 hj2) (b : ℂ) (Multiset.mem_map_of_mem _ hb)
  rwa [Multiset.card_map, hcard] at hb'

end GlobalTheory.ElementarySymmetricNormBound
end

section

open scoped ComplexOrder

namespace GlobalTheory

open Matrix

theorem schur_complement_step_cpx : ∀ (n r : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → (J * θ).PosDef →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * Y = 1 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u₁ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
      let Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩
      θ * X₂ = u₁ * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) → X₁.conjTranspose * (J * θ) * (Xb + X₁ * A) = 0 →
      θ * (Xb + X₁ * A) = u₁ * Yb * (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)) ∧
        (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)).PosDef := by
  intro n r J θ hJ hpos X Y hXY l d h u₁ A X₁ Xb X₂ Yb Y₂ hθ h0

  let K : Matrix (Fin (l + d)) (Fin d) ℂ := fun i j =>
    Fin.addCases (motive := fun _ => ℂ) (fun i => A i j)
      (fun i => (1 : Matrix (Fin d) (Fin d) ℂ) i j) i
  have hK : X₂ * K = Xb + X₁ * A := by
    ext a c
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp only [K, Fin.addCases_left, Fin.addCases_right, Matrix.add_apply, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Matrix.mul_apply]
    rw [add_comm]
    rfl
  have hP : ∀ {m : ℕ} (f : Fin m → Fin (l + d)),
      (X₂.submatrix id f)ᴴ * (J * θ) * (Xb + X₁ * A)
        = (X₂ᴴ * (J * θ) * (Xb + X₁ * A)).submatrix f id := fun _ => rfl
  have hrow1 : (X₂ᴴ * (J * θ) * (Xb + X₁ * A)).submatrix (Fin.castAdd d) id = 0 :=
    (hP (Fin.castAdd d)).symm.trans h0
  have key : ∀ P : Matrix (Fin (l + d)) (Fin d) ℂ, P.submatrix (Fin.castAdd d) id = 0 →
      Y₂ * P = Yb * P.submatrix (Fin.natAdd l) id := by
    intro P hP0
    ext a c
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
    have h00 : ∀ i, P (Fin.castAdd d i) c = 0 := fun i => by
      simpa using congrFun (congrFun hP0 i) c
    simp only [h00, mul_zero, Finset.sum_const_zero, zero_add]
    rfl
  have hmain : θ * (Xb + X₁ * A) = u₁ * Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A)) := by
    calc θ * (Xb + X₁ * A) = θ * X₂ * K := by rw [← hK, Matrix.mul_assoc]
      _ = u₁ * Y₂ * (X₂ᴴ * (J * θ) * X₂) * K := by rw [hθ]
      _ = u₁ * (Y₂ * (X₂ᴴ * (J * θ) * (X₂ * K))) := by simp only [Matrix.mul_assoc]
      _ = u₁ * (Y₂ * (X₂ᴴ * (J * θ) * (Xb + X₁ * A))) := by rw [hK]
      _ = u₁ * (Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A))) := by rw [key _ hrow1]; rfl
      _ = u₁ * Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A)) := (Matrix.mul_assoc u₁ Yb _).symm
  have hzero : (X₁ * A)ᴴ * (J * θ) * (Xb + X₁ * A) = 0 := by
    have h0' := h0
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc] at h0' ⊢
    rw [h0', Matrix.mul_zero]
  have hsame : Xbᴴ * (J * θ) * (Xb + X₁ * A)
      = (Xb + X₁ * A)ᴴ * (J * θ) * (Xb + X₁ * A) := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.add_mul, hzero, add_zero]
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg Matrix.conjTranspose hXY
    simpa [Matrix.conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hL : (Ybᴴ * J) * (Xb + X₁ * A) = 1 := by
    have e1 : Ybᴴ * J * Xb = 1 := by
      have : Ybᴴ * J * Xb = (Yᴴ * J * X).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
          (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := rfl
      rw [this, hYX]
      ext i j
      simp [Matrix.one_apply, Fin.ext_iff]
    have e2 : Ybᴴ * J * X₁ = 0 := by
      have : Ybᴴ * J * X₁ = (Yᴴ * J * X).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
          (fun j : Fin l => (⟨j.val, by omega⟩ : Fin r)) := rfl
      rw [this, hYX]
      ext i j
      have := j.isLt
      simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.ext_iff, Matrix.zero_apply]
      rw [if_neg (by omega)]
    rw [Matrix.mul_add, e1, ← Matrix.mul_assoc, e2, Matrix.zero_mul, add_zero]
  have hinj : Function.Injective (Xb + X₁ * A).mulVec := by
    intro v w hvw
    have := congrArg (Ybᴴ * J).mulVec hvw
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec, Matrix.one_mulVec] at this
    exact this
  refine ⟨hmain, ?_⟩
  rw [hsame]
  exact hpos.conjTranspose_mul_mul_same hinj

end GlobalTheory
end

section

open scoped ComplexOrder

namespace GlobalTheory

open Matrix

theorem levi_element_cpx : ∀ (n a b : ℕ) (J Q : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → Q.PosDef →
    ∀ (X₁ Y₁ : Matrix (Fin n) (Fin a) ℂ) (Xb Yb : Matrix (Fin n) (Fin b) ℂ),
      X₁.conjTranspose * J * X₁ = 0 → X₁.conjTranspose * J * Xb = 0 → Xb.conjTranspose * J * Xb = 0 →
      X₁.conjTranspose * J * Y₁ = 1 → X₁.conjTranspose * J * Yb = 0 → Yb.conjTranspose * J * Yb = 0 →
      Xb.conjTranspose * J * Yb = 1 →
    ∃ (u₂ : GL (Fin n) ℂ) (A : Matrix (Fin a) (Fin b) ℂ), (u₂.1).conjTranspose * J * u₂.1 = J ∧
      u₂.1 * X₁ = X₁ ∧ u₂.1 * Xb = Xb + X₁ * A ∧ u₂.1 * Yb = Yb ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₁.conjTranspose * J) v = 0 →
        Matrix.mulVec u₂.1 v = v + Matrix.mulVec X₁ (Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v))) ∧
      X₁.conjTranspose * Q * (Xb + X₁ * A) = 0 := by
  intro n a b J Q hJ hQ X₁ Y₁ Xb Yb h11 h1b hbb h1Y h1Yb hYbYb hbYb

  have hYb1 : Ybᴴ * J * X₁ = 0 := by
    have := congrArg conjTranspose h1Yb
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hYbb : Ybᴴ * J * Xb = 1 := by
    have := congrArg conjTranspose hbYb
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hY1 : Y₁ᴴ * J * X₁ = 1 := by
    have := congrArg conjTranspose h1Y
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this

  have hinj : Function.Injective X₁.mulVec := by
    intro x y hxy
    have := congrArg (fun w => (Y₁ᴴ * J) *ᵥ w) hxy
    simp only [mulVec_mulVec] at this
    simpa [hY1] using this
  set G := X₁ᴴ * Q * X₁ with hG
  have hGpd : G.PosDef := hQ.conjTranspose_mul_mul_same hinj
  have hGu : IsUnit G := hGpd.isUnit
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGu
  set A : Matrix (Fin a) (Fin b) ℂ := -(G⁻¹ * (X₁ᴴ * Q * Xb)) with hA
  set T : Matrix (Fin n) (Fin n) ℂ := X₁ * A * Ybᴴ * J - Yb * Aᴴ * X₁ᴴ * J with hT
  have hT2 : T * T = 0 := by
    simp only [hT, sub_mul, mul_sub]
    have e1 : X₁ * A * Ybᴴ * J * (X₁ * A * Ybᴴ * J) = X₁ * A * (Ybᴴ * J * X₁) * A * Ybᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e2 : X₁ * A * Ybᴴ * J * (Yb * Aᴴ * X₁ᴴ * J) = X₁ * A * (Ybᴴ * J * Yb) * Aᴴ * X₁ᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e3 : Yb * Aᴴ * X₁ᴴ * J * (X₁ * A * Ybᴴ * J) = Yb * Aᴴ * (X₁ᴴ * J * X₁) * A * Ybᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e4 : Yb * Aᴴ * X₁ᴴ * J * (Yb * Aᴴ * X₁ᴴ * J) = Yb * Aᴴ * (X₁ᴴ * J * Yb) * Aᴴ * X₁ᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e1, e2, e3, e4, hYb1, hYbYb, h11, h1Yb]
    simp
  have hTJ : Tᴴ * J = -(J * T) := by
    simp only [hT, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hJ, sub_mul, mul_sub,
      Matrix.mul_assoc, neg_sub]
  let u : GL (Fin n) ℂ := ⟨1 + T, 1 - T, by
      rw [mul_sub, mul_one, add_mul, one_mul, hT2]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, hT2]; abel⟩
  refine ⟨u, A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (1 + T)ᴴ * J * (1 + T) = J
    rw [conjTranspose_add, conjTranspose_one, add_mul, one_mul, add_mul, mul_add, mul_add, hTJ]
    simp only [mul_one, neg_mul, Matrix.mul_assoc, hT2, mul_zero, neg_zero, add_zero]
    abel
  · show (1 + T) * X₁ = X₁
    have : T * X₁ = 0 := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * X₁ = X₁ * A * (Ybᴴ * J * X₁) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * X₁ = Yb * Aᴴ * (X₁ᴴ * J * X₁) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYb1, h11]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this, add_zero]
  · show (1 + T) * Xb = Xb + X₁ * A
    have : T * Xb = X₁ * A := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * Xb = X₁ * A * (Ybᴴ * J * Xb) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * Xb = Yb * Aᴴ * (X₁ᴴ * J * Xb) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYbb, h1b]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this]
  · show (1 + T) * Yb = Yb
    have : T * Yb = 0 := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * Yb = X₁ * A * (Ybᴴ * J * Yb) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * Yb = Yb * Aᴴ * (X₁ᴴ * J * Yb) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYbYb, h1Yb]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this, add_zero]
  · intro v hv
    show (1 + T) *ᵥ v = v + X₁ *ᵥ (A *ᵥ ((Ybᴴ * J) *ᵥ v))
    rw [add_mulVec, one_mulVec]
    congr 1
    simp only [hT, sub_mulVec]
    have e1 : (X₁ * A * Ybᴴ * J) *ᵥ v = X₁ *ᵥ (A *ᵥ ((Ybᴴ * J) *ᵥ v)) := by
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    have e2 : (Yb * Aᴴ * X₁ᴴ * J) *ᵥ v = (Yb * Aᴴ) *ᵥ ((X₁ᴴ * J) *ᵥ v) := by
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    rw [e1, e2, hv, mulVec_zero, sub_zero]
  · rw [Matrix.mul_add]
    have : X₁ᴴ * Q * (X₁ * A) = G * A := by rw [hG]; simp only [Matrix.mul_assoc]
    rw [this, hA, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hGdet, Matrix.one_mul]
    simp

end GlobalTheory
end

section

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory

open Matrix

theorem posDef_exists_conjTranspose_mul_mul_eq_one :
    ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef →
      ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  intro d H hP
  have hH : H.IsHermitian := hP.isHermitian
  set U : Matrix (Fin d) (Fin d) ℂ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := hH.eigenvectorUnitary.2.1
  have hU2 : U * Uᴴ = 1 := hH.eigenvectorUnitary.2.2
  have hspec : H = U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hP.eigenvalues_pos i
  let r : Fin d → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  have hr : ∀ i, 0 < r i := fun i => Real.sqrt_pos.2 (hpos i)
  have hrr : ∀ i, r i * r i = hH.eigenvalues i := fun i => Real.mul_self_sqrt (hpos i).le
  let s : Fin d → ℂ := fun i => (((r i)⁻¹ : ℝ) : ℂ)
  let t : Fin d → ℂ := fun i => ((r i : ℝ) : ℂ)
  have hst : diagonal s * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ (hr i).ne', Complex.ofReal_one]
  have hts : diagonal t * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ (hr i).ne', Complex.ofReal_one]
  let Y : Matrix (Fin d) (Fin d) ℂ := U * diagonal s
  let Z : Matrix (Fin d) (Fin d) ℂ := diagonal t * Uᴴ
  have hYZ : Y * Z = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), hst, Matrix.one_mul, hU2]
  have hZY : Z * Y = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hts]
  refine ⟨⟨Y, Z, hYZ, hZY⟩, ?_⟩
  show Yᴴ * H * Y = 1
  have hsH : (diagonal s)ᴴ = diagonal s := by
    rw [diagonal_conjTranspose]
    congr 1; funext i
    simp [s]
  have hdiag : diagonal s * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, ← hrr i, ← Complex.ofReal_mul]
    rw [show (r i)⁻¹ * (r i * r i) * (r i)⁻¹ = ((r i)⁻¹ * r i) * (r i * (r i)⁻¹) by ring,
      inv_mul_cancel₀ (hr i).ne', mul_inv_cancel₀ (hr i).ne']
    simp
  simp only [Y]
  rw [conjTranspose_mul, hsH, hspec]
  calc diagonal s * Uᴴ * (U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal s)
      = diagonal s * (Uᴴ * U) * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal s := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU1, Matrix.mul_one, Matrix.mul_one, hdiag]

end GlobalTheory
end
end

section

noncomputable section

namespace GlobalTheory.SphereMeanDrop

open MeasureTheory Set

def gaussProb (n : ℕ) : Measure (EuclideanSpace ℂ (Fin n)) :=
  ProbabilityTheory.cond ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2))) univ

def radProb (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  ProbabilityTheory.cond ((Measure.volumeIoiPow (2 * n - 1)).withDensity
    fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ

def firstCoords {N n : ℕ} (h : N ≤ n) (x : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun j => WithLp.ofLp x (Fin.castLE h j)

end GlobalTheory.SphereMeanDrop
end
end
