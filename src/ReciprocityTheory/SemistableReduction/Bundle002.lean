module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def triChar {p : ℕ} (a : Fin p → ℕ) (b : Matrix (Fin p) (Fin p) ℂ) : ℂ :=
  ∏ i, b i i ^ a i

def IsTriEquivariant {p : ℕ} (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  ∀ x b : Matrix (Fin p) (Fin p) ℂ, x.det ≠ 0 → b.det ≠ 0 → b.BlockTriangular id →
    P (x * b) = triChar a b * P x

def colNormSq {p : ℕ} (x : Matrix (Fin p) (Fin p) ℂ) (j : Fin p) : ℝ :=
  ∑ i, ‖x i j‖ ^ 2

def LemmaHStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (a : ∀ s, Fin (p s) → ℕ)
    (P : (∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) → ℂ) (C R : ℝ),
    (∀ (x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (s : ι) (b : Matrix (Fin (p s)) (Fin (p s)) ℂ),
      (∀ t, (x t).det ≠ 0) → b.det ≠ 0 → b.BlockTriangular id →
      P (Function.update x s (x s * b)) = triChar (a s) b * P x) →
    (∀ k : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ,
      (∀ s, k s ∈ Matrix.unitaryGroup (Fin (p s)) ℂ) → ‖P k‖ ≤ C) → 0 ≤ R →
    ∀ x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ, (∀ s, (x s).det ≠ 0) →
      (∀ s j, colNormSq (x s) j ≤ R ^ 2) → ‖P x‖ ≤ C * R ^ (∑ s, ∑ i, a s i)

def TorsionNonvanishStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (θ : V → ℂ) (Λ : AddSubgroup V) (ρ : ℝ) (n : ℕ),
    Differentiable ℂ θ → (∃ z, θ z ≠ 0) →
    (∀ l ∈ Λ, ∀ z, ‖θ (z + l)‖ * Real.exp (-(Real.pi / 2) * ‖z + l‖ ^ 2) =
      ‖θ z‖ * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) →
    (∀ v : V, ∃ l ∈ Λ, ‖v - l‖ ≤ ρ) → 5 * ρ < n →
    ∃ l ∈ Λ, θ ((n : ℂ)⁻¹ • l) ≠ 0

def sgn (p : ℕ) {r : ℕ} (k : Fin r) : ℂ := if (k : ℕ) < p then 1 else -1

def jForm (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) : ℂ :=
  ∑ k, sgn p k * (conj (x k) * y k)

def normSq {r : ℕ} (u : Fin r → ℂ) : ℝ := ∑ k, ‖u k‖ ^ 2

def posSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ℝ :=
  ∑ k : Fin r, if (k : ℕ) < p then ‖u k‖ ^ 2 else 0

def negSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ℝ :=
  ∑ k : Fin r, if (k : ℕ) < p then 0 else ‖u k‖ ^ 2

def approxR (r : ℕ) (μ ρ : ℝ) : ℝ := 4 * Real.sqrt r * μ / ρ

def ApproxGraphStatement : Prop :=
  ∀ (r p : ℕ) (μ ρ : ℝ) (X : Fin r → Fin r → ℂ), p ≤ r → 0 < μ → 0 < ρ → ρ ≤ 1 →
    (∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2) →
    (∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j))) ∧
    (∀ y : Fin r → ℂ, (∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) → y ≠ 0 →
      (jForm p y y).re < 0) ∧
    (∀ v y : Fin r → ℂ, (∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) →
      v - y ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p}) →
      ‖jForm p y y‖ ≤ 2 * normSq v)

structure HermForm (K : Type) [Field K] [NumberField K] (r : ℕ) where

  c : K →+* K
  c_invol : ∀ x, c (c x) = x
  c_emb : ∀ (σ : K →+* ℂ) (x : K), σ (c x) = conj (σ x)

  G : Matrix (Fin r) (Fin r) K
  G_herm : ∀ a b, c (G a b) = G b a

def HermForm.h {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (x y : Fin r → K) : K :=
  ∑ a, ∑ b, S.c (x a) * S.G a b * y b

def embVec {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ) (x : Fin r → K) : Fin r → ℂ := fun a => σ (x a)

def IsIntegralElt {K : Type} [Field K] [NumberField K] (x : K) : Prop := ∃ z : 𝓞 K, (z : K) = x

def IsLattice {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin r → K)) = ⊤

def IsIntegralOn {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, IsIntegralElt (S.h x y)

def IsSelfDual {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  IsIntegralOn S L ∧ ∀ x, (∀ y ∈ L, IsIntegralElt (S.h x y)) → x ∈ L

def majSq {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (v : Fin r → K) : ℝ :=
  ∑ i, normSq (Q i *ᵥ embVec (σ i) v)

def ApproxStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [Nonempty ι] (r p : ℕ)
    (S : HermForm K r) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (v : Fin r → Fin r → K) (μ ρ : ℝ),
    p ≤ r → 0 < μ → 0 < ρ → ρ ≤ 1 → (∀ i, (Q i).det ≠ 0) →
    (∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) →
    IsIntegralOn S L →
    (∀ w : ι → Fin r → ℂ, ∃ l ∈ L, ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ μ ^ 2) →
    (∀ j, v j ∈ L) → LinearIndependent K v → (∀ j, majSq σ Q (v j) ≤ μ ^ 2) →
    ∃ la : Fin r → Fin r → K, (∀ j, la j ∈ L) ∧ LinearIndependent K la ∧
      (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → S.h (la j) (la k) = 0) ∧
      (∀ i (w : Fin r → ℂ), (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
        negSq p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j)) ≤
          (ρ / 3) ^ 2 * posSq p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j)) ∧
        (w ≠ 0 → 0 < (jForm p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))
          (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))).re)) ∧
      (∀ i (w : Fin r → ℂ), (∀ j : Fin r, (j : ℕ) < p → w j = 0) → w ≠ 0 →
        (jForm p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))
          (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))).re < 0) ∧
      (∀ i (j : Fin r), (j : ℕ) < p → ‖σ i (S.h (la j) (la j))‖ ≤ (2 * approxR r μ ρ) ^ 2) ∧
      (∀ i (j : Fin r), p ≤ (j : ℕ) →
        ‖σ i (S.h (la j) (la j))‖ ≤ (2 * approxR r μ ρ) ^ (4 * p) * (2 * μ ^ 2))

def OnePolyGrowthStatement : Prop :=
  ∀ (f : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (k : ℕ), B.Finite → DifferentiableOn ℂ f Bᶜ →
    (∀ t ∉ B, ‖f t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t ∉ B, f t = P.eval t

def IsHoloGL {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ (fun y : Fin p → Fin p → ℂ => P (Matrix.of y)) {y | (Matrix.of y).det ≠ 0}

def leadMinor {p : ℕ} (x : Matrix (Fin p) (Fin p) ℂ) (i : Fin p) : ℂ :=
  (Matrix.of fun a b : Fin (i + 1) => x (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)).det

def BWPolyStatement : Prop :=
  ∀ (p : ℕ) (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ), IsHoloGL P →
    IsTriEquivariant a P →
    ∃ F : MvPolynomial (Fin p × Fin p) ℂ, F.IsHomogeneous (∑ i, a i) ∧
      ∀ x : Matrix (Fin p) (Fin p) ℂ, x.det ≠ 0 → P x = MvPolynomial.eval (fun ij => x ij.1 ij.2) F

end ReciprocityTheory.MultiplicativeHeights
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open Finset InnerProductSpace

private theorem exists_eq_gramSchmidt_add_sum_Iio {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (n : ℕ) (v : Fin n → E) :
    ∃ c : Fin n → Fin n → ℂ,
      ∀ j, v j = gramSchmidt ℂ v j + ∑ i ∈ Iio j, c j i • gramSchmidt ℂ v i :=
  ⟨_, fun j => gramSchmidt_def'' (𝕜 := ℂ) v j⟩

theorem det_gram_eq_prod_gramSchmidt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) :
    (Matrix.gram ℂ v).det = ∏ k, (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) := by
  classical
  obtain ⟨c, hc⟩ := exists_eq_gramSchmidt_add_sum_Iio n v
  let A : Matrix (Fin n) (Fin n) ℂ := fun i j => if i = j then 1 else if i < j then c j i else 0
  have hA : ∀ j, v j = ∑ i, A i j • gramSchmidt ℂ v i := by
    intro j
    have h1 : ∀ i, A i j • gramSchmidt ℂ v i =
        (if i = j then gramSchmidt ℂ v i else 0) +
          (if i < j then c j i • gramSchmidt ℂ v i else 0) := by
      intro i
      by_cases h : i = j
      · subst h; simp [A]
      · by_cases h' : i < j
        · simp [A, h, h']
        · simp [A, h, h']
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, hc j]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i
    simp
  have horth : ∀ k l, ⟪gramSchmidt ℂ v k, gramSchmidt ℂ v l⟫_ℂ =
      if k = l then (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) else 0 := by
    intro k l
    by_cases h : k = l
    · subst h
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    · rw [if_neg h, gramSchmidt_orthogonal (𝕜 := ℂ) v h]
  have hG : Matrix.gram ℂ v =
      Matrix.conjTranspose A * Matrix.diagonal (fun k => (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ)) * A := by
    ext i j
    show ⟪v i, v j⟫_ℂ = _
    rw [hA i, hA j]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, horth, mul_ite, mul_zero,
      Finset.mem_univ, if_true, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq',
      Matrix.conjTranspose_apply, starRingEnd_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hAtri : A.BlockTriangular id := by
    intro i j h
    simp only [id] at h
    simp [A, h.ne', not_lt.mpr h.le]
  have hdetA : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAtri]
    simp [A]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdetA, Matrix.det_diagonal]
  simp

theorem prod_le_re_det_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) (δ : Fin n → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (h : ∀ k, ∀ x ∈ Submodule.span ℂ (v '' Set.Iio k), δ k ≤ ‖v k - x‖ ^ 2) :
    ∏ k, δ k ≤ (Matrix.gram ℂ v).det.re := by
  classical
  rw [det_gram_eq_prod_gramSchmidt, ← Complex.ofReal_prod, Complex.ofReal_re]
  refine Finset.prod_le_prod₀ (fun k _ => hδ k) (fun k _ => ?_)
  obtain ⟨c, hc⟩ := exists_eq_gramSchmidt_add_sum_Iio n v
  have hmem : ∑ i ∈ Iio k, c k i • gramSchmidt ℂ v i ∈ Submodule.span ℂ (v '' Set.Iio k) := by
    rw [← span_gramSchmidt_Iio (𝕜 := ℂ) v k]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)
  have h1 := h k _ hmem
  rwa [← eq_sub_of_add_eq (hc k).symm] at h1

end ReciprocityTheory.MultiplicativeHeights
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix
open scoped ComplexOrder

theorem sc_schur_posDef {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k]
    {A : Matrix k k ℂ} (B : Matrix k m ℂ) (D : Matrix m m ℂ) (hA : A.PosDef)
    (h : (fromBlocks A B Bᴴ D).PosDef) : (D - Bᴴ * A⁻¹ * B).PosDef := by
  classical
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  obtain ⟨N, hN⟩ : ∃ N : Matrix (k ⊕ m) m ℂ, N = fromRows (-(A⁻¹ * B)) 1 := ⟨_, rfl⟩
  have hinj : Function.Injective N.mulVec := by
    intro v w hvw
    funext i
    have h1 := congrFun hvw (Sum.inr i)
    simpa [hN, fromRows_mulVec] using h1
  have hAA : A * A⁻¹ = 1 := mul_nonsing_inv A hAu
  have h1 : A * (-(A⁻¹ * B)) + B * (1 : Matrix m m ℂ) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, hAA, Matrix.one_mul, Matrix.mul_one, neg_add_cancel]
  have h2 : Bᴴ * (-(A⁻¹ * B)) + D * (1 : Matrix m m ℂ) = D - Bᴴ * A⁻¹ * B := by
    rw [Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc]
    abel
  have key : Nᴴ * fromBlocks A B Bᴴ D * N = D - Bᴴ * A⁻¹ * B := by
    rw [hN, conjTranspose_fromRows_eq_fromCols_conjTranspose, ← fromRows_fromCols_eq_fromBlocks,
      fromCols_mul_fromRows, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [fromCols_mul_fromRows, fromCols_mul_fromRows, h1, h2, Matrix.mul_zero, zero_add,
      conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc]
  have hpd := h.conjTranspose_mul_mul_same hinj
  rwa [key] at hpd

end ReciprocityTheory.MultiplicativeHeights
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open scoped TensorProduct

def RankStatement : Prop :=
  ∀ (K L V : Type) [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) (ι : Type) (v : ι → V),
    (∀ i, v i ∈ W) →
    Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[K] v i) = ⊤ →
    W = ⊤ ∧ Submodule.span K (Set.range v) = ⊤

noncomputable def torusSum {K : Type*} [NormedField K] {n : ℕ} (c : (Fin n → ℤ) → K)
    (τ : Fin n → K) : K :=
  ∑' χ, c χ * ∏ i, τ i ^ χ i

def ResidueFieldInfiniteOn {K : Type*} [NormedField K] (S : Set K) : Prop :=
  ∀ s : Finset K, ∃ x ∈ S, ‖x‖ ≤ 1 ∧ ∀ y ∈ s, 1 ≤ ‖x - y‖

def CauchyTorusStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (K₀ : Subfield K),
    ResidueFieldInfiniteOn (K₀ : Set K) →
    ∀ (n : ℕ) (c : (Fin n → ℤ) → K),
      Filter.Tendsto (fun χ => ‖c χ‖) Filter.cofinite (nhds 0) →
      (∀ τ : Fin n → K, (∀ i, τ i ∈ K₀ ∧ ‖τ i‖ = 1) → ‖torusSum c τ‖ ≤ 1) →
      ∀ χ, ‖c χ‖ ≤ 1

def NormLengthStatement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B] [IsDomain B]
    [Algebra O B] [Module.Finite O B] [NoZeroSMulDivisors O B] (g : B),
    g ≠ 0 →
      IsDiscreteValuationRing.addVal O (Algebra.norm O g) =
        Module.length O (B ⧸ Ideal.span {g})

def NormOrdStatement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B] [IsDomain B]
    [IsDedekindDomain B] [Algebra O B] [Module.Finite O B] [NoZeroSMulDivisors O B] (g : B),
    g ≠ 0 →
      IsDiscreteValuationRing.addVal O (Algebra.norm O g) =
        ((∑ᶠ Q : {Q : Ideal B // Q.IsMaximal},
          Q.1.inertiaDeg O *
            Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {g})) :
          ℕ) : ℕ∞)

def comapInclusion {F₁ F₂ : Type*} [Field F₁] [Field F₂] (V : ValuationSubring F₂)
    (f : F₁ →+* F₂) : V.comap f →+* V :=
  f.restrict (V.comap f) V fun _ hx => hx

instance comapInclusion_isLocalHom {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    (V : ValuationSubring F₂) (f : F₁ →+* F₂) : IsLocalHom (comapInclusion V f) := by
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hx
  have hu' : f (x : F₁) * (u : F₂) = 1 := congrArg Subtype.val hu
  have hx0 : (x : F₁) ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero, zero_mul] at hu'; exact hu')
  have hinv : f ((x : F₁)⁻¹) = (u : F₂) := by rw [map_inv₀]; exact inv_eq_of_mul_eq_one_right hu'
  have hmem : (x : F₁)⁻¹ ∈ V.comap f := by rw [ValuationSubring.mem_comap, hinv]; exact u.2
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

noncomputable abbrev residueAlgebra {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    (V : ValuationSubring F₂) (f : F₁ →+* F₂) :
    Algebra (IsLocalRing.ResidueField (V.comap f)) (IsLocalRing.ResidueField V) :=
  (IsLocalRing.ResidueField.map (comapInclusion V f)).toAlgebra

def TRStatement : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] [Algebra F₁ F₂] (V : ValuationSubring F₂),
    letI := residueAlgebra V (algebraMap F₁ F₂)
    Algebra.trdeg (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (IsLocalRing.ResidueField V) ≤ Algebra.trdeg F₁ F₂

def DedekindRankStatement : Prop :=
  ∀ (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F]
    [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [Algebra O L] [IsScalarTower O F L],
    IsDedekindDomain (integralClosure O L) ∧ Module.Finite O (integralClosure O L) ∧
      Module.Free O (integralClosure O L) ∧
      Module.finrank O (integralClosure O L) = Module.finrank F L ∧
      {Q : Ideal (integralClosure O L) | Q.IsMaximal}.Finite ∧
      ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal},
          Q.1.ramificationIdx O * Q.1.inertiaDeg O = Module.finrank F L

abbrev SVars (D m : ℕ) : Type := Unit ⊕ (Fin (D + 1) × Fin m)

abbrev SField (Ω : Type) [Field Ω] (D m : ℕ) : Type :=
  FractionRing (MvPolynomial (SVars D m) Ω)

noncomputable def sImage {Ω : Type} [Field Ω] {D m : ℕ} (x : Fin m → Ω) :
    Fin (D + 1) × Fin (m + 1) → SField Ω D m :=
  fun p => algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m)
    (Fin.cases (motive := fun _ => MvPolynomial (SVars D m) Ω)
      (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
      (fun j => MvPolynomial.X (Sum.inr (p.1, j))) p.2)

def FieldOfSStatement : Prop :=
  ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] (D m : ℕ) (x : Fin m → Ω),
    (⊤ : IntermediateField K Ω).FG → Algebra.trdeg K Ω = D →
    (∃ J : Fin D → Fin m,
      LinearIndependent Ω fun a => KaehlerDifferential.D K Ω (x (J a))) →
    AlgebraicIndependent K (sImage (D := D) x) ∧
      FiniteDimensional (IntermediateField.adjoin K (Set.range (sImage (D := D) x)))
        (SField Ω D m)

def ResidueTrdegStatement : Prop :=
  ∀ (K Ω U : Type) [Field K] [Field Ω] [Field U] [Algebra K Ω] [Algebra Ω U] (D : ℕ),
    Algebra.trdeg K Ω = D →
    ∀ (σ : Type) [Fintype σ] (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
      (τ : Type) [Fintype τ] (u : τ → V) (p : τ → MvPolynomial σ Ω)
      (hp : ∀ j α, (p j).coeff α ∈ V.comap (algebraMap Ω U)),
      Fintype.card τ = Fintype.card σ + D → (∀ j, MvPolynomial.aeval t (p j) = (u j : U)) →
      letI _iW := residueAlgebra V (algebraMap Ω U)
      letI _io := residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
      letI : Algebra (IsLocalRing.ResidueField
          ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (IsLocalRing.ResidueField V) :=
        ((algebraMap _ (IsLocalRing.ResidueField V)).comp
          (algebraMap _ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
      AlgebraicIndependent
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (fun j => IsLocalRing.residue V (u j)) →
      (∀ k₁ : IntermediateField
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))),
        (∀ j α, IsLocalRing.residue _ ⟨(p j).coeff α, hp j α⟩ ∈ k₁) →
        Algebra.trdeg
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) k₁ = D) ∧
      Algebra.trdeg
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) = D ∧
        AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
          (fun s => IsLocalRing.residue V ⟨t s, ht s⟩)

end ReciprocityTheory.MultiplicativeHeights
end
