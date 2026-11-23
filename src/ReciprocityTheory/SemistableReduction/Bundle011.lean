module

public import ReciprocityTheory.SemistableReduction.Bundle002
public import Lemmata.MiscLemmasR.Imports
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ReciprocityTheory.SemistableReduction.Bundle004
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors

theorem hermForm_smul_smul {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a b : K) (u w : Fin r → K) : S.h (a • u) (b • w) = S.c a * b * S.h u w := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermForm_sum_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {ι : Type} (s : Finset ι) (u : ι → Fin r → K) (w : Fin r → K) :
    S.h (∑ i ∈ s, u i) w = ∑ i ∈ s, S.h (u i) w := by

  simp only [HermForm.h, Finset.sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

theorem hermForm_conj {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (u w : Fin r → K) : S.c (S.h u w) = S.h w u := by

  simp only [HermForm.h, map_sum, map_mul, S.c_invol, S.G_herm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def intInv {K : Type} [Field K] [NumberField K] (c : K →+* K) : 𝓞 K →+* 𝓞 K :=
  RingOfIntegers.mapRingHom c

theorem intInv_coe {K : Type} [Field K] [NumberField K] (c : K →+* K) (a : 𝓞 K) :
    algebraMap (𝓞 K) K (intInv c a) = c (algebraMap (𝓞 K) K a) := rfl

theorem mem_one_map {K : Type} [Field K] [NumberField K] (c : K →+* K) {x : K}
    (hx : x ∈ (1 : Submodule (𝓞 K) K)) : c x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.mp hx
  exact Submodule.mem_one.mpr ⟨intInv c y, intInv_coe c y⟩

def cImage {K : Type} [Field K] [NumberField K] (c : K →+* K) (C : Submodule (𝓞 K) K) :
    Submodule (𝓞 K) K := Bl.ThirdBlockLemmaC.goal1 c C

theorem mem_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K) (C : Submodule (𝓞 K) K)
    {x : K} : x ∈ cImage c C ↔ c x ∈ C := Iff.rfl

theorem cImage_fg {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (C : Submodule (𝓞 K) K) (hC : C.FG) : (cImage c C).FG := by
  haveI : RingHomSurjective (intInv c) :=
    ⟨fun y => ⟨intInv c y, by
      apply RingOfIntegers.ext
      show algebraMap (𝓞 K) K (intInv c (intInv c y)) = algebraMap (𝓞 K) K y
      rw [intInv_coe, intInv_coe, hc]⟩⟩
  let f : K →ₛₗ[intInv c] K :=
    { toFun := c
      map_add' := map_add c
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, intInv_coe] }
  have h : cImage c C = C.map f := by
    ext x
    rw [mem_cImage, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨c x, hx, hc x⟩
    · rintro ⟨y, hy, rfl⟩
      show c (c y) ∈ C
      rw [hc]
      exact hy
  rw [h]
  exact hC.map f

theorem one_le_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K)
    (C : Submodule (𝓞 K) K) (h1 : 1 ≤ C) : 1 ≤ cImage c C := by
  intro x hx
  rw [mem_cImage]
  exact h1 (mem_one_map c hx)

theorem relIndex_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K)
    (hc : ∀ x, c (c x) = x) (C : Submodule (𝓞 K) K) :
    (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex (cImage c C).toAddSubgroup =
      (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup := by
  have h1 : (1 : Submodule (𝓞 K) K).toAddSubgroup
      = (1 : Submodule (𝓞 K) K).toAddSubgroup.comap c.toAddMonoidHom := by
    ext x
    constructor
    · intro hx
      exact mem_one_map c hx
    · intro hx
      have h' : c (c x) ∈ (1 : Submodule (𝓞 K) K) := mem_one_map c hx
      rwa [hc] at h'
  have h2 : (cImage c C).toAddSubgroup = C.toAddSubgroup.comap c.toAddMonoidHom := by
    ext x
    exact mem_cImage c C
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]
  · rw [← h1]
  · exact fun y => ⟨c y, hc y⟩

theorem prod_mem_prod_sub {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) (x : Fin k → K) (hx : ∀ i, x i ∈ p i) :
    ∏ i, x i ∈ ∏ i, p i := by
  classical
  suffices h : ∀ s : Finset (Fin k), ∏ i ∈ s, x i ∈ ∏ i ∈ s, p i by exact h Finset.univ
  intro s
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Submodule.mul_mem_mul (hx a) ih

theorem det_mem_prod_sub {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) (T : Matrix (Fin k) (Fin k) K)
    (hT : ∀ i j, T i j ∈ p i) : T.det ∈ ∏ i, p i := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem_prod_sub p (fun i => Tᵀ (σ i) i) fun i => hT i (σ i)) _

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

def posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then u k else 0

def negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then 0 else u k

def euc {r : ℕ} (u : Fin r → ℂ) : EuclideanSpace ℂ (Fin r) := WithLp.toLp 2 u

lemma euc_add {r : ℕ} (u v : Fin r → ℂ) : euc (u + v) = euc u + euc v := rfl

lemma euc_smul {r : ℕ} (c : ℂ) (u : Fin r → ℂ) : euc (c • u) = c • euc u := rfl

lemma normSq_eq_euc {r : ℕ} (u : Fin r → ℂ) : normSq u = ‖euc u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [normSq, euc]

lemma posSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posSq p u = ‖euc (posPart p u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold posSq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [euc, posPart, PiLp.toLp_apply]
  split_ifs <;> simp

lemma negSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negSq p u = ‖euc (negPart p u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold negSq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [euc, negPart, PiLp.toLp_apply]
  split_ifs <;> simp

lemma normSq_split (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : normSq u = posSq p u + negSq p u := by
  unfold normSq posSq negSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma posPart_add_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p u + negPart p u = u := by
  funext k
  simp only [posPart, negPart, Pi.add_apply]
  split_ifs <;> simp

lemma posPart_add (p : ℕ) {r : ℕ} (u v : Fin r → ℂ) :
    posPart p (u + v) = posPart p u + posPart p v := by
  funext k
  simp only [posPart, Pi.add_apply]
  split_ifs <;> simp

lemma negPart_add (p : ℕ) {r : ℕ} (u v : Fin r → ℂ) :
    negPart p (u + v) = negPart p u + negPart p v := by
  funext k
  simp only [negPart, Pi.add_apply]
  split_ifs <;> simp

lemma posPart_smul (p : ℕ) {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    posPart p (c • u) = c • posPart p u := by
  funext k
  simp only [posPart, Pi.smul_apply]
  split_ifs <;> simp

lemma negPart_smul (p : ℕ) {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    negPart p (c • u) = c • negPart p u := by
  funext k
  simp only [negPart, Pi.smul_apply]
  split_ifs <;> simp

lemma inner_euc {r : ℕ} (x y : Fin r → ℂ) : inner ℂ (euc x) (euc y) = ∑ k, conj (x k) * y k := by
  simp [euc, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

lemma jForm_eq (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) :
    jForm p x y = inner ℂ (euc (posPart p x)) (euc (posPart p y)) -
      inner ℂ (euc (negPart p x)) (euc (negPart p y)) := by
  rw [inner_euc, inner_euc, ← Finset.sum_sub_distrib]
  unfold jForm
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sgn, posPart, negPart]
  split_ifs <;> simp

lemma jForm_self (p : ℕ) {r : ℕ} (y : Fin r → ℂ) :
    jForm p y y = ((posSq p y - negSq p y : ℝ) : ℂ) := by
  unfold jForm posSq negSq
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.conj_mul']
  unfold sgn
  split_ifs <;> simp

lemma norm_posPart_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖euc (posPart p u)‖ ≤ ‖euc u‖ := by
  have h1 := posSq_eq p u
  have h2 := normSq_eq_euc u
  have h3 := normSq_split p u
  have hn : 0 ≤ negSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have ha := norm_nonneg (euc (posPart p u))
  have hb := norm_nonneg (euc u)
  by_contra h
  push_neg at h
  nlinarith

lemma norm_negPart_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖euc (negPart p u)‖ ≤ ‖euc u‖ := by
  have h1 := negSq_eq p u
  have h2 := normSq_eq_euc u
  have h3 := normSq_split p u
  have hn : 0 ≤ posSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have ha := norm_nonneg (euc (negPart p u))
  have hb := norm_nonneg (euc u)
  by_contra h
  push_neg at h
  nlinarith

lemma euc_zero {r : ℕ} : euc (0 : Fin r → ℂ) = 0 := by
  rfl

lemma euc_sum {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) :
    euc (∑ j ∈ s, f j) = ∑ j ∈ s, euc (f j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact euc_zero
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, euc_add, ih]

lemma euc_eq_zero {r : ℕ} {w : Fin r → ℂ} (h : euc w = 0) : w = 0 := by
  have h' := congrArg WithLp.ofLp h
  simpa [euc] using h'

lemma sum_norm_le_sqrt {r : ℕ} (w : Fin r → ℂ) : ∑ j, ‖w j‖ ≤ √(r : ℝ) * ‖euc w‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin r => (1 : ℝ)) (fun j => ‖w j‖)
  rw [EuclideanSpace.norm_eq]
  simpa [euc] using h

lemma norm_err_le {r p : ℕ} {μ R : ℝ} (X : Fin r → Fin r → ℂ)
    (hX : ∀ j : Fin r, (j : ℕ) < p → normSq (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (hμ : 0 ≤ μ) (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    ‖euc (∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))‖ ≤ √(r : ℝ) * μ * ‖euc w‖ := by
  have he : ∀ j : Fin r, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ ≤ ‖w j‖ * μ := by
    intro j
    by_cases hj : (j : ℕ) < p
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := hX j hj
      rw [normSq_eq_euc] at h1
      have ha := norm_nonneg (euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))
      by_contra h
      push_neg at h
      nlinarith
    · rw [hw j (not_lt.mp hj)]
      simp
  calc ‖euc (∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))‖
      = ‖∑ j, w j • euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := by
        rw [euc_sum]
        simp only [euc_smul]
    _ ≤ ∑ j, ‖w j • euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := norm_sum_le _ _
    _ = ∑ j, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := by
        simp only [norm_smul]
    _ ≤ ∑ j, ‖w j‖ * μ := Finset.sum_le_sum fun j _ => he j
    _ = μ * ∑ j, ‖w j‖ := by
        rw [Finset.mul_sum]
        simp only [mul_comm]
    _ ≤ μ * (√(r : ℝ) * ‖euc w‖) := mul_le_mul_of_nonneg_left (sum_norm_le_sqrt w) hμ
    _ = √(r : ℝ) * μ * ‖euc w‖ := by ring

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField
open scoped nonZeroDivisors

def consZero (K : Type) [Field K] (k : ℕ) : (Fin k → K) →ₗ[K] (Fin (k + 1) → K) where
  toFun y := Fin.cons 0 y
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem consZero_injective (K : Type) [Field K] (k : ℕ) : Function.Injective (consZero K k) := by
  intro x y h
  funext i
  simpa [consZero] using congrFun h i.succ

theorem consZero_tail (K : Type) [Field K] {k : ℕ} (x : Fin (k + 1) → K) (hx : x 0 = 0) :
    consZero K k (Fin.tail x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [consZero, hx]
  · simp [consZero, Fin.tail]

theorem single_mem_intVec (K : Type) [Field K] [NumberField K] {k : ℕ} (i : Fin k) {a : K}
    (ha : a ∈ (1 : Submodule (𝓞 K) K)) : Pi.single i a ∈ intVec K k := by
  classical
  simp only [intVec, Submodule.mem_pi, Set.mem_univ, forall_const]
  intro j
  by_cases h : j = i
  · subst h
    simpa using ha
  · simp [h]

theorem consZero_mem_intVec (K : Type) [Field K] [NumberField K] {k : ℕ} {y : Fin k → K} :
    consZero K k y ∈ intVec K (k + 1) ↔ y ∈ intVec K k := by
  simp only [mem_intVec]
  constructor
  · intro h i
    simpa [consZero] using h i.succ
  · intro h i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [consZero]
    · simpa [consZero] using h j

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
end
end
