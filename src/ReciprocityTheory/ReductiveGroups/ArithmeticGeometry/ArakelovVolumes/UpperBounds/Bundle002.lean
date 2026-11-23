module

public import Mathlib.LinearAlgebra.Matrix.Block
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfA
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

abbrev UpI (ι : Type*) (r : ℕ) : Type _ := {i : Ix ι r // ¬ i.2.2 < i.2.1}

abbrev LoI (ι : Type*) (r : ℕ) : Type _ := {i : Ix ι r // i.2.2 < i.2.1}

def Umat (y : UpI ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if h : ¬ b < a then y ⟨(τ, a, b), h⟩ else 0

lemma Umat_add (y y' : UpI ι r → ℂ) (τ : ι) : Umat (y + y') τ = Umat y τ + Umat y' τ := by
  ext a b
  simp only [Umat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma Umat_smul (c : ℂ) (y : UpI ι r → ℂ) (τ : ι) : Umat (c • y) τ = c • Umat y τ := by
  ext a b
  simp only [Umat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) : (UpI ι r → ℂ) →ₗ[ℂ] (UpI ι r → ℂ) where
  toFun y i := (β i.1.1 * Umat y i.1.1) i.1.2.1 i.1.2.2
  map_add' y y' := by funext i; simp [Umat_add, Matrix.mul_add]
  map_smul' c y := by funext i; simp [Umat_smul]

def keyU (e : ι ≃ Fin (Fintype.card ι)) (i : UpI ι r) : ℕ ×ₗ (ℕ ×ₗ Fin (Fintype.card ι)) :=
  toLex ((i.1.2.2 : ℕ), toLex (r - (i.1.2.1 : ℕ), e i.1.1))

lemma keyU_injective (e : ι ≃ Fin (Fintype.card ι)) : Function.Injective (keyU (r := r) e) := by
  rintro ⟨⟨τ, a, b⟩, hi⟩ ⟨⟨τ', a', b'⟩, hj⟩ h
  simp only [keyU, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : (a : ℕ) = a' := by have := a.isLt; have := a'.isLt; omega
  apply Subtype.ext
  simp only [Prod.mk.injEq]
  exact ⟨e.injective h3, Fin.ext ha, Fin.ext h1⟩

private lemma toMatrix_entry_lemma (β : ι → Matrix (Fin r) (Fin r) ℂ) (i j : UpI ι r) :
    LinearMap.toMatrix' (Lβ β) i j =
      if j.1.1 = i.1.1 ∧ j.1.2.2 = i.1.2.2 then β i.1.1 i.1.2.1 j.1.2.1 else 0 := by
  obtain ⟨⟨τ, a, b⟩, hi⟩ := i
  obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
  rw [LinearMap.toMatrix'_apply]
  simp only [Lβ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Umat, Matrix.of_apply]
  rw [Finset.sum_eq_single a']
  · by_cases h : τ' = τ ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hj, Pi.single_apply]
    · rw [if_neg h]
      split_ifs with h'
      · simp
      · rw [Pi.single_apply, if_neg, mul_zero]
        intro heq
        apply h
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
        exact ⟨heq.1.symm, heq.2.2.symm⟩
  · intro c _ hc
    split_ifs with h'
    · simp
    · rw [Pi.single_apply, if_neg, mul_zero]
      intro heq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
      exact hc heq.2.1
  · simp

lemma toMatrix_Lβ_zero (e : ι ≃ Fin (Fintype.card ι)) (β : ι → Matrix (Fin r) (Fin r) ℂ)
    (hβ : ∀ τ, (β τ).BlockTriangular id) (i j : UpI ι r) (hij : keyU e i < keyU e j) :
    LinearMap.toMatrix' (Lβ β) i j = 0 := by
  rw [toMatrix_entry_lemma]
  split_ifs with h
  · obtain ⟨⟨τ, a, b⟩, hi⟩ := i
    obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
    obtain ⟨rfl, rfl⟩ := h
    simp only [keyU, Prod.Lex.toLex_lt_toLex, lt_irrefl, false_or, and_false, or_false,
      true_and] at hij
    apply hβ _
    have := a.isLt; have := a'.isLt
    show (a' : ℕ) < a
    omega
  · rfl

lemma toMatrix_Lβ_diag (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (i : UpI ι r) :
    LinearMap.toMatrix' (Lβ β) i i = β i.1.1 i.1.2.1 i.1.2.1 := by
  rw [toMatrix_entry_lemma, if_pos ⟨rfl, rfl⟩]

theorem det_Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) :
    LinearMap.det (Lβ β) = ∏ i : UpI ι r, β i.1.1 i.1.2.1 i.1.2.1 := by
  rw [← LinearMap.det_toMatrix']
  let e := Fintype.equivFin ι
  letI : LinearOrder (UpI ι r) := LinearOrder.lift' (keyU (r := r) e) (keyU_injective e)
  have h := Matrix.det_of_lowerTriangular (LinearMap.toMatrix' (Lβ β)) (fun i j hij =>
    toMatrix_Lβ_zero e β hβ i j hij)
  convert h using 2 with i
  exact (toMatrix_Lβ_diag β hβ i).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

variable {n : ℕ}

theorem mulO {f g : V n → ℂ} {a b c : ℕ} (hf : f =O[𝓝 0] fun z => ‖z‖ ^ a)
    (hg : g =O[𝓝 0] fun z => ‖z‖ ^ b) (h : a + b = c) :
    (fun z => f z * g z) =O[𝓝 0] fun z => ‖z‖ ^ c := by
  subst h
  exact (hf.mul hg).congr_right fun z => (pow_add _ _ _).symm

theorem pow_sub_pow {u v : V n → ℂ} (hu : u =O[𝓝 0] fun z => ‖z‖) (hv : v =O[𝓝 0] fun z => ‖z‖)
    (huv : (fun z => u z - v z) =O[𝓝 0] fun z => ‖z‖ ^ 2) (e : ℕ) :
    (fun z => u z ^ e - v z ^ e) =O[𝓝 0] fun z => ‖z‖ ^ (e + 1) := by
  rcases e with _ | e
  · simp only [pow_zero, sub_self]
    exact Asymptotics.isBigO_zero (fun z : V n => ‖z‖ ^ (0 + 1)) (𝓝 (0 : V n))
  · have hs : (fun z : V n => ∑ i ∈ Finset.range (e + 1), u z ^ i * v z ^ (e + 1 - 1 - i)) =O[𝓝 0]
        fun z : V n => ‖z‖ ^ e := by
      have hterm : ∀ i ∈ Finset.range (e + 1), (fun z : V n => u z ^ i * v z ^ (e + 1 - 1 - i)) =O[𝓝 0]
          fun z : V n => ‖z‖ ^ e := by
        intro i hi
        have hi' : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        refine ((hu.pow i).mul (hv.pow (e + 1 - 1 - i))).congr_right fun z => ?_
        rw [← pow_add]
        congr 1
        omega
      exact (Asymptotics.IsBigO.sum hterm).congr_left fun z => Finset.sum_apply z _ _
    refine ((hs.mul huv).congr_left fun z => ?_).congr_right fun z => ?_
    · exact (Commute.all (u z) (v z)).geom_sum₂_mul (e + 1)
    · ring

theorem prod_pow_O {ι : Type*} (s : Finset ι) (u : ι → V n → ℂ) (e : ι → ℕ)
    (hu : ∀ i, u i =O[𝓝 0] fun z => ‖z‖) :
    (fun z => ∏ i ∈ s, u i z ^ e i) =O[𝓝 0] fun z => ‖z‖ ^ (∑ i ∈ s, e i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]
    exact Asymptotics.isBigO_const_const (1 : ℂ) one_ne_zero _
  · intro a s ha ih
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mulO ((hu a).pow (e a)) ih rfl

theorem prod_pow_sub {ι : Type*} (s : Finset ι) (u v : ι → V n → ℂ) (e : ι → ℕ)
    (hu : ∀ i, u i =O[𝓝 0] fun z => ‖z‖) (hv : ∀ i, v i =O[𝓝 0] fun z => ‖z‖)
    (huv : ∀ i, (fun z => u i z - v i z) =O[𝓝 0] fun z => ‖z‖ ^ 2) :
    (fun z => ∏ i ∈ s, u i z ^ e i - ∏ i ∈ s, v i z ^ e i) =O[𝓝 0]
      fun z => ‖z‖ ^ (∑ i ∈ s, e i + 1) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty, sub_self]
    exact Asymptotics.isBigO_zero (fun z : V n => ‖z‖ ^ (∑ i ∈ (∅ : Finset ι), e i + 1)) (𝓝 (0 : V n))
  · intro a s ha ih
    have hc : e a + (∑ i ∈ s, e i + 1) = ∑ i ∈ insert a s, e i + 1 := by
      have := Finset.sum_insert ha (f := e); omega
    have hc' : (e a + 1) + ∑ i ∈ s, e i = ∑ i ∈ insert a s, e i + 1 := by
      have := Finset.sum_insert ha (f := e); omega
    have h1 := mulO ((hu a).pow (e a)) ih hc
    have h2 := mulO (pow_sub_pow (hu a) (hv a) (huv a) (e a)) (prod_pow_O s v e hv) hc'
    refine (h1.add h2).congr_left fun z => ?_
    simp only [Finset.prod_insert ha]
    ring

theorem taylor2 {g : V n → ℂ} (hg : AnalyticAt ℂ g 0) :
    (fun z => g z - g 0 - fderiv ℂ g 0 z) =O[𝓝 0] fun z => ‖z‖ ^ 2 := by
  obtain ⟨p, hp⟩ := hg
  have h := hp.isBigO_sub_partialSum_pow 2
  rw [hp.hasFDerivAt.fderiv]
  refine h.congr_left fun z => ?_
  have e1 : (p 1 fun _ => z) = p 1 ![z] := by
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, hp.coeff_zero, e1]
  try ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

variable {n : ℕ}

theorem comp_O (L : V n ≃L[ℂ] V n) (k : Fin n) :
    (fun z : V n => (L z) k) =O[𝓝 0] fun z => ‖z‖ := by
  have h1 : (fun z : V n => L z) =O[𝓝 0] fun z => z := (L : V n →L[ℂ] V n).isBigO_id _
  have h2 : (fun z : V n => (L z) k) =O[𝓝 0] fun z => L z := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun z => ?_)
    rw [one_mul]
    first
      | exact norm_le_pi_norm (L z) k
      | exact PiLp.norm_apply_le (L z) k
      | simpa using norm_le_pi_norm (L z) k
  exact (h2.trans h1).trans (isBigO_norm_right.mpr (isBigO_refl _ _))

theorem sub_val_O {g : V n → ℂ} (hg : AnalyticAt ℂ g 0) :
    (fun z => g 0 - g z) =O[𝓝 0] fun z => ‖z‖ ^ 1 := by
  have h := hg.differentiableAt.hasFDerivAt.isBigO_sub
  simp only [sub_zero] at h
  have h2 := h.neg_left
  simp only [neg_sub] at h2
  simp only [pow_one]
  exact h2.trans (isBigO_norm_right.mpr (isBigO_refl _ _))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder

noncomputable section

def nD (f p q : ℕ) : ℕ := f * (p * q)

def Zof {f p q : ℕ} (v : V (nD f p q)) (k : Fin f) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun a b => v (finProdFinEquiv (k, finProdFinEquiv (a, b)))

def Dset (f p q : ℕ) : Set (V (nD f p q)) :=
  {v | ∀ k, (1 - Zof v k * (Zof v k)ᴴ).PosDef}

def rh {f p q : ℕ} (v : V (nD f p q)) : ℝ :=
  -∑ k, Real.log (1 - Zof v k * (Zof v k)ᴴ).det.re

def RhGradStatement : Prop :=
  ∀ f p q : ℕ, ∀ v ∈ Dset f p q, ∀ ξ : Fin (nD f p q) → ℂ,
    Complex.normSq (∑ j, wd (nD f p q) j (fun w => ((rh w : ℝ) : ℂ)) v * ξ j) ≤
      ((f * min p q : ℕ) : ℝ) * (leviV (nD f p q) (fun w => ((rh w : ℝ) : ℂ)) v ξ).re

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace BigA

open Complex Matrix ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

theorem projPerp_self {N : ℕ} (g0 : Fin N → ℂ) (h : g0 ≠ 0) : projPerp g0 *ᵥ g0 = 0 := by
  have hs : (sqNorm g0 : ℂ) ≠ 0 := by
    exact_mod_cast (sqNorm_pos h).ne'
  have e : star g0 ⬝ᵥ g0 = (sqNorm g0 : ℂ) := by
    simp [sqNorm, dotProduct, Complex.normSq_eq_conj_mul_self]
  funext i
  simp only [projPerp, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul]
  rw [show (vecMulVec g0 (star g0) *ᵥ g0) i = g0 i * (star g0 ⬝ᵥ g0) by
    simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_assoc], e]
  field_simp
  ring

end BigA

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {n : ℕ}

abbrev lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Matrix (Fin i) (Fin i) ℂ :=
  M.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)

theorem det_lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (lb M i).det = lminor M (Fin.castSucc i) := rfl

def wv (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Fin i → ℂ :=
  vecMul (fun j : Fin i => M i (Fin.castLE i.isLt.le j)) (lb M i)⁻¹

def Lm (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => if h : (k : ℕ) < i then -wv M i ⟨k, h⟩ else if k = i then 1 else 0

theorem row_expand (N M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1) :
    (N * M) i j = (∑ k : Fin i, N i (Fin.castLE i.isLt.le k) * M (Fin.castLE i.isLt.le k) j) + M i j := by
  classical
  rw [Matrix.mul_apply]
  have h1 : ∑ k : Fin n, N i k * M k j = ∑ k ∈ Finset.univ.filter (fun k => k ≤ i), N i k * M k j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rfl
    · rw [hup k (lt_of_not_ge hk), zero_mul]
  have h2 : Finset.univ.filter (fun k : Fin n => k ≤ i) = insert i (Finset.univ.filter (fun k => k < i)) := by
    ext k
    simp [le_iff_lt_or_eq, or_comm]
  have h3 : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < i), N i k * M k j =
      ∑ k : Fin i, N i (Fin.castLE i.isLt.le k) * M (Fin.castLE i.isLt.le k) j := by
    refine Finset.sum_bij' (fun k hk => (⟨k, (Finset.mem_filter.mp hk).2⟩ : Fin i))
      (fun k _ => Fin.castLE i.isLt.le k) (fun _ _ => Finset.mem_univ _) (fun k _ => ?_)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact k.isLt
  rw [h1, h2, Finset.sum_insert (by simp), h3, hd, one_mul, add_comm]

theorem Lm_up (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) (h : i < k) : Lm M i k = 0 := by
  simp only [Lm, Matrix.of_apply]
  have h' : ¬ ((k : ℕ) < i) := by rw [Fin.lt_iff_val_lt_val] at h; omega
  rw [dite_eq_right h', if_neg (ne_of_gt h)]

theorem Lm_diag (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Lm M i i = 1 := by
  simp [Lm]

theorem Lm_det (M : Matrix (Fin n) (Fin n) ℂ) : (Lm M).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i k h => Lm_up M i k (OrderDual.toDual_lt_toDual.mp h))]
  simp [Lm_diag]

theorem row_sys (N M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1)
    (hz : ∀ j : Fin n, j < i → (N * M) i j = 0) :
    vecMul (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) (lb M i) =
      -fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
  funext j'
  have hrow := row_expand N M i (Fin.castLE i.isLt.le j') hup hd
  rw [hz _ (by simp [Fin.lt_iff_val_lt_val])] at hrow
  simp only [vecMul, dotProduct, lb, submatrix_apply, Pi.neg_apply]
  linear_combination (-1 : ℂ) * hrow

theorem Lm_mul_up (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (i j : Fin n) (h : j < i) : (Lm M * M) i j = 0 := by
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  rw [row_expand (Lm M) M i j (fun k hk => Lm_up M i k hk) (Lm_diag M i)]
  have hL : ∀ k : Fin i, Lm M i (Fin.castLE i.isLt.le k) = -wv M i k := by
    intro k
    simp only [Lm, Matrix.of_apply]
    rw [dite_eq_left (by simp)]
    rfl
  simp_rw [hL]
  have key : vecMul (wv M i) (lb M i) = fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
    rw [wv, vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, vecMul_one]
  have hk := congrFun key ⟨j, h⟩
  simp only [vecMul, dotProduct, lb, submatrix_apply] at hk
  have hk' : ∑ k : Fin i, wv M i k * M (Fin.castLE i.isLt.le k) j = M i j := hk
  simp only [neg_mul, Finset.sum_neg_distrib, hk', neg_add_cancel]

theorem Lm_unique (N M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (hup : ∀ i k : Fin n, i < k → N i k = 0) (hd : ∀ i, N i i = 1)
    (hz : ∀ i j : Fin n, j < i → (N * M) i j = 0) : N = Lm M := by
  ext i k
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  have h1 := row_sys N M i (hup i) (hd i) (hz i)
  have h2 := row_sys (Lm M) M i (fun k hk => Lm_up M i k hk) (Lm_diag M i)
    (fun j hj => Lm_mul_up M hM i j hj)
  have heq : (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) = fun k => Lm M i (Fin.castLE i.isLt.le k) := by
    have h3 := congrArg (fun v => vecMul v (lb M i)⁻¹) (h1.trans h2.symm)
    simpa only [vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, vecMul_one] using h3
  rcases lt_trichotomy k i with hk | rfl | hk
  · exact congrFun heq ⟨k, hk⟩
  · rw [hd, Lm_diag]
  · rw [hup i k hk, Lm_up M i k hk]

theorem lminor_nb (N B : Matrix (Fin n) (Fin n) ℂ) (hup : ∀ i k : Fin n, i < k → N i k = 0)
    (hd : ∀ i, N i i = 1) (hB : B.BlockTriangular id) (k : Fin (n + 1)) :
    lminor (N * B) k = ∏ j : Fin k, B (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
  set e : Fin k → Fin n := Fin.castLE (Nat.le_of_lt_succ k.isLt) with he
  have hmono : ∀ a b : Fin k, a < b → e a < e b := fun a b h => h
  have hsub : (N * B).submatrix e e = N.submatrix e e * B.submatrix e e := by
    ext a b
    simp only [submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective e (Fin.castLE_injective _) _ _ (fun c hc => ?_) (fun _ => rfl)
    have hc' : (k : ℕ) ≤ c := by
      by_contra hlt
      exact hc ⟨⟨c, by omega⟩, Fin.ext rfl⟩
    have hac : e a < c := by
      rw [Fin.lt_iff_val_lt_val]
      show (a : ℕ) < c
      omega
    rw [hup _ _ hac, zero_mul]
  have hNt : (N.submatrix e e).BlockTriangular OrderDual.toDual :=
    fun a b h => hup _ _ (hmono _ _ (OrderDual.toDual_lt_toDual.mp h))
  have hBt : (B.submatrix e e).BlockTriangular id := fun a b h => hB (hmono _ _ h)
  rw [lminor, ← he, hsub, det_mul, Matrix.det_of_lowerTriangular _ hNt,
    Matrix.det_of_upperTriangular hBt]
  simp [hd]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
end
