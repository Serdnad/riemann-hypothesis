module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle003
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private lemma tele_range (D : ℕ → ℂ) (hD : ∀ l, D l ≠ 0) (m : ℕ → ℤ) (N : ℕ) :
    ∏ i ∈ range N, (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1))) =
      (∏ l ∈ range N, D l ^ (-m l)) * (∏ l ∈ range N, D l) ^ m N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ (fun i => (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1)))) N, ih]
    simp only [Finset.prod_range_succ]
    have hP : (∏ l ∈ range N, D l) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hD l
    have hPd : (∏ l ∈ range N, D l) * D N ≠ 0 := mul_ne_zero hP (hD N)
    have h1 : ((∏ l ∈ range N, D l) * D N) ^ (-(m N - m (N + 1))) =
        ((∏ l ∈ range N, D l) * D N) ^ (-m N) * ((∏ l ∈ range N, D l) * D N) ^ (m (N + 1)) := by
      rw [← zpow_add₀ hPd]
      congr 1
      ring
    have h2 : ((∏ l ∈ range N, D l) * D N) ^ (-m N) =
        (∏ l ∈ range N, D l) ^ (-m N) * D N ^ (-m N) := mul_zpow _ _ _
    have h3 : (∏ l ∈ range N, D l) ^ m N * (∏ l ∈ range N, D l) ^ (-m N) = 1 := by
      rw [← zpow_add₀ hP, add_neg_cancel, zpow_zero]
    rw [h1, h2]
    linear_combination ((∏ l ∈ range N, D l ^ (-m l)) * D N ^ (-m N) *
      ((∏ l ∈ range N, D l) * D N) ^ m (N + 1)) * h3

private lemma filter_prod_eq_range (d : Fin n → ℂ) (k : ℕ) (hk : k ≤ n) :
    ∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < k), d l =
      ∏ j ∈ range k, (if h : j < n then d ⟨j, h⟩ else 1) := by
  have hr : range k = (range n).filter (fun j => j < k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> intro h <;> omega
  rw [hr]
  simp only [Finset.prod_filter]
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [l.2]

private lemma tele_fin (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (μ : Fin n → ℤ) :
    ∏ i : Fin n, (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), d l) ^ (-(μ i - muNext μ i)) =
      ∏ l, d l ^ (-μ l) := by
  set D : ℕ → ℂ := fun j => if h : j < n then d ⟨j, h⟩ else 1 with hDdef
  set m : ℕ → ℤ := fun j => if h : j < n then μ ⟨j, h⟩ else 0 with hmdef
  have hD : ∀ l, D l ≠ 0 := by
    intro l
    simp only [hDdef]
    split_ifs
    · exact hd _
    · exact one_ne_zero
  have h1 : ∀ i : Fin n, (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), d l) ^
      (-(μ i - muNext μ i)) = (∏ l ∈ range ((i : ℕ) + 1), D l) ^ (-(m i - m ((i : ℕ) + 1))) := by
    intro i
    rw [filter_prod_eq_range d _ (by have := i.2; omega)]
    congr 1
    all_goals first | rfl | simp [hmdef, muNext, i.2]
  rw [Finset.prod_congr rfl (fun i _ => h1 i),
    Fin.prod_univ_eq_prod_range (fun i => (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1)))) n,
    tele_range D hD m n]
  have hmn : m n = 0 := by simp [hmdef]
  rw [hmn, zpow_zero, mul_one, Finset.prod_range (fun l => D l ^ (-m l))]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [hDdef, hmdef, l.2]

private lemma lead_differentiable_lemma (i : ℕ) :
    Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) := by
  unfold lead
  split_ifs with h
  · simp only [Matrix.det_apply', Matrix.submatrix_apply]
    fun_prop
  · exact differentiable_const _

theorem isOpen_omega : IsOpen (OmegaSet n) := by
  have : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (lead_differentiable_lemma _).continuous continuous_const

theorem posSet_subset_omega : posSet n ⊆ OmegaSet n := by
  intro x hx i h
  have := (lead_posDef hx ((i : ℕ) + 1) (by have := i.2; omega)).1
  rw [h] at this
  simp at this

theorem phiM_differentiableOn (μ : Fin n → ℤ) : DifferentiableOn ℂ (PhiM μ) (OmegaSet n) := by
  intro z hz
  have hz' : ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0 := hz
  have hL : ∀ i : ℕ, Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) :=
    fun i => lead_differentiable_lemma i
  have hq : DifferentiableAt ℂ (PhiM μ) z := by
    unfold PhiM
    fun_prop (disch := exact Or.inl (hz' _))
  exact hq.differentiableWithinAt

theorem phiM_tri_mul (μ : Fin n → ℤ) {c z c' : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) (hc' : IsUpperTri c')
    (hcd : ∀ l, c l l ≠ 0) (hcd' : ∀ l, c' l l ≠ 0) (hz : z ∈ OmegaSet n) :
    c * z * c' ∈ OmegaSet n ∧
      PhiM μ (c * z * c') = (∏ l, (c l l * c' l l) ^ (-μ l)) * PhiM μ z := by
  have hd : ∀ l, c l l * c' l l ≠ 0 := fun l => mul_ne_zero (hcd l) (hcd' l)
  have hlead : ∀ i : Fin n, lead ((i : ℕ) + 1) (c * z * c') =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) * lead ((i : ℕ) + 1) z :=
    fun i => lead_tri_mul hc hc' _ i.isLt
  have hP : ∀ i : Fin n,
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) ≠ 0 :=
    fun i => prod_ne_zero_iff.mpr fun l _ => hd l
  refine ⟨fun i => by rw [hlead i]; exact mul_ne_zero (hP i) (hz i), ?_⟩
  have hterm : ∀ i : Fin n, lead ((i : ℕ) + 1) (c * z * c') ^ (-(μ i - muNext μ i)) =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) ^ (-(μ i - muNext μ i)) *
        lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i)) := fun i => by rw [hlead i, mul_zpow]
  unfold PhiM
  rw [prod_congr rfl fun i _ => hterm i, prod_mul_distrib,
    tele_fin (fun l => c l l * c' l l) hd μ]

theorem phiM_posDef (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    0 < (PhiM μ x).re ∧ (PhiM μ x).im = 0 := by
  have hpos : ∀ i : Fin n, 0 < (lead ((i : ℕ) + 1) x).re :=
    fun i => (lead_posDef hx _ (by have := i.2; omega)).1
  have hr : ∀ i : Fin n, lead ((i : ℕ) + 1) x = ((lead ((i : ℕ) + 1) x).re : ℂ) := by
    intro i
    apply Complex.ext
    · simp
    · simp [(lead_posDef hx ((i : ℕ) + 1) (by have := i.2; omega)).2]
  have hP : PhiM μ x = ((∏ i : Fin n, (lead ((i : ℕ) + 1) x).re ^ (-(μ i - muNext μ i)) : ℝ) : ℂ) := by
    unfold PhiM
    push_cast
    exact Finset.prod_congr rfl fun i _ => by rw [← hr i]
  rw [hP, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.prod_pos fun i _ => zpow_pos (hpos i) _, rfl⟩

theorem phiM_one (μ : Fin n → ℤ) : PhiM μ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold PhiM
  have h1 : ∀ i : Fin n, lead ((i : ℕ) + 1) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    intro i
    unfold lead
    rw [dite_eq_left (by have := i.2; omega), Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
  simp [h1]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dmW (U : Matrix (Fin n) (Fin n) ℂ) {i : ℕ} (hi : i ≤ n) (J : {J : Finset (Fin n) // J.card = i}) : ℝ :=
  ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2

def dmChi (i : ℕ) (a : Fin n) : ℂ := if (a : ℕ) < i then 1 else 0

def dmK (U : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) (k l : Fin n) : ℂ :=
  ∑ a, dmChi i a * (star (U a k) * U a l)

def dmInd (J : Finset (Fin n)) (k : Fin n) : ℂ := if k ∈ J then 1 else 0

lemma dm_sum_castLE {i : ℕ} (hi : i ≤ n) (f : Fin n → ℂ) :
    ∑ a : Fin i, f (Fin.castLE hi a) = ∑ a : Fin n, dmChi i a * f a := by
  simp only [dmChi, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => Fin.castLE hi a) ?_ ?_ ?_ ?_
  · intro a _
    simp [Finset.mem_filter, a.isLt]
  · intro a _ b _ h
    exact Fin.castLE_injective hi h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ⟨⟨b, hb⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro a _
    rfl

lemma dm_entry (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (a b : Fin n) :
    (U * Matrix.diagonal d * Uᴴ) a b = ∑ j, U a j * d j * star (U b j) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

lemma dm_UUh {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : U * Uᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU

lemma dm_UhU {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : Uᴴ * U = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU

lemma dm_unit {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (a b : Fin n) :
    ∑ j, U a j * star (U b j) = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  have h := congrFun (congrFun (dm_UUh hU) a) b
  rw [Matrix.mul_apply] at h
  simpa only [Matrix.conjTranspose_apply] using h

lemma dm_one_sub {i : ℕ} (hi : i ≤ n) (a b : Fin i) :
    (1 : Matrix (Fin n) (Fin n) ℂ) (Fin.castLE hi a) (Fin.castLE hi b) = (1 : Matrix (Fin i) (Fin i) ℂ) a b := by
  by_cases h : a = b
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    exact fun e => h (Fin.castLE_injective hi e)

lemma dm_normsq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma dm_mass {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) = 1 := by
  have h := lead_unitary_diag (U := U) (fun _ => (1 : ℂ)) i hi
  simp only [Finset.prod_const_one, mul_one] at h
  simp only [dmW]
  rw [← h, lead, dite_eq_left hi, Matrix.diagonal_one, Matrix.mul_one, dm_UUh hU]
  have h2 : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi) (Fin.castLE hi) = 1 := by
    ext a b; rw [Matrix.submatrix_apply, dm_one_sub]
  rw [h2, Matrix.det_one]

lemma sum_minorWeights_indicator {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n)
    (k : Fin n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * dmInd J.1 k = dmK U i k k := by
  have h := lead_unitary_diag (U := U) (fun j => if j = k then (2 : ℂ) else 1) i hi
  have hprod : ∀ J : Finset (Fin n), ∏ j ∈ J, (if j = k then (2 : ℂ) else 1) = 1 + dmInd J k := by
    intro J; rw [Finset.prod_ite_eq']; unfold dmInd; split_ifs <;> norm_num
  simp only [hprod, mul_add, mul_one, Finset.sum_add_distrib] at h
  have hm := dm_mass hU hi
  simp only [dmW] at hm ⊢
  rw [hm] at h
  let v : Fin i → ℂ := fun a => U (Fin.castLE hi a) k
  have hsub : (U * Matrix.diagonal (fun j => if j = k then (2 : ℂ) else 1) * Uᴴ).submatrix
      (Fin.castLE hi) (Fin.castLE hi) = 1 + Matrix.replicateCol Unit v * Matrix.replicateRow Unit (star v) := by
    ext a b
    rw [Matrix.submatrix_apply, dm_entry]
    have hj : ∀ j, U (Fin.castLE hi a) j * (if j = k then (2 : ℂ) else 1) * star (U (Fin.castLE hi b) j)
        = U (Fin.castLE hi a) j * star (U (Fin.castLE hi b) j) +
          if k = j then U (Fin.castLE hi a) k * star (U (Fin.castLE hi b) k) else 0 := by
      intro j
      by_cases hjk : j = k
      · subst hjk; simp; ring
      · rw [if_neg hjk, if_neg (Ne.symm hjk)]; ring
    simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, dm_unit hU, dm_one_sub]
    simp [Matrix.mul_apply, v]
  rw [lead, dite_eq_left hi, hsub, Matrix.det_one_add_replicateCol_mul_replicateRow] at h
  have hdot : star v ⬝ᵥ v = dmK U i k k := by
    rw [dotProduct, dmK, ← dm_sum_castLE hi (fun a => star (U a k) * U a k)]
    rfl
  rw [hdot] at h
  linear_combination -h

lemma sum_minorWeights_indicator_pair {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n)
    (k l : Fin n) (hkl : k ≠ l) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) =
      dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k := by
  have h := lead_unitary_diag (U := U)
    (fun j => (if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) i hi
  have hprod : ∀ J : Finset (Fin n),
      ∏ j ∈ J, ((if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) =
        1 + dmInd J k + dmInd J l + dmInd J k * dmInd J l := by
    intro J
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    unfold dmInd; split_ifs <;> norm_num
  simp only [hprod, mul_add, mul_one, Finset.sum_add_distrib] at h
  have hm := dm_mass hU hi
  have h1 := sum_minorWeights_indicator hU hi k
  have h2 := sum_minorWeights_indicator hU hi l
  simp only [dmW] at hm h1 h2 ⊢
  rw [hm, h1, h2] at h
  let W : Matrix (Fin i) (Fin 2) ℂ :=
    Matrix.of fun a c => if c = 0 then U (Fin.castLE hi a) k else U (Fin.castLE hi a) l
  have hsub : (U * Matrix.diagonal (fun j => (if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1))
      * Uᴴ).submatrix (Fin.castLE hi) (Fin.castLE hi) = 1 + W * Wᴴ := by
    ext a b
    rw [Matrix.submatrix_apply, dm_entry]
    have hj : ∀ j, U (Fin.castLE hi a) j * ((if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1))
        * star (U (Fin.castLE hi b) j)
        = U (Fin.castLE hi a) j * star (U (Fin.castLE hi b) j) +
          ((if k = j then U (Fin.castLE hi a) k * star (U (Fin.castLE hi b) k) else 0) +
          (if l = j then U (Fin.castLE hi a) l * star (U (Fin.castLE hi b) l) else 0)) := by
      intro j
      by_cases hjk : j = k
      · have hjl : j ≠ l := hjk ▸ hkl
        rw [if_pos hjk, if_neg hjl, if_pos hjk.symm, if_neg (Ne.symm hjl), hjk]; ring
      · by_cases hjl : j = l
        · rw [if_neg hjk, if_pos hjl, if_neg (Ne.symm hjk), if_pos hjl.symm, hjl]; ring
        · rw [if_neg hjk, if_neg hjl, if_neg (Ne.symm hjk), if_neg (Ne.symm hjl)]; ring
    simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, dm_unit hU,
      dm_one_sub]
    simp [Matrix.mul_apply, W, Fin.sum_univ_two]
  have hK : ∀ c c' : Fin 2, (Wᴴ * W) c c' = dmK U i (![k, l] c) (![k, l] c') := by
    intro c c'
    rw [Matrix.mul_apply, dmK, ← dm_sum_castLE hi (fun a => star (U a (![k, l] c)) * U a (![k, l] c'))]
    refine Finset.sum_congr rfl fun a _ => ?_
    fin_cases c <;> fin_cases c' <;> simp [W]
  rw [lead, dite_eq_left hi, hsub, Matrix.det_one_add_mul_comm, Matrix.det_fin_two] at h
  simp only [Matrix.add_apply, hK, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_add] at h
  linear_combination -h

lemma dm_m {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n)
    (k l : Fin n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) =
      dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k + if k = l then dmK U i k k else 0 := by
  by_cases hkl : k = l
  · subst hkl
    have hsq : ∀ (m : Fin n) (J : Finset (Fin n)), dmInd J m * dmInd J m = dmInd J m := by
      intro m J
      unfold dmInd
      split_ifs <;> simp
    rw [if_pos rfl]
    simp only [hsq, sum_minorWeights_indicator hU hi]
    ring
  · rw [sum_minorWeights_indicator_pair hU hi k l hkl, if_neg hkl, add_zero]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
