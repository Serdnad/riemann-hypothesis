module

public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.Params
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def iotaC (R : Type) [CommRing R] (n k : ℕ) (Y : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + k)) (Fin (n + k)) R :=
  Matrix.reindexAlgEquiv R R finSumFinEquiv (Matrix.fromBlocks Y 0 0 1)

theorem iotaC_mul (R : Type) [CommRing R] (n k : ℕ) (A B : Matrix (Fin n) (Fin n) R) :
    iotaC R n k (A * B) = iotaC R n k A * iotaC R n k B := by
  rw [iotaC, iotaC, iotaC, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem iotaC_one (R : Type) [CommRing R] (n k : ℕ) : iotaC R n k 1 = 1 := by
  rw [iotaC, Matrix.fromBlocks_one, map_one]

theorem iotaC_map (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (n k : ℕ)
    (Y : Matrix (Fin n) (Fin n) R) : (iotaC R n k Y).map φ = iotaC S n k (Y.map φ) := by
  ext i j
  simp only [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

theorem iotaC_conj (n k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    iotaC ℂ n k Y.conjTranspose = (iotaC ℂ n k Y).conjTranspose := by
  ext i j
  simp only [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, Matrix.conjTranspose_apply, apply_ite, eq_comm]

theorem iotaC_det (n k : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) : (iotaC ℂ n k Y).det = Y.det := by
  rw [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

theorem iotaC_zero (R : Type) [CommRing R] (n : ℕ) (Y : Matrix (Fin n) (Fin n) R) :
    iotaC R n 0 Y = Y := by
  have hi : ∀ i : Fin (n + 0), finSumFinEquiv.symm i = Sum.inl i := fun i => by
    rw [Equiv.symm_apply_eq]; rfl
  ext i j
  simp [iotaC, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply, hi]

open Formalism.REAL (fockF)

def fct {σ : Type} (m : σ →₀ ℕ) : ℂ := ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ)

theorem fockF_eq_sum {σ : Type} (p q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ))
    (hs : ∀ m, p.coeff m ≠ 0 → q.coeff m ≠ 0 → m ∈ s) :
    fockF p q = ∑ m ∈ s, p.coeff m * star (q.coeff m) * fct m := by
  classical
  trans ∑ m ∈ p.support ∩ s, p.coeff m * star (q.coeff m) * fct m
  · unfold fockF fct
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro m hm hms
    by_cases hq : q.coeff m = 0
    · simp [hq]
    · exact absurd (Finset.mem_inter.mpr ⟨hm, hs m (MvPolynomial.mem_support_iff.mp hm) hq⟩) hms
  · apply Finset.sum_subset Finset.inter_subset_right
    intro m hm hms
    by_cases hp : p.coeff m = 0
    · simp [hp]
    · exact absurd (Finset.mem_inter.mpr ⟨MvPolynomial.mem_support_iff.mpr hp, hm⟩) hms

theorem fockF_add_left {σ : Type} (p p' q : MvPolynomial σ ℂ) :
    fockF (p + p') q = fockF p q + fockF p' q := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ, r.support ⊆ p.support ∪ p'.support →
      fockF r q = ∑ m ∈ p.support ∪ p'.support, r.coeff m * star (q.coeff m) * fct m :=
    fun r hr => fockF_eq_sum r q _ (fun m h1 _ => hr (MvPolynomial.mem_support_iff.mpr h1))
  rw [hs (p + p') MvPolynomial.support_add, hs p Finset.subset_union_left,
    hs p' Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fockF_smul_left {σ : Type} (c : ℂ) (p q : MvPolynomial σ ℂ) :
    fockF (c • p) q = c * fockF p q := by
  classical
  rw [fockF_eq_sum (c • p) q p.support (fun m h _ => by
        rw [MvPolynomial.coeff_smul, smul_eq_mul] at h
        exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul h)),
    fockF_eq_sum p q p.support (fun m h _ => MvPolynomial.mem_support_iff.mpr h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fockF_zero_left {σ : Type} (q : MvPolynomial σ ℂ) : fockF 0 q = 0 := by
  simp [fockF]

theorem fockF_add_right {σ : Type} (p q q' : MvPolynomial σ ℂ) :
    fockF p (q + q') = fockF p q + fockF p q' := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ,
      fockF p r = ∑ m ∈ p.support, p.coeff m * star (r.coeff m) * fct m :=
    fun r => fockF_eq_sum p r _ (fun m h1 _ => MvPolynomial.mem_support_iff.mpr h1)
  rw [hs, hs, hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

theorem fockF_smul_right {σ : Type} (c : ℂ) (p q : MvPolynomial σ ℂ) :
    fockF p (c • q) = star c * fockF p q := by
  classical
  have hs : ∀ r : MvPolynomial σ ℂ,
      fockF p r = ∑ m ∈ p.support, p.coeff m * star (r.coeff m) * fct m :=
    fun r => fockF_eq_sum p r _ (fun m h1 _ => MvPolynomial.mem_support_iff.mpr h1)
  rw [hs, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem fockF_sum_left {σ ι : Type} (s : Finset ι) (x : ι → MvPolynomial σ ℂ) (q : MvPolynomial σ ℂ) :
    fockF (∑ i ∈ s, x i) q = ∑ i ∈ s, fockF (x i) q := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [fockF]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_left, ih]

theorem fockF_sum_right {σ ι : Type} (s : Finset ι) (x : ι → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ) :
    fockF p (∑ i ∈ s, x i) = ∑ i ∈ s, fockF p (x i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [fockF]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_right, ih]

theorem fockF_lc {σ ι : Type} (s : Finset ι) (a : ι → ℂ) (x : ι → MvPolynomial σ ℂ) :
    fockF (∑ i ∈ s, a i • x i) (∑ j ∈ s, a j • x j) =
      ∑ i ∈ s, ∑ j ∈ s, a i * star (a j) * fockF (x i) (x j) := by
  rw [fockF_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fockF_smul_left, fockF_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fockF_smul_right]
  ring

private theorem eq_zero_of_fockF_self_eq_zero {σ : Type} (p : MvPolynomial σ ℂ) (h : fockF p p = 0) : p = 0 := by
  classical
  by_contra hp
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hp)
  have hre : (fockF p p).re =
      ∑ m ∈ p.support, Complex.normSq (p.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) := by
    unfold fockF
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    show (p.coeff m * (starRingEnd ℂ) (p.coeff m) * _).re = _
    rw [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpos : 0 < ∑ m ∈ p.support, Complex.normSq (p.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) :=
    Finset.sum_pos (fun m hm => mul_pos (Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hm))
      (Nat.cast_pos.mpr (Finset.prod_pos fun k _ => Nat.factorial_pos _))) ⟨m, hm⟩
  rw [← hre, h, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

theorem lc_zero_of_gram {σ τ ι : Type} (s : Finset ι) (a : ι → ℂ) (xe : ι → MvPolynomial σ ℂ)
    (xf : ι → MvPolynomial τ ℂ) (K : ℂ)
    (hK : ∀ i j, fockF (xf i) (xf j) = K * fockF (xe i) (xe j))
    (h0 : ∑ i ∈ s, a i • xe i = 0) : ∑ i ∈ s, a i • xf i = 0 := by
  have hyy : fockF (∑ i ∈ s, a i • xf i) (∑ i ∈ s, a i • xf i) = 0 := by
    have he := fockF_lc s a xe
    rw [h0, fockF_zero_left] at he
    rw [fockF_lc]
    simp_rw [hK]
    calc _ = K * ∑ i ∈ s, ∑ j ∈ s, a i * star (a j) * fockF (xe i) (xe j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [← he, mul_zero]
  exact eq_zero_of_fockF_self_eq_zero _ hyy

theorem fockF_rowAct_right (r n : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) (p q : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF p (rowAct ℂ M q) = fockF (rowAct ℂ M.conjTranspose p) q := by
  rw [fockRowAdj r n M.conjTranspose p q, Matrix.conjTranspose_conjTranspose]

end PI.WGB
end
end

section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

private theorem fockF_eq_sum_lemma {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

theorem fockF_smul_left_B {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) g = c * Formalism.REAL.fockF f g := by
  rw [fockF_eq_sum_lemma (c • f) g f.support MvPolynomial.support_smul]
  unfold Formalism.REAL.fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fockF_smul_right_B {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (c • g) = star c * Formalism.REAL.fockF f g := by
  unfold Formalism.REAL.fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem fockF_add_left_B {σ : Type} [DecidableEq σ] (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  rw [fockF_eq_sum_lemma (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fockF_eq_sum_lemma f g (f.support ∪ f'.support) Finset.subset_union_left,
    fockF_eq_sum_lemma f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fockF_self_re_nonneg_B {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ (Formalism.REAL.fockF f f).re := by
  unfold Formalism.REAL.fockF
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun m _ => ?_
  rw [show star (f.coeff m) = (starRingEnd ℂ) (f.coeff m) from rfl, Complex.mul_conj,
    Complex.re_ofReal_mul, Complex.natCast_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

def coreB {N : ℕ} (lam : DomWeight N) : InnerProductSpace.Core ℂ (nablaSq ℂ N lam) where
  inner x y := Formalism.REAL.fockF (y : MvPolynomial (Fin N × Fin N) ℂ) x
  conj_inner_symm x y := by
    show starRingEnd ℂ (Formalism.REAL.fockF (x : MvPolynomial (Fin N × Fin N) ℂ) y) =
      Formalism.REAL.fockF (y : MvPolynomial (Fin N × Fin N) ℂ) x
    rw [starRingEnd_apply, ← Formalism.GradedWeylDivisibility.fockHerm]
  re_inner_nonneg x := fockF_self_re_nonneg_B (x : MvPolynomial (Fin N × Fin N) ℂ)
  add_left x y z := by
    show Formalism.REAL.fockF (z : MvPolynomial (Fin N × Fin N) ℂ)
      ((x + y : nablaSq ℂ N lam) : MvPolynomial (Fin N × Fin N) ℂ) = _
    rw [Submodule.coe_add, Formalism.GradedWeylDivisibility.fockHerm, fockF_add_left_B, star_add, ← Formalism.GradedWeylDivisibility.fockHerm,
      ← Formalism.GradedWeylDivisibility.fockHerm]
  smul_left x y r := by
    show Formalism.REAL.fockF (y : MvPolynomial (Fin N × Fin N) ℂ)
      ((r • x : nablaSq ℂ N lam) : MvPolynomial (Fin N × Fin N) ℂ) = _
    rw [Submodule.coe_smul, fockF_smul_right_B, starRingEnd_apply]
  definite x hx := by
    apply Subtype.ext
    by_contra hne
    have := (Formalism.GradedWeylDivisibility.fockPos _ (x : MvPolynomial (Fin N × Fin N) ℂ) hne).1
    have hx' : Formalism.REAL.fockF (x : MvPolynomial (Fin N × Fin N) ℂ) x = 0 := hx
    rw [hx'] at this; simp at this

theorem dualWeyl_le_homog_B (r n : ℕ) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl ℂ r n ν ≤ homogeneousSubmodule (Fin r × Fin n) ℂ (∑ s, ν s) := by
  intro f hf
  have hw := (Submodule.mem_inf.mp hf).1
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hw
  rw [MvPolynomial.mem_homogeneousSubmodule]
  intro d hd
  have h1 := hw hd
  rw [← h1]
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  simp

theorem fd_B (N : ℕ) (lam : DomWeight N) : FiniteDimensional ℂ (nablaSq ℂ N lam) := by
  have hle := dualWeyl_le_homog_B N N lam.natW
  have hfin : {d : (Fin N × Fin N) →₀ ℕ | d.degree = ∑ s, lam.natW s}.Finite := by
    refine (Finset.finsuppAntidiag Finset.univ (∑ s, lam.natW s)).finite_toSet.subset fun d hd => ?_
    rw [Finset.mem_coe, Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    rw [← hd, Finsupp.degree_eq_sum]
  have hsub : homogeneousSubmodule (Fin N × Fin N) ℂ (∑ s, lam.natW s) ≤
      Submodule.span ℂ ((fun d => (MvPolynomial.monomial d (1 : ℂ))) ''
        {d : (Fin N × Fin N) →₀ ℕ | d.degree = ∑ s, lam.natW s}) := by
    intro f hf
    rw [MvPolynomial.mem_homogeneousSubmodule] at hf
    rw [f.as_sum]
    refine Submodule.sum_mem _ fun d hd => ?_
    have hdeg : d.degree = ∑ s, lam.natW s := by
      have h2 := hf (MvPolynomial.mem_support_iff.mp hd)
      rw [Finsupp.degree_eq_weight_one]
      exact h2
    rw [show MvPolynomial.monomial d (f.coeff d) = f.coeff d • MvPolynomial.monomial d (1 : ℂ) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hdeg, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ ((fun d => (MvPolynomial.monomial d (1 : ℂ))) ''
      {d : (Fin N × Fin N) →₀ ℕ | d.degree = ∑ s, lam.natW s})) :=
    FiniteDimensional.span_of_finite ℂ (hfin.image _)
  exact Submodule.finiteDimensional_of_le (hle.trans hsub)

def gStarB {N : ℕ} (g : GL (Fin N) ℂ) : GL (Fin N) ℂ where
  val := Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ)
  inv := Matrix.conjTranspose ((g⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  val_inv := by rw [← Matrix.conjTranspose_mul]; simp
  inv_val := by rw [← Matrix.conjTranspose_mul]; simp

theorem gStarB_val {N : ℕ} (g : GL (Fin N) ℂ) :
    ((gStarB g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ) := rfl

theorem embGL_gStarB {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    embGL ℂ n N h (gStarB g) = gStarB (embGL ℂ n N h g) := by
  apply Units.ext
  simp only [embGL, Units.coe_map, gStarB_val, MonoidHom.comp_apply]
  simp [blkHom, Matrix.fromBlocks_conjTranspose]

theorem detPow_gStarB {N : ℕ} (g : GL (Fin N) ℂ) (k : ℤ) :
    detPow ℂ N (gStarB g) k = star (detPow ℂ N g k) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply, gStarB_val, Matrix.det_conjTranspose, star_zpow₀]

theorem sqAct_mem_B {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ nablaSq ℂ N lam) : sqAct ℂ N lam g f ∈ nablaSq ℂ N lam := by
  unfold sqAct
  exact (nablaSq ℂ N lam).smul_mem _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)

theorem fock_sqAct_adj_B {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.REAL.fockF (sqAct ℂ N lam g x) y = Formalism.REAL.fockF x (sqAct ℂ N lam (gStarB g) y) := by
  unfold sqAct
  rw [fockF_smul_left_B, fockF_smul_right_B, detPow_gStarB, star_star, Formalism.GradedWeylDivisibility.fockRowAdj]
  congr 2

theorem stableCompl_B : StableCompl := by
  intro n N h lam W hW hstab
  classical
  let W' : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
    { carrier := {f | f ∈ nablaSq ℂ N lam ∧ ∀ w ∈ W, Formalism.REAL.fockF f w = 0}
      add_mem' := fun {a b} ha hb => ⟨(nablaSq ℂ N lam).add_mem ha.1 hb.1, fun w hw => by
        rw [fockF_add_left_B, ha.2 w hw, hb.2 w hw, add_zero]⟩
      zero_mem' := ⟨(nablaSq ℂ N lam).zero_mem, fun w _ => by simp [Formalism.REAL.fockF]⟩
      smul_mem' := fun c a ha => ⟨(nablaSq ℂ N lam).smul_mem c ha.1, fun w hw => by
        rw [fockF_smul_left_B, ha.2 w hw, mul_zero]⟩ }
  have hW'V : W' ≤ nablaSq ℂ N lam := fun f hf => hf.1
  refine ⟨W', hW'V, ?_, ?_, ?_⟩
  · intro g f hf
    refine ⟨sqAct_mem_B lam _ f hf.1, fun w hw => ?_⟩
    rw [fock_sqAct_adj_B, ← embGL_gStarB]
    exact hf.2 _ (hstab (gStarB g) w hw)
  · apply le_antisymm (sup_le hW hW'V)
    intro f hf
    letI := coreB lam
    letI : NormedAddCommGroup (nablaSq ℂ N lam) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    letI : InnerProductSpace ℂ (nablaSq ℂ N lam) := InnerProductSpace.ofCore (coreB lam).toCore
    haveI : FiniteDimensional ℂ (nablaSq ℂ N lam) := fd_B N lam
    let K : Submodule ℂ (nablaSq ℂ N lam) := W.comap (nablaSq ℂ N lam).subtype
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq K K.orthogonal
    rw [Submodule.inf_orthogonal_eq_bot, finrank_bot, add_zero, Submodule.finrank_add_finrank_orthogonal] at h1
    have hs : K ⊔ K.orthogonal = ⊤ := Submodule.eq_top_of_finrank_eq h1
    have hmem : (⟨f, hf⟩ : nablaSq ℂ N lam) ∈ K ⊔ K.orthogonal := by
      rw [hs]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    rw [Submodule.mem_sup]
    refine ⟨(a : MvPolynomial (Fin N × Fin N) ℂ), ha, (b : MvPolynomial (Fin N × Fin N) ℂ),
      ⟨b.2, fun w hw => ?_⟩, ?_⟩
    · exact (Submodule.mem_orthogonal K b).mp hb ⟨w, hW hw⟩ hw
    · have hv := congrArg Subtype.val hab
      simpa using hv
  · rw [eq_bot_iff]
    intro f hf
    obtain ⟨hfW, hfW'⟩ := Submodule.mem_inf.mp hf
    have h0 : Formalism.REAL.fockF f f = 0 := hfW'.2 f hfW
    rw [Submodule.mem_bot]
    by_contra hne
    have hpos := (Formalism.GradedWeylDivisibility.fockPos _ f hne).1
    rw [h0] at hpos
    simp at hpos

end PI.WGB
end
end
