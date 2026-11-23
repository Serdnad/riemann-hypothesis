module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle004
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle003
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle289
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

private theorem rowGen_eval_C_eq_rowAct_transvection {n n' : ℕ} (a b : Fin n') (t : ℂ)
    (f : MvPolynomial (Fin n' × Fin n) ℂ) :
    (rowGen ℂ a b f).eval (C t) = rowAct ℂ (Matrix.transvection a b t)ᵀ f := by
  have key : (Polynomial.evalRingHom (C t : MvPolynomial (Fin n' × Fin n) ℂ)).comp
      (rowGen ℂ (n := n) a b).toRingHom = (rowAct ℂ (n := n) (Matrix.transvection a b t)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen, rowAct]
    · rintro ⟨i, s⟩
      by_cases h : i = b
      · subst h
        simp [rowGen, rowAct, Matrix.transvection, Matrix.single, Matrix.one_apply, add_mul,
          Finset.sum_add_distrib, ite_and, add_comm]
        rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp), if_pos rfl, mul_comm]
      · simp [rowGen, rowAct, Matrix.transvection, Matrix.single, Matrix.one_apply, add_mul,
          Finset.sum_add_distrib, h, Ne.symm h]
  exact RingHom.congr_fun key f

theorem rowDiv_eq_zero_of_matRep_unipotent_fixed : ∀ (n n' : ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), (∀ g : GL (Fin n') ℂ, (g : Matrix (Fin n') (Fin n') ℂ).BlockTriangular id → (∀ a, (g : Matrix (Fin n') (Fin n') ℂ) a a = 1) → matRep n n' (1, g) v = v) → ∀ a b : Fin n', a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0 := by
  intro n n' v hv a b hab k hk
  have hroot : ∀ t : ℂ, (rowGen ℂ a b v).eval (C t) = v := by
    intro t
    rw [rowGen_eval_C_eq_rowAct_transvection]
    have hdet : IsUnit (Matrix.transvection a b t).det := by
      rw [Matrix.det_transvection_of_ne _ _ (ne_of_lt hab)]
      exact isUnit_one
    let g : GL (Fin n') ℂ := Matrix.nonsingInvUnit _ hdet
    have hgv : (g : Matrix (Fin n') (Fin n') ℂ) = Matrix.transvection a b t := rfl
    have hbt : (g : Matrix (Fin n') (Fin n') ℂ).BlockTriangular id := by
      intro i j hij
      have hne : i ≠ j := fun h => by simp [h] at hij
      have hne' : ¬(a = i ∧ b = j) := by
        rintro ⟨rfl, rfl⟩
        exact absurd (lt_trans hab hij) (lt_irrefl _)
      simp [hgv, Matrix.transvection, Matrix.single, hne, hne']
    have hdiag : ∀ i, (g : Matrix (Fin n') (Fin n') ℂ) i i = 1 := by
      intro i
      have hne' : ¬(a = i ∧ b = i) := by
        rintro ⟨rfl, rfl⟩
        exact lt_irrefl _ hab
      simp [hgv, Matrix.transvection, Matrix.single, hne']
    have hg := hv g hbt hdiag
    rw [matRep_one_left, hgv] at hg
    exact hg
  have hconst : rowGen ℂ a b v = Polynomial.C v := by
    rw [← sub_eq_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_
      (Set.infinite_range_of_injective (MvPolynomial.C_injective (Fin n' × Fin n) ℂ))
    rintro _ ⟨t, rfl⟩
    simp [Polynomial.IsRoot, hroot t]
  show (rowGen ℂ a b v).coeff k = 0
  rw [hconst, Polynomial.coeff_C, if_neg (by omega)]

end GlobalTheory.GLDuality
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem matRep_diagGL_monomial {n n' : ℕ} (t : Fin n → ℂˣ) (d : Fin n' × Fin n →₀ ℕ) (c : ℂ) :
    matRep n n' (diagGL ℂ n t, 1) (monomial d c) =
      (∏ s, (t s : ℂ) ^ (Finsupp.weight (colW n' n) d s)) • monomial d c := by
  have hX : ∀ v : Fin n' × Fin n, matRep n n' (diagGL ℂ n t, 1) (X v) = (t v.2 : ℂ) • X v := by
    rintro ⟨a, s⟩
    rw [matRep_X, Finset.sum_eq_single a, Finset.sum_eq_single s]
    · simp [diagGL, smul_eq_C_mul]
    · intro b _ hb
      simp [diagGL, hb]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  induction d using Finsupp.induction_linear generalizing c with
  | zero => simp [matRep_apply]
  | add d e hd he =>
    have h1 : (monomial (d + e) c : MvPolynomial (Fin n' × Fin n) ℂ) = monomial d c * monomial e 1 := by
      rw [monomial_mul, mul_one]
    have hd' := hd c
    have he' := he 1
    rw [matRep_apply] at hd' he'
    rw [h1, matRep_apply, map_mul, hd', he', smul_mul_smul_comm, ← Finset.prod_mul_distrib]
    simp only [map_add (f := _), Pi.add_apply, pow_add]
  | single v k =>
    have h1 := hX v
    rw [matRep_apply] at h1
    rw [← C_mul_X_pow_eq_monomial, matRep_apply, map_mul, map_pow, h1, smul_pow, mul_smul_comm]
    congr 1
    · rw [Finset.prod_eq_single v.2]
      · simp [Finsupp.weight_single, colW]
      · intro b _ hb
        simp [Finsupp.weight_single, colW, hb]
      · simp
    · simp

theorem matRep_diagGL_component {n n' : ℕ} (t : Fin n → ℂˣ) (μ : Fin n → ℕ)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    matRep n n' (diagGL ℂ n t, 1) (weightedHomogeneousComponent (colW n' n) μ v) =
      (∏ s, (t s : ℂ) ^ μ s) • weightedHomogeneousComponent (colW n' n) μ v := by
  classical

  rw [weightedHomogeneousComponent_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [matRep_diagGL_monomial, (Finset.mem_filter.1 hd).2]

noncomputable def torusPowChar {n : ℕ} (μ : Fin n → ℕ) : (Fin n → ℂˣ) →* ℂ where
  toFun t := ∏ s, (t s : ℂ) ^ μ s
  map_one' := by simp
  map_mul' a b := by simp [mul_pow, Finset.prod_mul_distrib]

theorem torusPowChar_injective {n : ℕ} : Function.Injective (torusPowChar (n := n)) := by
  classical
  intro μ ν h
  funext a
  let t : Fin n → ℂˣ := Pi.mulSingle a (Units.mk0 2 two_ne_zero)
  have hprod : ∀ e : Fin n → ℕ, torusPowChar e t = 2 ^ e a := by
    intro e
    change ∏ s, (t s : ℂ) ^ e s = _
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb
      simp [t, hb]
    · simp
  have h1 : (2 : ℂ) ^ μ a = 2 ^ ν a := by rw [← hprod, ← hprod, h]
  have h' : (2 : ℕ) ^ μ a = 2 ^ ν a := by exact_mod_cast h1
  exact Nat.pow_right_injective le_rfl h'

theorem weightedHomogeneousComponent_colW_mem (n n' : ℕ) (M : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ))
    (hM : ∀ t : Fin n → ℂˣ, ∀ v ∈ M, matRep n n' (diagGL ℂ n t, 1) v ∈ M) (ν : Fin n → ℕ)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) (hv : v ∈ M) :
    weightedHomogeneousComponent (colW n' n) ν v ∈ M := by
  classical
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  have hfin := weightedHomogeneousComponent_finsupp (w := colW n' n) v
  have hsum := sum_weightedHomogeneousComponent (colW n' n) v
  rw [finsum_eq_sum _ hfin] at hsum
  by_cases hν : ν ∈ hfin.toFinset
  · have hli := (linearIndependent_monoidHom (Fin n → ℂˣ) ℂ).comp _ (torusPowChar_injective (n := n))
    refine linearIndependent_iff'.1 hli hfin.toFinset
      (fun μ => l (weightedHomogeneousComponent (colW n' n) μ v)) ?_ ν hν
    funext t
    have h0 := (Submodule.mem_dualAnnihilator l).1 hl _ (hM t v hv)

    rw [← hsum, map_sum, map_sum] at h0
    rw [Finset.sum_apply, Pi.zero_apply, ← h0]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [matRep_diagGL_component, map_smul, smul_eq_mul, mul_comm]
    rfl
  · have : weightedHomogeneousComponent (colW n' n) ν v = 0 := by
      by_contra h
      exact hν (hfin.mem_toFinset.2 h)
    rw [this, map_zero]

end GlobalTheory.GLDuality
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

noncomputable section

namespace GlobalTheory.GLDuality.Compl

private theorem totalDegree_sum_C_mul_X_le_one {σ : Type} [Fintype σ] (A : Matrix σ σ ℂ) (i : σ) :
    (∑ j, C (A i j) * X j : MvPolynomial σ ℂ).totalDegree ≤ 1 := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_X j).le

theorem totalDegree_linSub_le {σ : Type} [Fintype σ] (A : Matrix σ σ ℂ) (P : MvPolynomial σ ℂ) :
    (sub A P).totalDegree ≤ P.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [sub, aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  calc _ ≤ ∑ i ∈ m.support, ((∑ j, C (A i j) * X j : MvPolynomial σ ℂ) ^ m i).totalDegree :=
        totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ m.support, m i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans
          ((Nat.mul_le_mul_left (m i) (totalDegree_sum_C_mul_X_le_one A i)).trans (le_of_eq (mul_one _)))
    _ ≤ P.totalDegree := le_totalDegree hm

def fockLin {σ : Type} (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun f := fockF f g
  map_add' _ _ := Formalism.REAL.fischerInner_add_left _ _ _
  map_smul' c f := by
    rw [smul_eq_C_mul, LFocks_C_mul_left]
    rfl

def orth {σ : Type} (K : Submodule ℂ (MvPolynomial σ ℂ)) : Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨅ m : K, LinearMap.ker (fockLin (m : MvPolynomial σ ℂ))

theorem mem_orth {σ : Type} {K : Submodule ℂ (MvPolynomial σ ℂ)} {v : MvPolynomial σ ℂ} :
    v ∈ orth K ↔ ∀ m ∈ K, fockF v m = 0 := by
  constructor
  · intro h m hm
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 h ⟨m, hm⟩)
  · intro h
    exact (Submodule.mem_iInf _).2 fun m => LinearMap.mem_ker.2 (h m m.2)

private theorem fockF_sum_smul_right {σ ι : Type} (s : Finset ι) (c : ι → ℂ) (b : ι → MvPolynomial σ ℂ)
    (v : MvPolynomial σ ℂ) :
    fockF v (∑ i ∈ s, c i • b i) = ∑ i ∈ s, star (c i) * fockF v (b i) := by
  rw [Formalism.REAL.fischerInner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, Formalism.GradedWeylDivisibility.LFocks_C_mul_right]

theorem inf_orth_ne_bot {σ : Type} (U K : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ U] (h : K < U) :
    U ⊓ orth K ≠ ⊥ := by
  classical
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le h.le
  have hlt : Module.finrank ℂ K < Module.finrank ℂ U := Submodule.finrank_lt_finrank_of_lt h
  let b := Module.finBasis ℂ K

  let Φ : U →ₗ[ℂ] (Fin (Module.finrank ℂ K) → ℂ) :=
    LinearMap.pi fun i => (fockLin ((b i : K) : MvPolynomial σ ℂ)).comp U.subtype
  have hker : LinearMap.ker Φ ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hbot, finrank_bot, add_zero] at h1
    have h2 : Module.finrank ℂ (LinearMap.range Φ) ≤ Module.finrank ℂ K := by
      simpa using Submodule.finrank_le (LinearMap.range Φ)
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  intro hbot
  apply hx0
  have hmem : (x : MvPolynomial σ ℂ) ∈ U ⊓ orth K := by
    refine ⟨x.2, mem_orth.2 fun m hm => ?_⟩
    have hm' : m = ∑ i, (b.repr ⟨m, hm⟩ i) • ((b i : K) : MvPolynomial σ ℂ) := by
      have e := congrArg Subtype.val (b.sum_repr ⟨m, hm⟩)
      rw [Submodule.coe_sum] at e
      simpa only [Submodule.coe_smul] using e.symm
    rw [hm', fockF_sum_smul_right]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : fockF (x : MvPolynomial σ ℂ) ((b i : K) : MvPolynomial σ ℂ) = 0 :=
      congrFun (LinearMap.mem_ker.1 hx) i
    rw [h0, mul_zero]
  rw [hbot] at hmem
  exact Submodule.coe_eq_zero.1 ((Submodule.mem_bot ℂ).1 hmem)

theorem fockF_matRep {n n' : ℕ} (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (v m : MvPolynomial (Fin n' × Fin n) ℂ) :
    fockF (matRep n n' (g, h) v) m = fockF v (matRep n n' (star g, star h) m) := by
  have e : (((h : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (g : Matrix (Fin n) (Fin n) ℂ))ᵀ)ᴴ =
      (((star h : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ
        ((star g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ := by
    rw [Units.coe_star, Units.coe_star, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      ← Matrix.conjTranspose_kronecker]
    ext a b
    rfl
  rw [matRep_apply, matRep_apply, Formalism.GradedWeylDivisibility.fockSubAdj, e]

theorem exists_stable_disjoint (n n' : ℕ) (M : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hM : M ≠ ⊤)
    (hst : ∀ p : GL (Fin n) ℂ × GL (Fin n') ℂ, ∀ v ∈ M, matRep n n' p v ∈ M) :
    ∃ N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ), N ≠ ⊥ ∧ N ⊓ M = ⊥ ∧
      ∀ p : GL (Fin n) ℂ × GL (Fin n') ℂ, ∀ v ∈ N, matRep n n' p v ∈ N := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, p ∉ M := by
    by_contra hc
    push_neg at hc
    exact hM (eq_top_iff.2 fun x _ => hc x)

  let U := restrictTotalDegree (Fin n' × Fin n) ℂ p.totalDegree
  have hpU : p ∈ U := (mem_restrictTotalDegree _ _ _).2 le_rfl
  have hdeg : ∀ (a : GL (Fin n) ℂ) (c : GL (Fin n') ℂ) (w : MvPolynomial (Fin n' × Fin n) ℂ),
      w ∈ U → matRep n n' (a, c) w ∈ U := by
    intro a c w hw
    rw [mem_restrictTotalDegree] at hw ⊢
    rw [matRep_apply]
    exact (totalDegree_linSub_le _ _).trans hw
  have hKU : M ⊓ U < U := lt_of_le_of_ne inf_le_right fun hEq => by
    have hK : p ∈ M ⊓ U := by rw [hEq]; exact hpU
    exact hp hK.1
  refine ⟨U ⊓ orth (M ⊓ U), inf_orth_ne_bot U (M ⊓ U) hKU, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro v ⟨⟨hvU, hvO⟩, hvM⟩
    rw [Submodule.mem_bot]
    by_contra hv0
    have h0 : fockF v v = 0 := mem_orth.1 hvO v ⟨hvM, hvU⟩
    have hpos := (Formalism.GradedWeylDivisibility.fockPos _ v hv0).1
    rw [h0, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  · rintro ⟨a, c⟩ v ⟨hvU, hvO⟩
    refine ⟨hdeg a c v hvU, mem_orth.2 fun m hm => ?_⟩
    rw [fockF_matRep]
    exact mem_orth.1 hvO _ ⟨hst (star a, star c) m hm.1, hdeg _ _ m hm.2⟩

end GlobalTheory.GLDuality.Compl
end
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open scoped Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def dropCols (r m : ℕ) : MvPolynomial (Fin r × Fin r) ℂ →ₐ[ℂ] MvPolynomial (Fin r × Fin m) ℂ :=
  aeval fun v => if h : v.2.val < m then X (v.1, ⟨v.2.val, h⟩) else 0

theorem dropCols_rowAct (r m : ℕ) (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin r) ℂ) :
    dropCols r m (rowAct ℂ g f) = rowAct ℂ g (dropCols r m f) := by
  have : (dropCols r m).comp (rowAct ℂ g) = (rowAct ℂ g).comp (dropCols r m) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    by_cases hs : s.val < m <;> simp [dropCols, rowAct, hs]
  exact DFunLike.congr_fun this f

theorem dropCols_lpMinor (r m s : ℕ) (hr : s ≤ r) (hm : s ≤ m) :
    dropCols r m (lpMinor ℂ s hr hr) = lpMinor ℂ s hr hm := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext1 p q
  have hq : q.val < m := lt_of_lt_of_le q.2 hm
  simp [dropCols, hq, Fin.castLE]

theorem dropCols_hw (r m : ℕ) (h : m ≤ r) (ν : Fin m → ℕ) :
    dropCols r m (hw ℂ (le_refl r) (rowNu ν)) = hw ℂ h ν := by
  unfold hw
  rw [map_prod]
  symm
  refine Finset.prod_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro s _ hs
    have hs' : ¬ s.val < m := fun hlt => hs ⟨⟨s.val, hlt⟩, by simp, rfl⟩
    simp [rowNu, hs']
  · intro s _
    rw [map_pow]
    have e : nuNext (rowNu (r := r) ν) (Fin.castLE h s) = nuNext ν s := by
      simp only [nuNext, rowNu, Fin.val_castLE]
      split_ifs with h1 h2 h3
      · rfl
      · rfl
      · omega
      · rfl
    have e' : rowNu (r := r) ν (Fin.castLE h s) = ν s := by simp [rowNu]
    rw [e, e']
    congr 1
    exact (dropCols_lpMinor r m (s.val + 1) _ _).symm

theorem pad_detShift_nonneg {m : ℕ} (r : ℕ) (a : Part m) : 0 ≤ (pad r a).detShift := by
  unfold DomWeight.detShift
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

theorem pad_natW_add {m : ℕ} (r : ℕ) (a : Part m) (i : Fin r) :
    (pad r a).natW i + (pad r a).detShift.toNat = rowNu a.1 i := by
  have h0 := pad_detShift_nonneg r a
  have h1 : (pad r a).detShift ≤ (pad r a).w i := by
    unfold DomWeight.detShift
    rw [dite_eq_left i.pos]
    apply (pad r a).anti
    rw [Fin.le_def]
    have := i.2
    simp only
    omega
  have h2 : (pad r a).w i = (rowNu (r := r) a.1 i : ℕ) := rfl
  simp only [DomWeight.natW]
  omega

theorem exists_map_nablaSq_pad : ∀ (r m : ℕ) (h : m ≤ r) (a : Part m), ∃ j : nablaSq ℂ r (pad r a) →ₗ[ℂ] MvPolynomial (Fin r × Fin m) ℂ, (∀ (g : GL (Fin r) ℂ) (f : nablaSq ℂ r (pad r a)), j (sqRep ℂ r (pad r a) g f) = rowAct ℂ (g : Matrix (Fin r) (Fin r) ℂ)ᵀ (j f)) ∧ ∀ f : nablaSq ℂ r (pad r a), (f : MvPolynomial (Fin r × Fin r) ℂ) = extremal ℂ r (pad r a) → j f = hw ℂ h a.1 := by
  intro r m h a
  obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le (pad_detShift_nonneg r a)
  let j : nablaSq ℂ r (pad r a) →ₗ[ℂ] MvPolynomial (Fin r × Fin m) ℂ :=
    (dropCols r m).toLinearMap ∘ₗ LinearMap.mulLeft ℂ (lpMinor ℂ r le_rfl le_rfl ^ c) ∘ₗ
      (nablaSq ℂ r (pad r a)).subtype
  have hj : ∀ f, j f = dropCols r m (lpMinor ℂ r le_rfl le_rfl ^ c * f) := fun _ => rfl
  refine ⟨j, fun g f => ?_, fun f hf => ?_⟩
  · rw [hj, hj, ← dropCols_rowAct, (genericDet_pow_mul r c (fun _ => 0)).2.1, sqRep_coe, sqAct, hc,
      mul_smul_comm, Matrix.det_transpose]
    simp [detPow]
  · rw [hj, hf, extremal, genericDet_pow_mul_hw, ← dropCols_hw r m h]
    congr 2
    funext i
    have := pad_natW_add r a i
    rwa [hc, Int.toNat_natCast] at this

end GlobalTheory.GLDuality
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.symplectic_hom_transpose_gram_darboux : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    T'.gramᵀ = -(S.gram.submatrix e₁ e₁) → S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) → ∀ x y : WO S' T',
      symplO S T (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
        (HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      symplO S' T' x y := by
  first | exact @GlobalTheory.DarbouxSymp.symplO_darboux | exact GlobalTheory.DarbouxSymp.symplO_darboux | (intros; apply GlobalTheory.DarbouxSymp.symplO_darboux <;> assumption)
end
